include("compiler/ssair/ir.jl")
include("compiler/ssair/domtree.jl")
include("compiler/ssair/slot2ssa.jl")
include("compiler/ssair/queries.jl")
include("compiler/ssair/passes.jl")
include("compiler/ssair/verify.jl")
include("compiler/ssair/legacy.jl")

macro show(s)
    # return :(println($(QuoteNode(s)), " = ", $(esc(s))))
end

function normalize(@nospecialize(stmt), meta::Vector{Any}, inline::Vector{Any}, loc::RefValue{LineNumberNode})
    if isa(stmt, Expr)
        if stmt.head == :meta
            args = stmt.args
            if length(args) > 0
                a1 = args[1]
                if a1 === :push_loc
                    push!(inline, stmt)
                elseif a1 === :pop_loc
                    n = (length(args) > 1) ? args[2]::Int : 1
                    for i in 1:n
                        isempty(inline) && break
                        pop!(inline)
                    end
                else
                    push!(meta, stmt)
                end
            end
            return nothing
        elseif stmt.head === :line
            return nothing # deprecated - we shouldn't encounter this
        elseif stmt.head === :gotoifnot
            return GotoIfNot(stmt.args...)
        elseif stmt.head === :return
            return ReturnNode{Any}(stmt.args...)
        end
    elseif isa(stmt, LabelNode)
        return nothing
    elseif isa(stmt, LineNumberNode)
        loc[] = stmt
        return nothing
    end
    return stmt
end

function run_passes(ci::CodeInfo, mod::Module, nargs::Int, toploc::LineNumberNode)
    ci.code = copy(ci.code)
    meta = Any[]
    lines = fill(LineNumberNode(0), length(ci.code))
    let inline = Any[], loc = RefValue(toploc)
        for i = 1:length(ci.code)
            stmt = ci.code[i]
            stmt = normalize(stmt, meta, inline, loc)
            ci.code[i] = stmt
            stmt === nothing || (lines[i] = loc[])
        end
    end
    ci.code = strip_trailing_junk!(ci.code, lines)
    cfg = compute_basic_blocks(ci.code)
    defuse_insts = scan_slot_def_use(nargs, ci)
    domtree = construct_domtree(cfg)
    ir = let code = Any[nothing for _ = 1:length(ci.code)]
             argtypes = ci.slottypes[1:(nargs+1)]
            IRCode(code, lines, cfg, argtypes, mod, meta)
        end
    #ccall(:jl_, Cvoid, (Any,), domtree.idoms)
    #@Core.Main.Base.show domtree
    # @show ci.code
    ir = construct_ssa!(ci, ir, domtree, defuse_insts, nargs)
    #@Core.Main.Base.show ("pre_compact", ir)
    ir = compact!(ir)
    #@Core.Main.Base.show ("post_compact", ir)
    #ccall(:jl_, Cvoid, (Any,), ir.stmts)
    # @show ("pre_verify", ir)
    verify_ir(ir)
    #ir = predicate_insertion_pass!(ir, domtree)
    #ir = compact!(ir)
    #@show ("pre_getfield_elim", ir)
    #ir = getfield_elim_pass!(ir)
    #ir = compact!(ir)
    #@Core.Main.Base.show ("pre_lift", ir)
    #ccall(:jl_, Cvoid, (Any,), ir.stmts)
    ir = type_lift_pass!(ir)
    ir = compact!(ir)
    #ccall(:jl_, Cvoid, (Any,), ir.stmts)
    verify_ir(ir)
    return ir
end
