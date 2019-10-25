open Microsoft.Z3
open System
open System.Collections.Generic
open System.Diagnostics
open System.Text
open System.Text.RegularExpressions

let encodeEdge u v =
    let min, max = if u < v then u, v else v, u
    (min + max) * (min + max) + min

let getEdgesNumbers n =
    lazy(
            seq {for x in 1 .. n do yield seq{for y in x + 1 .. n do yield encodeEdge x y}}
            |> Seq.concat
        )

let getColorsNumbers k = lazy( List.init k ((+) 1))

let decodeEdge number =
    let sum = number |> double |> sqrt |> int
    let min = number - sum * sum
    let max = sum - min
    assert(min < max)
    min, max

//let defineColors k (sb : StringBuilder) =
//    let pattern = sprintf "(declare-const x%d Int)\n"
//    (getColorsNumbers k).Value |> List.fold (fun (sb : StringBuilder) c -> sb.Append(pattern c)) sb

let declareEdges n (sb : StringBuilder) =
    let pattern = sprintf "(declare-const y%d Int)\n"
    (getEdgesNumbers n).Value |> Seq.fold (fun (sb : StringBuilder) e -> sb.Append(pattern e)) sb

//let colorsAreDifferent k (sb : StringBuilder) =
//    let pattern = sprintf "(assert (not (= x%d x%d)))\n"
//    let colors = (getColorsNumbers k).Value
//    colors |> List.fold (fun (sb : StringBuilder) x1 ->
//        colors |> List.fold (fun (sb : StringBuilder) x2 ->
//            if x1 <= x2 then sb
//            else sb.Append(pattern x1 x2)) sb
//        ) sb

let paintEdges n k (sb : StringBuilder) =
    let assertP = sprintf "(assert %s)\n"
    let andP    = sprintf "(and %s)"
    let orP     = sprintf "(or %s)"
    let eqP     = sprintf "(= y%d %d)"
    let neqP    = sprintf "(not (= y%d %d))"
//    let pEq = sprintf "(assert (= y%d x%d))"
//    let pNEq = sprintf "(assert (not (= y%d x%d)))"
    let edges = (getEdgesNumbers n).Value
    let colors = (getColorsNumbers k).Value
    edges |> Seq.fold (fun (sb : StringBuilder) e ->
        let eIsPainted =
            colors |> Seq.fold (fun (sb : StringBuilder) c ->
                let colorIsC =
                     colors |> Seq.fold (fun (sb : StringBuilder) c' ->
                         if c = c' then sb.Append(eqP e c')  // hasColor
                         else sb.Append(neqP e c')           // doesNotHaveColor
                     ) (new StringBuilder())
                sb.Append(andP <| colorIsC.ToString())) (new StringBuilder())
        sb.Append(eIsPainted.ToString() |> orP |> assertP)
    ) sb

//
//        let falseTerm = ctx.MkFalse()
//        let sb = (getColorsNumbers k).Value |> List.fold (fun expr c ->
//
//            ctx.MkOr([expr; hasColorTerm])) falseTerm
//
//        sb.Append(pattern c)) sb

let trianglesAreNotOneColored n k (sb : StringBuilder) =
    let pattern = sprintf "(assert (not (and (= y%d %d) (= y%d %d) (= y%d %d))))\n"
    let colors = (getColorsNumbers k).Value
    let vertices = List.init n ((+) 1)
    let cartesian l1 l2 =
        l1 |> List.map (fun x -> l2 |> List.map (fun y -> (x, y))) |> List.concat
    let triples = cartesian vertices vertices
                  |> cartesian vertices
                  |> List.map (fun (x1, (x2, x3)) -> (x1, x2, x3))
                  |> List.filter (fun (x1, x2, x3) -> x1 < x2 && x2 < x3)

//    triples |> List.iter (fun x -> printfn "%O" x)

    triples |> List.fold (fun (sb : StringBuilder) (x1, x2, x3) ->
        colors |> List.fold (fun (sb : StringBuilder) c ->
            let e1 = encodeEdge x1 x2
            let e2 = encodeEdge x2 x3
            let e3 = encodeEdge x1 x3
            sb.Append(pattern e1 c e2 c e3 c)
            ) sb
        ) sb



let findN prefix k =
    let rec check n =
        printfn "%sChecking %d" prefix n
        let dict = new Dictionary<string, string>()
        dict.["model"] <- "true"
//        let assertP = sprintf "(assert (= %O %O))\n"
        let ctx = new Context(dict)
        let sb = new StringBuilder()
                 |> declareEdges n
//                 |> (fun sb -> Seq.fold (fun (sb : StringBuilder) (f : FuncDecl, e : Expr) -> sb.Append(assertP f.Name e)) sb definedColors)
                 |> paintEdges n k
                 |> trianglesAreNotOneColored n k

        let solver = ctx.MkSolver()
        let be = ctx.ParseSMTLIB2String(sb.ToString())

        solver.Add(be)
        let res = solver.Check();
        match res with
        | Status.SATISFIABLE ->
//            let model = solver.Model
//            model.Consts |> Seq.iter (fun v ->
//                let f = v.Key;
//                let e = v.Value;
//                let (u, v) = f.Name.ToString() |> (fun s -> s.Substring(1)) |> System.Int32.Parse |> decodeEdge
//                printfn "%O %O (%d, %d)" f.Name e u v)
//            check (model.Consts |> Seq.map(fun v -> (v.Key, v.Value))) (n + 1)
            check (n + 1)
        | Status.UNKNOWN -> printfn "%sres: %O" prefix res
        | Status.UNSATISFIABLE -> printfn "%s%d" prefix (n - 1)
        | _ -> raise <| new Exception()
    check (k + 1)


let countForK k =
    printfn "For k = %d" k
    let sw = new Stopwatch()
    sw.Start()
    findN "\t" k
    sw.Stop()
    printfn "Elapsed milliseconds = %O" sw.ElapsedMilliseconds

[<EntryPoint>]
let main _ =
    List.init 100 ((+)1) |> List.iter countForK
    0
