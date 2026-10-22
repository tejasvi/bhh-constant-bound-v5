# Lean 4 proof of beta >= 0.6421301 (kernel only, standard axioms)

Theorems (`BHH/MainK1.lean`):

    theorem BHH.mainBoundsK1   : MainBoundsK1    -- C_3 >= 0.0117028397 and C_4 >= 0.0054272702
    theorem BHH.betaBoundK1    : BetaBoundK1     -- beta >= 0.6421301 for every beta with DongCaoK30 beta
    theorem BHH.bhhBetaBoundK1 : BHHBetaBoundK1  -- the same for the BHH constant

The label K1 in the names (`MainK1`, `MainBoundsK1`, `AXIOMS_K1.txt`, `AxK1.lean`, ...) marks this kernel-only proof.
The statements are in `BHH/StatementK.lean`. They use the objects and the three named hypotheses of the native proof:
`GreenFormula` (`BHH/Defs.lean`), `VertexLemmaSeg` and `DongCaoK30` (`BHH/DefsV2.lean`). `DongCaoK30 beta` says
beta >= 5/8 + sum_{k=3}^{30} C_k (Theorem 3 of Dong and Cao with K = 30). The theorem for the BHH constant assumes
`DongCaoK30 beta` for every beta with `IsBHHConstant beta`.

Axioms (`AXIOMS_K1.txt`, printed by `lake env lean AxK1.lean`): `propext`, `Classical.choice`, `Quot.sound` only.
Every leaf value is computed by the Lean kernel (`decide +kernel`). Some imported modules that the native proof also
uses contain `native_decide` lemmas; the theorems above do not use them, as the axiom list shows.

Files: the import closure of `BHH/MainK1.lean` without the generated modules `BHH/KSub/**` (10,112 files, not
shipped), plus the library root `BHHCert.lean` and the untrusted cut generator `BHHCert/KCutGen.lean`. To regenerate
`BHH/KSub`, run the two commands in `GEN_PARAMS.txt` from this directory, then `sha256sum -c KSub_SHA256SUMS`.
The generated modules are 416 `Data`, 9,278 chunk modules `S*`, 416 `Box` and 2 `Asm` modules. The chunk modules hold
97,182 theorems `subOK k (LkK k) chunk = true`, each proved by `decide +kernel` and each with at most 25 leaves
(1,738,828 leaves in all). Each `Data` module holds one more theorem `top : cutOK ...`, also proved by
`decide +kernel`, which checks the top part of the cut tree of its box against the claims of its pieces.

Build: Lean v4.35.0-rc3 and Mathlib c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). After regenerating
`BHH/KSub`, run `lake build BHH.MainK1`, then `lake env lean AxK1.lean`. The chunk modules do not depend on each other
and can be built in parallel; the original build took about one hour on 740 vCPUs.
