/-
Track K sub-box generator (untrusted, compiled): for the initial boxes `t ∈ [a, b)` of the K1 tree of `k`, the tree of
the Float decisions (as `kgen`) is cut at the maximal subtrees with at most `M` evaluated leaves (external nodes, code
`15`); no leaf stays in the top tree.  Prints, per box,
  `BOX k t V nodes leaves nExt` (V = value of the cut tree with the native external values = the tree value),
  `TOP hexcode` (the top tree), and per external node in preorder
  `EXT v hexcode leaves lo_0,…,lo_{m-1} hi_0,…,hi_{m-1}` (v = native value of the subtree on its box).
Boxes with at most `M` leaves are printed as `WHOLE k t V nodes leaves hexcode` (they go to `shardSumK` shards).
Soundness never depends on this program: the kernel re-checks every claim (`cutOK`, `subOK`, `shardSumK`).
-/
import BHHCert.TreeKGen
import BHHCert.ShardK
import BHHCert.TreeCut

namespace BHH.Cert.KCut

/-- a tree read from preorder node codes (`m` coordinates: code `2 + d` with `d ≥ m` has no children, as in
`bnbStream`) -/
inductive CT
  | leaf
  | other (c : Nat)
  | split (c : Nat) (n : Nat) (l r : CT)
  deriving Inhabited

/-- number of evaluated leaves -/
def CT.leaves : CT → Nat
  | .leaf => 1
  | .other _ => 0
  | .split _ n _ _ => n

partial def parse (m : Nat) : List Nat → CT × List Nat
  | [] => (.other 0, [])
  | c :: rest =>
    if c = 1 then (.leaf, rest)
    else if 2 ≤ c ∧ c - 2 < m ∧ c ≠ 15 then
      let (l, r1) := parse m rest
      let (r, r2) := parse m r1
      (.split c (l.leaves + r.leaves) l r, r2)
    else (.other c, rest)

/-- preorder codes of a tree (accumulated in reverse) -/
def CT.codesRev : CT → List Nat → List Nat
  | .leaf, acc => 1 :: acc
  | .other c, acc => c :: acc
  | .split c _ l r, acc => r.codesRev (l.codesRev (c :: acc))

/-- an external node: subtree codes, box, leaves -/
structure Ext where
  codes : List Nat
  lo : List Int
  hi : List Int
  leaves : Nat

/-- cut at the maximal subtrees with `1 ≤ leaves ≤ M`: top codes (reversed) and external nodes (reversed) -/
def cut (M : Nat) : CT → List Int → List Int → List Nat × List Ext → List Nat × List Ext
  | t, lo, hi, (top, exts) =>
    if 1 ≤ t.leaves ∧ t.leaves ≤ M then
      (15 :: top, ⟨(t.codesRev []).reverse, lo, hi, t.leaves⟩ :: exts)
    else
      match t with
      | .split c _ l r =>
        let d := c - 2
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        let acc := cut M l lo (hi.set d mid) (c :: top, exts)
        cut M r (lo.set d mid) hi acc
      | .leaf => (1 :: top, exts)
      | .other c => (c :: top, exts)

def hexOf (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def intsStr (l : List Int) : String := ",".intercalate (l.map toString)

end BHH.Cert.KCut

open BHH.Cert BHH.Cert.KCut

def main (args : List String) : IO Unit := do
  match args with
  | [ks, as, bs, ms] =>
    let k := ks.toNat!
    let a := as.toNat!
    let b := bs.toNat!
    let M := ms.toNat!
    let ctx := if k == 3 then ctxK1_3 else ctxK1_4
    let L := LkK k
    for t in List.range' a (b - a) do
      let (lo, hi) := initBox k RNK t
      let cs := (encodeGo (floatDec ctx) FUEL lo hi []).reverse
      let (nodes, leaves) := codeStats cs
      let code := packCodes cs
      if leaves ≤ M then
        let v := treeK k L RNK t code
        IO.println s!"WHOLE {k} {t} {v} {nodes} {leaves} {hexOf code}"
      else
        let (tree, _) := parse (2 * k - 3) cs
        let (topRev, extsRev) := cut M tree lo hi ([], [])
        let top := topRev.reverse
        let exts := extsRev.reverse
        let vals := exts.map fun e => (bnbStream k L read4 FUEL (packCodes e.codes) e.lo e.hi).1
        let topCode := packCodes top
        let V := (bnbCut k L read4 FUEL topCode lo hi vals).1
        let whole := treeK k L RNK t code
        if V != whole then IO.eprintln s!"MISMATCH k={k} t={t} cut={V} whole={whole}"
        IO.println s!"BOX {k} {t} {V} {nodes} {leaves} {exts.length}"
        IO.println s!"TOP {hexOf topCode}"
        for (e, v) in exts.zip vals do
          IO.println s!"EXT {v} {hexOf (packCodes e.codes)} {e.leaves} {intsStr e.lo} {intsStr e.hi}"
  | _ => IO.println "usage: kcut k a b M"
