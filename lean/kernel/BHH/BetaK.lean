/-
The kernel-only proof: `BetaBoundK1` and `BHHBetaBoundK1` from `MainBoundsK1` (the terms `C_k`, `k ≥ 5`, are only used through
`C_k ≥ 0`).  Same pattern as `betaBoundV2_of` in `BHH/MainV2.lean`.
-/
import BHH.StatementK

open scoped ENNReal

namespace BHH

/-- `BetaBoundK1` from the bounds for `C_3` and `C_4` -/
theorem betaBoundK1_of (hM : MainBoundsK1) : BetaBoundK1 := by
  intro hG hV β hβ
  obtain ⟨h3, h4⟩ := hM hG hV
  unfold DongCaoK30 at hβ
  have e1 : Finset.Icc 3 30 = insert 3 (Finset.Icc 4 30) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by norm_num)).symm
  have e2 : Finset.Icc 4 30 = insert 4 (Finset.Icc 5 30) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (by norm_num)).symm
  rw [e1, Finset.sum_insert (by simp), e2, Finset.sum_insert (by simp)] at hβ
  have hsum : ENNReal.ofReal (6421301 / 10 ^ 7) ≤
      (5 / 8 : ℝ≥0∞) + (ENNReal.ofReal (117028397 / 10 ^ 10) + ENNReal.ofReal (54272702 / 10 ^ 10)) := by
    have e58 : (5 / 8 : ℝ≥0∞) = ENNReal.ofReal (5 / 8) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [e58, ← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hle : ENNReal.ofReal (6421301 / 10 ^ 7) ≤ ENNReal.ofReal β := by
    refine le_trans hsum (le_trans ?_ hβ)
    gcongr
    exact le_trans h4 le_self_add
  have hβpos : 0 < β := ENNReal.ofReal_pos.mp (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hle)
  exact (ENNReal.ofReal_le_ofReal_iff hβpos.le).mp hle

/-- `BHHBetaBoundK1` from `BetaBoundK1` -/
theorem bhhBetaBoundK1_of (hB : BetaBoundK1) : BHHBetaBoundK1 :=
  fun hG hV hDC β hβ => hB hG hV β (hDC β hβ)

end BHH
