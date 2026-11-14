import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheLossOfAnOverlapStepIsAdditiveBelowTheBindingEnergyOfTheMiddle
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeakenedOrTwistedContactsGiveASecondBoundStateOnWindowsOfRatioThreeAndFour
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsPositiveAndThereAreNoBoundStates
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfABlockAndAFarWindowIsMinusTheProductOfTheirCharges

/-!
# The sliver blocks of the Green matrix have a logarithmic diagonal and bulk dipole coupling

In the overlap splitting of a window `(R, 2(R + a) + b]` across its dyadic middle `(D, 2D]`,
`D = R + a`, the boundary-to-middle coupling `endCoupling Q R a b` decomposes into the
archimedean jet `endJet R a b` across the entire middle and the prime-contact coupling
`endContact Q R a b` localized on the two boundary slivers of the middle. This module proves the
two-sided analytical bounds on the middle's spectrum and Green matrix, closes the small-block
regime of the first overlap step unconditionally, and isolates the signed bulk-to-sliver dipole
cross-term that prevents pure sliver-block bounds from closing the step uniformly in block size.

* **Uniform two-sided enclosure of the binding energy** (`bindingEnergy_lt_three`):
  `-neutralBlock 1 1 1 ≤ bindingEnergy D < 3` at every block size `D ≥ 1`.
* **Logarithmic diagonal ridge on the Green matrix and its sliver blocks**
  (`primeFreeMiddle_diag_bounds`, `sum_erase_primeFreeMiddle_sq_le`, `groundVector_le`,
  `positiveChannel_diag_ge`, `greenMatrix_diag_bounds`): every row of `primeFreeMiddle D` has
  off-diagonal `ℓ²` mass at most `16` and diagonal `log D + O(1)`, so `groundVector D` is bounded
  entrywise by `4 / (log D − 3/2)` and both `greenPositive D` and `greenMatrix D` satisfy
  `1 / (2 log(2D)) ≤ greenMatrix D i i ≤ greenPositive D i i ≤ 1500 / log(2D)` for `D ≥ 2 ^ 256`.
  Consequently `D · greenMatrix D i i ≥ √(2D) / 8` diverges on every sliver block
  (`sqrt_div_eight_le_mul_greenMatrix_diag`, `not_exists_sliver_inv_bound`): neither
  `greenMatrix D` nor `greenPositive D` admits an `O(1/D)` entrywise sliver bound.
* **Unconditional small-block closure of the first overlap step**
  (`greenForm_of_firstStep_small`, `hermNegIndex_neutralWindow_eq_one_of_firstStep_small`):
  for `1 ≤ R ≤ 33`, `100 a ≤ 3 R`, `50 b ≤ 3(R + a)`, and `2 ≤ Q`, the Green inequality holds and
  `neutralWindow Q R (a + (R + a) + b)` holds one bound state.
* **Sliver localization, contact pencil, and sign-twin obstruction**
  (`endContact_eq_zero_of_bulk`, `endForm_eq_one_of_le_three_mul`,
  `pencilCoupling_greenPositive_add_neg`, `exists_primeFree_greenForm_gt`,
  `exists_signTwin_greenForm_gt`, `signTwin_obstruction`): up to ratio `3`, `endContact` vanishes
  on the interior bulk `{m | b ≤ 2 m ∧ D + m < 2 R}` and `endForm` is prime-free. Under
  `P(t) = −endJet − t • endContact`, both `t = 0` (prime-free) and `t = −1` (Liouville sign twin)
  violate the Green inequality on `(R, 3R]` at every block size `R ≥ 1`; hence no bound symmetric
  under `endContact ↦ −endContact` (omitting the negative bulk-to-sliver cross-term
  `2 (endJet e)ᵀ G₊ (endContact e)`) can hold.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### Uniform upper bound on the binding energy of the dyadic middle -/

/-- At a block maximizing `groundVector D`, the negative block potential bounds `bindingEnergy D`. -/
theorem bindingEnergy_le_exists_neg_blockPotential {D : ℕ} (hD : 1 ≤ D) :
    ∃ i : Fin D, bindingEnergy D ≤ -blockPotential 1 D D i := by
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ (groundVector D) Finset.univ_nonempty
  refine ⟨i₀, ?_⟩
  have hspec := groundPair_spec hD
  have hpos : 0 < groundVector D i₀ := hspec.1 i₀
  have heig := congrFun hspec.2.1.eig i₀
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at heig
  have hpot : blockPotential 1 D D i₀ = ∑ j : Fin D, primeFreeMiddle D i₀ j := by
    rw [blockPotential, ← Fin.sum_univ_eq_sum_range (fun l => neutralBlock 1 (D + i₀) (D + l)) D]
    rfl
  have hrow : blockPotential 1 D D i₀ * groundVector D i₀ ≤
      ∑ j : Fin D, primeFreeMiddle D i₀ j * groundVector D j := by
    rw [hpot, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i₀ = j
    · subst hij; exact le_rfl
    · have hneg : primeFreeMiddle D i₀ j ≤ 0 := (neutralWindow_neg_of_ne 1 D hij).le
      have hle : groundVector D j ≤ groundVector D i₀ := hi₀ j (Finset.mem_univ j)
      nlinarith
  nlinarith

/-- On the dyadic window `(D, 2D]`, every block has potential strictly above `−3`. -/
theorem neg_three_lt_blockPotential_dyadic {D j : ℕ} (hD : 1 ≤ D) (hj : j < D) :
    -3 < blockPotential 1 D D j := by
  rw [blockPotential_eq_of_window le_rfl hj]
  have hρ : blockDensity (D + j) =
      xLogXStep (D + j) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := rfl
  rw [hρ]
  have hb1 := le_xLogXStep (n := D + j) (by omega)
  have hb2 := xLogXStep_le (D + j + D + D)
  have hb3 := le_xLogXStep (n := D + j + D) (by omega)
  have hb4 := xLogXStep_le j
  have hb5 := xLogXStep_le (D - 1 - j)
  have h1 : 1 / (((D + j : ℕ) : ℝ) + 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 2 ≤ D + j + 1))
  have h2 : 1 / (((D + j + D : ℕ) : ℝ) + 1) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 3 ≤ D + j + D + 1))
  have hsum_log : Real.log (((D + j + D + D : ℕ) : ℝ) + 1) -
      Real.log (((D + j + D : ℕ) : ℝ) + 1) ≤ Real.log 2 := by
    have hp1 : (0 : ℝ) < ((D + j + D : ℕ) : ℝ) + 1 := by positivity
    have hle : ((D + j + D + D : ℕ) : ℝ) + 1 ≤ 2 * (((D + j + D : ℕ) : ℝ) + 1) := by
      push_cast; linarith
    have hl := Real.log_le_log (by positivity) hle
    rw [Real.log_mul two_ne_zero hp1.ne'] at hl
    linarith
  have hamgm : 4 * ((j : ℝ) + 1) * (((D - 1 - j : ℕ) : ℝ) + 1) ≤ (((D + j : ℕ) : ℝ) + 1) ^ 2 := by
    have hsub : ((D - 1 - j : ℕ) : ℝ) + 1 = (D : ℝ) - j := by
      have : D - 1 - j + 1 = D - j := by omega
      exact_mod_cast this
    rw [hsub]
    push_cast
    have hsq : ((D : ℝ) + 1) ^ 2 - 4 * ((j : ℝ) + 1) * ((D : ℝ) - j) =
        ((D : ℝ) - 1 - 2 * j) ^ 2 := by ring
    have hmon : ((D : ℝ) + 1) ^ 2 ≤ ((D : ℝ) + j + 1) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j, show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
    nlinarith [sq_nonneg ((D : ℝ) - 1 - 2 * j)]
  have hdiff_log : Real.log ((j : ℝ) + 1) + Real.log (((D - 1 - j : ℕ) : ℝ) + 1) ≤
      2 * Real.log (((D + j : ℕ) : ℝ) + 1) - 2 * Real.log 2 := by
    have hpj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hpk : (0 : ℝ) < ((D - 1 - j : ℕ) : ℝ) + 1 := by positivity
    have hpd : (0 : ℝ) < ((D + j : ℕ) : ℝ) + 1 := by positivity
    have hl := Real.log_le_log (by positivity) hamgm
    rw [Real.log_mul (by positivity) hpk.ne', Real.log_mul (by norm_num) hpj.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow] at hl
    push_cast at hl
    linarith
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := log_two_pi_lt_two
  have hl2 := Real.log_two_gt_d9
  linarith

/-- **Uniform two-sided enclosure of the binding energy**: `-neutralBlock 1 1 1 ≤ μ_D < 3` at
every block size `D ≥ 1`. -/
theorem bindingEnergy_lt_three {D : ℕ} (hD : 1 ≤ D) :
    -neutralBlock 1 1 1 ≤ bindingEnergy D ∧ bindingEnergy D < 3 := by
  refine ⟨(groundPair_spec hD).2.2, ?_⟩
  obtain ⟨i, hi⟩ := bindingEnergy_le_exists_neg_blockPotential hD
  linarith [neg_three_lt_blockPotential_dyadic hD i.2]

/-! ### Diagonal and off-diagonal bounds on `primeFreeMiddle` -/

/-- Telescoping bound `∑_{k=0}^{K-1} 1/(k + 1)² ≤ 2`. -/
theorem sum_range_inv_succ_sq_le (K : ℕ) :
    ∑ k ∈ range K, (1 / ((k : ℝ) + 1)) ^ 2 ≤ 2 := by
  have haux : ∀ n : ℕ, ∑ k ∈ range n, (1 / ((k : ℝ) + 1)) ^ 2 ≤
      if n = 0 then 0 else 2 - 1 / (n : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · rw [if_neg (Nat.succ_ne_zero n)]
        rw [if_neg hn.ne'] at ih
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hstep : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
          rw [div_sub_div _ _ hn0.ne' hn1.ne', one_mul, mul_one, add_sub_cancel_left]
          have : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
          rw [one_div_pow, one_pow]
          exact one_div_le_one_div_of_le (by positivity) this
        push_cast
        linarith
  refine (haux K).trans ?_
  split_ifs with hK
  · norm_num
  · have hK0 : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
    linarith [show (0 : ℝ) ≤ 1 / K by positivity]

/-- Each off-diagonal entry of `primeFreeMiddle D` is bounded in magnitude by `2 / |i − j|`. -/
theorem abs_primeFreeMiddle_of_ne_le {D : ℕ} {i j : Fin D} (hij : i ≠ j) :
    |primeFreeMiddle D i j| ≤ 2 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ) := by
  have hlt : max (D + (i : ℕ)) (D + (j : ℕ)) < 2 * min (D + (i : ℕ)) (D + (j : ℕ)) := by
    have := i.2; have := j.2; omega
  have hne : D + (i : ℕ) ≠ D + (j : ℕ) := fun h => hij (Fin.ext (by omega))
  have hdiff : max (D + (i : ℕ)) (D + (j : ℕ)) - min (D + (i : ℕ)) (D + (j : ℕ)) =
      max (i : ℕ) j - min (i : ℕ) j := by omega
  set d := max (i : ℕ) j - min (i : ℕ) j
  have hd1 : 1 ≤ d := by
    have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    omega
  set s := D + (i : ℕ) + (D + (j : ℕ)) + 1
  have hsd : d ≤ s := by omega
  have hp1 : 0 < xLogXDiff s := xLogXDiff_pos (by omega)
  have hp2 : 0 < xLogXDiff d := xLogXDiff_pos hd1
  have hb1 : xLogXDiff s ≤ 2 / (d : ℝ) :=
    (xLogXDiff_le (by omega)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hd1) (by exact_mod_cast hsd))
  have hb2 : xLogXDiff d ≤ 2 / (d : ℝ) := xLogXDiff_le hd1
  have hval : primeFreeMiddle D i j = -(xLogXDiff s + xLogXDiff d) / 2 := by
    simp only [primeFreeMiddle, neutralWindow, windowMatrix, Matrix.of_apply]
    rw [neutralBlock_eq_of_lt_two_mul hlt, if_neg hne, hdiff]
    ring
  rw [hval, abs_div, abs_neg, abs_of_pos (by linarith), abs_of_pos (by norm_num)]
  linarith

/-- **Uniform off-diagonal `ℓ²` row bound**: every row of `primeFreeMiddle D` has off-diagonal
square sum at most `16`. -/
theorem sum_erase_primeFreeMiddle_sq_le (D : ℕ) (i : Fin D) :
    ∑ j ∈ Finset.univ.erase i, (primeFreeMiddle D i j) ^ 2 ≤ 16 := by
  have hterm : ∀ j ∈ Finset.univ.erase i,
      (primeFreeMiddle D i j) ^ 2 ≤
        4 * (1 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ)) ^ 2 := by
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have habs := abs_primeFreeMiddle_of_ne_le hij
    have hsq : |primeFreeMiddle D i j| ^ 2 ≤
        (2 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    refine hsq.trans (le_of_eq ?_)
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  -- Split `j ≠ i` into `j < i` and `i < j`, reindexing each side into `range D`.
  have hsplit : (Finset.univ.erase i) =
      Finset.filter (fun j : Fin D => (j : ℕ) < i) Finset.univ ∪
        Finset.filter (fun j : Fin D => (i : ℕ) < j) Finset.univ := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
      Fin.ext_iff]
    omega
  have hdisj : Disjoint (Finset.filter (fun j : Fin D => (j : ℕ) < i) Finset.univ)
      (Finset.filter (fun j : Fin D => (i : ℕ) < j) Finset.univ) := by
    rw [Finset.disjoint_filter]
    intro j _ h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ j ∈ Finset.filter (fun j : Fin D => (j : ℕ) < i) Finset.univ,
      (1 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ)) ^ 2 ≤ 2 := by
    refine (Finset.sum_le_sum_of_ne_zero (t := range i)
      (f := fun j : Fin D => (1 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ)) ^ 2)
      (g := fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2)
      (i := fun j _ => (i : ℕ) - 1 - j) ?_ ?_ ?_).trans (sum_range_inv_succ_sq_le i)
    · intro j hj _
      have hj' := (Finset.mem_filter.mp hj).2
      exact Finset.mem_range.mpr (by omega)
    · intro j₁ hj₁ _ j₂ hj₂ _ heq
      have h1 := (Finset.mem_filter.mp hj₁).2
      have h2 := (Finset.mem_filter.mp hj₂).2
      exact Fin.ext (by omega)
    · intro j hj _
      have hj' := (Finset.mem_filter.mp hj).2
      have hd : max (i : ℕ) j - min (i : ℕ) j = ((i : ℕ) - 1 - j) + 1 := by omega
      rw [hd]; push_cast; exact le_rfl
  have hright : ∑ j ∈ Finset.filter (fun j : Fin D => (i : ℕ) < j) Finset.univ,
      (1 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ)) ^ 2 ≤ 2 := by
    refine (Finset.sum_le_sum_of_ne_zero (t := range (D - 1 - i))
      (f := fun j : Fin D => (1 / ((max (i : ℕ) j - min (i : ℕ) j : ℕ) : ℝ)) ^ 2)
      (g := fun k : ℕ => (1 / ((k : ℝ) + 1)) ^ 2)
      (i := fun j _ => (j : ℕ) - 1 - i) ?_ ?_ ?_).trans (sum_range_inv_succ_sq_le (D - 1 - i))
    · intro j hj _
      have hj' := (Finset.mem_filter.mp hj).2
      have hjD := j.2
      exact Finset.mem_range.mpr (by omega)
    · intro j₁ hj₁ _ j₂ hj₂ _ heq
      have h1 := (Finset.mem_filter.mp hj₁).2
      have h2 := (Finset.mem_filter.mp hj₂).2
      exact Fin.ext (by omega)
    · intro j hj _
      have hj' := (Finset.mem_filter.mp hj).2
      have hd : max (i : ℕ) j - min (i : ℕ) j = ((j : ℕ) - 1 - i) + 1 := by omega
      rw [hd]; push_cast; exact le_rfl
  linarith

/-- **Two-sided logarithmic enclosure of the diagonal of `primeFreeMiddle D`**. -/
theorem primeFreeMiddle_diag_bounds {D : ℕ} (hD : 1 ≤ D) (i : Fin D) :
    Real.log D - 5 / 2 ≤ primeFreeMiddle D i i ∧
      primeFreeMiddle D i i ≤ Real.log (2 * (D : ℝ)) := by
  have hlt : max (D + (i : ℕ)) (D + (i : ℕ)) < 2 * min (D + (i : ℕ)) (D + (i : ℕ)) := by omega
  have hdiag : primeFreeMiddle D i i =
      xLogXStep (D + i) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) -
        xLogXDiff (2 * (D + (i : ℕ)) + 1) / 2 := by
    simp only [primeFreeMiddle, neutralWindow, windowMatrix, Matrix.of_apply]
    rw [neutralBlock_eq_of_lt_two_mul hlt, if_pos rfl, Nat.sub_self, xLogXDiff_zero, add_zero,
      blockDensity, xLogXStep]
    congr 2; omega
  rw [hdiag]
  have hb_lo := le_xLogXStep (n := D + i) (by omega)
  have hb_hi := xLogXStep_le (D + i)
  have hjet_pos : 0 < xLogXDiff (2 * (D + (i : ℕ)) + 1) := xLogXDiff_pos (by omega)
  have hjet_hi : xLogXDiff (2 * (D + (i : ℕ)) + 1) ≤ 2 / 5 := by
    refine (xLogXDiff_le_two_div (by omega)).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by have : (3 : ℝ) ≤ ((2 * (D + (i : ℕ)) + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
          linarith)
  have h1 : 1 / (((D + (i : ℕ) : ℕ) : ℝ) + 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 2 ≤ D + (i : ℕ) + 1))
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hlog_lo : Real.log D ≤ Real.log (((D + (i : ℕ) : ℕ) : ℝ) + 1) :=
    Real.log_le_log hDpos (by exact_mod_cast (by omega : D ≤ D + (i : ℕ) + 1))
  have hlog_hi : Real.log (((D + (i : ℕ) : ℕ) : ℝ) + 1) ≤ Real.log (2 * (D : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have hi := i.2
    have : D + (i : ℕ) + 1 ≤ 2 * D := by omega
    exact_mod_cast this
  have hγ_lo := Real.one_half_lt_eulerMascheroniConstant
  have hγ_hi := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ_hi := log_two_pi_lt_two
  have hπ_lo : 1 < Real.log (2 * Real.pi) := by
    have : (3 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
    linarith [Real.log_lt_log (by norm_num) this, log_three_mem.1]
  constructor <;> linarith

/-! ### Ground-state delocalization and the universal Dirichlet diagonal bound -/

/-- **Delocalization of `groundVector D`**: whenever `3 / 2 < log D`, every coordinate of the unit
ground vector is bounded by `4 / (log D − 3/2)`. -/
theorem groundVector_le {D : ℕ} (hD : 1 ≤ D) (hlog : 3 / 2 < Real.log D) (i : Fin D) :
    groundVector D i ≤ 4 / (Real.log D - 3 / 2) := by
  have hspec := groundPair_spec hD
  have heig := congrFun hspec.2.1.eig i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at heig
  have hsplit : ∑ j : Fin D, primeFreeMiddle D i j * groundVector D j =
      primeFreeMiddle D i i * groundVector D i +
        ∑ j ∈ Finset.univ.erase i, primeFreeMiddle D i j * groundVector D j :=
    (Finset.add_sum_erase Finset.univ (fun j => primeFreeMiddle D i j * groundVector D j)
      (Finset.mem_univ i)).symm
  have hbal : (primeFreeMiddle D i i + bindingEnergy D) * groundVector D i =
      ∑ j ∈ Finset.univ.erase i, (-primeFreeMiddle D i j) * groundVector D j := by
    have hneg : ∑ j ∈ Finset.univ.erase i, (-primeFreeMiddle D i j) * groundVector D j =
        -(∑ j ∈ Finset.univ.erase i, primeFreeMiddle D i j * groundVector D j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i)
    (fun j => -primeFreeMiddle D i j) (groundVector D)
  have hrow : ∑ j ∈ Finset.univ.erase i, (-primeFreeMiddle D i j) ^ 2 ≤ 16 := by
    simpa only [neg_sq] using sum_erase_primeFreeMiddle_sq_le D i
  have hphi : ∑ j ∈ Finset.univ.erase i, groundVector D j ^ 2 ≤ 1 := by
    calc ∑ j ∈ Finset.univ.erase i, groundVector D j ^ 2
        ≤ ∑ j : Fin D, groundVector D j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
            (fun _ _ _ => sq_nonneg _)
      _ = groundVector D ⬝ᵥ groundVector D := Finset.sum_congr rfl fun j _ => sq (groundVector D j)
      _ = 1 := hspec.2.1.unit
  have hsq : ((primeFreeMiddle D i i + bindingEnergy D) * groundVector D i) ^ 2 ≤ 4 ^ 2 := by
    rw [hbal]
    have hprod : (∑ j ∈ Finset.univ.erase i, (-primeFreeMiddle D i j) ^ 2) *
        (∑ j ∈ Finset.univ.erase i, groundVector D j ^ 2) ≤ 16 * 1 :=
      mul_le_mul hrow hphi (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
    linarith
  have hMμ : Real.log D - 3 / 2 ≤ primeFreeMiddle D i i + bindingEnergy D := by
    linarith [(primeFreeMiddle_diag_bounds hD i).1, one_lt_bindingEnergy hD]
  have hpos : 0 < Real.log D - 3 / 2 := by linarith
  have habs : (primeFreeMiddle D i i + bindingEnergy D) * groundVector D i ≤ 4 := by
    by_contra hgt
    have : 4 < (primeFreeMiddle D i i + bindingEnergy D) * groundVector D i := not_le.mp hgt
    nlinarith
  rw [le_div_iff₀ hpos]
  nlinarith [hspec.1 i]

/-- **Universal Dirichlet diagonal lower bound** for the positive channel of a matrix with one
bound state. -/
theorem positiveChannel_diag_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    {φ : ι → ℝ} {μ c : ℝ} (h : OneBoundState M φ μ c) (i : ι)
    (hden : 0 < M i i + μ * (φ i) ^ 2) :
    (1 - (φ i) ^ 2) ^ 2 / (M i i + μ * (φ i) ^ 2) ≤ positiveChannel M φ μ i i := by
  set e : ι → ℝ := Pi.single i 1
  set z₀ : ι → ℝ := OneBoundState.perp φ e
  set α : ℝ := (1 - (φ i) ^ 2) / (M i i + μ * (φ i) ^ 2)
  have hφe : φ ⬝ᵥ e = φ i := by simp [e]
  have heM : e ⬝ᵥ (M *ᵥ e) = M i i := by simp [e]
  have hez₀ : e ⬝ᵥ z₀ = 1 - (φ i) ^ 2 := by
    simp [z₀, OneBoundState.perp, e, hφe, sq]
  have hMz₀ : z₀ ⬝ᵥ (M *ᵥ z₀) = M i i + μ * (φ i) ^ 2 := by
    have hf := h.form_eq e
    rw [heM, hφe] at hf
    linarith
  have hz : φ ⬝ᵥ (α • z₀) = 0 := by
    rw [dotProduct_smul, h.dot_perp e, smul_zero]
  have hdir := positiveChannel_ge h e hz
  have hdiag : e ⬝ᵥ (positiveChannel M φ μ *ᵥ e) = positiveChannel M φ μ i i := by simp [e]
  rw [hdiag, dotProduct_smul, smul_eq_mul, hez₀, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, hMz₀] at hdir
  refine le_trans (le_of_eq ?_) hdir
  dsimp [α]
  field_simp [hden.ne']
  ring

/-! ### Two-sided `Θ(1 / log D)` diagonal ridge on `greenPositive` and `greenMatrix` -/

theorem positiveChannel_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    (hM : ∀ i j, M i j = M j i) (φ : ι → ℝ) (μ : ℝ) (i j : ι) :
    positiveChannel M φ μ i j = positiveChannel M φ μ j i := by
  have hMt : Mᵀ = M := Matrix.ext fun a b => hM b a
  have hMinv : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMt]
  have hinv_symm : M⁻¹ i j = M⁻¹ j i := by
    rw [← hMinv, Matrix.transpose_apply]
  simp only [positiveChannel, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, hinv_symm]
  ring

/-- The column `greenPositive D *ᵥ e_i` is the orthogonal component of `M_D⁻¹ *ᵥ e_i`, so the
certified floor bounds its `ℓ²` norm squared by `5000 · greenPositive D i i`. -/
theorem greenPositive_col_norm_sq_le {D : ℕ} (hD : 1 ≤ D) (i : Fin D) :
    (greenPositive D *ᵥ Pi.single i 1) ⬝ᵥ (greenPositive D *ᵥ Pi.single i 1) ≤
      5000 * greenPositive D i i := by
  have h := oneBoundState_primeFreeMiddle hD
  set e : Fin D → ℝ := Pi.single i 1
  have hperp : greenPositive D *ᵥ e = OneBoundState.perp (groundVector D) ((primeFreeMiddle D)⁻¹ *ᵥ e) := by
    rw [greenPositive, positiveChannel_mulVec, OneBoundState.perp]
    have hφ : groundVector D ⬝ᵥ ((primeFreeMiddle D)⁻¹ *ᵥ e) =
        -(1 / bindingEnergy D) * (groundVector D ⬝ᵥ e) := by
      rw [dotProduct_mulVec_symm (fun a b => by
            have hMt : (primeFreeMiddle D)ᵀ = primeFreeMiddle D :=
              Matrix.ext fun x y => primeFreeMiddle_symm D y x
            have hMinv : ((primeFreeMiddle D)⁻¹)ᵀ = (primeFreeMiddle D)⁻¹ := by
              rw [Matrix.transpose_nonsing_inv, hMt]
            rw [← hMinv, Matrix.transpose_apply]),
        h.inv_mulVec_ground, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    rw [hφ, sub_eq_add_neg, ← neg_smul]
    congr 2; ring
  have hf := h.floor _ (h.dot_perp ((primeFreeMiddle D)⁻¹ *ᵥ e))
  have hform := positiveChannel_form h e
  have hdiag : e ⬝ᵥ (greenPositive D *ᵥ e) = greenPositive D i i := by simp [e]
  rw [← hperp] at hf hform
  change e ⬝ᵥ (greenPositive D *ᵥ e) = _ at hform
  rw [hdiag] at hform
  linarith

/-- Whenever `primeFreeMiddle D i i > 0`, `greenPositive D i i` is bounded above by the reciprocal
of the diagonal plus a quadratic correction. -/
theorem greenPositive_diag_le_of_pos {D : ℕ} (hD : 1 ≤ D) (i : Fin D)
    (hM : 0 < primeFreeMiddle D i i) :
    7 / 8 * primeFreeMiddle D i i * greenPositive D i i ≤
      1 + 160000 / primeFreeMiddle D i i := by
  have h := oneBoundState_primeFreeMiddle hD
  set e : Fin D → ℝ := Pi.single i 1
  set g : Fin D → ℝ := greenPositive D *ᵥ e
  have hMg : primeFreeMiddle D *ᵥ g = e - (groundVector D i) • groundVector D := by
    rw [show g = (primeFreeMiddle D)⁻¹ *ᵥ e +
        ((1 / bindingEnergy D) * (groundVector D ⬝ᵥ e)) • groundVector D from
      positiveChannel_mulVec _ _ _ e,
      Matrix.mulVec_add, h.mulVec_inv_mulVec, Matrix.mulVec_smul, h.eig, smul_smul]
    have hφe : groundVector D ⬝ᵥ e = groundVector D i := by simp [e]
    have hμ : (1 / bindingEnergy D * groundVector D i) * (-bindingEnergy D) = -groundVector D i := by
      field_simp [h.depth_pos.ne']
    rw [hφe, hμ, sub_eq_add_neg, neg_smul]
  have hcoord := congrFun hMg i
  simp only [Matrix.mulVec, dotProduct, e, Pi.sub_apply, Pi.single_eq_same, Pi.smul_apply,
    smul_eq_mul, ← sq] at hcoord
  have hgi : g i = greenPositive D i i := by simp [g, e, Matrix.mulVec]
  have hsplit : ∑ j : Fin D, primeFreeMiddle D i j * g j =
      primeFreeMiddle D i i * greenPositive D i i +
        ∑ j ∈ Finset.univ.erase i, primeFreeMiddle D i j * g j := by
    rw [← hgi]
    exact (Finset.add_sum_erase Finset.univ (fun j => primeFreeMiddle D i j * g j)
      (Finset.mem_univ i)).symm
  have hbal : primeFreeMiddle D i i * greenPositive D i i =
      1 - (groundVector D i) ^ 2 + ∑ j ∈ Finset.univ.erase i, (-primeFreeMiddle D i j) * g j := by
    have hneg : ∑ j ∈ Finset.univ.erase i, (-primeFreeMiddle D i j) * g j =
        -(∑ j ∈ Finset.univ.erase i, primeFreeMiddle D i j * g j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  have hamgm : ∀ j ∈ Finset.univ.erase i,
      (-primeFreeMiddle D i j) * g j ≤
        10000 / primeFreeMiddle D i i * (primeFreeMiddle D i j) ^ 2 +
          primeFreeMiddle D i i / 40000 * (g j) ^ 2 := by
    intro j _
    have hsq : 0 ≤ (20000 * primeFreeMiddle D i j + primeFreeMiddle D i i * g j) ^ 2 := sq_nonneg _
    have hden : 0 < 40000 * primeFreeMiddle D i i := by positivity
    rw [← mul_le_mul_left hden]
    have hrhs : 40000 * primeFreeMiddle D i i *
        (10000 / primeFreeMiddle D i i * (primeFreeMiddle D i j) ^ 2 +
          primeFreeMiddle D i i / 40000 * (g j) ^ 2) =
        400000000 * (primeFreeMiddle D i j) ^ 2 + (primeFreeMiddle D i i) ^ 2 * (g j) ^ 2 := by
      field_simp [hM.ne']; ring
    rw [hrhs]
    nlinarith
  have hsum := Finset.sum_le_sum hamgm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hrow := sum_erase_primeFreeMiddle_sq_le D i
  have hgnorm : ∑ j ∈ Finset.univ.erase i, (g j) ^ 2 ≤ 5000 * greenPositive D i i := by
    calc ∑ j ∈ Finset.univ.erase i, (g j) ^ 2
        ≤ ∑ j : Fin D, (g j) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
            (fun _ _ _ => sq_nonneg _)
      _ = g ⬝ᵥ g := Finset.sum_congr rfl fun j _ => sq (g j)
      _ ≤ 5000 * greenPositive D i i := greenPositive_col_norm_sq_le hD i
  have h1 : 10000 / primeFreeMiddle D i i * ∑ j ∈ Finset.univ.erase i, (primeFreeMiddle D i j) ^ 2 ≤
      160000 / primeFreeMiddle D i i := by
    have hp : 0 ≤ 10000 / primeFreeMiddle D i i := by positivity
    have := mul_le_mul_of_nonneg_left hrow hp
    linarith [show 10000 / primeFreeMiddle D i i * 16 = 160000 / primeFreeMiddle D i i by ring]
  have h2 : primeFreeMiddle D i i / 40000 * ∑ j ∈ Finset.univ.erase i, (g j) ^ 2 ≤
      1 / 8 * primeFreeMiddle D i i * greenPositive D i i := by
    have hp : 0 ≤ primeFreeMiddle D i i / 40000 := by positivity
    have := mul_le_mul_of_nonneg_left hgnorm hp
    linarith [show primeFreeMiddle D i i / 40000 * (5000 * greenPositive D i i) =
      1 / 8 * primeFreeMiddle D i i * greenPositive D i i by ring]
  linarith [sq_nonneg (groundVector D i)]

/-- **Two-sided `Θ(1 / log D)` diagonal enclosure of `greenMatrix D` and `greenPositive D`**:
for every `D ≥ 2 ^ 256` and every block `i : Fin D` (including both boundary slivers),
`1 / (2 log(2D)) ≤ greenMatrix D i i ≤ greenPositive D i i ≤ 1500 / log(2D)`. -/
theorem greenMatrix_diag_bounds {D : ℕ} (hD : 2 ^ 256 ≤ D) (i : Fin D) :
    1 / (2 * Real.log (2 * (D : ℝ))) ≤ greenMatrix D i i ∧
      greenMatrix D i i ≤ greenPositive D i i ∧
      greenPositive D i i ≤ 1500 / Real.log (2 * (D : ℝ)) := by
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  have hlogD : 177 < Real.log D := by
    have hle : ((2 ^ 256 : ℕ) : ℝ) ≤ D := by exact_mod_cast hD
    have hl := Real.log_le_log (by positivity) hle
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hl
    linarith [Real.log_two_gt_d9]
  have hlog2D_pos : 0 < Real.log (2 * (D : ℝ)) := by
    rw [Real.log_mul two_ne_zero hDpos.ne']
    linarith [Real.log_two_gt_d9]
  have hlog2D_le : Real.log (2 * (D : ℝ)) < Real.log D + 1 := by
    rw [Real.log_mul two_ne_zero hDpos.ne']
    linarith [Real.log_two_lt_d9]
  have hdiag := primeFreeMiddle_diag_bounds hD1 i
  have hM_lo : 9 / 10 * Real.log (2 * (D : ℝ)) ≤ primeFreeMiddle D i i := by linarith
  have hM_pos : 0 < primeFreeMiddle D i i := by linarith
  have hφ_pos : 0 < groundVector D i := (groundPair_spec hD1).1 i
  have hφ_hi : groundVector D i ≤ 4 / (Real.log D - 3 / 2) :=
    groundVector_le hD1 (by linarith) i
  have hφ_small : groundVector D i ≤ 1 / 40 := by
    have hden : (0 : ℝ) < Real.log D - 3 / 2 := by linarith
    rw [div_le_iff₀ hden] at hφ_hi
    nlinarith
  have hμ := bindingEnergy_lt_three hD1
  have hμ1 := one_lt_bindingEnergy hD1
  have hden_pos : 0 < primeFreeMiddle D i i + bindingEnergy D * (groundVector D i) ^ 2 := by
    nlinarith [sq_nonneg (groundVector D i)]
  have hden_hi : primeFreeMiddle D i i + bindingEnergy D * (groundVector D i) ^ 2 ≤
      11 / 10 * Real.log (2 * (D : ℝ)) := by
    have hφ2 : (groundVector D i) ^ 2 ≤ (1 / 40) ^ 2 :=
      pow_le_pow_left₀ hφ_pos.le hφ_small 2
    nlinarith [hdiag.2, hμ.2]
  have hnum_lo : 4 / 5 ≤ (1 - (groundVector D i) ^ 2) ^ 2 := by
    have hφ2 : (groundVector D i) ^ 2 ≤ 1 / 1600 := by
      have := pow_le_pow_left₀ hφ_pos.le hφ_small 2
      linarith
    have h1 : 9 / 10 ≤ 1 - (groundVector D i) ^ 2 := by linarith
    have := pow_le_pow_left₀ (by norm_num) h1 2
    linarith
  have hGplus_lo : 2 / (3 * Real.log (2 * (D : ℝ))) ≤ greenPositive D i i := by
    refine le_trans ?_ (positiveChannel_diag_ge (oneBoundState_primeFreeMiddle hD1) i hden_pos)
    calc 2 / (3 * Real.log (2 * (D : ℝ)))
        ≤ (4 / 5) / (11 / 10 * Real.log (2 * (D : ℝ))) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
      _ ≤ (1 - (groundVector D i) ^ 2) ^ 2 /
          (primeFreeMiddle D i i + bindingEnergy D * (groundVector D i) ^ 2) :=
          div_le_div₀ (by positivity) hnum_lo hden_pos hden_hi
  have hrank1_hi : 1 / bindingEnergy D * (groundVector D i) ^ 2 ≤
      1 / (6 * Real.log (2 * (D : ℝ))) := by
    have h1 : 1 / bindingEnergy D * (groundVector D i) ^ 2 ≤ (groundVector D i) ^ 2 := by
      have : 1 / bindingEnergy D ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_left (sq_nonneg _) this
    have hden : (0 : ℝ) < Real.log D - 3 / 2 := by linarith
    have h2 : (groundVector D i) ^ 2 ≤ (4 / (Real.log D - 3 / 2)) ^ 2 :=
      pow_le_pow_left₀ hφ_pos.le hφ_hi 2
    have h3 : (4 / (Real.log D - 3 / 2)) ^ 2 ≤ 1 / (6 * Real.log (2 * (D : ℝ))) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have hsub : 9 / 10 * Real.log (2 * (D : ℝ)) ≤ Real.log D - 3 / 2 := by linarith
      have hsq : (9 / 10 * Real.log (2 * (D : ℝ))) ^ 2 ≤ (Real.log D - 3 / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsub 2
      nlinarith
    linarith
  have hGeq : greenMatrix D i i =
      greenPositive D i i - 1 / bindingEnergy D * (groundVector D i) ^ 2 := by
    rw [greenMatrix_eq]
    simp [Matrix.vecMulVec_apply, sq]
  have hGplus_hi : greenPositive D i i ≤ 1500 / Real.log (2 * (D : ℝ)) := by
    have hub := greenPositive_diag_le_of_pos hD1 i hM_pos
    have h160 : (160 : ℝ) ≤ primeFreeMiddle D i i := by linarith
    have hquot : 160000 / primeFreeMiddle D i i ≤ 1000 := by
      rw [div_le_iff₀ hM_pos]; linarith
    rw [le_div_iff₀ hlog2D_pos]
    have hprod : 7 / 8 * (9 / 10 * Real.log (2 * (D : ℝ))) * greenPositive D i i ≤
        7 / 8 * primeFreeMiddle D i i * greenPositive D i i :=
      mul_le_mul_of_nonneg_right (by linarith) (by
        have := greenPositive_nonneg hD1 (Pi.single i 1)
        simpa using this)
    linarith
  refine ⟨?_, ?_, hGplus_hi⟩
  · rw [hGeq]
    have hdiff : 2 / (3 * Real.log (2 * (D : ℝ))) - 1 / (6 * Real.log (2 * (D : ℝ))) =
        1 / (2 * Real.log (2 * (D : ℝ))) := by field_simp [hlog2D_pos.ne']; ring
    linarith
  · rw [hGeq]
    have : 0 ≤ 1 / bindingEnergy D * (groundVector D i) ^ 2 := by positivity
    linarith

/-- Off-diagonal entrywise bound on `greenPositive D` and `greenMatrix D` for `D ≥ 2 ^ 256`. -/
theorem abs_greenMatrix_entry_le {D : ℕ} (hD : 2 ^ 256 ≤ D) (i j : Fin D) :
    |greenPositive D i j| ≤ 1500 / Real.log (2 * (D : ℝ)) ∧
      |greenMatrix D i j| ≤ 1501 / Real.log (2 * (D : ℝ)) := by
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  have hlog2D_pos : 0 < Real.log (2 * (D : ℝ)) := by
    rw [Real.log_mul two_ne_zero hDpos.ne']
    have hle : ((2 ^ 256 : ℕ) : ℝ) ≤ D := by exact_mod_cast hD
    have hl := Real.log_le_log (by positivity) hle
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hl
    linarith [Real.log_two_gt_d9]
  have hsymm : ∀ a b, greenPositive D a b = greenPositive D b a :=
    positiveChannel_symm (primeFreeMiddle_symm D) _ _
  have hpm : ∀ s : ℝ, s = 1 ∨ s = -1 →
      0 ≤ (Pi.single i 1 + s • Pi.single j 1) ⬝ᵥ
        (greenPositive D *ᵥ (Pi.single i 1 + s • Pi.single j 1)) :=
    fun s _ => greenPositive_nonneg hD1 _
  have expand : ∀ s : ℝ,
      (Pi.single i 1 + s • Pi.single j 1) ⬝ᵥ
        (greenPositive D *ᵥ (Pi.single i 1 + s • Pi.single j 1)) =
      greenPositive D i i + 2 * s * greenPositive D i j + s ^ 2 * greenPositive D j j := by
    intro s
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hij1 : (Pi.single i (1 : ℝ)) ⬝ᵥ (greenPositive D *ᵥ Pi.single j 1) = greenPositive D i j := by
      simp
    have hij2 : (Pi.single j (1 : ℝ)) ⬝ᵥ (greenPositive D *ᵥ Pi.single i 1) = greenPositive D i j := by
      simp [hsymm j i]
    have hii : (Pi.single i (1 : ℝ)) ⬝ᵥ (greenPositive D *ᵥ Pi.single i 1) = greenPositive D i i := by
      simp
    have hjj : (Pi.single j (1 : ℝ)) ⬝ᵥ (greenPositive D *ᵥ Pi.single j 1) = greenPositive D j j := by
      simp
    rw [hii, hjj, hij1, hij2]
    ring
  have hp1 := hpm 1 (Or.inl rfl)
  have hm1 := hpm (-1) (Or.inr rfl)
  rw [expand 1] at hp1
  rw [expand (-1)] at hm1
  have hbi := (greenMatrix_diag_bounds hD i).2.2
  have hbj := (greenMatrix_diag_bounds hD j).2.2
  have habs_plus : |greenPositive D i j| ≤ 1500 / Real.log (2 * (D : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨habs_plus, ?_⟩
  have hGeq : greenMatrix D i j =
      greenPositive D i j - 1 / bindingEnergy D * (groundVector D i * groundVector D j) := by
    rw [greenMatrix_eq]
    simp [Matrix.vecMulVec_apply]
  have hlogD : 177 < Real.log D := by
    have hle : ((2 ^ 256 : ℕ) : ℝ) ≤ D := by exact_mod_cast hD
    have hl := Real.log_le_log (by positivity) hle
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hl
    linarith [Real.log_two_gt_d9]
  have hlog2D_gt : 177 < Real.log (2 * (D : ℝ)) := by
    rw [Real.log_mul two_ne_zero hDpos.ne']
    linarith [Real.log_two_gt_d9]
  have hlog2D_le : Real.log (2 * (D : ℝ)) < Real.log D + 1 := by
    rw [Real.log_mul two_ne_zero hDpos.ne']
    linarith [Real.log_two_lt_d9]
  have hφi_pos := (groundPair_spec hD1).1 i
  have hφj_pos := (groundPair_spec hD1).1 j
  have hφi := groundVector_le hD1 (by linarith) i
  have hφj := groundVector_le hD1 (by linarith) j
  have hμ1 := one_lt_bindingEnergy hD1
  have hrank_nn : 0 ≤ 1 / bindingEnergy D * (groundVector D i * groundVector D j) := by positivity
  have hrank_hi : 1 / bindingEnergy D * (groundVector D i * groundVector D j) ≤
      1 / Real.log (2 * (D : ℝ)) := by
    have h1 : 1 / bindingEnergy D * (groundVector D i * groundVector D j) ≤
        groundVector D i * groundVector D j := by
      have : 1 / bindingEnergy D ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact mul_le_of_le_one_left (by positivity) this
    have hden : (0 : ℝ) < Real.log D - 3 / 2 := by linarith
    have h2 : groundVector D i * groundVector D j ≤ (4 / (Real.log D - 3 / 2)) ^ 2 := by
      rw [sq]
      exact mul_le_mul hφi hφj hφj_pos.le (by positivity)
    have h3 : (4 / (Real.log D - 3 / 2)) ^ 2 ≤ 1 / Real.log (2 * (D : ℝ)) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hlog2D_pos]
      have hsub : 9 / 10 * Real.log (2 * (D : ℝ)) ≤ Real.log D - 3 / 2 := by linarith
      have hsq : (9 / 10 * Real.log (2 * (D : ℝ))) ^ 2 ≤ (Real.log D - 3 / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsub 2
      nlinarith
    linarith
  rw [hGeq, abs_le]
  rw [abs_le] at habs_plus
  have hlo : -(1501 / Real.log (2 * (D : ℝ))) =
      -(1500 / Real.log (2 * (D : ℝ))) - 1 / Real.log (2 * (D : ℝ)) := by ring
  have hhi : 1500 / Real.log (2 * (D : ℝ)) ≤ 1501 / Real.log (2 * (D : ℝ)) :=
    div_le_div_of_nonneg_right (by norm_num) hlog2D_pos.le
  constructor <;> linarith

/-- **Divergence of `D · greenMatrix D i i` on every block of `(D, 2D]`**: for `D ≥ 2 ^ 256`,
`√(2D) / 8 ≤ D · greenMatrix D i i`. -/
theorem sqrt_div_eight_le_mul_greenMatrix_diag {D : ℕ} (hD : 2 ^ 256 ≤ D) (i : Fin D) :
    Real.sqrt (2 * (D : ℝ)) / 8 ≤ (D : ℝ) * greenMatrix D i i := by
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
  have h2D : (0 : ℝ) < 2 * (D : ℝ) := by positivity
  have hs : (0 : ℝ) < Real.sqrt (2 * (D : ℝ)) := Real.sqrt_pos.mpr h2D
  have hlog_pos : 0 < Real.log (2 * (D : ℝ)) := by
    rw [Real.log_mul two_ne_zero hDpos.ne']
    linarith [Real.log_two_gt_d9, Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD1)]
  have hlog_le : Real.log (2 * (D : ℝ)) ≤ 2 * Real.sqrt (2 * (D : ℝ)) := by
    have h1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt h2D.le] at h1
    linarith
  have hlo := (greenMatrix_diag_bounds hD i).1
  have hmul : (D : ℝ) / (2 * Real.log (2 * (D : ℝ))) ≤ (D : ℝ) * greenMatrix D i i := by
    have := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg D)
    rwa [mul_one_div] at this
  refine le_trans ?_ hmul
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have hsq : Real.sqrt (2 * (D : ℝ)) * Real.sqrt (2 * (D : ℝ)) = 2 * (D : ℝ) :=
    Real.mul_self_sqrt h2D.le
  nlinarith

/-- **Refutation of `O(1/D)` sliver bounds**: for every constant `M : ℝ`, there exists `D₀` such
that for every `D ≥ D₀` and every block `i : Fin D` (including both boundary slivers),
`M ≤ D · greenMatrix D i i ≤ D · greenPositive D i i`. -/
theorem not_exists_sliver_inv_bound (M : ℝ) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ i : Fin D,
      M ≤ (D : ℝ) * greenMatrix D i i ∧
        (D : ℝ) * greenMatrix D i i ≤ (D : ℝ) * greenPositive D i i := by
  set K : ℕ := Nat.ceil (max M 0)
  refine ⟨max (2 ^ 256) (32 * K ^ 2 + 1), fun D hD i => ?_⟩
  have hD256 : 2 ^ 256 ≤ D := le_trans (le_max_left _ _) hD
  have hDK : 32 * K ^ 2 + 1 ≤ D := le_trans (le_max_right _ _) hD
  refine ⟨?_, mul_le_mul_of_nonneg_left (greenMatrix_diag_bounds hD256 i).2.1 (Nat.cast_nonneg D)⟩
  have hMK : M ≤ (K : ℝ) := (le_max_left M 0).trans (Nat.le_ceil _)
  have h8K : 8 * (K : ℝ) ≤ Real.sqrt (2 * (D : ℝ)) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 8 * (K : ℝ))]
    refine Real.sqrt_le_sqrt ?_
    have hcast : ((32 * K ^ 2 + 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast hDK
    push_cast at hcast
    nlinarith
  linarith [sqrt_div_eight_le_mul_greenMatrix_diag hD256 i]

/-! ### Unconditional small-block closure of the first overlap step -/

/-- **Unconditional small-block bound state count**: for `1 ≤ R ≤ 33`, `100 a ≤ 3 R`,
`50 b ≤ 3(R + a)`, and `2 ≤ Q`, `a = 0` and `50(a + (R + a) + b) ≤ 53 R`, so the window holds
exactly one bound state. -/
theorem hermNegIndex_neutralWindow_eq_one_of_firstStep_small {Q R a b : ℕ} (hR : 1 ≤ R)
    (hR33 : R ≤ 33) (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (hQ : 2 ≤ Q) :
    hermNegIndex ((neutralWindow Q R (a + (R + a) + b)).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one hR (by omega) (by omega) hQ

/-- **Unconditional small-block Schur nonnegativity** on the first overlap step (`1 ≤ R ≤ 33`). -/
theorem overlapSchur_nonneg_of_firstStep_small {Q R a b : ℕ} (hR : 1 ≤ R) (hR33 : R ≤ 33)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (hQ : 2 ≤ Q)
    (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (overlapSchur Q R a b *ᵥ e) :=
  (hermNegIndex_neutralWindow_eq_one_iff_overlapSchur a b hR hQ).mp
    (hermNegIndex_neutralWindow_eq_one_of_firstStep_small hR hR33 ha hb hQ) e

/-- **Unconditional small-block Green inequality** on the first overlap step (`1 ≤ R ≤ 33`). -/
theorem greenForm_of_firstStep_small {Q R a b : ℕ} (hR : 1 ≤ R) (hR33 : R ≤ 33)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (hQ : 2 ≤ Q)
    (e : Fin a ⊕ Fin b → ℝ) :
    (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) ≤
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) := by
  have hS := overlapSchur_nonneg_of_firstStep_small hR hR33 ha hb hQ e
  rw [overlapSchur_form_eq_channels Q R a b (by omega)] at hS
  linarith

/-! ### Decomposition into bulk jet and sliver prime contact -/

/-- The positive archimedean jet coupling `−endCoupling 1 R a b` between the dyadic middle and the
two ends of `(R, 2(R + a) + b]`. -/
def endJet (R a b : ℕ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  -endCoupling 1 R a b

/-- The nonnegative prime-contact coupling `endCoupling 1 R a b − endCoupling Q R a b` between the
dyadic middle and the two ends of `(R, 2(R + a) + b]`. -/
def endContact (Q R a b : ℕ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  endCoupling 1 R a b - endCoupling Q R a b

theorem endCoupling_eq_neg_endJet_sub_endContact (Q R a b : ℕ) :
    endCoupling Q R a b = -endJet R a b - endContact Q R a b := by
  ext m p
  simp only [endJet, endContact, Matrix.sub_apply, Matrix.neg_apply]
  ring

theorem endCoupling_apply (Q R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    endCoupling Q R a b m p =
      neutralBlock Q (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) := by
  rcases p with i | j <;> rfl

theorem middlePos_ne_endPos (R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    middlePos R a m ≠ Sum.elim (leftPos R a) (rightPos R a b) p := by
  rcases p with i | j
  · have := i.2; simp only [middlePos, leftPos, Sum.elim_inl]; omega
  · have := m.2; simp only [middlePos, rightPos, Sum.elim_inr]; omega

theorem neutralBlock_eq_neg_jet_sub_contact_of_ne (Q : ℕ) {x y : ℕ} (hne : x ≠ y) :
    neutralBlock Q x y = -blockJet (min x y) (max x y) - floorContact Q (min x y) (max x y) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [neutralBlock_of_lt hlt, min_eq_left hlt.le, max_eq_right hlt.le]
  · rw [neutralBlock_comm, neutralBlock_of_lt hgt, min_eq_right hgt.le, max_eq_left hgt.le]

theorem floorContact_one (x y : ℕ) : floorContact 1 x y = 0 := by
  rw [floorContact, Finset.Icc_eq_empty_of_lt (by norm_num : 1 < 2), Finset.sum_empty]

theorem endJet_apply (R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    endJet R a b m p =
      blockJet (min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p))
        (max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p)) := by
  rw [endJet, Matrix.neg_apply, endCoupling_apply,
    neutralBlock_eq_neg_jet_sub_contact_of_ne 1 (middlePos_ne_endPos R a b m p),
    floorContact_one, sub_zero, neg_neg]

theorem endContact_apply (Q R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    endContact Q R a b m p =
      floorContact Q (min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p))
        (max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p)) := by
  rw [endContact, Matrix.sub_apply, endCoupling_apply, endCoupling_apply,
    neutralBlock_eq_neg_jet_sub_contact_of_ne 1 (middlePos_ne_endPos R a b m p),
    neutralBlock_eq_neg_jet_sub_contact_of_ne Q (middlePos_ne_endPos R a b m p),
    floorContact_one]
  ring

/-- Every entry of `endJet R a b` is strictly positive across the entire middle. -/
theorem endJet_pos (R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    0 < endJet R a b m p := by
  rw [endJet_apply, blockJet]
  have hlt : min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) <
      max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) :=
    min_lt_max.mpr (middlePos_ne_endPos R a b m p)
  have h1 := xLogXDiff_pos (n := min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) +
    max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) + 1) (by omega)
  have h2 := xLogXDiff_pos
    (n := max (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p) -
      min (middlePos R a m) (Sum.elim (leftPos R a) (rightPos R a b) p)) (by omega)
  linarith

/-- Every entry of `endContact Q R a b` is nonnegative. -/
theorem endContact_nonneg (Q R a b : ℕ) (m : Fin (R + a)) (p : Fin a ⊕ Fin b) :
    0 ≤ endContact Q R a b m p := by
  rw [endContact_apply, floorContact]
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
  · exact le_rfl

/-- **Sliver localization of `endContact`**: on the interior bulk `{m | b ≤ 2 m ∧ R + a + m < 2 R}`
of the dyadic middle, `endContact Q R a b` vanishes identically against both ends. -/
theorem endContact_eq_zero_of_bulk (Q R a b : ℕ) (m : Fin (R + a)) (hb : b ≤ 2 * (m : ℕ))
    (hR : R + a + (m : ℕ) < 2 * R) (p : Fin a ⊕ Fin b) :
    endContact Q R a b m p = 0 := by
  rw [endContact_apply]
  refine floorContact_eq_zero_of_lt_two_mul ?_
  rcases p with i | j
  · simp only [middlePos, leftPos, Sum.elim_inl]
    have := i.2; omega
  · simp only [middlePos, rightPos, Sum.elim_inr]
    have := j.2; omega

/-! ### Prime-freeness of `endForm` up to ratio `3`, contact pencil, and sign-twin obstruction -/

theorem floorGraph_eq_zero_of_lt_three_mul {k x y : ℕ} (hk : 3 ≤ k) (hxy : max x y < 3 * min x y) :
    floorGraph k x y = 0 := by
  rw [floorGraph]
  refine if_neg fun h => ?_
  have h1 : max x y / k * k ≤ max x y := Nat.div_mul_le_self _ k
  rw [h] at h1
  have h2 : min x y * 3 ≤ min x y * k := Nat.mul_le_mul_left _ hk
  omega

theorem floorGraph_endPos_eq_zero_of_le_three_mul {R a b k : ℕ} (hR : 1 ≤ R)
    (h3 : 2 * (R + a) + b ≤ 3 * R) (hk : 2 ≤ k) (p₁ p₂ : Fin a ⊕ Fin b) :
    floorGraph k (Sum.elim (leftPos R a) (rightPos R a b) p₁)
      (Sum.elim (leftPos R a) (rightPos R a b) p₂) = 0 := by
  have hwlog : ∀ u v : ℕ, u ≤ v →
      ((u < R + a ∧ v < R + a ∧ R ≤ u) ∨
        (2 * (R + a) ≤ u ∧ v < 2 * (R + a) + b) ∨
        (R ≤ u ∧ u < R + a ∧ 2 * (R + a) ≤ v ∧ v < 2 * (R + a) + b)) →
      floorGraph k u v = 0 := by
    intro u v huv hcases
    rcases hcases with ⟨_, hv, hu⟩ | ⟨hu, hv⟩ | ⟨hu, hua, hv, hvb⟩
    · exact floorGraph_eq_zero hk huv (by omega)
    · exact floorGraph_eq_zero hk huv (by omega)
    · rcases eq_or_lt_of_le hk with rfl | hk3
      · rw [floorGraph_of_le 2 huv]
        refine if_neg fun h => ?_
        have : R + a ≤ v / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
        omega
      · exact floorGraph_eq_zero_of_lt_three_mul hk3
          (by rw [max_eq_right huv, min_eq_left huv]; omega)
  set x := Sum.elim (leftPos R a) (rightPos R a b) p₁
  set y := Sum.elim (leftPos R a) (rightPos R a b) p₂
  rcases le_total x y with hxy | hyx
  · refine hwlog x y hxy ?_
    rcases p₁ with i₁ | j₁ <;> rcases p₂ with i₂ | j₂
    · exact Or.inl ⟨by simp [x, leftPos], by simp [y, leftPos], by simp [x, leftPos]⟩
    · exact Or.inr (Or.inr ⟨by simp [x, leftPos], by simp [x, leftPos],
        by simp [y, rightPos], by simp [y, rightPos]⟩)
    · exfalso
      have hx : 2 * (R + a) ≤ x := by simp [x, rightPos]
      have hy : y < R + a := by simp [y, leftPos]
      omega
    · exact Or.inr (Or.inl ⟨by simp [x, rightPos], by simp [y, rightPos]⟩)
  · rw [floorGraph_comm]
    refine hwlog y x hyx ?_
    rcases p₂ with i₂ | j₂ <;> rcases p₁ with i₁ | j₁
    · exact Or.inl ⟨by simp [y, leftPos], by simp [x, leftPos], by simp [y, leftPos]⟩
    · exact Or.inr (Or.inr ⟨by simp [y, leftPos], by simp [y, leftPos],
        by simp [x, rightPos], by simp [x, rightPos]⟩)
    · exfalso
      have hy : 2 * (R + a) ≤ y := by simp [y, rightPos]
      have hx : x < R + a := by simp [x, leftPos]
      omega
    · exact Or.inr (Or.inl ⟨by simp [y, rightPos], by simp [x, rightPos]⟩)

/-- **Prime-freeness of `endForm` up to ratio `3`**: when `2(R + a) + b ≤ 3 R`, neither `k = 2` nor
`k ≥ 3` connects any two blocks of the ends `(R, R + a] ∪ (2(R + a), 2(R + a) + b]`. -/
theorem endForm_eq_one_of_le_three_mul {R a b : ℕ} (Q : ℕ) (hR : 1 ≤ R)
    (h3 : 2 * (R + a) + b ≤ 3 * R) :
    endForm Q R a b = endForm 1 R a b := by
  have hblk : ∀ p₁ p₂ : Fin a ⊕ Fin b,
      neutralBlock Q (Sum.elim (leftPos R a) (rightPos R a b) p₁)
        (Sum.elim (leftPos R a) (rightPos R a b) p₂) =
      neutralBlock 1 (Sum.elim (leftPos R a) (rightPos R a b) p₁)
        (Sum.elim (leftPos R a) (rightPos R a b) p₂) := by
    intro p₁ p₂
    set x := Sum.elim (leftPos R a) (rightPos R a b) p₁
    set y := Sum.elim (leftPos R a) (rightPos R a b) p₂
    by_cases hxy : x = y
    · rw [hxy, neutralBlock, neutralBlock, blockMatrix, blockMatrix, floorContact_one]
      have hx1 : 1 ≤ y := by rcases p₂ with i | j <;> simp [y, leftPos, rightPos] <;> omega
      rw [min_self, max_self, floorContact_self hx1]
    · rw [neutralBlock_eq_neg_jet_sub_contact_of_ne Q hxy,
        neutralBlock_eq_neg_jet_sub_contact_of_ne 1 hxy, floorContact_one,
        floorContact_eq_sum_floorGraph Q min_le_max]
      have h0 : ∑ k ∈ Icc 2 Q, floorGraph k (min x y) (max x y) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rcases le_total x y with hle | hge
        · rw [min_eq_left hle, max_eq_right hle]
          exact floorGraph_endPos_eq_zero_of_le_three_mul hR h3 (Finset.mem_Icc.mp hk).1 p₁ p₂
        · rw [min_eq_right hge, max_eq_left hge]
          exact floorGraph_endPos_eq_zero_of_le_three_mul hR h3 (Finset.mem_Icc.mp hk).1 p₂ p₁
      rw [h0]
  ext p₁ p₂
  rcases p₁ with i₁ | j₁ <;> rcases p₂ with i₂ | j₂
  · exact hblk (Sum.inl i₁) (Sum.inl i₂)
  · exact hblk (Sum.inl i₁) (Sum.inr j₂)
  · simpa only [endForm, fromBlocks_apply₂₁, Matrix.transpose_apply, posMatrix, Matrix.of_apply,
      neutralBlock_comm] using hblk (Sum.inr j₁) (Sum.inl i₂)
  · exact hblk (Sum.inr j₁) (Sum.inr j₂)

/-- The one-parameter coupling pencil `P(t) = −endJet − t • endContact` interpolating between
prime-free coupling (`t = 0`), true coupling (`t = 1`), and the sign-flipped twin (`t = −1`). -/
def pencilCoupling (Q R a b : ℕ) (t : ℝ) : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ :=
  -endJet R a b - t • endContact Q R a b

theorem pencilCoupling_zero (Q R a b : ℕ) :
    pencilCoupling Q R a b 0 = endCoupling 1 R a b := by
  simp [pencilCoupling, endJet]

theorem pencilCoupling_one (Q R a b : ℕ) :
    pencilCoupling Q R a b 1 = endCoupling Q R a b := by
  rw [pencilCoupling, one_smul, ← endCoupling_eq_neg_endJet_sub_endContact]

/-- **Symmetric polarization identity** along the contact pencil `P(±t)`: averaging `t` and `−t`
cancels the bulk-to-sliver dipole cross-term and isolates the pure jet and pure sliver squares. -/
theorem pencilCoupling_greenPositive_add_neg (Q R a b : ℕ) (t : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    (pencilCoupling Q R a b t *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b t *ᵥ e)) +
      (pencilCoupling Q R a b (-t) *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b (-t) *ᵥ e)) =
    2 * ((endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endJet R a b *ᵥ e)) +
      t ^ 2 * ((endContact Q R a b *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (endContact Q R a b *ᵥ e)))) := by
  have hsymm : ∀ x y, greenPositive (R + a) x y = greenPositive (R + a) y x :=
    positiveChannel_symm (primeFreeMiddle_symm (R + a)) _ _
  have expand : ∀ s : ℝ,
      (pencilCoupling Q R a b s *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b s *ᵥ e)) =
      (endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endJet R a b *ᵥ e)) +
        2 * s * ((endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endContact Q R a b *ᵥ e))) +
        s ^ 2 * ((endContact Q R a b *ᵥ e) ⬝ᵥ
          (greenPositive (R + a) *ᵥ (endContact Q R a b *ᵥ e))) := by
    intro s
    have hmul : pencilCoupling Q R a b s *ᵥ e =
        -(endJet R a b *ᵥ e) - s • (endContact Q R a b *ᵥ e) := by
      rw [pencilCoupling, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec]
    rw [hmul]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_smul, sub_dotProduct,
      neg_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_neg, dotProduct_smul,
      smul_eq_mul, neg_neg]
    rw [dotProduct_mulVec_symm hsymm (endContact Q R a b *ᵥ e) (endJet R a b *ᵥ e)]
    ring
  rw [expand t, expand (-t)]
  ring

/-- **Antisymmetric polarization identity** along the contact pencil `P(±t)`: subtracting `−t` from
`t` isolates four times the bulk-to-sliver dipole cross-term. -/
theorem pencilCoupling_greenPositive_sub_neg (Q R a b : ℕ) (t : ℝ) (e : Fin a ⊕ Fin b → ℝ) :
    (pencilCoupling Q R a b t *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b t *ᵥ e)) -
      (pencilCoupling Q R a b (-t) *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b (-t) *ᵥ e)) =
    4 * t * ((endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endContact Q R a b *ᵥ e))) := by
  have hsymm : ∀ x y, greenPositive (R + a) x y = greenPositive (R + a) y x :=
    positiveChannel_symm (primeFreeMiddle_symm (R + a)) _ _
  have expand : ∀ s : ℝ,
      (pencilCoupling Q R a b s *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b s *ᵥ e)) =
      (endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endJet R a b *ᵥ e)) +
        2 * s * ((endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endContact Q R a b *ᵥ e))) +
        s ^ 2 * ((endContact Q R a b *ᵥ e) ⬝ᵥ
          (greenPositive (R + a) *ᵥ (endContact Q R a b *ᵥ e))) := by
    intro s
    have hmul : pencilCoupling Q R a b s *ᵥ e =
        -(endJet R a b *ᵥ e) - s • (endContact Q R a b *ᵥ e) := by
      rw [pencilCoupling, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec]
    rw [hmul]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_smul, sub_dotProduct,
      neg_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_neg, dotProduct_smul,
      smul_eq_mul, neg_neg]
    rw [dotProduct_mulVec_symm hsymm (endContact Q R a b *ᵥ e) (endJet R a b *ᵥ e)]
    ring
  rw [expand t, expand (-t)]
  ring

theorem windowMatrix_submatrix_overlapEquiv {K : ℕ → ℕ → ℝ} (hK : ∀ x y, K x y = K y x)
    (R a b : ℕ) :
    (windowMatrix K R (a + (R + a) + b)).submatrix (overlapEquiv a (R + a) b)
        (overlapEquiv a (R + a) b) =
      fromBlocks (windowMatrix K (R + a) (R + a))
        (joinColumns (posMatrix K (middlePos R a) (leftPos R a))
          (posMatrix K (middlePos R a) (rightPos R a b)))
        (joinColumns (posMatrix K (middlePos R a) (leftPos R a))
          (posMatrix K (middlePos R a) (rightPos R a b)))ᵀ
        (fromBlocks (posMatrix K (leftPos R a) (leftPos R a))
          (posMatrix K (leftPos R a) (rightPos R a b))
          (posMatrix K (leftPos R a) (rightPos R a b))ᵀ
          (posMatrix K (rightPos R a b) (rightPos R a b))) := by
  have hpos : ∀ x, R + (overlapEquiv a (R + a) b x : ℕ) =
      Sum.elim (middlePos R a) (Sum.elim (leftPos R a) (rightPos R a b)) x := by
    rintro (m | i | j) <;> simp [overlapEquiv, middlePos, leftPos, rightPos] <;> omega
  have hW : (windowMatrix K R (a + (R + a) + b)).submatrix (overlapEquiv a (R + a) b)
      (overlapEquiv a (R + a) b) =
      posMatrix K
        (Sum.elim (middlePos R a) (Sum.elim (leftPos R a) (rightPos R a b)))
        (Sum.elim (middlePos R a) (Sum.elim (leftPos R a) (rightPos R a b))) := by
    ext x y
    simp only [Matrix.submatrix_apply, windowMatrix, Matrix.of_apply, posMatrix, hpos]
  have hmid : posMatrix K (middlePos R a) (middlePos R a) = windowMatrix K (R + a) (R + a) := by
    ext m₁ m₂; rfl
  rw [hW, posMatrix_sumElim hK, posMatrix_sumElim_right, posMatrix_sumElim hK,
    posMatrix_transpose hK, hmid]

/-- Up to ratio `3`, reweighting the prime contacts by `ω` leaves the middle and end blocks
unchanged and replaces `endCoupling` by `pencilCoupling Q R a b (ω 2)`. -/
theorem reweightedWindow_submatrix_overlapEquiv_of_le_three_mul {Q R a b : ℕ} (hR : 1 ≤ R)
    (hQ : 2 ≤ Q) (h3 : 2 * (R + a) + b ≤ 3 * R) (ω : ℕ → ℝ) :
    (windowMatrix (reweightedNeutral ω Q) R (a + (R + a) + b)).submatrix
        (overlapEquiv a (R + a) b) (overlapEquiv a (R + a) b) =
      fromBlocks (primeFreeMiddle (R + a)) (pencilCoupling Q R a b (ω 2))
        (pencilCoupling Q R a b (ω 2))ᵀ (endForm Q R a b) := by
  rw [windowMatrix_submatrix_overlapEquiv (reweightedNeutral_comm ω Q) R a b]
  have hmid : windowMatrix (reweightedNeutral ω Q) (R + a) (R + a) = primeFreeMiddle (R + a) := by
    ext m₁ m₂
    simp only [windowMatrix, primeFreeMiddle, neutralWindow, Matrix.of_apply]
    have hlt : max (R + a + (m₁ : ℕ)) (R + a + (m₂ : ℕ)) <
        2 * min (R + a + (m₁ : ℕ)) (R + a + (m₂ : ℕ)) := by
      have := m₁.2; have := m₂.2; omega
    rcases le_total (R + a + (m₁ : ℕ)) (R + a + (m₂ : ℕ)) with hle | hge
    · rw [reweightedNeutral_eq_neutralBlock ω Q hle
        (by rwa [max_eq_right hle, min_eq_left hle] at hlt),
        neutralBlock_eq_of_lt_two_mul hlt, neutralBlock_eq_of_lt_two_mul hlt]
    · rw [reweightedNeutral_comm, reweightedNeutral_eq_neutralBlock ω Q hge
        (by rwa [max_eq_left hge, min_eq_right hge] at hlt),
        neutralBlock_comm, neutralBlock_eq_of_lt_two_mul hlt, neutralBlock_eq_of_lt_two_mul hlt]
  have hcoupl : joinColumns (posMatrix (reweightedNeutral ω Q) (middlePos R a) (leftPos R a))
      (posMatrix (reweightedNeutral ω Q) (middlePos R a) (rightPos R a b)) =
      pencilCoupling Q R a b (ω 2) := by
    ext m p
    have hne := middlePos_ne_endPos R a b m p
    set x := middlePos R a m
    set y := Sum.elim (leftPos R a) (rightPos R a b) p
    have hxy3 : max x y < 3 * min x y := by
      rcases p with i | j <;> simp only [x, y, middlePos, leftPos, rightPos, Sum.elim_inl,
        Sum.elim_inr]
      · have := m.2; have := i.2; omega
      · have := m.2; have := j.2; omega
    have hval : joinColumns (posMatrix (reweightedNeutral ω Q) (middlePos R a) (leftPos R a))
        (posMatrix (reweightedNeutral ω Q) (middlePos R a) (rightPos R a b)) m p =
        reweightedNeutral ω Q x y := by rcases p with i | j <;> rfl
    rw [hval, pencilCoupling, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      endJet_apply, endContact_apply]
    change reweightedNeutral ω Q x y = -blockJet (min x y) (max x y) - ω 2 * floorContact Q (min x y) (max x y)
    have hrew : reweightedNeutral ω Q x y = reweightedNeutral ω Q (min x y) (max x y) := by
      rcases le_total x y with hle | hge
      · rw [min_eq_left hle, max_eq_right hle]
      · rw [min_eq_right hge, max_eq_left hge, reweightedNeutral_comm]
    rw [hrew, reweightedNeutral_of_lt ω Q (min_lt_max.mpr hne),
      floorContact_eq_sum_floorGraph Q min_le_max]
    have hsplit : Icc 2 Q = insert 2 (Icc 3 Q) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h3' : max (min x y) (max x y) < 3 * min (min x y) (max x y) := by
      rwa [max_eq_right min_le_max, min_eq_left min_le_max]
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_eq_zero (fun k hk => by
        rw [floorGraph_eq_zero_of_lt_three_mul (Finset.mem_Icc.mp hk).1 h3', mul_zero]),
      Finset.sum_eq_zero (fun k hk =>
        floorGraph_eq_zero_of_lt_three_mul (Finset.mem_Icc.mp hk).1 h3'),
      add_zero, add_zero]
  have hends : fromBlocks (posMatrix (reweightedNeutral ω Q) (leftPos R a) (leftPos R a))
      (posMatrix (reweightedNeutral ω Q) (leftPos R a) (rightPos R a b))
      (posMatrix (reweightedNeutral ω Q) (leftPos R a) (rightPos R a b))ᵀ
      (posMatrix (reweightedNeutral ω Q) (rightPos R a b) (rightPos R a b)) = endForm Q R a b := by
    have hblk : ∀ p₁ p₂ : Fin a ⊕ Fin b,
        reweightedNeutral ω Q (Sum.elim (leftPos R a) (rightPos R a b) p₁)
          (Sum.elim (leftPos R a) (rightPos R a b) p₂) =
        neutralBlock Q (Sum.elim (leftPos R a) (rightPos R a b) p₁)
          (Sum.elim (leftPos R a) (rightPos R a b) p₂) := by
      intro p₁ p₂
      rw [reweightedNeutral, Finset.sum_eq_zero (fun k hk => by
        rw [floorGraph_endPos_eq_zero_of_le_three_mul hR h3 (Finset.mem_Icc.mp hk).1 p₁ p₂,
          mul_zero]), add_zero]
    ext p₁ p₂
    rcases p₁ with i₁ | j₁ <;> rcases p₂ with i₂ | j₂
    · exact hblk (Sum.inl i₁) (Sum.inl i₂)
    · exact hblk (Sum.inl i₁) (Sum.inr j₂)
    · simpa only [endForm, fromBlocks_apply₂₁, Matrix.transpose_apply, posMatrix, Matrix.of_apply]
        using hblk (Sum.inl i₂) (Sum.inr j₁)
    · exact hblk (Sum.inr j₁) (Sum.inr j₂)
  rw [hmid, hcoupl, hends]

theorem exists_greenForm_gt_of_two_le_hermNegIndex {D : ℕ} (hD : 1 ≤ D) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (P : Matrix (Fin D) κ ℝ) {N : Matrix κ κ ℝ}
    (hN : ∀ x y, N x y = N y x)
    (h2 : 2 ≤ hermNegIndex ((fromBlocks (primeFreeMiddle D) P Pᵀ N).map (↑) :
      Matrix (Fin D ⊕ κ) (Fin D ⊕ κ) ℂ)) :
    ∃ e : κ → ℝ,
      e ⬝ᵥ (N *ᵥ e) + (groundVector D ⬝ᵥ (P *ᵥ e)) ^ 2 / bindingEnergy D <
        (P *ᵥ e) ⬝ᵥ (greenPositive D *ᵥ (P *ᵥ e)) := by
  have hM := oneBoundState_primeFreeMiddle hD
  have hH := hermNegIndex_fromBlocks_transpose hM.symm hM.isUnit P hN
  rw [hM.hermNegIndex_eq_one] at hH
  have hpos : hermNegIndex ((N - Pᵀ * (primeFreeMiddle D)⁻¹ * P).map (↑) : Matrix κ κ ℂ) ≠ 0 := by
    omega
  have hnot := mt hermNegIndex_eq_zero_iff_forall.mpr hpos
  push_neg at hnot
  obtain ⟨e, he⟩ := hnot
  refine ⟨e, ?_⟩
  rw [schur_form_eq_channels hM P N e] at he
  change _ < (P *ᵥ e) ⬝ᵥ (greenPositive D *ᵥ (P *ᵥ e))
  linarith

/-- **Failure of the Green inequality on `(R, 3R]` for every nonpositive contact weight
`t ∈ [−4, 0]`**, at every block size `R ≥ 1`. -/
theorem exists_pencil_greenForm_gt {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) {t : ℝ} (ht1 : -4 ≤ t) (ht2 : t ≤ 0) :
    ∃ e : Fin a ⊕ Fin b → ℝ,
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (pencilCoupling Q R a b t *ᵥ e)) ^ 2 / bindingEnergy (R + a) <
      (pencilCoupling Q R a b t *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b t *ᵥ e)) := by
  have hsymm : ∀ x y, endForm Q R a b x y = endForm Q R a b y x :=
    fromBlocks_symm (posMatrix_symm (neutralBlock_symm Q) (leftPos R a)) _
      (posMatrix_symm (neutralBlock_symm Q) (rightPos R a b))
  have hidx := two_le_hermNegIndex_reweighted_of_ratio_three hR hQ (by omega)
    (fun _ => t) ht1 ht2
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b),
    reweightedWindow_submatrix_overlapEquiv_of_le_three_mul hR hQ (by omega) (fun _ => t)] at hidx
  exact exists_greenForm_gt_of_two_le_hermNegIndex (by omega) _ hsymm hidx

/-- **Prime-free failure (`t = 0`) on `(R, 3R]` at every block size `R ≥ 1`**: without the prime-`2`
sliver contact, the archimedean jet alone violates the Green inequality. -/
theorem exists_primeFree_greenForm_gt {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) :
    ∃ e : Fin a ⊕ Fin b → ℝ,
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endJet R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) <
      (endJet R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endJet R a b *ᵥ e)) := by
  obtain ⟨e, he⟩ := exists_pencil_greenForm_gt (Q := Q) hR hQ h3 (t := 0) (by norm_num)
    (by norm_num)
  refine ⟨e, ?_⟩
  have hmul : pencilCoupling Q R a b 0 *ᵥ e = -(endJet R a b *ᵥ e) := by
    rw [pencilCoupling, zero_smul, sub_zero, Matrix.neg_mulVec]
  rw [hmul, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, dotProduct_neg, neg_sq]
    at he
  exact he

/-- **Sign-twin failure (`t = −1`) on `(R, 3R]` at every block size `R ≥ 1`**: flipping the sign of
`endContact` (matching the Liouville twist on `(R, 3R]`) violates the Green inequality, even though
every entry of `endContact` retains the exact same magnitude on the boundary slivers. -/
theorem exists_signTwin_greenForm_gt {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R) :
    ∃ e : Fin a ⊕ Fin b → ℝ,
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (pencilCoupling Q R a b (-1) *ᵥ e)) ^ 2 / bindingEnergy (R + a) <
      (pencilCoupling Q R a b (-1) *ᵥ e) ⬝ᵥ
        (greenPositive (R + a) *ᵥ (pencilCoupling Q R a b (-1) *ᵥ e)) :=
  exists_pencil_greenForm_gt hR hQ h3 (by norm_num) (by norm_num)

/-- **Sign-twin obstruction to pure sliver-norm bounds**: no functional `F(P, e)` majorizing the
net Green quadratic form `(P e)ᵀ G_D (P e)` and invariant under `endContact ↦ −endContact` can lie
below `eᵀ N_e e` on `(R, 3R]` at any block size `R ≥ 1`. -/
theorem signTwin_obstruction {Q R a b : ℕ} (hR : 1 ≤ R) (hQ : 2 ≤ Q)
    (h3 : a + (R + a) + b = 2 * R)
    (F : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ → (Fin a ⊕ Fin b → ℝ) → ℝ)
    (hmaj : ∀ (P : Matrix (Fin (R + a)) (Fin a ⊕ Fin b) ℝ) (e : Fin a ⊕ Fin b → ℝ),
      (P *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (P *ᵥ e)) -
        (groundVector (R + a) ⬝ᵥ (P *ᵥ e)) ^ 2 / bindingEnergy (R + a) ≤ F P e)
    (hsym : ∀ e : Fin a ⊕ Fin b → ℝ,
      F (pencilCoupling Q R a b 1) e = F (pencilCoupling Q R a b (-1)) e) :
    ∃ e : Fin a ⊕ Fin b → ℝ, e ⬝ᵥ (endForm Q R a b *ᵥ e) < F (endCoupling Q R a b) e := by
  obtain ⟨e, he⟩ := exists_signTwin_greenForm_gt (Q := Q) hR hQ h3
  refine ⟨e, ?_⟩
  rw [← pencilCoupling_one, hsym e]
  linarith [hmaj (pencilCoupling Q R a b (-1)) e]

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
