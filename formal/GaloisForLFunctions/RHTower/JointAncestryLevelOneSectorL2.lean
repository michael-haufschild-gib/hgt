import GaloisForLFunctions.RHTower.JointAncestryLocalSquareNorm
import GaloisForLFunctions.RHTower.JointAncestrySectorNormBudget
import GaloisForLFunctions.HTGeometry.ComplexTorusProductLimit
import GaloisForLFunctions.HTGeometry.PositiveEulerProductBudget

/-! # Native signed level-one JAS sectors in L²

The local factors retain the full complex zero. Exact Parseval factors and a
finite positive Euler-product comparison bound every prime prefix by the
unconditionally summable strip-width budget.
-/

namespace RHTower

open MeasureTheory Filter GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology

noncomputable section

private theorem levelOneA_lt_one (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (1 / 2 : ℝ)) p‖ < 1 :=
  norm_jasHoloA_dressed_lt_one (by linarith [xiZeroCopy_re_pos q]) p

private theorem levelOneB_lt_one (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloB ((q.1 : ℂ) - (1 / 2 : ℝ)) p‖ < 1 :=
  norm_jasHoloB_dressed_lt_one (by linarith [xiZeroCopy_re_lt_one q]) p

def jasLevelOneCircle (q : XiZeroCopy) (p : Nat.Primes) : C(UnitAddCircle, ℂ) :=
  ⟨jasHoloCircle (jasHoloA ((q.1 : ℂ) + (1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (1 / 2 : ℝ)) p),
    continuous_jasHoloCircle (levelOneA_lt_one q p) (levelOneB_lt_one q p)⟩

theorem integral_jasLevelOneCircle (q : XiZeroCopy) (p : Nat.Primes) :
    ∫ θ, jasLevelOneCircle q p θ ∂AddCircle.haarAddCircle = 1 :=
  integral_jasHoloCircle (levelOneA_lt_one q p) (levelOneB_lt_one q p)

def jasLevelOnePrimeSquareRadius (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ) ^ (-(1 + 2 * jasZeroStripWidth q))

theorem jasLevelOnePrimeSquareRadius_nonneg (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ jasLevelOnePrimeSquareRadius q p :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem jasLevelOnePrimeSquareRadius_lt_one (q : XiZeroCopy) (p : Nat.Primes) :
    jasLevelOnePrimeSquareRadius q p < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast p.2.one_lt
  · linarith [jasZeroStripWidth_pos q]

theorem sq_norm_levelOneA_le_radius (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (1 / 2 : ℝ)) p‖ ^ 2 ≤ jasLevelOnePrimeSquareRadius q p := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [norm_jasHoloA, jasLevelOnePrimeSquareRadius, ← Real.exp_nat_mul,
    Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re, Complex.ofReal_re, Nat.cast_ofNat]
  nlinarith [mul_nonneg (sub_nonneg.mpr (jasZeroStripWidth_le_re q)) (log_prime_pos p).le]

theorem sq_norm_levelOneB_le_radius (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloB ((q.1 : ℂ) - (1 / 2 : ℝ)) p‖ ^ 2 ≤ jasLevelOnePrimeSquareRadius q p := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [norm_jasHoloB, jasLevelOnePrimeSquareRadius, ← Real.exp_nat_mul,
    Real.rpow_def_of_pos hp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.ofReal_re, Nat.cast_ofNat]
  nlinarith [mul_nonneg (sub_nonneg.mpr (jasZeroStripWidth_le_one_sub_re q))
    (log_prime_pos p).le]

theorem integral_sq_norm_jasLevelOneCircle_le (q : XiZeroCopy) (p : Nat.Primes) :
    ∫ θ, ‖jasLevelOneCircle q p θ‖ ^ 2 ∂AddCircle.haarAddCircle ≤
      ((1 - jasLevelOnePrimeSquareRadius q p)⁻¹) ^ 2 := by
  have hr := jasLevelOnePrimeSquareRadius_lt_one q p
  have hA := sq_norm_levelOneA_le_radius q p
  have hB := sq_norm_levelOneB_le_radius q p
  have hiA : (1 - ‖jasHoloA ((q.1 : ℂ) + (1 / 2 : ℝ)) p‖ ^ 2)⁻¹ ≤
      (1 - jasLevelOnePrimeSquareRadius q p)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hiB : (1 - ‖jasHoloB ((q.1 : ℂ) - (1 / 2 : ℝ)) p‖ ^ 2)⁻¹ ≤
      (1 - jasLevelOnePrimeSquareRadius q p)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  refine (integral_sq_norm_jasHoloCircle_le (levelOneA_lt_one q p)
    (levelOneB_lt_one q p)).trans ?_
  conv_rhs => rw [pow_two]
  apply mul_le_mul hiA hiB
  · exact inv_nonneg.mpr (by linarith)
  · exact inv_nonneg.mpr (by linarith)

theorem prod_jasLevelOnePrimeSquareRadius_inv_le (q : XiZeroCopy) (P : Finset Nat.Primes) :
    ∏ p ∈ P, (1 - jasLevelOnePrimeSquareRadius q p)⁻¹ ≤ jasSectorNormBudget q := by
  classical
  let S := P.image (fun p : Nat.Primes => (p : ℕ))
  have hS : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
    exact r.2
  have h := finite_prime_eulerProduct_le_one_add_inv
    (σ := 1 + 2 * jasZeroStripWidth q) (by linarith [jasZeroStripWidth_pos q]) S hS
  dsimp [S] at h
  rw [Finset.prod_image (by intro a _ b _ hab; exact Subtype.ext hab)] at h
  simpa only [jasLevelOnePrimeSquareRadius, jasSectorNormBudget, add_sub_cancel_left] using h

def jasLevelOneSectorLp (q : XiZeroCopy) (P : Finset Nat.Primes) :
    Lp ℂ 2 (torusHaar Nat.Primes) := torusFiniteProductLp (jasLevelOneCircle q) P

theorem norm_jasLevelOneSectorLp_le (q : XiZeroCopy) (P : Finset Nat.Primes) :
    ‖jasLevelOneSectorLp q P‖ ≤ jasSectorNormBudget q := by
  have hprod : ‖jasLevelOneSectorLp q P‖ ^ 2 ≤
      (∏ p ∈ P, (1 - jasLevelOnePrimeSquareRadius q p)⁻¹) ^ 2 := by
    rw [jasLevelOneSectorLp, norm_sq_torusFiniteProductLp, ← Finset.prod_pow]
    apply Finset.prod_le_prod
    · intro p _
      exact integral_nonneg fun θ => sq_nonneg _
    · intro p _
      exact integral_sq_norm_jasLevelOneCircle_le q p
  have hP := prod_jasLevelOnePrimeSquareRadius_inv_le q P
  have hP0 : 0 ≤ ∏ p ∈ P, (1 - jasLevelOnePrimeSquareRadius q p)⁻¹ := by
    apply Finset.prod_nonneg
    intro p _
    exact inv_nonneg.mpr (le_of_lt (sub_pos.mpr (jasLevelOnePrimeSquareRadius_lt_one q p)))
  nlinarith [norm_nonneg (jasLevelOneSectorLp q P), jasSectorNormBudget_pos q]

def jasPrimePrefix (N : ℕ) : Finset Nat.Primes := (Finset.range N).subtype Nat.Prime

theorem monotone_jasPrimePrefix : Monotone jasPrimePrefix := by
  intro n m hnm
  exact Finset.subtype_mono (Finset.range_mono hnm)

theorem mem_jasPrimePrefix (p : Nat.Primes) (N : ℕ) :
    p ∈ jasPrimePrefix N ↔ (p : ℕ) < N := by
  exact (Finset.mem_subtype (a := (p : {n : ℕ // Nat.Prime n}))).trans Finset.mem_range

theorem exists_jasLevelOneSectorLp_limit (q : XiZeroCopy) :
    ∃ g : Lp ℂ 2 (torusHaar Nat.Primes),
      Tendsto (fun N => jasLevelOneSectorLp q (jasPrimePrefix N)) atTop (𝓝 g) ∧
      ‖g‖ ≤ jasSectorNormBudget q := by
  obtain ⟨g, hg⟩ := exists_complexTorusProduct_limit (jasLevelOneCircle q)
    (integral_jasLevelOneCircle q) jasPrimePrefix monotone_jasPrimePrefix
    (B := jasSectorNormBudget q) (fun N => by
      rw [← norm_sq_torusFiniteProductLp]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_jasLevelOneSectorLp_le q _) 2)
  exact ⟨g, hg, le_of_tendsto hg.norm
    (Eventually.of_forall fun N => norm_jasLevelOneSectorLp_le q (jasPrimePrefix N))⟩

end

end RHTower
