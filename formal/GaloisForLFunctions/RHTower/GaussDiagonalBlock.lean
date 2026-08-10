import GaloisForLFunctions.RHTower.GaussSampleTranslationL2
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The diagonal block of the quasi-inner decomposition

The sampled Gauss component `d_i` is a bounded family on the frequency lattice: the uniform energy
bound gives `gaussArchConst · ‖d_i‖^(2m) ≤ C`, and a number exceeding `max 1 (C/gaussArchConst)`
would already exceed that bound at the first power.  No root extraction is needed.

Transporting the diagonal multiplier through the Fourier coordinate isometry therefore produces
the block `D_(m,k,p)` on `L²(ℝ/ℤ)`, with the exponential monomials as eigenvectors and the sampled
Gauss component as eigenvalues.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-! ## The uniform bound on the symbol -/

/-- The sampled Gauss component is uniformly bounded on the frequency lattice. -/
theorem exists_norm_gaussSampleValue_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℤ, ‖gaussSampleValue k p i‖ ≤ M := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  have harch : 0 < gaussArchConst m := gaussArchConst_pos hm
  refine ⟨max 1 (C / gaussArchConst m), le_trans zero_le_one (le_max_left _ _), fun i => ?_⟩
  by_cases hi : i = 0
  · rw [hi, gaussSampleValue_zero, norm_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  by_contra hcon
  rw [not_le] at hcon
  have hone : (1 : ℝ) < ‖gaussSampleValue k p i‖ :=
    lt_of_le_of_lt (le_max_left _ _) hcon
  have hself : ‖gaussSampleValue k p i‖ ≤ ‖gaussSampleValue k p i‖ ^ (2 * m) :=
    le_self_pow₀ hone.le (by omega)
  have habs1 : 1 ≤ i.natAbs := by omega
  have habsR : (1 : ℝ) ≤ ((i.natAbs - 1 : ℕ) : ℝ) + 1 := by
    have : (0 : ℝ) ≤ ((i.natAbs - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have henergy : gaussArchConst m * ‖gaussSampleValue k p i‖ ^ (2 * m) ≤ C := by
    rw [norm_gaussSampleValue_pow_eq hm k p hi]
    refine le_trans (hb (i.natAbs - 1)).2 ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hC.le, habsR]
  have hpow : ‖gaussSampleValue k p i‖ ^ (2 * m) ≤ C / gaussArchConst m := by
    rw [le_div_iff₀ harch]
    nlinarith [henergy]
  have hle : C / gaussArchConst m ≤ max 1 (C / gaussArchConst m) := le_max_right _ _
  linarith

/-- The chosen uniform bound on the symbol. -/
def gaussSampleValueBound {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) : ℝ :=
  Classical.choose (exists_norm_gaussSampleValue_le hm k p)

theorem gaussSampleValueBound_nonneg {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    0 ≤ gaussSampleValueBound hm k p :=
  (Classical.choose_spec (exists_norm_gaussSampleValue_le hm k p)).1

theorem norm_gaussSampleValue_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    ‖gaussSampleValue k p i‖ ≤ gaussSampleValueBound hm k p :=
  (Classical.choose_spec (exists_norm_gaussSampleValue_le hm k p)).2 i

/-! ## The diagonal block -/

/-- The diagonal block `D_(m,k,p)`: the Fourier multiplier with symbol the sampled Gauss
component. -/
def gaussDiagonalBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  conjugateOperator (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv
    (GaloisForLFunctions.lpDiagonalCLM (fun i : ℤ => gaussSampleValue k p i)
      (gaussSampleValueBound_nonneg hm k p) (norm_gaussSampleValue_le hm k p))

/-- **The exponential monomials are eigenvectors of the diagonal block**, with the sampled Gauss
component as eigenvalues. -/
theorem gaussDiagonalBlock_fourierLp {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (j : ℤ) :
    gaussDiagonalBlock hm k p (fourierLp 2 j) = gaussSampleValue k p j • fourierLp 2 j := by
  have hbasis : (fourierLp 2 j : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
      = (fourierBasis (T := (1 : ℝ))) j := by
    rw [coe_fourierBasis]
  have hsingle : lp.single (E := fun _ : ℤ => ℂ) 2 j (gaussSampleValue k p j)
      = gaussSampleValue k p j • lp.single (E := fun _ : ℤ => ℂ) 2 j (1 : ℂ) := by
    rw [← lp.single_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hbasis, gaussDiagonalBlock, conjugateOperator]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [HilbertBasis.repr_self, GaloisForLFunctions.lpDiagonalCLM_single, hsingle, map_smul]
  congr 1
  simp

end

end RHTower
