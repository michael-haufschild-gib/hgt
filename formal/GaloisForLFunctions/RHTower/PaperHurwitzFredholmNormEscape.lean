import GaloisForLFunctions.RHTower.PaperHurwitzFredholmEscape
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Exact Fredholm escape under native operator-norm convergence

A cubic source approach and a shrinking lattice coupling give trace-class
Hurwitz perturbations tending to zero in operator norm. Their actual Fredholm
determinants grow geometrically, with an exact hyperbolic prefactor tending to one.
-/

namespace RHTower
noncomputable section
open Filter GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open scoped Topology

/-- Polynomial form of `(N+3)^3-3`, avoiding truncated subtraction. -/
def paperHurwitzCubicIndex (N : ℕ) : ℕ := N ^ 3 + 9 * N ^ 2 + 27 * N + 24

def paperHurwitzSmallPerturbation (t : ℝ) (N : ℕ) :
    PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  ((Real.sinh (paperHurwitzApproachStep N) ^ 2 : ℝ) : ℂ) •
    paperHurwitzResolvent (paperHurwitzApproachPoint t (paperHurwitzCubicIndex N))

def paperHurwitzSmallFredholmValue (t : ℝ) (N : ℕ) : ℂ :=
  fredholmDetOp (lpBasis ℕ) (paperHurwitzSmallPerturbation t N)

private theorem cubic_step (N : ℕ) :
    paperHurwitzApproachStep (paperHurwitzCubicIndex N) = Real.log 2 / ((N : ℝ) + 3) ^ 3 := by
  unfold paperHurwitzApproachStep paperHurwitzCubicIndex
  push_cast
  congr 1
  ring

theorem paperHurwitzApproachStep_tendsto_zero :
    Tendsto paperHurwitzApproachStep atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => Real.log 2 / ((N : ℝ) + 3)) atTop (𝓝 0)
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
    (tendsto_const_nhds (x := (3 : ℝ)))
  have h := (tendsto_inv_atTop_zero.comp hn).const_mul (Real.log 2)
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using h

theorem paperHurwitzSmallPerturbation_traceClass (t : ℝ) (N : ℕ) :
    MemSchattenClass 1 (paperHurwitzSmallPerturbation t N) :=
  memSchattenClass_one_smul
    (paperHurwitzApproach_resolvent_traceClass t (paperHurwitzCubicIndex N)) _

theorem norm_paperHurwitzSmallPerturbation (t : ℝ) (N : ℕ) :
    ‖paperHurwitzSmallPerturbation t N‖ = Real.sinh (paperHurwitzApproachStep N) ^ 2 := by
  rw [paperHurwitzSmallPerturbation, norm_smul, norm_paperHurwitzResolvent, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem paperHurwitzSmallPerturbation_tendsto_zero (t : ℝ) :
    Tendsto (paperHurwitzSmallPerturbation t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := ((Real.continuous_sinh.tendsto 0).comp paperHurwitzApproachStep_tendsto_zero).pow 2
  simpa only [Function.comp_apply, norm_paperHurwitzSmallPerturbation,
    Real.sinh_zero, zero_pow (by omega : 2 ≠ 0)] using h

theorem paperHurwitzSmallFredholmValue_exact (t : ℝ) (N : ℕ) :
    paperHurwitzSmallFredholmValue t N =
      ((Real.cosh (paperHurwitzApproachStep N) * (2 : ℝ) ^ (N + 3) : ℝ) : ℂ) := by
  have h := paperHurwitzApproach_fredholmDet_lattice t (paperHurwitzCubicIndex N) ((N + 3) ^ 2)
  have hn : (N : ℝ) + 3 ≠ 0 := by positivity
  have ha : (((N + 3) ^ 2 : ℕ) : ℝ) * paperHurwitzApproachStep (paperHurwitzCubicIndex N) =
      paperHurwitzApproachStep N := by
    rw [cubic_step, paperHurwitzApproachStep]
    push_cast
    field_simp [hn]
  have hb : ((((N + 3) ^ 2 : ℕ) : ℝ) ^ 2) *
      paperHurwitzApproachStep (paperHurwitzCubicIndex N) = ((N + 3 : ℕ) : ℝ) * Real.log 2 := by
    rw [cubic_step]
    push_cast
    field_simp [hn]
  rw [ha, hb, Real.exp_nat_mul, Real.exp_log (by norm_num)] at h
  exact h

theorem norm_paperHurwitzSmallFredholmValue (t : ℝ) (N : ℕ) :
    ‖paperHurwitzSmallFredholmValue t N‖ =
      Real.cosh (paperHurwitzApproachStep N) * (2 : ℝ) ^ (N + 3) := by
  rw [paperHurwitzSmallFredholmValue_exact, Complex.norm_real, Real.norm_of_nonneg]
  positivity

theorem paperHurwitzSmallFredholmValue_tendsto_atTop (t : ℝ) :
    Tendsto (fun N => ‖paperHurwitzSmallFredholmValue t N‖) atTop atTop := by
  apply tendsto_atTop_mono (f := fun N : ℕ => (2 : ℝ) ^ N)
    (fun N => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  rw [norm_paperHurwitzSmallFredholmValue, pow_add]
  have hc := Real.one_le_cosh (paperHurwitzApproachStep N)
  have hp : (0 : ℝ) ≤ 2 ^ N := by positivity
  nlinarith

theorem paperHurwitzSmallFredholmValue_normalized_tendsto (t : ℝ) :
    Tendsto (fun N => ‖paperHurwitzSmallFredholmValue t N‖ / (2 : ℝ) ^ (N + 3))
      atTop (𝓝 1) := by
  have h := (Real.continuous_cosh.tendsto 0).comp paperHurwitzApproachStep_tendsto_zero
  rw [Real.cosh_zero] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  change Real.cosh (paperHurwitzApproachStep N) =
    ‖paperHurwitzSmallFredholmValue t N‖ / (2 : ℝ) ^ (N + 3)
  rw [norm_paperHurwitzSmallFredholmValue, mul_div_cancel_right₀ _ (by positivity)]

theorem paperHurwitzFredholm_zero :
    fredholmDetOp (lpBasis ℕ) (0 : PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory) = 1 := by
  simpa using paperHurwitzApproach_fredholmDet_lattice 0 0 0

theorem paperHurwitzFredholm_norm_zero_escape (t : ℝ) :
    (∀ N, MemSchattenClass 1 (paperHurwitzSmallPerturbation t N)) ∧
    Tendsto (paperHurwitzSmallPerturbation t) atTop (𝓝 0) ∧
    Tendsto (fun N => ‖paperHurwitzSmallFredholmValue t N‖) atTop atTop :=
  ⟨paperHurwitzSmallPerturbation_traceClass t, paperHurwitzSmallPerturbation_tendsto_zero t,
    paperHurwitzSmallFredholmValue_tendsto_atTop t⟩

end
end RHTower
