import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Complete positive covariance under bounded source weights

Weight the original coefficient space before synthesis. Square-root weighting gives the
exact full covariance, its trace is the weighted column energy, and bounded pointwise
vanishing of the weights gives strong convergence even when traces do not vanish.
-/

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty
open HTGeometry RHTower
noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev CoefficientSpace (ι : Type*) := lp (fun _ : ι => ℂ) 2

def realSourceDiagonal (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  lpDiagonalCLM (fun i => (a i : ℂ)) zero_le_one fun i => by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i).1] using (ha i).2

@[simp] theorem realSourceDiagonal_apply (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (x : CoefficientSpace ι) (i : ι) :
    realSourceDiagonal a ha x i = (a i : ℂ) * x i := rfl

theorem adjoint_realSourceDiagonal (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    (realSourceDiagonal a ha).adjoint = realSourceDiagonal a ha := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [realSourceDiagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem sqrt_sourceWeight_mem_unitInterval (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (i : ι) :
    0 ≤ Real.sqrt (a i) ∧ Real.sqrt (a i) ≤ 1 :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (ha i).2⟩

def weightedSourceSynthesis (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) : CoefficientSpace ι →L[ℂ] H :=
  S ∘L realSourceDiagonal (fun i => Real.sqrt (a i)) (sqrt_sourceWeight_mem_unitInterval a ha)

def weightedSourceCovariance (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) : H →L[ℂ] H :=
  rangeCovariance (weightedSourceSynthesis S a ha)

theorem weightedSourceCovariance_eq (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    weightedSourceCovariance S a ha = S ∘L realSourceDiagonal a ha ∘L S.adjoint := by
  have hsquare :
      realSourceDiagonal (fun i => Real.sqrt (a i)) (sqrt_sourceWeight_mem_unitInterval a ha) ∘L
        realSourceDiagonal (fun i => Real.sqrt (a i)) (sqrt_sourceWeight_mem_unitInterval a ha) =
      realSourceDiagonal a ha := by
    ext x i
    simp only [comp_apply, realSourceDiagonal_apply, ← mul_assoc, ← Complex.ofReal_mul]
    rw [← pow_two, Real.sq_sqrt (ha i).1]
  unfold weightedSourceCovariance rangeCovariance weightedSourceSynthesis
  rw [adjoint_comp, adjoint_realSourceDiagonal]
  simpa only [comp_assoc] using congrArg (fun D => S ∘L D ∘L S.adjoint) hsquare

theorem weightedSourceCovariance_isPositive (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    (weightedSourceCovariance S a ha).IsPositive := rangeCovariance_isPositive _

/-- Every physical matrix entry retains the original synthesis and its adjoint. -/
theorem inner_weightedSourceCovariance (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (x y : H) :
    ⟪x, weightedSourceCovariance S a ha y⟫_ℂ =
      ∑' i, (a i : ℂ) * star (S.adjoint x i) * S.adjoint y i := by
  rw [weightedSourceCovariance_eq]
  simp only [comp_apply]
  rw [← adjoint_inner_left, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [realSourceDiagonal_apply, RCLike.inner_apply, starRingEnd_apply]
  ring

omit [CompleteSpace H] in
theorem weightedSourceSynthesis_basis (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (i : ι) :
    weightedSourceSynthesis S a ha (HilbertSchmidt.lpBasis ι i) =
      (Real.sqrt (a i) : ℂ) • S (HilbertSchmidt.lpBasis ι i) := by
  classical
  have hsingle : realSourceDiagonal (fun i => Real.sqrt (a i))
        (sqrt_sourceWeight_mem_unitInterval a ha) (lp.single 2 i (1 : ℂ)) =
      (Real.sqrt (a i) : ℂ) • lp.single 2 i (1 : ℂ) := by
    rw [realSourceDiagonal, lpDiagonalCLM_single, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [HilbertSchmidt.lpBasis_apply, weightedSourceSynthesis, comp_apply, hsingle, map_smul]

omit [CompleteSpace H] in
theorem norm_sq_weightedSourceSynthesis_basis (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (i : ι) :
    ‖weightedSourceSynthesis S a ha (HilbertSchmidt.lpBasis ι i)‖ ^ 2 =
      a i * ‖S (HilbertSchmidt.lpBasis ι i)‖ ^ 2 := by
  rw [weightedSourceSynthesis_basis, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (ha i).1]

theorem weightedSourceSynthesis_isHilbertSchmidt (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (henergy : Summable (fun i => a i * ‖S (HilbertSchmidt.lpBasis ι i)‖ ^ 2)) :
    (weightedSourceSynthesis S a ha).IsHilbertSchmidt :=
  isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis ι)
    (henergy.congr fun i => (norm_sq_weightedSourceSynthesis_basis S a ha i).symm)

theorem weightedSourceCovariance_memSchattenClass_one (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (henergy : Summable (fun i => a i * ‖S (HilbertSchmidt.lpBasis ι i)‖ ^ 2)) :
    RHTower.MemSchattenClass 1 (weightedSourceCovariance S a ha) := by
  have hS := weightedSourceSynthesis_isHilbertSchmidt S a ha henergy
  rw [weightedSourceCovariance, rangeCovariance,
    ← memRectSchattenClass_iff_memSchattenClass]
  exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hS.adjoint hS

theorem re_opTrace_weightedSourceCovariance (S : CoefficientSpace ι →L[ℂ] H)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (henergy : Summable (fun i => a i * ‖S (HilbertSchmidt.lpBasis ι i)‖ ^ 2)) :
    (opTrace (weightedSourceCovariance S a ha)).re =
      ∑' i, a i * ‖S (HilbertSchmidt.lpBasis ι i)‖ ^ 2 := by
  have hS := weightedSourceSynthesis_isHilbertSchmidt S a ha henergy
  calc
    _ = hsNormSq (weightedSourceSynthesis S a ha).adjoint := by
      simpa only [weightedSourceCovariance, rangeCovariance, adjoint_adjoint,
        RCLike.re_to_complex] using
        re_opTrace_adjoint_comp_self hS.adjoint
    _ = hsNormSq (weightedSourceSynthesis S a ha) := hS.hsNormSq_adjoint
    _ = _ := by
      rw [hsNormSq_eq hS (HilbertSchmidt.lpBasis ι)]
      exact tsum_congr (norm_sq_weightedSourceSynthesis_basis S a ha)

/-- Weight differences are differences of full covariances, with all cross entries retained. -/
theorem weightedSourceCovariance_sub (S : CoefficientSpace ι →L[ℂ] H)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, 0 ≤ a i - b i ∧ a i - b i ≤ 1) :
    weightedSourceCovariance S (fun i => a i - b i) hab =
      weightedSourceCovariance S a ha - weightedSourceCovariance S b hb := by
  have hd : realSourceDiagonal (fun i => a i - b i) hab =
      realSourceDiagonal a ha - realSourceDiagonal b hb := by
    ext x i
    simp only [realSourceDiagonal_apply, sub_apply, lp.coeFn_sub, Pi.sub_apply,
      Complex.ofReal_sub, sub_mul]
  simp only [weightedSourceCovariance_eq, hd, comp_sub, sub_comp]

/-- Bounded pointwise source weights vanish strongly, without a summable column-energy premise. -/
theorem tendsto_realSourceDiagonal_zero {κ : Type*} {l : Filter κ}
    (a : κ → ι → ℝ) (ha : ∀ k i, 0 ≤ a k i ∧ a k i ≤ 1)
    (hpoint : ∀ i, Tendsto (fun k => a k i) l (𝓝 0)) (x : CoefficientSpace ι) :
    Tendsto (fun k => realSourceDiagonal (a k) (ha k) x) l (𝓝 0) := by
  let f : κ → ι → ℝ := fun k i => ‖(a k i : ℂ) * x i‖ ^ 2
  have hp (i : ι) : Tendsto (fun k => f k i) l (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp (hpoint i)
    simpa [f] using (h.mul_const (x i)).norm.pow 2
  have hb (k : κ) (i : ι) : ‖f k i‖ ≤ ‖x i‖ ^ 2 := by
    have hai : ‖(a k i : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha k i).1] using
        (ha k i).2
    have hmul := mul_le_mul_of_nonneg_right hai (norm_nonneg (x i))
    simpa only [f, Real.norm_eq_abs, abs_sq, norm_mul, one_mul] using
      pow_le_pow_left₀ (by positivity) hmul 2
  have hsum : Tendsto (fun k => ∑' i, f k i) l (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence (HilbertSchmidt.summable_coe_sq x)
      hp (Eventually.of_forall hb)
  have hs : Tendsto (fun k => ‖realSourceDiagonal (a k) (ha k) x‖ ^ 2) l (𝓝 0) := by
    simpa only [HilbertSchmidt.lp_norm_sq_eq, realSourceDiagonal_apply, f] using hsum
  have hn : Tendsto (fun k => ‖realSourceDiagonal (a k) (ha k) x‖) l (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

theorem tendsto_weightedSourceCovariance_zero {κ : Type*} {l : Filter κ}
    (S : CoefficientSpace ι →L[ℂ] H) (a : κ → ι → ℝ)
    (ha : ∀ k i, 0 ≤ a k i ∧ a k i ≤ 1)
    (hpoint : ∀ i, Tendsto (fun k => a k i) l (𝓝 0)) (x : H) :
    Tendsto (fun k => weightedSourceCovariance S (a k) (ha k) x) l (𝓝 0) := by
  have h := (S.continuous.tendsto 0).comp
    (tendsto_realSourceDiagonal_zero a ha hpoint (S.adjoint x))
  simpa only [weightedSourceCovariance_eq, comp_apply, map_zero, Function.comp_def] using h

end
end GaloisForLFunctions.BiScaleUncertainty
