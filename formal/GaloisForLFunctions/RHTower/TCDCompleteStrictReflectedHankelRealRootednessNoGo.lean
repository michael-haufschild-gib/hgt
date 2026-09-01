import GaloisForLFunctions.RHTower.TCDCompleteReflectedHankelRealRootednessNoGo
import GaloisForLFunctions.HTGeometry.ObservablePushforwardHankelStrict
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import GaloisForLFunctions.HTGeometry.GaussianRealMoments

/-!
# Complete strict reflected-Hankel positivity does not force real-rootedness

This module kills the strongest generic cofinal landing after the finite TCD gate:

`finite D1 positivity → all-rank strict reflected-Hankel positivity → real-rootedness → RH`.

The source
`F(z) = exp(z²/4) * (cosh z + cosh (2z))`
is entire and positive on the real line. At every real center, every finite Hankel matrix of the
exact even reflected jets is positive definite: Gaussian dressing replaces each of the five
reflected atoms by an infinite-support shifted-Gaussian square law. Nevertheless `F(iπ/3)=0`.

Thus no TCD proof may infer real-rootedness from complete strict reflected-Hankel positivity alone.
Any survivor needs independent theta-to-Xi/source-to-divisor incidence information.
-/

open Real Polynomial Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

def gaussianShiftSquareMoment (a : ℝ) (n : ℕ) : ℝ :=
  ∫ y, (y ^ 2) ^ n ∂(gaussianReal a 1)

private theorem gaussianReal_moment_eq_shiftKernel (a : ℝ) (n : ℕ) :
    ∫ y, y ^ n ∂(gaussianReal a 1) =
      iteratedDeriv n (fun t : ℝ => Real.exp (a * t + t ^ 2 / 2)) 0 := by
  have hset : integrableExpSet (fun y : ℝ => y) (gaussianReal a 1) = Set.univ := by
    ext t
    simp [integrableExpSet, integrable_exp_mul_gaussianReal t]
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun y : ℝ => y) (gaussianReal a 1)) := by
    rw [hset]
    simp
  have hmgf := iteratedDeriv_mgf_zero
    (X := fun y : ℝ => y) (μ := gaussianReal a 1) h0 n
  rw [mgf_fun_id_gaussianReal] at hmgf
  simpa using hmgf.symm

private theorem gaussianReal_evenMoment_neg_mean (a : ℝ) (n : ℕ) :
    ∫ y, y ^ (2 * n) ∂(gaussianReal (-a) 1) =
      ∫ y, y ^ (2 * n) ∂(gaussianReal a 1) := by
  rw [← gaussianReal_map_neg (μ := a) (v := 1)]
  rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
  simp

theorem gaussianShiftSquareMoment_eq_evenJet (a : ℝ) (n : ℕ) :
    gaussianShiftSquareMoment a n =
      iteratedDeriv (2 * n)
        (fun t : ℝ => Real.exp (t ^ 2 / 2) * Real.cosh (a * t)) 0 := by
  have hpow : (fun y : ℝ => (y ^ 2) ^ n) = fun y : ℝ => y ^ (2 * n) := by
    funext y
    rw [← pow_mul]
  rw [gaussianShiftSquareMoment, hpow,
    gaussianReal_moment_eq_shiftKernel a (2 * n)]
  have hfun :
      (fun t : ℝ => Real.exp (t ^ 2 / 2) * Real.cosh (a * t)) =
        fun t : ℝ =>
          (Real.exp (a * t + t ^ 2 / 2) + Real.exp ((-a) * t + t ^ 2 / 2)) / 2 := by
    funext t
    rw [Real.cosh_eq]
    calc
      Real.exp (t ^ 2 / 2) *
          ((Real.exp (a * t) + Real.exp (-(a * t))) / 2) =
        (Real.exp (t ^ 2 / 2) * Real.exp (a * t) +
          Real.exp (t ^ 2 / 2) * Real.exp (-(a * t))) / 2 := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        apply congrArg₂ (· + ·)
        · apply congrArg Real.exp
          ring
        · apply congrArg Real.exp
          ring
  rw [hfun, iteratedDeriv_div_const]
  rw [show (fun t : ℝ => Real.exp (a * t + t ^ 2 / 2) +
      Real.exp ((-a) * t + t ^ 2 / 2)) =
      (fun t : ℝ => Real.exp (a * t + t ^ 2 / 2)) +
        (fun t : ℝ => Real.exp ((-a) * t + t ^ 2 / 2)) by rfl]
  rw [iteratedDeriv_add (by fun_prop) (by fun_prop)]
  rw [← gaussianReal_moment_eq_shiftKernel a (2 * n),
    ← gaussianReal_moment_eq_shiftKernel (-a) (2 * n),
    gaussianReal_evenMoment_neg_mean]
  ring

private theorem gaussianReal_one_open_pos (a : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (hUne : U.Nonempty) :
    0 < gaussianReal a 1 U := by
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => y + a) = gaussianReal a 1 := by
    simpa using gaussianReal_map_add_const (μ := (0 : ℝ)) (v := 1) a
  rw [← hmap, Measure.map_apply (by fun_prop) hU.measurableSet]
  have hVopen : IsOpen ((fun y : ℝ => y + a) ⁻¹' U) := hU.preimage (by fun_prop)
  have hVne : ((fun y : ℝ => y + a) ⁻¹' U).Nonempty := by
    obtain ⟨u, hu⟩ := hUne
    exact ⟨u - a, by simpa using hu⟩
  obtain ⟨y, hy⟩ := hVne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hVopen y hy
  have hIcc : Set.Icc (y - r / 2) (y + r / 2) ⊆ Metric.ball y r := by
    rw [Real.ball_eq_Ioo]
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  exact (GaloisForLFunctions.HTGeometry.gaussianReal_Icc_pos (by linarith : y - r / 2 < y + r / 2)).trans_le
    (measure_mono (hIcc.trans hball))

private theorem square_compl_finset_open_nonempty (F : Finset ℝ) :
    IsOpen {y : ℝ | y ^ 2 ∉ F} ∧ Set.Nonempty {y : ℝ | y ^ 2 ∉ F} := by
  constructor
  · exact F.isClosed.preimage (by fun_prop) |>.isOpen_compl
  · let M : ℝ := ∑ c ∈ F, |c|
    refine ⟨M + 1, ?_⟩
    intro hmem
    have hMnonneg : 0 ≤ M := by
      dsimp [M]
      positivity
    have hc_le : ∀ c ∈ F, c ≤ M := by
      intro c hc
      have habs : |c| ≤ M := by
        dsimp [M]
        exact Finset.single_le_sum (fun d _ => abs_nonneg d) hc
      exact le_trans (le_abs_self c) habs
    have hle := hc_le ((M + 1) ^ 2) hmem
    nlinarith

private theorem gaussianShiftSquare_infiniteSupport (a : ℝ) (F : Finset ℝ) :
    0 < gaussianReal a 1 {y : ℝ | y ^ 2 ∉ F} := by
  exact gaussianReal_one_open_pos a
    (square_compl_finset_open_nonempty F).1
    (square_compl_finset_open_nonempty F).2

private theorem gaussianShiftSquare_integrable (a : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => (y ^ 2) ^ n) (gaussianReal a 1) := by
  have hset : integrableExpSet (fun y : ℝ => y) (gaussianReal a 1) = Set.univ := by
    ext t
    simp [integrableExpSet, integrable_exp_mul_gaussianReal t]
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun y : ℝ => y) (gaussianReal a 1)) := by
    rw [hset]
    simp
  have h := integrable_pow_of_mem_interior_integrableExpSet h0 (2 * n)
  simpa [← pow_mul] using h

theorem gaussianShiftSquareMoment_posDef (a : ℝ) (n : ℕ) :
    (HTGeometry.momentHankelMatrix (gaussianShiftSquareMoment a) n).PosDef := by
  let nu : Measure ℝ := HTGeometry.observablePushforwardMeasure
    (gaussianReal a 1) (fun y : ℝ => y ^ 2)
  apply HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (μ := nu) (gaussianShiftSquareMoment a)
  · intro k
    rw [gaussianShiftSquareMoment, show nu = HTGeometry.observablePushforwardMeasure
      (gaussianReal a 1) (fun y : ℝ => y ^ 2) by rfl]
    exact (HTGeometry.integral_pow_observablePushforwardMeasure
      (gaussianReal a 1) (by fun_prop) k).symm
  · intro k
    exact HTGeometry.integrable_pow_observablePushforwardMeasure
      (gaussianReal a 1) (by fun_prop) (gaussianShiftSquare_integrable a k)
  · intro F
    exact HTGeometry.observablePushforwardMeasure_infiniteSupport
      (gaussianReal a 1) (by fun_prop) (gaussianShiftSquare_infiniteSupport a) F

def gaussianDressedTwoCoshRealSource (x : ℝ) : ℝ :=
  Real.exp (x ^ 2 / 4) * twoCoshRealSource x

def gaussianDressedTwoCoshEntireSource (z : ℂ) : ℂ :=
  Complex.exp (z ^ 2 / 4) * twoCoshEntireSource z

def gaussianDressedTwoCoshReflectedProfile (x t : ℝ) : ℝ :=
  Real.exp (x ^ 2 / 2) *
    ∑ i : Fin 5, twoCoshReflectedWeight x i *
      (Real.exp (t ^ 2 / 2) * Real.cosh (twoCoshReflectedFrequency i * t))

def gaussianDressedTwoCoshReflectedMoment (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (x ^ 2 / 2) *
    ∑ i : Fin 5, twoCoshReflectedWeight x i *
      gaussianShiftSquareMoment (twoCoshReflectedFrequency i) n

theorem gaussianDressedTwoCoshReflected_product_identity (x t : ℝ) :
    gaussianDressedTwoCoshRealSource (x + t) *
        gaussianDressedTwoCoshRealSource (x - t) =
      gaussianDressedTwoCoshReflectedProfile x t := by
  unfold gaussianDressedTwoCoshRealSource gaussianDressedTwoCoshReflectedProfile
  rw [show Real.exp ((x + t) ^ 2 / 4) * twoCoshRealSource (x + t) *
      (Real.exp ((x - t) ^ 2 / 4) * twoCoshRealSource (x - t)) =
      (Real.exp ((x + t) ^ 2 / 4) * Real.exp ((x - t) ^ 2 / 4)) *
        (twoCoshRealSource (x + t) * twoCoshRealSource (x - t)) by ring]
  rw [← Real.exp_add, twoCoshReflected_product_identity]
  rw [show (x + t) ^ 2 / 4 + (x - t) ^ 2 / 4 = x ^ 2 / 2 + t ^ 2 / 2 by ring,
    Real.exp_add]
  unfold twoCoshReflectedProfile
  rw [show (∑ i : Fin 5, twoCoshReflectedWeight x i *
      (Real.exp (t ^ 2 / 2) * Real.cosh (twoCoshReflectedFrequency i * t))) =
      Real.exp (t ^ 2 / 2) *
        ∑ i : Fin 5, twoCoshReflectedWeight x i *
          Real.cosh (twoCoshReflectedFrequency i * t) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  ring

theorem gaussianDressedTwoCoshReflectedMoment_eq_evenJet (x : ℝ) (n : ℕ) :
    gaussianDressedTwoCoshReflectedMoment x n =
      iteratedDeriv (2 * n)
        (fun t : ℝ => gaussianDressedTwoCoshRealSource (x + t) *
          gaussianDressedTwoCoshRealSource (x - t)) 0 := by
  have hfun :
      (fun t : ℝ => gaussianDressedTwoCoshRealSource (x + t) *
        gaussianDressedTwoCoshRealSource (x - t)) =
        gaussianDressedTwoCoshReflectedProfile x := by
    funext t
    exact gaussianDressedTwoCoshReflected_product_identity x t
  rw [hfun]
  unfold gaussianDressedTwoCoshReflectedProfile
  rw [iteratedDeriv_const_mul_field]
  have hsum :
      (fun t : ℝ => ∑ i : Fin 5, twoCoshReflectedWeight x i *
        (Real.exp (t ^ 2 / 2) * Real.cosh (twoCoshReflectedFrequency i * t))) =
      ∑ i : Fin 5, fun t : ℝ => twoCoshReflectedWeight x i *
        (Real.exp (t ^ 2 / 2) * Real.cosh (twoCoshReflectedFrequency i * t)) := by
    funext t
    simp
  rw [hsum, iteratedDeriv_sum]
  · unfold gaussianDressedTwoCoshReflectedMoment
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_const_mul_field,
      ← gaussianShiftSquareMoment_eq_evenJet]
  · intro i hi
    fun_prop

theorem gaussianDressedTwoCoshReflectedMoment_posDef (x : ℝ) (n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (gaussianDressedTwoCoshReflectedMoment x) n).PosDef := by
  let A : Fin 5 → Matrix (Fin n) (Fin n) ℝ := fun i =>
    twoCoshReflectedWeight x i •
      HTGeometry.momentHankelMatrix
        (gaussianShiftSquareMoment (twoCoshReflectedFrequency i)) n
  have hA : ∀ i, (A i).PosDef := by
    intro i
    exact (gaussianShiftSquareMoment_posDef (twoCoshReflectedFrequency i) n).smul
      (twoCoshReflectedWeight_pos x i)
  have hsum : (∑ i : Fin 5, A i).PosDef := by
    simpa [Fin.sum_univ_succ] using
      (hA 0).add ((hA 1).add ((hA 2).add ((hA 3).add (hA 4))))
  have hmatrix :
      HTGeometry.momentHankelMatrix
          (gaussianDressedTwoCoshReflectedMoment x) n =
        Real.exp (x ^ 2 / 2) • ∑ i : Fin 5, A i := by
    ext i j
    simp only [HTGeometry.momentHankelMatrix,
      gaussianDressedTwoCoshReflectedMoment, Matrix.smul_apply, smul_eq_mul]
    congr 1
  rw [hmatrix]
  exact hsum.smul (Real.exp_pos _)

theorem analyticAt_gaussianDressedTwoCoshEntireSource (z : ℂ) :
    AnalyticAt ℂ gaussianDressedTwoCoshEntireSource z := by
  unfold gaussianDressedTwoCoshEntireSource
  have hexp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w ^ 2 / 4)) z := by
    fun_prop
  exact hexp.mul (analyticAt_twoCoshEntireSource z)

theorem gaussianDressedTwoCoshEntireSource_ofReal (x : ℝ) :
    gaussianDressedTwoCoshEntireSource x = gaussianDressedTwoCoshRealSource x := by
  simp [gaussianDressedTwoCoshEntireSource, gaussianDressedTwoCoshRealSource,
    twoCoshEntireSource_ofReal]

theorem gaussianDressedTwoCoshRealSource_pos (x : ℝ) :
    0 < gaussianDressedTwoCoshRealSource x := by
  exact mul_pos (Real.exp_pos _) (twoCoshRealSource_pos x)

theorem gaussianDressedTwoCoshEntireSource_nonreal_zero :
    gaussianDressedTwoCoshEntireSource ((Real.pi / 3 : ℝ) * Complex.I) = 0 := by
  unfold gaussianDressedTwoCoshEntireSource
  rw [twoCoshEntireSource_nonreal_zero, mul_zero]

/-- Gaussian dressing makes every reflected Hankel block positive definite but preserves a
nonreal zero. Thus even complete strict reflected-Hankel positivity cannot supply the TCD
real-rootedness landing. -/
theorem completeStrictReflectedHankel_realRootedness_noGo :
    (∀ z, AnalyticAt ℂ gaussianDressedTwoCoshEntireSource z) ∧
    (∀ x : ℝ, gaussianDressedTwoCoshEntireSource x =
      gaussianDressedTwoCoshRealSource x) ∧
    (∀ x : ℝ, 0 < gaussianDressedTwoCoshRealSource x) ∧
    (∀ x : ℝ, ∀ n : ℕ,
      gaussianDressedTwoCoshReflectedMoment x n =
        iteratedDeriv (2 * n)
          (fun t : ℝ => gaussianDressedTwoCoshRealSource (x + t) *
            gaussianDressedTwoCoshRealSource (x - t)) 0) ∧
    (∀ x : ℝ, ∀ n : ℕ,
      (HTGeometry.momentHankelMatrix
        (gaussianDressedTwoCoshReflectedMoment x) n).PosDef) ∧
    ¬ (∀ z, gaussianDressedTwoCoshEntireSource z = 0 → z.im = 0) := by
  refine ⟨analyticAt_gaussianDressedTwoCoshEntireSource,
    gaussianDressedTwoCoshEntireSource_ofReal,
    gaussianDressedTwoCoshRealSource_pos,
    gaussianDressedTwoCoshReflectedMoment_eq_evenJet,
    gaussianDressedTwoCoshReflectedMoment_posDef, ?_⟩
  intro hall
  exact twoCoshEntireSource_nonreal_zero_im_ne_zero
    (hall _ gaussianDressedTwoCoshEntireSource_nonreal_zero)

end

end RHTower
