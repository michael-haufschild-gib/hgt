import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The hyperbolic source range on an interval

The operator `L_κ ψ = -ψ'' + κ²ψ` acting on functions supported in `[-R,R]` has a one-codimensional
range: variation of parameters against the two hyperbolic solutions produces

`ψ(t) = -(sinh(κt)·A(t) - cosh(κt)·B(t))/κ`,  `A(t) = ∫_{-R}^t cosh(κs)φ(s) ds`,

which solves `L_κψ = φ` and vanishes to the left of the support automatically; it vanishes to the
right of the support exactly when both hyperbolic moments of `φ` vanish.  For an even source the
odd moment vanishes by parity, so a single scalar condition — the vanishing of
`∫ cosh(κs)φ(s) ds` — decides solvability inside the interval.

Consequently a linear functional annihilating the whole range is a multiple of the hyperbolic
pairing `φ ↦ ∫ cosh(κs)φ(s) ds`: this is the classification of even distributional solutions of
`L_κ w = 0` in the form actually used against a source.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The partial hyperbolic-cosine moment of a source. -/
def hyperbolicCosMoment (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (-R)..t, Real.cosh (κ * s) * φ s

/-- The partial hyperbolic-sine moment of a source. -/
def hyperbolicSinMoment (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (-R)..t, Real.sinh (κ * s) * φ s

/-- The particular solution of `-ψ'' + κ²ψ = φ` built from the hyperbolic Green kernel
`sinh(κ(t-s))/κ`. -/
def hyperbolicSolution (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(Real.sinh (κ * t) * hyperbolicCosMoment κ R φ t
      - Real.cosh (κ * t) * hyperbolicSinMoment κ R φ t) / κ

/-- The derivative of the particular solution. -/
def hyperbolicSolutionDeriv (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(Real.cosh (κ * t) * hyperbolicCosMoment κ R φ t
      - Real.sinh (κ * t) * hyperbolicSinMoment κ R φ t)

theorem continuous_cosh_mul {κ : ℝ} : Continuous fun s : ℝ => Real.cosh (κ * s) :=
  Real.continuous_cosh.comp (continuous_const.mul continuous_id)

theorem continuous_sinh_mul {κ : ℝ} : Continuous fun s : ℝ => Real.sinh (κ * s) :=
  Real.continuous_sinh.comp (continuous_const.mul continuous_id)

theorem hasDerivAt_const_mul_id (κ t : ℝ) : HasDerivAt (fun z : ℝ => κ * z) κ t := by
  simpa using (hasDerivAt_id t).const_mul κ

theorem hasDerivAt_cosh_mul (κ t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.cosh (κ * z)) (Real.sinh (κ * t) * κ) t :=
  (Real.hasDerivAt_cosh (κ * t)).comp t (hasDerivAt_const_mul_id κ t)

theorem hasDerivAt_sinh_mul (κ t : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sinh (κ * z)) (Real.cosh (κ * t) * κ) t :=
  (Real.hasDerivAt_sinh (κ * t)).comp t (hasDerivAt_const_mul_id κ t)

theorem hasDerivAt_hyperbolicCosMoment {κ R : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (t : ℝ) :
    HasDerivAt (hyperbolicCosMoment κ R φ) (Real.cosh (κ * t) * φ t) t :=
  ((continuous_cosh_mul.mul hφ).integral_hasStrictDerivAt (-R) t).hasDerivAt

theorem hasDerivAt_hyperbolicSinMoment {κ R : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (t : ℝ) :
    HasDerivAt (hyperbolicSinMoment κ R φ) (Real.sinh (κ * t) * φ t) t :=
  ((continuous_sinh_mul.mul hφ).integral_hasStrictDerivAt (-R) t).hasDerivAt

/-- The particular solution differentiates to `hyperbolicSolutionDeriv`. -/
theorem hasDerivAt_hyperbolicSolution {κ R : ℝ} (hκ : κ ≠ 0) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (t : ℝ) : HasDerivAt (hyperbolicSolution κ R φ) (hyperbolicSolutionDeriv κ R φ t) t := by
  have hA := hasDerivAt_hyperbolicCosMoment (κ := κ) (R := R) hφ t
  have hB := hasDerivAt_hyperbolicSinMoment (κ := κ) (R := R) hφ t
  have h := ((((hasDerivAt_sinh_mul κ t).mul hA).sub
    ((hasDerivAt_cosh_mul κ t).mul hB)).neg).div_const κ
  refine h.congr_deriv ?_
  simp only [hyperbolicSolutionDeriv]
  field_simp
  ring

/-- The second derivative closes the hyperbolic equation `-ψ'' + κ²ψ = φ`. -/
theorem hasDerivAt_hyperbolicSolutionDeriv {κ R : ℝ} (hκ : κ ≠ 0) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (t : ℝ) :
    HasDerivAt (hyperbolicSolutionDeriv κ R φ)
      (κ ^ 2 * hyperbolicSolution κ R φ t - φ t) t := by
  have hA := hasDerivAt_hyperbolicCosMoment (κ := κ) (R := R) hφ t
  have hB := hasDerivAt_hyperbolicSinMoment (κ := κ) (R := R) hφ t
  have h := (((hasDerivAt_cosh_mul κ t).mul hA).sub ((hasDerivAt_sinh_mul κ t).mul hB)).neg
  refine h.congr_deriv ?_
  have hpyth : Real.cosh (κ * t) ^ 2 - Real.sinh (κ * t) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (κ * t)
  have hexp : κ ^ 2 * hyperbolicSolution κ R φ t
      = -(κ * (Real.sinh (κ * t) * hyperbolicCosMoment κ R φ t
          - Real.cosh (κ * t) * hyperbolicSinMoment κ R φ t)) := by
    simp only [hyperbolicSolution]
    field_simp
  rw [hexp]
  linear_combination (-(φ t)) * hpyth

/-! ## Support -/

theorem hyperbolicCosMoment_eq_zero_left {κ R t : ℝ} {φ : ℝ → ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0) (ht : t ≤ -R) : hyperbolicCosMoment κ R φ t = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_).trans (by simp)
  have hs' : s ≤ -R := by
    rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have habs : R ≤ |s| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  simp [hsupp s habs]

theorem hyperbolicSinMoment_eq_zero_left {κ R t : ℝ} {φ : ℝ → ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0) (ht : t ≤ -R) : hyperbolicSinMoment κ R φ t = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_).trans (by simp)
  have hs' : s ≤ -R := by
    rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have habs : R ≤ |s| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  simp [hsupp s habs]

theorem hyperbolicCosMoment_eq_right {κ R t : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0) (ht : R ≤ t) :
    hyperbolicCosMoment κ R φ t = hyperbolicCosMoment κ R φ R := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => Real.cosh (κ * s) * φ s) volume a b :=
    fun a b => (continuous_cosh_mul.mul hφ).intervalIntegrable a b
  have htail : ∫ s in R..t, Real.cosh (κ * s) * φ s = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_).trans (by simp)
    have hs' : R ≤ s := by
      rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have habs : R ≤ |s| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simp [hsupp s habs]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint (-R) R) (hint R t)
  simp only [hyperbolicCosMoment]
  rw [← hsplit, htail, add_zero]

theorem hyperbolicSinMoment_eq_right {κ R t : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0) (ht : R ≤ t) :
    hyperbolicSinMoment κ R φ t = hyperbolicSinMoment κ R φ R := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s => Real.sinh (κ * s) * φ s) volume a b :=
    fun a b => (continuous_sinh_mul.mul hφ).intervalIntegrable a b
  have htail : ∫ s in R..t, Real.sinh (κ * s) * φ s = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_).trans (by simp)
    have hs' : R ≤ s := by
      rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have habs : R ≤ |s| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simp [hsupp s habs]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint (-R) R) (hint R t)
  simp only [hyperbolicSinMoment]
  rw [← hsplit, htail, add_zero]

/-- The particular solution vanishes to the left of the support. -/
theorem hyperbolicSolution_eq_zero_left {κ R t : ℝ} {φ : ℝ → ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0) (ht : t ≤ -R) : hyperbolicSolution κ R φ t = 0 := by
  simp [hyperbolicSolution, hyperbolicCosMoment_eq_zero_left hR hsupp ht,
    hyperbolicSinMoment_eq_zero_left hR hsupp ht]

/-- The particular solution vanishes to the right of the support exactly when both hyperbolic
moments of the source vanish. -/
theorem hyperbolicSolution_eq_zero_right {κ R t : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0)
    (hC : hyperbolicCosMoment κ R φ R = 0) (hS : hyperbolicSinMoment κ R φ R = 0)
    (ht : R ≤ t) : hyperbolicSolution κ R φ t = 0 := by
  simp [hyperbolicSolution, hyperbolicCosMoment_eq_right hφ hR hsupp ht,
    hyperbolicSinMoment_eq_right hφ hR hsupp ht, hC, hS]

/-! ## The odd moment of an even source -/

/-- The hyperbolic-sine moment of an even source over a symmetric interval vanishes. -/
theorem hyperbolicSinMoment_eq_zero_of_even {κ R : ℝ} {φ : ℝ → ℝ}
    (heven : ∀ t, φ (-t) = φ t) : hyperbolicSinMoment κ R φ R = 0 := by
  have hcomp : ∫ s in (-R)..R, Real.sinh (κ * -s) * φ (-s)
      = ∫ s in (-R)..R, Real.sinh (κ * s) * φ s := by
    have h := intervalIntegral.integral_comp_neg (a := -R) (b := R)
      (fun s => Real.sinh (κ * s) * φ s)
    rw [neg_neg] at h
    exact h
  have hodd : ∀ s : ℝ, Real.sinh (κ * -s) * φ (-s) = -(Real.sinh (κ * s) * φ s) := by
    intro s
    rw [heven s, mul_neg, Real.sinh_neg]
    ring
  rw [intervalIntegral.integral_congr (g := fun s => -(Real.sinh (κ * s) * φ s))
    (fun s _ => hodd s), intervalIntegral.integral_neg] at hcomp
  simp only [hyperbolicSinMoment]
  linarith

/-! ## The even solution -/

/-- The even part of the particular solution. -/
def hyperbolicEvenSolution (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (hyperbolicSolution κ R φ t + hyperbolicSolution κ R φ (-t)) / 2

/-- The derivative of the even part of the particular solution. -/
def hyperbolicEvenSolutionDeriv (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (hyperbolicSolutionDeriv κ R φ t - hyperbolicSolutionDeriv κ R φ (-t)) / 2

theorem hyperbolicEvenSolution_even (κ R : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    hyperbolicEvenSolution κ R φ (-t) = hyperbolicEvenSolution κ R φ t := by
  simp only [hyperbolicEvenSolution, neg_neg]
  ring

theorem hasDerivAt_hyperbolicEvenSolution {κ R : ℝ} (hκ : κ ≠ 0) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (t : ℝ) :
    HasDerivAt (hyperbolicEvenSolution κ R φ) (hyperbolicEvenSolutionDeriv κ R φ t) t := by
  have h1 := hasDerivAt_hyperbolicSolution (R := R) hκ hφ t
  have hneg : HasDerivAt (fun z : ℝ => hyperbolicSolution κ R φ (-z))
      (-hyperbolicSolutionDeriv κ R φ (-t)) t := by
    have hcomp : HasDerivAt (fun z : ℝ => hyperbolicSolution κ R φ (-z))
        (hyperbolicSolutionDeriv κ R φ (-t) * -1) t :=
      (hasDerivAt_hyperbolicSolution (R := R) hκ hφ (-t)).comp t (hasDerivAt_neg' t)
    exact hcomp.congr_deriv (by ring)
  refine (h1.add hneg).div_const 2 |>.congr_deriv ?_
  simp only [hyperbolicEvenSolutionDeriv]
  ring

theorem hasDerivAt_hyperbolicEvenSolutionDeriv {κ R : ℝ} (hκ : κ ≠ 0) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (heven : ∀ t, φ (-t) = φ t) (t : ℝ) :
    HasDerivAt (hyperbolicEvenSolutionDeriv κ R φ)
      (κ ^ 2 * hyperbolicEvenSolution κ R φ t - φ t) t := by
  have h1 := hasDerivAt_hyperbolicSolutionDeriv (R := R) hκ hφ t
  have hneg : HasDerivAt (fun z : ℝ => hyperbolicSolutionDeriv κ R φ (-z))
      (-(κ ^ 2 * hyperbolicSolution κ R φ (-t) - φ (-t))) t := by
    have hcomp : HasDerivAt (fun z : ℝ => hyperbolicSolutionDeriv κ R φ (-z))
        ((κ ^ 2 * hyperbolicSolution κ R φ (-t) - φ (-t)) * -1) t :=
      (hasDerivAt_hyperbolicSolutionDeriv (R := R) hκ hφ (-t)).comp t (hasDerivAt_neg' t)
    exact hcomp.congr_deriv (by ring)
  refine (h1.sub hneg).div_const 2 |>.congr_deriv ?_
  simp only [hyperbolicEvenSolution]
  rw [heven t]
  ring

theorem hyperbolicEvenSolution_eq_zero {κ R t : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) (hR : 0 ≤ R)
    (hsupp : ∀ u, R ≤ |u| → φ u = 0)
    (hC : hyperbolicCosMoment κ R φ R = 0) (hS : hyperbolicSinMoment κ R φ R = 0)
    (ht : R ≤ |t|) : hyperbolicEvenSolution κ R φ t = 0 := by
  rcases le_total 0 t with hpos | hneg
  · have ht' : R ≤ t := by rwa [abs_of_nonneg hpos] at ht
    have h1 := hyperbolicSolution_eq_zero_right hφ hR hsupp hC hS ht'
    have h2 := hyperbolicSolution_eq_zero_left (κ := κ) hR hsupp (by linarith : -t ≤ -R)
    simp [hyperbolicEvenSolution, h1, h2]
  · have ht' : R ≤ -t := by rwa [abs_of_nonpos hneg] at ht
    have h1 := hyperbolicSolution_eq_zero_left (κ := κ) hR hsupp (by linarith : t ≤ -R)
    have h2 := hyperbolicSolution_eq_zero_right hφ hR hsupp hC hS ht'
    simp [hyperbolicEvenSolution, h1, h2]

/-! ## The range of the hyperbolic operator -/

/-- **The hyperbolic source range.**  An even continuous source supported in `[-R,R]` whose
hyperbolic moment vanishes is `-ψ'' + κ²ψ` for an even twice-differentiable `ψ` supported in
`[-R,R]`. -/
theorem exists_hyperbolic_preimage {κ R : ℝ} (hκ : κ ≠ 0) (hR : 0 ≤ R) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (heven : ∀ t, φ (-t) = φ t) (hsupp : ∀ u, R ≤ |u| → φ u = 0)
    (hmom : (∫ s in (-R)..R, Real.cosh (κ * s) * φ s) = 0) :
    ∃ ψ ψ' : ℝ → ℝ,
      (∀ t, ψ (-t) = ψ t) ∧ (∀ u, R ≤ |u| → ψ u = 0) ∧
      (∀ t, HasDerivAt ψ (ψ' t) t) ∧ (∀ t, HasDerivAt ψ' (κ ^ 2 * ψ t - φ t) t) := by
  have hS : hyperbolicSinMoment κ R φ R = 0 := hyperbolicSinMoment_eq_zero_of_even heven
  refine ⟨hyperbolicEvenSolution κ R φ, hyperbolicEvenSolutionDeriv κ R φ,
    hyperbolicEvenSolution_even κ R φ,
    fun u hu => hyperbolicEvenSolution_eq_zero hφ hR hsupp hmom hS hu,
    fun t => hasDerivAt_hyperbolicEvenSolution hκ hφ t,
    fun t => hasDerivAt_hyperbolicEvenSolutionDeriv hκ hφ heven t⟩

/-! ## Classification of functionals annihilating the range -/

/-- **The hyperbolic source classification.**  A linear functional annihilating every image
`-ψ'' + κ²ψ` of an even twice-differentiable function supported in `[-R,R]` is a multiple of the
hyperbolic pairing on even continuous sources supported in `[-R,R]`.  This is the classification of
even solutions of `L_κ w = 0` in the form used against a source. -/
theorem exists_const_hyperbolic_representation {κ R : ℝ} (hκ : κ ≠ 0) (hR : 0 ≤ R)
    (w : (ℝ → ℝ) → ℝ)
    (hlin : ∀ (a : ℝ) (φ ψ : ℝ → ℝ), w (fun t => φ t - a * ψ t) = w φ - a * w ψ)
    (hann : ∀ ψ ψ' φ : ℝ → ℝ, (∀ t, ψ (-t) = ψ t) → (∀ u, R ≤ |u| → ψ u = 0) →
      (∀ t, HasDerivAt ψ (ψ' t)  t) → (∀ t, HasDerivAt ψ' (κ ^ 2 * ψ t - φ t) t) → w φ = 0) :
    ∃ c : ℝ, ∀ φ : ℝ → ℝ, Continuous φ → (∀ t, φ (-t) = φ t) → (∀ u, R ≤ |u| → φ u = 0) →
      w φ = c * ∫ s in (-R)..R, Real.cosh (κ * s) * φ s := by
  classical
  by_cases hex : ∃ φ₀ : ℝ → ℝ, Continuous φ₀ ∧ (∀ t, φ₀ (-t) = φ₀ t) ∧
      (∀ u, R ≤ |u| → φ₀ u = 0) ∧ (∫ s in (-R)..R, Real.cosh (κ * s) * φ₀ s) ≠ 0
  · obtain ⟨φ₀, hc₀, he₀, hs₀, hm₀⟩ := hex
    refine ⟨w φ₀ / ∫ s in (-R)..R, Real.cosh (κ * s) * φ₀ s, fun φ hc he hs => ?_⟩
    have hint : ∀ ψ : ℝ → ℝ, Continuous ψ →
        IntervalIntegrable (fun s => Real.cosh (κ * s) * ψ s) volume (-R) R :=
      fun ψ hψ => (continuous_cosh_mul.mul hψ).intervalIntegrable _ _
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ s in (-R)..R, Real.cosh (κ * s) * φ s := ⟨_, rfl⟩
    obtain ⟨m₀, hm₀'⟩ : ∃ m₀ : ℝ, m₀ = ∫ s in (-R)..R, Real.cosh (κ * s) * φ₀ s := ⟨_, rfl⟩
    have hm₀ne : m₀ ≠ 0 := by rw [hm₀']; exact hm₀
    have hdiffmom : (∫ s in (-R)..R, Real.cosh (κ * s) * (φ s - m / m₀ * φ₀ s)) = 0 := by
      have hsplit : (fun s => Real.cosh (κ * s) * (φ s - m / m₀ * φ₀ s))
          = fun s => Real.cosh (κ * s) * φ s - m / m₀ * (Real.cosh (κ * s) * φ₀ s) := by
        funext s
        ring
      rw [hsplit, intervalIntegral.integral_sub (hint φ hc)
        (((hint φ₀ hc₀).const_mul (m / m₀))), intervalIntegral.integral_const_mul, ← hm, ← hm₀',
        div_mul_cancel₀ m hm₀ne, sub_self]
    have hcsub : Continuous fun s => φ s - m / m₀ * φ₀ s :=
      hc.sub (continuous_const.mul hc₀)
    have hesub : ∀ t : ℝ, φ (-t) - m / m₀ * φ₀ (-t) = φ t - m / m₀ * φ₀ t := by
      intro t
      rw [he t, he₀ t]
    have hssub : ∀ u : ℝ, R ≤ |u| → φ u - m / m₀ * φ₀ u = 0 := by
      intro u hu
      rw [hs u hu, hs₀ u hu]
      ring
    obtain ⟨ψ, ψ', hψeven, hψsupp, hψd, hψd'⟩ :=
      exists_hyperbolic_preimage hκ hR hcsub hesub hssub hdiffmom
    have hzero : w (fun t => φ t - m / m₀ * φ₀ t) = 0 := hann ψ ψ' _ hψeven hψsupp hψd hψd'
    rw [hlin] at hzero
    have hwφ : w φ = m / m₀ * w φ₀ := by linarith
    rw [hwφ, ← hm, ← hm₀']
    ring
  · refine ⟨0, fun φ hc he hs => ?_⟩
    have hm : (∫ s in (-R)..R, Real.cosh (κ * s) * φ s) = 0 := by
      by_contra hne
      exact hex ⟨φ, hc, he, hs, hne⟩
    obtain ⟨ψ, ψ', hψeven, hψsupp, hψd, hψd'⟩ :=
      exists_hyperbolic_preimage hκ hR hc he hs hm
    rw [hann ψ ψ' φ hψeven hψsupp hψd hψd', hm]
    ring

/-! ## The weak hyperbolic source equation -/

/-- **(HSC.8)-(HSC.9) The weak hyperbolic source equation.**  If a form annihilates every image
`-ψ'' + κ²ψ` of an even twice-differentiable function supported in `[-R,R]`, then against even
continuous sources supported in `[-R,R]` it is the hyperbolic pairing scaled by the ratio of the
form's own energy to its hyperbolic pairing: `q(η,·) = (γ/F')·⟨cosh(κ·),·⟩` with `γ = q(η,η)` and
`F' = ⟨cosh(κ·),η⟩`. -/
theorem hyperbolic_source_equation {κ R : ℝ} (hκ : κ ≠ 0) (hR : 0 ≤ R)
    (w : (ℝ → ℝ) → ℝ) (η : ℝ → ℝ)
    (hlin : ∀ (a : ℝ) (φ ψ : ℝ → ℝ), w (fun t => φ t - a * ψ t) = w φ - a * w ψ)
    (hann : ∀ ψ ψ' φ : ℝ → ℝ, (∀ t, ψ (-t) = ψ t) → (∀ u, R ≤ |u| → ψ u = 0) →
      (∀ t, HasDerivAt ψ (ψ' t) t) → (∀ t, HasDerivAt ψ' (κ ^ 2 * ψ t - φ t) t) → w φ = 0)
    (hcη : Continuous η) (heη : ∀ t, η (-t) = η t) (hsη : ∀ u, R ≤ |u| → η u = 0)
    (hpair : (∫ s in (-R)..R, Real.cosh (κ * s) * η s) ≠ 0)
    (φ : ℝ → ℝ) (hc : Continuous φ) (he : ∀ t, φ (-t) = φ t) (hs : ∀ u, R ≤ |u| → φ u = 0) :
    w φ = w η / (∫ s in (-R)..R, Real.cosh (κ * s) * η s)
      * ∫ s in (-R)..R, Real.cosh (κ * s) * φ s := by
  obtain ⟨c, hc'⟩ := exists_const_hyperbolic_representation hκ hR w hlin hann
  have hη := hc' η hcη heη hsη
  have hcval : c = w η / ∫ s in (-R)..R, Real.cosh (κ * s) * η s := by
    rw [hη]
    field_simp
  rw [hc' φ hc he hs, hcval]

end GaloisForLFunctions.HTGeometry

end
