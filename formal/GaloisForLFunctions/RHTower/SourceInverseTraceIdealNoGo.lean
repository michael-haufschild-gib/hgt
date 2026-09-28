import GaloisForLFunctions.RHTower.MertensClockDefectSignedSpectrum
import GaloisForLFunctions.RHTower.PoissonPrimePhaseTwistThetaNoGo
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNearIsometryCount
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxSourceWeld

/-!
# The Xi-divisor source inverse is not trace class

Let `S` be a positive density source with bounded density and `B` its compact source inverse in
the quantile coordinate, `(B f)(t) = i q(t) P f(t)` with the quantile speed `q` and the pinned
Volterra primitive `P f(t) = ∫_0^t f - t ∫_0^1 f`.  Since `q ≥ mass / sup k > 0`, the bounded
multiplier `M = 1/q` gives `M B = i P`.  Against the orthonormal systems
`f_n = √2 cos(a_n t)`, `g_n = √2 sin(a_n t)`, `a_n = (n + 1/2)π`,

`⟪g_n, M B f_n⟫ = i (1/a_n - 2/a_n³)`,

and `∑ 1/a_n = ∞`.  A product of two Hilbert–Schmidt operators — in particular any trace-class
operator, and any two-sided bounded transport `L E R` of one — has uniformly bounded diagonal
pairings `∑ |⟪g_n, T f_n⟫|`.  Hence `B` is not trace class, and `B ≠ L E R + F` for every
trace-class `E`, bounded `L, R` and trace-class `F`.  This applies to the theta source inverse
whose regularized determinant is `XiC(z)/XiC(0)`, with `E` the Mertens-clock prime defect.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmCompactSource HedenmalmThetaSource

noncomputable section
set_option autoImplicit false

local notation "L²ᵤ" => Lp ℂ 2 unitIntervalMeasure

/-! ### Diagonal pairings of Hilbert–Schmidt products -/

section Pairing

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `∑_{n∈s} |⟪g_n, X Y f_n⟫| ≤ (‖X‖²_HS + ‖Y‖²_HS)/2` for orthonormal `g, f`. -/
theorem sum_norm_inner_comp_le {X : K →L[ℂ] H} {Y : H →L[ℂ] K}
    (hX : ContinuousLinearMap.IsHilbertSchmidt X) (hY : ContinuousLinearMap.IsHilbertSchmidt Y)
    {ι : Type*} {g f : ι → H} (hg : Orthonormal ℂ g) (hf : Orthonormal ℂ f) (s : Finset ι) :
    ∑ n ∈ s, ‖inner ℂ (g n) (X (Y (f n)))‖ ≤
      (ContinuousLinearMap.hsNormSq (ContinuousLinearMap.adjoint X) +
        ContinuousLinearMap.hsNormSq Y) / 2 := by
  have h1 := sum_finset_norm_sq_apply_le_hsNormSq hX.adjoint hg s
  have h2 := sum_finset_norm_sq_apply_le_hsNormSq hY hf s
  calc ∑ n ∈ s, ‖inner ℂ (g n) (X (Y (f n)))‖
      = ∑ n ∈ s, ‖inner ℂ (ContinuousLinearMap.adjoint X (g n)) (Y (f n))‖ :=
        Finset.sum_congr rfl fun n _ => by rw [ContinuousLinearMap.adjoint_inner_left]
    _ ≤ ∑ n ∈ s, (‖ContinuousLinearMap.adjoint X (g n)‖ ^ 2 + ‖Y (f n)‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun n _ => by
          have := norm_inner_le_norm (𝕜 := ℂ) (ContinuousLinearMap.adjoint X (g n)) (Y (f n))
          nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint X (g n)‖ - ‖Y (f n)‖),
            norm_nonneg (ContinuousLinearMap.adjoint X (g n)), norm_nonneg (Y (f n))]
    _ = ((∑ n ∈ s, ‖ContinuousLinearMap.adjoint X (g n)‖ ^ 2) + ∑ n ∈ s, ‖Y (f n)‖ ^ 2) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by gcongr

/-- A two-sided bounded transport of a trace-class operator has bounded diagonal pairings. -/
theorem exists_sum_norm_inner_transport_le {E : K →L[ℂ] K} (hE : ContinuousLinearMap.IsTraceClass E)
    (L : K →L[ℂ] H) (R : H →L[ℂ] K) {ι : Type*} {g f : ι → H} (hg : Orthonormal ℂ g)
    (hf : Orthonormal ℂ f) :
    ∃ C, ∀ s : Finset ι, ∑ n ∈ s, ‖inner ℂ (g n) ((L ∘L E ∘L R) (f n))‖ ≤ C := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hE
  refine ⟨(ContinuousLinearMap.hsNormSq (ContinuousLinearMap.adjoint (L ∘L A)) +
    ContinuousLinearMap.hsNormSq (B ∘L R)) / 2, fun s => ?_⟩
  have h := sum_norm_inner_comp_le (hA.comp_left L) (hB.comp_right R) hg hf s
  simpa only [ContinuousLinearMap.comp_apply] using h

end Pairing

/-! ### The cosine and sine systems of the unit interval -/

/-- The frequencies `a_n = (n + 1/2) π`. -/
def halfIntFreq (n : ℕ) : ℝ := ((n : ℝ) + 1 / 2) * Real.pi

theorem halfIntFreq_pos (n : ℕ) : 0 < halfIntFreq n := by
  unfold halfIntFreq; have := Real.pi_pos; positivity

theorem halfIntFreq_eq (n : ℕ) : halfIntFreq n = (n : ℝ) * Real.pi + Real.pi / 2 := by
  unfold halfIntFreq; ring

theorem sin_halfIntFreq (n : ℕ) : Real.sin (halfIntFreq n) = (-1) ^ n := by
  rw [halfIntFreq_eq, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]

theorem cos_halfIntFreq (n : ℕ) : Real.cos (halfIntFreq n) = 0 := by
  rw [halfIntFreq_eq, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

theorem sin_int_mul_pi' (k : ℤ) : Real.sin ((k : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi k

theorem sin_sub_halfIntFreq (n m : ℕ) : Real.sin (halfIntFreq n - halfIntFreq m) = 0 := by
  have h : halfIntFreq n - halfIntFreq m = (((n : ℤ) - m : ℤ) : ℝ) * Real.pi := by
    unfold halfIntFreq; push_cast; ring
  rw [h, Real.sin_int_mul_pi]

theorem sin_add_halfIntFreq (n m : ℕ) : Real.sin (halfIntFreq n + halfIntFreq m) = 0 := by
  have h : halfIntFreq n + halfIntFreq m = (((n + m + 1 : ℕ) : ℤ) : ℝ) * Real.pi := by
    unfold halfIntFreq; push_cast; ring
  rw [h, Real.sin_int_mul_pi]

theorem halfIntFreq_add_ne_zero (n m : ℕ) : halfIntFreq n + halfIntFreq m ≠ 0 :=
  (add_pos (halfIntFreq_pos n) (halfIntFreq_pos m)).ne'

theorem halfIntFreq_sub_ne_zero {n m : ℕ} (h : n ≠ m) : halfIntFreq n - halfIntFreq m ≠ 0 := by
  unfold halfIntFreq
  have hpi := Real.pi_pos
  intro h0
  have h1 : ((n : ℝ) - m) * Real.pi = 0 := by linarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h (by exact_mod_cast sub_eq_zero.mp h2)
  · exact hpi.ne' h2

/-- `∫_0^1 2 cos(at) cos(bt) dt = sin(a-b)/(a-b) + sin(a+b)/(a+b)`. -/
theorem integral_two_cos_mul_cos {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ∫ t in (0 : ℝ)..1, 2 * Real.cos (a * t) * Real.cos (b * t) =
      Real.sin (a - b) / (a - b) + Real.sin (a + b) / (a + b) := by
  have hderiv : ∀ t, HasDerivAt
      (fun t => Real.sin ((a - b) * t) / (a - b) + Real.sin ((a + b) * t) / (a + b))
      (2 * Real.cos (a * t) * Real.cos (b * t)) t := by
    intro t
    have e1 := (((hasDerivAt_id' t).const_mul (a - b)).sin).div_const (a - b)
    have e2 := (((hasDerivAt_id' t).const_mul (a + b)).sin).div_const (a + b)
    refine (e1.add e2).congr_deriv ?_
    rw [mul_one, mul_one, mul_div_assoc, mul_div_assoc, div_self h1, div_self h2, mul_one, mul_one,
      show (a - b) * t = a * t - b * t by ring, show (a + b) * t = a * t + b * t by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => 2 * Real.cos (a * t) * Real.cos (b * t)).intervalIntegrable
      _ _)]
  simp

/-- `∫_0^1 2 sin(at) sin(bt) dt = sin(a-b)/(a-b) - sin(a+b)/(a+b)`. -/
theorem integral_two_sin_mul_sin {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
    ∫ t in (0 : ℝ)..1, 2 * Real.sin (a * t) * Real.sin (b * t) =
      Real.sin (a - b) / (a - b) - Real.sin (a + b) / (a + b) := by
  have hderiv : ∀ t, HasDerivAt
      (fun t => Real.sin ((a - b) * t) / (a - b) - Real.sin ((a + b) * t) / (a + b))
      (2 * Real.sin (a * t) * Real.sin (b * t)) t := by
    intro t
    have e1 := (((hasDerivAt_id' t).const_mul (a - b)).sin).div_const (a - b)
    have e2 := (((hasDerivAt_id' t).const_mul (a + b)).sin).div_const (a + b)
    refine (e1.sub e2).congr_deriv ?_
    rw [mul_one, mul_one, mul_div_assoc, mul_div_assoc, div_self h1, div_self h2, mul_one, mul_one,
      show (a - b) * t = a * t - b * t by ring, show (a + b) * t = a * t + b * t by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => 2 * Real.sin (a * t) * Real.sin (b * t)).intervalIntegrable
      _ _)]
  simp

/-- `∫_0^1 2 cos²(at) dt = 1 + sin(2a)/(2a)`. -/
theorem integral_two_cos_sq {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..1, 2 * Real.cos (a * t) * Real.cos (a * t) = 1 + Real.sin (2 * a) / (2 * a) := by
  have hderiv : ∀ t, HasDerivAt (fun t => t + Real.sin ((2 * a) * t) / (2 * a))
      (2 * Real.cos (a * t) * Real.cos (a * t)) t := by
    intro t
    have e := (((hasDerivAt_id' t).const_mul (2 * a)).sin).div_const (2 * a)
    refine ((hasDerivAt_id' t).add e).congr_deriv ?_
    field_simp
    rw [show 2 * a * t = 2 * (a * t) by ring, Real.cos_two_mul]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => 2 * Real.cos (a * t) * Real.cos (a * t)).intervalIntegrable
      _ _)]
  simp

/-- `∫_0^1 2 sin²(at) dt = 1 - sin(2a)/(2a)`. -/
theorem integral_two_sin_sq {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..1, 2 * Real.sin (a * t) * Real.sin (a * t) = 1 - Real.sin (2 * a) / (2 * a) := by
  have hderiv : ∀ t, HasDerivAt (fun t => t - Real.sin ((2 * a) * t) / (2 * a))
      (2 * Real.sin (a * t) * Real.sin (a * t)) t := by
    intro t
    have e := (((hasDerivAt_id' t).const_mul (2 * a)).sin).div_const (2 * a)
    refine ((hasDerivAt_id' t).sub e).congr_deriv ?_
    field_simp
    rw [show 2 * a * t = 2 * (a * t) by ring, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => 2 * Real.sin (a * t) * Real.sin (a * t)).intervalIntegrable
      _ _)]
  simp

theorem sin_two_mul_halfIntFreq (n : ℕ) : Real.sin (2 * halfIntFreq n) = 0 := by
  rw [two_mul]; exact sin_add_halfIntFreq n n

/-- Integration of a real continuous function over the unit interval. -/
theorem integral_unitInterval_ofReal {g : ℝ → ℝ} :
    ∫ t, ((g t : ℝ) : ℂ) ∂unitIntervalMeasure = ((∫ t in (0 : ℝ)..1, g t : ℝ) : ℂ) := by
  rw [integral_complex_ofReal, unitIntervalMeasure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]

theorem memLp_unitInterval_of_continuous {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ t, ‖g t‖ ≤ C) : MemLp g 2 unitIntervalMeasure :=
  MemLp.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hC)

theorem norm_sqrt_two_mul_le {c : ℝ} (hc : |c| ≤ 1) : ‖((Real.sqrt 2 * c : ℝ) : ℂ)‖ ≤ Real.sqrt 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg 2) hc

/-- The cosine system `f_n(t) = √2 cos(a_n t)` in `L²(0,1)`. -/
def cosVec (n : ℕ) : L²ᵤ :=
  (memLp_unitInterval_of_continuous (C := Real.sqrt 2)
    (by fun_prop : Continuous fun t : ℝ => ((Real.sqrt 2 * Real.cos (halfIntFreq n * t) : ℝ) : ℂ))
    fun t => norm_sqrt_two_mul_le (Real.abs_cos_le_one _)).toLp _

/-- The sine system `g_n(t) = √2 sin(a_n t)` in `L²(0,1)`. -/
def sinVec (n : ℕ) : L²ᵤ :=
  (memLp_unitInterval_of_continuous (C := Real.sqrt 2)
    (by fun_prop : Continuous fun t : ℝ => ((Real.sqrt 2 * Real.sin (halfIntFreq n * t) : ℝ) : ℂ))
    fun t => norm_sqrt_two_mul_le (Real.abs_sin_le_one _)).toLp _

theorem cosVec_coeFn (n : ℕ) :
    (cosVec n : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => ((Real.sqrt 2 * Real.cos (halfIntFreq n * t) : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem sinVec_coeFn (n : ℕ) :
    (sinVec n : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => ((Real.sqrt 2 * Real.sin (halfIntFreq n * t) : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem inner_cosVec (n m : ℕ) :
    inner ℂ (cosVec n) (cosVec m) =
      ((∫ t in (0 : ℝ)..1, 2 * Real.cos (halfIntFreq n * t) * Real.cos (halfIntFreq m * t) : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_unitInterval_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [cosVec_coeFn n, cosVec_coeFn m] with t h1 h2
  rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  linear_combination Real.cos (halfIntFreq n * t) * Real.cos (halfIntFreq m * t) * h

theorem inner_sinVec (n m : ℕ) :
    inner ℂ (sinVec n) (sinVec m) =
      ((∫ t in (0 : ℝ)..1, 2 * Real.sin (halfIntFreq n * t) * Real.sin (halfIntFreq m * t) : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_unitInterval_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [sinVec_coeFn n, sinVec_coeFn m] with t h1 h2
  rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  have h := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  linear_combination Real.sin (halfIntFreq n * t) * Real.sin (halfIntFreq m * t) * h

theorem orthonormal_cosVec : Orthonormal ℂ cosVec := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [inner_cosVec]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, integral_two_cos_sq (halfIntFreq_pos n).ne', sin_two_mul_halfIntFreq]
    simp
  · rw [if_neg h, integral_two_cos_mul_cos (halfIntFreq_sub_ne_zero h) (halfIntFreq_add_ne_zero n m),
      sin_sub_halfIntFreq, sin_add_halfIntFreq]
    simp

theorem orthonormal_sinVec : Orthonormal ℂ sinVec := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [inner_sinVec]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, integral_two_sin_sq (halfIntFreq_pos n).ne', sin_two_mul_halfIntFreq]
    simp
  · rw [if_neg h, integral_two_sin_mul_sin (halfIntFreq_sub_ne_zero h) (halfIntFreq_add_ne_zero n m),
      sin_sub_halfIntFreq, sin_add_halfIntFreq]
    simp

/-! ### The pinned Volterra primitive of the cosine system -/

theorem hasDerivAt_sqrt_two_sin_div (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun t => Real.sqrt 2 * Real.sin (a * t) / a)
      (Real.sqrt 2 * Real.cos (a * t)) t := by
  have e := ((((hasDerivAt_id' t).const_mul a).sin).const_mul (Real.sqrt 2)).div_const a
  refine e.congr_deriv ?_
  field_simp

/-- `∫_0^t √2 cos(a_n u) du = √2 sin(a_n t)/a_n` for `t ∈ [0,1]`. -/
theorem intervalIntegral_cosVec (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..t, (cosVec n : ℝ → ℂ) u =
      ((Real.sqrt 2 * Real.sin (halfIntFreq n * t) / halfIntFreq n : ℝ) : ℂ) := by
  have hae : ∀ᵐ u ∂volume, u ∈ Icc (0 : ℝ) 1 →
      (cosVec n : ℝ → ℂ) u = ((Real.sqrt 2 * Real.cos (halfIntFreq n * u) : ℝ) : ℂ) :=
    (ae_restrict_iff' measurableSet_Icc).mp (cosVec_coeFn n)
  rw [intervalIntegral.integral_congr_ae (g := fun u : ℝ =>
    ((Real.sqrt 2 * Real.cos (halfIntFreq n * u) : ℝ) : ℂ)) ?_]
  · rw [intervalIntegral.integral_ofReal,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hasDerivAt_sqrt_two_sin_div (halfIntFreq n) (halfIntFreq_pos n).ne' u)
        ((by fun_prop : Continuous fun u : ℝ =>
          Real.sqrt 2 * Real.cos (halfIntFreq n * u)).intervalIntegrable _ _)]
    simp
  · filter_upwards [hae] with u hu hmem
    rw [uIoc_of_le ht.1] at hmem
    exact hu ⟨hmem.1.le, hmem.2.trans ht.2⟩

theorem pinnedMean_cosVec (n : ℕ) :
    pinnedMean (cosVec n) = ((Real.sqrt 2 * Real.sin (halfIntFreq n) / halfIntFreq n : ℝ) : ℂ) := by
  rw [pinnedMean, integral_congr_ae (cosVec_coeFn n), integral_unitInterval_ofReal,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hasDerivAt_sqrt_two_sin_div (halfIntFreq n) (halfIntFreq_pos n).ne' u)
      ((by fun_prop : Continuous fun u : ℝ =>
        Real.sqrt 2 * Real.cos (halfIntFreq n * u)).intervalIntegrable _ _)]
  simp

theorem pinnedVolterraFun_cosVec (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedVolterraFun (cosVec n) t =
      ((Real.sqrt 2 * Real.sin (halfIntFreq n * t) / halfIntFreq n -
        t * (Real.sqrt 2 * Real.sin (halfIntFreq n) / halfIntFreq n) : ℝ) : ℂ) := by
  rw [pinnedVolterraFun, pinnedPrefix_eq_intervalIntegral _ ht, intervalIntegral_cosVec n ht,
    pinnedMean_cosVec]
  push_cast; ring

/-- `∫_0^1 t sin(at) dt = sin(a)/a² - cos(a)/a`. -/
theorem integral_mul_sin {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..1, t * Real.sin (a * t) = Real.sin a / a ^ 2 - Real.cos a / a := by
  have hderiv : ∀ t, HasDerivAt (fun t => -(t * Real.cos (a * t)) / a + Real.sin (a * t) / a ^ 2)
      (t * Real.sin (a * t)) t := by
    intro t
    have e1 := (((hasDerivAt_id' t).mul ((hasDerivAt_id' t).const_mul a).cos).neg).div_const a
    have e2 := (((hasDerivAt_id' t).const_mul a).sin).div_const (a ^ 2)
    refine (e1.add e2).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => t * Real.sin (a * t)).intervalIntegrable _ _)]
  simp
  ring

/-- `⟪g_n, P f_n⟫ = 1/a_n - 2/a_n³` as an integral over `[0,1]`. -/
theorem integral_sinVec_pinnedVolterra (n : ℕ) :
    ∫ t in (0 : ℝ)..1, Real.sqrt 2 * Real.sin (halfIntFreq n * t) *
        (Real.sqrt 2 * Real.sin (halfIntFreq n * t) / halfIntFreq n -
          t * (Real.sqrt 2 * Real.sin (halfIntFreq n) / halfIntFreq n)) =
      1 / halfIntFreq n - 2 / halfIntFreq n ^ 3 := by
  set a := halfIntFreq n with ha
  have ha0 : a ≠ 0 := (halfIntFreq_pos n).ne'
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have e : (fun t => Real.sqrt 2 * Real.sin (a * t) *
      (Real.sqrt 2 * Real.sin (a * t) / a - t * (Real.sqrt 2 * Real.sin a / a))) =
      fun t => (1 / a) * (2 * Real.sin (a * t) * Real.sin (a * t)) +
        (-(2 * Real.sin a / a)) * (t * Real.sin (a * t)) := by
    funext t
    field_simp
    linear_combination (Real.sin (a * t) * Real.sin (a * t) - t * Real.sin a * Real.sin (a * t)) * h2
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_two_sin_sq ha0, integral_mul_sin ha0, ha,
    sin_two_mul_halfIntFreq, cos_halfIntFreq, sin_halfIntFreq]
  · have hsq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hb := (halfIntFreq_pos n).ne'
    rw [zero_div, zero_div, sub_zero, sub_zero, mul_one]
    have e2 : (-(2 * (-1 : ℝ) ^ n / halfIntFreq n)) * ((-1) ^ n / halfIntFreq n ^ 2) =
        -(2 * ((-1 : ℝ) ^ n) ^ 2 / halfIntFreq n ^ 3) := by
      field_simp
    rw [e2, hsq]
    ring
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      (1 / a) * (2 * Real.sin (a * t) * Real.sin (a * t))).intervalIntegrable _ _)
  · exact ((by fun_prop : Continuous fun t : ℝ =>
      (-(2 * Real.sin a / a)) * (t * Real.sin (a * t))).intervalIntegrable _ _)

theorem trigPairing_pos (n : ℕ) : 0 < 1 / halfIntFreq n - 2 / halfIntFreq n ^ 3 := by
  have ha := halfIntFreq_pos n
  have hbig : 2 < halfIntFreq n ^ 2 := by
    have hpi := Real.pi_gt_three
    have h1 : (3 : ℝ) / 2 ≤ halfIntFreq n := by
      unfold halfIntFreq
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    nlinarith
  rw [sub_pos, div_lt_div_iff₀ (by positivity) ha]
  nlinarith

/-- The pairings are not summable: `1/a_n - 2/a_n³ ≥ 1/(2 a_n)` for `n ≥ 1` and `∑ 1/a_n = ∞`. -/
theorem not_summable_trigPairing : ¬ Summable fun n => 1 / halfIntFreq n - 2 / halfIntFreq n ^ 3 := by
  intro hsum
  have hsum1 := (summable_nat_add_iff 1).mpr hsum
  have hpi := Real.pi_pos
  have hlow : ∀ n : ℕ, 1 / (4 * Real.pi) * (1 / ((n : ℝ) + 2)) ≤
      1 / halfIntFreq (n + 1) - 2 / halfIntFreq (n + 1) ^ 3 := by
    intro n
    have ha := halfIntFreq_pos (n + 1)
    have hlo : (3 / 2 : ℝ) * Real.pi ≤ halfIntFreq (n + 1) := by
      unfold halfIntFreq; push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hup : halfIntFreq (n + 1) ≤ ((n : ℝ) + 2) * Real.pi := by
      unfold halfIntFreq; push_cast; nlinarith
    have hbig : 4 ≤ halfIntFreq (n + 1) ^ 2 := by nlinarith [Real.pi_gt_three]
    have h1 : 1 / (2 * halfIntFreq (n + 1)) ≤ 1 / halfIntFreq (n + 1) - 2 / halfIntFreq (n + 1) ^ 3 := by
      rw [div_sub_div _ _ ha.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine le_trans ?_ h1
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 2) := by
    have h := (Summable.of_nonneg_of_le (fun n => by positivity) hlow hsum1).mul_left (4 * Real.pi)
    refine h.congr fun n => ?_
    field_simp
  have hsum3 : Summable fun n : ℕ => 1 / (n : ℝ) :=
    (summable_nat_add_iff 2).mp (hsum2.congr fun n => by push_cast; ring)
  exact Real.not_summable_one_div_natCast hsum3

/-! ### The source inverse -/

section SourceInverse

variable (S : PositiveDensitySource) (hfin : HasFiniteKernelEnergy S)

theorem measurable_inv_quantileSpeed :
    Measurable fun t : ℝ => (((quantileSpeed S t)⁻¹ : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_quantileSpeed S).inv

theorem norm_inv_quantileSpeed_le {K : ℝ} (hK : ∀ x, S.k x ≤ K) (t : ℝ) :
    ‖(((quantileSpeed S t)⁻¹ : ℝ) : ℂ)‖ ≤ K / S.mass := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (quantileSpeed_pos S t)),
    quantileSpeed, inv_div]
  exact div_le_div_of_nonneg_right (hK _) S.mass_pos.le

theorem div_mass_nonneg {K : ℝ} (hK : ∀ x, S.k x ≤ K) : 0 ≤ K / S.mass :=
  div_nonneg ((S.pos_k 0).le.trans (hK 0)) S.mass_pos.le

/-- Multiplication by the inverse quantile speed `1/q`, bounded by `sup k / mass`. -/
def inverseSpeedMul {K : ℝ} (hK : ∀ x, S.k x ≤ K) : L²ᵤ →L[ℂ] L²ᵤ :=
  lpBoundedMulCLM (p := 2) (μ := unitIntervalMeasure) (measurable_inv_quantileSpeed S)
    (div_mass_nonneg S hK) (norm_inv_quantileSpeed_le S hK)

/-- `(1/q) B f = i P f`. -/
theorem inverseSpeedMul_sourceInverse_ae {K : ℝ} (hK : ∀ x, S.k x ≤ K) (f : L²ᵤ) :
    (inverseSpeedMul S hK
        (kernelOperator (E := L²ᵤ) unitIntervalMeasure (pinnedKernelL2 S hfin) f) : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure] fun t => Complex.I * pinnedVolterraFun f t := by
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := unitIntervalMeasure)
      (measurable_inv_quantileSpeed S) (div_mass_nonneg S hK) (norm_inv_quantileSpeed_le S hK)
      (kernelOperator (E := L²ᵤ) unitIntervalMeasure (pinnedKernelL2 S hfin) f),
    pinnedKernelOperator_ae S hfin f] with t h1 h2
  rw [inverseSpeedMul, h1, h2, pinnedKernelField_apply_eq_pinnedVolterraFun]
  have hq : ((quantileSpeed S t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (quantileSpeed_pos S t).ne'
  push_cast
  field_simp

/-- `⟪g_n, (1/q) B f_n⟫ = i (1/a_n - 2/a_n³)`. -/
theorem inner_sinVec_inverseSpeedMul_sourceInverse_cosVec {K : ℝ} (hK : ∀ x, S.k x ≤ K) (n : ℕ) :
    inner ℂ (sinVec n) (inverseSpeedMul S hK
        (kernelOperator (E := L²ᵤ) unitIntervalMeasure (pinnedKernelL2 S hfin) (cosVec n))) =
      Complex.I * ((1 / halfIntFreq n - 2 / halfIntFreq n ^ 3 : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_sinVec_pinnedVolterra, ← integral_unitInterval_ofReal,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [sinVec_coeFn n, inverseSpeedMul_sourceInverse_ae S hfin hK (cosVec n),
    ae_restrict_mem (μ := volume) measurableSet_Icc] with t h1 h2 ht
  rw [h1, h2, pinnedVolterraFun_cosVec n ht, RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- **No bounded two-sided transport.**  For a bounded density, the source inverse is not of
the form `L E R + F` with `E, F` trace class and `L, R` bounded. -/
theorem sourceInverse_ne_transport_add {K : ℝ} (hK : ∀ x, S.k x ≤ K)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {E : H' →L[ℂ] H'} (hE : ContinuousLinearMap.IsTraceClass E) (L : H' →L[ℂ] L²ᵤ)
    (R : L²ᵤ →L[ℂ] H') {F : L²ᵤ →L[ℂ] L²ᵤ} (hF : ContinuousLinearMap.IsTraceClass F) :
    kernelOperator (E := L²ᵤ) unitIntervalMeasure (pinnedKernelL2 S hfin) ≠ L ∘L E ∘L R + F := by
  intro hB
  set M := inverseSpeedMul S hK
  obtain ⟨C₁, hC₁⟩ := exists_sum_norm_inner_transport_le hE (M ∘L L) R orthonormal_sinVec
    orthonormal_cosVec
  obtain ⟨C₂, hC₂⟩ := exists_sum_norm_inner_transport_le hF M (ContinuousLinearMap.id ℂ L²ᵤ)
    orthonormal_sinVec orthonormal_cosVec
  apply not_summable_trigPairing
  refine summable_of_sum_le (fun n => (trigPairing_pos n).le) (c := C₁ + C₂) fun s => ?_
  calc ∑ n ∈ s, (1 / halfIntFreq n - 2 / halfIntFreq n ^ 3)
      = ∑ n ∈ s, ‖inner ℂ (sinVec n) (M (kernelOperator (E := L²ᵤ) unitIntervalMeasure
          (pinnedKernelL2 S hfin) (cosVec n)))‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [inner_sinVec_inverseSpeedMul_sourceInverse_cosVec S hfin hK n, norm_mul, Complex.norm_I,
          one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (trigPairing_pos n)]
    _ ≤ ∑ n ∈ s, (‖inner ℂ (sinVec n) (((M ∘L L) ∘L E ∘L R) (cosVec n))‖ +
          ‖inner ℂ (sinVec n) ((M ∘L F ∘L ContinuousLinearMap.id ℂ L²ᵤ) (cosVec n))‖) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [hB]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, _root_.add_apply,
          map_add, inner_add_right]
        exact norm_add_le _ _
    _ ≤ C₁ + C₂ := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (hC₁ s) (hC₂ s)

theorem isTraceClass_zero' {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] : ContinuousLinearMap.IsTraceClass (0 : H' →L[ℂ] H') :=
  ⟨0, 0, ContinuousLinearMap.isHilbertSchmidt_zero, ContinuousLinearMap.isHilbertSchmidt_zero,
    by simp⟩

/-- **The source inverse is not trace class** when the density is bounded. -/
theorem not_isTraceClass_sourceInverse {K : ℝ} (hK : ∀ x, S.k x ≤ K) :
    ¬ ContinuousLinearMap.IsTraceClass
      (kernelOperator (E := L²ᵤ) unitIntervalMeasure (pinnedKernelL2 S hfin)) := fun h =>
  sourceInverse_ne_transport_add S hfin hK (isTraceClass_zero' (H' := L²ᵤ)) 0 0 h (by simp)

theorem not_memSchattenClass_one_sourceInverse {K : ℝ} (hK : ∀ x, S.k x ≤ K) :
    ¬ MemSchattenClass 1
      (kernelOperator (E := L²ᵤ) unitIntervalMeasure (pinnedKernelL2 S hfin)) := fun h =>
  not_isTraceClass_sourceInverse S hfin hK h.one_isTraceClass

end SourceInverse

/-! ### The theta source inverse -/

theorem thetaSource_k_le (x : ℝ) : thetaSource.k x ≤ thetaCuspTiltDecayConstant 0 := by
  have h := thetaCuspFullSource_le_tiltDecayConstant 0 x
  simpa using h

/-- **The Xi-divisor source inverse is not trace class.**  Its regularized determinant is
`XiC(z)/XiC(0)` (`thetaSourceEntireDet2_eq_XiC_normalized`). -/
theorem not_isTraceClass_thetaKernelOperator :
    ¬ ContinuousLinearMap.IsTraceClass thetaKernelOperator :=
  not_isTraceClass_sourceInverse thetaSource hasFiniteKernelEnergy_thetaSource thetaSource_k_le

theorem not_memSchattenClass_one_thetaKernelOperator : ¬ MemSchattenClass 1 thetaKernelOperator :=
  not_memSchattenClass_one_sourceInverse thetaSource hasFiniteKernelEnergy_thetaSource
    thetaSource_k_le

/-- **No bounded two-sided transport of the Mertens-clock defect onto the Xi inverse**:
`B_θ ≠ L E R + F` for every bounded `L, R` and trace-class `F`. -/
theorem thetaKernelOperator_ne_transport_mertensClockDefect (L : Lp ℂ 2 halfLineMeasure →L[ℂ] L²ᵤ)
    (R : L²ᵤ →L[ℂ] Lp ℂ 2 halfLineMeasure) {F : L²ᵤ →L[ℂ] L²ᵤ}
    (hF : ContinuousLinearMap.IsTraceClass F) :
    thetaKernelOperator ≠ L ∘L mertensClockDefectOp ∘L R + F :=
  sourceInverse_ne_transport_add thetaSource hasFiniteKernelEnergy_thetaSource thetaSource_k_le
    isTraceClass_mertensStepSechOp_sub L R hF

end

end RHTower
