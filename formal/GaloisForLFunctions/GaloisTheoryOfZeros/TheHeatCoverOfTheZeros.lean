import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.CollisionsBlowUpToHermiteProfiles
import GaloisForLFunctions.RHTower.OddWeilFunctionRigidity
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# The heat cover of the zeros and its blow-up at a collision

The zeros of the heat family `H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` form a cover of the plane of
complex times `τ`. Its branch points are the collisions: pairs `(τ₀, z₀)` with `z₀` a multiple zero
of `H_τ₀`. This module resolves a collision of order `m` at an arbitrary complex time.

On the double cover `τ = τ₀ + s²` and at the parabolic scale `z = z₀ + s y`,

`H_{τ₀+s²}(z₀ + s y) = s^m G(s, y)`,

where `G` is analytic on `ℂ²` and `G(0, y) = (a/m!) Q_m(y)`, with `a = H_τ₀^{(m)}(z₀)` and
`Q_m = e^{−D²} y^m` the Hermite profile. The proof expands the kernel. With `X = ix` and
`u = sX(y − sX)`, write `e^u = Σ_{n<m} u^n/n! + u^m e_m(u)`. The moments
`∫ Φ e^{τ₀x²} e^{iz₀x} X^k` are the derivatives `H_τ₀^{(k)}(z₀)`, which vanish for `k < m`, so every
surviving term carries the factor `s^m`. At `s = 0` only the moment of order `m` remains, with the
coefficients of `Q_m`.

* `complexHeat`, `complexHeat_ofReal`, `complexHeat_neg`, `complexHeat_conj`: the family at complex
  time and its two symmetries; `analyticAt_complexHeat`: it is analytic in time and place;
  `exists_complexHeat_ne_zero`: at no time does it vanish identically.
* `iteratedDeriv_complexHeat`: the derivatives in the place are the moments of the weight.
* `collisionBlowup`, `complexHeat_blowup`: the function `G` and the factorization.
* `analyticAt_collisionBlowup`, `collisionBlowup_zero`: analyticity and the profile at `s = 0`.
* `collisionBlowup_neg`: the deck symmetry `G(−s, −y) = (−1)^m G(s, y)` of the double cover.
* `collisionBlowup_conj`, `collisionBlowup_reflect`: conjugation carries the blow-up at `(τ₀, z₀)`
  to the blow-up at `(conj τ₀, conj z₀)`, and the reflection `z ↦ −z` carries the blow-up at `z₀`
  to the blow-up at `−z₀`.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Analytic functions of two complex variables -/

/-- A continuous function on `ℂ × ℂ` that is holomorphic on every complex line is analytic. -/
theorem analyticAt_of_continuous_of_lines {f : ℂ × ℂ → ℂ} (hc : Continuous f)
    (hl : ∀ p v : ℂ × ℂ, Differentiable ℂ fun z : ℂ => f (p + z • v)) (p : ℂ × ℂ) :
    AnalyticAt ℂ f p := by
  let e : (Fin 2 → ℂ) ≃L[ℂ] ℂ × ℂ := ContinuousLinearEquiv.piFinTwo ℂ (fun _ : Fin 2 => ℂ)
  have hg : AnalyticOnNhd ℂ (f ∘ e) univ :=
    analyticOnNhd_of_continuous_affineLineEntire (hc.comp e.continuous) fun x v => by
      simpa only [Function.comp_apply, map_add, map_smul] using hl (e x) (e v)
  have hfe : f = (f ∘ e) ∘ e.symm := by
    funext q
    simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hfe]
  exact (hg (e.symm p) (mem_univ _)).comp ((e.symm : ℂ × ℂ →L[ℂ] (Fin 2 → ℂ)).analyticAt p)

/-- **Kernel integrals are analytic in two parameters.** If `K p x` is holomorphic in `p ∈ ℂ²`,
measurable in `x`, and dominated by an integrable function on every bounded set of parameters, then
`p ↦ ∫ K p x dx` is analytic. -/
theorem analyticAt_integral_of_dominated {K : ℂ × ℂ → ℝ → ℂ}
    (hK : ∀ x, Differentiable ℂ fun p => K p x)
    (hm : ∀ p, AEStronglyMeasurable (K p) volume)
    (hb : ∀ R : ℝ, ∃ g : ℝ → ℝ, Integrable g ∧ ∀ p : ℂ × ℂ, ‖p‖ ≤ R → ∀ x, ‖K p x‖ ≤ g x)
    (p : ℂ × ℂ) : AnalyticAt ℂ (fun p => ∫ x, K p x) p := by
  refine analyticAt_of_continuous_of_lines (continuous_iff_continuousAt.mpr fun p₀ => ?_)
    (fun q v => ?_) p
  · obtain ⟨g, hg, hgb⟩ := hb (‖p₀‖ + 1)
    refine continuousAt_of_dominated (Eventually.of_forall hm) ?_ hg
      (Eventually.of_forall fun x => (hK x).continuous.continuousAt)
    filter_upwards [Metric.ball_mem_nhds p₀ one_pos] with q hq
    refine Eventually.of_forall (hgb q ?_)
    have h1 := norm_le_norm_add_norm_sub' q p₀
    have h2 : ‖q - p₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at hq
    linarith
  · refine differentiableOn_univ.mp (differentiableOn_integral_of_locally_bounded isOpen_univ
      (F := fun x z => K (q + z • v) x)
      (fun x => ((hK x).comp (by fun_prop : Differentiable ℂ fun z : ℂ => q + z • v)).differentiableOn)
      (fun z _ => hm _) fun z₀ _ => ?_)
    obtain ⟨g, hg, hgb⟩ := hb (‖q‖ + (‖z₀‖ + 1) * ‖v‖)
    refine ⟨1, one_pos, subset_univ _, g, hg, fun x z hz => hgb _ ?_ x⟩
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h1 := norm_le_norm_add_norm_sub' z z₀
      have h2 : ‖z - z₀‖ ≤ 1 := by rwa [mem_closedBall, dist_eq_norm] at hz
      linarith
    calc ‖q + z • v‖ ≤ ‖q‖ + ‖z • v‖ := norm_add_le _ _
      _ = ‖q‖ + ‖z‖ * ‖v‖ := by rw [norm_smul]
      _ ≤ ‖q‖ + (‖z₀‖ + 1) * ‖v‖ := by gcongr

/-! ## The exponential quotient -/

/-- The entire function `e_k(u) = (e^u − Σ_{n<k} u^n/n!)/u^k`, built by repeated division. -/
def expQuot : ℕ → ℂ → ℂ
  | 0 => cexp
  | k + 1 => dslope (expQuot k) 0

theorem differentiable_expQuot (k : ℕ) : Differentiable ℂ (expQuot k) := by
  induction k with
  | zero => exact Complex.differentiable_exp
  | succ k ih =>
    exact differentiableOn_univ.mp ((differentiableOn_dslope univ_mem).mpr ih.differentiableOn)

/-- The value at `0` is forced by the exponential remainder bound. -/
private theorem expQuot_zero_of_identity {k : ℕ}
    (h : ∀ u : ℂ, cexp u = ∑ n ∈ Finset.range k, u ^ n / (n.factorial : ℂ) + u ^ k * expQuot k u) :
    expQuot k 0 = 1 / (k.factorial : ℂ) := by
  have hbound : ∀ u : ℂ, u ≠ 0 →
      ‖expQuot k u - 1 / (k.factorial : ℂ)‖ ≤ ‖u‖ * Real.exp ‖u‖ := by
    intro u hu
    have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp u (k + 1)
    rw [Finset.sum_range_succ, h u] at h1
    have e : (∑ n ∈ Finset.range k, u ^ n / (n.factorial : ℂ) + u ^ k * expQuot k u) -
        (∑ n ∈ Finset.range k, u ^ n / (n.factorial : ℂ) + u ^ k / (k.factorial : ℂ)) =
        u ^ k * (expQuot k u - 1 / (k.factorial : ℂ)) := by ring
    rw [e, norm_mul, norm_pow, pow_succ, mul_assoc] at h1
    exact le_of_mul_le_mul_left h1 (pow_pos (norm_pos_iff.mpr hu) k)
  have hc : Continuous fun u => ‖expQuot k u - 1 / (k.factorial : ℂ)‖ :=
    ((differentiable_expQuot k).continuous.sub continuous_const).norm
  have hc2 : Continuous fun u : ℂ => ‖u‖ * Real.exp ‖u‖ := by fun_prop
  have hlim := (hc2.tendsto 0).mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
  simp only [norm_zero, zero_mul] at hlim
  have hle := le_of_tendsto_of_tendsto ((hc.tendsto 0).mono_left nhdsWithin_le_nhds) hlim
    (eventually_nhdsWithin_of_forall fun u hu => hbound u hu)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

/-- `e^u = Σ_{n<k} u^n/n! + u^k e_k(u)`. -/
theorem exp_eq_sum_add_expQuot (k : ℕ) (u : ℂ) :
    cexp u = ∑ n ∈ Finset.range k, u ^ n / (n.factorial : ℂ) + u ^ k * expQuot k u := by
  induction k generalizing u with
  | zero => simp [expQuot]
  | succ k ih =>
    have h0 := expQuot_zero_of_identity ih
    have hs : u * expQuot (k + 1) u = expQuot k u - expQuot k 0 := by
      have h := sub_smul_dslope (expQuot k) 0 u
      rw [sub_zero, smul_eq_mul] at h
      exact h
    rw [Finset.sum_range_succ, ih u]
    linear_combination (-(u ^ k)) * hs + u ^ k * h0

theorem expQuot_zero (k : ℕ) : expQuot k 0 = 1 / (k.factorial : ℂ) :=
  expQuot_zero_of_identity (exp_eq_sum_add_expQuot k)

theorem norm_expQuot_le (k : ℕ) (u : ℂ) : ‖expQuot k u‖ ≤ Real.exp ‖u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [expQuot_zero, norm_zero, Real.exp_zero, norm_div, norm_one, Complex.norm_natCast]
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.factorial_pos k)
  · have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp u k
    rw [exp_eq_sum_add_expQuot k u, add_sub_cancel_left, norm_mul, norm_pow] at h1
    exact le_of_mul_le_mul_left h1 (pow_pos (norm_pos_iff.mpr hu) k)

/-! ## The heat family at complex time -/

/-- The weight `Φ(x) e^{τx²}` of the family at the complex time `τ`. -/
def complexWeight (τ : ℂ) (x : ℝ) : ℂ := (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2)

/-- The heat family `H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` at complex time `τ`. -/
def complexHeat (τ z : ℂ) : ℂ :=
  ∫ x : ℝ, (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2 + I * z * x)

theorem continuous_complexWeight (τ : ℂ) : Continuous (complexWeight τ) := by
  have h := continuous_riemannKernelReal
  unfold complexWeight
  fun_prop

theorem complexWeight_neg (τ : ℂ) (x : ℝ) : complexWeight τ (-x) = complexWeight τ x := by
  simp only [complexWeight, riemannKernel_superExp.even x, Complex.ofReal_neg, neg_sq]

theorem complexWeight_conj (τ : ℂ) (x : ℝ) :
    starRingEnd ℂ (complexWeight τ x) = complexWeight (starRingEnd ℂ τ) x := by
  simp only [complexWeight, map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj]

/-- `|Φ(x) e^{τx²}| = Φ(x) e^{Re τ · x²}` is at most the weight at the real time `‖τ‖`. -/
theorem norm_complexWeight_le (τ : ℂ) (x : ℝ) : ‖complexWeight τ x‖ ≤ ‖heatWeight ‖τ‖ x‖ := by
  have hpos := riemannKernelReal_pos x
  rw [complexWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, heatWeight,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hpos (Real.exp_pos _)),
    Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)) hpos.le
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem complexHeat_eq_expTransform (τ : ℂ) : complexHeat τ = expTransform (complexWeight τ) := by
  funext z
  rw [complexHeat, expTransform]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [complexWeight]
  rw [Complex.exp_add]
  ring

/-- At a real time the family is the de Bruijn–Newman deformation. -/
theorem complexHeat_ofReal (t : ℝ) (z : ℂ) : complexHeat t z = riemannHeat t z := by
  rw [riemannHeat_eq_expTransform, complexHeat, expTransform]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [heatWeight]
  rw [Complex.exp_add]
  push_cast
  ring

/-- `H_τ` is even. -/
theorem complexHeat_neg (τ z : ℂ) : complexHeat τ (-z) = complexHeat τ z := by
  have h := integral_neg_eq_self
    (fun x : ℝ => (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2 + I * z * x)) volume
  rw [complexHeat, complexHeat, ← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [riemannKernel_superExp.even x, Complex.ofReal_neg]
  congr 2
  ring

/-- Conjugation acts on the family by conjugating the time and the place. -/
theorem complexHeat_conj (τ z : ℂ) :
    starRingEnd ℂ (complexHeat τ z) = complexHeat (starRingEnd ℂ τ) (starRingEnd ℂ z) := by
  rw [← complexHeat_neg (starRingEnd ℂ τ), complexHeat, complexHeat, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [map_mul, map_add, map_pow, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  congr 2
  ring

/-- **The heat family is analytic in time and place.** -/
theorem analyticAt_complexHeat (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => complexHeat p.1 p.2) p := by
  refine analyticAt_integral_of_dominated
    (K := fun p x => (riemannKernelReal x : ℂ) * cexp (p.1 * (x : ℂ) ^ 2 + I * p.2 * x))
    (fun x => by fun_prop) (fun p => ?_) (fun R => ?_) p
  · have h := continuous_riemannKernelReal
    exact (by fun_prop : Continuous fun x : ℝ =>
      (riemannKernelReal x : ℂ) * cexp (p.1 * (x : ℂ) ^ 2 + I * p.2 * x)).aestronglyMeasurable
  · refine ⟨fun x => ‖heatWeight |R| x‖ * Real.exp (|R| * |x|),
      integrable_heatWeight (abs_nonneg R) |R|, fun p hp x => ?_⟩
    show ‖(riemannKernelReal x : ℂ) * cexp (p.1 * (x : ℂ) ^ 2 + I * p.2 * x)‖ ≤
      ‖heatWeight |R| x‖ * Real.exp (|R| * |x|)
    have h1 : ‖p.1‖ ≤ |R| := ((norm_fst_le p).trans hp).trans (le_abs_self R)
    have h2 : ‖p.2‖ ≤ |R| := ((norm_snd_le p).trans hp).trans (le_abs_self R)
    have hpos := riemannKernelReal_pos x
    have hw : ‖heatWeight |R| x‖ = riemannKernelReal x * Real.exp (|R| * x ^ 2) := by
      rw [heatWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hpos (Real.exp_pos _))]
    have he1 : ‖cexp (p.1 * (x : ℂ) ^ 2)‖ ≤ Real.exp (|R| * x ^ 2) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg x)
    have he2 : ‖cexp (I * p.2 * x)‖ ≤ Real.exp (|R| * |x|) :=
      (norm_exp_I_mul_le p.2 x).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm _).trans h2) (abs_nonneg x)))
    rw [Complex.exp_add, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, hw]
    calc riemannKernelReal x * (‖cexp (p.1 * (x : ℂ) ^ 2)‖ * ‖cexp (I * p.2 * x)‖)
        ≤ riemannKernelReal x * (Real.exp (|R| * x ^ 2) * Real.exp (|R| * |x|)) := by gcongr
      _ = riemannKernelReal x * Real.exp (|R| * x ^ 2) * Real.exp (|R| * |x|) := by ring

theorem continuous_complexHeat : Continuous fun p : ℂ × ℂ => complexHeat p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_complexHeat p).continuousAt

/-- At every complex time the family is entire in the place. -/
theorem differentiable_complexHeat (τ : ℂ) : Differentiable ℂ (complexHeat τ) := fun z =>
  (analyticAt_complexHeat (τ, z)).differentiableAt.comp z
    (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (τ, z)) z)

/-! ## Moments -/

theorem integrable_norm_complexWeight_mul_pow (τ : ℂ) (n : ℕ) (c : ℝ) :
    Integrable fun x : ℝ => ‖complexWeight τ x * (I * x) ^ n‖ * Real.exp (c * |x|) := by
  refine (integrable_pow_mul_heatWeight (norm_nonneg τ) n c).mono'
    (((continuous_complexWeight τ).mul (by fun_prop)).norm.mul
      (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have h := norm_complexWeight_le τ x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖complexWeight τ x‖ * |x| ^ n * Real.exp (c * |x|)
      ≤ ‖heatWeight ‖τ‖ x‖ * |x| ^ n * Real.exp (c * |x|) := by gcongr
    _ = |x| ^ n * ‖heatWeight ‖τ‖ x‖ * Real.exp (c * |x|) := by ring

/-- `H_τ^{(n)}(z) = ∫ Φ(x) e^{τx²} (ix)^n e^{izx} dx`. -/
theorem iteratedDeriv_complexHeat (τ : ℂ) (n : ℕ) :
    iteratedDeriv n (complexHeat τ) = expTransform fun x => complexWeight τ x * (I * x) ^ n := by
  induction n with
  | zero => simp [complexHeat_eq_expTransform]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hc : Continuous fun x : ℝ => complexWeight τ x * (I * x) ^ n := by
      have := continuous_complexWeight τ
      fun_prop
    rw [(hasDerivAt_expTransform hc (integrable_norm_complexWeight_mul_pow τ n) z).deriv]
    congr 1
    funext x
    ring

theorem integrable_complexWeight_mul_pow_mul_exp (τ : ℂ) (n : ℕ) (z : ℂ) :
    Integrable fun x : ℝ => complexWeight τ x * (I * x) ^ n * cexp (I * z * x) := by
  refine (integrable_norm_complexWeight_mul_pow τ n |z.im|).mono'
    (((continuous_complexWeight τ).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  gcongr
  exact norm_exp_I_mul_le z x

/-- The derivatives of the even function `H_τ` at `−z`. -/
theorem iteratedDeriv_complexHeat_neg (τ : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (complexHeat τ) (-z) = (-1) ^ n * iteratedDeriv n (complexHeat τ) z := by
  have h := integral_neg_eq_self
    (fun x : ℝ => complexWeight τ x * (I * x) ^ n * cexp (I * (-z) * x)) volume
  simp only [iteratedDeriv_complexHeat, expTransform]
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [complexWeight_neg, Complex.ofReal_neg]
  rw [show I * -z * -(x : ℂ) = I * z * x by ring, show I * -(x : ℂ) = -(I * x) by ring, neg_pow]
  ring

/-- The derivatives at the conjugate time and place. -/
theorem iteratedDeriv_complexHeat_conj (τ : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (complexHeat (starRingEnd ℂ τ)) (starRingEnd ℂ z) =
      starRingEnd ℂ (iteratedDeriv n (complexHeat τ) z) := by
  have h := integral_neg_eq_self (fun x : ℝ =>
    complexWeight (starRingEnd ℂ τ) x * (I * x) ^ n * cexp (I * starRingEnd ℂ z * x)) volume
  simp only [iteratedDeriv_complexHeat, expTransform]
  rw [← h, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [complexWeight_neg, Complex.ofReal_neg, map_mul, map_pow, complexWeight_conj,
    Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  rw [show I * starRingEnd ℂ z * -(x : ℂ) = -I * starRingEnd ℂ z * x by ring,
    show I * -(x : ℂ) = -I * x by ring]

/-! ## The family never vanishes identically -/

/-- **At no complex time does the family vanish identically**: the weight `Φ e^{τx²}` is a nonzero
integrable function, and the family is its Fourier transform. -/
theorem exists_complexHeat_ne_zero (τ : ℂ) : ∃ z, complexHeat τ z ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hint : Integrable (complexWeight τ) := by
    have h := integrable_complexWeight_mul_pow_mul_exp τ 0 0
    simpa using h
  have hzero : complexWeight τ =ᵐ[volume] 0 :=
    HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hint fun ξ => by
      have h := hall (-(2 * Real.pi * ξ))
      rw [complexHeat_eq_expTransform, expTransform] at h
      rw [Real.fourier_real_eq_integral_exp_smul, ← h]
      congr 1
      funext v
      rw [smul_eq_mul, mul_comm]
      congr 2
      push_cast
      ring
  have h0 : complexWeight τ = 0 :=
    ((continuous_complexWeight τ).ae_eq_iff_eq volume continuous_const).mp hzero
  have h1 := congrFun h0 0
  simp only [complexWeight, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero,
    Complex.exp_ne_zero, or_false] at h1
  exact (riemannKernelReal_pos 0).ne' h1

/-- Every zero of the family has finite order. -/
theorem analyticOrderAt_complexHeat_ne_top (τ z : ℂ) : analyticOrderAt (complexHeat τ) z ≠ ⊤ := by
  obtain ⟨z₁, hz₁⟩ := exists_complexHeat_ne_zero τ
  intro htop
  exact hz₁ (((differentiable_complexHeat τ).differentiableOn.analyticOnNhd
    isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z)
    (analyticOrderAt_eq_top.mp htop) (mem_univ z₁))

/-! ## The remainder kernel -/

/-- The remainder kernel of the blow-up at `(τ₀, z₀)` in the parameters `p = (s, y)`:
`Φ(x) e^{τ₀x²} e^{iz₀x} X^m (y − sX)^m e_m(sX(y − sX))` with `X = ix`. -/
def blowupKernel (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) (x : ℝ) : ℂ :=
  complexWeight τ₀ x * cexp (I * z₀ * x) *
    ((I * x) ^ m * (p.2 - p.1 * (I * x)) ^ m * expQuot m (p.1 * (I * x) * (p.2 - p.1 * (I * x))))

theorem continuous_blowupKernel (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    Continuous fun x : ℝ => blowupKernel τ₀ z₀ m p x := by
  have h1 := continuous_complexWeight τ₀
  have h2 := (differentiable_expQuot m).continuous
  unfold blowupKernel
  fun_prop

theorem differentiable_blowupKernel (τ₀ z₀ : ℂ) (m : ℕ) (x : ℝ) :
    Differentiable ℂ fun p : ℂ × ℂ => blowupKernel τ₀ z₀ m p x := by
  have h := differentiable_expQuot m
  unfold blowupKernel
  fun_prop

/-- The kernel is dominated, on the parameter ball of radius `R`, by a heat weight at the real time
`‖τ₀‖ + R²` against a polynomial and an exponential. -/
theorem norm_blowupKernel_le (τ₀ z₀ : ℂ) (m : ℕ) {R : ℝ} {p : ℂ × ℂ} (hp : ‖p‖ ≤ R) (x : ℝ) :
    ‖blowupKernel τ₀ z₀ m p x‖ ≤
      R ^ m * (|x| ^ m * ‖heatWeight (‖τ₀‖ + R ^ 2) x‖ *
        Real.exp ((|z₀.im| + R ^ 2 + m) * |x|)) := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have h1 : ‖p.1‖ ≤ R := (norm_fst_le p).trans hp
  have h2 : ‖p.2‖ ≤ R := (norm_snd_le p).trans hp
  have hX : ‖I * (x : ℂ)‖ = |x| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hd0 : ‖p.2 - p.1 * (I * x)‖ ≤ R * (|x| + 1) := by
    calc ‖p.2 - p.1 * (I * x)‖ ≤ ‖p.2‖ + ‖p.1 * (I * x)‖ := norm_sub_le _ _
      _ = ‖p.2‖ + ‖p.1‖ * |x| := by rw [norm_mul, hX]
      _ ≤ R + R * |x| := by gcongr
      _ = R * (|x| + 1) := by ring
  have hd : ‖p.2 - p.1 * (I * x)‖ ≤ R * Real.exp |x| :=
    hd0.trans (mul_le_mul_of_nonneg_left (Real.add_one_le_exp |x|) hR)
  have hu : ‖p.1 * (I * x) * (p.2 - p.1 * (I * x))‖ ≤ R ^ 2 * |x| + R ^ 2 * x ^ 2 := by
    rw [norm_mul, norm_mul, hX]
    calc ‖p.1‖ * |x| * ‖p.2 - p.1 * (I * x)‖ ≤ R * |x| * (R * (|x| + 1)) := by gcongr
      _ = R ^ 2 * |x| + R ^ 2 * x ^ 2 := by rw [← sq_abs x]; ring
  have hE : ‖expQuot m (p.1 * (I * x) * (p.2 - p.1 * (I * x)))‖ ≤
      Real.exp (R ^ 2 * |x|) * Real.exp (R ^ 2 * x ^ 2) := by
    rw [← Real.exp_add]
    exact (norm_expQuot_le m _).trans (Real.exp_le_exp.mpr hu)
  have hW := norm_exp_I_mul_le z₀ x
  have hcw := norm_complexWeight_le τ₀ x
  have hh : ‖heatWeight (‖τ₀‖ + R ^ 2) x‖ = ‖heatWeight ‖τ₀‖ x‖ * Real.exp (R ^ 2 * x ^ 2) := by
    rw [heatWeight_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [blowupKernel, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hX, hh]
  calc ‖complexWeight τ₀ x‖ * ‖cexp (I * z₀ * x)‖ * (|x| ^ m * ‖p.2 - p.1 * (I * x)‖ ^ m *
        ‖expQuot m (p.1 * (I * x) * (p.2 - p.1 * (I * x)))‖)
      ≤ ‖heatWeight ‖τ₀‖ x‖ * Real.exp (|z₀.im| * |x|) * (|x| ^ m * (R * Real.exp |x|) ^ m *
        (Real.exp (R ^ 2 * |x|) * Real.exp (R ^ 2 * x ^ 2))) := by gcongr
    _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul,
          show (|z₀.im| + R ^ 2 + m) * |x| = |z₀.im| * |x| + m * |x| + R ^ 2 * |x| by ring,
          Real.exp_add, Real.exp_add]
        ring

theorem integrable_blowupMajorant (τ₀ z₀ : ℂ) (m : ℕ) (R : ℝ) :
    Integrable fun x : ℝ =>
      R ^ m * (|x| ^ m * ‖heatWeight (‖τ₀‖ + R ^ 2) x‖ *
        Real.exp ((|z₀.im| + R ^ 2 + m) * |x|)) :=
  (integrable_pow_mul_heatWeight (by positivity) m _).const_mul _

theorem integrable_blowupKernel (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    Integrable fun x : ℝ => blowupKernel τ₀ z₀ m p x :=
  (integrable_blowupMajorant τ₀ z₀ m ‖p‖).mono'
    (continuous_blowupKernel τ₀ z₀ m p).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_blowupKernel_le τ₀ z₀ m le_rfl x)

/-! ## The blow-up function -/

/-- The integral part of the blow-up. -/
def blowupRemainder (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  ∫ x : ℝ, blowupKernel τ₀ z₀ m p x

/-- The polynomial part of the blow-up: the terms of order `n < m` of the exponential series,
`Σ_j (−1)^j C(n,j)/n! · y^{n−j} s^{n+j−m} H_τ₀^{(n+j)}(z₀)`. -/
def blowupJet (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  ∑ n ∈ Finset.range m, ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ j * (n.choose j : ℂ) / (n.factorial : ℂ) * p.2 ^ (n - j) * p.1 ^ (n + j - m) *
      iteratedDeriv (n + j) (complexHeat τ₀) z₀

/-- The blown-up heat family `G(s, y)` at `(τ₀, z₀)`: for `s ≠ 0` it is
`H_{τ₀+s²}(z₀ + s y) / s^m` (`complexHeat_blowup`). -/
def collisionBlowup (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  blowupJet τ₀ z₀ m p + blowupRemainder τ₀ z₀ m p

theorem analyticAt_blowupRemainder (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (blowupRemainder τ₀ z₀ m) p :=
  analyticAt_integral_of_dominated (K := blowupKernel τ₀ z₀ m)
    (differentiable_blowupKernel τ₀ z₀ m)
    (fun p => (continuous_blowupKernel τ₀ z₀ m p).aestronglyMeasurable)
    (fun R => ⟨_, integrable_blowupMajorant τ₀ z₀ m R,
      fun _ hp x => norm_blowupKernel_le τ₀ z₀ m hp x⟩) p

/-- **The blow-up is analytic on `ℂ²`.** -/
theorem analyticAt_collisionBlowup (τ₀ z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (collisionBlowup τ₀ z₀ m) p := by
  have hjet : Differentiable ℂ fun p : ℂ × ℂ => blowupJet τ₀ z₀ m p := by
    unfold blowupJet
    fun_prop
  exact (analyticAt_of_continuous_of_lines hjet.continuous
    (fun q v => hjet.comp (by fun_prop : Differentiable ℂ fun z : ℂ => q + z • v)) p).add
    (analyticAt_blowupRemainder τ₀ z₀ m p)

theorem continuous_collisionBlowup (τ₀ z₀ : ℂ) (m : ℕ) : Continuous (collisionBlowup τ₀ z₀ m) :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_collisionBlowup τ₀ z₀ m p).continuousAt

/-- The kernel expansion: the exponential of `u = sX(y − sX)` splits into moments of order `n + j`
and the remainder, which carries `s^m`. -/
private theorem kernel_expansion (τ₀ z₀ : ℂ) (m : ℕ) (s y : ℂ) (x : ℝ) :
    complexWeight τ₀ x * cexp (I * z₀ * x) * cexp (s * (I * x) * (y - s * (I * x))) =
      ∑ n ∈ Finset.range m, ∑ j ∈ Finset.range (n + 1),
        (s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ)) *
          (complexWeight τ₀ x * (I * x) ^ (n + j) * cexp (I * z₀ * x)) +
      s ^ m * blowupKernel τ₀ z₀ m (s, y) x := by
  rw [exp_eq_sum_add_expQuot m (s * (I * x) * (y - s * (I * x))), mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    have hpow : (s * (I * x) * (y - s * (I * x))) ^ n = ∑ j ∈ Finset.range (n + 1),
        s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) * (I * x) ^ (n + j) := by
      rw [mul_pow, show y - s * (I * x) = -s * (I * x) + y by ring, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hpow, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · have hu : (s * (I * x) * (y - s * (I * x))) ^ m =
        s ^ m * ((I * x) ^ m * (y - s * (I * x)) ^ m) := by
      rw [mul_pow, mul_pow, mul_assoc]
    simp only [blowupKernel]
    rw [hu]
    ring

/-- **The blow-up of a collision.** If the derivatives of `H_τ₀` of order `< m` vanish at `z₀`,
then `H_{τ₀+s²}(z₀ + s y) = s^m G(s, y)` for all complex `s` and `y`. -/
theorem complexHeat_blowup {τ₀ z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (complexHeat τ₀) z₀ = 0) (s y : ℂ) :
    complexHeat (τ₀ + s ^ 2) (z₀ + s * y) = s ^ m * collisionBlowup τ₀ z₀ m (s, y) := by
  have hmom : ∀ k : ℕ, ∫ x : ℝ, complexWeight τ₀ x * (I * x) ^ k * cexp (I * z₀ * x) =
      iteratedDeriv k (complexHeat τ₀) z₀ := fun k => by
    rw [iteratedDeriv_complexHeat τ₀ k]
    rfl
  have hint : ∀ k : ℕ,
      Integrable fun x : ℝ => complexWeight τ₀ x * (I * x) ^ k * cexp (I * z₀ * x) :=
    fun k => integrable_complexWeight_mul_pow_mul_exp τ₀ k z₀
  have hterm : ∀ n ∈ Finset.range m, Integrable fun x : ℝ => ∑ j ∈ Finset.range (n + 1),
      (s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ)) *
        (complexWeight τ₀ x * (I * x) ^ (n + j) * cexp (I * z₀ * x)) :=
    fun n _ => integrable_finsetSum _ fun j _ => (hint (n + j)).const_mul _
  calc complexHeat (τ₀ + s ^ 2) (z₀ + s * y)
      = ∫ x : ℝ, complexWeight τ₀ x * cexp (I * z₀ * x) *
          cexp (s * (I * x) * (y - s * (I * x))) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [show (τ₀ + s ^ 2) * (x : ℂ) ^ 2 + I * (z₀ + s * y) * x =
            τ₀ * (x : ℂ) ^ 2 + I * z₀ * x + s * (I * x) * (y - s * (I * x)) by
          linear_combination (s ^ 2 * (x : ℂ) ^ 2) * Complex.I_sq, Complex.exp_add, Complex.exp_add]
        simp only [complexWeight]
        ring
    _ = ∑ n ∈ Finset.range m, ∑ j ∈ Finset.range (n + 1),
          (s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ)) *
            iteratedDeriv (n + j) (complexHeat τ₀) z₀ + s ^ m * blowupRemainder τ₀ z₀ m (s, y) := by
        simp_rw [kernel_expansion τ₀ z₀ m s y]
        rw [integral_add (integrable_finsetSum _ hterm)
          ((integrable_blowupKernel τ₀ z₀ m (s, y)).const_mul _),
          integral_finsetSum _ hterm, integral_const_mul, blowupRemainder]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_finsetSum _ fun j _ => (hint (n + j)).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, hmom]
    _ = s ^ m * collisionBlowup τ₀ z₀ m (s, y) := by
        rw [collisionBlowup, blowupJet, mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only
        rcases lt_or_ge (n + j) m with h | h
        · rw [hvan _ h, mul_zero, mul_zero, mul_zero]
        · have hs : s ^ n * (-s) ^ j = (-1) ^ j * (s ^ m * s ^ (n + j - m)) := by
            rw [← pow_add, Nat.add_sub_cancel' h, neg_pow, pow_add]
            ring
          linear_combination
            (y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ) *
              iteratedDeriv (n + j) (complexHeat τ₀) z₀) * hs

/-- **The Hermite profile.** At `s = 0` the blow-up is `(a/m!) Q_m` with `a = H_τ₀^{(m)}(z₀)`:
the integral part gives `a y^m/m!`, and in the polynomial part only the terms with `n + j = m`
survive, with the coefficient `(−1)^j/(j!(m−2j)!)`. -/
theorem collisionBlowup_zero {τ₀ z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (complexHeat τ₀) z₀ = 0) (y : ℂ) :
    collisionBlowup τ₀ z₀ m (0, y) =
      iteratedDeriv m (complexHeat τ₀) z₀ / (m.factorial : ℂ) * heatModelFwd m y := by
  have hrem : blowupRemainder τ₀ z₀ m (0, y) =
      y ^ m / (m.factorial : ℂ) * iteratedDeriv m (complexHeat τ₀) z₀ := by
    have hk : ∀ x : ℝ, blowupKernel τ₀ z₀ m (0, y) x =
        y ^ m / (m.factorial : ℂ) * (complexWeight τ₀ x * (I * x) ^ m * cexp (I * z₀ * x)) := by
      intro x
      simp only [blowupKernel, zero_mul, sub_zero, expQuot_zero]
      ring
    rw [blowupRemainder, iteratedDeriv_complexHeat, expTransform]
    simp_rw [hk]
    rw [integral_const_mul]
  -- in the polynomial part the inner sum reduces to the term `j = m − n`
  have hjet : blowupJet τ₀ z₀ m (0, y) = ∑ n ∈ Finset.range m,
      (-1 : ℂ) ^ (m - n) * (n.choose (m - n) : ℂ) / (n.factorial : ℂ) * y ^ (n - (m - n)) *
        iteratedDeriv m (complexHeat τ₀) z₀ := by
    rw [blowupJet]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n < m := Finset.mem_range.mp hn
    rw [Finset.sum_eq_single (m - n)]
    · dsimp only
      rw [show n + (m - n) - m = 0 by omega, pow_zero, mul_one, show n + (m - n) = m by omega]
    · intro j _ hjne
      dsimp only
      rcases lt_or_gt_of_ne (show n + j ≠ m by omega) with h | h
      · rw [hvan _ h, mul_zero]
      · rw [zero_pow (by omega), mul_zero, zero_mul]
    · intro hnot
      have h0 : n.choose (m - n) = 0 :=
        Nat.choose_eq_zero_of_lt (by simp only [Finset.mem_range, not_lt] at hnot; omega)
      rw [h0]
      simp
  -- the surviving terms, indexed by `k = m − n − 1`
  have hsum : ∑ n ∈ Finset.range m,
      (-1 : ℂ) ^ (m - n) * (n.choose (m - n) : ℂ) / (n.factorial : ℂ) * y ^ (n - (m - n)) *
        iteratedDeriv m (complexHeat τ₀) z₀ =
      ∑ k ∈ Finset.range (m / 2),
        (-1 : ℂ) ^ (k + 1) / (((k + 1).factorial : ℂ) * ((m - 2 * (k + 1)).factorial : ℂ)) *
          y ^ (m - 2 * (k + 1)) * iteratedDeriv m (complexHeat τ₀) z₀ := by
    rw [← Finset.sum_range_reflect _ m]
    have hsub : Finset.range (m / 2) ⊆ Finset.range m := by
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    rw [← Finset.sum_subset hsub fun k hk hk' => by
      simp only [Finset.mem_range] at hk hk'
      have h0 : (m - 1 - k).choose (m - (m - 1 - k)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h0]
      simp]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 2 * (k + 1) ≤ m := by
      have := Finset.mem_range.mp hk
      omega
    have hc := Nat.cast_choose ℂ (show k + 1 ≤ m - 1 - k by omega)
    have hN : ((m - 1 - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hK : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hM : ((m - 2 * (k + 1)).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [show m - (m - 1 - k) = k + 1 by omega, show m - 1 - k - (k + 1) = m - 2 * (k + 1) by omega,
      hc, show m - 1 - k - (k + 1) = m - 2 * (k + 1) by omega]
    field_simp
  have hk0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  rw [collisionBlowup, hjet, hrem, hsum, heatModelFwd, Finset.sum_range_succ', mul_add,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hK : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hM : ((m - 2 * (k + 1)).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_zero, Nat.sub_zero]
    field_simp

/-! ## The symmetries of the blow-up -/

/-- **The deck symmetry.** `G(−s, −y) = (−1)^m G(s, y)`: the two square roots of `τ − τ₀` describe
the same zeros. -/
theorem collisionBlowup_neg {τ₀ z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (complexHeat τ₀) z₀ = 0) (s y : ℂ) :
    collisionBlowup τ₀ z₀ m (-s, -y) = (-1) ^ m * collisionBlowup τ₀ z₀ m (s, y) := by
  have hG := continuous_collisionBlowup τ₀ z₀ m
  have hfun : (fun s : ℂ => collisionBlowup τ₀ z₀ m (-s, -y)) =
      fun s : ℂ => (-1) ^ m * collisionBlowup τ₀ z₀ m (s, y) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (by fun_prop) (by fun_prop)
      fun s hs => ?_
    have hs0 : s ≠ 0 := hs
    have h1 := complexHeat_blowup hvan s y
    have h2 := complexHeat_blowup hvan (-s) (-y)
    rw [show (-s) ^ 2 = s ^ 2 by ring, show -s * -y = s * y by ring, h1, neg_pow] at h2
    have hm : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    show collisionBlowup τ₀ z₀ m (-s, -y) = (-1) ^ m * collisionBlowup τ₀ z₀ m (s, y)
    apply mul_left_cancel₀ (pow_ne_zero m hs0)
    linear_combination (-((-1 : ℂ) ^ m)) * h2 - (s ^ m * collisionBlowup τ₀ z₀ m (-s, -y)) * hm
  exact congrFun hfun s

/-- **Conjugation.** The conjugate of the blow-up at `(τ₀, z₀)` is the blow-up at the conjugate
time and place: `conj G_{τ₀,z₀}(s, y) = G_{conj τ₀, conj z₀}(conj s, conj y)`. -/
theorem collisionBlowup_conj {τ₀ z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (complexHeat τ₀) z₀ = 0) (s y : ℂ) :
    starRingEnd ℂ (collisionBlowup τ₀ z₀ m (s, y)) =
      collisionBlowup (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m
        (starRingEnd ℂ s, starRingEnd ℂ y) := by
  have hvan' : ∀ i < m,
      iteratedDeriv i (complexHeat (starRingEnd ℂ τ₀)) (starRingEnd ℂ z₀) = 0 := fun i hi => by
    rw [iteratedDeriv_complexHeat_conj, hvan i hi, map_zero]
  have hG := continuous_collisionBlowup τ₀ z₀ m
  have hG' := continuous_collisionBlowup (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m
  have hfun : (fun s : ℂ => starRingEnd ℂ (collisionBlowup τ₀ z₀ m (s, y))) =
      fun s : ℂ => collisionBlowup (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m
        (starRingEnd ℂ s, starRingEnd ℂ y) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (Complex.continuous_conj.comp (hG.comp (continuous_id.prodMk continuous_const)))
      (hG'.comp (Complex.continuous_conj.prodMk continuous_const)) fun s hs => ?_
    have hs0 : s ≠ 0 := hs
    have h1 := congrArg (starRingEnd ℂ) (complexHeat_blowup hvan s y)
    rw [complexHeat_conj] at h1
    simp only [map_add, map_mul, map_pow] at h1
    rw [complexHeat_blowup hvan' (starRingEnd ℂ s) (starRingEnd ℂ y)] at h1
    exact (mul_left_cancel₀ (pow_ne_zero m ((map_ne_zero _).mpr hs0)) h1).symm
  exact congrFun hfun s

/-- **Reflection.** The blow-up at `−z₀` is the blow-up at `z₀` with `y ↦ −y`. -/
theorem collisionBlowup_reflect {τ₀ z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (complexHeat τ₀) z₀ = 0) (s y : ℂ) :
    collisionBlowup τ₀ (-z₀) m (s, y) = collisionBlowup τ₀ z₀ m (s, -y) := by
  have hvan' : ∀ i < m, iteratedDeriv i (complexHeat τ₀) (-z₀) = 0 := fun i hi => by
    rw [iteratedDeriv_complexHeat_neg, hvan i hi, mul_zero]
  have hG := continuous_collisionBlowup τ₀ z₀ m
  have hG' := continuous_collisionBlowup τ₀ (-z₀) m
  have hfun : (fun s : ℂ => collisionBlowup τ₀ (-z₀) m (s, y)) =
      fun s : ℂ => collisionBlowup τ₀ z₀ m (s, -y) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (by fun_prop) (by fun_prop)
      fun s hs => ?_
    have hs0 : s ≠ 0 := hs
    have h1 := complexHeat_blowup hvan' s y
    have h2 := complexHeat_blowup hvan s (-y)
    rw [show z₀ + s * -y = -(-z₀ + s * y) by ring, complexHeat_neg, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero m hs0) h2
  exact congrFun hfun s

end

end GaloisForLFunctions.GaloisTheoryOfZeros
