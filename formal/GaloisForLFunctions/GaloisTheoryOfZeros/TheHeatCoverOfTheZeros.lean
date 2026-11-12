import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.CollisionsBlowUpToHermiteProfiles
import GaloisForLFunctions.RHTower.OddWeilFunctionRigidity
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# The heat cover of the zeros and its blow-up at a collision

The zeros of the heat family `H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` form a cover of the plane of
complex times `τ`. Its branch points are the collisions: pairs `(t, z₀)` with `z₀` a multiple zero
of `H_t`. This module resolves a collision of order `m` at a real time `t ≥ 0`.

On the double cover `τ = t + s²` and at the parabolic scale `z = z₀ + s y`,

`H_{t+s²}(z₀ + s y) = s^m G(s, y)`,

where `G` is analytic on `ℂ²` and `G(0, y) = (a/m!) Q_m(y)`, with `a = H_t^{(m)}(z₀)` and
`Q_m = e^{−D²} y^m` the Hermite profile. The proof expands the kernel. With `X = ix` and
`u = sX(y − sX)`, write `e^u = Σ_{n<m} u^n/n! + u^m e_m(u)`. The moments
`∫ Φ e^{tx²} e^{iz₀x} X^k` are the derivatives `H_t^{(k)}(z₀)`, which vanish for `k < m`, so every
surviving term carries the factor `s^m`.

* `complexHeat`, `complexHeat_ofReal`, `complexHeat_neg`, `complexHeat_conj`: the family at complex
  time and its two symmetries; `analyticAt_complexHeat`: it is analytic in time and place.
* `collisionBlowup`, `complexHeat_blowup`: the function `G` and the factorization.
* `analyticAt_collisionBlowup`, `collisionBlowup_zero`: analyticity and the profile at `s = 0`.
* `collisionBlowup_neg`, `collisionBlowup_conj`: the deck symmetry `G(−s, −y) = (−1)^m G(s, y)` of
  the double cover, and the real structure at a real centre.
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

/-- The heat family `H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` at complex time `τ`. -/
def complexHeat (τ z : ℂ) : ℂ :=
  ∫ x : ℝ, (riemannKernelReal x : ℂ) * cexp (τ * (x : ℂ) ^ 2 + I * z * x)

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

/-! ## The remainder kernel -/

/-- The remainder kernel of the blow-up at `(t, z₀)` in the parameters `p = (s, y)`:
`Φ(x) e^{tx²} e^{iz₀x} X^m (y − sX)^m e_m(sX(y − sX))` with `X = ix`. -/
def blowupKernel (t : ℝ) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) (x : ℝ) : ℂ :=
  heatWeight t x * cexp (I * z₀ * x) *
    ((I * x) ^ m * (p.2 - p.1 * (I * x)) ^ m * expQuot m (p.1 * (I * x) * (p.2 - p.1 * (I * x))))

theorem continuous_blowupKernel (t : ℝ) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    Continuous fun x : ℝ => blowupKernel t z₀ m p x := by
  have h1 := continuous_heatWeight t
  have h2 := (differentiable_expQuot m).continuous
  unfold blowupKernel
  fun_prop

theorem differentiable_blowupKernel (t : ℝ) (z₀ : ℂ) (m : ℕ) (x : ℝ) :
    Differentiable ℂ fun p : ℂ × ℂ => blowupKernel t z₀ m p x := by
  have h := differentiable_expQuot m
  unfold blowupKernel
  fun_prop

/-- The kernel is dominated, on the parameter ball of radius `R`, by a heat weight at the later time
`t + R²` against a polynomial and an exponential. -/
theorem norm_blowupKernel_le (t : ℝ) (z₀ : ℂ) (m : ℕ) {R : ℝ} {p : ℂ × ℂ} (hp : ‖p‖ ≤ R)
    (x : ℝ) :
    ‖blowupKernel t z₀ m p x‖ ≤
      R ^ m * (|x| ^ m * ‖heatWeight (t + R ^ 2) x‖ * Real.exp ((|z₀.im| + R ^ 2 + m) * |x|)) := by
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
  have hh : ‖heatWeight (t + R ^ 2) x‖ = ‖heatWeight t x‖ * Real.exp (R ^ 2 * x ^ 2) := by
    rw [heatWeight_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [blowupKernel, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hX, hh]
  calc ‖heatWeight t x‖ * ‖cexp (I * z₀ * x)‖ * (|x| ^ m * ‖p.2 - p.1 * (I * x)‖ ^ m *
        ‖expQuot m (p.1 * (I * x) * (p.2 - p.1 * (I * x)))‖)
      ≤ ‖heatWeight t x‖ * Real.exp (|z₀.im| * |x|) * (|x| ^ m * (R * Real.exp |x|) ^ m *
        (Real.exp (R ^ 2 * |x|) * Real.exp (R ^ 2 * x ^ 2))) := by gcongr
    _ = _ := by
        rw [mul_pow, ← Real.exp_nat_mul,
          show (|z₀.im| + R ^ 2 + m) * |x| = |z₀.im| * |x| + m * |x| + R ^ 2 * |x| by ring,
          Real.exp_add, Real.exp_add]
        ring

theorem integrable_blowupMajorant {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) (m : ℕ) (R : ℝ) :
    Integrable fun x : ℝ =>
      R ^ m * (|x| ^ m * ‖heatWeight (t + R ^ 2) x‖ * Real.exp ((|z₀.im| + R ^ 2 + m) * |x|)) :=
  (integrable_pow_mul_heatWeight (by positivity) m _).const_mul _

theorem integrable_blowupKernel {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    Integrable fun x : ℝ => blowupKernel t z₀ m p x :=
  (integrable_blowupMajorant ht z₀ m ‖p‖).mono'
    (continuous_blowupKernel t z₀ m p).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_blowupKernel_le t z₀ m le_rfl x)

/-! ## The blow-up function -/

/-- The integral part of the blow-up. -/
def blowupRemainder (t : ℝ) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  ∫ x : ℝ, blowupKernel t z₀ m p x

/-- The polynomial part of the blow-up: the terms of order `n < m` of the exponential series,
`Σ_j (−1)^j C(n,j)/n! · y^{n−j} s^{n+j−m} H_t^{(n+j)}(z₀)`. -/
def blowupJet (t : ℝ) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  ∑ n ∈ Finset.range m, ∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ j * (n.choose j : ℂ) / (n.factorial : ℂ) * p.2 ^ (n - j) * p.1 ^ (n + j - m) *
      iteratedDeriv (n + j) (riemannHeat t) z₀

/-- The blown-up heat family `G(s, y)` at `(t, z₀)`: for `s ≠ 0` it is
`H_{t+s²}(z₀ + s y) / s^m` (`complexHeat_blowup`). -/
def collisionBlowup (t : ℝ) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  blowupJet t z₀ m p + blowupRemainder t z₀ m p

theorem analyticAt_blowupRemainder {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (blowupRemainder t z₀ m) p :=
  analyticAt_integral_of_dominated (K := blowupKernel t z₀ m) (differentiable_blowupKernel t z₀ m)
    (fun p => (continuous_blowupKernel t z₀ m p).aestronglyMeasurable)
    (fun R => ⟨_, integrable_blowupMajorant ht z₀ m R,
      fun _ hp x => norm_blowupKernel_le t z₀ m hp x⟩) p

/-- **The blow-up is analytic on `ℂ²`.** -/
theorem analyticAt_collisionBlowup {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (collisionBlowup t z₀ m) p := by
  have hjet : Differentiable ℂ fun p : ℂ × ℂ => blowupJet t z₀ m p := by
    unfold blowupJet
    fun_prop
  exact (analyticAt_of_continuous_of_lines hjet.continuous
    (fun q v => hjet.comp (by fun_prop : Differentiable ℂ fun z : ℂ => q + z • v)) p).add
    (analyticAt_blowupRemainder ht z₀ m p)

theorem continuous_collisionBlowup {t : ℝ} (ht : 0 ≤ t) (z₀ : ℂ) (m : ℕ) :
    Continuous (collisionBlowup t z₀ m) :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_collisionBlowup ht z₀ m p).continuousAt

/-- The kernel expansion: the exponential of `u = sX(y − sX)` splits into moments of order `n + j`
and the remainder, which carries `s^m`. -/
private theorem kernel_expansion (t : ℝ) (z₀ : ℂ) (m : ℕ) (s y : ℂ) (x : ℝ) :
    heatWeight t x * cexp (I * z₀ * x) * cexp (s * (I * x) * (y - s * (I * x))) =
      ∑ n ∈ Finset.range m, ∑ j ∈ Finset.range (n + 1),
        (s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ)) *
          (heatWeight t x * (I * x) ^ (n + j) * cexp (I * z₀ * x)) +
      s ^ m * blowupKernel t z₀ m (s, y) x := by
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

/-- **The blow-up of a collision.** If the derivatives of `H_t` of order `< m` vanish at `z₀`, then
`H_{t+s²}(z₀ + s y) = s^m G(s, y)` for all complex `s` and `y`. -/
theorem complexHeat_blowup {t : ℝ} (ht : 0 ≤ t) {z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (riemannHeat t) z₀ = 0) (s y : ℂ) :
    complexHeat (t + s ^ 2) (z₀ + s * y) = s ^ m * collisionBlowup t z₀ m (s, y) := by
  have hmom : ∀ k : ℕ, ∫ x : ℝ, heatWeight t x * (I * x) ^ k * cexp (I * z₀ * x) =
      iteratedDeriv k (riemannHeat t) z₀ := fun k => by
    rw [iteratedDeriv_riemannHeat ht k]
    rfl
  have hint : ∀ k : ℕ, Integrable fun x : ℝ => heatWeight t x * (I * x) ^ k * cexp (I * z₀ * x) :=
    fun k => integrable_heatWeight_mul_pow_mul_exp ht k z₀
  have hterm : ∀ n ∈ Finset.range m, Integrable fun x : ℝ => ∑ j ∈ Finset.range (n + 1),
      (s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ)) *
        (heatWeight t x * (I * x) ^ (n + j) * cexp (I * z₀ * x)) :=
    fun n _ => integrable_finsetSum _ fun j _ => (hint (n + j)).const_mul _
  calc complexHeat (t + s ^ 2) (z₀ + s * y)
      = ∫ x : ℝ, heatWeight t x * cexp (I * z₀ * x) * cexp (s * (I * x) * (y - s * (I * x))) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [show ((t : ℂ) + s ^ 2) * (x : ℂ) ^ 2 + I * (z₀ + s * y) * x =
            (t : ℂ) * (x : ℂ) ^ 2 + I * z₀ * x + s * (I * x) * (y - s * (I * x)) by
          linear_combination (s ^ 2 * (x : ℂ) ^ 2) * Complex.I_sq, Complex.exp_add, Complex.exp_add]
        simp only [heatWeight]
        push_cast
        ring
    _ = ∑ n ∈ Finset.range m, ∑ j ∈ Finset.range (n + 1),
          (s ^ n * (-s) ^ j * y ^ (n - j) * (n.choose j : ℂ) / (n.factorial : ℂ)) *
            iteratedDeriv (n + j) (riemannHeat t) z₀ + s ^ m * blowupRemainder t z₀ m (s, y) := by
        simp_rw [kernel_expansion t z₀ m s y]
        rw [integral_add (integrable_finsetSum _ hterm)
          ((integrable_blowupKernel ht z₀ m (s, y)).const_mul _),
          integral_finsetSum _ hterm, integral_const_mul, blowupRemainder]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_finsetSum _ fun j _ => (hint (n + j)).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, hmom]
    _ = s ^ m * collisionBlowup t z₀ m (s, y) := by
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
              iteratedDeriv (n + j) (riemannHeat t) z₀) * hs

/-- **The Hermite profile.** At `s = 0` the blow-up is `(a/m!) Q_m` with `a = H_t^{(m)}(z₀)`. -/
theorem collisionBlowup_zero {t : ℝ} (ht : 0 ≤ t) {z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (riemannHeat t) z₀ = 0) (y : ℂ) :
    collisionBlowup t z₀ m (0, y) =
      iteratedDeriv m (riemannHeat t) z₀ / (m.factorial : ℂ) * heatModelFwd m y := by
  obtain ⟨C, q₀, hq₀, hmodel⟩ :=
    exists_norm_riemannHeat_sub_heatModelFwd_le ht hvan (norm_nonneg y)
  set c := iteratedDeriv m (riemannHeat t) z₀ / (m.factorial : ℂ) * heatModelFwd m y with hc
  have hG := continuous_collisionBlowup ht z₀ m
  -- for real `q > 0` the factorization turns the forward model into `‖G(q, y) − c‖ ≤ |C| q`
  have hbound : ∀ᶠ q : ℝ in 𝓝[>] 0, ‖collisionBlowup t z₀ m ((q : ℂ), y) - c‖ ≤ |C| * q := by
    filter_upwards [Ioc_mem_nhdsGT hq₀] with q hq
    have h := hmodel q hq.1.le hq.2 y le_rfl
    rw [← complexHeat_ofReal,
      show ((t + q ^ 2 : ℝ) : ℂ) = (t : ℂ) + (q : ℂ) ^ 2 by push_cast; ring,
      complexHeat_blowup ht hvan] at h
    have e : (q : ℂ) ^ m * collisionBlowup t z₀ m ((q : ℂ), y) -
        iteratedDeriv m (riemannHeat t) z₀ / (m.factorial : ℂ) * (q : ℂ) ^ m * heatModelFwd m y =
        (q : ℂ) ^ m * (collisionBlowup t z₀ m ((q : ℂ), y) - c) := by
      rw [hc]
      ring
    rw [e, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1, pow_succ] at h
    have hCq : C * (q ^ m * q) ≤ q ^ m * (|C| * q) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self C)
        (mul_nonneg (pow_nonneg hq.1.le m) hq.1.le)
      linarith
    exact le_of_mul_le_mul_left (h.trans hCq) (pow_pos hq.1 m)
  have hcq : Continuous fun q : ℝ => ‖collisionBlowup t z₀ m ((q : ℂ), y) - c‖ := by fun_prop
  have hcont := (hcq.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [Complex.ofReal_zero] at hcont
  have hc0 : Continuous fun q : ℝ => |C| * q := by fun_prop
  have hlim := (hc0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [mul_zero] at hlim
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_tendsto_of_tendsto hcont hlim hbound))

/-! ## The two symmetries of the blow-up -/

/-- **The deck symmetry.** `G(−s, −y) = (−1)^m G(s, y)`: the two square roots of `τ − t` describe
the same zeros. -/
theorem collisionBlowup_neg {t : ℝ} (ht : 0 ≤ t) {z₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (riemannHeat t) z₀ = 0) (s y : ℂ) :
    collisionBlowup t z₀ m (-s, -y) = (-1) ^ m * collisionBlowup t z₀ m (s, y) := by
  have hG := continuous_collisionBlowup ht z₀ m
  have hfun : (fun s : ℂ => collisionBlowup t z₀ m (-s, -y)) =
      fun s : ℂ => (-1) ^ m * collisionBlowup t z₀ m (s, y) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (by fun_prop) (by fun_prop)
      fun s hs => ?_
    have hs0 : s ≠ 0 := hs
    have h1 := complexHeat_blowup ht hvan s y
    have h2 := complexHeat_blowup ht hvan (-s) (-y)
    rw [show (-s) ^ 2 = s ^ 2 by ring, show -s * -y = s * y by ring, h1, neg_pow] at h2
    have hm : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    show collisionBlowup t z₀ m (-s, -y) = (-1) ^ m * collisionBlowup t z₀ m (s, y)
    apply mul_left_cancel₀ (pow_ne_zero m hs0)
    linear_combination (-((-1 : ℂ) ^ m)) * h2 - (s ^ m * collisionBlowup t z₀ m (-s, -y)) * hm
  exact congrFun hfun s

/-- **The real structure.** At a real centre, `conj G(s, y) = G(conj s, conj y)`. -/
theorem collisionBlowup_conj {t : ℝ} (ht : 0 ≤ t) {x₀ : ℝ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i (riemannHeat t) x₀ = 0) (s y : ℂ) :
    starRingEnd ℂ (collisionBlowup t x₀ m (s, y)) =
      collisionBlowup t x₀ m (starRingEnd ℂ s, starRingEnd ℂ y) := by
  have hG := continuous_collisionBlowup ht (x₀ : ℂ) m
  have hfun : (fun s : ℂ => starRingEnd ℂ (collisionBlowup t x₀ m (s, y))) =
      fun s : ℂ => collisionBlowup t x₀ m (starRingEnd ℂ s, starRingEnd ℂ y) := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (Complex.continuous_conj.comp (hG.comp (continuous_id.prodMk continuous_const)))
      (hG.comp (Complex.continuous_conj.prodMk continuous_const)) fun s hs => ?_
    have hs0 : s ≠ 0 := hs
    have h1 := congrArg (starRingEnd ℂ) (complexHeat_blowup ht hvan s y)
    rw [complexHeat_conj] at h1
    simp only [map_add, map_mul, map_pow, Complex.conj_ofReal] at h1
    rw [complexHeat_blowup ht hvan (starRingEnd ℂ s) (starRingEnd ℂ y)] at h1
    exact (mul_left_cancel₀ (pow_ne_zero m ((map_ne_zero _).mpr hs0)) h1).symm
  exact congrFun hfun s

end

end GaloisForLFunctions.GaloisTheoryOfZeros
