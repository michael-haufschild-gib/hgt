import GaloisForLFunctions.FiniteFreeProbability.HurwitzDeflation
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreePolyaClass
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv

/-!
# The finite free class of genus one

For a genus-one product `g(w) = e^{aw} Π_i E₁(w/z_i)` the **drift** is
`D = Im a + Σ_i Im(1/z_i)`. The finite free class is exactly described by it.

**Theorem (classification).** All reversed Jensen polynomials of `g` have their roots in `Im ≤ 0`
iff all `z_i` lie in `Im ≥ 0` and `D ≥ 0`. For zeros in the closed upper half-plane, every root has
`Im x ≤ −D`, and this bound is sharp: for every `μ > 0` and all large `d` there is a root with
`Im x > −D − μ`; at `D = 0` almost all roots converge to the real axis. Only finitely many outliers
`x ≈ d/z_i` carry the imaginary mass `Σ Im x/d = −Im a`.
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

theorem differentiable_canonicalProduct {ι : Type*} {z : ι → ℂ} (hz0 : ∀ i, z i ≠ 0)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) :
    Differentiable ℂ (canonicalProductE1Indexed z) :=
  differentiableOn_univ.1 (canonicalProductE1Indexed_analytic z hz0 hsq).differentiableOn

theorem differentiable_canonicalProduct_compl {ι : Type*} {z : ι → ℂ} (hz0 : ∀ i, z i ≠ 0)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (s : Set ι) :
    Differentiable ℂ (canonicalProductE1Indexed fun x : ↑sᶜ => z x.1) :=
  differentiable_canonicalProduct (fun x => hz0 x.1) (hsq.subtype (· ∈ sᶜ))

theorem isRoot_jensenRev_expSeries_mul_iff (d : ℕ) (c : ℂ) (F : PowerSeries ℂ) (x : ℂ) :
    (jensenRev d (expSeries c * F)).IsRoot x ↔ (jensenRev d F).IsRoot (x + c) := by
  rw [jensenRev_expSeries_mul, IsRoot, eval_comp, eval_add, eval_X, eval_C, IsRoot]

section Polya

variable {ι : Type*} {z : ι → ℂ}

/-- The genus-one product `e^{aw} Π_i E₁(w/z_i)`. -/
def polyaFunction (z : ι → ℂ) (a : ℂ) (w : ℂ) : ℂ :=
  Complex.exp (a * w) * canonicalProductE1Indexed z w

/-- The Taylor coefficients of an entire function. -/
def taylorCoeff (g : ℂ → ℂ) (k : ℕ) : ℂ := PowerSeries.coeff k (taylorPS g)

theorem mk_taylorCoeff (g : ℂ → ℂ) : PowerSeries.mk (taylorCoeff g) = taylorPS g := by
  ext k
  simp [taylorCoeff]

theorem hasSum_taylorCoeff {g : ℂ → ℂ} (hg : Differentiable ℂ g) (u : ℂ) :
    HasSum (fun k => taylorCoeff g k * u ^ k) (g u) := by
  refine (Complex.hasSum_taylorSeries_of_entire hg 0 u).congr_fun fun k => ?_
  simp only [taylorCoeff, taylorPS, PowerSeries.coeff_mk, sub_zero, smul_eq_mul]
  ring

theorem differentiable_polyaFunction (hz0 : ∀ i, z i ≠ 0)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (a : ℂ) :
    Differentiable ℂ (polyaFunction z a) :=
  (by fun_prop : Differentiable ℂ fun w => Complex.exp (a * w)).mul
    (differentiable_canonicalProduct hz0 hsq)

theorem canonicalProduct_zero : canonicalProductE1Indexed z 0 = 1 := by
  simp [canonicalProductE1Indexed, weierstrassE1_zero]

theorem taylorCoeff_polya_zero (a : ℂ) : taylorCoeff (polyaFunction z a) 0 = 1 := by
  simp [taylorCoeff, taylorPS, polyaFunction, canonicalProduct_zero]

/-- The first Taylor coefficient of `e^{aw} Π_i E₁(w/z_i)` is `a`: the genus-one factors have no
linear term. -/
theorem taylorCoeff_polya_one (hz0 : ∀ i, z i ≠ 0) (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ))
    (a : ℂ) : taylorCoeff (polyaFunction z a) 1 = a := by
  have hC := differentiable_canonicalProduct hz0 hsq
  have hlog := logDeriv_canonicalProductE1Indexed hz0 hsq (z := 0) (fun i => (hz0 i).symm)
  simp only [zero_sub, inv_neg, neg_add_cancel, tsum_zero] at hlog
  rw [logDeriv_apply, canonicalProduct_zero, div_one] at hlog
  have hE : HasDerivAt (fun w => Complex.exp (a * w)) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).cexp
  have hd := (hE.mul (hC 0).hasDerivAt).deriv
  simp only [taylorCoeff, taylorPS, PowerSeries.coeff_mk, iteratedDeriv_one, Nat.factorial_one,
    Nat.cast_one, div_one]
  rw [show polyaFunction z a = (fun w => Complex.exp (a * w)) * canonicalProductE1Indexed z from rfl]
  rw [hd, hlog, canonicalProduct_zero]
  simp

/-- Finitely many zeros factor out of `e^{aw} Π_i E₁(w/z_i)`. -/
theorem exists_polya_factor [DecidableEq ι] (hz0 : ∀ i, z i ≠ 0)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (a : ℂ) (T : Finset ι) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ u : ℂ,
      polyaFunction z a u = (∏ i ∈ T, (1 - u / z i)) * G u := by
  set Cc : ℂ → ℂ := canonicalProductE1Indexed (fun x : ↑((T : Set ι)ᶜ) => z x.1)
  have hCc : Differentiable ℂ Cc := differentiable_canonicalProduct_compl hz0 hsq (T : Set ι)
  refine ⟨fun u => Complex.exp ((a + ∑ i ∈ T, 1 / z i) * u) * Cc u,
    (by fun_prop : Differentiable ℂ fun u => Complex.exp ((a + ∑ i ∈ T, 1 / z i) * u)).mul hCc,
    fun u => ?_⟩
  have hsplit := canonicalProductE1Indexed_split hz0 hsq (T : Set ι) u
  rw [Finset.tprod_subtype' T fun i => weierstrassE1 (u / z i)] at hsplit
  have hterm : ∀ i ∈ T, weierstrassE1 (u / z i) =
      (1 - u / z i) * Complex.exp ((1 / z i) * u) := fun i _ => by
    simp only [weierstrassE1]
    ring_nf
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, ← Complex.exp_sum,
    ← Finset.sum_mul] at hsplit
  have hexp : Complex.exp ((a + ∑ i ∈ T, 1 / z i) * u) =
      Complex.exp (a * u) * Complex.exp ((∑ i ∈ T, 1 / z i) * u) := by
    rw [add_mul, Complex.exp_add]
  rw [polyaFunction, ← hsplit]
  change _ = _ * (Complex.exp ((a + ∑ i ∈ T, 1 / z i) * u) *
    (∏' x : ↑((T : Set ι)ᶜ), weierstrassE1 (u / z x.1)))
  rw [hexp]
  ring

theorem taylorPS_polya_translate (hz0 : ∀ i, z i ≠ 0)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (a c : ℂ) :
    taylorPS (polyaFunction z (a + c)) = expSeries c * taylorPS (polyaFunction z a) := by
  rw [show polyaFunction z (a + c) = (fun w => Complex.exp (c * w)) * polyaFunction z a from
    funext fun w => by
      simp only [polyaFunction, Pi.mul_apply, add_mul, Complex.exp_add]
      ring,
    taylorPS_mul (by fun_prop) (differentiable_polyaFunction hz0 hsq a), taylorPS_exp]

/-- At drift zero, almost all reversed Jensen roots of `e^{aw} Π_i E₁(w/z_i)` converge to the real
axis. -/
theorem tendsto_card_filter_div_polya (hz0 : ∀ i, z i ≠ 0) (hz : ∀ i, 0 ≤ (z i).im)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (him : Summable fun i => (1 / z i).im)
    {a : ℂ} (hdrift : a.im + ∑' i, (1 / z i).im = 0) {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun d : ℕ => (Multiset.card ((jensenRev d (taylorPS (polyaFunction z a))).roots.filter
      fun x => x.im ≤ -μ) : ℝ) / d) atTop (𝓝 0) := by
  classical
  rw [← mk_taylorCoeff]
  have hd := differentiable_polyaFunction hz0 hsq a
  refine tendsto_card_filter_div (taylorCoeff_polya_zero a)
    (summable_norm_mul_pow_of_summable fun u => (hasSum_taylorCoeff hd u).summable)
    (fun d x hx => ?_) z hz0 (fun ε hε => ?_) hμ
  · rw [mk_taylorCoeff] at hx
    exact im_le_zero_of_isRoot_jensenRev_polya hz0 hz hsq him hdrift.ge d hx
  · have hlim : Tendsto (fun T : Finset ι => a.im + ∑ i ∈ T, (1 / z i).im) atTop (𝓝 0) := by
      rw [← hdrift]
      exact him.hasSum.const_add a.im
    obtain ⟨T, hT⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    obtain ⟨G, hG, hfac⟩ := exists_polya_factor hz0 hsq a T
    refine ⟨T, G, hG, fun u => ?_, ?_⟩
    · rw [(hasSum_taylorCoeff hd u).tsum_eq, hfac]
    · rwa [taylorCoeff_polya_one hz0 hsq]

/-- **The drift is the exact margin.** For zeros in the closed upper half-plane and
`D = Im a + Σ_i Im(1/z_i)`, every reversed Jensen root of `e^{aw} Π_i E₁(w/z_i)` satisfies
`Im x ≤ −D`. -/
theorem im_le_neg_drift (hz0 : ∀ i, z i ≠ 0) (hz : ∀ i, 0 ≤ (z i).im)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (him : Summable fun i => (1 / z i).im)
    (a : ℂ) (d : ℕ) {x : ℂ} (hx : (jensenRev d (taylorPS (polyaFunction z a))).IsRoot x) :
    x.im ≤ -(a.im + ∑' i, (1 / z i).im) := by
  set D := a.im + ∑' i, (1 / z i).im
  set a₀ := a - I * D
  have ha : a = a₀ + I * D := by simp only [a₀]; ring
  have hdrift : 0 ≤ a₀.im + ∑' i, (1 / z i).im := by
    simp [a₀, D]
  rw [ha, taylorPS_polya_translate hz0 hsq, isRoot_jensenRev_expSeries_mul_iff] at hx
  have := im_le_zero_of_isRoot_jensenRev_polya hz0 hz hsq him hdrift d hx
  simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at this
  linarith

/-- **Sharpness of the margin.** For every `μ > 0` and all large `d` there is a root with
`Im x > −D − μ`. -/
theorem eventually_exists_root_im_gt_neg_drift (hz0 : ∀ i, z i ≠ 0) (hz : ∀ i, 0 ≤ (z i).im)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (him : Summable fun i => (1 / z i).im)
    (a : ℂ) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ d : ℕ in atTop, ∃ x, (jensenRev d (taylorPS (polyaFunction z a))).IsRoot x ∧
      -(a.im + ∑' i, (1 / z i).im) - μ < x.im := by
  set D := a.im + ∑' i, (1 / z i).im
  set a₀ := a - I * D
  have ha : a = a₀ + I * D := by simp only [a₀]; ring
  have hdrift : a₀.im + ∑' i, (1 / z i).im = 0 := by
    simp [a₀, D]
  have hconc := tendsto_card_filter_div_polya hz0 hz hsq him hdrift hμ
  rw [← mk_taylorCoeff] at hconc
  filter_upwards [eventually_exists_root_im_gt (taylorCoeff_polya_zero a₀) hconc] with d hd
  obtain ⟨y, hy, hyim⟩ := hd
  rw [mk_taylorCoeff] at hy
  refine ⟨y - I * D, ?_, ?_⟩
  · rw [ha, taylorPS_polya_translate hz0 hsq, isRoot_jensenRev_expSeries_mul_iff,
      sub_add_cancel]
    exact hy
  · simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
    linarith

/-- **Classification of the finite free class of genus one.** All reversed Jensen polynomials of
`e^{aw} Π_i E₁(w/z_i)` have their roots in `Im ≤ 0` iff all `z_i` lie in `Im ≥ 0` and
`Im a + Σ_i Im(1/z_i) ≥ 0`. -/
theorem jensenRev_polya_stable_iff (hz0 : ∀ i, z i ≠ 0)
    (hsq : Summable fun i => 1 / ‖z i‖ ^ (2 : ℕ)) (him : Summable fun i => (1 / z i).im) (a : ℂ) :
    (∀ d x, (jensenRev d (taylorPS (polyaFunction z a))).IsRoot x → x.im ≤ 0) ↔
      (∀ i, 0 ≤ (z i).im) ∧ 0 ≤ a.im + ∑' i, (1 / z i).im := by
  constructor
  · intro h
    have hd := differentiable_polyaFunction hz0 hsq a
    have hzim : ∀ i, 0 ≤ (z i).im := fun i => by
      classical
      refine im_nonneg_of_frequently_im_le (f := taylorCoeff (polyaFunction z a))
        (summable_norm_mul_pow_of_summable fun u => (hasSum_taylorCoeff hd u).summable)
        (by rw [taylorCoeff_polya_zero]; exact one_ne_zero) (K := 0)
        (Frequently.of_forall fun d x hx => h d x (by rwa [mk_taylorCoeff] at hx)) ?_
      obtain ⟨G, _, hfac⟩ := exists_polya_factor hz0 hsq a {i}
      rw [(hasSum_taylorCoeff hd (z i)).tsum_eq, hfac, Finset.prod_singleton, div_self (hz0 i),
        sub_self, zero_mul]
    refine ⟨hzim, ?_⟩
    by_contra hD
    push Not at hD
    obtain ⟨d, x, hx, hxim⟩ := (eventually_exists_root_im_gt_neg_drift hz0 hzim hsq him a
      (neg_pos.2 hD)).exists
    have := h d x hx
    linarith
  · rintro ⟨hz, hD⟩ d x hx
    have := im_le_neg_drift hz0 hz hsq him a d hx
    linarith

end Polya

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.tendsto_card_filter_div_polya
#print axioms FiniteFreeProbability.jensenRev_polya_stable_iff
