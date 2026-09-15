import GaloisForLFunctions.RHTower.SelbergMaassBoundaryFlux
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Quantitative decay of actual exceptional Maass cusp mass

The actual mass equation and zero constant coefficient give `M'' ≥ k²*M` above
`1/k`, where `k=2*pi/(N+1)`. Convexity and the defining cusp limit force `M'≤0`.
The increasing factor `exp(-k*y)*(M'+k*M)` is bounded above by a function tending
to zero, hence is nonpositive. Therefore `exp(k*y)*M` decreases: actual source
mass decays exponentially, without a Bessel asymptotic or decay premise.

Backward unit secants also force `M'` to zero. Thus the actual boundary flux
vanishes at infinity; its nonnegative derivative above the cutoff is integrable
and has integral equal to minus the boundary value.

These are cusp-local conclusions. The global quotient-core inequality is not proved.
-/

open Set Filter Topology UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassCuspDecay
open SelbergMaassFlux
noncomputable section

/-- The first nonzero horizontal frequency at the actual congruence period. -/
def rate (N : ℕ) : ℝ := 2 * Real.pi / (N + 1 : ℕ)
/-- An explicit source height above which the mass differential inequality is coercive. -/
def cutoff (N : ℕ) : ℝ := 1 / rate N

/-- Every positive congruence period has positive first frequency. -/
theorem rate_pos (N : ℕ) : 0 < rate N := by unfold rate; positivity
/-- The explicit decay cutoff lies in the upper half-plane. -/
theorem cutoff_pos (N : ℕ) : 0 < cutoff N := one_div_pos.mpr (rate_pos N)

/-- Actual exceptional mass obeys a coercive second-derivative inequality above the cutoff. -/
theorem mass_second_lower (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : cutoff N ≤ y) :
    rate N ^ 2 * mass N f y ≤ deriv (deriv (mass N f)) y := by
  have hypos := (cutoff_pos N).trans_le hy
  have hky : 1 ≤ y * rate N := (div_le_iff₀ (rate_pos N)).mp hy
  have hsq : 1 ≤ rate N ^ 2 * y ^ 2 := by nlinarith [sq_nonneg (y * rate N - 1)]
  have hpot : (lam : ℝ) / y ^ 2 ≤ rate N ^ 2 / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hypos)]
    nlinarith [lam.2.2]
  have hm := mass_nonneg N f hypos
  have hG := gradientEnergy_ge_first_frequency N lam f hypos
  change rate N ^ 2 * mass N f y ≤ gradientEnergy N f y at hG
  have hh := mul_le_mul_of_nonneg_right hpot hm
  rw [(mass_second_hasDerivAt N f hypos).deriv]
  nlinarith [mul_nonneg (sq_nonneg (rate N)) hm]

private theorem decaying_convex_deriv_nonpos {u v a2 : ℝ → ℝ} {A : ℝ}
    (hu : ∀ y ∈ Ici A, HasDerivAt u (v y) y)
    (hv : ∀ y ∈ Ici A, HasDerivAt v (a2 y) y)
    (ha2 : ∀ y ∈ Ici A, 0 ≤ a2 y)
    (hdec : Tendsto u atTop (𝓝 0)) : ∀ y ∈ Ici A, v y ≤ 0 := by
  have hmono : MonotoneOn v (Ici A) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici A)
    · intro y hy; exact (hv y hy).continuousAt.continuousWithinAt
    · intro y hy; exact (hv y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy; rw [(hv y (interior_subset hy)).deriv]; exact ha2 y (interior_subset hy)
  intro y hy
  have ht : Tendsto (fun t : ℝ => t - y) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-y) tendsto_id
  apply ge_of_tendsto ((hdec.sub_const (u y)).div_atTop ht)
  filter_upwards [eventually_gt_atTop y] with t ht
  have htan := (convex_Ici y).mul_sub_le_image_sub_of_le_deriv
    (f := u)
    (by intro s hs
        have has : A ≤ s := le_trans hy hs
        exact (hu s has).continuousAt.continuousWithinAt)
    (by intro s hs
        have hys : y ≤ s := interior_subset hs
        exact (hu s (hy.trans hys)).differentiableAt.differentiableWithinAt)
    (C := v y)
    (fun s hs => by
      have hys : y ≤ s := interior_subset hs
      rw [(hu s (by exact le_trans hy hys)).deriv]
      exact hmono hy (by exact le_trans hy hys) hys)
    y (by simp) t ht.le ht.le
  exact (le_div_iff₀ (sub_pos.mpr ht)).mpr htan

private theorem decaying_ode_barrier {u v a2 : ℝ → ℝ} {A k : ℝ} (hk : 0 < k)
    (hu : ∀ y ∈ Ici A, HasDerivAt u (v y) y)
    (hv : ∀ y ∈ Ici A, HasDerivAt v (a2 y) y)
    (hu0 : ∀ y ∈ Ici A, 0 ≤ u y)
    (ha2 : ∀ y ∈ Ici A, k ^ 2 * u y ≤ a2 y)
    (hdec : Tendsto u atTop (𝓝 0)) : ∀ y ∈ Ici A, v y + k * u y ≤ 0 := by
  have hv0 := decaying_convex_deriv_nonpos hu hv
    (fun y hy => (mul_nonneg (sq_nonneg k) (hu0 y hy)).trans (ha2 y hy)) hdec
  let B := fun y => Real.exp (-k * y) * (v y + k * u y)
  have hdB (y : ℝ) (hy : y ∈ Ici A) :
      HasDerivAt B (Real.exp (-k * y) * (a2 y - k ^ 2 * u y)) y := by
    convert (((hasDerivAt_id y).const_mul (-k)).exp).mul
      ((hv y hy).add ((hu y hy).const_mul k)) using 1 <;> try rfl
    simp only [id_eq, Pi.add_apply]
    ring
  have hmono : MonotoneOn B (Ici A) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici A)
    · intro y hy; exact (hdB y hy).continuousAt.continuousWithinAt
    · intro y hy; exact (hdB y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hdB y (interior_subset hy)).deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (ha2 y (interior_subset hy)))
  have he : Tendsto (fun t : ℝ => Real.exp (-k * t)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [← neg_mul, Function.comp_def, id_eq] using tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hk)
  have hlim : Tendsto (fun t => Real.exp (-k * t) * (k * u t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using he.mul (hdec.const_mul k)
  intro y hy
  have hB : B y ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop y] with t ht
    have hyt := hy.trans ht
    exact (hmono hy hyt ht).trans (mul_le_mul_of_nonneg_left
      (by linarith [hv0 t hyt]) (Real.exp_pos _).le)
  by_contra hn
  exact (not_lt_of_ge hB) (mul_pos (Real.exp_pos _) (lt_of_not_ge hn))

private theorem decaying_ode_exponential {u v a2 : ℝ → ℝ} {A k : ℝ} (hk : 0 < k)
    (hu : ∀ y ∈ Ici A, HasDerivAt u (v y) y)
    (hv : ∀ y ∈ Ici A, HasDerivAt v (a2 y) y)
    (hu0 : ∀ y ∈ Ici A, 0 ≤ u y)
    (ha2 : ∀ y ∈ Ici A, k ^ 2 * u y ≤ a2 y)
    (hdec : Tendsto u atTop (𝓝 0)) :
    ∀ y ∈ Ici A, u y ≤ u A * Real.exp (-k * (y - A)) := by
  have hb := decaying_ode_barrier hk hu hv hu0 ha2 hdec
  have hd (y : ℝ) (hy : y ∈ Ici A) : HasDerivAt (fun t => Real.exp (k * t) * u t)
      (Real.exp (k * y) * (v y + k * u y)) y := by
    convert (((hasDerivAt_id y).const_mul k).exp).mul (hu y hy) using 1 <;> try rfl
    simp only [id_eq]
    ring
  have hanti : AntitoneOn (fun t => Real.exp (k * t) * u t) (Ici A) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici A)
    · intro y hy; exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy; exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hb y (interior_subset hy))
  intro y hy
  have hh := hanti (show A ∈ Ici A by simp) hy hy
  have he : Real.exp (-k * (y - A)) = Real.exp (k * A) / Real.exp (k * y) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he, ← mul_div_assoc, le_div_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hh

/-- The actual source cusp mass has an explicit exponential upper bound. -/
theorem mass_exponential_decay (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : cutoff N ≤ y) :
    mass N f y ≤ mass N f (cutoff N) * Real.exp (-rate N * (y - cutoff N)) := by
  apply decaying_ode_exponential (rate_pos N)
    (u := mass N f) (v := deriv (mass N f))
    (a2 := deriv (deriv (mass N f))) ?_ ?_ ?_ ?_ (mass_decay N f) y hy
  · intro t ht
    exact (mass_hasDerivAt N f ((cutoff_pos N).trans_le ht)).differentiableAt.hasDerivAt
  · intro t ht
    exact (mass_second_hasDerivAt N f ((cutoff_pos N).trans_le ht)).differentiableAt.hasDerivAt
  · intro t ht; exact mass_nonneg N f ((cutoff_pos N).trans_le ht)
  · intro t ht; exact mass_second_lower N lam f ht

private theorem decaying_convex_deriv_decay {u v a2 : ℝ → ℝ} {A : ℝ}
    (hu : ∀ y ∈ Ici A, HasDerivAt u (v y) y)
    (hv : ∀ y ∈ Ici A, HasDerivAt v (a2 y) y)
    (hu0 : ∀ y ∈ Ici A, 0 ≤ u y)
    (ha2 : ∀ y ∈ Ici A, 0 ≤ a2 y)
    (hdec : Tendsto u atTop (𝓝 0)) : Tendsto v atTop (𝓝 0) := by
  have hv0 := decaying_convex_deriv_nonpos hu hv ha2 hdec
  have hmono : MonotoneOn v (Ici A) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici A)
    · intro y hy; exact (hv y hy).continuousAt.continuousWithinAt
    · intro y hy; exact (hv y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy; rw [(hv y (interior_subset hy)).deriv]; exact ha2 y (interior_subset hy)
  have ht : Tendsto (fun y : ℝ => y - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1) tendsto_id
  have hvlim : Tendsto (fun y => -v y) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (hdec.comp ht)
    · filter_upwards [eventually_ge_atTop A] with y hy
      exact neg_nonneg.mpr (hv0 y hy)
    · filter_upwards [eventually_ge_atTop (A + 1)] with y hy
      have hAy : A ≤ y := by linarith
      have hsub := (convex_Icc (y - 1) y).image_sub_le_mul_sub_of_deriv_le
        (f := u)
        (by intro s hs
            have hAs : A ≤ s := by linarith [hs.1]
            exact (hu s hAs).continuousAt.continuousWithinAt)
        (by intro s hs
            have hss : s ∈ Icc (y - 1) y := interior_subset hs
            have hAs : A ≤ s := by linarith [hss.1]
            exact (hu s hAs).differentiableAt.differentiableWithinAt)
        (C := v y)
        (by intro s hs
            have hss : s ∈ Icc (y - 1) y := interior_subset hs
            have hAs : A ≤ s := by linarith [hss.1]
            rw [(hu s hAs).deriv]
            exact hmono hAs hAy hss.2)
        (y - 1) (by constructor <;> linarith) y (by constructor <;> linarith) (by linarith)
      change -v y ≤ u (y - 1)
      nlinarith [hu0 y hAy]
  simpa only [neg_neg, neg_zero] using hvlim.neg

/-- Backward secants and convexity force the actual mass derivative to zero. -/
theorem mass_deriv_decay (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    Tendsto (deriv (mass N f)) atTop (𝓝 0) := by
  apply decaying_convex_deriv_decay (A := cutoff N) (u := mass N f)
    (v := deriv (mass N f)) (a2 := deriv (deriv (mass N f))) ?_ ?_ ?_ ?_ (mass_decay N f)
  · intro t ht
    exact (mass_hasDerivAt N f ((cutoff_pos N).trans_le ht)).differentiableAt.hasDerivAt
  · intro t ht
    exact (mass_second_hasDerivAt N f ((cutoff_pos N).trans_le ht)).differentiableAt.hasDerivAt
  · intro t ht; exact mass_nonneg N f ((cutoff_pos N).trans_le ht)
  · intro t ht
    exact (mul_nonneg (sq_nonneg (rate N)) (mass_nonneg N f ((cutoff_pos N).trans_le ht))).trans
      (mass_second_lower N lam f ht)

/-- The actual outgoing Maass mass flux vanishes at infinite height. -/
theorem flux_decay (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    Tendsto (flux N f) atTop (𝓝 0) := by
  have h : Tendsto (fun y => deriv (mass N f) y / 2) atTop (𝓝 0) := by
    simpa using (mass_deriv_decay N lam f).div_const 2
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [(mass_hasDerivAt N f hy).deriv]
  ring

/-- Above the frequency cutoff, the actual outgoing mass flux is nonpositive.
The cusp ODE makes the mass convex while its terminal value vanishes, so its
derivative, hence half the flux, cannot be positive. -/
theorem flux_nonpos (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : cutoff N ≤ y) :
    flux N f y ≤ 0 := by
  have hderiv := decaying_convex_deriv_nonpos (A := cutoff N) (u := mass N f)
    (v := deriv (mass N f)) (a2 := deriv (deriv (mass N f)))
    (fun t ht => (mass_hasDerivAt N f ((cutoff_pos N).trans_le ht)).differentiableAt.hasDerivAt)
    (fun t ht => (mass_second_hasDerivAt N f ((cutoff_pos N).trans_le ht)).differentiableAt.hasDerivAt)
    (fun t ht =>
      (mul_nonneg (sq_nonneg (rate N))
        (mass_nonneg N f ((cutoff_pos N).trans_le ht))).trans
        (mass_second_lower N lam f ht))
    (mass_decay N f)
  have hm : deriv (mass N f) y ≤ 0 := hderiv y hy
  rw [(mass_hasDerivAt N f ((cutoff_pos N).trans_le hy)).deriv] at hm
  linarith

/-- Above the cutoff, actual flux growth dominates a fixed positive multiple of mass. -/
theorem flux_deriv_lower (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : cutoff N ≤ y) :
    rate N ^ 2 / 2 * mass N f y ≤ deriv (flux N f) y := by
  have hp := (cutoff_pos N).trans_le hy
  have h := mass_second_lower N lam f hy
  rw [(mass_second_hasDerivAt N f hp).deriv, (flux_hasDerivAt N f hp).deriv] at *
  linarith

open MeasureTheory

/-- The source flux derivative is integrable on the infinite tail. -/
theorem flux_deriv_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    IntegrableOn (deriv (flux N f)) (Ioi (cutoff N)) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := flux N f) ?_ ?_ (flux_decay N lam f)
  · intro y hy
    exact (flux_hasDerivAt N f ((cutoff_pos N).trans_le hy)).differentiableAt.hasDerivAt
  · intro y hy
    exact (mul_nonneg (by positivity : 0 ≤ rate N ^ 2 / 2)
      (mass_nonneg N f ((cutoff_pos N).trans hy))).trans (flux_deriv_lower N lam f hy.le)

/-- Infinite-height flux balance with its terminal value proved to vanish. -/
theorem flux_integral (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ∫ y in Ioi (cutoff N), deriv (flux N f) y = -flux N f (cutoff N) := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => (flux_hasDerivAt N f ((cutoff_pos N).trans_le hy)).differentiableAt.hasDerivAt)
    (flux_deriv_integrable N lam f) (flux_decay N lam f)

end
end GaloisForLFunctions.RHTower.SelbergMaassCuspDecay
