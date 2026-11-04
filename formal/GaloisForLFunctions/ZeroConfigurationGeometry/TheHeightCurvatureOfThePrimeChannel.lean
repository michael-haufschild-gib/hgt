import GaloisForLFunctions.ZeroConfigurationGeometry.TheArithmeticPinningIsStable

/-!
# The height curvature of the prime channel

Moving the camera to height `T` (`modulate T`) multiplies the kernel `k = f ⋆ g̃` by `e^{−iTs}`
(`weilTest_modulate`). The prime channel of the explicit formula,
`P_λ(k) = Σ_n λ(n) n^{−1/2} (k(log n) + k(−log n))` (`primeChannel`), then becomes a Dirichlet
polynomial in `T` of length `e^{2r}` (`primeChannel_modulate`).

* **The coalescent channel is the height curvature** (`deriv_deriv_primeChannel_modulate`). The
  second derivative in `T` of the prime channel at height `T` is minus the prime channel of
  `s² k_T(s)`: the prime sum weighted by `(log n)²`.

By `TheSquaredGapIsReadAtSecondOrder`, a near-collision at height `T` is imaged as the doubled
centre plus `w²` times the height curvature of the image. Through the explicit formula, the
curvature of the image splits into the pole and archimedean curvatures and this
`(log n)²`-weighted prime sum. The sign of `w²` (real or tilted) is therefore carried by the
`(log n)²`-weighted primes below `e^{2r}`: the coalescent channel of the field, as an exact
identity.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-- The prime channel `Σ_n λ(n) n^{−1/2} (k(log n) + k(−log n))` of the explicit formula. -/
def primeChannel (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((primeWeight lam n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))

/-- **Moving the camera to height `T` modulates the kernel.** -/
theorem weilTest_modulate (T : ℝ) (f g : ℝ → ℂ) (s : ℝ) :
    EF.weilTest (modulate T f) (modulate T g) s = cexp (-(I * T * s)) * EF.weilTest f g s := by
  rw [_root_.RHTower.weilTest_apply, _root_.RHTower.weilTest_apply, ← integral_const_mul]
  congr 1 with t
  simp only [modulate, map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, conj_ofReal]
  rw [show cexp (-(-I * (T : ℂ) * ((t - s : ℝ) : ℂ))) = cexp (-(I * T * s)) * cexp (I * T * t) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]
  rw [show f t * cexp (-(I * T * t)) * (conj (g (t - s)) * (cexp (-(I * T * s)) * cexp (I * T * t))) =
    cexp (-(I * T * s)) * (f t * conj (g (t - s))) * (cexp (-(I * T * t)) * cexp (I * T * t)) by ring,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The prime channel of a kernel supported in `[−2r, 2r]` is a finite sum over `n ≤ e^{2r}`. -/
theorem primeChannel_eq_sum (lam : ℕ → ℝ) {k : ℝ → ℂ} {r : ℝ}
    (hk : ∀ s, 2 * r < |s| → k s = 0) :
    primeChannel lam k =
      ∑ n ∈ primeRange r, ((primeWeight lam n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) :=
  tsum_eq_sum fun n hn => by
    have h := two_mul_lt_log_of_not_mem_primeRange hn
    rw [hk _ h, hk _ (by rwa [abs_neg]), add_zero, mul_zero]

/-- **At height `T` the prime channel is a Dirichlet polynomial of length `e^{2r}`.** -/
theorem primeChannel_modulate (lam : ℕ → ℝ) {f g : ℝ → ℂ} {r : ℝ} (hf : ApertureWindow r f)
    (hg : ApertureWindow r g) (T : ℝ) :
    primeChannel lam (EF.weilTest (modulate T f) (modulate T g)) =
      ∑ n ∈ primeRange r, ((primeWeight lam n : ℝ) : ℂ) *
        (cexp (-(I * Real.log n) * T) * EF.weilTest f g (Real.log n) +
          cexp (I * Real.log n * T) * EF.weilTest f g (-Real.log n)) := by
  have hfs : tsupport (modulate T f) ⊆ Icc (-r) r := (tsupport_modulate_subset T f).trans hf.2
  have hgs : tsupport (modulate T g) ⊆ Icc (-r) r := (tsupport_modulate_subset T g).trans hg.2
  rw [primeChannel_eq_sum lam (fun s hs => weilTest_eq_zero_of_lt hfs hgs hs)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [weilTest_modulate, weilTest_modulate]
  push_cast
  ring_nf

/-- **The coalescent channel is the height curvature of the prime channel.** -/
theorem deriv_deriv_primeChannel_modulate (lam : ℕ → ℝ) {f g : ℝ → ℂ} {r : ℝ}
    (hf : ApertureWindow r f) (hg : ApertureWindow r g) (T : ℝ) :
    deriv (deriv fun T : ℝ => primeChannel lam (EF.weilTest (modulate T f) (modulate T g))) T =
      -∑ n ∈ primeRange r, ((primeWeight lam n : ℝ) : ℂ) * ((Real.log n : ℂ) ^ 2 *
        (cexp (-(I * Real.log n) * T) * EF.weilTest f g (Real.log n) +
          cexp (I * Real.log n * T) * EF.weilTest f g (-Real.log n))) := by
  have hF : (fun T : ℝ => primeChannel lam (EF.weilTest (modulate T f) (modulate T g))) =
      fun x : ℝ => ∑ n ∈ primeRange r, ((primeWeight lam n : ℝ) : ℂ) *
        (cexp (-(I * Real.log n) * x) * EF.weilTest f g (Real.log n) +
          cexp (I * Real.log n * x) * EF.weilTest f g (-Real.log n)) :=
    funext fun x => primeChannel_modulate lam hf hg x
  have hexp : ∀ a : ℂ, ∀ x : ℝ, HasDerivAt (fun T : ℝ => cexp (a * T)) (a * cexp (a * x)) x :=
    fun a x => by
      have h := (((hasDerivAt_id (x : ℂ)).const_mul a).cexp).comp_ofReal
      simp only [id, mul_one] at h
      exact h.congr_deriv (mul_comm _ _)
  -- a two-exponential term differentiates by its frequencies
  have hterm : ∀ (c a p q : ℂ) (x : ℝ), HasDerivAt
      (fun T : ℝ => c * (cexp (-a * T) * p + cexp (a * T) * q))
      (c * (-a * cexp (-a * x) * p + a * cexp (a * x) * q)) x := fun c a p q x =>
    (((hexp (-a) x).mul_const p).add ((hexp a x).mul_const q)).const_mul c
  have hterm2 : ∀ (c a p q : ℂ) (x : ℝ), HasDerivAt
      (fun T : ℝ => c * (-a * cexp (-a * T) * p + a * cexp (a * T) * q))
      (c * (-a * (-a) * cexp (-a * x) * p + a * a * cexp (a * x) * q)) x :=
    fun c a p q x => by
      have := ((((hexp (-a) x).const_mul (-a)).mul_const p).add
        (((hexp a x).const_mul a).mul_const q)).const_mul c
      exact this.congr_deriv (by ring)
  have hd1 : deriv (fun x : ℝ => ∑ n ∈ primeRange r, ((primeWeight lam n : ℝ) : ℂ) *
        (cexp (-(I * Real.log n) * x) * EF.weilTest f g (Real.log n) +
          cexp (I * Real.log n * x) * EF.weilTest f g (-Real.log n))) =
      fun x : ℝ => ∑ n ∈ primeRange r, ((primeWeight lam n : ℝ) : ℂ) *
        (-(I * Real.log n) * cexp (-(I * Real.log n) * x) * EF.weilTest f g (Real.log n) +
          I * Real.log n * cexp (I * Real.log n * x) * EF.weilTest f g (-Real.log n)) :=
    funext fun x => (HasDerivAt.fun_sum (u := primeRange r) fun (n : ℕ) _ =>
      hterm ((primeWeight lam n : ℝ) : ℂ) (I * ((Real.log n : ℝ) : ℂ))
        (EF.weilTest f g (Real.log n)) (EF.weilTest f g (-Real.log n)) x).deriv
  rw [hF, hd1]
  refine ((HasDerivAt.fun_sum (u := primeRange r) fun (n : ℕ) _ =>
    hterm2 ((primeWeight lam n : ℝ) : ℂ) (I * ((Real.log n : ℝ) : ℂ))
      (EF.weilTest f g (Real.log n)) (EF.weilTest f g (-Real.log n)) T).deriv).trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((primeWeight lam n : ℝ) : ℂ) * (Real.log n : ℂ) ^ 2 *
    (cexp (-(I * Real.log n) * T) * EF.weilTest f g (Real.log n) +
      cexp (I * Real.log n * T) * EF.weilTest f g (-Real.log n)) * hI

end GaloisForLFunctions.ZeroConfigurationGeometry
