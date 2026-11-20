import GaloisForLFunctions.BlackHoleRingdown.PassiveTwinEchoAndFiniteTimeDistinction
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PrimePowerReturnsForceSignedCancellation
import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.ThePositiveEulerTwinsHaveNoRealZero

/-!
# Classification of Degree-One Rational Prime Gates on the Pure Modular Bounce and Integral-Trace Degree-Two Slow Modes

Once the global cusp worldline fixes the single-bounce transform to `B(w, 1/2) = Γ_ℝ(2w)/Γ_ℝ(2w+1)`,
local rational prime deformations separate sharply by degree:

1. **Exact Dichotomy of Passive Unitary Degree-One Rational Prime Gates
   (`degree_one_rational_prime_gate_classification`, `finite_prime_degree_one_gate_classification`)**:
   Replacing `primeEchoGate p w = (p - v) / (p (1 - v))` (`v = p^{-2w}`) at finitely many primes
   `p ∈ S` by any degree-`≤ 1` rational function `(c₀ + c₁ v) / (d₀ + d₁ v)` whose local ratio to
   `primeEchoGate p` is continuous and contractive on `‖v‖ ≤ 1` (`Re w ≥ 0`) with unitary product
   on `Re w = 0` forces `d₁ = -d₀` (`d₀ ≠ 0`) and, at each prime `p ∈ S`, either:
   - the trivial branch `u_p * primeEchoGate p w` (`‖u_p‖ = 1`), or
   - the **flipped degree-one integral branch** `u_p * (1 - p · p^{-2w}) / (p (1 - p^{-2w}))`
     (`u_p ∈ {-1, 1}` for real or integer coefficients).

2. **Causal Flipped Horizon and Exact Pulse-by-Pulse Ringdown Equivalence
   (`flippedEchoKernel`, `finiteFlippedReflected_decay_iff`, `finiteFlipped_strip_and_rh_equivalence`)**:
   Every flipped gate ratio `(1 - p · p^{-2w}) / (p - p^{-2w})` has poles strictly on
   `Re w = -1/2 < -1/4`, zeros strictly on `Re w = +1/2`, a causal retarded echo kernel
   `flippedEchoKernel p`, an entire `s ↦ 1 - s` symmetric completion, global Schur passivity,
   Herglotz positivity, and imaginary-axis unitarity. Both the forward and inverse time-domain
   operators have absolutely convergent geometric shift expansions on `‖v‖ = 1`, giving
   **pulse-by-pulse** `O(e^{-σ τ})` equivalence with `pulseReflected h` for every `0 ≤ σ < 1/2`,
   unconditional decay below `3001 / 48000`, and quarter-rate decay iff `RiemannHypothesis`.

3. **Sharpness of Degree One via Integral-Trace Degree-Two Slow Modes for All `p ≥ 5`
   (`no_integral_slow_trace_two_or_three`, `integral_trace_degree_two_slow_mode_of_ge_five`)**:
   While `(2√p, p + 1) ∩ ℤ = ∅` for `p ∈ {2, 3}`, every integer `p ≥ 5` (in particular every prime
   `p ≥ 5`) admits `r + u = p ∈ ℤ` with `1 < u < r` and `r * u = p`, yielding a pure-bounce causal,
   globally Schur-passive, Herglotz-positive, axis-unitary, FE-symmetric horizon with integer local
   Euler coefficients that unconditionally violates quarter-rate decay `δ = 1/4`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology Finset
open scoped ContDiff FourierTransform Classical BigOperators

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ExclusionOfTheCriticalState (positiveEuler_completedXi_real_pos)

/-! ## 1. Classification of Passive Unitary Degree-One Rational Prime Gates -/

/-- Standard degree-one local prime gate `(p - v) / (p (1 - v))` in variable `v = p^{-2w}`. -/
def zetaLocalGate (p : ℕ) (v : ℂ) : ℂ :=
  ((p : ℂ) - v) / ((p : ℂ) * (1 - v))

/-- Flipped degree-one integral local prime gate `(1 - p v) / (p (1 - v))` in variable `v = p^{-2w}`. -/
def flippedLocalGate (p : ℕ) (v : ℂ) : ℂ :=
  (1 - (p : ℂ) * v) / ((p : ℂ) * (1 - v))

/-- Local scattering multiplier `(1 - p v) / (p - v) = flippedLocalGate p v / zetaLocalGate p v`. -/
def flippedGateRatio (p : ℕ) (v : ℂ) : ℂ :=
  (1 - (p : ℂ) * v) / ((p : ℂ) - v)

theorem zetaLocalGate_primeEchoGate (p : Nat.Primes) (w : ℂ) :
    zetaLocalGate p ((p : ℂ) ^ (-(2 * w))) = primeEchoGate p w := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  unfold zetaLocalGate primeEchoGate
  rw [show -(2 * w + 1) = -(2 * w) - 1 by ring, Complex.cpow_sub _ _ hpC, Complex.cpow_one]
  field_simp [hpC]

/-- **Single-Prime Degree-One Rational Gate Classification.**
Suppose `p ≥ 2`, `(d₀, d₁) ≠ (0, 0)`, and `M : ℂ → ℂ` is continuous on `{v | ‖v‖ ≤ 1}` with
`‖M v‖ = 1` on `‖v‖ = 1` and clears the rational ratio identity
`(p - v)(d₀ + d₁ v) M(v) = p(1 - v)(c₀ + c₁ v)` on `‖v‖ ≤ 1`.
Then `d₀ ≠ 0`, `d₁ = -d₀`, and there exists `u : ℂ` with `‖u‖ = 1` such that either:
- `c₀ = u * d₀` and `c₁ = -(u / p) * d₀` (`M v = u`, trivial branch `u * zetaLocalGate p`), or
- `c₀ = (u / p) * d₀` and `c₁ = -(u * d₀)` (`M v = u * flippedGateRatio p v`, flipped branch
  `u * flippedLocalGate p`). -/
theorem degree_one_rational_prime_gate_classification {p : ℕ} (hp2 : 2 ≤ p)
    {c₀ c₁ d₀ d₁ : ℂ} (hd_ne : d₀ ≠ 0 ∨ d₁ ≠ 0) {M : ℂ → ℂ}
    (hM_cont : ContinuousOn M {v : ℂ | ‖v‖ ≤ 1})
    (hM_eq : ∀ v : ℂ, ‖v‖ ≤ 1 →
      ((p : ℂ) - v) * (d₀ + d₁ * v) * M v = (p : ℂ) * (1 - v) * (c₀ + c₁ * v))
    (hM_unit : ∀ v : ℂ, ‖v‖ = 1 → ‖M v‖ = 1) :
    d₀ ≠ 0 ∧ d₁ = -d₀ ∧
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ((c₀ = u * d₀ ∧ c₁ = -(u / (p : ℂ)) * d₀ ∧
          (∀ v : ℂ, ‖v‖ ≤ 1 → M v = u) ∧
          (∀ v : ℂ, v ≠ 1 → (c₀ + c₁ * v) / (d₀ + d₁ * v) = u * zetaLocalGate p v)) ∨
       (c₀ = (u / (p : ℂ)) * d₀ ∧ c₁ = -(u * d₀) ∧
          (∀ v : ℂ, ‖v‖ ≤ 1 → M v = u * flippedGateRatio p v) ∧
          (∀ v : ℂ, v ≠ 1 → (c₀ + c₁ * v) / (d₀ + d₁ * v) = u * flippedLocalGate p v))) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hp1_ne : (p : ℂ) - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have h1_unit : ‖M 1‖ = 1 := hM_unit 1 norm_one
  have hM1_ne : M 1 ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1_unit; norm_num at h1_unit
  have hd_sum : d₀ + d₁ = 0 := by
    have hv1 := hM_eq 1 (by simp)
    simp only [mul_one, sub_self, mul_zero, zero_mul] at hv1
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hv1).resolve_right hM1_ne)).resolve_left hp1_ne
  have hd₁ : d₁ = -d₀ := eq_neg_of_add_eq_zero_right hd_sum
  have hd₀ : d₀ ≠ 0 := by
    rcases hd_ne with h | h
    · exact h
    · exact fun h0 => h (by rw [hd₁, h0, neg_zero])
  set a : ℂ := (p : ℂ) * c₀ / d₀
  set b : ℂ := (p : ℂ) * c₁ / d₀
  have hpv_ne : ∀ {v : ℂ}, ‖v‖ ≤ 1 → (p : ℂ) - v ≠ 0 := by
    intro v hv h0
    have hv_eq : v = (p : ℂ) := (sub_eq_zero.mp h0).symm
    rw [hv_eq, Complex.norm_natCast] at hv
    linarith
  have hM_form_ne1 : ∀ {v : ℂ}, ‖v‖ ≤ 1 → v ≠ 1 → M v = (a + b * v) / ((p : ℂ) - v) := by
    intro v hv hne1
    have h1v : 1 - v ≠ 0 := sub_ne_zero.mpr hne1.symm
    have hdv : d₀ + d₁ * v = d₀ * (1 - v) := by rw [hd₁]; ring
    have heq := hM_eq v hv
    rw [hdv] at heq
    have hcancel : ((p : ℂ) - v) * d₀ * M v = (p : ℂ) * (c₀ + c₁ * v) := by
      apply mul_right_cancel₀ h1v
      linear_combination heq
    rw [eq_div_iff (hpv_ne hv)]
    apply mul_left_cancel₀ hd₀
    calc d₀ * (M v * ((p : ℂ) - v))
        = ((p : ℂ) - v) * d₀ * M v := by ring
      _ = (p : ℂ) * (c₀ + c₁ * v) := hcancel
      _ = d₀ * (a + b * v) := by
          dsimp only [a, b]
          field_simp [hd₀]
  have hM_form : ∀ v : ℂ, ‖v‖ ≤ 1 → M v = (a + b * v) / ((p : ℂ) - v) := by
    intro v hv
    by_cases hne1 : v = 1
    · subst hne1
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr
          fun n => by simp only [Function.comp_apply, one_div]; congr 1; push_cast; ring
      have h1_real : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub h0
      have htend_r : Tendsto (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 1) := by
        have hc := Complex.continuous_ofReal.continuousAt (x := (1 : ℝ)).tendsto.comp h1_real
        rw [Complex.ofReal_one] at hc
        exact hc.congr fun _ => rfl
      have hmem_D : ∀ n : ℕ, ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) ∈ {z : ℂ | ‖z‖ ≤ 1} := by
        intro n
        show ‖((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have hle1 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
        have hgt0 : 0 < 1 / ((n : ℝ) + 2) := one_div_pos.mpr hpos
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hne_1 : ∀ n : ℕ, ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) ≠ 1 := by
        intro n h
        have hr : (1 : ℝ) - 1 / ((n : ℝ) + 2) = 1 :=
          Complex.ofReal_injective (by simpa using h)
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
      have hM_lim : Tendsto (fun n : ℕ => M ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ))
          atTop (𝓝 (M 1)) :=
        (hM_cont 1 (by simp)).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
          _ htend_r (Eventually.of_forall hmem_D))
      have hR_cont : ContinuousAt (fun z : ℂ => (a + b * z) / ((p : ℂ) - z)) 1 :=
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
          (continuousAt_const.sub continuousAt_id) hp1_ne
      have hR_lim : Tendsto (fun n : ℕ =>
          (a + b * ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) /
            ((p : ℂ) - ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)))
          atTop (𝓝 ((a + b * 1) / ((p : ℂ) - 1))) :=
        hR_cont.tendsto.comp htend_r
      have heq_seq : (fun n : ℕ => M ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) =
          fun n : ℕ => (a + b * ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) /
            ((p : ℂ) - ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) :=
        funext fun n => hM_form_ne1 (hmem_D n) (hne_1 n)
      rw [heq_seq] at hM_lim
      exact tendsto_nhds_unique hM_lim hR_lim
    · exact hM_form_ne1 hv hne1
  have hnormSq_circle : ∀ {v : ℂ}, ‖v‖ = 1 →
      Complex.normSq (a + b * v) = Complex.normSq ((p : ℂ) - v) := by
    intro v hv
    have hu := hM_unit v hv
    rw [hM_form v hv.le, norm_div] at hu
    have hd_pos : 0 < ‖(p : ℂ) - v‖ := norm_pos_iff.mpr (hpv_ne hv.le)
    have hnorm_eq : ‖a + b * v‖ = ‖(p : ℂ) - v‖ := (div_eq_one_iff_eq hd_pos.ne').mp hu
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hnorm_eq]
  have hv_one := hnormSq_circle norm_one
  have hv_neg := hnormSq_circle (by simp : ‖(-1 : ℂ)‖ = 1)
  have hv_I := hnormSq_circle Complex.norm_I
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im] at hv_one hv_neg hv_I
  set A : ℝ := a.re ^ 2 + a.im ^ 2
  set B : ℝ := b.re ^ 2 + b.im ^ 2
  set X : ℝ := a.re * b.re + a.im * b.im
  set Y : ℝ := a.im * b.re - a.re * b.im
  have hAB : A + B = (p : ℝ) ^ 2 + 1 := by linear_combination (hv_one + hv_neg) / 2
  have hX : X = -(p : ℝ) := by linear_combination (hv_one - hv_neg) / 4
  have hY : Y = 0 := by linear_combination (hv_I - hAB) / 2
  have hbrahma : A * B = X ^ 2 + Y ^ 2 := by dsimp only [A, B, X, Y]; ring
  have hquad : (B - 1) * (B - (p : ℝ) ^ 2) = 0 := by
    have hp2_eq : A * B = (p : ℝ) ^ 2 := by rw [hbrahma, hX, hY]; ring
    linear_combination B * hAB - hp2_eq
  refine ⟨hd₀, hd₁, ?_⟩
  rcases mul_eq_zero.mp hquad with hB1 | hBp2
  · have hB_eq : B = 1 := sub_eq_zero.mp hB1
    have hnormSq_rel : Complex.normSq (a + (p : ℂ) * b) = 0 := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im]
      have hA_eq : A = (p : ℝ) ^ 2 := by linarith [hAB, hB_eq]
      dsimp only [A, B, X] at hA_eq hB_eq hX
      linear_combination hA_eq + 2 * (p : ℝ) * hX + (p : ℝ) ^ 2 * hB_eq
    have hapb : a + (p : ℂ) * b = 0 := Complex.normSq_eq_zero.mp hnormSq_rel
    set u : ℂ := -b
    have hu_norm : ‖u‖ = 1 := by
      rw [norm_neg, ← Real.sqrt_sq (norm_nonneg b), ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      have hsq : b.re * b.re + b.im * b.im = 1 := by dsimp only [B] at hB_eq; linear_combination hB_eq
      rw [hsq, Real.sqrt_one]
    have hb_eq : b = -u := by simp [u]
    have ha_eq : a = (p : ℂ) * u := by linear_combination hapb
    have hc₀_eq : c₀ = u * d₀ := by
      have : (p : ℂ) * c₀ = a * d₀ := (div_mul_cancel₀ _ hd₀).symm
      apply mul_left_cancel₀ hp0
      rw [this, ha_eq]; ring
    have hc₁_eq : c₁ = -(u / (p : ℂ)) * d₀ := by
      have : (p : ℂ) * c₁ = b * d₀ := (div_mul_cancel₀ _ hd₀).symm
      apply mul_left_cancel₀ hp0
      rw [this, hb_eq]
      field_simp [hp0]
    refine ⟨u, hu_norm, Or.inl ⟨hc₀_eq, hc₁_eq, ?_, ?_⟩⟩
    · intro v hv
      rw [hM_form v hv, ha_eq, hb_eq]
      have hnum : (p : ℂ) * u + -u * v = u * ((p : ℂ) - v) := by ring
      rw [hnum, mul_div_cancel_right₀ _ (hpv_ne hv)]
    · intro v hv1
      have h1v : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
      have hd_prod : d₀ + -d₀ * v ≠ 0 := by
        rw [show d₀ + -d₀ * v = d₀ * (1 - v) by ring]
        exact mul_ne_zero hd₀ h1v
      rw [hc₀_eq, hc₁_eq, hd₁, zetaLocalGate, mul_div_assoc',
        div_eq_div_iff hd_prod (mul_ne_zero hp0 h1v)]
      field_simp [hp0]
      ring
  · have hB_eq : B = (p : ℝ) ^ 2 := sub_eq_zero.mp hBp2
    have hA_eq : A = 1 := by linarith [hAB, hB_eq]
    have hnormSq_rel : Complex.normSq ((p : ℂ) * a + b) = 0 := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.natCast_re, Complex.natCast_im]
      dsimp only [A, B, X] at hA_eq hB_eq hX
      linear_combination (p : ℝ) ^ 2 * hA_eq + 2 * (p : ℝ) * hX + hB_eq
    have hpab : (p : ℂ) * a + b = 0 := Complex.normSq_eq_zero.mp hnormSq_rel
    set u : ℂ := a
    have hu_norm : ‖u‖ = 1 := by
      rw [← Real.sqrt_sq (norm_nonneg a), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hsq : a.re * a.re + a.im * a.im = 1 := by dsimp only [A] at hA_eq; linear_combination hA_eq
      rw [hsq, Real.sqrt_one]
    have hb_eq : b = -((p : ℂ) * u) := by linear_combination hpab
    have hc₀_eq : c₀ = (u / (p : ℂ)) * d₀ := by
      have : (p : ℂ) * c₀ = a * d₀ := (div_mul_cancel₀ _ hd₀).symm
      apply mul_left_cancel₀ hp0
      rw [this]
      dsimp only [u]
      field_simp [hp0]
    have hc₁_eq : c₁ = -(u * d₀) := by
      have : (p : ℂ) * c₁ = b * d₀ := (div_mul_cancel₀ _ hd₀).symm
      apply mul_left_cancel₀ hp0
      rw [this, hb_eq]; ring
    refine ⟨u, hu_norm, Or.inr ⟨hc₀_eq, hc₁_eq, ?_, ?_⟩⟩
    · intro v hv
      rw [hM_form v hv, hb_eq, flippedGateRatio]
      dsimp only [u]
      have hnum : a + -((p : ℂ) * a) * v = a * (1 - (p : ℂ) * v) := by ring
      rw [hnum, mul_div_assoc]
    · intro v hv1
      have h1v : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
      have hd_prod : d₀ + -d₀ * v ≠ 0 := by
        rw [show d₀ + -d₀ * v = d₀ * (1 - v) by ring]
        exact mul_ne_zero hd₀ h1v
      rw [hc₀_eq, hc₁_eq, hd₁, flippedLocalGate, mul_div_assoc',
        div_eq_div_iff hd_prod (mul_ne_zero hp0 h1v)]
      field_simp [hp0]
      ring

/-- Real/integral specialization: when `c₀, c₁, d₀, d₁` are real (in particular integers), the unit
scalar `u` lies in `{-1, 1}`. -/
theorem degree_one_real_prime_gate_classification {p : ℕ} (hp2 : 2 ≤ p)
    {c₀ c₁ d₀ d₁ : ℝ} (hd_ne : d₀ ≠ 0 ∨ d₁ ≠ 0) {M : ℂ → ℂ}
    (hM_cont : ContinuousOn M {v : ℂ | ‖v‖ ≤ 1})
    (hM_eq : ∀ v : ℂ, ‖v‖ ≤ 1 →
      ((p : ℂ) - v) * ((d₀ : ℂ) + (d₁ : ℂ) * v) * M v =
        (p : ℂ) * (1 - v) * ((c₀ : ℂ) + (c₁ : ℂ) * v))
    (hM_unit : ∀ v : ℂ, ‖v‖ = 1 → ‖M v‖ = 1) :
    d₀ ≠ 0 ∧ d₁ = -d₀ ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ((∀ v : ℂ, v ≠ 1 → ((c₀ : ℂ) + (c₁ : ℂ) * v) / ((d₀ : ℂ) + (d₁ : ℂ) * v) =
          (ε : ℂ) * zetaLocalGate p v) ∨
       (∀ v : ℂ, v ≠ 1 → ((c₀ : ℂ) + (c₁ : ℂ) * v) / ((d₀ : ℂ) + (d₁ : ℂ) * v) =
          (ε : ℂ) * flippedLocalGate p v)) := by
  have hd_neC : (d₀ : ℂ) ≠ 0 ∨ (d₁ : ℂ) ≠ 0 := by
    rcases hd_ne with h | h
    · exact Or.inl (Complex.ofReal_ne_zero.mpr h)
    · exact Or.inr (Complex.ofReal_ne_zero.mpr h)
  obtain ⟨hd₀C, hd₁C, u, hu_norm, hbranch⟩ :=
    degree_one_rational_prime_gate_classification hp2 hd_neC hM_cont hM_eq hM_unit
  have hd₀ : d₀ ≠ 0 := Complex.ofReal_ne_zero.mp hd₀C
  have hd₁ : d₁ = -d₀ := by
    apply Complex.ofReal_injective
    simpa using hd₁C
  refine ⟨hd₀, hd₁, ?_⟩
  rcases hbranch with ⟨hc₀, _, _, hrat⟩ | ⟨hc₀, _, _, hrat⟩
  · have hu_im : u.im = 0 := by
      have him := congrArg Complex.im hc₀
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add] at him
      exact (mul_eq_zero.mp him.symm).resolve_right hd₀
    have hu_eq : u = (u.re : ℂ) := Complex.ext rfl hu_im
    have habs : |u.re| = 1 := by
      rw [hu_eq, Complex.norm_real, Real.norm_eq_abs] at hu_norm
      exact hu_norm
    refine ⟨u.re, (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs, Or.inl ?_⟩
    simpa [← hu_eq] using hrat
  · have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hu_im : u.im = 0 := by
      have hc₀' : (c₀ : ℂ) * (p : ℂ) = u * (d₀ : ℂ) := by
        rw [hc₀]
        have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
        field_simp [hpC]
      have him := congrArg Complex.im hc₀'
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
        Complex.natCast_im, mul_zero, zero_mul, add_zero, zero_add] at him
      exact (mul_eq_zero.mp him.symm).resolve_right hd₀
    have hu_eq : u = (u.re : ℂ) := Complex.ext rfl hu_im
    have habs : |u.re| = 1 := by
      rw [hu_eq, Complex.norm_real, Real.norm_eq_abs] at hu_norm
      exact hu_norm
    refine ⟨u.re, (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs, Or.inr ?_⟩
    simpa [← hu_eq] using hrat

private theorem norm_finset_prod (S : Finset ℕ) (g : ℕ → ℂ) :
    ‖∏ p ∈ S, g p‖ = ∏ p ∈ S, ‖g p‖ := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S' hp ih => rw [Finset.prod_insert hp, Finset.prod_insert hp, norm_mul, ih]

private theorem norm_eq_one_of_prod_eq_one {S : Finset ℕ} {f : ℕ → ℝ}
    (hf0 : ∀ p ∈ S, 0 ≤ f p) (hf1 : ∀ p ∈ S, f p ≤ 1) (hprod : ∏ p ∈ S, f p = 1) :
    ∀ p ∈ S, f p = 1 := by
  intro p hp
  by_contra hne
  have hlt : f p < 1 := lt_of_le_of_ne (hf1 p hp) hne
  have hrest_le : ∏ q ∈ S.erase p, f q ≤ 1 :=
    Finset.prod_le_one (fun q hq => hf0 q (mem_of_mem_erase hq))
      (fun q hq => hf1 q (mem_of_mem_erase hq))
  have hrest_nn : 0 ≤ ∏ q ∈ S.erase p, f q :=
    Finset.prod_nonneg fun q hq => hf0 q (mem_of_mem_erase hq)
  have hsplit := (Finset.mul_prod_erase S f hp).symm
  rw [hprod] at hsplit
  have hle_fp : f p * ∏ q ∈ S.erase p, f q ≤ f p := mul_le_of_le_one_right (hf0 p hp) hrest_le
  linarith

private theorem exists_imag_axis_prime_coord {p : ℕ} (hp2 : 2 ≤ p) {v : ℂ} (hv : ‖v‖ = 1) :
    ∃ t : ℝ, (p : ℂ) ^ (-(2 * ((t : ℂ) * I))) = v := by
  have hp1 : (1 : ℝ) < p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  set θ : ℝ := Complex.arg v
  set t : ℝ := -θ / (2 * Real.log p)
  refine ⟨t, ?_⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  have hexp' : (((Real.log (p : ℕ) : ℝ) : ℂ) * -(2 * ((t : ℂ) * I))) = (θ : ℂ) * I := by
    dsimp only [t]
    have hlC : ((Real.log (p : ℕ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
    rw [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp [hlC]
  rw [hexp']
  have hv_polar := Complex.norm_mul_exp_arg_mul_I v
  rwa [hv, Complex.ofReal_one, one_mul] at hv_polar

/-- **Multi-Prime Finite-Family Degree-One Classification.**
If finitely many primes `S` carry locally passive degree-one rational gates whose combined
scattering product is unitary on the imaginary axis, then every prime `p ∈ S` is individually
unitary on `‖v‖ = 1` and belongs to `{u_p * zetaLocalGate p, u_p * flippedLocalGate p}`. -/
theorem finite_prime_degree_one_gate_classification (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {c₀ c₁ d₀ d₁ : ℕ → ℂ} (hd_ne : ∀ p ∈ S, d₀ p ≠ 0 ∨ d₁ p ≠ 0)
    {M : ℕ → ℂ → ℂ}
    (hM_cont : ∀ p ∈ S, ContinuousOn (M p) {v : ℂ | ‖v‖ ≤ 1})
    (hM_passive : ∀ p ∈ S, ∀ v : ℂ, ‖v‖ ≤ 1 → ‖M p v‖ ≤ 1)
    (hM_eq : ∀ p ∈ S, ∀ v : ℂ, ‖v‖ ≤ 1 →
      ((p : ℂ) - v) * (d₀ p + d₁ p * v) * M p v = (p : ℂ) * (1 - v) * (c₀ p + c₁ p * v))
    (h_unit : ∀ t : ℝ, ‖∏ p ∈ S, M p ((p : ℂ) ^ (-(2 * ((t : ℂ) * I))))‖ = 1) :
    ∀ p ∈ S, d₀ p ≠ 0 ∧ d₁ p = -d₀ p ∧
      ∃ u : ℂ, ‖u‖ = 1 ∧
        ((∀ v : ℂ, v ≠ 1 → (c₀ p + c₁ p * v) / (d₀ p + d₁ p * v) = u * zetaLocalGate p v) ∨
         (∀ v : ℂ, v ≠ 1 → (c₀ p + c₁ p * v) / (d₀ p + d₁ p * v) = u * flippedLocalGate p v)) := by
  intro p hp
  have hp_prime := hS p hp
  have hunit_p : ∀ v : ℂ, ‖v‖ = 1 → ‖M p v‖ = 1 := by
    intro v hv
    obtain ⟨t, ht⟩ := exists_imag_axis_prime_coord hp_prime.two_le hv
    have hprod_norm : ∏ q ∈ S, ‖M q ((q : ℂ) ^ (-(2 * ((t : ℂ) * I))))‖ = 1 := by
      rw [← norm_finset_prod S, h_unit t]
    have hle1 : ∀ q ∈ S, ‖M q ((q : ℂ) ^ (-(2 * ((t : ℂ) * I))))‖ ≤ 1 := by
      intro q hq
      refine hM_passive q hq _ ?_
      rw [Complex.norm_natCast_cpow_of_pos (hS q hq).pos]
      simp
    have h1 := norm_eq_one_of_prod_eq_one (fun _ _ => norm_nonneg _) hle1 hprod_norm p hp
    rwa [ht] at h1
  obtain ⟨hd₀, hd₁, u, hu, hbr⟩ := degree_one_rational_prime_gate_classification
    hp_prime.two_le (hd_ne p hp) (hM_cont p hp) (hM_eq p hp) hunit_p
  refine ⟨hd₀, hd₁, u, hu, ?_⟩
  rcases hbr with ⟨_, _, _, h1⟩ | ⟨_, _, _, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

/-! ## 2. Causal Flipped Horizon and Exact Pulse-by-Pulse Ringdown Equivalence -/

theorem flippedGateRatio_schur_and_unitary {p : ℕ} (hp2 : 2 ≤ p) :
    (∀ v : ℂ, ‖v‖ < p → (p : ℂ) - v ≠ 0) ∧
    (∀ v : ℂ, ‖v‖ ≤ 1 → ‖flippedGateRatio p v‖ ≤ 1) ∧
    (∀ v : ℂ, ‖v‖ = 1 → ‖flippedGateRatio p v‖ = 1 ∧
      flippedGateRatio p v * flippedGateRatio p v⁻¹ = 1) ∧
    (∀ v : ℂ, ‖v‖ < p →
      HasSum (fun k : ℕ => -((((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2) : ℝ) : ℂ) * v ^ (k + 1))
        (flippedGateRatio p v - 1 / (p : ℂ))) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp2_sub : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hden_ne : ∀ v : ℂ, ‖v‖ < p → (p : ℂ) - v ≠ 0 := by
    intro v hv h0
    have heq : v = (p : ℂ) := (sub_eq_zero.mp h0).symm
    rw [heq, Complex.norm_natCast] at hv
    exact lt_irrefl _ hv
  have hnormSq_diff : ∀ v : ℂ,
      Complex.normSq ((p : ℂ) - v) - Complex.normSq (1 - (p : ℂ) * v) =
        ((p : ℝ) ^ 2 - 1) * (1 - Complex.normSq v) := by
    intro v
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.natCast_re, Complex.natCast_im]
    ring
  refine ⟨hden_ne, ?_, ?_, ?_⟩
  · intro v hv
    have hv_lt : ‖v‖ < p := hv.trans_lt (by linarith)
    have hd_pos : 0 < ‖(p : ℂ) - v‖ := norm_pos_iff.mpr (hden_ne v hv_lt)
    rw [flippedGateRatio, norm_div, div_le_one hd_pos]
    have hv2 : Complex.normSq v ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg v]
    have hdiff_nn : 0 ≤ Complex.normSq ((p : ℂ) - v) - Complex.normSq (1 - (p : ℂ) * v) := by
      rw [hnormSq_diff v]
      exact mul_nonneg hp2_sub (by linarith)
    have hsq_le : ‖1 - (p : ℂ) * v‖ ^ 2 ≤ ‖(p : ℂ) - v‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
    nlinarith [norm_nonneg (1 - (p : ℂ) * v)]
  · intro v hv
    have hv_lt : ‖v‖ < p := by rw [hv]; linarith
    have hv0 : v ≠ 0 := fun h0 => by rw [h0, norm_zero] at hv; norm_num at hv
    have hv_inv_lt : ‖v⁻¹‖ < p := by rw [norm_inv, hv, inv_one]; linarith
    have hd1 := hden_ne v hv_lt
    have hd2 := hden_ne v⁻¹ hv_inv_lt
    refine ⟨?_, ?_⟩
    · have hd_pos : 0 < ‖(p : ℂ) - v‖ := norm_pos_iff.mpr hd1
      rw [flippedGateRatio, norm_div, div_eq_one_iff_eq hd_pos.ne']
      have hv2 : Complex.normSq v = 1 := by rw [Complex.normSq_eq_norm_sq, hv, one_pow]
      have hdiff0 : Complex.normSq ((p : ℂ) - v) - Complex.normSq (1 - (p : ℂ) * v) = 0 := by
        rw [hnormSq_diff v, hv2, sub_self, mul_zero]
      have hsq_eq : ‖1 - (p : ℂ) * v‖ ^ 2 = ‖(p : ℂ) - v‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq_eq
    · rw [flippedGateRatio, flippedGateRatio, div_mul_div_comm,
        div_eq_one_iff_eq (mul_ne_zero hd1 hd2)]
      field_simp [hv0]
      ring
  · intro v hv
    have hvp_lt : ‖v / (p : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_natCast]
      exact (div_lt_one hp_pos).mpr hv
    have hgeom := (hasSum_geometric_of_norm_lt_one hvp_lt).mul_left
      (-((((p : ℂ) ^ 2 - 1) / (p : ℂ) ^ 2) * v))
    have hterm : (fun k : ℕ =>
        -((((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2) : ℝ) : ℂ) * v ^ (k + 1)) =
        fun k : ℕ => (-((((p : ℂ) ^ 2 - 1) / (p : ℂ) ^ 2) * v)) * (v / (p : ℂ)) ^ k := by
      funext k
      push_cast
      rw [div_pow, pow_add, pow_succ]
      field_simp [hpC]
      ring
    have hval_eq : (-((((p : ℂ) ^ 2 - 1) / (p : ℂ) ^ 2) * v)) * (1 - v / (p : ℂ))⁻¹ =
        flippedGateRatio p v - 1 / (p : ℂ) := by
      have h1_sub : 1 - v / (p : ℂ) ≠ 0 := sub_ne_zero.mpr fun h => by
        rw [← h, norm_one] at hvp_lt; exact lt_irrefl _ hvp_lt
      have hd := hden_ne v hv
      rw [flippedGateRatio]
      field_simp [hpC, h1_sub, hd]
      ring
    rwa [← hterm, hval_eq] at hgeom

/-- Retarded time-domain echo kernel of the single-prime flipped degree-one integral gate. -/
def flippedEchoKernel (p : ℕ) (τ : ℝ) : ℝ :=
  (1 / (p : ℝ)) * echoKernel τ -
    ∑' k : ℕ, (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2)) *
      echoKernel (τ - 2 * ((k : ℝ) + 1) * Real.log p)

/-- Entire self-dual completion `p^{s - 1/2} (1 - p^{1 - s})(1 - p^{-s}) ξ(s)` of the flipped
degree-one integral gate at prime `p`. -/
def xiFlipped (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (s - 1 / 2) * (1 - (p : ℂ) ^ (1 - s)) * (1 - (p : ℂ) ^ (-s)) * xi s

/-- Strict causality and exact Laplace/Euler-product representation of `flippedEchoKernel p`. -/
theorem flippedEchoKernel_causal_and_laplace {p : ℕ} (hp : p.Prime) :
    (∀ τ : ℝ, τ ≤ 0 → flippedEchoKernel p τ = 0) ∧
    Differentiable ℂ (xiFlipped p) ∧
    (∀ s : ℂ, xiFlipped p (1 - s) = xiFlipped p s) ∧
    (∀ w : ℂ, 1 / 2 < w.re →
      (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((flippedEchoKernel p τ : ℝ) : ℂ)) =
        flippedGateRatio p ((p : ℂ) ^ (-(2 * w))) *
          (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) ∧
      HasProd (fun q : Nat.Primes =>
          if (q : ℕ) = p then flippedLocalGate p ((p : ℂ) ^ (-(2 * w))) else primeEchoGate q w)
        (flippedGateRatio p ((p : ℂ) ^ (-(2 * w))) *
          (riemannZeta (2 * w) / riemannZeta (2 * w + 1)))) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hp2_sub : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlog_nn : 0 ≤ Real.log p := (Real.log_pos hp1).le
  have hcpow_exp : ∀ z : ℂ, (p : ℂ) ^ z = Complex.exp (z * ((Real.log p : ℝ) : ℂ)) := by
    intro z
    rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ hτ
    rw [flippedEchoKernel, echoKernel_eq_zero_of_nonpos hτ, mul_zero, zero_sub, neg_eq_zero]
    have h0 : ∀ k : ℕ, (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2)) *
        echoKernel (τ - 2 * ((k : ℝ) + 1) * Real.log p) = 0 := fun k => by
      have hd_nn : 0 ≤ 2 * ((k : ℝ) + 1) * Real.log p := by positivity
      rw [echoKernel_eq_zero_of_nonpos (by linarith), mul_zero]
    simp [h0]
  · unfold xiFlipped
    have hd_cpow : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → Differentiable ℂ (fun s => (p : ℂ) ^ f s) := by
      intro f hf
      have heq : (fun s => (p : ℂ) ^ f s) = fun s => Complex.exp (f s * ((Real.log p : ℝ) : ℂ)) :=
        funext fun s => hcpow_exp (f s)
      rw [heq]; exact (hf.mul_const _).cexp
    exact (((hd_cpow (by fun_prop)).mul ((differentiable_const 1).sub (hd_cpow (by fun_prop)))).mul
      ((differentiable_const 1).sub (hd_cpow (by fun_prop)))).mul xi_differentiable
  · intro s
    set L : ℂ := ((Real.log p : ℝ) : ℂ)
    have hexpand : ∀ z : ℂ, (p : ℂ) ^ (z - 1 / 2) * (1 - (p : ℂ) ^ (1 - z)) * (1 - (p : ℂ) ^ (-z)) =
        Complex.exp ((z - 1 / 2) * L) + Complex.exp ((1 / 2 - z) * L) -
          Complex.exp ((1 / 2 : ℂ) * L) - Complex.exp (-(1 / 2 : ℂ) * L) := by
      intro z
      simp only [hcpow_exp]
      have e1 : Complex.exp ((z - 1 / 2) * L) * Complex.exp ((1 - z) * L) =
          Complex.exp ((1 / 2 : ℂ) * L) := by rw [← Complex.exp_add]; congr 1; ring
      have e2 : Complex.exp ((z - 1 / 2) * L) * Complex.exp (-z * L) =
          Complex.exp (-(1 / 2 : ℂ) * L) := by rw [← Complex.exp_add]; congr 1; ring
      have e3 : Complex.exp ((1 / 2 : ℂ) * L) * Complex.exp (-z * L) =
          Complex.exp ((1 / 2 - z) * L) := by rw [← Complex.exp_add]; congr 1; ring
      calc Complex.exp ((z - 1 / 2) * L) * (1 - Complex.exp ((1 - z) * L)) *
              (1 - Complex.exp (-z * L))
          = (Complex.exp ((z - 1 / 2) * L) -
              Complex.exp ((z - 1 / 2) * L) * Complex.exp ((1 - z) * L)) *
            (1 - Complex.exp (-z * L)) := by ring
        _ = (Complex.exp ((z - 1 / 2) * L) - Complex.exp ((1 / 2 : ℂ) * L)) *
            (1 - Complex.exp (-z * L)) := by rw [e1]
        _ = Complex.exp ((z - 1 / 2) * L) -
              Complex.exp ((z - 1 / 2) * L) * Complex.exp (-z * L) -
              Complex.exp ((1 / 2 : ℂ) * L) +
              Complex.exp ((1 / 2 : ℂ) * L) * Complex.exp (-z * L) := by ring
        _ = _ := by rw [e2, e3]; ring
    unfold xiFlipped
    rw [hexpand (1 - s), hexpand s, xi_one_sub]
    have h1 : (1 - s - 1 / 2) * L = (1 / 2 - s) * L := by ring
    have h2 : (1 / 2 - (1 - s)) * L = (s - 1 / 2) * L := by ring
    rw [h1, h2]; ring
  · intro w hw
    set v : ℂ := (p : ℂ) ^ (-(2 * w))
    have hv_norm : ‖v‖ < 1 := by
      dsimp only [v]
      rw [Complex.norm_natCast_cpow_of_pos hp.pos, show (-(2 * w)).re = -2 * w.re by simp]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hv_lt_p : ‖v‖ < p := hv_norm.trans (by linarith)
    obtain ⟨hden_ne, _, _, hser⟩ := flippedGateRatio_schur_and_unitary hp2
    refine ⟨?_, ?_⟩
    · set Kw : ℝ → ℂ := fun u => Complex.exp (-w * (u : ℂ)) * ((echoKernel u : ℝ) : ℂ)
      have hKw_int : Integrable Kw := integrable_cexp_mul_echoKernel hw
      have hKw_val : ∫ u : ℝ, Kw u = completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1) :=
        integral_cexp_mul_echoKernel_eq_completed hw
      set d : ℕ → ℝ := fun k => 2 * ((k : ℝ) + 1) * Real.log p
      set c : ℕ → ℝ := fun k => ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2)
      have hc_nn : ∀ k, 0 ≤ c k := fun k => div_nonneg hp2_sub (pow_nonneg hp_pos.le _)
      set G : ℕ → ℝ → ℂ := fun k τ =>
        ((c k : ℝ) : ℂ) * Complex.exp (-w * ((d k : ℝ) : ℂ)) * Kw (τ - d k)
      have hG_eq : ∀ k τ, G k τ = Complex.exp (-w * (τ : ℂ)) *
          (((c k * echoKernel (τ - d k) : ℝ)) : ℂ) := by
        intro k τ
        dsimp only [G, Kw]
        have hexp : Complex.exp (-w * ((d k : ℝ) : ℂ)) * Complex.exp (-w * ((τ - d k : ℝ) : ℂ)) =
            Complex.exp (-w * (τ : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; rw [Complex.ofReal_sub]; ring
        calc ((c k : ℝ) : ℂ) * Complex.exp (-w * ((d k : ℝ) : ℂ)) *
                (Complex.exp (-w * ((τ - d k : ℝ) : ℂ)) * ((echoKernel (τ - d k) : ℝ) : ℂ))
            = (Complex.exp (-w * ((d k : ℝ) : ℂ)) * Complex.exp (-w * ((τ - d k : ℝ) : ℂ))) *
                (((c k : ℝ) : ℂ) * ((echoKernel (τ - d k) : ℝ) : ℂ)) := by ring
          _ = Complex.exp (-w * (τ : ℂ)) * (((c k * echoKernel (τ - d k) : ℝ)) : ℂ) := by
                rw [hexp, Complex.ofReal_mul]
      have hG_int : ∀ k, Integrable (G k) := fun k =>
        (hKw_int.comp_sub_right (d k)).const_mul _
      have hc_sum : Summable c := by
        have hgeom : Summable fun k : ℕ => (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2) * ((p : ℝ)⁻¹) ^ k :=
          (summable_geometric_of_lt_one (inv_nonneg.mpr hp_pos.le) (inv_lt_one_of_one_lt₀ hp1)).mul_left _
        refine hgeom.congr fun k => ?_
        dsimp only [c]; rw [inv_pow, pow_add]; field_simp [hp_pos.ne']
      have hG_norm : Summable fun k => ∫ τ, ‖G k τ‖ := by
        refine (hc_sum.mul_right (∫ u, ‖Kw u‖)).of_nonneg_of_le
          (fun _ => integral_nonneg fun _ => norm_nonneg _) fun k => ?_
        have hpt : ∀ τ, ‖G k τ‖ = ‖((c k : ℝ) : ℂ) * Complex.exp (-w * ((d k : ℝ) : ℂ))‖ *
            ‖Kw (τ - d k)‖ := fun _ => norm_mul _ _
        simp_rw [hpt]
        rw [integral_const_mul, integral_sub_right_eq_self (fun u => ‖Kw u‖) (d k)]
        refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => norm_nonneg _)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc_nn k),
          Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
        have hd_nn : 0 ≤ d k := by dsimp [d]; positivity
        exact mul_le_of_le_one_right (hc_nn k) (Real.exp_le_one_iff.mpr (by nlinarith))
      have hG_tsum_int : Integrable fun τ => ∑' k, G k τ :=
        HTGeometry.integrable_tsum_of_summable_integral_norm hG_int hG_norm
      have hHS := hasSum_integral_of_summable_integral_norm hG_int hG_norm
      have hpt_ker : ∀ τ : ℝ,
          Complex.exp (-w * (τ : ℂ)) * ((flippedEchoKernel p τ : ℝ) : ℂ) =
            (1 / (p : ℂ)) * Kw τ - ∑' k, G k τ := by
        intro τ
        unfold flippedEchoKernel
        rw [Complex.ofReal_sub, mul_sub, Complex.ofReal_mul,
          show Complex.exp (-w * (τ : ℂ)) * (((1 / (p : ℝ) : ℝ) : ℂ) * ((echoKernel τ : ℝ) : ℂ)) =
            (1 / (p : ℂ)) * Kw τ by simp [Kw]; ring]
        congr 1
        rw [Complex.ofReal_tsum, ← tsum_mul_left]
        exact tsum_congr fun k => (hG_eq k τ).symm
      simp_rw [hpt_ker]
      rw [integral_sub (hKw_int.const_mul _) hG_tsum_int, integral_const_mul, ← hHS.tsum_eq]
      have hG_val : ∀ k : ℕ, ∫ τ, G k τ =
          (((c k : ℝ) : ℂ) * v ^ (k + 1)) * ∫ u, Kw u := by
        intro k
        dsimp only [G]
        rw [integral_const_mul, integral_sub_right_eq_self Kw (d k)]
        congr 2
        dsimp only [v, d]
        rw [hcpow_exp, ← Complex.exp_nat_mul]
        congr 1; push_cast; ring
      simp_rw [hG_val]
      have htsum_pos : (∑' k : ℕ, ((c k : ℝ) : ℂ) * v ^ (k + 1)) =
          1 / (p : ℂ) - flippedGateRatio p v := by
        have hts := (hser v hv_lt_p).tsum_eq
        simp only [neg_mul] at hts
        rw [tsum_neg] at hts
        dsimp only [c]
        linear_combination -hts
      rw [tsum_mul_right, htsum_pos, ← sub_mul, hKw_val]
      ring
    · set p₀ : Nat.Primes := ⟨p, hp⟩
      have hbase := hasProd_primeEchoGate hw
      have hsingle : HasProd (fun q : Nat.Primes =>
          if q = p₀ then flippedGateRatio p v else 1) (flippedGateRatio p v) :=
        hasProd_ite_eq p₀ (flippedGateRatio p v)
      refine (hsingle.mul hbase).congr_fun fun q => ?_
      by_cases hqp : q = p₀
      · subst hqp
        rw [if_pos (rfl : (p₀ : ℕ) = p), if_pos (rfl : p₀ = p₀), ← zetaLocalGate_primeEchoGate]
        change flippedLocalGate p v = flippedGateRatio p v * zetaLocalGate p v
        dsimp only [flippedGateRatio, zetaLocalGate, flippedLocalGate]
        have h1v : 1 - v ≠ 0 := sub_ne_zero.mpr fun h => by
          rw [← h, norm_one] at hv_norm; exact lt_irrefl _ hv_norm
        have hd := hden_ne v hv_lt_p
        field_simp [hpC, h1v, hd]
      · have hval : (q : ℕ) ≠ p := fun h => hqp (Subtype.ext h)
        simp [hqp, hval]

/-- Multi-prime flipped scattering multiplier `∏_{p ∈ S} ε p * flippedGateRatio p (p^{-2w})`. -/
def finiteFlippedMultiplier (S : Finset ℕ) (ε : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∏ p ∈ S, ε p * flippedGateRatio p ((p : ℂ) ^ (-(2 * w)))

/-- Reduced scattering operator of the `(S, ε)`-flipped pure-bounce horizon. -/
def finiteFlippedReducedScattering (S : Finset ℕ) (ε : ℕ → ℂ) (w : ℂ) : ℂ :=
  finiteFlippedMultiplier S ε w * (xi (2 * w) / xi (1 + 2 * w))

/-- Continuous-spectrum scattering phase of the `(S, ε)`-flipped pure-bounce horizon. -/
def finiteFlippedScatteringPhase (S : Finset ℕ) (ε : ℕ → ℂ) (w : ℂ) : ℂ :=
  finiteFlippedMultiplier S ε w * scatteringPhase w

/-- Reflected cusp wavepacket of the `(S, ε)`-flipped pure-bounce horizon. -/
def finiteFlippedReflected (S : Finset ℕ) (ε : ℕ → ℂ) (h : ℝ → ℂ) (T : ℝ) : ℂ :=
  unitaryReflected (fun ξ => finiteFlippedScatteringPhase S ε ((ξ : ℂ) * I)) h T

/-- **Global Schur Passivity, Herglotz Positivity, Axis Unitarity, and Half-Line Pole/Zero Rigidity
of `finiteFlippedMultiplier S ε`.** -/
theorem finiteFlipped_passive_unitary_and_strip_rigid (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℕ → ℂ} (hε : ∀ p ∈ S, ‖ε p‖ = 1) :
    (∀ w : ℂ, 0 ≤ w.re →
      ‖finiteFlippedReducedScattering S ε w‖ ≤ 1 ∧
      0 ≤ ((1 - finiteFlippedReducedScattering S ε w) /
        (1 + finiteFlippedReducedScattering S ε w)).re) ∧
    (∀ t : ℝ, ‖finiteFlippedScatteringPhase S ε ((t : ℂ) * I)‖ = 1) ∧
    (∀ w : ℂ, -(1 / 2 : ℝ) < w.re → w.re ≤ 0 → finiteFlippedMultiplier S ε w ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hmul_le : ‖finiteFlippedMultiplier S ε w‖ ≤ 1 := by
      rw [finiteFlippedMultiplier, norm_finset_prod S]
      refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun p hp => ?_
      rw [norm_mul, hε p hp, one_mul]
      have hp_prime := hS p hp
      have hv_le : ‖(p : ℂ) ^ (-(2 * w))‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp_prime.pos, show (-(2 * w)).re = -2 * w.re by simp]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp_prime.one_lt.le) (by linarith)
      exact (flippedGateRatio_schur_and_unitary hp_prime.two_le).2.1 _ hv_le
    have hxi_le : ‖xi (2 * w) / xi (1 + 2 * w)‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr (xi_shift_ne_zero hw))).mpr
        (norm_xi_two_mul_le_of_re_nonneg hw)
    have hred_le : ‖finiteFlippedReducedScattering S ε w‖ ≤ 1 := by
      rw [finiteFlippedReducedScattering, norm_mul]
      exact mul_le_one₀ hmul_le (norm_nonneg _) hxi_le
    refine ⟨hred_le, ?_⟩
    set z : ℂ := finiteFlippedReducedScattering S ε w
    by_cases hz1 : 1 + z = 0
    · rw [hz1, div_zero, Complex.zero_re]
    · rw [Complex.div_re, ← add_div]
      have hd_pos : 0 < Complex.normSq (1 + z) := Complex.normSq_pos.mpr hz1
      have hnum_nn : 0 ≤ (1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im := by
        have hsq : Complex.normSq z ≤ 1 := by
          rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
        rw [Complex.normSq_apply] at hsq
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.one_re, Complex.one_im]
        linarith
      exact div_nonneg hnum_nn hd_pos.le
  · intro t
    rw [finiteFlippedScatteringPhase, norm_mul, norm_scatteringPhase_line t, mul_one,
      finiteFlippedMultiplier, norm_finset_prod S]
    refine Finset.prod_eq_one fun p hp => ?_
    rw [norm_mul, hε p hp, one_mul]
    have hp_prime := hS p hp
    have hv1 : ‖(p : ℂ) ^ (-(2 * ((t : ℂ) * I)))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp_prime.pos]; simp
    exact ((flippedGateRatio_schur_and_unitary hp_prime.two_le).2.2.1 _ hv1).1
  · intro w hw_lo hw_hi
    rw [finiteFlippedMultiplier]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hp_prime := hS p hp
    have hε_ne : ε p ≠ 0 := fun h0 => by have := hε p hp; rw [h0, norm_zero] at this; norm_num at this
    refine mul_ne_zero hε_ne ?_
    set v : ℂ := (p : ℂ) ^ (-(2 * w))
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp_prime.one_lt
    have hpR2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
    have hv_norm : ‖v‖ = (p : ℝ) ^ (-2 * w.re) := by
      dsimp only [v]
      rw [Complex.norm_natCast_cpow_of_pos hp_prime.pos, show (-(2 * w)).re = -2 * w.re by simp]
    have hv_lt_p : ‖v‖ < p := by
      calc ‖v‖ = (p : ℝ) ^ (-2 * w.re) := hv_norm
        _ < (p : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
        _ = p := Real.rpow_one (p : ℝ)
    have hv_ge_1 : 1 ≤ ‖v‖ := by
      rw [hv_norm]
      exact Real.one_le_rpow hp1.le (by linarith)
    have hnum_ne : 1 - (p : ℂ) * v ≠ 0 := by
      intro h0
      have hpv : (p : ℂ) * v = 1 := (sub_eq_zero.mp h0).symm
      have hn := congrArg norm hpv
      rw [norm_mul, Complex.norm_natCast, norm_one] at hn
      have hge2 : (2 : ℝ) ≤ (p : ℝ) * ‖v‖ := by
        calc (2 : ℝ) = 2 * 1 := by ring
          _ ≤ (p : ℝ) * ‖v‖ := mul_le_mul hpR2 hv_ge_1 zero_le_one (by linarith)
      linarith [hn, hge2]
    exact div_ne_zero hnum_ne ((flippedGateRatio_schur_and_unitary hp_prime.two_le).1 v hv_lt_p)

/-! ### Exact Time-Domain Geometric Shift Equivalence for One Flipped Gate -/

private theorem singleFlipped_time_domain_identities {p : ℕ} (hp2 : 2 ≤ p)
    {ε₀ : ℂ} (hε₀ : ‖ε₀‖ = 1) {J : ℝ → ℂ} (hJ_meas : Measurable J) (hJ_le : ∀ ξ : ℝ, ‖J ξ‖ ≤ 1)
    (h : CompactPulse) (T : ℝ) :
    let J' : ℝ → ℂ := fun ξ => ε₀ * flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))) * J ξ
    unitaryReflected J' h T =
      ε₀ * ((1 / (p : ℂ)) * unitaryReflected J h T -
        ∑' k : ℕ, ((((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2) : ℝ) : ℂ) *
          unitaryReflected J h (T - 2 * ((k : ℝ) + 1) * Real.log p)) ∧
    unitaryReflected J h T =
      ε₀⁻¹ * ((1 / (p : ℂ)) * unitaryReflected J' h T -
        ∑' k : ℕ, ((((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2) : ℝ) : ℂ) *
          unitaryReflected J' h (T + 2 * ((k : ℝ) + 1) * Real.log p)) := by
  intro J'
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hp2_sub : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hε₀_ne : ε₀ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hε₀; norm_num at hε₀
  obtain ⟨hden_ne, _, hunit_v, hser⟩ := flippedGateRatio_schur_and_unitary hp2
  set c : ℕ → ℝ := fun k => ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2)
  set d : ℕ → ℝ := fun k => 2 * ((k : ℝ) + 1) * Real.log p
  have hc_nn : ∀ k, 0 ≤ c k := fun k => div_nonneg hp2_sub (pow_nonneg hp_pos.le _)
  have hc_sum : Summable c := by
    have hgeom : Summable fun k : ℕ => (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2) * ((p : ℝ)⁻¹) ^ k :=
      (summable_geometric_of_lt_one (inv_nonneg.mpr hp_pos.le) (inv_lt_one_of_one_lt₀ hp1)).mul_left _
    refine hgeom.congr fun k => ?_
    dsimp only [c]; rw [inv_pow, pow_add]; field_simp [hp_pos.ne']
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
    ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
  have hv_exp : ∀ ξ : ℝ, (p : ℂ) ^ (-(2 * ((ξ : ℂ) * I))) =
      Complex.exp (-(I * (ξ : ℂ) * ((2 * Real.log p : ℝ) : ℂ))) := by
    intro ξ
    rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log]
    congr 1; push_cast; ring
  have hv_norm1 : ∀ ξ : ℝ, ‖(p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))‖ = 1 := by
    intro ξ
    rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < p)]
    simp
  have hJ'_meas : Measurable J' := by
    refine (measurable_const.mul ?_).mul hJ_meas
    have hcont_r : Continuous fun ξ : ℝ => flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))) := by
      unfold flippedGateRatio
      have hcont_v : Continuous fun ξ : ℝ => (p : ℂ) ^ (-(2 * ((ξ : ℂ) * I))) := by
        simp_rw [hv_exp]; fun_prop
      exact (continuous_const.sub (continuous_const.mul hcont_v)).div
        (continuous_const.sub hcont_v) fun ξ => hden_ne _ (by rw [hv_norm1]; linarith)
    exact hcont_r.measurable
  have hJ'_le : ∀ ξ : ℝ, ‖J' ξ‖ ≤ 1 := by
    intro ξ
    dsimp only [J']
    rw [norm_mul, norm_mul, hε₀, (hunit_v _ (hv_norm1 ξ)).1, one_mul, one_mul]
    exact hJ_le ξ
  have hshift_fubini : ∀ {K : ℝ → ℂ} (hKm : Measurable K) (hKb : ∀ ξ : ℝ, ‖K ξ‖ ≤ 1) (sgn : ℝ),
      (∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * K ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
          ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp ((sgn : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) =
        ∑' k : ℕ, ((c k : ℝ) : ℂ) * unitaryReflected K h (T + sgn * d k) := by
    intro K hKm hKb sgn
    set F : ℕ → ℝ → ℂ := fun k (ξ : ℝ) => ((c k : ℝ) : ℂ) *
      (pulseAmplitude h (ξ : ℂ) * K ξ * Complex.exp (I * (ξ : ℂ) * ((T + sgn * d k : ℝ) : ℂ)))
    have hF_pt : ∀ (k : ℕ) (ξ : ℝ),
        pulseAmplitude h (ξ : ℂ) * K ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
          (((c k : ℝ) : ℂ) * Complex.exp ((sgn : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) =
        F k ξ := by
      intro k ξ
      dsimp only [F]
      have hexp : Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
          Complex.exp ((sgn : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) =
          Complex.exp (I * (ξ : ℂ) * ((T + sgn * d k : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      linear_combination ((c k : ℂ) * pulseAmplitude h (ξ : ℂ) * K ξ) * hexp
    have hF_int : ∀ k : ℕ, Integrable (F k) := fun k =>
      (h.integrable_amplitude_mul hKm hKb (T + sgn * d k)).const_mul _
    have hF_norm : Summable fun k : ℕ => ∫ ξ : ℝ, ‖F k ξ‖ := by
      refine (hc_sum.mul_right (∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖)).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _) fun k => ?_
      have hle_pt : ∀ ξ : ℝ, ‖F k ξ‖ ≤ c k * ‖pulseAmplitude h (ξ : ℂ)‖ := by
        intro ξ
        dsimp only [F]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc_nn k), norm_mul, norm_mul,
          norm_exp_I_mul, mul_one]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) (hKb ξ)) (hc_nn k)
      calc (∫ ξ : ℝ, ‖F k ξ‖)
          ≤ ∫ ξ : ℝ, c k * ‖pulseAmplitude h (ξ : ℂ)‖ :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (hint_a.const_mul (c k)) (Eventually.of_forall hle_pt)
        _ = c k * ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := integral_const_mul _ _
    have hHS := hasSum_integral_of_summable_integral_norm hF_int hF_norm
    have hcongr : (∫ ξ : ℝ, pulseAmplitude h (ξ : ℂ) * K ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
        ∑' k : ℕ, ((c k : ℝ) : ℂ) *
          Complex.exp ((sgn : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) =
        ∫ ξ : ℝ, ∑' k : ℕ, F k ξ := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      dsimp only
      rw [← tsum_mul_left]
      exact tsum_congr fun k => hF_pt k ξ
    rw [hcongr, ← hHS.tsum_eq]
    refine tsum_congr fun k => ?_
    dsimp only [F, unitaryReflected]
    exact integral_const_mul _ _
  refine ⟨?_, ?_⟩
  · have hf1 := hshift_fubini hJ_meas hJ_le (-1)
    have hint0 := h.integrable_amplitude_mul hJ_meas hJ_le T
    have hint1 := h.integrable_amplitude_mul hJ'_meas hJ'_le T
    have hser_neg : ∀ ξ : ℝ, flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))) =
        1 / (p : ℂ) - ∑' k : ℕ, ((c k : ℝ) : ℂ) *
          Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
      intro ξ
      have hts := (hser _ (by rw [hv_norm1 ξ]; linarith)).tsum_eq
      simp only [neg_mul] at hts
      rw [tsum_neg] at hts
      have hpow_rw : ∀ k : ℕ, (((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I))))) ^ (k + 1) =
          Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
        intro k
        rw [hv_exp, ← Complex.exp_nat_mul]
        dsimp only [d]; congr 1; push_cast; ring
      have hsum_eq : (∑' k : ℕ, ((((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2) : ℝ) : ℂ) *
            (((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I))))) ^ (k + 1)) =
          ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) :=
        tsum_congr fun k => by rw [hpow_rw k]
      rw [hsum_eq] at hts
      linear_combination -hts
    have hlhs : unitaryReflected J' h T =
        ε₀ * ∫ ξ : ℝ, (1 / (p : ℂ)) *
            (pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ))) -
          pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
            ∑' k : ℕ, ((c k : ℝ) : ℂ) *
              Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
      unfold unitaryReflected
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      dsimp only [J']
      rw [hser_neg ξ]; ring
    have hint_diff : Integrable fun ξ : ℝ =>
        pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
          ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
      have h1' : Integrable fun ξ : ℝ => ε₀⁻¹ *
          (pulseAmplitude h (ξ : ℂ) * J' ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ))) :=
        hint1.const_mul _
      refine ((hint0.const_mul (1 / (p : ℂ))).sub h1').congr (Eventually.of_forall fun ξ => ?_)
      simp only [Pi.sub_apply]
      dsimp only [J']
      rw [hser_neg ξ]
      have hcancel : ε₀⁻¹ * (pulseAmplitude h (ξ : ℂ) *
          (ε₀ * (1 / (p : ℂ) - ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) * J ξ) *
          Complex.exp (I * (ξ : ℂ) * (T : ℂ))) =
          (ε₀⁻¹ * ε₀) * (pulseAmplitude h (ξ : ℂ) *
            (1 / (p : ℂ) - ∑' k : ℕ, ((c k : ℝ) : ℂ) *
              Complex.exp (((-1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) * J ξ *
            Complex.exp (I * (ξ : ℂ) * (T : ℂ))) := by ring
      rw [hcancel, inv_mul_cancel₀ hε₀_ne, one_mul]
      ring
    rw [hlhs, integral_sub (hint0.const_mul _) hint_diff, integral_const_mul, hf1]
    simp only [neg_one_mul, ← sub_eq_add_neg, unitaryReflected, c, d]
  · have hf2 := hshift_fubini hJ'_meas hJ'_le 1
    have hint0 := h.integrable_amplitude_mul hJ_meas hJ_le T
    have hint1 := h.integrable_amplitude_mul hJ'_meas hJ'_le T
    have hser_pos : ∀ ξ : ℝ, (flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))))⁻¹ =
        1 / (p : ℂ) - ∑' k : ℕ, ((c k : ℝ) : ℂ) *
          Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
      intro ξ
      set v : ℂ := (p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))
      have hv1 : ‖v‖ = 1 := hv_norm1 ξ
      have hinv_eq : (flippedGateRatio p v)⁻¹ = flippedGateRatio p v⁻¹ :=
        inv_eq_of_mul_eq_one_right (hunit_v v hv1).2
      rw [hinv_eq]
      have hts := (hser v⁻¹ (by rw [norm_inv, hv1, inv_one]; linarith)).tsum_eq
      simp only [neg_mul] at hts
      rw [tsum_neg] at hts
      have hpow_rw : ∀ k : ℕ, (v⁻¹) ^ (k + 1) =
          Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
        intro k
        dsimp only [v]
        rw [hv_exp, ← Complex.exp_neg, ← Complex.exp_nat_mul]
        dsimp only [d]; congr 1; push_cast; ring
      have hsum_eq : (∑' k : ℕ, ((((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2) : ℝ) : ℂ) *
            (v⁻¹) ^ (k + 1)) =
          ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) :=
        tsum_congr fun k => by rw [hpow_rw k]
      rw [hsum_eq] at hts
      linear_combination -hts
    have hJ_recover : ∀ ξ : ℝ, J ξ = ε₀⁻¹ *
        (flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))))⁻¹ * J' ξ := by
      intro ξ
      set r : ℂ := flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I))))
      have hr_ne : r ≠ 0 := fun h0 => by
        have h1 : ‖r‖ = 1 := (hunit_v _ (hv_norm1 ξ)).1
        rw [h0, norm_zero] at h1; norm_num at h1
      calc J ξ = (ε₀⁻¹ * ε₀) * (r⁻¹ * r) * J ξ := by
              rw [inv_mul_cancel₀ hε₀_ne, inv_mul_cancel₀ hr_ne, one_mul, one_mul]
        _ = ε₀⁻¹ * r⁻¹ * J' ξ := by dsimp only [J', r]; ring
    have hlhs : unitaryReflected J h T =
        ε₀⁻¹ * ∫ ξ : ℝ, (1 / (p : ℂ)) *
            (pulseAmplitude h (ξ : ℂ) * J' ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ))) -
          pulseAmplitude h (ξ : ℂ) * J' ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
            ∑' k : ℕ, ((c k : ℝ) : ℂ) *
              Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
      unfold unitaryReflected
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      dsimp only
      rw [hJ_recover ξ, hser_pos ξ]; ring
    have hint_diff : Integrable fun ξ : ℝ =>
        pulseAmplitude h (ξ : ℂ) * J' ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ)) *
          ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ))) := by
      have h1' : Integrable fun ξ : ℝ => ε₀ *
          (pulseAmplitude h (ξ : ℂ) * J ξ * Complex.exp (I * (ξ : ℂ) * (T : ℂ))) :=
        hint0.const_mul _
      refine ((hint1.const_mul (1 / (p : ℂ))).sub h1').congr (Eventually.of_forall fun ξ => ?_)
      simp only [Pi.sub_apply]
      rw [hJ_recover ξ, hser_pos ξ]
      have hcancel : ε₀ * (pulseAmplitude h (ξ : ℂ) *
          (ε₀⁻¹ * (1 / (p : ℂ) - ∑' k : ℕ, ((c k : ℝ) : ℂ) *
            Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) * J' ξ) *
          Complex.exp (I * (ξ : ℂ) * (T : ℂ))) =
          (ε₀ * ε₀⁻¹) * (pulseAmplitude h (ξ : ℂ) *
            (1 / (p : ℂ) - ∑' k : ℕ, ((c k : ℝ) : ℂ) *
              Complex.exp (((1 : ℝ) : ℂ) * (I * (ξ : ℂ) * ((d k : ℝ) : ℂ)))) * J' ξ *
            Complex.exp (I * (ξ : ℂ) * (T : ℂ))) := by ring
      rw [hcancel, mul_inv_cancel₀ hε₀_ne, one_mul]
      ring
    rw [hlhs, integral_sub (hint1.const_mul _) hint_diff, integral_const_mul, hf2]
    simp only [one_mul, unitaryReflected, c, d]

private theorem unitaryReflected_uniform {J : ℝ → ℂ} (hJ_le : ∀ ξ : ℝ, ‖J ξ‖ ≤ 1)
    (h : CompactPulse) (T : ℝ) :
    ‖unitaryReflected J h T‖ ≤ ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖ := by
  have hint_a : Integrable fun ξ : ℝ => ‖pulseAmplitude h (ξ : ℂ)‖ :=
    ((h.integrable_amplitude_line 0).norm).congr (Eventually.of_forall fun _ => by simp)
  unfold unitaryReflected
  refine norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (hJ_le ξ)

private theorem weightedBound_iff_nonneg_decay {J : ℝ → ℂ} (hJ_le : ∀ ξ : ℝ, ‖J ξ‖ ≤ 1)
    (h : CompactPulse) {σ : ℝ} (hσ : 0 ≤ σ) :
    ReturnCancellation.weightedBound σ (unitaryReflected J h) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ‖unitaryReflected J h τ‖ ≤ C * Real.exp (-σ * τ) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max C 0, le_max_right _ _, fun τ _ => ?_⟩
    have hb := (hC τ).trans (le_max_left C 0)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hb
    exact (le_div_iff₀' (Real.exp_pos _)).mpr hb |>.trans_eq
      (by rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul])
  · rintro ⟨C, _, hC⟩
    set M : ℝ := ∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖
    refine ⟨max C M, fun u => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rcases le_or_gt 0 u with hu | hu
    · calc Real.exp (σ * u) * ‖unitaryReflected J h u‖
          ≤ Real.exp (σ * u) * (C * Real.exp (-σ * u)) :=
            mul_le_mul_of_nonneg_left (hC u hu) (Real.exp_pos _).le
        _ = C * Real.exp (σ * u + -σ * u) := by rw [mul_left_comm, ← Real.exp_add]
        _ = C := by simp
        _ ≤ max C M := le_max_left _ _
    · have hexp_le : Real.exp (σ * u) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hσ hu.le)
      exact ((mul_le_of_le_one_left (norm_nonneg _) hexp_le).trans
        (unitaryReflected_uniform hJ_le h u)).trans (le_max_right _ _)

/-- **Exact Pulse-by-Pulse Ringdown Equivalence of Any Finite Flipped Degree-One Horizon.**
For every finite set of primes `S`, unit phases `ε`, compact pulse `h`, and exponent `0 ≤ σ < 1/2`,
`finiteFlippedReflected S ε h` decays as `O(e^{-σ τ})` if and only if `pulseReflected h` decays
as `O(e^{-σ τ})`. -/
theorem finiteFlippedReflected_decay_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℕ → ℂ} (hε : ∀ p ∈ S, ‖ε p‖ = 1) (h : CompactPulse) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ_half : σ < 1 / 2) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      ‖finiteFlippedReflected S ε h τ‖ ≤ C * Real.exp (-σ * τ)) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      ‖pulseReflected h τ‖ ≤ C * Real.exp (-σ * τ)) := by
  suffices hwb : (Measurable fun ξ : ℝ => finiteFlippedScatteringPhase S ε ((ξ : ℂ) * I)) ∧
      (∀ ξ : ℝ, ‖finiteFlippedScatteringPhase S ε ((ξ : ℂ) * I)‖ ≤ 1) ∧
      (ReturnCancellation.weightedBound σ (finiteFlippedReflected S ε h) ↔
        ReturnCancellation.weightedBound σ (pulseReflected h)) by
    have hl := weightedBound_iff_nonneg_decay hwb.2.1 h hσ0
    have hr := weightedBound_iff_nonneg_decay (fun ξ => (norm_scatteringPhase_line ξ).le) h hσ0
    have hl_eq : unitaryReflected (fun ξ => finiteFlippedScatteringPhase S ε ((ξ : ℂ) * I)) h =
        finiteFlippedReflected S ε h := rfl
    have hr_eq : unitaryReflected (fun ξ => scatteringPhase ((ξ : ℂ) * I)) h =
        pulseReflected h := rfl
    rw [hl_eq] at hl
    rw [hr_eq] at hr
    exact hl.symm.trans (hwb.2.2.trans hr)
  induction S using Finset.induction_on with
  | empty =>
    have hph_eq : ∀ ξ : ℝ, finiteFlippedScatteringPhase ∅ ε ((ξ : ℂ) * I) =
        scatteringPhase ((ξ : ℂ) * I) := fun ξ => by
      simp [finiteFlippedScatteringPhase, finiteFlippedMultiplier]
    have href_eq : finiteFlippedReflected ∅ ε h = pulseReflected h := by
      funext T; simp [finiteFlippedReflected, hph_eq, unitaryReflected_modular_eq]
    exact ⟨by rw [funext hph_eq]; exact continuous_scatteringPhase_line.measurable,
      fun ξ => by rw [hph_eq ξ]; exact (norm_scatteringPhase_line ξ).le,
      by rw [href_eq]⟩
  | @insert p S' hp_notMem ih =>
    have hp : p.Prime := hS p (mem_insert_self p S')
    have hS' : ∀ q ∈ S', q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hε' : ∀ q ∈ S', ‖ε q‖ = 1 := fun q hq => hε q (mem_insert_of_mem hq)
    obtain ⟨hJm, hJb, hwb_ih⟩ := ih hS' hε'
    have hεp : ‖ε p‖ = 1 := hε p (mem_insert_self p S')
    set J : ℝ → ℂ := fun ξ => finiteFlippedScatteringPhase S' ε ((ξ : ℂ) * I)
    set J' : ℝ → ℂ := fun ξ => ε p * flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))) * J ξ
    have hJ'_pt : ∀ ξ : ℝ,
        finiteFlippedScatteringPhase (insert p S') ε ((ξ : ℂ) * I) = J' ξ := fun ξ => by
      simp [J', J, finiteFlippedScatteringPhase, finiteFlippedMultiplier,
        Finset.prod_insert hp_notMem, mul_assoc]
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp_pos : (0 : ℝ) < p := by linarith
    have hp1 : (1 : ℝ) < p := by linarith
    have hp2_sub : 0 ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    obtain ⟨hden_ne, _, hunit_v, _⟩ := flippedGateRatio_schur_and_unitary hp.two_le
    have hv_norm1 : ∀ ξ : ℝ, ‖(p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))‖ = 1 := by
      intro ξ; rw [Complex.norm_natCast_cpow_of_pos hp.pos]; simp
    have hJ'm : Measurable J' := by
      refine (measurable_const.mul ?_).mul hJm
      have hcont_r : Continuous fun ξ : ℝ => flippedGateRatio p ((p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))) := by
        unfold flippedGateRatio
        have hcont_v : Continuous fun ξ : ℝ => (p : ℂ) ^ (-(2 * ((ξ : ℂ) * I))) := by
          have hv_exp : (fun ξ : ℝ => (p : ℂ) ^ (-(2 * ((ξ : ℂ) * I)))) =
              fun ξ : ℝ => Complex.exp (-(I * (ξ : ℂ) * ((2 * Real.log p : ℝ) : ℂ))) := by
            funext ξ; rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log]; congr 1; push_cast; ring
          rw [hv_exp]; fun_prop
        exact (continuous_const.sub (continuous_const.mul hcont_v)).div
          (continuous_const.sub hcont_v) fun ξ => hden_ne _ (by rw [hv_norm1]; linarith)
      exact hcont_r.measurable
    have hJ'b : ∀ ξ : ℝ, ‖J' ξ‖ ≤ 1 := by
      intro ξ; dsimp only [J']
      rw [norm_mul, norm_mul, hεp, (hunit_v _ (hv_norm1 ξ)).1, one_mul, one_mul]
      exact hJb ξ
    refine ⟨by rw [funext hJ'_pt]; exact hJ'm,
      fun ξ => by rw [hJ'_pt ξ]; exact hJ'b ξ, ?_⟩
    rw [← hwb_ih]
    have href_eq : finiteFlippedReflected (insert p S') ε h = unitaryReflected J' h := by
      funext T; simp [finiteFlippedReflected, hJ'_pt]
    rw [href_eq]
    set c : ℕ → ℝ := fun k => ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ (k + 2)
    set d : ℕ → ℝ := fun k => 2 * ((k : ℝ) + 1) * Real.log p
    have hc_nn : ∀ k, 0 ≤ c k := fun k => div_nonneg hp2_sub (pow_nonneg hp_pos.le _)
    constructor
    · rintro ⟨C, hC⟩
      have hC_nn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      have hc_sum : Summable c := by
        have hgeom : Summable fun k : ℕ => (((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2) * ((p : ℝ)⁻¹) ^ k :=
          (summable_geometric_of_lt_one (inv_nonneg.mpr hp_pos.le) (inv_lt_one_of_one_lt₀ hp1)).mul_left _
        refine hgeom.congr fun k => ?_
        dsimp only [c]; rw [inv_pow, pow_add]; field_simp [hp_pos.ne']
      refine ⟨(1 / (p : ℝ) + ∑' k, c k) * C, fun T => ?_⟩
      have hid := (singleFlipped_time_domain_identities hp.two_le hεp hJm hJb h T).2
      change ‖(Real.exp (σ * T) : ℂ) * unitaryReflected J h T‖ ≤ _
      rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        norm_mul, norm_inv, hεp, inv_one, one_mul]
      have hterm_le : ∀ k : ℕ,
          Real.exp (σ * T) * ‖(((c k : ℝ) : ℂ)) * unitaryReflected J' h (T + d k)‖ ≤ c k * C := by
        intro k
        have hd_nn : 0 ≤ d k := by
          dsimp [d]; exact mul_nonneg (by positivity) (Real.log_pos hp1).le
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc_nn k)]
        have hexp_le : Real.exp (σ * T) ≤ Real.exp (σ * (T + d k)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hCk := hC (T + d k)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hCk
        calc Real.exp (σ * T) * (c k * ‖unitaryReflected J' h (T + d k)‖)
            = c k * (Real.exp (σ * T) * ‖unitaryReflected J' h (T + d k)‖) := by ring
          _ ≤ c k * (Real.exp (σ * (T + d k)) * ‖unitaryReflected J' h (T + d k)‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)) (hc_nn k)
          _ ≤ c k * C := mul_le_mul_of_nonneg_left hCk (hc_nn k)
      have hsum_n : Summable fun k : ℕ =>
          ‖(((c k : ℝ) : ℂ)) * unitaryReflected J' h (T + d k)‖ := by
        refine ((hc_sum.mul_right C).mul_left (Real.exp (-σ * T))).of_nonneg_of_le
          (fun _ => norm_nonneg _) fun k => ?_
        have h1' := mul_le_mul_of_nonneg_left (hterm_le k) (Real.exp_pos (-σ * T)).le
        rwa [← mul_assoc, ← Real.exp_add, show -σ * T + σ * T = 0 by ring, Real.exp_zero,
          one_mul] at h1'
      have hC0 := hC T
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hC0
      calc Real.exp (σ * T) *
              ‖(1 / (p : ℂ)) * unitaryReflected J' h T -
                ∑' k : ℕ, (((c k : ℝ) : ℂ)) * unitaryReflected J' h (T + d k)‖
          ≤ Real.exp (σ * T) * (‖(1 / (p : ℂ)) * unitaryReflected J' h T‖ +
              ∑' k : ℕ, ‖(((c k : ℝ) : ℂ)) * unitaryReflected J' h (T + d k)‖) :=
            mul_le_mul_of_nonneg_left
              ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_tsum_le_tsum_norm hsum_n)))
              (Real.exp_pos _).le
        _ = (1 / (p : ℝ)) * (Real.exp (σ * T) * ‖unitaryReflected J' h T‖) +
              ∑' k : ℕ, Real.exp (σ * T) *
                ‖(((c k : ℝ) : ℂ)) * unitaryReflected J' h (T + d k)‖ := by
            rw [mul_add, norm_mul, norm_div, norm_one, Complex.norm_natCast, tsum_mul_left]
            ring
        _ ≤ (1 / (p : ℝ)) * C + ∑' k : ℕ, c k * C :=
            add_le_add (mul_le_mul_of_nonneg_left hC0 (by positivity))
              (Summable.tsum_le_tsum hterm_le (hsum_n.mul_left _) (hc_sum.mul_right C))
        _ = (1 / (p : ℝ) + ∑' k, c k) * C := by rw [tsum_mul_right, add_mul]
    · rintro ⟨C, hC⟩
      have hC_nn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      set r : ℝ := (p : ℝ) ^ (2 * σ - 1)
      have hr_nn : 0 ≤ r := Real.rpow_nonneg hp_pos.le _
      have hr_lt1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
      set cw : ℕ → ℝ := fun k => c k * Real.exp (σ * d k)
      have hcw_nn : ∀ k, 0 ≤ cw k := fun k => mul_nonneg (hc_nn k) (Real.exp_pos _).le
      have hcw_eq : ∀ k : ℕ, cw k = (((p : ℝ) ^ 2 - 1) / (p : ℝ)) * r ^ (k + 1) := by
        intro k
        dsimp only [cw, c, d, r]
        have hexp_dk : Real.exp (σ * (2 * ((k : ℝ) + 1) * Real.log p)) =
            ((p : ℝ) ^ (2 * σ)) ^ (k + 1) := by
          rw [Real.rpow_def_of_pos hp_pos, ← Real.exp_nat_mul]
          congr 1; push_cast; ring
        have hr_pow : ((p : ℝ) ^ (2 * σ)) ^ (k + 1) / (p : ℝ) ^ (k + 1) =
            ((p : ℝ) ^ (2 * σ - 1)) ^ (k + 1) := by
          rw [← div_pow, ← Real.rpow_sub_one hp_pos.ne']
        rw [hexp_dk, show k + 2 = 1 + (k + 1) by omega, pow_add, pow_one]
        calc (((p : ℝ) ^ 2 - 1) / ((p : ℝ) * (p : ℝ) ^ (k + 1))) * ((p : ℝ) ^ (2 * σ)) ^ (k + 1)
            = (((p : ℝ) ^ 2 - 1) / (p : ℝ)) *
                (((p : ℝ) ^ (2 * σ)) ^ (k + 1) / (p : ℝ) ^ (k + 1)) := by ring
          _ = (((p : ℝ) ^ 2 - 1) / (p : ℝ)) * ((p : ℝ) ^ (2 * σ - 1)) ^ (k + 1) := by rw [hr_pow]
      have hcw_sum : Summable cw := by
        have hg : Summable fun k : ℕ => (((p : ℝ) ^ 2 - 1) / (p : ℝ) * r) * r ^ k :=
          (summable_geometric_of_lt_one hr_nn hr_lt1).mul_left _
        exact hg.congr fun k => by rw [hcw_eq, pow_succ']; ring
      refine ⟨(1 / (p : ℝ) + ∑' k, cw k) * C, fun T => ?_⟩
      have hid := (singleFlipped_time_domain_identities hp.two_le hεp hJm hJb h T).1
      change ‖(Real.exp (σ * T) : ℂ) * unitaryReflected J' h T‖ ≤ _
      rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        norm_mul, hεp, one_mul]
      have hterm_le : ∀ k : ℕ,
          Real.exp (σ * T) * ‖(((c k : ℝ) : ℂ)) * unitaryReflected J h (T - d k)‖ ≤ cw k * C := by
        intro k
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc_nn k)]
        have hexp_split : Real.exp (σ * T) = Real.exp (σ * d k) * Real.exp (σ * (T - d k)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hCk := hC (T - d k)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hCk
        calc Real.exp (σ * T) * (c k * ‖unitaryReflected J h (T - d k)‖)
            = cw k * (Real.exp (σ * (T - d k)) * ‖unitaryReflected J h (T - d k)‖) := by
              rw [hexp_split]; dsimp [cw]; ring
          _ ≤ cw k * C := mul_le_mul_of_nonneg_left hCk (hcw_nn k)
      have hsum_n : Summable fun k : ℕ =>
          ‖(((c k : ℝ) : ℂ)) * unitaryReflected J h (T - d k)‖ := by
        refine ((hcw_sum.mul_right C).mul_left (Real.exp (-σ * T))).of_nonneg_of_le
          (fun _ => norm_nonneg _) fun k => ?_
        have h1' := mul_le_mul_of_nonneg_left (hterm_le k) (Real.exp_pos (-σ * T)).le
        rwa [← mul_assoc, ← Real.exp_add, show -σ * T + σ * T = 0 by ring, Real.exp_zero,
          one_mul] at h1'
      have hC0 := hC T
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hC0
      calc Real.exp (σ * T) *
              ‖(1 / (p : ℂ)) * unitaryReflected J h T -
                ∑' k : ℕ, (((c k : ℝ) : ℂ)) * unitaryReflected J h (T - d k)‖
          ≤ Real.exp (σ * T) * (‖(1 / (p : ℂ)) * unitaryReflected J h T‖ +
              ∑' k : ℕ, ‖(((c k : ℝ) : ℂ)) * unitaryReflected J h (T - d k)‖) :=
            mul_le_mul_of_nonneg_left
              ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_tsum_le_tsum_norm hsum_n)))
              (Real.exp_pos _).le
        _ = (1 / (p : ℝ)) * (Real.exp (σ * T) * ‖unitaryReflected J h T‖) +
              ∑' k : ℕ, Real.exp (σ * T) *
                ‖(((c k : ℝ) : ℂ)) * unitaryReflected J h (T - d k)‖ := by
            rw [mul_add, norm_mul, norm_div, norm_one, Complex.norm_natCast, tsum_mul_left]
            ring
        _ ≤ (1 / (p : ℝ)) * C + ∑' k : ℕ, cw k * C :=
            add_le_add (mul_le_mul_of_nonneg_left hC0 (by positivity))
              (Summable.tsum_le_tsum hterm_le (hsum_n.mul_left _) (hcw_sum.mul_right C))
        _ = (1 / (p : ℝ) + ∑' k, cw k) * C := by rw [tsum_mul_right, add_mul]

/-- **Unconditional Sub-`3001/48000` Decay and Exact RH Equivalence on Every Flipped Degree-One Horizon.** -/
theorem finiteFlipped_strip_and_rh_equivalence (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {ε : ℕ → ℂ} (hε : ∀ p ∈ S, ‖ε p‖ = 1) :
    (∀ σ : ℝ, 0 < σ → σ < 3001 / 48000 → ∀ h : CompactPulse,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
        ‖finiteFlippedReflected S ε h τ‖ ≤ C * Real.exp (-σ * τ)) ∧
    (RiemannHypothesis ↔
      ∀ σ : ℝ, 0 < σ → σ < 1 / 4 → ∀ h : CompactPulse,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
          ‖finiteFlippedReflected S ε h τ‖ ≤ C * Real.exp (-σ * τ)) := by
  refine ⟨?_, ?_⟩
  · intro σ hσ0 hσ_top h
    obtain ⟨C, hC0, hdec, _⟩ := (unconditional_cusp_escape_sub_seven_eighths hσ0 hσ_top h).2
    exact (finiteFlippedReflected_decay_iff S hS hε h hσ0.le (by linarith)).mpr ⟨C, hC0, hdec⟩
  · have heq := zeroFreeStrip_tailEnergy_equivalences (δ := 1 / 4) (by norm_num) le_rfl
    have hrh : RiemannHypothesis ↔
        ∀ ε' : ℝ, 0 < ε' → ∀ h : CompactPulse,
          ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
            ‖pulseReflected h T‖ ≤ C * Real.exp (-((1 / 4 : ℝ) - ε') * T) :=
      (RingdownRate.riemannHypothesis_iff_pulse_ringdown.trans heq.1.symm).trans heq.2.1
    rw [hrh]
    constructor
    · intro H σ hσ0 hσ4 h
      obtain ⟨C, hC⟩ := H (1 / 4 - σ) (by linarith) h
      refine (finiteFlippedReflected_decay_iff S hS hε h hσ0.le (by linarith)).mpr
        ⟨max C 0, le_max_right _ _, fun τ hτ => ?_⟩
      calc ‖pulseReflected h τ‖
          ≤ C * Real.exp (-((1 / 4 : ℝ) - (1 / 4 - σ)) * τ) := hC τ hτ
        _ = C * Real.exp (-σ * τ) := by congr 2; ring
        _ ≤ max C 0 * Real.exp (-σ * τ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · intro H ε' hε' h
      by_cases hle : (1 / 4 : ℝ) ≤ ε'
      · refine ⟨∫ ξ : ℝ, ‖pulseAmplitude h (ξ : ℂ)‖, fun T hT => ?_⟩
        have hb := unitaryReflected_uniform (fun ξ => (norm_scatteringPhase_line ξ).le) h T
        rw [unitaryReflected_modular_eq] at hb
        have hexp_ge1 : 1 ≤ Real.exp (-((1 / 4 : ℝ) - ε') * T) :=
          Real.one_le_exp (by nlinarith)
        exact hb.trans (le_mul_of_one_le_right (integral_nonneg fun _ => norm_nonneg _) hexp_ge1)
      · push Not at hle
        set σ : ℝ := 1 / 4 - ε'
        have hσ0 : 0 < σ := by dsimp [σ]; linarith
        have hσ4 : σ < 1 / 4 := by dsimp [σ]; linarith
        obtain ⟨C, _, hC⟩ := (finiteFlippedReflected_decay_iff S hS hε h hσ0.le (by linarith)).mp
          (H σ hσ0 hσ4 h)
        exact ⟨C, hC⟩

/-! ## 3. Sharpness of Degree One: Integral-Trace Degree-Two Slow Modes for All `p ≥ 5` -/

/-- At `p = 2` and `p = 3`, the open slow-mode trace window `(2√p, p + 1)` contains no integers. -/
theorem no_integral_slow_trace_two_or_three :
    (¬ ∃ t : ℤ, 2 * Real.sqrt 2 < (t : ℝ) ∧ (t : ℝ) < 3) ∧
    (¬ ∃ t : ℤ, 2 * Real.sqrt 3 < (t : ℝ) ∧ (t : ℝ) < 4) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨t, hlo, hhi⟩
    have ht_pos : (0 : ℝ) < t := lt_trans (by positivity) hlo
    have ht_le2 : t ≤ 2 := by
      have : t < 3 := by exact_mod_cast hhi
      omega
    have hsq_gt : 8 < (t : ℝ) ^ 2 := by
      have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      nlinarith [Real.sqrt_nonneg 2]
    have hsq_le : (t : ℝ) ^ 2 ≤ 4 := by
      have htR : (t : ℝ) ≤ 2 := by exact_mod_cast ht_le2
      nlinarith
    linarith
  · rintro ⟨t, hlo, hhi⟩
    have ht_pos : (0 : ℝ) < t := lt_trans (by positivity) hlo
    have ht_le3 : t ≤ 3 := by
      have : t < 4 := by exact_mod_cast hhi
      omega
    have hsq_gt : 12 < (t : ℝ) ^ 2 := by
      have h12 : (2 * Real.sqrt 3) ^ 2 = 12 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      nlinarith [Real.sqrt_nonneg 3]
    have hsq_le : (t : ℝ) ^ 2 ≤ 9 := by
      have htR : (t : ℝ) ≤ 3 := by exact_mod_cast ht_le3
      nlinarith
    linarith

/-- Upper root `(p + √(p² - 4p)) / 2` of `X² - p X + p = 0`. -/
def integralTraceUpperRoot (p : ℕ) : ℝ :=
  ((p : ℝ) + Real.sqrt ((p : ℝ) ^ 2 - 4 * (p : ℝ))) / 2

/-- Lower root `(p - √(p² - 4p)) / 2` of `X² - p X + p = 0`. -/
def integralTraceLowerRoot (p : ℕ) : ℝ :=
  ((p : ℝ) - Real.sqrt ((p : ℝ) ^ 2 - 4 * (p : ℝ))) / 2

/-- Off-line zero real part `log r / log p ∈ (1/2, 1)` for `p ≥ 5`. -/
def integralTraceExponent (p : ℕ) : ℝ :=
  Real.log (integralTraceUpperRoot p) / Real.log (p : ℝ)

theorem integralTraceRoots_properties {p : ℕ} (hp5 : 5 ≤ p) :
    2 * Real.sqrt p < ((p : ℤ) : ℝ) ∧
    ((p : ℤ) : ℝ) < (p : ℝ) + 1 ∧
    1 < integralTraceLowerRoot p ∧
    integralTraceLowerRoot p < integralTraceUpperRoot p ∧
    integralTraceUpperRoot p * integralTraceLowerRoot p = p ∧
    integralTraceUpperRoot p + integralTraceLowerRoot p = (p : ℝ) ∧
    1 / 2 < integralTraceExponent p ∧
    integralTraceExponent p < 1 ∧
    (1 - integralTraceExponent p) / 2 < 1 / 4 ∧
    (p : ℝ) ^ integralTraceExponent p = integralTraceUpperRoot p ∧
    (p : ℝ) ^ (1 - integralTraceExponent p) = integralTraceLowerRoot p := by
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hp_pos : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hdisc_pos : 0 < (p : ℝ) ^ 2 - 4 * (p : ℝ) := by nlinarith
  have hD_pos : 0 < Real.sqrt ((p : ℝ) ^ 2 - 4 * (p : ℝ)) := Real.sqrt_pos.mpr hdisc_pos
  have hD_sq : Real.sqrt ((p : ℝ) ^ 2 - 4 * (p : ℝ)) ^ 2 = (p : ℝ) ^ 2 - 4 * (p : ℝ) :=
    Real.sq_sqrt hdisc_pos.le
  have hD_lt : Real.sqrt ((p : ℝ) ^ 2 - 4 * (p : ℝ)) < (p : ℝ) - 2 := by
    nlinarith [hD_sq]
  have h2sqrt : 2 * Real.sqrt p < ((p : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    have hsq : (2 * Real.sqrt p) ^ 2 < (p : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp_pos.le]; nlinarith
    nlinarith [Real.sqrt_nonneg p]
  have hu1 : 1 < integralTraceLowerRoot p := by
    unfold integralTraceLowerRoot; linarith
  have hur : integralTraceLowerRoot p < integralTraceUpperRoot p := by
    unfold integralTraceLowerRoot integralTraceUpperRoot; linarith
  have hr1 : 1 < integralTraceUpperRoot p := hu1.trans hur
  have hru : integralTraceUpperRoot p * integralTraceLowerRoot p = p := by
    unfold integralTraceUpperRoot integralTraceLowerRoot; nlinarith [hD_sq]
  have hsum : integralTraceUpperRoot p + integralTraceLowerRoot p = (p : ℝ) := by
    unfold integralTraceUpperRoot integralTraceLowerRoot; ring
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hr_rpow : (p : ℝ) ^ integralTraceExponent p = integralTraceUpperRoot p := by
    unfold integralTraceExponent
    rw [Real.rpow_def_of_pos hp_pos, mul_div_cancel₀ _ hlogp.ne',
      Real.exp_log (zero_lt_one.trans hr1)]
  have hu_rpow : (p : ℝ) ^ (1 - integralTraceExponent p) = integralTraceLowerRoot p := by
    have hprod : (p : ℝ) ^ integralTraceExponent p * (p : ℝ) ^ (1 - integralTraceExponent p) = p := by
      rw [← Real.rpow_add hp_pos, show integralTraceExponent p + (1 - integralTraceExponent p) = 1 by ring,
        Real.rpow_one]
    rw [hr_rpow] at hprod
    exact mul_left_cancel₀ (zero_lt_one.trans hr1).ne' (hprod.trans hru.symm)
  have hσ_half : 1 / 2 < integralTraceExponent p := by
    have hr_sq : (p : ℝ) < integralTraceUpperRoot p ^ 2 := by
      nlinarith [hur, hru, zero_lt_one.trans hr1]
    have hlog_lt : Real.log p < 2 * Real.log (integralTraceUpperRoot p) := by
      have := Real.log_lt_log hp_pos hr_sq
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    unfold integralTraceExponent
    rw [div_lt_div_iff₀ (by norm_num) hlogp]
    linarith
  have hσ1 : integralTraceExponent p < 1 := by
    have hr_lt_p : integralTraceUpperRoot p < p := by unfold integralTraceUpperRoot; linarith
    unfold integralTraceExponent
    exact (div_lt_one hlogp).mpr (Real.log_lt_log (zero_lt_one.trans hr1) hr_lt_p)
  exact ⟨h2sqrt, by rw [Int.cast_natCast]; linarith, hu1, hur, hru, hsum,
    hσ_half, hσ1, by linarith, hr_rpow, hu_rpow⟩

/-- **Integral-Trace Degree-Two Slow-Mode Theorem for Every `p ≥ 5`.**
For every integer `p ≥ 5` (in particular every prime `p ≥ 5`), the integer trace `t = p ∈ ℤ` lies
strictly inside `(2√p, p + 1)` with `r = integralTraceUpperRoot p`, `u = integralTraceLowerRoot p`,
`r * u = p`, `r + u = (p : ℤ)`, and `σ = integralTraceExponent p ∈ (1/2, 1)`.
Consequently, the pure-bounce horizon `PositiveEulerHorizon` at `(p, p)` is causal, globally
Schur-passive, Herglotz-positive, axis-unitary, entire, and `s ↦ 1 - s` symmetric with positive
real-axis values and integer local coefficients `1 + p · p^{-s} + p · p^{-2s}`, yet unconditionally
violates `O(e^{-δ τ})` for every `δ > (1 - σ) / 2` — and in particular violates the quarter law
`δ = 1 / 4`! -/
theorem integral_trace_degree_two_slow_mode_of_ge_five {p : ℕ} (hp5 : 5 ≤ p) :
    let r := integralTraceUpperRoot p
    let u := integralTraceLowerRoot p
    let σ := integralTraceExponent p
    2 * Real.sqrt p < ((p : ℤ) : ℝ) ∧ ((p : ℤ) : ℝ) < (p : ℝ) + 1 ∧
    1 < u ∧ u < r ∧ r * u = p ∧ r + u = ((p : ℤ) : ℝ) ∧
    1 / 2 < σ ∧ σ < 1 ∧ (1 - σ) / 2 < 1 / 4 ∧
    (∀ τ : ℝ, τ ≤ 0 → twinEchoKernel p r u τ = 0) ∧
    Differentiable ℂ (PositiveEulerHorizon.completedXi p (p : ℝ)) ∧
    (∀ s : ℂ, PositiveEulerHorizon.completedXi p (p : ℝ) (1 - s) =
      PositiveEulerHorizon.completedXi p (p : ℝ) s) ∧
    (∀ x : ℝ, 0 < (PositiveEulerHorizon.completedXi p (p : ℝ) (x : ℂ)).re) ∧
    (∀ w : ℂ, 0 ≤ w.re →
      ‖PositiveEulerHorizon.reducedScattering p (p : ℝ) w‖ ≤ 1 ∧
      0 ≤ ((1 - PositiveEulerHorizon.reducedScattering p (p : ℝ) w) /
        (1 + PositiveEulerHorizon.reducedScattering p (p : ℝ) w)).re) ∧
    (∀ t : ℝ, ‖PositiveEulerHorizon.scatteringPhase p (p : ℝ) ((t : ℂ) * I)‖ = 1) ∧
    (∀ η : ℝ, 0 < η → η < min (3001 / 48000) ((1 - σ) / 2) → ∀ h : CompactPulse,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
        ‖twinReflected p (p : ℝ) h τ‖ ≤ C * Real.exp (-η * τ)) ∧
    (∀ δ : ℝ, (1 - σ) / 2 < δ →
      ∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖twinReflected p (p : ℝ) h τ‖ ≤ C * Real.exp (-δ * τ)) ∧
    (∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖twinReflected p (p : ℝ) h τ‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * τ)) := by
  dsimp only
  have hp1_nat : 1 < p := by omega
  have hp_ne0 : p ≠ 0 := by omega
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp1_nat
  obtain ⟨h2sq, hp_lt1, hu1, hur, hru, hsum, hσ_half, hσ1, hquarter, hr_pow, hu_pow⟩ :=
    integralTraceRoots_properties hp5
  have hr1 : 1 < integralTraceUpperRoot p := hu1.trans hur
  have hparam_eq : (p : ℝ) ^ integralTraceExponent p + (p : ℝ) ^ (1 - integralTraceExponent p) =
      (p : ℝ) := by rw [hr_pow, hu_pow, hsum]
  have hfail_above : ∀ δ : ℝ, (1 - integralTraceExponent p) / 2 < δ →
      ∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖twinReflected p (p : ℝ) h τ‖ ≤ C * Real.exp (-δ * τ) := by
    intro δ hδ
    refine ⟨excitingPulse ((GaloisForLFunctions.SelbergClass.PositiveFiniteEuler.factorZero p
      ((p : ℝ) ^ integralTraceExponent p) - 1) / 2), ?_⟩
    have ht := not_twinReflected_decay_gt hp1_nat hσ_half hσ1 hδ
    rwa [hparam_eq] at ht
  refine ⟨h2sq, hp_lt1, hu1, hur, hru, by rw [Int.cast_natCast, hsum],
    hσ_half, hσ1, hquarter, ?_,
    PositiveEulerHorizon.differentiable_completedXi hp_ne0 (p : ℝ),
    PositiveEulerHorizon.completedXi_one_sub p (p : ℝ),
    positiveEuler_completedXi_real_pos (by omega) hp_pos.le, ?_, ?_, ?_, hfail_above,
    hfail_above (1 / 4) hquarter⟩
  · intro τ hτ
    rw [twinEchoKernel, echoKernel_eq_zero_of_nonpos hτ, mul_zero, zero_add]
    have h0 : ∀ m : ℕ, twinEchoCoeff p (integralTraceUpperRoot p) (integralTraceLowerRoot p) m *
        echoKernel (τ - 2 * ((m : ℝ) + 1) * Real.log p) = 0 := fun m => by
      have hd_nn : 0 ≤ 2 * ((m : ℝ) + 1) * Real.log p :=
        mul_nonneg (by positivity) (Real.log_pos hp1).le
      rw [echoKernel_eq_zero_of_nonpos (by linarith), mul_zero]
    simp [h0]
  · intro w hw
    have h1 := PositiveEulerHorizon.norm_reducedScattering_le_one hp1_nat hr1 hu1 hru hw
    have h2 := PositiveEulerHorizon.herglotz_re_nonneg hp1_nat hr1 hu1 hru hw
    rw [hsum] at h1 h2
    exact ⟨h1, h2⟩
  · intro t
    have h1 := PositiveEulerHorizon.norm_scatteringPhase_axis hp1_nat hr1 hu1 hru t
    rwa [hsum] at h1
  · intro η hη0 hη_min h
    have ht := twinReflected_decay_lt hp1_nat hσ_half hσ1 hη0
      (lt_of_lt_of_le hη_min (min_le_left _ _))
      (lt_of_lt_of_le hη_min (min_le_right _ _)) h
    rwa [hparam_eq] at ht

#print axioms degree_one_rational_prime_gate_classification
#print axioms degree_one_real_prime_gate_classification
#print axioms finite_prime_degree_one_gate_classification
#print axioms flippedEchoKernel_causal_and_laplace
#print axioms finiteFlipped_passive_unitary_and_strip_rigid
#print axioms finiteFlippedReflected_decay_iff
#print axioms finiteFlipped_strip_and_rh_equivalence
#print axioms no_integral_slow_trace_two_or_three
#print axioms integral_trace_degree_two_slow_mode_of_ge_five

end GaloisForLFunctions.BlackHoleRingdown
