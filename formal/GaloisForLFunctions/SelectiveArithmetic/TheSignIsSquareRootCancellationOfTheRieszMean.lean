import GaloisForLFunctions.SelectiveArithmetic.CancellationInTheContactsBuysTheLadder
import GaloisForLFunctions.SelectiveArithmetic.TheFeasibleSetsOfAConductor

/-!
# The sign is square-root cancellation of the Riesz mean

Cancellation in the contacts buys the sign (`exists_cancellation_margin`). Conversely the sign
at one aperture is cancellation at that scale: the form of a dominated system on the two polar
packets reads the Riesz mean of its contacts.

**Theorem** (`exists_riesz_le_of_polar_nonneg`, `exists_riesz_le_of_feasible`). There is an
absolute constant `C` such that for every dominated system `w`, every conductor with
`log q ≥ 0` and every aperture `a ≥ 1`: if the form of `(w, q)` is nonnegative on the even and
on the odd polar packet of the window `[−a, a]` with margin `e^{−a}`, then
`|Σ_{2 ≤ n ≤ e^{2a}} w(n) (2a − log n)| ≤ (3 log q + C (1 + a)³) e^{a}`.
With `Y = e^{2a}` the Riesz mean `Σ_{n ≤ Y} w(n) log(Y/n)` is at most `√Y (3 log q + C log³ Y)`.

**Corollary** (`exists_not_feasible_of_riesz_ge`). A dominated system whose Riesz mean at
`Y = e^{2a}` is at least `cY` in absolute value is infeasible as soon as
`3 log q + C (1 + a)³ < c e^{a}`.

**Corollary** (`exists_riesz_twist_le_of_nonneg`). For a primitive character `χ` of conductor
`q`: if the sum over the zeros of `L(s, χ)` is nonnegative on these two packets, then
`|Σ_{n ≤ e^{2a}} Λ(n) Re χ(n) (2a − log n)| ≤ (3 (log q + π) + C (1 + a)³) e^{a}`.

So on the ladder the exchange rate holds in both directions on the prime side: a sign up to the
rung `κ` gives the saving `Y^{1/2 + 1/(2κ)}` of the Riesz mean at `Y = (log q)^{2κ}`, and a saving
`n^{1/2 + γ}` gives the sign up to the rung `1/(2γ)`. The three fakes of the trivial aperture are
the dominated systems whose Riesz mean has no saving.

**Mechanism.** With `E = cosh(u/2) χ` and `O = sinh(u/2) χ`:
`E(u)E(u+y) − O(u)O(u+y) = cosh(y/2) χ(u) χ(u+y)` and
`E(u)E(u+y) + O(u)O(u+y) = cosh(u + y/2) χ(u) χ(u+y)`. The difference of the two contact forms
is `Σ w(n) (1 + 1/n) Φ(log n)` with `Φ = χ ⋆ χ̃`, `2a − 2δ − y ≤ Φ(y) ≤ 2a − y`; the sum is at
most `4a e^{a} Σ Λ(n)/n`. Each contact form is bounded above by the archimedean energy of its
packet, which for a cutoff of margin `δ` is at most `(log(1 + 1/δ) + 5) ∫ f² + δ² ∫ f'²`.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### The archimedean energy of a packet with a narrow cutoff -/

/-- The archimedean symbol is at most `log(1 + 1/δ) + 5 + δ² τ²`. -/
theorem archimedeanWeilSymbol_le_scaled {δ : ℝ} (hδ : 0 < δ) (τ : ℝ) :
    _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      Real.log (1 + 1 / δ) + 5 + δ ^ 2 * τ ^ 2 := by
  have h := _root_.RHTower.archimedeanWeilSymbol_le_log_add τ
  have hprod : 1 + |τ| ≤ (1 + 1 / δ) * (1 + δ * |τ|) := by
    have e : (1 + 1 / δ) * (1 + δ * |τ|) = 1 + δ * |τ| + 1 / δ + |τ| := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ δ * |τ| + 1 / δ := by positivity
    linarith
  have h1 : Real.log (1 + |τ|) ≤ Real.log (1 + 1 / δ) + Real.log (1 + δ * |τ|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) hprod
  have h2 : Real.log (1 + δ * |τ|) ≤ δ * |τ| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + δ * |τ|)
    linarith
  have h3 : δ * |τ| ≤ 1 + δ ^ 2 * τ ^ 2 := by
    have e : δ ^ 2 * τ ^ 2 = (δ * |τ|) ^ 2 := by rw [mul_pow, sq_abs]
    rw [e]
    nlinarith [sq_nonneg (δ * |τ| - 1)]
  linarith

/-- **The form of a system on a packet with a narrow cutoff** is at most
`(log(1 + 1/δ) + 5 + log q) ∫ f² + δ² ∫ f'²` minus its contact form. -/
theorem systemForm_le_of_packet_scaled {a δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (h0 : ∀ u, a ≤ |u| → f u = 0) (w : ℕ → ℝ) (q : ℝ) :
    systemForm w q a (fun u => (f u : ℂ)) ≤
      (Real.log (1 + 1 / δ) + 5 + Real.log q) * (∫ u, f u ^ 2) + δ ^ 2 * (∫ u, deriv f u ^ 2) -
        contactForm w (fun u => (f u : ℂ)) ⌊Real.exp (2 * a)⌋₊ := by
  have hF : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet (hf.of_le (by norm_num))
  have hFs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  have hA := _root_.RHTower.integrable_normSq_paperFT_mul_arch hF hFs
  have hneg : Integrable fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
      (-_root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) := by
    have e : (fun τ : ℝ => ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          (-_root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)))) =
        fun τ : ℝ => -(‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) := by
      funext τ
      ring
    rw [e]
    exact hA.neg
  have h := integral_normSq_paperFT_mul_ge hf h0 hneg
    (α := -(Real.log (1 + 1 / δ) + 5)) (β := δ ^ 2) fun τ => by
      have := archimedeanWeilSymbol_le_scaled hδ τ
      linarith
  have e : ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        (-_root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) =
      -∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    show ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        (-_root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) =
      -(‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)))
    ring
  rw [e] at h
  rw [systemForm_eq hF hFs, integral_norm_ofReal_sq]
  nlinarith

/-! ### The correlation of the cutoff -/

theorem hasCompactSupport_cutoff {a δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (cutoff a δ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu =>
    cutoff_eq_zero hδ (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl h.le))

theorem integrable_cutoff_mul {a δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Integrable fun u => cutoff a δ u * cutoff a δ (u + y) :=
  ((contDiff_cutoff a δ).continuous.mul ((contDiff_cutoff a δ).continuous.comp
    (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hasCompactSupport_cutoff hδ).mul_right

/-- `Φ(y) ≥ 2a − 2δ − y` for the correlation `Φ` of the cutoff, `y ≥ 0`. -/
theorem packetAutocorr_cutoff_ge {a δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : 0 ≤ y) :
    2 * a - 2 * δ - y ≤ packetAutocorr (cutoff a δ) y := by
  have hnn : 0 ≤ packetAutocorr (cutoff a δ) y :=
    integral_nonneg fun _ => mul_nonneg (cutoff_nonneg a δ _) (cutoff_nonneg a δ _)
  by_cases hneg : 2 * a - 2 * δ - y ≤ 0
  · linarith
  push Not at hneg
  have hg : ∫ u, (Set.Icc (-a + δ) (a - δ - y)).indicator (fun _ => (1 : ℝ)) u =
      2 * a - 2 * δ - y := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [← hg, packetAutocorr]
  refine integral_mono (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
    (integrable_cutoff_mul hδ y) fun u => ?_
  by_cases hu : u ∈ Set.Icc (-a + δ) (a - δ - y)
  · rw [Set.indicator_of_mem hu,
      cutoff_eq_one hδ (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩),
      cutoff_eq_one hδ (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩), mul_one]
  · rw [Set.indicator_of_notMem hu]
    exact mul_nonneg (cutoff_nonneg a δ _) (cutoff_nonneg a δ _)

/-- `Φ(y) ≤ 2a − y` for `0 ≤ y ≤ 2a`. -/
theorem packetAutocorr_cutoff_le {a δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hya : y ≤ 2 * a) :
    packetAutocorr (cutoff a δ) y ≤ 2 * a - y := by
  have hg : ∫ u, (Set.Icc (-a) (a - y)).indicator (fun _ => (1 : ℝ)) u = 2 * a - y := by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  rw [← hg, packetAutocorr]
  refine integral_mono (integrable_cutoff_mul hδ y)
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc) fun u => ?_
  by_cases hu : u ∈ Set.Icc (-a) (a - y)
  · rw [Set.indicator_of_mem hu]
    exact mul_le_one₀ (cutoff_le_one a δ u) (cutoff_nonneg a δ _) (cutoff_le_one a δ _)
  · rw [Set.indicator_of_notMem hu]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with h | h
    · show cutoff a δ u * cutoff a δ (u + y) ≤ 0
      rw [cutoff_eq_zero hδ (le_abs.mpr (Or.inr (by linarith))), zero_mul]
    · show cutoff a δ u * cutoff a δ (u + y) ≤ 0
      rw [cutoff_eq_zero (u := u + y) hδ (le_abs.mpr (Or.inl (by linarith))), mul_zero]

/-! ### Sum and difference of the correlations of the polar packets -/

/-- `(E ⋆ Ẽ)(y) − (O ⋆ Õ)(y) = cosh(y/2) Φ(y)`. -/
theorem packetAutocorr_evenPolar_sub_oddPolar {a δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    packetAutocorr (evenPolar a δ) y - packetAutocorr (oddPolar a δ) y =
      Real.cosh (y / 2) * packetAutocorr (cutoff a δ) y := by
  rw [packetAutocorr, packetAutocorr, packetAutocorr,
    ← integral_sub (integrable_evenPolar_mul hδ y) (integrable_oddPolar_mul hδ y),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show evenPolar a δ u * evenPolar a δ (u + y) - oddPolar a δ u * oddPolar a δ (u + y) =
    Real.cosh (y / 2) * (cutoff a δ u * cutoff a δ (u + y))
  have hc := Real.cosh_sub ((u + y) / 2) (u / 2)
  rw [show (u + y) / 2 - u / 2 = y / 2 by ring] at hc
  rw [evenPolar, evenPolar, oddPolar, oddPolar, hc]
  ring

/-- `(E ⋆ Ẽ)(y) + (O ⋆ Õ)(y) ≥ 0`. -/
theorem packetAutocorr_evenPolar_add_oddPolar_nonneg {a δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ packetAutocorr (evenPolar a δ) y + packetAutocorr (oddPolar a δ) y := by
  rw [packetAutocorr, packetAutocorr,
    ← integral_add (integrable_evenPolar_mul hδ y) (integrable_oddPolar_mul hδ y)]
  refine integral_nonneg fun u => ?_
  show 0 ≤ evenPolar a δ u * evenPolar a δ (u + y) + oddPolar a δ u * oddPolar a δ (u + y)
  have hc := Real.cosh_add (u / 2) ((u + y) / 2)
  have e : evenPolar a δ u * evenPolar a δ (u + y) + oddPolar a δ u * oddPolar a δ (u + y) =
      Real.cosh (u / 2 + (u + y) / 2) * (cutoff a δ u * cutoff a δ (u + y)) := by
    rw [evenPolar, evenPolar, oddPolar, oddPolar, hc]
    ring
  rw [e]
  exact mul_nonneg (Real.cosh_pos _).le (mul_nonneg (cutoff_nonneg a δ _) (cutoff_nonneg a δ _))

/-! ### The two polar packets read the Riesz mean -/

/-- `2 cosh(½ log n)/√n = 1 + 1/n`. -/
theorem two_cosh_half_log_div_sqrt {n : ℕ} (hn : 0 < n) :
    2 * Real.cosh (Real.log n / 2) / Real.sqrt n = 1 + 1 / (n : ℝ) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnr.le
  have h1 : Real.exp (Real.log n / 2) = Real.sqrt n := by
    have h := exp_add_half_log hn 0
    rwa [zero_add, Real.exp_zero, one_mul] at h
  have h2 : Real.exp (-(Real.log n / 2)) = 1 / Real.sqrt n := by
    rw [Real.exp_neg, h1, one_div]
  rw [Real.cosh_eq, h1, h2]
  field_simp
  nlinarith

/-- **The difference of the contact forms of the two polar packets is the Riesz mean of the
contacts**, up to the margin of the cutoff:
`|T_E − T_O − Σ w(n)(2a − log n)| ≤ 4δ Σ Λ(n) + 2a Σ Λ(n)/n`. -/
theorem abs_contactForm_evenPolar_sub_oddPolar_sub_riesz_le {a δ : ℝ} (hδ : 0 < δ)
    {w : ℕ → ℝ} (hw : Dominated w) :
    |contactForm w (fun u => (evenPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊ -
        contactForm w (fun u => (oddPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊ -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n * (2 * a - Real.log n)| ≤
      4 * δ * (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ)) +
        2 * a * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n := by
  rw [contactForm_packet, contactForm_packet, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn2 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog : Real.log n ≤ 2 * a := by
    calc Real.log n ≤ Real.log (Real.exp (2 * a)) :=
          Real.log_le_log hnr ((Nat.cast_le.mpr hnN).trans (Nat.floor_le (Real.exp_pos _).le))
      _ = 2 * a := Real.log_exp _
  -- the term at `n`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = packetAutocorr (cutoff a δ) (Real.log n) := ⟨_, rfl⟩
  have hΦ1 : 2 * a - 2 * δ - Real.log n ≤ Φ := by
    rw [hΦ]
    exact packetAutocorr_cutoff_ge hδ hlog0
  have hΦ2 : Φ ≤ 2 * a - Real.log n := by
    rw [hΦ]
    exact packetAutocorr_cutoff_le hδ hlog
  have hterm : w n / Real.sqrt n * (2 * packetAutocorr (evenPolar a δ) (Real.log n)) -
        w n / Real.sqrt n * (2 * packetAutocorr (oddPolar a δ) (Real.log n)) -
        w n * (2 * a - Real.log n) =
      w n * ((1 + 1 / (n : ℝ)) * (Φ - (2 * a - Real.log n)) + (2 * a - Real.log n) / n) := by
    have hdiff := packetAutocorr_evenPolar_sub_oddPolar (a := a) hδ (Real.log n)
    rw [← hΦ] at hdiff
    have hk := two_cosh_half_log_div_sqrt hn0
    have e1 : w n / Real.sqrt n * (2 * packetAutocorr (evenPolar a δ) (Real.log n)) -
        w n / Real.sqrt n * (2 * packetAutocorr (oddPolar a δ) (Real.log n)) =
        w n * (2 * Real.cosh (Real.log n / 2) / Real.sqrt n) * Φ := by
      rw [← mul_sub, ← mul_sub, hdiff]
      ring
    rw [e1, hk]
    ring
  rw [hterm, abs_mul]
  have hin : |(1 + 1 / (n : ℝ)) * (Φ - (2 * a - Real.log n)) + (2 * a - Real.log n) / n| ≤
      4 * δ + 2 * a / n := by
    have h1 : |Φ - (2 * a - Real.log n)| ≤ 2 * δ := by
      rw [abs_le]
      constructor <;> linarith
    have h2 : 1 + 1 / (n : ℝ) ≤ 2 := by
      have : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one hnr]
        exact hn1
      linarith
    have h3 : |(1 + 1 / (n : ℝ)) * (Φ - (2 * a - Real.log n))| ≤ 2 * (2 * δ) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + 1 / (n : ℝ))]
      exact mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
    have h4 : |(2 * a - Real.log n) / n| ≤ 2 * a / n := by
      rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a - Real.log n), abs_of_pos hnr]
      exact div_le_div_of_nonneg_right (by linarith) hnr.le
    calc _ ≤ |(1 + 1 / (n : ℝ)) * (Φ - (2 * a - Real.log n))| + |(2 * a - Real.log n) / n| :=
          abs_add_le _ _
      _ ≤ 2 * (2 * δ) + 2 * a / n := add_le_add h3 h4
      _ = 4 * δ + 2 * a / n := by ring
  calc |w n| * |(1 + 1 / (n : ℝ)) * (Φ - (2 * a - Real.log n)) + (2 * a - Real.log n) / n|
      ≤ (Λ n : ℝ) * (4 * δ + 2 * a / n) :=
        mul_le_mul (hw n) hin (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ = 4 * δ * (Λ n : ℝ) + 2 * a * ((Λ n : ℝ) / n) := by ring

/-- The sum of the contact forms of the two polar packets is at most
`4a e^{a} Σ Λ(n)/n` in absolute value. -/
theorem abs_contactForm_evenPolar_add_oddPolar_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    {w : ℕ → ℝ} (hw : Dominated w) :
    |contactForm w (fun u => (evenPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊ +
        contactForm w (fun u => (oddPolar a δ u : ℂ)) ⌊Real.exp (2 * a)⌋₊| ≤
      4 * a * Real.exp a * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n := by
  rw [contactForm_packet, contactForm_packet, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn2 := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnr
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnr.le
  have hsum0 := packetAutocorr_evenPolar_add_oddPolar_nonneg (a := a) hδ (Real.log n)
  have hsum1 := packetAutocorr_oddPolar_le (δ := δ) ha hδ (Real.log n)
  rw [exp_sub_half_log hn0 a] at hsum1
  have e : w n / Real.sqrt n * (2 * packetAutocorr (evenPolar a δ) (Real.log n)) +
      w n / Real.sqrt n * (2 * packetAutocorr (oddPolar a δ) (Real.log n)) =
      w n / Real.sqrt n * (2 * (packetAutocorr (evenPolar a δ) (Real.log n) +
        packetAutocorr (oddPolar a δ) (Real.log n))) := by ring
  rw [e, abs_mul, abs_div, abs_of_pos hs,
    abs_of_nonneg (mul_nonneg zero_le_two hsum0)]
  have h1 : |w n| / Real.sqrt n ≤ (Λ n : ℝ) / Real.sqrt n :=
    div_le_div_of_nonneg_right (hw n) hs.le
  have h2 : 2 * (packetAutocorr (evenPolar a δ) (Real.log n) +
      packetAutocorr (oddPolar a δ) (Real.log n)) ≤ 2 * (2 * a * (Real.exp a / Real.sqrt n)) := by
    linarith
  calc |w n| / Real.sqrt n * (2 * (packetAutocorr (evenPolar a δ) (Real.log n) +
        packetAutocorr (oddPolar a δ) (Real.log n)))
      ≤ (Λ n : ℝ) / Real.sqrt n * (2 * (2 * a * (Real.exp a / Real.sqrt n))) :=
        mul_le_mul h1 h2 (mul_nonneg zero_le_two hsum0)
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hs.le)
    _ = 4 * a * Real.exp a * ((Λ n : ℝ) / n) := by
        have h3 : (Λ n : ℝ) / Real.sqrt n * (Real.exp a / Real.sqrt n) =
            Real.exp a * ((Λ n : ℝ) / n) := by
          rw [div_mul_div_comm, hss]
          ring
        linear_combination (4 * a) * h3

/-! ### The sign gives the saving -/

/-- **The budget of a polar packet.** A packet of mass `≤ a + sinh a` and derivative energy
`≤ (½ + 2S/δ)² (a + sinh a)`, `δ = e^{−a}`, on which the form of `(w, q)` is nonnegative, has
contact form at most `(log q + a + 6 + (½ + 2S)²) · (3/2) e^{a}`. -/
theorem contactForm_le_of_systemForm_nonneg {S q a : ℝ} (hS0 : 0 ≤ S)
    (hx : 0 ≤ Real.log q) (ha : 1 ≤ a) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (hM : ∫ u, f u ^ 2 ≤ a + Real.sinh a)
    (hD : ∫ u, deriv f u ^ 2 ≤ (1 / 2 + 2 * S / Real.exp (-a)) ^ 2 * (a + Real.sinh a))
    (w : ℕ → ℝ) (hpos : 0 ≤ systemForm w q a (fun u => (f u : ℂ))) :
    contactForm w (fun u => (f u : ℂ)) ⌊Real.exp (2 * a)⌋₊ ≤
      (Real.log q + a + 6 + (1 / 2 + 2 * S) ^ 2) * (3 / 2 * Real.exp a) := by
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = Real.exp (-a) := ⟨_, rfl⟩
  rw [← hδdef] at hD
  have hδ : 0 < δ := by rw [hδdef]; exact Real.exp_pos _
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp a := ⟨_, rfl⟩
  rw [← hEdef]
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have haE : a ≤ E := by rw [hEdef]; linarith [Real.add_one_le_exp a]
  have hδE : δ * E = 1 := by
    rw [hδdef, hEdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hsinh : Real.sinh a ≤ E / 2 := by
    rw [Real.sinh_eq, ← hEdef]
    linarith [Real.exp_pos (-a)]
  have hsinh0 : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha0
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = a + Real.sinh a := ⟨_, rfl⟩
  rw [← hMb] at hM hD
  have hMb0 : 0 ≤ Mb := by rw [hMb]; linarith
  have hMbE : Mb ≤ 3 / 2 * E := by rw [hMb]; linarith
  have hM0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  -- the derivative energy at the scale of the margin
  have hKδ : δ ^ 2 * ((1 / 2 + 2 * S / δ) ^ 2 * Mb) ≤ (1 / 2 + 2 * S) ^ 2 * Mb := by
    have e : δ ^ 2 * ((1 / 2 + 2 * S / δ) ^ 2 * Mb) = (δ / 2 + 2 * S) ^ 2 * Mb := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) 2) hMb0
  have hlogδ : Real.log (1 + 1 / δ) ≤ a + 1 := by
    have h1 : 1 / δ = E := by
      rw [eq_comm, eq_div_iff hδ.ne', mul_comm]
      exact hδE
    have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 := mul_le_mul_of_nonneg_left he hE0.le
    rw [h1]
    calc Real.log (1 + E) ≤ Real.log (Real.exp (a + 1)) := by
          refine Real.log_le_log (by linarith) ?_
          rw [Real.exp_add, ← hEdef]
          linarith
      _ = a + 1 := Real.log_exp _
  have hlogδ0 : 0 ≤ Real.log (1 + 1 / δ) := Real.log_nonneg (by
    have : 0 ≤ 1 / δ := by positivity
    linarith)
  have h := systemForm_le_of_packet_scaled hδ hf h0 w q
  have h1 : (Real.log (1 + 1 / δ) + 5 + Real.log q) * (∫ u, f u ^ 2) ≤
      (Real.log q + a + 6) * Mb :=
    calc (Real.log (1 + 1 / δ) + 5 + Real.log q) * (∫ u, f u ^ 2)
        ≤ (Real.log (1 + 1 / δ) + 5 + Real.log q) * Mb :=
          mul_le_mul_of_nonneg_left hM (by linarith)
      _ ≤ (Real.log q + a + 6) * Mb := mul_le_mul_of_nonneg_right (by linarith) hMb0
  have h2 : δ ^ 2 * (∫ u, deriv f u ^ 2) ≤ (1 / 2 + 2 * S) ^ 2 * Mb :=
    (mul_le_mul_of_nonneg_left hD (sq_nonneg δ)).trans hKδ
  have h3 : (Real.log q + a + 6 + (1 / 2 + 2 * S) ^ 2) * Mb ≤
      (Real.log q + a + 6 + (1 / 2 + 2 * S) ^ 2) * (3 / 2 * E) :=
    mul_le_mul_of_nonneg_left hMbE (by positivity)
  linarith

/-- The arithmetic of the last step. -/
theorem riesz_bound_algebra {x a E cS L TE TO R B : ℝ} (ha : 1 ≤ a) (hE : 1 ≤ E)
    (hcS : 0 ≤ cS) (hL : 0 ≤ L) (hB : B = (x + a + 6 + cS) * (3 / 2 * E)) (hTE : TE ≤ B)
    (hTO : TO ≤ B) (hS1 : |TE + TO| ≤ 4 * a * E * (2 + 2 * a) ^ 2)
    (hD1 : |TE - TO - R| ≤ 4 * L * E + 2 * a * (2 + 2 * a) ^ 2) :
    |R| ≤ (3 * x + (3 * (7 + cS) + 24 + 4 * L) * (1 + a) ^ 3) * E := by
  have hE0 : 0 ≤ E := by linarith
  have h1 := abs_le.mp hS1
  have h2 := abs_le.mp hD1
  have hRle : |R| ≤ 2 * B + 4 * a * E * (2 + 2 * a) ^ 2 +
      (4 * L * E + 2 * a * (2 + 2 * a) ^ 2) := by
    rw [abs_le]
    constructor <;> linarith
  have hs1 : (1 : ℝ) ≤ (1 + a) ^ 3 := one_le_pow₀ (by linarith)
  have hs2 : a * (1 + a) ^ 2 ≤ (1 + a) ^ 3 := by
    have e : (1 + a) ^ 3 = (1 + a) * (1 + a) ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hs3 : a ≤ (1 + a) ^ 3 :=
    (by linarith : a ≤ 1 + a).trans (le_self_pow₀ (by linarith) (by norm_num))
  have hP0 : 0 ≤ (1 + a) ^ 3 := by linarith
  have t1 : 3 * (a + 6 + cS) ≤ 3 * (7 + cS) * (1 + a) ^ 3 := by
    linarith [mul_nonneg hcS (sub_nonneg.mpr hs1)]
  have t2 : 8 * (a * (1 + a) ^ 2) ≤ 8 * ((1 + a) ^ 3 * E) := by
    linarith [mul_le_mul_of_nonneg_left hE hP0]
  have t3 : 4 * L ≤ 4 * L * (1 + a) ^ 3 := by
    linarith [mul_nonneg hL (sub_nonneg.mpr hs1)]
  have p1 := mul_le_mul_of_nonneg_right t1 hE0
  have p2 := mul_le_mul_of_nonneg_right hs2 hE0
  have p3 := mul_le_mul_of_nonneg_right t3 hE0
  refine hRle.trans ?_
  rw [hB]
  have e1 : (2 + 2 * a) ^ 2 = 4 * (1 + a) ^ 2 := by ring
  rw [e1]
  linarith

/-- **The sign on the two polar packets is square-root cancellation of the Riesz mean.** There
is an absolute constant `C` such that for every dominated system `w`, every conductor with
`log q ≥ 0` and every aperture `a ≥ 1`: if the form of `(w, q)` is nonnegative on the even and
on the odd polar packet of margin `e^{−a}`, then
`|Σ_{2 ≤ n ≤ e^{2a}} w(n)(2a − log n)| ≤ (3 log q + C (1 + a)³) e^{a}`. -/
theorem exists_riesz_le_of_polar_nonneg :
    ∃ C : ℝ, ∀ {q a : ℝ}, 0 ≤ Real.log q → 1 ≤ a → ∀ {w : ℕ → ℝ}, Dominated w →
      0 ≤ systemForm w q a (fun u => (evenPolar a (Real.exp (-a)) u : ℂ)) →
      0 ≤ systemForm w q a (fun u => (oddPolar a (Real.exp (-a)) u : ℂ)) →
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n * (2 * a - Real.log n)| ≤
        (3 * Real.log q + C * (1 + a) ^ 3) * Real.exp a := by
  obtain ⟨S, hS0, hS⟩ := exists_abs_deriv_smoothTransition_le
  refine ⟨3 * (7 + (1 / 2 + 2 * S) ^ 2) + 24 + 4 * (Real.log 4 + 4),
    fun {q a} hx ha w hw hE hO => ?_⟩
  have ha0 : 0 ≤ a := by linarith
  have hδ : 0 < Real.exp (-a) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp a := Real.one_le_exp ha0
  -- each contact form is below the budget
  have hTE := contactForm_le_of_systemForm_nonneg hS0 hx ha (contDiff_evenPolar a _)
    (fun u hu => evenPolar_eq_zero hδ hu) (integral_evenPolar_sq_le ha0 hδ)
    (integral_deriv_evenPolar_sq_le hS ha0 hδ) w hE
  have hTO := contactForm_le_of_systemForm_nonneg hS0 hx ha (contDiff_oddPolar a _)
    (fun u hu => oddPolar_eq_zero hδ hu) (integral_oddPolar_sq_le ha0 hδ)
    (integral_deriv_oddPolar_sq_le hS ha0 hδ) w hO
  -- Mertens and Chebyshev on the window
  have hmer2 : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) / n ≤ (2 + 2 * a) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
      rw [Finset.mem_Icc] at hn ⊢
      omega) fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Nat.cast_nonneg n)).trans (sum_vonMangoldt_div_window_le ha0)
  have hpsi : Real.exp (-a) * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, (Λ n : ℝ) ≤
      (Real.log 4 + 4) * Real.exp a := by
    have h1 := sum_vonMangoldt_le_psi (S := Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊)
      (x := Real.exp (2 * a)) fun n hn =>
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le (Real.exp_pos _).le)
    have h2 := h1.trans (Chebyshev.psi_le_const_mul_self (Real.exp_pos (2 * a)).le)
    have h3 := mul_le_mul_of_nonneg_left h2 hδ.le
    have e : Real.exp (-a) * ((Real.log 4 + 4) * Real.exp (2 * a)) =
        (Real.log 4 + 4) * Real.exp a := by
      have e' : Real.exp (-a) * Real.exp (2 * a) = Real.exp a := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination (Real.log 4 + 4) * e'
    rwa [e] at h3
  -- sum and difference of the two contact forms
  have hS1 := (abs_contactForm_evenPolar_add_oddPolar_le ha0 hδ hw).trans
    (mul_le_mul_of_nonneg_left hmer2 (by positivity))
  have hD1 : |contactForm w (fun u => (evenPolar a (Real.exp (-a)) u : ℂ))
          ⌊Real.exp (2 * a)⌋₊ -
        contactForm w (fun u => (oddPolar a (Real.exp (-a)) u : ℂ)) ⌊Real.exp (2 * a)⌋₊ -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n * (2 * a - Real.log n)| ≤
      4 * (Real.log 4 + 4) * Real.exp a + 2 * a * (2 + 2 * a) ^ 2 := by
    refine (abs_contactForm_evenPolar_sub_oddPolar_sub_riesz_le hδ hw).trans
      (add_le_add ?_ (mul_le_mul_of_nonneg_left hmer2 (by linarith)))
    linarith
  exact riesz_bound_algebra ha hE1 (sq_nonneg _)
    (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) rfl hTE hTO hS1 hD1

/-- **Feasibility at an aperture is square-root cancellation of the Riesz mean at its scale.** -/
theorem exists_riesz_le_of_feasible :
    ∃ C : ℝ, ∀ {q a : ℝ}, 0 ≤ Real.log q → 1 ≤ a → ∀ {w : ℕ → ℝ}, Dominated w →
      Feasible q a w →
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n * (2 * a - Real.log n)| ≤
        (3 * Real.log q + C * (1 + a) ^ 3) * Real.exp a := by
  obtain ⟨C, hC⟩ := exists_riesz_le_of_polar_nonneg
  refine ⟨C, fun {q a} hx ha w hw hfe => ?_⟩
  have hδ : 0 < Real.exp (-a) := Real.exp_pos _
  exact hC hx ha hw
    (hfe _ (contDiff_ofReal_packet ((contDiff_evenPolar a _).of_le (by norm_num)))
      (tsupport_ofReal_subset_of_eq_zero fun u hu => evenPolar_eq_zero hδ hu))
    (hfe _ (contDiff_ofReal_packet ((contDiff_oddPolar a _).of_le (by norm_num)))
      (tsupport_ofReal_subset_of_eq_zero fun u hu => oddPolar_eq_zero hδ hu))

/-- **A dominated system without cancellation fails beyond the trivial aperture.** If the
Riesz mean of the contacts at `Y = e^{2a}` is at least `c Y` in absolute value and
`3 log q + C (1 + a)³ < c e^{a}`, the system is infeasible at aperture `a`. -/
theorem exists_not_feasible_of_riesz_ge :
    ∃ C : ℝ, ∀ {q a c : ℝ}, 0 ≤ Real.log q → 1 ≤ a → ∀ {w : ℕ → ℝ}, Dominated w →
      c * Real.exp (2 * a) ≤
        |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n * (2 * a - Real.log n)| →
      3 * Real.log q + C * (1 + a) ^ 3 < c * Real.exp a → ¬ Feasible q a w := by
  obtain ⟨C, hC⟩ := exists_riesz_le_of_feasible
  refine ⟨C, fun {q a c} hx ha w hw hR hbig hfe => ?_⟩
  have h := hC hx ha hw hfe
  have e : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hR' : c * (Real.exp a * Real.exp a) ≤
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n * (2 * a - Real.log n)| := by
    rw [← e]
    exact hR
  have h2 := mul_lt_mul_of_pos_right hbig (Real.exp_pos a)
  linarith

/-! ### The twisted part of a quadratic ring -/

/-- The energy of the second archimedean factor is at most `π ∫ |F|²`. -/
theorem placeEnergy_le {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    placeEnergy χ F ≤ π * ∫ x, ‖F x‖ ^ 2 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hmass : 0 ≤ ∫ x, ‖F x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  unfold placeEnergy
  split_ifs
  · positivity
  · have hI := _root_.RHTower.integrable_normSq_paperFT hF hFs
    have hle : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) ≤
        ∫ τ : ℝ, π * ‖paperFT F τ‖ ^ 2 := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun τ =>
        mul_nonneg (sq_nonneg _) (div_nonneg hπ.le (Real.cosh_pos _).le)) (hI.const_mul π)
        (Eventually.of_forall fun τ => ?_)
      show ‖paperFT F τ‖ ^ 2 * (π / Real.cosh (π * τ)) ≤ π * ‖paperFT F τ‖ ^ 2
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (div_le_self hπ.le (Real.one_le_cosh _)) (sq_nonneg _)
    rw [integral_const_mul, _root_.RHTower.integral_norm_paperFT_sq hF hFs] at hle
    have h1 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
    have e : 1 / (2 * π) * (π * (2 * π * ∫ x, ‖F x‖ ^ 2)) = π * ∫ x, ‖F x‖ ^ 2 := by
      field_simp
    rwa [e] at h1

/-- **The sign of the twisted part at an aperture bounds the Riesz mean of the character.**
There is an absolute constant `C` such that for every primitive character `χ` of conductor
`q > 1` and every aperture `a ≥ 1`: if the sum over the zeros of `L(s, χ)` is nonnegative on the
even and on the odd polar packet of margin `e^{−a}`, then
`|Σ_{2 ≤ n ≤ e^{2a}} Λ(n) Re χ(n) (2a − log n)| ≤ (3 (log q + π) + C (1 + a)³) e^{a}`. -/
theorem exists_riesz_twist_le_of_nonneg :
    ∃ C : ℝ, ∀ {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
      (hprim : χ.IsPrimitive) {a : ℝ}, 1 ≤ a →
      0 ≤ twistedZeroSum hq hprim (evenPolar a (Real.exp (-a))) →
      0 ≤ twistedZeroSum hq hprim (oddPolar a (Real.exp (-a))) →
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, twistWeight χ n * (2 * a - Real.log n)| ≤
        (3 * (Real.log q + π) + C * (1 + a) ^ 3) * Real.exp a := by
  obtain ⟨C, hC⟩ := exists_riesz_le_of_polar_nonneg
  refine ⟨C, fun {q} _ hq χ hprim a ha hE hO => ?_⟩
  have hδ : 0 < Real.exp (-a) := Real.exp_pos _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hlog : Real.log ((q : ℝ) * Real.exp π) = Real.log q + π := by
    rw [Real.log_mul hq0.ne' (Real.exp_pos π).ne', Real.log_exp]
  -- a nonnegative zero sum is feasibility of the two packets at the conductor `q e^{π}`
  have key : ∀ {f : ℝ → ℝ}, ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
      0 ≤ twistedZeroSum hq hprim f →
      0 ≤ systemForm (twistWeight χ) ((q : ℝ) * Real.exp π) a (fun u => (f u : ℂ)) := by
    intro f hf h0 hZ
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
    have hF := contDiff_ofReal_packet hf2
    have hFs := tsupport_ofReal_subset_of_eq_zero h0
    rw [twistedZeroSum_eq_systemForm hq hprim hf2 hFs] at hZ
    have hpl := placeEnergy_le χ hF hFs
    rw [systemForm_conductor_mul_exp hq0 π hF hFs]
    linarith
  have h := hC (q := (q : ℝ) * Real.exp π) (a := a) (by rw [hlog]; linarith) ha
    (dominated_twistWeight χ)
    (key (contDiff_evenPolar a _) (fun u hu => evenPolar_eq_zero hδ hu) hE)
    (key (contDiff_oddPolar a _) (fun u hu => oddPolar_eq_zero hδ hu) hO)
  rwa [hlog] at h

end GaloisForLFunctions.SelectiveArithmetic
