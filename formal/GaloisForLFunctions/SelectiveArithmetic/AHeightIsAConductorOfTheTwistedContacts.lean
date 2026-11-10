import GaloisForLFunctions.SelectiveArithmetic.APoleAtTheHeightFailsBeyondTheTrivialAperture
import GaloisForLFunctions.SelectiveArithmetic.TheSignIsSquareRootCancellationOfTheRieszMean

/-!
# A height is a conductor of the twisted contacts

A packet modulated to the height `t`, `F(u) = e^{−itu} f(u)`, sees the contacts of a system with
the phase `cos(t log n)` and the archimedean place at the height `t`. This module turns both into
the language of the conductor.

The **contacts seen from the height `t`** are `w_t(n) = w(n) cos(t log n)`.

* **Subadditivity of the archimedean symbol** (`archimedeanWeilSymbol_add_le`):
  `S_∞(τ + t) ≤ S_∞(τ) + log(2 + |t|) + A₂`.
* **The height transfer** (`systemForm_modulatedTest_le`, `systemForm_modulatedTest_ge`):
  `𝔚_{w_t,q}(f) + (log(2 + |t|) − A₃) ∫ f² − 2 ∫ f'² ≤ 𝔚_{w,q}(e^{−itu} f) ≤
  𝔚_{w_t,q}(f) + (log(2 + |t|) + A₂) ∫ f²`.
  The form of a system at the height `t` is the form of the twisted contacts at the conductor
  `q (2 + |t|)`, exactly from above and up to the shape of the packet from below.
* **The sign at every height is cancellation of the twisted Riesz mean**
  (`exists_twisted_riesz_le_of_feasible`): a dominated system that is feasible at `(q, a)` has
  `|Σ_{n ≤ e^{2a}} w(n) cos(t log n)(2a − log n)| ≤ (log q + log(2 + |t|))(e^{a} + 2a) +
  C (1 + a)³ e^{a}` at every height `t`.
* **Cancellation of the twisted contacts buys the ladder of the analytic conductor**
  (`systemForm_modulated_ge_of_twisted_cancellation`, `exists_height_cancellation_margin`): a
  saving `n^{1/2 + γ}` in the partial sums of `w_t` gives the sign at the height `t`, on packets of
  bounded shape, up to the rung `κ < 1/(2γ)` of the mass `log q + log(2 + |t|)`.
* **All packets** (`feasible_of_symbol_nonneg`, `feasible_of_twisted_cancellation`): the form is
  a Fourier multiplier, so a system is feasible as soon as its symbol plus `log q` is nonnegative;
  a saving in the partial sums of `w_τ` at every height `τ`, with a constant that may grow like
  the archimedean symbol, gives feasibility with no condition on the shape.

So the exchange rate of the ladder is a law of the twisted contacts: the sign on packets of
bounded shape reads the partial sums of `w`, the sign on all packets reads the partial sums of
`w(n) n^{−iτ}` at every height. The system aligned with a height (`alignedWeight`) is the twist of
`Λ` by its own height: its twisted contacts are `Λ(n) cos²(t log n)` and have no cancellation.
-/

open Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### The contacts seen from a height -/

/-- The contacts of a system seen from the height `t`: `w(n) cos(t log n)`. -/
def twistedWeight (w : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ := w n * Real.cos (t * Real.log n)

theorem dominated_twistedWeight {w : ℕ → ℝ} (hw : Dominated w) (t : ℝ) :
    Dominated (twistedWeight w t) := fun n => by
  unfold twistedWeight
  rw [abs_mul]
  calc |w n| * |Real.cos (t * Real.log n)| ≤ |w n| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ = |w n| := mul_one _
    _ ≤ Λ n := hw n

/-- The system aligned with a height is the twist of `Λ` by that height. -/
theorem alignedWeight_eq_twistedWeight (t : ℝ) :
    alignedWeight t = twistedWeight (fun n => Λ n) t := rfl

/-- **The contact form on a packet modulated to the height `t`** is the contact form of the
twisted contacts on the packet. -/
theorem contactForm_modulatedTest_eq (w : ℕ → ℝ) (t : ℝ) (f : ℝ → ℝ) (N : ℕ) :
    contactForm w (_root_.RHTower.modulatedTest t f) N =
      contactForm (twistedWeight w t) (fun u => (f u : ℂ)) N := by
  rw [contactForm_modulatedTest, contactForm_packet]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold twistedWeight
  ring

/-! ### Subadditivity of the archimedean symbol -/

/-- The constant of the height transfer. -/
def heightConstant : ℝ :=
  |_root_.RHTower.digammaVerticalCoercivityConst (1 / 4)| + Real.log 2 + Real.log π + 4

theorem heightConstant_nonneg : 0 ≤ heightConstant := by
  unfold heightConstant
  have h1 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith [abs_nonneg (_root_.RHTower.digammaVerticalCoercivityConst (1 / 4))]

/-- **The archimedean symbol is subadditive up to a constant**:
`S_∞(τ + t) ≤ S_∞(τ) + log(2 + |t|) + A₂`. -/
theorem archimedeanWeilSymbol_add_le (τ t : ℝ) :
    _root_.RHTower.archimedeanWeilSymbol ((τ + t) / (2 * π)) ≤
      _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) + Real.log (2 + |t|) +
        heightConstant := by
  have h1 := _root_.RHTower.archimedeanWeilSymbol_le_log_add (τ + t)
  have h2 := log_sub_le_archimedeanWeilSymbol τ
  have habs : |τ + t| ≤ |τ| + |t| :=
    abs_le.mpr ⟨by linarith [neg_abs_le τ, neg_abs_le t],
      by linarith [le_abs_self τ, le_abs_self t]⟩
  have h3 : Real.log (1 + |τ + t|) ≤ Real.log (2 + |τ|) + Real.log (2 + |t|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg τ, abs_nonneg t, mul_nonneg (abs_nonneg τ) (abs_nonneg t)]
  unfold heightConstant
  linarith [le_abs_self (_root_.RHTower.digammaVerticalCoercivityConst (1 / 4))]

/-- **Modulating a packet to the height `t` raises its archimedean energy by at most
`(log(2 + |t|) + A₂)` times its mass.** -/
theorem integral_arch_modulated_le_add {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (t : ℝ) :
    1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      1 / (2 * π) * (∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) +
        (Real.log (2 + |t|) + heightConstant) * ∫ u, f u ^ 2 := by
  have hF := _root_.RHTower.modulatedTest_contDiff t hf
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hG : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet hf
  have hGs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  have hφ := _root_.RHTower.integrable_normSq_paperFT_mul_arch hF hFs
  have hI := _root_.RHTower.integrable_normSq_paperFT hG hGs
  have hIa := _root_.RHTower.integrable_normSq_paperFT_mul_arch hG hGs
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = Real.log (2 + |t|) + heightConstant := ⟨_, rfl⟩
  rw [← hc]
  -- the transform of the modulated packet at `τ + t` is the transform of the packet at `τ`
  have hshift : ∀ τ : ℝ, paperFT (_root_.RHTower.modulatedTest t f) ((τ + t : ℝ) : ℂ) =
      paperFT (fun u => (f u : ℂ)) (τ : ℂ) := fun τ => by
    rw [paperFT_modulatedTest]
    congr 1
    push_cast
    ring
  have htrans : ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) =
      ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) ((τ + t : ℝ) : ℂ)‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol ((τ + t) / (2 * π)) :=
    (integral_add_right_eq_self (fun τ : ℝ =>
      ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) t).symm
  have hmono : ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) ((τ + t : ℝ) : ℂ)‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol ((τ + t) / (2 * π)) ≤
      ∫ τ : ℝ, (‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) +
        c * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2) := by
    refine integral_mono (hφ.comp_add_right t) (hIa.add (hI.const_mul c)) fun τ => ?_
    show ‖paperFT (_root_.RHTower.modulatedTest t f) ((τ + t : ℝ) : ℂ)‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol ((τ + t) / (2 * π)) ≤
      ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) +
        c * ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2
    rw [hshift]
    have h3 : _root_.RHTower.archimedeanWeilSymbol ((τ + t) / (2 * π)) ≤
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) + c := by
      rw [hc]
      linarith [archimedeanWeilSymbol_add_le τ t]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖paperFT (fun u => (f u : ℂ)) τ‖)]
  rw [integral_add hIa (hI.const_mul c), integral_const_mul,
    _root_.RHTower.integral_norm_paperFT_sq hG hGs, integral_norm_ofReal_sq] at hmono
  rw [htrans]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e2 : 1 / (2 * π) * (c * (2 * π * ∫ u, f u ^ 2)) = c * ∫ u, f u ^ 2 := by
    field_simp
  rw [mul_add, e2] at h1
  exact h1

/-! ### The height transfer -/

/-- **The height transfer, from above.** The form of a system on a packet modulated to the height
`t` is at most the form of the twisted contacts on the packet plus `(log(2 + |t|) + A₂)` times
its mass. -/
theorem systemForm_modulatedTest_le {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (w : ℕ → ℝ) (q t : ℝ) :
    systemForm w q a (_root_.RHTower.modulatedTest t f) ≤
      systemForm (twistedWeight w t) q a (fun u => (f u : ℂ)) +
        (Real.log (2 + |t|) + heightConstant) * ∫ u, f u ^ 2 := by
  have hF := _root_.RHTower.modulatedTest_contDiff t hf
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hG : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet hf
  have hGs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  rw [systemForm_eq hF hFs, systemForm_eq hG hGs, integral_norm_modulatedTest_sq,
    integral_norm_ofReal_sq, contactForm_modulatedTest_eq]
  linarith [integral_arch_modulated_le_add hf h0 t]

/-- **The height transfer, from below.** On a `C³` packet the form at the height `t` is at least
the form of the twisted contacts plus `(log(2 + |t|) − A₁ − 5) ∫ f² − 2 ∫ f'²`. -/
theorem systemForm_modulatedTest_ge {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (w : ℕ → ℝ) (q t : ℝ) :
    systemForm (twistedWeight w t) q a (fun u => (f u : ℂ)) +
        (Real.log (2 + |t|) - archGrowthConstant - 5) * (∫ u, f u ^ 2) -
        2 * ∫ u, deriv f u ^ 2 ≤
      systemForm w q a (_root_.RHTower.modulatedTest t f) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hF := _root_.RHTower.modulatedTest_contDiff t hf2
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hG : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet hf2
  have hGs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  rw [systemForm_eq hF hFs, systemForm_eq hG hGs, integral_norm_modulatedTest_sq,
    integral_norm_ofReal_sq, contactForm_modulatedTest_eq]
  have h1 := integral_arch_modulated_ge hf h0 t
  have h2 := integral_arch_le hf h0
  linarith

/-! ### The sign at every height is cancellation of the twisted Riesz mean -/

/-- **Feasibility is square-root cancellation of the twisted Riesz means at every height.** There
is an absolute constant `C` such that a dominated system that is feasible at `(q, a)`, `a ≥ 1`,
satisfies at every height `t`
`|Σ_{2 ≤ n ≤ e^{2a}} w(n) cos(t log n)(2a − log n)| ≤
(log q + log(2 + |t|))(e^{a} + 2a) + C (1 + a)³ e^{a}`. -/
theorem exists_twisted_riesz_le_of_feasible :
    ∃ C : ℝ, ∀ {q a : ℝ}, 0 ≤ Real.log q → 1 ≤ a → ∀ {w : ℕ → ℝ}, Dominated w →
      Feasible q a w → ∀ t : ℝ,
      |∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          twistedWeight w t n * (2 * a - Real.log n)| ≤
        (Real.log q + Real.log (2 + |t|)) * (Real.exp a + 2 * a) +
          C * (1 + a) ^ 3 * Real.exp a := by
  obtain ⟨C, hC⟩ := exists_riesz_le_of_polar_nonneg
  refine ⟨C + 3 * heightConstant, fun {q a} hx ha w hw hfe t => ?_⟩
  have ha0 : 0 ≤ a := by linarith
  have hδ : 0 < Real.exp (-a) := Real.exp_pos _
  have hL0 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hH := heightConstant_nonneg
  -- the twisted system at the conductor multiplied by the height is positive on real packets
  obtain ⟨q', hq'⟩ : ∃ q' : ℝ,
      q' = Real.exp (Real.log q + Real.log (2 + |t|) + heightConstant) := ⟨_, rfl⟩
  have hlogq' : Real.log q' = Real.log q + Real.log (2 + |t|) + heightConstant := by
    rw [hq', Real.log_exp]
  have key : ∀ {f : ℝ → ℝ}, ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
      0 ≤ systemForm (twistedWeight w t) q' a (fun u => (f u : ℂ)) := by
    intro f hf h0
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
    have h1 := hfe _ (_root_.RHTower.modulatedTest_contDiff t hf2)
      (_root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0))
    have h2 := systemForm_modulatedTest_le hf2 h0 w q t
    have hG : ContDiff ℝ 2 fun u => (f u : ℂ) := contDiff_ofReal_packet hf2
    have hGs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
      tsupport_ofReal_subset_of_eq_zero h0
    rw [systemForm_eq hG hGs, hlogq', integral_norm_ofReal_sq]
    rw [systemForm_eq hG hGs, integral_norm_ofReal_sq] at h2
    linarith
  have h := hC (by rw [hlogq']; linarith) ha (dominated_twistedWeight hw t)
    (key (contDiff_evenPolar a _) fun u hu => evenPolar_eq_zero hδ hu)
    (key (contDiff_oddPolar a _) fun u hu => oddPolar_eq_zero hδ hu)
  rw [hlogq'] at h
  -- the constant of the height is absorbed
  have hE1 : 1 ≤ Real.exp a := Real.one_le_exp ha0
  have haE : a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  have hs1 : (1 : ℝ) ≤ (1 + a) ^ 3 := one_le_pow₀ (by linarith)
  have h4 : heightConstant * (Real.exp a + 2 * a) ≤ heightConstant * (3 * Real.exp a) :=
    mul_le_mul_of_nonneg_left (by linarith) hH
  have h5 : 3 * heightConstant * Real.exp a ≤ 3 * heightConstant * Real.exp a * (1 + a) ^ 3 :=
    le_mul_of_one_le_right (by positivity) hs1
  linarith

/-! ### Cancellation of the twisted contacts buys the sign at the height -/

/-- **The form at a height of a system whose twisted contacts cancel.** If
`|Σ_{2 ≤ k ≤ n} w(k) cos(t log k)| ≤ C √n n^{γ}`, then on a `C³` packet `f` vanishing off
`(−a, a)` and modulated to the height `t`:
`𝔚_{w,q}(F) ≥ (log q + log(2 + |t|) − A₀ − A₁ − 5 − 3c) ∫ f² − (c + 2) ∫ f'²`,
`c = C e^{2γa} (2 + 2a)`. -/
theorem systemForm_modulated_ge_of_twisted_cancellation {w : ℕ → ℝ} {C γ t : ℝ} (hC : 0 ≤ C)
    (hγ : 0 ≤ γ) (hw : HasCancellation (twistedWeight w t) C γ) {a : ℝ} (ha : 0 ≤ a)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (h0 : ∀ u, a ≤ |u| → f u = 0) (q : ℝ) :
    (Real.log q + Real.log (2 + |t|) - archConstant - archGrowthConstant - 5 -
          3 * (C * Real.exp (2 * γ * a) * (2 + 2 * a))) * (∫ u, f u ^ 2) -
        (C * Real.exp (2 * γ * a) * (2 + 2 * a) + 2) * ∫ u, deriv f u ^ 2 ≤
      systemForm w q a (_root_.RHTower.modulatedTest t f) := by
  have h1 := systemForm_ge_of_cancellation hC hγ hw ha hf h0 q
  have h2 := systemForm_modulatedTest_ge hf h0 w q t
  linarith

/-- **The exchange rate at a height.** For `2γκ < 1` there is `M₀` such that whenever the mass
`x = log q + log(2 + |t|) − A₁ − 5` is at least `M₀` and `a ≤ κ log x`: a system whose contacts
twisted by the height `t` have cancellation `(C, γ)` satisfies
`𝔚_{w,q}(F) ≥ (x/2) (∫ f² − ∫ f'²) − 2 ∫ f'²` on packets modulated to the height `t`. -/
theorem exists_height_cancellation_margin {C γ κ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (hγκ : 2 * γ * κ < 1) :
    ∃ M₀ : ℝ, ∀ q t x : ℝ, x = Real.log q + Real.log (2 + |t|) - archGrowthConstant - 5 →
      M₀ ≤ x → ∀ a : ℝ, 0 ≤ a → a ≤ κ * Real.log x →
      ∀ {w : ℕ → ℝ}, HasCancellation (twistedWeight w t) C γ → ∀ {f : ℝ → ℝ},
        ContDiff ℝ 3 f → (∀ u, a ≤ |u| → f u = 0) →
        x / 2 * ((∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2) - 2 * ∫ u, deriv f u ^ 2 ≤
          systemForm w q a (_root_.RHTower.modulatedTest t f) := by
  obtain ⟨M₀, hM₀⟩ := exists_cancellation_margin hC hγ hκ hγκ
  refine ⟨M₀, fun q t x hx hxM a ha0 ha w hw f hf h0 => ?_⟩
  have hlogQ : Real.log (Real.exp x) = x := Real.log_exp x
  have h1 := hM₀ (Real.exp x) (by rw [hlogQ]; exact hxM) a ha0 (by rw [hlogQ]; exact ha) hw hf h0
  rw [hlogQ] at h1
  have h2 := systemForm_modulatedTest_ge hf h0 w q t
  -- the conductor `e^{x}` adds `(x − log q) ∫ f²` to the form of the twisted contacts
  have hG : ContDiff ℝ 2 fun u => (f u : ℂ) :=
    contDiff_ofReal_packet (hf.of_le (by norm_num))
  have hGs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a :=
    tsupport_ofReal_subset_of_eq_zero h0
  rw [systemForm_eq hG hGs, hlogQ, integral_norm_ofReal_sq] at h1
  rw [systemForm_eq hG hGs, integral_norm_ofReal_sq] at h2
  rw [hx] at h1 ⊢
  linarith

/-! ### All packets -/

/-- **The symbol criterion.** The form of a system is a Fourier multiplier: if its symbol plus
`log q` is nonnegative at every frequency, the system is feasible. -/
theorem feasible_of_symbol_nonneg {q a : ℝ} {w : ℕ → ℝ}
    (h : ∀ τ : ℝ, 0 ≤ _root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
      Real.log q) : Feasible q a w := fun F _ _ => by
  unfold systemForm
  exact mul_nonneg (by positivity)
    (integral_nonneg fun τ => mul_nonneg (sq_nonneg _) (h τ))

/-- The symbol of a system at the frequency `τ` is the archimedean symbol minus twice the sum of
the contacts twisted by `τ`, weighted by `1/√n`. -/
theorem weilAtomSymbol_eq_twisted (w : ℕ → ℝ) (N : ℕ) (τ : ℝ) :
    _root_.RHTower.weilAtomSymbol w N (τ / (2 * π)) =
      _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) -
        2 * ∑ n ∈ Finset.Icc 2 N, twistedWeight w τ n / Real.sqrt n := by
  have e : ∑ n ∈ Finset.Icc 2 N, w n * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))) =
      2 * ∑ n ∈ Finset.Icc 2 N, twistedWeight w τ n / Real.sqrt n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have harg : 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n := by field_simp
    rw [harg]
    unfold twistedWeight
    ring
  unfold _root_.RHTower.weilAtomSymbol
  linarith

/-- **Cancellation of the twisted contacts at every height buys feasibility.** If at every
height `τ` the contacts twisted by `τ` have cancellation `(C(τ), γ)` and
`2 C(τ) e^{2γa} (2 + 2a) ≤ log q + S_∞(τ)`, the system is feasible at `(q, a)`: no condition on
the shape of the packet remains. -/
theorem feasible_of_twisted_cancellation {q a γ : ℝ} (ha : 0 ≤ a) (hγ : 0 ≤ γ) {w : ℕ → ℝ}
    {C : ℝ → ℝ} (hC : ∀ τ, 0 ≤ C τ)
    (hw : ∀ τ, HasCancellation (twistedWeight w τ) (C τ) γ)
    (hb : ∀ τ, 2 * (C τ * Real.exp (2 * γ * a) * (2 + 2 * a)) ≤
      Real.log q + _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) :
    Feasible q a w := by
  refine feasible_of_symbol_nonneg fun τ => ?_
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊Real.exp (2 * a)⌋₊ := ⟨_, rfl⟩
  rw [← hNdef]
  have hexp1 : (1 : ℝ) ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hN : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by rw [Nat.cast_one]; exact hexp1)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNle : (N : ℝ) ≤ Real.exp (2 * a) := by
    rw [hNdef]
    exact Nat.floor_le (Real.exp_pos _).le
  have hpow : (N : ℝ) ^ γ ≤ Real.exp (2 * γ * a) := by
    have h1 : (N : ℝ) ^ γ ≤ Real.exp (2 * a) ^ γ :=
      Real.rpow_le_rpow (by linarith) hNle hγ
    rw [← Real.exp_mul] at h1
    rwa [show 2 * a * γ = 2 * γ * a by ring] at h1
  have hlog : Real.log N ≤ 2 * a := by
    calc Real.log N ≤ Real.log (Real.exp (2 * a)) := Real.log_le_log (by linarith) hNle
      _ = 2 * a := Real.log_exp _
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hcN : C τ * (N : ℝ) ^ γ * (2 + Real.log N) ≤
      C τ * Real.exp (2 * γ * a) * (2 + 2 * a) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hpow (hC τ)) (by linarith) (by linarith)
      (mul_nonneg (hC τ) (Real.exp_pos _).le)
  -- summation by parts for the contacts twisted by `τ`, against `1/√n`
  have h := (abs_le.mp (abs_sum_contact_cos_le (hC τ) hγ (hw τ) hN 0)).2
  have e : ∑ n ∈ Finset.Icc 2 N,
        twistedWeight w τ n * (Real.cos (0 * Real.log n) / Real.sqrt n) =
      ∑ n ∈ Finset.Icc 2 N, twistedWeight w τ n / Real.sqrt n :=
    Finset.sum_congr rfl fun n _ => by
      rw [zero_mul, Real.cos_zero]
      ring
  rw [e, abs_zero, add_zero, mul_one] at h
  rw [weilAtomSymbol_eq_twisted]
  linarith [hb τ]

end GaloisForLFunctions.SelectiveArithmetic
