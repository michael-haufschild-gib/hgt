import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.BezoutDeterminesTheConstantOfTheCounterterm
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSignIsCarriedByTheContacts
import GaloisForLFunctions.RHTower.WeilPositivityBeurlingPerturbationRigidity
import GaloisForLFunctions.RHTower.PolarConeAbelRigidity
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion

/-!
# The counterterm pays for the contacts at the supremum of their symbol

On the comb of the integers take the contacts `Λ + δ` in place of the contact orders `Λ`, and the
counterterm `log(n/2π) + c` in place of `log(n/2π)`. The deviation `δ` has the symbol
`P_δ(τ) = Σ_{n ≥ 2} 2 δ(n) n^{-1/2} cos(τ log n)`, a function with mean zero.

* **The pairing** (`tendsto_pairPairing`): jets, the contacts `Λ + δ` and the counterterm
  `log(n/2π) + c` tend to `2 d₁ d₂` minus the functional of the pair,
  `Re W_{Λ+δ}(f ⋆ f̃) + c ∫f²`.
* **The functional in terms of the symbol** (`two_pi_mul_pairForm_eq`): on a packet,
  `2π (Re W_{Λ+δ} + c ∫f²) = 2π Z(f) + ∫ |f̂(τ)|² (c − P_δ(τ)) dτ`, with `Z` the sum over the
  zeros of `ζ`.
* **The exchange law** (`combBezoutWith_iff`): for `Σ |δ(n)| n^{-1/2} < ∞`, Bézout holds for the
  pair `(δ, c)` iff the Riemann hypothesis holds and `P_δ(τ) ≤ c` for every `τ`. Where
  `P_δ(τ₁) > c`, tests in the radical of the form of `ζ` concentrated at `τ₁` violate the
  inequality on a packet with both degrees zero (`exists_packet_pairForm_neg`), without
  hypothesis.
* **The constant** (`nonneg_of_combBezoutWith`, `combBezoutWith_zero_right_iff`): the inequality
  forces `c ≥ 0`, and with `c = 0` it forces `δ = 0`.
* **One contact** (`combBezoutWith_contactAt_iff`): with the contact at `n₀` changed by `t`,
  Bézout holds iff the Riemann hypothesis holds and `c ≥ 2|t|/√n₀`.

So the pairs of contact weights and constants that are not refuted form the epigraph of
`δ ↦ sup P_δ`, a convex cone with its vertex at the square of the integers: `δ = 0`, constant
`2π`. A wrong contact is paid in the counterterm at a fixed rate, and a construction that leaves
the constant free does not determine the contacts.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {δ : ℕ → ℝ} {f : ℝ → ℝ}

/-! ### The pairing of a pair -/

/-- Bézout on the comb of the integers with the contacts `Λ + δ` and the counterterm
`log(n/2π) + c`. -/
def CombBezoutWith (δ : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
    ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N -
        c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
        2 * weightedContact (fun n => (Λ n : ℝ) + δ n) f (3 * K) N) atTop (𝓝 l) →
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- The functional of the pair `(δ, c)` on a packet: `Re W_{Λ+δ}(g ⋆ g̃) + c ∫g²`. -/
def pairForm (δ : ℕ → ℝ) (c : ℝ) (g : ℝ → ℝ) : ℝ :=
  (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ) + δ n)
    (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re + c * ∫ u, g u ^ 2

/-- **The pairing of a pair.** Jets, the contacts `Λ + δ` and the counterterm `log(n/2π) + c`
tend to twice the product of the degrees minus the functional of the pair. -/
theorem tendsto_pairPairing (δ : ℕ → ℝ) (c : ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreeForm f (3 * K) N -
        c * ∑ n ∈ Ioc N (N + 3 * K * N), degreeSample f N n ^ 2 / n +
        2 * weightedContact (fun n => (Λ n : ℝ) + δ n) f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        pairForm δ c f)) := by
  have h := (tendsto_degreeForm_add_weightedContact (fun n => (Λ n : ℝ) + δ n) hf hfc hK
    hsupp).sub ((tendsto_degreeMass hf.continuous hK hsupp).const_mul c)
  have e : 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) - pairForm δ c f =
      2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
          (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ) + δ n)
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re -
        c * ∫ u, f u ^ 2 := by
    unfold pairForm
    ring
  rw [e]
  exact h.congr fun N => by ring

/-- The functional of a pair does not see a translation of the packet. -/
theorem pairForm_translate (δ : ℕ → ℝ) (c : ℝ) (g : ℝ → ℝ) (s : ℝ) :
    pairForm δ c (fun u => g (u - s)) = pairForm δ c g := by
  show (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ) + δ n)
      (EF.weilTest (fun u => ((g (u - s) : ℝ) : ℂ)) (fun u => ((g (u - s) : ℝ) : ℂ)))).re +
      c * ∫ u, g (u - s) ^ 2 = pairForm δ c g
  rw [weilTest_packet_translate g s, integral_sub_right_eq_self (fun u => g u ^ 2) s]
  rfl

/-- Bézout for a pair is the positivity of its functional on all packets. -/
theorem combBezoutWith_iff_pairForm (δ : ℕ → ℝ) (c : ℝ) :
    CombBezoutWith δ c ↔
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ pairForm δ c g := by
  constructor
  · intro h g hg hgc
    obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
    have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
    have hgc' : HasCompactSupport fun u => g (u - s) :=
      hgc.comp_homeomorph (Homeomorph.subRight s)
    have hle := h _ hg' hgc' K hK hsupp _ (tendsto_pairPairing δ c hg' hgc' hK hsupp)
    rw [pairForm_translate] at hle
    linarith
  · intro h f hf hfc K hK hsupp l hl
    rw [tendsto_nhds_unique hl (tendsto_pairPairing δ c hf hfc hK hsupp)]
    linarith [h f hf hfc]

/-! ### The symbol of the deviation against a test -/

/-- A packet, as a complex test, is supported in a symmetric interval. -/
theorem exists_tsupport_ofReal_subset_Icc (hfc : HasCompactSupport f) :
    ∃ a : ℝ, tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a := by
  obtain ⟨a, ha⟩ :=
    (hasCompactSupport_ofReal_packet hfc).isCompact.isBounded.subset_closedBall 0
  refine ⟨a, fun x hx => ?_⟩
  have := ha hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact abs_le.mp this

section Symbol

variable {a : ℝ} {F : ℝ → ℂ}

theorem integrable_normSq_paperFT_mul_perturbationSymbol
    (hsum : Summable fun n => |δ n| / Real.sqrt n) (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    Integrable fun τ : ℝ => ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ := by
  have hint := _root_.RHTower.integrable_normSq_paperFT hF hFs
  obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  have hHc : Continuous fun τ : ℝ => ‖paperFT F τ‖ ^ 2 :=
    (_root_.RHTower.continuous_paperFT_real_of_integrable
      (hF.continuous.integrable_of_hasCompactSupport hFc)).norm.pow 2
  refine (hint.mul_const (∑' n : ℕ, 2 * (|δ n| / Real.sqrt n))).mono'
    (hHc.mul (_root_.RHTower.continuous_perturbationSymbol hsum)).aestronglyMeasurable
    (Eventually.of_forall fun τ => ?_)
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (_root_.RHTower.abs_perturbationSymbol_le hsum τ) (sq_nonneg _)

/-- A symbol below `c` has energy at most `c` times the mass. -/
theorem integral_normSq_mul_perturbationSymbol_le
    (hsum : Summable fun n => |δ n| / Real.sqrt n) (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Set.Icc (-a) a) {c : ℝ}
    (hP : ∀ τ, _root_.RHTower.perturbationSymbol δ τ ≤ c) :
    ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ ≤
      c * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_normSq_paperFT_mul_perturbationSymbol hsum hF hFs)
    ((_root_.RHTower.integrable_normSq_paperFT hF hFs).const_mul c) fun τ => ?_
  show ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ ≤ c * ‖paperFT F τ‖ ^ 2
  nlinarith [hP τ, sq_nonneg ‖paperFT F τ‖]

/-- The energy of the symbol is bounded below by its sup norm times the mass. -/
theorem neg_mul_le_integral_normSq_mul_perturbationSymbol
    (hsum : Summable fun n => |δ n| / Real.sqrt n) (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    -((∑' n : ℕ, 2 * (|δ n| / Real.sqrt n)) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ := by
  rw [← integral_const_mul, ← integral_neg]
  refine integral_mono
    ((_root_.RHTower.integrable_normSq_paperFT hF hFs).const_mul _).neg
    (integrable_normSq_paperFT_mul_perturbationSymbol hsum hF hFs) fun τ => ?_
  have h := (abs_le.mp (_root_.RHTower.abs_perturbationSymbol_le hsum τ)).1
  show -((∑' n : ℕ, 2 * (|δ n| / Real.sqrt n)) * ‖paperFT F τ‖ ^ 2) ≤
    ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ
  nlinarith [sq_nonneg ‖paperFT F τ‖]

end Symbol

/-- **The functional of a pair in terms of the symbol.** On a packet in a window,
`2π (Re W_{Λ+δ} + c ∫f²)` is `2π` times the sum over the zeros plus the energy of `c − P_δ`. -/
theorem two_pi_mul_pairForm_eq (hsum : Summable fun n => |δ n| / Real.sqrt n) (c : ℝ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {a : ℝ}
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a) :
    2 * π * pairForm δ c f = 2 * π * zeroSum f +
      (c * (∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2) -
        ∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
          _root_.RHTower.perturbationSymbol δ τ) := by
  have hδ3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsuppW := window_of_support hK hsupp
  have h1L : (0 : ℝ) < 1 + ((3 * K : ℕ) : ℝ) := by positivity
  have hQ : ∀ n : ℕ, 3 * K < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_window hδ3 hsuppW (Real.log_le_log h1L (by
      have : ((3 * K : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith))
  have h1 := re_weilFullFunctional_packet_of_weight (fun n => (Λ n : ℝ) + δ n) f hQ
  have h2 := re_weilFullFunctional_packet_of_weight (fun n => (Λ n : ℝ)) f hQ
  have hz := zeroSum_eq_weilFullFunctional hf hfc
  have hFd := contDiff_ofReal_packet hf
  -- the energy of the symbol is the deviation of the contacts on the autocorrelation
  have hts : (∫ τ : ℝ, ‖paperFT (fun u => (f u : ℂ)) τ‖ ^ 2 *
        _root_.RHTower.perturbationSymbol δ τ) =
      2 * π * (2 * ∑ k ∈ Icc 2 (3 * K), δ k / Real.sqrt k * packetAutocorr f (Real.log k)) := by
    rw [_root_.RHTower.integral_normSq_mul_perturbationSymbol hsum hFd hfs,
      tsum_eq_sum (s := Icc 2 (3 * K)) fun n hn => ?_, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1, weilTest_packet, weilTest_packet, packetAutocorr_neg,
        ← Complex.ofReal_add, Complex.ofReal_re]
      ring
    · by_cases h2n : 2 ≤ n
      · have hn' : 3 * K < n := by
          by_contra hcon
          exact hn (Finset.mem_Icc.mpr ⟨h2n, not_lt.mp hcon⟩)
        rw [if_pos h2n, weilTest_packet, weilTest_packet, packetAutocorr_neg, hQ n hn']
        simp
      · rw [if_neg h2n]
  have hmass := _root_.RHTower.integral_norm_paperFT_sq hFd hfs
  have hnorm : (∫ x : ℝ, ‖((f x : ℝ) : ℂ)‖ ^ 2) = ∫ x, f x ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => by
      show ‖((f x : ℝ) : ℂ)‖ ^ 2 = f x ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
  have hsplit : ∑ k ∈ Icc 2 (3 * K),
        ((Λ k : ℝ) + δ k) / Real.sqrt k * packetAutocorr f (Real.log k) =
      ∑ k ∈ Icc 2 (3 * K), (Λ k : ℝ) / Real.sqrt k * packetAutocorr f (Real.log k) +
        ∑ k ∈ Icc 2 (3 * K), δ k / Real.sqrt k * packetAutocorr f (Real.log k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold pairForm
  rw [h1, hsplit, hz, h2, hts, hmass, hnorm]
  ring

/-! ### Where the symbol exceeds the constant the inequality fails -/

/-- **A test in the radical concentrated where the symbol exceeds the constant.** If
`P_δ(τ₁) > c`, some test whose transform vanishes at `±i/2` has a negative functional. -/
theorem exists_test_pair_neg (hsum : Summable fun n => |δ n| / Real.sqrt n) {c τ₁ : ℝ}
    (hτ₁ : c < _root_.RHTower.perturbationSymbol δ τ₁) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Set.Icc (-a) a ∧
      paperFT F (Complex.I / 2) = 0 ∧ paperFT F (-(Complex.I / 2)) = 0 ∧
      (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ) + δ n) (EF.weilTest F F)).re +
        c * ∫ x, ‖F x‖ ^ 2 < 0 := by
  set P : ℝ → ℝ := fun τ => _root_.RHTower.perturbationSymbol δ τ - c with hPdef
  have hPc : Continuous P :=
    (_root_.RHTower.continuous_perturbationSymbol hsum).sub continuous_const
  have hPb : ∀ τ, |P τ| ≤ (∑' n : ℕ, 2 * (|δ n| / Real.sqrt n)) + |c| := fun τ => by
    have h1 := _root_.RHTower.abs_perturbationSymbol_le hsum τ
    have h2 := abs_add_le (_root_.RHTower.perturbationSymbol δ τ) (-c)
    rw [abs_neg, ← sub_eq_add_neg] at h2
    exact h2.trans (by linarith)
  set d₁ := P τ₁ with hd₁
  have hd₁0 : 0 < d₁ := sub_pos.mpr hτ₁
  obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
    (hPc.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
  have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ P τ := by
    intro τ hτ
    have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  -- a point near `τ₁` where the limit of the radical tests does not vanish
  have hev := ((_root_.RHTower.eventually_radicalLimit_shift_ne_zero 0 τ₁).and
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0))))
  obtain ⟨τ₀, h0, hball⟩ := hev.exists
  have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
  have hlim0 : _root_.RHTower.twistLimit 0 τ₀ ≠ 0 := by
    unfold _root_.RHTower.twistLimit
    simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  set m := ‖_root_.RHTower.twistLimit 0 τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hlim0
  obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
    ((_root_.RHTower.continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m / 2) (by linarith)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η →
      d₁ / 2 ≤ P τ ∧ m / 2 ≤ ‖_root_.RHTower.twistLimit 0 τ‖ := by
    intro τ hτ
    constructor
    · refine hnear₁ τ ?_
      have : |τ - τ₁| ≤ |τ - τ₀| + |τ₀ - τ₁| := by
        calc |τ - τ₁| = |(τ - τ₀) + (τ₀ - τ₁)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have := min_le_left (η₁ / 2) (η₂ / 2)
      linarith
    · have hd : dist τ τ₀ < η₂ := by
        rw [Real.dist_eq]
        have := min_le_right (η₁ / 2) (η₂ / 2)
        linarith
      have := hη₂ hd
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le (_root_.RHTower.twistLimit 0 τ₀) (_root_.RHTower.twistLimit 0 τ)
      rw [norm_sub_rev] at this
      linarith
  obtain ⟨a, ha, F, hFd, hFs, hp, hm', hneg⟩ :=
    _root_.RHTower.vonMangoldt_sub_symbol_violation_of_concentration hPc hPb hη0 hm0 hd₁0 hnear
  refine ⟨a, ha, F, hFd, hFs, hp, hm', ?_⟩
  -- the energy of `S_Λ − P_δ + c` is `2π` times the functional of the pair
  have hFint := _root_.RHTower.integrable_normSq_paperFT hFd hFs
  have hΛi := _root_.RHTower.integrable_normSq_paperFT_mul_weilAtomSymbol hFd hFs
  have hPi := integrable_normSq_paperFT_mul_perturbationSymbol hsum hFd hFs
  have hsub : Integrable fun τ : ℝ => ‖paperFT F τ‖ ^ 2 *
      _root_.RHTower.weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) -
      ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ := hΛi.sub hPi
  have hcm : Integrable fun τ : ℝ => c * ‖paperFT F τ‖ ^ 2 := hFint.const_mul c
  have e : (fun τ : ℝ => ‖paperFT F τ‖ ^ 2 *
        (_root_.RHTower.weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) -
          P τ)) =
      fun τ : ℝ => (‖paperFT F τ‖ ^ 2 *
          _root_.RHTower.weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) -
          ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ) +
        c * ‖paperFT F τ‖ ^ 2 := by
    funext τ
    simp only [hPdef]
    ring
  rw [e, integral_add hsub hcm, integral_sub hΛi hPi, integral_const_mul] at hneg
  have e1 := _root_.RHTower.EvenSector.integral_weilAtomSymbol_eq_two_pi_mul_re
    (lam := fun n => (Λ n : ℝ) + δ n) ha hFd hFs hp hm'
  have e2 := _root_.RHTower.integral_weilAtomSymbol_eq_sub hFd hFs (fun n => (Λ n : ℝ) + δ n)
  have e3 : (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * _root_.RHTower.perturbationSymbol δ τ) =
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        ((Λ n : ℝ) + δ n - Λ n) / Real.sqrt n *
          (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re := by
    rw [_root_.RHTower.integral_normSq_mul_perturbationSymbol hsum hFd hFs,
      tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) fun n hn => ?_, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1]
      ring
    · by_cases h2n : 2 ≤ n
      · have hn' : ⌊Real.exp (2 * a)⌋₊ < n := by
          by_contra hcon
          exact hn (Finset.mem_Icc.mpr ⟨h2n, not_lt.mp hcon⟩)
        have hlog : 2 * a < Real.log n := by
          rw [Real.lt_log_iff_exp_lt (by exact_mod_cast (by omega : 0 < n))]
          exact Nat.lt_of_floor_lt hn'
        obtain ⟨-, -, hks, -, -⟩ := _root_.RHTower.weilTest_self_data hFd hFs
        have hz1 : EF.weilTest F F (Real.log n) = 0 :=
          image_eq_zero_of_notMem_tsupport fun hmem => by
            have := (hks hmem).2
            linarith
        have hz2 : EF.weilTest F F (-Real.log n) = 0 :=
          image_eq_zero_of_notMem_tsupport fun hmem => by
            have := (hks hmem).1
            linarith
        rw [if_pos h2n, hz1, hz2]
        simp
      · rw [if_neg h2n]
  have e4 := _root_.RHTower.integral_norm_paperFT_sq hFd hFs
  rw [e4] at hneg
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hkey : 2 * π * ((_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ) + δ n)
      (EF.weilTest F F)).re + c * ∫ x, ‖F x‖ ^ 2) < 0 := by
    linarith
  by_contra hcon
  exact absurd (mul_nonneg h2π.le (not_lt.mp hcon)) (not_le.mpr hkey)

/-- **Where the symbol exceeds the constant the inequality fails.** If `P_δ(τ₁) > c`, some packet
with both degrees zero has a negative functional. -/
theorem exists_packet_pairForm_neg (hsum : Summable fun n => |δ n| / Real.sqrt n) {c τ₁ : ℝ}
    (hτ₁ : c < _root_.RHTower.perturbationSymbol δ τ₁) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∫ u, g u * Real.exp (-u / 2)) = 0 ∧ (∫ u, g u * Real.exp (u / 2)) = 0 ∧
      pairForm δ c g < 0 := by
  obtain ⟨a, -, F, hFd, hFs, hp, hm, hneg⟩ := exists_test_pair_neg hsum hτ₁
  obtain ⟨hFc, -, -, -, -⟩ := _root_.RHTower.weilTest_self_data hFd hFs
  obtain ⟨hd1, hd2, hd3, hd4⟩ := degrees_eq_zero_of_polar hFd.continuous hFc hp hm
  rw [re_weilFullFunctional_split (fun n => (Λ n : ℝ) + δ n) hFd hFc,
    integral_norm_sq_split hFd.continuous hFc, mul_add] at hneg
  have hu : ContDiff ℝ 2 fun x => (F x).re := Complex.reCLM.contDiff.comp hFd
  have hv : ContDiff ℝ 2 fun x => (F x).im := Complex.imCLM.contDiff.comp hFd
  have huc : HasCompactSupport fun x => (F x).re :=
    hFc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have hvc : HasCompactSupport fun x => (F x).im :=
    hFc.comp_left (g := fun z : ℂ => z.im) (by simp)
  by_cases h : pairForm δ c (fun x => (F x).re) < 0
  · exact ⟨fun x => (F x).re, hu, huc, hd1, hd2, h⟩
  · refine ⟨fun x => (F x).im, hv, hvc, hd3, hd4, ?_⟩
    have h' := not_lt.mp h
    unfold pairForm at h' ⊢
    linarith

/-! ### The exchange law -/

section Floor

open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticPositivityTheory

/-- **The exchange law.** For a deviation with `Σ |δ(n)| n^{-1/2} < ∞`, Bézout on the comb of the
integers with the contacts `Λ + δ` and the counterterm `log(n/2π) + c` holds iff the Riemann
hypothesis holds and the symbol of `δ` is at most `c` everywhere. -/
theorem combBezoutWith_iff (hsum : Summable fun n => |δ n| / Real.sqrt n) (c : ℝ) :
    CombBezoutWith δ c ↔
      RiemannHypothesis ∧ ∀ τ, _root_.RHTower.perturbationSymbol δ τ ≤ c := by
  rw [combBezoutWith_iff_pairForm]
  have h2π : (0 : ℝ) < 2 * π := by positivity
  constructor
  · intro h
    refine ⟨?_, fun τ => ?_⟩
    · -- the zero sum is bounded below by a multiple of the mass
      refine SquareRootThreshold.riemannHypothesis_of_odd_fullZeroForm_bddBelow
        (C := |c| + ∑' n : ℕ, 2 * (|δ n| / Real.sqrt n)) fun F hF hFc _ => ?_
      obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hFc
      have hg : ContDiff ℝ 2 fun u => F (u - s) := hF.comp (contDiff_id.sub contDiff_const)
      have hgc : HasCompactSupport fun u => F (u - s) :=
        hFc.comp_homeomorph (Homeomorph.subRight s)
      obtain ⟨a, hgs⟩ := exists_tsupport_ofReal_subset_Icc hgc
      have hGd := contDiff_ofReal_packet hg
      have hid := two_pi_mul_pairForm_eq hsum c hg hgc hK hsupp hgs
      have hpos := mul_nonneg h2π.le (h _ hg hgc)
      have hlow := neg_mul_le_integral_normSq_mul_perturbationSymbol hsum hGd hgs
      have hX := _root_.RHTower.integral_norm_paperFT_sq hGd hgs
      have hnorm : (∫ x : ℝ, ‖((F (x - s) : ℝ) : ℂ)‖ ^ 2) = ∫ x, F (x - s) ^ 2 :=
        integral_congr_ae (Eventually.of_forall fun x => by
          show ‖((F (x - s) : ℝ) : ℂ)‖ ^ 2 = F (x - s) ^ 2
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
      have hmass : ∫ u, F (u - s) ^ 2 = ∫ u, F u ^ 2 :=
        integral_sub_right_eq_self (fun u => F u ^ 2) s
      have hI0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun u => sq_nonneg _
      rw [hX, hnorm, hmass] at hid hlow
      have hc : c * (2 * π * ∫ u, F u ^ 2) ≤ |c| * (2 * π * ∫ u, F u ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (mul_nonneg h2π.le hI0)
      have hkey : 0 ≤ 2 * π * (zeroSum (fun u => F (u - s)) +
          (|c| + ∑' n : ℕ, 2 * (|δ n| / Real.sqrt n)) * ∫ u, F u ^ 2) := by
        linarith
      have := (mul_nonneg_iff_of_pos_left h2π).mp hkey
      rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc,
        ← zeroSum_eq_weilFullFunctional hF hFc, ← zeroSum_translate hF hFc s]
      linarith
    · by_contra hcon
      obtain ⟨g, hg, hgc, -, -, hneg⟩ := exists_packet_pairForm_neg hsum (not_le.mp hcon)
      exact absurd (h g hg hgc) (not_le.mpr hneg)
  · rintro ⟨hRH, hP⟩ g hg hgc
    obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
    have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
    have hgc' : HasCompactSupport fun u => g (u - s) :=
      hgc.comp_homeomorph (Homeomorph.subRight s)
    obtain ⟨a, hgs⟩ := exists_tsupport_ofReal_subset_Icc hgc'
    have hid := two_pi_mul_pairForm_eq hsum c hg' hgc' hK hsupp hgs
    have hup := integral_normSq_mul_perturbationSymbol_le hsum (contDiff_ofReal_packet hg') hgs hP
    have hZ : 0 ≤ zeroSum fun u => g (u - s) := by
      have h1 := neg_offLineDefect_le_zeroSum hg' hgc'
      rw [riemannHypothesis_iff_offLineDefect_eq_zero.mp hRH _ hg' hgc'] at h1
      linarith
    rw [← pairForm_translate δ c g s]
    refine (mul_nonneg_iff_of_pos_left h2π).mp ?_
    rw [hid]
    linarith [mul_nonneg h2π.le hZ]

end Floor

/-! ### The constant -/

/-- The symbol of a deviation that vanishes on the integers `n ≥ 2` is zero. -/
theorem perturbationSymbol_eq_zero (h : ∀ n, 2 ≤ n → δ n = 0) (τ : ℝ) :
    _root_.RHTower.perturbationSymbol δ τ = 0 := by
  unfold _root_.RHTower.perturbationSymbol
  have h0 : ∀ n : ℕ, _root_.RHTower.weightAtom δ n (τ / (2 * π)) = 0 := fun n => by
    unfold _root_.RHTower.weightAtom
    split_ifs with h2
    · rw [h n h2]
      ring
    · rfl
  simp only [h0, tsum_zero]

/-- **Bézout forces a nonnegative constant.** The density of the comb over `2π` is the largest
counterterm for which the inequality is not refuted, whatever the contacts. -/
theorem nonneg_of_combBezoutWith (hsum : Summable fun n => |δ n| / Real.sqrt n) {c : ℝ}
    (h : CombBezoutWith δ c) : 0 ≤ c := by
  obtain ⟨-, hP⟩ := (combBezoutWith_iff hsum c).mp h
  by_contra hc
  have hc' : c < 0 := not_le.mp hc
  have hδ : ∀ n, 2 ≤ n → δ n = 0 := fun n hn =>
    _root_.RHTower.eq_zero_of_perturbationSymbol_nonpos hsum (fun τ => (hP τ).trans hc'.le) hn
  have := hP 0
  rw [perturbationSymbol_eq_zero hδ] at this
  linarith

/-- **At the constant `2π` the contacts are rigid.** With the counterterm of the comb, Bézout
holds iff the Riemann hypothesis holds and the deviation vanishes. -/
theorem combBezoutWith_zero_right_iff (hsum : Summable fun n => |δ n| / Real.sqrt n) :
    CombBezoutWith δ 0 ↔ RiemannHypothesis ∧ ∀ n, 2 ≤ n → δ n = 0 := by
  rw [combBezoutWith_iff hsum 0]
  refine and_congr_right fun _ => ⟨fun hP n hn => ?_, fun hδ τ => ?_⟩
  · exact _root_.RHTower.eq_zero_of_perturbationSymbol_nonpos hsum hP hn
  · rw [perturbationSymbol_eq_zero hδ]

/-! ### One contact -/

/-- The deviation that changes the contact at `n₀` by `t`. -/
def contactAt (n₀ : ℕ) (t : ℝ) : ℕ → ℝ := fun n => if n = n₀ then t else 0

theorem summable_contactAt (n₀ : ℕ) (t : ℝ) :
    Summable fun n => |contactAt n₀ t n| / Real.sqrt n :=
  summable_of_ne_finset_zero (s := {n₀}) fun n hn => by
    rw [contactAt, if_neg (by simpa using hn), abs_zero, zero_div]

/-- The symbol of one contact: `2t n₀^{-1/2} cos(τ log n₀)`. -/
theorem perturbationSymbol_contactAt {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (t τ : ℝ) :
    _root_.RHTower.perturbationSymbol (contactAt n₀ t) τ =
      2 * t / Real.sqrt n₀ * Real.cos (τ * Real.log n₀) := by
  unfold _root_.RHTower.perturbationSymbol
  rw [tsum_eq_single n₀ fun n hn => ?_]
  · unfold _root_.RHTower.weightAtom contactAt
    rw [if_pos hn₀, if_pos rfl]
    have harg : 2 * π * Real.log n₀ * (τ / (2 * π)) = τ * Real.log n₀ := by
      rw [show 2 * π * Real.log n₀ * (τ / (2 * π)) = 2 * π / (2 * π) * (τ * Real.log n₀) by ring,
        div_self (by positivity), one_mul]
    rw [harg]
    ring
  · unfold _root_.RHTower.weightAtom contactAt
    rw [if_neg hn]
    split_ifs
    · ring
    · rfl

/-- **The price of one contact.** With the contact at `n₀` changed by `t` and the counterterm
`log(n/2π) + c`, Bézout holds iff the Riemann hypothesis holds and `c ≥ 2|t|/√n₀`. -/
theorem combBezoutWith_contactAt_iff {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (t c : ℝ) :
    CombBezoutWith (contactAt n₀ t) c ↔
      RiemannHypothesis ∧ 2 * |t| / Real.sqrt n₀ ≤ c := by
  rw [combBezoutWith_iff (summable_contactAt n₀ t) c]
  have hs : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hlog : 0 < Real.log n₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < n₀))
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h τ => ?_⟩
  · rcases le_or_gt 0 t with ht | ht
    · have h0 := h 0
      rw [perturbationSymbol_contactAt hn₀, zero_mul, Real.cos_zero, mul_one] at h0
      rwa [abs_of_nonneg ht]
    · have hπ := h (π / Real.log n₀)
      have harg : π / Real.log n₀ * Real.log n₀ = π := by field_simp
      rw [perturbationSymbol_contactAt hn₀, harg, Real.cos_pi] at hπ
      rw [abs_of_neg ht]
      have e : 2 * -t / Real.sqrt n₀ = 2 * t / Real.sqrt n₀ * -1 := by ring
      rw [e]
      exact hπ
  · rw [perturbationSymbol_contactAt hn₀]
    have hcos := Real.abs_cos_le_one (τ * Real.log n₀)
    have h2 : |2 * t / Real.sqrt n₀ * Real.cos (τ * Real.log n₀)| ≤ 2 * |t| / Real.sqrt n₀ := by
      rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hs]
      calc 2 * |t| / Real.sqrt n₀ * |Real.cos (τ * Real.log n₀)| ≤ 2 * |t| / Real.sqrt n₀ * 1 :=
            mul_le_mul_of_nonneg_left hcos (by positivity)
        _ = _ := mul_one _
    exact ((le_abs_self _).trans h2).trans h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
