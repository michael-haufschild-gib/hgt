import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePairingOfTheDegreePointsWeighsTheZeros
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrbitRingWithABaseIsATowerOfLines

/-!
# The sign is carried by the contacts

A packet of width below `log 2` meets no contact. Between `log 2` and `log 3` it meets one: the
contact of `Γ_m` and `Γ_{2m}`, of weight `Λ(2)/√2`. On packets of width at most `181/250 > log 2`
the sign of the pairing of the degree points is decided, and it is decided by the sign of this
one contact.

* **The inequality where the first contact enters**
  (`tendsto_degreePairing_le_degrees_of_width`): for every packet of width at most `181/250`, of
  any sign, the limit of jets plus contacts minus the counterterm is at most
  `2 d₁ d₂ − ∫ f²/5000`. The input is the positivity of Weil's functional on these windows.
* **Any weight in place of the contact orders** (`tendsto_degreeForm_add_weightedContact`): with
  weights `w(k)/√k` on the pairs `(m, mk)` the limit is `2 d₁ d₂` minus the functional of the
  weight `w` on the packet. The jets and the counterterm do not depend on the weight.
* **The reversed contact** (`exists_packet_degreePairing_gt_of_flippedContact`): with the weight
  `−log 2` at `k = 2` and the contact orders `Λ(k)` elsewhere there is a packet whose limit
  exceeds `2 d₁ d₂`.

* **The comb selects the contacts** (`combBezout_iff`, `not_combBezout_of_ne`): Bézout on the
  comb of the integers, the inequality for every packet with the jets and the counterterm of the
  comb and the contacts of weight `w`, holds iff the Riemann hypothesis holds and `w = Λ`. A
  weight that differs from `Λ` at one integer fails on some packet, without hypothesis. The
  contact weights of an integer-norm system other than `ℤ` differ from `Λ`: the square does not
  see such a system, the comb does.
* **The weights are contact numbers of the object** (`contactWeight_eq_log_card_orbitBaseRing`):
  `Λ(k)/√k` is the logarithm of the order of the contact of the diagonal and `Γ_k` on the orbit
  ring with a base, over `√k`.

So the inequality of Castelnuovo and Severi on the degree points is not a property of the jets,
of the counterterm or of the shape of the pairing: it holds with the contact of the square at the
prime `2` and fails with its negative. A contact order is the logarithm of the order of a scheme
and is positive; a proof of the sign has to use it. The additive datum that separates `ℤ` from
every other system of contact weights is the comb of the degree points: unit masses on all
integers, with its jets and its counterterm.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {f : ℝ → ℝ}

/-! ### The inequality where the first contact enters -/

/-- The sum over the zeros does not change under a translation of the packet. -/
theorem zeroSum_translate (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (s : ℝ) :
    zeroSum (fun u => f (u - s)) = zeroSum f := by
  have hg : ContDiff ℝ 2 fun u => f (u - s) := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - s) :=
    hfc.comp_homeomorph (Homeomorph.subRight s)
  rw [zeroSum_eq_weilFullFunctional hg hgc, zeroSum_eq_weilFullFunctional hf hfc]
  exact congrArg (fun k => (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ)) k).re)
    (weilTest_packet_translate f s)

/-- For a packet of width at most `181/250` the sum over the zeros is at least `∫ f²/5000`. -/
theorem zeroSum_ge_of_width (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {c : ℝ}
    (hshort : ∀ u, 181 / 500 < |u - c| → f u = 0) :
    1 / 5000 * ∫ u, f u ^ 2 ≤ zeroSum f := by
  have hg : ContDiff ℝ 2 fun u => f (u - -c) := hf.comp (contDiff_id.sub contDiff_const)
  have hg0 : ∀ x : ℝ, 181 / 500 < |x| → f (x - -c) = 0 := fun x hx =>
    hshort _ (by rwa [sub_neg_eq_add, add_sub_cancel_right])
  have hts : tsupport (fun x => ((f (x - -c) : ℝ) : ℂ)) ⊆
      Set.Icc (-(181 / 500)) (181 / 500) := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra hxI
    have hx' : 181 / 500 < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
      rcases hxI with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact h
    exact hx (by
      show ((f (x - -c) : ℝ) : ℂ) = 0
      rw [hg0 x hx', Complex.ofReal_zero])
  have h : 1 / 5000 * ∫ x, ‖((f (x - -c) : ℝ) : ℂ)‖ ^ 2 ≤
      (zetaZeroConfig.W (fun x => ((f (x - -c) : ℝ) : ℂ))
        (fun x => ((f (x - -c) : ℝ) : ℂ))).re :=
    SelectivePositivityAndThresholdLaws.zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths
      (contDiff_ofReal_packet hg) hts
  have hnorm : ∫ x, ‖((f (x - -c) : ℝ) : ℂ)‖ ^ 2 = ∫ u, f u ^ 2 := by
    have h1 : ∫ x, ‖((f (x - -c) : ℝ) : ℂ)‖ ^ 2 = ∫ x, f (x - -c) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun x => by
        show ‖((f (x - -c) : ℝ) : ℂ)‖ ^ 2 = f (x - -c) ^ 2
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])
    rw [h1]
    exact integral_sub_right_eq_self (μ := volume) (fun u => f u ^ 2) (-c)
  rw [hnorm] at h
  rw [← zeroSum_translate hf hfc (-c)]
  exact h

/-- **The inequality of Castelnuovo and Severi where the first contact enters.** For every packet
of width at most `181/250`, of any sign, the pairing of the degree points has a limit, at most
twice the product of the degrees minus `∫ f²/5000`. -/
theorem tendsto_degreePairing_le_degrees_of_width (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) {c : ℝ}
    (hshort : ∀ u, 181 / 500 < |u - c| → f u = 0) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * degreeContact f (3 * K) N)
        atTop (𝓝 l) ∧
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        1 / 5000 * ∫ u, f u ^ 2 :=
  ⟨_, tendsto_degreePairing_degrees_sub_zeroSum hf hfc hK hsupp, by
    linarith [zeroSum_ge_of_width hf hfc hshort]⟩

/-! ### Any weight in place of the contact orders -/

/-- The contacts with a weight `w` in place of the contact orders `Λ`. -/
def weightedContact (w : ℕ → ℝ) (f : ℝ → ℝ) (L N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 L, w k / Real.sqrt k *
    ∑ m ∈ Ioc N (N + L * N), degreeSample f N m * degreeSample f N (m * k) / m

theorem weightedContact_vonMangoldt (f : ℝ → ℝ) (L N : ℕ) :
    weightedContact (fun n => (Λ n : ℝ)) f L N = degreeContact f L N :=
  rfl

theorem tendsto_weightedContact (w : ℕ → ℝ) (hcont : Continuous f) {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (weightedContact w f L) atTop
      (𝓝 (∑ k ∈ Icc 2 L, w k / Real.sqrt k *
        ∫ u in (0 : ℝ)..Real.log (1 + L), f u * f (u + Real.log k))) :=
  tendsto_finsetSum _ fun k hk =>
    (tendsto_contactRow hcont hL (by
      have := (Finset.mem_Icc.mp hk).1
      omega)).const_mul _

/-- **The pairing with any weight on the contacts.** Jets, weighted contacts and the counterterm
tend to twice the product of the degrees minus the functional of the weight on the packet. -/
theorem tendsto_degreeForm_add_weightedContact (w : ℕ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * weightedContact w f (3 * K) N) atTop
      (𝓝 (2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re)) := by
  have hδ : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hL3 : 1 ≤ 3 * K := by omega
  have hsuppW := window_of_support hK hsupp
  have h1L : (0 : ℝ) < 1 + ((3 * K : ℕ) : ℝ) := by positivity
  have hQ : ∀ n : ℕ, 3 * K < n → packetAutocorr f (Real.log n) = 0 := fun n hn =>
    packetAutocorr_eq_zero_of_window hδ hsuppW (Real.log_le_log h1L (by
      have : ((3 * K : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
      linarith))
  have h1 : Tendsto (degreeForm f (3 * K)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
          (_root_.RHTower.weilPoleTerm
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re))) :=
    tendsto_degreeForm hf hfc hK hsupp
  have h2 := (tendsto_weightedContact w hf.continuous hL3).const_mul 2
  have hsum : ∑ k ∈ Icc 2 (3 * K), w k / Real.sqrt k *
        ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u * f (u + Real.log k) =
      ∑ k ∈ Icc 2 (3 * K), w k / Real.sqrt k * packetAutocorr f (Real.log k) :=
    Finset.sum_congr rfl fun k _ => by
      rw [packetAutocorr_eq_integral_window hδ hsuppW]
  have hfull := re_weilFullFunctional_packet_of_weight w f hQ
  have hlim := h1.add h2
  rw [hsum, weilPoleTerm_packet hf.continuous hfc] at hlim
  have e : 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) -
        (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      -(_root_.RHTower.WeilOneSided.weilArchRe
            (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
          2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) +
        2 * ∑ k ∈ Icc 2 (3 * K), w k / Real.sqrt k * packetAutocorr f (Real.log k) := by
    rw [hfull]
    ring
  rw [e]
  exact hlim

/-! ### The reversed contact -/

/-- **With the contact at the prime `2` reversed the inequality fails.** There is a packet for
which jets, the counterterm and the contacts with the weight `−log 2` at `k = 2` and `Λ(k)` at
`k ≠ 2` have a limit above twice the product of the degrees. -/
theorem exists_packet_degreePairing_gt_of_flippedContact :
    ∃ (f : ℝ → ℝ) (K : ℕ), ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ 1 ≤ K ∧
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) ∧
      ∃ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N +
          2 * weightedContact SelectivePositivityAndThresholdLaws.flippedTwoVonMangoldt f
            (3 * K) N) atTop (𝓝 l) ∧
        2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)) < l := by
  obtain ⟨F, hF, hFc, -, -, hpos, hneg⟩ :=
    SelectivePositivityAndThresholdLaws.exists_odd_smooth_threeHundredSixtyTwoThousandths_flippedTwo_neg
  obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hFc
  have hg : ContDiff ℝ 2 fun u => F (u - s) := hF.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => F (u - s) :=
    hFc.comp_homeomorph (Homeomorph.subRight s)
  refine ⟨fun u => F (u - s), K, hg, hgc, hK, hsupp, _,
    tendsto_degreeForm_add_weightedContact _ hg hgc hK hsupp, ?_⟩
  have hW : (_root_.RHTower.weilFullFunctional
        SelectivePositivityAndThresholdLaws.flippedTwoVonMangoldt
        (EF.weilTest (fun u => ((F (u - s) : ℝ) : ℂ)) (fun u => ((F (u - s) : ℝ) : ℂ)))).re =
      (_root_.RHTower.weilFullFunctional
        SelectivePositivityAndThresholdLaws.flippedTwoVonMangoldt
        (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re :=
    congrArg (fun k => (_root_.RHTower.weilFullFunctional
      SelectivePositivityAndThresholdLaws.flippedTwoVonMangoldt k).re)
      (weilTest_packet_translate F s)
  show 2 * ((∫ u, F (u - s) * Real.exp (-u / 2)) * ∫ u, F (u - s) * Real.exp (u / 2)) <
    2 * ((∫ u, F (u - s) * Real.exp (-u / 2)) * ∫ u, F (u - s) * Real.exp (u / 2)) -
      (_root_.RHTower.weilFullFunctional
        SelectivePositivityAndThresholdLaws.flippedTwoVonMangoldt
        (EF.weilTest (fun u => ((F (u - s) : ℝ) : ℂ)) (fun u => ((F (u - s) : ℝ) : ℂ)))).re
  rw [hW]
  linarith

/-! ### The comb selects the contacts -/

/-- Bézout on the comb of the integers for contacts of weight `w`: for every packet in a window
the limit of jets, weighted contacts and counterterm is at most twice the product of the
degrees. -/
def CombBezout (w : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
    ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * weightedContact w f (3 * K) N)
        atTop (𝓝 l) →
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- Bézout on the comb for the weight `w` is the positivity of the functional of `w` on all
tests. -/
theorem combBezout_iff_weilPositiveFull (w : ℕ → ℝ) :
    CombBezout w ↔ _root_.RHTower.WeilPositiveFull w := by
  constructor
  · intro h
    refine _root_.RHTower.WeilSpectral.weilPositiveFull_of_real fun g hg hgc => ?_
    obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
    have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
    have hgc' : HasCompactSupport fun u => g (u - s) :=
      hgc.comp_homeomorph (Homeomorph.subRight s)
    have hle : 2 * ((∫ u, g (u - s) * Real.exp (-u / 2)) * ∫ u, g (u - s) * Real.exp (u / 2)) -
          (_root_.RHTower.weilFullFunctional w
            (EF.weilTest (fun u => ((g (u - s) : ℝ) : ℂ)) (fun u => ((g (u - s) : ℝ) : ℂ)))).re ≤
        2 * ((∫ u, g (u - s) * Real.exp (-u / 2)) * ∫ u, g (u - s) * Real.exp (u / 2)) :=
      h _ hg' hgc' K hK hsupp _ (tendsto_degreeForm_add_weightedContact w hg' hgc' hK hsupp)
    have hW : (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (fun u => ((g (u - s) : ℝ) : ℂ)) (fun u => ((g (u - s) : ℝ) : ℂ)))).re =
        (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re :=
      congrArg (fun k => (_root_.RHTower.weilFullFunctional w k).re)
        (weilTest_packet_translate g s)
    rw [hW] at hle
    linarith
  · intro h f hf hfc K hK hsupp l hl
    have hlim := tendsto_degreeForm_add_weightedContact w hf hfc hK hsupp
    have hpos := h (fun u => (f u : ℂ)) (contDiff_ofReal_packet hf)
      (hasCompactSupport_ofReal_packet hfc)
    rw [tendsto_nhds_unique hl hlim]
    linarith

/-- **The comb selects the contacts.** Bézout on the comb of the integers holds for the weight
`w` iff the Riemann hypothesis holds and `w` is the von Mangoldt function. -/
theorem combBezout_iff (w : ℕ → ℝ) :
    CombBezout w ↔ RiemannHypothesis ∧ ∀ n, 2 ≤ n → w n = Λ n := by
  rw [combBezout_iff_weilPositiveFull]
  exact _root_.RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt

/-- **Every other weight fails.** A weight that differs from the von Mangoldt function at one
integer `n ≥ 2` does not satisfy Bézout on the comb of the integers. -/
theorem not_combBezout_of_ne {w : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n) (h : w n ≠ Λ n) :
    ¬ CombBezout w :=
  fun hB => h (((combBezout_iff w).mp hB).2 n hn)

/-- The Riemann hypothesis is Bézout on the comb of the integers for the contacts of the
square. -/
theorem riemannHypothesis_iff_combBezout :
    RiemannHypothesis ↔ CombBezout fun n => (Λ n : ℝ) := by
  rw [combBezout_iff]
  exact ⟨fun h => ⟨h, fun _ _ => rfl⟩, fun h => h.1⟩

/-! ### The weights are contact numbers of the object -/

/-- **The contact weights are the contact numbers of the orbit ring with a base.** For `k ≥ 2`,
`Λ(k)/√k` is the logarithm of the order of the contact of the diagonal and `Γ_k` on `𝒪_q`,
divided by `√k`. -/
theorem contactWeight_eq_log_card_orbitBaseRing (q : ℤ) {k : ℕ} (hk : 1 < k) :
    contactWeight k =
      Real.log (Nat.card (ℤ ⧸ Ideal.span {z : ℤ | ∃ x ∈ orbitBaseRing q,
        z = ghostComponent 1 x - ghostComponent ⟨k, by omega⟩ x})) / Real.sqrt k := by
  have h1 : (1 : ℕ+) < ⟨k, by omega⟩ := hk
  rw [span_orbitBaseRing_sub_eq_graphIdeal, log_card_quotient_graphIdeal_one h1, contactWeight]
  rfl

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
