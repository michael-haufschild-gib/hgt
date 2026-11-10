import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.BezoutDeterminesTheConstantOfTheCounterterm
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheMarginLawOfTheWindowCone

/-!
# The squares with Bézout at an aperture are the window cone

A system of contact weights `w` on the comb of the integers, with the jets and the counterterm
of the comb, is a square for the purposes of the pairing. **Bézout at the aperture `a`** asks
the inequality `D·D ≤ 2 d₁ d₂` for the packets supported within `a` of a centre
(`CombBezoutAt`). The set of these squares is the window cone `𝒜(a)` of the corpus, the weights
whose functional is nonnegative on the tests supported in `[−a, a]`
(`combBezoutAt_iff_mem_windowCone`): a packet and its translate have the same functional, and
the functional of a complex test is the sum of those of its real and imaginary parts.

With this the theory of the window cone is a theory of squares:

* **Existence decides** (`riemannHypothesis_iff_forall_exists_combBezoutAt`,
  `exists_aperture_forall_not_combBezoutAt`). The Riemann hypothesis holds iff at every aperture
  some square satisfies Bézout; if it fails, beyond some aperture no square does.
* **Squares other than that of the integers** (`hasMargin_vonMangoldt`,
  `exists_combBezoutAt_weight_two`, `exists_combBezoutAt_ne_vonMangoldt`). At the aperture
  `181/500` the square of the integers has the margin `1/5000`, and a margin is an inradius of
  the cone: for every `t` within `√2/10000` of `log 2` a system of contact weights with
  `w(2) = t` satisfies Bézout at that aperture.
* **Below the first contact** (`combBezoutAt_of_short`). For `2a < log 2` every system of
  weights satisfies Bézout at the aperture `a`.

So at a finite aperture Bézout does not single out the contacts of the square; it does so in
the limit of the apertures, where the cone is the point `Λ` or empty.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open CriticalHardyTheoryOfTheWindowCone

/-- **Bézout at an aperture** for contacts of weight `w`: the inequality for the packets in a
window that are supported within `a` of a centre. -/
def CombBezoutAt (w : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ K : ℕ, 1 ≤ K →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
    ∀ c : ℝ, (∀ u, a < |u - c| → f u = 0) →
    ∀ l : ℝ, Tendsto (fun N : ℕ => degreeForm f (3 * K) N + 2 * weightedContact w f (3 * K) N)
        atTop (𝓝 l) →
      l ≤ 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- A real function that vanishes outside `[−a, a]` has its complexification supported there. -/
theorem tsupport_ofReal_subset_of_vanish {g : ℝ → ℝ} {a : ℝ} (hg0 : ∀ x, a < |x| → g x = 0) :
    tsupport (fun x => ((g x : ℝ) : ℂ)) ⊆ Set.Icc (-a) a := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hxI
  have hx' : a < |x| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h | h
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl h)
  exact hx (by
    show ((g x : ℝ) : ℂ) = 0
    rw [hg0 x hx', Complex.ofReal_zero])

/-- Bézout at the aperture `a` gives a nonnegative functional on the real tests vanishing
outside `[−a, a]`: a translate of the test is a packet of that aperture in a window. -/
theorem re_weilFullFunctional_nonneg_of_combBezoutAt {w : ℕ → ℝ} {a : ℝ} (h : CombBezoutAt w a)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ x, a < |x| → g x = 0) :
    0 ≤ (_root_.RHTower.weilFullFunctional w
      (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re := by
  obtain ⟨s, K, hK, hsupp⟩ := exists_translate_window hgc
  have hg' : ContDiff ℝ 2 fun u => g (u - s) := hg.comp (contDiff_id.sub contDiff_const)
  have hgc' : HasCompactSupport fun u => g (u - s) :=
    hgc.comp_homeomorph (Homeomorph.subRight s)
  have hle : 2 * ((∫ u, g (u - s) * Real.exp (-u / 2)) * ∫ u, g (u - s) * Real.exp (u / 2)) -
        (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (fun u => ((g (u - s) : ℝ) : ℂ)) (fun u => ((g (u - s) : ℝ) : ℂ)))).re ≤
      2 * ((∫ u, g (u - s) * Real.exp (-u / 2)) * ∫ u, g (u - s) * Real.exp (u / 2)) :=
    h _ hg' hgc' K hK hsupp s (fun u hu => hg0 _ hu) _
      (tendsto_degreeForm_add_weightedContact w hg' hgc' hK hsupp)
  have hW : (_root_.RHTower.weilFullFunctional w
        (EF.weilTest (fun u => ((g (u - s) : ℝ) : ℂ)) (fun u => ((g (u - s) : ℝ) : ℂ)))).re =
      (_root_.RHTower.weilFullFunctional w
        (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re :=
    congrArg (fun k => (_root_.RHTower.weilFullFunctional w k).re)
      (weilTest_packet_translate g s)
  rw [hW] at hle
  linarith

/-- **The squares with Bézout at the aperture `a` are the window cone `𝒜(a)`.** -/
theorem combBezoutAt_iff_mem_windowCone (w : ℕ → ℝ) (a : ℝ) :
    CombBezoutAt w a ↔ w ∈ windowCone a := by
  constructor
  · intro h F hF hFs
    have hFc : HasCompactSupport F := hasCompactSupport_of_tsupport_subset hFs
    have hF0 : ∀ x, a < |x| → F x = 0 := fun x hx => by
      by_contra hne
      have hmem := hFs (subset_tsupport _ hne)
      rw [Set.mem_Icc] at hmem
      have : |x| ≤ a := abs_le.mpr hmem
      linarith
    have hre : ContDiff ℝ 2 fun u => (F u).re := Complex.reCLM.contDiff.comp hF
    have him : ContDiff ℝ 2 fun u => (F u).im := Complex.imCLM.contDiff.comp hF
    have hrec : HasCompactSupport fun u => (F u).re := hFc.comp_left Complex.zero_re
    have himc : HasCompactSupport fun u => (F u).im := hFc.comp_left Complex.zero_im
    have h1 := re_weilFullFunctional_nonneg_of_combBezoutAt h hre hrec fun x hx => by
      show (F x).re = 0
      rw [hF0 x hx, Complex.zero_re]
    have h2 := re_weilFullFunctional_nonneg_of_combBezoutAt h him himc fun x hx => by
      show (F x).im = 0
      rw [hF0 x hx, Complex.zero_im]
    rw [re_weilFullFunctional_split w hF hFc]
    exact add_nonneg h1 h2
  · intro h f hf hfc K hK hsupp c hshort l hl
    have hlim := tendsto_degreeForm_add_weightedContact w hf hfc hK hsupp
    -- the packet translated to the origin is a test supported in `[−a, a]`
    have hg : ContDiff ℝ 2 fun u => f (u - -c) := hf.comp (contDiff_id.sub contDiff_const)
    have hts : tsupport (fun x => ((f (x - -c) : ℝ) : ℂ)) ⊆ Set.Icc (-a) a :=
      tsupport_ofReal_subset_of_vanish fun x hx =>
        hshort _ (by rwa [sub_neg_eq_add, add_sub_cancel_right])
    have hpos : 0 ≤ (_root_.RHTower.weilFullFunctional w
        (EF.weilTest (fun u => ((f (u - -c) : ℝ) : ℂ)) (fun u => ((f (u - -c) : ℝ) : ℂ)))).re :=
      h _ (contDiff_ofReal_packet hg) hts
    rw [weilTest_packet_translate f (-c)] at hpos
    rw [tendsto_nhds_unique hl hlim]
    linarith

/-- **Existence at every aperture decides.** The Riemann hypothesis holds iff at every aperture
some system of contact weights satisfies Bézout on the comb of the integers. -/
theorem riemannHypothesis_iff_forall_exists_combBezoutAt :
    RiemannHypothesis ↔ ∀ a : ℝ, ∃ w : ℕ → ℝ, CombBezoutAt w a := by
  rw [_root_.RHTower.riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo]
  exact forall_congr' fun a => exists_congr fun w => (combBezoutAt_iff_mem_windowCone w a).symm

/-- **If the Riemann hypothesis fails, beyond some aperture no square satisfies Bézout.** -/
theorem exists_aperture_forall_not_combBezoutAt (h : ¬ RiemannHypothesis) :
    ∃ a₀ : ℝ, ∀ a, a₀ ≤ a → ∀ w : ℕ → ℝ, ¬ CombBezoutAt w a := by
  obtain ⟨a₀, ha₀⟩ := exists_windowCone_eq_empty_iff.mp h
  refine ⟨a₀, fun a ha w hw => ?_⟩
  have hmem := (combBezoutAt_iff_mem_windowCone w a).mp hw
  rw [ha₀ a ha] at hmem
  exact hmem

/-- The square of the integers has the margin `1/5000` at the aperture `181/500`. -/
theorem hasMargin_vonMangoldt :
    HasMargin (fun n => (Λ n : ℝ)) (181 / 500) (1 / 5000) := by
  intro g hg hgs
  rw [← _root_.RHTower.zeta_W_eq_weilFullFunctional hg (hasCompactSupport_of_tsupport_subset hgs)]
  exact SelectivePositivityAndThresholdLaws.zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths
    hg hgs

/-- **Squares other than that of the integers satisfy Bézout at a finite aperture.** For every
`t` within `√2/10000` of `log 2` some system of contact weights with `w(2) = t` satisfies Bézout
at the aperture `181/500`. -/
theorem exists_combBezoutAt_weight_two {t : ℝ}
    (ht : |t - Real.log 2| ≤ Real.sqrt 2 / 10000) :
    ∃ w : ℕ → ℝ, CombBezoutAt w (181 / 500) ∧ w 2 = t := by
  have hmem : t ∈ bandSet (181 / 500) 2 := by
    refine Icc_subset_bandSet hasMargin_vonMangoldt le_rfl ?_
    have hΛ : (Λ 2 : ℝ) = Real.log 2 := by
      exact_mod_cast ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have h1 := abs_le.mp ht
    simp only [hΛ, Nat.cast_ofNat]
    constructor <;> linarith [h1.1, h1.2]
  obtain ⟨w, hw, hw2⟩ := hmem
  exact ⟨w, (combBezoutAt_iff_mem_windowCone w _).mpr hw, hw2⟩

/-- At the aperture `181/500` a square with a contact at `2` other than `log 2` satisfies
Bézout. -/
theorem exists_combBezoutAt_ne_vonMangoldt :
    ∃ w : ℕ → ℝ, CombBezoutAt w (181 / 500) ∧ w 2 ≠ Λ 2 := by
  have hpos : 0 < Real.sqrt 2 / 10000 := by positivity
  obtain ⟨w, hw, hw2⟩ := exists_combBezoutAt_weight_two
    (t := Real.log 2 + Real.sqrt 2 / 10000) (by
      rw [add_sub_cancel_left, abs_of_pos hpos])
  refine ⟨w, hw, fun h => ?_⟩
  have hΛ : (Λ 2 : ℝ) = Real.log 2 := by
    exact_mod_cast ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  rw [hw2, hΛ] at h
  linarith

/-- **Below the first contact every square satisfies Bézout.** For `2a < log 2` the packets of
aperture `a` meet no contact, and the inequality is that of the square of the integers. -/
theorem combBezoutAt_of_short {a : ℝ} (ha : 2 * a < Real.log 2) (w : ℕ → ℝ) :
    CombBezoutAt w a := by
  rw [combBezoutAt_iff_mem_windowCone]
  have h2 : Real.log 2 < 181 / 250 := by
    have := Real.log_two_lt_d9
    linarith
  have hΛ : (fun n => (Λ n : ℝ)) ∈ windowCone a :=
    windowCone_anti (by linarith) (hasMargin_vonMangoldt.weilPositiveFullUpTo (by norm_num))
  have hzero : (fun _ : ℕ => (0 : ℝ)) ∈ windowCone a :=
    (DimensionZeroGeometryOfSpecZ.weilPositiveFullUpTo_iff_zero ha _).mp hΛ
  exact (DimensionZeroGeometryOfSpecZ.weilPositiveFullUpTo_iff_zero ha w).mpr hzero

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
