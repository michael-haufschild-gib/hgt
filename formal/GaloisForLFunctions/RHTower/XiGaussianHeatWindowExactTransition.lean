import GaloisForLFunctions.RHTower.XiGaussianHeatWindowEvenSource
import GaloisForLFunctions.RHTower.EvenWeilRHCriterion

/-!
# Unconditional single-transition law for critical HCF windows

The full polar ground can change parity, whereas heat polynomials have even
physical sources. Strict decrease within the even sector and its exact smooth
core remove that mismatch from the critical-window law.

Either every positive window is nonnegative (the RH branch), or there is exactly
one finite positive half-width A: every window below A²/4 is eventually
nonnegative, and every window above A²/4 has a negative direction at every large
degree. No sign is asserted at the single transition constant.
-/

open Complex MeasureTheory Set Filter Topology Polynomial
noncomputable section
namespace RHTower
open CCMEvenSector

/-- A negative direction exists in every sufficiently large critical heat section. -/
def HeatWindowEventuallyNegative (K : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
    (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re < 0

/-- One aperture separates the eventual positive and negative heat-window phases. -/
def HeatWindowTransition (A : ℝ) : Prop :=
  0 < A ∧
    (∀ K : ℝ, 0 < K → 4 * K < A ^ 2 → HeatWindowNonneg K) ∧
    (∀ K : ℝ, 0 < K → A ^ 2 < 4 * K → HeatWindowEventuallyNegative K)

theorem heatWindow_nonneg_not_eventuallyNegative (K : ℝ) (hp : HeatWindowNonneg K) :
    ¬ HeatWindowEventuallyNegative K := by
  intro hn
  obtain ⟨n, hnp, P, hPd, hPe, hneg⟩ := (hp.and hn).exists
  exact (not_lt_of_ge (hnp P hPd hPe)) hneg

private theorem exists_evenGround_negative_of_not_RH (hn : ¬ RiemannHypothesis) :
    ∃ a : SuzukiPositiveAperture, evenGroundEnergy a < 0 := by
  by_contra hnone
  push Not at hnone
  apply hn
  apply riemannHypothesis_iff_forall_evenPoleWeilNonneg.mpr
  intro A hA
  let b : SuzukiPositiveAperture := ⟨A + 1, by positivity⟩
  have hf := evenWeilFloor_of_evenGroundEnergy b (show A < b.1 by dsimp [b]; linarith)
  intro u hu hc hs he hp
  have h := hf u hu hc hs he hp
  exact (mul_nonneg (hnone b) (integral_nonneg fun x => sq_nonneg (u x))).trans h

private theorem exists_evenGround_sign_transition (hn : ¬ RiemannHypothesis) :
    ∃ A : ℝ, 0 < A ∧
      (∀ b : SuzukiPositiveAperture, b.1 < A → 0 < evenGroundEnergy b) ∧
      (∀ b : SuzukiPositiveAperture, A < b.1 → evenGroundEnergy b < 0) := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_aperture_polarGroundEnergy_pos
  let c : SuzukiPositiveAperture := ⟨δ / 2, half_pos hδ⟩
  have hc : 0 < evenGroundEnergy c :=
    (hsmall c (by change δ / 2 < δ; linarith)).trans_le
      (polarGroundEnergy_le_evenGroundEnergy c)
  obtain ⟨d, hd⟩ := exists_evenGround_negative_of_not_RH hn
  let S : Set ℝ := {r | ∃ hr : 0 < r, 0 < evenGroundEnergy ⟨r, hr⟩}
  have hcm : c.1 ∈ S := ⟨c.2, hc⟩
  have hne : S.Nonempty := ⟨c.1, hcm⟩
  have hbdd : BddAbove S := by
    refine ⟨d.1, ?_⟩
    rintro r ⟨hr, hpos⟩
    by_contra hle
    have horder : d ≤ (⟨r, hr⟩ : SuzukiPositiveAperture) := (lt_of_not_ge hle).le
    have henergy := evenGroundEnergy_antitone horder
    linarith
  let A := sSup S
  have hA : 0 < A := c.2.trans_le (le_csSup hbdd hcm)
  refine ⟨A, hA, ?_, ?_⟩
  · intro b hb
    by_contra hn
    have hupper : ∀ r ∈ S, r ≤ b.1 := by
      rintro r ⟨hr, hpos⟩
      by_contra hle
      have horder : b ≤ (⟨r, hr⟩ : SuzukiPositiveAperture) := (lt_of_not_ge hle).le
      have henergy := evenGroundEnergy_antitone horder
      linarith [not_lt.mp hn]
    have hbound : A ≤ b.1 := csSup_le hne hupper
    linarith
  · intro b hb
    by_contra hn
    let e : SuzukiPositiveAperture := ⟨(A + b.1) / 2, by linarith [b.2]⟩
    have heA : A < e.1 := by dsimp [e]; linarith
    have heb : e < b := by change (A + b.1) / 2 < b.1; linarith
    have hepos : 0 < evenGroundEnergy e := (not_lt.mp hn).trans_lt (strictAnti_evenGroundEnergy heb)
    have hem : e.1 ∈ S := ⟨e.2, hepos⟩
    have hbound : e.1 ≤ A := le_csSup hbdd hem
    linarith

private theorem heatWindowTransition_of_ground_transition {A : ℝ} (hA : 0 < A)
    (hpos : ∀ b : SuzukiPositiveAperture, b.1 < A → 0 < evenGroundEnergy b)
    (hneg : ∀ b : SuzukiPositiveAperture, A < b.1 → evenGroundEnergy b < 0) :
    HeatWindowTransition A := by
  refine ⟨hA, ?_, ?_⟩
  · intro K hK hKA
    have hs := Real.sqrt_nonneg (4 * K)
    have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * K)
    have hsA : Real.sqrt (4 * K) < A := by nlinarith
    let b : SuzukiPositiveAperture := ⟨(Real.sqrt (4 * K) + A) / 2, by positivity⟩
    have hbA : b.1 < A := by dsimp [b]; linarith
    have hsb : Real.sqrt (4 * K) < b.1 := by dsimp [b]; linarith
    exact heatWindowNonneg_of_evenGroundEnergy_pos (hpos b hbA) hK (by nlinarith)
  · intro K hK hAK
    have hs := Real.sqrt_nonneg (4 * K)
    have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * K)
    have hAs : A < Real.sqrt (4 * K) := by nlinarith
    let b : SuzukiPositiveAperture := ⟨(A + Real.sqrt (4 * K)) / 2, by positivity⟩
    have hAb : A < b.1 := by dsimp [b]; linarith
    have hbs : b.1 < Real.sqrt (4 * K) := by dsimp [b]; linarith
    exact eventually_heatWindow_negative_of_evenGroundEnergy_neg (hneg b hAb) hK (by nlinarith [b.2])

theorem heatWindowTransition_unique {A B : ℝ}
    (hA : HeatWindowTransition A) (hB : HeatWindowTransition B) : A = B := by
  have hle {C D : ℝ} (hC : HeatWindowTransition C) (hD : HeatWindowTransition D) : C ≤ D := by
    by_contra hn
    have hDC : D < C := lt_of_not_ge hn
    let K := (C ^ 2 + D ^ 2) / 8
    have hK : 0 < K := by dsimp [K]; nlinarith [hC.1, hD.1]
    have hDK : D ^ 2 < 4 * K := by dsimp [K]; nlinarith [hC.1, hD.1]
    have hKC : 4 * K < C ^ 2 := by dsimp [K]; nlinarith [hC.1, hD.1]
    exact heatWindow_nonneg_not_eventuallyNegative K (hC.2.1 K hK hKC) (hD.2.2 K hK hDK)
  exact le_antisymm (hle hA hB) (hle hB hA)

/-- **Unconditional HCF phase transition.** No parity, spectral gap or source-sign premise is used.
Outside at most one critical window constant the finite-section sign stabilizes. -/
theorem hcf_exact_window_transition :
    (RiemannHypothesis ∧ ∀ K : ℝ, 0 < K → HeatWindowNonneg K) ∨
      ∃! A : ℝ, HeatWindowTransition A := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH, riemannHypothesis_iff_forall_heatWindowNonneg.mp hRH⟩
  · obtain ⟨A, hA, hp, hn⟩ := exists_evenGround_sign_transition hRH
    have ht := heatWindowTransition_of_ground_transition hA hp hn
    exact Or.inr ⟨A, ht, fun B hB => heatWindowTransition_unique hB ht⟩

end RHTower
