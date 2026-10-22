import GaloisForLFunctions.ScaleSignedIncidenceCriticality.RefutationIsFiniteConfirmationIsNot

/-!
# The refutation calculus is complete on both faces

`Resolves` asks a reading to decide a property, and the programme's gates say that no bounded
reading decides the critical line. Deciding is two tasks, and only one of them is hard. This module
isolates the easy one and shows the bounded readings do it **completely**.

A reading `r` **refutes** `P` at `d` when every datum it cannot distinguish from `d` fails `P`
(`Refutes`). Refutation is inherited by finer readings (`Refutes.of_refines`) and implies the
property fails (`not_of_refutes`), so it is the honest formalisation of "finite data established the
negative answer".

* Zero side: a divisor truncated above an off-line zero refutes the critical line
  (`refutes_heightReading`), and conversely RH holds exactly when no bounded-height reading refutes
  it (`riemannHypothesis_iff_no_heightReading_refutes`).
* Prime side: a certificate of radius beyond a failure aperture refutes membership in the full Weil
  cone (`refutes_radiusReading`), and RH holds exactly when no bounded-radius reading refutes it
  (`riemannHypothesis_iff_no_radiusReading_refutes`).

`theRefutationCalculus` states the two completeness theorems together. The asymmetry they expose is
structural, not technical: the negative side of RH is a *finite* statement in both units, and the
programme's floors are entirely about the positive side. A mechanism that only needs to detect a
violation may work at a bounded aperture, a bounded radius and a bounded height; a mechanism that
must confirm may not.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

variable {D O O' : Type*}

/-! ### 1. Refutation -/

/-- A reading **refutes** `P` at `d` when nothing it admits satisfies `P`. -/
def Refutes (r : D → O) (P : D → Prop) (d : D) : Prop := ∀ e ∈ shadow r d, ¬ P e

theorem not_of_refutes {r : D → O} {P : D → Prop} {d : D} (h : Refutes r P d) : ¬ P d :=
  h d (mem_shadow_self r d)

/-- A finer reading refutes whatever a coarser one refutes. -/
theorem Refutes.of_refines {r : D → O} {r' : D → O'} {P : D → Prop} {d : D}
    (href : Refines r r') (h : Refutes r' P d) : Refutes r P d := fun e he => h e (href d e he)

/-! ### 2. The zero side refutes completely -/

/-- **A truncated divisor above an off-line zero refutes the critical line.** -/
theorem refutes_heightReading {T : ℝ} {Z : TemperedZeroConfig} {ρ : ℂ} (hρ : ρ ∈ Z.1.carrier)
    (hT : |ρ.im| ≤ T) (hoff : ρ.re ≠ 1 / 2) :
    Refutes (heightReading T) (fun W => width W = 0) Z := by
  intro W hW hw
  have hmem := mem_carrier_of_mem_shadow_heightReading hW hρ hT
  have hle := abs_re_sub_half_le_configWidth hmem
  have hpos : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero_of_ne hoff)
  have : (0 : ℝ) < width W := lt_of_lt_of_le hpos hle
  rw [hw] at this
  exact absurd this (lt_irrefl 0)

/-- **Completeness on the zero side.** RH holds exactly when no bounded-height reading refutes the
critical line at `ζ`'s configuration. -/
theorem riemannHypothesis_iff_no_heightReading_refutes :
    RiemannHypothesis ↔
      ¬ ∃ T : ℝ, Refutes (heightReading T) (fun W => width W = 0) zetaConfig := by
  refine ⟨fun hRH ⟨T, href⟩ => not_of_refutes href
      (riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero.mp hRH), fun h => ?_⟩
  by_contra hRH
  have hw : width zetaConfig ≠ 0 := fun hw =>
    hRH (riemannHypothesis_iff_configWidth_zetaZeroConfig_eq_zero.mpr hw)
  obtain ⟨ρ, hρ, hoff⟩ : ∃ ρ ∈ zetaConfig.1.carrier, ρ.re ≠ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    exact hw (configWidth_eq_zero_iff_onLine.mpr fun ρ hρ => hcon ρ hρ)
  exact h ⟨|ρ.im|, refutes_heightReading hρ le_rfl hoff⟩

/-! ### 3. The prime side refutes completely -/

/-- **A certificate of radius beyond a failure aperture refutes the cone.** -/
theorem refutes_radiusReading {R : ℝ} {lam : ℕ → ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-R) R)
    (hneg : (weilFullFunctional lam (EF.weilTest f f)).re < 0) :
    Refutes (radiusReading R) WeilPositiveFull lam := by
  intro lam' hlam' hpos
  have hval : weilFullFunctional lam' (EF.weilTest f f) =
      weilFullFunctional lam (EF.weilTest f f) :=
    congrFun (mem_shadow_iff.mp hlam') ⟨f, hf, hfs⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have := hpos f hf hfc
  rw [hval] at this
  linarith

/-- **Completeness on the prime side.** RH holds exactly when no bounded-radius certificate refutes
membership of the von Mangoldt weight in the full Weil cone. -/
theorem riemannHypothesis_iff_no_radiusReading_refutes :
    RiemannHypothesis ↔
      ¬ ∃ R : ℝ, Refutes (radiusReading R)
        WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  refine ⟨fun hRH ⟨R, href⟩ => not_of_refutes href
      (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr
        ⟨hRH, fun _ _ => rfl⟩), fun h => ?_⟩
  by_contra hRH
  have hnot : ¬ WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := fun hW =>
    hRH (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hW).1
  obtain ⟨a, ha, hfail⟩ : ∃ a : ℝ, 0 < a ∧
      ¬ weightAperturePositivity a (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
    by_contra hcon
    push Not at hcon
    refine hnot ((weightFailureApertures_eq_empty_iff _).mp
      (Set.eq_empty_iff_forall_notMem.mpr fun b hb => ?_))
    exact hb.2 (hcon b hb.1)
  obtain ⟨f, hf, hfs, hneg⟩ : ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f f)).re < 0 := by
    by_contra hcon
    push Not at hcon
    exact hfail fun f hf hfs => by
      have := hcon f hf hfs
      linarith
  exact h ⟨a, refutes_radiusReading hf hfs hneg⟩

/-! ### 4. The calculus -/

/-- **The refutation calculus.** On both faces the negative side of RH is decided by bounded data,
and RH itself is the statement that no bounded reading refutes it. -/
theorem theRefutationCalculus :
    (RiemannHypothesis ↔
        ¬ ∃ T : ℝ, Refutes (heightReading T) (fun W => width W = 0) zetaConfig) ∧
      (RiemannHypothesis ↔
        ¬ ∃ R : ℝ, Refutes (radiusReading R)
          WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) :=
  ⟨riemannHypothesis_iff_no_heightReading_refutes,
    riemannHypothesis_iff_no_radiusReading_refutes⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
