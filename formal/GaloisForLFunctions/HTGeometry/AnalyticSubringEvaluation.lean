import GaloisForLFunctions.HTGeometry.MeromorphicTranslation

/-!
# Pointwise evaluation of global analytic germs

Over the principal filter of the whole complex plane, germ equality is literal pointwise equality.
This file packages evaluation as a ring homomorphism, proves pointwise extensionality, and records the
identity-theorem bridge from local equality back to the global analytic subring.  These lemmas let
field identities between global meromorphic fractions be proved on any nonempty regular
neighborhood and then promoted without choosing representatives in theorem statements.
-/

open Filter Set Topology

namespace GaloisForLFunctions

open Bottcher

noncomputable section

/-- Evaluation at a point is well-defined on germs over the principal filter of `univ`. -/
def univGermEval (z : ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ →+* ℂ where
  toFun := Quotient.lift (fun f : ℂ → ℂ => f z) (by
    intro f g h
    exact eventually_principal.mp h z (Set.mem_univ z))
  map_one' := rfl
  map_mul' := by
    intro f g
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl
  map_zero' := rfl
  map_add' := by
    intro f g
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl

@[simp] theorem univGermEval_coe (z : ℂ) (f : ℂ → ℂ) :
    univGermEval z (f : Germ (𝓟 Set.univ) ℂ) = f z := by
  rfl

/-- Global germs are equal when all of their point evaluations agree. -/
theorem univGerm_ext {f g : Germ (𝓟 (Set.univ : Set ℂ)) ℂ}
    (h : ∀ z, univGermEval z f = univGermEval z g) : f = g := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      apply Quotient.sound
      exact eventually_principal.mpr fun z _ => by
        simpa only [univGermEval_coe] using! h z

/-- Evaluation intertwines analytic translation with translation of the evaluation point. -/
@[simp] theorem univGermEval_addTranslationAnalyticEquiv
    (q z : ℂ) (a : analyticSubring (Set.univ : Set ℂ)) :
    univGermEval z
        ((addTranslationAnalyticEquiv q a : analyticSubring Set.univ) :
          Germ (𝓟 Set.univ) ℂ) =
      univGermEval (z + q) (a : Germ (𝓟 Set.univ) ℂ) := by
  change univGermEval z
      (((Bottcher.precompAnalytic (analyticOnNhd_addTranslation q _)
        (Set.mapsTo_univ _ _) a : analyticSubring Set.univ) :
          Germ (𝓟 Set.univ) ℂ)) = _
  rw [Bottcher.precompAnalytic_coe]
  induction a.1 using Quotient.inductionOn with
  | _ f => rfl

/-- Evaluation respects multiplication in the global analytic subring. -/
@[simp] theorem univGermEval_analyticSubring_mul (z : ℂ)
    (a b : analyticSubring (Set.univ : Set ℂ)) :
    univGermEval z ((a * b : analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ) =
      univGermEval z (a : Germ (𝓟 Set.univ) ℂ) *
        univGermEval z (b : Germ (𝓟 Set.univ) ℂ) := by
  change univGermEval z
      ((a : Germ (𝓟 Set.univ) ℂ) * (b : Germ (𝓟 Set.univ) ℂ)) = _
  exact map_mul (univGermEval z) _ _

/-- Evaluation respects subtraction in the global analytic subring. -/
@[simp] theorem univGermEval_analyticSubring_sub (z : ℂ)
    (a b : analyticSubring (Set.univ : Set ℂ)) :
    univGermEval z ((a - b : analyticSubring Set.univ) : Germ (𝓟 Set.univ) ℂ) =
      univGermEval z (a : Germ (𝓟 Set.univ) ℂ) -
        univGermEval z (b : Germ (𝓟 Set.univ) ℂ) := by
  change univGermEval z
      ((a : Germ (𝓟 Set.univ) ℂ) - (b : Germ (𝓟 Set.univ) ℂ)) = _
  exact map_sub (univGermEval z) _ _

/-- Local equality of two global analytic germs implies equality in the analytic subring. -/
theorem analyticSubring_eq_of_eventually_eval_eq
    {a b : analyticSubring (Set.univ : Set ℂ)} {z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝 z₀,
      univGermEval z (a : Germ (𝓟 Set.univ) ℂ) =
        univGermEval z (b : Germ (𝓟 Set.univ) ℂ)) :
    a = b := by
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  have hfg : f =ᶠ[𝓝 z₀] g := by
    filter_upwards [h] with z hz
    rw [← hfa, ← hgb] at hz
    simpa using hz
  have hall : f = g := hf.eq_of_eventuallyEq hg hfg
  apply Subtype.ext
  rw [← hfa, ← hgb, hall]

/-- A nonzero global analytic germ has a point where its evaluation is nonzero. -/
theorem exists_univGermEval_ne_zero_of_ne_zero
    {a : analyticSubring (Set.univ : Set ℂ)} (ha : a ≠ 0) :
    ∃ z : ℂ, univGermEval z (a : Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
  by_contra h
  push Not at h
  apply ha
  apply Subtype.ext
  apply univGerm_ext
  intro z
  simpa using h z

/-- Nonvanishing of a global analytic germ persists on a neighborhood of the point. -/
theorem eventually_univGermEval_ne_zero
    {a : analyticSubring (Set.univ : Set ℂ)} {z₀ : ℂ}
    (ha : univGermEval z₀ (a : Germ (𝓟 Set.univ) ℂ) ≠ 0) :
    ∀ᶠ z in 𝓝 z₀,
      univGermEval z (a : Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
  obtain ⟨f, hf, hfa⟩ := a.2
  have hcont : ContinuousAt f z₀ := (hf z₀ (Set.mem_univ z₀)).continuousAt
  have hfa0 : f z₀ ≠ 0 := by
    have ha' := ha
    rw [← hfa] at ha'
    simpa using ha'
  filter_upwards [hcont.eventually_ne hfa0] with z hz
  rw [← hfa]
  simpa using hz

end

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- Evaluation respects addition in the global analytic subring. -/
@[simp] theorem univGermEval_analyticSubring_add (z : ℂ)
    (a b : Bottcher.analyticSubring (Set.univ : Set ℂ)) :
    univGermEval z ((a + b : Bottcher.analyticSubring Set.univ) :
      Germ (𝓟 Set.univ) ℂ) =
      univGermEval z (a : Germ (𝓟 Set.univ) ℂ) +
        univGermEval z (b : Germ (𝓟 Set.univ) ℂ) := by
  change univGermEval z
      ((a : Germ (𝓟 Set.univ) ℂ) + (b : Germ (𝓟 Set.univ) ℂ)) = _
  exact map_add (univGermEval z) _ _

end GaloisForLFunctions
