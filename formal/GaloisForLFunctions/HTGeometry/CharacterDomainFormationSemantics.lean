import GaloisForLFunctions.HTGeometry.ExponentialCharacterDomain
import GaloisForLFunctions.HTGeometry.ConstitutiveCharacterDomainFormation

/-!
# Measure semantics of the character-domain formation grammar

A finite formation expression built from positive mixture, independent fusion, legal exponential
tilt, reflection and clock-preserving recovery evaluates to a finite positive measure on the line,
and its exponential-character domain is exactly the intersection of the affine pullbacks of the
leaf domains.
-/

open MeasureTheory CharacterDomainFormation
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- Measure semantics of a finite formation expression. -/
def evalMeasure (leafMeasure : ι → Measure ℝ) : Expr ι → Measure ℝ
  | .leaf i => leafMeasure i
  | .mix L R => evalMeasure leafMeasure L + evalMeasure leafMeasure R
  | .fuse L R => (evalMeasure leafMeasure L) ∗ (evalMeasure leafMeasure R)
  | .tilt a E => exponentialTilt (evalMeasure leafMeasure E) a
  | .reflect E => reflectMeasure (evalMeasure leafMeasure E)
  | .recover E => evalMeasure leafMeasure E

/-- A formation expression is legal when every tilt uses an admitted parameter. -/
def Legal (leafMeasure : ι → Measure ℝ) : Expr ι → Prop
  | .leaf _ => True
  | .mix L R => Legal leafMeasure L ∧ Legal leafMeasure R
  | .fuse L R => Legal leafMeasure L ∧ Legal leafMeasure R
  | .tilt a E => Legal leafMeasure E ∧ a ∈ characterDomain (evalMeasure leafMeasure E)
  | .reflect E => Legal leafMeasure E
  | .recover E => Legal leafMeasure E

/-- Every legal formation of nonzero finite leaves is a nonzero finite measure. -/
theorem evalMeasure_ne_zero_and_finite {leafMeasure : ι → Measure ℝ}
    (hne : ∀ i, leafMeasure i ≠ 0) (hfin : ∀ i, IsFiniteMeasure (leafMeasure i))
    (E : Expr ι) (hE : Legal leafMeasure E) :
    evalMeasure leafMeasure E ≠ 0 ∧ IsFiniteMeasure (evalMeasure leafMeasure E) := by
  induction E with
  | leaf i => exact ⟨hne i, hfin i⟩
  | mix L R ihL ihR =>
      obtain ⟨hL0, hLf⟩ := ihL hE.1
      obtain ⟨hR0, hRf⟩ := ihR hE.2
      haveI := hLf
      haveI := hRf
      simp only [evalMeasure]
      refine ⟨?_, inferInstance⟩
      intro h
      refine hL0 ?_
      have huniv : (evalMeasure leafMeasure L + evalMeasure leafMeasure R) Set.univ = 0 := by
        rw [h]
        simp
      rw [Measure.coe_add, Pi.add_apply, add_eq_zero] at huniv
      exact Measure.measure_univ_eq_zero.1 huniv.1
  | fuse L R ihL ihR =>
      obtain ⟨hL0, hLf⟩ := ihL hE.1
      obtain ⟨hR0, hRf⟩ := ihR hE.2
      haveI := hLf
      haveI := hRf
      have hmass : (evalMeasure leafMeasure L ∗ evalMeasure leafMeasure R) Set.univ
          = evalMeasure leafMeasure L Set.univ * evalMeasure leafMeasure R Set.univ :=
        conv_univ _ _
      simp only [evalMeasure]
      refine ⟨?_, ⟨?_⟩⟩
      · intro h
        rw [h] at hmass
        simp only [Measure.coe_zero, Pi.zero_apply] at hmass
        rcases mul_eq_zero.1 hmass.symm with h1 | h1
        · exact hL0 (Measure.measure_univ_eq_zero.1 h1)
        · exact hR0 (Measure.measure_univ_eq_zero.1 h1)
      · rw [hmass]
        exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)
  | tilt a E ih =>
      obtain ⟨h0, hf⟩ := ih hE.1
      haveI := hf
      haveI := isProbabilityMeasure_exponentialTilt h0 hE.2
      have huniv := exponentialTilt_univ h0 hE.2
      simp only [evalMeasure]
      refine ⟨?_, inferInstance⟩
      intro h
      rw [h] at huniv
      simp at huniv
  | reflect E ih =>
      obtain ⟨h0, hf⟩ := ih hE
      haveI := hf
      simp only [evalMeasure]
      refine ⟨reflectMeasure_ne_zero h0, ?_⟩
      refine ⟨?_⟩
      rw [reflectMeasure, Measure.map_apply measurable_neg MeasurableSet.univ]
      exact measure_lt_top _ _
  | recover E ih => exact ih hE

/-- **Global affine-leaf legality.**  The character domain of a legal formation is the
intersection of the affine pullbacks of the leaf domains. -/
theorem characterDomain_evalMeasure {leafMeasure : ι → Measure ℝ}
    (hne : ∀ i, leafMeasure i ≠ 0) (hfin : ∀ i, IsFiniteMeasure (leafMeasure i))
    (E : Expr ι) (hE : Legal leafMeasure E) :
    characterDomain (evalMeasure leafMeasure E)
      = {t : ℝ | E.Admitted (fun i => characterDomain (leafMeasure i)) t} := by
  induction E with
  | leaf i => rfl
  | mix L R ihL ihR =>
      obtain ⟨hL0, hLf⟩ := evalMeasure_ne_zero_and_finite hne hfin L hE.1
      obtain ⟨hR0, hRf⟩ := evalMeasure_ne_zero_and_finite hne hfin R hE.2
      have hsplit : evalMeasure leafMeasure (Expr.mix L R)
          = (1 : ℝ≥0∞) • evalMeasure leafMeasure L + (1 : ℝ≥0∞) • evalMeasure leafMeasure R := by
        simp [evalMeasure]
      rw [hsplit, characterDomain_mixture one_ne_zero ENNReal.one_ne_top one_ne_zero
        ENNReal.one_ne_top, ihL hE.1, ihR hE.2]
      rfl
  | fuse L R ihL ihR =>
      obtain ⟨hL0, hLf⟩ := evalMeasure_ne_zero_and_finite hne hfin L hE.1
      obtain ⟨hR0, hRf⟩ := evalMeasure_ne_zero_and_finite hne hfin R hE.2
      haveI := hRf
      simp only [evalMeasure]
      rw [characterDomain_conv hL0 hR0, ihL hE.1, ihR hE.2]
      rfl
  | tilt a E ih =>
      obtain ⟨h0, hf⟩ := evalMeasure_ne_zero_and_finite hne hfin E hE.1
      simp only [evalMeasure]
      rw [characterDomain_exponentialTilt h0 hE.2]
      ext t
      simp only [Set.mem_setOf_eq]
      rw [Set.ext_iff.1 (ih hE.1) (t + a)]
      rfl
  | reflect E ih =>
      simp only [evalMeasure]
      rw [characterDomain_reflectMeasure]
      ext t
      simp only [Set.mem_neg, Set.mem_setOf_eq]
      rw [Set.ext_iff.1 (ih hE) (-t)]
      rfl
  | recover E ih => exact ih hE

/-- **Global affine-leaf legality, constraint form.** -/
theorem characterDomain_evalMeasure_constraints {leafMeasure : ι → Measure ℝ}
    (hne : ∀ i, leafMeasure i ≠ 0) (hfin : ∀ i, IsFiniteMeasure (leafMeasure i))
    (E : Expr ι) (hE : Legal leafMeasure E) :
    characterDomain (evalMeasure leafMeasure E)
      = {t : ℝ | ∀ c ∈ E.constraints, c.eval t ∈ characterDomain (leafMeasure c.leaf)} := by
  rw [characterDomain_evalMeasure hne hfin E hE]
  ext t
  simpa [Constraint.Holds] using
    Expr.admitted_iff_constraints (fun i => characterDomain (leafMeasure i)) E t

end

end GaloisForLFunctions.HTGeometry
