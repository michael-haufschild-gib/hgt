import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClopenHodgeTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgeTraceTower
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ClopenHodgeCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgePullbackComposition

/-! Trace from a clopen component is the coordinate inclusion under
the product decomposition of Hodge cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [CommRing k] {X : Scheme.{0}} {J : Type} [Fintype J] [DecidableEq J]
  (s : X ⟶ Spec (CommRingCat.of k)) (V : J → X.Opens)
  (hclosed : ∀ j, IsClosed (V j : Set X))
  (hdis : ∀ i j, i ≠ j → V i ⊓ V j = ⊥) (hcov : iSup V = ⊤)

/-- In the product of component cohomologies, the trace of a class
on one component is supported in that coordinate. -/
theorem hodgeClopenEquiv_trace (p q : ℕ) (i : J)
    (x : HodgeCohomology ((V i).ι ≫ s) p q) :
    letI (j : J) : IsClosedImmersion (V j).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed j)
    hodgeClopenEquiv s V p q hclosed hdis hcov (hodgeTrace (f := (V i).ι) rfl p q x) =
      Pi.single i x := by
  letI (j : J) : IsClosedImmersion (V j).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed j)
  let E := hodgeClopenEquiv s V p q hclosed hdis hcov
  let w : ∀ j, HodgeCohomology ((V j).ι ≫ s) p q := Pi.single i x
  let z := E.symm w
  let pull (j : J) := hodgePullback (s := s) (f := (V j).ι) rfl p q
  let trace (j : J) := hodgeTrace (s := s) (f := (V j).ι) rfl p q
  let hid : (𝟙 X) ≫ s = s := Category.id_comp s
  have htrace := hodgeTrace_hodgePullback_of_trace_one hid p q 1
    (fun U hU => by simpa only [Nat.cast_one] using affineSectionTrace_id_one s hU) z
  rw [one_nsmul] at htrace
  have hpull (j : J) :
      pull j (hodgePullback hid p q z) = pull j z := by
    have h := hodgePullback_comp hid (f := 𝟙 X) (g := (V j).ι) rfl
      (by rw [Category.comp_id]) p q z
    refine h.trans ?_
    have he (a b : (V j).toScheme ⟶ X) (e : a = b)
        (ha : a ≫ s = (V j).ι ≫ s) (hb : b ≫ s = (V j).ι ≫ s) :
        hodgePullback ha p q z = hodgePullback hb p q z := by
      subst b
      rfl
    exact he _ _ (Category.comp_id _) _ rfl
  have hz : z = ∑ j, trace j (pull j z) := by
    calc
      z = hodgeTrace hid p q (hodgePullback hid p q z) := htrace.symm
      _ = _ := (hodgeTrace_eq_sum_clopen hid V hdis hcov p q (hodgePullback hid p q z)).trans
        (Finset.sum_congr rfl (fun j _ => by
          rw [hodgeTrace_congr (Category.comp_id (V j).ι) _ rfl]
          exact congrArg (trace j) (hpull j)))
  have hE : E z = w := E.apply_symm_apply _
  have he (j : J) : pull j z = w j := by
    calc
      _ = E z j := (hodgeClopenEquiv_apply s V p q hclosed hdis hcov z j).symm
      _ = _ := congrFun hE j
  have hs : (∑ j, trace j (pull j z)) = trace i x := by
    rw [Finset.sum_eq_single i]
    · rw [he i, show w i = x from
        Pi.single_eq_same (M := fun j => HodgeCohomology ((V j).ι ≫ s) p q) i x]
    · intro j _ hj
      rw [he j, show w j = 0 from
        Pi.single_eq_of_ne (M := fun j => HodgeCohomology ((V j).ι ≫ s) p q) hj x, map_zero]
    · simp
  exact (congrArg E (hz.trans hs).symm).trans hE

end GlobalTheory.SchemeCohomology
