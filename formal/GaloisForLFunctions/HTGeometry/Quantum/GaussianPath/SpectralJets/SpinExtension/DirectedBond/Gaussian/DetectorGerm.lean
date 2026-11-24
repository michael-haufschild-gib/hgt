import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.ComplexChart
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.EnergySeparation

/-! # Detecting a nonzero physical response minor from its labeled root germs -/
open Matrix MvPolynomial Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {n D : ℕ} {R : Type*} [CommRing R]

private theorem partial_value (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R→+*ℂ)
    (x : Fin n→ℂ) (y : ℂ) :
    eval (fun o : Option (Fin n) => o.elim y x) (pderiv none (map φ (characteristic A))) =
      (∑ a, x a • (A a).map φ).charpoly.derivative.eval y := by
  let v (u : ℂ) (o : Option (Fin n)) := o.elim u x
  let d (o : Option (Fin n)) : ℂ := o.elim 1 (fun _ => 0)
  have hv : HasDerivAt v d y := by
    apply hasDerivAt_pi.mpr
    intro o
    cases o with
    | none => exact hasDerivAt_id _
    | some i => exact hasDerivAt_const _ _
  have h' : HasDerivAt (fun u => eval (v u) (map φ (characteristic A)))
      (eval (v y) (pderiv none (map φ (characteristic A)))) y := by
    simpa [v,d,Fintype.sum_option] using hasDerivAt_mvPolynomial_eval_comp (map φ (characteristic A)) hv
  have hz : (fun u => eval (v u) (map φ (characteristic A))) =
      fun u => (∑ a, x a • (A a).map φ).charpoly.eval u := by
    funext u
    rw [eval_map,Matrix.eval_charpoly]
    exact eval_characteristic A φ x u
  rw [hz] at h'
  exact h'.unique (Polynomial.hasDerivAt _ _)

/-- Choosing the individual energy labels at the witness does not require them
to be in sorted order. Distinct roots already supply the full trace packet. -/
theorem detector_of_germs (A : Fin n → Matrix (Fin D) (Fin D) R) (φ : R→+*ℂ)
    (x : Fin n→ℂ) (F : Fin D → (Fin n→ℂ) → ℂ) (hi : Function.Injective (fun l => F l x))
    (hf : ∀ l, AnalyticAt ℂ (F l) x ∧ ∀ᶠ z in 𝓝 x,
      matrixCharpolyRelation (∑ a, z a • (A a).map φ,F l z)=0)
    (L : ℕ) (rows : Fin D→Option (List (Fin n))) (hw : ∀ i v, v∈rows i → v.length≤L)
    (hm : (of fun i l => rowValue (rows i) (F l) x).det≠0) :
    eval₂Hom φ x (jetGram A L rows)≠0 := by
  have h₁ (l) := (hf l).1.eventually_analyticAt.and (hf l).2
  have h₂ (i j : Fin D) : ∀ᶠ z in 𝓝 x, F i z=F j z → i=j := by
    by_cases he : i=j
    · exact Eventually.of_forall fun _ _ => he
    · have hn := ((hf i).1.continuousAt.sub (hf j).1.continuousAt).eventually_ne (sub_ne_zero.mpr (hi.ne he))
      exact hn.mono fun _ h eq => (sub_ne_zero.mp h eq).elim
  have hnear := (eventually_all.mpr h₁).and (eventually_all.mpr fun i => eventually_all.mpr (h₂ i))
  obtain ⟨U,hU,ho,hx⟩ := mem_nhds_iff.mp hnear
  have hs (z) (hz : z∈U) (j : Fin D) : onRoot (pderiv none (map φ (characteristic A))) (F j) z≠0 := by
    rw [onRoot,partial_value]
    exact simple_packet _ (fun i => F i z) (fun _ _ => (hU hz).2 _ _) (fun i => by
      simpa only [matrixCharpolyRelation,←Matrix.eval_charpoly] using ((hU hz).1 i).2) j
  rw [eval_jetGram_on_chart A φ ho F (fun j z hz => ((hU hz).1 j).1)
    (fun z hz _ _ => (hU hz).2 _ _) (fun z hz j => ((hU hz).1 j).2) hs hx L rows hw]
  exact pow_ne_zero _ (mul_ne_zero hm (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hs x hx j)))

#print axioms detector_of_germs
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
