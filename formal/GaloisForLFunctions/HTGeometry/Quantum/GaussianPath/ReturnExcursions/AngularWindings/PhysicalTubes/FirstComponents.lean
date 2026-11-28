import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Laboratory
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.Reflection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # The exact circuit interval entered at the original first return -/

open Matrix MeasureTheory Real Set Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open PrescribedTimes ShortWindows SharpOccupation
noncomputable section

/-- At the actual first affordable visit, one implementing laboratory circuit enters a
single convex interval after the crossing. The first date is minimal over every
implementing circuit; the interval for its own circuit has width at most twice
the physical arc fraction divided by the extreme frequency gap. -/
theorem gaussian_first_visit_interval :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let K := k+3
      let X := prefixPoint k ω
      let H := prefixGenerator (k+1) X
      let A (i : Fin K → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
      let V := H.2.isHermitian.eigenvectorUnitary
      let P := nearHilbertContinuousCircuitBudget K
      let σ := crossingOrigin (k+1) P (9/80) X
      let x := physicalArc (1/10)
      ∃ l u : Fin K → Bool, let G := A u-A l
        0<G ∧ ∀ s : ℕ, let v := σ+crossingWait (k+1) P s X
          ∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ ∃ N : ℤ,
            let d := circuitTurns (V⁻¹*C.eval*V)
            let J := indexWindow G (d u-d l) x N
            let S := laboratoryDates H C.eval (1/10) ∩ J
            Convex ℝ S ∧ IsLeast (S ∩ Ici σ) v ∧
              ∀ C' : TwoQubitCircuit K, C'.gateCount ≤ s →
                ∀ t∈laboratoryDates H C'.eval (1/10), σ≤t → v≤t := by
  classical
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro K X H A V P σ x
  let w := pathPauliDisorderShell ω (k+1)
  have hmat : H.val=pathHamiltonian w := numberedGenerator_shell w
  have hinj : Function.Injective H.2.isHermitian.eigenvalues := by
    have hH : H=⟨pathHamiltonian w,isSelfAdjoint_pathHamiltonian _⟩ := Subtype.ext hmat
    rw [hH]
    exact (hω k).injective
  have hA : Function.Injective A := by
    intro i j he
    exact hinj (neg_injective ((div_left_inj' two_pi_pos.ne').mp he))
  obtain ⟨l,_,hmin⟩ := Finset.exists_min_image Finset.univ A Finset.univ_nonempty
  obtain ⟨u,_,hmax⟩ := Finset.exists_max_image Finset.univ A Finset.univ_nonempty
  have hext (i) : A i∈Icc (A l) (A u) := ⟨hmin i (mem_univ _),hmax i (mem_univ _)⟩
  have hg : A l<A u := lt_of_le_of_ne (hext u).1 (by
    intro he
    have hc (i : Fin K → Bool) : A i=A l := le_antisymm ((hext i).2.trans_eq he.symm) (hext i).1
    have hh := hA ((hc (fun _ => false)).trans (hc (fun _ => true)).symm)
    have hfalse := congrFun hh (⟨0,by dsimp only [K]; omega⟩ : Fin K)
    exact Bool.false_ne_true hfalse)
  refine ⟨l,u,sub_pos.mpr hg,?_⟩
  intro s v
  have hf := ElapsedWindow.first_wait_fit (k+1) P s X
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hf.2
  obtain ⟨c,hc,C,hC,herr⟩ := hfit
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) := ⟨by norm_num,
    (by norm_num : (1/10:ℝ)<1).trans_le (one_le_sqrt.mpr (by norm_num))⟩
  have hv : v∈laboratoryDates H C.eval (1/10) := ⟨c,hc,herr⟩
  obtain ⟨hcover,_,hconv⟩ := laboratory_cells H C.eval l u he hg hext
  obtain ⟨N,hN⟩ := mem_iUnion.mp (hcover hv)
  refine ⟨C,hC,N,?_⟩
  intro d J S
  have hfirst (C' : TwoQubitCircuit K) (hb : C'.gateCount ≤ s) (t : ℝ)
      (ht : t∈laboratoryDates H C'.eval (1/10)) (hσ : σ≤t) : v≤t := by
    obtain ⟨z,hz,hclose⟩ := ht
    have hd : pathGateDistance (k+1) s X t≤1/10 :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,C',hb,hclose⟩
    have hh := (crossingWait_le_iff (k+1) P s X (t-σ)).mpr
      ⟨t,⟨hσ,by change t≤σ+(t-σ); linarith⟩,hd⟩
    dsimp only [v]
    linarith only [hh]
  exact ⟨hconv N,⟨⟨⟨hv,hN⟩,le_add_of_nonneg_right hf.1⟩,fun t ht => hfirst C hC t ht.1.1 ht.2⟩,hfirst⟩

#print axioms gaussian_first_visit_interval
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
