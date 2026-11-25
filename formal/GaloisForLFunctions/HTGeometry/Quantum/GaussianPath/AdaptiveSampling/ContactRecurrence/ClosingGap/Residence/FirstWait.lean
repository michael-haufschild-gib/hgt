import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence.BackwardVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence.InwardWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.PhysicalClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon
import Mathlib.Data.Fin.Tuple.Sort

/-! # First scalar wait from the length of the visit and the ordered energy gaps -/

open Set Filter Finset Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
open EmptyVisitFlux PrecisionReturns
noncomputable section

private theorem arc_relabel {I J : Type*} [Fintype I] [Fintype J] (e : J ≃ I)
    (p : I → UnitAddCircle) (r : ℝ) : p ∘ e∈enclosingUnitArc r ↔ p∈enclosingUnitArc r := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    refine mem_iUnion.mpr ⟨e j,fun i hi => ?_⟩
    obtain ⟨k,rfl⟩ := e.surjective i
    exact hj k (fun hh => hi (congrArg e hh))
  · intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    obtain ⟨j,rfl⟩ := e.surjective i
    exact mem_iUnion.mpr ⟨j,fun k hk => hi (e k) (fun hh => hk (e.injective hh))⟩

/-- For each ordered adjacent gap, the elapsed time to the midpoint
of a first scalar visit is bounded in terms of its length and the
other gaps. All spacings are in turns per unit of physical time. -/
theorem first_residence_deadline {N d : ℕ} (H : selfAdjoint (Register N))
    (e : Fin (d+1) ≃ (Fin N → Bool)) (hi : Function.Injective H.2.isHermitian.eigenvalues) :
    ∃ b : Fin (d+1) ≃ (Fin N → Bool),
      let w (i : Fin (d+1)) := -H.2.isHermitian.eigenvalues (b i)/(2*π)
      let g (k : Fin d) := w k.succ-w k.castSucc
      StrictMono w ∧ ∀ a : ℝ, ∀ ε∈Ioo (0:ℝ) (sqrt 2), let v := firstVisit H a 0 ε
        ∀ h>0, (∀ u∈Icc (0:ℝ) h, HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val (v+u))) →
          ∀ p : Fin d, (v-a+h/2)*g p<((∏ k : {j : Fin d // j≠p}, ⌈2/(h*g k)⌉₊ : ℕ):ℝ) := by
  let w₀ (i : Fin N → Bool) := -H.2.isHermitian.eigenvalues i/(2*π)
  let b := (Tuple.sort (w₀ ∘ e)).trans e
  have hinj : Function.Injective w₀ := fun _ _ h => hi (neg_inj.mp ((div_left_inj' (by positivity : (2:ℝ)*π≠0)).mp h))
  refine ⟨b,?_⟩
  intro w g
  have hw : StrictMono w := (Tuple.monotone_sort (w₀ ∘ e)).strictMono_of_injective (hinj.comp b.injective)
  refine ⟨hw,?_⟩
  intro a ε hε v h hh hv p
  let r := SharpOccupation.physicalArc ε
  have hr := (SharpOccupation.physicalArc_spec hε.1 hε.2).1
  have ha (t : ℝ) : flow w t∈enclosingUnitArc r ↔ HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val t) :=
    (arc_relabel b (flow w₀ t) r).trans (physical_visit H hε.1 hε.2 t)
  obtain ⟨q,hq,hQ,ht,hback⟩ := backward_visit w hw p hr.1.le hr.2 hh (fun u hu => (ha _).mpr (hv u hu))
  have ht0 : v+h/2-(q:ℝ)/g p<a := by
    by_contra! hle
    exact ht.not_ge ((firstVisit_isLeast H a 0 hε.1).2 ⟨hle,(ha _).mp hback⟩)
  have hg : 0<g p := sub_pos.mpr (hw (Fin.castSucc_lt_succ (i:=p)))
  exact ((lt_div_iff₀ hg).mp (show v-a+h/2<(q:ℝ)/g p by linarith only [ht0])).trans_le (Nat.cast_le.mpr hQ)

/-- At the actual first scalar return after the 9/80 crossing, every
positive residence length gives the gap-product deadline at error 1/10. -/
theorem gaussian_first_wait_residence :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let d := 2^N-1
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∃ b : Fin (d+1) ≃ (Fin N → Bool),
          let w (i : Fin (d+1)) := -H.2.isHermitian.eigenvalues (b i)/(2*π)
          let g (j : Fin d) := w j.succ-w j.castSucc
          let v := firstVisit H σ 0 (1/10)
          StrictMono w ∧ (∃ h>0, ∀ u∈Icc (0:ℝ) h, HasProjectiveCircuitApproximation N (1/10) 0 (unitaryEvolution H.val (v+u))) ∧
            ∀ h>0, (∀ u∈Icc (0:ℝ) h, HasProjectiveCircuitApproximation N (1/10) 0 (unitaryEvolution H.val (v+u))) →
            ∀ p : Fin d, (v-σ+h/2)*g p<((∏ j : {i : Fin d // i≠p}, ⌈2/(h*g j)⌉₊ : ℕ):ℝ) := by
  have ht : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  have he : (0:ℝ)<1/10 := by norm_num
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,gaussian_unshifted_first_excursion_tick_gaps,
    EntrySensitivity.gaussian_first_empty_inward_face (1/10) he ht] with ω hi hc hf
  filter_upwards [hc] with k hk
  intro N d H P
  obtain ⟨σ,hσ,hcross,hprior,_⟩ := hk
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  obtain ⟨b,hmono,hbound⟩ := first_residence_deadline H e.symm (hi k).injective
  have hout : 1/10<orbitCircuitDistance H 0 σ := by
    by_contra! h
    obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr h
    have hl : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
      ⟨z,hz,C,hC.trans (Nat.zero_le _),herr⟩
    rw [hcross] at hl
    norm_num at hl
  obtain ⟨i,j,hface⟩ := hf k σ hσ hout
  obtain ⟨h,hh,hstay⟩ := inward_window (SharpOccupation.physicalArc_spec he ht).1.1 hface
  exact ⟨σ,hσ,hcross,hprior,b,hmono,⟨h,hh,fun u hu => (physical_visit H he ht _).mp (hstay u hu)⟩,
    hbound σ (1/10) ⟨he,ht⟩⟩

#print axioms gaussian_first_wait_residence
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
