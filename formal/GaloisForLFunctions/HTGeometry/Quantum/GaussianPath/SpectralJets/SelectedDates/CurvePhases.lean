import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicClock
import GaloisForLFunctions.HTGeometry.ExponentialLinearIndependence

/-! # Independence of phase monomials on an algebraic spectral curve -/
open scoped Differential
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates
noncomputable section
universe u
variable {C L : Type u} [Field C] [Field L] [Algebra C L] [CharZero C]

/-- Distinct algebraic actions giving nonconstant differences cannot have
a vanishing exponential sum over the curve's algebraic function field.
This applies to monomials in the phases by taking their actions to be the
corresponding integral sums of the eigenphases' arguments. -/
theorem exponential_sum_on_curve {ι : Type*} [Fintype ι] (K : IntermediateField C L)
    (hcurve : Algebra.trdeg C K=1) (D : Derivation C K K) (D₀ : Derivation C L L)
    (hext : ∀ a : K, D₀ (a:L)=(D a:L)) {u : K} (hu : D u ≠ 0)
    (f : ι → K) (E : ι → L) (hE : ∀ i, E i ≠ 0)
    (hE' : ∀ i, D₀ (E i)=(D (f i):L)*E i)
    (hd : ∀ i j, i ≠ j → Transcendental C (f i-f j))
    (c : ι → K) (hc : ∑ i, (c i:L)*E i=0) : ∀ i, c i=0 := by
  letI : Differential L := differentialOfDerivation D₀
  let τ (i : ι) : L := D (f i)
  have closed (x : L) (hx : x∈K.toSubfield) : x′∈K.toSubfield := by
    change D₀ x∈K
    change D₀ ((⟨x,hx⟩ : K):L)∈K
    rw [hext]
    exact (D ⟨x,hx⟩).property
  have no_log (i j : ι) (hne : i ≠ j) (x : L) (hx : x∈K.toSubfield) (hx₀ : x ≠ 0)
      (he : x′=(τ i-τ j)*x) : False := by
    let y : K := ⟨x,hx⟩
    have hy : y ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
    have hh : D y=y*D (f i-f j) := by
      apply Subtype.ext
      change (D y:L)=x*((D (f i-f j)):L)
      rw [←hext,map_sub]
      exact he.trans (mul_comm _ _)
    exact (hd i j hne) (curve_logarithmic_rigidity hcurve D hu hy hh).1
  have h := eq_zero_of_sum_expLike_eq_zero K.toSubfield closed E τ hE hE'
    (fun i => (D (f i)).property) no_log (fun i => (c i:L)) (fun i => (c i).property) hc
  exact fun i => Subtype.ext (h i)

#print axioms exponential_sum_on_curve
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates
