import GaloisForLFunctions.HTGeometry.KaehlerRankTranscendenceDegree
import GaloisForLFunctions.HTGeometry.LogarithmicDifferentialAlgebraicity

/-! # Exponential phases of algebraic clocks on a spectral curve -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates
noncomputable section
universe u
variable {C K : Type u} [Field C] [Field K] [Algebra C K] [CharZero C]

/-- A nonzero tangent derivation detects the entire cotangent space of
an algebraic curve. A logarithmic derivative equal to an exact derivative
along that tangent forces both functions to be algebraic constants. -/
theorem curve_logarithmic_rigidity (hcurve : Algebra.trdeg C K=1)
    (D : Derivation C K K) {u : K} (hu : D u ≠ 0) {f w : K} (hw : w ≠ 0)
    (hlog : D w=w*D f) : IsAlgebraic C f ∧ IsAlgebraic C w := by
  let d := KaehlerDifferential.D C K
  let L := D.liftKaehlerDifferential
  have hL (a : K) : L (d a)=D a := Derivation.liftKaehlerDifferential_comp_D D a
  have he : d u ≠ 0 := by
    intro h
    exact hu ((hL u).symm.trans (by rw [h,map_zero]))
  have inject : Function.Injective L := by
    intro v z hz
    obtain ⟨c,hc,_⟩ := exists_unique_smul_of_trdeg_eq_one C K hcurve he (v-z)
    have hcz : c*D u = 0 := by
      calc c*D u = L (c • d u) := by rw [map_smul,hL,smul_eq_mul]
           _ = L (v-z) := congrArg L hc.symm
           _ = 0 := by rw [map_sub,hz,sub_self]
    have hc₀ := (mul_eq_zero.mp hcz).resolve_right hu
    exact sub_eq_zero.mp (hc.trans (by rw [hc₀,zero_smul]))
  apply algebraic_of_kaehlerD_eq_smul hw
  apply inject
  rw [map_smul,hL,hL,smul_eq_mul,hlog]

#print axioms curve_logarithmic_rigidity
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates
