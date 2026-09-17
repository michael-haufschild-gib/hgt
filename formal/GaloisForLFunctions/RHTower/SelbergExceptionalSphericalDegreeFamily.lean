import GaloisForLFunctions.RHTower.SelbergExceptionalSphericalModel
import GaloisForLFunctions.RHTower.SymmetricPowerDegreeFamilies

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- An exceptional Selberg eigenvalue fails the spherical packet unitarity test
in at least one degree of every infinite degree family. Thus an SQB realization
needs compatible unitary symmetric-power lifts only on one infinite family,
not necessarily every degree. -/
theorem SelbergExceptionalEigenvalue.exists_nonunitarizable_symmetricPower_degree_in
    (eigenvalue : SelbergExceptionalEigenvalue) (D : Set ℕ) (hD : D.Infinite) :
    ∃ d : ℕ, d ∈ D ∧
      ¬ SymmetricPowerSphericalPacketUnitarizable eigenvalue.complementaryExponent d := by
  by_contra h
  have hunit : ∀ d ∈ D,
      SymmetricPowerSphericalPacketUnitarizable eigenvalue.complementaryExponent d := by
    intro d hd
    by_contra hnot
    exact h ⟨d, hd, hnot⟩
  have hgeneric : eigenvalue.complementaryExponent ∈
      {ν : ℝ | ∀ d ∈ D, ν ∈ genericUnitarySymPowerLocus d} := by
    intro d hd
    exact (symmetricPowerSphericalPacketUnitarizable_iff
      eigenvalue.complementaryExponent d).mp (hunit d hd)
  have hfamily : {ν : ℝ | ∀ d ∈ D, ν ∈ genericUnitarySymPowerLocus d} = {0} :=
    (genericUnitarySymPower_degree_family_eq_singleton_iff D).mpr hD
  rw [hfamily] at hgeneric
  exact eigenvalue.complementaryExponent_mem_Ioo.1.ne' (by simpa using hgeneric)

end
end GaloisForLFunctions.RHTower
