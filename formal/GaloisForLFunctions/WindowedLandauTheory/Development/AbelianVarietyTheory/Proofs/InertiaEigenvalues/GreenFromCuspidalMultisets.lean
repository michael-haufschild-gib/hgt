import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalMultisetCount
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalExhaustion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenBridge

/-! The Gelfand–Graev bound exhausts the regular-character family and hence
the polynomial labels for cuspidal characters. -/

namespace GlobalTheory

/-- The regular-character construction exhausts the cuspidal characters of prime-field general linear groups. -/
theorem greenRegularCharacters : Published.GreenRegularCharacters :=
  greenRegularCharacters_of_multiset_bound GLq.card_cuspidal_multisets_le

/-- Green's cuspidal parameterization by irreducible polynomial labels. -/
theorem green : GLq.Green := GreenBridge.green_of_regular greenRegularCharacters

end GlobalTheory
