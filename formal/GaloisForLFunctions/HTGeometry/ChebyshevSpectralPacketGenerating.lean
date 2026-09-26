import GaloisForLFunctions.HTGeometry.ChebyshevFormalGenerating
import GaloisForLFunctions.HTGeometry.ChebyshevSpectralPacketTrace

namespace GaloisForLFunctions.HTGeometry

noncomputable def packetChebyshevSeries {r : ℕ} (lam w : Fin r → ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk (packetChebyshevTrace lam w)

theorem packetChebyshevSeries_eq_nodes {r : ℕ} (lam w : Fin r → ℂ) :
    packetChebyshevSeries lam w =
      ∑ j : Fin r,
        PowerSeries.C (w j * lam j) *
          _root_.HTGeometry.chebyshevNodeSeries (1 - 2 * lam j) := by
  classical
  apply PowerSeries.ext
  intro n
  rw [packetChebyshevSeries, PowerSeries.coeff_mk, map_sum]
  simp only [PowerSeries.coeff_C_mul, _root_.HTGeometry.chebyshevNodeSeries,
    PowerSeries.coeff_mk]
  exact packetChebyshevTrace_eq_nodes lam w n

theorem packetChebyshevSeries_centered {r : ℕ} (lam w : Fin r → ℂ) :
    2 * packetChebyshevSeries lam w -
        PowerSeries.C (∑ j : Fin r, w j * lam j) =
      ∑ j : Fin r,
        PowerSeries.C (w j * lam j) *
          (2 * _root_.HTGeometry.chebyshevNodeSeries (1 - 2 * lam j) - 1) := by
  classical
  rw [packetChebyshevSeries_eq_nodes, map_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end GaloisForLFunctions.HTGeometry
