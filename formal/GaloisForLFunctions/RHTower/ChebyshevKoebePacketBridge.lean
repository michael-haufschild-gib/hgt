import GaloisForLFunctions.RHTower.ChebyshevKoebeGenerating
import GaloisForLFunctions.HTGeometry.ChebyshevSpectralPacketGenerating

namespace RHTower

noncomputable def packetCenteredChebyshevRational {r : ℕ}
    (lam w : Fin r → ℂ) (v : ℂ) : ℂ :=
  ∑ j : Fin r,
    w j * lam j * (1 - v ^ (2 : ℕ)) /
      (1 - 2 * v * (1 - 2 * lam j) + v ^ (2 : ℕ))

noncomputable def packetKoebeResolvent {r : ℕ}
    (lam w : Fin r → ℂ) (v : ℂ) : ℂ :=
  ∑ j : Fin r,
    if lam j = 0 then 0 else
      w j * (chebyshevTraceKoebeMap v /
        (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / lam j)))

theorem packetCenteredChebyshevRational_eq_koebe {r : ℕ}
    (lam w : Fin r → ℂ) {v : ℂ} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hden : ∀ j, 1 - 2 * v * (1 - 2 * lam j) + v ^ (2 : ℕ) ≠ 0) :
    packetCenteredChebyshevRational lam w v =
      (1 - v ^ (2 : ℕ)) / (4 * v) * packetKoebeResolvent lam w v := by
  classical
  rw [packetCenteredChebyshevRational, packetKoebeResolvent,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hlam0 : lam j = 0
  · simp [hlam0]
  simp only [if_neg hlam0]
  calc
    w j * lam j * (1 - v ^ (2 : ℕ)) /
        (1 - 2 * v * (1 - 2 * lam j) + v ^ (2 : ℕ)) =
      w j * (lam j * (1 - v ^ (2 : ℕ)) /
        (1 - 2 * v * (1 - 2 * lam j) + v ^ (2 : ℕ))) := by ring
    _ = w j * ((1 - v ^ (2 : ℕ)) / (4 * v) *
        (chebyshevTraceKoebeMap v /
          (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / lam j)))) := by
      rw [chebyshevKoebe_centeredNode hv0 hv1 hlam0 (hden j)]
    _ = (1 - v ^ (2 : ℕ)) / (4 * v) *
        (w j * (chebyshevTraceKoebeMap v /
          (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / lam j)))) := by ring

end RHTower
