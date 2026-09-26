import GaloisForLFunctions.RHTower.ChebyshevKoebeFiniteAtoms

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
  simpa only [packetCenteredChebyshevRational, packetKoebeResolvent,
    finiteChebyshevCenteredRational, finiteKoebeResolvent] using
    (finiteChebyshevCenteredRational_eq_koebe
      (Finset.univ : Finset (Fin r)) w lam hv0 hv1
      (fun j _ => hden j))

end RHTower
