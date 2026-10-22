import GaloisForLFunctions.RHTower.ChebyshevKoebeFiniteAtoms

/-!
# Koebe resolvent form for finite Chebyshev packets indexed by `Fin r`

Restates the finite Chebyshev-to-Koebe identity for a packet of `r` nodes `λ_j` with weights
`w_j`: the centered Chebyshev rational `∑ w_j λ_j (1 - v²)/(1 - 2v(1 - 2λ_j) + v²)` equals
`(1 - v²)/(4v)` times the Koebe resolvent `∑_{λ_j ≠ 0} w_j K(v)/(K(v) + (27/4)/λ_j)`.

## Main results

- `packetCenteredChebyshevRational_eq_koebe`: the identity for `v ≠ 0, 1` with all Chebyshev
  denominators nonzero.

## Hypotheses

Unconditional; the premises only exclude vanishing denominators.
-/

namespace RHTower

/-- The centered Chebyshev rational function of a packet: `∑_j w_j λ_j (1 - v²)/(1 - 2v(1 - 2λ_j) + v²)`. -/
noncomputable def packetCenteredChebyshevRational {r : ℕ}
    (lam w : Fin r → ℂ) (v : ℂ) : ℂ :=
  ∑ j : Fin r,
    w j * lam j * (1 - v ^ (2 : ℕ)) /
      (1 - 2 * v * (1 - 2 * lam j) + v ^ (2 : ℕ))

/-- The Koebe resolvent of a packet: `∑_{λ_j ≠ 0} w_j K(v)/(K(v) + (27/4)/λ_j)`. -/
noncomputable def packetKoebeResolvent {r : ℕ}
    (lam w : Fin r → ℂ) (v : ℂ) : ℂ :=
  ∑ j : Fin r,
    if lam j = 0 then 0 else
      w j * (chebyshevTraceKoebeMap v /
        (chebyshevTraceKoebeMap v - (-(27 / 4 : ℂ) / lam j)))

/-- For `v ≠ 0, 1` with every Chebyshev denominator nonzero, the packet Chebyshev rational equals
`(1 - v²)/(4v)` times the packet Koebe resolvent. -/
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
