import GaloisForLFunctions.HTGeometry.ChebyshevFormalGenerating
import GaloisForLFunctions.HTGeometry.ChebyshevSpectralPacketTrace

/-!
# Generating series of Chebyshev traces of a spectral packet

A finite complex spectral packet is given by nodes `λ_j` and weights `w_j`. Its Chebyshev trace sequence
`n ↦ Σ_j w_j λ_j T_n(1 - 2 λ_j)` is packaged as a formal power series, and this series is identified with
the weighted sum of the Chebyshev node series at the shifted nodes `1 - 2 λ_j`. Combined with the node
generating identity, this exhibits the packet series as a rational function with denominators
`1 - 2(1 - 2λ_j) X + X^2`.

## Main results

- `packetChebyshevSeries_eq_nodes`: the packet series equals `Σ_j w_j λ_j · Σ_n T_n(1 - 2 λ_j) X^n`.
- `packetChebyshevSeries_centered`: `2 · (packet series) - Σ_j w_j λ_j` equals
  `Σ_j w_j λ_j (2 Σ_n T_n(1 - 2 λ_j) X^n - 1)`.

## Hypotheses

Unconditional identities of formal power series for arbitrary complex nodes and weights.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The formal power series whose `n`-th coefficient is the Chebyshev trace of the packet `(λ, w)`. -/
noncomputable def packetChebyshevSeries {r : ℕ} (lam w : Fin r → ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk (packetChebyshevTrace lam w)

/-- The packet Chebyshev series is the weighted node sum `Σ_j w_j λ_j Σ_n T_n(1 - 2 λ_j) X^n`. -/
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

/-- Centered packet series: `2 · (packet series) - Σ_j w_j λ_j = Σ_j w_j λ_j (2 Σ_n T_n(1 - 2 λ_j) X^n - 1)`. -/
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
