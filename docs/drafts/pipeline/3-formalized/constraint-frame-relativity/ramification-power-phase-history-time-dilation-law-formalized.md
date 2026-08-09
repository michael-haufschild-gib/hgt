# Ramification-power phase/history time dilation — formalized

- **ID:** `cfr-ramification-power-phase-history-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `ramification-power-phase-history-time-dilation-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.PhaseHistoryDilation` | new |
| `GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity` | reused parent |
| `GaloisForLFunctions.HTGeometry.KroneckerWeylDensity` | reused parent (`kronecker_approx`) |

Wired into `GaloisForLFunctions.HTGeometry`.

## Reused, not rebuilt

The rational independence of the prime logarithms on a finite aperture is the existing
`GaloisForLFunctions.primeLogFiniteSlice_linearIndependent`, and Kronecker's approximation theorem
is the existing `GaloisForLFunctions.kronecker_approx`; the card's scope note explicitly asks that
these not be duplicated.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Theorem 2.1 — orbit invariance and lifted dilation, card `(PH.1)`–`(PH.8)`:

1. `primeClockVec`, `shellGenerator`, `shellFlow`, `shellLift` — the objects of `(PH.1)`–`(PH.4)`.
2. `shellGenerator_mul`, `shellFlow_mul`, `shellLift_mul` — the boxed triple `(PH.6)`:
   `D_{rm} = r D_m`, `U_{rm}(t) = U_m(rt)`, `h_{rm}(t) = r h_m(t)`.
3. `shellFlow_range_eq` — the boxed orbit invariance `(PH.7)`.
4. `shellFlow_div`, `shellLift_div` — the clock compensation `(PH.8)`.

Corollary 2.2 — fixed-clock representation separation:

5. `sum_shellGenerator_ne` — the generator traces differ, so the representations are not linearly
   conjugate.
6. `centeredVariance_mul` — the centred spectral variance scales by `r²`, so they are not
   projectively conjugate either.

Theorem 3.1 — dense recurrence and unbounded lift, card `(PH.9)`/`(PH.10)`:

7. `primeClockVec_linearIndependent`, `shellGenerator_linearIndependent` — rational independence of
   the shell frequencies.
8. `shellFlow_dense` — the orbit is dense in the aperture torus.
9. `exists_large_return` — arbitrarily large return times: for every tolerance and every horizon
   there is `t ≥ T` with all phases within the tolerance of one.  The proof is compactness of the
   phase torus plus the homomorphism property, so it needs no extra arithmetic input.
10. `norm_shellLift` — the exact lift energy `∑ h_m(t)_p² = t² m² ∑ λ_p²`, which diverges along the
    return times of item 9.

Theorem 4.1 — homogeneous cost dilation, card `(PH.11)`–`(PH.14)`:

11. `cost_dilation` — the boxed endpoint law `K_{rm}(t) = r^q K_m(t)`.
12. `action_dilation` — the boxed fixed-clock action law `A_{rm}(T) = r^q A_m(T)`.
13. `action_dilation_compensated` — the boxed reparametrised law `A_{rm}(T/r) = r^{q-1} A_m(T)`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/PhaseHistoryDilation.lean  # clean
#print axioms  ⇒  propext, Classical.choice, Quot.sound
```
