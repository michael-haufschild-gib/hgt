# The Wigner--Eisenstein cross energy has a positive dual floor

- **ID:** `theta-wigner-eisenstein-cross-energy-dual-floor`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE DUAL OF A NO-GO
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThetaWignerEisensteinCrossEnergy.lean`

## Statement

For a positive scalar symbol `p` and complex channels `z,w`,

```text
p normSq(z) + 2 Re(conj(z)w) + normSq(w)/p
  = normSq(pz+w)/p >= 0.
```

Therefore

```text
Re(conj(z)w)
  >= -(p normSq(z) + normSq(w)/p)/2.                    (1)
```

The Wigner--Eisenstein symbol is strictly positive at every real height and
dilation frequency, so `(1)` applies pointwise with

```text
p=p_b(tau)=(b^2+1/4-tau^2)^2+tau^2.
```

## Positive content of the obstruction

Bulk coercivity does not turn the Xi orientation current into a squared norm:
the current is a cross energy.  The positive theorem left by that failure is
more precise than a rejection.  A lower bound follows once two quantities are
controlled together:

```text
the p_b-weighted primal energy
  + the p_b^(-1)-weighted boundary/scattering energy.   (2)
```

Thus the obstruction identifies the missing constructive carrier: the dual
boundary channel in `(2)`.  Any Wigner--Eisenstein proof may use the positive
archimedean floor, but it must also establish an aperture-uniform bound for the
actual arithmetic boundary/scattering datum.  Coercivity alone supplies no
such bound.

## RH boundary

This theorem does not identify the channels in `(1)` with the logarithmically
sampled rectangular Weil family and does not bound the reciprocal-symbol
energy of the distinguished theta/Eisenstein source.  Either assertion would
be additional mathematics.  The current RH-facing open core remains a
source-defined, aperture-uniform lower bound for the rectangular family.

## Lean certificate

- `complexCrossEnergy_completeSquare`
- `complexCrossEnergy_lowerBound`
- `thetaWignerEisenstein_crossEnergy_lowerBound`

The focused module build passes.  The proof uses the already-formalized strict
positivity `thetaWignerEisensteinSymbol_pos` and elementary complex algebra.

