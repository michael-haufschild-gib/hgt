# CCM self-polarized complex Dirac shear

- **ID:** `ccm-self-polarized-complex-dirac-shear`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** complex Dirac two-shear plane × source-selected adaptive shear × Julia orientation-preserving plane lift × quantum complex-Gram energy
- **Statement:** The actual matched complex phase symbol canonically selects a Hermitian shear whose nodal form is its squared norm and whose Dirac determinant has one strict global sign away from spectral center.

## Goal

Turn the nowhere-zero two-shear crossing covector into a scalar determinant without choosing a
fragile fixed projection and without dividing by its norm. This must remove every off-center
determinant crossing at each actual prime-power wall and preserve labels under finite packets.

## Gates

- [x] 0 → 1  in-progress: source-pure conjecture extracted from Lean-proved C2 identities and adjacent corpus search
- [ ] 1 → 2  fully-proven: complete proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, direct check, exact leaf build, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper

## Conjecture C3

For the full matched symbol `Z=Z_n(x)`, let the source choose its own shear direction

```text
B_Z = Re(Z) B_re + Im(Z) B_im.
```

This is Hermitian and division-free. On the canonical gauge-dressed nodal vector `v`,

```text
v* B_Z v = 2 gauge(n)^2 normSq(Z).
```

For the one-parameter adaptive Dirac family

```text
A_n(x,t) = H(Z_n(x)) + t B_{Z_n(x)},
```

the exact determinant should be

```text
det A_n(x,t) = -2 t normSq(Z_n(x)).
```

Consequently, for every actual prime-power atom and `t>0`, the determinant is strictly negative
exactly when `x≠0`, and equals zero exactly when `x=0`. A nonempty finite label-preserving sum of
adaptive determinant responses inherits the same global sign and unique-zero law.

## Corpus synthesis

- `CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracTwoShear`: exact two-coordinate determinant plane and off-center symbol nonvanishing.
- `GammaSewnMobiusJuliaSourceTransport`: scalar compression must be completed by an orientation-preserving real plane lift; one extra channel is minimal.
- `QuantumGeometricTensorGram`: complex Gram energy, not Berry curvature alone, is the strict two-channel invariant.
- `InvolutiveProjectiveWedgeTransportLaw`: moving frames add a connection term; pair-invariant invertible frames preserve selection loci.
- shifted-Hankel adaptive-source modules: source-selected bilinear shears are genuine connection observables, not arbitrary test polarizations.

C3 applies these adjacent mechanisms to the actual matched CCM symbol: its own oriented plane
coordinate supplies the adaptive covector, while the resulting scalar is the positive complex
Gram/norm-square invariant.

## Kill tests

1. Kill if the adaptive matrix cannot be proved Hermitian without normalization.
2. Kill if its nodal form is not exactly the C2 joint energy up to the gauge factor.
3. Kill if the determinant retains an uncontrolled real or imaginary projection.
4. Kill any claim that this alone identifies the adaptive determinant with the published Weil/Xi receiver.

## Log

- 2026-08-21 — conjectured after broad corpus search across Julia lifts, quantum metric–Berry gaps, involutive projective wedge transport, adaptive Hankel shears, and Plücker covariant connections.
