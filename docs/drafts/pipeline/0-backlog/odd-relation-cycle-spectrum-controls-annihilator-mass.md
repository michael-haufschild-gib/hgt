# Odd-relation cycle spectrum controls annihilator mass

- **Stage:** 0-backlog
- **Type:** CONJECTURE; uncounted
- **Obstacles:** B13, B112; simultaneous positive annihilation.
- **Statement:** For odd `q>=3`, ordinates with `sum gamma_j=0`, and joint evaluation accuracy `epsilon`, conjecture `cos(pi/q) H >= 1-epsilon`. Conjecture this is sharp over all such ordinate lists, at every real abscissa and every `epsilon` in `[0,1]`.
- **Novelty:** The proved odd-relation telescoping bound is not sharp. A cycle spectral certificate could give the optimal obstruction for arbitrary odd additive relations, extending the sharp first/fourth-harmonic law beyond that special pattern.

## Proposed mechanism

Cumulative monomial phases form a closed unit-valued cycle. Its adjacency quadratic form should have lower bound `-cos(pi/q)` times its squared norm. Integrating this certificate against positive coefficients would give the conjectured mass bound.

For sharpness, write `q=2r+1`, use `q-1` copies of `gamma` and one copy of `-(q-1)gamma`, with `gamma=2pi/(q log 2)`. Candidate annihilator: `1+a(X_beta^r+X_beta^(r+1))`, where `a=(1-epsilon)/(2cos(pi/q))` and `X_beta` is the existing scaled two-monomial.

## Proof gates

Prove the odd-cycle spectral bound, transfer it to cumulative phases, and verify the positive polynomial witness. No spectral statement or extremizer is assumed proved.

Corpus leads: `RHTower/FieldOneFiniteCyclicFourierParseval.lean`, declarations `fieldOneFiniteCyclicFourier_parseval` and `fieldOneFiniteCyclicFourier_orthogonality`; `ArithmeticPositiveDuality/SharpSparseHarmonicAnnihilation.lean` for the special fifth-root witness. Search hits require source inspection before use.
