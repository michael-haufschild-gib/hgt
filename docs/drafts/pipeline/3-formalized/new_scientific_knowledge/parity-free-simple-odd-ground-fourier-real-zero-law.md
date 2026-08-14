# Parity-free simple odd-ground Fourier real-zero law

- **ID:** `parity-free-simple-odd-ground-fourier-real-zero-law`
- **Stage:** 3-formalized
- **Route:** O / CCM primary-literature parity
- **Type:** THEOREM
- **Scientific status:** `[LEAN-PROVED] [PAPER-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/CCMParityFreeOddGroundFourier.lean`
- **Paper parent:**
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/parity-free-simple-ground-fourier-real-zero-law.md`

## Exact advance

The finite simple-ground Fourier theorem no longer needs even parity.  For the odd block of a
finite CCM rank-two frequency commutator, let `Qminus` be the positive-semidefinite ground metric,
`Qplus` the positive-semidefinite opposite-parity metric, `B` the cross-frequency block, `eta` and
`beta` the boundary vectors, and `c` the normalized simple odd ground.  Assume only the exact block
commutator, radical line, and source-active cross-frequency condition.  No real-rootedness or
spectral conclusion occurs in the data.

Writing

~~~
delta = B* eta,
T = B* B,
b = <beta,c>,
A = T - |Tc><delta|,
~~~

Lean proves

~~~
b > 0,
Qminus A = A* Qminus,
Qminus A = B* Qplus B - b |delta><delta|,
Qminus A >= 0.
~~~

The last inequality is the new load-bearing step.  It follows from Cauchy--Schwarz in the
semidefinite `Qplus` metric and does not require `Qplus` to be positive definite.  Every zero of
the full characteristic polynomial of `A` is therefore real and nonnegative, including the
radical zero.  The exact rank-one determinant identity then shows that every non-pole zero of the
odd squared resolvent numerator is nonnegative.  Evaluating at `z^2` forces every non-pole Fourier
resolvent zero to satisfy `Im z = 0`.

## Lean endpoints

- `CCMParityFreeOddGroundData.betaGround_pos`
- `CCMParityFreeOddGroundData.qminus_mul_completion_eq`
- `CCMParityFreeOddGroundData.qminus_mul_completion_posSemidef`
- `CCMParityFreeOddGroundData.completion_charpoly_zero_im_eq_zero`
- `CCMParityFreeOddGroundData.completion_charpoly_zero_re_nonneg`
- `CCMParityFreeOddGroundData.squaredResolventNumerator_zero_nonnegative_real`
- `CCMParityFreeOddGroundData.oddFourierResolventNumerator_zero_im_eq_zero`

## Audit

- `lake env lean GaloisForLFunctions/RHTower/CCMParityFreeOddGroundFourier.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.CCMParityFreeOddGroundFourier`: pass.
- `#print axioms` on the three load-bearing endpoints: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or numerical computation.
- Leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; umbrella was not built.

## Exact boundary

This closes the finite odd algebraic theorem, not Route O.  It does not construct the literal
parity blocks of the published restricted-Weil matrix, prove that its selected floor is simple,
or prove finite-to-continuous ground convergence.  The infinite truncated-convolution theorem's
source approximation/Hurwitz step remains outside this Lean module.  Most importantly, real-zero
reality of either parity gives no comparison between the prolate leakage ground and every true
restricted-Weil near-ground direction.  Route O's RH-bearing open core remains source-derived
upper control `eta(a)=exp(o(a))`.
