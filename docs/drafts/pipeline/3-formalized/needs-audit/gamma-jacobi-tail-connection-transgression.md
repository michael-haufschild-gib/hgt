# Gamma--Jacobi tail/connection transgression

- **ID:** `gamma-jacobi-tail-connection-transgression`
- **Stage:** 3 — formalized; external novelty audit pending
- **Parents:** `SR-38`, `SR-41`, `SR-46`
- **Type:** source-specific head/tail boundary weld / projective source reconstruction
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [ADVANCE]`
  `[EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Collision boundary

Generic coherent states, Szegő kernels, geometric shift eigenvectors, and
Meixner--Pollaczek coherent-state constructions are classical.  They are not the claim.  Corpus
already contains a different prime-valuation Hardy shift in
`XiTransverseGammaValuationCoherence.lean`.  No corpus theorem joined that system, or any Szegő
tail, to the actual adaptive odd Gamma--Jacobi residual and the artanh successor connection.

The source-specific content below is the exact equality between:

1. first surviving coordinate of the existing `SR-38` residual;
2. derivative defect of the `SR-46` log head;
3. rank-one aperture loss of the singularly normalized infinite tail;
4. a projective coordinate that reconstructs the prime from every common surviving adjacent pair.

## Exact boundary readout

Write

```text
a_k(t)=(-1)^k c_(2k+1) phi(t) tanh(t)^(2k+1)
T_K'(t)=1-tanh(t)^(2K).
```

On `t>0`, define forced singular readout

```text
d_K(t)=(-1)^k a_K(t)/[c_(2K+1) phi(t) tanh(t)].
```

Direct cancellation gives

```text
d_K(t)=tanh(t)^(2K)=1-T_K'(t).                         (1)
```

At `K=gammaOddJacobiPrimeCapacity(p)`, coordinate `K` is exactly first nonzero coordinate of
zero-padded coherent `SR-38` residual.  Therefore Lean proves literal adaptive weld

```text
1-T_(K(p))'(log p)=ResidualBoundaryReadout(p).          (2)
```

This is stronger than saying head and tail are complementary: boundary value controlling failure
of finite head to be flat connection is carried by first actual tail coordinate.

## Singular Szegő tail and rank-one transgression

Apply same forced readout to every tail coordinate and form

```text
H_K(t,u)=sum_(j>=0) d_(K+j)(t)d_(K+j)(u).
```

Since `0<tanh(t),tanh(u)<1`, geometric summation gives exact kernel

```text
H_K(t,u)
  =[tanh(t)tanh(u)]^(2K)/[1-(tanh(t)tanh(u))^2].        (3)
```

Consecutive apertures obey

```text
H_K(t,u)-H_(K+1)(t,u)=d_K(t)d_K(u)
                    =[1-T_K'(t)][1-T_K'(u)].           (4)
```

Thus normalized `SR-38` tail and `SR-46` connection are not separate contractions glued by a
direct sum.  They are complementary corners of one nested kernel: connection defect is exact
rank-one boundary current of tail exhaustion.

## Cofinal projective faithfulness

For any surviving adjacent pair define

```text
r_K(t)=-c_(2K+1)a_(K+1)(t)/[c_(2K+3)a_K(t)].
```

Then

```text
r_K(t)=tanh(t)^2,                                       (5)
r_K(t)=r_K(u) iff t=u                 (t,u>0).           (6)
```

For primes and every common absolute index beyond both adaptive cutoffs,

```text
r_K(p)=((p^2-1)/(p^2+1))^2,                             (7)
r_K(p)=r_K(q) iff p=q.                                  (8)
```

Hence discarding arbitrary finite source-dependent heads does not lose prime label even
projectively.  Any common surviving adjacent `SR-38` pair reconstructs source exactly.

## Scientific change

`SR-46` left head current and residual tail as complementary coordinates without one boundary
law.  Equations `(2)` and `(4)` provide that law.  Equation `(8)` proves residual tail itself is a
faithful nonlinear source chart; joint object no longer needs extra prime labels or fitted cross
block.

This does **not** yet construct completed Euler multiplication or cyclic reader.  Next falsifier is
whether existing canonical Toeplitz countertrace can be represented on this nested Szegő tail so
its non-cyclicity is exactly rank-one boundary `(4)`.  A successful representation would give one
source-fixed singular reader; failure must classify which Euler covariance is impossible.

## External calibration

Meixner--Pollaczek coherent states and shift-generated associated polynomials occur in classical
and modern literature, including arXiv:1004.3589 and arXiv:1708.03358.  Those calibrate generic
coherent-state layer as known.  Targeted search found no von-Mangoldt successor connection whose
defect is first adaptive Gamma--Jacobi residual coordinate, nor projective prime reconstruction
`(8)`.  External expert audit remains necessary.

## Lean

Module:

```text
formal/GaloisForLFunctions/RHTower/GammaJacobiTailConnectionTransgression.lean
```

Capstones:

- `gammaOddJacobiLogHead_connection_defect_eq_tailBoundary`;
- `gammaOddJacobiPrime_logHead_connection_defect_eq_residualBoundary`;
- `gammaOddJacobiPrimeResidualProjectiveNode_eq_iff`;
- `gammaOddJacobiHardyTailKernel_eq`;
- `gammaOddJacobiHardyTailKernel_sub_succ`.

Direct command passed:

```text
lake env lean GaloisForLFunctions/RHTower/GammaJacobiTailConnectionTransgression.lean
```

Audit record (2026-08-01):

- `lake build GaloisForLFunctions.RHTower.GammaJacobiTailConnectionTransgression` passed (`9052`
  jobs, exit `0`);
- all eleven theorem declarations have only `[propext, Classical.choice, Quot.sound]` under
  `#print axioms`;
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- module is imported by `formal/GaloisForLFunctions/RHTower.lean`;
- repository lint reaches all RHTower modules and remains red only because concurrently added
  `HTGeometry.RadicalBaseChangeFromRoots` is absent from HTGeometry umbrella.

## Gates

- [x] whole-corpus collision audit
- [x] generic Hardy/Meixner--Pollaczek layer demoted as known
- [x] paper proof `(1)`--`(8)`
- [x] direct unconditional Lean proof
- [x] umbrella wiring
- [x] capstone axiom audit
- [x] forbidden-declaration lint
- [x] final narrow module build
- [ ] repository-wide lint (one unrelated HTGeometry umbrella failure)
- [ ] external expert novelty audit
- [ ] completed Euler cyclic-reader representation
- [ ] fibre orientation / RH
