# CCM first-clock Julia equilibrium coherent capacity — not new knowledge

- **ID:** `ccm-first-clock-julia-equilibrium-coherent-capacity`
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** BOOKKEEPING REPACKAGING / RETIRED AS FRONTIER CLAIM
- **RH used:** no
- **Computation used:** no

## Novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The inequality proved here is the standard anchored Gram
inequality (equivalently Cauchy--Schwarz/Schur complement) after substituting corpus-specific
names.  Its application to the first-clock source is exact, but exact renaming is not a new
mathematical mechanism and does not advance the RH dependency graph.  It must not be cited as a
frontier result or used to motivate another rank-one/kernel-capacity iteration.

## Historical collision context

This route was not selected because one new HTGeometry card looked compatible with RHTower.
Whole declaration census and collision audit first consumed all relevant existing endpoints:

1. `SoninSemilocalWeylGenerator` and `SoninSemilocalCyclicWeylDescent` already close scalar
   thermal differentiation through literal von Mangoldt flux; scalar Julia susceptibility was a
   collision, not novelty.
2. `GammaSewnMobiusJuliaSourceTransport` already supplies non-diagonal two-channel Julia source
   recovery and literal `log p` at the boundary.
3. `GammaSewnMobiusJuliaPrimeOrderAttenuation` identifies the diagonal arithmetic Julia weight but
   leaves all powers over one prime under one scalar gate.
4. `GammaConductorSchurCapacity`, `rectangular-semilocal-finite-part-curvature-rh`, and
   `semilocal-one-prime-harmonic-moment-defect` exclude an RH route assembled from independent
   one-prime positive innovations plus summable defects.
5. `JuliaDefectSpectralEquilibrium` paper-proves that the corrected Julia attenuation is a
   characteristic function and hence a full stationary Gram kernel, but had not acted on the
   reduced first-clock source.
6. `GammaSewnMobiusXiWardCofinalBoundaryLift` uses “Julia Gram” for a different complex Cauchy
   object. Its positive-semidefinite law is already equivalent to RH and is not silently assumed
   here.

Thus missing corpus-native test was forced: restore cross-prime covariance before applying the
first-clock signed functional.

## Exact theorem

Let

```text
R(0)=1,
R(y)=(4/3)(1-kappa(y))/y^2  (y!=0),
kappa(y)=cosh(y/2)^2/sqrt(cosh(2y)).
```

For an admitted finite prime packet `p_i`, write its literal collapsed tower as

```text
T_i(L)=G_i(L)-B_i(L),    G_i(L)>=0, B_i(L)>=0.
```

Here `G_i` is the stable tower plus positive small-square part and `B_i` is exactly the one-mode
outer residual plus negative small-square part. Put

```text
C_L = ccmFirstClockContinuousHalfWaveBudget(L,2*pi/L) > 0,
A_x(L) = C_L + sum_i R(x log p_i) (G_i(L)-B_i(L)),
B_x(L) = sum_i R(x log p_i) B_i(L),
E_B(x,L) = sum_i sum_j B_i(L) B_j(L)
             R(x log p_j-x log p_i).
```

Existing arithmetic Julia transport and the corrected zero branch give the exact source action

```text
gammaSewnMobiusJuliaPrimeAttenuation(x,p)=R(x log p),       x>0,
```

so `A_x` is the literal diagonally Julia-attenuated completed reduced first-clock packet. It is
not an analogy or a proxy carrier.

The paper-proved equilibrium-clock law says `R` is normalized, even, and positive definite. Add
the origin to the bad packet and use coefficients

```text
c_0=-B_x(L),  c_i=B_i(L).
```

Its Gram quadratic form is exactly

```text
E_B(x,L)-B_x(L)^2 >= 0.                                  (JCC1)
```

If `A_x(L)<0`, then the completed good correlation

```text
C_L+sum_i R(x log p_i)G_i(L)
```

is positive, so

```text
0 < -A_x(L) <= B_x(L).
```

Together with `(JCC1)`:

```text
A_x(L)^2 <= E_B(x,L).                                    (JCC2)
```

This is sharp at the normalized origin face. It converts every negative deformed first-clock
excursion into compulsory coherent outer-prime energy.

## Bookkeeping meaning and boundary

`(JCC2)` records, in the first-clock notation, that Julia attenuation values are origin-column
entries of a positive-definite kernel.  This is useful bookkeeping only.  It neither supplies a
new source mechanism nor narrows the load-bearing RH obstruction.

It does **not** prove sign of `A_x`, and `A_x` at positive `x` is a deformed source rather than the
published `x=0` endpoint. PSD bounds a correlation by energy; it does not orient that correlation.
No RH conclusion is claimed.

## Retirement rule

Do not pursue an operator-placement, rank-one, RKHS, Schur-complement, or independent-channel
follow-up from this card.  Any future use must enter a genuinely new load-bearing construction
obtained independently from the global corpus audit; this inequality alone provides no frontier
leverage.

## Lean status

Formal modules:

```text
formal/GaloisForLFunctions/HTGeometry/JuliaDefectSpectralEquilibrium.lean
formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaEquilibriumGram.lean
```

Unconditionally formalized:

- corrected Julia kernel is even and strictly positive;
- generic anchored Schur-capacity theorem for every normalized even real positive-definite
  kernel;
- literal cellwise `T_i=G_i-B_i` and nonnegativity of `G_i,B_i`;
- exact arithmetic attenuation/origin-kernel identity;
- exact continuous-plus-prime source action on every finite admitted packet;
- `(JCC1)` and `(JCC2)` from the named `JuliaDefectEquilibriumGramLaw` interface.

The Lean proofs contain no axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration. Full
unconditional instantiation of `(JCC1)`--`(JCC2)` awaits Lean closure of the already paper-proved
compound-Poisson/equilibrium-clock identity `(JSE11)`.

## Gates

- [x] whole-corpus and failed-route collision audit
- [x] dependency-closed paper proof
- [x] exact source action formalized
- [x] generic anchored capacity and conditional Julia specialization formalized
- [ ] `JuliaDefectEquilibriumGramLaw` proved in Lean from `(JSE11)`
- [x] novelty rejected: generic Gram/Schur consequence
- [x] frontier follow-up retired
- [ ] RH
