# Möbius Schur depth differences are the summable valuation marking

- **ID:** `xi-mobius-schur-valuation-marking`
- **Stage:** 3-formalized, needs external novelty audit
- **Type:** THEOREM PACKAGE, `[SOURCE BRIDGE] [POSITIVE NO-GO SALVAGE]`
- **Scientific status:** `[CANDIDATE NEW] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiMobiusSchurValuationIntertwiner.lean`
- **Parents:** `MobiusFiniteSchurTransfer`, `XiTransverseValuationSzegoMetric`,
  `XiTransverseGammaValuationCoherence`, and the finite-fusion valuation successor law

## Exact statement

Put `q_p=p^{-1}` and sample the actual local Möbius--Bernoulli Schur factor at nonnegative
integer depth:

```text
B_p(e)=(1-q_p^(e+1))/(1+q_p).
```

This is not an auxiliary sequence: as a complex number it is exactly

```text
bernoulliSignedSchurFactor(primeSchurWeight(1,p),log p,e).
```

Its forward difference is

```text
Delta B_p(e)
 =B_p(e+1)-B_p(e)
 =q_p^(e+1)(1-q_p)/(1+q_p)
 =[sqrt(q_p)/(1+q_p)] H_p(e),
```

where

```text
H_p(e)=sqrt(q_p)(1-q_p)q_p^e
```

is the half-shifted valuation coordinate selected by the Gamma Schur completion.  Thus the
valuation-depth marking is already the discrete depth derivative of the genuine local Möbius
Schur contraction.

Moreover the diagonal damping is not an ad hoc weight.  The dyadic squarefree source already has
local parity Fisher variance

```text
Var_parity(p)=q_p/(1+q_p)^2,
```

and therefore

```text
[sqrt(q_p)/(1+q_p)]^2=Var_parity(p).
```

The summable frame is exactly the local-Fisher-damped Gamma--valuation frame; inverse recovery is
primewise Fisher whitening.

The completed difference Gram is

```text
K_M(p,r)
 =sum_(e>=0) Delta B_p(e) Delta B_r(e)
 =q_p q_r(1-q_p)(1-q_r)
   /[(1+q_p)(1+q_r)(1-q_p q_r)].
```

Its diagonal is

```text
K_M(p,p)=q_p^2(1-q_p)/(1+q_p)^3 <= q_p^2.
```

Consequently `sum_p K_M(p,p)<infinity`: unlike the undamped Gamma-vacuum coordinates, the
actual all-prime Möbius difference frame is Hilbert-summable without a cutoff.  Diagonal damping
cancels under unit normalization, so its normalized defect is still exactly

```text
1-Corr_M(p,r)^2=((q_p-q_r)/(1-q_p q_r))^2.
```

For every injective packet of `N` primes, the first `N` source differences form a weighted
Vandermonde matrix with nonzero determinant.  The all-prime summable frame therefore retains the
finite source marking required by the HT graph-saturation obstruction.

## Exact Gamma relation and obstruction

Define the recovery gauge

```text
A_p=(1+q_p)/sqrt(q_p).
```

Then

```text
A_p Delta B_p(e)=H_p(e)
```

and, at depth zero,

```text
R_p u_p=-(3 sqrt(2)/4) A_p Delta B_p(0).
```

This identifies the corrected Gamma conductor cross-coordinate with the first discrete depth
derivative of the local Möbius characteristic multiplier.

The inverse dressing is not bounded:

```text
p <= A_p^2,
```

and hence `A_p^2` exceeds every real bound along the primes.  Therefore finite recovery and
finite Vandermonde invertibility do **not** supply the missing bounded source-to-Xi intertwiner.
The positive survivor is the globally summable damped source RKHS with the same normalized
aperture geometry; the remaining RH-bearing map must be bounded in that damped geometry rather
than recover the Gamma frame channel by channel.

## Relation to hypertranscendence geometry

The finite-fusion law advances valuation depth, while the Gamma Schur complement removes depth
zero and leaves the shifted tail.  The identity above adds the missing source selection:
valuation translation is the forward discrete derivative of the actual Möbius Schur transfer.
This is precisely the kind of marking that must be retained before graph closure in the
singular-maximal HT Toeplitz-weld saturation no-go.

## Remaining RH core

Construct a source-defined nonexpansive map from the globally summable marked Möbius difference
RKHS to the physical Xi boundary graph/core.  It must preserve the valuation successor action
and control the four-unit Pick defect without applying the unbounded diagonal recovery `A_p`.

## Formal verification

- Direct module check: passed.
- Narrow object build: passed.
- Principal theorem axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- RHTower umbrella import: wired; no broad umbrella build was run.

## Gates

- [x] exact local Schur sample identified
- [x] damping square identified with the actual local squarefree-parity Fisher variance
- [x] forward difference identified with the damped half-shifted valuation coordinate
- [x] completed source Gram and diagonal `O(p^-2)` law proved on paper
- [x] normalized pseudohyperbolic aperture defect proved on paper
- [x] finite source-difference Vandermonde marking proved on paper
- [x] exact Gamma vacuum relation proved on paper
- [x] unbounded inverse-recovery obstruction proved on paper
- [x] targeted Lean compilation
- [x] narrow object build
- [x] axiom audit
- [ ] external novelty audit
- [ ] bounded marked source-to-Xi graph intertwiner
- [ ] four-unit Pick estimate
- [ ] RH
