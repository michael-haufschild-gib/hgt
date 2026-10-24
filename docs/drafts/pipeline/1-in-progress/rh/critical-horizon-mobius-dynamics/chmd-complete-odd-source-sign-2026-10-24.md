# CHMD complete odd-source sign

- **ID:** chmd-complete-odd-source-sign-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The literal theta–Doob energy is nonnegative on every odd compact smooth source, with every prime-power edge and the complete polar subtraction retained.

## Goal

Unconditional Lean proof of RH through CHMD. New criteria, numerical improvements,
and further no-go results do not discharge this goal. No external search, novelty
audit, numerical experiment, or added mathematical premise is authorized.

## Verified source frontier

Read the CHMD section of `docs/reports/rh-current-frontier-map.md` and all CHMD
entries of `docs/reports/rh-killed-routes.md`; checked the relevant Lean sources.

- `CHMDDoobSourceGraph` uses mass `Theta(x) cosh(x/2) dx` and the full
  archimedean-plus-prime edge measure. Signed energy is edge norm squared minus
  mass norm squared.
- `CHMDPrimeChainSourceFactorization.doob_source_eq_chain_variances_sub_cosh`
  retains the negative cosh mass after exact nonnegative chain factorization.
- `CHMDOddHarmonicIdentityAndPolarDoobAbsorption` supplies a positive half-line
  profile `m_a`, a positive sinh pairing, and an absorbed archimedean kernel.
- `CHMDOddProfileArchAbsorptionAndPrimeChainBridge` retains the negative prime
  collar when converting to the secondary odd profile. The collar duality is
  exact; it supplies no complete-form sign.
- `CHMDNodalCrossPrimeShiftAndPrimitiveRayleighClosure` requires both a primitive
  absolute-graph Rayleigh bound and payment of the `oneL` defect. Its conclusion
  cannot be used with either premise omitted.
- `StationaryResolventMarkovPositivityAndNodalDefectProducer` proves positivity
  of the stationary resolvent, not the needed primitive half-Rayleigh bound.

## Exact target

For every real odd compact C2 function `v`, prove

```
phiDoobCoshMass (fun x => v x ^ 2)
  <= phiDoobArchJumpEnergy v
     + 2 * CHMDPrimeCuts.sameSide v
     + tsum (CHMDPrimeChainSource.chainIntegral v).
```

Regularity and oddness specify the test domain; the proposed theorem must not
assume RH, a spectral ceiling, a discrepancy bound, or a signed-energy premise.

## Active attack

Retain the direct and reflected prime contributions together in secondary
`m_a` coordinates. Test whether the exact odd theta source identity pays the
reflected collar through a joint quadratic identity, without estimating prime
atoms independently or throwing away the direct contribution. A proof must
cover sign-changing multipliers and arbitrary aperture.

The eigenstate alternative is to exploit the exact shifted-theta pairing law
on the actual weighted mass space. Small-shift admission is essential:
`1 < 2 * exp(-2 * |a|)`. Extending the pairing to all shifts, or applying an
unweighted Fourier uniqueness theorem to the mass-space eigenvector, is not
justified by the existing domain theorems.

## Direct/reflected calculation and unresolved inference

Write `m = m_a`, `l_n = log n`, `b_n = vonMangoldtAtom n`, and let `w` be even
and compactly supported. The actual secondary prime jump is

```
2 * sum_n b_n * integral_(x>0)
      m(x) m(x+l_n) (w(x)-w(x+l_n))^2
  - sum_n b_n * integral_(0<x<l_n)
      m(x) m(l_n-x) (w(x)-w(l_n-x))^2.
```

This follows from the existing full-line folding identity, not a sign
assertion. The second sum is the collar that must be paid. Midpoint symmetry
does not hold for a general even `w`: evenness gives `w(-x)=w(x)`, whereas
collar cancellation requires `w(l_n-x)=w(x)` for each relevant prime lag.

The genuine secondary ground-state strategy would pay this collar from the
direct prime term, the absorbed archimedean term, and
`S = 2 * integral_(x>0) m(x) sinh(x/2) w(x)^2`. No such joint inequality has
been proved here. A bound for each nonnegative piece separately cannot be
substituted for it.

Inspection of `convex_doob_chain_sinh_interpolation` gives a particularly
important accounting check. With `J` the primary full jump energy, `M` its
cosh mass, and `P = sourcePair (oddPolarVectorAt a ha) p`, its statement is

```
E = J + theta*S - (M + theta*P),     P = S.
```

Its proof rewrites the primary energy identity and the polar pairing, then
uses `ring`. Thus the displayed sinh terms cancel exactly. Even an estimate
`M <= theta*S` yields only `J <= E + theta*P`; `P` remains nonnegative and
uncontrolled. It cannot be dropped to conclude `E >= 0`. This is a reading
of the existing theorem's retained term, not a new no-go result or a claim
that the joint secondary strategy fails.

The primitive nodal alternative has the analogous unresolved payment. At
the desired half-Rayleigh ceiling, the current receiver requires

```
2 * inner ((absGraph q).fst) oneL ^ 2
  <= -4 * sourcePair (posGraph q) (negGraph q).
```

The proven strict negativity of the cross pairing supplies no comparison
with the magnitude on the left. Stationary-resolvent positivity also leaves
the primitive absolute-graph half-Rayleigh premise open.

## Gates

- [x] Exact source and open arithmetic sign identified.
- [ ] Dependency-closed proof of a significant source-sign advance.
- [ ] Lean formalization without added open inputs.
- [ ] Final leaf audit with `lake --old env lean`, transitive axiom inspection,
      and umbrella import.
- [ ] Complete unconditional RH theorem.

## Status

No dependency-closed source-sign proof was obtained. No significant CHMD
obstacle has been solved in this batch. No Lean module, umbrella import,
compiler audit, or new theorem is claimed. The next mathematical task is
the joint collar payment above, retaining all prime and polar terms; merely
reformalizing its identity would not meet the goal.

Corpus searches and direct source inspection supplied the evidence above;
search hits were not treated as kernel certificates. External novelty work
was excluded by the user, so no novelty claim is made. Existing worktree
changes belong to other work and remain untouched. Goal remains active.
