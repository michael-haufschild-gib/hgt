# Causally anchored future-alias regrouping

- **ID:** `causally-anchored-future-alias-regrouping`
- **Stage:** 3-formalized / needs-audit
- **Type:** `[PAPER-PROVED] [FORMALIZED] [NOVELTY UNVERIFIED]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF10)`--`(PF16)`
- **Statement:** In a fixed first-crossing color sector, all unrestricted future frequency aliases
  collapse exactly to a sharp probability contraction on causally anchored responses.

## Exact theorem

Let `c,N>=1`, with `N` squarefree and `(c,N)=1`.  For the reducible root count and root sum

```text
nu_h(n)=#{r mod n:n|r(r+h)},
S_(n,h)(k)=sum_(r(r+h)=0 mod n)e(k r/n),
```

and a finitely supported frequency weight `F`, define

```text
T_(c,N,h)(F)
 =sum_(m|N)mu(m)/(c m)
    sum_(k!=0)F(k/(c m))S_(c m,h)(k).                  (R1)
```

Put

```text
V_R(h)=product_(ell|R)(1-nu_h(ell)/ell).               (R2)
```

Then

```text
T_(c,N,h)(F)
 =sum_(r|N)mu(r)/(c r)V_(N/r)(h)
    sum_(u!=0,(u,r)=1)F(u/(c r))S_(c r,h)(u).          (R3)
```

The frequency `u` is required to be coprime only to the future remainder `r`, not to the protected
causal anchor `c`.

## Dependency-closed proof

For every pair `(m,k)` on the left of `(R3)`, define

```text
d=gcd(m,|k|),  r=m/d,  u=k/d.                          (R4)
```

Because `m` is squarefree,

```text
m=r d,  k=u d,  (r,d)=1,  (u,r)=1.                    (R5)
```

Since `(c,N)=1`, also `(c r,d)=1`.  The causally anchored root-sum theorem gives

```text
S_(c r d,h)(u d)=nu_h(d)S_(c r,h)(u).                 (R6)
```

Conversely, for `r|N`, `(u,r)=1`, and `d|N/r`, equations `(R4)`--`(R5)` recover the unique pair
`(m,k)=(r d,u d)`.  This is a bijection.  Squarefreeness gives
`mu(r d)=mu(r)mu(d)`, and summing the `d` fibre yields

```text
sum_(d|N/r)mu(d)nu_h(d)/d=V_(N/r)(h),                 (R7)
```

which proves `(R3)`.

## Sharp contraction corollary

Set

```text
w_(N,h)(r)=nu_h(r)/r V_(N/r)(h),

B_(c,r,h)(F)=1/(nu_h(c)nu_h(r))
  sum_(u!=0,(u,r)=1)F(u/(c r))S_(c r,h)(u).            (R8)
```

The Boolean probability law gives

```text
w_(N,h)(r)>=0,
sum_(r|N)w_(N,h)(r)=1.                                 (R9)
```

Root-count multiplicativity turns `(R3)` into

```text
T_(c,N,h)(F)
 =nu_h(c)/c sum_(r|N)mu(r)w_(N,h)(r)B_(c,r,h)(F),

|T_(c,N,h)(F)|
 <=nu_h(c)/c sup_(r|N)|B_(c,r,h)(F)|.                 (R10)
```

The source-independent norm is exactly `nu_h(c)/c`: the abstract choice `B_r=mu(r)` attains
equality.

The formal finite theory additionally proves that normalized root responses lie in the unit disk
and are exactly invariant under complementary alias insertion.  Hence the repetition eliminated
by `(R3)` is literal normalized-response duplication, not merely a comparable upper bound.

## Hostile audit and PF10 fit

- The first-crossing prime must remain an outer color.  The anchored denominator `c r` does not by
  itself identify which factor of `c` crossed first.
- Full lowest-term reduction is a different normal form and can remove the first-crossing prime.
  Equation `(R4)` extracts only future-complement factors.
- In `(PF10)`, fix the first-crossing prime and earlier-shell divisor in `c`; take `N` to be the
  unrestricted future-prime packet.  Then `(R3)` collapses exactly the redundant future aliases.
- The physical condition `c r d<=H_h` truncates the `d` fibre.  Its coefficient is a partial
  divisor sum, not the Euler product `(R7)`, and the zero-mode law changes at the same threshold.
- The future packet in a fixed `(PF10)` color contains only primes greater than the crossing prime,
  hence never supplies the parity prime `2`; odd-gap Euler annihilation is not a sectorwise gain.
- `(R10)` is sharp and supplies no `M^(-1)` aperture power.  The truncated anchored response and
  its signed joining remain `FCRJ`-strength.

## Gates

- [x] 0 -> 1: fixed-color theorem and counterexamples to uncolored reduction isolated
- [x] 1 -> 2: bijection `(R4)`--`(R7)` and contraction `(R8)`--`(R10)` dependency-closed
- [x] Lean finite core: `quadraticCongruenceRootSumTotal_causalGCDReduction`,
  `causalGCDReduction_complement_coprime`, and alias probability/contraction declarations
- [x] 2 -> 3: formalize the finite-support pair reindexing `(R3)` —
      `formal/GaloisForLFunctions/RHTower/CausallyAnchoredFutureAliasRegrouping.lean`
- [ ] priority audit against finite sieve and harmonic-analysis literature

## Lean status

`[FORMALIZED]` `(R1)`--`(R7)` are unconditional in
`formal/GaloisForLFunctions/RHTower/CausallyAnchoredFutureAliasRegrouping.lean`, namespace
`RHTower`, importing only `RHTower.ReducedFrequencyMobiusAliasCollapse`.  Foreground build clean
with zero warnings; `/tmp` `#print axioms` on all ten declarations reports only `propext`,
`Classical.choice`, `Quot.sound` (`causalPair_gcd` and `causalPair_injOn` need only `propext`,
`Quot.sound`).  No `sorry`, `axiom`, `opaque`, or `unsafe`.

The unrestricted frequency sum is modelled with `∑ᶠ` over all nonzero `k : ℤ` against a frequency
weight `F : ℚ → ℂ` of finite support — the card's "finitely supported `F`".  This is load-bearing
rather than cosmetic: the hostile audit's physical truncation `c r d <= H_h` is exactly the failure
of the `d` fibre to be complete, and a `Finset`-truncated frequency range would produce a partial
divisor sum instead of the Euler product `(R7)`.

- **The bijection `(R4)`--`(R5)`.** `causalPairSet m` is the set of pairs `(d, u)` with `d ∣ m`,
  `u ≠ 0`, and `u` coprime to the future remainder `m / d`.  `causalPair_gcd` proves the map
  `(d, u) ↦ u * d` remembers `d` as `gcd (m, |u d|)`, hence `causalPair_injOn`; `causalPair_image`
  proves the map is onto the nonzero frequencies for squarefree `m`, using the existing
  `causalGCDReduction_complement_coprime` for the coprimality half.  Together these are the card's
  bijection, isolated as reusable arithmetic with no summation attached.
- **Fibre regrouping.** `finsum_nonzero_eq_finsum_causalPairSet` is the reindexing from the
  bijection alone (no finiteness); `finsum_nonzero_eq_sum_divisors_finsum` splits an unrestricted
  finitely supported frequency sum into the complementary divisor sum of reduced-frequency sums.
- **`(R6)`** is the existing `quadraticCongruenceRootSumTotal_causalAnchor`, applied with
  `m = r * d`; the anchor `c` is never reduced.
- **`(R7)`** is the existing `quadraticCongruenceRootDensity_squarefree_euler`.
- **`(R3)`** is `causallyAnchoredFutureAliasRegrouping`, the full regrouping identity, including
  the frequency invariance `k / (c m) = u / (c r)` that makes the reduction weight-preserving.
- `sum_divisors_sum_divisors_reindex` is the supporting divisor-pair reindexing
  `(m, d) ↦ (m / d, d)`.

Two pieces of infrastructure absent from mathlib were built here rather than worked around:
`finsum_mem_finset_biUnion_of_support_finite` (mathlib's `finsum_mem_iUnion` requires each piece of
the family to be finite, while the frequency fibres are infinite and only *meet the support*
finitely) and `mul_finsum_cond` (pulling a constant through a conditional `∑ᶠ`).

Scope note: the Lean gate on this card covers `(R1)`--`(R7)`.  The sharp contraction corollary
`(R8)`--`(R10)` is *not* formalized here.  The corpus carries the generic Boolean statement
(`quadraticCongruenceAliasSurvivalWeights_sum_eq_one`,
`quadraticCongruenceAliasSurvivalContraction`), but not the divisor-indexed weight
`w_(N,h)(r) = nu_h(r)/r V_(N/r)(h)` or the sharp norm `nu_h(c)/c` of `(R10)`.  That remains
paper-level.

## Next generative move

`causalPairSet` is now an object rather than a proof step, and it has structure the card never
uses: the bijection is defined for *any* modulus, but `causalPair_image` needs squarefreeness only
to make the reduction land back in the same family.  `[CONJECTURE]` For non-squarefree `m` the same
map is still injective and its image is the set of nonzero `k` whose gcd with `m` is *unitary* (a
divisor `d ∣ m` with `gcd (d, m/d) = 1`), so the failure of `(R3)` off squarefree moduli is
measured exactly by the non-unitary divisors — the same place the generalized-prime equal-norm
bursts of the hostile audit break the bijection.  Building `causalPair_image` in that generality
would turn the audit's fourth bullet from a counterexample class into a computed defect, and is the
natural next object on top of this file.
