# Source-horizontal Euler--Gamma cubic negative renormalized channel

- **ID:** `source-horizontal-euler-gamma-cubic-negative-renormalized-channel`
- **Stage:** 3 — formalized in Lean 4
- **Status:** `[LEAN-PROVED] [DEPENDENCY-CLOSED] [PRE-XI] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** Frankenstein Euler logarithm / reflected Hellinger / Gamma depth moment / Wold BV /
  primitive Route P budget

## Exact problem

Construct before Xi selection a negative channel which is simultaneously:

1. a literal source derivative, not a cutoff-dependent multiple of a convergent current;
2. non-summable with cubic prime-clock mass;
3. coefficient-faithful in prime and valuation depth, including the depth multiplicity;
4. canonically source-renormalized by another proved source current; and
5. strong enough to remove the positive `1/3` limit left by the canonical BV Krein split.

## Heavy-conjecture loop

### C1 — genus-one `det₂` supplies the cubic channel

The prime-log genus-one operator is Hilbert--Schmidt but not trace class. Its regularized
determinant therefore looks like a canonical source renormalization.

**Verdict: `[FALSIFIED]` for cubic Wold mass.** The third logarithmic coefficient is the trace of
the cube of a Hilbert--Schmidt operator. That cube is trace class. Hence its cubic coefficient is
summable and becomes zero after division by the divergent Wold prime-clock cube. The determinant
is a valid genus-one renormalization, but cannot supply the required non-summable cubic channel.

### C2 — logarithmically differentiated causal von Mangoldt current

The second logarithmic source derivative has coefficient

```text
Lambda(n) log(n)^2 / n,
```

whose partial mass is cubic. Endpoint subtraction makes the causal remainder summable because it
gains one inverse power of `n`.

**Verdict: `[BRIDGE]`, not frozen producer.** Cubic growth and causal renormalization are genuine,
but choosing the compensating sign or restoring the divided Gamma-jet factor after the fact does
not yet make that sign part of the source law.

### C3 — negative Euler-log third jet with Wold source counterterm

For a prime `p`, put

```text
G_p = (log p)^3 * sum_(k>=1) k^2 p^(-k),
W_p = woldCoeff(1,p) * (log p)^2.
```

Frozen claim:

> **[PAPER-PROVED] Source-horizontal Euler--Gamma cubic negative renormalization.** The finite Euler
> logarithm supplies the literal negative source current `-sum G_p`. Every valuation depth `k` is
> retained with coefficient `k^2`. The pointwise defect `D_p=G_p-W_p` is positive and summable.
> Consequently `-sum G_p + sum W_p = -sum D_p` converges without any cutoff-dependent scaling,
> while `sum G_p / log(p_N)^3 -> 1/3`. Adding the normalized negative Gamma channel to the
> canonical BV Krein split therefore gives limit zero and is eventually below every nonzero
> primitive Route-P source budget.

Public sentence: the divergent negative Euler third derivative and the divergent positive Wold
interior are two source presentations of the same cubic bulk; their coefficientwise mismatch is
finite, so the source itself supplies the counterterm.

## Why source naturality is literal

The channel is not obtained by multiplying a summable current by the terminal clock. Existing
source theorems give

```text
P_X'''(1) = - sum_(p<X) G_p,
12 G_p = cubicAnnulusPrimeCurrent(p),
cubicAnnulusPrimeCurrent(p)
  = 48 log(p) * woldGeometricActivation(p)
      * gammaSewnSynchronizedEulerHalfHeightSecondMoment(p).
```

Thus sign comes from Euler-log orientation, cubic order comes from the third source derivative,
and depth multiplicity `k^2` comes from the complete prime-power annulus. No Xi divisor or
post-selection scalar occurs.

## Hostile falsifiers

1. If `D_p` is not summable, Wold is not a valid additive source counterterm.
2. If `G_p/W_p` is constant, this is a duplicated presentation rather than a distinct channel.
3. If the ordered normalized Gamma mass does not tend to `1/3`, it cannot cancel the BV firewall.
4. If source budget can vanish for nonzero coefficient, convergence to zero does not imply eventual
   budget control.
5. The theorem does **not** prove that completed Xi-selected physical descent contains this channel
   as an independent Krein leg. That transport remains separate and may still fail.

## Dependency-closed paper proof

Write `q=1/p` and `L=log p`. For every ordinary prime, `0<q<=1/2` and `L>0`. Existing Euler
third-jet and annulus identities give

```text
G_p = L^3 q(1+q)/(1-q)^3
    = L^3 sum_(k>=1) k^2 q^k,

P_X'''(1) = -sum_(p<X) G_p.
```

The second equality retains every valuation depth and its exact multiplicity `k^2`. The sign is
the Euler-log third-derivative sign; it is not selected after taking a limit.

The depth-one Wold cubic atom is

```text
W_p = L^3 q(1-q)^3.
```

Therefore

```text
D_p := G_p-W_p
     = L^3 q * ((1+q)-(1-q)^6)/(1-q)^3.                 (1)
```

Since `0<1-q<1`, the numerator in `(1)` is strictly positive, so `D_p>0`; in particular the new
atom is not the old Wold atom. Bernoulli's inequality gives `(1-q)^6 >= 1-6q`, while
`(1-q)^3 >= 1/8`. Hence

```text
0 < D_p <= 56 L^3 q^2 = 56 (log p)^3/p^2.               (2)
```

The majorant in `(2)` is summable even over all positive integers. Thus `sum_p D_p<infinity`.
For ordered primes `p_0,...,p_N`, put

```text
G_N=sum_(j<=N) G_(p_j),
W_N=sum_(j<=N) W_(p_j),
D_N=sum_(j<=N) D_(p_j),
H_N=log p_N.
```

Coefficientwise identity gives `G_N=W_N+D_N`. The proved Wold moment theorem says
`W_N/H_N^3 -> 1/3`. Summability gives `D_N -> sum_p D_p`, while `H_N^3 -> infinity`, so
`D_N/H_N^3 -> 0`. Consequently

```text
G_N/H_N^3 -> 1/3.                                      (3)
```

Because the limit in `(3)` is positive and `H_N^3 -> infinity`, `G_N -> infinity`. Therefore the
positive atom sequence is not summable and the raw source current `-G_N -> -infinity`.

Renormalization is additive and source-intrinsic:

```text
(-G_N)+W_N = -D_N -> -sum_p D_p.                       (4)
```

No coefficient depends on `N`; no convergent current is multiplied by `H_N^3`. Equation `(4)` is
the requested source renormalization.

To exclude any ordered-clock artifact, Lean also extends all three coefficients by zero from the
prime subtype to the literal natural-number source and proves

```text
sum_(n<X) (-G_n + W_n) = -sum_(n<X) D_n -> -sum_n D_n.
```

The cutoff is the ordinary source cutoff `Finset.range X`; coefficients contain neither `X` nor an
ordered-prime index. The same formalization proves the raw natural atom is not summable and its
finite negative sum is exactly `P_X'''(1)`.

Finally let `K_N(c)` be the proved canonical BV Krein energy. The corpus gives

```text
K_N(c) -> (8/3)||c||^2.
```

Define the Euler--Gamma compensated energy using the already-forced four-orientation coefficient:

```text
K_N^Gamma(c)=K_N(c)-8||c||^2 G_N/H_N^3.
```

By `(3)`, `K_N^Gamma(c)->0`. For `c!=0`, the literal primitive budget is
`(8/3)||c||^2 B_P>0`, because both `||c||^2` and the proved primitive base budget `B_P` are
strictly positive. Hence eventually

```text
K_N^Gamma(c) < (8/3)||c||^2 B_P.                       (5)
```

This proves the frozen claim. It does not prove the separate physical descent asserting that the
completed Xi-selected residue contains the new pre-Xi channel as an independent Krein leg.

## Hostile proof audit

- The only infinite comparison is `(2)`, dominated by a standard convergent logarithmic
  `p`-series; no conditional rearrangement occurs.
- Cubic limit has coefficient exactly `1/3`; no fitted constant is inserted.
- Strict `D_p>0` kills duplicate-coefficient objection, while summability of `D_p` explains equal
  cubic asymptotics.
- Raw current is non-summable before normalization, killing forbidden amplified-summable-current
  interpretation.
- Eventual budget theorem uses proved strict positivity of literal primitive budget, not a guessed
  numerical lower bound.
- Remaining Xi landing is stated as an open transport obligation, not smuggled into this theorem.

## External boundary

Euler-product logarithmic derivatives, von Mangoldt logarithmic weights, Mertens/Abel asymptotics,
and regularized determinant counterterms are parent mathematics. Current primary-source searches
found dynamical Lefschetz/regularized-determinant trace formulae and standard explicit-formula
prime-power currents, but not this exact Euler-third-jet/Wold additive renormalization or its
primitive-budget use. This is `[NOVELTY UNVERIFIED]`, not a priority claim.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.SourceHorizontalEulerGammaCubicNegativeRenormalizedChannel`.

Capstone theorem:
`sourceHorizontalEulerGammaCubicNegativeRenormalizedChannel_producer`.

Key declarations additionally expose strict positive defect, the `56 (log p)^3/p^2` summable
majorant, exact prime-power `k^2` series, Euler/reflected-Hellinger third-jet identities, raw
non-summability, natural-cutoff renormalized convergence, compensated-energy convergence, and
eventual primitive-budget control. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Gates

- [x] internal Wold / Gamma / determinant / Fock / budget audit
- [x] bounded primary-literature collision audit
- [x] freeze exact C3 statement
- [x] prove positive summable defect
- [x] prove exact Euler-third-jet and depth-faithful presentations
- [x] prove cubic normalized limit and raw non-summability
- [x] prove source-renormalized finite limit
- [x] prove compensated BV budget limit and eventual bound
- [x] hostile proof audit
- [x] Stage 2 promotion
- [x] unconditional Lean formalization
- [x] natural-number source-cutoff strengthening
- [x] exact module `.olean` build and axiom audit
- [x] Stage 3 promotion
