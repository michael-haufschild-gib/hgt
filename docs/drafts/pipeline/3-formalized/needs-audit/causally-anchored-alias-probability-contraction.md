# Causally anchored alias probability and cutoff localization

- **ID:** `causally-anchored-alias-probability-contraction`
- **Stage:** 3-formalized
- **Type:** `[FORMALIZED POSITIVE THEOREM] [NOVELTY UNVERIFIED] [FCRJ NOT CLOSED]`
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md`, `(PF10)`--`(PF16)`
- **Statement:** Complete complementary root aliases form an exact probability contraction around
  a causally anchored active denominator; the contraction has norm exactly one, local
  annihilation is exactly parity, and odd-gap survivors localize to the physical cutoff.

## Lean-discovered causal strengthening

The initial reduced-frequency conjecture imposed `(a,q)=1`.  Formalizing its character identity
showed that this assumption is unnecessary:

```text
S_(qd,h)(ad)=nu_h(d)S_(q,h)(a),
```

for arbitrary integer `a`.  In `(PF10)`, this means the first-crossing prime `p` can remain inside
the active modulus `q` even when `p|a`.  Fully reducing the fraction first would move `p` into the
complementary modulus and erase the causal color.  The nonprimitive form therefore supplies the
correct anchored regrouping, not merely a more general statement for its own sake.

The color `p` must still remain an outer label: the anchored denominator alone does not identify
which of its factors was the first crossing.  What Lean makes possible is retaining that labeled
factor rather than forcing it out by lowest-term reduction.

More exactly, write the modulus as `c*m`, where `c` is the protected causal anchor and `m` is its
squarefree coprime complement.  For any frequency `k`, set

```text
d=gcd(m,|k|),  r=m/d,  u=k/d.                          (AP0)
```

Then the formal maximal anchored normal form is

```text
S_(cm,h)(k)=nu_h(d)S_(cr,h)(u),
(r,|u|)=1.                                             (AP0')
```

Every complementary frequency factor is extracted, while common factors belonging to `c` remain.
The theorem handles negative and zero frequencies as well.

Lean also proves the normalized form

```text
S_(qd,h)(ad)/nu_h(qd)=S_(q,h)(a)/nu_h(q),              (AP0'')
```

and every normalized root response has norm at most one.  Thus an alias fibre consists of repeated
copies of one unit-disk response, scaled only by root counts.

## Exact local classification

For every prime `p`,

```text
nu_h(p)=1  if p|h,
nu_h(p)=2  if p does not divide h.                     (AP1)
```

Thus the local survival factor is

```text
1-nu_h(p)/p = (p-1)/p  if p|h,
                (p-2)/p  otherwise.                   (AP2)
```

It vanishes exactly when `p=2` and `2` does not divide `h`.  Consequently a finite prime survival
product vanishes exactly when its coordinate set contains `2` and the gap is odd.  There is no
odd-prime local annihilation.

## Alias probability law

For a finite coordinate set `S`, an active packet `T subset S`, and

```text
theta_n=nu_h(n)/n,
w_(S,h)(T)=product_(n in T)theta_n
            product_(n in S\T)(1-theta_n),             (AP3)
```

the formal theorem proves

```text
w_(S,h)(T)>=0,
sum_(T subset S)w_(S,h)(T)=1.                          (AP4)
```

Primality and squarefreeness are not needed for the normalization; nonzero coordinates suffice
for nonnegativity.  Therefore, for responses `R_T` in any real normed space,

```text
||sum_(T subset S) w_(S,h)(T) R_T||
 <= sup_(T subset S)||R_T||.                           (AP5)
```

The constant response attains equality, so the source-independent contraction norm is exactly
one.  Complementary alias multiplicity disappears, but no power of the aperture is gained.

## Exact parity cutoff localization

For a complementary squarefree packet `N` containing `2` and odd `h`, the complete anchored alias
family vanishes.  Splitting it at an arbitrary physical threshold `H` gives the formal identity

```text
sum_(d|N,qd<=H) mu(qd)/(qd) S_(qd,h)(ad)
 =-sum_(d|N,H<qd) mu(qd)/(qd) S_(qd,h)(ad).             (AP6)
```

Thus every surviving odd-gap contribution is a support-cutoff term.  This is a positive boundary
localization theorem, not an estimate for that boundary.

## Hostile audit and exact fit

- **Causal label:** reducing `a/q` before alias collapse can erase the first-crossing prime.  The
  arbitrary-`a` theorem permits an anchored denominator containing that prime and avoids this
  failure, provided the first-crossing color remains an outer label.
- **Physical support:** `(AP4)` uses a complete Boolean coordinate cube.  The moving condition
  `qd<=H_h` truncates that cube and replaces the Euler survival factor by an incomplete divisor
  remainder.  No pointwise Euler damping survives automatically.
- **Sharpness:** `(AP5)` has norm exactly one on abstract response packets.  Any aperture power
  must come from the signed primitive responses and their joined endpoint source.
- **Parity:** odd-gap completion vanishes, but the relevant even-gap packet has strictly positive
  local factors.  In a fixed `(PF10)` sector the unrestricted future primes are all greater than
  the first-crossing prime, so the prime `2` is not in that future packet; the parity zero cannot
  be imported into the sectorwise future contraction.  It does not close the primitive ridge.
- **RH status:** these are unconditional finite identities.  They neither assume nor prove RH.

The module belongs between `(PF11)` and the large-sieve wall `(PF16)`: join all aliases compatible
with a fixed causal anchor before estimating.  The surviving open core is the physically truncated
anchored primitive response with the `k=0` switch, still the signed interval-local `FCRJ` boundary.

## Formalization

File: `formal/GaloisForLFunctions/RHTower/ReducedFrequencyMobiusAliasCollapse.lean`.

Principal declarations:

- `quadraticCongruenceRootCountTotal_prime`
- `quadraticCongruencePrimeSurvivalFactor_eq_zero_iff`
- `quadraticCongruencePrimeFactorsSurvivalProduct_eq_zero_iff`
- `quadraticCongruenceAliasSurvivalWeights_sum_eq_one`
- `quadraticCongruenceAliasSurvivalWeight_nonneg`
- `quadraticCongruenceAliasSurvivalContraction`
- `norm_quadraticCongruenceNormalizedRootSum_le_one`
- `quadraticCongruenceNormalizedRootSum_mul_alias`
- `quadraticCongruenceRootSumTotal_causalAnchor`
- `quadraticCongruenceRootSumTotal_causalGCDReduction`
- `causalGCDReduction_complement_coprime`
- `quadraticCongruence_reducedFrequencyAliasCollapse_eq_zero_of_parity`
- `quadraticCongruence_oddGapAliasPhysicalCutoffBalance`

## Gates

- [x] 0 -> 1: anchored causal claim and cutoff failure mode isolated
- [x] 1 -> 2: finite proofs dependency-closed
- [x] 2 -> 3: owned-module narrow build passes; `#print axioms` for the probability,
  contraction, normalized-response, causal-gcd, parity, and cutoff-balance theorems reports only
  `propext`, `Classical.choice`, and `Quot.sound`
- [ ] priority audit against finite sieve/harmonic-analysis literature
- [ ] derive a source-specific bound for the truncated anchored primitive response
