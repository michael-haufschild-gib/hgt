# Route-P critical Pluecker complement-depletion audit

- **ID:** `P-G76`
- **Stage:** `5-failed`
- **Type:** failed source-identification conjecture / exact signed survivor
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-critical-information-schur-depletion.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalPluckerComplementDepletion.lean`

## Heavy-conjecture loop

### C4 — complement symmetrization supplies coherent missing depletion

For the six two-cell minors of a four-rate Gamma boundary packet, complementary-pair exchange is
the involution `[5,4,3,2,1,0]`. Averaging a normalized minor packet with its complement forces

```text
complementary Fisher mean = (1/2) total Fisher.
```

This algebraic statement is true. On the hostile cell `(2,0),(2,1),(3,0),(3,1)`, exact rational
source bounds give raw four-atom mass `<37/400`; therefore half the information-depleted mass is
`<37/800<29/625`. The receiver clears the P-G72/P-G73 local mass obstruction.

### C5 — physical Pluecker probability is already complement invariant

**False, retired unconditionally.** Take one literal prime-two source fibre at physical valuation
depths `0,1,2,3`, midpoint rates `(e+1/2)log 2`, and positive nonboundary aperture `(log 2)/4`.
The physical minors `{0,1}` and `{2,3}` have unequal raw weights. Their normalized probabilities
remain unequal, so the complement-symmetrized packet is not the physical source packet.

Thus the C4 half-factor is locally adequate only after inserting a new averaging operator. It is
not the missing source-derived Feshbach law.

### C6 — retain the discarded odd class instead of averaging it away

**True, unconditionally proved.** Define physical complement chirality

```text
chi_w(s)=w(s)-w(comp(s)).
```

Lean proves its exact laws

```text
chi_w(comp(s))=-chi_w(s),
sum_s chi_w(s)=0,
w = sym(w) + chi_w/2,
E_w[F_comp] = F_total/2 + (1/2) sum_s chi_w(s) F_comp(s).
```

The depth-test physical chirality is nonzero. However the complementary Fisher clock on a
one-prime fibre is constant, so its pairing with this nonzero chirality is exactly zero. Valuation
depth amplification can retain a signed horizontal class while prime-only Fisher scalarization
erases it completely.

## New universal principle

Complement symmetry is not a source law; complement **chirality** is the source carrier. The
scalar half-factor is the even quotient, and its precise missing correction is one signed
chirality--Fisher moment. Same-prime packetization cannot produce that correction because Fisher
clock depends on prime label, not valuation depth. Any viable pre-compression Schur law must couple
distinct prime labels in P-G75's source graph/Köthe topology while retaining the complement-odd
class.

This connects two previously separate obstructions:

- P-G74/P-G75: Hardy compression erases critical clock topology;
- P-G76: Fisher scalarization erases same-prime complement chirality.

Both are quotient failures. Required producer must act on cross-prime source graph before either
quotient.

## Lean realization

Headline declarations:

- `gammaSewnCriticalPlucker_symmetrize_eq_self_iff_complementInvariant`;
- `gammaSewnCriticalPlucker_complementChirality_complementIndex`;
- `gammaSewnCriticalPlucker_eq_symmetrize_add_half_chirality`;
- `gammaSewnCriticalPlucker_complementaryFisherMean_eq_half_add_chirality`;
- `gammaSewnCriticalPlucker_depthTest_probability_not_complementInvariant`;
- `gammaSewnCriticalPlucker_depthTest_chirality_ne_zero`;
- `gammaSewnCriticalPlucker_depthTest_chiralityFisherMoment_eq_zero`;
- `gammaSewnCriticalPlucker_depthTest_symProbability_ne_sourceProbability`.

## Positive survivor and next conjecture

Construct a cofinal cross-prime graph transport `T` on physical Pluecker packets and prove an exact
source law for

```text
sum_s chi_(T w)(s) F_comp(s).
```

The law must orient or annihilate this signed moment without replacing `w` by `sym(w)`, and must
retain every prime-power label, divisor copy, and both complement orientations. A zero law would
make the half-factor source-derived; a signed law could supply the missing negative central mass.

## Honest boundary

P-G76 does not construct the cross-prime transport, identify completed seam moments, or prove RH.
It retires complement averaging and all same-prime depth packetizations as source producers while
exposing the exact signed class they discard.
