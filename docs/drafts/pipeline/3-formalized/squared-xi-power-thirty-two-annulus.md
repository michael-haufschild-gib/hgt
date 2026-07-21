# Squared-Xi power-32 angular-annulus reduction

- **ID:** `squared-xi-power-thirty-two-annulus`
- **Stage:** 3-formalized
- **Type:** THEOREM / RH BACKWARD BRIDGE
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `squared-xi-low-dyadic-tail-reduction.md`

## Exact conjecture

For a Xi divisor copy `q`, a real shift `y > 1/4`, and

```text
u = (Re(q)-1/2)^2,
v = Im(q)^2,
A = v-u+y,
B = 2 (Re(q)-1/2) Im(q),
mu = (A-iB)^(-1),
```

prove:

1. `417 B^2 < A^2 -> 0 < Re(mu^32)`;
2. `Re(mu^32) <= 0 -> 1/20 < u < 1/4 and 85 < v < 417`;
3. using the already formalized order-19 theorem at the same shift,
   `Re(mu^32) <= 0 -> 147 B^2 < A^2 <= 417 B^2`.

At fixed shift `y=1`, emptiness of this exact angular annulus supplies dyadic rung `k=5`.

## Paper proof

From `417 B^2 < A^2`, positivity of `A`, and

```text
1,000,000 < 417 * 49^2 = 1,001,217,
```

one gets `|B/A| < 49/1000`.  The reciprocal `mu` has positive real part and
`tan(arg(mu))=B/A`, hence `|arg(mu)|<49/1000`.  Therefore

```text
|32 arg(mu)| < 32 * 49/1000 = 1.568 < pi/2,
```

so `Re(mu^32)>0`.

For an off-line copy, the source height theorem gives `v>85`, while the critical strip gives
`u<1/4` and `A>v`.  If `u<=1/20`, then

```text
417 B^2 = 1668 u v <= (417/5) v < 85 v < v^2 < A^2.
```

If `417<=v`, then `B^2=4uv<v`, so again `417 B^2<v^2<A^2`.  Thus failure of the `417` certificate
forces the stated compact corner.  Finally `xiOrderNineteenReciprocalPower_re_pos` plus its proved
sector reduction gives `147 B^2<A^2`; the failed `417` certificate supplies the upper side.

## Hostile audit

1. Coefficient `417` is strict and chosen to make the rational `49/1000` angular bound valid.
2. Power `32` is the actual first open dyadic rung; no exponent substitution occurs.
3. Annulus emptiness is not asserted here.  It is the next source theorem to prove.
4. No zero table or computation is used.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.XiSquaredSeamPowerThirtyTwoAnnulus`.
- Rational sector theorem: `orderThirtyTwoReciprocalPower_re_pos_of_sectorRatio`.
- Recovered unconditional order-19 sector: `xiOrderNineteenSectorRatio_unconditional`.
- Exact failure localization: `xiOrderThirtyTwoReciprocalPower_nonpos_mem_annulus`.
- Rung-five connector: `xiSquaredSeamDyadic_rung_five_pos_of_annulusEmpty`.
- New RH factorization:
  `xiSquaredSeamPowerThirtyTwoAnnulusEmpty_and_tailFromSix_iff_riemannHypothesis`.
- Direct `lake env lean`: passed.
- `#print axioms` for capstones: only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint: passed with proof debt `0`.
- Final targeted module build: passed.
- Umbrella import: `GaloisForLFunctions.RHTower`.

## Gates

- [x] Internal corpus audit
- [x] Complete paper proof
- [x] Hostile audit
- [x] Exact Lean theorem
- [x] Axiom/lint/module audit and Stage-3 promotion
- [ ] Source exclusion of the surviving angular annulus
- [ ] Full RH proof
