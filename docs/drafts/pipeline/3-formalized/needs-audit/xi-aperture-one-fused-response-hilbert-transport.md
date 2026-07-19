# Xi aperture-one fused response Hilbert transport

- **ID:** `xi-aperture-one-fused-response-hilbert-transport`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (Lean) / raywise source-to-response Hilbert transport
- **Source:** `XiMobiusContinuousApertureSzegoMetric.lean`,
  `XiAperturePoissonValuationClockShuttle.lean`,
  `XiMobiusSchurRationalHurwitzLorentzAperture.lean`, and *Finite Fusion Forces Infinite
  Hypertranscendence*
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE]`
  `[LEAN-PROVED] [EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Statement:** At the minimal positive integral aperture, the complete valuation-fused Poisson
  response energy is pointwise bounded by the actual all-valuation Szego source metric with sharp
  squared gain `27`; hence the fused response is an all-prime Hilbert vector.

## Goal

Test whether the true incoming aperture Hilbert metric can control the actual valuation-fused
Poisson response, rather than merely placing source columns in an abstract RKHS.  The unit aperture
is the minimal positive integral source aperture and therefore the first possible uniform transport
gate for the actual shift tower.

## Paper proof `[PROVED HERE]`

At a prime `p`, put `q=p^-1`.  The complete valuation fusion theorem gives

```text
F_1(p)=sum_(e>=0) exp(-(e+1) log p)=q/(1-q).            (HT1)
```

The diagonal of the actual continuous Möbius--Szego source metric is

```text
G_1(p)=(q/(1+q))^2 (1-q)/(1+q).                        (HT2)
```

Therefore the exact raywise squared gain is

```text
F_1(p)^2/G_1(p)=((1+q)/(1-q))^3.                       (HT3)
```

Every prime satisfies `0<q<=1/2`, so the right side is at most `3^3=27`.  Equality holds at
`p=2`; the constant is sharp.  Thus

```text
F_1(p)^2 <= 27 G_1(p)                                  (HT4)
```

for every prime.  Since `sum_p G_1(p)<infinity` is already Lean-proved by the true-aperture metric,
comparison gives

```text
sum_p F_1(p)^2 < infinity.                             (HT5)
```

## What this changes

The valuation-fused response is not merely sign-correct.  On the first actual integral aperture
ray it is quantitatively controlled by the source-selected Hilbert geometry with an exact sharp
constant.  This removes an unboundedness objection on that ray and turns the next gap into a
genuine operator/intertwining question: extend the raywise coefficient identity through the
completed prime--Gamma and functional-equation joins without losing the negative response channel.

## Hostile audit

1. `(HT4)` is raywise.  It does not construct a bounded operator on the whole aperture completion.
2. The all-prime Hilbert membership `(HT5)` is not an RH criterion and contains no zero selection.
3. The algebra and the constant `27` are elementary.  Candidate novelty is restricted to the exact
   splice between the actual HT source metric and the valuation-fused Xi/Poisson current.
4. The live corpus contains both ingredients and related `4/27` Möbius--Lorentz comparisons, but a
   targeted search found no existing theorem `(HT3)`--`(HT5)` for this fused response.
5. External specialist novelty review remains open.

## No-go closure

- **Exact killing theorem/mechanism:** Hilbert membership in the canonical Möbius source metric is
  unconditional on every Xi zero, so source membership alone cannot imply RH.
- **Strongest positive survivor:** the actual minimal integral source ray controls the fully fused
  response with the sharp pointwise energy law `(HT3)`--`(HT4)` and all-prime conclusion `(HT5)`.
- **New insight:** the first missing step is not source-ray boundedness; it is extension from that
  exact raywise splice to the completed prime--Gamma response operator and its orbit-selecting
  indefinite channel.
- **Status:** dependency-closed paper and Lean proof in
  `XiAperturePoissonUnitApertureHilbertTransport.lean`; external novelty unverified.

## Lean status

`RHTower/XiAperturePoissonUnitApertureHilbertTransport.lean` formalizes:

1. positivity and the sharp prime-uniform bound `gain^2<=27`;
2. equality at the prime-two channel;
3. the exact local identity `(HT3)`;
4. the true-aperture energy comparison `(HT4)`; and
5. the all-prime summability theorem `(HT5)`.

The exact leaf compilation passes.  `#print axioms` for the gain bound, local energy identity,
pointwise comparison, and all-prime summability reports only `propext`, `Classical.choice`, and
`Quot.sound`.  No umbrella or full project build was used.

## Gates

- [x] 0 -> 1: exact source metric and response current identified; paper proof dependency-closed
- [x] 1 -> 2: `(HT1)`--`(HT5)` proved without RH or numerical input
- [ ] hostile external novelty audit
- [x] 2 -> 3: targeted Lean theorem, leaf check, and axiom audit
- [ ] prime--Gamma completed response intertwiner

## Log

- 2026-07-19 — derived by comparing the complete valuation-fused Bose current with the actual
  continuous Möbius--Szego diagonal at the minimal positive integral aperture.
- 2026-07-19 — formalized with sharp prime-two equality, targeted leaf verification, and an
  axiom audit of the load-bearing transport and summability theorems.
