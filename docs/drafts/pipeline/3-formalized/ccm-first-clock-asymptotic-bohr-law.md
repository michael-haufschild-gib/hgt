# CCM first-clock asymptotic Bohr law

- **ID:** `ccm-first-clock-asymptotic-bohr-law`
- **Stage:** `3-formalized`
- **Type:** THEOREM / source-side RH equivalence and conditional value law
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../3-formalized/needs-audit/ccm-first-clock-tail-lower-bound-completeness.md`
- **HT source:** `HTGeometry/SummableSpectrumScrewRecurrence.lean`

## Exact source-only equivalence

Put

```text
B1(L) = ccmPublishedSourceSineCoefficient(L/2, 2*pi/L),
F(L)  = L * B1(L).
```

Call `F` asymptotically Bohr almost periodic when there is a continuous Bohr almost-periodic
function `P : R -> R` such that

```text
F(L) - P(L) -> 0 as L -> +infinity.                         (ABP)
```

Then

```text
(ABP) <-> RiemannHypothesis.                                (1)
```

This statement names only the literal published CCM source on its left side. It does not put a
zero-location condition into the definition.

## Explicit RH asymptote

For each Xi zero copy `q`, set

```text
omega(q) = Re(xiSpectralPoint(q)),
a(q)     = 1 / omega(q)^2,
S(L)     = sum_q a(q) * (1 - cos(omega(q)*L)).               (2)
```

Under RH, `xiSpectralPoint(q)=omega(q)` is real, `|omega(q)|>4`, `a(q)>0`, and `sum_q a(q)<infinity`.
The witness in `(ABP)` is

```text
P(L) = 2*S(L).                                               (3)
```

Let

```text
M = 2 * screwHullMax(a,omega).                               (4)
```

Under RH the stronger value law holds:

1. `liminf F = 0` and `limsup F = M`;
2. the asymptotic tail-cluster set of `F` is exactly `[0,M]`;
3. every `y in [0,M]` is approximated by `F` with bounded gaps after a sufficiently large
   starting time;
4. `M = 4*sum_q a(q)` exactly when every finite integral relation among the ordinates has even
   total coefficient.

No simplicity or rational-independence hypothesis occurs.

## Paper proof

### 1. RH identifies the Xi screw with the HT screw series

Assume RH. The corpus gives

```text
xiSpectralPoint(q) = (omega(q) : C),
sum_q 1/|xiSpectralPoint(q)|^2 < infinity,
|xiSpectralPoint(q)| > 4.
```

Consequently `a(q)=1/|xiSpectralPoint(q)|^2` is a strictly positive summable family. Termwise,

```text
ccmFirstClockScrewKernel(L,xiSpectralPoint(q))
  = (1-cos(omega(q)*L))/omega(q)^2.
```

Absolute summability permits summation, hence

```text
Re xiScrewDivisor(L) = S(L).                                 (5)
```

Finite partial sums of `(2)` are trigonometric polynomials, hence Bohr almost periodic. Their
tails are uniformly bounded by twice the corresponding tail of `sum a(q)`. Therefore `S`, and
thus `P=2S`, is Bohr almost periodic by uniform closure. Continuity also follows from the same
uniform convergence.

### 2. The moving first-clock denominator is asymptotically invisible

Write `w_L=2*pi/L` and

```text
Q(L) = ccmFirstClockXiRationalDivisor(L).
```

For `L>=2*pi`, `0<=w_L<=1`. Under RH every summand is real and

```text
Q_q(L) - S_q(L)
 = (1-cos(omega(q)*L)) * w_L^2
     / (omega(q)^2 * (omega(q)^2-w_L^2)).                   (6)
```

Since `omega(q)^2>16`, all factors in `(6)` are nonnegative and

```text
0 <= Q_q(L)-S_q(L)
   <= (2/15) * w_L^2 / omega(q)^2.                          (7)
```

Indeed `1-cos<=2` and `omega(q)^2-w_L^2 >= omega(q)^2-1 >15`. Summing `(7)` gives

```text
0 <= Re Q(L)-S(L) <= (2/15)*w_L^2*sum_q a(q) -> 0.          (8)
```

The literal source identity, valid for `L>=pi/2`, is

```text
B1(L) = (2/L) * Re Q(L).
```

Thus

```text
F(L)-P(L) = 2*(Re Q(L)-S(L)) -> 0.                          (9)
```

This proves RH implies `(ABP)`.

### 3. Asymptotic Bohr behavior forces RH

Assume `(ABP)` with witness `P`. A continuous Bohr almost-periodic function is globally bounded;
this is `HTGeometry.BohrMeanValue.exists_bound_of_isBohrAlmostPeriodic`. Equation `(ABP)` then
makes `F` bounded on some positive tail. On a tail where `L>=1`, division by `L` shows that `B1`
has a finite lower bound. The already formalized theorem

```text
ccmFirstClockPublishedSourceEventuallyBoundedBelow_iff_rh
```

therefore gives RH. This proves `(1)`.

### 4. Exact value law

`HTGeometry.SummableSpectrumScrewRecurrence` applies to the positive summable family `(a,omega)`.
It proves that every cofinal tail of `S` has closure `[0,screwHullMax(a,omega)]`, that `liminf S=0`,
that `limsup S=screwHullMax(a,omega)`, and that every value in this interval is approximated with
bounded gaps. Its parity theorem identifies when the absolute upper bound is attained.

Multiplication by `2` transfers these statements to `P`. The vanishing perturbation `(9)` preserves
liminf, limsup, and the intersection of all closed tail images. For bounded-gap approximation,
first choose the perturbation below half the requested tolerance beyond one threshold and then use
the HT bounded-gap return window starting after that threshold. This proves all four claims after
`(4)`.

The proof deliberately claims only the asymptotic tail-cluster set of `F`, not closure of every
fixed tail image: a finite initial segment can contribute extra values.

## Hostile audit

1. **Circular witness?** No. `(ABP)` quantifies over an arbitrary real Bohr almost-periodic
   function and mentions no zero. Zero ordinates construct the witness only in the RH-to-source
   direction.
2. **Does boundedness of the witness suffice?** Yes. A vanishing perturbation of a bounded function
   is eventually bounded, so `F/L=B1` has a fixed lower floor; the exact Stage-3 tail-floor theorem
   then gives RH.
3. **Can a denominator approach zero?** No on the audited tail: `w_L<=1` and every RH ordinate has
   absolute value greater than `4`.
4. **Can the infinite sum invalidate `(8)`?** No. `(7)` is dominated by the already proved
   reciprocal-square summable Xi family.
5. **Does asymptotic closeness preserve exact level hits?** Not asserted. It preserves cluster
   values and approximate bounded-gap recurrence, not exact equality at finite times.
6. **Is the recurrence theorem merely Suzuki's rational-independence argument?** No. The HT proof
   uses the compact relation hull and works with arbitrary multiplicity and arbitrary integral
   relations.

Verdict: `SURVIVES PRELIMINARY ATTACK`; paper proof is dependency-closed.

## External frontier and priority

- Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, JLMS 108
  (2023), arXiv:2206.03682, proves `Psi=O(1) <-> RH` and `Psi>=0 <-> RH`.
- In Section 7.1 Suzuki says the exact extreme values are not easy in general and derives
  `liminf Psi=0` and the absolute `limsup` only after adding simplicity and rational independence
  of positive zero ordinates.
- Suzuki, *The screw line of the Riemann zeta-function and its applications*, arXiv:2209.04658,
  develops the RH screw-line Hilbert geometry but does not state a relation-hull value law for the
  literal CCM first clock.
- Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, connects the 2026 CCM
  finite Weil framework to the screw function; no scaled-first-clock asymptotic Bohr criterion or
  relation-hull recurrence theorem was found.

The generic relation-hull theorem is already `[CORPUS]` in HTGeometry. Candidate new content is its
Xi instantiation without simplicity/independence, the sharp moving-denominator estimate `(8)`, and
the transfer of the complete recurrence law to the literal published CCM first clock. Keep
`[NOVELTY UNVERIFIED]` pending independent expert review.

## Lean target

```text
formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockAsymptoticBohrLaw.lean
```

Required capstones:

```text
ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_iff_rh
ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh
```

Both capstones are Lean-proved. The same module also proves the sharp summand and full-sum
`(2/15)*(2*pi/L)^2` error bounds, eventual bounded-gap approximation of every relation-hull value,
and the exact integral-relation parity law for the absolute endpoint. Generic summable screw-series
Bohr almost periodicity is proved in
`formal/GaloisForLFunctions/HTGeometry/SummableSpectrumScrewAlmostPeriodic.lean`.

Targeted `lake env lean` checks and
`lake build GaloisForLFunctions.RHTower.CCM.CCMFirstClockAsymptoticBohrLaw` are green. `#print axioms`
on the generic HT theorem, both required capstones, bounded-gap recurrence, and parity theorem
reports exactly `[propext, Classical.choice, Quot.sound]`.

The same module now also proves the remaining exact value-law capstones:

```text
ccmFirstClockScaledPublishedSource_liminf_eq_zero_of_rh
ccmFirstClockScaledPublishedSource_limsup_eq_asymptoticHullMax_of_rh
iInter_closure_ccmFirstClockScaledPublishedSource_image_Ici_eq_of_rh
```

The last theorem identifies the intersection of all closed cofinal tail images with
`[0, ccmFirstClockAsymptoticHullMax]`, exactly matching the paper's asymptotic tail-cluster set.
Targeted `lake env lean`, final
`lake build GaloisForLFunctions.RHTower.CCM.CCMFirstClockAsymptoticBohrLaw`, and `#print axioms` on all
three new capstones are green. Their axiom set is exactly
`[propext, Classical.choice, Quot.sound]`.
