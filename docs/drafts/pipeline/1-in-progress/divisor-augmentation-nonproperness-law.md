# Divisor augmentation and charge nonproperness

- **ID:** `divisor-augmentation-nonproperness-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM / RH ROUTE CLASSIFICATION / HT GEOMETRY
- **Scientific status:** `[PARENT LAW PROVED] [XI NONPROPERNESS PROVED] [NOVELTY AUDIT ACTIVE]`

## Reinterpretation

The common obstruction is not positivity, ramification, or Ward charge separately. It is a
forgetful augmentation map.

Let `R=C[∂]`, let `I` be a finite nonempty reporter packet, and let `g` be a meromorphic common
mode with one simple pole. The packet action factors as

```text
R^I --sum--> R --P↦P(∂)g--> meromorphic functions.
```

The second arrow is injective. Therefore

```text
ker(packet action) = {(P_i) : sum_i P_i = 0} = A_(|I|-1),
im(packet action) = R·g.
```

This is the divisor-augmentation exact sequence. Relative/projective reporters occupy the
augmentation directions and delete the single diagonal divisor mode. The source-marked
logarithmic current `g=d log F` is the cyclic quotient; at every zero it has a simple pole,
independently of zero multiplicity.

## Why earlier results are shadows

1. **Pairwise HT common-mode loss.** Complete pairwise differences generate the rooted
   augmentation field. One genuinely hypertranscendental translation mode remains outside.
2. **Isodivisorial relative independence.** Arbitrarily rich projective differential geometry can
   coexist with one fixed divisor because projectivization is the augmentation quotient.
3. **Intensity and squared-coordinate blindness.** Even/invariant readers descend through a
   quotient and cannot choose the marked orientation sheet. The logarithmic current survives,
   but the source mark does not.
4. **Cubic exterior threshold.** Three labels first provide the two-dimensional `A_2` relative
   space whose determinant line can carry an oriented exterior observable. This is why the first
   response sign fracture appears at three nodes rather than one or two.
5. **Ward quantization.** The boundary Poisson/Julia transgression reads the residue divisor of
   the cyclic marked mode. One strict-right quartet contributes exactly `8π`.
6. **Compact-window failure.** Forgetting the mark makes the divisor-charge map nonproper:
   residues can escape to the height boundary while every bounded-window observer converges to
   vacuum.

## Xi nonproperness theorem

Fix `0<a<1/2`. For every `N>0` there is a sequence

```text
F_(N,n)(s)=G_(a,n)(s)^N Xi(s)
```

such that:

- every `F_(N,n)` is entire, hypertranscendental, FE-symmetric, Schwarz-symmetric, and has an
  off-critical quartet of multiplicity `N`;
- every holomorphic jet converges compact-open to the corresponding Xi jet;
- every represented even-shift differential matroid is exactly Xi's, both over `C(s)` and after
  adjoining all scalar Euler valuation layers;
- the Ward density converges uniformly to zero on every bounded height window;
- total Ward mass remains exactly `8πN`;
- the marked logarithmic source current has a simple pole at the inserted divisor and realizes
  the same augmentation exact sequence for every `N,n`.

Consequently, the off-critical divisor charge is unbounded on one completed-symmetry Kolchin
stratum and is invisible to compact-open convergence of all jets and all bounded Ward windows.

## RH consequence

No rational-differential-gauge-invariant criterion can imply RH on the natural completed-symmetry
class. This includes criteria depending only on:

- hypertranscendence or differential transcendence degree;
- generated differential fields;
- finite, countable, or all-valuation represented differential matroids;
- compact-open knowledge of every holomorphic jet;
- bounded-height Ward densities.

The positive successor is exact, not aspirational: retain the marked logarithmic divisor current
and a coercive boundary-at-infinity topology. The marked current is complete for every finite
rational divisor surgery; all unmarked observers above are provably incomplete.

## Novelty falsifiers

Reject general-journal significance if literature already contains the simultaneous statement:

```text
same complete Euler-enlarged Kolchin stratum
+ all-jet compact-open convergence
+ arbitrary off-critical multiplicity
+ exact A_(n-1) principal-part sequence
+ locally vanishing but globally quantized Ward charge.
```

Gauthier--Xarles prove compact-open density of FE-preserving RH failures and are the closest known
predecessor. Their theorem does not preserve the complete differential field/matroid, identify
the augmentation-residue sequence, or produce the quantized marked boundary charge.

## Internal theorem trace

- `HTGeometry.DifferentialPairwiseCommonMode`
- `RHTower.CompactOpenKolchinWardChargeEscape`
- `RHTower.HypertranscendentalFiniteQuartetWardIndex`
- `RHTower.XiApertureCubicExteriorMatching`
- `RHTower.DivisorAugmentationExactSequence`

## Gates

- [x] universal local exact sequence
- [x] arbitrary-charge Xi nonproperness
- [x] exact marked simple-pole survivor
- [x] prove explicit exterior `A_2` connector rather than leave it interpretive
- [ ] complete primary-source novelty audit
- [ ] write publication manuscript
- [ ] hostile general-journal review
- [ ] final formal, axiom, lint, PDF, and process audit
