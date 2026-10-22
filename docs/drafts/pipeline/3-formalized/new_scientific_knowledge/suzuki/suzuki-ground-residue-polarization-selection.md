# Suzuki Ground-Residue Polarization Selection

- **ID:** suzuki-ground-residue-polarization-selection
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** Suzuki 2026 finite-aperture defect path; prime--Gamma Xi first-defect calibration
- **Statement:** A pure simple-even spectral floor is not needed to select Suzuki's canonical
  Xi-matching shift. Mixed and multiple bottom eigenspaces work exactly when their source residues
  satisfy one sharp polarization inequality.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
  `[NOVELTY-BOUNDARY-AUDITED]`

## Goal

Remove an artificial hypothesis from Suzuki's first-jet source selector. Earlier closure used
ground-edge limit `kappa -> 1`, obtained from a simple pure-even ground state. Actual restricted
Weil floors may have multiplicity or mixed parity. The relevant datum is not eigenspace dimension
but source mass in its even and odd parts.

This card proves the exact replacement and isolates the remaining arithmetic obligation. It does
not prove that Suzuki's restricted-Weil bottom projection satisfies that obligation, does not
construct the two-angle meromorphic limit, and does not imply RH.

## Gates

- [x] 0 -> 1 in-progress: exact mixed-ground endpoint stated in source-residue variables
- [x] 1 -> 2 fully-proven: limit transport, sharp threshold, and greatest-root proof closed
- [x] 2 -> 3 formalized: unconditional
      `RHTower/Suzuki/SuzukiGroundResiduePolarizationSelection.lean`
- [ ] 3 -> 4 publication-ready: specialist priority review and inclusion in a standalone Suzuki
      source paper

## Setup

At one aperture let `lambda_a` be the spectral floor and let `E(lambda), O(lambda)` be Suzuki's
even and odd source energies below it. Suppose the pole-rescaled energies have finite limits

```text
(lambda_a-lambda) E(lambda) -> m_E,
(lambda_a-lambda) O(lambda) -> m_O                 (lambda -> lambda_a-),
```

with `m_E+m_O>0`. No simplicity or pure parity is assumed. Put

```text
kappa(lambda) = [E(lambda)-O(lambda)]/[E(lambda)+O(lambda)],
kappa_g       = (m_E-m_O)/(m_E+m_O).                         (1)
```

Let `kappa_Xi` be the unconditional prime--Gamma first-defect calibration already satisfying

```text
77/85 < kappa_Xi < 1.                                      (2)
```

## Theorem 1: exact mixed-ground endpoint

Under the two residue limits,

```text
kappa(lambda) -> kappa_g             (lambda -> lambda_a-). (3)
```

### Proof

The defect angle is invariant under a common nonzero scale:

```text
[(cE)-(cO)]/[(cE)+(cO)] = (E-O)/(E+O).                     (4)
```

Choose `c=lambda_a-lambda`. The numerator and denominator of the scaled quotient converge to
`m_E-m_O` and `m_E+m_O`; the latter is nonzero. Quotient continuity proves (3).

For a resolvent pole, `m_E,m_O` are precisely the source weights of the even and odd parts of the
bottom spectral projection, with multiplicity already summed. Thus the endpoint remembers source
polarization rather than spectral multiplicity.

## Theorem 2: sharp Xi-admission threshold

For `m_E+m_O>0`,

```text
kappa_Xi < kappa_g
iff
(1+kappa_Xi)m_O < (1-kappa_Xi)m_E.                         (5)
```

If `m_E>0` and `m_O>=0`, define

```text
tau_Xi = (1-kappa_Xi)/(1+kappa_Xi).                        (6)
```

Then

```text
kappa_Xi < kappa_g
iff
m_O/m_E < tau_Xi,                                         (7)

0 < tau_Xi < 4/81.                                        (8)
```

### Proof

Multiply `kappa_Xi<(m_E-m_O)/(m_E+m_O)` by the positive denominator and collect the two residue
terms. This is (5). Under `m_E>0`, divide (5) by `(1+kappa_Xi)m_E>0` to obtain (7). Positivity in
(8) follows from `kappa_Xi<1`. The lower bound in (2) gives

```text
tau_Xi < (1-77/85)/(1+77/85) = 4/81.                       (9)
```

The inequality is sharp: equality in (5) makes the ground endpoint equal the target and removes
the strict endpoint separation needed to trap an interior matching set.

## Theorem 3: canonical matching shift without simple-even ground

Assume:

```text
kappa : (-infinity,lambda_a) -> R is continuous,
kappa(lambda) -> kappa_free       as lambda -> -infinity,
kappa_free < kappa_Xi,
the residue limits above hold,
(1+kappa_Xi)m_O < (1-kappa_Xi)m_E.                         (10)
```

Then the matching set

```text
S = {lambda < lambda_a : kappa(lambda)=kappa_Xi}           (11)
```

is nonempty and has a greatest member. Moreover the source-defined selector

```text
lambda_* = sup S                                            (12)
```

is that member:

```text
IsGreatest S lambda_*.                                      (13)
```

### Proof

Theorem 1 and (5) place the ground endpoint strictly above `kappa_Xi`, while (10) places the free
endpoint strictly below it. Continuity gives a root. The two strict endpoint limits trap every
root inside one compact interval. The inverse image of the singleton `{kappa_Xi}` is closed on
that interval, so the trapped root set is nonempty compact and attains its maximum. Its supremum
equals that maximum. No monotonicity or root uniqueness is assumed.

## Strongest positive conclusion

The cofinal first-jet source problem no longer asks for simple ground eigenvalues or eventually
pure even parity. It asks for the quantitatively weaker and exact bottom-projection law

```text
m_O/m_E < tau_Xi < 4/81.                                  (14)
```

This permits arbitrary bottom multiplicity and mixed parity. It makes the pole-driven sufficient
branch source-local: prove (14) for the literal restricted-Weil bottom projection on one cofinal
aperture family, then control the selected shifts through second jets and the two-angle
meromorphic limit. The separate interior-excursion theorem shows that this pole branch is not
necessary for selection.

## Theorem 4: exact bottom-projection reflection cone

Let `P_0` be the bottom spectral projection at one aperture, let `Jf(x)=f(-x)`, and take the
literal exponential source

```text
w=P_0 e^x,                 Jw=P_0 e^(-x).               (15)
```

Here `P_0J=JP_0`, so `||Jw||=||w||`, while

```text
evenPart(w,Jw)=P_0 cosh(x),
oddPart(w,Jw)=P_0 sinh(x).                               (16)
```

If `w!=0`, the residue admission inequality (5) is equivalent to each of

```text
kappa_Xi ||w||^2 < <Jw,w>,                               (17)

2 ||P_0 sinh(x)||^2
  < (1-kappa_Xi)||w||^2,                                 (18)

||w-Jw||^2
  < 2(1-kappa_Xi)||w||^2.                                (19)
```

### Proof

Equal norms give the exact polarization identities

```text
<Jw,w>
 =||evenPart(w,Jw)||^2-||oddPart(w,Jw)||^2,

||w||^2
 =||evenPart(w,Jw)||^2+||oddPart(w,Jw)||^2.              (20)
```

Substituting (20) into (5) gives (17) and (18). Since
`oddPart(w,Jw)=(w-Jw)/2`, (18) is equivalent to (19). No simplicity, positivity of a ground
eigenfunction, or choice of eigenbasis occurs.

## Theorem 5: unconditional Xi cone and parity-floor classification

The unconditional calibration `77/85<kappa_Xi` sharpens (17)--(19) to

```text
<Jw,w> > (77/85)||w||^2,
||P_0 sinh(x)||^2/||w||^2 < 4/85,
||w-Jw||^2 < (16/85)||w||^2,
||P_0 cosh(x)||^2 > (81/4)||P_0 sinh(x)||^2.              (21)
```

Consequently:

- a nonzero reflection-fixed bottom source (`Jw=w`) is admitted;
- a nonzero reflection-antifixed bottom source (`Jw=-w`) is excluded;
- a mixed even/odd bottom collision is admitted exactly when it lies in (17);
- a source-invisible bottom space (`P_0e^x=0`) has no ground pole and is not covered by the
  residue endpoint theorem.

In Suzuki's parity-floor notation, strict visible even-floor dominance is therefore sufficient,
strict visible odd-floor dominance is fatal, and an even/odd floor collision is governed by the
sharp reflection cone rather than multiplicity.

## Frontier conjecture: `SUZUKI-GROUND-REFLECTION-CONE`

There is a cofinal aperture family `a_j -> infinity` on which the literal restricted-Weil bottom
projection is source-visible and satisfies

```text
<P_(0,a_j)e^(-x),P_(0,a_j)e^x>
  > kappa_Xi ||P_(0,a_j)e^x||^2.                         (22)
```

This is not asserted as proved. It is the exact pole-driven first-jet frontier. A proof must use
Suzuki's prime--archimedean restricted-Weil operator; generic positive-resolvent geometry cannot
establish it. Failure of this conjecture does not kill Suzuki: a finite-shift interior excursion
above `kappa_Xi` can still produce the canonical selector. A negative closure must rule out both
branches.

## Hostile falsification audit

- If `m_E=0` and `m_O>0`, then `kappa_g=-1`; selection fails.
- If `m_E=m_O>0`, then `kappa_g=0`; selection fails because `kappa_Xi>0`.
- If `m_O/m_E=tau_Xi`, the endpoint only touches the target; an interior root need not exist.
- If `m_O/m_E>tau_Xi`, endpoint ordering is reversed and the intermediate-value argument gives
  no root.
- Multiple roots and nonmonotone defect paths do not break the theorem; the greatest-root
  construction handles both.
- The theorem cannot be used by defining `m_E,m_O` from `kappa_Xi`; they must be residues of the
  literal source-resolvent path.
- A bottom eigenvalue alone is insufficient. If the exponential source is orthogonal to its
  eigenspace, the putative pole residue vanishes.
- The constants in (21) are strict. Replacing them by non-strict bounds loses the interior
  endpoint separation required by the greatest-root construction.
- Failure of the bottom cone does not imply absence of an interior matching root.

## Novelty audit

Common-scale quotient limits, pole residues, and compact endpoint interpolation are classical and
are not claimed as new. Targeted arXiv searches for the exact conjunction

```text
Suzuki restricted-Weil defect angle
+ mixed bottom-eigenspace source residues
+ prime--Gamma Xi calibration
+ canonical greatest matching shift
```

found Suzuki's screw-function construction and classical canonical-system parents, but no matching
result. The candidate new knowledge is this Suzuki-specific synthesis: the exact residue
polarization boundary (5)--(8), removal of simple-evenness from the source selector, and
the equivalent reflection-fidelity cone (17)--(19), including its sharp pure-parity boundary and
the unconditional quantitative aperture (21). Targeted arXiv searches found no occurrence of this
Suzuki/Xi bottom-projection criterion. Search absence does not certify priority; specialist review
remains required.

Primary comparison:

- Masatoshi Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
- Masatoshi Suzuki, *An inverse problem for a class of canonical systems and its applications to
  self-reciprocal polynomials*, arXiv:1308.0228.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGroundResiduePolarizationSelection.lean
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGroundProjectionReflectionCone.lean
```

Capstone declarations:

```text
tendsto_suzukiDefectAngle_groundResidues
target_lt_suzukiGroundResidueAngle_iff
primeArchSuzukiGroundOddEvenThreshold_mem_Ioo
primeArchSuzuki_target_lt_groundResidueAngle_iff_ratio
exists_isGreatest_suzukiDefectMatchingShiftSet_of_two_limits
primeArchSuzukiGreatestDefectShift_spec_of_groundResidues
primeArchSuzukiGroundProjection_admitted_iff_reflectionCone
primeArchSuzukiGroundProjection_reflectionCone_iff_oddMass
primeArchSuzukiGroundProjection_reflectionCone_iff_distance
primeArchSuzukiGroundProjection_reflectionCorrelation_gt_seventySeven_div_eightyFive
primeArchSuzukiGroundProjection_oddShare_lt_four_div_eightyFive
primeArchSuzukiGroundProjection_reflectionDistance_sq_lt
primeArchSuzukiGroundProjection_evenMass_gt_eightyOne_div_four_mul_oddMass
primeArchSuzukiGroundProjection_admitted_of_reflection_fixed
primeArchSuzukiGroundProjection_not_admitted_of_reflection_antifixed
```

All theorems are unconditional. No `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, or computation
occurs.

## Log

- 2026-08-01 — paper proof closed; unconditional Lean formalization completed; simple-even
  endpoint replaced by exact mixed-ground residue polarization.
- 2026-08-01 — residue selector identified with exact bottom-projection reflection cone; pure
  parity boundary and unconditional `77/85`, `4/85`, `16/85` aperture formalized; cofinal literal
  restricted-Weil cone isolated as named open conjecture.
