# Suzuki Two-Jet Shifted-Hankel Gate

- **ID:** suzuki-two-jet-shifted-hankel-gate
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Source:** Suzuki 2026 finite-aperture Livšic carrier; safe-shift prime--Gamma Xi moments
- **Statement:** The second-jet Schwarz--Pick slack of Suzuki's anchored finite-aperture carrier is
  exactly a nonlinear parity-source numerator; at the Xi target it is exactly the normalized first
  `2 x 2` Hankel minor of the safe-shift reciprocal moment tower. Position torque alone determines
  this slack only on the parity-balanced locus and is class-completely insufficient off that locus.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL]`
  `[NOVELTY-BOUNDARY-AUDITED]`

## Goal

Close the first genuinely nonlinear source gate left after Suzuki's exact first-defect
calibration. The result must say what finite-aperture Schur geometry forces on the literal
even/odd deficiency response and must identify the exact Xi-side obligation without defining a
source interface from the desired target.

This card does **not** claim RH, the safe-shift determinant sign, or the two-angle Xi limit.
It replaces an unspecified “second-jet compatibility” problem by one exact source inequality and
proves a class-complete obstruction to using position torque as its only control variable.

## Gates

- [x] 0 -> 1 in-progress: source-pure parity variables, hostile torque-only hypothesis, exact
      safe-shift target
- [x] 1 -> 2 fully-proven: dependency-closed Schwarz--Pick, parity, moment, and torque-fiber proofs
- [x] 2 -> 3 formalized: unconditional Lean module
      `RHTower/Suzuki/SuzukiTwoJetShiftedHankelGate.lean`
- [ ] 3 -> 4 publication-ready: specialist priority review and integration into a standalone
      Suzuki operator paper

## Setup

Let `f` be an anchored holomorphic self-map of the unit disk:

```text
f(0)=0,       f(D) subset closed(D).
```

Write its real first two jets as

```text
kappa=f'(0),       q=f''(0).
```

For Suzuki's even/odd deficiency response write

```text
E = even energy,             O = odd energy,
alpha = even tilt moment,    beta = odd tilt moment.
```

The already-derived endpoint identities give

```text
kappa = (E-O)/(E+O),                                      (1)
q = 8(alpha O-beta E)/(E+O)^2.                            (2)
```

For the normalized Xi target at the safe squared shift `y=1`, put

```text
A = Re M_0(1),       B = Re M_1(1),       C = Re M_2(1),  (3)
```

where `M_n(1)` is the source-only negative-binomial prime--Gamma realization of the shifted
reciprocal Xi moment. Existing source identities give

```text
kappa_Xi = (A-2B)/A,                                      (4)
q_Xi = 8(2C/A-B/A-(B/A)^2).                               (5)
```

The zeroth moment satisfies `A>0` unconditionally.

## Theorem 1: anchored Schur second-jet law

If `|kappa|<1`, then

```text
|q| <= 2(1-|kappa|^2).                                    (6)
```

For real `kappa,q`, in particular,

```text
0 <= q+2(1-kappa^2).                                      (7)
```

### Proof

Set

```text
g(z)=f(z)/z
```

with the removable value `g(0)=f'(0)=kappa`. Schwarz's lemma gives `|g(z)|<=1`. Compose `g` with
the disk automorphism taking `kappa` to zero:

```text
h(z)=(g(z)-kappa)/(1-conj(kappa)g(z)).
```

The exact norm-square identity

```text
|1-conj(kappa)w|^2-|w-kappa|^2
  =(1-|kappa|^2)(1-|w|^2)                                (8)
```

shows `h(D) subset closed(D)`. Since `h(0)=0`, Schwarz's lemma gives `|h'(0)|<=1`. Removable
division gives

```text
g'(0)=f''(0)/2,
h'(0)=g'(0)/(1-|kappa|^2).
```

This is (6), and (7) follows from `-|q|<=q`. No boundary regularity or RH assumption is used.

The coefficient estimate itself is classical Schwarz--Pick theory. Novelty is not claimed for
Theorem 1 in isolation.

## Theorem 2: exact Suzuki parity law

Substituting (1)--(2) into (7) gives the identity

```text
q+2(1-kappa^2)
  = 8[O(E+alpha)-E beta]/(E+O)^2.                         (9)
```

Therefore every anchored Suzuki Schur carrier with `E,O>0` satisfies

```text
O(E+alpha)-E beta >= 0.                                  (10)
```

### Proof

The elementary polarization

```text
(E+O)^2-(E-O)^2=4EO
```

turns the Schwarz boundary contribution into `8EO/(E+O)^2`. Adding (2) gives (9). Positivity of
`(E+O)^2` converts (7) to (10).

Equation (10) is the finite-aperture source obligation. It retains parity and tilt information
before scalar target identification. In Lean the disk-self-map hypotheses are also discharged
from Suzuki's actual all-angle real-zero theorem: finite-aperture Hermite--Biehler separation
supplies the disk map directly, so (10) is not left behind an abstract Schur-interface assumption.

## Theorem 3: exact safe-shift Hankel identification

Substituting (4)--(5) yields

```text
q_Xi+2(1-kappa_Xi^2)
  = 16(AC-B^2)/A^2.                                      (11)
```

Since `A>0`,

```text
q_Xi+2(1-kappa_Xi^2) >= 0
  iff AC-B^2 >= 0.                                       (12)
```

Thus the Xi two-jet Schur compatibility problem is **exactly** the first shifted reciprocal
Hankel minor at `y=1`.

This is not the already-known central minor

```text
normalizedPrimeArchMoment(0) normalizedPrimeArchMoment(2)
  - normalizedPrimeArchMoment(1)^2.
```

It is its full safe-shift negative-binomial transform, forced specifically by Suzuki's
Donoghue/Livšic normalization.

## Theorem 4: class-complete torque-only obstruction

The source numerator in (10) has the exact decomposition

```text
O(E+alpha)-E beta
  = EO + E(alpha-beta) + alpha(O-E).                      (13)
```

The position commutator determines the torque

```text
delta=alpha-beta.
```

If `O != E`, then for every fixed `E,O,delta` and every prescribed real number `s`, there exist
`alpha,beta` with

```text
alpha-beta=delta,
O(E+alpha)-E beta=s.                                     (14)
```

Indeed choose

```text
alpha=(s-EO-E delta)/(O-E),       beta=alpha-delta.       (15)
```

Consequently torque alone imposes **no sign whatsoever** on the Suzuki Schur slack away from exact
parity-energy balance. This is a full fiber classification, not failure of one estimate.

On the balanced locus `E=O=m>0`, the residual term vanishes and

```text
O(E+alpha)-E beta = m(m+delta),                           (16)
```

so the sharp torque criterion is

```text
delta >= -m.                                             (17)
```

## Theorem 5: normalized transition window and reciprocal-radial concavity

The missing coordinate has a canonical dimensionless normalization:

```text
g = beta/O-alpha/E.                                      (18)
```

For `E,O>0`, direct elimination gives

```text
q = -2(1-kappa^2)g,                                      (19)
O(E+alpha)-E beta = EO(1-g).                             (20)
```

Thus negative Xi curvature supplies the strict lower wall `g>0`, while the actual all-angle
Suzuki Schur carrier supplies the sharp upper wall `g<=1`. Every Xi-identifying transition scale
must therefore enter

```text
0 < g <= 1.                                              (21)
```

This is stronger typing than the unnormalized residual `alpha(O-E)`: `g` is invariant under
independent positive rescaling of each channel pair `(E, alpha)` and `(O, beta)`, and is exactly
half the logarithmic tilt velocity of their ratio.

At the safe-shift target,

```text
g_Xi = (AB+B^2-2AC)/(B(A-B)),                            (22)
```

where `A>0`, `B>0`, and the unconditional `85B<4A` bound gives `A-B>0`. Existing negative
curvature proves `g_Xi>0`; elementary elimination proves

```text
g_Xi <= 1  iff  AC-B^2 >= 0.                             (23)
```

There is also an exact differential form. Put

```text
G(y)=Re M_0(y)/2.
```

Termwise differentiation of the shifted reciprocal moment tower gives

```text
G'(1)=-B/2,        G''(1)=C,
(1/G)''(1)=4(B^2-AC)/A^3.                               (24)
```

Since `A>0`,

```text
g_Xi<=1
  iff AC-B^2>=0
  iff (1/G)''(1)<=0.                                     (25)
```

Suzuki's first nonlinear admission gate is therefore local concavity, at the safe shift, of the
reciprocal squared-Xi radial logarithmic-derivative response. The calculus and generic
Hankel/concavity equivalence are classical; claimed novelty is the exact Suzuki source coordinate
`g`, its sharp window (21), and its identification with this particular prime--Gamma radial
response.

## Theorem 6: positive-resolvent/parity axioms are class-completely insufficient

The torque-only scalar no-go extends to a literal operator countermodel. For every `E,O>0` and
every `alpha,beta in R`, define positive two-plane blocks

```text
R(E,alpha) = [[E, alpha], [alpha, alpha^2/E+1]],
R(O,beta)  = [[O, beta ], [beta,  beta^2/O+1]].
```

Their quadratic forms have the completed-square identities

```text
<v,R(E,alpha)v> = (E v_1+alpha v_2)^2/E+v_2^2 > 0,
<v,R(E,alpha)^(-1)v>
  = (v_2-alpha v_1/E)^2+v_1^2/E > 0                     (26)
```

for every nonzero `v`; likewise for the odd block. On the direct sum of even and odd planes put

```text
R=R(E,alpha) direct_sum R(O,beta),
J=diag(+I,-I),
X=[[0,K],[K,0]],             K=[[0,1],[1,0]].
```

Then `R` and `R^(-1)` are positive definite and self-adjoint, `RJ=JR`, `X` is self-adjoint,
and `XJ=-JX`. For the first basis vectors `c` and `s` in the even and odd planes,

```text
<c,Rc>=E,       <s,Rs>=O,
<Rc,Xs>=alpha,  <Rs,Xc>=beta.                            (27)
```

Hence every positive energy pair and every two tilts occur inside an invertible positive
parity-resolvent model with a self-adjoint parity-reversing position operator. Combining (27)
with (14)--(15), for `O!=E` the fixed-torque Schur numerator remains surjective onto all of `R`
even inside this operator class.

This is a class-complete no-go for closure from generic positivity, self-adjointness, invertibility,
parity, and position geometry. It is not a no-go for Suzuki's concrete restricted-Weil operator.
The remaining theorem must use arithmetic kernel structure absent from the abstract operator
axioms—for example a source-derived total-positivity, variation-diminishing, or comparison law
forcing the literal deficiency responses into (21).

## Theorem 7: even positive exponential spectral response is insufficient

The preceding model did not impose the literal exponential source or require the resolvent to
commute with position. Both strengthenings still fail. Work on the symmetric three-point position
spectrum `{-1,0,1}`. Put

```text
C=cosh(1),       S=sinh(1),
D=C-S=exp(-1)>0,       P=SC-1>0,
L=2CP/D+1>0.                                             (28)
```

Let `X=diag(-1,0,1)`, reflection exchange the two flanks, and let

```text
R=diag(1,L,1),              T=R^(-1),
e^X=(exp(-1),1,exp(1)),     u=R e^X.                     (29)
```

Then `R` and `T` are positive definite, self-adjoint, mutually inverse, reflection preserving,
and commute with `X`. The response `u` is pointwise strictly positive and satisfies the literal
source equation `Tu=e^X`. Its parity moments are

```text
E=L+2C^2,       O=2S^2,       alpha=beta=2SC.             (30)
```

Direct substitution, using `C^2-S^2=1`, gives the strict identity

```text
O(E+alpha)-E beta=-2SD<0.                                (31)
```

Hence its normalized relative tilt satisfies

```text
g=beta/O-alpha/E>1.                                      (32)
```

This is stronger than Theorem 6: compact symmetric spectral support, literal exponential
sourcing, pointwise positivity, positive invertible source/resolvent operators, parity, and even
resolvent--position commutation do not force Suzuki's wall. The missing property is not generic
spectral positivity. It must couple center and flanks through Suzuki's concrete restricted-Weil
kernel and all-angle extension geometry.

## Consequence for an Xi-identifying Suzuki family

Suppose actual finite-aperture disk carriers remain anchored Schur maps and converge locally
uniformly to the normalized Xi disk target. Holomorphic derivative convergence transports (7) to
the limit. Equations (11)--(12) then force

```text
Re M_0(1) Re M_2(1)-Re M_1(1)^2 >= 0.                    (28)
```

Therefore:

- proving the strict reverse of (28) would give a class-complete no-go for this anchored Schur
  limit;
- proving (28) is only the first nonlinear admission gate, not RH;
- the full cofinal shifted Hankel cone remains RH-equivalent, so one `2 x 2` minor cannot replace
  the all-order problem;
- neither the position-torque recurrence nor generic positive-resolvent/parity structure can close
  (28); the literal restricted-Weil kernel must force the normalized response gap `g<=1`.

The live hard problem is now sharply typed:

```text
SUZUKI-TWO-JET-HANKEL:
prove the safe-shift determinant (28) from the literal transition-scale source,
or prove that every source-admitted transition scale violates it;
in either case derive the normalized gap 0<g<=1 from the arithmetic kernel,
not from torque or generic positive-resolvent axioms.
```

After this gate, full-frequency two-angle normality, nondegeneration, and Xi/de Branges
identification still remain.

## What is new

Claimed new content:

1. Suzuki's finite-aperture second Schur coefficient is the exact nonlinear parity-source law
   (9)--(10).
2. Its normalized Xi value is exactly the safe-shift reciprocal-Xi Hankel minor (11), joining the
   source deficiency jets to the shifted moment criterion without a target-fitted interface.
3. The source numerator splits as (13), identifying position torque as only one component.
4. The fixed-torque fibers are surjective off parity balance, (14)--(15), giving a class-complete
   obstruction to every torque-only closure.
5. Exact balance is the unique locus where torque is a complete sign coordinate, with sharp
   threshold (17).
6. The dimensionless relative tilt gap `g` gives the exact source transition window `0<g<=1`,
   with safe-shift target formula (22).
7. The upper window wall is exactly local reciprocal-radial concavity (24)--(25).
8. Explicit positive invertible parity-resolvent models realize arbitrary `E,O,alpha,beta`;
   generic positivity, self-adjointness, invertibility, parity, and position geometry therefore
   cannot force the gate.
9. A positive diagonal three-point resolvent driven by the literal exponential source crosses the
   wall explicitly, so pointwise positivity, compact symmetric support, and commutation with
   position are also insufficient.

Not claimed new:

- Schwarz--Pick's coefficient estimate;
- elementary `2 x 2` Hankel algebra;
- the general fact that moment determinants encode Schur coefficients;
- the generic completed-square proof for positive `2 x 2` matrices;
- the generic calculus identity relating a first Hankel minor to curvature of a reciprocal
  response;
- the elementary three-point diagonal spectral model and hyperbolic identities in isolation;
- the previously formalized all-order shifted-Hankel RH criterion.

The advance is Suzuki-specific source identification, the normalized transition observable, and
the operator-class boundary showing exactly which source structure remains necessary.

## Novelty audit

- [Suzuki 2026](https://arxiv.org/abs/2606.09096) constructs the finite self-adjoint extensions,
  deficiency functions, real-zero all-angle family, and conjectural one-angle limit. Searches of
  the paper find no second disk-jet/Schwarz slack, shifted reciprocal Hankel determinant, parity
  tilt inequality (10), position-torque decomposition, or fixed-torque fiber classification.
- [Kim--Hong--Kim--Choi--Jang--Kim 2026](https://arxiv.org/abs/2607.24830) numerically realizes
  Suzuki's spectrum and arithmetic moments but does not derive these two-jet identities or a
  torque-only obstruction.
- Classical Schur algorithm and Carathéodory--Fejér theory contain abstract coefficient/moment
  correspondences. Priority is restricted to the literal Suzuki deficiency variables, the
  safe-shift prime--Gamma target, and the exact torque fiber.
- Internal search found the central Hilbert-dispersion/transverse-charge identity and the full
  shifted-Hankel tail criterion, but no Suzuki two-jet bridge or safe-shift first-minor theorem.
  Those prior results prevent claiming the determinant itself as a new positivity problem.
- Targeted arXiv searches found classical Xi/Turán, Stieltjes/Bernstein, and Hankel literature but
  no statement identifying Suzuki's literal relative tilt gap with reciprocal concavity of the
  squared-Xi safe-shift radial response, nor either positive spectral-response realization no-go.
  Absence from search is not a priority proof.
- Specialist review remains required before an external priority claim.

## Relation to the modular-superselection paper

The result supplies a new positive pre-scalar row for the admission--separation ledger. Its
observable is formed from Suzuki's literal parity energies and exponential tilt moments before
invariant scalarization. It lies outside the paper's conjunctive regular-unit-response /
finite-Rees / post-fusion no-go class.

It also strengthens the paper's anti-theatre rule. The Xi moment determinant is admitted only
after (1)--(2) derive it as the limit of the source Schur slack. Starting from `AC-B^2` and declaring
it a Suzuki interface would prove no source map.

The explicit positive-resolvent countermodel adds a second anti-theatre test: abstract operator
positivity cannot be presented as source admission, because the same axioms realize every sign of
the gate. Only an arithmetic property of Suzuki's restricted-Weil kernel can move the source into
the sharp `0<g<=1` window.

The three-point exponential countermodel closes a tempting repair of that test. Requiring a
pointwise-positive response of a positive spectral multiplier is still not source admission:
Suzuki's arithmetic center--flank correlation, not an arbitrary functional calculus of position,
must do the work.

## Lean certificate

Unconditional theorems in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiTwoJetShiftedHankelGate.lean`:

- `norm_iteratedDeriv_two_le_schurSlack`
- `real_secondJet_add_schurBoundary_nonneg`
- `suzukiAllAngleCarrier_forces_real_twoJetSlack`
- `suzukiParity_twoJetSlack_eq`
- `suzukiSchurCarrier_forces_parity_twoJetSlack`
- `suzukiAllAngleCarrier_forces_parity_twoJetSlack`
- `suzukiParity_twoJetSlack_torque_decomposition`
- `suzukiParity_twoJetSlack_surjective_at_fixed_torque`
- `suzukiParity_twoJetSlack_of_balanced_energy`
- `suzukiParity_twoJetSlack_balanced_nonneg_iff`
- `moment_twoJetSlack_eq_hankelMinor`
- `primeArchSuzuki_twoJetSlack_eq_shiftedHankelMinor`
- `primeArchSuzuki_twoJetSlack_nonneg_iff_shiftedHankelMinor_nonneg`

Unconditional theorems in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiRelativeTiltReciprocalConcavity.lean` include:

- `suzukiSecondDefectParityCurvature_eq_relativeTiltGap`
- `suzukiAllAngleCarrier_forces_relativeTiltGap_le_one`
- `primeArchSuzukiRelativeTiltGapCalibration_pos`
- `primeArchSuzukiRelativeTiltGapCalibration_eq_moments`
- `primeArchSuzukiRelativeTiltGapCalibration_le_one_iff_shiftedHankelMinor_nonneg`
- `iteratedDeriv_two_squaredXiReciprocalRadialField`
- `squaredXiReciprocalRadialField_concaveAt_one_iff_shiftedHankelMinor_nonneg`

The explicit operator realization and strengthened no-go are in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPositiveResolventParityNoGo.lean`, culminating in:

- `suzukiPositiveParityResolventModel_of_positive`
- `suzukiPositiveParityResolvent_slack_surjective_at_fixed_torque`

The stronger exponential spectral-response no-go is formalized in
`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPositiveSpectralResponseNoGo.lean`. Its capstones are:

- `suzukiThreePointResponse_sourceEquation`
- `suzukiThreePointResolvent_commutes_position`
- `suzukiThreePoint_twoJetSlack_eq`
- `suzukiThreePoint_relativeTiltGap_gt_one`

No `sorry`, `admit`, new axiom, opaque theorem, unsafe declaration, computation, or RH hypothesis
occurs.

## Log

- 2026-08-01 — exact parity and safe-shift Hankel identities derived.
- 2026-08-01 — anchored Schur force law proved unconditionally.
- 2026-08-01 — torque-only fixed-fiber surjectivity and balanced exception classified.
- 2026-08-01 — full theorem stack formalized in Lean.
- 2026-08-01 — normalized transition window and reciprocal-radial concavity connector proved.
- 2026-08-01 — positive invertible parity-resolvent class proved unable to constrain the gate.
- 2026-08-01 — literal exponential three-point positive spectral response proved to cross `g=1`.
