# Arithmetic Levinson completion-index law

- **ID:** ULF-ALCI-1
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Status:** killed by exact kernel--cokernel cancellation; family-index survivor extracted

## 0. No-go closure

- **Exact killing theorem/mechanism:** Let `S : Y -> Z` be injective and let `A : X -> Y` be
  Fredholm. Then `ker(S A) = ker A` and there is a canonical short exact sequence
  `0 -> coker A -> coker(S A) -> coker S -> 0`. For the one-defect shift `S` and
  `A_z = I + z B`, compact perturbation gives `ind A_z = 0`; hence
  `dim ker(S A_z) = g_z`, `dim coker(S A_z) = 1 + g_z`, and `ind(S A_z) = -1` for every `z`.
  The exact theta identity `det_2(A_z) = XiC(z)/XiC(0)` therefore implies that every Xi mode adds
  a matched kernel--cokernel pair without changing the source index. ALCI-3's equation
  `-1 = -(1+k)` omits the matching kernel and is false.
- **Strongest positive survivor:** Pointwise Fredholm index is the group completion of an effective
  defect pair and erases diagonal additions. The analytic family still retains each Xi mode as
  torsion of its determinant-line section, with algebraic multiplicity. Any completion index must
  be a family/local-length invariant equipped with source provenance and a no-escape theorem.
- **New insight:** A source vacuum index and a multiplicity-exact Xi determinant already coexist
  unconditionally. Their coexistence cannot constrain the divisor. The missing law is not
  cokernel exhaustion but a source restriction on the support of analytic-family torsion.
- **Status:** dependency-closed paper proof in
  `pipeline/2-fully-proven/universal-law-field/completion-index-transgression-mechanics/`
  (`vacuum-index-cancellation-determinant-torsion.md`). Lean formalization deliberately deferred
  during the current Lean-audit/no-build phase.

## 1. Big-picture interpretation

The common object is not a Lorentzian manifold and not an index-one inner-product space. It is a
source-generated **one-channel scattering extension**.

- The universal theta `(1,1)` Green block is the crossing form on incoming/outgoing boundary data.
- Horizontal grade `a = 2 Re(s)-1` is boundary rapidity; functional equation reverses it.
- An off-line pair is a resolved collision of opposite Krein signatures, hence a bound-state
  channel of the completed system.
- Krein--Langer negative squares count these bound states with analytic multiplicity.
- Roos/formation-boundary escape is failure of asymptotic completeness.
- Compact recurrence is the closed observer projection of the same open scattering history.
- Positivity is a polarization of incoming/outgoing data, not the source law.

RH is therefore the statement that arithmetic completion has no bound state beyond its universal
vacuum defect.

This interpretation corrects the false statement “one boundary line implies one index.” One scalar
channel can carry arbitrary winding and arbitrarily many bound states. Selection must come from a
source-fixed total index plus asymptotic completeness.

## 2. Corpus audit before conjecture

Search used `scripts/formal_tools.py research` on relative index, Fredholm polarization, confluent
multiplicity, boundary triples, source wave operators, completion escape, recurrence descent,
successor--dilation actions, and countermodels.

### Existing pieces

1. `HedenmalmPinnedVolterraBoundaryDefect` and
   `HedenmalmThetaStageGreenBoundaryCofinalMixedInertia` give the actual cofinal self-adjoint
   rank-two Green form with exact values `+1/6,-1/6` and fixed inertia `(1,1)`.
2. `HedenmalmThetaGreenHyperbolicGaugeNoGo` identifies its current with the boost-invariant
   rank-two source current. Euclidean polarization selects only neutral boost, but boost invariance
   itself is nonselective.
3. `SeamCollisionMechanism` proves the negative carrier vanishes exactly on the critical line and
   an off-line pair is exactly a resolved opposite-sign collision.
4. `FiniteHardyConfluentBasis` supplies independent higher Cauchy jets for every repeated root.
   `FiniteBlaschkeGeneralizedSchurKernel` and `SuzukiShiftedXiFiniteInertia` give exact
   multiplicity-aware negative-square counts.
5. `CCMArithmeticPrimeFredholmOrientation` constructs a literal one-prime Hardy Fredholm cycle of
   index `-1`, duality by adjoint, and compact-perturbation stability.
6. `ArithmeticFormationCompletionBoundaryFusion` constructs a one-line singular arithmetic
   completion boundary; every off-line Xi copy lands in it, while every on-line copy is finitely
   effective.
7. `PreDivisorTransverseRamificationRoosTransgression` identifies the same off-wall condition with
   a coefficient-faithful Roos class, but only its zero radical, not a multiplicity-exact carrier.
8. `ArithmeticFormationRecurrenceDescentFusion` identifies formation-boundary birth with failure of
   faithful compact recurrence descent.
9. `KreinEscapeAnalyticFamily` and `KreinIndexEscapeStratification` show negative index can escape to
   infinity under compact-open convergence, even with all derivatives.
10. `CountermodelCarrierHyperbolicPlane` shows the Beurling and entire-FE countermodels acquire one
    hyperbolic plane per off-line pair; arbitrarily small reciprocal mass can create such a plane.
11. `FiniteBlaschkeGeneralizedSchurKernel` also kills boundary-rank counting: a scalar carrier has
    arbitrary finite negative-square count.
12. The all-prime source rigged form has an exact one-sided Witt defect, but reflected fibres have
    arbitrarily large opposite finite inertia. Absolute global index one is false.

### External parents

- generalized boundary triples turn a Green identity into a Weyl function and extension theory;
- Fredholm--Lagrangian/Maslov theory and real spectral flow turn crossings into relative indices;
- topological Levinson theorems identify scattering winding with bound-state index;
- Toeplitz/Cuntz algebras of `N ⋊ N^×` encode successor--dilation completion and exact residue-class
  occurrence, but admit several natural boundary quotients.

These supply technology, not the arithmetic source theorem below.

## 3. Exact RH closure

For every finite symmetric height window `W`, construct from literal pre-divisor prime--Gamma and
integer-occurrence data a coefficient-faithful wave operator

`Omega_W : H_free,W -> H_arith,W`

with the following dependency-ordered laws.

### ALCI-1 — source index law

`Omega_W` is Fredholm, injective, and

`ind(Omega_W) = -1`.

The single cokernel dimension is forced by the successor boundary of ordinary integers. All prime
dilations act on this same successor history through exact residue-class occurrence; they are not
direct-summed Fredholm channels.

### ALCI-2 — arithmetic characteristic law

The boundary characteristic/Weyl function of `Omega_W` is obtained coefficient-faithfully from the
literal prime--Gamma Green source and has completed characteristic determinant equal to normalized
Xi on `W`. This statement is pre-divisor: Xi appears as the determinant of the constructed source
system, not as input eigenvalue data.

### ALCI-3 — asymptotic-completeness/exhaustion law

There is a canonical multiplicity-preserving decomposition

`coker(Omega_W) ~= V_vac,W ⊕ K_Xi,W^- ⊕ E_W`,

where

- `dim V_vac,W = 1` is the universal theta/pole vacuum;
- `K_Xi,W^-` is the confluent negative Hardy model of off-line Xi pairs in `W`;
- `E_W` is the unobserved escape channel;
- source asymptotic completeness proves `E_W = 0`.

Consequently

`-1 = ind(Omega_W) = -(1 + dim K_Xi,W^- + dim E_W)`.

Hence `dim K_Xi,W^- = 0` in every window. Exact Krein--Langer inertia gives no off-line Xi pair in
any window, therefore RH.

The proof does not ask positivity, self-adjointness, recurrence, or completion descent to select
the wall. It asks literal arithmetic to construct one complete scattering system whose already
fixed source index leaves no room for extra bound states.

## 4. Why this narrows the pre-divisor model class

Admissible sources must simultaneously satisfy:

1. exact successor occurrence on ordinary integers;
2. prime dilation acting on the same occurrence space, with the exact residue-class partition;
3. literal von Mangoldt/Gamma coefficient action;
4. one source-selected boundary extension and one fixed topology;
5. coefficient-faithful Xi characteristic formation;
6. Fredholm/gap properness and multiplicity-exact cokernel exhaustion.

Beurling generalized-prime countermodels fail ordinary-integer residue-class occurrence. Entire
FE multipliers are not generated by the fixed coefficient action. Generic hyperbolic doubling
fails chiral coefficient faithfulness. A divisor-built Hardy model fails item 5's direction of
construction.

## 5. Hostile audit

### Killed formulations

- **Absolute Pontryagin index one:** false; reflected source fibres have unbounded negative finite
  restrictions.
- **One boundary line implies one defect:** false; scalar generalized-Schur carriers have arbitrary
  negative-square count.
- **Fixed theta `(1,1)` block bounds Xi inertia:** false; finite negative spectators preserve the
  essential Toeplitz index.
- **One-prime Fredholm cycle is full arithmetic source:** false; it forgets all-prime coefficient
  incidence.
- **Generic boundary triple or Levinson theorem supplies selection:** false; it proves only the
  index dictionary after the arithmetic wave operator and completeness are given.
- **Choose the Cuntz boundary quotient:** invalid; affine-semigroup completion has several natural
  boundary quotients.
- **Compact-open convergence conserves index:** false by explicit all-jet index escape.

### Current live core

Construct the coupled successor--dilation wave operator and prove ALCI-1 before attempting the Xi
landing. Then prove ALCI-2 without divisor-defined state space. Only after both exist is ALCI-3 a
meaningful completeness theorem rather than an RH restatement.

## 6. Fourth-organ prediction

The existing formation/recurrence theorem is only binary. ALCI predicts a multiplicity-exact
refinement:

`RecurrenceNonDescent_W ~= K_Xi,W^- ⊕ E_W`.

Thus the rank of open history lost by closed prime-circle observation equals the confluent
Krein--Langer off-line multiplicity plus the escape rank. Under ALCI-3 it equals the off-line
multiplicity exactly. This prediction is not contained in the current zero-radical equivalence,
which collapses all off-line copies to one scalar boundary direction.

## 7. Falsifiers

1. Exact integer residue-class covariance forces infinite rather than unit source Fredholm index
   for every coefficient-faithful common operator.
2. Any pre-divisor common operator satisfying ALCI-1 has a characteristic function incompatible
   with the actual theta/Xi determinant.
3. The actual Xi confluent Hardy space does not inject into the completed cokernel.
4. A finite invisible Krein spectator compatible with every source relation survives in the
   cokernel, falsifying exhaustion.
5. Either corpus countermodel satisfies all six admissibility clauses.
6. Recurrence non-descent rank disagrees with finite-window off-line multiplicity.

## 8. Research order

1. Build/check the exact common successor--dilation representation and identify the unique vacuum
   defect; do not infer ALCI-1 from per-prime cycles.
2. Compare actual finite theta source operators with compressions or transfer operators of that
   representation.
3. Construct boundary maps and prove the Green identity; obtain the source Weyl/characteristic
   function.
4. Prove determinant equality with normalized Xi from coefficients.
5. Construct the cokernel-to-confluent-Hardy map and prove injectivity, surjectivity, and no escape.
6. Derive the recurrence-rank prediction.
7. Only then promote any dependency-closed theorem to Stage 2 and Lean.

## Log

- 2026-09-01 — opened after absolute index-one and boundary-dimension versions failed hostile
  audit; surviving law isolated as source index plus arithmetic asymptotic completeness.
