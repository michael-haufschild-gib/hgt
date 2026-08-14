# Route P differentiable unit-frame overlap no-go

- **ID:** `route-p-differentiable-unit-frame-overlap-no-go`
- **Label:** P-G164
- **Stage:** 1-in-progress
- **Type:** THEOREM / CATEGORY-WIDE NO-GO / POSITIVE SURVIVOR
- **Lean:** scratch-checked, axiom-audited, umbrella-wired in current working tree
- **RH status:** open

## Conjecture attacked

After P-G163 excluded differentiable scalar Halmos defect completions, try to
avoid scalarization by realizing the fixed-node Xi phase as a matrix
coefficient of two differentiable unit source paths:

```text
||x(a)||=||y(a)||=1,
x(0)=y(0),
<x(a),y(a)>=Phi_(1/2)(a).
```

This is the largest fixed-coefficient unitary-source repair left by P-G163:
both source and observer frames may move independently.

## Result

The conjecture fails exactly.  For arbitrary complex Hilbert space and two
differentiable unit paths meeting at zero,

```text
Re d/da <x(a),y(a)>|_(a=0)=0.                 (P-G164.1)
```

Both tangent vectors lie in the real tangent hyperplane of the unit sphere;
their overlap can change only in phase at first order.  The actual Xi phase
obeys

```text
Phi'_(1/2)(0)=-r_Xi(1/2),
not-RH  ==> Re r_Xi(1/2)>0.                  (P-G164.2)
```

Therefore

```text
differentiable unit-frame overlap realization of Phi_(1/2)
  ==> RiemannHypothesis.                     (P-G164.3)
```

Under false RH no such pair has finite derivatives at zero.

## Heavy conjecturing loop verdict

1. **Conjecture:** pre-scalar unitary paths repair square-root Halmos
   singularity.
2. **Hostile test:** differentiate each unit norm and then their common-base
   overlap.
3. **Failure:** source geometry forces zero radial overlap jet, while the Xi
   phase has strictly negative radial jet under false RH.
4. **Pivot:** do not represent the strict-right scalar phase as any unitary
   coefficient.  Work with the division-free graph-normal difference before
   the right-factor quotient.  Any successful incidence must have genuine
   first-order norm exchange between causal and anti-causal blocks, with
   cancellation visible only in the joint conserved source—not separately
   unit causal frames.

## Big-picture principle

P-G162--P-G164 are three faces of one jet-order law:

```text
first-order dissipative scalar loss
  cannot be converted by differentiable unitary completion
  into second-order positive Ward curvature.
```

Scalar contraction leaves linear slack; its orthogonal defect is
square-root scale; moving unit frames have no radial linear jet at all.
Thus the repeated obstruction is not lack of dilation machinery.  It is a
contact-order mismatch between the scalar right-factor phase and the
source-level division-free graph.

## Formalization

`formal/GaloisForLFunctions/RHTower/RoutePDifferentiableUnitFrameOverlapNoGo.lean`
proves:

- `re_overlap_deriv_eq_zero_of_unit_paths`;
- `riemannHypothesis_of_differentiable_unitFrame_scalarXiPhase`;
- `no_differentiable_unitFrame_scalarXiPhase_of_not_rh`.

All three were checked with `lake env lean` against scratch `.olean` output.
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]`.
Targeted forbidden-token scan is clean.  No project or umbrella build was
run.

## Positive survivor and next falsifier

Survivor: source-native incidence must transport the unquotiented

```text
GraphNormal_sigma - TrueComplement_sigma
```

as an off-diagonal vector block.  It may become scalar only after the
causal/anti-causal first jets cancel in one conserved form.  Immediate
falsifier for every proposed Gamma/Sonin construction:

- if it realizes `Phi_(1/2)` as overlap of differentiable unit vectors,
  P-G164 says it is already RH-equivalent;
- if it completes the scalar phase by a differentiable orthogonal defect,
  P-G163 says the same;
- if it uses only scalar contractivity, P-G162 shows linear slack hides the
  quadratic Ward toll.

Exact next construction problem: identify an indefinite or two-channel
conserved source form whose individual blocks exchange linear mass but whose
joint first variation vanishes, then prove its second variation lands on the
P-G160 Hardy block with P-G161 mass coefficient.
