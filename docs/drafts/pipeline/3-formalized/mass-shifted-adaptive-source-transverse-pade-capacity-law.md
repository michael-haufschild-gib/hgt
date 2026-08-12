# Mass-shifted adaptive source-transverse Padé capacity law

- **ID:** `mass-shifted-adaptive-source-transverse-pade-capacity-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE PRODUCER / EXACT NO-GO CORRECTION
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `mass-shifted-adaptive-null-gauge-source-law`,
  `mass-shifted-hard-edge-gauss-node-jet-residue-law`
- **Retires:** `mass-shifted-hard-edge-root-spread-bandwidth-rigidity`

## Result

Let `P` be current degree-`N` admitted polynomial, `x != 0` one root, and `y` current mass. Put

```text
u = x⁻¹-y,
S(U) = (y+U)^N P((y+U)⁻¹),
T(U) = ReverseEuler(y,2N+2,S(U)^2).
```

`T` is exactly reciprocal clearing of actual adaptive bilinear/completed `P^sharp` source before
scalar arithmetic aggregation. Then

```text
T(u) = 0,
T'(u) = -2*x⁻¹*S'(u)^2.
```

Define endogenous transverse source capacity

```text
C_source(y,N,P,x) = -(x/2) T'(u) = S'(u)^2 >= 0.
```

It is strictly positive at every simple hard root. Clearing derivative obeys

```text
x^N S'(u) = -x^2 P'(x).
```

For Gauss weight `lambda`, absolute Padé residue `rho=lambda/x`, and finite hard terminal mass

```text
Gamma = y*x^4*lambda*P'(x)^2,
```

the exact source-capacity law is

```text
rho * [y*x^(2N+1)*C_source] = Gamma.
```

Thus

```text
rho = Gamma / EffectiveSourceCapacity
```

whenever effective capacity is nonzero. This is admission-sensitive and source-first: polynomial,
hard root, degree weight, and completed source change together before any reflection scalar is
read. It is neither fixed linear reporting nor an orientation Boolean.

## Conjecture -> proof/failure loop

1. **Affine Gauss-root spread prices hard compactness — FALSIFIED.** Bounded reciprocal roots all
   map to affine roots tending to `1`; affine spread collapse is compatible with every nonzero hard
   limit.
2. **Use reciprocal root spread instead — INSUFFICIENT.** Unweighted reciprocal levels retain hard
   positions but discard Christoffel/terminal mass. A negative hard root with zero terminal mass
   may be invisible.
3. **Padé residue is independent extra data — FALSIFIED.** Exact source derivative law makes its
   denominator an actual completed-source capacity.
4. **Source sign at root excludes positive-axis pole — FALSIFIED.** Every positive simple Gauss
   node has the same negative source slope; this is local transversality, not absolute endpoint
   exclusion.
5. **Positive survivor.** Residue, terminal divided-root mass, and adaptive completed-source
   transverse capacity satisfy one exact multiplicative conservation law.

## Higher universal principle

Previous obstruction was a coordinate shadow. Affine hard-edge roots are nonproper observations
of reciprocal root geometry. Correct conserved object is not root variance but a three-factor
source law:

```text
absolute pole visibility * adaptive source transversality = divided-root terminal mass.
```

Finite faces remain observations. Faithful hard information reappears only after reciprocal
clearing and differentiation of source producer at its admission-selected zero.

## Exact remaining obstruction

Compact-normalized capacity is now proved to converge to the nonzero divided-root derivative square
at every simple normalized hard root, so capacity divergence is removed from generic branch.
Subsequent worldline/source conservation identifies **relative** terminal mass `Gamma/h_n` as
inverse hard-root mobility inside a positive chamber: on parabolic schedule, relative mass times
actual hard speed equals `4*n*w^3*x^2`. This gives no floor for absolute `Gamma` at a flat face,
where `h_n=0`. Flat-contact source transmutation instead proves first-order hard-root freeze and
moves arithmetic forcing into higher norm-flux/contact jets. Route closure still requires either
positive-axis Padé-atom extinction in positive terminal-mass branch or exploitation of
parity-doubled radical in zero-mass branch. RH is not claimed.

## Lean realization

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedHardEdgeAdaptiveSourceTransversality
```

Principal capstones:

```text
xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal_eq_zero
xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal_eq_zero
derivative_xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal
xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq
pow_mul_derivative_xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal
xiShiftedHardEdgeGaussPadeResidue_mul_effectiveSourceCapacity_eq_terminalMass
xiShiftedHardEdgeGaussPadeResidue_eq_terminalMass_div_effectiveSourceCapacity
xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_pos
xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity_pos
affineHardEdgeCoordinate_sub_affineHardEdgeCoordinate
```

Successor module:

```text
GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw
```

## Verification

- direct `lake env lean` check: passed;
- umbrella import: present;
- targeted `lake build` passed (`11757/11757`);
- eleven capstone axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
