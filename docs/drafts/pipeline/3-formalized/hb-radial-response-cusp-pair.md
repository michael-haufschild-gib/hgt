# HB: scalar-tested cusp data for radial response work

- **ID:** HB-RRCP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [source-contact attack](../1-in-progress/hb-source-contact-spin-two-balance.md)
- **Predecessor:** [original radial response work](hb-incoming-radial-response-work.md)

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source
→ physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact source-work identity

Fix an actual Xi occurrence q. Use the original full half-square Q, its complete
three-power principal part Q0, and the original cutoff chi. Let A and B be the
constructed full angular responses. For any literal scalar test psi, including
the actual physical angular test, let P be its principal part. Define

```
T_A  = (psi Q-chi P Q0)A,
T_B  = (psi Q-chi P Q0)B,
T_QQ = psi Q²-chi P Q0².
```

All three functions belong to L1 of the actual native quotient measure. This
uses the complete scalar test, squared source and angular responses. No decay,
integrability, boundary cancellation or field-equation premise is supplied by
the caller.

Write the already derived original incoming SV-SV work coefficient as

```
W = rs alpha QA+rt beta QB+CQQ Q².
```

At every height y>3, its width-one horizontal mean is exactly

```
mean(psi W)
 = P Q0[rs alpha M_A+rt beta M_B]+CQQ P Q0²
   +rs alpha mean(T_A)+rt beta mean(T_B)+CQQ mean(T_QQ).
```

Here each M is the actual full response mean. With the branch-specific roots
r_minus and r_plus and their original gap, the formula is

```
M(y) = K_particular(y)+y^r_minus C_minus
       +[y^r_minus integral_y^infinity F_plus(t)dt
          -y^r_plus integral_y^infinity F_minus(t)dt]/gap.
```

K_particular is the actual three-power particular cusp response. C_minus is the
native limiting coefficient, and both F integrals contain the complete forcing
tails. The earlier native-energy theorem sets the growing homogeneous
coefficient to zero; it does not set C_minus to zero. Both branch coefficients
are retained in W's mean.

## Closed source proof

The literal Fourier source gives every complex height-weighted bound for the
square remainder and scalar Fourier tail. Splitting the full scalar into its two
Weyl powers and full tail gives every weighted L2 bound for psi(Q-chi Q0).
Continuity controls the compact part of the quotient. The native residual of
each actual angular response is in L2. Hölder therefore admits its product with
these source remainders without changing the complex-bilinear pairing.

On the original fundamental domain, the remaining response is chi times a
fixed three-power particular solution. Each power shifts the available weight,
so this part also pairs absolutely. This proves admission of the first term in

```
T_A = psi(Q-chi Q0)A+chi(psi-P)Q0 A.
```

The second term uses the same response admission and the original three-power
expansion of Q0. The proof for B uses the other constructed branch, with its own
parameters and native coefficient.

For T_QQ the source's six-slot quartic jet theorem already admits
psi(Q²-chi Q0²). The difference chi(psi-P)Q0² is admitted through the complete
five-power quartic principal expansion. That expansion retains all ordered
products of the original three source powers. No term is removed by parity or
an assumed clock symmetry.

Above height three the cutoff is one, and all principal parts are independent
of the horizontal coordinate. Integral linearity gives the displayed mean
identity. Substitution of the independently constructed native mean formula
retains C_minus and both infinite forcing integrals on each branch.

## Extinction interface still open

This is an identity for one actual incoming SV-SV radial work coefficient. The
original response-work theorem places it alongside two angular divergences and
retains the horizon onset endpoint and derivative-clock energy. This leaf does
not evaluate the height periods or those divergences' full boundary action.

The complete independent SS/SV/VV assembly, solved ++/+- corrections, changing
metric weights, and horizon, characteristic and source-contact contributions
must still identify an actual left-QNM action with a source-derived vanishing
quantity. In particular, native L2 selection cannot be used to discard the
remaining homogeneous coefficients or their weighted left-test periods.

For the established transduction C=-Sigma E_clock, Sigma>0 and E_clock>=0, a
source-derived complete-action estimate Re(C)>=0 would force E_clock=0. A sharp
balance with a remainder bounded by kappa Sigma E_clock for a fixed kappa<1
would also suffice. Neither estimate follows from the present complex-bilinear
cusp decomposition. No fixed finite physical-clock invariance is asserted.

## Search and validation

Deep corpus retrieval for full angular response/source products returned native
L2 response, cusp flux reconstruction and physical source-pairing candidates.
Hybrid/method retrieval for quartic scalar remainders located the existing
six-slot admission. Both searches reported partial coverage or pending compiler
metadata; actual source statements were inspected and applicability was checked
in the proof. Generated ingredient sets were not treated as proofs.

The proof is in
[ThetaCuspHawkingBMQuarticResponseCuspPair.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQuarticResponseCuspPair.lean),
namespace `RHTower.D4BMQuarticResponseCuspPair`. Its eleven public theorems and
four definitions are wired into the RHTower umbrella once.

`lake env lean /tmp/hb-quartic-response-cusp-pair.lean` passed without diagnostics.
The proof uses explicit continuity composition, source expansions and typed
integral linearity. No heartbeat, recursion-depth or transparency override is
present. Final
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticResponseCuspPair`
passed without warnings in 18 seconds against cached imports, with the exact
source hash `afb5b3652aeb0d89c1dadbab23a6cdd167af8454dd7d9c2390478a9f57488771`.
No dependency or umbrella build ran.

Index regeneration registered all fifteen public declarations. Whole-tree
`scripts/formal_tools.py lint --check-generated` remains non-green: five other
worktree modules are unreachable (`ThetaCuspHawkingBMHorizonModeOuterUniformBound`,
`ThetaCuspHawkingBMTemporalCurrentClearedDensity`,
`ThetaCuspHawkingBMTemporalCurrentClearedDensityBound`, `JetCoefficientUniqueness`,
and `SecondEndpointMellinLaurentInterchange`), and `LEAN_OVERVIEW.md` became stale
after regeneration during concurrent work. No error names the new leaf. Its
source hash, single umbrella import and cached build artifacts were verified;
all Lean processes started for this leaf have finished.
