# Route R Kummer cyclic one-cocycle detector

## Status

Stage 3 — KCC-1 through KCC-4 formalized; coefficient-faithful Xi comparison remains open;
final audit pending.

## Frontier

Route R's current scalar residue reads the retained prime chain but is not a Hochschild
one-cocycle: it does not kill general degree-two boundaries.  Therefore ordinary Hochschild or
mixed-complex null-homology cannot yet be transported to the explicit physical Bockstein.

## Conjecture KCC-1

Let `A = S(A_Q) ⋊_alg Qx` be the exact nonunital rational-adelic crossed product, `A+` its minimal
unitization, and `epsilon0` the zero-adele trace.  For a scaling label `q`, put

`ell(q) = log |q|`.

Coefficientwise multiplication by `ell` defines a derivation

`partial_ell(a U_q) = ell(q) a U_q`.

The bilinear functional

`phi_ell(x0,x1) = epsilon0(x0 * partial_ell(x1))`

is a cyclic Hochschild one-cocycle.  On the retained ordinary-prime atom `u_p U_p tensor
u_p U_(p^-1)` it has value `-log p`, hence is nonzero for every ordinary prime.

## Paper proof

Additivity `ell(qr)=ell(q)+ell(r)` and the crossed-product multiplication rule give

`partial_ell(xy)=partial_ell(x)y+x partial_ell(y)`

first on monomials and then by finite-support bilinearity.  Since `epsilon0` reads only the
identity-scaling coefficient, `epsilon0(partial_ell x)=0`.  Trace cyclicity and Leibniz imply

`phi_ell(a,b) = -phi_ell(b,a)`

and, for every pure degree-two Hochschild boundary,

`phi_ell(ab,c)-phi_ell(a,bc)+phi_ell(ca,b)=0`.

For the prime/inverse-prime tensor, `ell(p^-1)=-log p` and the previously proved zero-adele product
trace is one.

## Route-R consequence

This supplies the missing boundary-compatible source detector, not the final annihilation.  A
strict coefficient-faithful Cartier comparison carrying this cocycle to the fixed Xi physical
residue would turn source null-homology of the central Bockstein into

`(g_p(rho)-1) * c_rho * log p = 0`.

All other factors are independently nonzero, so that comparison would force `g_p(rho)=1` and
close Route R.  Exact remaining producer is therefore narrower: construct the all-degree
source-to-Xi comparison and prove it preserves `phi_ell`; degree-one rotation compatibility is
insufficient.

## Conjecture KCC-2 — proved

The correct cyclic receiver of `phi_ell` is signed: quotient degree-one chains by `tau + 1`, not
the unsigned `tau - 1` relation used by the symmetric product trace.  Adjoin the image of the full
alternating Hochschild boundary `d0 - d1 + d2`.  Antisymmetry kills `tau + 1`; the cocycle law
kills the full linear Hochschild boundary.  Therefore `phi_ell` descends to this joint quotient.

The retained prime class remains nonzero because its descended regulator is `-log p`.  Pairing
with the first nonzero Xi jet gives a boundary-compatible coefficient

`L_(p,rho) = -log(p) * c_rho != 0`.

Its physical mate-dilation defect is exactly

`(1 - g_(p,rho)) * L_(p,rho)`

and also exactly `-log(p)` times the established source Cartier/central-Bockstein defect.  Hence
its vanishing is equivalent to `K_(p,rho)=0`.  This constructs the missing non-erasing,
boundary-compatible landing; remaining theorem is specifically annihilation of this explicit
landed physical defect, not existence or faithfulness of a detector.

## Hostile cycle test KCC-3 — original atom fails

The retained tensor is not a Hochschild one-cycle.  Its degree-one boundary is the crossed-product
commutator

`(u_p U_p)(u_p U_(p^-1)) - (u_p U_(p^-1))(u_p U_p)`.

At identity scaling, the two Bruhat coefficients are `u_p * (p dot u_p)` and
`u_p * (p^-1 dot u_p)`.  Evaluation at real coordinate `1` and finite adele `0` gives the common
nonzero factor `gauss(1)` times respectively `gauss(p^-1)` and `gauss(p)`.  Strict injectivity of
the real exponential and `p > 1` prove inequality.  Therefore the signed Kummer quotient retains
a boundary-compatible chain class, not yet a homology class.

Strongest survivor: genuine source homology must add a singular relative correction cancelling
this explicit commutator, or use a genuine multiplier/K1 prime-dilation cycle and separately prove
coefficient-faithful comparison to the Bruhat-decorated Xi landing.  Any proof calling the current
two-leg tensor null-homologous without this correction is invalid.

## Conjecture KCC-4 — proved: genuine multiplier K1 homology carrier

Let `B` be the actual rational-adelic Bruhat coefficient core, `B+` its unitization, and

`M = B+ rtimes Qx`

the unital rational-scaling multiplier crossed product.  Rational dilation gives a genuine unit
`u_q in M^x`; therefore

`z_p = u_p^(-1) tensor u_p`

has Hochschild boundary `u_p^(-1)u_p - u_pu_p^(-1) = 0`.  On the full cyclic bar, the alternating
maps satisfy `b_1 b_2 = 0`, so `z_p` defines an honest `HH_1(M)` class.

Scalar augmentation `B+ -> C` and the identity on `Qx` induce an algebra homomorphism from `M` to
the rational dilation group ring.  Pulling back the logarithmic Kummer cocycle gives a Hochschild
one-cocycle which kills the full range of `b_2` and evaluates

`[z_p] |-> log p != 0`.

Thus `[z_p]` is nonzero in genuine Hochschild-one homology and cannot be a degree-two boundary.
This repairs KCC-3's exact chain defect.  It does **not** yet identify the undecorated multiplier
unit cycle with the Bruhat-decorated Xi physical landing: scalar augmentation deliberately forgets
the Bruhat coefficient.  Remaining hard theorem is a coefficient-faithful relative/Cartier
comparison carrying this genuine class to the existing nonzero Xi landing, followed by an
independently source-derived annihilation law.

## Hostile tests

1. Product-formula cancellation alone fails: it cancels finite and archimedean components only as
   a pair and does not kill the fixed physical component.
2. Existing product residue fails: it reads a nonzero degree-two boundary at `(1,1,1)`.
3. An arbitrarily adjoined target primitive fails coefficient faithfulness.
4. KCC-1 is falsified if `partial_ell` fails Leibniz on a crossed-product monomial, if `phi_ell`
   reads a pure Hochschild boundary, or if its prime-atom value vanishes.

## Lean gates

- [x] construct logarithmic weight and prove multiplicative additivity/inverse law;
- [x] construct nonunital and unitized derivation;
- [x] construct tensor one-cocycle;
- [x] prove cyclic antisymmetry and degree-two boundary annihilation;
- [x] prove exact nonzero ordinary-prime pairing;
- [x] construct signed cyclic/Hochschild quotient and descended prime regulator;
- [x] construct coefficient-faithful Xi landing and identify exact physical Bockstein defect;
- [x] compute degree-one Hochschild boundary and prove retained decorated atom is not a cycle;
- [x] construct actual Bruhat-core unitization and rational-scaling multiplier crossed product;
- [x] construct genuine prime K1 cycle and prove its degree-one boundary is zero;
- [x] prove full multiplier chain law `b1 b2 = 0`;
- [x] descend Kummer regulator to genuine `HH1` and prove retained prime class is nonzero;
- [x] wire modules into `RHTower.lean`;
- [ ] direct Lean check, targeted module build, lint, and axiom audit.

Lean modules:

- `RouteRKummerCyclicOneCocycleDetector.lean`
- `RouteRSignedKummerCyclicCartierLanding.lean`
- `RouteRPrimeChainHochschildCycleWall.lean`
- `RouteRPreDivisorRationalAdelicMultiplierKOneHomology.lean`

## Producer narrowed by the defect-blindness law (2026-08-05)

The remaining producer — "construct the all-degree source-to-Xi comparison and prove it preserves
`phi_ell`" — is now known to be *necessarily* phase-level.

`GaloisForLFunctions.RHTower.not_exists_phaseDefect_criterion_adelicScaling` proves that no
predicate on coboundary-defect data over `CCMRationalAdelicScaling` is equivalent to triviality of
a character twist, and `adelicLogPowerCharacter_eq_one_iff` shows the character group of that
scaling group is faithfully parametrised by `s |-> (q |-> s * log |q|)`, faithful because
`log p != 0` for every ordinary prime.

So weakening the requirement "the comparison preserves `phi_ell`" to "the comparison preserves the
coboundary defect of `phi_ell`" is provably dead: the defect is invariant under the very twist that
carries `Re rho`. The comparison obligation cannot be discharged by matching reciprocity data,
Stokes boundary defects, or product-formula gains; it must carry the cocycle itself.

Card: `docs/drafts/pipeline/3-formalized/adelic-phase-defect-character-blindness-law.md`.

## Producer reduced to two intertwining identities (2026-08-05)

KCC-1 and KCC-2 are now corollaries of a universal law, and the comparison obligation has an exact
reduction.

`[CORPUS]` `GaloisForLFunctions.HTGeometry.traceDerivCocycle_boundary` and
`traceDerivCocycle_antisymm_iff` — for any associative ring with additive trace `tau` and additive
derivation `D`, the form `phi(a,b) = tau(a * D b)` kills every degree-two Hochschild boundary, and
antisymmetry holds **iff** `tau (D (a*b)) = 0` for all `a,b`. The KCC-1 hypothesis was therefore
exactly cyclicity, not a model accident.

`[CORPUS]` `GaloisForLFunctions.RHTower.primeAtom_not_erased` — for ANY target ring `B` with trace
`tau_B` and derivation `D_B`, and any additive multiplicative `f` from the cyclic source with

```text
D_B . f = f . partial_ell        and        tau_B . f = epsilon_0,
```

both legs of the retained ordinary-prime atom survive `f`, and `primeAtom_transported_value` gives
the transported cocycle value exactly `-log p`.

Consequence: the requirement "coefficient-faithful on the ordinary-prime top atom" is **not** an
independent gate; it is implied by the two intertwining identities. The exact remaining producer is
now: exhibit a target `(B, tau_B, D_B)` reading the fixed Xi physical residue together with a
multiplicative additive `f` satisfying those two identities. Read together with
`adelic-phase-defect-character-blindness-law`, the comparison must transport the phase itself, and
once it does, non-erasure is free.

Card: `docs/drafts/pipeline/3-formalized/trace-derivation-cyclic-cocycle-transport-law.md`.
