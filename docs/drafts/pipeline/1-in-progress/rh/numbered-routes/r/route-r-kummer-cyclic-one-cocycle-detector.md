# Route R Kummer cyclic one-cocycle detector

## Status

Stage 3 — KCC-1 through KCC-6 formalized; one explicit Gamma-naturality square remains;
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

## Conjecture KCC-5 — proved: corrected coefficient-faithful multiplier cycle

Let `a` be the canonical retained Bruhat coefficient in the unitized multiplier core.  The
normalized coinvariant potential

`b_p = (p^-1 dot a) a - 1`

satisfies the exact source identity

`p dot b_p - b_p = a (p dot a) - a (p^-1 dot a)`.

The right side is the Hochschild boundary of the raw decorated prime tensor.  The left side is the
boundary of `U_p tensor b_p U_(p^-1)`.  Their difference is therefore a genuine Hochschild
one-cycle retaining the actual Bruhat coefficient.  Its raw term has zero scalar Kummer value,
while the normalized correction has value `log p`; consequently the corrected class has value
`-log p` and is nonzero in genuine `HH_1`.

Multiplying its descended regulator by the first nonzero Xi jet gives a homological Xi landing
equal, on the corrected class, to the established signed Kummer landing.  Thus cycle existence,
Bruhat coefficient fidelity, prime retention, and Xi non-erasure are all closed.  Remaining burden
is no longer a comparison-existence theorem: it is the source-native law forcing the fixed
physical Hodge/Bockstein port to annihilate this explicit nonzero landed class.

## Conjecture KCC-6 — proved: faithful central-Bockstein cap and Gamma-parity reduction

Cap the corrected multiplier `HH_1` class into the genuine retained rational-adelic relative
`H^1` class using three literal factors: Kummer regulator, first nonzero Xi jet, and fixed physical
Hodge-mate coefficient `K_(p,rho)`.  The independent period-one Stokes regulator reads the cap as

`K_(p,rho) * L_(p,rho)`

with `L_(p,rho) != 0`.  Hence this explicit central-Bockstein cap is null-homologous if and only if
`K_(p,rho)=0`; no injectivity assumption on a large comparison space is needed.

Functional-equation reflection contributes Xi-jet parity `(-1)^m`, while `K` is reflection-odd.
Therefore the physical cap obeys the unconditional *opposite-parity* law

`B_(p,sigma rho) = -(-1)^m B_(p,rho)`.

If the pre-divisor comparison fixes the same source orientation in both Gamma fibres, its
naturality square is

`B_(p,sigma rho) = (+1)(-1)^m B_(p,rho)`.

The two laws are compatible exactly when `B_(p,rho)=0`, equivalently `K_(p,rho)=0`, equivalently
the fixed same-fibre norm/source-dagger law.  Globally at one prime, this *fixed-orientation*
naturality square is equivalent to RH.  It is an exact candidate producer, but source orientation
must be audited rather than silently identified.

## Conjecture KCC-7 — falsified: ordinary source dagger does not fix orientation

Genuine degree-one cyclic reversal preserves the corrected Hochschild-cycle condition and flips
its Kummer period from `-log p` to `+log p`.  The resulting reversed homology class is provably
distinct from the original class.  When functional-equation reflection transports this genuine
source dagger, its Kummer minus sign cancels the Hodge-mate minus sign, giving unconditionally

`B_(p,sigma rho; dagger z_p) = (-1)^m B_(p,rho; z_p)`.

Therefore ordinary Gamma/dagger naturality is compatible with every horizontal grade and cannot
annihilate `K`.  KCC-6's RH-bearing same-class parity would require erasing the genuine source
orientation, contradicted by the nonzero Kummer period.  Functional-equation reflection is not the
missing independent law.

## Conjecture KCC-8 — open producer

Construct a same-fibre, fixed-source-orientation law independent of functional-equation transport.
It must annihilate the explicit cap class while preserving the nonzero corrected multiplier and
relative Stokes periods.  Equivalently, it must place the fixed physical lift in the harmonic corona
graph without identifying the two distinct Gamma-oriented source classes.  Resolved `D1 D0 = 0`,
ordinary source dagger, defect data, cyclic rotation, and coefficient non-erasure are now all
formally ruled out as substitutes.

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
- [x] construct normalized Bruhat coinvariant potential and cancel raw Hochschild boundary;
- [x] prove corrected decorated class is nonzero in genuine `HH1`;
- [x] land corrected class on first nonzero Xi jet and identify signed Kummer landing;
- [x] cap corrected multiplier class into retained relative `H1` and prove Stokes faithfulness;
- [x] prove exact opposite physical Gamma parity and reduce source parity to `K = 0`;
- [x] hostile-test source rotation; prove reversed class is distinct and dagger naturality is blind;
- [ ] construct independent same-fibre fixed-orientation annihilation law;
- [x] wire modules into `RHTower.lean`;
- [ ] direct Lean check, targeted module build, lint, and axiom audit.

Lean modules:

- `RouteRKummerCyclicOneCocycleDetector.lean`
- `RouteRSignedKummerCyclicCartierLanding.lean`
- `RouteRPrimeChainHochschildCycleWall.lean`
- `RouteRPreDivisorRationalAdelicMultiplierKOneHomology.lean`
- `RouteRPreDivisorRationalAdelicCorrectedMultiplierXiLanding.lean`
- `RouteRCorrectedMultiplierGammaOrientationDescent.lean`

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

## Necessary spectral condition on any admissible target (2026-08-05)

`GaloisForLFunctions.RHTower.hasEigenvalue_primeLog` — a ℂ-linear multiplicative `f` satisfying the
two intertwining identities forces `+log p` and `-log p` into the point spectrum of the target
derivation `D_B`, with eigenvectors the images of the two legs of the ordinary-prime atom (nonzero
by `primeAtom_not_erased`).

`GaloisForLFunctions.RHTower.not_module_finite_of_comparison` — the images of the forward legs are
linearly independent (distinct eigenvalues), so no finite-dimensional target can receive the
comparison.

Practical test for candidate targets: **the target derivation must already carry
`{+/- log p : p prime}` in its point spectrum.** Finite-rank models, and any operator whose point
spectrum misses a prime logarithm, are excluded before construction. Non-vacuity is certified by the
identity comparison (`cyclicSource_not_module_finite`).

Card: `docs/drafts/pipeline/3-formalized/route-r-comparison-prime-log-spectrum-obligation.md`.

## KCC-9 — paper-proved: prime-log essential cap normal form

Put

\[
 a_\rho=2\Re\rho-1,\qquad
 K_{p,\rho}=a_\rho\frac{(1-p^{-1})(2-p^{-1})}{2\log p},
\]

and let `B_(p,rho)` be KCC-6's explicit central-Bockstein cap.  Its
period-one Stokes readout contains the corrected multiplier Kummer period
`-log p`.  Therefore the nondivisive, coefficient-faithful prime-log port

\[
 \mathcal P_{p,\rho}:=-2\,\operatorname{Stokes}_p(B_{p,\rho})
\]

satisfies the exact identity

\[
 \boxed{\mathcal P_{p,\rho}
   =a_\rho(1-p^{-1})(2-p^{-1})c_\rho},
 \qquad c_\rho=\XiC^{(m_\rho)}(w_\rho)\ne0.       \tag{EC1}
\]

Along the canonical increasing enumeration of the ordinary primes,

\[
 \mathcal P_{p,\rho}\longrightarrow 2a_\rho c_\rho.                \tag{EC2}
\]

Thus infinite-rank transport does not disperse the cap.  It removes the
local `1/log p` attenuation and leaves one constant essential-corona class.
Since `c_rho != 0`, cofinal fixed-orientation singular Stokes flatness
`P_(p,rho) -> 0` is equivalent to `a_rho=0`, hence annihilates the original
cap at every prime.  This is strictly stronger than another pointwise zero
test: it proves that every admissible singular law has only one possible
global output channel, the constant essential scalar `2 a_rho c_rho`.

Hostile audit:

1. Ordinary source reversal cannot supply flatness; it flips the nonzero
   Kummer period and preserves the transported cap by KCC-7.
2. A `c0` or compact correction cannot cancel `(EC2)` off centre, because
   the correction vanishes while the essential scalar does not.
3. Declaring unrestricted product-topology tails to be boundaries is
   coefficient-unfaithful: it also erases the period-one Stokes detector.
4. The still-open producer is now exactly the source theorem
   `P_(p,rho) -> 0`; the algebraic implication from that law to cap nullity
   is dependency-closed and unconditional.
