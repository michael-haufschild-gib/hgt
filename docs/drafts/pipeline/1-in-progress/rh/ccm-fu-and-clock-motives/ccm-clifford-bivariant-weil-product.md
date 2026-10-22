# CCM Clifford bivariant Weil product

- **ID:** `ccm-clifford-bivariant-weil-product`
- **Stage:** 1-in-progress
- **Type:** FALSIFIED principal-effectivity conjecture with dependency-closed positive bridge
- **Parent:** `rh-current-frontier-map.md`, Route C1--CCM
- **Statement:** the source modular sharp and the spectral critical-line reflection are different
  typed operations; the proposed complex-linear homotopy between reflection and the identity is
  impossible on nonzero complex homology, while the Clifford matrix lift remains positive.

## Goal

Construct the product requested by the Real-corona/CCM route without treating parity correction as
Hodge positivity.  Identify the first source-only statement whose proof would turn the exact Weil
coefficient into a positive square and hence prove RH.

## Internal frontier

- `[CORPUS]` `KRealHom.cliffordTransgression` in
  `formal/GaloisForLFunctions/RHTower/KRealCyclicCliffordTransgression.lean` multiplies a Real-even
  all-degree cyclic morphism by `i`, producing the required anti-Real parity.
- `[CORPUS]` `realCoronaP2_no_bivariantChernRealization_eq_lefschetz` and
  `realCoronaP2_cliffordTransgression_eq_i_lefschetz` in
  `formal/GaloisForLFunctions/RHTower/RealCoronaFourProblemsResolution.lean` prove the exact Real
  parity obstruction and its Clifford survivor on the closed rational CCM quotient.
- `[CORPUS]` `inner_xiWeilLineConjLp_evaluation_eq_polarization` in
  `formal/GaloisForLFunctions/RHTower/XiWeilLineConjHilbert.lean` identifies the Weil polarization
  unconditionally with the Hilbert coefficient of critical-line reflection.
- `[CORPUS]` `riemannHypothesis_iff_xiWeilPolarization_nonneg` in
  `formal/GaloisForLFunctions/RHTower/XiWeilPositivityCriterion.lean` proves that nonnegativity on
  the complete square-summable divisor domain is exactly RH.
- `[LOCAL-RESEARCH]` `rh-current-frontier-map.md` records the remaining C1--CCM core as a positive
  bivariant/intersection trace pairing on the exact closed quotient, identified with Weil.

## External frontier

- `[LITERATURE]` Connes--Consani--Marcolli, *The Weil proof and the geometry of the adeles class
  space*, Proposition 6.2 and Corollary 6.3, identify RH for Grossencharacter L-functions with
  positivity of the CCM trace pairing `Tr(W(f*f*))`; their Section 7 leaves the characteristic-zero
  analog of principal correspondences open: <https://arxiv.org/abs/math/0703392>.
- `[LITERATURE]` Perrot's bivariant JLO character and equivariant index theorem construct cup
  products in bivariant entire cyclic theory under bornological/summability hypotheses, but supply
  no arithmetic Hodge sign: <https://arxiv.org/abs/math-ph/0103016> and
  <https://arxiv.org/abs/math/0410315>.
- `[LITERATURE]` Voigt constructs a multiplicative equivariant Chern--Connes character in local
  cyclic homology; multiplicativity does not make a Lefschetz trace positive:
  <https://arxiv.org/abs/math/0608609>.
- `[LITERATURE]` Connes--Consani--Moscovici's 2025 zeta spectral triples obtain self-adjoint finite
  operators; rigorous convergence of their spectra/determinants to the zeta zeros/Xi is stated as
  the missing implication which would establish RH: <https://arxiv.org/abs/2511.22755>.

## The modular involution and the exact product

Use the centered spectral coordinate `z=-i(s-1/2)`.  On the complete multiplicity divisor let

```text
S z = -z                 (functional equation),
R z = -conj(z)           (Schwarz Real structure),
J z = conj(z) = S R z    (critical-line reflection).
```

`S` and `R` commute.  Both reverse the upper/lower Real-corona orientation, while their composite
`J` preserves it.  A hostile typing audit exposes a distinction suppressed in the original
conjecture:

```text
source sharp:   F(z) |-> conj(F(conj z))       conjugate-linear, holomorphic;
spectral J:     E(F)(q) |-> E(F)(lineConj q)  complex-linear divisor reindexing.
```

The first is the actual source operation formalized by `XiWeilSourceInvolution.lean`.  The second
is the fundamental symmetry formalized by `XiWeilLineConjHilbert.lean` and
`GaussHodgeWeilFundamentalSymmetry.lean`.  The apparent test-function action
`F(z) |-> F(conj z)` is anti-holomorphic unless `F` is constant, so it is not an endomorphism of
the holomorphic CCM test category.

If `L_f` denotes the integrated Lefschetz action, the source sharp still supports the formal
Clifford-corrected product

```text
Omega_Cl(f) := (-i L_(f^sharp)) # (i L_f)
             = L_(f^sharp * f).                               (1)
```

Here `#` is composition/Yoneda product in the derived cyclic-module category; on a bornological
algebra realization it is the corresponding bivariant cyclic product.  The scalar phases cancel.
But passing from the source-sharp product to the spectral `J` coefficient is now an explicit
comparison obligation, not a typing identity.  Once such a landing has been supplied, the
multiplicity-exact divisor coefficient is

```text
<J E(G), E(F)>
  = sum_q F(alpha_q) conj(G(conj(alpha_q)))
  = Weil(F,G).                                                (2)
```

The displayed divisor equality is unconditional.  Identification of `(1)` with it is not.  Any
CCM bivariant realization must construct the source-to-spectral comparison as well as the smooth
bornological model, justified integration, and required theta-summability.

## First conjecture and hostile verdict

`[CONJECTURE] [CCM_CLIFFORD_POSITIVE_WEIL_PRODUCT]`

There is a source-defined positive dagger trace on the exact closed CCM quotient such that, for
every admissible scaling test `f`, the positive bivariant square of the Clifford-corrected class
has numerical value `Weil(f,f)`.

**Verdict: `CIRCULAR` as stated.**  By `(2)` and the exact Weil criterion, positivity for every
test implies RH; under RH the divisor realization is an ordinary Hilbert square.  Calling the
trace positive therefore assumes precisely the missing Hodge sign unless its positivity is
derived from an independently constructed arithmetic chain homotopy or effectivity theorem.
Perrot/Voigt multiplicativity, Clifford/Morita invariance, self-adjoint finite truncations, and
completion in the Weil norm do not provide that input.

## Relentless interrogation and falsified stronger conjecture

The killing mechanism is not failure of the product.  It is the false identification

```text
Real parity correction = Hodge-sign correction.
```

The two Clifford phases disappear in `(1)`, so stabilization preserves the Witt/signature class
of `J`.  A stronger conjecture must explain why `J`, rather than merely its Clifford lift, becomes
the identity on source cohomology.

`[FALSIFIED] [CCM_CLIFFORD_PRINCIPAL_EFFECTIVITY]`

On the completed reduced CCM cyclic complex there is a source-built, scaling-equivariant bounded
odd operator `K`, defined before spectral decomposition and from the adelic restriction/Poisson
data, such that

```text
J - 1 = (b+B) K + K (b+B),                                    (3)
```

with `K` compatible with the closed restriction quotient and the Lefschetz trace domain.  The
construction is functorial under finite enlargement of places and does not use zero locations,
the Weil form, a completion by that form, or an RH-equivalent sign assumption.

The displayed equation is not a well-typed source conjecture.  There are two readings, and both
fail before any boundedness or trace-domain question.

1. If `J` means source modular sharp, then `J-1` is conjugate-linear while `(b+B)K+K(b+B)` is
   complex-linear for a complex-linear odd homotopy `K`.
2. If `J` means spectral divisor reindexing, it is born only after divisor evaluation and has no
   pre-divisor endomorphism on the holomorphic test complex.

Allowing a real-linear `K` does not repair the proposal.  A homotopy would make source sharp the
identity on homology.  For any class `x`, conjugate-linearity gives

```text
sharp(i*x) = -i*sharp(x),
```

whereas the identity gives `i*x`.  Thus `sharp=id` on complex homology forces `2i*x=0`, hence
`x=0`.  The retained prime class is nonzero, so no such principal-effectivity homotopy exists on
the intended reduced homology.

Had `(3)` existed, it would have made `J=1` on reduced cyclic homology and turned `(2)` into

```text
Weil(F,F) = ||E(F)||^2 >= 0,                                  (4)
```

because the trace kills `(b+B)`-boundaries.  That implication explains why the false conjecture
looked attractive; it does not rescue it.

**Strongest positive survivor.**  Source modular sharp remains a valid conjugate-linear Real
structure, and the spectral `J` remains a valid complex-linear fundamental symmetry.  The positive
product must therefore come from a comparison/compression or intersection form carrying source
sharp to the fixed spectral polarization; it cannot come from homotopy-trivializing either
involution.  This is exactly the enlarged Gate-II/Route-R positive-polar handoff.

## Dependency-closed positive survivor

`[PAPER-PROVED] [CLIFFORD_MATRIX_LIFT] [BRIDGE]`

Let `H` be a complex Hilbert space, let `J` be a self-adjoint unitary, and let `a in H`.  Put

```text
T_a(lambda,mu) = lambda a + mu (i J a),
G_Cl(a) = T_a* T_a,
Gamma = [[0,i],[-i,0]].
```

Then `G_Cl(a)` is positive and

```text
G_Cl(a) = [[||a||^2, i Q_J(a)],[-i Q_J(a),||a||^2]],
Q_J(a) = <J a,a> in R,
(1/2) Tr(Gamma G_Cl(a)) = Q_J(a).                             (5)
```

Writing `P_plus=(1+J)/2` and `P_minus=(1-J)/2`, the two eigenvalues of `G_Cl(a)` are

```text
||a||^2 + Q_J(a) = 2 ||P_plus a||^2,
||a||^2 - Q_J(a) = 2 ||P_minus a||^2.                         (6)
```

Thus the Clifford lift is unconditionally positive and its Clifford numerical coefficient is
exactly the Weil form, but scalar Weil positivity is the additional dominance
`||P_minus a|| <= ||P_plus a||`.  On the full Xi evaluation domain that dominance is equivalent
to RH.  Matrix positivity cannot be advertised as Weil positivity.

### Proof

`J*=J` gives `<Ja,a>=<a,Ja>` and therefore `Q_J(a)` is real; unitarity gives `||Ja||=||a||`.
Expanding the Gram matrix of `a` and `iJa` gives `(5)`, and every Gram matrix is positive.
The orthogonal projections `P_plus,P_minus` diagonalize `J`; Pythagoras gives `(6)`.  The trace
calculation in `(5)` is direct.  No positivity of `Q_J` is used.

This bridge is the strongest honest unconditional survivor of the failed positivity claim.  It
changes the representation: Weil is an indefinite Clifford coefficient of a positive matrix
product, not itself the positive product.  The unresolved arithmetic content is a source-to-spectral
comparison or compression selecting the `+` channel; `(3)` is no longer an admissible formulation.

## Falsifiers

1. A complex-linear source endomorphism realizing spectral `J` on nonconstant holomorphic tests
   would falsify the typing obstruction and must exhibit its action explicitly.
2. A Clifford correction which changes the scalar signature while preserving the exact coefficient
   `(2)` falsifies the phase-cancellation/Witt law.
3. A published construction of the characteristic-zero principal correspondence with the exact
   CCM quotient and trace-domain hypotheses would make the conjecture rediscovered.

## Gates

- [x] 0 -> 1: exact frontier, source-pure conjecture, hostile circularity audit
- [x] exact Clifford product and Weil coefficient on divisor/Hilbert realization
- [x] dependency-closed paper proof of the positive matrix lift
- [x] source-sharp/spectral-`J` typing audit
- [x] dependency-closed no-go for complex-linear and real-linear homotopy repairs
- [ ] prove smooth bornological/entire realization of the product
- [ ] construct the surviving source-to-spectral comparison/compression
- [ ] 2 -> 3: exact unconditional Lean theorem after paper closure

## Log

- 2026-08-04 — initial positive-square conjecture killed as circular by the exact CCM/Weil
  criterion.  Clifford phases were found to cancel in the two-sided product, exposing the stronger
  source-homotopy conjecture `(3)` and the unconditional positive matrix lift `(5)`--`(6)`.
- 2026-08-11 — hostile typing audit falsified `(3)`: source sharp is conjugate-linear, spectral
  `J` is a post-evaluation complex-linear reindexing, and real-linear homotopy trivialization would
  kill every nonzero complex homology class.  Positive matrix lift retained; comparison/compression
  handoff survives.  Lean corpus remained read-only during refactor.
