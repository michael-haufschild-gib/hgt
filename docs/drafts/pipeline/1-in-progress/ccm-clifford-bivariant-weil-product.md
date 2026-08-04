# CCM Clifford bivariant Weil product

- **ID:** `ccm-clifford-bivariant-weil-product`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with exact circularity obstruction and dependency-closed positive bridge
- **Parent:** `rh-current-frontier-map.md`, Route C1--CCM
- **Statement:** the two Real-odd symmetries of the exact CCM quotient have a Clifford-corrected
  composite equal to critical-line reflection; its Lefschetz coefficient is the Weil form, while
  scalar positivity requires a source-built homotopy of that composite to the identity.

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
`J` preserves it.  On the CCM test convolution algebra this composite is encoded by the modular
involution `f |-> f^sharp`.  If `L_f` denotes the integrated Lefschetz action, its Real-even
character has the Clifford correction `i L_f`; the correction of its dagger is
`-i L_(f^sharp)`.  Their two-sided product is therefore

```text
Omega_Cl(f) := (-i L_(f^sharp)) # (i L_f)
             = L_(f^sharp * f).                               (1)
```

Here `#` is composition/Yoneda product in the derived cyclic-module category; on a bornological
algebra realization it is the corresponding bivariant cyclic product.  The scalar phases cancel.
The CCM Lefschetz trace of `(1)` is the modular trace pairing.  In the multiplicity-exact divisor
realization, `f^sharp` is implemented by `J`; hence for square-summable evaluation vectors
`E(F),E(G)` its polarized numerical coefficient is

```text
<J E(G), E(F)>
  = sum_q F(alpha_q) conj(G(conj(alpha_q)))
  = Weil(F,G).                                                (2)
```

The second displayed equality is unconditional and is the exact coefficient that any CCM
bivariant realization must reproduce.  Equation `(1)` is already an all-degree cyclic-module
composition for finite Lefschetz translations and is the algebraic formula for integrated tests.
What remains to call the integrated class a bivariant *entire Chern character* is a smooth
bornological algebra model, justified integration, and required theta-summability; the
cyclic-module formula itself does not supply those analytic data.

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

## Relentless interrogation and stronger conjecture

The killing mechanism is not failure of the product.  It is the false identification

```text
Real parity correction = Hodge-sign correction.
```

The two Clifford phases disappear in `(1)`, so stabilization preserves the Witt/signature class
of `J`.  A stronger conjecture must explain why `J`, rather than merely its Clifford lift, becomes
the identity on source cohomology.

`[CONJECTURE] [CCM_CLIFFORD_PRINCIPAL_EFFECTIVITY]`

On the completed reduced CCM cyclic complex there is a source-built, scaling-equivariant bounded
odd operator `K`, defined before spectral decomposition and from the adelic restriction/Poisson
data, such that

```text
J - 1 = (b+B) K + K (b+B),                                    (3)
```

with `K` compatible with the closed restriction quotient and the Lefschetz trace domain.  The
construction is functorial under finite enlargement of places and does not use zero locations,
the Weil form, a completion by that form, or an RH-equivalent sign assumption.

This is the characteristic-zero principal-correspondence law missing in CCM 2007.  If `(3)` holds,
then `J=1` on reduced cyclic homology, and `(2)` becomes the norm square

```text
Weil(F,F) = ||E(F)||^2 >= 0,                                  (4)
```

because the trace kills `(b+B)`-boundaries.  Hence `(3)` implies RH non-circularly from a source
identity.  `[OPEN CORE]` Construct `K` and prove the boundedness, quotient descent, and trace-domain
compatibility in `(3)`.  No current corpus or audited literature supplies this operator.

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
product, not itself the positive product.  The unresolved arithmetic content is selection of the
`+` channel, equivalently `(3)`.

## Falsifiers

1. A source-defined `K` satisfying `(3)` but leaving a nontrivial `-1` eigenspace of `J` on reduced
   homology falsifies trace compatibility or the conjecture.
2. A Clifford correction which changes the scalar signature while preserving the exact coefficient
   `(2)` falsifies the phase-cancellation/Witt law.
3. A published construction of the characteristic-zero principal correspondence with the exact
   CCM quotient and trace-domain hypotheses would make the conjecture rediscovered.

## Gates

- [x] 0 -> 1: exact frontier, source-pure conjecture, hostile circularity audit
- [x] exact Clifford product and Weil coefficient on divisor/Hilbert realization
- [x] dependency-closed paper proof of the positive matrix lift
- [ ] external novelty audit of the source-homotopy conjecture after exact chain model is fixed
- [ ] construct source-only homotopy `K`
- [ ] prove smooth bornological/entire realization of the product
- [ ] 1 -> 2: complete proof of `(3)` and all analytic descent obligations
- [ ] 2 -> 3: exact unconditional Lean theorem after paper closure

## Log

- 2026-08-04 — initial positive-square conjecture killed as circular by the exact CCM/Weil
  criterion.  Clifford phases were found to cancel in the two-sided product, exposing the stronger
  source-homotopy conjecture `(3)` and the unconditional positive matrix lift `(5)`--`(6)`.
