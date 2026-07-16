# Before There Was Time: Kähler reconstruction of the holographic horizon scheme

- **ID:** `kaehler-holographic-horizon-scheme-reconstruction`
- **Stage:** 3-formalized
- **Type:** GENERAL PRINCIPAL-SYMBOL THEOREM / SCHEME RECONSTRUCTION / HYPERTRANSCENDENCE HORIZON
- **Scientific status:** `[LEAN-PROVEN] [NOVELTY PROVISIONAL] [SIGNIFICANCE DEPENDS ON FULL REALIZATION PACKAGE]`
- **Paper lane:** *Before There Was Time: Holographic Universality of Hypertranscendence Horizons*

## Statement

Let `K` be a field, let `c_i` be finitely many law coordinates, and let

```text
I = (P_j) subset K[c_i]
```

be an arbitrary finite homogeneous terminal law ideal.  For a depth-`d` free ordered-word packet,
let `J_K` be the scalar maximal-minor ideal underlying the top universal Kähler wedge of the jet
packet.  Put

```text
m = (c_i),
T = 0 + 1 + ... + (d-1) = d(d-1)/2.
```

Then

```text
J_K = m^T I.                                               (1)
```

The actual Kähler coefficient ideal in the universal jet algebra is exactly the constant-
polynomial base change of `(1)`.  If

```text
Sat_m(J) = sup_n (J : m^n),
```

then

```text
Sat_m(J_K) = Sat_m(I).                                    (2)
```

Consequently the Kähler principal symbol intrinsically recovers the saturated external horizon
ideal.  The factor `m^T` is the complete algebraic residue of the lower free jet layers.
Moreover, for any two finite homogeneous law packets (even with different equation-index types),
their saturated external ideals are equal if and only if the saturated scalar Kähler/minor ideals
of their free pretemporal realizations are equal.  Thus the realization is faithful on saturated
projective horizon schemes, not merely surjective onto their point sets.

## General theorem underneath the realization

For any commutative coefficient ring and any polynomial packet `f_1,...,f_n`, every coordinate of

```text
d f_1 wedge ... wedge d f_n
```

in the canonical exterior Kähler basis is the corresponding maximal Jacobian minor.  Hence the
Kähler coefficient ideal is exactly the maximal-Jacobian-minor ideal.  For a universal linear
packet with scalar coefficient matrix `M`, the Kähler ideal is the base change of the scalar
maximal-minor ideal of `M`.

If row `i` of `M` lies in an ideal `I_i`, every maximal minor lies in `product_i I_i`.  For disjoint
row blocks the inclusion is an equality.  In the ordered-word packet, row `r` generates `m^r` and
the final row generates `I`, giving `(1)`.

## Physical interpretation `[CONJECTURE]`

The affine cone vertex `c=0` is the state in which no law direction has yet been selected.  The
universal factor `m^T` is a finite thickening concentrated at that pre-directional state.  Power
saturation removes exactly this vertex residue and leaves the external horizon scheme.  This is a
precise mathematical meaning for “before there was time”: not an earlier clock value, but the
scheme-theoretic point before a direction of propagation exists.

No theorem here identifies the law space with a physical QFT, black-hole horizon, cosmology, or
many-worlds model.  A physical application must independently construct the observable algebra,
law derivations, locality/positivity constraints, and the terminal ideal.

There is also exact bulk nonuniqueness.  For one fixed coordinate horizon, the depth-`n+2` free
realizations have pairwise distinct affine Kähler/minor ideals but identical saturated horizon
schemes for all `n`.  Boundary reconstruction is faithful for the law scheme while discarding an
infinite family of pretemporal vertex thickenings.  This is the unconditional algebraic content of
the “many worlds behind one horizon” language; nonuniqueness of representatives under saturation
is classical and is not itself the novelty claim.

## Novelty and anti-theatre gate

Kähler differentials, Jacobian minors, Fitting ideals, determinantal loci, and saturation are
classical.  None is claimed as new.  The candidate new content is their exact occurrence in the
varying-derivation hypertranscendence realization: the complete differential-algebraicity horizon
of one observable can be prescribed by an arbitrary finite homogeneous ideal, while the intrinsic
Kähler symbol recovers its saturated scheme and records the discarded affine vertex with the
universal exponent `d(d-1)/2`.

Realization universality has close parent theories in quiver Grassmannians, support/rank varieties,
linear determinantal presentations of projective schemes, and formally integrable PDE symbols.
The literature audit has not located the combined one-observable varying-derivation
hypertranscendence statement.  This is an absence-of-hit verdict, not a priority claim.  The result
becomes Fields-scale only if the commuting/prolonged classification and consequences survive the
parent-theory audit.

## RH impact

Arbitrary saturated projective horizon ideals occur in the free noncommuting realization.  Horizon
scheme geometry alone therefore cannot select the zeta or completed-`L`-function law.  Any RH
application must use arithmetic, commutativity/integrability, positivity, or source constraints
that exclude generic free realizations.

## Lean surface

- `GeneralKaehlerPrincipalSymbol.lean`
  - `polynomialKaehlerWedge_coordinate`
  - `polynomialKaehlerCoefficientIdeal_eq_jacobianMinorIdeal`
  - `universalLinearJetKaehlerCoefficientIdeal_eq_map_minorIdeal`
- `BlockKaehlerPrincipalSymbol.lean`
  - `universalLinearJetMinorIdeal_le_prod_rowIdeals`
  - `blockDiagonalLinearJetMinorIdeal_eq_prod_rowIdeals`
  - `blockDiagonalLinearJetKaehlerCoefficientIdeal_eq_map_prod_rowIdeals`
- `FreeKaehlerHorizonScheme.lean`
  - `pretemporalPrincipalLowerRowIdeal`
  - `pretemporalPrincipalFinalRowIdeal`
  - `pretemporalPrincipalRowIdealProduct`
  - `freePretemporalPrincipalMinorIdeal_eq_generalPrincipalSymbolIdeal`
  - `freePretemporalPrincipalKaehlerCoefficientIdeal_eq_map_generalPrincipalSymbolIdeal`
  - `freePretemporalPrincipalMinorIdeal_saturation`
  - `freePretemporalPrincipal_saturatedScheme_eq_iff`
- `IdealPowerSaturation.lean`
  - `idealPowerSaturation_pow_mul`
- `ManyWorldsHolographicNonuniqueness.lean`
  - `pretemporalVertexThickness_strictMono`
  - `hyperplaneBulkPrincipalIdeal_saturation_independent`
  - `hyperplaneBulkPrincipalIdeal_pairwise_distinct`
  - `hyperplane_holographic_manyWorlds`

All declarations are theorem-valued and unconditional.  Targeted module builds pass.  The axiom
surface is restricted to standard Lean quotient/extensionality principles.
