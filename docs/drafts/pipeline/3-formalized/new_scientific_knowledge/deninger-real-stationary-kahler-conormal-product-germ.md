# Real stationary Kähler--conormal product germ

- **ID:** `deninger-real-stationary-kahler-conormal-product-germ`
- **Stage:** 3-formalized
- **Type:** SOURCE LOCAL GEOMETRY THEOREM
- **Label:** `DAC_REAL_STATIONARY_KAHLER_CONORMAL_PRODUCT_GERM`
- **Parent:** `deninger-archimedean-conormal-dual-conormal-trace-domain`
- **Statement:** A three-real-dimensional orbifold germ simultaneously
  realizes Deninger's real stationary exponent \(-2\), the
  weight-one leafwise Kähler form, the orientation-sign Hodge star,
  and the full even dual-conormal jet character.

## 1. Oriented cover and real involution

Let
\[
 \widetilde U=\mathbb C_z\times\mathbb R_r,\qquad
 z=X+iY,                                                        \tag{1}
\]
with involution
\[
 \sigma(z,r)=(\overline z,-r).                                 \tag{2}
\]
The quotient germ is
\[
 U_{\mathbb R}=\widetilde U/\langle\sigma\rangle.               \tag{3}
\]
The foliation upstairs is given by the complex planes
\(\mathbb C\times\{r\}\). The involution exchanges the leaves at
\(r\) and \(-r\), so downstairs the transverse coordinate is
\[
 x=r^2\in\mathbb R_{\ge0}.                                     \tag{4}
\]
The leaf at \(x=0\) is the preserved real quotient
\[
 L_\infty=(\mathbb C\times\{0\})/\langle\sigma\rangle
          =\mathbb C/\langle z\mapsto\overline z\rangle.        \tag{5}
\]

## 2. Flow

Define
\[
 \widetilde\phi^t(z,r)
   =(e^{t/2}z,e^{-t}r).                                        \tag{6}
\]
It commutes with `(2)` and therefore descends to \(U_{\mathbb R}\).
The point
\[
 x_\infty=[(0,0)]                                               \tag{7}
\]
is stationary, and \(L_\infty\) is preserved.

The invariant normal coordinate satisfies
\[
 (\phi^t)^*x=e^{-2t}x,                                         \tag{8}
\]
so the transverse exponent is exactly
\(\kappa_\infty=-2\).

The map
\[
 \iota_\infty:\mathbb R_{\ge0}\longrightarrow U_{\mathbb R},
 \qquad
 \iota_\infty(x)=[(0,\sqrt x)]                                 \tag{9}
\]
is a smooth orbifold map because it is induced from the equivariant
lift \(r\mapsto(0,r)\). It is transverse to the leaf distribution,
\(\iota_\infty^{-1}(L_\infty)=\{0\}\), and
\[
 \phi^t\iota_\infty(x)=\iota_\infty(e^{-2t}x).                 \tag{10}
\]
Thus `(9)` realizes Deninger's real-place transverse embedding.

## 3. Leafwise Kähler and Hodge laws

On every oriented leaf put
\[
 \omega=dX\wedge dY,\qquad
 *dX=dY,\quad *dY=-dX.                                        \tag{11}
\]
Then
\[
 (\widetilde\phi^t)^*\omega=e^t\omega.                         \tag{12}
\]
Moreover
\[
 \sigma^*\omega=-\omega,\qquad
 \sigma^**=-*\sigma^*.                                        \tag{13}
\]
Hence leaf orientation descends through the sign local system, and
the Hodge star exchanges untwisted and orientation-sign one-forms.
After coefficient conjugation, \(J=*c\) has square \(-1\) and the
usual positive Hodge density.

Equations `(8)` and `(12)` are compatible because they concern
different tangent blocks:
\[
 T_{x_\infty}U_{\mathbb R}
 \sim
 T_{x_\infty}\mathcal F
 \oplus N_{x_\infty}\mathcal F.                               \tag{14}
\]
The leaf plane has half-density weight \(+1/2\), while the transverse
line has weight \(-2\) in the orbifold coordinate \(x=r^2\).

## 4. Dual-conormal jets

For a smooth transverse germ \(f(x)\), let
\[
 j_k(f)=\frac{f^{(k)}(0)}{k!}.                                 \tag{15}
\]
By `(8)`,
\[
 j_k((\phi^t)^*f)=e^{-2kt}j_k(f).                             \tag{16}
\]
Thus the complete dual-conormal product has positive-time character
\[
 \sum_{k\ge0}e^{-2kt}
 =\frac1{1-e^{-2t}}\qquad(t>0),                               \tag{17}
\]
as proved in
`DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER`.

## 5. The theorem

`[PAPER-PROVED] [DAC_REAL_STATIONARY_KAHLER_CONORMAL_PRODUCT_GERM]`

The explicit quotient germ `(1)`--`(6)` simultaneously satisfies:

1. real dimension three;
2. a codimension-one complex-leaf foliation;
3. one stationary point `(7)` on the preserved real leaf `(5)`;
4. Deninger's real transverse orbifold and exponent \(-2\);
5. leafwise Kähler weight one;
6. forced orientation-sign Hodge descent;
7. the complete dual-conormal even-jet character `(17)`.

All assertions follow directly from `(2)`, `(6)`, the chain rule, and
the geometric series.

## 6. Relation to prior atoms

- `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX` is the preserved-leaf
  \(z\)-factor of this germ.
- `DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER` is its transverse
  \(x=r^2\)-factor.

The two factors must not be identified. The Kähler flow expands the
leaf tangent plane, while Deninger's archimedean exponent contracts
the independent transverse normal.

## 7. Boundary of the theorem

The germ does not yet prove:

- embedding into the global rational-Witt suspension;
- existence or uniqueness of a global arithmetic compactification;
- compactness/bounded geometry of the preserved leaf;
- the strong conormal/dual-conormal exact sequences globally;
- the \(b\)-trace extension at \(t=0\);
- harmonic faithfulness on \(M_\zeta\).

These remain in
`DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN`.

## Hostile audit

- No single radial coordinate is assigned both incompatible weights.
- The real involution acts simultaneously on leaf orientation and the
  square-root normal.
- The gamma density is derived from the source normal jet weights.
- No finite prime is a fixed or preserved component.
- No zeta zero, RH premise, CCM object, or numerical computation enters
  the construction.

## References

- Christopher Deninger, *A note on arithmetic topology and dynamical
  systems*, arXiv:math/0204274.
- `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX`.
- `DAC_REAL_ORBIFOLD_REES_DUAL_CONORMAL_JET_TOWER`.

## Log

- 2026-07-27 — Split the leaf half-density and transverse real Rees
  weights into independent tangent blocks and constructed their
  compatible three-dimensional stationary quotient germ.

- 2026-08-01 — Formalized the germ, its involution, its flow, the transverse
  exponent, the tangent-block dimensions and weights, the orientation-sign
  Hodge laws, and the dual-conormal character in Lean.

## Lean status

### The whole germ landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerStationaryKahlerGerm.lean`, on top of the already
formalized leaf factor (`DeningerLeafwiseKahler.lean`) and transverse factor
(`DeningerReesJetTower.lean`).  Axiom audit for all 48 declarations:
`propext, Classical.choice, Quot.sound`.

Each numbered claim of §5:

1. **Real dimension three** — `deningerGerm_finrank` : `finrank ℝ (ℂ × ℝ) = 3`.
2. **Codimension-one complex-leaf foliation** — `deningerGermLeafBlock` is the kernel of the
   transverse projection and `deningerGermLeafBlock_finrank` gives it real dimension two, by
   rank--nullity against the surjectivity `deningerGermTransverseProj_range`.
3. **One stationary point on the preserved real leaf** — `deningerGermFlow_apex` and
   `deningerGermFlow_fixed_iff` (the apex `(7)` is the *only* fixed point of the whole flow),
   `deningerGermFlow_leaf_iff` (the leaf `r = 0` and its complement are preserved),
   `deningerGermSigma_leaf` (the involution acts on the leaf by conjugation, so `(5)` is the real
   quotient), and `deningerGermSigma_fixed_iff` (the fixed locus of `(2)` is exactly the real axis
   of that leaf, so the quotient is an orbifold precisely along `L_∞`).
4. **Deninger's real transverse orbifold and exponent `-2`** — `deningerGermFlow_zero`,
   `deningerGermFlow_add` (the flow `(6)` is a one-parameter group), `deningerGermFlow_sigma` (it
   commutes with `(2)`, hence descends to `(3)`), `deningerGermTransverse_sigma` and
   `deningerGermTransverse_fiber` (`x = r²` of `(4)` is invariant and its fibres are exactly the
   involution pairs `{r, -r}`, so it is the transverse coordinate downstairs), and
   `deningerGermTransverse_flow` — **`(8)`**: the descended flow on `x` is literally
   `deningerReesFlow t`, i.e. `e^{-2t}x`.  The embedding `(9)` is `deningerGermIota`, with
   `deningerGermTransverse_iota` (it is a section of the transverse coordinate, i.e. transverse to
   the leaf distribution), `deningerGermIota_leaf_iff` (`ι^{-1}(L_∞) = {0}`),
   `deningerGermIota_injOn`, and `deningerGermIota_equivariant` — **`(10)`**.
5. **Leafwise Kähler weight one** — `deningerGermKahler_weight` : the flow scales the leafwise
   Kähler form `(11)` by `e^{t}`, i.e. `(12)`, the square of the half-density weight
   (`deningerGermLeafWeight_sq`).  The block-diagonality `(14)` is
   `deningerGermFlow_leafBlock` (on the leaf block the flow is multiplication by `e^{t/2}`)
   together with `deningerGermTransverse_flow`; the two weights are provably independent,
   `deningerGermWeight_ne` : `e^{t/2} = e^{-2t}` only at `t = 0`, which is the hostile-audit claim
   that no coordinate carries both weights.
6. **Forced orientation-sign Hodge descent** — `deningerGermSigmaOne` is the action of `(2)` on
   leafwise one-forms; `deningerGermSigmaOne_wedge` is `σ^*ω = -ω` and
   `deningerGermSigmaOne_star` is `σ^* ⋆ = -⋆ σ^*`, both halves of `(13)`.
   `deningerGermKahler_invariant_eq_zero` is the forcing: an *invariant* multiple of the Kähler
   form is zero, so the form descends only through the sign local system.
   `deningerGermStar_of_invariant` and `deningerGermStar_of_antiInvariant` are the statement that
   the star exchanges untwisted and orientation-sign one-forms.  `deningerGermJ`,
   `deningerGermJ_sq`, `deningerGermJ_pos` and `deningerGermJ_pos_of_ne` are `J = ⋆c` with
   `J² = -1` and the strictly positive Hodge density.
7. **The complete dual-conormal even-jet character `(17)`** — `deningerGermPullback` (the
   transverse pullback along the germ flow is the Rees pullback in the coordinate `x`),
   `deningerGermJet_flow` (**`(16)`** in the germ's own weight vocabulary) and
   `deningerGermJetTower_character` (**`(17)`**), the last two resting on the already formalized
   `deningerRealJet_reesFlow` and `deningerJetTower_tsum`.

### Remaining

Nothing for the germ.  The six clauses of §7 — global embedding into the rational-Witt suspension,
existence and uniqueness of a global arithmetic compactification, compactness of the preserved
leaf, the global conormal/dual-conormal exact sequences, the `b`-trace extension at `t = 0`, and
harmonic faithfulness on `M_ζ` — are explicitly outside this theorem and stay with
`DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN`.
