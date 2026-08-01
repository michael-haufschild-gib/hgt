# Hilbert--Kummer radial suspension realizes the Poisson dilations

- **ID:** `deninger-hilbert-kummer-radial-flow-poisson`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Labels:** `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`,
  `DAC_DENINGER_FLOW_POISSON_DILATION`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** the Hilbert-bounded modulus characters in Deninger's
  generic rational-Witt character space form a canonical dense,
  Frobenius-stable refinement on whose suspension the norm of the
  logarithmic Kummer character is a global radial coordinate; discrete
  flow pullbacks are exactly Meyer's dilations.
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerArithmeticPoissonTransfer`
  (`(11)`--`(14)`),
  `GaloisForLFunctions.RHTower.DeningerArithmeticHilbertKummerRadius`
  (`(6)`, `(8)`, `(9)` in operator-norm form),
  `GaloisForLFunctions.RHTower.DeningerFiniteExtension`,
  `GaloisForLFunctions.RHTower.DeningerHilbertKummerCharacter`
  (the density proof of `(7)`, the exponent form of `(8)`, and the
  descent and positivity of `(9)`),
  `GaloisForLFunctions.RHTower.DeningerHeightZeroKummer`
  (the height-zero theorem, the injectivity of `(2)`, and `(4)` ⟹ `(5)`),
  `GaloisForLFunctions.RHTower.DeningerKummerPlaceIsometry`
  (the place isometry `‖f_α‖₁ = 2h(α)` behind `(1)`--`(2)`),
  `GaloisForLFunctions.RHTower.DeningerArchimedeanBaseChange`,
  `GaloisForLFunctions.RHTower.DeningerFinitePlaceBaseChange`,
  `GaloisForLFunctions.RHTower.DeningerFinitePlaceSumBaseChange`,
  `GaloisForLFunctions.RHTower.DeningerPlaceRestriction`,
  `GaloisForLFunctions.RHTower.DeningerHeightBaseChange`,
  `GaloisForLFunctions.RHTower.DeningerAbsoluteHeight`
  (the gluing of the place tower and the absolute height on `Q̄`)

## Source Hilbert space

Let
\[
 \mathcal G=\overline{\mathbb Q}^{\times}/\mu_\infty
\]
and let \(Y\) be the Allcock--Vaaler place space.  For
\(\alpha\in\overline{\mathbb Q}^{\times}\), put
\[
 f_\alpha(y)=\log\lVert\alpha\rVert_y,\qquad
 H_{\rm Kum}=L^2(Y,\lambda).
                                                               \tag{1}
\]
The map
\[
 \iota:\mathcal G\otimes_{\mathbb Z}\mathbb Q
       \longrightarrow H_{\rm Kum},\qquad
 [\alpha]\longmapsto f_\alpha                                  \tag{2}
\]
is injective and has dense real span.  Injectivity follows from the
height-zero theorem; density is the \(p=2\) theorem of
Allcock--Vaaler.

A generic Deninger point is represented by a multiplicative character
\[
 P:\overline{\mathbb Q}^{\times}\longrightarrow\mathbb C^\times .
\]
Its logarithmic modulus
\[
 L_P([\alpha])=\log|P(\alpha)|                                  \tag{3}
\]
is a well-defined \(\mathbb Q\)-linear functional on
\(\mathcal G\otimes\mathbb Q\).  Call \(P\)
**Hilbert--Kummer bounded** if
\[
 |L_P([\alpha])|\le C\lVert f_\alpha\rVert_2                    \tag{4}
\]
for some \(C\) and every \(\alpha\).  In that case `(2)`--`(4)` give
a unique bounded functional
\[
 \ell_P\in H_{\rm Kum}',\qquad
 \ell_P(f_\alpha)=L_P([\alpha]),                                \tag{5}
\]
and define the canonical radius
\[
 r(P)=\lVert\ell_P\rVert_{H_{\rm Kum}'}\ge0.                    \tag{6}
\]

## Hilbert--Kummer refinement theorem

`[PROVED HERE] [DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION]`

Let \(\check X_{\rm HK}\) be the Hilbert--Kummer bounded generic
character locus, equipped with the operator-norm topology on `(5)`
together with pointwise topology on the unitary part.

1. \(\check X_{\rm HK}\) is stable under Deninger's Galois and positive
   rational Frobenius actions.
2. Its map
   \[
   \alpha_{\rm HK}:\check X_{\rm HK}\longrightarrow
   \check X_{\rm Den}(\mathbb C)_\eta                         \tag{7}
   \]
   to the pointwise-topologized generic rational-Witt character space
   is continuous and has dense image.
3. For every \(q\in\mathbb Q_{>0}\),
   \[
   r(F_qP)=q\,r(P),                                             \tag{8}
   \]
   and \(r(P^\sigma)=r(P)\) after the corresponding unitary Galois
   transport on \(H_{\rm Kum}\).
4. On the suspension
   \[
   X_{\rm HK}
   =\check X_{\rm HK}\times_{\mathbb Q_{>0}}\mathbb R_{>0},
   \]
   the formula
   \[
   x([P,u])=u\,r(P)                                             \tag{9}
   \]
   is a well-defined continuous function.  It is positive precisely
   off the unitary locus \(r(P)=0\).

### Proof

For Frobenius, Deninger's exact character formula is
\[
 F_qP=P\circ(\,\cdot\,)^q.
\]
Therefore
\[
 L_{F_qP}([\alpha])
 =\log|P(\alpha^q)|
 =qL_P([\alpha]).
\]
This proves boundedness and `(8)`.  Galois permutes \(Y\) and preserves
\(\lambda\), hence acts unitarily on \(H_{\rm Kum}\); `(5)` then proves
Galois stability and invariance of the norm.

The refined topology makes every evaluation
\(\ell\mapsto\ell(f_\alpha)\) continuous, so `(7)` is continuous.
For density, fix a character \(P\) and finitely many
\(\alpha_1,\ldots,\alpha_m\).  The restriction of \(L_P\) to
\[
 W=\operatorname{span}_{\mathbb R}
   \{f_{\alpha_1},\ldots,f_{\alpha_m}\}
\]
is a linear functional.  Finite-dimensional Riesz representation and
orthogonal extension give a bounded
\(\ell_W\in H_{\rm Kum}'\) with
\(\ell_W(f_{\alpha_j})=L_P([\alpha_j])\) for all \(j\).
Keep the unitary character \(P/|P|\) and replace only its modulus by
\(\exp(\ell_W(f_\alpha))\).  The resulting Hilbert--Kummer bounded
character agrees with \(P\) on the prescribed finite set.  This proves
pointwise density.  The replacement does not alter the character on
roots of unity, so it preserves Deninger's admissibility condition on
the torsion kernel.

Deninger's deck relation is
\[
 (P,u)\cdot q=(F_qP,q^{-1}u).                                   \tag{10}
\]
Equations `(8)` and `(10)` give
\[
 (q^{-1}u)r(F_qP)=q^{-1}u\cdot qr(P)=ur(P),
\]
proving descent of `(9)`.  Continuity holds in the refined topology by
construction.

## Exact Poisson-flow theorem

`[PROVED HERE] [DAC_DENINGER_FLOW_POISSON_DILATION]`

Deninger's flow is
\[
 \phi^t[P,u]=[P,e^tu].
\]
Consequently
\[
 x(\phi^t[P,u])=e^t x([P,u]).                                   \tag{11}
\]
At the discrete time \(t=\log n\),
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u],                             \tag{12}
\]
because applying the deck transformation \(n\) to \((P,nu)\) gives
\((F_nP,u)\).

For any function \(f:\mathbb R_{>0}\to\mathbb C\), set
\[
 A_f=f\circ x
\]
on the nonunitary locus.  Pullback along `(12)` is
\[
 (\phi^{\log n})^*A_f
 =A_{D_nf},\qquad
 (D_nf)(x)=f(nx).                                                \tag{13}
\]
Hence, on Meyer's right-decaying Schwartz domain where his sum
converges in \(H_-\),
\[
 \sum_{n\ge1}(\phi^{\log n})^*A_f
 =A_{Zf},\qquad
 (Zf)(x)=\sum_{n\ge1}f(nx).                                     \tag{14}
\]

Thus every summand of Meyer's Poisson--zeta differential is an
ordinary scalar **flow pullback** on the Hilbert--Kummer radial
suspension.  It is not a pullback by the deck map `(10)`: deck
pullback is the identity on descended functions.

## Relation to local Kummer coordinates

For one algebraic Kummer coordinate \(a\), put
\[
 r_a(P)=-\log|P(a)|.
\]
The exact identities
\[
 r_a(F_nP)=nr_a(P),\qquad
 r_{ab}=r_a+r_b,\qquad
 r_{a^m}=mr_a,\qquad
 r_\zeta=0\quad(\zeta\in\mu_\infty)                              \tag{15}
\]
show that the local logarithmic collar is the evaluation of the global
functional `(5)` at \(f_a\).  Formula `(6)` removes the noncanonical
choice of \(a\): it is the operator norm of the entire Kummer
functional, not one coordinate.

The earlier punctured-disk identity
\[
 -\log|z^n|=n(-\log|z|)
\]
is the one-coordinate restriction of `(8)`.

## Exact consequence for the relevant complex

The individual Poisson terms no longer require a conjectural
coefficient-valued transfer.  The remaining comparison work is:

1. sheafify the Hilbert--Kummer refinement `(7)` and compute
   \(R\alpha_{\rm HK,*}\) on the coarse Deninger suspension;
2. prove that the radial Schwartz domain is exactly Meyer's
   \(H_\cap\), including the two real endpoint conditions;
3. prove normal convergence and strict closed range of `(14)` in the
   global nuclear topology;
4. show that angular/nonradial derived directions are acyclic in the
   relative middle summand;
5. transport cup, trace, flow, and the Kähler/Hodge operator through
   the resulting quasi-isomorphism.

The topology refinement is essential.  The norm `(6)` need not be
continuous for Deninger's coarse pointwise topology.  It is continuous
on \(\check X_{\rm HK}\), and `(7)` is precisely the kind of
true-to-approximate map for which Deninger proposed a relevant complex
\(R\alpha_*\mathcal G\).

## Hostile audit

- No zeta zero, RH, CCM object, or numerical computation enters the
  construction.
- `(14)` uses flow pullback, not deck pullback.
- Density of `(7)` does not imply that its derived pushforward is
  trivial or that nonradial directions are acyclic.
- The bare \(L^2\) completion is not declared arithmetic cohomology;
  the mixed \(L^1/L^2\), nuclear, residue, and endpoint structures
  remain necessary.
- Positivity on the Kummer Hilbert source is not yet positivity on
  Meyer's generalized-zero quotient; that requires the Hodge
  comparison.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  the character formula for \(F_q\), the suspension relation, and the
  flow in §6:
  https://arxiv.org/abs/1807.06400
- Daniel Allcock and Jeffrey D. Vaaler,
  *A Banach space determined by the Weil height*:
  https://arxiv.org/abs/0808.1038
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, Definition 3.1 and Theorem 3.3:
  https://arxiv.org/abs/math/0412277

## Log

- 2026-07-27 — Constructed the canonical dense Hilbert--Kummer
  refinement and proved that Deninger's discrete flow pullbacks are
  exactly the Poisson dilation semigroup.

### The exact Poisson-flow theorem is formalized

`formal/GaloisForLFunctions/RHTower/DeningerArithmeticPoissonTransfer.lean`, verified and
extended.  Axiom audit: `propext, Classical.choice, Quot.sound`; two of the identities need only
`propext` (and `Quot.sound`).

- `deningerSuspensionLogRadius_flow` — **`(11)`**: the flow scales the descended radius.
- `deningerRawDeckMap_flow_eq_frobenius_fixedHeight` — **`(12)`**: applying the `n`-deck map after
  the raw time-`n` flow is Frobenius at fixed height, so `[F_nP, u]` and `φ^{log n}[P,u]` have the
  same image in the suspension quotient.
- `deningerDiscreteFlowPullback_eq_dilation` — **`(13)`**: discrete flow pullback on a radial
  section is Meyer's dilation `f(x) ↦ f(nx)`.
- `deningerMeyerSum` and `deningerPoissonSum_eq_meyerSum` — **`(14)`**: summing the discrete flow
  pullbacks over positive times gives the radial section of Meyer's summation operator.  The
  identity is termwise, each summand being `(13)`, so no convergence hypothesis is needed to state
  it: both sides are the same series.
- `deningerSuspensionLogRadius_deck_invariant` and, in operator-norm form,
  `deningerHilbertKummerRadius_smul` and `deningerHilbertKummerSuspensionRadius_deck_invariant` —
  the radius scaling `(8)` and the descent of `x` to the quotient `(9)`.

The earlier "direct check deferred" note is superseded: both modules pass `lake env lean` with no
errors and no warnings, their cached builds complete, and they are imported by the
`GaloisForLFunctions.RHTower` umbrella.

### Remaining

The analytic inputs of the refinement theorem: injectivity and dense span of `(2)`, which rest on
the height-zero theorem and Allcock--Vaaler, and the Hilbert--Kummer boundedness `(4)` that
produces the functional `(5)`.  Those are quoted results about the place space, not identities of
the flow.

### The refinement theorem's proof mechanism is formalized

`formal/GaloisForLFunctions/RHTower/DeningerFiniteExtension.lean` and
`formal/GaloisForLFunctions/RHTower/DeningerHilbertKummerCharacter.lean`.  Axiom audit on all
seventeen declarations: `propext, Classical.choice, Quot.sound`.

**Bounded extension off a finite-dimensional subspace.**

- `deningerFiniteDimExtend` — every linear functional on a finite-dimensional subspace `W` of an
  inner-product space is the restriction of a *continuous* functional on the whole space.  A
  finite-dimensional subspace is complete, hence has an orthogonal projection, and a linear map on
  a finite-dimensional space is automatically continuous; the extension is
  `l ∘ proj_W`.  This is the card's "finite-dimensional Riesz representation and orthogonal
  extension".
- `deningerFiniteFamilyExtend` — the finite-family form, on the span of `f_{α_1},…,f_{α_m}`.

**Characters, their logarithmic modulus, and the Frobenius scaling law.**

- `deningerChar_ne_zero`, `deningerChar_norm_pos` — a `ℂ`-valued character of a *group* never
  vanishes, so `L_P(a) = log ‖P a‖` is everywhere defined.  This is what makes the whole
  logarithmic-modulus calculus unconditional: no nonvanishing hypothesis is needed.
- `deningerLogModulus_mul` — `L_P` is additive.
- `deningerLogModulus_zpow` — `L_P(a^n) = n L_P(a)` for every `n ∈ ℤ`.
- `deningerLogModulus_ratPow` — **the exponent form of `(8)`**: if `b^m = a^k` with `m ≠ 0`, so
  that `b` is the rational power `a^{k/m}`, then `L_P(b) = (k/m) L_P(a)`.  This is
  `r(F_q P) = q r(P)` for positive rational `q`, proved from the integer power law alone.
- `deningerLogModulus_torsion`, `deningerChar_norm_torsion` — a character has modulus one on
  roots of unity, so `L_P` vanishes on the torsion kernel.

**Modulus replacement.**

- `deningerUnitPart`, `deningerUnitPart_norm` — the unitary part `P/|P|`, a character of modulus
  one.
- `deningerModulusReplace`, `deningerModulusReplace_mul` — keeping the unitary part and installing
  a new *additive* logarithmic modulus again produces a character.
- `deningerModulusReplace_norm` — the replacement has exactly the prescribed modulus.
- `deningerModulusReplace_eq_self` — it agrees with `P` wherever the new modulus was prescribed to
  be the old one.
- `deningerAdditive_torsion` — an additive real-valued function kills torsion (`ℝ` is
  torsion-free).
- `deningerModulusReplace_torsion` — **the admissibility check**: the replacement is *equal* to
  `P` on every root of unity, so it preserves Deninger's condition on the torsion kernel.  The
  card asserted this; it is now proved.

**The density step `(7)`.**

- `deningerHilbertKummer_pointwise` — given a character `P` whose logarithmic modulus is computed
  by an a priori *unbounded* linear functional `φ` along the Kummer class map `f`, and any finite
  family `α_1,…,α_m`, there is a genuinely *bounded* `L ∈ H_Kum'` such that `L ∘ f` is additive
  and the modulus replacement built from `L` is a character agreeing with `P` at every `α_i`.
  Proof: restrict `φ` to the span of the `f_{α_i}`, extend boundedly by
  `deningerFiniteDimExtend`, and replace the modulus.  Together with
  `deningerModulusReplace_torsion` this is the card's pointwise density argument in full.

**The suspension value function `(9)`.**

- `deningerSuspensionValue_descent` — if the radius scales by `q` under Frobenius, then
  `u · r(P)` is invariant under the deck relation `(P,u) ↦ (F_q P, q^{-1} u)`, so `x([P,u])` is
  well defined.  This is `(8)` + `(10)` ⟹ descent, isolated from the model.
- `deningerSuspensionValue_pos` — `u · r(P) > 0` exactly off the unitary locus `r(P) = 0`.

### The height-zero theorem and `(4)` ⟹ `(5)` landed

`formal/GaloisForLFunctions/RHTower/DeningerHeightZeroKummer.lean`.  Axiom audit on all four
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerMulHeightOne_iff_isOfFinOrder` — **the height-zero theorem** (Kronecker's theorem in
  height form): a nonzero element of a number field has multiplicative height `1` exactly when it
  is a root of unity.  Forward direction: by the power law `H(x^n) = H(x)^n` all powers of a
  height-one element lie in the Northcott set `{y | H(y) ≤ 1}`, which is finite, so two powers
  coincide and cancellation in the field gives `x^{q-p} = 1`.  Backward direction: `H(x)^n = 1`
  with `H(x) > 0` forces `H(x) = 1`.  This was the card's quoted input; it is now proved from
  mathlib's Northcott property alone.
- `deningerLogHeightZero_iff_isOfFinOrder` — the logarithmic form, `h(α) = 0 ⟺ α ∈ μ_∞`.
- `deningerKummerClass_eq_zero_iff` — **injectivity of `(2)`**: if `‖f_α‖ = c·h(α)` with `c > 0`,
  then `f_α = 0` exactly for roots of unity, so `ι` is injective on `𝒢 = Q̄ˣ/μ_∞`.  This is the
  card's "injectivity follows from the height-zero theorem", now a proof rather than a citation.
- `deningerHilbertKummerBounded_extend` — **`(4)` ⟹ `(5)`**: a linear functional on the span of a
  total set which is bounded by the ambient norm extends to a bounded functional on the whole
  Hilbert space, and — because the span is dense — the extension is *unique*.  Existence is
  Hahn--Banach (`exists_extension_norm_eq`); uniqueness is that two continuous maps agreeing on a
  dense set are equal.  The `∃!` matches the card's "unique bounded functional `ℓ_P`".

### The place isometry and the density-free extension landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerPlaceIsometry.lean`, plus two additions to
`DeningerHeightZeroKummer.lean`.  Axiom audit on all seven declarations:
`propext, Classical.choice, Quot.sound`.

**The place model of `(1)`--`(2)`.**  For any field with mathlib's `AdmissibleAbsValues` — in
particular every number field — the place space carries the archimedean absolute values as a
multiset and the nonarchimedean ones as a set with finite multiplicative support, together with
the product formula.  That is exactly the data `(Y, λ)` needs at one level of the tower.

- `deningerAbsLog_eq` — the pointwise identity `|log t| = 2 log⁺ t - log t` for `t ≥ 0`.  This is
  the whole mechanism: the absolute value splits into twice the positive part minus the signed
  value.
- `deningerLogProductFormula` — **the product formula in logarithmic form**: for `α ≠ 0`,
  `∑_v log‖α‖_v = 0`, with the archimedean places counted with multiplicity.  Obtained from
  `AdmissibleAbsValues.product_formula` by `Real.log_multiset_prod` and `Real.log_finprod`, both
  applicable because every absolute value of a nonzero element is strictly positive.
- `deningerKummerL1Norm`, `deningerKummerL1Norm_eq_two_mul_logHeight` — **the Kummer place
  isometry**

  `∑_v |log‖α‖_v| = 2 h(α)`.

  Summing the pointwise identity over all places, the signed part dies by the logarithmic product
  formula and the positive part is `logHeight₁` on the nose (mathlib's `logHeight₁_eq`).  This is
  the `p = 1` Allcock--Vaaler isometry, now proved rather than quoted.
- `deningerKummerL1Norm_eq_zero_iff` — **injectivity of `(2)` in the place model**: `f_α` has
  vanishing total variation exactly when `α` is a root of unity.  Isometry plus the height-zero
  theorem.
- `deningerAllPlaces_one_isOfFinOrder` — the pointwise form used by the `p = 2` norm: an element
  with `‖α‖_v = 1` at *every* place is a root of unity.  This is what makes `ι` injective for any
  `L^p` norm on the place space, not just `p = 1`.

**The extension without a density citation.**

- `deningerClosedSpan_eqOn` — two bounded functionals agreeing on a set agree on the *closed span*
  of that set, unconditionally: their equalizer is a closed submodule containing the set, so it
  contains the closure of the span (`Submodule.topologicalClosure_minimal`).
- `deningerHilbertKummerBounded_extend_closedSpan` — **`(4)` ⟹ `(5)` with no density
  hypothesis**: a logarithmic modulus bounded by the Hilbert norm extends by Hahn--Banach, and any
  two extensions agree on the closed span of the Kummer classes.  Taking `H_Kum` to be that
  closed span — which is the only part of `L²(Y, λ)` the theorem ever uses — makes the card's
  "dense real span" true by construction rather than by citation, and `ℓ_P` is then genuinely
  unique on `H_Kum`.

### The archimedean half of the gluing landed

`formal/GaloisForLFunctions/RHTower/DeningerArchimedeanBaseChange.lean`.  Axiom audit on all four
declarations: `propext, Classical.choice, Quot.sound`.

What the tower needs is that the place model of `K` sits inside the place model of `L` with a
uniform factor `[L : K]`, so that the normalized functions `f_α` agree at every level and glue.
The archimedean half of that is now proved:

- `deningerEmbeddingSum_eq_placeSum` — summing a function of `‖φ x‖` over all complex embeddings
  equals summing over infinite places weighted by `mult`, because the embeddings inducing a given
  place number exactly `mult` (`InfinitePlace.card_filter_mk_eq`).
- `deningerEmbeddingFibre_card` — **the fibres of restriction have constant size `[L : K]`**.
  Making `ℂ` a `K`-algebra through `φ`, the embeddings of `L` restricting to `φ` are exactly the
  `K`-algebra maps `L → ℂ`, and an algebraically closed target admits `[L : K]` of them
  (`AlgHom.card`).  The equivalence between the fibre and `L →ₐ[K] ℂ` is the identity on
  underlying ring maps: the fibre condition *is* the `commutes'` field.
- `deningerEmbeddingSum_baseChange`, `deningerArchPlaceSum_baseChange` — **the base-change law**:
  for `x ∈ K`,

  `∑_{w : InfinitePlace L} mult(w) · F(w(x)) = [L : K] · ∑_{v : InfinitePlace K} mult(v) · F(v(x))`

  for every `F`.  Fibrewise summation plus the constant fibre size.  Taking `F = log⁺` gives the
  archimedean part of the height, and `F = |log ·|` the archimedean part of the Kummer norm; both
  scale by exactly `[L : K]`, which is the compatibility the tower needs.

### The local-degree scaling law landed

`formal/GaloisForLFunctions/RHTower/DeningerFinitePlaceBaseChange.lean`.  Axiom audit on all three
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerToNNReal_congr` — the value of `WithZeroMulInt.toNNReal` depends only on the base, not
  on the proof that it is nonzero.  Needed because the two absolute values are built from
  *different* nonvanishing proofs for what turns out to be the same base.
- `deningerToNNReal_base_pow` — **raising the base raises the value**: `toNNReal` with base `e^f`
  is the `f`-th power of `toNNReal` with base `e`.  This is the exact point where the residue
  degree enters an absolute value: `‖·‖_w` and `‖·‖_v` are the same construction with bases
  `N(w)` and `N(v)`, and `N(w) = N(v)^f`.
- `deningerAdicAbv_liesOver` — **the local-degree scaling law**: for `x` in the base field and a
  height-one prime `w` of `𝓞 L` above `v` of `𝓞 K`,

  `‖x‖_w = ‖x‖_v ^ (e(w|v) · f(w|v))`.

  The valuation contributes the ramification index
  (`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`) and the base contributes the inertia
  degree (`Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver`); the two combine through the base-power
  lemma.  Nonvanishing of the inertia degree is `Ideal.inertiaDeg'_ne_zero`, which needs
  `v.asIdeal` maximal — supplied by `HeightOneSpectrum.isMaximal`.

### The fibrewise sum law landed

`formal/GaloisForLFunctions/RHTower/DeningerFinitePlaceSumBaseChange.lean`.  Axiom audit on all
four declarations: `propext, Classical.choice, Quot.sound`.

- `deningerSpectrumOfMem` — a prime of `𝓞 L` in the fibre `primesOverFinset v.asIdeal (𝓞 L)`,
  packaged as a point of the height-one spectrum.  Primality comes from
  `IsDedekindDomain.mem_primesOverFinset_iff` and nonvanishing from
  `Ideal.ne_bot_of_mem_primesOver`; `deningerSpectrumOfMem_liesOver` records that it does lie
  over `v`.
- `deningerFinitePlaceSum_baseChange` — **the fibrewise base-change law**: for any `F` with
  `F(t^n) = n·F(t)` and any `x` in the base field,

  `∑_{w | v} F(‖x‖_w) = [L : K] · F(‖x‖_v)`.

  Each term contributes the local degree by `deningerAdicAbv_liesOver`, and
  `Ideal.sum_ramification_inertia` — the fundamental identity `∑_{w|v} e·f = [L : K]` — turns the
  sum of local degrees into the global one.
- `deningerFinitePlaceSum_posLog` and `deningerFinitePlaceSum_absLog` — the two instances that are
  actually used: `F = log⁺` computes the finite part of the logarithmic height, and
  `F = |log ·|` the finite part of the Kummer norm.  Both hypotheses are one line
  (`Real.posLog_pow`, and `Real.log_pow` plus `Nat.abs_cast`).

This is the exact non-archimedean counterpart of `deningerArchPlaceSum_baseChange`.  Both halves
of the base-change law are now proved.

### The base-change law is complete

`formal/GaloisForLFunctions/RHTower/DeningerPlaceRestriction.lean` and
`formal/GaloisForLFunctions/RHTower/DeningerHeightBaseChange.lean`.  Axiom audit on all
declarations: `propext, Classical.choice, Quot.sound`.

**Restriction of finite places.**

- `deningerUnderSpectrum`, `deningerRestrictPlace` — a finite place of `L` restricts to one of `K`
  by taking the prime under its maximal ideal; nonvanishing of the ideal below is
  `Ideal.under_ne_bot`, which applies because `𝓞 L` is integral over `𝓞 K`.
- `deningerFinitePlace_apply` — the value law `‖x‖_w = ‖x‖_{w|K} ^ (e·f)` at the level of places,
  obtained from `deningerAdicAbv_liesOver` through
  `FinitePlace.norm_embedding`.
- `deningerPlacesOver`, `deningerMem_placesOver` — the fibre of the restriction over `v`, as a
  finite set of places, and the proof that it is *exactly* the set of places restricting to `v`.
  The fibre condition matches `primesOverFinset` because `LiesOver p P` unfolds to
  `p = P.under A`.
- `deningerLocalDegree_ne_zero` — the local degree `e·f` is nonzero
  (`ramificationIdx'_ne_zero_of_liesOver`, `inertiaDeg'_ne_zero`).  This is what makes the fibre
  over a place in the support consist *entirely* of places in the support: `‖x‖_v ≠ 1` forces
  `‖x‖_v^{ef} ≠ 1`.
- `deningerPlacesOver_sum`, `deningerFinitePlaceFinsum_baseChange` — the fibre sum law transported
  to places, and then the full `finsum` over `FinitePlace L`, obtained by cutting both sides down
  to the finite multiplicative supports and applying `Finset.sum_fiberwise_of_maps_to`.

**The capstone.**

- `deningerLogHeight_baseChange` — **`h_L(x) = [L : K] · h_K(x)`** for every `x ∈ K`.  The
  archimedean part scales by `deningerArchPlaceSum_baseChange`, the finite part by
  `deningerFinitePlaceFinsum_baseChange`, both with `F = log⁺`.
- `deningerKummerL1Norm_baseChange` — the same for the Kummer norm, immediately from the place
  isometry `‖f_α‖₁ = 2h(α)`.
- `deningerNormalizedHeight_baseChange` — **the normalized height `h_K(x)/[K : ℚ]` does not depend
  on the field of definition**, by the tower law `[L : ℚ] = [K : ℚ]·[L : K]`.

This is precisely the compatibility the card's place tower needs: the function `f_α`, normalized by
the absolute degree, is the same at every level, so the level-wise place models are compatible and
the Kummer norm of `α` is an invariant of `α` alone.  Note that mathlib has no absolute height on
`Q̄` and no base-change law for `Height.logHeight₁`; both are built here.

### The absolute Weil height on the algebraic numbers landed

`formal/GaloisForLFunctions/RHTower/DeningerAbsoluteHeight.lean`.  Axiom audit on all
declarations: `propext, Classical.choice, Quot.sound`.

mathlib has heights only on a fixed number field.  The global object the card's place space needs
is the height on all of `Q̄` at once; it is built here.

- `deningerNormalizedHeight K x = h_K(x)/[K : ℚ]`, and `deningerNormalizedHeight_ringHom` — **it is
  preserved by every field embedding** `φ : K →+* K'`.  A ring map between number fields is
  automatically a `ℚ`-algebra map, because `ℚ` admits a unique ring map into a field of
  characteristic zero (`RingHom.ext_rat`); that supplies the `IsScalarTower ℚ K K'` needed by
  `deningerNormalizedHeight_baseChange`.  Note this needs no compatibility hypothesis on `φ` at
  all.
- `deningerAbsHeight α` — **the absolute logarithmic Weil height** of an element of any algebraic
  extension `F/ℚ`: its normalized height in `ℚ⟮α⟯`.
- `deningerAbsHeight_intermediateField` — **any** finite intermediate field containing `α`
  computes it, since the inclusion `ℚ⟮α⟯ ↪ E` is a field embedding.  This is the well-definedness
  that makes the height an invariant of `α` alone.
- `deningerAbsHeight_eq_zero_iff` — **the height-zero theorem on `Q̄`**: a nonzero algebraic number
  has absolute height zero exactly when it is a root of unity.  The generator of `ℚ⟮α⟯` and `α`
  have the same order because the structure map is an injective ring hom.
- `deningerAbsHeight_pow`, `deningerAbsHeight_nonneg` — homogeneity `h(α^n) = n·h(α)` and
  nonnegativity.

One trap worth recording: `↥ℚ⟮α⟯` carries two `Algebra ℚ` structures — `IntermediateField.algebra'`
and the canonical `DivisionRing.toRatAlgebra` — which are equal but not definitionally so.
`NumberField` is stated for the latter, `IntermediateField.adjoin.finiteDimensional` produces the
former.  The fix is to transport once, at the `NumberField ℚ⟮α⟯` instance, via
`Subsingleton (Module ℚ M)`, and to state everything downstream on a *type variable* carrying
`[NumberField K]` so that only the canonical structure is ever mentioned.

### Remaining

The Hilbert--Kummer space itself: `𝒢 = Q̄ˣ/μ_∞` tensored with `ℚ`, normed by the absolute height,
and completed.  The three inputs are in place — the height is defined on all of `Q̄`
(`deningerAbsHeight`), it vanishes exactly on the torsion that is quotiented out
(`deningerAbsHeight_eq_zero_iff`), and it is homogeneous (`deningerAbsHeight_pow`) — so what
remains is subadditivity `h(αβ) ≤ h(α) + h(β)`, which makes it a seminorm on the group, and then
the completion.  With `H_Kum` defined as that completion, `(2)` is injective by the height-zero
theorem and has dense span by construction.
