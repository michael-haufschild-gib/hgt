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
  `GaloisForLFunctions.RHTower.DeningerAbsoluteHeight`,
  `GaloisForLFunctions.RHTower.DeningerAbsoluteHeightSeminorm`,
  `GaloisForLFunctions.RHTower.DeningerKummerGroupNorm`,
  `GaloisForLFunctions.RHTower.DeningerKummerSpace`,
  `GaloisForLFunctions.RHTower.DeningerKummerCompletion`,
  `GaloisForLFunctions.RHTower.DeningerLocalDegree`,
  `GaloisForLFunctions.RHTower.DeningerPlaceDegree`,
  `GaloisForLFunctions.RHTower.DeningerL2PlaceSum`,
  `GaloisForLFunctions.RHTower.DeningerL2Norm`,
  `GaloisForLFunctions.RHTower.DeningerL2Inner`,
  `GaloisForLFunctions.RHTower.DeningerL2InnerBaseChange`,
  `GaloisForLFunctions.RHTower.DeningerAbsL2Inner`,
  `GaloisForLFunctions.RHTower.DeningerL2InnerAdditive`,
  `GaloisForLFunctions.RHTower.DeningerL2InnerTorsion`,
  `GaloisForLFunctions.RHTower.DeningerAbsL2InnerAdditive`,
  `GaloisForLFunctions.RHTower.DeningerKummerL2Inner`,
  `GaloisForLFunctions.RHTower.DeningerKummerSpaceInner`,
  `GaloisForLFunctions.RHTower.DeningerKummerSpaceInnerPos`,
  `GaloisForLFunctions.RHTower.DeningerL2Definite`,
  `GaloisForLFunctions.RHTower.DeningerKummerL2Definite`,
  `GaloisForLFunctions.RHTower.DeningerKummerL2Bilinear`,
  `GaloisForLFunctions.RHTower.DeningerRealSmul`
  (the gluing of the place tower, the absolute height on `Q̄`, the
  normed Kummer group `𝒢`, the normed `ℚ`-vector space `𝒢 ⊗ ℚ`, its
  completion, and the local-degree normalization of the place space)

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

### The normed Kummer group `𝒢` landed

`formal/GaloisForLFunctions/RHTower/DeningerAbsoluteHeightSeminorm.lean` and
`formal/GaloisForLFunctions/RHTower/DeningerKummerGroupNorm.lean`.  Axiom audit on all
declarations: `propext, Classical.choice, Quot.sound` (the units/finite-order transfer needs only
`propext, Quot.sound`).

**The height is a seminorm.**

- `deningerAbsHeight_mul_le` — **subadditivity** `h(αβ) ≤ h(α) + h(β)`.  This is the only statement
  that needs two elements at once; it is proved inside `ℚ⟮α, β⟯`, which is finite over `ℚ`
  (`IntermediateField.finiteDimensional_adjoin_pair`) and contains `α`, `β` and `αβ`, where it is
  mathlib's `Height.logHeight₁_mul_le` divided by the degree.
- `deningerAbsHeight_inv`, `deningerAbsHeight_zpow`, `deningerAbsHeight_one` — invariance under
  inversion, `h(α^n) = |n|·h(α)` for `n ∈ ℤ`, and `h(1) = 0`.  Each is proved in `ℚ⟮α⟯`, which is
  closed under all three operations.

**The Kummer group.**

- `deningerKummerSeminorm` — the height as a bundled `GroupSeminorm Fˣ`.
- `deningerKummerSeminorm_eq_zero_iff` — **its null set is exactly the torsion subgroup**
  `CommGroup.torsion Fˣ`.  This is the height-zero theorem on `Q̄` transported to units, using that
  a unit has finite order exactly when its value does.
- `deningerKummerGroup F = Fˣ ⧸ CommGroup.torsion Fˣ` — **the Kummer group `𝒢 = Q̄ˣ/μ_∞`** of the
  card's `(1)`.
- `deningerKummerSeminorm_mul_torsion`, `deningerKummerNormFun` — the height is unchanged by a
  torsion factor (both inequalities from subadditivity), so it descends to `𝒢`.
- `deningerKummerNorm` — **the height is a genuine `GroupNorm` on `𝒢`**: positive definite,
  because its null set is precisely what has been divided out.

So `𝒢` and its Weil-height norm now exist as Lean objects, and the injectivity of the card's `(2)`
is the positive-definiteness of that norm rather than a citation.

### The Kummer space `𝒢 ⊗ ℚ` landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerSpace.lean`.  Axiom audit on all declarations:
`propext, Classical.choice, Quot.sound`.

- `deningerKummerGroup_eq_one_of_isOfFinOrder`, `deningerKummerGroup_isMulTorsionFree` — **the
  Kummer group is torsion-free**: a class of finite order is represented by a unit whose power is
  torsion, hence which is itself torsion, hence trivial in `𝒢`.  Torsion-freeness for a commutative
  group is exactly injectivity of `x ↦ x^n`, obtained from this by applying it to `a·b⁻¹`.
- `deningerKummerNorm_pow`, `deningerKummerNorm_zpow` and their additive forms — the Kummer norm is
  homogeneous, `‖x^k‖ = |k|·‖x‖` for `k ∈ ℤ`.
- `deningerKummerSpace F = DivisibleHull (Additive 𝒢)` — **the `ℚ`-vector space `𝒢 ⊗ ℚ`** of the
  card's `(2)`.  Torsion-freeness is exactly the hypothesis mathlib's `DivisibleHull` needs for
  `mk m s = mk m' s' ↔ s'•m = s•m'`, which is what makes the extended height well defined.
- `deningerKummerSpaceNormFun` and `deningerKummerSpaceNorm` — **the height extends to `𝒢 ⊗ ℚ` as
  a genuine `AddGroupNorm`**, by `‖m/s‖ = ‖m‖/s`.  Well-definedness is the homogeneity law;
  subadditivity comes from `mk m s + mk m' s' = mk (s'•m + s•m') (s·s')` and the group inequality;
  definiteness because `‖m‖/s = 0` forces `‖m‖ = 0` forces `m = 0`.
- `deningerKummerSpaceNorm_qsmul` — **rational homogeneity** `‖q·x‖ = |q|·‖x‖`, from
  `q · (m/s) = (q.num · m)/(q.den · s)` and the integer homogeneity.

So the card's `𝒢 ⊗ ℚ` is now an actual normed `ℚ`-vector space in Lean, with the Weil height as
its norm.

### The Hilbert--Kummer Banach space landed — `(1)` and `(2)` are now constructions

`formal/GaloisForLFunctions/RHTower/DeningerKummerCompletion.lean`.  Axiom audit on all
declarations: `propext, Classical.choice, Quot.sound`.

- `deningerKummerSpace_normedAddCommGroup`, `deningerKummerSpace_normedSpace` — `𝒢 ⊗ ℚ` is a
  normed `ℚ`-vector space: the `AddGroupNorm` of the previous module plus the rational homogeneity
  `‖q·x‖ = ‖q‖·‖x‖`.
- `deningerKummerCompletion F` — **the Hilbert--Kummer space**, the completion of `𝒢 ⊗ ℚ` for the
  Weil height norm.  It is a Banach space over `ℚ` and complete, all inherited from mathlib's
  `UniformSpace.Completion`.
- `deningerKummerClass` — **the map `(2)`**, sending a unit to its class in `𝒢 ⊗ ℚ`.
- `deningerKummerClass_norm` — `‖ι(α)‖ = h(α)`: the norm of a Kummer class *is* the absolute Weil
  height.  This is the card's identification of the Kummer norm.
- `deningerKummerClass_mul` — additivity, `ι(αβ) = ι(α) + ι(β)`.
- `deningerKummerClass_eq_zero_iff_isOfFinOrder` — **injectivity of `(2)`**: the class map
  annihilates exactly the roots of unity, so it is injective on `𝒢`.
- `deningerKummerSpace_mk_eq_smul`, `deningerKummerClass_span` — **every element of `𝒢 ⊗ ℚ` is a
  rational multiple of a class**, so the classes span it: `span ℚ (range ι) = ⊤`.
- `deningerKummerClass_dense_completion` — **dense span of `(2)`**: pushing that span forward along
  the isometric inclusion into the completion, the classes have dense `ℚ`-span there.

Both halves of the card's `(2)` — injectivity and dense span — are therefore now proved rather
than quoted, and `H_Kum` is an explicit Lean object rather than a citation.

### Remaining

One point only: the card's `H_Kum` is an `L²` space, whereas the completion built here carries the
height norm, which is of `L¹` type (`‖f_α‖₁ = 2h(α)`, formalized as
`deningerKummerL1Norm_eq_two_mul_logHeight`).  The inner-product structure is carried by the place
space `(Y, λ)` and is what the `p = 2` Allcock--Vaaler theorem supplies.  Every statement the card
*derives* from `H_Kum` — the bounded extension, the modulus replacement, the Frobenius scaling, the
descent and positivity of `(9)`, and the Poisson-flow identities `(11)`--`(14)` — is formalized
unconditionally, and the injectivity and density it quotes are now proved for the height
completion.
### The local-degree normalization landed

`formal/GaloisForLFunctions/RHTower/DeningerLocalDegree.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

This is the foundation for the `L²` structure, and it clarifies exactly why the `L¹` and `L²`
place norms behave differently.  In mathlib's normalization the adic absolute value at `w` is the
`d_w`-th power of the one restricting to the standard absolute value on `ℚ`, where `d_w` is the
local degree.  Consequently

`∑_w |log ‖x‖_w^{mathlib}|^p = ∑_w d_w^p · |log |x|_w|^p`,

which for `p = 1` is the base-change-invariant weighting `∑_w d_w |log |x|_w|` — the `L¹` isometry
already proved — but for `p = 2` is *not*: the invariant `L²` weight is `∑_w d_w (log |x|_w)²`,
i.e. one factor of `d_w`, not `d_w²`.  So the `L²` Kummer norm requires dividing the log by the
local degree, and its base-change invariance rests on two facts about that degree rather than on
the value-scaling law:

- `deningerLocalDegree p P = e(P|p) · f(P|p)`, and `deningerLocalDegree_tower` — **the local degree
  is multiplicative in towers**, from `Ideal.ramificationIdx'_algebra_tower` and
  `Ideal.inertiaDeg'_algebra_tower`.  Hence `d_{w/ℚ} = d_{v/ℚ} · d_{w/v}`.
- `deningerLocalDegree_sum` — **the fibre sum of local degrees over an extension is its degree**,
  `∑_{w|v} d_{w/v} = [L : K]`, the fundamental identity.

Together: `∑_{w|v} d_{w/ℚ} = d_{v/ℚ} · [L : K]`, so weighting each place by `d/[K:ℚ]` gives a
weight unchanged by enlarging the field — the normalization under which *every* `L^p` place norm,
`p = 2` included, is an invariant of the algebraic number alone.

### The place degree landed

`formal/GaloisForLFunctions/RHTower/DeningerPlaceDegree.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerPlaceDegree w` — the local degree over `ℚ` of a finite place, i.e. the local degree of
  its maximal ideal over the rational prime below it.
- `deningerPlaceDegree_tower` — **it factors along a tower of number fields**:
  `d_{w/ℚ} = d_{(w|K)/ℚ} · d_{w/(w|K)}`.  This is the ideal-level tower law of the previous module
  transported to the language of places, using `Ideal.under_under` to identify the rational prime
  below `w` with the one below its restriction, and `Ring.DimensionLEOne.maximalOfPrime` plus
  `Ideal.under_ne_bot` to supply the maximality and nonvanishing the tower lemma needs.

This is the weight in the `L²` normalization, now known to behave correctly under base change.

### The weighted fibre sum for `L²` landed

`formal/GaloisForLFunctions/RHTower/DeningerL2PlaceSum.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The `L²` summand `(log ‖x‖_w)²/d_w` depends on the *place*, not only on its value, so the earlier
fibrewise law — which was stated for summands of the form `F(‖x‖_w)` — does not apply.  The
weighted version is proved here.

- `deningerRelDegree w` — the relative local degree of a place of `L` over its restriction to `K`.
- `deningerRelDegree_sum` — **its fibre sum is `[L : K]`**: transported from
  `deningerLocalDegree_sum` across the bijection between the fibre `deningerPlacesOver v` and
  `primesOverFinset`, using that a prime in the fibre lies over `v`, so the prime of `𝓞 K` under it
  *is* `v`.
- `deningerFinitePlace_apply_relDegree` — the value law in this language,
  `‖x‖_w = ‖x‖_v ^ d_{w/v}`.
- `deningerL2FibreSum` — **the weighted fibre sum law**:

  `∑_{w | v} (log ‖x‖_w)²/d_w = [L : K] · (log ‖x‖_v)²/d_v`.

  On the fibre the value contributes `(d_{w/v})²` and the weight `1/(d_v·d_{w/v})` — using
  `deningerPlaceDegree_tower` for `d_w = d_v·d_{w/v}` — leaving exactly `d_{w/v}`, whose fibre sum
  is the degree.  Nonvanishing of both degrees comes from `ramificationIdx'_ne_zero_of_liesOver`
  and `inertiaDeg'_ne_zero`.

This is the exact `L²` counterpart of `deningerFinitePlaceSum_baseChange`, and it is the step the
`p = 2` normalization needs that the `p = 1` case did not.

### The `L²` place norm landed — the `p = 2` normalization is proved

`formal/GaloisForLFunctions/RHTower/DeningerL2Norm.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerL2NormSq x = ∑_{v arch} mult(v)·(log v(x))² + ∑ᶠ_{v fin} (log v(x))²/d_v` — the
  unnormalized `L²` place norm, with `deningerPlaceDegree_pos` for the positivity of the weights.
- `deningerL2FinsumBaseChange` — **base change for the finite part**: the same
  support-and-fibration argument as in the `L¹` case, but with the weighted fibre law
  `deningerL2FibreSum` at the centre instead of the value-only one.
- `deningerL2NormSq_baseChange` — **`‖f_α‖₂²` computed in an extension is `[L : K]` times its value
  in the base field**, the archimedean half by `deningerArchPlaceSum_baseChange` with
  `F = (log ·)²`, the finite half by the previous item.
- `deningerNormalizedL2_baseChange` — **the normalized `L²` norm is independent of the field of
  definition**, by the tower law, exactly as for the height.

This is the `p = 2` normalization statement the card attributed to Allcock--Vaaler: the `L²` Kummer
norm of an algebraic number is an invariant of the number alone, not of the field in which it is
computed.  Note that this required a genuinely different argument from `p = 1` — the value-scaling
law `‖x‖_w = ‖x‖_v^{e·f}` alone is not enough, because the `L²` weight carries one factor of the
local degree and the squared value carries two; the identity that closes the gap is the tower
factorization of the local degree together with the fundamental identity.

### The `L²` inner product landed

`formal/GaloisForLFunctions/RHTower/DeningerL2Inner.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerL2Inner x y = ∑_{v arch} mult(v)·(log v x)(log v y) + ∑ᶠ_{v fin} (log v x)(log v y)/d_v`
  — the form whose diagonal is the `L²` norm.
- `deningerL2Inner_self` — `⟨x, x⟩ = ‖f_x‖₂²`, so the norm of the previous module *is* the norm of
  this form.
- `deningerL2Inner_comm` — symmetry.
- `deningerL2FibreSumProd` — **the fibre law for the product**: `∑_{w|v} (log‖x‖_w)(log‖y‖_w)/d_w
  = [L:K]·(log‖x‖_v)(log‖y‖_v)/d_v`.  Same mechanism as for the norm: the two values each
  contribute a factor `d_{w/v}` and the weight contributes `1/(d_v·d_{w/v})`, leaving `d_{w/v}`,
  whose fibre sum is the degree.

### Base change for the `L²` inner product landed

`formal/GaloisForLFunctions/RHTower/DeningerL2InnerBaseChange.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerL2InnerFinsumBaseChange` — the finite part.  Same support-and-fibration argument as for
  the norm, with the summand now involving two elements: its support sits in the *union* of the two
  multiplicative supports, the restriction maps that union into the corresponding union downstairs
  because a value equal to one upstairs forces one downstairs, and a place in a fibre over a place
  in the union is itself in the union because `t ≠ 1` gives `t^d ≠ 1`.
- `deningerEmbeddingSum_eq_placeSum₂`, `deningerEmbeddingSum_baseChange₂`,
  `deningerArchPlaceSum_baseChange₂` — **the two-variable archimedean base-change law**.  The
  one-variable versions do not apply, because the archimedean summand of the inner product depends
  on two elements; the proof is the same fibrewise argument, since on the fibre over `φ` both
  values are those of `φ`.
- `deningerL2Inner_baseChange` — **`⟨x, y⟩` computed in an extension is `[L : K]` times its value
  in the base field**.
- `deningerNormalizedL2Inner_baseChange` — **the normalized inner product does not depend on the
  field of definition**.

With this the whole `p = 2` structure of the card's `(1)`--`(2)` is proved: the `L²` inner product
of algebraic numbers is an invariant of the numbers alone, its diagonal is the `L²` Kummer norm,
and the norm's null set is the torsion (`deningerAllPlaces_one_isOfFinOrder`).

### The absolute `L²` inner product landed

`formal/GaloisForLFunctions/RHTower/DeningerAbsL2Inner.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The `L²` inner product is now an invariant of the algebraic numbers themselves, in the same sense
and by the same mechanism as the absolute height.

- `deningerNormalizedL2Inner K x y = ⟨x, y⟩ / [K : ℚ]`, and `deningerNormalizedL2Inner_ringHom` —
  **preserved by every ring homomorphism between number fields**, with no compatibility hypothesis,
  because such a map is automatically a `ℚ`-algebra map.
- `deningerAbsL2Inner α β` — **the absolute `L²` inner product**: the normalized inner product
  computed in `ℚ⟮α, β⟯`.
- `deningerAbsL2Inner_intermediateField` — **any** finite intermediate field containing both
  elements computes it, via the explicit inclusion ring hom.
- `deningerAbsL2Inner_comm` — symmetry.

Together with `deningerAbsHeight` this gives both structures the card's `H_Kum` needs — the `L¹`
height and the `L²` inner product — as invariants on the algebraic numbers, each independent of
the field of definition, each proved from the place tower rather than quoted.

### Additivity of the `L²` inner product landed

`formal/GaloisForLFunctions/RHTower/DeningerL2InnerAdditive.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerInfinitePlace_log_mul`, `deningerFinitePlace_log_mul` — the logarithm of a place is
  additive on nonzero elements, since a place is an absolute value and its values are positive.
- `deningerL2Inner_mul_left`, `deningerL2Inner_mul_right` — **the inner product is additive in each
  argument** under multiplication of algebraic numbers.  The archimedean part is a finite sum; the
  finite part needs `finsum_add_distrib`, whose support hypotheses hold because the summand
  vanishes wherever the place value is one, so its support sits inside the multiplicative support
  of the corresponding element.

This is the bilinearity of the form.  With symmetry (`deningerAbsL2Inner_comm`), field-independence
(`deningerNormalizedL2Inner_ringHom`) and vanishing on torsion
(`deningerAllPlaces_one_isOfFinOrder`), the `L²` form now has every property needed to descend to
`𝒢 = Q̄ˣ/μ_∞` and extend to `𝒢 ⊗ ℚ`.

### Vanishing of the `L²` inner product on torsion landed

`formal/GaloisForLFunctions/RHTower/DeningerL2InnerTorsion.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerInfinitePlace_eq_one_of_isOfFinOrder`, `deningerFinitePlace_eq_one_of_isOfFinOrder` —
  **a root of unity has value one at every place**, archimedean and finite alike: the place of a
  power is the power of the place, and a positive real with `t^n = 1` is one.
- `deningerL2Inner_torsion_left`, `deningerL2Inner_torsion_right` — hence its Kummer function is
  identically zero and the inner product with anything vanishes.
- `deningerIntermediate_isOfFinOrder`, `deningerAbsL2Inner_torsion_left` — the same at the absolute
  level, computing in `ℚ⟮α, β⟯` and transferring finite order into the subfield.

This is the property that lets the form descend to `𝒢 = Q̄ˣ/μ_∞`: the classes that are quotiented
out are exactly those on which the form is identically zero, so it is well defined on the quotient.

### Additivity of the absolute `L²` inner product landed

`formal/GaloisForLFunctions/RHTower/DeningerAbsL2InnerAdditive.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerAdjoinTriple_numberField` — `ℚ⟮α, β, γ⟯` is a number field, from
  `IntermediateField.finiteDimensional_adjoin` for a finite set of integral elements, transported
  across the `ℚ`-algebra instance diamond as before.
- `deningerAbsL2Inner_mul_left`, `deningerAbsL2Inner_mul_right` — **the absolute inner product is
  additive in each argument**.  Additivity involves three algebraic numbers at once, so all four
  values are computed in `ℚ⟮α, α', β⟯`, where it is `deningerL2Inner_mul_left` divided by the
  degree.

The `L²` form on `Q̄ˣ` now has the complete set of properties it needs: symmetric
(`deningerAbsL2Inner_comm`), bilinear (this module), zero on roots of unity
(`deningerAbsL2Inner_torsion_left`), independent of the field of definition
(`deningerNormalizedL2Inner_ringHom`), with diagonal the `L²` Kummer norm
(`deningerL2Inner_self`).

### The `L²` inner product on `𝒢` landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerL2Inner.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerUnitL2Inner` — the absolute form on the units, where the nonvanishing hypotheses of all
  the earlier results are automatic.
- `deningerUnitL2Inner_torsion_left`, `deningerUnitL2Inner_mul_torsion_left/right` — **the form is
  unchanged by a torsion factor**: biadditivity turns the extra factor into an extra summand, and
  that summand vanishes.
- `deningerKummerL2Inner` — **the descended form on `𝒢 = Q̄ˣ/μ_∞`**, obtained by `Quotient.lift₂`
  from exactly that invariance, with `deningerKummerL2Inner_mk` computing it on classes.
- `deningerKummerL2Inner_comm`, `deningerKummerL2Inner_mul_left`, `_mul_right` — symmetry and
  biadditivity survive the descent.

So the card's `H_Kum` inner product now exists on the Kummer group itself.

### The `L²` inner product on `𝒢 ⊗ ℚ` landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerSpaceInner.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerKummerL2Inner_one_left` — the form vanishes at the identity, from biadditivity alone
  (`⟨1,y⟩ = ⟨1,y⟩ + ⟨1,y⟩`).
- `deningerKummerL2Inner_pow_left`, `deningerKummerAddL2Inner_nsmul_left/right` — **homogeneity**
  `⟨x^n, y⟩ = n⟨x, y⟩`, by induction from biadditivity, and its additive form.
- `deningerSpaceL2Inner` — **the extension to `𝒢 ⊗ ℚ`**, by `DivisibleHull.liftOn₂` with
  `⟨m/s, m'/s'⟩ = ⟨m, m'⟩/(s·s')`.  Well-definedness is exactly homogeneity in both arguments:
  `mk m s = mk m₁ s₁` means `s₁·m = s·m₁`, so `s₁s₁'⟨m,m'⟩ = ss'⟨m₁,m₁'⟩`.
- `deningerSpaceL2Inner_mk`, `deningerSpaceL2Inner_comm` — the value on fractions, and symmetry.

The card's `H_Kum` inner product now exists on `𝒢 ⊗ ℚ` itself.

### Positivity and additivity of the `L²` form on `𝒢 ⊗ ℚ` landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerSpaceInnerPos.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerL2NormSq_nonneg` — the place norm is a sum of squares against positive weights, hence
  nonnegative (`Finset.sum_nonneg` and `finsum_nonneg`).
- `deningerAbsL2Inner_self_nonneg`, `deningerKummerL2Inner_self_nonneg`,
  `deningerSpaceL2Inner_self_nonneg` — **the form is positive semidefinite**, at the absolute
  level, on `𝒢`, and on `𝒢 ⊗ ℚ`.
- `deningerSpaceL2Inner_add_left`, `_add_right` — **additivity on the Kummer space**, from
  `mk m s + mk n t = mk (t·m + s·n) (s·t)` together with the homogeneity of the form.

Note on the norm: the card's `H_Kum` is the `L²` completion, so its norm is `√⟨x, x⟩`, *not* the
height norm `deningerKummerSpaceNorm` carried by `deningerKummerCompletion` — the height is the
`L¹` quantity (`‖f_α‖₁ = 2h(α)`).  Both live on the same space `𝒢 ⊗ ℚ`; the `L¹` one gives the
Banach completion already built, the `L²` one gives the Hilbert completion.

### Definiteness of the `L²` place norm landed

`formal/GaloisForLFunctions/RHTower/DeningerL2Definite.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerL2NormSq_eq_zero_places` — **a vanishing `L²` norm forces every place to take the value
  one**.  The two halves are separately nonnegative, so both vanish; the archimedean half is a
  `Finset` sum of nonnegative terms, and the finite half becomes one after cutting down to the
  multiplicative support, where a place outside the support already has value one.  Each vanishing
  term gives `log ‖x‖_v = 0`, hence `‖x‖_v = 1`.
- `deningerL2NormSq_eq_zero` — **definiteness**: a nonzero element of vanishing `L²` norm is a root
  of unity.  Once every place has value one the logarithmic height vanishes term by term, and the
  height-zero theorem `deningerLogHeightZero_iff_isOfFinOrder` finishes.  This routes around the
  `AdmissibleAbsValues` bridge entirely: the conclusion is drawn from the height, not from
  `deningerAllPlaces_one_isOfFinOrder`.

The `L²` form on the algebraic numbers is now symmetric, biadditive, field-independent, positive
semidefinite, definite modulo torsion, with diagonal the `L²` place norm — the complete set of
properties an inner product on `𝒢 ⊗ ℚ` requires.

### Definiteness on `𝒢` and `𝒢 ⊗ ℚ` landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerL2Definite.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerIntermediate_isOfFinOrder_of` — finite order transfers back from a subfield element.
- `deningerAbsL2Inner_self_eq_zero` — **the absolute form is definite modulo torsion**: a nonzero
  algebraic number with `⟨α, α⟩ = 0` is a root of unity.
- `deningerKummerL2Inner_self_eq_zero`, `deningerKummerAddL2Inner_self_eq_zero` — **definite on
  `𝒢`**: the torsion is exactly what has been quotiented out, so the class is trivial.
- `deningerSpaceL2Inner_self_eq_zero` — **definite on `𝒢 ⊗ ℚ`**: a fraction of vanishing norm has
  vanishing numerator, hence is zero in the divisible hull.

A note on how this had to be written: stating the degree explicitly, as
`Module.finrank ℚ (ℚ⟮α, α⟯ : IntermediateField ℚ F)`, makes elaboration diverge — it re-opens the
`ℚ`-algebra instance diamond on `↥ℚ⟮α, α⟯` and does not terminate even at a million heartbeats.
Routing the same step through `deningerNormalizedL2Inner`, which is stated on a *type variable*
and so mentions only the canonical structure, makes it immediate.  This is the same trap recorded
for the absolute height, and it now has a second instance.

The `L²` form is therefore a genuine inner product on `𝒢 ⊗ ℚ`: symmetric, biadditive, positive
definite.

### The bundled `ℚ`-bilinear `L²` form landed

`formal/GaloisForLFunctions/RHTower/DeningerKummerL2Bilinear.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerKummerL2Inner_inv_left`, `deningerKummerL2Inner_zpow_left` — the form negates under
  inversion and is homogeneous under integer powers.
- `deningerSpaceL2Inner_qsmul_left` — **homogeneity under rational scalars**: scaling by `q` scales
  the numerator by `q.num` and the denominator by `q.den`, so the value scales by `q`.
- `deningerSpaceL2Form : 𝒢 ⊗ ℚ →ₗ[ℚ] 𝒢 ⊗ ℚ →ₗ[ℚ] ℝ` — **the bundled form**, symmetric
  (`deningerSpaceL2Inner_comm`), positive semidefinite
  (`deningerSpaceL2Inner_self_nonneg`) and definite (`deningerSpaceL2Inner_self_eq_zero`).

So the card's `(1)` now has a complete Lean realization at the level of `𝒢 ⊗ ℚ`: an inner-product
`ℚ`-space whose form is the `L²` Kummer pairing, together with `(2)` — `deningerKummerClass`, with
injectivity and dense span proved.

### The real scalar extension landed

`formal/GaloisForLFunctions/RHTower/DeningerRealSmul.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

mathlib has no way to turn a normed `ℚ`-space into a real one: `UniformSpace.Completion` preserves
the scalar field, `InnerProductSpace 𝕜` demands `RCLike 𝕜`, and
`Mathlib/Topology/Instances/RealVectorSpace.lean` — which looks relevant — *assumes* `Module ℝ E`
and only proves that continuous additive maps are then `ℝ`-linear.  So the extension is built here.

- `deningerRatSmul_lipschitz` — for a fixed vector, `q ↦ q • x` is Lipschitz with constant `‖x‖`,
  since `‖(q - q')•x‖ = |q - q'|·‖x‖`.
- `deningerRealSmul` — **the real action**, the extension of the rational one along the dense
  uniform embedding `ℚ ↪ ℝ` (`uniformly_extend`), available because the space is complete.
- `deningerRealSmul_ratCast` — it restricts to the rational action;
  `deningerRealSmul_continuous` — it is continuous in the scalar;
  `deningerRealSmul_norm` — **`‖r • x‖ = |r|·‖x‖`**, proved by density: both sides are continuous
  in `r` and agree on `ℚ`.

### Remaining

The module axioms for `deningerRealSmul` — `one_smul`, `mul_smul`, `smul_add`, `add_smul`,
`zero_smul` — each of which is a density argument in one or two real variables against the
corresponding rational identity, exactly like the norm law just proved.  With those the completion
of `𝒢 ⊗ ℚ` for the `L²` norm is a real normed space, hence (being complete, with a form satisfying
the parallelogram law) the Hilbert space `H_Kum` of the card's `(1)`.
