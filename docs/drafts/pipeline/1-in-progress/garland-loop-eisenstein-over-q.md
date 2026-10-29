# Garland loop-group Eisenstein series over ℚ

- **ID:** garland-loop-eisenstein-over-q
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME
- **Target:** Construct an actual arithmetic loop-group Eisenstein series over ℚ, prove its
  absolute convergence, and identify its unipotent constant term with Garland's affine Weyl
  sum containing completed zeta functions in the denominators.

## Exact target and normalization

Use Garland's minimal-parabolic series on the completed, centrally extended real loop group
with its integral arithmetic subgroup. Include the degree rotation `exp(-rD)`, `r > 0`.
The concrete first group is the completed central extension of the loop group of `SL₂`;
this is a genuine instance of the requested construction.
With `λ = -(ν + ρ)`, the Godement chamber is `Re λ(h_i) > 1` for every simple coroot.
The required coefficient is

\[
 c_w(λ)=\prod_{\substack{β>0\\wβ<0}}
 \frac{ξ(λ(β^\vee))}{ξ(λ(β^\vee)+1)},\qquad
 ξ(s)=π^{-s/2}Γ(s/2)ζ(s).
\]

Here ξ is `completedRiemannZeta`, not the entire function obtained by multiplying by
`s(s-1)/2`. The target is the Eisenstein series on the arithmetic quotient, not a function
defined to equal this proposed constant term. Proving finite coefficient identities or
convergence of the Weyl sum alone does not complete the target.

## Evidence and literature audit

- Corpus searches for loop groups and affine Weyl Eisenstein series found no existing
  construction. Existing `GarlandLocalization` concerns cohomological vanishing and cannot
  supply this theorem.
- Finite-dimensional Eisenstein series, completed zeta, Euler products, Laurent series,
  and Steinberg presentations provide reusable ingredients; each imported statement must
  be checked before use.
- Garland, *Eisenstein series on arithmetic quotients of loop groups*, Mathematical
  Research Letters 6 (1999), 723–733, §§2–4, especially Theorems 4.1 and 4.2:
  <https://intlpress.com/api/bgcloud-front/resource/pdf/volume/1806606802735230978-1806606802735230978-6ac9bbce4cb59ca80211107a5db9f4c4.pdf>.
- Garland, *Absolute convergence of Eisenstein series on loop groups*, Duke Math. J.
  135 (2006), DOI 10.1215/S0012-7094-06-13521-4, is the convergence reference.
- Garland–Miller–Patnaik, *Entirety of cuspidal Eisenstein series on loop groups*,
  <https://arxiv.org/abs/1304.4913>, concerns cuspidal induction; it does not replace the
  requested minimal-parabolic ξ-denominator construction.
- **Novelty verdict: BRIDGE.** The requested theorem and the affine rank-one formulas
  below are established mathematics. No claim of new scientific knowledge.

## Dependency order

1. Concrete untwisted affine `A₁` root datum, affine Weyl action, and inversion sets;
   actual ξ coefficients with proved denominator nonvanishing in the entire Godement
   chamber. This supplies the first nontrivial loop-group case, without reducing the
   overall target to its constant-term formula.
2. Affine weight/Cartan action with central and degree coordinates; quadratic translation
   decay; absolute and locally uniform convergence of the affine Weyl constant-term sum.
3. Completed central extension, arithmetic subgroup, root subgroups, Iwasawa coordinates,
   and the degree rotation. The central extension and completion cannot be omitted.
4. Arithmetic coset series, absolute convergence, invariance, and the unipotent quotient's
   probability measure.
5. Bruhat unfolding and local intertwining integrals; the rational Euler product must
   produce the literal coefficient above. Identify the integral of the constructed
   Eisenstein series with its affine Weyl expansion.
6. Subsequent extension: general untwisted affine root data, reusing rather than replacing
   the rank-one inputs. The actual loop-`SL₂` arithmetic series remains the first target.

## Dependency-closed first proof: affine A₁ inversion sets

Write a real root as `plus n = α+nδ` or `minus n = -α+nδ`, `n ∈ ℤ`. Positivity means
`n ≥ 0` in the first family and `n > 0` in the second. The Weyl group is the actual
infinite dihedral group, with elements `r m` and `sr m`, `m ∈ ℤ`.

Its action is

\[
\begin{array}{c|cc}
 & α+nδ & -α+nδ\\ \hline
r_m & α+(n-2m)δ & -α+(n+2m)δ\\
sr_m & -α+(n-2m)δ & α+(n+2m)δ.
\end{array}
\]

The multiplication rules `r_i r_j=r_{i+j}`, `r_i sr_j=sr_{j-i}`,
`sr_i r_j=sr_{i+j}`, and `sr_i sr_j=r_{j-i}` verify the action by substitution.
The simple reflections are `s₁=sr 0`, `s₀=sr (-1)`; `s₀s₁=r 1`.
Thus every translation is an integer power of `s₀s₁`, and every reflection is
`s₁` times such a power. The image of `α` determines both the sign and `m`, so the
action is faithful.

Intersecting positivity with negativity of the image gives exact finite inversion sets:

\[
\begin{aligned}
I(r_m)&=\{α+nδ:0≤n<2m\}\;\sqcup\;\{-α+nδ:0<n≤-2m\},\\
I(sr_m)&=\{α+nδ:0≤n≤2m\}\;\sqcup\;\{-α+nδ:0<n<-2m\}.
\end{aligned}
\]

Empty integer intervals handle all negative endpoints. In particular `I(s₁)={α}`
and `I(s₀)={δ-α}`; both simple reflections occur, and translations of arbitrarily
large length occur. This is not a finite Weyl-group substitute.

## Dependency-closed first proof: the actual ξ denominators

Parametrize each chamber coordinate without an assumed analytic input by
`q(z)=1+exp(Re z)+i Im z`, `z ∈ ℂ`. Its image is exactly `Re s>1`: positivity of
the exponential proves inclusion, and `z=log(Re s-1)+i Im s` gives the inverse.
For arbitrary `z₀,z₁∈ℂ`, let `λ_i=q(z_i)` and `κ=λ₀+λ₁`.

The real coroot arguments are
`λ((α+nδ)∨)=nλ₀+(n+1)λ₁` and
`λ((-α+nδ)∨)=nλ₀+(n-1)λ₁`.
For a positive root their real parts exceed one: in the first case `n≥0` and
the second coefficient is at least one; in the second case `n≥1` and the first
coefficient is at least one. Hence both `ξ(argument)` and `ξ(argument+1)` are
nonzero. Indeed `ζ(s)=ξ(s)/Γℝ(s)` for `Re s>1`, and Euler-product nonvanishing
of ζ rules out `ξ(s)=0`. Finite products are therefore nonzero, and multiplying
`c_w` by its literal ξ-denominator product recovers its numerator product.
No nonvanishing, convergence, or constant-term identification is postulated.

The argument bound is quantitative: every positive-root argument has real part at least
`min(Re λ₀, Re λ₁)`. The interval cardinalities give `#I(r_m)=|2m|` and
`#I(sr_m)=|2m+1|` exactly.

## Dependency-closed coefficient-growth proof

Set `δ=min(Re λ₀,Re λ₁)-1>0` and `B=2/δ`. Write `Ξ(s)=s(s-1)ξ(s)/2` for the
entire completion. The corpus theorem
`RHTower.SelbergThetaHorizontalBoundary.norm_scatteringCore_le`, at `z=s-1`, gives
`|Ξ(s)/Ξ(s+1)|≤1` for `Re s>1`. Its stated assumptions and transitive axioms were
checked: no RH premise; only `propext`, `Classical.choice`, `Quot.sound`.
The parent result is the Lagarias–Suzuki shift-modulus theorem, not a new result:
<https://arxiv.org/abs/math/0412039>.

For every inversion argument `s`, normalization and proved nonvanishing give

\[
 \frac{ξ(s)}{ξ(s+1)}=\frac{s+1}{s-1}\frac{Ξ(s)}{Ξ(s+1)},\qquad
 \left|\frac{ξ(s)}{ξ(s+1)}\right|
 \le 1+\frac{2}{|s-1|}\le1+\frac2δ\le e^{2/δ}.
\]

Here `|s-1|≥Re s-1≥δ`, and the first estimate uses `s+1=(s-1)+2`.
Multiplying over the exact inversion set proves
`|c_w(λ)|≤exp(B #I(w))`. In particular the translation and reflection bounds are
`exp(B|2m|)` and `exp(B|2m+1|)`. Every input is already proved; the next Lean
module must formalize these exact bounds before they count as established.

## Degree-rotation calculation for the next convergence theorem

An affine weight has coordinates `(κ,b,d)=(λ(c),λ(h₁),λ(D))`. The Weyl action is

\[
 r_m(κ,b,d)=(κ,b+2mκ,d-mb-m^2κ),\quad
 sr_m(κ,b,d)=(κ,-b-2mκ,d-mb-m^2κ).
\]

Direct substitution verifies the four dihedral multiplication laws, preserves the
central coordinate, and preserves `b²+4κd`. Substitution into the two real-coroot
strings also proves `(wλ)(β∨)=λ((w⁻¹β)∨)`, so the root and weight actions are dual.
For `λ=(λ₀,λ₁)` set `κ=λ₀+λ₁`,
`b=λ₁`, `d=0`, and `ρ=(2,1,0)`. At logarithmic torus/rotation coordinates
`H=t h₁+z c-rD`, `r>0`, the exponent `(-wλ-ρ)(H)` is

\[
\begin{aligned}
 r_m &: -(b+1)t-(κ+2)z+(-2κt-rb)m-rκm^2,\\
 sr_m &: (b-1)t-(κ+2)z+(2κt-rb)m-rκm^2.
\end{aligned}
\]

The common quadratic coefficient has strictly negative real part because
`r Re κ>0`. Together with the coefficient bounds this yields Gaussian summability
of both integer-indexed families. These calculations describe the actual affine
degree term; using only the finite root coordinate would lose this convergence.
The Weyl sum will be named as such until the arithmetic-series unfolding is proved.

For completeness, the summability implication has an explicit geometric majorant.
For `a>0`, real `B,C`, and real `x`, expanding the nonnegative square
`(2a|x|-(B+1))²` gives

\[
 C+B|x|-ax^2\le C+\frac{(B+1)^2}{4a}-|x|.
\]

Thus the corresponding exponential on `ℤ` is bounded by a constant times
`exp(-|m|)`. The latter is summable by splitting into its two geometric tails;
this is already `HTGeometry.summable_exp_neg_abs_int` in Lean (standard-axiom
audit passed). For each Weyl family take `a=r Re κ`,
`B=2 coefficientRate+|linearCoefficient|`, and
`C=constantCoefficient+coefficientRate`. The inequality
`|2m+1|≤2|m|+1` handles reflections; translations satisfy the same bound.
The exact norm formulas above and `linearCoefficient*m≤|linearCoefficient||m|`
prove domination. Finally `W ≃ ℤ ⊕ ℤ` joins the two summable families. This
proves absolute convergence of the full affine Weyl sum for every Godement
parameter, every real torus coordinate, and every positive rotation, without
postulating convergence or any group-level constant-term identity.

## Open core and completion audit

The completed sub-result is [absolute convergence of the full affine A₁ Weyl
sum](../3-formalized/garland-affine-a1-weyl-sum.md), with the exact paper proof,
declaration map, and saved transitive axiom audit. It includes root/weight duality,
exact inversion sets and lengths, all ξ denominator nonvanishing, exponential
coefficient bounds, actual degree-rotation exponents, and Gaussian domination.

| Required component | Current authoritative status |
| --- | --- |
| Actual ξ denominator products | Formalized; `xiDenominator_ne_zero`, `xiCoefficient_mul_denominator` |
| Infinite affine Weyl group and action | Formalized; actual `DihedralGroup 0`, faithful root action, dual weight action |
| Absolute convergence of affine Weyl expansion | Formalized; `summable_norm_weylTerm`, `hasSum_weylTerm` |
| Locally uniform convergence of this expansion | Still open |
| Formal Laurent central extension | Formalized; exact kernel `Fˣ`, both root splittings, inverse tame-symbol torus defect |
| Rational-to-real central loop embedding | Formalized and audited; injective coefficient-field map, center/root compatibility |
| Garland completion comparison and arithmetic subgroup | Still open |
| Group-level degree rotation | Formalized; tame-cocycle-preserving action, semidirect product, every positive real contraction, affine-root scaling |
| Affine simple coroots and Cartan coordinates | Formalized; actual root words, `h₀(a)=z(a)h₁(a⁻¹)`, injective central/finite torus |
| Actual Weyl conjugation on Cartan and degree rotation | Formalized and audited; quadratic central shift, finite reflection, intrinsic complex characters, exact affine-weight comparison |
| Positive power-series subgroup splitting | Formalized and audited; injective `LoopSL2.positiveEmbedding`, both root restrictions |
| Positive Iwahori and unipotent coordinates | Formalized and audited; full Gauss equivalence, exact unipotent kernel, unique central/finite/unipotent Borel factors |
| Affine Bruhat decomposition of the actual central extension | Formalized and audited; `LoopSL2.exists_unique_bruhat`, unique infinite-dihedral double-coset label |
| Two simple rank-one subgroups | Formalized and audited; both injective homomorphisms, exact root maps, and simple coroot restrictions |
| Group-level Iwasawa existence | Formalized and audited; `LoopSL2.exists_iwasawa` for every actual real Laurent central-loop element |
| Uniqueness of absolute Iwasawa torus coordinates | Compact–Borel intersection proof in progress |
| Arithmetic coset Eisenstein series and its convergence | Still open |
| Unipotent quotient measure and constant-term integral | Still open |
| Bruhat unfolding identifying that integral with `weylSum` | Still open |

**[OPEN CORE]** Construct the completed central loop group and its arithmetic series,
then prove the convergence and unfolding statements. The full objective stays active.
A convergent Weyl expansion cannot be advertised as a constructed arithmetic
loop-group Eisenstein series.

## Next group-level dependency audit

Corpus leads, with statements inspected:

- `HTGeometry/SteinbergGroupPresentation.lean`: a presented Steinberg group and its
  elementary root generators. Its perfectness argument needs a third distinct index.
- `HTGeometry/SteinbergRowCentrality.lean`, `KTwo_mem_center`: centrality requires an
  index outside the support of the word. It does **not** certify the needed rank-one
  loop central extension by substitution of `Fin 2`.
- `HTGeometry/MilnorKTameValuation.lean`, `tameDataOfValuation` and
  `tameHomOfValuation`: the actual tame-symbol homomorphism is constructed from an
  integer-valued valuation. This is a possible central-extension ingredient, not
  a loop-group construction or an Iwasawa theorem.

The [rank-one Kubota construction](../3-formalized/garland-sl2-kubota-central-extension.md) now
supplies a direct alternative. Its Milnor-valued cocycle identity, exact central
extension, injective root splittings, and inverse-symbol torus defect have Lean
proofs. The actual Laurent tame map constructs the extension by the coefficient
field's units. Constant/uniformizer normalization and all final source/axiom
audits passed. This does not yet identify the algebraic group with Garland's
completed Chevalley model or construct its arithmetic series.

The [degree-rotation construction](../3-formalized/garland-loop-degree-rotation.md)
is formalized and audited. Coefficientwise Laurent scaling preserves valuation,
residue, and the actual tame cocycle, giving a central-fixing action and the
rotation semidirect product. Its action on all affine real-root elements agrees
with their degree labels. Positive real contractions cover exactly `(0,1)`.

The [simple-coroot construction](../3-formalized/garland-affine-simple-coroots.md)
proves `h₀(a)=z(a)h₁(a⁻¹)` from the actual root words. Its Cartan embedding is
injective, identifying the central sign and coordinates in the affine weight
model. The [positive-loop splitting](../3-formalized/garland-positive-loop-splitting.md)
constructs the lift of `SL₂(F[[X]])` using the actual tame cocycle and elementary
generation over the power-series ring. Its projection is faithful and it agrees
with both canonical root embeddings. All five source checks and the transitive
axiom audit passed.

The [rational coefficient embedding](../3-formalized/garland-rational-loop-embedding.md)
is formalized and audited: the coefficientwise field map preserves the actual
tame symbol and lifts faithfully to the central extension. Its specialization
gives `LoopSL2 ℚ →* LoopSL2 ℝ`, with exact center/root compatibility.
[Positive Iwahori coordinates](../3-formalized/garland-positive-iwahori.md)
are formalized and audited, including unique central/finite/unipotent Borel
coordinates. [Actual Weyl conjugation](../3-formalized/garland-weyl-cartan-conjugation.md)
and its intrinsic complex-character comparison are formalized and audited. No Iwasawa or arithmetic-series theorem has been assumed.

For the subsequent global matrix decomposition, corpus search found
`SmithNormalFormDVR.exists_smithNormalForm` over an actual discrete valuation
ring. Its statement and clearing proof were inspected. Mathlib supplies the
`IsDiscreteValuationRing (PowerSeries F)` instance. The specialization and
transitive axiom audit remain unchecked and this theorem is not imported by
the current construction. A direct rank-two
[Iwahori–Bruhat proof](../3-formalized/garland-affine-bruhat-decomposition.md)
is formalized and audited, using four pivot cases and lattice-chain valuation
invariants. Its exact central lift gives unique affine Weyl labels over both
the rationals and reals. The
[two simple rank-one subgroups](../3-formalized/garland-simple-rank-one-subgroups.md)
are formalized and audited. The
[Iwasawa existence proof](../3-formalized/garland-real-iwasawa-existence.md)
is also formalized and audited: two vertex parabolics generate the entire
central group, and ordinary real Iwasawa supplies their Borel–rotation factors. The separate
[compact–Borel intersection proof](garland-compact-borel-intersection.md)
uses alternating words and Laurent boundary coefficients to control central
and finite torus coordinates. The
[determinant-metric route](../0-backlog/garland-determinant-metric-iwasawa.md) remains an
alternative for more general root data.

Do not instantiate the stable Steinberg centrality theorem outside its hypotheses.

## Work log

- 2026-10-29: Current tree and primary source audited; exact normalization fixed;
  dependency-closed first proof recorded before Lean implementation. No earlier
  loop-group progress was verifiable from the supplied continuation; treated as
  no progress for the continuation audit, then advanced the actual worktree.
- 2026-10-29: Five Lean leaves built and the full affine Weyl convergence theorem
  checked. Transitive axiom audit passed with only the three standard axioms.
  Programme and finished sub-result recorded separately; full goal remains active.
- 2026-10-29: Final source audits all exited 0, without warnings, using
  `lake --old env lean GaloisForLFunctions/HTGeometry/LoopEisenstein/<Module>.lean`
  separately for `AffineA1Roots`, `AffineA1XiCoefficients`, `AffineA1XiEstimates`,
  `AffineA1Weights`, and `AffineA1WeylSum`. No umbrella or full build was run.
  Both umbrellas are wired. Owned scratch files were removed; unrelated work was
  preserved. This goal turn is **progress**, not a wait or blocked turn.
- 2026-10-29: Constructed and audited the rank-one Laurent central extension in
  five additional modules. The Kubota cocycle, exact central kernel, injective
  root groups, inverse tame torus defect, and constant/degree commutator are
  formalized. Saved axiom audit contains only the three standard axioms. Full
  objective remains active; degree rotation is in progress.
- 2026-10-29: Degree rotation completed in three further modules. Final direct
  source checks and saved transitive axiom audit passed. Iwasawa decomposition,
  arithmetic-series convergence, and constant-term unfolding remain open.
- 2026-10-29: The Weyl-word symbol identity and affine simple coroots completed
  in two further modules. The Cartan torus is injective. Final direct source
  checks and the saved transitive axiom audit passed; positive-loop splitting
  is the next group-level dependency.
- 2026-10-29: Positive-loop splitting completed in five modules. The explicit
  bottom-row correction satisfies both elementary multiplication laws, hence
  defines an injective homomorphism on the full power-series matrix group.
  Final individual source checks and the saved axiom audit passed.
- 2026-10-29: Coefficient-field embeddings completed in two modules, including
  the faithful rational-to-real central loop embedding. Both final direct
  source checks and the saved transitive axiom audit passed.
