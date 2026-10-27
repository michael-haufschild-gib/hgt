# The successor-visible dilation spectrum is absolutely continuous

- **ID:** successor-visible-spectrum-is-absolutely-continuous
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ArithmeticPositiveDuality README, open topic 6; prescribed successor coordinates
- **Statement:** A finite archimedean dilation measure admits a nonblind positive-definite affine extension exactly when its absolutely continuous part is nonzero.

## Goal

Resolve the stated singular-continuous spectrum question by a positive
classification, including realization of every nonzero absolutely continuous
part. The existing atomic blindness theorem and compactly supported
autocorrelation examples leave this distinction open.

Let ν be a finite positive measure on ℝ and let φ be positive definite on
Aff(ℚ), with positive-slope dilation coefficient
`φ(dilation u) = ∫ exp(i γ log u) dν(γ)`.
The proposed quantitative classification is

`|φ(translation b) − φ(translation b')| ≤ 2 ν_ac(ℝ)` for nonzero b,b',

where ν_ac is the Lebesgue absolutely continuous part. In the reverse
direction, every ν with nonzero ν_ac should have such an extension whose
successor coefficient is nonconstant away from zero. Prove the decomposition
underlying the bound; do not insert it as a premise or count blindness alone.

## Gates

- [x] Concrete open question and existing exact interfaces located and read.
- [ ] Corpus novelty audit of regularization and affine spectral decomposition.
- [ ] Dependency-closed paper proof of necessity and positive realization.
- [ ] Exact Lean formalization, individual source checks, transitive axiom audit.
- [ ] Significance audit against the stated APD frontier.

## Existing inputs

`TheSuccessorOscillationIsBoundedByTheContinuousDilationMass` bounds the
oscillation by twice the nonatomic mass and proves atomic blindness.
`AContinuousArchimedeanSpectrumIsSeenByTheSuccessor` constructs nonblind
extensions for autocorrelations of nonzero continuous compactly supported H.
`TheSuccessorSeesOnlyTheContinuousDilationSpectrum` supplies the affine GNS
representation, its dilation spectral norm identity, and finite-atom splitting.
The integer-successor Kronecker-null theorem concerns a different restriction;
it must not be presented as a solution of the singular-continuous question.

## Approach and unresolved dependencies

The dilation-cyclic subspace has a strongly continuous real dilation action
because its coefficients are Fourier transforms of finite measures on ℝ.
Affine conjugation expresses a coefficient at nonzero translation b using
two dilation-orbit vectors and the fixed operators at translations ±1.
This gives continuity off b=0, but does not make the full representation
continuous. That distinction is essential.

Conjectural decomposition: project onto vectors with continuous translation
orbits. The projection commutes with rational affine operations. Its
translation-invariant subspace is blind; its nontrivial translation spectrum
should have absolutely continuous dilation spectrum. The remaining component
should contribute only at translation zero. These assertions still require
proof: neither a real-affine representation theorem nor a regularization
decomposition is currently available as a checked input.

For sufficiency, write dν_ac = w dγ, take an L² inverse Fourier transform of
√w, and extend the existing real-affine vector-state construction from C_c
to L². Its successor is the Fourier transform of a nonzero positive measure
on positive translation frequencies and is nonconstant. Add a blind affine
state carrying ν−ν_ac, using extension from the dilation subgroup. This
would realize exactly the prescribed ν rather than only a dense family.

## No-go closure

Not retired. If the proposed decomposition fails, identify a concrete
singular-continuous nonblind extension and formalize its positive realization.
No contribution is credited while either direction remains conjectural.

## Refined proof architecture

For the positive-slope affine group, write D(a) for dilation and U(b) for
translation in the rational GNS representation, and v for its cyclic vector.
The ν identity makes a ↦ D(a)v norm-continuous in log a and extends this
orbit to every positive real a. For b≠0 the coefficient has the expression

`⟨D(|b|)⁻¹ v, U(sign b) D(a/|b|) v⟩`.

This defines a continuous extension away from b=0. On b=0 use the original
Fourier transform of ν. Positivity of the real-affine extension should follow
by approximating a finite family of affine elements with rational ones while
preserving every equality among their translation coordinates. This preserves
which pairwise quotients have zero translation; arbitrary approximation would
not suffice at that discontinuity.

Regularization can be proved through weak translation integrals, without
assuming the whole GNS representation is continuous. For f∈C_c(ℝ), define
`A_f=∫ f(b)U(b) db` weakly by Hilbert-space Riesz representation. Its range
has continuous translation orbits because L¹ translation is continuous.
The closed span of these ranges is invariant under translations and dilations,
so its orthogonal projection commutes with both. On its orthogonal complement
all weak translation integrals vanish, hence matrix coefficients vanish almost
everywhere. Their already established continuity off b=0 then makes them zero
there. The resulting singular component is blind, with no spectral assumption
inserted into the definition.

On the continuous-translation component, a route to absolute continuity avoids
a full irreducible-representation classification. Filter translation spectrum
into a compact frequency band bounded away from zero. Sufficiently separated
dyadic dilates of that band are disjoint, so its dilation iterates are mutually
orthogonal. The spectral measure of the discrete dilation then is Haar on the
circle; its real spectral measure must be Lebesgue absolutely continuous.
Approximate the complement of translation-invariant vectors by these filters.
The needed spectral-filter construction, density argument, and passage from
norm approximation to absolute continuity still require complete proofs and
Lean implementations. This is a route, not a completed paper proof.

## External audit

The measurable positive-definite regularization step is classical, not a new
contribution: H. Langer's 1983 paper, page 282, recalls the continuous plus
almost-everywhere-zero decomposition and attributes the locally compact group
case to von Neumann and Segal; its reference is Hewitt–Ross, volume II.
[Primary paper](https://acta.bibl.u-szeged.hu/14894/1/math_045_281-292.pdf).
Corpus searches have not located a usable Lean version. No external theorem
is being added as an axiom. The potential contribution is the exact affine
visibility/realization theorem under the existing rational-group hypothesis,
subject to its own novelty and significance audit.

### Band argument to replace irreducible decomposition

If a vector has translation spectral support in `[α,β]`, where 0<α<β,
choose L>log(β/α). Its translates under D(exp(nL)), n∈ℤ, have disjoint
translation spectral supports. Their mutual inner products vanish. Thus the
real dilation measure μ of that vector obeys `μ̂(nL)=0` for n≠0.
Periodizing μ modulo 2π/L gives its total mass times normalized Haar measure,
by uniqueness of circle Fourier coefficients. Every restricted period of μ
is dominated by that Haar measure, so μ is Lebesgue absolutely continuous
(indeed its density is bounded by L μ(ℝ)/(2π)). The negative translation
frequency bands give the same argument.

Taking the closed span of these bands excludes only translation-invariant
vectors. Absolute continuity must be passed through norm convergence of
vectors, not weak convergence of measures: the latter does not preserve it.
One usable domination is `μ_v ≤ 2 μ_w + 2 μ_(v−w)`, obtained from the
spectral quadratic form, with `μ_(v−w)(ℝ)=‖v−w‖²`. This yields the desired
null-set conclusion by approximation. The corpus supplies real Bochner
representation in `HTGeometry.BochnerPositiveDefiniteReal`; the compatible
spectral-band projections and their covariance are still to be constructed.

### Scalar Fourier filters supply the bands

Use integrated translation operators `A_f=∫ f(b)U(b) db`, with f Schwartz
and Fourier support in a compact interval avoiding zero. For two such
kernels, the identity for `⟨A_f u,A_g v⟩` involves the convolution of the
reflected conjugate of f with g. Disjoint Fourier supports make that
convolution zero by Fourier injectivity. Dilation covariance rescales those
supports. Consequently the preceding orthogonal-orbit argument applies
directly to every A_f v.

These ranges span the orthogonal complement of translation-invariant vectors.
Indeed, a vector orthogonal to every range is killed by every A_f, since the
adjoint kernel is in the same class. Its scalar translation measure μ, supplied
by Bochner, satisfies `‖A_f v‖² = ∫ |f̂|² dμ = 0`. Smooth frequency bumps on
each compact interval away from zero imply that μ is supported at zero.
Then `⟨v,U(b)v⟩=‖v‖²`, and the squared norm identity gives U(b)v=v.
The converse follows from f̂(0)=0.

Thus scalar Bochner measures, Fourier injectivity, and integrated operators
are enough for the band and density steps. No general operator-valued spectral
measure has to be presumed. Still needed in Lean: weak integral construction,
real-affine extension, translation regularization, integrated-filter calculus,
periodized-measure absolute continuity, and the L² realization of an arbitrary
density. The paper dependency audit remains open until these identities and
limit passages are written in full.

## Checked infrastructure and further reuse

`HTGeometry.WeakHilbertIntegrals` now proves weak Hilbert integration from
scalar measurability and an integrable norm majorant, plus bounded integration
of a weakly measurable unitary family against every L¹ kernel. Its individual
source check passed; main axiom lists contain only `propext`, `Classical.choice`,
and `Quot.sound`. It is wired into the HTGeometry umbrella. This is uncredited
analytic infrastructure, not the affine decomposition.

The corpus already proves `TheSuccessorInheritsTheRegularityOfTheDilations`:
the successor modulus is bounded by the dilation modulus. Reuse this for
off-zero continuity rather than reproduce that theorem.
`RHTower.PrimeCirclePeriodization.map_phase_eq_of_blind` already identifies
the periodized measure as Haar from vanishing lattice Fourier coefficients.
The remaining real-line absolute-continuity lift can be proved on each
fundamental interval using its measurable section, then a countable cover.

That lift is now checked in
`HTGeometry.LatticeFourierVanishingForcesAbsoluteContinuity`:
`absolutelyContinuous_of_addCircle_map` and
`absolutelyContinuous_of_lattice_charFun_zero`. The final individual source
check passed; the latter's transitive axiom list is standard only. The module
is imported by the HTGeometry umbrella; no umbrella build was run.

## Full decomposition argument under audit

The following closes the main logical passages in the proposed architecture;
its Lean implementation remains incomplete. It is not a new premise for the
final theorem.

1. **Real extension.** Put v_t=lim D(q_n)v whenever log q_n→t. The identity
   `‖D(q)v−D(r)v‖²=2(ν(ℝ)−Re ν̂(log r−log q))` gives a unique limit,
   independent of the sequence, and a uniformly continuous orbit. For b≠0
   define F(b,a) by the displayed two-orbit formula; put F(0,a)=ν̂(log a).
   For finitely many real affine elements (b_i,a_i), approximate their slopes
   independently by positive rationals and approximate each distinct b_i by
   one common rational sequence for its equality class. Distinct classes stay
   distinct eventually. Every entry F(g_i⁻¹g_j) then converges to its intended
   value, including exactly those with zero translation. The limit of each
   nonnegative finite Gram form is nonnegative. Thus F is positive definite
   and Borel, continuous on b≠0 and on the dilation subgroup.

2. **Weak regularization.** In F's GNS space define A_f x by its scalar
   pairings for f∈L¹(ℝ). Weak measurability follows first on finite linear
   combinations of cyclic orbit vectors from Borel measurability of F, then
   on all vectors by norm approximation. The proved weak-integration theorem
   gives `‖A_f‖≤‖f‖₁`. Translation and dilation covariance follow by scalar
   changes of variables. In particular
   `U(h)A_f=A_(f(·−h))`, and the L¹ continuity of translation makes each
   range vector translation-continuous. Let Hc be the closed span of these
   ranges. Unitarity makes continuity stable under norm limits. Covariance
   makes Hc reducing for every U(b) and D(a), so its orthogonal projection P
   commutes with them.

   If z∈Hc⊥, then `∫ f(b)⟨z,U(b)z⟩db=0` for every compactly supported
   continuous f. The bounded measurable scalar coefficient is therefore zero
   almost everywhere. For z=(1−P)v it is the difference of the original
   coefficient and the continuous coefficient of Pv, hence continuous off
   zero. It consequently vanishes at every b≠0. This component contributes
   nothing to the successor there.

3. **Strong dilation continuity on Hc.** The vector Pv has a continuous
   dilation orbit because P commutes with D. The vectors U(b)D(a)Pv span Hc:
   cyclicity of v and boundedness of P give totality. Dilation of such a vector
   is `U(e^t b)D(e^t a)Pv`, which varies continuously by translation continuity
   and the orbit continuity of Pv. Uniform operator norm one extends this to
   all of Hc. Thus scalar Bochner measures exist there for both actions.

4. **Nontrivial translation bands.** For a Schwartz kernel f, integration and
   Fubini give `A_f* A_g=A_(f̃*g)`, with f̃(t)=conj f(−t). Fourier injectivity
   makes this zero when the Fourier supports of f and g are disjoint. If f̂ is
   supported in [α,β] with 0<α<β, choose L>log(β/α). D(exp(nL))A_f x lies
   in the filter range with frequency band exp(−nL)[α,β]. These bands are
   pairwise disjoint, so the orbit vectors are orthogonal. The dilation
   measure of A_f x has zero Fourier coefficients at nonzero multiples of L.
   Existing circle uniqueness identifies its phase measure as Haar. On every
   fundamental interval the original measure is dominated by the pullback of
   that Haar measure through the measurable section. A countable interval
   cover proves absolute continuity on ℝ. Negative bands give the same result.

5. **Density and measure limits.** If x is orthogonal to every such filter
   range, adjoint closure of the filter class implies A_f x=0 for all f.
   Scalar Bochner representation and Fubini give
   `‖A_f x‖²=∫|f̂(−γ/(2π))|²dτ_x(γ)`.
   Smooth bumps with compact support in rational intervals avoiding zero
   force τ_x to be supported at zero. Then
   `‖U(b)x−x‖²=2(τ_x(ℝ)−Re τ̂_x(b))=0`.
   Conversely a translation-invariant vector is annihilated by every filter
   because f̂(0)=0. The filter ranges therefore span precisely the orthogonal
   complement of the translation-invariant subspace H0 in Hc.

   For dilation Bochner measures, the parallelogram identity and uniqueness
   give `μ_(x+y)+μ_(x−y)=2μ_x+2μ_y`. Hence
   `μ_x≤2μ_y+2μ_(x−y)` and `μ_(x−y)(ℝ)=‖x−y‖²`.
   A norm limit of vectors with absolutely continuous measures also has an
   absolutely continuous measure: apply the inequality to each Lebesgue null
   set and send the norm error to zero. Finite sums of band vectors have the
   same property by the inequality. Thus all of Hc∩H0⊥ has absolutely
   continuous dilation spectrum.

6. **The bound.** H0 is closed and reducing for dilations. Split v into its
   Hc⊥, H0, and Hc∩H0⊥ components. Their dilation measures add to ν, by
   orthogonality and uniqueness. The first successor coefficient vanishes off
   zero; the second is constant. The third has measure μvis≪Leb and μvis≤ν,
   hence μvis≤ν_ac by maximality of the absolutely continuous part. Its
   vector-state coefficient has modulus at most ‖vvis‖²=μvis(ℝ), giving
   the claimed oscillation bound `2ν_ac(ℝ)`.

7. **Every density is realized.** Write dν_ac=w(γ)dγ. Under the convention
   `f̂(ξ)=∫f(x)e^(−2πixξ)dx`, choose H∈L² with
   `|Ĥ(ξ)|²=2πw(2πξ)` by the inverse unitary Fourier transform. Plancherel
   gives `⟨H,H(·+t)⟩=∫e^(iγt)dν_ac(γ)`. The real positive-affine vector
   state `∫e^(ib exp x)H(x+log a)conj H(x)dx` is well-defined by
   Cauchy–Schwarz and positive definite by its Gram form. Extend by zero
   outside the positive-slope subgroup. Its translation coefficient is the
   characteristic function of the finite measure `exp_*(|H|²dx)`. This
   measure has positive mass and gives {0} mass zero. If the successor were
   constant on nonzero rationals, continuity would make its characteristic
   function constant everywhere. Fourier uniqueness would make the measure
   its mass times δ₀, a contradiction. Add the blind state
   `∫|a|^(iγ)d(ν−ν_ac)(γ)` to obtain exactly the prescribed dilation measure.

The main unresolved work is formal, plus the final novelty/significance audit.
In particular, regularization, filter density, scalar spectral domination,
and arbitrary L² realization must each be proved; none is an admissible
assumption in the final affine theorem.

## Significance caution from the wall audit

Wall 3.16 asks for a self-dual identity with its gap on the spectral side;
its positive survivor is source-prescribed mixed data. The proposed
classification alone supplies neither. In particular Weil's discrete spectrum
was already covered by atomic blindness. Closing README topic 6 therefore does
not by itself justify significant RH-contribution credit. Keep that gate open;
no count change follows from formalizing the classification or its helpers.

The strongly continuous real-affine representation mechanism is also classical:
the 1996 paper by W. Tomé recalls the two faithful irreducible unitary
representations (positive and negative translation generator), page 206.
[Primary paper](https://www.numdam.org/item/AIHPA_1996__65_2_175_0.pdf).
The rational-group extension and exact visibility statement require their own
audit; no absence claim follows from the web searches.

The L² vector-state extension is now checked in
`APD.EverySquareIntegrableWaveHasAVisibleSuccessor`.
`successor_sees_L2_autocorrelation` realizes every nonzero square-integrable
wave and proves its successor nonconstant on the nonzero rationals. The final
individual source check and transitive axiom audit passed; its umbrella import
is present. This closes the vector-state part of step 7, not the realization
of an arbitrary prescribed density or the necessity direction.

`HTGeometry.AbsolutelyContinuousMeasuresAreAutocorrelations` now proves
`exists_L2_autocorrelation_eq_charFun`: every finite absolutely continuous
measure is the exact translation-autocorrelation law of an L² wave, whose
squared norm equals its mass. The individual source and main axiom audits
passed; the HTGeometry umbrella imports it. The remaining realization step
is composition with the affine state and addition of the singular measure
as a blind state. Necessity remains open in Lean.

Further corpus reuse: `RHTower.Suzuki.SuzukiCanonicalL1Translation` proves
strong continuity of real L¹ translation, directly through mathlib
`Continuous.compMeasurePreservingLp`. Use that mechanism for weak-integral
regularization; do not assume strong measurability of the unregularized
Hilbert-valued orbit. `EveryPointOfTheAtomicBoxIsAnExtension` also provides
`IsPosDefOnGroup.of_tendsto`. Real-affine approximation needs its finite-Gram
closed-cone argument, since rational coordinate approximants are not group
homomorphisms.

## Positive realization completed

The entire sufficiency direction is now formalized, including every finite
prescribed measure with a nonzero absolutely continuous part and an arbitrary
singular remainder. Exact statement, paper proof, declaration map and audits:
[positive realization](../3-formalized/every-absolutely-continuous-dilation-part-has-a-visible-successor.md).
`APD.EveryDensityHasAVisibleAffineExtension` passed its final individual source
check; all three main axiom lists are standard only. Its umbrella import is
present. This completes step 7. Necessity, its oscillation bound, and the
significance gate remain open. Accepted count remains **0 / 250**.

## Significance-driven deferral

The sufficiency theorem is preserved in the linked stage-3 card; necessity
remains unproved in Lean. Further classical regularization/filter formalization
is deferred as a route to the requested RH contributions. The proposed
classification does not address the source-prescribed mixed-data wall, and the
atomic case already covers Weil's spectrum. This is a failed significance gate,
not a mathematical counterexample or a claim that the classification is false.
The strongest checked positive survivor is exact realization of every finite
measure with nonzero absolutely continuous part, including its arbitrary
singular remainder. No positive survivor is omitted from formalization.
