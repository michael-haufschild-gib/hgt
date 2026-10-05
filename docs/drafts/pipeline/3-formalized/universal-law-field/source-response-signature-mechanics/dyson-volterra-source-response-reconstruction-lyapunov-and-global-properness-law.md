# Dyson--Volterra source response, positive formation, and global properness law

- **ID:** ULF-SRSM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** One cyclic dissipative source and its legal generator interventions canonically
  generate the complete ordered response tower, its positive Gram response, its inverse
  reconstruction cost, and its cofinal closed-range obstruction.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM, NOT ROUTE]`
  `[RESPONSE MAPS GENERATED] [FOUR-ORGAN FUSION] [FUNCTIONAL-EQUATION NEUTRAL]`
  `[GLOBAL PROPERNESS CLASSIFIED] [LEAN-PROVED] [NOT RH]`

## 1. Why this theorem changes the field programme

Most universal-law candidates begin with response maps

\[
 \rho_i:V\longrightarrow W_i
\]

and then prove reconstruction, positivity, synchronization, or properness.  This leaves the main
constitutive question untouched: why were those response maps legal, and why should their metric
strength be source-defined rather than fitted after seeing a failed route?

This theorem replaces supplied response maps by a source evolution.  A positive generator `L`, a
marked cyclic seed `v`, and legal perturbations `K` force their own responses through Duhamel's
formula.  The same forced response then generates:

1. an ordered noncommutative word tower;
2. a coefficient-faithful time packet;
3. a positive formation Gramian and its Sylvester response;
4. a least-response energy and exact global closed-range test.

The functional equation can act on the entire construction, but an invertible symmetry acts by
isometries and is therefore information-neutral.  Selection can only come from a source theorem
forcing a response to vanish together with a source-generated lower response bound.

## 2. Finite source setup

Let `H` be a nonzero finite-dimensional complex Hilbert space.  Let

\[
 L=L^*>0
 \tag{SR.1}
\]

and choose `v in H` cyclic for `L`:

\[
 \operatorname{span}\{L^n v:n\ge0\}=H.
 \tag{SR.2}
\]

Put

\[
 S_t=e^{-tL},\qquad x(t)=S_tv,\qquad P=|v\rangle\langle v|.
 \tag{SR.3}
\]

Let `E=Herm(H)` be the finite-dimensional real Hilbert space of self-adjoint interventions, with
Hilbert--Schmidt norm.  For `K in E`, define its first source response

\[
 \boxed{
 Y_K(t)=-\int_0^t S_{t-s}K S_s v\,ds.}
 \tag{SR.4}
\]

For `T>0`, define the response operator and response work

\[
 \mathcal R_T:E\longrightarrow L^2([0,T];H),
 \qquad \mathcal R_TK=Y_K,
 \qquad \mathcal W_T(K)=\|Y_K\|_{L^2}^2.
 \tag{SR.5}
\]

Finally define the infinite-time source Gramian

\[
 G=\int_0^\infty |x(t)\rangle\langle x(t)|\,dt.
 \tag{SR.6}
\]

All integrals are ordinary finite-dimensional Bochner integrals.

## 3. Main theorem

### Theorem 3.1 — generated response, reconstruction, and positive fusion

Under `(SR.1)`--`(SR.6)`, for every `T>0`:

#### I. Duhamel generation

For sufficiently small real `epsilon`, put

\[
 x_{\epsilon,K}(t)=e^{-t(L+\epsilon K)}v.
\]

Then

\[
 \boxed{
 \left.\frac d{d\epsilon}\right|_{\epsilon=0}x_{\epsilon,K}(t)=Y_K(t),}
 \tag{SR.7}
\]

and `Y_K` is the unique solution of

\[
 \boxed{
 Y_K'(t)+LY_K(t)=-Kx(t),\qquad Y_K(0)=0.}
 \tag{SR.8}
\]

Thus the response map is forced by the source evolution; it is not an observer choice.

#### II. Complete intervention reconstruction

The map `mathcal R_T` is injective.  More precisely,

\[
 \boxed{Kx(t)=-Y_K'(t)-LY_K(t)}
 \tag{SR.9}
\]

for every `t`, and the vectors `{x(t):0<=t<=T}` span `H`.  Consequently finitely many values
`x(t_1),...,x(t_d)` form a basis, and `(SR.9)` reconstructs the matrix `K` from the single response
history `Y_K`.

#### III. Source-generated positive work and finite properness

The quadratic form `mathcal W_T` is positive definite on `E`.  Hence there is a source-determined
constant `c_T>0` such that

\[
 \boxed{
 \mathcal W_T(K)\ge c_T\|K\|_{\mathrm{HS}}^2\qquad(K\in E).}
 \tag{SR.10}
\]

The response-work sublevels are compact.  If a sequence of legal interventions has vanishing
formed response, then it converges to zero:

\[
 \mathcal W_T(K_n)\to0\quad\Longrightarrow\quad K_n\to0.
 \tag{SR.11}
\]

#### IV. Positive Gram formation and the withheld Sylvester law

The Gramian `G` is positive definite and is the unique solution of

\[
 \boxed{LG+GL=P.}
 \tag{SR.12}
\]

For small `epsilon`, let

\[
 G_{\epsilon,K}=\int_0^\infty
 |x_{\epsilon,K}(t)\rangle\langle x_{\epsilon,K}(t)|\,dt.
\]

Its derivative is

\[
 \dot G_K=
 \int_0^\infty
 \bigl(|Y_K(t)\rangle\langle x(t)|
      +|x(t)\rangle\langle Y_K(t)|\bigr)\,dt,
 \tag{SR.13}
\]

and it satisfies the forced fourth-organ identity

\[
 \boxed{
 L\dot G_K+\dot G_KL=-(KG+GK).}
 \tag{SR.14}
\]

The positive Gram response still reconstructs every self-adjoint intervention.  Indeed,
`dot G_K=0` implies `KG+GK=0`, and positivity of `G` implies `K=0`.  Explicitly, from a measured
`dot G` first solve

\[
 B=-(L\dot G+\dot GL),
\]

then solve the positive Sylvester equation

\[
 KG+GK=B.
 \tag{SR.15}
\]

Both solutions are unique.  Thus source response, time history, and positive Gram response are
joint gauges of one intervention rather than independent organs.

#### V. Inverse-cost response

Put `C=G^{-1}`.  Its first variation is forced by

\[
 \boxed{\dot C_K=-C\dot G_KC.}
 \tag{SR.16}
\]

The determinant response is

\[
 \boxed{
 \left.\frac d{d\epsilon}\right|_0\log\det G_{\epsilon,K}
 =\operatorname{tr}(C\dot G_K).}
 \tag{SR.17}
\]

Equations `(SR.14)`--`(SR.17)` are withheld predictions: they were not used to define `Y_K`.
Every claimed Gram, inverse-cost, or determinant response arising from the same source intervention
must satisfy them.

#### VI. Functional-equation neutrality

Let `J` be a unitary involution satisfying

\[
 JL=LJ,\qquad Jv=\zeta v,\qquad |\zeta|=1.
 \tag{SR.18}
\]

For `K^J=JKJ^*`,

\[
 \boxed{
 Y_{K^J}(t)=\overline\zeta\,JY_K(t),
 \quad
 \dot G_{K^J}=J\dot G_KJ^*,
 \quad
 \mathcal W_T(K^J)=\mathcal W_T(K).}
 \tag{SR.19}
\]

Moreover `G` and `C` commute with `J`; kernels, singular values, reconstruction constants, inverse
costs, and determinant responses are transported isometrically.  An involutive functional-equation
action therefore cannot select the neutral intervention.  It only pairs equally informative
histories.

### Proof

For `(SR.7)`, write the difference quotient of the matrix exponential or differentiate the finite
dimensional ODE.  Variation of constants gives exactly `(SR.4)` and `(SR.8)`.

If `Y_K=0` in `L^2([0,T];H)`, continuity gives `Y_K(t)=0` for every `t`.  Equation `(SR.8)` gives
`Kx(t)=0`.  To see that `{x(t):0<=t<=T}` spans `H`, let `z` be orthogonal to all those vectors.
The analytic function

\[
 f_z(t)=\langle z,e^{-tL}v\rangle
\]

vanishes on an interval, hence all derivatives at zero vanish.  Therefore
`<z,L^n v>=0` for every `n`; cyclicity `(SR.2)` gives `z=0`.  This proves `(SR.9)` and injectivity.

Since `E` is finite dimensional, the continuous function
`K mapsto mathcal W_T(K)` has a positive minimum on the Hilbert--Schmidt unit sphere.  This is
`c_T` and proves `(SR.10)`--`(SR.11)`.

Differentiating `|x(t)><x(t)|` gives

\[
 \frac d{dt}|x(t)\rangle\langle x(t)|
 =-L|x(t)\rangle\langle x(t)|
  -|x(t)\rangle\langle x(t)|L.
\]

Integration over `[0,infinity)` proves `(SR.12)` because `x(t)->0`.  If `z^*Gz=0`, then
`<z,x(t)>=0` for every `t`; cyclicity gives `z=0`, so `G>0`.  The same identity with `L+epsilon K`
gives

\[
 (L+\epsilon K)G_{\epsilon,K}
 +G_{\epsilon,K}(L+\epsilon K)=P.
\]

Differentiate at zero to obtain `(SR.13)`--`(SR.14)`.  If `G` is diagonalized with eigenvalues
`gamma_i>0`, the matrix of `K mapsto KG+GK` has entries
`(gamma_i+gamma_j)K_ij`; it is invertible.  This proves `(SR.15)` and the reconstruction claim.
Differentiating `CG=1` and the standard finite-dimensional determinant identity proves
`(SR.16)`--`(SR.17)`.

Finally `(SR.18)` implies `JS_t=S_tJ` and `Jx(t)=zeta x(t)`.  Substitute into `(SR.4)` to obtain
the first identity in `(SR.19)`; the remaining statements follow by integration and unitary
invariance.  QED.

## 4. Ordered response tower and exact fusion

The first response is not the end of the mechanism.  Let `A` be a finite alphabet of legal source
interventions `(K_a)_(a in A)`.  For every word `w` in the free monoid `A*`, define operator-valued
responses recursively by

\[
 U_{\varnothing}(t)=S_t,
 \qquad
 U_{aw}(t)=-\int_0^tS_{t-s}K_aU_w(s)\,ds.
 \tag{SR.20}
\]

### Theorem 4.1 — Dyson--Chen formation law

Let `ell^1(A*)` denote the Banach convolution algebra of absolutely summable complex functions on
the free monoid, with word-concatenation product.  Regard

\[
 B=L\otimes\delta_{\varnothing}+\sum_{a\in A}K_a\otimes\delta_a
 \in\operatorname{End}(H)\widehat\otimes\ell^1(A^*).
\]

Its Banach-algebra exponential is well-defined.  The family `(U_w)` is the unique coefficient
system of the noncommutative perturbation expansion

\[
 \exp\!\left[-t\left(L+\sum_{a\in A}K_a a\right)\right]
 =\sum_{w\in A^*}U_w(t)w
 \tag{SR.21}
\]

in the completed tensor algebra.  It obeys:

1. **word equation**
   \[
   U_{aw}'(t)+LU_{aw}(t)=-K_aU_w(t),\qquad U_{aw}(0)=0;
   \tag{SR.22}
   \]
2. **time-fusion/deconcatenation**
   \[
   \boxed{
   U_w(t+s)=\sum_{w=uv}U_u(t)U_v(s);}
   \tag{SR.23}
   \]
3. **ordered-memory separation:** scalar mixed derivatives retain only sums over words with the
   same commutative content, whereas the free response tower retains each word separately;
4. **functional-equation covariance:** if `JK_aJ*=K_{sigma(a)}`, then
   \[
   JU_w(t)J^*=U_{\sigma(w)}(t).
   \tag{SR.24}
   \]

### Proof

Work degreewise in the tensor algebra; every fixed degree is finite.  Comparing word coefficients
in the ODE for `(SR.21)` gives `(SR.20)` and `(SR.22)`.  The semigroup identity

\[
 e^{-(t+s)B}=e^{-tB}e^{-sB},
 \qquad B=L+\sum_aK_aa,
\]

and comparison of the coefficient of `w` gives `(SR.23)`.  Passing from free letters to commuting
scalar parameters identifies all word orders with the same letter counts, proving clause 3.
Conjugating `(SR.21)` by `J` proves `(SR.24)`.  QED.

The noncommutative word tower is the exact source of schedule/orientation data.  Ordinary Taylor,
moment, determinant, and positive scalar reporters see symmetrized word sums unless a separate
ordered reporter is retained.

## 5. Cofinal global properness

The finite theorem has an exact infinite-dimensional boundary.  Let `mathcal E` and `mathcal Y` be
Hilbert spaces and let

\[
 \mathcal R:\mathcal E\longrightarrow\mathcal Y
 \tag{SR.25}
\]

be any bounded response operator obtained after admitting a Duhamel response tower in the chosen
completion.  Put `Q=mathcal R*mathcal R` and `N=ker mathcal R`.

### Theorem 5.1 — global response/properness classification

The following are equivalent:

1. `ran mathcal R` is closed;
2. there is `alpha>0` such that
   \[
   \|\mathcal RK\|^2\ge\alpha\operatorname{dist}(K,N)^2;
   \tag{SR.26}
   \]
3. the reduced positive response `Q|_(N^perp)` has a bounded inverse;
4. no unit sequence `K_n in N^perp` has `mathcal RK_n->0`.

When these conditions hold, vanishing or asymptotically vanishing full source response forces the
intervention to vanish modulo the exact invisible kernel.  If `mathcal R` is compact and
`N^perp` is infinite dimensional, none of the four conditions holds: an orthonormal intervention
sequence has a subsequence with response tending to zero.

### Proof

This is the bounded-below/closed-range theorem applied to
`mathcal R|_(N^perp)`.  The equivalence with clause 3 follows from
`<QK,K>=||mathcal RK||^2`.  If `mathcal R` is compact on an infinite-dimensional `N^perp`, apply
it to an orthonormal sequence; compactness and weak convergence to zero force a norm-convergent
subsequence with limit zero.  QED.

### Corollary 5.2 — functional equation cannot repair global formation

If a functional-equation action intertwines `mathcal R` by unitaries on intervention and response
spaces, it preserves `N`, closed range, `alpha`, the spectrum of `Q`, and every adaptive null
sequence.  It cannot turn a nonproper response tower into a proper one or select the neutral
intervention.  A successful selection law must provide an independent source identity forcing
full response to vanish and a source-derived proof of `(SR.26)`.

## 6. Exact five-frontier dictionary

This theorem does not identify unlike route receivers.  It gives them one generated mechanism and
five mathematically distinct failure modes.

| frontier obstruction | source-response signature meaning |
|---|---|
| singular source descent | a word response exists algebraically but not in the admitted response completion |
| all-prime oscillatory transport | imaginary/character contractions of the tower exist while the full response is not uniformly admitted |
| adaptive spectral orientation | least-response singular vectors migrate with aperture; fixed tests miss them |
| whole-space coercivity | `mathcal R` is injective but has nonclosed range, so `(SR.26)` fails |
| positive carrier existence | the carrier is the generated Gram `mathcal R*mathcal R`; existence requires admission of the response tower, not formal moments |

Further shadows are forced rather than postulated:

- recurrence is possible after contracting the ordered tower to a compact unitary character;
- open history is retained by word order and unwrapped time;
- hypertranscendence can only be claimed after proving that no finite word/prolongation quotient
  carries the complete source response;
- positive scalarization retains `mathcal R*mathcal R` and may erase word orientation;
- functional reflection acts as an isometry of the tower and is information-neutral.

## 7. Sharp no-go boundary

The theorem kills four common regressions.

1. **Choose response maps and prove a frame inequality.**  That starts after genesis.  Here
   `(SR.4)` and `(SR.20)` force every response from source evolution.
2. **Use one first commutator as the missing orientation.**  Scalar differentiation symmetrizes
   word orders.  Orientation lives in the ordered response tower, not in a universal first
   commutator.
3. **Use functional equation as selector.**  `(SR.19)` and Corollary 5.2 prove it is an isometric
   relabelling whenever it lifts through the source law.
4. **Infer cofinal selection from finite cyclicity.**  Every finite aperture has `c_T>0`; the
   global theorem shows the infimum can collapse exactly through nonclosed range.

## 8. Selection interface

The new RH-facing question is not “find a source-native object.”  It is the following pair of
source theorems.

1. **Generation:** identify the literal pre-zero arithmetic law as an evolution `L` with legal
   interventions `K(a)` whose Duhamel response tower is admitted before divisor specialization.
2. **Uniform properness:** prove the completed response operator satisfies `(SR.26)` on the
   transverse intervention line or module.
3. **Physical null-response:** prove the divisor/functional-equation law forces the complete
   generated response—not a routewise scalar contraction—to vanish.

Then Theorem 5.1 gives `K(a)=0`; a coefficient-faithful source identification of `K(a)=0` with
`a=0` yields critical-line selection.  None of these three clauses is presently proved for the
literal Xi source, so no RH claim is made.

## 9. Parent boundary and corpus delta

Duhamel perturbation, Dyson expansions, Chen--Fliess series, sensitivity Gramians, Lyapunov
equations, cyclic system identification, and the closed-range theorem are established mathematics.
Recent primary parents include Gray--Pham,
[*Parameter Dependent Chen--Fliess Series and Their Nonrecursive Interconnections*](https://arxiv.org/abs/2406.19077),
Kazma--Taha,
[*Observability for Nonlinear Systems: Connecting Variational Dynamics, Lyapunov Exponents, and
Empirical Gramians*](https://arxiv.org/abs/2402.14711), and Krstic,
[*Feedback Linearization of Hyperbolic PDEs with Volterra Nonlinearities*](https://arxiv.org/abs/2604.27400).

The exact corpus advance is not those ingredients.  It is closure of the missing genesis step:

\[
 \boxed{
 \text{one source evolution}
 \Longrightarrow
 \text{ordered responses + positive carrier + inverse cost + global properness test}.}
 \tag{SR.27}
\]

Earlier formation-Laplacian and synchronization theorems assumed response maps.  Earlier
orbit-Gramian mechanics generated a state observer and cost but did not generate the legal
intervention-response atlas.  The Duhamel response signature supplies that atlas and proves its
fourth-organ Sylvester law.

## 10. Gates

- [x] response maps generated by one source evolution;
- [x] finite complete reconstruction;
- [x] positive work and finite properness;
- [x] positive Gram / inverse cost / determinant response predicted;
- [x] ordered higher-response fusion law;
- [x] functional-equation neutrality;
- [x] exact cofinal closed-range boundary;
- [x] hostile collision audit against synchronization, formation-Laplacian, and orbit-Gramian parents;
- [ ] literal pre-zero arithmetic source evolution and intervention module;
- [ ] cofinal admission of its complete ordered response tower;
- [ ] source-derived uniform lower response bound;
- [ ] physical complete-response null law;
- [ ] RH selection, only after the preceding four gates.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.DuhamelSourceResponse`, `GaloisForLFunctions.HTGeometry.SourceGramianSylvester`, `GaloisForLFunctions.HTGeometry.ComplexJacobiFormula`, `GaloisForLFunctions.HTGeometry.SourceGramResponse`, `GaloisForLFunctions.HTGeometry.SourceResponseNeutrality`, `GaloisForLFunctions.HTGeometry.DysonChenWordTower`, `GaloisForLFunctions.HTGeometry.GlobalResponseProperness`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.DuhamelSourceResponse` (source semigroup, first response,
Duhamel generation, reconstruction, positive work), `GaloisForLFunctions.HTGeometry.SourceGramianSylvester`
(coercive generators, Gramian, Lyapunov law, Sylvester injectivity and inverse bound),
`GaloisForLFunctions.HTGeometry.ComplexJacobiFormula` (Jacobi's formula for complex matrices and operators),
`GaloisForLFunctions.HTGeometry.SourceGramResponse` (positive Gram formation, Gram response, inverse-cost and
determinant responses), `GaloisForLFunctions.HTGeometry.SourceResponseNeutrality` (functional-equation
neutrality), `GaloisForLFunctions.HTGeometry.DysonChenWordTower` (ordered word tower, time fusion, commutative
specialization, covariance) and `GaloisForLFunctions.HTGeometry.GlobalResponseProperness` (closed-range
classification and intertwining).  Corpus inputs: `WordL1` (the Banach algebra `ℓ¹(A*; E)`),
`SelfAdjointDysonSource` (`generator`, `response`, `coeff`, `constantTerm_response`), `WordL1.relabel`,
`unitaryConj`, `ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range`,
`ContinuousLinearMap.surjective_of_reCoercive`, `ContinuousLinearMap.norm_le_of_reCoercive`,
`ContinuousLinearMap.range_adjoint_le_ker_orthogonal`, `ContinuousLinearMap.hsNormSq_eq`.

| Claim | Lean declaration |
|-|-|
| (SR.1)–(SR.3) source `L = L* > 0`, cyclic `v`, `S_t = e^{-tL}`, `x(t) = S_t v` | `CyclicSource`, `CyclicSource.S`, `CyclicSource.x`, `CyclicSource.exists_coercive`, `exists_coercive_of_pos`, `norm_exp_neg_le` |
| (SR.4) first response `Y_K(t) = -∫₀ᵗ S_{t-s} K S_s v ds` | `CyclicSource.response`, `CyclicSource.response_eq` |
| (SR.5) response operator and work `W_T(K) = ‖Y_K‖²_{L²}` | `CyclicSource.responseCLM`, `CyclicSource.responseCLM_apply`, `CyclicSource.responseWork` |
| (SR.6) Gramian `G = ∫₀^∞ ∣x⟩⟨x∣` | `gramian`, `CyclicSource.gram`, `inner_gramian` |
| I, (SR.7) `d/dε x_{ε,K}(t) ∣₀ = Y_K(t)` | `CyclicSource.perturbedOrbit`, `CyclicSource.duhamel`, `CyclicSource.hasDerivAt_perturbedOrbit` |
| I, (SR.8) `Y' + L Y = -K x`, `Y(0) = 0`, uniqueness | `CyclicSource.hasDerivAt_response`, `CyclicSource.response_zero`, `CyclicSource.response_unique` |
| II, (SR.9) `K x(t) = -Y' - L Y`; the orbit on `[0,T]` spans; finitely many orbit values form a basis; reconstruction; injectivity of `R_T` | `CyclicSource.span_orbit`, `CyclicSource.span_orbit_Ioo`, `CyclicSource.exists_orbit_basis`, `CyclicSource.reconstruction`, `CyclicSource.eq_zero_of_response_eq_zero`, `CyclicSource.response_injective` |
| III, (SR.10) `W_T` positive definite, `W_T(K) ≥ c_T ‖K‖²_HS` | `CyclicSource.responseWork_pos`, `CyclicSource.exists_responseWork_coercive`, `CyclicSource.exists_responseWork_coercive_hs` |
| III, (SR.11) `W_T(K_n) → 0 ⇒ K_n → 0`; compact sublevels | `CyclicSource.tendsto_zero_of_responseWork`, `CyclicSource.isCompact_responseWork_le` |
| IV, (SR.12) `G > 0`, `L G + G L = P`, uniqueness | `CyclicSource.gram_pos`, `CyclicSource.lyapunov_gram`, `CyclicSource.eq_gram_of_lyapunov`, `lyapunov_gramian`, `eq_gramian_of_lyapunov`, `eq_zero_of_sylvester` |
| IV, perturbed Gramians `G_{ε,K}` (coercive generator `L + εK`, Lyapunov identity, uniform bound) | `CyclicSource.perturbedGram`, `CyclicSource.coercive_add_smul`, `CyclicSource.lyapunov_perturbedGram_sub`, `CyclicSource.norm_perturbedGram_le` |
| IV, (SR.13) `Ġ_K = ∫₀^∞ (∣Y_K⟩⟨x∣ + ∣x⟩⟨Y_K∣)` is `d/dε G_{ε,K} ∣₀` | `CyclicSource.gramDot`, `CyclicSource.inner_gramDot`, `CyclicSource.hasDerivAt_perturbedGram`, `exists_lyapunov_inverse_bound` |
| IV, (SR.14) `L Ġ_K + Ġ_K L = -(K G + G K)` | `CyclicSource.lyapunov_gramDot` |
| IV, (SR.15) `B = -(LĠ + ĠL)`, unique solution of `K G + G K = B`; `Ġ_K` reconstructs `K` | `CyclicSource.gram_sylvester_gramDot`, `CyclicSource.existsUnique_gram_sylvester`, `CyclicSource.eq_of_gram_sylvester`, `CyclicSource.gramDot_injective`, `existsUnique_sylvester` |
| V, (SR.16) `Ċ_K = -C Ġ_K C` | `CyclicSource.isUnit_gram`, `CyclicSource.hasDerivAt_inverseCost` |
| V, (SR.17) `d/dε log det G_{ε,K} ∣₀ = tr (C Ġ_K)` | `CyclicSource.hasDerivAt_logDet`, `CyclicSource.exists_det_gram_eq_pos`, `hasDerivAt_det_operator`, `hasDerivAt_det_complex` |
| VI, (SR.18) unitary symmetry `J L = L J`, `J v = ζ v`, `∣ζ∣ = 1` (involutions included) | `SourceSymmetry`, `SourceSymmetry.apply_x`, `SourceSymmetry.star_apply_x` |
| VI, (SR.19) `Y_{K^J} = ζ̄ J Y_K`, `Ġ_{K^J} = J Ġ_K J*`, `W_T(K^J) = W_T(K)` | `SourceSymmetry.response_conjugate`, `SourceSymmetry.gramDot_conjugate`, `SourceSymmetry.responseWork_conjugate` |
| VI, `G`, `C` commute with `J`; kernels, norms, reconstruction constants, inverse costs and determinant responses transported | `SourceSymmetry.conj_gram`, `SourceSymmetry.comm_gram`, `SourceSymmetry.comm_inverseCost`, `SourceSymmetry.response_conjugate_eq_zero_iff`, `SourceSymmetry.norm_conjugate`, `SourceSymmetry.hsNormSq_conjugate`, `SourceSymmetry.responseWork_coercive_conjugate`, `SourceSymmetry.inverseCostResponse_conjugate`, `SourceSymmetry.logDetResponse_conjugate` |
| Theorem 4.1, (SR.21) `e^{-tB} = ∑_w U_w(t) w` in `ℓ¹(A*; End H)`, unique coefficients | `SelfAdjointDysonSource.hasSum_response`, `SelfAdjointDysonSource.eq_coeff_of_hasSum` |
| (SR.20) `U_∅ = S_t`, `U_{aw}(t) = -∫₀ᵗ S_{t-s} K_a U_w(s) ds`; uniqueness of the recursion | `SelfAdjointDysonSource.coeff_nil`, `SelfAdjointDysonSource.coeff_cons`, `SelfAdjointDysonSource.eq_coeff_of_recursion` |
| (SR.22) `U_{aw}' + L U_{aw} = -K_a U_w`, `U_{aw}(0) = 0` | `SelfAdjointDysonSource.hasDerivAt_coeff_cons`, `SelfAdjointDysonSource.coeff_cons_zero`, `SelfAdjointDysonSource.generator_mul_apply_cons`, `WordL1.single_mul_apply` |
| (SR.23) `U_w(t+s) = ∑_{w=uv} U_u(t) U_v(s)` | `SelfAdjointDysonSource.coeff_add` |
| Theorem 4.1(3) scalar specialization `∑_w ε^w U_w(t) = e^{-t(L+∑ ε_a K_a)}` sees only content sums; the word tower separates orders | `WordL1.specializeHom`, `SelfAdjointDysonSource.specialize_response`, `WordL1.hasSum_specialize_content`, `WordL1.specialize_eq_of_contentSum_eq`, `SelfAdjointDysonSource.specialize_response_eq_of_contentSum_eq`, `WordL1.contentSum_swap`, `WordL1.single_swap_ne_zero` |
| (SR.24) `J K_a J* = K_{σ a}`, `J L = L J` ⇒ `J U_w(t) J* = U_{σ w}(t)` | `SelfAdjointDysonSource.conj_coeff_of_symmetry` |
| Theorem 5.1 (1)⇔(2)⇔(3)⇔(4) | `globalProperness_tfae`, `reducedPositiveResponse`, `invisibleKernel`, `infDist_invisibleKernel` |
| Theorem 5.1 vanishing response modulo `N` | `tendsto_infDist_of_isClosed_range` |
| Theorem 5.1 compact `R`, infinite-dimensional `N^⊥`: orthonormal subsequence to zero, no condition holds | `exists_subseq_tendsto_zero_of_orthonormal`, `exists_nullSequence_of_isCompactOperator`, `not_isClosed_range_of_isCompactOperator` |
| Corollary 5.2 intertwining unitaries preserve `N`, distance, response norms, `Q`, null sequences, `α`, closed range | `mem_invisibleKernel_iff_intertwined`, `infDist_intertwined`, `norm_apply_intertwined`, `positiveResponse_intertwined`, `tendsto_intertwined_iff`, `lowerBound_intertwined_iff`, `isClosed_range_intertwined_iff` |

Sections 6–9 (dictionary, no-go list, selection interface, corpus delta) restate the theorems above
or record open programme items; they carry no further Lean obligation.

## Log

- 2026-08-14 — created after whole-frontier audit showed that every leading field programme still
  supplied response maps, transports, challenges, or proper costs before its main theorem.
- 2026-08-14 — first-order Duhamel reconstruction, positive Sylvester response, inverse-cost law,
  free-word time fusion, functional-equation neutrality, and cofinal properness classification
  proved dependency-closed on paper.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
