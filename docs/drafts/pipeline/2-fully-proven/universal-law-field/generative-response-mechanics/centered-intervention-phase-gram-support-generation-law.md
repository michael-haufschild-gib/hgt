# Centered intervention, phase reconstruction, Gram response, and support-generation law

- **ID:** `ulf-grm-centered-phase-gram-support-generation`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / GENERATIVE RESPONSE FUSION LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HOSTILE-ACCEPTED] [FOUR-ORGAN FUSION]`
  `[LEAN-CERTIFIED FINITE CORE] [CLASSICAL COMPONENTS] [NOVELTY NOT LOAD-BEARING] [NOT RH]`
- **Source:** `rh-current-frontier-map.md`; `marked-mellin-normalization-exchange-response-law.md`;
  `XiShiftedHankelBoundaryExtensionClass.lean`.
- **Statement:** On a finite positive law, normalization turns every coefficient intervention into
  one centered signed tangent. Its phase jets reconstruct that tangent, its quadratic pushforward is
  the complete Gram response, and at a positive Gram null face every hereditary intervention
  vanishes: first-order rank and determinant orientation is generated exactly by off-support mass.

## 1. Why this is the current field candidate

The dyadic squarefree--Euler reconstruction is already corpus mathematics and classical unique
factorization. It supplies a useful instance of dilation resolution, but it is not a new field.
The stronger common mechanism suggested by the full frontier is not a new carrier. It is a grammar
of interventions and generated responses:

1. **center** an absolute source intervention by normalization;
2. **report** the resulting mass-zero tangent through characters, moments, energies, or incidence;
3. **reconstruct** the tangent when one reporter family separates source atoms;
4. **distinguish hereditary motion from generation** relative to the current positive support;
5. **orient a boundary only through the generative normal component**.

This is designed to explain, in one theorem, why ordinary coefficient tilts can move interior
statistics but repeatedly fail to orient first null faces, while singular/admission/source-birth
mechanisms remain open in the live routes.

## 2. Finite atomic setup

Let `X` be a finite nonempty set. Fix:

- positive source weights `w_x>=0`, with
  \[
  Z=\sum_{x\in X}w_x>0,
  \qquad P_x=\frac{w_x}{Z};
  \tag{GRM.1}
  \]
- an absolute coefficient intervention `h:X->R`, with `H=sum_x h_x`;
- pairwise distinct real history labels `lambda_x`;
- a real finite-dimensional inner-product space `V` and feature vectors `Phi_x in V`.

For small `epsilon`, normalize the perturbed source whenever it is positive:

\[
P_x(\epsilon)=
 \frac{w_x+\epsilon h_x}{Z+\epsilon H}.
\tag{GRM.2}
\]

Define the centered intervention tangent

\[
\eta_x=\left.\frac d{d\epsilon}\right|_0P_x(\epsilon)
       =\frac1Z\left(h_x-H P_x\right).
\tag{GRM.3}
\]

Define the history and Gram reporters

\[
C_\epsilon(t)=\sum_xP_x(\epsilon)e^{-it\lambda_x},
\qquad
G_\epsilon=\sum_xP_x(\epsilon)\,\Phi_x\Phi_x^*.
\tag{GRM.4}
\]

Write `dot C` and `dot G` for their derivatives at zero.

## 3. Fusion theorem

### Theorem 3.1 — centered response and phase reconstruction

The same tangent `eta` controls both reporters:

\[
\sum_x\eta_x=0,
\qquad
\dot C(t)=\sum_x\eta_xe^{-it\lambda_x},
\qquad
\dot G=\sum_x\eta_x\Phi_x\Phi_x^*.
\tag{GRM.5}
\]

Put

\[
m_k=\sum_x\eta_x\lambda_x^k.
\tag{GRM.6}
\]

Then

\[
\dot C^{(k)}(0)=(-i)^k m_k.
\tag{GRM.7}
\]

The first `|X|` moments `m_0,...,m_(|X|-1)` reconstruct every coefficient `eta_x`; hence the full
phase response reconstructs `eta`, and therefore predicts `dot G` for every feature reporter.

### Theorem 3.2 — null-response localization and rank generation

Let `a in V` satisfy

\[
G_0a=0.
\tag{GRM.8}
\]

Then

\[
\boxed{
\langle a,\dot G a\rangle
 =\frac1Z\sum_{x:w_x=0}h_x|\langle a,\Phi_x\rangle|^2.}
\tag{GRM.9}
\]

More strongly, if `K=ker G_0` and `Pi_K` is the orthogonal projection, then as an operator on `K`,

\[
\boxed{
\Pi_K\dot G\Pi_K
 =\frac1Z\sum_{x:w_x=0}h_x
   (\Pi_K\Phi_x)(\Pi_K\Phi_x)^*.}
\tag{GRM.9a}
\]

For a one-sided positive intervention, the right side is positive semidefinite and

\[
\operatorname{rank}(\Pi_K\dot G\Pi_K)
 =\dim\operatorname{span}
   \{\Pi_K\Phi_x:w_x=0,\ h_x>0\}.
\tag{GRM.9b}
\]

Consequences:

1. every fixed-support reweighting `h_x=w_xr_x` has zero response on every present null direction;
2. every two-sided positive intervention has zero null response;
3. every one-sided positive intervention has nonnegative null response;
4. strict first-order opening occurs exactly when positive mass is born at an off-support feature
   not annihilated by the null covector.
5. the number of null directions opened to first order is exactly the dimension of the projected
   birth span.

This is the proposed generation law. Hereditary interventions change weights inside the current
face. Generative interventions add a source atom outside the current face, and only the latter can
open a positive null direction to first order.

### Theorem 3.3 — interior leverage conservation

If `G_0` is invertible and

\[
\ell(x)=\langle\Phi_x,G_0^{-1}\Phi_x\rangle,
\tag{GRM.10}
\]

then

\[
\boxed{\sum_xP_x\ell(x)=\dim V,}
\qquad
\boxed{\left.\frac d{d\epsilon}\right|_0\log\det G_\epsilon
       =\sum_x\eta_x\ell(x).}
\tag{GRM.11}
\]

For a hereditary score intervention `h_x=w_xr_x`, this becomes

\[
\left.\frac d{d\epsilon}\right|_0\log\det G_\epsilon
 =\operatorname{Cov}_P(r,\ell).
\tag{GRM.12}
\]

### Theorem 3.4 — simple null-face determinant orientation

Assume `dim V=d>=1`, `G_0` has rank `d-1`, and `a` is a unit vector spanning `ker G_0`. Let
`det_+(G_0)` be the product of the positive eigenvalues, with empty product one. Then

\[
\boxed{
\left.\frac d{d\epsilon}\right|_0\det G_\epsilon
 =\frac{\det_+(G_0)}Z
   \sum_{x:w_x=0}h_x|\langle a,\Phi_x\rangle|^2.}
\tag{GRM.13}
\]

Thus the crossing orientation of a positive simple null face is exactly positive pseudovolume
times support-generation energy.

## 4. Complete proof candidate

### Proof of Theorem 3.1

Differentiating `(GRM.2)` gives `(GRM.3)`. Summing `(GRM.3)` gives

\[
\sum_x\eta_x=Z^{-1}(H-H\sum_xP_x)=0.
\]

Finite differentiation of `(GRM.4)` gives `(GRM.5)` and `(GRM.7)`.

For each `x`, let

\[
L_x(z)=\prod_{y\ne x}\frac{z-\lambda_y}{\lambda_x-\lambda_y}
      =\sum_{k=0}^{|X|-1}a_{xk}z^k.
\tag{GRM.14}
\]

Distinctness of the labels makes every denominator nonzero, and
`L_x(lambda_y)=1` for `y=x`, zero otherwise. Therefore

\[
\eta_x
 =\sum_y\eta_yL_x(\lambda_y)
 =\sum_{k=0}^{|X|-1}a_{xk}\sum_y\eta_y\lambda_y^k
 =\sum_{k=0}^{|X|-1}a_{xk}m_k.
\tag{GRM.15}
\]

Thus the phase jet reconstructs `eta` and substitution into `(GRM.5)` reconstructs every Gram
response. QED.

### Proof of Theorem 3.2

Since `G_0` is positive semidefinite,

\[
0=\langle a,G_0a\rangle
 =\sum_xP_x|\langle a,\Phi_x\rangle|^2.
\tag{GRM.16}
\]

Every summand is nonnegative. Hence

\[
w_x>0\Longrightarrow \langle a,\Phi_x\rangle=0.
\tag{GRM.17}
\]

Using `(GRM.3)`, `(GRM.5)`, and `(GRM.16)`,

\[
\begin{aligned}
\langle a,\dot Ga\rangle
 &=\sum_x\eta_x|\langle a,\Phi_x\rangle|^2\\
 &=\frac1Z\sum_xh_x|\langle a,\Phi_x\rangle|^2
   -\frac HZ\sum_xP_x|\langle a,\Phi_x\rangle|^2\\
 &=\frac1Z\sum_{x:w_x=0}h_x|\langle a,\Phi_x\rangle|^2.
\end{aligned}
\]

This is `(GRM.9)`. A fixed-support score has `h_x=0` off support. If both
`w+epsilon h` and `w-epsilon h` are nonnegative for some `epsilon>0`, then at every zero coordinate
both `epsilon h_x>=0` and `-epsilon h_x>=0`, so `h_x=0`. For a one-sided positive path,
`h_x>=0` at every zero coordinate. The remaining claims follow termwise. QED.

For `a,b in K`, polarization of the same pointwise argument gives

\[
\langle a,\dot G b\rangle
 =\frac1Z\sum_{x:w_x=0}h_x
   \langle a,\Phi_x\rangle\langle\Phi_x,b\rangle,
\]

which is `(GRM.9a)`. Under one-sided positivity it is the Gram operator of the vectors
`sqrt(h_x/Z) Pi_K Phi_x`. The rank of a finite Gram operator is the dimension of the span of its
generating vectors, proving `(GRM.9b)`. QED.

### Proof of Theorem 3.3

Use cyclicity of the finite trace:

\[
\sum_xP_x\ell(x)
 =\operatorname{tr}\left(G_0^{-1}\sum_xP_x\Phi_x\Phi_x^*\right)
 =\operatorname{tr}(I_V)=d.
\tag{GRM.18}
\]

Jacobi's formula and `(GRM.5)` give

\[
\frac d{d\epsilon}\log\det G_\epsilon\bigg|_0
 =\operatorname{tr}(G_0^{-1}\dot G)
 =\sum_x\eta_x\ell(x).
\tag{GRM.19}
\]

If `h=wr`, then `(GRM.3)` is `eta_x=P_x(r_x-E_Pr)`, so `(GRM.19)` and `(GRM.18)` give
`(GRM.12)`. QED.

### Proof of Theorem 3.4

Choose an orthonormal eigenbasis of `G_0` whose last vector is `a`. If the positive eigenvalues are
`gamma_1,...,gamma_(d-1)`, then in this basis

\[
G_0=\operatorname{diag}(\gamma_1,\ldots,\gamma_{d-1},0),
\qquad
\operatorname{adj}(G_0)=\det_+(G_0)aa^*.
\tag{GRM.20}
\]

The determinant derivative formula, valid also at a singular matrix, gives

\[
\left.\frac d{d\epsilon}\right|_0\det G_\epsilon
 =\operatorname{tr}(\operatorname{adj}(G_0)\dot G)
 =\det_+(G_0)\langle a,\dot Ga\rangle.
\tag{GRM.21}
\]

Substitute `(GRM.9)`. QED.

## 5. Fourth-organ prediction: Hankel null faces

Take `V=R^(R+1)` and

\[
\Phi_x=(1,\lambda_x,\ldots,\lambda_x^R)^T.
\tag{GRM.22}
\]

Then `G_0` is the order-`R` Hankel moment matrix. A null vector `a` is the polynomial

\[
p_a(z)=\sum_{j=0}^Ra_jz^j.
\tag{GRM.23}
\]

Equation `(GRM.9)` predicts the exact Hankel crossing theorem

\[
\boxed{
a^*\dot G a
=\frac1Z\sum_{x:w_x=0}h_x|p_a(\lambda_x)|^2.}
\tag{GRM.24}
\]

At a simple rank defect, `(GRM.13)` adds the determinant orientation. Therefore:

- an ordinary positive Gibbs/Esscher tilt on the current support cannot produce strict first-order
  shifted-Hankel crossing;
- a strict positive crossing requires a one-sided atom birth outside the current polynomial zero
  set, or else departure from positive-Gram mechanics (signed/indefinite/admission-changing data);
- a phase reporter that separates the source labels reconstructs the exact atom-birth tangent and
  therefore predicts the Hankel crossing without fitting a sign.
- at a higher-corank adaptive flag, the first-order rank gained is the dimension of the restrictions
  of the new evaluation vectors to the current null-polynomial space.

This is a theorem prediction in the adaptive spectral-orientation organ. It does not prove the live
prime--archimedean inequality. It identifies what kind of source intervention could possibly prove
it and rules out all fixed-support positive tilts at once.

## 6. Hostile attacks and exact boundaries

### Attack A — this is only covariance calculus

**Verdict:** partly true. `(GRM.3)`, `(GRM.5)`, and `(GRM.11)` are standard score/Fisher and
optimal-design identities. The candidate contribution is not a claim of component novelty. It is
the fused generation law `(GRM.9)` plus phase reconstruction and boundary orientation
`(GRM.13)`, used as one mechanism across source, history, positive Gram, and spectral crossing.

### Attack B — moving existing feature points can open the null direction

**Fails at first order.** If `Phi_x=Phi_x(epsilon)` is differentiable, the derivative of
`|<a,Phi_x(epsilon)>|^2` is
`2<a,Phi_x><a,dot Phi_x>`, which vanishes on every currently weighted atom by `(GRM.17)`.
Motion can enter at second order, but it does not alter the first-order birth law.

### Attack C — signed or indefinite Gram forms violate localization

**Correct.** Positivity is load-bearing. In an indefinite representation, a null vector can arise
by cancellation while remaining pointwise visible; hereditary interventions can then orient it.
This is not a counterexample to `(GRM.9)` but a sharp boundary separating positive-carrier and
Krein-type mechanics.

### Attack D — a finite Hankel face cannot reconstruct phase history

**Correct.** Reconstruction uses the separating phase jet through order `|X|-1`, not one fixed
Hankel truncation. A fixed proper face is intentionally lossy. The theorem says the complete phase
reporter predicts every finite Gram response, not conversely.

### Attack E — infinite support invalidates finite interpolation

**Correct boundary.** Fourier uniqueness extends reconstruction to finite signed Borel measures on
`R`, but moment-jet reconstruction requires a determinacy condition. The finite theorem needs no
such analytic hypothesis and is the first Lean target.

### Attack F — phase reconstruction without distinct labels

**False, and the hypothesis is sharp.** Take two source atoms with the same `lambda`, tangent
`eta=(1,-1)`, and different feature vectors. Every phase response and every phase jet vanishes,
while the Gram response need not vanish. The separating-label hypothesis cannot be removed; in the
general grammar it must be replaced by joint faithfulness of the declared reporter family.

### Attack G — positivity is cosmetic

**False.** On a one-dimensional feature space, take two signed carrier weights `1` and `-1` with
the same nonzero feature. Their signed Gram is zero although the feature is pointwise visible, and
changing only one weight gives a nonzero first response. Positivity is exactly what turns a Gram
null vector into pointwise annihilation on occupied support.

### Attack H — `(GRM.13)` controls every corank

**False outside corank one.** If `dim ker G_0>=2`, the first derivative of the determinant is zero.
The correct first-order invariant is the compressed operator `(GRM.9a)` and its rank
`(GRM.9b)`; determinant orientation moves to a higher coefficient. This is why the field grammar
retains the full null compression instead of scalarizing immediately.

## 7. Internal and external collision ledger

- `[LOCAL-RESEARCH]` `marked-mellin-normalization-exchange-response-law.md` proves centering and
  phase covariance but not Gram-null support localization or determinant orientation.
- `[CORPUS]` `XiShiftedHankelBoundaryExtensionClass.lean` computes the actual shifted-Xi first
  unseen square and source tangent, but does not classify which positive interventions can generate
  a null crossing.
- `[LOCAL-RESEARCH]` `dyadic-squarefree-euler-fock-source-factorization.md` proves a classical
  dyadic source reconstruction; it is a scalar instance, not this support-generation law.
- `[LITERATURE]` De Castro--Gamboa--Henrion--Hess--Lasserre,
  <https://arxiv.org/abs/1703.01777>, uses moment matrices, log determinant, and Christoffel
  polynomials in D-optimal design.
- `[LITERATURE]` Yang--Deng, <https://arxiv.org/abs/2606.29678>, couples Fourier data and Hankel rank
  for phase-center recovery and signed component counting.
- finite signed-measure Fourier uniqueness, Jacobi's determinant formula, simple eigenvalue
  perturbation, and Lagrange interpolation are standard parent mechanisms.

No originality claim is load-bearing. The question is whether their exact fusion supplies the
missing generation grammar and yields route-independent deductions.

## 8. Promotion gate

- [x] exact source intervention and normalization typed;
- [x] three organs fused by one centered tangent;
- [x] phase-jet reconstruction proved;
- [x] conservation and null localization proved;
- [x] multi-null rank-generation classification proved;
- [x] fourth-organ Hankel crossing theorem predicted and proved in the finite model;
- [x] hostile review of every algebraic factor and edge case;
- [x] promote unchanged theorem to Stage 2;
- [x] formalize exact finite theorem in `HTGeometry` and wire `UniversalLawField` umbrella;
- [ ] only then test a literal arithmetic intervention against the RH selection gate.

## 9. Frontier-wide grammar extraction

The five obstruction classes in `rh-current-frontier-map.md` become five exact roles of the same
intervention grammar. This is not a claim that their receivers are isomorphic.

| Frontier class | Hereditary mechanism already exhausted | Generative mechanism still capable of changing the obstruction | Consequence of this card |
|---|---|---|---|
| singular source descent | bounded/diagonal reweighting inside fixed domain, ideal, or coframe | domain birth, support birth, or a singular component not absolutely continuous with respect to current law | a fixed-support positive tilt cannot open a null response |
| all-prime oscillatory transport | modulus, norm, or finitely many moments of the tangent | a separating signed character family retaining the complete centered tangent | full phase response reconstructs the finite tangent; proper faces need not |
| adaptive spectral orientation | covariance and positive Gram motion inside a fixed rank stratum | new mass outside the null polynomial zero set, or genuinely indefinite polarization | first determinant sign is exactly support-generation energy |
| whole-space coercivity | estimates on each fixed occupied face | control of the generative normal cone and its cofinal escape cost | facewise coercivity cannot bound unseen support birth |
| positive carrier existence | signed or indefinite moments with cancellation | construction of an actual positive carrier, or an explicitly polarized replacement | pointwise null localization is valid exactly on the positive side of this boundary |

Two further corpus phenomena fit without being identified with those five classes:

- hypertranscendence concerns unbounded growth of separating prolongation reporters, not local
  noncompactness of one observed orbit;
- recurrence concerns compactness of a phase projection, while accumulated lifted intervention
  history may remain open. Static phase reconstruction and path-history reconstruction are distinct
  gates.

This gives the requested common grammar: **center → report → separate → localize → generate**.
The theorem candidate supplies exact laws for every arrow except the arithmetic production of a
specific generative tangent. That production is deliberately postponed until after the universal
theorem is certified.

## 10. Selection consequence: the generative tangent cone

The certification now permits the selection question. Define the legal one-sided normalized
tangent cone at `w` by

\[
\mathcal T_w^+
=\left\{\eta:\sum_x\eta_x=0,\quad w_x=0\Longrightarrow\eta_x\ge0\right\}.
\tag{GRM.15}
\]

### Theorem 10.1 — universal generative-cone selection

Assume `w_x>=0` and `Z>0`. For a signed tangent `eta`, the following are equivalent:

1. `η ∈ 𝒯⁺_w`;
2. its zeroth phase response vanishes, and for every finite real feature packet `Phi` and every
   current Gram-null covector `a`,
   \[
   \sum_x\eta_x|\langle a,\Phi_x\rangle|^2\ge0.
   \tag{GRM.16}
   \]

Moreover, if one positive Gram observer has a negative first response at a current null covector,
then there is a concrete source atom `x` with

\[
w_x=0,\qquad \eta_x<0.
\tag{GRM.17}
\]

**Proof.** Membership in the cone implies `(GRM.16)` by pointwise null localization: occupied
atoms vanish and every surviving square is multiplied by a nonnegative newborn coefficient.
Conversely use the universal coordinate feature packet `Phi_x=e_x` and null covector `e_x` at
every absent atom. Its response is exactly `eta_x`. The zeroth phase moment is `sum eta`, hence
supplies the conservation clause. Negating the implication gives `(GRM.17)`. QED.

This is stronger than another positivity criterion. It classifies *all* finite positive quadratic
observers at once. Phase data reconstruct the tangent; the coordinate reporter tests cone
membership; every other positive Gram/Hankel crossing is then a consequence. Lean certifies the
equivalence and negative-birth witness in `generativeSelection_capstone`.

### RH-facing gate exposed by the field law

The next theorem is no longer “prove another endpoint inequality.” It is a coefficient-faithful
**generative-normal transport law**: construct the actual pre-zero arithmetic intervention, recover
its centered tangent through a separating source reporter, and prove that every comparison into a
current positive face transports that tangent into `mathcal T_w^+`. Once this is proved, no positive
Gram or Hankel face can have a negative first crossing. In the shifted-Xi first-crossing chart this
would exclude the remaining adaptive crossing and therefore give the advertised RH handoff.

The reduction is exact but not yet the handoff theorem. Current Route-U data already identify the
first-unseen source/atomic tangent difference; they do not prove that the comparison preserves the
generative cone through the infinite signed/Krein completion. Thus the field contributes a sharp
producer criterion and a source-coordinate falsifier:

- a hereditary/fixed-support tilt cannot select RH;
- a negative crossing must be a negative newborn coefficient, not a mysterious determinant sign;
- a valid proof must construct a pre-zero comparison preserving conservation, reporter
  reconstruction, and the generative cone at every adaptive cutoff;
- failure of any one clause identifies the exact non-functoriality or admission wall, rather than
  spawning another endpoint reformulation.

## Log

- 2026-08-10 — candidate created after the dyadic reconstruction proposal collided with the
  existing squarefree--Euler Fock factorization. The killing mechanism forced the stronger
  hereditary-versus-generative intervention distinction.
- 2026-08-10 — full finite proof survived label-collision, indefinite-carrier, moving-feature, and
  higher-corank attacks; exact statement promoted to Stage 2.
- 2026-08-11 — finite fusion core formalized in
  `GaloisForLFunctions.HTGeometry.GenerativeResponseFusion` and wired into
  `GaloisForLFunctions.HTGeometry.UniversalLawField`. Direct elaboration and the final foreground
  umbrella build pass; the latter completed 11,608 jobs. Axiom audit of load-bearing declarations
  and the unconditional full capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
  Lean certifies centered conservation, finite phase reconstruction, positive null localization,
  newborn-span rank generation, leverage conservation, literal Gram/log-determinant response,
  Hankel prediction, and diagonal/adjugate-certificate simple-null determinant response. The final
  coordinate-free spectral reduction of an arbitrary positive corank-one face to diagonal gauge
  remains a paper proof rather than a separate Lean declaration.
- 2026-08-11 — selection step completed at the universal finite level. Lean proves that legal
  centered source tangents are exactly conserved phase tangents with nonnegative response on every
  positive Gram null face, and that every negative crossing exposes a specific absent atom with
  negative tangent coefficient. This isolates generative-normal transport as the RH-facing gate;
  no RH or infinite-completion transport theorem is claimed.
