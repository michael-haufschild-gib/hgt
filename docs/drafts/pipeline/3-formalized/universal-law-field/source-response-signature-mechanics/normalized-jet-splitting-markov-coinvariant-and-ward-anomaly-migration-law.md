# Normalized jet splitting, Markov coinvariants, and Ward-anomaly migration law

- **ID:** ULF-SRSM-9
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT NO-GO / POSITIVE SURVIVOR
- **Sources:** ULF-SRSM-8 complete base-norm formation; Generative Response Mechanics;
  Inverse-Response Ward Mechanics
- **Statement:** Common mass recovery splits every finite jet of a normalized formation into a
  recovered coefficient jet and a vertical shape jet. Reporters invariant under every Markov
  refinement factor through mass and therefore erase all positive-order normalized shape jets.
  In a statistical realization the inverse-response Ward law becomes the Bartlett identity, so
  positive Fisher mass is cancelled by the score-connection term rather than forced to vanish.
  Under Markov observation, Fisher loss equals the exact migration of that Ward anomaly.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [MECHANISM LEVEL]`
  `[ALL-ORDER JET SPLITTING] [MARKOV COINVARIANT CLASSIFICATION]`
  `[BARTLETT-WARD NO-GO] [FISHER/CONNECTION MIGRATION] [PRE-RH]`
  `[LEAN-FORMALIZED FULL] [ACTIVE-SUPPORT EXACT] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## 1. Why the next obvious fusion fails

ULF-SRSM-8 gives a globally proper probability-formation map with total mass as a common recovery.
Inverse-Response Ward Mechanics gives a product-current identity that can select only after a
reporter turns the fused current into faithful positive mass. A tempting fusion is to differentiate
the normalized probability formation and use total mass as the Ward reporter.

That fusion is impossible. Normalization places every positive-order shape derivative in the
kernel of mass. More strongly, this is not a first-order accident: the whole finite jet tower splits
triangularly, and every reporter natural under all Markov refinements factors through the same mass
quotient. The corresponding Ward identity is the classical score/Hessian cancellation and permits
strictly positive Fisher information.

The positive survivor is not another obstruction label. It is an exact transport law: under a
Markov observer, the amount of Fisher information lost is precisely the amount by which the mean
Ward connection changes.

## 2. Algebraic all-order jet splitting

Let `K` be a field of characteristic zero, let `E,V` be `K`-vector spaces, and let

\[
 \mathsf R:V\longrightarrow E
 \tag{NJS.1}
\]

be linear. Let `M_0,...,M_N:E->V` satisfy

\[
 \mathsf R M_0=\operatorname{id}_E,
 \qquad
 \mathsf R M_k=0\quad(1\le k\le N).
 \tag{NJS.2}
\]

For a coefficient jet `c=(c_0,...,c_N)`, define its normalized formed jet by the Leibniz rule

\[
 \boxed{
  (\mathsf S_Nc)_n
   =\sum_{k=0}^n\binom nk M_kc_{n-k}}
 \qquad(0\le n\le N).
 \tag{NJS.3}
\]

Let `R_N:V^(N+1)->E^(N+1)` act levelwise by `R`.

### Theorem 2.1 — all-order common-recovery splitting

For every finite order `N`,

\[
 \boxed{\mathsf R_N\mathsf S_N=\operatorname{id}_{E^{N+1}}.}
 \tag{NJS.4}
\]

Consequently `S_N` is injective,

\[
 \boxed{
 V^{N+1}=\operatorname{im}\mathsf S_N\oplus\ker\mathsf R_N,}
 \tag{NJS.5}
\]

and `P_N=S_NR_N` is the projection onto the formed jet range. The recovered order-`n`
coefficient is exactly `c_n`; no lower coefficient or normalized shape jet can change it.

### Proof

Apply `R` to `(NJS.3)`. The `k=0` term is `c_n` by `(NJS.2)`. Every `k>0` term vanishes by the
same equation. This proves `(NJS.4)`. A map with a left inverse is injective. For arbitrary
`v in V^(N+1)`,

\[
 v=\mathsf S_N\mathsf R_Nv+
   \bigl(v-\mathsf S_N\mathsf R_Nv\bigr),
\]

and the second summand lies in `ker R_N`. The intersection is zero by `(NJS.4)`. The projection
claim follows. QED.

### Analytic realization

Let `mu(t)` be an `N`-times differentiable probability-valued curve and let `c(t)` be an
`E`-valued coefficient curve. Put

\[
 \nu(t)=c(t)\mu(t).
 \tag{NJS.6}
\]

Here multiplication means channelwise scalar formation, as in ULF-SRSM-8. Take
`M_k d=d mu^(k)(0)`. Since `mu(t)(Omega)=1`,

\[
 \mathsf R M_0=\operatorname{id},
 \qquad
 \mathsf R M_k=0\quad(k>0).
 \tag{NJS.7}
\]

Leibniz gives `(NJS.3)`, hence

\[
 \boxed{\mathsf R\,\nu^{(n)}(0)=c^{(n)}(0).}
 \tag{NJS.8}
\]

For fixed coefficients, every positive-order formation jet is vertical. For changing coefficients,
every coefficient derivative is recovered exactly despite arbitrary normalized shape response.

### Normed consequence

Assume `E,V` are normed, `||R||<=1`, and `M_0,...,M_N` are bounded. Give finite jet products the
sum norm. Then

\[
 \|\mathsf S_Nc\|\ge\|c\|,
 \tag{NJS.9}
\]

while

\[
 \|\mathsf S_Nc\|
 \le C_N\|c\|,
 \qquad
 C_N=\max_{0\le j\le N}
 \sum_{k=0}^{N-j}\binom{j+k}{k}\|M_k\|.
 \tag{NJS.10}
\]

Thus every finite normalized jet formation has closed range and inverse norm at most one whenever
the finitely many shape-derivative operators are admitted. The infinite jet tower can still fail
through growth of `C_N`; no analytic-radius or hypertranscendence conclusion is smuggled in.

## 3. Markov coinvariant classification

Let `X` be a nonempty finite set, let `V=K^X`, and let

\[
 m(v)=\sum_{x\in X}v_x.
 \tag{NJS.11}
\]

Let `S` be any family of mass-preserving linear maps `T:V->V`. Define its response radical

\[
 \mathcal N_S
 =\operatorname{span}\{Tv-v:T\in S,\ v\in V\}.
 \tag{NJS.12}
\]

### Theorem 3.1 — invariant reporters are dual to the coinvariant quotient

A linear reporter `tau:V->Y` satisfies

\[
 \tau T=\tau\qquad(T\in S)
 \tag{NJS.13}
\]

if and only if `N_S subset ker tau`. Hence invariant reporters are exactly linear maps out of

\[
 \boxed{V/\mathcal N_S.}
 \tag{NJS.14}
\]

### Proof

Equation `(NJS.13)` is equivalent to `tau(Tv-v)=0` for every generator of `N_S`; linearity gives
the claim. QED.

Let `S_all` contain every stochastic map, in particular every reset

\[
 K_yv=m(v)e_y.
 \tag{NJS.15}
\]

### Corollary 3.2 — universal refinement invariance is mass only

\[
 \boxed{\mathcal N_{S_{\rm all}}=\ker m,
 \qquad V/\mathcal N_{S_{\rm all}}\simeq K.}
 \tag{NJS.16}
\]

Every reporter invariant under all Markov refinements has the form

\[
 \boxed{\tau(v)=m(v)y_0}
 \tag{NJS.17}
\]

for one fixed `y_0 in Y`. It annihilates every normalized positive-order shape jet.

### Proof

Mass preservation gives `N_Sall subset ker m`. Conversely, if `m(v)=0`, then
`K_yv-v=-v`, so `v in N_Sall`. This proves `(NJS.16)`. The reporter classification follows from
Theorem 3.1. QED.

For labelled channels, if all admitted Markov maps preserve the channel label, the same proof
applies coordinatewise: invariant linear reporters factor through the common vector of channel
masses `R` from ULF-SRSM-8.

## 4. Inverse response becomes Bartlett cancellation

Let `X` be finite and let `p_t(x)>0` be twice differentiable for `t` near zero, with

\[
 \sum_xp_t(x)=1.
 \tag{NJS.18}
\]

Define score and score connection

\[
 s_t(x)=\frac{p_t'(x)}{p_t(x)},
 \qquad
 a_t(x)=s_t'(x).
 \tag{NJS.19}
\]

The pointwise inverse-response Riccati identity is

\[
 \boxed{a_t+s_t^2=\frac{p_t''}{p_t}.}
 \tag{NJS.20}
\]

### Theorem 4.1 — Bartlett-Ward neutrality

At every admitted parameter,

\[
 \boxed{\mathbb E_t[s_t]=0,
 \qquad
 \mathbb E_t[a_t+s_t^2]=0,}
 \tag{NJS.21}
\]

and therefore

\[
 \boxed{\mathbb E_t[s_t^2]=-\mathbb E_t[a_t].}
 \tag{NJS.22}
\]

The Ward balance does not imply zero Fisher information.

### Proof

Multiply `s_t` by `p_t`, sum, and differentiate total mass to obtain the first identity. Multiply
`(NJS.20)` by `p_t`, sum, and differentiate total mass twice to obtain the second. Rearrangement
gives `(NJS.22)`. QED.

### Sharp countermodel

On `X={+,-}`, set

\[
 p_t(+)=\frac{1+t}{2},
 \qquad
 p_t(-)=\frac{1-t}{2},
 \qquad |t|<1.
 \tag{NJS.23}
\]

At `t=0`, `s_0=(1,-1)`, `a_0=(-1,-1)`, and

\[
 \mathbb E_0[s_0^2]=1,
 \qquad
 \mathbb E_0[a_0]=-1,
 \qquad
 \mathbb E_0[a_0+s_0^2]=0.
 \tag{NJS.24}
\]

The source experiment is affine (`p_t''=0`) and the Ward balance is exact, yet the positive Fisher
mass is one. The missing premise in the faithful-square Ward schema is not a technicality: the
mass reporter does not annihilate the score derivative; its exact anomaly is the negative Fisher
mass.

## 5. Positive survivor: Ward-anomaly migration under observation

Let `K(y|x)` be a parameter-independent Markov kernel from finite `X` to finite `Y`. Put

\[
 q_t(y)=\sum_xK(y|x)p_t(x),
 \tag{NJS.25}
\]

and let `\bar s_t,\bar a_t` be its score and score connection. Under the joint law
`p_t(x)K(y|x)`,

\[
 \bar s_t(Y)=\mathbb E_t[s_t(X)\mid Y].
 \tag{NJS.26}
\]

Scores are defined on the active output support `{y:q_t(y)>0}`. Zero-probability output rows carry
no term in any expectation and may be discarded.

### Theorem 5.1 — Fisher loss is exact Ward-anomaly migration

\[
 \boxed{
 \mathbb E_t[s_t^2]-\mathbb E_t[\bar s_t^2]
 =\mathbb E_t[(s_t-\bar s_t)^2]
 =\mathbb E_t[\bar a_t]-\mathbb E_t[a_t]
 \ge0.}
 \tag{NJS.27}
\]

Equality holds exactly when the source score is a function of the observed variable almost surely.

### Proof

Equation `(NJS.26)` follows by differentiating `(NJS.25)` and dividing by `q_t(y)`. Orthogonal
conditional-expectation decomposition gives

\[
 \mathbb E[s_t^2]
 =\mathbb E[\bar s_t^2]
  +\mathbb E[(s_t-\bar s_t)^2].
\]

Apply `(NJS.22)` to `p_t` and `q_t` to replace the two Fisher terms by the negatives of the
corresponding mean connections. Equality in the nonnegative conditional variance holds exactly
when `s_t=\bar s_t(Y)` almost surely. QED.

This is the fourth-organ theorem predicted by the fusion. Positive information loss in a Markov
observer is not destroyed Ward current; it reappears exactly as displacement of the mean score
connection.

## 6. Consequences for the universal-law field

### 6.1 Exact horizontal/vertical classification

Common recovery separates two mechanisms that earlier programmes could conflate:

\[
 \boxed{
 \text{coefficient jets}=\text{recovered horizontal quotient},
 \qquad
 \text{normalized shape jets}=\text{vertical response radical}.}
 \tag{NJS.28}
\]

This is all-order and independent of a route realization.

### 6.2 Selection no-go

A physical Xi/transverse current represented only by normalized deformation of the subset-phase
probabilities cannot be selected by the common mass recovery of ULF-SRSM-8. Every universally
Markov-natural linear reporter kills it. Inverse-response Ward balance with that reporter is
Bartlett cancellation and permits positive Hodge/Fisher mass.

### 6.3 Strongest surviving selection gate

A successful source theorem must do at least one of the following:

1. place the selection-bearing current in a nonzero **coefficient jet**, which common mass recovers
   exactly by `(NJS.8)`;
2. derive a restricted source Markov semigroup whose coinvariant quotient retains a nonconstant
   harmonic reporter pairing nontrivially with the vertical current;
3. derive a genuinely transverse boundary anomaly not equal to the canonical Bartlett connection;
4. use a nonlinear faithful positive reporter and separately prove why its connection term vanishes
   rather than assuming Ward conservation does so.

This replaces the vague requirement that the current merely “land in the formed range.” Its
horizontal/vertical type must be proved before any selection consequence is legal.

## 7. Conjecture -> proof/failure loops

1. **Differentiate the probability formation and recover the current by mass. — Failed.**
   Every positive-order normalized shape jet has zero mass. **Survivor:** coefficient jets are
   recovered exactly at every order.
2. **Use a reporter invariant under every common refinement to detect shape. — Failed.**
   The all-Markov coinvariant quotient is the mass line. **Survivor:** a restricted source semigroup
   is measured by its explicit coinvariant quotient `(NJS.14)`.
3. **Affine source plus Ward conservation forces Fisher mass zero. — Failed.**
   The two-point affine family `(NJS.23)` has Fisher mass one. **Survivor:** the score connection
   cancels it exactly.
4. **Observation simply erases the cancelled term. — Failed.**
   Fisher loss is conserved as the change of mean Ward connection by `(NJS.27)`.
5. **Finite jet splitting implies complete analytic-jet properness. — Failed.**
   Finite splitting gives `(NJS.9)` only when the relevant derivative operators are bounded; the
   constants `C_N` may diverge. **Survivor:** the finite-order lower bound is universal while
   infinite-order admission remains an independent source-growth law.

## 8. Hostile scope

1. The algebraic splitting is classical triangular linear algebra.
2. The score identities are classical Bartlett/Fisher identities.
3. Markov coinvariants and sufficient-statistic equality are classical probability/ergodic
   mechanisms.
4. No claim of priority for those ingredients is made. Field-level leverage is their exact joint
   placement: they close a proposed common-recovery/Ward selector, preserve all coefficient jets,
   classify every universally natural reporter, and force the anomaly-migration law.
5. Finite `X` avoids differentiation-under-integral and conditional-expectation domain issues.
   Standard dominated differentiability extends the formulas to measure models, but is not needed
   here.
6. The theorem does not construct the restricted arithmetic semigroup, a nonconstant harmonic
   reporter, physical Xi landing, or RH.

## 9. Literature boundary

Ay--Jost--Le--Schwachhoefer's sufficient-statistics framework characterizes Fisher/Amari tensors
under Markov morphisms (`arXiv:1207.6736`). Bohinen--Perrone's categorical probability work gives
current probability-monad and conditioning architecture (`arXiv:2502.14941`). Tangent-category and
tangentad machinery (`arXiv:2503.18354`, `arXiv:2509.15524`) provides a general categorical home
for differentiated monads. These occupy the abstract ingredients; none is used as evidence that
the HGT source has the missing restricted reporter.

The exact corpus result is the new fusion/no-go interface between:

- all-grade arithmetic probability formation and common mass recovery;
- centered generative response;
- inverse-response Ward products;
- Markov/Fisher observation.

## 10. Formal status

The complete dependency-closed surface `(NJS.1)`--`(NJS.28)` is formalized in
`GaloisForLFunctions.HTGeometry.ConstitutiveNormalizedJetWardMigration`. Certification includes:

- exact finite-jet Leibniz formation, common-recovery left inverse, injection, projection,
  range/kernel complement, and explicit decomposition;
- the exact sum norm and attained constant `C_N`, both inequalities `(NJS.9)`--`(NJS.10)`,
  inverse bound, continuous formation/recovery, and closed formed-jet range;
- response radicals for arbitrary refinement families, the split-common-recovery classification,
  the all-mass radical equality, both quotient equivalences, and mass-only reporter factorization;
- finite Riccati, centered-score, Bartlett, Fisher nonnegativity, and the exact affine Bernoulli
  countermodel;
- finite Markov observation using the corpus kernel type, canonical deletion of zero-mass outputs,
  conditional-score identity, exact Fisher/connection migration, nonnegativity, and the equality
  classification.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`. Direct leaf and
umbrella elaboration pass; targeted module build passes. Scoped forbidden-token scan is clean.
Audited significant declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-14 — common-recovery/Ward fusion attacked and falsified by normalized affine
  probability families.
- 2026-08-14 — extracted all-order coefficient/shape jet splitting, universal Markov coinvariant
  classification, and exact Fisher/Ward-anomaly migration as positive survivors.
- 2026-08-14 — full Lean closure completed, including exact `C_N` stability, closed range,
  common-recovery and mass coinvariant quotients, canonical active-support observation, equality
  case, and sharp affine countermodel; leaf, targeted build, umbrella, scoped lint, and axiom audits
  pass.
- 2026-08-14 — Full unconditional Lean closure: all-order common-recovery splitting, exact attained C_N sum-norm bounds and closed range, abstract and finite-mass coinvariant quotients, Bartlett-Ward identities and sharp affine countermodel, plus canonical active-support Fisher/connection migration and equality classification; targeted build, wired umbrella, scoped forbidden-token scan, and standard-only axiom audits pass.
