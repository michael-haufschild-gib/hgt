# Minimal law curvature, gauge invariance, and observer irreversibility law

- **ID:** `nhg-minimal-law-curvature`
- **Stage:** 2 — fully proven on paper
- **Field:** Nomological Homotopy Geometry
- **Type:** UNIVERSAL THEOREM / FORMAL-LAW KINEMATICS
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]`
  `[GAUGE-INVARIANT FIRST CURVATURE] [STRICTIFICATION OBSTRUCTION]`
  `[SERIAL OBSERVER IRREVERSIBILITY] [NOT SOURCE SELECTION] [NOT RH]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Statement:** The arity and linear-conjugacy class of the first nonzero bracket in a minimal
  `L_infinity` law model are invariant under every `L_infinity` coordinate change. A nonzero first
  bracket cannot be removed by higher gauge terms. Any observer whose tangent map loses a law
  direction can never be repaired by later serial observers.

## 1. Minimal formal law germs

Let `k` be a field of characteristic zero and let `H` be a graded `k`-vector space. Write `sH` for
its suspension and

\[
 \overline S^c(sH)=\bigoplus_{n\geq1}S^n(sH)
\tag{MLC.1}
\]

for the reduced conilpotent symmetric coalgebra.

A minimal `L_infinity` structure on `H` is a degree-one coderivation

\[
 Q:\overline S^c(sH)\longrightarrow\overline S^c(sH),
 \qquad Q^2=0,
\tag{MLC.2}
\]

whose unary Taylor coefficient is zero. Let

\[
 q_n:S^n(sH)\longrightarrow sH
\tag{MLC.3}
\]

be its `n`-ary Taylor coefficient. Define the **minimal law-curvature order**

\[
 \rho(H,Q)=\inf\{n\geq2:q_n\ne0\}\in\{2,3,\ldots,\infty\}.
\tag{MLC.4}
\]

If `rho=r<infinity`, call `q_r` the first minimal law-curvature tensor. If all `q_n` vanish, set
`rho=infinity` and call the germ formally abelian.

This is a definition on a minimal formal law germ. It is not a claim that every mathematical
obstruction is curvature.

## 2. Gauge-invariance theorem

Let `(H,Q)` and `(H',Q')` be minimal `L_infinity` algebras. An `L_infinity` morphism is a coalgebra
map

\[
 F:\overline S^c(sH)\longrightarrow\overline S^c(sH')
\tag{MLC.5}
\]

satisfying `FQ=Q'F`. Let `f_n:S^n(sH)->sH'` be its Taylor coefficients.

### Theorem 2.1 — first-curvature invariance

Assume `F` is an `L_infinity` isomorphism, equivalently its linear coefficient
`f_1:sH->sH'` is invertible. Then

\[
 \boxed{\rho(H,Q)=\rho(H',Q').}
\tag{MLC.6}
\]

If their common finite value is `r`, then

\[
 \boxed{
 f_1q_r=q'_r\,S^r(f_1).}
\tag{MLC.7}
\]

Therefore the `GL(H)`-orbit of the first nonzero bracket is an invariant of the formal law germ.
For a pointed gauge transformation with `f_1=id`, the tensor `q_r` itself is unchanged.

### Proof

Project the identity `FQ=Q'F` to the cogenerators `sH'` and restrict it to coalgebra weight `n`.
Let `m` be the smaller of the two first nonzero arities. For every weight below `m`, both sides
contain only zero bracket coefficients.

At weight `m`, every summand involving a nonlinear coefficient `f_j`, `j>1`, also contains a
bracket of arity below `m`, hence vanishes. The entire weight-`m` equation reduces to

\[
 f_1q_m=q'_mS^m(f_1).
\tag{MLC.8}
\]

If exactly one of `q_m,q'_m` were nonzero, invertibility of `f_1` would contradict `(MLC.8)`.
Thus their first nonzero arities agree. Equation `(MLC.7)` is then `(MLC.8)` at that arity.
`[PROVED HERE]`

### Corollary 2.2 — strictification obstruction

A minimal `L_infinity` algebra is `L_infinity`-isomorphic to an abelian one if and only if every
Taylor coefficient `q_n`, `n>=2`, vanishes.

### Proof

The reverse implication is immediate. If some `q_r` is first nonzero, Theorem 2.1 forbids an
isomorphism to a structure with curvature order `infinity`. `[PROVED HERE]`

This is the exact anti-theatre boundary. Higher coordinate terms can move later brackets and their
representatives, but they cannot erase the first nonzero operation.

## 3. Intrinsic germ at a sourced law

Let `L` be a complete filtered `L_infinity` algebra and let `alpha` be a Maurer--Cartan element.
Twist the brackets by `alpha`; the unary bracket of the twist is the deformation differential at
the sourced law. Suppose this complex admits a contraction onto its cohomology `H_alpha`.

The homotopy-transfer theorem supplies a minimal `L_infinity` structure on `H_alpha`. Minimal-model
uniqueness supplies an `L_infinity` isomorphism between the structures obtained from any two
contractions, with linear part the canonical cohomology identification. Theorem 2.1 therefore
gives:

### Corollary 3.1 — sourced formal-curvature invariant

The value

\[
 \rho_\alpha:=\rho(H_\alpha,Q_\alpha)
\tag{MLC.9}
\]

and the linear-conjugacy class of its first nonzero bracket depend only on the formal moduli germ
of the sourced law `alpha`, not on the chosen contraction, resolution, propagator, or local proof
coordinates.

This corollary uses standard homotopy transfer and minimal-model uniqueness as parent theory. The
new field definition is the decision to reserve **nomological curvature** for this invariant germ
data, rather than for an arbitrary noncommuting observer square.

## 4. Observer irreversibility

Let

\[
 F:(H,Q)\longrightarrow(M,R)
\tag{MLC.10}
\]

be an `L_infinity` observer between minimal formal law germs. Its tangent reporter is `f_1:H->M`.

### Theorem 4.1 — serial loss cannot be repaired

If `f_1` is not injective, then for every later `L_infinity` observer

\[
 G:(M,R)\longrightarrow(N,S),
\]

the composite `G o F` is not an `L_infinity` equivalence. More precisely,

\[
 \ker f_1\subseteq\ker(g_1f_1).
\tag{MLC.11}
\]

### Proof

The linear coefficient of an `L_infinity` composite is the composite of the linear coefficients.
Thus `f_1x=0` implies `g_1f_1x=0`. An `L_infinity` equivalence must have invertible linear
coefficient. `[PROVED HERE]`

### Corollary 4.2 — parallel infinitesimal reconstruction gate

For observers `F_i:(H,Q)->(M_i,R_i)`, the product observer can be infinitesimally conservative only
if

\[
 \bigcap_i\ker(f_i)_1=0.
\tag{MLC.12}
\]

This condition is necessary, not sufficient, for equivalence of formal moduli problems: nonlinear
brackets, isotropy, topology, and global components can still be lost.

## 5. Curvature versus positive shadow

Assume now that the relevant graded pieces are finite-dimensional complex Hilbert spaces and let
`q_r:S^r(sH)->sH` be the first curvature tensor. Its positive polar shadow is

\[
 G_r=q_r^*q_r\succeq0.
\tag{MLC.13}
\]

It records `ker q_r`, rank, and squared singular values. It does not recover the unsquared tensor:

\[
 (e^{i\theta}q_r)^*(e^{i\theta}q_r)=G_r
\tag{MLC.14}
\]

for every `theta`. Over the reals, `q_r` and `-q_r` have the same shadow.

### Theorem 5.1 — no gauge-invariant phase recovery from the polar shadow

On any class containing a nonzero `q_r` and its full scalar phase orbit, there is no function of
`G_r` alone that recovers the original phased tensor for every point of the orbit.

### Proof

All phased tensors in the orbit have the same input `G_r`. A function of that input has one value,
but recovery would require it to equal the distinct tensors `e^(i theta)q_r`. `[PROVED HERE]`

This theorem does not say positivity always loses phase. It says the specific Gram scalarization
of the invariant law-curvature tensor is a phase quotient.

## 6. Hostile countermodels and limits

1. **Global holonomy is independent.** A flat local system has all local minimal brackets zero and
   can still have nontrivial global holonomy. `rho=infinity` does not classify the global law.
2. **First curvature is incomplete.** Two minimal structures can have the same `q_r` and different
   higher brackets. The theorem supplies a first invariant, not a complete moduli invariant.
3. **Cohomology dimension is insufficient.** The same graded vector space supports an abelian
   structure and a nonabelian minimal Lie structure; they are not gauge equivalent.
4. **Tangent injectivity is insufficient.** An observer can be tangent-injective and still identify
   distinct global components or destroy topology, order, polarization, or action.
5. **Source selection remains independent.** Choosing a Maurer--Cartan point after inspecting a
   desired theorem is circular. This card proves coordinate invariance only after a source point is
   supplied.
6. **Arbitrary square defects are excluded.** A Beck--Chevalley cofiber, commutator, or chosen
   comparison is not nomological curvature unless it is shown to represent the invariant minimal
   bracket of a sourced formal law germ.

## 7. Field consequence

The theorem supplies Nomological Homotopy Geometry with a coordinate-free local curvature:

\[
 \boxed{
 \text{formal sourced law germ}
 \longmapsto
 (\rho_\alpha,[q_{\rho_\alpha}]).}
\tag{MLC.15}
\]

Proof routes may choose different resolutions and contractions. If they describe the same sourced
formal law, their first minimal curvature tensors must agree up to linear conjugacy. A disagreement
is a falsifier of the claim that the routes are gauges of one law.

## 8. Literature boundary

Formal moduli problems, `L_infinity` algebras, homotopy transfer, and minimal-model uniqueness are
established parent mathematics. Relevant primary sources include:

- Pridham, *Unifying derived deformation theories*;
- Lurie, *Derived Algebraic Geometry X: Formal Moduli Problems*;
- Maunder, *Homotopy transfer for L-infinity structures and the BV-formalism*,
  <https://arxiv.org/abs/2408.12461>.

The field-level delta is not parent machinery. It is the invariant acceptance rule: only the first
nonzero transferred operation of a source-normalized law germ may be called intrinsic local
nomological curvature.

## Gates

- [x] coordinate-free definition on minimal formal law germs
- [x] gauge-invariance proof
- [x] strictification obstruction
- [x] serial observer-loss theorem
- [x] exact polar-shadow phase-loss theorem
- [x] hostile global/local and source-selection boundaries
- [ ] construct a nontrivial source-normalized formal law stack
- [ ] prove cyclic/self-dual transfer in a source-selected example
- [ ] formalize only after field foundations stabilize

## Lean-return note

No Lean file was written or built. Any future formalization should begin with conilpotent symmetric
coalgebras and weight filtrations, after checking existing mathlib support.

## Log

- 2026-08-09 — extracted as first route-independent curvature theorem for Nomological Homotopy
  Geometry after arbitrary observer-square curvature was rejected as presentation-dependent.
