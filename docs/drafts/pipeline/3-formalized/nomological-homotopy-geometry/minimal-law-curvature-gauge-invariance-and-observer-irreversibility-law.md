# Leading formal-law jet and serial tangent irreversibility law

- **ID:** `nhg-minimal-law-curvature`
- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Field:** Nomological Homotopy Geometry
- **Type:** UNIVERSAL THEOREM / FORMAL-LAW KINEMATICS
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM]`
  `[GAUGE-INVARIANT PRIMARY OPERATION] [HOMOTOPY-ABELIANITY OBSTRUCTION]`
  `[SERIAL TANGENT IRREVERSIBILITY] [FRAMED POLAR THEOREM] [NOT RH]`
  `[LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED]`
- **Statement:** Order of vanishing and leading homogeneous jet of a pointed formal homological
  vector field are invariant under formal coordinate change. For minimal `L_infinity` laws this is
  the first primary operation, not geometric curvature. Serial observers cannot repair tangent
  directions already killed.

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

be its `n`-ary Taylor coefficient. Define the **primary minimal-operation order**

\[
 \rho(H,Q)=\inf\{n\geq2:q_n\ne0\}\in\{2,3,\ldots,\infty\}.
\tag{MLC.4}
\]

If `rho=r<infinity`, call `q_r` the primary minimal operation. If all `q_n` vanish, set
`rho=infinity` and call the germ formally abelian.

This is a definition on a minimal formal law germ. It is not connection or Atiyah curvature.

## 2. Gauge-invariance theorem

Let `(H,Q)` and `(H',Q')` be minimal `L_infinity` algebras. An `L_infinity` morphism is a coalgebra
map

\[
 F:\overline S^c(sH)\longrightarrow\overline S^c(sH')
\tag{MLC.5}
\]

satisfying `FQ=Q'F`. Let `f_n:S^n(sH)->sH'` be its Taylor coefficients.

### Theorem 2.1 — leading formal-jet invariance

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

Therefore the isomorphism class of `(sH,q_r)` under degree-preserving linear isomorphisms is an
invariant of the formal law germ. For a pointed gauge transformation with `f_1=id`, `q_r` itself is
unchanged.

### Proof

If both structures vanish, the conclusion is immediate. If exactly one vanishes, let `m` be the
first nonzero arity of the other. If both are nonzero, let `m` be the smaller first nonzero arity.
Project `FQ=Q'F` to the cogenerators `sH'` and restrict it to coalgebra weight `m`.

In the full coalgebra-morphism equation, every partition term other than
`q'_m S^m(f_1)` contains a target bracket below arity `m`, and every source-side term other than
`f_1q_m` contains a source bracket below arity `m`. They vanish by definition of `m`. The equation
therefore reduces to

\[
 f_1q_m=q'_mS^m(f_1).
\tag{MLC.8}
\]

If exactly one of `q_m,q'_m` is nonzero, invertibility of `f_1` contradicts `(MLC.8)`. Thus either
both structures vanish or their first nonzero arities agree. Equation `(MLC.7)` is `(MLC.8)` at
that arity.
`[PROVED HERE]`

### Corollary 2.2 — homotopy-abelianity obstruction

A minimal `L_infinity` algebra is `L_infinity`-isomorphic to an abelian one if and only if every
Taylor coefficient `q_n`, `n>=2`, vanishes.

### Proof

The reverse implication is immediate. If some `q_r` is first nonzero, Theorem 2.1 forbids an
isomorphism to a structure with curvature order `infinity`. `[PROVED HERE]`

This obstructs abelianization, not strictification to a dg Lie algebra. A nonabelian ordinary Lie
algebra is already strict and has nonzero `q_2`. Higher coordinate terms can move later operations,
but cannot erase the leading operation.

## 3. Intrinsic germ at a sourced law

Let `L` have a complete separated descending filtration compatible with all brackets, let
`alpha in F^1L` be Maurer--Cartan, and twist by the convergent series

\[
 \ell_n^\alpha(x_1,\ldots,x_n)=
 \sum_{j\geq0}{1\over j!}
 \ell_{n+j}(\alpha^{\otimes j},x_1,\ldots,x_n).
\]

Assume the twisted complex has a filtered strong deformation retract onto `H_alpha` and any
comparison of resolutions is supplied by a pointed filtered quasi-isomorphism or zigzag.

Homotopy transfer supplies a minimal structure on `H_alpha`. Minimal-model uniqueness supplies an
isomorphism after fixing the tangent-cohomology identification induced by the comparison zigzag.

### Corollary 3.1 — sourced primary-operation invariant

The value

\[
 \rho_\alpha:=\rho(H_\alpha,Q_\alpha)
\tag{MLC.9}
\]

and the linear-conjugacy class of its first nonzero bracket depend only on the pointed filtered
formal-moduli germ with fixed tangent-cohomology identification, not on the compatible contraction
or resolution.

This is primary nonformality data. Geometric curvature belongs to a relative connection/Atiyah
class on an anchored law algebroid.

## 4. Observer irreversibility

Let

\[
 F:(H,Q)\longrightarrow(M,R)
\tag{MLC.10}
\]

be an `L_infinity` observer between minimal formal law germs. Its tangent reporter is `f_1:H->M`.

### Theorem 4.1 — serial tangent non-equivalence

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

For a finite family of observers `F_i:(H,Q)->(M_i,R_i)`, the componentwise product observer has
injective tangent map if and only if

\[
 \bigcap_i\ker(f_i)_1=0.
\tag{MLC.12}
\]

This need not be an equivalence because injectivity need not be surjectivity. The abelian inclusion
`k->k^2`, `x |-> (x,0)`, is the sharp countermodel. If the product tangent map is invertible, then an
existing morphism of minimal conilpotent `L_infinity` algebras is an isomorphism.

## 5. Framed polar observer

Let `D` and `W` be finite-dimensional Hermitian spaces and let `T:D->W`. Its framed Gram observer is

\[
 G_T=T^*T\succeq0.
\tag{MLC.13}
\]

### Theorem 5.1 — polar fibre classification

For maps `A,B:D->W`,

\[
 \boxed{A^*A=B^*B}
\]

if and only if there is a unitary `U:W->W` such that `B=UA`.

### Proof

If `B=UA`, equality is immediate. Conversely define `U_0(Ax)=Bx`. Equality of the Gram operators
shows that `Ax=0` iff `Bx=0` and that `U_0` preserves inner products. It is therefore an isometry
from `ran A` to `ran B`. Extend it to a unitary between their orthogonal complements. QED.

Thus Gram formation is a full left-unitary quotient. It is not an invariant under arbitrary formal
coordinates: if `q'_r=Cq_rS^r(C^{-1})`, then its Gram contains the metric factor `C^*C`. The theorem
is valid only after Hermitian frames and unitary gauge have been declared as part of the observer.

## 6. Hostile countermodels and limits

1. **Primary operation is not geometric curvature.** A flat nonabelian deformation problem may have
   nonzero `q_2`. Conversely an abelian fibre can have nontrivial flat monodromy.
2. **Leading operation is incomplete.** The theorem gives no conclusion about later operations.
3. **Cohomology dimension is insufficient.** The same graded vector space supports an abelian
   structure and a nonabelian minimal Lie structure; they are not gauge equivalent.
4. **Tangent injectivity is not equivalence.** The abelian inclusion `k->k^2` is injective but not
   invertible. Global topology lies outside this local theorem.
5. **Source selection remains independent.** Choosing a Maurer--Cartan point after inspecting a
   desired theorem is circular. This card proves coordinate invariance only after a source point is
   supplied.
6. **Metric Gram data are framed.** Formal coordinate scaling can change `q_r^*q_r`; no intrinsic
   polar claim exists without a compatible metric and restricted gauge group.

## 7. Field consequence

The theorem supplies Nomological Homotopy Geometry with coordinate-free primary nonformality data:

\[
 \boxed{
 \text{formal sourced law germ}
 \longmapsto
 (\rho_\alpha,[H_\alpha,q_{\rho_\alpha}]).}
\tag{MLC.15}
\]

Different compatible resolutions of one sourced formal law must agree on this leading-jet class.
Actual Atiyah curvature and history require the anchored relative geometry developed separately.

## 8. Literature boundary

Formal moduli problems, `L_infinity` algebras, homotopy transfer, and minimal-model uniqueness are
established parent mathematics. Relevant primary sources include:

- Pridham, *Unifying derived deformation theories*;
- Lurie, *Derived Algebraic Geometry X: Formal Moduli Problems*;
- Maunder, *Homotopy transfer for L-infinity structures and the BV-formalism*,
  <https://arxiv.org/abs/2408.12461>.

The field-level role is an acceptance rule for primary operations: arbitrary comparison defects are
not invariants of a formal law germ.

## Gates

- [x] coordinate-free definition on minimal formal law germs
- [x] gauge-invariance proof
- [x] homotopy-abelianity obstruction
- [x] serial tangent-loss theorem
- [x] exact framed polar-fibre theorem
- [x] hostile global/local and source-selection boundaries
- [ ] construct a nontrivial source-anchored relative law algebroid
- [ ] prove cyclic/self-dual transfer in a source-selected example
- [x] formalize exact leading-jet invariant and observer consequences

## Lean formalization status

- **Module:** `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet`
- **Exact promoted theorem:** `MinimalLawEquiv.firstNonzero_order_eq` and
  `MinimalLawEquiv.firstNonzero_conjugacy` prove the leading nonzero arity and conjugacy invariants;
  the same module formalizes abelianity, serial kernel persistence, product-kernel gates, sharp
  inclusion countermodel, and framed Gram fibre consequences.
- **Verification:** module is wired into NHG umbrella; umbrella build and scratch `#print axioms`
  audit passed on 2026-08-13.

## Log

- 2026-08-09 — leading-jet theorem retained; “curvature” interpretation demoted after flat
  nonabelian countermodel. Relative Atiyah curvature moved to anchored field geometry.
