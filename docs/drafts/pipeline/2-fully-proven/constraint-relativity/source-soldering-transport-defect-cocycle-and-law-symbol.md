# Source-soldering curved transport law and first-order law symbol

- **ID:** `source-soldering-transport-defect-cocycle-and-law-symbol`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CURVED BIVARIANT TRANSPORT LAW / FIRST-ORDER OBSTRUCTION
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [ABSTRACT BRIDGE]`
  `[CLASSICAL CATEGORY/DEFORMATION PARENTS] [NO RH CLAIM] [NO LEAN WRITTEN]`
- **Field card:** `../../1-in-progress/constraint-relativity/source-soldering-bivariant-law-geometry.md`.
- **Concrete model:** `congruence-order-trace-kahler-exterior-square-nonmetricity-law.md`.
- **Route-R source parent:** `../interfinity-geometry/arithmetic-three-chart-stable-boundary.md`.

## Theorem 1: soldering transport defect is twisted cocycle

Let `C` be source-history category. For each object `A`, let `K_A,T_A` lie in additive target
category over `A`. For arrow `f:A->B`, suppose extension/transport gives

\[
 K_f:f_!K_A\to K_B,
 \qquad
 T_f:f_!T_A\to T_B,
 \tag{1}
\]

compatible with composition. Let local solderings be

\[
 s_A:K_A\to T_A.
 \tag{2}
\]

For a nonvacuous application, also fix source-derived constitutive groupoids/torsors
`mathscr S_A` mapping into `Hom(K_A,T_A)` and require `s_A in mathscr S_A`. Typical constraints are a
prescribed nonzero head symbol, orientation normalization, quasi-isomorphism, or adjoint of a
nondegenerate pairing. Without such a constraint, zero solderings make every transport system
trivially flat.

Define transport defect

\[
 \boxed{
 Q_f
 =T_f\circ f_!(s_A)-s_B\circ K_f:
 f_!K_A\longrightarrow T_B.}
 \tag{3}
\]

For composable `A -f-> B -g-> C`, canonical associators understood,

\[
 \boxed{
 Q_{gf}
 =T_g\circ g_!(Q_f)
 +Q_g\circ g_!(K_f).}
 \tag{4}
\]

Whenever two admissible solderings have difference `s_A'=s_A+h_A`, changing soldering gives

\[
 \boxed{
 Q_f'-Q_f
 =T_f\circ f_!(h_A)-h_B\circ K_f.}
 \tag{5}
\]

Hence, under strict transports, defect is twisted one-cocycle and an allowed additive change of
local soldering is coboundary. Natural constitutive soldering exists exactly when one may choose
`s_A in mathscr S_A` so every `Q_f=0`. An actual cohomology class requires specified admissible
gauge morphisms of `mathscr S`; arbitrary subsets do not suffice. No obstruction claim is made for
unconstrained Hom-space, which always contains zero family.

### Proof

Composition compatibility gives

\[
 K_{gf}=K_g\circ g_!(K_f),
 \qquad
 T_{gf}=T_g\circ g_!(T_f).
\]

Expand `(3)`:

\[
\begin{aligned}
 Q_{gf}
 &=T_g g_!(T_f) (gf)_!(s_A)-s_CK_g g_!(K_f)\\
 &=T_g g_!\bigl(T_ff_!(s_A)-s_BK_f\bigr)
 +\bigl(T_gg_!(s_B)-s_CK_g\bigr)g_!(K_f),
\end{aligned}
\]

which is `(4)`. Substitute `s+h` into `(3)` to obtain `(5)`. QED.

## Theorem 1b: curved transports force bivariant two-curvature

Drop strict composition compatibility. Define intrinsic transport curvatures

\[
 F^K_{g,f}=K_g\circ g_!(K_f)-K_{gf},
 \qquad
 F^T_{g,f}=T_g\circ g_!(T_f)-T_{gf}.
 \tag{5a}
\]

Then edge defect `(3)` obeys exact curved Bianchi/transgression identity

\[
 \boxed{
 T_g\circ g_!(Q_f)+Q_g\circ g_!(K_f)-Q_{gf}
 =F^T_{g,f}\circ(gf)_!(s_A)-s_C\circ F^K_{g,f}.}
 \tag{5b}
\]

Thus strict cocycle `(4)` is flat special case `F^K=F^T=0`. Curvatures `F^K,F^T` are independent
transport data; `(5b)` computes their soldered difference.

### Proof

Expand left side using `(3)`. Two middle terms
`-T_g g_!(s_B)g_!(K_f)` and `+T_g g_!(s_B)g_!(K_f)` cancel. Remaining terms are

\[
 \left(T_gg_!(T_f)-T_{gf}\right)(gf)_!(s_A)
 -s_C\left(K_gg_!(K_f)-K_{gf}\right),
\]

which is exactly `(5b)`. QED.

### Literal Route-R curvature instance

In existing Route-R same-prime depth chart at `p=2`, put

\[
 m_e=2^{-(e+1)},
 \qquad
 \lambda_e=(e+1)\log2,
 \qquad
 \theta_{ef}=m_e\lambda_f-m_f\lambda_e,
 \tag{5c}
\]

and scalar transports `U_c(e,f)=exp(c theta_ef)` for real `c`. For depths `0,1,2`, direct arithmetic
gives

\[
 \theta_{01}=\frac34\log2,
 \quad
 \theta_{12}=\frac12\log2,
 \quad
 \theta_{02}=\frac{11}{8}\log2,
 \tag{5d}
\]

so

\[
 \boxed{
 \theta_{01}+\theta_{12}-\theta_{02}=-\frac18\log2.}
 \tag{5e}
\]

Therefore scalar `K`-transport curvature

\[
 F^K_{2,1,0}(c)=U_c(1,2)U_c(0,1)-U_c(0,2)
 \tag{5f}
\]

has

\[
 \left.\frac d{dc}F^K_{2,1,0}(c)\right|_{c=0}=-\frac18\log2\ne0.
 \tag{5g}
\]

Take strict scalar `T`-transport and normalized solderings `s_e=1`. Then `Q_{ef}=1-U_c(e,f)`
and `(5b)` reads `delta Q=-F^K` exactly. This is source-defined before critical-line
specialization. It proves Route R requires curved two-transport; strict theorem `(4)` alone cannot
model it. It detects radial displacement but does not force curvature to vanish.

### Bianchi consistency for source current

Field equation

\[
 Q_f=J_f:f_!K_A\longrightarrow T_B
 \tag{6}
\]

is consistent only if independently constructed source current obeys curved law

\[
 \boxed{
 T_g g_!(J_f)+J_g g_!(K_f)-J_{gf}
 =F^T_{g,f}(gf)_!(s_A)-s_CF^K_{g,f}.}
 \tag{7}
\]

This is `(5b)` with `Q=J`; under strict transports it reduces to flat cocycle law. It is necessary,
not sufficient: `J` must also lie in image of constrained soldering problem. Thus arbitrary post-hoc
`J_f` is falsified before any RH application. Equation `(6)` is substantive only together with
constitutive constraint `s_A in mathscr S_A`; otherwise `s=J=0` is tautological.

## Theorem 2: first-order law symbol and soldering obstruction

Let `(A,mathfrak m,k)` be a local `k`-algebra equipped with a coefficient embedding
`k -> A` inducing the identity `k -> A/mathfrak m`, and let `M` be an `A`-module with
`mathfrak m^2M=0`. Define

\[
 W=\mathfrak m/\mathfrak m^2,
 \qquad
 H_M=M/\mathfrak mM,
 \qquad
 S_M=\mathfrak mM.
 \tag{8}
\]

Multiplication induces canonical first-order law symbol

\[
 \boxed{
 \sigma_M:W\otimes_kH_M\longrightarrow S_M.}
 \tag{9}
\]

For modules `M,N` annihilated by `mathfrak m^2`, head map `f:H_M->H_N` lifts to an `A`-linear
map `M->N` only if there exists radical-layer map `g:S_M->S_N` satisfying

\[
 \boxed{
 g\circ\sigma_M
 =\sigma_N\circ(1_W\otimes f).}
 \tag{10}
\]

Conversely such `g` is sufficient. Therefore exact first-order obstruction is

\[
 \boxed{
 \mathcal N(f)
 =\left[\sigma_N(1_W\otimes f)\right]
 \in
 \operatorname{coker}\left(
 \operatorname{Hom}_k(S_M,S_N)
 \xrightarrow{g\mapsto g\sigma_M}
 \operatorname{Hom}_k(W\otimes H_M,S_N)
 \right).}
 \tag{11}
\]

Map `f` lifts iff `mathcal N(f)=0`.

### Proof

For `A`-linear `phi:M->N`, induced maps on head and radical layer satisfy

\[
 g([u]m)=\phi(um)=u\phi(m)=\sigma_N([u]\otimes f([m])),
\]

which is `(10)`. Conversely, the chosen coefficient field makes `M` and `N` `k`-vector spaces.
Choose `k`-linear splittings `M=H_M+S_M`, `N=H_N+S_N`. Define
`phi` by `f` on chosen head lifts and `g` on radical layer. Condition `(10)` is precisely compatibility
with multiplication by `mathfrak m`; scalars act through `k`, and `mathfrak m^2` kills both modules.
Thus `phi` is `A`-linear. Obstruction statement follows. QED.

## Concrete sharp model

For congruence order `A=R1+aR^N`, `N>=3`, take `R=C[[a]]` and

\[
 M=\Omega_{A/R},
 \qquad N=L=A^\sharp/A.
\]

Both are killed by `mathfrak m_A^2`. Concrete theorem proves reduction map

\[
 \operatorname{Hom}_A(\Omega,L)
 \to\operatorname{Hom}_k(H_\Omega,H_L)
\]

is zero. Hence `f \mapsto \mathcal N(f)` is injective and every nonzero tangent soldering has nonzero
first-order obstruction, even for `N=3` where Kähler and Dedekind differents agree.

This is stronger than barcode or determinant mismatch: obstruction lives in multiplication symbol
across one square-zero thickening.

## Novelty and scope

Natural-transformation defects, category cohomology, cotangent obstruction theory, Loewy symbols,
and deformation lifting are classical. The theorem is abstract infrastructure, not novelty claim.
Potentially new leverage is exact coupling to trace-duality/cotangent source charts and literal
arithmetic comparisons.

Latest adjacent cotangent work: https://arxiv.org/abs/2602.07353.

No RH conclusion follows. To carry arithmetic weight, one must instantiate `C,K,T,s,J` from literal
source independently of critical line and compute nontrivial `Q`.

## Lean-return note

No Lean work authorized. Later formalization can begin with Theorem 1 in additive category with
strict transports, then finite-dimensional square-zero algebra version of Theorem 2.

## Gates

- [x] typed defect and cocycle law
- [x] curved two-transport Bianchi law
- [x] literal Route-R nonzero two-curvature instance
- [x] gauge/coboundary law
- [x] source-current consistency condition
- [x] zero-soldering vacuity isolated and excluded by constitutive class
- [x] coordinate-free first-order obstruction
- [x] concrete maximal obstruction model
- [x] second tensor-composition family (separate paper card)
- [x] literal Route-R scalar two-curvature computation
- [ ] typed Route L/R trace--cotangent realization
- [ ] Lean formalization

## Log

- 2026-08-08 -- converted trace/cotangent mismatch into bivariant transport curvature and
  first-infinitesimal law-symbol obstruction.
