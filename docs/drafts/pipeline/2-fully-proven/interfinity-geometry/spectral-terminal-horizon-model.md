# Spectral terminal-horizon model

- **ID:** `spectral-terminal-horizon-model`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md` · Theorems
  IX, XI, XII, XV
- **Statement:** A singular Laplace cocycle is distributionally exact at every admissible observer
  but forward-stably exact only across a sharp cut; below the cut it concentrates on a fixed ray,
  and complex-time phase equals signed distance to the cut.

## Goal

Give one dependency-closed analytic model where algebraic exactness, endpoint formation, horizon
residue, observer topology, and phase are provably different pieces of data.

## Gates

- [x] 0 → 1 in-progress: weighted model and observer scale fixed before computation
- [x] 1 → 2 fully-proven: complete paper proof below
- [ ] 2 → 3 formalized: no Lean work authorized in source task
- [ ] 3 → 4 publication-ready: external priority review remains at program level

## Setup

Fix `c>0` and `beta>-2`.  Put

\[
 H_\beta=L^2((0,1),c s^{\beta-1}ds),
 \qquad (T_Vf)(s)=e^{-Vs}f(s),
 \qquad b_V(s)=e^{-Vs}-1.
\tag{1}
\]

For a real observer parameter `rho`, let

\[
 \Phi_\rho=s^\rho C^\infty[0,1]
\tag{2}
\]

with topology transported from `C^infinity[0,1]`, and give `Phi_rho'` the weak-star topology.
The embedding `Phi_rho -> H_beta` is admissible exactly when

\[
 2\rho+\beta>0.
\tag{3}
\]

Write `a=rho+beta`.  Admissibility and `beta>-2` imply `a>-1`.  On
`f=s^rho h`, define

\[
 \eta_a(f)=
 \begin{cases}
 c\displaystyle\int_0^1h(s)s^{a-1}ds,&a>0,\\[2mm]
 c\left(\displaystyle\int_0^1(h(s)-h(0))s^{a-1}ds+{h(0)\over a}\right),&-1<a<0,\\[2mm]
 c\displaystyle\int_0^1{h(s)-h(0)\over s}ds,&a=0.
 \end{cases}
\tag{4}
\]

Let `delta_0(s^rho h)=h(0)`.

## Theorem

1. `b_V in H_beta` for every finite `V`, and

   \[
   b_{V+W}=b_V+T_Vb_W.
   \tag{5}
   \]

   It is a Hilbert coboundary exactly when `beta>0`.
2. At every admissible observer, `(4)` is a continuous distributional primitive:

   \[
   T_V\eta_a-\eta_a=b_V.
   \tag{6}
   \]

   It is forward stable exactly when `a>0`, equivalently `rho+beta>0`.  No alternative primitive
   is stable when `a<=0`.
3. The observer line and stable death region are

   \[
   \mathcal O_\beta=(-\beta/2,\infty),
   \qquad
   D_\beta=(\mathfrak d_\beta,\infty),
   \qquad
   \mathfrak d_\beta=\max(-\beta/2,-\beta),
   \tag{7}
   \]

   with `D_beta=O_beta` when the two left endpoints coincide.  Its horizon width is

   \[
   \mathfrak d_\beta+\beta/2=\max(0,-\beta/2).
   \tag{8}
   \]
4. The common fixed subspace of the multiplication semigroup on `Phi_rho'` is `C delta_0`.  At a
   deficient observer,

   \[
   \begin{aligned}
   V^aT_V\eta_a&\longrightarrow c\Gamma(a)\delta_0,
      &&-1<a<0,\\
   (\log V)^{-1}T_V\eta_0&\longrightarrow-c\delta_0,
      &&a=0.
   \end{aligned}
   \tag{9}
   \]

   These projective limits are unchanged by the finite-part choice.
5. For complex time `z=R exp(i theta)` in any closed subsector of `Re z>0`, if
   `a>-1` and `a!=0`, then

   \[
   R^aT_z\eta_a
   \longrightarrow c\Gamma(a)e^{-ia\theta}\delta_0.
   \tag{10}
   \]

   If `a<0`, the angular phase slope equals the remaining distance to the death cut:

   \[
   \partial_\theta\arg q_a=-a=\mathfrak d_\beta-\rho.
   \tag{11}
   \]

   At `a=0`, on the principal branch,

   \[
   T_z\eta_0=-c(\log z+\gamma)\delta_0+o(1).
   \tag{12}
   \]

## Proof

Near zero, `e^(-Vs)-1=O(s)`, so the squared integrand in `H_beta` is
`O(s^(beta+1))`, integrable exactly under `beta>-2`.  Identity `(5)` is direct.  If `beta>0`, the
constant function `1` belongs to `H_beta` and is a primitive.  Conversely, if
`b_V=(T_V-I)eta` in `H_beta` for one `V>0`, then
`(e^(-Vs)-1)(eta-1)=0` almost everywhere, so `eta=1`; this is square-integrable exactly when
`beta>0`.

For `a>0`, `(6)` follows from the ordinary source integral.  For `-1<a<0`, multiplication by
`e^(-Vs)-1=O(s)` turns `(4)` into an ordinary convergent integral; constants cancel, proving
`(6)`.  The same argument with the logarithmic finite part proves the case `a=0`.

When `a>0`, dominated convergence gives `T_V eta_a ->0`.  If `-1<a<0`, testing `b_V` on the
constant transported test gives a nonzero multiple of `-V^(-a)` asymptotically; at `a=0` it grows
as `-log V`.  Thus `b_V` has no weak-star endpoint.  A stable primitive would force
`b_V -> -eta`, so none exists.  This proves item 2.  Intersecting `rho>-beta` with `(3)` proves
`(7)` and `(8)`.

If a distribution `u` is fixed, then `(e^(-Vs)-1)u=0`.  Since
`(e^(-Vs)-1)/s` is smooth and nowhere zero on `[0,1]`, `su=0`.  Writing every smooth `h` as
`h(0)+sr` shows `u` is a multiple of `delta_0`.

For `-1<a<0`, substitution into `(4)` gives

\[
 (T_V\eta_a)(s^\rho h)
 =c h(0)V^{-a}\gamma(a,V)
  +c\int_0^1e^{-Vs}r(s)s^a ds,
 \qquad h=h(0)+sr.
\tag{13}
\]

The second term is `O(V^(-a-1))` and `gamma(a,V)->Gamma(a)`, proving the first line of `(9)`.
At `a=0`,

\[
 (T_V\eta_0)(s^\rho h)
 =c h(0)\int_0^V{e^{-t}-1\over t}dt+O(V^{-1})
 =-c h(0)(\log V+\gamma)+o(1),
\]

which proves the second line.  Two finite-part extensions differ by a fixed multiple of
`delta_0`; this is negligible under the divergent normalizations in `(9)`.

Replacing `V` by `z` in `(13)`, uniformly on a closed decay subsector, gives
`gamma(a,z)->Gamma(a)` and an `O(R^(-a-1))` remainder.  Since
`z^(-a)=R^(-a)e^(-ia theta)`, `(10)` follows.  For `a<0`, `(7)` has
`d_beta=-beta`, hence `-a=-(rho+beta)=d_beta-rho`, proving `(11)`.  The standard exponential
integral asymptotic

\[
 \int_0^1{e^{-zs}-1\over s}ds=-\log z-\gamma+o(1)
\]

proves `(12)`. `QED`

## Lean handoff notes

Items 1 and the cut arithmetic are elementary.  Hard dependency is a concrete model of the
finite-part distributions `(4)` and weak-star convergence on transported smooth tests.  Formalize
ordinary `a>0` and fixed-space rigidity first; deficient `a<=0` requires incomplete-Gamma and
exponential-integral asymptotics.

## Boundary

Mellin asymptotics, finite-part distributions, and phase locking are classical ingredients.
Candidate-new content belongs to their interpretation as stable-primitive death, fixed-face
residue, and observer-cut distance inside the parent geometry.

