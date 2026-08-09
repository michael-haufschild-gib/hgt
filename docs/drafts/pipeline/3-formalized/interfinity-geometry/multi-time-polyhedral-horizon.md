# Multi-time polyhedral horizon

- **ID:** `multi-time-polyhedral-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md` · Theorem
  XXIV
- **Statement:** A tensor Laplace source with `d` independent future times has an open polyhedral
  stable-exactness region, a Boolean lattice of fixed boundary faces, and complex-time phase equal
  to the conormal covector of its deficient faces.

## Goal

Prove that stable-exactness geometry is not intrinsically one-dimensional.  Produce a complete
corner model with independent source times and all face conditions visible.

## Gates

- [x] 0 → 1 in-progress: tensor source and face-stability fixed
- [x] 1 → 2 fully-proven: complete paper proof below
- [x] 2 → 3 formalized: `multi-time-polyhedral-horizon-formalized.md`
- [ ] 3 → 4 publication-ready: program-level novelty audit remains open

## Setup

Fix `d>=1`, `c>0`, and `beta_j>-2`.  Put

\[
 H_{\boldsymbol\beta}
 =L^2\!\left((0,1)^d,c\prod_{j=1}^d s_j^{\beta_j-1}d\mathbf s\right),
 \qquad
 (T^{(j)}_{V_j}f)(\mathbf s)=e^{-V_js_j}f(\mathbf s).
\tag{1}
\]

The formal constant source has cubical coboundary

\[
 b_{\mathbf V}(\mathbf s)=\prod_{j=1}^d(e^{-V_js_j}-1).
\tag{2}
\]

For `rho in R^d`, use

\[
 \Phi_{\boldsymbol\rho}
 =\left(\prod_j s_j^{\rho_j}\right)C^\infty([0,1]^d).
\tag{3}
\]

A primitive is **face-stable** if, for every nonempty `J subset {1,...,d}`, its orbit under
`prod_(j in J)T^(j)_(V_j)` tends weak-star to zero as all `V_j`, `j in J`, tend cofinally to
infinity.

## Theorem

1. `b_V in H_beta` for every finite time tuple.
2. The admissible observer region and face-stable death region are

   \[
   \begin{aligned}
   \mathcal O_{\boldsymbol\beta}
   &=\{\boldsymbol\rho:2\rho_j+\beta_j>0\ \forall j\},\\
   D_{\boldsymbol\beta}
   &=\{\boldsymbol\rho\in\mathcal O_{\boldsymbol\beta}:
        \rho_j+\beta_j>0\ \forall j\}.
   \end{aligned}
   \tag{4}
   \]

   At every admissible observer, `(2)` is an iterated finite-part coboundary.  It has a
   face-stable primitive exactly in `D_beta`.
3. For `J subset {1,...,d}`, the common fixed subspace of the times in `J` is

   \[
   F_J
   =\delta_{\{s_j=0:j\in J\}}
     \widehat\otimes\mathcal D'([0,1]^{J^c}).
   \tag{5}
   \]

   These spaces form the Boolean face lattice of a `d`-corner.  The deepest fixed stratum is
   `C delta_0`.
4. Put `a_j=rho_j+beta_j` and assume `a_j>-1`, `a_j!=0`.  Under the transported smooth charts,
   define

   \[
   \eta_{\mathbf a}
   =c\bigotimes_{j=1}^d\operatorname {Fp}(s_j^{a_j-1}),
   \tag{6}
   \]

   with coefficient-one finite parts.  For `z_j=R_j exp(i theta_j)` in closed decay subsectors,

   \[
   \left(\prod_jR_j^{a_j}\right)T_{\mathbf z}\eta_{\mathbf a}
   \longrightarrow
   c\left(\prod_j\Gamma(a_j)e^{-ia_j\theta_j}\right)\delta_0.
   \tag{7}
   \]

   On every deficient coordinate `a_j<0`, its phase covector is the inward conormal distance to
   the corresponding death face:

   \[
   \partial_{\theta_j}\arg q_{\mathbf a}
   =-a_j=-\beta_j-\rho_j.
   \tag{8}
   \]

   Coordinates with `a_j=0` obey the logarithmic one-dimensional contact law.

## Proof

The norm factorizes:

\[
 \lVert b_{\mathbf V}\rVert^2
 =c\prod_j\int_0^1|e^{-V_js}-1|^2s^{\beta_j-1}ds.
\]

Each factor is finite because its integrand is `O(s^(beta_j+1))` at zero and `beta_j>-2`.

For `f=(prod s_j^rho_j)h`, membership in `H_beta` for every smooth `h` is equivalent to
`2rho_j+beta_j>0` in every coordinate.  Necessity follows by a factorized test nonzero at the
chosen face.  This proves the first line of `(4)`.

Put `a_j=rho_j+beta_j`.  Admissibility implies `a_j>-1`.  Distribution `(6)` is continuous.
Multiplication by each `e^(-V_js_j)-1=O(s_j)` converts its corresponding finite-part factor into
an ordinary integral, so applying all differences gives `(2)`.  If every `a_j>0`, ordinary
dominated convergence in any varying tensor factor, together with equicontinuity of the others,
proves every nonempty partial orbit tends to zero.

Conversely, suppose `a_k<=0` and let `eta'` be any primitive.  The difference
`u=eta'-eta_a` is killed, for one fixed positive time tuple, by
`prod_j(e^(-V_js_j)-1)`, hence by `prod_j s_j` because the quotient is smooth and nowhere zero.
Test with a tensor whose factors away from `k` have compact support inside `(0,1)` and pair
nontrivially with the corresponding source distributions.  On this support every `s_j`, `j!=k`,
is invertible, so `s_k u=0`; therefore `T^(k)_V u=u` on the test.  The canonical primitive's
pairing grows as a nonzero power when `a_k<0` and as `log V` when `a_k=0`.  The fixed contribution
from `u` cannot cancel it.  Thus the singleton `k`-face is not stable.  This proves the second line
of `(4)` and primitive-independent necessity.

If a distribution is fixed by every `T^(j)` with `j in J`, division by the smooth nowhere-zero
function `(e^(-V_js_j)-1)/s_j` shows `s_j u=0` for every such `j`.  A distribution killed by
multiplication by one coordinate is a delta in that coordinate with arbitrary distribution in the
others.  Iteration proves `(5)`.

Finally, `(6)` and the semigroup are tensor products.  The one-dimensional sectorial asymptotic

\[
 R^aT_{R e^{i\theta}}\operatorname {Fp}(s^{a-1})
 \longrightarrow\Gamma(a)e^{-ia\theta}\delta_0
\]

holds uniformly in closed right-half-plane subsectors for every `a>-1`, `a!=0`.  Tensoring gives
`(7)`.  Its phase is `-sum_j a_j theta_j` up to a constant.  In a deficient coordinate the death
face is `rho_j=-beta_j`, so `(8)` follows. `QED`

## Lean handoff notes

Split formalization into: product integrability; algebraic tensor difference; fixed-distribution
classification; face-stability; sectorial asymptotics.  Last two require distribution and complex
Gamma infrastructure.  No existing Lean file is designated.

## Boundary

Tensor products, cubical differences, orthant persistence, and Mellin asymptotics are parents.
Candidate-new content lies in their stable-primitive gluing: all partial futures are required,
fixed strata become the horizon face lattice, and phase records its conormal deficit.

