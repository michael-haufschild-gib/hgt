# Hard-edge Gauss-node jet coherence and Padé-residue survival

- **ID:** `mass-shifted-hard-edge-gauss-node-jet-residue-law`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, selected shifted-Xi null faces
- **Type:** THEOREM + FRONTIER REDUCTION (paper)
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-hard-edge-super-apex-hausdorff-inertia`, the literal shifted-Xi
  moment ODE, finite flat quadrature, finite Padé-contact parity, and hard-edge compactification
- **Statement:** In every positive shifted-Xi Hankel chamber, each positive Gauss node has a
  strictly increasing centered-reciprocal hard coordinate. At a flat face, all hard coordinates
  share the complete Padé-contact jet: every lower derivative vanishes and the first nonzero
  derivative has the right-face sign. A simple negative limiting hard root with positive terminal
  mass produces a positive, nonvanishing Padé-pole residue on the analytic positive-mass axis.

## Goal

The super-apex theorem identifies a negative hard root as a quadrature node with

\[
u_i=x_i^{-1}-y<0.
\]

This card asks two harder questions.

1. How can `u_i` move under the **actual** shifted-Xi moment flow?
2. Can a node whose ordinary Christoffel weight vanishes still remain visible to a literal source
   observable?

Both answers are exact. The resulting theorem also falsifies another proposed shortcut: Padé
contact orientation controls derivatives of hard roots, not their absolute side of the endpoint.

## 1. Positive-chamber setup

Put

\[
s_y(k)=\Re\,\operatorname{xiShiftedReciprocalMoment}(y,k),
\qquad L_y(X^k)=s_y(k).
\]

The literal moment ODE is

\[
\frac d{dy}s_y(k)=-(k+1)s_y(k+1).                            \tag{GJRS.1}
\]

Fix a positive integer `n` and an interval on which the Hankel blocks required for the monic
degree-`n` orthogonal polynomial are positive definite. Let

\[
p_y(X)=\prod_{i=1}^n(X-x_i(y))
\]

be that monic polynomial, with its simple real roots locally enumerated smoothly. Let `omega_i(y)`
be the positive `n`-node Gauss weights. Quadrature is exact through degree `2n-1`:

\[
L_y(g)=\sum_i\omega_i g(x_i),
\qquad \deg g\le2n-1.                                      \tag{GJRS.2}
\]

Write

\[
h_n(y)=L_y(p_y^2)>0,
\qquad
\ell_i(X)=\frac{p_y(X)}{X-x_i},
\qquad
\gamma_i(y)=L_y(\ell_i^2)=\omega_i p_y'(x_i)^2>0.          \tag{GJRS.3}
\]

The centered reciprocal and normalized endpoint coordinates are

\[
u_i(y)=x_i(y)^{-1}-y,
\qquad t_i(y)=yx_i(y)=\frac y{y+u_i(y)}.                    \tag{GJRS.4}
\]

Only positive nodes are used in (GJRS.4). Every node with bounded hard coordinate is positive for
large `y`, which is the regime consumed by Route U.

## 2. Exact hard-node velocity in a positive chamber

The canonical atomic Möbius flow from the current Gauss quadrature is

\[
\widetilde x_i(h)=\frac{x_i}{1+hx_i},
\qquad
\widetilde\omega_i(h)=\frac{\omega_i}{1+hx_i}.              \tag{GJRS.5}
\]

Its `k`th moment derivative at zero is

\[
\frac d{dh}\sum_i
 \frac{\omega_i x_i^k}{(1+hx_i)^{k+1}}\bigg|_{h=0}
=-(k+1)\sum_i\omega_i x_i^{k+1}.                            \tag{GJRS.6}
\]

For `k<2n-1`, (GJRS.1), (GJRS.2), and (GJRS.6) agree. At `k=2n-1` their difference is

\[
-2n\left(s_y(2n)-\sum_i\omega_i x_i^{2n}\right).
\]

Since `p_y` is monic and quadrature kills `p_y^2`, exactness below degree `2n` gives

\[
s_y(2n)-\sum_i\omega_i x_i^{2n}=L_y(p_y^2)=h_n.             \tag{GJRS.7}
\]

The moment map from `n` distinct nodes and nonzero weights to moments `0,...,2n-1` has confluent
Vandermonde Jacobian and is locally invertible. To extract one node component, use the normalized
Lagrange polynomial

\[
L_i(X)=\frac{p_y(X)}{(X-x_i)p_y'(x_i)}
\]

and its Hermite derivative cardinal

\[
H_i(X)=(X-x_i)L_i(X)^2.                                    \tag{GJRS.8}
\]

It satisfies

\[
H_i(x_j)=0,
\qquad H_i'(x_j)=\mathbf1_{i=j},
\qquad [X^{2n-1}]H_i=\frac1{p_y'(x_i)^2}.                   \tag{GJRS.9}
\]

Applying the one-coordinate moment discrepancy to (GJRS.9) gives

\[
\boxed{\quad
x_i'(y)=-x_i(y)^2-\frac{2n\,h_n(y)}{\gamma_i(y)}.
\quad}                                                       \tag{GJRS.10}
\]

Consequently

\[
\boxed{\quad
u_i'(y)=\frac{2n\,h_n(y)}{x_i(y)^2\gamma_i(y)}>0.
\quad}                                                       \tag{GJRS.11}
\]

This is the exact source flow of every hard node. It is stronger than monotonicity of a symmetric
recurrence coefficient: it resolves each individual Gauss root and its Christoffel-normalized
speed.

Two immediate consequences are:

\[
u_i(Y)-u_i(y)
=\int_y^Y\frac{2n\,h_n(v)}{x_i(v)^2\gamma_i(v)}\,dv,        \tag{GJRS.12}
\]

and the super-apex count can only decrease as mass moves to the right. Each endpoint crossing is
simple inside the positive chamber. Moving left from the far-right chamber, leakage can occur only
by monotone loss of an absolute hard-coordinate reserve.

## 3. Complete flat-contact jet

Now fix a positive flat face at `y=y_0`. Its degree-`n` null polynomial `p` has nodes `x_i` and
weights `omega_i`, and the flat quadrature is exact through degree `2n`. Define its Padé defects

\[
\delta_k=s_{y_0}(k)-\sum_i\omega_i x_i^k.                   \tag{GJRS.13}
\]

Suppose the first nonzero defect is

\[
\delta_k=0\quad(k<2n+d),
\qquad
\delta_{2n+d}\ne0,
\qquad d>0.                                                  \tag{GJRS.14}
\]

Such a finite `d` exists for every literal shifted-Xi flat face because an infinite-order finite
atomic shadow would make the Xi logarithmic derivative rational.

For the actual moment curve and the atomic Möbius curve, the `r`th derivatives satisfy

\[
s_{y_0}^{(r)}(k)
=(-1)^r(k+1)^{\overline r}s_{y_0}(k+r),                     \tag{GJRS.15}
\]

with the same formula using quadrature moments for the atomic curve. Here

\[
a^{\overline r}=a(a+1)\cdots(a+r-1).
\]

Equations (GJRS.14)--(GJRS.15) show that the first `2n` moment jets agree through order `d`. At
order `d+1`, every coordinate still agrees except the top visible moment `k=2n-1`, where actual
minus atomic equals

\[
(-1)^{d+1}(2n)^{\overline{d+1}}\delta_{2n+d}.               \tag{GJRS.16}
\]

Local invertibility of the moment map and the same Hermite cardinal (GJRS.8) therefore give

\[
x_i^{(r)}(y_0)=\widetilde x_i^{(r)}(0)quad(0\le r\le d),    \tag{GJRS.17}
\]

\[
x_i^{(d+1)}(y_0)-\widetilde x_i^{(d+1)}(0)
=\frac{(-1)^{d+1}(2n)^{\overline{d+1}}\delta_{2n+d}}
       {\gamma_i}.                                          \tag{GJRS.18}
\]

The atomic hard coordinate is exactly constant:

\[
\widetilde x_i(h)^{-1}-(y_0+h)=x_i^{-1}-y_0.
\]

Thus (GJRS.17)--(GJRS.18) become the complete hard-coordinate jet law

\[
\boxed{\quad
u_i^{(r)}(y_0)=0\quad(1\le r\le d),
\quad}                                                       \tag{GJRS.19}
\]

\[
\boxed{\quad
u_i^{(d+1)}(y_0)
=\frac{(-1)^d(2n)^{\overline{d+1}}\delta_{2n+d}}
       {x_i^2\gamma_i}.
\quad}                                                       \tag{GJRS.20}
\]

At a face positive semidefinite immediately to the right, the existing literal Xi contact-parity
theorem gives

\[
(-1)^d\delta_{2n+d}>0.
\]

Hence every positive hard node has the **same strictly positive first nonzero derivative**:

\[
\boxed{\qquad u_i^{(d+1)}(y_0)>0.\qquad}                    \tag{GJRS.21}
\]

For a genuine two-sided cone loss, existing parity classification forces `d` odd. Then `d+1` is
even, so every hard coordinate has a strict local minimum at the selected face. Contact order is
therefore a coherent root-jet order, not merely a determinant multiplicity.

## 4. Orientation does not anchor level

Equation (GJRS.21) is strong but does not imply `u_i(y_0)>=0`. It remains valid if every local
minimum lies below zero. Thus:

> every source theorem that only signs the first nonzero Padé defect controls hard-root
> orientation but cannot determine which side of the endpoint the root occupies.

This explains the repeated Route-U failure of terminal flux, contact parity, cumulant reserve,
and generic Riccati arguments. They all see a derivative of `u_i`; the missing datum is an
absolute anchor for (GJRS.12).

The exact minimal positive-chamber anchor is

\[
u_i(Y)\ge
\int_{y_0}^Y\frac{2n\,h_n(v)}{x_i(v)^2\gamma_i(v)}\,dv      \tag{GJRS.22}
\]

at one source-controlled right mass `Y`. Fixed-degree arcsine limits do not give (GJRS.22) at
`n asymp sqrt(y_0)`.

## 5. Canonical Padé resolvent and absolute poles

The flat quadrature defines its canonical finite atomic continuation

\[
R_{y_0}(Y)
=\sum_i\frac{\omega_i}{1+(Y-y_0)x_i}
=\sum_i\frac{\rho_i}{Y+u_i},
\qquad
\rho_i=\frac{\omega_i}{x_i}>0.                              \tag{GJRS.23}
\]

By (GJRS.1) and flat exactness, the Taylor series of `R_(y_0)` at `Y=y_0` agrees with the literal
field

\[
G(Y)=s_Y(0)=\Re\sum_q\frac1{Y+\operatorname{xiSquaredNode}(q)}
\]

through order `2n`. The first later disagreement is the Padé defect (GJRS.14).

The pole of `R_(y_0)` carried by node `x_i` is

\[
Y_i=y_0-x_i^{-1}=-u_i.                                     \tag{GJRS.24}
\]

A negative hard root is therefore a positive-mass Padé pole. This pole lies on an axis where the
literal completed-Xi resolvent `G` is analytic, because every squared Xi node has positive real
part. Analyticity alone is not enough: moving-order Padé approximants can carry spurious poles
unless local boundedness or convergence is proved.

## 6. Exact residue in hard-edge variables

Put `y_0=a^2` and allow the flat null polynomial `p` to carry the normalization used by hard-edge
compactness. Define

\[
S(u)=\left(1+\frac u{y_0}\right)^n
      p\!\left(\frac1{y_0+u}\right).                        \tag{GJRS.25}
\]

At the root pair `u_i=x_i^{-1}-y_0`, differentiation gives

\[
S'(u_i)=-t_i^{-n}x_i^2p'(x_i),
\qquad t_i=y_0x_i.                                         \tag{GJRS.26}
\]

Let

\[
g_p(z)=\frac a{\sqrt{a^2+z^2}}
       p\!\left((a^2+z^2)^{-1}\right)
\]

be the literal rational hard-edge test. Continuous cancellation gives

\[
\frac{g_p(z)}{z^2-u_i}
=-x_i\,g_{X\ell_i}(z).                                     \tag{GJRS.27}
\]

The exact finite completed-Xi identity `mathcal W(g_(a,q))=y_0 L_(y_0)(q^2)` and flat radical
orthogonality yield

\[
\Gamma_i
:=\mathcal W\!\left(\frac{g_p}{z^2-u_i}
                         ,\frac{g_p}{z^2-u_i}\right)
=y_0x_i^4\gamma_i>0.                                       \tag{GJRS.28}
\]

Combining (GJRS.3), (GJRS.23), (GJRS.26), and (GJRS.28) gives the scale-invariant residue law

\[
\boxed{\quad
\rho_i
=\operatorname*{Res}_{Y=-u_i}R_{y_0}(Y)
=\frac{\Gamma_i}{t_i^{2n+1}S'(u_i)^2}.
\quad}                                                       \tag{GJRS.29}
\]

Ordinary quadrature weight may vanish because

\[
\omega_i=x_i\rho_i\asymp y_0^{-1}\rho_i,
\]

while the absolute Padé residue remains nonzero. This is the precise topology missed by fixed
moments and weak arcsine recession.

## 7. Residue survival at a simple hard root

Take the selected Route-U sequence with

\[
n_j/a_j\longrightarrow\tau,
\qquad S_j\longrightarrow F
\]

locally uniformly. Let `r` be a simple real root of `F`, and choose the unique roots `u_j` of
`S_j` converging to `r`. Then

\[
t_j=\frac{y_j}{y_j+u_j},
\qquad
t_j^{2n_j+1}\longrightarrow1,                               \tag{GJRS.30}
\]

because `n_j=O(sqrt(y_j))` and `u_j` is bounded. Local uniform convergence gives

\[
S_j'(u_j)\longrightarrow F'(r)\ne0.                         \tag{GJRS.31}
\]

The divided hard-edge functions converge locally uniformly after continuous cancellation. Away
from a fixed compact interval, division supplies two additional powers of decay, so the same
completed-source form passage used for the parent hard-edge theorem gives

\[
\Gamma_j\longrightarrow
\gamma_r
=\mathfrak b_\sigma\!\left(\frac F{u-r},\frac F{u-r}\right)\ge0. \tag{GJRS.32}
\]

Therefore (GJRS.29)--(GJRS.32) prove

\[
\boxed{\quad
\rho_j\longrightarrow\frac{\gamma_r}{F'(r)^2}.
\quad}                                                       \tag{GJRS.33}
\]

If `r<0` and `gamma_r>0`, the canonical Padé resolvents have poles approaching the positive point
`Y=-r` with residues bounded below by a positive constant. Such a pole cannot be hidden by the
vanishing ordinary Christoffel weight.

## 8. Exact surviving source target

For the selected face define the positive-axis Padé-pole measure

\[
\mu_j^+=\sum_{u_{j,i}<0}\rho_{j,i}\,\delta_{-u_{j,i}}.       \tag{GJRS.34}
\]

For `Z=Y+i\varepsilon`, positivity of every residue gives

\[
-\Im R_j(Z)
=\sum_i\frac{\rho_{j,i}\varepsilon}
 {(Y+u_{j,i})^2+\varepsilon^2}.                             \tag{GJRS.35}
\]

Hence at a pole `Y=-u_(j,i)`,

\[
\varepsilon\bigl[-\Im R_j(Y+i\varepsilon)\bigr]
\ge\rho_{j,i}.                                              \tag{GJRS.36}
\]

For a simple negative root with positive terminal mass, any one of the following literal estimates
would now exclude it:

1. `mu_j^+(K) -> 0` for every compact interval `K` in `(0,infinity)`;
2. for some `epsilon_j -> 0`,
   `sup_(Y in K) epsilon_j[-Im R_j(Y+i epsilon_j)] -> 0` on every such `K`;
3. local boundedness of `R_j` on complex neighborhoods crossing the positive mass axis;
4. any source-derived estimate ruling out positive-axis Padé atoms with residue bounded below.

This target is narrower than full first-Hausdorff positivity and stronger than bulk moment
convergence. Unlike eventual pole absence, conditions 1--2 allow finite nodes with residues tending
to zero; they exclude exactly the hard-visible atoms certified by (GJRS.33). They retain the
literal Xi logarithmic derivative and the exact residue that survives hard scaling.

The zero-terminal-mass branch is separate. If `gamma_r=0`, (GJRS.33) permits residue collapse and
the parent parity-jet theorem instead creates an additional even and odd radical direction. A
complete Route-U closure must either prove terminal mass positivity or exploit that degeneracy.

## 9. Conjecture -> proof/failure -> pivot

1. **Conjecture:** shifted-Xi Gauss nodes move arbitrarily inside a positive chamber.
   **FALSIFIED.** Equation (GJRS.11) gives an exact strictly increasing hard coordinate.
2. **Conjecture:** first Padé-contact sign pushes every node to the correct side of the endpoint.
   **FALSIFIED.** It gives the coherent jet (GJRS.19)--(GJRS.21), but does not anchor `u_i(y_0)`.
3. **Conjecture:** a vanishing Christoffel weight makes a negative hard root invisible to every
   finite source observable. **FALSIFIED WHEN `gamma_r>0`.** The absolute Padé residue converges to
   `gamma_r/F'(r)^2`.
4. **Conjecture:** analyticity of the literal Xi resolvent immediately excludes the positive Padé
   pole. **FAILED AS AN INFERENCE.** Moving-order Padé approximants need not be locally bounded
   merely because their target is analytic.
5. **Pivot:** prove positive-axis local boundedness of the canonical selected Padé resolvents, or
   prove terminal-mass collapse and use the resulting parity-doubled radical.

## 10. Higher universal principle

Padé defect and hard-root motion are the same object in two coordinate systems:

\[
\text{first unseen moment defect}
\longleftrightarrow
\text{first non-Möbius Gauss-node jet}
\longleftrightarrow
\text{first nonzero hard-coordinate derivative}.
\]

Terminal divided-jet mass supplies the complementary absolute observable:

\[
\text{hard terminal mass}
\longleftrightarrow
\text{positive Padé-pole residue}.
\]

The previous obstacles are shadows of a derivative/level separation. Contact laws control how a
root leaves its Möbius orbit; they do not say where that orbit sits. Bulk limits discard the node's
weight; hard-resolvent residue restores exactly the missing absolute scale.

## 11. Corpus and Lean audit

The corpus already contains:

- the shifted-Xi moment ODE and finite atomic Möbius first jet;
- positive flat quadrature and Padé-defect contact parity;
- second-kind ratios for finite Gauss Cauchy transforms;
- hard-edge polynomial compactification and divided root-jet mass.

Targeted searches found no theorem resolving individual Gauss-node velocity as (GJRS.10), no
all-order coherent hard-coordinate contact jet (GJRS.19)--(GJRS.21), and no identity transporting
hard terminal mass to the absolute Padé residue (GJRS.29)--(GJRS.33). External priority remains
unverified.

No Lean declaration is claimed. Formalizing the confluent-Vandermonde mechanics without the
positive-axis Padé bound would certify a generic implication but would not close literal Route U.
Lean work begins only when the selected completed-Xi local-boundedness theorem, terminal-mass
alternative, or another unconditional source closure is proved.
