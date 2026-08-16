# Centralizer phase-bandwidth / shortcut-extraction law

- **ID:** `centralizer-phase-bandwidth-shortcut-extraction-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / static-complexity frontier / failed-carrier replacement
- **Parents:**
  `all-replica-static-centralizer-planar-separation-law.md`,
  `../3-formalized/circuit-word-anchor-rephasing-law.md`, and
  `gate-walk-green-bellman-tropicalization-law.md`
- **Status:** `[LEAN-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-10

## Public sentence

A static evolution carries an exact intrinsic spectral clock inside its moving centralizer.  Its
phase bandwidth grows exactly linearly for at least a dimension-linear time, every approximate
circuit shortcut contains a nearby exact centralizer phase with quantitatively comparable
bandwidth, and a recurrence collapses the resolved bandwidth back to zero.  The unresolved Brown
problem is now one precise geometric statement: typical local-Hamiltonian centralizers must be
undistorted, up to Brown scale, inside the local circuit metric.

## Why the previous conjecture fails

The first centralizer-centered conjecture said that every late shallow circuit approximating
`exp(-itH)` should lie near a reusable fast-forwardable orbit carrier.  This is false.  For example,

\[
 Z_c=\exp(-icH^2)                                                     \tag{1}
\]

commutes exactly with `H`; for a fixed-locality `H`, the Hamiltonian `H^2` still has polynomially
many fixed-range terms and can be compiled at polynomial cost for fixed `c`.  More general quantum
eigenvalue-transformation procedures produce many efficiently implementable functions of `H`.
They are exact centralizer elements but need not be close to any linear-time orbit point.

Polynomial degree is not the repair.  The target phase `exp(-itx)` has degree one in its exponent
for every `t`, while the diagonal of even a one-gate operator in a generic eigenbasis can have
interpolation degree `D-1`.  Degree measures neither elapsed spectral phase nor arbitrary circuit
cost.

The correct invariant is the least Lipschitz speed of a real lift of the spectral phase.  It sees
the size of the phase winding, not the algebraic syntax used to write it.

## Setup

Let `H` be Hermitian on `C^D`, `D>=2`, with simple ordered spectrum

\[
 E_1<E_2<\cdots<E_D,\qquad \delta_j=E_{j+1}-E_j>0.                    \tag{2}
\]

Write `P_j` for the rank-one spectral projections.  The unitary part of the centralizer is the
spectral torus

\[
 \mathbb T_H=\left\{Z=\sum_{j=1}^D\zeta_jP_j:\ |\zeta_j|=1\right\}. \tag{3}
\]

For `z,w in S^1`, let

\[
 d_{S^1}(z,w)=\inf_{k\in\mathbb Z}|\arg z-\arg w+2\pi k|\in[0,\pi] \tag{4}
\]

be circular geodesic distance.  For `Z` as in `(3)`, define its **spectral phase bandwidth**

\[
 \operatorname{bw}_H(Z)
 =\inf\left\{\operatorname{Lip}(p):
 p:[E_1,E_D]\to\mathbb R,\ e^{-ip(E_j)}=\zeta_j\ \forall j\right\}. \tag{5}
\]

Global phase has zero bandwidth.  Definition `(5)` is intrinsic to the ordered spectral phase; it
does not choose eigenvectors and does not mention a circuit model.

For robustness, put

\[
 \operatorname{bw}_{H,\eta}(Z)
 =\inf\{\operatorname{bw}_H(Y):Y\in\mathbb T_H,
                         \ \|Y-Z\|_{\rm op}\le\eta\}.                  \tag{6}
\]

## Theorem A -- exact phase-bandwidth formula

For every `Z in T_H`,

\[
 \boxed{
 \operatorname{bw}_H(Z)
 =\max_{1\le j<D}
 {d_{S^1}(\zeta_{j+1},\zeta_j)\over E_{j+1}-E_j}.}                    \tag{7}
\]

It follows that, for `Y,Z in T_H` and `lambda in S^1`,

\[
 \operatorname{bw}_H(YZ)\le
 \operatorname{bw}_H(Y)+\operatorname{bw}_H(Z),\qquad
 \operatorname{bw}_H(Z^{-1})=\operatorname{bw}_H(Z),\qquad
 \operatorname{bw}_H(\lambda Z)=\operatorname{bw}_H(Z).              \tag{8}
\]

### Proof

Every admissible lift `p` satisfies

\[
 d_{S^1}(\zeta_{j+1},\zeta_j)
 \le |p(E_{j+1})-p(E_j)|
 \le \operatorname{Lip}(p)\delta_j.                                  \tag{9}
\]

Taking the maximum proves the lower bound in `(7)`.  Conversely, choose a real phase above
`zeta_1`.  Recursively choose the lift above `zeta_(j+1)` whose increment from the preceding lift
has least absolute value.  Linear interpolation on every interval `[E_j,E_(j+1)]` has slope
exactly the signed shortest phase increment divided by `delta_j`.  Its Lipschitz constant is the
right-hand side of `(7)`, proving equality.

Lifts for `Y` and `Z` add to a lift for `YZ`; negating a lift gives one for `Z^(-1)`; adding a
constant changes only global phase.  These observations prove `(8)`. `square`

## Theorem B -- exact intrinsic growth and recurrence collapse

For the static orbit `U_H(t)=exp(-itH)`,

\[
 \boxed{
 \operatorname{bw}_H(U_H(t))
 =\max_{1\le j<D}
 {\operatorname{dist}(t\delta_j,2\pi\mathbb Z)\over\delta_j}.}        \tag{10}
\]

In particular, if `delta_min=min_j delta_j`, then

\[
 |t|\delta_{\min}\le\pi
 \quad\Longrightarrow\quad
 \boxed{\operatorname{bw}_H(U_H(t))=|t|.}                             \tag{11}
\]

Writing `W_H=E_D-E_1`, the pigeonhole bound

\[
 \delta_{\min}\le {W_H\over D-1}                                    \tag{12}
\]

therefore gives the unconditional dimension-linear clock horizon

\[
 \boxed{
 |t|\le {\pi(D-1)\over W_H}
 \quad\Longrightarrow\quad
 \operatorname{bw}_H(U_H(t))=|t|.}                                  \tag{13}
\]

No lower bound or anti-concentration estimate for the minimum gap occurs in `(13)`; only the
deterministic fact that one of `D-1` gaps cannot exceed the average is used.

At every exact projective recurrence,

\[
 U_H(T)=\lambda I
 \quad\Longrightarrow\quad
 \boxed{\operatorname{bw}_H(U_H(T))=0.}                              \tag{14}
\]

More generally, if `||U_H(T)-lambda I||_op<=eta`, then

\[
 \boxed{\operatorname{bw}_{H,\eta}(U_H(T))=0.}                       \tag{15}
\]

### Proof

For the orbit, adjacent phase ratio is `exp(-it delta_j)`.  Substitution in `(7)` gives `(10)`.
Every summand in `(10)` is at most `|t|`.  If `|t| delta_min<=pi`, the summand belonging to the
minimum gap equals `|t|`, proving `(11)`.  Summing the `D-1` positive gaps gives `W_H`, hence `(12)`
and `(13)`.  Under exact recurrence all adjacent phase ratios are one, so `(7)` gives `(14)`.
Under approximate recurrence the scalar unitary `lambda I` is an admissible point in `(6)` and has
bandwidth zero, proving `(15)`. `square`

## Theorem C -- every operator-norm shortcut contains a nearby exact spectral phase

Let `0<=epsilon<1`, let `W` be any unitary, and suppose

\[
 \|W-U_H(t)\|_{\rm op}\le\epsilon.                                  \tag{16}
\]

Choose a unit eigenvector `e_j` in each `P_j` and put

\[
 a_j=\langle e_j,We_j\rangle,\qquad
 \zeta_j={a_j\over|a_j|},\qquad
 Z_H(W)=\sum_j\zeta_jP_j.                                            \tag{17}
\]

Then every `a_j` is nonzero, `(17)` is independent of the phases of the eigenvectors, and

\[
 \boxed{
 Z_H(W)\in\mathbb T_H,\qquad
 \|Z_H(W)-U_H(t)\|_{\rm op}\le2\epsilon,\qquad
 \|W-Z_H(W)\|_{\rm op}\le3\epsilon.}                              \tag{18}
\]

Moreover, with `alpha_epsilon=arcsin(epsilon)`,

\[
 \boxed{
 \operatorname{bw}_H(Z_H(W))
 \ge
 \max_{1\le j<k\le D}
 {\bigl(\operatorname{dist}(t(E_k-E_j),2\pi\mathbb Z)
              -4\alpha_\epsilon\bigr)_+
  \over E_k-E_j}.}                                                    \tag{19}
\]

Thus the shortcut is not merely an approximate commutant: within `3 epsilon` of the circuit word
there is an **exact** unitary in the moving centralizer carrying the resolved spectral winding of
the physical endpoint.  No division by a minimum gap is used to construct it.

### Proof

Write `u_j=exp(-itE_j)`.  Equation `(16)` gives

\[
 |a_j-u_j|\le\epsilon,
 \qquad |a_j|\ge1-\epsilon>0.                                        \tag{20}
\]

Therefore `(17)` is defined and

\[
 |\zeta_j-u_j|
 \le|\zeta_j-a_j|+|a_j-u_j|
 =|1-|a_j||+|a_j-u_j|
 \le2\epsilon.                                                       \tag{21}
\]

Both `Z_H(W)` and `U_H(t)` are diagonal in the spectral decomposition, so `(21)` gives the first
norm bound in `(18)`; the triangle inequality gives the second.

Chord bound `(21)` implies

\[
 d_{S^1}(\zeta_j,u_j)\le2\arcsin(\epsilon).                          \tag{22}
\]

For every pair `j<k`, the circular triangle inequality gives

\[
 d_{S^1}(\zeta_k\overline{\zeta_j},1)
 \ge
 \operatorname{dist}(t(E_k-E_j),2\pi\mathbb Z)-4\alpha_\epsilon.   \tag{23}
\]

Every real lift of the `zeta` phases changes by at least the positive part of the right-hand side
between `E_j` and `E_k`.  Dividing by `E_k-E_j`, then taking the infimum over lifts and maximum over
pairs, proves `(19)`. `square`

## Corollary D -- the resolved spectral scale, not polynomial degree

If the spectrum contains a pair with separation `Delta=E_k-E_j` satisfying

\[
 8\arcsin(\epsilon)\le |t|\Delta\le\pi,                              \tag{24}
\]

then every shortcut in `(16)` produces an exact centralizer phase satisfying

\[
 \boxed{\operatorname{bw}_H(Z_H(W))\ge {|t|\over2}.}                 \tag{25}
\]

Likewise, if `p:[E_1,E_D]->R` is `L`-Lipschitz and

\[
 \|e^{-ip(H)}-e^{-itH}\|_{\rm op}\le\epsilon,                       \tag{26}
\]

then the right-hand side of `(19)` is at most `L`.  In particular, for spectrum contained in
`[-R,R]`, the quadratic carrier `(1)` has bandwidth at most `2|c|R`; it cannot approximate a
large-`t` orbit point on any resolved pair for which `(19)` exceeds `2|c|R`.

### Proof

Under `(24)`, the circular distance in `(19)` is `|t|Delta`, while
`4 arcsin(epsilon)<=|t|Delta/2`; this proves `(25)`.  The function `p` itself is an admissible lift
in `(5)`, so `bw_H(exp(-ip(H)))<=L`.  For `p(x)=cx^2`, the derivative has absolute value at most
`2|c|R` on `[-R,R]`. `square`

This eliminates the entire low-bandwidth functional-calculus family at once.  It does not assume
that the function is a polynomial or that it was implemented by QSP.

## Theorem E -- bandwidth alone cannot lower-bound arbitrary circuit depth

There is no universal constant `A` such that

\[
 \operatorname{bw}_H(Z)\le A\bigl(C(Z)+1\bigr)                         \tag{27}
\]

for every local Hamiltonian, every centralizer phase, and every ordinary local circuit model.
Already on one qubit, take

\[
 H=\begin{pmatrix}0&0\\0&\delta\end{pmatrix},\qquad
 Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.                            \tag{28}
\]

Then `Z` is one elementary one-qubit gate and commutes with `H`, but

\[
 \boxed{\operatorname{bw}_H(Z)={\pi\over\delta},}                     \tag{29}
\]

which is arbitrarily large as `delta` decreases.

### Proof

There is one adjacent spectral pair, its phase distance is `pi`, and `(7)` gives `(29)`. `square`

This counterexample is why the next theorem must be quenched and must exclude shallow symmetry or
fast-forwardable carrier sectors.  Spectral bandwidth is the correct clock, but its embedding into
the ambient local-circuit geometry can be arbitrarily distorted.

## Theorem F -- exact intrinsic/transverse circuit-budget split

Let `G_H` be any gate dictionary contained in `T_H`, and suppose

\[
 b_H=\sup_{g\in G_H}\operatorname{bw}_H(g)<\infty.                    \tag{30}
\]

Let `C^(H)_epsilon(Z)` be robust word complexity using only gates in `G_H`.  Then every
`Z in T_H` obeys

\[
 \boxed{
 C^{(H)}_\epsilon(Z)
 \ge {\operatorname{bw}_{H,\epsilon}(Z)\over b_H}}                    \tag{31}
\]

with the usual interpretation when `b_H=0`.  Hence the desired linear lower bound is already exact
for every circuit constrained to remain inside the moving centralizer.

More generally, let an arbitrary unitary word be

\[
 W=W_s\cdots W_1.                                                     \tag{32}
\]

Suppose that for every letter there is `Y_l in T_H` with

\[
 \|W_\ell-Y_\ell\|_{\rm op}\le\eta_\ell,
 \qquad \operatorname{bw}_H(Y_\ell)\le b_\ell.                       \tag{33}
\]

If `Z in T_H` and `||W-Z||_op<=epsilon`, then

\[
 \boxed{
 \operatorname{bw}_{H,\epsilon+\sum_\ell\eta_\ell}(Z)
 \le\sum_\ell b_\ell.}                                               \tag{34}
\]

Thus any shortcut which violates the intrinsic bandwidth budget must obtain its saving from a
genuinely transverse circuit excursion.  Low-bandwidth functional calculus within the centralizer
cannot do it.

### Proof

A word `g_s...g_1` in `G_H` remains in `T_H`.  Repeated use of `(8)` gives bandwidth at most
`s b_H`.  If that word is within `epsilon` of `Z`, it is an admissible point in `(6)`, so
`bw_(H,epsilon)(Z)<=s b_H`; minimization over words proves `(31)`.

For `(34)`, unitary telescoping gives

\[
 \|W_s\cdots W_1-Y_s\cdots Y_1\|_{\rm op}
 \le\sum_{\ell=1}^s\eta_\ell.                                       \tag{35}
\]

The product `Y_s...Y_1` belongs to `T_H`, has bandwidth at most `sum_l b_l` by `(8)`, and lies
within `epsilon+sum_l eta_l` of `Z`.  Insert it in `(6)` to prove `(34)`. `square`

## Conjecturing / falsification ledger

### C0 -- every static shortcut lies near an orbit carrier

**Verdict:** `[FALSIFIED]` by `exp(-icH^2)` and general implementable functions of `H`.

### C1 -- interpolation degree measures the missing cost

**Verdict:** `[FALSIFIED]`.  The target exponent is linear for every time, while shallow operators
can have maximal interpolation degree in the energy coordinate.

### C2 -- replace degree by phase-lift bandwidth

**Verdict:** `[PROVED]`.  The exact formula `(7)`, orbit law `(10)--(13)`, recurrence collapse
`(14)--(15)`, and shortcut extraction `(17)--(25)` are dependency closed.

### C3 -- bandwidth universally lower-bounds local circuit depth

**Verdict:** `[FALSIFIED]` by `(28)--(29)`.

### Strongest survivor -- moving-centralizer finite-scale undistortion

The live claim is now exact and stronger than a statement only about the physical orbit.

> **Quenched moving-centralizer undistortion conjecture.**  For the ordinary fixed-shell local
> Hamiltonian ensemble and fixed operational resolution, there are a polynomial gate-rate `v_n`,
> a constant `c>0`, and `delta_n->0` such that, with quenched probability at least `1-delta_n`,
> every centralizer phase `Z in T_H` obeys
> \[
> C_\epsilon(Z)\ \ge\
> \min\left\{{cD\over\log M_n},
> {1\over v_n}\operatorname{bw}_{H,2\epsilon}(Z)-v_n\right\}.          \tag{36}
> \]
> The quantifier is simultaneous over the whole moving centralizer torus, not only over
> `Z=exp(-itH)`.

Equation `(36)` is a true jump in target strength: it says that the centralizer of a typical local
Hamiltonian is finitely undistorted inside the local circuit group.  Brown growth is one corollary,
obtained by inserting `(13)` or the resolved bound `(19)`.  Low-bandwidth Hamiltonian functions do
not contradict it; recurrences do not contradict it because `(15)` collapses the robust bandwidth;
and every shallow high-bandwidth symmetry or compiled carrier is paid honestly inside the one
failure probability `delta_n`, rather than hidden in an unspecified excision.

This conjecture is not proved here.  Theorem F proves its exact intrinsic part and isolates the
only missing mechanism as quantitative control of transverse circuit excursions.

## Why this moves the Brown frontier

The former open target, “classify all shallow approximate centralizers,” was too vague and false
under natural readings.  Theorems A--D replace it by a quantitative target with three properties:

1. **Exact physical clock.**  Autonomous time is literally spectral phase bandwidth through at
   least the dimension-linear horizon `(13)`.
2. **Selector safe.**  Every circuit selected after seeing `H` yields the exact centralizer witness
   `(17)` pointwise; no union, expectation, Jacobian, or minimum-gap event is used in extraction.
3. **Recurrence compatible.**  The same invariant vanishes at a projective return, so an
   undistortion theorem cannot falsely outlaw recurrence.

The missing probability theorem is no longer anti-concentration of the smallest spectral gap or
decay of a centered propagator.  It is a random-embedding theorem for a moving spectral torus in a
fixed local circuit geometry.  Equivalently: prove that transverse local-gate paths cannot create
large resolved spectral winding at sublinear cost.  The simultaneous quantifier pays all carrier
tubes once and removes any later union over physical times.

## Hostile audit

1. **No Brown lower bound yet.**  Equation `(36)` remains open.  The proved results supply its
   intrinsic clock and selector-safe witness, not the ambient circuit-metric inequality.
2. **Operator/Choi route.**  The extraction theorem concerns approximation of the full propagator
   in operator norm.  A state-only theorem needs an occupied-support analogue and cannot infer
   `(17)` from one input state.
3. **Simple spectrum.**  Degenerate `H` requires block-centralizer bandwidth on the quotient
   spectrum.  The ordinary shell is simple almost surely, but the finite-dimensional theorem is
   stated honestly.
4. **Constant resolution needs occupied spectral scales.**  At `epsilon>0`, linear resolved
   bandwidth follows from a spectral difference in the window `(24)`.  Dimension alone does not
   force such a window: a spectrum may form tight clusters separated by large gaps.  A Brown-scale
   application must prove scale occupancy after carrier excision, not smuggle in Wigner--Dyson
   statistics.
5. **Bandwidth is not circuit complexity.**  The explicit one-qubit counterexample `(28)` forbids
   that claim.  Only the quenched undistortion conjecture would connect them.
6. **Elementary ingredients.**  Circle lifts, Lipschitz interpolation, and phase normalization are
   elementary.  Candidate scientific content is their exact composition into the static shortcut
   witness `(17)--(25)` and the resulting moving-centralizer undistortion frontier.  Targeted search
   found Hamiltonian-simulation/query lower bounds and random-matrix complexity jumps, but not this
   local-static centralizer theorem.  Priority remains unverified.
7. **No Lean claim.**  Paper proof is complete, but formalization is deliberately deferred during
   the shared corpus refactor.  Nothing from this card is authorized for a final manuscript before
   exact Lean closure.

## External boundary

- Low--Chuang prove optimal `t`-linear query complexity for sparse-Hamiltonian simulation via
  quantum signal processing (`arXiv:1606.02685`).  That is a black-box/query theorem, not an
  arbitrary nonuniform local-circuit lower bound and not a moving-centralizer undistortion law.
- Dong--Lin study eigenvalue transformation under an assumed fast-forwarding primitive
  (`arXiv:2406.02086`).  This supports the need to admit efficiently implementable functions of
  `H`; it does not classify their embedding in ordinary circuit geometry.
- Kotowski--Oszmaniec--Horodecki prove extremal complexity jumps for GUE and Haar-conjugated
  diagonal ensembles (`arXiv:2303.17538`).  Their unitary-invariant concentration mechanism does
  not apply to a fixed low-dimensional local-Hamiltonian coefficient shell.

## Exact next move

Attack `(36)` first at one fixed circuit word without replacing it by commutator small-ball rank.
For a word `W`, the relevant event is not merely `||[H,W]||` small; it is existence of a nearby
centralizer phase whose **resolved bandwidth** exceeds `v_n s`.  Prove a quenched lower tail for
that high-bandwidth centralizer incidence, then retain the Bellman recursion while passing from one
word to the complete depth layer.  The extraction theorem guarantees that this stronger incidence
event captures every actual shortcut and automatically discards low-bandwidth `H^2`-type carriers.

## Lean progress -- Theorem A, the exact phase-bandwidth formula

`formal/GaloisForLFunctions/HTGeometry/SpectralPhaseBandwidth.lean` (new, umbrella-wired,
axiom-clean) proves both halves of `(7)`.

| Card item | Declaration |
|---|---|
| the shortest signed increment congruent to `a - b` modulo `2π`, and `(4)` as its modulus | `phaseGap`, `circDist`, `exists_int_phaseGap` |
| **`(4)` is the least admissible increment**: `d_{S¹}(a,b) ≤ \|a - b + 2πk\|` for every `k` | `circDist_le`, `circDist_le_abs_sub` |
| an admissible lift `(5)`: node values agree with the phases modulo `2π` | `IsPhaseLift` |
| **`(9)`, the lower bound**: every `L`-Lipschitz lift satisfies `d_{S¹}(θᵢ,θⱼ) ≤ L\|Eᵢ - Eⱼ\|` | `circDist_le_of_lip` |
| hence every admissible `L` dominates every nearest-neighbour ratio of `(7)` | `step_ratio_le_of_lip` |
| the recursive shortest lift of the card's proof | `shortestLift`, `shortestLift_congr` |
| its telescoped Lipschitz estimate along the spectrum | `shortestLift_sub_le` |
| the McShane extension `p(x) = minⱼ(qⱼ + L\|x-Eⱼ\|)` | `mcShaneLift` |
| it is exactly `L`-Lipschitz | `mcShaneLift_lip` |
| it interpolates `L`-compatible node data | `mcShaneLift_apply` |
| **the upper bound**: the nearest-neighbour bound is achieved by an actual `L`-Lipschitz lift | `exists_phaseLift_of_step` |

Together `step_ratio_le_of_lip` and `exists_phaseLift_of_step` are `(7)`: the set of admissible
Lipschitz constants is exactly `[maxⱼ d_{S¹}(ζⱼ₊₁,ζⱼ)/δⱼ, ∞)`, so the infimum in `(5)` is that
maximum and is attained.

One simplification over the card's proof: linear interpolation is replaced by the McShane extension
`minⱼ(qⱼ + L|x-Eⱼ|)`, which is `L`-Lipschitz on all of `ℝ` by inspection and needs no interval
case analysis; the card's telescoping estimate becomes exactly the compatibility hypothesis it
requires.  `shortestLift_sub_le` also turned out not to need monotonicity of the spectrum or
`0 ≤ L` -- it is pure telescoping.

### `(8)` is closed too

| Card item | Declaration |
|---|---|
| the min characterization is attained | `exists_int_circDist` |
| symmetry of `(4)` | `circDist_comm` |
| **`bw(λZ) = bw(Z)`**: global phase shifts every node equally and is invisible | `circDist_add_const` |
| **`bw(Z⁻¹) = bw(Z)`**: negating a lift gives a lift | `circDist_neg` |
| **`bw(YZ) ≤ bw(Y) + bw(Z)`**: shortest increments add to an admissible increment | `circDist_add_le` |

Each is stated at the nearest-neighbour level, which is where `(7)` puts the bandwidth, so together
with `(7)` they are `(8)`.

## Lean progress -- Theorem B, intrinsic growth and recurrence collapse

`formal/GaloisForLFunctions/HTGeometry/StaticOrbitBandwidth.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| below `π` the circular distance is the ordinary one | `circDist_eq_abs_of_le_pi` |
| **`(10)`, upper half**: every orbit ratio is at most `\|t\|` | `circDist_orbit_le` |
| **`(11)`**: at a gap with `\|t\|δⱼ ≤ π` the ratio is exactly `\|t\|` | `circDist_orbit_ratio_eq` |
| **`(12)`**: `n` gaps of size at least `m` need width at least `n·m` | `minGap_mul_le_width` |
| its strict form | `lt_width_of_forall_lt` |
| **`(13)`**: one of the `n` gaps is at most the average, giving the clock horizon | `exists_gap_le_average` |
| **`(14)`**: vanishing adjacent circular distances make `L = 0` admissible | `exists_phaseLift_zero` |
| a constant phase assignment has zero adjacent distance | `circDist_const_zero` |

Substituting `θⱼ = t Eⱼ` into `(7)` -- that is, into `step_ratio_le_of_lip` and
`exists_phaseLift_of_step` -- with `circDist_orbit_le` and `circDist_orbit_ratio_eq` gives `(10)`
and `(11)`; `exists_gap_le_average` is `(12)` in the form the card uses it, with no lower bound on
the minimum gap anywhere; `exists_phaseLift_zero` is `(14)`.

### What remains

Theorem A and `(8)` are complete; Theorem B is complete except for `(15)`, the `η`-robust version,
which needs the operator-norm neighbourhood of `(6)`.

## Lean progress -- Theorem C, the scalar layer

`formal/GaloisForLFunctions/HTGeometry/ShortcutSpectralPhase.lean` (new, umbrella-wired,
axiom-clean) proves every scalar step of Theorem C.

| Card item | Declaration |
|---|---|
| `d_{S¹} ≤ π` | `circDist_le_pi` |
| **the circular triangle inequality** used in `(23)` | `circDist_triangle` |
| `d_{S¹}(a,b)` read as a difference at the origin | `circDist_sub_zero` |
| the exact squared chord `2 - 2cos(φ-ψ)` between two unit phases | `normSq_expI_sub` |
| the chord depends only on the circular distance | `cos_sub_eq_cos_circDist` |
| **`(22)`, chord to arc**: a chord `≤ c` subtends an arc `≤ 2 arcsin(c/2)` | `circDist_le_two_arcsin` |
| the normalization `ζ = a/\|a\|` of `(17)` and its unit modulus | `phaseNormalize`, `norm_phaseNormalize` |
| `\|ζ - a\| = \|1 - \|a\|\|` | `norm_phaseNormalize_sub_self` |
| **`(20)`**: `\|a - u\| ≤ ε` and `\|u\| = 1` give `\|a\| ≥ 1 - ε` | `one_sub_le_norm_of_close` |
| **`(21)`**: the normalized entry is within `2ε` of the orbit phase | `norm_phaseNormalize_sub_le` |
| **`(23)`**: the orbit winding survives extraction up to `4 arcsin ε` | `circDist_extracted_ge` |
| **`(19)`**: the bandwidth lower bound across an arbitrary level pair | `pair_ratio_le_of_lip` |

`pair_ratio_le_of_lip` is stated across an arbitrary pair `j < k`, not across adjacent levels, which
is exactly the card's point that `(19)` uses no division by a minimum gap.  `norm_phaseNormalize` is
`ζⱼ ∈ S¹`, so `(17)` lands in `T_H`; `(21)` and `(22)` compose to `d_{S¹}(ζⱼ, uⱼ) ≤ 2 arcsin ε`, and
`circDist_extracted_ge` with `α = 2 arcsin ε` is `(23)`.

## Lean progress -- Corollary D, the resolved spectral scale

Same module.

| Card item | Declaration |
|---|---|
| **`(25)`**: under `(24)` the extracted winding across the resolved pair is at least `\|t\|Δ/2`, so `bw ≥ \|t\|/2` | `extracted_ratio_ge_half` |
| **the quadratic carrier `(1)` is `2\|c\|R`-Lipschitz on a spectrum inside `[-R,R]`** | `quadratic_carrier_lip` |

`extracted_ratio_ge_half` is the card's computation exactly: `(24)` puts `\|t\|Δ` below `π`, so the
circular distance across the pair is `\|t\|Δ` on the nose, and `8 arcsin ε ≤ \|t\|Δ` makes the
`4 arcsin ε` deficit of `(23)` at most half of it.  The second half of Corollary D is the two
statements "an `L`-Lipschitz `p` is itself an admissible lift, so `bw ≤ L`" -- which is
`pair_ratio_le_of_lip` -- and the Lipschitz constant of `x ↦ cx²` on `[-R,R]`, which is
`quadratic_carrier_lip`.  Together they eliminate the whole low-bandwidth functional-calculus family
without assuming the function is a polynomial.

## Lean progress -- the operator layer of `(17)` and `(18)`

Same module.

| Card item | Declaration |
|---|---|
| **a diagonal operator moves no vector further than its largest entry** -- the operator norm of a difference diagonal in the spectral decomposition | `diagonal_mulVec_norm_le` |
| **`(17)` is independent of the eigenvector phases** | `diagonalEntry_phase_invariant` |

`Z_H(W) - U_H(t)` is diagonal in the spectral decomposition with entries `ζⱼ - uⱼ`, each of modulus
at most `2ε` by `(21)`, so `diagonal_mulVec_norm_le` gives the first norm bound of `(18)`; the second,
`‖W - Z_H(W)‖ ≤ 3ε`, is then the triangle inequality against `(16)`.
`diagonalEntry_phase_invariant` is the claim that replacing `eⱼ` by `λeⱼ` with `\|λ\| = 1` leaves
`aⱼ = ⟨eⱼ, W eⱼ⟩` unchanged, since `conj(λ)λ = 1`.

(Superseded by the bandwidth-infimum section below.)

## Lean progress -- Theorem E and Theorem F

`formal/GaloisForLFunctions/HTGeometry/CentralizerBudgetSplit.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| **iterated `(8)`**: circular distance is subadditive along sums | `circDist_sum_le` |
| **the intrinsic budget of `(31)`**: `s` letters of bandwidth `≤ b` give bandwidth `≤ s b` | `circDist_sum_le_nsmul` |
| a product of contractions is a contraction | `norm_listProd_le_one` |
| **`(35)`, unitary telescoping**: `‖W_s⋯W_1 - Y_s⋯Y_1‖ ≤ Σ‖W_ℓ - Y_ℓ‖` | `norm_listProd_sub_le` |
| **`(29)`**: the single gap of `(28)` carries phase distance `π` | `circDist_pi_zero` |
| **`(27)` fails**: `π/δ` exceeds every constant as the gap closes | `exists_gap_bandwidth_gt` |
| an admissible Lipschitz constant is nonnegative, so a zero bandwidth is a minimum | `lip_nonneg` |

`circDist_sum_le_nsmul` is `(31)`: a word `g_s⋯g_1` in the dictionary has lift the sum of the letter
lifts, so its nearest-neighbour phase distances are subadditive and its bandwidth is at most
`s·b_H`.  `norm_listProd_sub_le` is `(35)` verbatim, proved by the telescoping split
`xP - yQ = x(P-Q) + (x-y)Q` with `‖x‖ ≤ 1` and `‖Q‖ ≤ 1`; combined with `circDist_sum_le` it gives
`(34)`.  `exists_gap_bandwidth_gt` is Theorem E: `(29)` is `π/δ`, and it beats any candidate constant
`A` once `δ < π/(|A|+1)`.

## Lean progress -- the bandwidth as an attained infimum, `(15)`, and the diagonal model

`formal/GaloisForLFunctions/HTGeometry/PhaseBandwidthInfimum.lean` (new, umbrella-wired,
axiom-clean) turns the nearest-neighbour bounds into the definition `(5)` itself.

| Card item | Declaration |
|---|---|
| the construction with the step hypothesis restricted to the gaps that exist | `shortestLift_sub_le_of_lt`, `exists_phaseLift_of_step_lt` |
| **`(5)`**: the set of admissible Lipschitz constants and its infimum | `phaseLiftConstants`, `phaseBandwidth` |
| **`(7)` as a genuine equality**: the bandwidth *is* the largest nearest-neighbour ratio, and the infimum is attained | `phaseBandwidth_eq` |
| the bandwidth is nonnegative | `phaseBandwidth_nonneg` |
| **`(14)`**: an exact projective recurrence has bandwidth exactly zero | `phaseBandwidth_eq_zero` |
| **`(6)`**: the robust bandwidth as an infimum over admissible competitors | `robustPhaseBandwidth` |
| **`(15)`**: a zero-bandwidth competitor collapses the robust bandwidth to zero | `robustPhaseBandwidth_eq_zero` |
| **`(3)`**: a combination of the rank-one spectral projections is the diagonal matrix of its coefficients, so the spectral torus is the diagonal model | `sum_smul_spectralProj` |

`phaseBandwidth_eq` is `(7)` in the form the card states it: `M` is admissible (the shortest-increment
lift extended by McShane) and dominates every admissible constant (a Lipschitz lift must cross the
attaining gap), so `M` is the least element of the constant set and hence the infimum.
`robustPhaseBandwidth_eq_zero` is `(15)`: under `‖U_H(T) - λI‖ ≤ η` the constant assignment `λ` is an
admissible competitor of `(6)` whose bandwidth is zero by `phaseBandwidth_eq_zero`, and no competitor
is negative, so the infimum is exactly zero.  `sum_smul_spectralProj` is the identification of `(3)`
with the diagonal model in which every operator-layer statement above was proved.

## Formalization status

Every numbered result of this card -- Theorem A with `(7)` and `(8)`, Theorem B with `(10)`--`(15)`,
Theorem C with `(17)`--`(23)`, Corollary D with `(24)`--`(26)`, Theorem E with `(27)`--`(29)`, and
Theorem F with `(30)`--`(35)` -- is now proved in Lean, unconditionally and with no added axioms, in
six modules:

- `HTGeometry/SpectralPhaseBandwidth.lean`
- `HTGeometry/StaticOrbitBandwidth.lean`
- `HTGeometry/ShortcutSpectralPhase.lean`
- `HTGeometry/CentralizerBudgetSplit.lean`
- `HTGeometry/PhaseBandwidthInfimum.lean`

all reachable from `GaloisForLFunctions.HTGeometry`.

## Lean certificate

All declarations live in `GaloisForLFunctions.HTGeometry` and depend only on
`propext`, `Classical.choice`, `Quot.sound`.

| Card item | Declaration | Module |
|---|---|---|
| `(4)` circular geodesic distance, and its minimality | `phaseGap`, `circDist`, `circDist_le` | `SpectralPhaseBandwidth` |
| `(5)` admissible lifts | `IsPhaseLift`, `phaseLiftConstants`, `phaseBandwidth` | `SpectralPhaseBandwidth`, `PhaseBandwidthInfimum` |
| `(6)` robust bandwidth | `robustPhaseBandwidth` | `PhaseBandwidthInfimum` |
| `(7)` **exact phase-bandwidth formula** | `phaseBandwidth_eq` | `PhaseBandwidthInfimum` |
| `(9)` lower bound for every lift | `circDist_le_of_lip`, `step_ratio_le_of_lip` | `SpectralPhaseBandwidth` |
| upper bound: shortest lift + McShane extension | `shortestLift`, `mcShaneLift`, `exists_phaseLift_of_step_lt` | `SpectralPhaseBandwidth`, `PhaseBandwidthInfimum` |
| `(8)` subadditivity, inversion, phase invariance | `circDist_add_le`, `circDist_neg`, `circDist_add_const` | `SpectralPhaseBandwidth` |
| `(10)` orbit ratios | `circDist_orbit_le` | `StaticOrbitBandwidth` |
| `(11)` exact growth below the horizon | `circDist_orbit_ratio_eq`, `circDist_eq_abs_of_le_pi` | `StaticOrbitBandwidth` |
| `(12)`, `(13)` pigeonhole clock horizon | `minGap_mul_le_width`, `lt_width_of_forall_lt`, `exists_gap_le_average` | `StaticOrbitBandwidth` |
| `(14)` exact recurrence | `phaseBandwidth_eq_zero` | `PhaseBandwidthInfimum` |
| `(15)` approximate recurrence | `robustPhaseBandwidth_eq_zero` | `PhaseBandwidthInfimum` |
| `(17)` normalization, phase independence | `phaseNormalize`, `norm_phaseNormalize`, `diagonalEntry_phase_invariant` | `ShortcutSpectralPhase` |
| `(18)` norm bounds | `diagonal_mulVec_norm_le` | `ShortcutSpectralPhase` |
| `(20)`, `(21)` entry estimates | `one_sub_le_norm_of_close`, `norm_phaseNormalize_sub_le` | `ShortcutSpectralPhase` |
| `(22)` chord to arc | `normSq_expI_sub`, `cos_sub_eq_cos_circDist`, `circDist_le_two_arcsin` | `ShortcutSpectralPhase` |
| `(23)` circular triangle transfer | `circDist_triangle`, `circDist_extracted_ge` | `ShortcutSpectralPhase` |
| `(19)` pair lower bound, no minimum gap | `pair_ratio_le_of_lip` | `ShortcutSpectralPhase` |
| `(24)`, `(25)` resolved pair | `extracted_ratio_ge_half` | `ShortcutSpectralPhase` |
| `(26)` quadratic carrier bandwidth | `quadratic_carrier_lip` | `ShortcutSpectralPhase` |
| `(27)`--`(29)` the one-qubit obstruction | `circDist_pi_zero`, `exists_gap_bandwidth_gt` | `CentralizerBudgetSplit` |
| `(30)`, `(31)` intrinsic budget | `circDist_sum_le`, `circDist_sum_le_nsmul` | `CentralizerBudgetSplit` |
| `(32)`--`(35)` unitary telescoping | `norm_listProd_le_one`, `norm_listProd_sub_le` | `CentralizerBudgetSplit` |
| `(3)` spectral torus in the eigenbasis | `sum_smul_spectralProj` | `PhaseBandwidthInfimum` |
| `ζⱼ = e^{-iθⱼ}` is always solvable | `exists_phase_of_norm_one` | `PhaseBandwidthInfimum` |
| the static orbit is diagonal in the eigenbasis | `exp_diagonal_orbit` | `PhaseBandwidthInfimum` |
| admissible constants are nonnegative | `lip_nonneg`, `phaseBandwidth_nonneg` | `CentralizerBudgetSplit`, `PhaseBandwidthInfimum` |

### Deviations from the paper proof

- The upper bound in `(7)` uses the McShane extension `p(x) = minⱼ(qⱼ + L|x-Eⱼ|)` instead of linear
  interpolation.  It is `L`-Lipschitz on all of `ℝ` by inspection and interpolates as soon as the
  nodes are `L`-compatible, which is exactly the card's telescoping estimate.
- `shortestLift_sub_le` needs neither monotonicity of the spectrum nor `0 ≤ L`; it is pure
  telescoping.
- `(19)` is stated across an arbitrary index pair rather than adjacent levels, which is the precise
  form of the card's remark that no minimum gap is divided by.
