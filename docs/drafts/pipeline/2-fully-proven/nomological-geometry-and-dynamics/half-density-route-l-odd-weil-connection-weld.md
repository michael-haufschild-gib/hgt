# Half-density Route-L / odd-Weil connection weld

- **ID:** `ngd-half-density-route-l-odd-weil-connection-weld`
- **Stage:** 2 — fully proved on paper
- **Status:** `[PAPER-PROVED] [COEFFICIENT-CHANGING THEOREM] [NOT RH]`
  `[NO LEAN WRITTEN]`
- **Purpose:** prove that the Route-L Euler connection and the reflection-odd Weil/Stokes
  distribution are two exact coefficient realizations of one arithmetic current; identify the
  normal derivative and close the false completion-cofiber mechanism.

## 1. Setup

Let

\[
 (U_n f)(x)=f(nx),\qquad
 (\mathcal Lf)(t)=e^{t/2}f(e^t),\qquad
 (T_hg)(t)=g(t+h).
\]

On a compactly supported smooth core on `R_{>0}` define

\[
 A_a^+=\sum_{n\ge2}\Lambda(n)n^{-a}U_n,
 \qquad
 A_a^-=\sum_{n\ge2}\Lambda(n)n^{-a-1}U_{1/n},
 \qquad
 \kappa_a=A_a^- - A_a^+ .
\tag{1}
\]

For `b in R` put

\[
 D_b=\sum_{n\ge2}\Lambda(n)n^{-b}
       (\delta_{\log n}-\delta_{-\log n}).
\tag{2}
\]

This is locally finite, hence a distribution in `D'(R)`, for every `b`.  Write
`C_Dg=D*g` with the convention `(\delta_y*g)(t)=g(t-y)`.

## 2. Exact coefficient-changing identity

### Theorem 2.1 — half-density weld

On `C_c^infty(R)`, equivalently on its inverse image under `L`,

\[
 \boxed{\mathcal L\kappa_a\mathcal L^{-1}=C_{D_{a+1/2}}.}
\tag{3}
\]

#### Proof

For `g in C_c^infty(R)`, direct substitution gives

\[
 \mathcal L U_n\mathcal L^{-1}g
   =n^{-1/2}T_{\log n}g,
 \qquad
 \mathcal L U_{1/n}\mathcal L^{-1}g
   =n^{1/2}T_{-\log n}g.
\]

Therefore

\[
 \mathcal L A_a^+\mathcal L^{-1}
   =\sum_{n\ge2}\Lambda(n)n^{-a-1/2}T_{\log n},
\]

and

\[
 \mathcal L A_a^-\mathcal L^{-1}
   =\sum_{n\ge2}\Lambda(n)n^{-a-1/2}T_{-\log n}.
\]

By the convolution convention, `\delta_{\log n}` acts as `T_{-\log n}` and
`\delta_{-\log n}` as `T_{\log n}`. Subtraction proves `(3)`. For fixed compact support only
finitely many translated atoms meet a fixed compact test region, so every displayed sum is
well-defined in `D'(R)`. ∎

### Corollary 2.2 — odd normal derivative

The map `a -> D_{a+1/2}` is weakly entire in `D'(R)`, and

\[
 \left.\partial_a\right|_{a=0}
   \mathcal L\kappa_a\mathcal L^{-1}
 = C_{XK_{\rm pr}},
\tag{4}
\]

where

\[
 XK_{\rm pr}
 =-\sum_{n\ge2}\Lambda(n)(\log n)n^{-1/2}
     (\delta_{\log n}-\delta_{-\log n}).
\tag{5}
\]

In particular, the coefficient at a prime `p` is

\[
 -\frac{(\log p)^2}{\sqrt p},
\tag{6}
\]

the reflection-odd prime position/torque coefficient appearing in the Weil and Stokes charts.

#### Proof

Against a compactly supported test function the sum `(2)` is locally finite, so it may be
differentiated termwise. Since

\[
 \partial_a n^{-a-1/2}=-(\log n)n^{-a-1/2},
\]

evaluation at `a=0` gives `(5)`. For prime `p`, `Lambda(p)=log p`, giving `(6)`. ∎

## 3. Boundary-connection law

Let `b_Gamma(F,G)=F-G` be the Euler--Gamma boundary map from the established Route-L complex and
let `pi_-(F,G)=G` project to its second, physical Euler leg. Write

\[
 \nabla^-_a=\partial_a-A_a^-,\qquad
 \nabla_a^{\rm diag}=\partial_a-(A_a^-\oplus A_a^+).
\]

### Theorem 3.1 — exact connection transgression

On the common algebraic core,

\[
 \boxed{
 \nabla^-_a b_\Gamma-b_\Gamma\nabla_a^{\rm diag}
 =\kappa_a\pi_- .}
\tag{7}
\]

#### Proof

Thus

\[
 \begin{aligned}
 \nabla^-_a b_\Gamma(F,G)
 &=(\partial_a-A_a^-)(F-G),\\
 b_\Gamma\nabla_a^{\rm diag}(F,G)
 &=(\partial_a-A_a^-)F-(\partial_a-A_a^+)G.
 \end{aligned}
\]

Their difference is `(A_a^--A_a^+)G=kappa_a pi_-(F,G)`, proving `(7)`. Restricting to the
horizontal lift `(F,G)=D_a u` gives the established Green--Stokes identity. ∎

### Corollary 3.2

The operator-valued Route-L connection defect, the odd atomic Weil current, and the
Green--Stokes boundary defect are not three fitted analogies. They are respectively the operator,
distributional, and boundary-transgression realizations of the same coefficient family
`kappa_a`.

## 4. Completion-cofiber no-go

### Theorem 4.1 — completion does not create this defect

The atomic comparison

\[
 X\iota_+(\Theta_a)=\iota_-(\delta\Theta_a)
\tag{8}
\]

and the conjugacy `(3)` remain exact identities in `D'(R)` through `a=0`. Consequently their
mapping cofibres are zero in any stable coefficient category faithfully realizing these
identities. The nonzero current `kappa_a` already exists away from the endpoint; strict
completion does not create it.

If the coefficient category is restricted to tempered distributions, the comparison cell is
absent below the admission threshold proved in the companion card. Absence of a morphism is not a
noninvertible morphism and has no canonical cofiber.

#### Proof

Equation `(8)` is coefficientwise. Theorem 2.1 proves `(3)` as an equality of distributional
operators for every `a`. The cofiber of an isomorphism is zero. Restricting the codomain can make
an object or morphism undefined, but cannot turn an undefined cell into a canonical nonzero
cofiber. ∎

## 5. Anexact-geometric consequence

The correct carrier is a **relative admission class**. If `S` is a strict/tempered complex inside
a larger distributional complex `R`, then a primitive may exist in `R` while its differential is
admitted in `S`. The exact carrier is

\[
 \mathcal E^1(R,S)
 =\frac{dR^0\cap S^1}{dS^0}.
\tag{9}
\]

For Route L the desired arithmetic realization has `d b_Gamma=kappa_a pi_-` in the large
coefficient system while `b_Gamma` is not an admitted strict primitive at the horizon. Gamma
endpoint transgression, the odd comb, and the source Cartier/Bockstein class should be realizations
of `(9)`. This last identification remains conjectural; Theorems 2.1--4.1 do not imply RH.

## 6. Hostile loop ledger

1. **Completion creates odd current.** Failed by Theorem 4.1.
2. **Coefficient change is only metaphor.** Failed: `(3)` is an exact conjugacy.
3. **Odd current is fitted after seeing Xi.** Failed: `(2)` uses only `Lambda`, dilation, and
   half-density normalization; no Xi zero appears.
4. **Tangent coefficient differs from Stokes coefficient.** Failed by `(6)`.
5. **The current is automatically tempered at the critical endpoint.** False; companion card
   proves a sharp admission wall.
6. **Relative admission class selects RH.** Not proved. It supplies the correct type for the live
   source-normal lift problem, not its vanishing.

## 7. Formalization notes

No Lean was written or built. Later formalization can reuse the existing Dirichlet current,
Route-L connection, prime-position torque, and PNT estimate files. First formal targets should be
finite truncations of `(3)` and `(4)`; topology/admission should remain a separate theorem.
