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

Put

\[
 E=C_c^\infty(\mathbb R_{>0}),\quad \bar E=C^\infty(\mathbb R_{>0}),\quad
 H=C_c^\infty(\mathbb R),\quad \bar H=C^\infty(\mathbb R).
\]

For `a in C`, define the locally finite operators `A_a^\pm:E->bar E` by

\[
 A_a^+=\sum_{n\ge2}\Lambda(n)n^{-a}U_n,
 \qquad
 A_a^-=\sum_{n\ge2}\Lambda(n)n^{-a-1}U_{1/n},
 \qquad
 \kappa_a=A_a^- - A_a^+ .
\tag{1}
\]

For `b in C` put, with `n^(-b)=exp(-b log n)`,

\[
 D_b=\sum_{n\ge2}\Lambda(n)n^{-b}
       (\delta_{\log n}-\delta_{-\log n}).
\tag{2}
\]

This is locally finite, hence a distribution in `D'(R)`, for every `b`. Write
`C_D:H->bar H`, `C_Dg=D*g`, with the convention `(\delta_y*g)(t)=g(t-y)`.

## 2. Exact coefficient-changing identity

### Theorem 2.1 — half-density weld

As an equality in `Hom(H,bar H)`,

\[
 \boxed{\mathcal L_1\kappa_a\mathcal L_0^{-1}=C_{D_{a+1/2}}.}
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
finitely many translated atoms meet a fixed compact output region, so every displayed operator is
well-defined. The infinite sums need not preserve compact support; this is why the codomains are
`bar E` and `bar H`. ∎

### Corollary 2.2 — odd normal derivative

The map `a -> D_{a+1/2}` is weakly entire in `D'(R)`, and

\[
 \left.\partial_a\right|_{a=0}
   \mathcal L_1\kappa_a\mathcal L_0^{-1}
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

the coefficient in the imported reflection-odd prime position/torque current. The normalization
and sign comparison are those of
`critical-euler-mass-weil-stokes-shadow-law.md`, Sections 3--4, and
`suzuki-weil-position-torque-recurrence.md`, equations (9)--(10).

#### Proof

Against a compactly supported test function the sum `(2)` is locally finite, so it may be
differentiated termwise. Since

\[
 \partial_a n^{-a-1/2}=-(\log n)n^{-a-1/2},
\]

evaluation at `a=0` gives `(5)`. For prime `p`, `Lambda(p)=log p`, giving `(6)`. ∎

## 3. Boundary-connection law

Let `b_Gamma(F,G)=F-G` denote both continuous difference maps `E^2->E` and
`bar E^2->bar E`, and let `pi_-(F,G)=G`. For `C^1` paths `(F_a,G_a)` in `E^2`, write the following
operators with values in `bar E` and `bar E^2`:

\[
 \nabla^-_a=\partial_a-A_a^-,\qquad
 \nabla_a^{\rm diag}=\partial_a-(A_a^-\oplus A_a^+).
\]

### Theorem 3.1 — exact connection transgression

For every such `C^1` path,

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

Their difference is `(A_a^--A_a^+)G=kappa_a pi_-(F,G)`, proving `(7)`. For real `a>0`, the
imported Deninger theorem proves the same algebraic identity on its strict Route-L moment/
distribution domain and applies it to the horizontal lift `D_a u`; see
`deninger-euler-gamma-mobius-connection-transgression.md`, equations (9)--(10). ∎

### Corollary 3.2

The Route-L dilation defect and odd convolution kernel are two coefficient realizations of the
same family `kappa_a`. Green--Stokes is its covariant boundary transgression after applying
`kappa_a pi_-` to the horizontal two-collar section; it is not a third literal realization.

## 4. Completion-cofiber no-go

### Theorem 4.1 — log-coordinate arrow equivalence has zero cofiber

Let `L_0:E->H` and `L_1:bar E->bar H` be the half-density isomorphisms. Theorem 2.1 is the
commutative square

\[
\begin{CD}
 E @>{\kappa_a}>> \bar E\\
 @V{\mathcal L_0}VV @VV{\mathcal L_1}V\\
 H @>{C_{D_{a+1/2}}}>> \bar H.
\end{CD}
\tag{8}
\]

Thus `(L_0,L_1)` is an equivalence from the arrow `kappa_a` to the arrow
`C_(D_(a+1/2))` in the arrow category. Any stable realization sends this arrow-category
equivalence to an equivalence, whose cofiber is zero. The nonzero arrow `kappa_a` already exists
away from the endpoint; strict completion does not create it.

If a coefficient category requires convolution kernels to lie in `S'`, the kernel object is absent
below the admission threshold proved in the companion card. The core operator
`C_(D_b):H->bar H` still exists; it is the tempered-kernel realization that is unavailable.
Absence of a morphism is not noninvertibility and has no canonical cofiber.

#### Proof

The vertical maps are isomorphisms and commutativity is exactly Theorem 2.1. Hence they define an
equivalence in the arrow category. Stable functors preserve equivalences, and the cofiber of an
equivalence is zero. The final admission statement follows from the companion threshold theorem.
∎

## 5. Anexact-geometric consequence

A possible successor carrier is a **relative admission class**. Suppose complexes `S subset R`
are constructed and one proves `b_Gamma in R^0 setminus S^0` while
`d b_Gamma in S^1`. Then it defines

\[
 \mathcal E^1(R,S)
 =\frac{dR^0\cap S^1}{dS^0}.
\tag{9}
\]

The connection identity proves the formal differential
`d b_Gamma=kappa_a pi_-` on the common core, but it does **not** prove the nonadmission premise.
Constructing `S subset R`, proving that premise, and comparing Gamma endpoint, odd comb, and source
Cartier/Bockstein remain conjectural. Theorems 2.1--4.1 do not imply RH.

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
