# Rational CCM restriction has a continuous Real-Brauer lift

- **Status:** Fully proven on paper
- **Claim type:** THEOREM
- **Date:** 2026-07-25
- **Role:** Real descent through the exact CCM trace-class cyclic target

## Statement

Let
\[
  \mathcal A_{\mathbb Q}=\mathcal S(\mathcal G_{\mathbb Q})^\natural_0
  =\ker\varepsilon_0^\natural\cap\ker\varepsilon_1^\natural
\]
be the source cyclic module of Connes--Consani--Marcolli, and let
\[
  \mathcal B_{\mathbb Q}
  ={\bf S}^{\,\natural}
    (C_{\mathbb Q},\mathcal L^1(\mathcal H_b))
\]
be their strongly-Schwartz operator-valued target cyclic module. In the canonical rational
trivialization \(\mathcal H_b=\ell^2(\mathbb Q^\times)\), define
\[
  (J\xi)(q)=\operatorname{sgn}(q)\overline{\xi(-q)}.
  \tag{1}
\]
On a source monomial and a target operator field define
\[
\begin{aligned}
  \alpha_{\mathcal A}(f_kU_k)(x)
    &=\operatorname{sgn}(k)\overline{f_k(-x)}\,U_k,\\
  \alpha_{\mathcal B}(T)(b)
    &=-J\,T(b)\,J.
\end{aligned}
\tag{2}
\]

Then:

1. \(\alpha_{\mathcal A}\) extends to a continuous conjugate-linear unital algebra
   involution of \(\mathcal S(\mathcal G_{\mathbb Q})\);
2. it preserves \(\mathcal A_{\mathbb Q}\);
3. \(\alpha_{\mathcal B}\) is an isometric conjugate-linear algebra involution of the
   continuous trace-class operator field and preserves
   \(\mathcal B_{\mathbb Q}\) degreewise;
4. the CCM operator-valued restriction morphism is Real-equivariant:
   \[
     \rho^\natural\alpha_{\mathcal A}^\natural
       =\alpha_{\mathcal B}^\natural\rho^\natural;
     \tag{3}
   \]
5. the quotient by the closed range of \(\rho^\natural\) therefore inherits an even
   \(K_{\mathbb R}\)-structure;
6. all constructions commute with the rational \(C_{\mathbb Q}\)-action in the canonical
   positive-real section.

This theorem constructs the even Real operator object required as input to quaternionic Real
Morita parity shift. It does not yet identify the Morita intertwiner realization with CCM's
single complex cyclic realization.

Here “strongly-Schwartz operator-valued target” is shorthand only. Precisely, CCM Definition
4.9 defines \(\mathcal B_{\mathbb Q}\) as the cyclic submodule of continuous trace-class
operator fields for which
\[
  b\longmapsto\operatorname{Tr}(T_0(b)\cdots T_n(b))
\]
on the main cyclic diagonal belongs to
\({\bf S}(C_{\mathbb Q})=\bigcap_{\beta\in\mathbb R}
\mu^\beta\mathcal S(C_{\mathbb Q})\). It does **not** require the trace norm of the operator
field itself to be strongly Schwartz. This distinction is essential: the fixed-base
trace-class estimate is an absolute-value statement, whereas the rapid decay of the signed
diagonal trace uses \(\ker\varepsilon_0\cap\ker\varepsilon_1\) and Poisson summation.

## Proof

### 1. Source Schwartz continuity

The map \(x\mapsto-x\) is a continuous additive automorphism of the adele ring. Pullback along
it preserves the Bruhat--Schwartz space: at finite places it permutes locally constant
compactly supported functions, and at the archimedean place it preserves every Schwartz
seminorm. Complex conjugation also preserves those spaces and seminorms. Thus
\[
  Rf(x)=\overline{f(-x)}
\]
is a continuous conjugate-linear involution of
\(\mathcal S(\mathbb A_{\mathbb Q})\).

The sign character is multiplicative. The crossed-product multiplication is
\[
  (f_kU_k)(g_\ell U_\ell)
    =\bigl[x\mapsto f_k(x)g_\ell(k^{-1}x)\bigr]U_{k\ell}.
\]
Consequently
\[
  \alpha_{\mathcal A}((f_kU_k)(g_\ell U_\ell))
  =\alpha_{\mathcal A}(f_kU_k)\,
   \alpha_{\mathcal A}(g_\ell U_\ell).
\]
The finite-support direct-sum bornology makes the coefficientwise map continuous.
Multiplicativity, preservation of the unit, conjugate-linearity, and
\(\alpha_{\mathcal A}^2=1\) follow.

### 2. Vanishing cyclic submodule

Only the coefficient of \(U_1\) enters the two CCM traces. Since
\(\operatorname{sgn}(1)=1\),
\[
\begin{aligned}
 \varepsilon_0(\alpha_{\mathcal A}a)
   &=\overline{\varepsilon_0(a)},\\
 \varepsilon_1(\alpha_{\mathcal A}a)
   &=\int_{\mathbb A_{\mathbb Q}}\overline{f_1(-x)}\,dx
    =\overline{\int_{\mathbb A_{\mathbb Q}}f_1(x)\,dx}
    =\overline{\varepsilon_1(a)}.
\end{aligned}
\]
The middle equality uses invariance of additive Haar measure under \(x\mapsto-x\).
Because \(\alpha_{\mathcal A}\) is multiplicative, the same identity holds for
\(\varepsilon_j^\natural(a_0\otimes\cdots\otimes a_n)
=\varepsilon_j(a_0\cdots a_n)\). Both cyclic kernels and their intersection are stable.

### 3. Target trace-class completion

Formula (1) defines an antiunitary and \(J^2=-1\). Hence
\[
  \alpha_{\mathcal B}(T)=JTJ^{-1}=-JTJ
\]
is a conjugate-linear algebra involution. Left and right composition by an antiunitary
preserve singular values, so
\[
  \|\alpha_{\mathcal B}(T)\|_1=\|T\|_1.
\]
It therefore preserves trace-class operators and continuity of their field.

For trace-class \(P\),
\[
  \operatorname{Tr}(\alpha_{\mathcal B}(P))
    =\overline{\operatorname{Tr}(P)}.
  \tag{4}
\]
In cyclic degree \(n\), apply \(\alpha_{\mathcal B}\) tensorwise. Multiplicativity and (4)
give, on the main diagonal,
\[
 \operatorname{Tr}\!\left(
   \alpha_{\mathcal B}(T_0)\cdots\alpha_{\mathcal B}(T_n)\right)
 =\overline{\operatorname{Tr}(T_0\cdots T_n)}.
\]
The number-field space
\({\bf S}(C_{\mathbb Q})=\bigcap_{\beta\in\mathbb R}
\mu^\beta\mathcal S(C_{\mathbb Q})\)
is stable under complex conjugation. Therefore the strongly-Schwartz cyclic submodule is
stable.

### 4. Restriction equivariance

For a source monomial, CCM's rational Morita matrix is
\[
  M_b(x,y)=
  \begin{cases}
    f_k(xb),&k=xy^{-1},\\
    0,&\text{otherwise}.
  \end{cases}
\]
Quaternionic kernel conjugation gives
\[
\begin{aligned}
  \alpha_{\mathcal B}(M_b)(x,y)
   &=\operatorname{sgn}(x)\operatorname{sgn}(y)
     \overline{M_b(-x,-y)}\\
   &=\operatorname{sgn}(k)\overline{f_k(-xb)}
    =M_b(\alpha_{\mathcal A}(f_kU_k))(x,y).
\end{aligned}
\]
Finite sums, continuity, and completion yield (3).

### 5. Cyclic operators and closed cokernel

Any unital algebra morphism induces its cyclic morphism tensorwise. Since both Real maps are
unital algebra automorphisms, tensorwise application commutes with every face, degeneracy, and
cyclic rotation. Thus (3) is an equality of cyclic morphisms, not only a degree-zero identity.

Equivariance makes the range of \(\rho^\natural\) stable. Continuity makes its closure stable.
The quotient by the closed range inherits the even involution. This is precisely the generic
closed-cokernel descent already formalized in `KRealClosedCokernel.lean`.

### 6. Idele-class action

Source pullback by an idele \(\gamma\) commutes with \(x\mapsto-x\). In the rational
trivialization using
\(\Delta_{\mathbb Q}=\widehat{\mathbb Z}^{\,*}\times\mathbb R_+^*\), transition scalars are
positive rational numbers. The proved covariance
\[
  J L_k=\operatorname{sgn}(k)L_kJ
\]
therefore reduces to \(JL_k=L_kJ\). Hence target conjugation commutes with the induced
\(C_{\mathbb Q}\)-action, and so does the closed quotient involution.

## Hostile checks

- **No change to CCM complex spectrum:** underlying source, target, morphism, and closed quotient
  are unchanged; only a conjugate-linear involution is added.
- **No trace-class gap:** target conjugation is trace-norm isometric.
- **No cyclic-degree gap:** compatibility follows from unital multiplicativity, not a
  degree-zero extrapolation.
- **No RH premise:** proof uses no zero location, positivity, determinant, or explicit-formula
  sign.
- **Parity limit:** quotient involution squares to \(+1\). Odd parity appears only after applying
  the separately proved Real Morita parity-shift theorem.
- **Remaining application gap:** a chain-level Real Morita equivalence must identify the
  intertwiner realization with the single CCM cyclic realization and preserve the trace formula.

## Lean boundary

Already formalized:

- algebraic source involution and its multiplicativity;
- target quaternionic kernel conjugation and monomial equivariance;
- actual antiunitary on the single CCM Hilbert fiber;
- bounded-operator Real isometry, quaternionic fixed algebra, exact approximation-number,
  Hilbert--Schmidt-norm and trace-norm invariance, trace-class/Schatten-\(1\) stability, and
  \(\operatorname{Tr}(\alpha T)=\overline{\operatorname{Tr}(T)}\);
- actual bounded weighted-shift representation of rational CCM monomials and operator-level
  Real equivariance;
- the unconditional trace-class criterion for a weighted shift whose rational orbit
  coefficient is in \(\ell^1(\mathbb Q^\times)\);
- absolute summability of every archimedean Schwartz function on every nonzero real integer
  lattice;
- common integer-denominator confinement for compact subsets of the actual rational finite
  adele ring and for diagonal support of finite Bruhat functions;
- fixed-base \(\ell^1(\mathbb Q^\times)\) orbit summability and actual trace-class weighted
  shifts for every element of the full algebraic adelic Bruhat tensor core;
- exact scaled Poisson duality and arbitrary-power two-ended scalar trace bounds in the
  \(1_{\widehat{\mathbb Z}}\) finite-adele sector, with the two CCM cancellations represented
  as \(f(0)=0\) and \(\int f=0\);
- closed equivariant cokernel descent;
- represented-algebra Real Morita parity shift.

Not yet represented in Lean:

- the full Bruhat--Schwartz adele LF space/bornology and trace-norm continuity of the
  pointwise trace-class field;
- the two source functionals \(\varepsilon_0,\varepsilon_1\), their cyclic kernels, and the
  signed Poisson theorem proving that the cyclic diagonal trace—not the operator trace
  norm—belongs to \({\bf S}(C_{\mathbb Q})\);
- continuous trace-class fields and proof that the completed CCM image lands in the exact
  cyclic submodule of CCM Definition 4.9;
- cyclic category, cyclic modules, and CCM's completed restriction map.

These analytic and categorical definitions must be built before formalizing the whole theorem;
they are not replaced by axioms.

## Gates

- [x] Exact source and target formulas fixed
- [x] Source-faithful Real-stability proof, conditional only on CCM's established analytic
      landing theorem
- [x] Hostile continuity, cyclic-degree, no-doubling, and circularity audit
- [ ] Formalized in Lean
- [ ] Real Morita comparison with single CCM realization

## Sources

- Alain Connes, Caterina Consani, Matilde Marcolli,
  *The Weil proof and the geometry of the adeles class space*, arXiv:math/0703392,
  §§4.2--4.6.
- André Weil/Bruhat--Schwartz functoriality under locally compact group automorphisms, as used
  in CCM's construction of \(\mathcal S(\mathbb A_{\mathbb Q})\).

## Log

- 2026-07-25 — extracted exact CCM source, target, strong-Schwartz, and closed-cokernel
  definitions. Completed proof from rational monomial Real identity; no numerical evidence or
  RH assumption used.
- 2026-07-25 — hostile source re-audit corrected a material shorthand: CCM Definition 4.9
  imposes strong-Schwartz decay only after cyclic diagonal trace. Pointwise trace class is
  separate. Removed the false prospective requirement of strong-Schwartz trace-norm decay and
  isolated the correct remaining Poisson/cancellation theorem.
- 2026-07-25 — formalized first signed-Poisson sector: exact scaling identity plus explicit
  two-ended arbitrary-power value bounds from the evaluation and integral cancellations.
