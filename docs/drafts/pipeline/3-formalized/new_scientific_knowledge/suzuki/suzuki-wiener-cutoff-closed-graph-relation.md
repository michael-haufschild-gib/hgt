# Suzuki's global Wiener carrier has an exact closed cutoff-graph relation

- **ID:** `suzuki-wiener-cutoff-closed-graph-relation`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT COMPLETED-SOURCE RELATION / CUTOFF-DEFECT CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-exterior-residual-rigged-wiener-realization.md`,
  `suzuki-wiener-neumann-plancherel-order-repair.md`,
  `suzuki-low-frequency-boundary-counterterm-renormalization.md`,
  `suzuki-polar-remainder-lipschitz-gamma-subcriticality.md`,
  `suzuki-localized-orbit-lift-selfadjointness-trilemma.md`

## 0. Scope correction: mixed norm is part of the theorem

The first version inferred a physical \(L^2_x(\ell^1)\) carrier from a frequency
\(L^2_\xi(\ell^1)\) bound. That inference is false for general \(\ell^1\)-valued Fourier
transforms. The corrected theorem uses the fixed coefficientwise Neumann majorant proved in
`suzuki-wiener-neumann-plancherel-order-repair.md`. It first proves

```text
chat in ell1_valuation(L2_frequency),
```

then applies scalar Plancherel coordinatewise. Every physical cutoff and evaluation statement
below uses this stronger mixed norm.

## 1. Result

The impossible bounded localized orbit lift is not needed.  Suzuki's literal whole-line
multiplier defines a source-dependent **closed graph relation** from every completed zero mode to
its global valuation-Wiener coefficient state.  Cutting that state to the physical interval gives
an exact self-adjoint carrier equation with one, and only one, nonregular source:

```text
the cross-boundary logarithmic Carleman commutator.       (1)
```

More precisely, fix \(I=(-a,a)\), let \(P=1_I\), and write Suzuki's exact finite-aperture symbol as

```text
p_a(xi)=a_a(xi)+Ev_xi(t_a),                              (2)

a_a(xi)=log<xi>+q_a(xi),
||q_a||_infinity<=C_a,
||t_a||_(ell1)=M_a.                                      (3)
```

Here \(t_a\) is the real symmetric finite prime-valuation convolution coefficient and
`Ev_xi(t_a)` is its literal prime trigonometric polynomial. Choose \(L_0>2(C_a+M_a)\). Let
\(\chi_a\) be a smooth high-pass multiplier supported where

```text
log<xi>>=L_0>2(C_a+M_a).                                 (4)
```

For a bounded completed zero mode \(u\), extended by zero from \(I\), put

```text
b=p_a(D)u.                                               (5)
```

The completed-source theorem gives \(b\in L^2(\mathbb R)\) and \(Pb=0\).  Split \(b=b_-+b_+\)
over the two exterior half-lines and embed these pieces at the two oriented zero-valuation roots.
Then there is a unique coefficient state

```text
c in ell1_valuation(L2_x(two roots))
       subset L2_x(ell1_valuation)
       subset L2_x(ell2)
```

whose Fourier transform is

```text
chat(xi)
 =[(a_a(xi)delta_0+t_a)^(-1)]
    *chi_a(xi) Shat b(xi).                               (6)
```

It satisfies:

```text
(a_a(D)+T_a)c=chi_a(D)S b,                               (7)
Ev(c)=chi_a(D)u,                                         (8)
```

where \(T_a\) is the bounded self-adjoint valuation convolution on the middle \(\ell^2\) carrier.

Put \(d=Pc\), componentwise in physical position.  Then \(d\) belongs to the Dirichlet graph
domain and obeys the exact cutoff identity

```text
(a_a(D)+T_a)d
 =P chi_a(D)S b+[a_a(D),P]c.                            (9)
```

Because \(T_a\) acts only in valuation coordinates, it commutes with \(P\) and contributes no
cutoff defect.  Since \(Pb=0\), the first term on the right of `(9)` is bandlimited and analytic
inside \(I\).  The commutator has the exact interior form

```text
P[a_a(D),P]c=-P a_a(D)(1-P)c.                           (10)
```

Its logarithmic part is a two-ended Carleman cross block; its bounded \(q_a(D)\) part is an
ordinary bounded commutator.  Thus `(10)` belongs to \(L^2(I;\ell^2)\).

Every source term previously left inside “global-to-log intertwining” is now classified:

```text
low frequency         -> bandlimited analytic port,
polar remainder       -> exp(-L) Gamma-subcritical port,
scalar/eigenvalue     -> bounded self-adjoint diagonal,
prime translations    -> homogeneous self-adjoint T_a,
physical cutoff       -> the sole Carleman graph port (10).                  (11)
```

Consequently the live trace-zero theorem is no longer construction or closedness of a carrier
relation.  It is the sharp weighted boundary statement

```text
zero physical half-log trace
 -> exp(sigma L) d/dL [P a_a(D)(1-P)c] in L2
    for some sigma>1/2.                                  (12)
```

Once `(12)` is proved, the existing Gamma-strip coercivity theorem puts the mode in
\(H^1_0(I)\).  No unidentified forcing remains.

## 2. Exact global coefficient relation

Let

```text
h_xi=a_a(xi)delta_0+t_a.                                 (13)
```

On the support of \(\chi_a\), `(4)` gives the valuation-Wiener inverse

```text
h_xi^(-1)
 =a_a(xi)^(-1)
   sum_(k>=0)(-t_a/a_a(xi))^(*k),                        (14)

||h_xi^(-1)||_1
 <=1/[log<xi>-C_a-M_a].                                  (15)
```

The scalar bound `(15)` alone yields only

```text
integral ||chat(xi)||_1^2 dxi<infinity.                  (16)
```

That bound does **not** Fourier-transfer to physical \(L^2(\ell^1)\). The fixed-majorant theorem
from `suzuki-wiener-neumann-plancherel-order-repair.md`, using the uniform margin `(4)`, instead
gives

```text
sum_nu ||chat_nu||_(L2_xi)<infinity.
```

Scalar coordinatewise Plancherel and Minkowski therefore give

```text
sum_nu ||c_nu||_(L2_x)<infinity,
||c||_(L2_x(ell1_nu))<infinity.
```

The inclusion \(\ell^1\subset\ell^2\) gives the middle Hilbert state.  Convolution by the real
symmetric \(t_a\) is bounded self-adjoint on \(\ell^2\).  Multiplying `(6)` by \(h_\xi\) proves
`(7)` after inverse Fourier transformation.

For every \(\xi\), absolute character evaluation is a bounded functional on \(\ell^1\) of norm at
most one.  It is a convolution character:

```text
Ev_xi(h_xi*chat(xi))
 =p_a(xi)Ev_xi(chat(xi)).                                (17)
```

The root phases reconstruct \(\widehat b\).  Since \(p_a\widehat u=\widehat b\) globally and
`(4)` excludes a zero of \(p_a\), `(17)` gives

```text
Ev_xi(chat(xi))=chi_a(xi)uhat(xi),                       (18)
```

which is `(8)`.  This is an \(\ell^1\)-graph evaluation, never an illegal bounded
\(\ell^2\)-codiagonal.

## 3. Closedness on the completed source

Let

```text
D_a^graph
 ={u in L2(R):
     supp u subset [-a,a],
     p_a(D)u in L2(R)}
```

with norm

```text
||u||_graph^2=||u||_2^2+||p_a(D)u||_2^2.                (19)
```

The Fourier multiplier \(p_a(D)\) is closed.  The support condition is a closed subspace.
Therefore `D_a^graph` is complete. The fixed-majorant estimate strengthening `(15)` shows that

```text
u |-> c
```

is bounded from `(19)` to the high-frequency
\(\ell^1_{\nu}(L^2_x)\cap L^2_x(\ell^2_\nu)\) carrier. Its graph is consequently closed.
Completed zero modes enter this domain because boundedness and the exact exterior residual theorem
prove `(5)` with \(b\in L^2\).

This closed relation is not the forbidden orbit lift.  The entries of \(c\) are the successive
valuation-Wiener parametrix coefficients in `(14)`, not equal-norm translated copies of \(u\).
Their inverse-logarithmic decay is source-dependent.

The low-pass part

```text
u_low=(1-chi_a)(D)u                                     (20)
```

is retained as a regular Paley--Wiener port.  It reconstructs the exact full mode:

```text
u=Ev(c)+u_low.                                           (21)
```

Its two endpoint values are precisely the finite counterterms used to match the high profiles.
After subtracting them, all its boundary derivatives are \(O(e^{-L})\).  Thus adding `(20)` keeps
the full relation closed and changes no singular carrier theorem.

## 4. Exact cutoff graph identity

Let

```text
H_a=a_a(D)+T_a.                                          (22)
```

The coordinate operator \(T_a\) commutes with the physical cutoff \(P\).  Starting from `(7)`:

```text
H_a(Pc)
 =P H_a c+(H_aP-PH_a)c
 =P chi_a(D)S b+[a_a(D),P]c.                            (23)
```

This proves `(9)` distributionally.  It also proves membership in the Dirichlet graph domain once
the two terms on the right are in \(L^2\).

Write \(\phi_a=1-\chi_a\).  Since \(Pb=0\),

```text
P chi_a(D)S b
 =-P phi_a(D)S b.                                       (24)
```

The multiplier \(\phi_a\) has compact frequency support.  By Cauchy--Schwarz, every derivative of
\(\phi_a(D)b\) is bounded; Paley--Wiener gives an entire extension of finite exponential type.
Thus `(24)` is analytic at both endpoints.

For the commutator, decompose

```text
[a_a(D),P]=[log<D>,P]+[q_a(D),P].                        (25)
```

The second term has norm at most \(2\|q_a\|_\infty\).  The first has, modulo a bounded smooth
kernel, the cross-boundary kernel

```text
1/(s+t),       s,t>0,                                   (26)
```

at each endpoint.  The Mellin transform diagonalizes `(26)` with multiplier
\(\pi/\sin(\pi z)\) on the critical line, so the Carleman operator is bounded on \(L^2\).
Equivalently, this is the cross-block estimate already used in the exact logarithmic Dirichlet
reconstruction.  Hence `[a_a(D),P]` extends boundedly on \(L^2\), and `(23)` holds in
\(L^2(I;\ell^2)\).

Projecting `(23)` back to the interior gives `(10)`, because \(P[a_a(D),P]P=0\) and

```text
P[a_a(D),P]
 =P a_a(D)P-Pa_a(D)
 =-P a_a(D)(1-P).                                       (27)
```

This is the exact exterior-return port hidden by a componentwise Dirichlet identification.

## 5. Boundary-log consequence

Apply the exact logarithmic boundary chart \(r=e^{-L}\) to \(d=Pc\).  The principal logarithmic
part of `(23)` becomes the literal Gamma normal operator.  The prime term is \(T_a\), the scalar
part is a bounded diagonal, `(24)` is analytic, and the polar convolution has differentiated rate
\(O(e^{-L})\).  Therefore the only forcing not already in every Gamma strip below the first pole
is the Carleman port `(10)`.

If `(12)` holds, choose \(1/2<\sigma<1\).  The weighted Gamma-wall numerical-range estimate and
terminal \(2L\) coercivity then yield

```text
e^(sigma L)d'(L) in L2(dL;ell2).                         (28)
```

The valuation-Wiener grade majorant upgrades `(28)` to the \(\ell^1\) graph on a terminal ray, so
absolute evaluation and `(21)` give spatial \(H^1\).  The analytic low port supplies the finite
remainder.  Thus:

```text
(12) -> trace-zero completed mode lies in H1_0.          (29)
```

Equation `(12)`, not carrier existence, is now `SUZUKI-TRACE-ZERO-H1`.

## 6. Hostile audit

1. **No bounded orbit lift.**  The carrier is the coefficient state `(14)` on the multiplier graph
   domain, consistent with the orbit-lift trilemma.
2. **No componentwise support claim.**  The global coefficients are delocalized.  Their physical
   cutoff is performed explicitly, and `(23)` retains its nonzero commutator.
3. **No plain support compression.**  Exterior return is `(10)`, not deleted.  This is the physical
   analogue of the positive Feshbach correction.
4. **No low-frequency division.**  The inverse is used only on `(4)`; `(20)` is retained as a
   regular port.
5. **No illegal `ell2` evaluation.**  Reconstruction uses the `ell1` graph state.
6. **No Banach-valued Plancherel shortcut.** The fixed Neumann majorant proves
   \(\ell^1_\nu(L^2_\xi)\) before scalar coordinatewise Plancherel.
7. **No weighted conclusion from unweighted `L2`.**  Carleman boundedness proves only the cutoff
   graph identity.  The weighted estimate `(12)` remains open and is stated explicitly.
8. **No RH claim.**  Even `(29)` would leave the raw Evans determinant and the nonzero-trace
   two-port return.

## 7. Novelty boundary

Closed Fourier multipliers, Wiener inversion, commutator identities, Paley--Wiener regularity, and
Carleman boundedness are classical separately.  Candidate-new source knowledge is the exact
assembly

```text
completed Suzuki exterior residual
 -> closed valuation-Wiener graph relation
 -> physical cutoff identity
 -> unique Carleman defect port
 -> exact weighted trace-zero target (12).               (30)
```

The corpus previously had the global high-frequency carrier, the physical-log normal operator,
and the warning that a cutoff intertwiner was missing.  It did not construct the closed relation
or prove that every omitted term collapses to the single cross-boundary operator `(10)`.
External priority remains unaudited.

## 8. Lean decision

The formal tree has the valuation adjacency, its self-adjointness, Wiener-grade coefficients,
evaluation fracture, and orbit-lift trilemma.  It does not yet model the unbounded Fourier
multiplier \(a_a(D)\), sharp physical interval projection, or Carleman cross block.  Formalizing
only the algebraic identity in `(23)` would be a wrapper around the missing source operators and
would not certify `(1)`.  No new Lean module is added for this theorem until that analytic
infrastructure exists.

## Gates

- [x] define the completed-source multiplier graph domain
- [x] construct the global `ell1(L2) subset L2(ell1) subset L2(ell2)` coefficient relation
- [x] prove graph closedness
- [x] retain the exact low-frequency Paley--Wiener port
- [x] prove exact physical cutoff identity
- [x] prove the cutoff defect is the cross-boundary Carleman block
- [x] prove every other source term is analytic, homogeneous, or Gamma-subcritical
- [x] isolate the exact weighted Carleman target `(12)`
- [ ] prove `(12)` from zero physical half-log trace
- [ ] formalize the unbounded multiplier/cutoff/Carleman infrastructure
- [ ] prove trace-zero completed modes enter `H1_0`
- [ ] prove raw Evans injectivity
- [ ] RH
