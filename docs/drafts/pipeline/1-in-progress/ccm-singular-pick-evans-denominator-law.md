# CCM singular-Pick Evans denominator law

- **ID:** `ccm-singular-pick-evans-denominator-law`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / finite universal theorem plus cofinal RH attack
- **Source:** `ccm-source-pencil-radical-evans-coefficient-law.md`; actual CCM divided-difference
  matrices in Connes--Consani--Moscovici
- **Statement:** Every negative CCM source divided difference forces a zero of the actual
  active-even radical-quotient characteristic polynomial between the corresponding clock nodes.
  Therefore any such quotient family converging locally uniformly to centered Xi must eventually
  preserve source order throughout Xi's unconditional central zero-free slab. The live question is
  whether the explicit von-Mangoldt--Gamma source violates this forced order cofinally.

## Goal

Turn C28's explicit coefficient polynomial into a source-side pole detector requiring no inverse,
cyclic vector, or residue lower bound. Then decide the exact arithmetic alternative: prove the
actual CCM source is eventually ordered on every Xi-zero-free interval, or exhibit a persistent
descent and rule out divisor-faithful CCM determinant convergence.

## Gates

- [x] 0 -> 1 in-progress: exact source matrix, quotient realization, and hostile convergence test
- [x] finite descent--pole theorem and cofinal central-slab order theorem proved
- [x] unconditional Lean theorem(s) completed; final audit tracked on the formalized child card
- [ ] 1 -> 2 decisive source theorem: prove actual cofinal order or persistent actual descent
- [ ] 3 -> 4 publication-ready: only after RH or a category-wide CCM no-go

## Exact finite candidate

Let `x_i` be distinct real clock nodes, let `b_i,d_i` be real, and put

```text
T_ii=d_i,
T_ij=(b_i-b_j)/(x_i-x_j),  i != j.                         (1)
```

Assume `T` is positive semidefinite and singular.  In the active constant-boundary branch choose
`c in ker T` with `sum_i c_i=1` and form

```text
A=diag(x_i)-|diag(x_i)c><1|.                               (2)
```

Let `B` be a surjective Gram factor, `T=B^*B`, and let `C` be the operator induced by `A` on
`H=C^I/ker T`.  If `v_i=B e_i` and `u=B(diag(x_i)c)`, then

```text
(C-x_i)v_i=-u,
<v_i,v_j>=T_ij.                                           (3)
```

The columns `v_i` span `H`, but this does **not** imply that `u` is cyclic: a selected radical
coordinate may vanish, a clock node may itself be a quotient eigenvalue, and cancellation can
remove a declared boundary pole. The valid inverse-free consequence of `(3)` is instead

```text
<v_i,v_j><0  and  x_i<x_j
  -> spec(C) intersects [x_i,x_j].                         (4)
```

Indeed, if `[x_i,x_j]` avoided the spectrum, simultaneous spectral expansion of the two resolvent
columns in `(3)` would express their cross Gram product as a sum of nonnegative terms. For the CCM
divided-difference Gram,

```text
<v_i,v_j>=(b_i-b_j)/(x_i-x_j),                            (5)
```

so a strict source descent `b_j<b_i` across `x_i<x_j` forces the spectral intersection. Every such
eigenvalue is a zero of the complexified quotient characteristic polynomial. C28 still identifies
that polynomial, up to its nonzero semimetric coefficient, with

```text
det(C-zI)
 = [X^(|I|-rank T)] charpoly(T(diag(x)-zI)+|b><1|)
   / [X^(|I|-rank T)] charpoly(T).                         (6)
```

The response branch has the reflected formula with `-|1><b|`. Unlike the discarded cyclicity
claim, `(3)--(6)` require neither a one-dimensional radical nor nonzero coordinates of a selected
kernel vector, and remain valid when a clock node is itself a quotient eigenvalue.

## Actual CCM source interpolation law

For `L=2 log lambda`, the physical nodes are `t_n=2 pi n/L`.  With

```text
B_L(t)=-(1/pi) integral_[0,L] sin(t y) dD(y),
G_L(t)= (1/pi) integral_[0,L] cos(t y) dD(y),              (7)
```

the entire source function

```text
H_(L,epsilon)(t)
 = B_L(t)+sin(Lt)(G_L(t)-epsilon/(2pi))                   (8)
```

has at every CCM grid point

```text
H_(L,epsilon)(t_n)=b_n,
H_(L,epsilon)'(t_n)=L(a_n-epsilon)/(2pi).                 (9)
```

Hence the shifted CCM matrix, after multiplication by `L/(2pi)`, is exactly the confluent boundary
Pick data of `(8)` on the finite clock grid.  Equation `(8)` is a source identity, not a claim that
the entire function itself is Pick.

## Live cofinal conjecture and hostile test

The prior normal-family paragraph depended on the false cyclic realization and is withdrawn.
The inverse-free theorem gives a sharper hostile test. Centered Xi is unconditionally nonzero on
`[-4,4]`; compact-open convergence therefore makes every approximant zero-free on the whole closed
slab eventually. Combining this with `(4)--(5)` proves:

```text
active-even CCM quotient determinants -> Xi locally uniformly
  => for every moving pair x_i<x_j in [-4,4], eventually b_i<=b_j.   (10)
```

Dimensions, radical dimensions, scalar normalizations, and node pairs may all move. Thus one
cofinal actual source descent inside this slab kills the surviving active-even determinant
transfer. Exact unresolved source theorem is now the sign of the explicit finite
von-Mangoldt--Gamma divided differences, not Herglotz normality or pole tightness.

## Novelty and non-duplication boundary

- Singular boundary Pick uniqueness, rational Herglotz realizations, and cyclic minimal
  denominators remain classical parent theory but are no longer asserted to apply at every CCM
  boundary node.
- Corpus already proves that Xi's own Schur/Pick inverse limit is RH-equivalent and that a single
  finite singular Pick interpolant cannot equal nonrational Xi.
- Candidate-new content is the exact inverse-free assembly `(3)--(6)` and the cofinal central-slab
  order law `(10)` for the actual active-even quotient, valid for arbitrary radical dimension.
- No RH claim is made while cofinal determinacy remains open.

## Log

- 2026-07-23 — created after C28 corpus audit; finite quotient realization and exact source Hermite
  interpolation derived; cofinal normality separated from the unresolved determinacy/tightness
  theorem.
- 2026-07-23 — hostile correction: arbitrary radical dimension does not make the quotient source
  cyclic and clock nodes can be poles. Withdrew the rational-interpolation overclaim. Replaced it
  by the inverse-free Hermitian descent--pole theorem and formalized the resulting cofinal Xi
  central-slab source-order law. Remaining kill test is persistent descent of the actual
  von-Mangoldt--Gamma source.
