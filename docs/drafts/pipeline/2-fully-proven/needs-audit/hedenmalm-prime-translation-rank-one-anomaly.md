# Prime-translation rank-one anomaly of the Hedenmalm compact source operator

- **ID:** `hedenmalm-prime-translation-rank-one-anomaly`
- **Stage:** 2-fully-proven / needs literature and Lean audit
- **Type:** THEOREM / FIBREWISE ORDINARY-INTEGER INCIDENCE LANDING
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  `hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `hedenmalm-essential-inverse-flow-prime-tomography.md`;
  `../not_new_scientific_knowledge/poisson-euler-sobolev-natural-cone-bipolarity.md`.
- **Positive successor:**
  `hedenmalm-two-prime-theta-interval-normal-frame.md`.

## Source core

Let `k` be the normalized Hedenmalm theta source, let

\[
 M=\int_{\mathbb R}k(x)\,dx=\Xi_C(0)>0,
 \tag{1}
\]

and use the exponential source core

\[
 \mathscr E=\left\{f\in C^\infty(\mathbb R):
 e^{c|x|}f^{(j)}(x)\in L^1(\mathbb R)
 \text{ for every }c>0,\ j\ge0\right\}.
 \tag{2}
\]

This core contains compactly supported smooth functions and `k`, is translation invariant, and
supports Fourier--Laplace evaluation at every complex point.  Put

\[
 \ell(f)=\int_{\mathbb R}f,
 \qquad
 Pf=f-\frac{\ell(f)}M k,
 \qquad
 (Vg)(x)=i\int_{-\infty}^xg(y)\,dy
 \quad(\ell(g)=0),
 \tag{3}
\]

and define

\[
 \mathsf B=VP:\mathscr E\longrightarrow\mathscr E.
 \tag{4}
\]

On its weighted-Hilbert domain, `(4)` is the source-core realization of the compact operator
`B=A^(-1)P` on `H_k=L2(R,k^(-1)dx)`.

For `a in R`, let

\[
 (S_af)(x)=f(x-a).
 \tag{5}
\]

For every positive integer `n`, define the normalized integer shift

\[
 T_n=n^{-1/2}S_{-\log n},
 \qquad
 (T_nf)(x)=n^{-1/2}f(x+\log n).
 \tag{6}
\]

Then `T_m T_n=T_(mn)`.  The prime shifts `T_p` therefore generate the literal free
multiplicative ordinary-integer action before any zero is chosen.

## Theorem

### 1. Rank-one source anomaly

For every real `a` and every `f in E`,

\[
 [\mathsf B,S_a]f
 =\frac{\ell(f)}M r_a,
 \qquad
 r_a=V(S_ak-k).
 \tag{7}
\]

For every positive integer `n`,

\[
 [\mathsf B,T_n]f
 =\frac{\ell(f)}M r_n,
 \qquad
 r_n=V(T_nk-n^{-1/2}k).
 \tag{8}
\]

Every `r_a` with `a ne 0`, and every `r_n` with `n>1`, is nonzero.  Thus prime covariance does not
disappear: its complete failure is a canonical one-dimensional source channel.

### 2. Fibrewise ordinary-integer character

For `z in C`, put

\[
 \ell_z(f)=\int_{\mathbb R}f(x)e^{izx}\,dx,
 \qquad
 s(z)=\frac12+iz.
 \tag{9}
\]

Then, before zero specialization,

\[
 \ell_z\circ T_n=n^{-s(z)}\ell_z
 \qquad(n\ge1).
 \tag{10}
\]

If `XiC(z)=0`, `ell_z` is the nonzero cokernel conormal of `A+z`, and hence of the corresponding
Grushin pencil.  Therefore every Xi conormal carries the actual ordinary-integer character
`n mapsto n^(-s)`, whose prime values determine it by unique factorization.  No generalized-prime
or divisor-indexed action is inserted.

### 3. Explicit nonzero right mode

At every zero `z` of `XiC`, define

\[
 I_z(x)=\int_{-\infty}^x k(y)e^{izy}\,dy,
 \qquad
 u_z(x)=-i e^{-izx}I_z(x),
 \qquad
 f_z=-zu_z.
 \tag{11}
\]

Then `u_z,f_z in E cap H_k`, `f_z ne 0`, and

\[
 (A+z)u_z=-k,
 \qquad
 (I+zB)f_z=0,
 \qquad
 Bf_z=-z^{-1}f_z.
 \tag{12}
\]

Thus every Xi divisor point produces a nonzero source-normalized global right mode in the fixed
weighted Hilbert space.  The normalization is the fixed Grushin source coefficient `1`, not a
zero-dependent metric.

Writing

\[
 k(x)=e^{x/2}\sum_{n\ge1}h(ne^x),
 \qquad
 H_s^{\mathrm{tail}}(X)=\int_X^\infty h(t)t^{s-1}\,dt,
 \tag{13}
\]

gives the absolutely convergent literal integer expansion

\[
 I_z(x)=-\sum_{n\ge1}n^{-s(z)}H_{s(z)}^{\mathrm{tail}}(ne^x).
 \tag{14}
\]

Equation `(14)` is an incomplete Mellin expansion on the actual integers.  Unlike the completed
scalar Fourier transform, it retains the scale cutoff `ne^x` inside every mode.

### 4. Reflection and multiplicity package

Let `Rf(x)=f(-x)`.  Evenness and reality of `k` give, at divisor points,

\[
 Rf_z=f_{-z},
 \qquad
 \overline{f_z}=f_{-\overline z},
 \qquad
 RBR=-B.
 \tag{15}
\]

If `z_0` is a zero of analytic order `m`, then

\[
 \dim\ker(I+z_0B)=1,
 \tag{16}
\]

while the algebraic multiplicity of `-1/z_0` is `m`.  Its generalized eigenspace is therefore one
Jordan block of length `m`; no multiplicity level is lost.

The left incidence jets

\[
 \ell_z^{[j]}(f)=\frac{d^j}{dz^j}\ell_z(f)
 =\int_{\mathbb R}(ix)^j f(x)e^{izx}\,dx
 \tag{17}
\]

obey the exact triangular prime law

\[
 \ell_z^{[j]}(T_nf)
 =n^{-s(z)}\sum_{r=0}^j
   \binom jr(-i\log n)^{j-r}\ell_z^{[r]}(f).
 \tag{18}
\]

Hence the full conormal jet carries the expected logarithmic prime Jordan data, including at a
multiple zero.

## Proof

### Source-core closure

Translations preserve `(2)`.  The theta source and all of its derivatives have
double-exponential tails, so `k in E`.  If `g in E` and `ell(g)=0`, then

\[
 Vg(x)=-i\int_x^\infty g(y)\,dy
 \tag{19}
\]

as well as the left-tail formula in `(3)`.  Exponential tail estimates on the two formulas and
`(Vg)'=ig` show `Vg in E`.  Thus `(4)` is well defined.

### Rank-one commutator

Lebesgue integration is translation invariant, and `V S_a=S_aV` on the zero-integral source
subspace.  If `c=ell(f)/M`, then

\[
\begin{aligned}
 P S_af-S_aPf
 &=S_af-ck-S_a(f-ck)\\
 &=c(S_ak-k).
\end{aligned}
\tag{20}
\]

Applying `V` proves `(7)`.  More generally, `ell(T_nf)=n^(-1/2)ell(f)`, so

\[
 PT_nf-T_nPf
 =\frac{\ell(f)}M(T_nk-n^{-1/2}k).
\tag{21}
\]

Applying `V` proves `(8)`.  If `r_a=0`, differentiation gives `S_ak=k`; a nonzero function tending
to zero at both infinities cannot have a nonzero real period.  If `r_n=0`, then
`T_nk=n^(-1/2)k`, equivalently `k(x+log n)=k(x)`, and the same argument applies.

### Character law and conormal landing

The substitution `y=x+log n` gives

\[
\begin{aligned}
 \ell_z(T_nf)
 &=n^{-1/2}\int_{\mathbb R}f(x+\log n)e^{izx}\,dx\\
 &=n^{-1/2-iz}\ell_z(f)
 =n^{-s(z)}\ell_z(f),
\end{aligned}
\tag{22}
\]

proving `(10)`.  Integration by parts gives

\[
 \ell_z((A+z)u)=0.
 \tag{23}
\]

At a zero, `ell_z(k)=XiC(z)=0`, so `ell_z` annihilates the full Grushin range.  The parent
Fredholm theorem says that `A+z` has codimension-one range, making this conormal exact and nonzero.

### Right mode

Differentiate `(11)`:

\[
 -iu_z'(x)+zu_z(x)=-k(x).
 \tag{24}
\]

At `-infinity`, the left integral in `(11)` has theta-tail decay.  At `+infinity`, the zero
condition rewrites it as

\[
 I_z(x)=-\int_x^\infty k(y)e^{izy}\,dy.
 \tag{25}
\]

The double-exponential theta tails dominate every exponential introduced by `z`, proving
`u_z,f_z in E cap H_k`.  The integral in `(11)` cannot vanish identically because its derivative
is `k(x)e^(izx) ne 0`; hence `f_z ne 0` (and `z ne 0` for a nontrivial centered Xi zero).

Equation `(24)` gives `G_z(u_z,1)=0` and

\[
 G_0(u_z,1)=Au_z+k=-zu_z=f_z.
\tag{26}
\]

The Grushin factorization `(I+zB)G_0=G_z` proves `(12)`.

For `(14)`, use the zero-dependent but exact tail identity `(25)`, substitute `(13)`, and set
`t=ne^y`:

\[
\begin{aligned}
 I_z(x)
 &=-\sum_{n\ge1}\int_x^\infty
    e^{(1/2+iz)y}h(ne^y)\,dy\\
 &=-\sum_{n\ge1}n^{-s(z)}
   \int_{ne^x}^\infty h(t)t^{s(z)-1}\,dt.
\end{aligned}
\tag{27}
\]

For each fixed `x`, Gaussian decay of `h` makes the last series absolutely convergent.  Using the
left incomplete integral term by term in the critical strip would incorrectly replace this
convergent tail by a divergent uncontinued Dirichlet series; no such interchange is made.

### Reflection, block length, and jets

Since `XiC(-z)=0` and `k` is even,

\[
 I_z(-x)=\int_x^\infty k(t)e^{-izt}\,dt=-I_{-z}(x),
\tag{28}
\]

which gives the first identity in `(15)`; conjugation gives the second.  The third is the parent
operator theorem.

If `(u,c)` lies in `ker G_z` with `c=0`, injectivity of `A+z` gives `u=0`.  Projection to the scalar
coordinate is therefore injective on `ker G_z`, so its dimension is at most one.  The explicit
vector `(u_z,1)` makes it exactly one.  Grushin equivalence transports this to `(16)`.  Analytic
Fredholm multiplicity is the order `m` of `XiC`; one geometric block with total algebraic size `m`
is a single Jordan block of length `m`.

Finally, differentiate `(10)` `j` times.  Since

\[
 \frac{d^q}{dz^q}n^{-s(z)}=(-i\log n)^q n^{-s(z)},
\tag{29}
\]

Leibniz's rule gives `(18)`.

## What this changes

The prior compact inverse theorem constructed every divisor mode but did not retain literal prime
labels.  The essential-trace theorem welded only the aggregate Riesz trace to a prime--Gamma
sequence.  Equations `(7)`--`(18)` now add the missing fibrewise incidence layer:

```text
theta source k
  -> compact reciprocal-divisor operator B
  -> nonzero right mode f_z in one fixed weighted Hilbert space
  -> exact left conormal ell_z
  -> ordinary-integer character n^(-s)
  -> logarithmic prime jet representation through full multiplicity.
```

The rank-one commutator is a nonzero source-core anomaly, but it is **not** a divisor extension
class.  The successor theorem computes

```text
Fourier(r_n)(z)
  = n^(-1/2) (1-exp(-i z log n))/z * XiC(z).
```

Hence the raw anomaly is divisor-exact.  Its source-normal quotient is nonzero and, after centered
interval symmetrization, the prime-2 and prime-3 quotients generate the complete Xi conormal
module.  This realizes concretely why ordinary Hilbert closure erases the anomaly while a
source-normal blow-up retains it.

## Remaining RH theorem

This still does not make `B` self-adjoint.  On a strict-right zero, `(10)` is a nonunitary
ordinary-prime character, and source-linear superselection forbids its reflected sector from being
coupled by a nonzero closed boundary operator.  The theorem above lives on the preboundary
exponential core, with the rank-one anomaly retained.

The old proposed descent of the raw vectors `r_p` is false: they vanish in every analytic Xi
divisor fibre.  The corrected source theorem acts on their source-normal quotients, not on the raw
commutator range.  It can now be stated on a completely explicit object:

> Show that the essential reciprocal symbols
> `2 p^(-1/2) mu sin(log(p)/(2 mu))`, for at least the prime pair `p=2,3`, define a closed strict
> reflection-compatible boundary descent on the theta Grushin root expansion and retain their
> unsymmetrized prime phase.

The successor theorem proves pointwise nonannihilation on every root block but also proves failure
of every bounded two-prime corona estimate.  Proving strict closed descent is RH-bearing; merely
asserting closedness, source linearity, or a same-fibre dagger restates the missing step.

## Preliminary literature audit

Hedenmalm's source paper constructs the differential pencil and its zero eigenfunctions, but its
stated operator problem does not introduce the compact Grushin inverse, normalized ordinary-
integer shift semigroup, rank-one covariance anomaly, or the conormal prime-jet law above:
<https://arxiv.org/abs/2606.17494>.

Rank-one commutators, translation eigenfunctionals, Mellin characters, and Jordan differentiation
are classical ingredients.  Targeted searches for their Hedenmalm/Xi combination found general
compact-commutator theory but no direct source-specific match; for example:
<https://arxiv.org/abs/1303.4844>.  No standalone novelty is claimed for any ingredient, and the
combined theorem remains `[NOVELTY UNVERIFIED]` pending an independent operator-theory audit.

## Hostile audit

1. **Core, not Hilbert covariance.**  `T_n` need not be bounded on `H_k`; `(7)`--`(8)` are
   exponential-core identities.  This domain fracture is part of the result, not silently ignored.
2. **No positivity.**  A rank-one commutator and a character law do not supply a positive metric.
3. **No fake prime decoration.**  The complete semigroup `T_n` is defined before zeros, and
   `(10)` follows by change of variables.  Prime labels enter by unique factorization of the
   actual integer action.
4. **No aggregate-to-fibre inference.**  Fibrewise incidence comes from `(10)` and `(18)`, not from
   the aggregate trace theorem.
5. **No simplicity assumption.**  One geometric block plus exact analytic multiplicity gives the
   full Jordan length; it does not prove that the length is one.
6. **No closed boundary landing.**  The exponential source core permits nonunitary characters.
   Upgrading it to the fixed prime-cylinder `C*` boundary is exactly the missing theorem.
7. **Generic-source falsifier survives.**  Any sufficiently decaying source has analogous
   translation identities.  The arithmetic content is the simultaneous ordinary-integer
   expansion `(14)`, unique-factorization action `(6)`, and exact Xi determinant; these still do
   not force reality alone.
8. **Raw anomaly is fibrewise exact.**  Its Fourier transform is divisible by `XiC`; the entire
   multiplicity jet below the first normal order vanishes.  Only the source-normal quotient in the
   successor theorem survives.

## Gates

- [x] exponential source core defined
- [x] rank-one translation anomaly proved
- [x] literal ordinary-integer semigroup action proved
- [x] exact fibrewise Dirichlet character proved
- [x] nonzero source-normalized right mode constructed
- [x] incomplete ordinary-integer Mellin expansion proved
- [x] reflection and conjugation internalized
- [x] geometric multiplicity one and full Jordan length proved
- [x] prime logarithmic conormal jets proved
- [x] raw anomaly proved divisor-exact
- [x] nonzero source-normal successor extracted
- [ ] independent analytic/operator hostile audit
- [x] preliminary literature noncollision search
- [ ] independent literature priority audit
- [ ] closed untwisted boundary descent
- [ ] positive self-adjoint realization
- [ ] RH
