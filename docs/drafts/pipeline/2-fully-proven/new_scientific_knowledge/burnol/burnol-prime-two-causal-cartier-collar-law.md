# Burnol prime-two Gamma-sewn causal Cartier collar law

- **ID:** `burnol-prime-two-causal-cartier-collar-law`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM (paper)
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [COEFFICIENT-FAITHFUL]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Statement:** The exact prime-two Burnol--Xi completion, including the Gamma factor required by
  the physical source typing, is a labelled dyadic family of explicit sign-changing convolution
  kernels.  Its fixed-aperture commutator is an explicit cross-boundary Cartier operator, and every
  dyadic depth has one negative logarithmic collar of the same width.

## Goal

Construct the literal noncommuting source object hidden behind

```text
[P_(1/2), C_2]
```

without confusing Burnol's raw physical Mellin transform with its Gamma-completed evaluation.
The result must retain dyadic depth, both Gamma orientations, and the exact negative channels from
which a source proof of the Route R current sign could come.

This card does not assert `J_rho <= 0`.  It replaces an unspecified singular Stokes comparison by
one explicit kernel and identifies its exact remaining source inequality.

## Conventions

Put

\[
 L=\log 2,\qquad q=2^{-1/2},\qquad
 A=\partial_u+\frac12,
 \qquad (\tau_a g)(u)=g(u-a).
\tag{1}
\]

Use logarithmic coordinate `u=log x` and Fourier convention

\[
 \widehat g(t)=\int_{\mathbb R}g(u)e^{-itu}\,du.
\tag{2}
\]

Convolution below is normalized so that its Fourier transform is the product of Fourier
transforms.  With a different Fourier normalization, every kernel acquires one common positive
constant; none of the identities, supports, or signs changes.

## Theorem 1 — causal dyadic realization of the rational completion

On the critical Mellin line `w=1/2+it`, the multiplier

\[
 C_2(w)=\frac{w^2(w-1)}{2(2^w-1)}
\]

has logarithmic realization

\[
 \boxed{
 {\cal C}_2=\frac12 A^2(A-1)T_2,
 \qquad
 T_2=\sum_{n\ge1}q^n\tau_{nL}.}
\tag{3}
\]

The series converges in operator norm on every Sobolev space because translations are isometries
and `sum q^n < infinity`.

### Proof

For `Re w>0`,

\[
 \frac1{2^w-1}=\sum_{n\ge1}2^{-nw}.
\tag{4}
\]

At `w=1/2+it`, the `n`-th term is `q^n e^{-itnL}`, the multiplier of
`q^n tau_(nL)`.  Under `(2)`, the symbol of `A` is `w`.  Multiplication of `(4)` by
`w^2(w-1)/2` proves `(3)` first on Schwartz functions and then as a continuous map
`H^3 -> L^2`.  `QED`

## The typing wall: why `(3)` alone is not yet physical

For the fixed co-Poisson atom, the corpus proves

\[
 F(w)=\Gamma_{\mathbb R}(w)H(w),
 \qquad
 H(w)=\frac{(2^w-1)\zeta(w)}{w},
\tag{5}
\]

and `C_2(w)F(w)=xi(w)`.  The physical logarithmic vector has raw Mellin transform `H`, not `F`.
Therefore applying `(3)` directly to the constant physical head is ill-typed: Gamma completion is
a nonlocal convolution and must be sewn in before taking the aperture commutator.

This observation kills the tempting but false inference that the rational dyadic ladder alone
turns the physical constant head into a pure delta ladder.  The correctly typed operator is the
product `C_2 Gamma_R` constructed next.

## Theorem 2 — explicit Gamma-sewn depth kernel

Define

\[
 \gamma(u)=2e^{-u/2}\exp(-\pi e^{-2u}).
\tag{6}
\]

Then

\[
 \widehat\gamma(t)=\Gamma_{\mathbb R}\!\left(\frac12+it\right).
\tag{7}

For each dyadic depth `n>=1`, put

\[
 z_n(u)=\pi4^n e^{-2u}
\tag{8}
\]

and

\[
 \boxed{
 \kappa_n(u)=
 4e^{-u/2}e^{-z_n(u)}z_n(u)
 \bigl(2z_n(u)^2-7z_n(u)+3\bigr).}
\tag{9}
\]

The full physical completion operator whose Fourier multiplier is

\[
 M_2(w)=C_2(w)\Gamma_{\mathbb R}(w)
\tag{10}
\]

is convolution with the locally normally convergent kernel

\[
 \boxed{
 \kappa_2=\sum_{n\ge1}\kappa_n.}
\tag{11}
\]

Keeping the summands before addition gives a coefficient-faithful depth lift

\[
 \widetilde{\cal K}_2g=(\kappa_n*g)_{n\ge1}.
\tag{12}
\]

### Proof of the Gamma kernel

Substitute `r=e^{-u}` in the Fourier transform of `(6)`:

\[
 \begin{aligned}
 \widehat\gamma(t)
 &=\int_0^\infty 2e^{-\pi r^2}r^{1/2+it}\frac{dr}{r}\\
 &=\pi^{-(1/2+it)/2}\Gamma\!\left(\frac{1/2+it}{2}\right),
 \end{aligned}
\]

which is `(7)`.

The `n`-th labelled summand of `T_2 gamma` is

\[
 q^n\gamma(u-nL)
 =2e^{-u/2}\exp(-\pi4^ne^{-2u}).
\tag{13}
\]

Write the right side as `h_n(u)`.  Since `z_n'=-2z_n`, direct differentiation gives

\[
 Ah_n=2z_nh_n.
\tag{14}
\]

For any polynomial `p`,

\[
 A(h_np(z_n))=2z_nh_n\bigl(p(z_n)-p'(z_n)\bigr).
\tag{15}
\]

Starting with `(A-1)h_n=(2z_n-1)h_n` and applying `(15)` twice yields

\[
 A^2(A-1)h_n
 =h_n(8z_n^3-28z_n^2+12z_n).
\tag{16}
\]

The factor `1/2` in `(3)` turns `(16)` exactly into `(9)`.  For `u` in a compact interval,
`z_n(u)` grows geometrically while `e^{-z_n(u)}` decays superexponentially.  Hence `(11)` and all
of its differentiated versions converge normally on compact sets.  Fourier transformation of
`(11)` now gives `(10)`.  `QED`

## Corollary 3 — one universal negative collar at every depth

Because all factors outside the final quadratic in `(9)` are strictly positive,

\[
 \operatorname{sgn}\kappa_n(u)
 =\operatorname{sgn}\bigl(2z_n(u)^2-7z_n(u)+3\bigr).
\]

The quadratic factors as

\[
 2z^2-7z+3=2(z-1/2)(z-3).
\]

Therefore

\[
 \boxed{
 \kappa_n(u)<0
 \iff
 nL+\frac12\log\frac\pi3
 <u<
 nL+\frac12\log(2\pi).}
\tag{17}
\]

Every depth has exactly one negative logarithmic collar, of depth-independent width

\[
 \frac12\log6.
\tag{18}
\]

The kernel is positive on both flanks.  Thus Gamma sewing does not merely make the dyadic boundary
indefinite; it gives one rigid three-chamber pattern at every retained depth.

## Corollary 3a — exact negative-mass surplus at every depth

Let `kappa_*` be the depth-zero profile obtained from `(9)` by setting
`z_*(u)=pi exp(-2u)`.  Then

\[
 \boxed{\kappa_n=q^n\tau_{nL}\kappa_*.}
\tag{18a}
\]

Indeed, `z_*(u-nL)=z_n(u)`, and `q^n` exactly compensates the translation of the
`exp(-u/2)` factor.  Thus every depth is one translated copy of the same three-chamber profile.

Its total mass is strictly negative and exact:

\[
 \boxed{
 \int_{\mathbb R}\kappa_n(u)\,du
 =-\frac{q^n}{16}\Gamma_{\mathbb R}\!\left(\frac12\right)<0.}
\tag{18b}
\]

To prove `(18b)`, evaluate the Fourier multiplier of the `n`-th summand at frequency zero.  At
`w=1/2`,

\[
 \frac12w^2(w-1)=-\frac1{16};
\]

the translation multiplier is `q^n`, and `Gamma_R(1/2)>0`.

Writing `kappa_n=kappa_n^+-kappa_n^-` for its positive and negative parts, `(18b)` is equivalent
to the exact surplus

\[
 \boxed{
 \int\kappa_n^--\int\kappa_n^+
 =\frac{q^n}{16}\Gamma_{\mathbb R}\!\left(\frac12\right).}
\tag{18c}
\]

The negative collar therefore already outweighs both positive flanks in unweighted mass.  A Route
R producer need not create a negative channel.  It must prove that weighting this fixed profile by
the actual zero-divided co-Poisson cross-correlation does not reverse `(18c)`.

## Corollary 3b — scale-free collar plateau criterion

For a logarithmic source vector `g`, define its oriented aperture-crossing correlation

\[
 W_{g,b}(s)=
 \int_{\mathbb R}\overline{g(v+s)}
 \bigl({\bf1}_{v+s\le b}-{\bf1}_{v\le b}\bigr)g(v)\,dv.
\tag{18d}
\]

Let

\[
 Q_n(g)=\langle g,[P_b,{\cal K}_{2,n}]g\rangle.
\]

Fubini and the change of variables `s=u-v` give

\[
 \boxed{
 Q_n(g)=\int_{\mathbb R}\kappa_n(s)W_{g,b}(s)\,ds,
 \qquad
 q^{-n}Q_n(g)=
 \int_{\mathbb R}\kappa_*(r)W_{g,b}(nL+r)\,dr.}
\tag{18e}
\]

Suppose there are positive numbers `a_n` and a complex scalar `c` such that

\[
 \int_{\mathbb R}|\kappa_*(r)|
 \left|a_n^{-1}W_{g,b}(nL+r)-c\right|\,dr
 \longrightarrow0.
\tag{18f}
\]

Then `(18b)` and `(18e)` imply the exact normalized limit

\[
 \boxed{
 (q^na_n)^{-1}Q_n(g)
 \longrightarrow
 -\frac{c}{16}\Gamma_{\mathbb R}\!\left(\frac12\right).}
\tag{18g}
\]

In particular, `Re c>0` forces `Re Q_n(g)<0` for every sufficiently large depth.  This is the
precise tightness statement needed to preserve the collar's negative surplus: after the natural
source normalization `a_n`, the crossing correlation must become asymptotically constant across
one fixed-width translated profile.  No pointwise sign of `kappa_n` and no global operator order
is required.

## Theorem 4 — exact fixed-aperture Cartier crossing operator

Let `P_b` be multiplication by `1_{(-infinity,b]}`; Route R uses `b=-log 2`.  If

\[
 ({\cal K}_2g)(u)=(\kappa_2*g)(u),
\]

then

\[
 \boxed{
 ([P_b,{\cal K}_2]g)(u)
 =\int_{\mathbb R}\kappa_2(u-v)
 \bigl({\bf1}_{u\le b}-{\bf1}_{v\le b}\bigr)g(v)\,dv.}
\tag{19}
\]

Coefficient-faithfully,

\[
 [P_b,{\cal K}_2]=\sum_{n\ge1}[P_b,{\cal K}_{2,n}],
\tag{20}
\]

where `(19)` with `kappa_n` in place of `kappa_2` is the depth-`n` component.

Equation `(19)` has only cross-boundary support:

```text
u <= b < v   or   v <= b < u.
```

It is the literal singular Cartier/Stokes boundary missing from the diagonal spectral landing.

### Proof

Expand

\[
 P_b(\kappa_2*g)-\kappa_2*(P_bg)
\]

under the convolution integral.  The two indicator factors give `(19)`.  Local normal
convergence of `(11)` permits the labelled expansion `(20)` on compactly supported smooth test
vectors, hence distributionally on the natural source core.  `QED`

## Corollary 5 — actual raw-source-to-Xi operator landing

Let `rho` be an Xi divisor in the open right half strip.  Since `Gamma_R(rho)` is nonzero, `(5)`
and `F(rho)=0` give `H(rho)=0`.  Consequently

\[
 \begin{aligned}
 [F]_{\rho,w}
 &=\frac{\Gamma_{\mathbb R}(w)H(w)}{w-\rho}\\
 &=\Gamma_{\mathbb R}(w)[H]_{\rho,w}.
 \end{aligned}
\tag{21}

The formalized completion landing therefore becomes

\[
 \boxed{
 [\xi]_{\rho,w}
 =M_2(w)[H]_{\rho,w}.}
\tag{22}

After the existing centered-coordinate unit phase is inserted, `(22)` says that convolution by
`kappa_2` sends the raw zero-divided co-Poisson source to the genuine completed-Xi first-divided
vector.  This is the correctly typed physical operator landing; neither divisor location nor a
same-fibre norm premise is used.

The reflected Gamma orientation has multiplier

\[
 M_2^\vee(w)=M_2(1-w).
\tag{23}

On the critical line it is complex conjugate to `M_2(w)`, so its logarithmic kernel is the
reflected real kernel

\[
 \kappa_2^\vee(u)=\kappa_2(-u).
\tag{24}

Thus both Gamma orientations and their full depth labels are explicit before any Xi fibre is
chosen.

## Consequence for the Route R current

For the raw zero-divided fixed source `v_rho`, the corpus already proves

\[
 h(v_\rho)=\frac1{1-\rho},
 \qquad
 h(Cv_\rho)=-\frac{\log2}{\rho},
\]

and hence

\[
 J_\rho=|h(v_\rho)|^2-|h(Cv_\rho)|^2.
\tag{25}
\]

Equations `(17)`--`(24)` now exhibit an actual source-side sign carrier: the two reflected
Gamma-sewn crossing operators have labelled negative collars.  What is not yet proved is the
restricted Stokes trace identity that transports their signed cross-boundary pairing to `(25)`.
This is a strictly smaller and correctly typed burden than constructing the completion,
constructing the commutator, or guessing a positive physical metric.

## Conjecture / hostile-attack loop

1. **Negative normal slope of `C_2` gives `J_rho <= 0`.**
   `[FAILED]`  The normal slope is height-only and makes the dressed current negative at every Xi
   divisor, including a hypothetical off-line divisor.  It masks the bare port.
2. **Forward/reflected sewing gives an independent sign.**
   `[FAILED — CONCLUSION LAUNDERING]`  The reflected lift is exactly the negative divided shift;
   the proposed sewing asserts `P_rho=-P_rho`.
3. **Zero-divided Sonin landing makes the shift source-orthogonal.**
   `[FAILED]`  Strict accretivity and formalized non-erasure prove the opposite.
4. **The rational multiplier itself gives a physical constant-head collar.**
   `[FAILED — TYPING ERROR]`  The physical source carries raw Mellin transform `H`, whereas `C_2`
   acts on the Gamma-completed transform `F`.  Ignoring `Gamma_R` silently moves the physical
   aperture to another representation.
5. **Sew Gamma before taking the commutator.**
   `[PROVED]`  Theorems 2 and 4 construct the resulting kernel and crossing operator.
6. **The sewn kernel is globally dissipative.**
   `[FAILED, WITH POSITIVE SURVIVOR]`  Formula `(17)` proves two positive flanks and one negative
   collar at every depth.  Global semidefiniteness is false; `(18c)` proves the collar nevertheless
   has an exact strict surplus in total mass.
7. **Strongest survivor.**
   `[PROVED]`  The actual raw-source-to-Xi completion is a coefficient-faithful, two-orientation
   dyadic family of explicit three-chamber kernels.  Its aperture commutator is the cross-boundary
   operator `(19)`, and the negative chamber has the same exact width `(18)` and strict mass
   surplus `(18c)` at every depth.  The scale-free criterion `(18f)` is sufficient to retain that
   sign after weighting by a source correlation.

## Corrected open core after the actual-source correlation audit

The follow-up card
`burnol-first-wall-cartier-residue-cancellation-law.md` proves that the proposed positive constant
plateau `(18f)` is **false** for the actual zero-divided source.  Its unique nonzero deep profile is
proportional to `exp(-r/2)`, and the factor `w-1` in the completed multiplier annihilates that
profile exactly.

The same follow-up constructs the surviving singular source coordinate before this annihilation.
For the two Fourier/Gamma orientations its residue difference lands exactly on

\[
 |h(v_\rho)|^2-|h(Cv_\rho)|^2=J_\rho.
\tag{26}
\]

Thus the remaining producer is not an asymptotic collar theorem after completion.  It is a
pre-completion singular Stokes/Cartier orientation law on the one `A=partial_u+1/2` null mode.
Any argument factoring through the completed kernel `(9)` has already erased the required physical
coefficient.

## Novelty and dependency audit

- Internal search located the spectral multiplier, exact Burnol-to-Xi landing, its normal slope,
  and the abstract open commutator, but no Gamma-sewn physical kernel `(9)`, three-chamber law
  `(17)`, negative-mass surplus `(18c)`, collar plateau criterion `(18f)`, crossing formula `(19)`,
  or raw-source operator landing `(22)`.
- Geometric series, the Gamma integral, convolution commutators, and elementary differentiation
  are classical ingredients.  No priority claim is made for them separately.  Candidate new
  content is their exact coefficient-faithful synthesis with the prime-two Burnol--Xi landing and
  fixed Route R aperture.
- Closed dependencies: formalized fixed-atom Mellin formula, nonvanishing of `Gamma_R` in the
  strip, coefficient-faithful `C_2` landing, and completed first-divided `L^2` membership.
- No RH, critical-line placement, source-dagger identity, same-fibre norm identity, or desired
  signed correlation theorem is assumed.

## Gates

- [x] 0 -> 1: source-pure statement and hostile attack
- [x] 1 -> 2: complete paper proof of `(3)`, `(9)`, `(17)`, `(18c)`, `(18g)`, `(19)`, and `(22)`
- [ ] 2 -> 3: formalize after current corpus refactor ends
- [x] construct restricted singular Stokes trace scalarization `(26)` on paper
- [x] classify and falsify two-orientation constant collar plateau `(18f)` on the actual source
- [x] prove exact Gamma annihilation of the stable actual-source collar profile
- [ ] prove pre-completion singular residue orientation
- [ ] RH

## Log

- 2026-08-08 — three shortcut conjectures failed; direct rational-collar conjecture caught as a
  representation-typing error; Gamma-sewn conjecture proved; explicit negative collar and exact
  fixed-aperture crossing operator promoted to Stage 2.
