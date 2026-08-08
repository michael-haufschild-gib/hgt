# Burnol current as a folded prime-tail Laplace port and the rank-one double-mode obstruction

- **ID:** `burnol-prime-tail-folded-mode-witt-bridge`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / CROSS-ROUTE SOURCE BRIDGE / FINITE HERMITICITY REDUCTION
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`
- **Route:** R, using the prime-tail reflection fold and coefficient-generated Stokes Witt law
- **Parents:**
  - `burnol-gamma-bockstein-first-wall-extraction-law.md`;
  - `../other/prime-tail-reflection-folded-second-order-resolvent.md`;
  - `../../../4-publication-ready/polarized-stokes-microlocal-witt-law/main.tex`.
- **Lean:** deliberately deferred while `HTGeometry` and `RHTower` are being refactored.

## 1. Result

Put

\[
 c=\frac12,\qquad \ell=\log 2,\qquad
 \lambda=\rho-\frac12,\qquad \mu=\lambda^2.
 \tag{1}
\]

Let `m>=1` be the multiplicity of an Xi divisor point and let

\[
 q_m=2\pi i m\ne0.
 \tag{2}
\]

The reflection-folded prime-tail construction gives the two source-pointed monodromy modes

\[
 E_{\rho,m}(L)=q_m\cosh(\lambda L),\qquad
 O_{\rho,m}(L)=q_m\frac{\sinh(\lambda L)}{\lambda},
 \tag{3}
\]

where the second expression has value `q_m L` at `lambda=0`. They solve the same equation

\[
 E''=\mu E,\qquad O''=\mu O,
 \tag{4}
\]

and carry independent source Cauchy data

\[
 (E(0),E'(0))=(q_m,0),\qquad
 (O(0),O'(0))=(0,q_m).
 \tag{5}
\]

For `0<Re rho<1`, define the fixed source Laplace port

\[
 \mathcal L_c f=\int_0^\infty e^{-cL}f(L)\,dL.
 \tag{6}
\]

The first theorem identifies the already-constructed Burnol current with this new global source
doublet.

### Theorem 1 — exact folded-mode landing on the Burnol current

For every `rho` in the open critical strip,

\[
 \begin{aligned}
 \mathcal L_cE_{\rho,m}
   &=q_m\frac{c}{c^2-\mu},\\
 \mathcal L_cO_{\rho,m}
   &=q_m\frac1{c^2-\mu},
 \end{aligned}
 \tag{7}
\]

and hence

\[
 \boxed{
 \begin{aligned}
  \mathcal L_c(E_{\rho,m}+\lambda O_{\rho,m})
    &=\frac{q_m}{1-\rho},\\
  \mathcal L_c(E_{\rho,m}-\lambda O_{\rho,m})
    &=\frac{q_m}{\rho}.
 \end{aligned}}
 \tag{8}
\]

If

\[
 a_\rho=\frac1{1-\rho},\qquad
 b_\rho=-\frac{\ell}{\rho}
 \tag{9}
\]

are the two Burnol first-wall head coefficients, then

\[
 \boxed{
 \begin{aligned}
 a_\rho
   &=q_m^{-1}\mathcal L_c(E_{\rho,m}+\lambda O_{\rho,m}),\\
 b_\rho
   &=-\ell q_m^{-1}\mathcal L_c(E_{\rho,m}-\lambda O_{\rho,m}),
 \end{aligned}}
 \tag{10}
\]

and the explicit Route-R current is the fixed Lorentz-port value

\[
 \boxed{
 J_\rho
 =\frac1{|q_m|^2}
 \left(
  \left|\mathcal L_c(E_{\rho,m}+\lambda O_{\rho,m})\right|^2
  -\ell^2
  \left|\mathcal L_c(E_{\rho,m}-\lambda O_{\rho,m})\right|^2
 \right).}
 \tag{11}
\]

Thus the singular Gamma--Bockstein residue and the prime-tail monodromy are not merely two
RH-equivalent detectors. They are two presentations of the same physical scalar port: the former
is a translated-wall residue, while the latter is a fixed Laplace resolvent reading of the global
reflection-folded source mode.

### Proof

Because `|Re lambda|<c`, both exponentials in

\[
 E+\lambda O=q_me^{\lambda L},\qquad
 E-\lambda O=q_me^{-\lambda L}
 \tag{12}
\]

are integrable against `e^(-cL)`. Therefore

\[
 \mathcal L_c(E+\lambda O)=\frac{q_m}{c-\lambda},\qquad
 \mathcal L_c(E-\lambda O)=\frac{q_m}{c+\lambda}.
 \tag{13}
\]

Since `c-lambda=1-rho` and `c+lambda=rho`, this is `(8)`. Half-sum and the divided half-difference
give `(7)`, including the removable value at `lambda=0`. Equations `(9)`--`(11)` follow by
substitution. QED.

## 2. Exact Cayley orientation

The quotient of the two unweighted Laplace readings is

\[
 \boxed{
 \frac{\mathcal L_c(E+\lambda O)}
      {\mathcal L_c(E-\lambda O)}
 =\frac{c+\lambda}{c-\lambda}
 =\frac{\rho}{1-\rho}.}
 \tag{14}
\]

This is the Cayley transform of the centered divisor coordinate. Consequently

\[
 \Re\rho>\frac12
 \quad\Longrightarrow\quad
 \left|\frac{\mathcal L_c(E+\lambda O)}
              {\mathcal L_c(E-\lambda O)}\right|>1>\ell,
 \tag{15}
\]

and `(11)` gives `J_rho>0` immediately. This recovers the Lean-proved hard obstruction from the
global prime-tail mode and explains its direction: the right-half branch is the expansive side of
the centered Cayley transform. A positive Laplace or Poisson estimate cannot reverse this sign.

Equation `(14)` is also a falsifier. Any proposed source-dagger comparison whose scalar action is
only this fixed Laplace port necessarily reproduces the positive right-half gain. The missing
arithmetic input must act before, or nontrivially on, the two-dimensional Cauchy doublet; it cannot
be a scalar contractive estimate applied after `(10)`.

## 3. Rank-one double-mode obstruction

The new bridge also exposes a smaller source producer than full limiting absorption.

Let `V` be a complex vector space with Hermitian form `[.,.]`. Write `w(V)` for the largest
dimension of a totally isotropic subspace, meaning a subspace `W` such that

\[
 [x,y]=0\qquad(x,y\in W).
 \tag{16}
\]

Every Hermitian complexification of a coefficient-generated Stokes form in the finite, affine, or
Lorentz chamber satisfies

\[
 w(V)\le \operatorname{ind}^-[V]+\dim\operatorname{Rad}[V]\le1.
 \tag{17}
\]

### Theorem 2 — two source Cauchy modes force spectral reality in one Stokes port

Let `A` be a linear operator on `V` that is Hermitian for `[.,.]` on its domain:

\[
 [Ax,y]=[x,Ay].
 \tag{18}
\]

Assume `w(V)<=1`. Suppose there is a linear map

\[
 T_\rho:\operatorname{span}_{\mathbb C}\{E_{\rho,m},O_{\rho,m}\}
       \longrightarrow\operatorname{Dom}A
 \tag{19}
\]

which is injective and intertwines the folded source operator:

\[
 A T_\rho f=T_\rho(f'')
 \qquad
 (f\in\operatorname{span}\{E_{\rho,m},O_{\rho,m}\}).
 \tag{20}
\]

Then

\[
\boxed{\mu_\rho=(\rho-\frac12)^2\in\mathbb R.}
 \tag{21}
\]

If `rho` is a nonreal point of the open critical strip, `(21)` forces

\[
 \boxed{\Re\rho=\frac12.}
 \tag{22}
\]

### Proof

By `(4)` and `(20)`, both `T E` and `T O` are `A`-eigenvectors with eigenvalue `mu`. Suppose
`mu` is nonreal. For any two vectors `x,y` in their span, Hermiticity gives

\[
 \mu[x,y]=[Ax,y]=[x,Ay]=\overline\mu[x,y].
 \tag{23}
\]

Hence `[x,y]=0`. Equations `(5)` and `q_m!=0` make `E,O` linearly independent, and injectivity of
`T` makes their image a two-dimensional totally isotropic subspace. This contradicts `w(V)<=1`.
Therefore `mu` is real.

Write `lambda=u+iv`. Reality of `lambda^2` gives `2uv=0`. A nonreal `rho` has `v!=0`, hence
`u=0`, which is `(22)`. QED.

## 4. Route-R consequence

Theorem 2 changes the producer burden. A full self-adjoint Hilbert realization, a global GNS
comparison, and resolvent-stable limiting absorption are sufficient but no longer necessary for
this lane. It suffices to construct, from pre-divisor Euler--Gamma--Stokes data, the finite
comparison `(19)`--`(20)` with the following exact properties:

1. both source-fixed Cauchy modes `(3)` are retained;
2. their independent data `(5)` are not codiagonalized to one scalar;
3. the target form is the Hermitian complexification of the existing coefficient-generated
   one-port Stokes polarization;
4. the folded operator is formally Hermitian on their image;
5. no divisor location or `J_rho` sign is used to define the map.

Call this source statement

`ROUTE_R_FOLDED_CAUCHY_STOKES_HERMITICITY`.

If it holds at every Xi divisor, Theorem 2 excludes every right-half divisor. Therefore the
original Route-R target

\[
 \forall\rho\ \bigl(\tfrac12<\Re\rho<1\Longrightarrow J_\rho\le0\bigr)
 \tag{24}
\]

follows without trying to reverse the already-proved strict inequality `J_rho>0`: the antecedent
has been independently made impossible by a pre-scalar two-mode source law. Functional-equation
reflection then gives RH.

This is a strict reduction, not a proof of the missing comparison. Existing organs do not yet
compose to `(19)`:

- the prime-tail fold supplies `E`, `O`, their Cauchy data, and the common `mu`;
- the Stokes--microlocal theorem supplies the one-port Witt bound;
- the Burnol Gamma--Bockstein theorem supplies the physical Laplace marginal `(11)`;
- no current theorem gives an injective, operator-intertwining map from the folded Cauchy doublet
  to the same coefficient-generated Hermitian Stokes carrier.

The remaining map is smaller than the former full physical comparison but still RH-bearing. It
must be created from literal source incidence.

## 5. Heavy conjecture / proof-or-failure loop

1. **Diagonal Poisson coercivity should force inverse-completed jets into `ell2`.**
   `[FAILED]` The equation `partial_y^2 X=DX` and its flux are diagonal and commute with physical
   gain. They propagate the already-known entrance wall but do not suppress it.
2. **Reflected Poisson Wronskians annihilate the first-wall coefficient.**
   `[FAILED]` Their cofinite term is the nonzero harmonic `1/p` boundary charge. Reflection
   retains the singular class rather than killing it.
3. **The coefficient-generated Witt index directly signs `J_rho`.**
   `[FAILED]` The Witt form is on finite coefficient charges; `J_rho` is on a singular physical
   Laplace marginal. No canonical Hermitian intertwiner between them was present.
4. **The two folded modes may remove that missing comparison.**
   `[PARTIAL SUCCESS]` They give a two-dimensional source Cauchy space at one common `mu`, but
   Cauchy trace by itself is not spectral or Stokes landing.
5. **Burnol heads are unrelated to the folded source modes.**
   `[FAILED, POSITIVE SURVIVOR]` Equations `(8)`--`(11)` give their exact fixed Laplace landing.
6. **A scalar positive Laplace estimate can orient the result.**
   `[FAILED SHARPLY]` The Cayley identity `(14)` forces the opposite strict direction throughout
   the right half-strip.
7. **A nonnegative transverse Gamma family signs its first Bockstein derivative.**
   `[FAILED]` A norm square whose zeroth-order vector vanishes has zero first derivative. The
   signed Bockstein is a linear cross-boundary reading, not the derivative of a positive scalar
   minimum. Squaring loses its orientation.
8. **Full Hilbert self-adjoint limiting absorption remains necessary.**
   `[FAILED, POSITIVE SURVIVOR]` The finite algebraic Theorem 2 needs only a Hermitian
   intertwiner on the two source modes plus Witt index one.
9. **One retained scalar mode is enough for the Witt contradiction.**
   `[FAILED]` A one-port Lorentz carrier may contain one neutral nonreal eigenvector. Retention of
   both independent Dirichlet and Neumann source modes is load-bearing.
10. **Existing one-dimensional oriented source cohomology automatically retains both modes.**
    `[FAILED]` It retains the common monodromy coefficient but may codiagonalize the two Cauchy
    slots. Cauchy-faithful injectivity is new content and cannot be inferred from period one.
11. **Strongest survivor.**
    `[PAPER-PROVED]` The physical Route-R current is the Lorentzian fixed-Laplace shadow of the
    global folded prime-tail doublet, and any Cauchy-faithful Hermitian landing of that doublet in
    the existing one-port Stokes carrier forces critical-line placement.

## 6. Anti-theatre audit

- Every object in `(1)`--`(13)` is explicit and already source-defined before the new comparison.
- The Laplace integrals converge in the whole open critical strip; no analytic continuation is
  hidden in Theorem 1.
- Multiplicity is retained through the nonzero coefficient `q_m` and cancels only after the exact
  physical landing is proved.
- Theorem 2 is unconditional finite Hermitian linear algebra. It does not assume RH, critical-line
  placement, `J_rho<=0`, source-dagger isometry, or same-fibre norm conservation.
- No claim is made that the comparison `(19)` exists. Naming it without constructing it would not
  close Route R.
- The result does not relabel the first-wall criterion: it proves an explicit cross-presentation
  identity `(11)` and replaces an infinite-dimensional realization demand by a two-mode
  coefficient-faithful Hermiticity demand.
- External novelty was not audited in this pass. The new claim is internal corpus synthesis, not
  a priority claim.

## Gates

- [x] exact prime-tail folded modes and independent Cauchy data
- [x] exact fixed-Laplace landing to both Burnol head coefficients
- [x] exact current identity `(11)`
- [x] Cayley-orientation falsifier
- [x] rank-one double-mode Hermiticity theorem
- [x] full-resolvent requirement reduced to finite two-mode comparison
- [ ] construct `ROUTE_R_FOLDED_CAUCHY_STOKES_HERMITICITY` from pre-divisor source incidence
- [ ] formalize after corpus refactor
- [ ] RH

## Log

- 2026-08-08 — identified the Burnol first-wall current with the fixed Laplace port of the
  reflection-folded prime-tail monodromy doublet; proved the rank-one two-mode Hermiticity
  obstruction and reduced full spectral landing to one finite Cauchy-faithful source comparison.
