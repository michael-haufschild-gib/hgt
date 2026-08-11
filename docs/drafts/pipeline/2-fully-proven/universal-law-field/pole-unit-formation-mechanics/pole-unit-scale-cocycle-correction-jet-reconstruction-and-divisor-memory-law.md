# Pole-unit scale cocycle, correction-jet reconstruction, and divisor-memory law

- **ID:** ULF-PUFM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / COMPLETED FORMATION MECHANICS
- **Statement:** A meromorphic formation near a pole splits into a universal polar response and an
  exact scale cocycle; the logarithmic correction tower on one nontrivial scale ray reconstructs
  the regular unit germ, controls the complete critical-clock moment hierarchy, and remembers the
  divisor after analytic continuation, while every finite correction depth remains divisor-blind.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [SOURCE-INDEPENDENT CORE]`
  `[EXACT COCYCLE] [JOINT RECONSTRUCTION] [FOUR-ORGAN FUSION] [FINITE-DEPTH NO-GO]`
  `[EULER-SHELL SPECIALIZATION] [LEAN-CERTIFIED ALGEBRAIC CORE] [NOT RH]`

## 1. Setup

Let `r>=1`, let `R>0`, and let `U` be holomorphic and nonvanishing on the disc
`D_R={z:|z|<R}`.  Assume `U(0) != 0`.  On the punctured disc define

\[
 Z(z)=z^{-r}U(z).
 \tag{PUF.1}
\]

For nonzero `epsilon,w` with `epsilon,epsilon w in D_R`, put

\[
 B_\epsilon(w)=\frac{Z(\epsilon w)}{Z(\epsilon)},\qquad
 C_\epsilon(w)=w^rB_\epsilon(w).
 \tag{PUF.2}
\]

The first response `B` retains the pole.  The corrected response `C` isolates the regular
constitutive unit.

## 2. Exact formation and conservation

### Theorem 2.1 — polar splitting and scale cocycle

Whenever all displayed terms are defined,

\[
 \boxed{B_\epsilon(w)=w^{-r}\frac{U(\epsilon w)}{U(\epsilon)},
 \qquad C_\epsilon(w)=\frac{U(\epsilon w)}{U(\epsilon)}.}
 \tag{PUF.3}
\]

For successive relative scales `u,v`,

\[
 \boxed{
 B_\epsilon(uv)=B_\epsilon(u)B_{\epsilon u}(v),\qquad
 C_\epsilon(uv)=C_\epsilon(u)C_{\epsilon u}(v).}
 \tag{PUF.4}
\]

Moreover, replacing `U` by `aU` for any nonzero scalar `a` leaves `B` and `C` unchanged.

### Proof

Equation `(PUF.3)` is cancellation of `epsilon^{-r}` in `(PUF.1)`.  For `(PUF.4)`, insert the
intermediate value `Z(epsilon u)`:

\[
 \frac{Z(\epsilon uv)}{Z(\epsilon)}
 =\frac{Z(\epsilon uv)}{Z(\epsilon u)}
  \frac{Z(\epsilon u)}{Z(\epsilon)}.
\]

The corrected identity follows identically with `U`.  Scalar gauge cancellation is immediate.
QED.

This is the conservation law missing from a bare list of response objects: direct and iterated
formation agree exactly, with the base scale transported in the second step.

## 3. Ghost linearization and one-ray reconstruction

Since `D_R` is simply connected and `U` is nonvanishing, there is a unique holomorphic `L` with

\[
 L(0)=0,\qquad U(z)=U(0)e^{L(z)}.
 \tag{PUF.5}
\]

Write its Taylor expansion

\[
 L(z)=\sum_{k\ge1}\ell_k z^k.
 \tag{PUF.6}
\]

### Theorem 3.1 — exact correction-jet identity

On every smaller disc on which the series converges,

\[
 \boxed{
 \log_C C_\epsilon(w)
 :=L(\epsilon w)-L(\epsilon)
 =\sum_{k\ge1}\ell_k\epsilon^k(w^k-1).}
 \tag{PUF.7}
\]

Here `log_C` denotes the distinguished logarithm supplied by `(PUF.5)`, not an arbitrary
principal branch.

Fix one real `q>1`.  Then every denominator `q^k-1` is nonzero, and

\[
 \boxed{
 \ell_k=\frac{[\epsilon^k]\log_C C_\epsilon(q)}{q^k-1}.
 \tag{PUF.8}
\]

Consequently one nontrivial scale ray reconstructs `L`, hence reconstructs `U/U(0)`.  Marking the
residue `U(0)` reconstructs the full meromorphic germ `Z`.

### Proof

Equation `(PUF.3)` and `(PUF.5)` give

\[
 C_\epsilon(w)=e^{L(\epsilon w)-L(\epsilon)}.
\]

Substitute `(PUF.6)` and subtract termwise on a smaller closed polydisc to obtain `(PUF.7)`.
Coefficient extraction at `w=q` gives `(PUF.8)`.  The Taylor series determines `L` as a germ;
exponentiation and the marked value `U(0)` determine `U`, and `(PUF.1)` determines `Z`. QED.

## 4. Probability, phase, and Hankel fusion at the wall

Assume now that `Z(sigma_0+epsilon)` is the Mellin transform of a nonnegative source for every
small real `epsilon>0`, and that the pole coordinate in `(PUF.1)` is
`z=s-sigma_0`.  Under the normalized Gibbs law, let

\[
 Y_\epsilon=\epsilon X
 \tag{PUF.9}
\]

be the rescaled logarithmic clock.  Its Laplace transform is

\[
 \mathbb E_\epsilon e^{-tY_\epsilon}
 =B_\epsilon(1+t)
 =(1+t)^{-r}\frac{U(\epsilon(1+t))}{U(\epsilon)}.
 \tag{PUF.10}
\]

### Theorem 4.1 — universal Gamma base with complete constitutive corrections

Locally uniformly for `t` near zero,

\[
 \boxed{B_\epsilon(1+t)\longrightarrow(1+t)^{-r}.}
 \tag{PUF.11}
\]

Hence `Y_epsilon` converges in law to `Gamma(r,1)`.  Its characteristic functions converge to
`(1-it)^(-r)`, and for every `n>=0`,

\[
 \boxed{\mathbb E(Y_\epsilon^n)\longrightarrow(r)_n
 =r(r+1)\cdots(r+n-1).}
 \tag{PUF.12}
\]

Therefore every finite Hankel moment matrix converges entrywise to

\[
 \boxed{[(r)_{i+j}]_{0\le i,j<N},}
 \tag{PUF.13}
\]

the positive-definite Gamma moment matrix.

More strongly, the complete correction law is

\[
 \boxed{
 \log\mathbb E_\epsilon e^{-tY_\epsilon}
 =-r\log(1+t)
  +\sum_{k\ge1}\ell_k\epsilon^k((1+t)^k-1).}
 \tag{PUF.14}
\]

Thus probability, phase, Hankel moments, and the analytic unit are generated by one scale
cocycle.  The universal Gamma law is only its grade-zero shadow; the coefficients `ell_k` are the
constitutive grades.

### Proof

The quotient of units in `(PUF.10)` tends locally uniformly to one.  This proves `(PUF.11)`.
The limit is the Laplace transform of `Gamma(r,1)`; the continuity theorem gives weak convergence.
Putting `t=-iu` gives the characteristic-function limit.  Local uniform holomorphic convergence
permits differentiation of every order at zero, proving `(PUF.12)`.  Equation `(PUF.13)` follows
entrywise.  Its strict positivity is

\[
 \int_0^\infty |p(x)|^2\frac{x^{r-1}e^{-x}}{\Gamma(r)}\,dx>0
\]

for every nonzero polynomial `p`.  Finally `(PUF.14)` is `(PUF.7)` with `w=1+t`. QED.

Two existing corpus results are recovered but not rediscovered: the simple-pole `Exp(1)` limit
is `r=1`, and the critical-clock blindness theorem says precisely that discarding every
`ell_k` destroys divisor memory.

## 5. Fourth-organ theorem: complete divisor memory and finite-depth blindness

### Theorem 5.1 — complete formation memory

Let `Omega` be a connected continuation domain on which two regular units `U,V` are holomorphic.
If they have the same marked value at zero and the same one-ray correction coefficients in
`(PUF.8)` for every `k`, then `U=V` first as germs and then throughout `Omega`.  Consequently their
meromorphic sources `z^{-r}U` and `z^{-r}V` have the same divisor on `Omega\{0}`.

### Proof

Equation `(PUF.8)` gives equality of every Taylor coefficient of the distinguished logarithms.
Thus the logarithms, units, and sources agree near zero.  The identity theorem propagates equality
through the connected common continuation domain. QED.

### Theorem 5.2 — no finite correction depth determines the divisor

Fix `N>=0`.  Choose `a != 0` so small that the circle `|z|=|a|` lies in the zero-free disc, and
define

\[
 V_N(z)=U(z)\left(1-(z/a)^{N+1}\right).
 \tag{PUF.15}
\]

Then `V_N(0)=U(0)`, the first `N` logarithmic correction coefficients of `V_N` equal those of
`U`, but `V_N` has the `N+1` additional zeros

\[
 z=a\omega,\qquad \omega^{N+1}=1.
 \tag{PUF.16}
\]

### Proof

Near zero,

\[
 \log(V_N/U)=\log(1-(z/a)^{N+1})
\]

starts in degree `N+1`.  Hence all logarithmic jets through order `N` agree.  The added factor
vanishes exactly at `(PUF.16)`, while `U` does not vanish there. QED.

Theorem 5.2 is an analytic-category no-go.  It does not claim that every `V_N` is the Mellin
transform of a positive measure.  Its conclusion is exactly what it proves: finite local formation
data cannot determine a continued divisor.

## 6. Euler-shell specialization and new boundary statistics

For the high-exponent shell with `m>=12`, write `epsilon=sigma-1` and

\[
 U_m(z)=\operatorname{shellResidueUnit}_m(1+z)
 =G(1+z)H_m(1+z),
 \tag{PUF.17}
\]

where `G(s)=(s-1)zeta(s)` is the entire zeta residue unit.  Then `U_m(0)=H_m(1)>0`, and

\[
 \boxed{
 \frac{S_m(1+\epsilon w)}{S_m(1+\epsilon)}
 =w^{-1}\frac{U_m(\epsilon w)}{U_m(\epsilon)}.}
 \tag{PUF.18}
\]

Let

\[
 \log(U_m(z)/U_m(0))=\sum_{k\ge1}\ell_{m,k}z^k.
 \tag{PUF.19}
\]

The first constitutive coefficient is

\[
 \boxed{
 \ell_{m,1}=\gamma+\frac{H_m'(1)}{H_m(1)},}
 \tag{PUF.20}
\]

where `gamma` is Euler's constant.  Therefore, for the critical shell clock
`Y_epsilon=epsilon log n`,

\[
 \boxed{
 \mathbb E Y_\epsilon=1-\ell_{m,1}\epsilon+O(\epsilon^2),\qquad
 \operatorname{Var}(Y_\epsilon)=1+2\ell_{m,2}\epsilon^2+O(\epsilon^3).}
 \tag{PUF.21}
\]

This is the withheld fourth-organ prediction: all high-exponent shells coalesce to the same
`Exp(1)` observer at leading order, while their first boundary splitting is the logarithmic
derivative of the literal shell multiplier.  Higher splitting orders are exactly the correction
jets `(PUF.19)`.

### Proof

Equation `(PUF.18)` is `(PUF.3)` applied to the already-proved shell pole factorization.
Since `G(1)=1` and `G'(1)=gamma`, logarithmic differentiation gives `(PUF.20)`.  Differentiate
the cumulant identity `(PUF.14)` once and twice at `t=0`; the first derivative of a Laplace
cumulant is minus the mean and the second is the variance. QED.

## 7. What this changes about RH

For `m>=12`, `H_m` is zero-free on `Re(s)>1/2`.  Therefore the continued unit `U_m(s-1)` has,
away from the pole, exactly the zeta divisor in that half-plane.  The complete correction tower
is consequently a coefficient-faithful pre-zero encoding of every strict-right zeta zero.

This closes a carrier problem and opens the genuine selector problem:

> derive from source operations a reflected, completely order-preserving admission law for the
> full scale cocycle—not only its universal Gamma shadow—and show that the law survives analytic
> continuation of the reconstructed unit.

If such a law forces the reconstructed unit to be zero-free on `Re(s)>1/2`, reflection gives RH.
No such order law is proved here.  Positive Mellin coefficients on `s>1` do not suffice: the
explicit critical-clock blind witness is a positive source with an off-critical zero.

## 8. Hostile audit

1. **Not a new Gamma-limit claim.**  Simple-pole critical-clock universality is already formal in
   the corpus and is classical Tauberian/mod-phi territory.
2. **Not a curvature metaphor.**  `(PUF.4)` is a typed composition law; `(PUF.8)` is an explicit
   inverse; `(PUF.14)` is a joint probability/analytic identity.
3. **Not finite-jet selection.**  Theorem 5.2 proves exact finite-depth blindness.
4. **Not positivity selection.**  Positivity on the convergent real axis neither supplies the
   continuation nor orients its zeros.
5. **Not automatic global reconstruction.**  The germ determines a continuation only where a
   common connected continuation exists.
6. **Not yet reflection-marked.**  The theorem reconstructs the divisor but does not force its
   symmetry fixed locus.  That is the next field law.

## 9. Parent mathematics

The polar factorization and Taylor expansion are classical complex analysis.  Critical-clock
universality belongs to Laplace/Tauberian theory; mod-phi convergence is a nearby probabilistic
language (Delbaen--Kowalski--Nikeghbali, <https://arxiv.org/abs/1107.5657>).  The exact HGT use is
the graded formation interpretation and its coefficient-faithful Euler-shell/divisor
specialization.  No priority claim is made for the elementary analytic identities.

## 10. Formalization boundary

Future Lean module:

`formal/GaloisForLFunctions/HTGeometry/PoleUnitFormationMechanics.lean`.

Dependency-closed core to certify:

1. polar splitting and scale-cocycle composition;
2. scalar-gauge invariance;
3. finite logarithmic correction polynomial and coefficient reconstruction;
4. exact exponential realization of a finite correction packet;
5. finite-depth divisor perturbation polynomial.

The infinite holomorphic logarithm, weak convergence, and Euler-shell asymptotics should be added
only after the algebraic core is certified against the current toolchain.

## 11. Gates

- [x] exact scale cocycle proved
- [x] one-ray correction-jet reconstruction proved
- [x] probability/phase/Hankel fusion proved
- [x] complete divisor-memory theorem proved
- [x] finite-depth divisor no-go proved
- [x] Euler-shell boundary-splitting theorem proved
- [x] RH claim blocked at reflected complete-order continuation
- [x] hostile dependency and scope reread
- [x] Lean certification of algebraic core and Stage-3 promotion

## Log

- 2026-08-11 — created after recognizing that the already-formal universal `Exp(1)` critical
  clock is grade zero and provably divisor-blind; the correction cocycle is the first retained
  constitutive layer.
- 2026-08-11 — exact cocycle, scalar-gauge invariance, finite correction ghost law, one-scale
  reconstruction, exponential realization, and finite-depth divisor blindness compiled in Lean.
