# Prime--archimedean Bernstein half-order Pringsheim singularity

- **ID:** `prime-arch-bernstein-half-order-pringsheim-singularity`
- **Stage:** 3-formalized
- **Type:** exact local branch decomposition / top-down RH bridge / value-relation consequence
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** paper theorem; its divisor-pencil, maximal-packet, phase-rigidity, exact-radius,
  and Gutzmer parents are formalized, but the finite-packet branch decomposition below is not

## Statement

Write

\[
 R=\texttt{primeArchEndpointHausdorffRadius},\qquad
 u_q=\frac{\texttt{xiZeroCopyReciprocalSquare}(q)}R,
 \qquad c_q=\texttt{xiZeroCopyReciprocalSquare}(q),
\]

and

\[
 P_n(w)=\sum_q c_q(1-u_q+u_qw)^n,
 \qquad
 \Pi_n=\frac1{2\pi}\int_0^{2\pi}|P_n(e^{i\phi})|^2\,d\phi.
                                                               \tag{1}
\]

The formal prime--Gamma/Xi Bernstein-pencil identity and finite Parseval theorem identify this
`Pi_n` with `primeArchEndpointBernsteinPurity(n)`.

Assume RH is false.  Let

\[
 B=\max_q\bigl(|u_q|+|1-u_q|\bigr)>1.                  \tag{2}
\]

The live Lean corpus proves that this maximum is attained.  Let `U_B` be the finite set of
distinct normalized coordinates attaining `(2)`, and put

\[
 C_u=\sum_{q:u_q=u}c_q.                                 \tag{3}
\]

Then every `C_u` is nonzero and

\[
 B_-(u)=|u|-|1-u|.
\]

There are functions `H` and `A`, holomorphic on a neighborhood of `R_A=B^{-2}`, such that the
susceptibility germ admits the exact continuation

\[
 \boxed{
 \chi(t)=H(t)+\frac{A(t)}{\sqrt{1-B^2t}}
 }                                                       \tag{4}
\]

on a slit neighborhood reached from the interval `0<t<R_A`, where

\[
 \boxed{
 A(t)=\sum_{u\in U_B}
 \frac{|C_u|^2}{\sqrt{1-B_-(u)^2t}}
 }
                                                               \tag{5}
\]

and all square-root branches are positive on the left real interval.  In particular,

\[
 \boxed{
 A(R_A)=
 \sum_{u\in U_B}\frac{|C_u|^2B}{2\sqrt{|u|\,|1-u|}}>0.
 }                                                       \tag{6}
\]

Thus `R_A` is a genuine square-root branch point of the complete susceptibility: its local
half-order term has nonzero monodromy and cannot be cancelled by the holomorphic remainder.

As coefficient and radial corollaries,

\[
 \boxed{
 \Pi_n\sim
 \frac{B^{2n}}{\sqrt n}
 \sum_{u\in U_B}
 \frac{|C_u|^2B}{2\sqrt{\pi |u|\,|1-u|}}.
 }                                                       \tag{7}
\]

Consequently, for the positive susceptibility

\[
 \chi(t)=\sum_{n\ge0}\Pi_nt^n,
 \qquad R_A=B^{-2},                                     \tag{8}
\]

one has the exact half-order radial law

\[
 \boxed{
 \lim_{t\uparrow R_A}
 \sqrt{1-B^2t}\,\chi(t)
 =\sum_{u\in U_B}
 \frac{|C_u|^2B}{2\sqrt{|u|\,|1-u|}}>0.
 }                                                       \tag{9}
\]

In particular, the susceptibility germ has no single-valued meromorphic continuation through
`t=R_A`.  This strengthens the previously available conclusion that `R_A` is merely a singular
point.

## Exact finite-packet branch decomposition

The formal corpus supplies

\[
 u_q\longrightarrow0\quad\text{cofinally},\qquad
 \sum_q|c_q|<\infty.                                    \tag{10}
\]

Hence `|u_q|+|1-u_q| -> 1`.  Since `B>1`, only finitely many coordinates attain `B`, and there is
a uniform `beta<B` such that every nonmaximal coordinate has affine amplitude at most `beta`.
Indeed, all but finitely many amplitudes lie below `(1+B)/2`, and the remaining nonmaximal set is
finite.

Group the maximal indices by their common coordinate.  Because `c_q=Ru_q`, each fibre sum is

\[
 C_u=R u\,\#\{q:u_q=u\}\ne0.                            \tag{11}
\]

This includes both exact multiplicity copies and the functional-equation partner, which has the
same reciprocal-square coordinate; they add rather than cancel.  Therefore, uniformly for
`|w|=1`,

\[
 P_n(w)=\sum_{u\in U_B}C_u(1-u+uw)^n+O(\beta^n).         \tag{12}
\]

Expand the Gutzmer square before summing in `n`.  For a pair of source coordinates the exact
double-source kernel is

\[
 K(t;u,\bar v)=
 \sum_{n\ge0}t^n\operatorname{CT}_w
 \bigl((1-u+uw)(1-\bar v+\bar v w^{-1})\bigr)^n.
                                                               \tag{13}
\]

Absolute summability of the source weights permits coefficientwise expansion near the origin:

\[
 \chi(t)=\sum_{q,r}c_q\overline{c_r}\,K(t;u_q,\overline{u_r}).
                                                               \tag{14}
\]

For a diagonal coordinate, the reflected Legendre factorization already proved on paper gives

\[
 K(t;u,\bar u)=
 \frac1{\sqrt{(1-B^2t)(1-B_-(u)^2t)}}.                  \tag{15}
\]

After grouping equal maximal coordinates in `(14)`, their complete diagonal contribution is therefore
exactly the second term of `(4)` with `A` as in `(5)`.

It remains to prove that everything else is holomorphic past `R_A`.  A term containing a
nonmaximal coordinate has affine product amplitude at most `B beta<B^2`.  For two distinct
maximal coordinates, the formal ellipse-rigidity theorem gives distinct maximizing phases, hence

\[
 \max_{|w|=1}
 |(1-u+uw)(1-\bar v+\bar v w^{-1})|<B^2.                \tag{16}
\]

There are only finitely many maximal coordinates, so the strict inequalities in `(16)` have a
uniform gap.  The coefficient of `t^n` in `(13)` is bounded by the corresponding product
amplitude to the power `n`.  Together with `sum_q |c_q|<infinity`, this makes the sum of all
nonmaximal and mixed-maximal pairs normally convergent on a disk of radius strictly larger than
`R_A`.  Call its holomorphic sum `H`.

Finally, `|B_-(u)|<B` for every off-line maximal coordinate, so every second square root in `(15)`
is holomorphic near `R_A`.  Since

\[
 1-\frac{B_-(u)^2}{B^2}
 =\frac{4|u|\,|1-u|}{B^2},                              \tag{17}
\]

evaluation of `(5)` at `R_A` gives `(6)`.  This proves the exact local decomposition and its
nonzero square-root monodromy.

## Coefficient asymptotic

For a fixed nonreal `u`, set `a=|1-u|` and `b=|u|`.  The affine factor has one maximizing phase
`phi_u`, and

\[
 |1-u+ue^{i\phi}|^2
 =a^2+b^2+2ab\cos(\phi-\phi_u).                         \tag{18}
\]

Its maximum is `(a+b)^2=B^2`, and the maximum is nondegenerate:

\[
 \log |1-u+ue^{i(\phi_u+x)}|^2
 =2\log B-\frac{ab}{B^2}x^2+O(x^4).                    \tag{19}
\]

Laplace's method therefore gives

\[
 \frac1{2\pi}\int_0^{2\pi}|1-u+ue^{i\phi}|^{2n}\,d\phi
 \sim \frac{B^{2n}B}{2\sqrt{\pi ab\,n}}.               \tag{20}
\]

Distinct elements of `U_B` have distinct maximizing phases.  The formal ellipse-rigidity theorem
says that equal amplitude and equal phase force either `v=u` or `v=1-conj(u)`.  The second option
is excluded by the formal strict quarter-disk bound on every off-line normalized coordinate.
Thus for distinct `u,v` in `U_B`, compactness gives

\[
 \max_{|w|=1}
 |(1-u+uw)(1-\bar v+\bar v w^{-1})|<B^2.               \tag{21}
\]

All mixed maximal terms are consequently exponentially smaller than `B^(2n)/sqrt(n)`.  The
uniform remainder in `(12)` is smaller for the same reason.  Applying `(20)` to the finitely many
diagonal packets proves `(7)`.  Every displayed leading coefficient is positive by `(11)`.

## Abelian transfer and nonmeromorphicity

After setting `x=B^2t`, equation `(7)` reduces `(8)` to the standard Abelian asymptotic

\[
 \sum_{n\ge1}n^{-1/2}x^n
 \sim\sqrt\pi(1-x)^{-1/2}\qquad(x\uparrow1),             \tag{22}
\]

which proves `(9)`.  Alternatively, `(9)` follows immediately by multiplying the exact local
decomposition `(4)` by `sqrt(1-B^2t)` and taking the left real limit.

If a single-valued meromorphic continuation existed at `R_A`, its local order would be an integer.
A removable germ would make the left side of `(9)` tend to zero; a pole of integer order `m>=1`
would make its modulus tend to infinity after multiplication by `(R_A-t)^(1/2)`.  Neither is the
finite nonzero limit in `(9)`.  Hence the germ is not meromorphic at `R_A`.  More strongly, `(4)`
exhibits its nontrivial local square-root monodromy directly.

The phrase *half-order singularity* therefore refers both to the exact Puiseux term `(4)` and to
its radial consequence `(9)`.

## Weaker top-down RH predecessor

Let

\[
 r_0=\frac{250000}{251001}.
\]

Suppose an independently constructed prime--Gamma or exact-theta expression gives one
single-valued meromorphic continuation of the susceptibility germ through every point of the real
collar `[r_0,1)`, coherently with the unconditional left-hand germ.  Then RH holds.

Indeed, false RH would put the exact radius `R_A=B^(-2)` strictly inside that collar.  Equation
`(4)` forbids meromorphicity at precisely that point.  Therefore `R_A=1`, and the formal exact
radius theorem gives RH.

This is strictly weaker than the previous holomorphic-collar target: isolated poles of arbitrary
integer order are allowed.  The only excluded behavior is the source-created half-order pinch.

```text
single-valued meromorphic prime--Gamma susceptibility on the thin collar
  -> no positive half-order maximal-packet pinch before 1
  -> exact Abel radius = 1
  -> RH.
```

## Source interpretation

The Möbius-pullback law writes

\[
 \mathscr B_R(s,w)=\frac1{1-s}
 M_R\!\left(\frac{s(w-1)}{1-s}\right),                 \tag{23}
\]

where `M_R` is the continued prime--Gamma moment germ, and double Gutzmer recovers `chi(r^2)`.
The individual pulled-back source terms are meromorphic.  The half-order law shows exactly where
meromorphicity can be lost: taking the diagonal/Gutzmer pairing through a conjugate pole pinch.
Thus global meromorphicity of `M_R` alone does not prove RH; the remaining source theorem is a
single-valued meromorphic continuation of the *paired susceptibility*, or equivalently an exact
cancellation of every collar pinch monodromy.

## Circularity firewall

An admissible meromorphic continuation must be built from the prime--Gamma decomposition, the
theta integral plus the all-order cumulant relation, or a source-side operator/contour formula.  It
may not use the Xi divisor expansion, the maximal amplitude `B`, the exact Abel radius, an
RH-equivalent limiting measure, or coefficient bounds equivalent to RH.

## Formal parents

- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPencil.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinLoschmidtPurity.lean`
- `formal/GaloisForLFunctions/RHTower/BernsteinEllipseRigidity.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPurityDivergence.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinExactExponentialThreshold.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinAbelSusceptibility.lean`

## Paper parents

- `prime-arch-bernstein-legendre-double-source-kernel.md`
- `prime-arch-bernstein-mobius-pullback-gutzmer-law.md`
- `prime-arch-bernstein-pringsheim-collar-transfer.md`
- `prime-arch-moment-pole-residue-pinch-law.md`

## Literature calibration

The asymptotic tools are standard: Laplace's method for a nondegenerate interior maximum is
recorded in [NIST DLMF section 2.3(iii)](https://dlmf.nist.gov/2.3.iii), and the polylogarithm
series and its expansion near `1` are recorded in
[NIST DLMF section 25.12(ii)](https://dlmf.nist.gov/25.12.ii).  No novelty is claimed for those
parent tools.  The project-specific result is their exact application to the multiplicity-exact
Xi Bernstein packet, using the already formalized maximal-coordinate and phase-rigidity laws to
prove a nonzero positive half-order coefficient.  The stronger local decomposition `(4)` itself
uses only the exact algebraic double-source kernel, normal convergence, and the same phase gap;
the Laplace and Abelian tools are no longer needed for the meromorphic-collar obstruction.

## Gates

- [x] maximal packet is finite and uniformly separated
- [x] maximal fibres have nonzero aggregate weights
- [x] phase rigidity excludes mixed leading-order interference
- [x] exact finite-packet Puiseux decomposition proved on paper
- [x] nonzero local monodromy coefficient proved on paper
- [x] exact coefficient asymptotic proved on paper
- [x] half-order Abel law proved on paper
- [x] meromorphic-collar-to-RH transfer proved on paper
- [ ] formalize the exact finite-packet branch decomposition in Lean
- [ ] optionally formalize the coefficient asymptotic
- [ ] construct the independent source-side meromorphic collar
- [ ] RH

## 2026-08-20 — Stage-3 formalization

The Lean gate — the exact finite-packet branch decomposition — is closed by

`formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinBranchDecomposition.lean`,

which supplies the analytic half the corpus was missing: the remainder left after the finite
maximal diagonal packet decays at a geometric rate strictly below `B²`, so its Abel series
converges on a disc strictly larger than `R_A = B^{-2}` and is holomorphic across it.  The only
non-single-valued part of the germ at `R_A` is therefore the explicit square-root kernel.

| card item | Lean declaration |
|-|-|
| `(1)` finite packet and its purity | `primeArchEndpointBernsteinPurity`, `primeArchEndpointBernsteinPurity_eq_atomicBernsteinPacketSquareEnergy` |
| `(2)` the maximum `B` is attained | `exists_uniformlySeparated_maximal_xiEndpointAmplitudePacket_of_not_rh` |
| `(3)`, `(11)` fibre weights `C_u` | `xiEndpointCoordinateSet`, `xiEndpointCoordinateWeight` |
| `(4)` exact branch decomposition | `exists_branchDecomposition_of_not_rh` (new), with `exists_exact_maximalDiagonalSquareRootDecomposition_of_not_rh` |
| `(5)` the amplitude `A(t)` | `finiteBernsteinCoordinateDiagonalSquareRootKernel` |
| `(6)`, `(9)` positive half-order boundary | `exists_positive_halfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh` |
| `(7)` coefficient asymptotic | `exists_positive_halfOrder_primeArchEndpointBernsteinPurity_of_not_rh` |
| `(10)`, `(12)` cofinal decay and the `β^n` tail | `summable_xiZeroCopyReciprocalSquare`, `finitePacketL1_atomicBernsteinComplementPacket_le` |
| `(13)`--`(15)` the diagonal double-source kernel | `hasSum_centralBinomialDiagonalKernelCoefficient`, `hasSum_centralBinomialDiagonalKernelCoefficient_eq_kernel` |
| `(16)`, `(21)` mixed-maximal gap | `exists_uniform_mixedCrossMoment_gap` (new), `exists_uniform_mixedXiBernsteinCrossMoment_gap_of_distinct_maximal_coordinates`, `eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq` |
| `(18)`--`(20)` one-row Laplace asymptotic | `tendsto_sqrtNat_mul_bernsteinAffineRowEnergy_div_pow` |
| `(22)` Abelian transfer | `tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder` |
| remainder holomorphy across `R_A` | `exists_remainder_exponential_bound`, `summable_remainder_of_lt_inv_gamma` |
| polarized packet identity | `abs_finiteBernsteinCoordinatePacketEnergy_sub_diagonal_le` (new), `finiteBernsteinCoordinatePacketEnergy_eq_sum_re_crossMoment` |

All new declarations have axiom set `[propext, Classical.choice, Quot.sound]`.

The nonmeromorphicity conclusion is the Lean-proved finite nonzero limit of
`√(1-B²t)·χ(t)` together with the branch decomposition: a removable germ would force the limit to
be zero and a pole of integer order would force it to be infinite.

**Stage: 3-formalized.**

## Gates (stage 3)

- [x] formalize the exact finite-packet branch decomposition in Lean
- [x] formalize the coefficient asymptotic (already carried by the corpus half-order modules)
- [x] uniform mixed-maximal cross-moment gap formalized
- [x] remainder proved holomorphic across the critical radius
- [x] axiom audit clean
