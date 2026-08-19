# Prime--archimedean Bernstein Möbius-pullback Gutzmer law

- **ID:** `prime-arch-bernstein-mobius-pullback-gutzmer-law`
- **Stage:** 3-formalized
- **Type:** exact value relation / source reformulation
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** fully formalized — see the 2026-08-19 section

## One-source Möbius pullback

Let `m : N -> R`, let `L_m` be its polynomial moment functional, and define

\[
 b_{n,i}=L_m\!\left(\binom niX^i(1-X)^{n-i}\right),
 \qquad
 P_n(w)=\sum_{i=0}^n b_{n,i}w^i.                         \tag{1}
\]

Let

\[
 M(v)=\sum_{k\ge0}m_kv^k                                \tag{2}
\]

be the ordinary moment germ.  Then the full degree-generating function of the Bernstein pencils
is the single Möbius pullback

\[
 \boxed{
 \mathscr B(s,w):=\sum_{n\ge0}P_n(w)s^n
 =\frac1{1-s}M\!\left(\frac{s(w-1)}{1-s}\right).
 }                                                               \tag{3}
\]

This is a formal identity at `s=0`, and an analytic identity wherever the displayed series and
composition converge.

## Proof

The Bernstein generating polynomial satisfies

\[
 P_n(w)
 =L_m\!\left((1-X+Xw)^n\right)
 =\sum_{k=0}^n\binom nkm_k(w-1)^k.                       \tag{4}
\]

Therefore

\[
\begin{aligned}
 \sum_{n\ge0}P_n(w)s^n
 &=\sum_{k\ge0}m_k(w-1)^k
   \sum_{n\ge k}\binom nk s^n\\
 &=\sum_{k\ge0}m_k(w-1)^k\frac{s^k}{(1-s)^{k+1}}\\
 &=\frac1{1-s}M\!\left(\frac{s(w-1)}{1-s}\right),
\end{aligned}                                                   \tag{5}
\]

using the standard negative-binomial identity
`sum_(n>=k) choose(n,k) s^n = s^k/(1-s)^(k+1)`.

## Double Gutzmer recovery of the purity susceptibility

Put

\[
 \Pi_n=\sum_{i=0}^n b_{n,i}^2,
 \qquad \chi(t)=\sum_{n\ge0}\Pi_nt^n.                   \tag{6}
\]

Because the coefficients are real, finite Parseval on the `w` circle gives

\[
 \Pi_n=\frac1{2\pi}\int_0^{2\pi}|P_n(e^{i\varphi})|^2\,d\varphi.
                                                                    \tag{7}
\]

A second Parseval identity in the degree variable gives, for every nonnegative `r` in the common
domain of convergence,

\[
 \boxed{
 \chi(r^2)=\frac1{(2\pi)^2}
 \int_0^{2\pi}\!\int_0^{2\pi}
 \left|\mathscr B(re^{i\theta},e^{i\varphi})\right|^2
 \,d\theta\,d\varphi.
 }                                                               \tag{8}
\]

Thus the positive Abel susceptibility is the exact two-torus Gutzmer norm of one explicit
Möbius pullback of the moment germ.  The Legendre double-source kernel in
`prime-arch-bernstein-legendre-double-source-kernel.md` is obtained by eliminating these two
circle variables coefficientwise.

## Prime--Gamma specialization

For the endpoint source, set

\[
 R=\texttt{primeArchEndpointHausdorffRadius},\qquad
 m_k=\frac{\texttt{normalizedPrimeArchMoment}(k)}{R^k}.
\]

The ordinary moment germ is

\[
 M_R(v)=
 \texttt{normalizedPrimeArchMomentGerm}\!\left(\sqrt{v/R}\right) \tag{9}
\]

as a germ at zero.  Evenness makes the right side independent of the local square-root choice.
Consequently

\[
 \boxed{
 \mathscr B_R(s,w)=\frac1{1-s}
 \texttt{normalizedPrimeArchMomentGerm}\!\left(
   \sqrt{\frac{s(w-1)}{R(1-s)}}\right).
 }                                                               \tag{10}
\]

The formal identity

```text
continuedPrimeArchSourceRelativeTrace(z)
  = -z * normalizedPrimeArchMomentGerm(z)
```

turns `(10)` into a direct value formula in the analytically continued prime--Gamma trace.  No
finite Bernstein coefficient remains in the source expression.

## Atomic pole surface and reflected pinch

On the divisor-resolved side, write the normalized coordinate as `u`.  The corresponding summand
of `M_R` is proportional to `(1-uv)^(-1)`, so its pullback in `(3)` is proportional to

\[
 \frac1{1-s(1-u+uw)}.                                    \tag{11}
\]

For `|w|=1`,

\[
 \max_{|w|=1}|1-u+uw|=|1-u|+|u|=:B_+(u).                \tag{12}
\]

Hence the first radius at which this pole surface reaches the `w` circle is

\[
 |s|=B_+(u)^{-1}.                                        \tag{13}
\]

The two-torus norm uses `t=r^2`, so `(13)` becomes the reflected susceptibility pinch

\[
 t=B_+(u)^{-2},                                          \tag{14}
\]

exactly matching the conjugate-factorized Legendre kernel and the formal endpoint amplitude.
This gives a direct source-germ interpretation of the exact Abel radius selected under false RH:
it is where a Möbius-pulled prime--Gamma pole first reaches the Gutzmer torus.

## Top-down chains

The value relation yields two exact predecessor interfaces:

```text
for every 0 <= r < 1, the explicit source pullback B_R is L2 on the two-torus
  -> chi(r^2) is finite for every r < 1
  -> RH,
```

and

```text
a coherent holomorphic regularization of the diagonal Gutzmer pairing
through the thin Abel collar
  -> Pringsheim excludes every reflected pinch before 1
  -> RH.
```

The first interface is equivalent to the coefficient criterion by Parseval if its `L2` property is
proved from the series itself.  An admissible proof must instead use the explicit continued
prime--Gamma/theta expression `(10)`.

## Theta warning

The positive theta-cusp raw moments do not directly represent `m_k`.  The formal all-order
cumulant recurrence proves that `normalizedPrimeArchMoment(k)` is a logarithmic cumulant of the
theta source, recursively determined by raw theta moments and lower cumulants.  Replacing `M_R` in
`(10)` by the raw positive theta moment transform would therefore be incorrect.  Any theta proof
must pass through the exact differential identity

\[
 \Xi_C'(z)+z\,\texttt{normalizedPrimeArchMomentGerm}(z)\Xi_C(z)=0. \tag{15}
\]

## Formalization target

1. Prove `(4)` from `bernsteinCoefficientTransform` and `momentFunctional`.
2. Formalize the negative-binomial summation and the germ identity `(3)`.
3. Specialize `(3)` to `normalizedPrimeArchMomentGerm` and the continued source trace.
4. Apply the existing `HTGeometry/GutzmerIdentity.lean` infrastructure twice to prove `(8)`.
5. Prove the atom pole-surface relation `(11)`--`(14)` and connect it to the exact Abel radius.
6. Only after targeted Lean verification is permitted, wire the new module into `RHTower.lean`.

## Literature calibration

Equation `(3)` is the classical ordinary-generating-function law for the binomial transform, and
`(8)` is Parseval/Gutzmer applied in two variables.  No novelty is claimed for those parent
identities.  The project contribution is the exact source specialization `(10)` and the
identification of the formal endpoint amplitude with the first Möbius-pulled prime--Gamma pole to
reach the Gutzmer torus.

## Gates

- [x] Möbius-pullback generating identity proved on paper
- [x] double Gutzmer susceptibility formula proved on paper
- [x] prime--Gamma source specialization identified
- [x] atom pole surface and reflected pinch identified
- [x] theta cumulant warning established from the formal corpus
- [ ] Lean formalization
- [ ] source-only `L2` or single-valued meromorphic collar theorem
- [ ] RH

## Half-order Gutzmer pinch law

The companion theorem
`prime-arch-bernstein-half-order-pringsheim-singularity.md` expands the double Gutzmer kernel into
the finitely many maximal same-pole packets plus a remainder holomorphic beyond the first contact.
It obtains an exact local square-root term with nonzero coefficient; Laplace's method then gives
the coefficient asymptotic as a corollary.  The source pole law
`prime-arch-moment-pole-residue-pinch-law.md` further shows that every ordinary moment pole has
residue exactly `-R` times its multiplicity and that this residue and pole position determine the
square-root coefficient.  The remaining source target is only single-valued meromorphic
continuation of the paired Gutzmer value; holomorphic continuation is stronger than necessary.

## 2026-07-15 radial-Jensen Schur-capacity consumer

`xi-radial-jensen-schur-capacity-rigidity.md` uses the same ordinary moment germ `M` as a reflected
unit-circle boundary symbol.  The source radius and narrow-sector laws, combined with Schwarz--
Pick, determine its `L^1/H^1_0` quotient norm exactly as `primeArchCentralCurvature`, attained by
the constant `1`.  Thus `(3)` and `(10)` here supply an explicit continued prime--Gamma formula for
a norm that is now closed rather than open.  Its deficit from radial Jensen mass is exactly half
the global reflection energy.  The double Gutzmer `L^2` identity remains useful source geometry,
but any RH-bearing transfer must couple it to an adjoint, absolute-value, trace-norm, or polar
channel rather than seek another holomorphic extremizer.

## 2026-08-19 — unconditional Lean formalization (stage 3)

Every proved equation of this card is now Lean-proved, with no added analytic hypothesis: each
statement carries exactly the convergence condition the card itself states ("wherever the displayed
series and composition converge", "for every nonnegative `r` in the common domain of convergence").
`#print axioms` on each capstone reports only `propext, Classical.choice, Quot.sound`.

**New reusable infrastructure**

| Statement | Lean declaration |
|---|---|
| antidiagonal regrouping of a summable family on `ℕ × ℕ` | `GaloisForLFunctions.HTGeometry.tsum_sum_antidiagonal`, `summable_sum_antidiagonal` (`HTGeometry/AntidiagonalRegrouping.lean`) |
| Gutzmer's identity from an absolutely convergent coefficient series | `GaloisForLFunctions.HTGeometry.hasSum_gutzmer_of_summable_norm` (`HTGeometry/GutzmerPowerSeries.lean`) |

**The card** — `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinMobiusPullback.lean` and
`.../PrimeArchBernsteinMobiusPullbackSource.lean`

| Card item | Lean declaration |
|---|---|
| `b_{n,i}`, `P_n(w)`, eq. (1) | `bernsteinCoefficient`, `bernsteinCoefficientTransform` (pre-existing) |
| `∑_i w^i B_{n,i}(X) = (1+(w-1)X)^n` | `bernstein_smul_sum` |
| eq. (4) | `bernsteinCoefficientTransform_eq_binomial` |
| `M(v) = ∑_k m_k v^k`, eq. (2) | `bernsteinMomentGerm` |
| eq. (5), the negative-binomial double sum | `pencilFamily`, `hasSum_pencilFamily_fiber`, `summable_pencilFamily`, `sum_antidiagonal_pencilFamily` |
| **eq. (3), the Möbius-pullback law** | `tsum_bernsteinPencil_eq_mobiusPullback` |
| `Π_n`, `χ(t)`, eq. (6) | `bernsteinCoefficientPurity` (pre-existing) |
| eq. (7), finite Parseval on the `w` circle | `bernsteinCoefficientPurity_eq_circleMean` |
| **eq. (8), the double Gutzmer susceptibility** | `hasSum_purity_doubleCircleMean` (with `hasSum_inner_gutzmer`) |
| `B(s,w)` | `bernsteinPencilGenerating` |
| eq. (9), the square-root coordinate | `bernsteinMomentGerm_primeArch`, `bernsteinMomentGerm_primeArch_neg` (evenness) |
| **eq. (10), the prime--Gamma pullback** | `tsum_bernsteinPencil_primeArch` |
| `continuedPrimeArchSourceRelativeTrace(z) = -z · normalizedPrimeArchMomentGerm(z)` | `continuedPrimeArchSourceRelativeTrace_eq` |
| eq. (11)--(12), `B_+(u) = \|1-u\|+\|u\|` and its attainment | `poleSurfaceRadius`, `norm_affine_le_poleSurfaceRadius`, `exists_norm_affine_eq_poleSurfaceRadius` |
| eq. (13)--(14), the reflected pinch radius | `pole_ne_zero_of_norm_lt`, `exists_pole_at_poleSurfaceRadius` |

The uniform coefficient control needed for `(8)` is `pencilBound`, `summable_pencilBound` and
`summable_norm_bernsteinCoefficientTransform`: on the `w` circle `‖P_n(w)‖ ≤ ∑_{k≤n} C(n,k)|m_k|2^k`,
and that majorant is summable against `ρ^n` exactly when `∑_k |m_k| (2ρ/(1-ρ))^k` converges.

## Gates

- [x] Möbius-pullback generating identity proved on paper
- [x] double Gutzmer susceptibility formula proved on paper
- [x] prime--Gamma source specialization identified
- [x] atom pole surface and reflected pinch identified
- [x] theta cumulant warning established from the formal corpus
- [x] Lean formalization
- [ ] source-only `L2` or single-valued meromorphic collar theorem  *(declared future research)*
- [ ] RH  *(declared future research)*
