# Deninger--Möbius prime-normal successor blow-up

- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION / SINGULAR CROSS-PRIME TRANSPORT / ROUTE-L FRONTIER ADVANCE
- **Status:** `[FORMALIZED]`
- **Corpus inputs:**
  `MobiusThetaPhysicalSourceToXiLanding.lean`,
  `MobiusThetaInternalJetPrimeNormalComplexGraph.lean`

## 1. Source packet

Let \(H=L^2(\mathbb R)\), let \(\Theta\in H\) be the physical theta source, and let
\(U_t\) be additive translation in the normalized Mellin coordinate.  For \(p\geq1\) and
\(m\geq3\), the existing complete prime-normal source is

\[
 R_{p,m}
 =\mu(p)\Theta+
   \sum_{n>p}\mu(n)\left(\frac pn\right)^{m/2}
   U_{-m\log(n/p)}\Theta .                              \tag{1}
\]

The normalization constant suppressed in the subscript of \(U\) is the fixed corpus Mellin
spectral normalization.  Existing \(m=3\) majorants make the sum in (1) absolutely convergent in
\(H\), and existing prime-normal extraction gives

\[
              R_{p,m}\longrightarrow \mu(p)\Theta .    \tag{2}
\]

No divisor point or spectral parameter occurs in (1).

## 2. Exact successor theorem

Let

\[
 r=\operatorname{succ}_{\mu}(p)
   :=\min\{n>p:\mu(n)\neq0\}.
\]

This integer exists because there is a prime larger than \(p\).  Define the singular successor
blow-up

\[
 T_{p\to r,m}
   =\left(\frac rp\right)^{m/2}U_{m\log(r/p)}.           \tag{3}
\]

### Theorem (exact Möbius successor transport)

For every \(p\geq1\), every \(m\geq3\), and \(r=\operatorname{succ}_{\mu}(p)\),

\[
 \boxed{
 T_{p\to r,m}\bigl(R_{p,m}-\mu(p)\Theta\bigr)=R_{r,m}.}
                                                               \tag{4}
\]

In particular, because \(\mu(2)=\mu(3)=-1\),

\[
 \boxed{
 \left(\frac32\right)^{m/2}U_{m\log(3/2)}
       \bigl(R_{2,m}+\Theta\bigr)=R_{3,m}.}              \tag{5}
\]

### Proof

By minimality of \(r\), \(\mu(n)=0\) for \(p<n<r\).  Subtracting the head of (1), applying (3),
and using \(U_aU_b=U_{a+b}\) gives

\[
\begin{aligned}
T_{p\to r,m}(R_{p,m}-\mu(p)\Theta)
 &=\sum_{n\ge r}\mu(n)
   \left(\frac rp\right)^{m/2}
   \left(\frac pn\right)^{m/2}
   U_{m\log(r/p)-m\log(n/p)}\Theta\\
 &=\sum_{n\ge r}\mu(n)
   \left(\frac rn\right)^{m/2}
   U_{-m\log(n/r)}\Theta\\
 &=R_{r,m}.
\end{aligned}
\]

All rearrangements are legitimate in \(H\): terms with \(p<n<r\) are zero and the remaining
series is exactly the already absolutely convergent series defining \(R_{r,m}\).  This proves
(4); \(r=3\) for \(p=2\) proves (5).  ∎

## 3. Spectral and multiplicity-faithful form

Write \(s(w)\) for the existing centered Mellin parameter and

\[
 M_{p,m}(w)=\sum_{n\ge p}\mu(n)\left(\frac pn\right)^{m s(w)}
\]

on its honest convergence domain.  Fourier--Laplace transformation of (4) gives the exact scalar
identity

\[
 \boxed{
 \left(\frac rp\right)^{m s(w)}
       \bigl(M_{p,m}(w)-\mu(p)\bigr)=M_{r,m}(w).}         \tag{6}
\]

The existing internal-jet landing theorem multiplies \(M_{p,m}(w)\) by the corresponding Xi jet.
At a divisor support \(\rho\) of multiplicity \(d\), the first conormal pair is therefore

\[
 \left(0,
 M_{p,m}(\rho)\Xi^{(d)}(\rho)\right),
\qquad \Xi^{(d)}(\rho)\neq0,                            \tag{7}
\]

for all sufficiently large \(m\).  Hence (6) transports the actual leading nonzero multiplicity
jet; it is not a zeroth-order or simple-zero surrogate.

## 4. Forced nonclosability

For the \(2\to3\) successor, (2) and (5) give

\[
 R_{p,m}+\Theta\longrightarrow0,
 \qquad
 T_{p\to r,m}(R_{p,m}+\Theta)=R_{r,m}\longrightarrow-\Theta . \tag{8}
\]

The theta source is nonzero because its Fourier transform has value \(\Xi_C(0)\neq0\) at the
origin.  Thus the cofinal graph has the nonzero vertical limit \((0,-\Theta)\).  No closable
operator on the ambient \(L^2\) completion can contain this graph.  Moreover

\[
                 \|T_{p\to r,m}\|=(r/p)^{m/2}\to\infty, \tag{9}
\]

so the singularity is exponential and explicit, not an unspecified failure of boundedness.

## 5. Reflection anomaly

The source construction (4) is unconditional, but reflected Mellin transport does not commute
with its blow-up.  For \(a=r/p>1\), the two spectral normalizers are

\[
                 a^{m s},\qquad a^{m(1-\bar s)}.
\]

Their common phase cancels and their radial ratio is

\[
 \frac{|a^{m s}|}{|a^{m(1-\bar s)}|}
       =a^{m(2\Re s-1)}.                                \tag{10}
\]

Consequently reflected successor compatibility holds exactly when

\[
                  \Re s=\frac12.                        \tag{11}
\]

For the formal one-exponent shadow \(p=2,r=3,m=1\), (10) is the ratio
\(g_3(s)/g_2(s)\) of the fixed two-prime radial gains.
Thus \(g_2(s)-g_3(s)\) is a nowhere-zero multiple of \(1-(3/2)^{2\Re s-1}\).  The existing
Calderón--Witt physical reporter is precisely the finite radial shadow of the failure of the
source successor blow-up to commute with reflection.

## 6. Route-L consequence

This theorem closes one previously missing construction, but not RH:

1. It supplies a literal, source-first, off-diagonal \(2\to3\) transport before divisor
   specialization.
2. It retains ordinary-integer label, exponent depth, and the leading nonzero Xi jet.
3. Its singular/nonclosable character is proved, not postulated.
4. It identifies the two-prime Burnol/Deninger wall as the exact reflection anomaly of that
   transport.

The open Route-L theorem is consequently narrower.  It is no longer “find some singular
cross-prime transport.”  One must construct, from the rational-Witt/Milnor relevant degree-two
source, a same-full-grade counterterm whose target differential absorbs the explicit anomaly

\[
 a^{m s}-a^{m(1-\bar s)}                                \tag{12}
\]

while the fixed coefficient-faithful reader kills that target boundary.  Postulating reflected
compatibility of (4), quotienting by (12), or requiring the graph to be closable would each be
equivalent to imposing the critical line and is forbidden.

## 7. Hostile audit

- No Xi zero, divisor enumeration, zero location, RH predicate, or physical vanishing is used in
  (1)--(5).
- The relation is cross-prime before scalar codiagonalization; \(2\) and \(3\) remain the source
  head and its first surviving Möbius successor.
- Equation (7) uses divisor specialization only to verify coefficient and multiplicity survival.
- Equation (11) is reported as the obstruction, not assumed as a proof input.
- Flat multiplicative factorization is not misread as annihilation: it constructs (4), while its
  reflection anomaly (12) remains nonzero off the wall.
- The result is project-specific new knowledge: it is an exact identity between the corpus's
  complete prime-normal theta packets, not a relabeling of standard Möbius inversion.

## Lean status

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerMobiusPrimeNormalSuccessorBlowup.lean` and
`DeningerMobiusSuccessorAmplitude.lean`, on the corpus inputs
`MobiusThetaPhysicalSourceToXiLanding.lean` and
`MobiusThetaInternalJetPrimeNormalComplexGraph.lean`.  Axiom audit for every declaration:
`propext, Classical.choice, Quot.sound`.

### Done

- **The Möbius successor.** `exists_mobius_ne_zero_gt` (there is always a larger prime, hence a
  larger nonzero Möbius coefficient), `mobiusSuccessor`, `lt_mobiusSuccessor`,
  `moebius_mobiusSuccessor_ne_zero`, `moebius_eq_zero_of_lt_mobiusSuccessor`, and
  `mobiusSuccessor_two : mobiusSuccessor 2 = 3`.
- **`(3)`, `(4)`: the exact successor transport.**  `mobiusThetaSuccessorBlowup` and its bounded
  form `mobiusThetaSuccessorBlowupCLM`, with `summable_mobiusThetaPrimeNormalTailTerm`,
  `mobiusThetaSuccessorBlowup_tail_head`, `mobiusThetaSuccessorBlowup_tail_succ`,
  `mobiusThetaPrimeNormalTailTerm_eq_zero_before_successor`, and
  **`mobiusTheta_successor_transport`**.
- **`(5)`: the `2 → 3` case.**  `mobiusThetaTwoThreeSuccessorBlowup` and
  **`mobiusTheta_two_three_successor_transport`**.
- **`(6)`: the scalar Fourier--Laplace shadow.**  `DeningerMobiusSuccessorAmplitude.lean`:
  `mobiusThetaPrimeNormalAmplitude` is `M_{p,m}(s)`, `lSeriesSummable_moebius_of_one_lt_re`
  gives absolute convergence on `1 < Re(ms)` (so `m ≥ 3` on the critical line is inside the
  domain), `mobiusThetaPrimeNormalAmplitude_head` identifies the head term as `μ(p)`,
  `mobiusSuccessor_indicator_eq` kills every index strictly between `p` and its successor, and
  **`mobiusThetaPrimeNormalAmplitude_successor`** is the identity
  `(r/p)^{ms}(M_{p,m}(s) - μ(p)) = M_{r,m}(s)`.
  The literal multiplier used by the complete internal-jet source is connected directly by
  **`mobiusThetaPrimeNormalResidualMultiplier_successor_transport`**; its honest convergence
  inequality is encoded in `MobiusSuccessorSpectralPoint`, not supplied as an analytic premise.
- **`(7)`: the conormal pair at a divisor.**  `mobiusThetaInternalJetRawHeadConormalPair` and
  `mobiusThetaInternalJetRawHeadConormalPair_at_divisor` in the jet module, plus
  `mobiusThetaTwoThreeTargetConormalPair` and
  **`eventually_mobiusThetaTwoThreeTargetConormalPair_at_divisor`** for the complete transported
  `3`-residual.  The latter retains the first nonzero Xi jet at arbitrary analytic multiplicity.
- **`(8)`, `(9)`: forced nonclosability.**  `mobiusThetaTwoThreeCofinalSource`,
  `mobiusThetaTwoThreeCofinalTarget`, `tendsto_mobiusThetaTwoThreeCofinalSource_zero`,
  `tendsto_mobiusThetaTwoThreeCofinalTarget`, `xiThetaSourceL2_ne_zero`,
  **`MobiusThetaTwoThreeGraphExtension.not_sequentiallyClosable`**, together with
  `norm_mobiusThetaSuccessorBlowupCLM` and
  **`tendsto_norm_mobiusThetaSuccessorBlowupCLM_atTop`**, which is the explicit exponential
  divergence `(r/p)^{m/2} → ∞`.
- **`(10)`, `(11)`: the reflection anomaly.**  `mobiusThetaSuccessorSpectralNormalizer`,
  `mobiusThetaSuccessorReflectedSpectralNormalizer`,
  **`mobiusThetaSuccessorSpectralNormalizer_norm_ratio`** (the radial ratio is
  `(r/p)^{m(2 Re s - 1)}`) and **`mobiusThetaSuccessorSpectralNormalizer_norm_ratio_eq_one_iff`**,
  which is exactly `Re s = 1/2`.

## Gates

- [x] 1 → 2 fully-proven: dependency-closed paper proof `(1)`--`(12)`
- [x] 2 → 3 formalized: `(3)`--`(11)` proved unconditionally (see *Lean status*)
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-12 — Audited the corpus against the card: the source transport, nonclosability, norm
  divergence and reflection anomaly were already built; added the missing scalar shadow `(6)` and
  wired the module into the umbrella.  Card moved to stage 3.
- 2026-08-12 — Strengthened `(6)` from the independent amplitude presentation to the exact
  `mobiusThetaPrimeNormalResidualMultiplier` used by the complete internal-jet source; added the
  named transported `2 → 3` arbitrary-multiplicity conormal theorem.
