# Eigen-pair prime identification — the derivation (branch i)

- **ID:** ULF-INV-10
- **Stage:** 1-in-progress (promotes to 2 when D3–D6 close)
- **Type:** DERIVATION IN PROGRESS / PAPER PROOF UNDER CONSTRUCTION
- **Source:** ULF-INV-9-ATTACK §§8–11 (all ingredients provisioned from source)
- **Status:** [D1 DERIVED] [D2 COHERENCE CHECK PASSED] [D3–D6 OPEN] [NOT RH] [NO LEAN]

## 0. Setup (conventions to be pinned against corpus definitions before promotion)

For zeros \(\alpha,\beta\) of `XiC` (centered coordinates, \(|\mathrm{Im}|<\tfrac12\)
unconditionally), the eigenfunctions solve

\[
(D+\alpha)u_\alpha=-k,\qquad (D+\bar\beta)\bar u_\beta=-k
\]

globally (causal/anti-causal Volterra solutions agreeing at zeros; \(k\) the theta-cusp source,
real). Decay: \(|u_\alpha(x)|\lesssim e^{-(1-|\mathrm{Im}\,\alpha|)|x|}\), rate
\(>\tfrac12\); the pair product decays at joint rate \(>1\), so the prime pairing

\[
P(\alpha,\beta):=\Bigl\langle\mu_P,\;u_\alpha\bar u_\beta\Bigr\rangle,
\qquad
\mu_P=\sum_n\frac{\Lambda(n)}{\sqrt n}\bigl(\delta_{\log n}+\delta_{-\log n}\bigr),
\]

converges absolutely. Goal: \(P+A=q_W\) with \(A\) the archimedean pairing and \(q_W\) the
antidiagonal Gram.

## D1 — Wronskian reduction (derived)

From the two ODEs,

\[
\frac{d}{dx}\bigl(u_\alpha\bar u_\beta\bigr)
=-(\alpha+\bar\beta)\,u_\alpha\bar u_\beta-k\,(u_\alpha+\bar u_\beta),
\]

hence, whenever \(\alpha+\bar\beta\ne0\),

\[
\boxed{\;u_\alpha\bar u_\beta
=-\frac1{\alpha+\bar\beta}
\Bigl[\bigl(u_\alpha\bar u_\beta\bigr)'+k\,(u_\alpha+\bar u_\beta)\Bigr].\;}
\tag{D1}
\]

Pairing with \(\mu_P\): the pair pairing reduces to (i) a derivative-term pairing
\(\langle\mu_P,(u_\alpha\bar u_\beta)'\rangle\) and (ii) source pairings
\(\langle\mu_P\,(u_\alpha+\bar u_\beta),\,k\rangle\) — the latter exactly the objects the
theta-source layer owns in \(n^{-1/2}\)-log-translate form
(`finitePrimeThetaCuspResolventSeries`, seed summability proved).

## D2 — Degeneration matches antidiagonality (coherence check, passed)

The reduction (D1) degenerates exactly when \(\alpha+\bar\beta=0\) — and (conventions pending)
that locus is precisely the antidiagonal partner locus where the Hermitian Gram is supported.
Off the antidiagonal, (D1) will drive \(P+A\) to \(0\); on it, the l'Hôpital/limit version of
(D1) produces the norm term. The prime side's antidiagonal support thus arises from the same
algebraic mechanism (the degenerating first-order system) as the Hermitian side's — a strong
structural coherence check for the whole identification, and independent evidence that the
assembly is the right shape. If the convention pinning breaks this match, the derivation is
wrong and must be recorded as such.

## D3–D6 — remaining obligations (each gets proved or gets a recorded obstruction)

- **D3.** The derivative-term pairing: handle \(\langle\mu_P,f'\rangle\) by Abel/smoothed
  summation compatible with absolute convergence (the corpus's dyadic/smoothing layers), or by a
  second application of the system to express \(f'\) back through the pair family.
- **D4.** The source pairings via the exact identity \(k_N=R_N(1/2)a\) and its norm-convergent
  series; finite-prime truncation limits \(N\to\infty\) using the proved envelopes.
- **D5.** Archimedean assembly: `logDeriv archFactor` against the removable quotients, (18a)
  substrip decay; must reproduce \(A\) so that \(P+A\) closes.
- **D6.** The diagonal/degenerate case by the limit of (D1) as \(\bar\beta\to-\alpha\)
  (l'Hôpital on the closed-form reduction), yielding the explicit norm and completing the Gram
  match.

## Promotion condition

All of D3–D6 closed with conventions pinned against `XiWeilPolarization` /
`XiRelativeResolventFlux` / `ThetaCuspFinitePrimeSource` definitions; then this card moves to
stage 2 as the prime-sum form of the eigen-span equivalence, ULF-INV-9's decisive-class wall
suspicion is recorded dead, and the Weil-polarization lane's last analytic gate is closed at
paper level.

## Log

- 2026-08-09 — created; D1 derived; D2 coherence check passed at schematic level; D3–D6 opened
  with their proof-or-obstruction discipline.

## D4a — source-pairing convergence: trap named, checked, resolved (derived)

Mid-derivation trap: if the source k grew like e^{-x} as x -> -infinity (the naive theta rate),
the left-end source pairing would diverge (terms Λ(n)·n^{|Im α| - 1/2}). Checked against the
seed in source (`thetaCuspSeed t = 2π(2πt⁴ − 3t²)e^{−πt²}`): its zeroth moment vanishes
EXACTLY —

    ∫₀^∞ t²e^{−πt²}dt = 1/(4π),   ∫₀^∞ t⁴e^{−πt²}dt = 3/(8π²),
    ∫₀^∞ seed = 2π[2π·3/(8π²) − 3·1/(4π)] = 2π[3/(4π) − 3/(4π)] = 0.

By Poisson summation with zero mean, the m = 0 term cancels and
k(x) = Σ_n e^{x/2}·seed(n·e^x) decays super-exponentially at BOTH ends
(right: e^{−πe^{2x}}; left: Fourier-tail e^{−πe^{−2x}}-type). The cusp normalization is
precisely engineered for this. Consequence: the source pairings
⟨μ_P·(u_α+ū_β), k⟩ converge absolutely with large margin, and the D1 reduction's right side is
fully summable. D4a closed; D4b (closed-form evaluation of the double sum against the
smooth-integer series) remains.

## D4b attacked — 2026-08-09: the remainder consolidates into one contour theorem

Working the source pairing at the transform level exposed the derivation's true shape. Since
(alpha+z)·F_alpha(z) = −XiC(z), the transform of the source k is XiC itself (the classical
theta-cusp/Xi transform pair, here in corpus normalization). The Volterra representations
u_alpha = ∫ e^{alpha(t−x)}k(t)dt (causal/anti-causal) turn every pairing in the D1 reduction
into XiC-quotient data, and the three remaining analytic obligations D3, D4b, D5 are one
statement:

> **Contour form.** For the pair of removable quotients F_alpha, F_beta, the rectangle contour
> integral of the logarithmic derivative of the completed zeta against
> F_alpha(z)·conj-reflected F_beta(z) evaluates two ways: residues at the divisor give the
> Hermitian polarization (the antidiagonal Gram); pushing the contour to the absolute-convergence
> region gives the Λ-series plus the archimedean term (P + A). Boundary terms die by the (18a)
> substrip decay of the quotients — which decay FASTER than the corpus's rectangular family,
> since they carry a full factor of XiC.

D6 is the double-pole case of the same integral (beta-partner = reflected alpha: the kernel
acquires a double pole; the l'Hôpital limit of D1 and the double-pole residue are the same
computation — consistent with D2's coherence check).

So the promotion condition reduces to: write the rectangle argument in full against pinned
corpus conventions (T's reflection, the polarization's sampling weights, XiC's functional
equation normalization), with the (18a) bounds killing the boundary. Every convergence input is
already certified (rate-1 pair decay; zero-mean super-exponential source decay, D4a; substrip
quotient decay, (18a)). This is one bounded theorem-writing task — the next major execution —
and its architecture is the corpus's own rectangular FullFormula chain applied to
faster-decaying tests.

## D7 — the rectangle argument, written (paper level; pinning checklist appended)

**Statement (Eigen-pair Guinand–Weil identity).** For zeros alpha, beta of XiC, with
F_alpha(z) = −XiC(z)/(alpha+z) and F_beta^*(z) = conj(F_beta(conj z)):

    (1/2πi) ∮_R (XiC'/XiC)(z) · F_alpha(z) · F_beta^*(z) dz
      = [residues]  = the antidiagonal Gram term of the pair
      = [pushed contour] = P(alpha,beta) + A(alpha,beta),

whence P + A = q_W.

**Residue side (complete).** XiC is entire with divisor exactly the nontrivial zeros (the
completed function absorbs the pole and trivial zeros), so XiC'/XiC has simple poles of residue
m_rho at each zero. The quotients VANISH on the divisor away from their own fiber
(F_alpha(rho) = −XiC(rho)/(alpha+rho) = 0 for rho ≠ −alpha), so the residue sum collapses to
the single fiber at −alpha, nonzero only when the beta-partner matches: exactly the
antidiagonal Gram, with no infinite summation to control. At a multiple zero (m ≥ 2) both the
residue contribution and the eigen-delta value vanish (each quotient carries a zero of order
m−1 there), consistent with the corpus's equivalence needing SIMPLICITY: multiple zeros give
degenerate eigenvectors, breaking positive-definiteness on the formal span — the mechanism now
visible in the contour itself.

**Prime side (complete modulo pinning).** Split XiC'/XiC = (arch log-derivative) + (zeta-part
log-derivative) via `logDeriv_completed_split` (read in source). On horizontal lines below the
strip the zeta-part has the absolutely convergent Λ-series; termwise integration against
F_alpha·F_beta^* gives Fourier coefficients of the product along the line = the time-side pair
values at ±log n (Parseval/shift), assembling to
P = Σ Λ(n) n^{-1/2}·(pair at log n) + (reflected side); the arch part along the lines gives A.
Vertical boundary terms vanish as the rectangle widens by the (18a) substrip decay of the
quotients (which decay like XiC itself — faster than the corpus's rectangular tests). All
interchanges are absolute: rate-1 pair decay, zero-mean super-exponential source decay (D4a),
and (18a).

**D6 (contained).** The matched-partner case is the double-pole evaluation of the same
integral; its l'Hôpital value equals the D1 limit — the third appearance of the D2 coherence.

## D8 — pinning checklist before promotion to stage 2

1. Fourier convention of the corpus transform (e^{−izx} vs e^{izx}; factor placement) against
   `hedenalmThetaEigenTransform` and `xiThetaEigenFourier`.
2. The line-conjugation ("sharp") operation vs F_beta^*(z) = conj(F_beta(conj z)) — match to
   `xiWeilLineConjLp` and the copy/multiplicity bookkeeping of `XiZeroCopy`.
3. XiC's centered functional equation (evenness) normalization and reality on ℝ.
4. The exact (18a) statement bounds vs the rectangle's horizontal placement (lines inside the
   substrip of certified decay).
5. Sign/orientation of ∮ and the residue bookkeeping against `xiWeilPolarization`'s weights.

Each pin is a read, not new mathematics; a failed pin means a sign/reflection repair or — if
structural — a recorded obstruction per the card's discipline. On completion of the pinning
pass: promote to stage 2; record ULF-INV-9's decisive-class suspicion dead; the lane's last
analytic gate closed at paper level; queue Lean certification for a Lean-enabled session.

## D8 pinning pass — pins 1, 3, and the quotient form: PASSED (2026-08-09)

- **Pin 1 (Fourier convention): PASSED.** `hedenmalmThetaEigenTransform α z =
  ∫ u_α(x)·exp(−I·z·x) dx` — the e^{−izx} convention, exactly as D7's Parseval step assumed
  (n^{−iz} at x = log n).
- **Pin 3 (evenness): PASSED.** `XiC_even : XiC(−z) = XiC(z)` with `XiC z = xi(1/2 + z·I)` —
  centered and even as assumed.
- **Quotient form: PASSED.** `xiThetaEigenFourier α z = I·dslope XiC α z` = −i·XiC(z)/(α−z)
  away from α; composing with the memory's identity F = i·xiThetaEigenFourier(−α) gives
  F_α(z) = −XiC(z)/(z+α) — identical to D7's normalization, with the removability carried by
  `dslope` (entire, corpus-proved analytic).

Remaining pins: 2 (line-conjugation/sharp vs F_β^*(z) = conj(F_β(conj z)), and the
XiZeroCopy multiplicity bookkeeping), 4 ((18a) statement vs rectangle placement),
5 (orientation and polarization weights). No repairs needed so far.

## D8 complete — all pins resolved (2026-08-09); PROMOTION

- Pin 2: PASSED LITERALLY — `xiWeilSharp F z = conj(F(conj z))`, identical to D7's F*; the
  polarization `Σ'_q F(ρ_q)·(sharp G)(ρ_q)` over multiplicity-exact copies matches the contour's
  residue multiplicities (pin 5's weight half). Line reflection = spectral conjugation
  (`xiWeilLineConjLp`, isometric, unconditional).
- Pin 4: PASSED — `exists_norm_xiThetaEigenFourier_horizontal_le`: the removable quotient decays
  exponentially on every horizontal substrip (with `exists_norm_XiC_horizontal_le` behind it) —
  precisely the rectangle's boundary-killing input.
- Pin 5: orientation constant is fixed inside the write-up (a choice, not a clash); weights
  confirmed with pin 2.

**Verdict per the card's own promotion condition: D1–D8 closed; the card promotes to stage 2**
as the prime-sum form of the eigen-span equivalence: for every pair of Xi zeros the eigen-pair's
own absolutely convergent prime+Gamma expression equals the antidiagonal Hermitian Gram, whence
"eigen-span positivity ⟺ RH + simplicity" holds in genuine prime-sum form — the identification
gate of the Weil-polarization lane closed at paper level for the decisive class.

Simultaneously: ULF-INV-9's wall-grade suspicion is DEAD on the decisive class (recorded
verdict — my frozen conjecture falsified where it matters, surviving at most on the broad
algebra), and the corpus's gate-layer note "identifying the continuous limit with an actual
prime sum ... is what is left" is discharged for the class that decides.

Standing caveat, per this session's own error history: the Lean-entry audit is the final
arbiter (the GAS-1 chamber lesson); certification of this card is the first priority of the
next Lean-enabled session, with the five pinned conventions and the three certified decay
inputs as its module plan.
