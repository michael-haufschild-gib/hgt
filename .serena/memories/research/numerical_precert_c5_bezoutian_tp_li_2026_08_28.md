# Numerical pre-certification: C5 gate, theta Bezoutian ladder, TP order of Phi, Li tower (2026-08-28)

All computations ran on a remote 128-core pod (scripts at `/root/precert/` there; session copies in the
Claude scratchpad `precert/`). Implementations were transcribed **literally from the Lean definitions**
(`thetaCuspSeed/SourceTerm/FullSource/LogSource`, reflected jets from `ThetaCuspGlobalReflectedRiccati`,
`A/D/J/C5` from `ThetaCuspReflectedSourceFifthRootCurvature`, `xi` from `RiemannTower`, Bezoutian from
`XiBezoutianPointedIncidence`, Li tower from `LiPairedPrimeArchShiftedMomentLanding`), smoke-tested
against ∫Phi = xi(1/2) (matches `thetaBilateralLaplace_eq_xiCent` normalization exactly), lambda_1,
evenness, and the two exact C5 identities (`= P^2·action`, `= A^2·barrier`) at every grid point.
Phi evaluated at |x| via the Lean evenness theorem `thetaCuspFullSource_neg` (the literal series has
catastrophic cancellation for x << 0; ~10^7 digits would be needed at x = -8).

## 1. C5(u,t) >= 0 (CLG/TTF rank-four gate) — PASSES with sharp structure

- 58,083 points, u ∈ [0,6] (evenness in u verified), t ∈ (1e-3, 8], dps 40: **zero violations**; y ∈ [0,2] confirmed.
- Margin C5/A^2 ≈ 24 at generic points. Infimum 0 is attained **only** at the coalescence boundary t→0,
  at exact rate coeff(u)·t^4 with coeff ≥ ~633 (minimum at u=0), growing to ~7.7e12 by u=6.
  No interior near-zero manifold exists; the mid-scale danger from the no-go counterexamples does not
  materialize for the literal theta source.
- Criticality ratio G := (9ra+5ra^2+4a^2)/(24r^2+5rb) (a = t·q1, b = t^2·q2, r = e^q−1; C5 ≥ 0 ⟺ G ≤ 1):
  **G → 1 identically as t→0** — the quadratic-jet contributions cancel exactly (num = den = 34q^2 at
  leading order). This is the structural reason the 2026-08-28 Riccati/jet no-gos exist: the inequality is
  leading-order degenerate at coalescence and decided at relative order t^4 (the corpus order-8 jet
  = 1120×Hankel(2,6) theorem).
- **G(u,·) is monotone decreasing in t on every tested fibre** (115-point scans at u ∈ {0, 0.5, 1, 2, 4};
  no violations). G ≤ 0.909 for t ≥ 0.25 on the grid. Candidate proof shape: a theta-specific
  ∂_t G ≤ 0 (or any monotone majorant) reduces global C5 to the closed cusp jet. The binding region is a
  compact neighborhood of (u,t)=(0,0); margins explode in u.

## 2. Bezoutian PSD ladder ranks 2–20 (GORZ red-flag test) — no genuine violation exists

- `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`: B(w,y) = (xic'(w)xic(y)+xic(w)xic'(y))/(w+y),
  nodes Re w > 1/2, entries B(w_j, conj w_k). 3,920 random node systems (moderate/clustered/edge/tall) +
  8 adversarial descents (250 steps each): **zero PSD violations**.
- Every adversarial "negative" was exactly the dps-80 conditioning floor; all 8 endpoints re-verified
  **strictly PD at dps 300** (raw rel margins 1e−130..1e−190 = conditioning; correlation-normalized min
  eigenvalues 0.99 (rank 2) → ~0.008 (rank 20), all positive).
- Margin-vs-rank decay is inherent analytic-kernel spectral decay + node clustering, NOT RH tension.
  The only meaningful GORZ red flag is a sign flip that survives precision escalation; none exists.
- Detection sensitivity: rank-2 nodes straddling gamma_1 (±0.1) at Re = 1/2+eps keep correlation margin
  ≈ 1.3e−3 stable as eps → 1e−4. Individual on-line zeros are resolved far above noise.

## 3. TP order of the translation kernel Phi(x−y) — breaks exactly at order 5

- TP2: 120k random minors ✓ (consistent with Lean `thetaCuspLogConcavityNumerator_neg_all`),
  TP3: 100k ✓, TP4: 100k ✓ — zero violations (widths up to 3, centers in [−2,2], dps 40).
- **TP5 FAILS**: violations found (4/40k at widths ≤ 6), re-confirmed at dps 150 (normalized minors
  ≈ −1e−12), at ordinary near-diagonal configurations (nodes within width-1 windows, e.g. around x≈3 and
  around x≈0). TP6: 94/40k, TP7: 117/40k, TP8: 38/40k, all resolved.
- A priori argument why a finite break is forced: Phi cannot be PF_infinity — Schoenberg would force its
  bilateral Laplace transform to be 1/(LP-entire); but the transform is xiCent, entire WITH zeros.
- Strategic reading: the "free" total-positivity budget of the literal theta kernel ends **exactly at
  order 4 — the same order as the CLG rank-four wall**. Four-point/rank-4 structures (C5) sit inside the
  generically-provable zone; packets of order ≥ 5 cannot be closed by translation-kernel total positivity
  and need the reflected/completed (Fourier-side, RH-strength) mechanism — sharp numerical localization
  of where RH content begins, consistent with the frontier map's "rank-four closure would still not prove
  higher packets".

## 4. Li tower health (LI route)

- lambda_d > 0 for all d ≤ 300, computed from 4,000 zeros with RvM tail estimate subtracted; minimum
  ratio lambda_d / RH-asymptotic = 0.953 (at d ≈ 270), trending to 1. Head matches Keiper values.
- Shifted tower m_k = Σ 2 u_q^{k+1}, u_q = 1/(gamma^2+1/4) ∈ (0, ~5.0e−3]: Hankel H0 and the [0,4]-side
  H1 = (4m_{j+k} − m_{j+k+1}) both **PD through size 12 at dps 150** (rel margins 1e−17 at N=4 down to
  1e−74 at N=12 — pure atom-clustering decay, not RH tension; dps-30 runs show spurious negatives beyond
  N=6, so always escalate precision before reading Hankel signs here).

## Verdict for the route ranking

The theta-positivity complex assumptions survived pre-certification and sharpened: the C5 finite gate is
numerically safe with compact tight region and two proof-shaping facts (leading-order G-degeneracy at the
cusp; global G-monotonicity in t). The master-mechanism hypothesis is REFINED, not confirmed: kernel total
positivity is not the master law (breaks at order 5); the viable master object is the reflected/Bezoutian
positivity itself, with C5/rank-4 the last gate reachable by finite-order theta structure.

Recommended next: (1) paper-attack ∂_t G ≤ 0 using the corpus source signs (L4>0, L5<0, L6>0) and the
strict second–sixth Hankel margin; (2) try to derive the four-point odd wall from TP4-adjacent minors of
translates (TP4 empirically true; would need its own Lean proof — finite-order, non-RH-strength);
(3) do NOT invest in TP_m mechanisms for m ≥ 5 — provably (numerically) dead.
