# Petersson pairing of Γ(N) Poincaré series with the Kloosterman side (Kuznetsov without the spectral theorem)

- **ID:** SELBERG-PP-KLOOSTERMAN
- **Stage:** 1-in-progress
- **Type:** THEOREM programme (infrastructure for every route past 3/16)
- **Source:** `3-formalized/selberg-three-sixteenths-kloosterman.md`; `5-failed/selberg-multiplicity-pole-density.md`.

## Target
⟨P_m(·,s), P_n(·,s')⟩ = δ_{mn}·(diagonal Γ-integral) + Σ_{c≠0} c^{-2s'} N^{-s'} S_N(n,m;c) · (Mellin transform of the
kernel Fourier transform), with every term explicit and absolutely convergent, for Re s > 1 and Re s' > 2. This is
the arithmetic side of a Petersson/Kuznetsov formula for Γ(N). The density, large-sieve and Linnik–Selberg routes
past 3/16 all go through it.

## Log
- 2026-09-25 — `SelbergPoincareBounded` (built, wired, axioms clean): `continuous_poincare` (Re s > 1),
  `summand_le`, `poincare_bounded` (m ≥ 1, Re s > 2), `poincare_pairing_poincare`:
  ⟨P_m(s), P_n(s')⟩ = N ∫ y^{s−2} e^{−2πmy/N} conj(a_m(P_n(·,s'))(y)) dy.
  Next: the m-th Fourier coefficient of P_n(·,s') from `poincare_eq_Q`: integrate the Q-series term by term over one
  period (Fubini, using the absolute bounds of `norm_Qc_le`), which gives δ_{mn} y^{s'} e^{−2πny/N} +
  Σ_c c^{−2s'} N^{−s'} 𝓕ker_c(m) S_N(n,m;c).
- 2026-09-25 — `SelbergPeterssonKloosterman` (built, wired, no warnings): `coeff_tsum`, `coeff_tsum_characters`,
  `kcoef` (B_{c,m} = c^{-2s}N^{-s}𝓕ker_c(m)S_N(n,m;c)), `norm_kcoef_le`, `coefficient_Q`
  (a_m(Q_n(·,s))(y) = δ_{mn} y^s e^{−2πny/N} + Σ_c B_{c,m}(y) for Re s > 3/4), and `petersson_kloosterman`: the full
  arithmetic side ⟨P_m(s), P_n(s')⟩ = N∫ y^{s−2}e^{−2πmy/N} conj(δ_{mn}y^{s'}e^{−2πny/N} + Σ_c B_{c,m}(y)) dy,
  for N ≥ 3, m, n ≥ 1, Re s > 1, Re s' > 2.
  Next: split into the diagonal Γ-integral plus the Kloosterman series (Fubini in (y, c)), then evaluate the Mellin
  transform of 𝓕ker_c(m) in closed form (a Bessel-type integral), giving the Kloosterman-zeta side of Kuznetsov.
- 2026-09-25 — `SelbergPeterssonSplit` (built, wired, no warnings, axioms clean): `norm_kcoef_le'`, `Fc`, `norm_Fc_le`,
  `integrableOn_Fc`, `F0`, `integral_F0` (diagonal = (N/4πm)^{s+s̄'−1}Γ(s+s̄'−1)), `petersson_split`:
  ⟨P_m(s),P_n(s')⟩ = N(δ_{mn}(N/4πm)^{s+s̄'−1}Γ(s+s̄'−1) + Σ_c ∫_0^∞ Fc_c(y) dy), for N ≥ 3, m, n ≥ 1, 2 < Re s' < Re s.
  Next (paper first): does positivity of ‖Σ_m x_m P_m‖² combined with this formula give a density or large-sieve
  statement for exceptional coefficients that beats 3/16 on average over m? Decide before any more Lean.
- 2026-09-25 — Paper check of "positivity of ‖Σ_m x_m P_m(s)‖² + petersson_split ⇒ averaged bound beating 3/16":
  **FAILED.** Bessel against any combination of cusp-∞ Poincaré series at s → 1⁺ only sees the exceptional forms
  through their mass in the ∞-cusp region. At level p that is a share of about p^{-2} of the total, while
  the diagonal is about p²/m. Averaging over m changes the constants, not the power of p. This is the same loss of
  a factor about p² recorded in `5-failed/selberg-multiplicity-pole-density.md`. Density results past 3/16 (Iwaniec,
  Huxley, Sarnak–Xue) need either a test function whose Kloosterman side can be taken with φ concentrated at small
  argument (the full Kuznetsov inversion, i.e. the spectral theorem for Γ(N)\ℍ including Eisenstein series), or
  averaging over the level. Neither can be reached from the Petersson identity alone.
