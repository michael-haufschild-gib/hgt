# Selberg 3/16 through Kloosterman sums over all moduli

- **ID:** SELBERG-316
- **Stage:** 3-formalized
- **Type:** THEOREM (classical) — Lean programme toward the Selberg frontier
- **Source:** `3-formalized/selberg-pretrace-uniform-route.md` (5/36 closed; multiplicity methods stop there).

## Why this route
- Multiplicity + counting (Sarnak–Xue) is capped at 5/36: the exceptional eigenspace of Γ(p) has dimension ≍ p
  (Γ(p)-fixed vectors of the local representation at p), so no better lower bound exists.
- Hecke amplification of the pretrace (paper check, 2026-09-25): with amplifier length L, m ≲ p³e^{-2sR}(e^R/L +
  Le^{2R}/p³); optimising R gives p ≲ p^{6-6s} L^{4s-3}, worse for s > 3/4. **No-go for naive amplification.**
- Arithmetic input beyond density: Selberg's Kloosterman zeta Z(s) = Σ_c S(m,n;c) c^{-2s} has its poles at
  s_j (λ_j = s_j(1-s_j)), and Weil's bound gives absolute convergence for Re s > 3/4, hence λ₁ ≥ 3/16 for every
  congruence level.

## Plan
1. Kloosterman sums over all moduli: twisted multiplicativity for the corpus `Sieve.kloostermanSum`, the prime
   bound (bridge to `kloosterman_weil_bound`), prime-power evaluation (stationary phase), and
   |S(m,n;c)| ≤ τ(c) gcd(m,n,c)^{1/2} c^{1/2}.
2. Poincaré series on Γ₀(N) and their spectral expansion (corpus: level-one Poincaré/Petersson modules).
3. Analytic continuation of Z(s) with poles exactly at the exceptional s_j; convergence for Re s > 3/4.

## Log
- 2026-09-25 — Step 1 (arithmetic side) in Lean: `KloostermanComposite` (built `--old`, wired):
  `kloostermanSum_mul` (twisted multiplicativity via CRT), `kloostermanSum_stationary` (averaging over the units
  1 + p^j w), `norm_kloostermanSum_prime_pow_le` (|S(m,n;p^k)| ≤ 2p^j for odd p, n a unit, k ≤ 2j, j < k).
  Prime level: `EstermannKloostermanSaving.norm_kloostermanSum_le_weil` (built on `kloosterman_weil_bound`).
  With the trivial bound at 2 and at primes dividing mn, Σ_c |S(m,n;c)| c^{-2σ} converges for σ > 3/4.
  Next: absolute convergence of the Kloosterman zeta in Lean, then the spectral side (Poincaré series
  P_m(z,s) on Γ(N), inner products with Maass forms, continuation to Re s > 1/2 with poles at s_j).
- 2026-09-25 — Step 1 closed in Lean: `KloostermanZeta` (built `--old`, wired): `summable_of_submult` (general
  Euler-product summability for submultiplicative functions via `equivProdNatSmoothNumbers`), `kmax_mul`,
  local bounds, and `kloosterman_zeta_summable`: Σ_{c≥1} |S(m,n;c)| c^{-2σ} < ∞ for n ≠ 0, σ > 3/4.
  Next: step 2 — non-holomorphic Poincaré series on Γ(N) (corpus has level-one holomorphic Poincaré/Petersson
  and `PoincareSeriesKloostermanPhase`); their Fourier coefficients in terms of S(m,n;c).

## Spectral half — spectral-theorem-free route (paper plan, 2026-09-25)
Fix an exceptional Γ(N) cusp form u, λ = s₀(1−s₀), s₀ ∈ (3/4, 1), coefficients a_n(y) (corpus `maassCoefficient`).
1. P_m(z,s) = Σ_{γ∈Γ∞\Γ(N)} Im(γz)^s e(m γz/N) converges absolutely for Re s > 1 (mathlib
   `EisensteinSeries.summable_one_div_norm_rpow`), is Γ(N)-invariant.
2. Unfolding: ⟨P_m(·,s), u⟩ = N ∫_0^∞ y^{s−2} e^{−2πmy/N} conj(a_m(y)) dy for Re s > 1.
3. Pole: the modal ODE a'' = (k² − λ/y²)a is regular-singular at 0 with indices s₀, 1−s₀; the decaying solution has a
   nonzero y^{1−s₀} component, so the right side of 2 continues meromorphically with a simple pole at s = s₀
   unless a_m ≡ 0.
4. Continuation of the left side: Poisson summation in d gives P_m(z,s) = y^s e(mz/N) + Σ_n Z_{m,n}(s)-weighted
   Bessel-type integrals, Z_{m,n}(s) = Σ_c S_{Γ(N)}(m,n;c) c^{−2s}; with |S_{Γ(N)}(m,n;c)| ≪ c^{1/2+ε} (reduce
   Γ(N)-Kloosterman sums to `KloostermanZeta`) the expansion continues holomorphically to Re s > 3/4, polynomially
   bounded at the cusps, so ⟨P_m(·,s), u⟩ is holomorphic there.
5. Identity theorem: s₀ > 3/4 forces a_m ≡ 0 for all m, so u = 0. Hence λ₁(Γ(N)) ≥ 3/16 for every N.
Components to build: (1) convergence/invariance; (2) unfolding over Γ∞\Γ(N) (corpus strip unfolding for level one);
(3) Frobenius analysis of the modal ODE at 0; (4) Γ(N)-Kloosterman sums, Poisson summation, Bessel-integral bounds;
(5) assembly.
- 2026-09-25 — Component (1) started: `Σ_{(c,d)≠0} |cz+d|^{-2σ} < ∞` for σ > 1 (scratch `PS.lean`, via mathlib
  `r_mul_max_le` + `summable_one_div_norm_rpow`); next the coset parametrisation Γ∞\Γ(N) ↔ admissible bottom rows,
  the definition of P_m(z,s) and its Γ(N)-invariance.
- 2026-09-25 — Component (1) closed in Lean: `SelbergPoincareSeries` (built `--old`, wired): `Hinf` = ⟨T^N⟩ ≤ Γ(N),
  cosets `Cosets N`, `poincare N m s z`, `term_Hinf`, `rightRel_of_bottom`, `summable_termQ` (Re s > 1),
  `poincare_smul` (Γ(N)-invariance). Next: component (2), unfolding ⟨P_m(·,s), u⟩ against a Γ(N) cusp form via a
  fundamental domain of Γ(N) built from `cellP`-type coset unions and the strip `0 ≤ x < N`.
- 2026-09-25 — Component (2) in Lean: `SelbergPoincareUnfolding` (built `--old`, wired): Γ(N)-action instances,
  `isFundamentalDomain_stripN`, `isFundamentalDomain_cellP_Gamma` (N ≥ 3), general `integral_iUnion_eq_integral_tsum`,
  `poincare_unfold`: ∫_{cellP} P_m(z,s) g = ∫_{0≤x<N} y^s e(mz/N) g for Γ(N)-invariant g, given integrability of the
  strip integrand. Remaining for (2): integrability on the strip (Re s > 1, m ≥ 1, g bounded) and the Fourier
  reduction of the strip integral to N ∫_0^∞ y^{s−2} e^{−2πmy/N} a_{−m}(y) dy.
- 2026-09-25 — `SelbergPoincareIntegrability` (built, wired): majorant integrability on strips and
  `poincare_unfold'` — unfolding with no integrability hypothesis (N ≥ 3, m ≥ 1, Re s > 1, g continuous, bounded,
  Γ(N)-invariant). Next: strip integral → N∫_0^∞ y^{s−2}e^{−2πmy/N} a_{−m}(y) dy (Fubini via corpus
  `setIntegral_modularStrip_eq_iterated`-type lemma for width N), then component (3).
- 2026-09-25 — Component (2) closed: `SelbergPoincarePairing` (built, wired): `strip_integral_eq`,
  `poincare_pairing`: ∫_{cellP} P_m(z,s) g = N ∫_0^∞ y^{s−2} e^{−2πmy/N} a_{−m}(y) dy (N ≥ 3, m ≥ 1, Re s > 1,
  g continuous bounded Γ(N)-invariant). Next: component (3), the pole of the right side at s₀.
- 2026-09-25 — Component (3a) closed: `SelbergModalFrobenius` (built, wired): `frobenius_asymptotics`:
  a(y) = α y^{1−s₀} + O(y^{s₀}) on (0,1] for bounded solutions of y²a'' = (k²y² − s₀(1−s₀))a, 1/2 < s₀ ≤ 1.
  Next (3b), paper-checked: if α = 0 then a ≡ 0. Energy F(y) = Re(ā a') − |a|²/(2y) has
  F' = |a' − a/(2y)|² + (k² + (1/4 − λ)/y²)|a|² ≥ 0, F → 0 at 0 (α = 0 gives a, y a' = O(y^{s₀})) and at ∞
  (|a|² convex, decreasing to 0 ⇒ Re(ā a') → 0), so F ≡ 0 and a ≡ 0. (3c): if α ≠ 0,
  ∫_0^∞ y^{s−2} e^{−cy} conj a(y) dy ~ conj(α)/(s − s₀) as s ↓ s₀.
- 2026-09-25 — Component (3b) closed: `SelbergModalEnergy` (built, wired): `eq_zero_of_energy` (λ < 1/4, energy → 0 at 0⁺,
  a → 0 at ∞ ⇒ a ≡ 0; F ≥ 0 by monotonicity, then (|a|²)' = 2F + |a|²/y ≥ 0), `energy_tendsto_zero`,
  `maassCoefficient_bounded`, `maassCoefficient_leading`: for λ = s₀(1−s₀), 1/2 < s₀ < 1, every coefficient is
  αy^{1−s₀} + O(y^{s₀}) at 0 and α = 0 ⇒ coefficient ≡ 0. `frobenius_asymptotics` now also bounds y a' − s₀ a.

### Component (4) refined plan (paper, 2026-09-25)
Continuation Q(z,s) of P_m(z,s) to Re s > 3/4 (not claimed Γ(N)-invariant a priori; it is, by the identity theorem):
- K1 (arithmetic): S_N(m,n;c) = Σ_{d ∈ (ℤ/|c|N)^×, d ≡ 1 (N)} e(sgn c·(m d̄ + n d)/(|c|N)) for N | c; detecting d ≡ 1 (N)
  by additive characters gives S_N = N^{-1} Σ_t e(−t/N) S(±m, ±(n + t c/N·N); |c|N); a uniform-in-n bound B(c) with
  Σ_c B(c)|c|^{-2σ} < ∞ for σ > 3/4 (Weil at p ∤ 2Nm, trivial at the finitely many bad primes).
- K2: cosets Γ∞\Γ(N) ↔ primitive (c,d) with c ≡ 0, d ≡ 1 (N); a ≡ d^{-1} (mod |c|N); regroup d = d₀ + j|c|N.
- K3: f(x) = (y/(x²+y²))^s e(−m/(c²N(x+iy))) is C², |f''| ≤ y^σ|w|^{-2σ}·poly(|s|, m/N)(|w|^{-2}+|w|^{-4}) (w = x+iy,
  the phase has modulus ≤ 1 since m > 0), so |f̂(ξ)| ≤ ‖f''‖₁/(2πξ)² with ‖f''‖₁ ≤ C_σ y^{1−σ}(y^{-2}+y^{-4})·poly;
  Poisson (`Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`, b = 2σ > 1).
- K4: Q(z,s) = y^s e(mz/N) + Σ_{c ≠ 0, N | c} |c|^{-2s} N^{-1} Σ_n S_N(m,n;c) f̂_c(n/N) e(nx/N): P_m = Q for Re s > 1,
  Q holomorphic in s on Re s > 3/4, |Q(z,s)| ≤ C_K (y^σ + y^{-A}) uniformly on compact K.
- K5: exponential decay of every Γ(N) Maass cusp form at every cusp (per mode: G = |a_n|² convex, G'' ≥ κ²G beyond
  t₀ ⇒ (G' + κG) ≤ 0 ⇒ G ≤ G(t₀)e^{−κ(t−t₀)}; sum by Parseval), so ∫_{cellP} (y^σ + y^{-A})|u| dμ < ∞.
- K6: holomorphy of s ↦ ∫_{cellP} Q(s)u and of R(s) = N∫ y^{s−2}e^{−2πmy/N} a_{−m} (Re s > s₀); identity theorem on
  {Re s > max(s₀, 3/4)}.
- K7: if α ≠ 0, |R(s)| ≥ N|α|e^{−2πm/N}/(s−s₀) − C → ∞ as s ↓ s₀, contradicting continuity of the left side at
  s₀ > 3/4. So every a_{−m} ≡ 0 (m ≥ 1); conj u gives a_m ≡ 0; a_0 ≡ 0; Parseval ⇒ u = 0. Hence no Γ(N) Maass
  cusp form has 0 < λ < 3/16.
- 2026-09-25 — K3 closed: `SelbergPoincareKernel` (built, wired): kernel ker_{β,y,s}(x) = (y/(x²+y²))^s e^{-2πiβ/(x+iy)},
  `norm_ker_le`, explicit first/second derivatives and bounds, `integral_wt_rpow` (= y^{1−σ}C_σ),
  `norm_fourier_ker_le`, `norm_fourier_ker_le_sq` ((2πξ)²|𝓕ker| ≤ D y^{1−σ}C_σ), `tsum_ker_eq_tsum_fourier`
  (Poisson, Re s ≥ 3/4).
- 2026-09-25 — K2 closed: `SelbergPoincareFourier` (built, wired): `term_eq`, `exp_phase_eq`, `range_bot`
  (cosets ↔ admissible rows), `term_of_c_zero` (N ≥ 3), `tsum_eq_sum_residues`, `ker_scale`, `tsum_ker_shift`,
  Γ(N) Kloosterman sum `ksum`, `slice`, and `poincare_eq_Q`: P_m(z,s) = y^s e(mz/N) + Σ_{c≠0} c^{-2s}N^{-s}
  Σ_n 𝓕ker(n) e(nx/N) S_N(m,n;c) for Re s > 1, N ≥ 3. Next: K1 (uniform bound for S_N), then convergence and
  holomorphy of Q on Re s > 3/4 (K4).
- 2026-09-25 — K1 closed: `KloostermanUniform` (general Weil-majorant summability `gw_summable`; `kmaxU`,
  `kmaxU_summable`: Σ_c max_A |S(A,n;c)| c^{-2σ} < ∞ for σ > 3/4, n ≠ 0) and `SelbergKloostermanCongruence`
  (`norm_ksum_le`: |S_N(m,n;c)| ≤ kmaxU(sgn(c)m; |c|N) by additive-character detection of d ≡ 1 (N)).
- 2026-09-25 — K4 closed: `SelbergPoincareContinuation` (built, wired): `differentiableAt_fourier_ker`,
  `norm_fourier_ker_le_uniform`, `summable_cw`, `norm_Qc_le`, `differentiableAt_Q` (Q holomorphic on Re s > 3/4),
  `norm_Q_le_poly` (|Q(z,s)| ≤ C(y^{-6} + y^3) locally uniformly for Re s ≤ 3). Next: measurability of Q in z,
  K5 (cusp decay of u ⇒ ∫_{cellP} (y^{-6}+y^3)|u| < ∞), K6 (identity theorem), K7 (assembly).
- 2026-09-25 — K5 closed: `SelbergMaassExpDecayCell` (built, wired): `normSq_le_exp` (ODE exponential decay via
  H = G' + κG), `mode_decay`, `maass_decay` (|f(z)| ≤ C e^{-π Im z/(N+1)} beyond t₀, by pointwise Fourier inversion),
  `integrableOn_fd`, `im_smul_bound`, `finite_cosets`, `integrableOn_cellP`: (y^{-6}+y^3)|f| ∈ L¹(cellP(N+1)).
  Next: K6 (holomorphy of ∫_{cellP} Q(z,s) f(z) dμ on 3/4 < Re s < 3 and of the Mellin side; identity theorem),
  K7 (assembly).
- 2026-09-25 — K6/K7 closed; **Selberg 3/16 formalized.** `SelbergPoincarePole` (measurability of Q in z,
  `differentiableAt_pairing`, Mellin side `mel`, `differentiableAt_mel`, `J_lower`, `alpha_eq_zero`) and
  `SelbergThreeSixteenths` (`alpha_zero_of_pairing` via the identity theorem on {s₀ < Re s < 3},
  `coefficient_conj` for the positive modes, `selberg_three_sixteenths`: Γ(N+1), N ≥ 2, has no Maass cusp form
  with 0 < λ < 3/16; `selberg_three_sixteenths_all`: every Γ(N), N ≥ 1, by restriction to Γ(4)). Built `--old`,
  wired, axioms propext/choice/Quot.sound, lint passes. The proof uses no spectral theorem: unfolding + Weil +
  Poisson + identity theorem + ODE energy rigidity.
- 2026-09-25 — `selberg_three_sixteenths_congruence`: λ₁ ≥ 3/16 for every congruence subgroup Γ ⊇ Γ(N) (Γ₀(N),
  Γ₁(N), …), by restricting Maass forms to Γ(N).
