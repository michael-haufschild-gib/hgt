# Eisenstein series of Γ(N): continuation to Re s > 1/2 from the Fourier–Kloosterman expansion

- **ID:** SELBERG-EIS-CONT
- **Stage:** 1-in-progress
- **Type:** THEOREM programme (step 1 of the spectral decomposition of L²(Γ(N)\ℍ), the prerequisite for Kuznetsov)
- **Source:** `1-in-progress/selberg-poincare-petersson-kloosterman.md`; corpus `SelbergPoincareFourier` (the expansion
  holds for every m ≥ 0, so m = 0 is the Eisenstein series at ∞); Ramanujan-sum assets
  (`cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum`, `KloostermanRamanujanDivisorSum`).

## Plan (paper)
E(z,s) = P_0(z,s) = y^s + Σ_{c≠0} c^{-2s} N^{-s} Σ_n 𝓕ker_{0,y/N,s}(n) S_N(0,n;c) e(nx/N).
- n ≠ 0: S_N(0,n;c) is a restricted Ramanujan sum; |S_N(0,n;c)| ≤ gcd-type bound ⇒ Σ_c |S_N(0,n;c)| c^{-2σ}
  converges for σ > 1/2, with polynomial dependence on n. 𝓕ker_0(n) = K-Bessel, decaying exponentially in |n|y.
  So the non-constant part continues holomorphically to Re s > 1/2 (absolute convergence; no Weil needed).
- n = 0: φ_N(s) y^{1-s} with φ_N(s) = (Γ-factor) · Σ_c S_N(0,0;c) c^{-2s}. This Dirichlet series is an explicit
  ζ(2s−1)/ζ(2s)-type expression (Euler product over p ∤ N, finite correction at p | N); meromorphic, with a simple
  pole at s = 1 and holomorphic on 1/2 < Re s < 1 (ζ(2s) ≠ 0 there).
- Deliverables: (1) the restricted Ramanujan bound; (2) the constant-term Dirichlet series in closed form; (3) E(z,s)
  meromorphic on Re s > 1/2 with at most a simple pole at 1; (4) the Maass–Selberg relation for truncated E. These
  are the Eisenstein inputs of the spectral decomposition.

## Log
- 2026-09-25 — created. Corpus check: Ramanujan-sum divisor identities present; Fourier–Kloosterman expansion valid
  for m = 0; continuation lemmas currently require m ≠ 0 (Weil majorant), so m = 0 needs the Ramanujan majorant.
- 2026-09-25 — Paper bookkeeping for deliverable (1):
  - Detection (as in `norm_ksum_le`) gives ‖S_N(0,n;c)‖ ≤ max_t |c_K(εn + t|c|)|, where K = |c|N and c_K is the
    Ramanujan sum.
  - |c_K(a)| ≤ gcd(a,K), and gcd(εn + t|c|, |c|N) ≤ N·gcd(n,|c|) ≤ N|n|: the part of the gcd dividing |c| also
    divides n, and the cofactor divides N.
  - So ‖S_N(0,n;c)‖ ≤ N|n|, uniformly in c. The c-sum converges for σ > 1/2.
  - The n-sum then needs Σ|n||𝓕ker_0(n)| < ∞, i.e. 𝓕ker decaying faster than n^{-2}. The current kernel module
    gives only n^{-2} (two integrations by parts).
  - **Needed next:** the fourth-derivative bound for ker_{0,y,s} = exp(s·log(y/(x²+y²))), where
    f'''' = (sL4 + 4s²L1L3 + 3s²L2² + 6s³L1²L2 + s⁴L1⁴) f with |L_k| ≤ C_k y^{-k}, giving |𝓕ker_0(ξ)| ≪ ξ^{-4}.
    Alternatively the K-Bessel closed form with exponential decay.
- 2026-09-25 — `SelbergEisensteinKernel` (built, wired, no warnings): L''', L'''' bounds, derivative chain h₁…h₄,
  `norm_fourier_ker0_le_four`: (2πξ)⁴|𝓕ker_{0,y,s}(ξ)| ≤ 109((1+|s|)/y)⁴ y^{1−σ}C_σ. Next: the Ramanujan bound
  ‖S_N(0,n;c)‖ ≤ N|n| (detection plus |c_K(a)| ≤ gcd(a,K), via the corpus Möbius-divisor formula).
- 2026-09-25 — `SelbergRamanujanBound` (built, wired, no warnings): `norm_kloostermanSum_zero_le`
  (|S(a,0;K)| ≤ gcd(a,K)²), `gcd_le`, `norm_ksum_zero_le`: |S_N(0,n;c)| ≤ (N|n|)² uniformly in c (n ≠ 0).
  Deliverable (1) done. Next: continuation of the non-constant part E*(z,s) = Σ_{c≠0} c^{-2s}N^{-s}
  Σ_{n≠0} 𝓕ker_0(n) S_N(0,n;c) e(nx/N) to Re s > 1/2 (Σ_c |c|^{-2σ} with σ > 1/2, and Σ_n n²·n^{-4}).
- 2026-09-25 — `SelbergEisensteinStar` (built, wired, no warnings): `eterm`, `Estar`, `norm_eterm_le`,
  `differentiableAt_Estar`: the non-constant part E*(z,s) is holomorphic on Re s > 1/2. Next: identify
  E(z,s) = y^s + φ_N(s) y^{1−s} + E*(z,s) for Re s > 1 (from `poincare_eq_Q` with m = 0: split off the n = 0 terms),
  with φ_N(s) = N^{-s} 𝓕ker_0(0)·Σ_c S_N(0,0;c)|c|^{-2s}, and 𝓕ker_0(0) = y^{1−s}√π Γ(s−1/2)/Γ(s).
- 2026-09-25 — `SelbergEisensteinDecomposition` (built, wired, no warnings): `cterm`, `Qc_split`,
  `norm_ksum_le_trivial`, `summable_eterm`, `summable_cterm`, `eisenstein_decomp`: for N ≥ 3, Re s > 1,
  E(z,s) = y^s + Σ_c cterm_c(z,s) + E*(z,s). Next: (2) closed form of Σ_c cterm_c = φ_N(s) y^{1−s}:
  𝓕ker_0(0) = (y/N)^{1−s}√πΓ(s−1/2)/Γ(s) (Beta integral) and the Dirichlet series Σ_c S_N(0,0;c)|c|^{-2s} as an Euler
  product (ζ(2s−1)/ζ(2s) times finitely many local factors at p | N), which gives meromorphic continuation to
  Re s > 1/2 with a single simple pole at s = 1.
- 2026-09-25 — `SelbergRamanujanZeroZero` (built, wired): `card_ker_unitsMap`, `ksum_zero_zero`:
  S_N(0,0;c)·φ(N) = φ(|c|N) for N | c. Plan for the constant term (paper, checked):
  - φ(N²n) = N·φ(Nn), and φ(Nn) = φ(N)·Σ_{d|n, (d,N)=1} μ(d)(n/d).
  - Hence Σ_n φ(N²n) n^{-2s} = Nφ(N)·M_N(2s)·ζ(2s−1), where M_N(w) = Σ_{(d,N)=1} μ(d)d^{-w} converges absolutely on
    Re w > 1.
  - So the constant term continues to Re s > 1/2 with its only pole at s = 1, the pole of ζ(2s−1). This needs
    neither ζ(2s) ≠ 0 nor an explicit Euler product.
- 2026-09-25 — `TotientMulMoebius` (built, wired, no warnings): `H`, `chi`, `Hf`, `Hf_mult`, `Hf_eq`, `H_prime_pow`,
  `totient_mul_self_pow`, `totient_mul_coprime_split`, `totient_mul_eq`: φ(Nn) = φ(N)·Σ_{e|n,(e,N)=1} μ(e)(n/e).
  Next: the Dirichlet-series rearrangement Σ_n φ(N²n)n^{−w} = Nφ(N)·M_N(w)·ζ(w−1) for Re w > 2, then the continued
  constant term and E(z,s) − y^s meromorphic on Re s > 1/2 with its only pole at s = 1.
- 2026-09-25 — `TotientMulLSeries` (built, wired, no warnings): `LSeries_id_eq` (L(id, w) = ζ(w−1)), `muChi`,
  `summable_muChi` (Re w > 1), `H_eq_conv`, `LSeries_H`, `LSeries_totient_mul`:
  Σ_n φ(Mn)n^{−w} = φ(M)·L(μχ_M, w)·ζ(w−1) for Re w > 2.
  Next: reindex Σ_c cterm_c (c = ±Nc') into the Dirichlet series with M = N², w = 2s, and define the continued
  constant term φ_N(s,y) = 2N^{−3s}φ(N²)/φ(N)·𝓕ker_0(0)·L(μχ, 2s)·ζ(2s−1), holomorphic on Re s > 1/2 except at s = 1.
- 2026-09-25 — **Eisenstein continuation closed**: `SelbergEisensteinContinuation` (built, wired, no warnings, axioms
  clean): `cterm_neg`, `cterm_nat`, `tsum_cterm`, `constTerm`, `eisenstein_eq` (E(z,s) = y^s + constTerm(s,z) +
  E*(z,s) for N ≥ 3, Re s > 1), `differentiableAt_constTerm` (holomorphic on Re s > 1/2, s ≠ 1). Together with
  `differentiableAt_Estar`, E(z,s) − y^s continues meromorphically to Re s > 1/2 with at most a pole at s = 1.
  Deliverables (1)–(3) done. Remaining: (4) Maass–Selberg relation for the truncated Eisenstein series; then the
  continuous spectrum, spectral decomposition, and Kuznetsov.
- 2026-09-25 — Corpus check for deliverable (4):
  - The level-one Maass–Selberg relation already exists: `EisensteinMaassSelbergRegion.maassSelberg_region`, for the
    SL₂(ℤ) Eisenstein line model on 𝒟 in the absolutely convergent region. Its method (truncation identity, unfold
    the row sum to the strip slab, one-dimensional cusp and slab integrals) is the template for Γ(N).
  - No spectral decomposition or Kuznetsov formula exists in the corpus at any level; the searches found none.
  - Next: port the Maass–Selberg argument to Γ(N) at the cusp ∞, using `SelbergPoincareUnfolding` (strips and cellP),
    `eisenstein_eq` and the constant term `constTerm`.
- 2026-09-25 — Maass–Selberg for Γ(N) requires the constant terms of E_∞ at *every* cusp a = σ∞ (σ ∈ SL₂(ℤ)),
  i.e. the scattering entries φ_{∞a}(s). Plan (paper):
  - E_∞(σz, s) = Σ over primitive bottom rows (c,d) ≡ (σ₁₀, σ₁₁) mod N of (Im z/|cz+d|²)^s. This is the
    `SelbergPoincareFourier` regrouping with the admissible class (0,1) mod N replaced by (σ₁₀, σ₁₁) mod N.
  - The y^s term appears iff σ₁₀ ≡ 0 (N).
  - Constant term: φ_{∞a}(s) y^{1−s} with φ_{∞a}(s) = (Γ-factor)·Σ_c #{d mod |c|N : (c,d) ≡ (σ₁₀,σ₁₁), (c,d)=1}|c|^{-2s},
    a finite combination of ζ(2s−1)/ζ(2s)-type Dirichlet series (Ramanujan counts with congruence conditions).
  - Deliverables: (4a) regrouping for a general residue class of bottom rows (refactor of `adm`, `slice`,
    `poincare_eq_Q`); (4b) the count and Dirichlet series for each class; (4c) the truncated E_∞^Y at all cusps and
    the Maass–Selberg relation, following `EisensteinMaassSelbergRegion` (level one).
- 2026-09-25 — (4a) started: `SelbergEisensteinCusp` (built, wired): `botσ`, `botσ_injective`, `esum`, `termQ_smul`,
  `poincare_smul_eq` (E_∞(σz,s) as a lattice sum), `rowMul`, `range_botσ` (rows = adm·σ). Next: the constant term
  at σ∞: integrate over one period, group d by residues mod |c|N, and compute the count
  #{d mod |c|N : (c,d) ∈ adm·σ} and its Dirichlet series (Hurwitz/character sums when σ₁₀ ≢ 0 mod N).
- 2026-09-25 — `SelbergEisensteinCuspRows` (built, wired, no warnings): `rowMul_mul`, `rowMul_inv`, `mem_image_iff`,
  `isCoprime_rowMul`, `rowMul_add_shift`, `mem_image_shift` (admissibility at σ∞ is |c|N-periodic in d),
  `hasSum_translates` (period-T translate integrals sum to ∫_ℝ). Next: the constant term at σ∞ for Re s > 1:
  (1/N)∫_0^N E_∞(σ(x+iy),s) dx = δ y^s + (1/N) y^{1−s} C(s) Σ_{c≠0} |c|^{-2s} #{d mod |c|N admissible at σ∞}.
- 2026-09-25 — `SelbergEisensteinCuspSlice` (built, wired, no warnings): `esumxy_eq` (row summand = (c²)^{-s}·ker₀(x+d/c)),
  `Gc_eq`, `hasSum_translates_sign`, `countσ`, `hasSum_Gc`: Σ_d ∫_0^N (row summand) dx = (c²)^{-s}·countσ(c)·∫_ℝ ker₀
  for c ≠ 0, Re s > 1/2. Next: sum over c (interchange tsum/integral) to get the constant term at σ∞.
- 2026-09-25 — `SelbergEisensteinCuspConstant` (built, wired, no warnings; axioms propext/choice/Quot.sound):
  `integral_poincare_cusp`: for Re s > 1, ∫_0^N E_∞(σ(x+iy), s) dx = N·count₀·y^s + (Σ_c (c²)^{-s} countσ(c))·∫_ℝ ker₀,
  count₀ = #{d = ±1 : (0,d) a row at σ∞}. Interchange by `integral_tsum_of_summable_integral_norm` with row
  majorant (c²)^{-Re s}·|c|N (`weight_le`, `summable_weight`). Next: rows at σ∞ = primitive rows ≡ (σ₁₀, σ₁₁) mod N;
  countσ(c) = [c ≡ σ₁₀ (N)]·|c|·Π_{p|c, p∤N}(1 − 1/p); Dirichlet series = Σ_{(e,N)=1} μ(e)e^{-2s}·(Hurwitz ζ at 2s−1
  in the class σ₁₀ē mod N); continuation to Re s > 1/2, s ≠ 1.
- 2026-09-25 — `CoprimeClassCount` (built, wired): `card_coprime_class_mul_totient`: (gcd(n,N), b) = 1 ⇒
  #{r mod nN : r ≡ b (N), (r,n)=1}·φ(N) = φ(nN) (Möbius + CRT, via `totient_mul_eq`). `SelbergEisensteinCuspCount`
  (built, wired): `mem_image_congr` (rows at σ∞ = primitive rows ≡ (σ₁₀,σ₁₁) mod N), `countσ_mul_totient`:
  countσ(c)·φ(N) = [c ≡ σ₁₀ (N)]·φ(|c|N). Next: D_σ(s) = Σ_c (c²)^{-s}countσ(c) as Σ_{u∈(ℤ/N)^×} L(μχ_N δ_u, 2s)·
  L(δ_{±σ₁₀u⁻¹}, 2s−1) (ZMod.LFunction) ⇒ meromorphic continuation to Re s > 1/2, pole only at s = 1.
- 2026-09-25 — `SelbergEisensteinCuspScattering` (built, wired, no warnings; axioms clean): `countσ_eq`
  (countσ(c) = [c ≡ σ₁₀]·H_N(|c|)), `tsum_weight_eq` (Σ_c (c²)^{-s}countσ(c) = L(H_N Φ_σ, 2s), Φ_σ = δ_{σ₁₀}+δ_{−σ₁₀}),
  `LSeries_H_mul` (L(H_N Φ, w) = Σ_{u∈(ℤ/N)^×} L(μχ_N δ_u, w)·L(Φ(u·), w−1) via ZMod.LFunction), `Dσ`,
  `tsum_weight_eq_Dσ`, `differentiableAt_Dσ` (holomorphic on Re s > 1/2, s ≠ 1).
  Next: ∫ker₀ = y^{1−s}·√π Γ(s−1/2)/Γ(s); the constant term of E_∞ at σ∞ for Re s > 1/2 by continuation.
- 2026-09-25 — `SelbergEisensteinScatteringEntry` (built, wired, no warnings): `integral_ker0_scale`
  (∫(y/(x²+y²))^s dx = y^{1−s}C(s)), `phiσ = Dσ·C`, `differentiableAt_phiσ` (holomorphic on Re s > 1/2, s ≠ 1),
  `integral_poincare_cusp_phi`: ∫_0^N E_∞(σ(x+iy),s)dx = N·count₀·y^s + φ_{∞,σ∞}(s)·y^{1−s} (Re s > 1).
  Next: pass the identity to Re s > 1/2 (needs s-analyticity of ∫_0^N E^cont(σ(x+iy),s)dx: locally uniform bounds on
  E* and constTerm), then the truncated Eisenstein series and Maass–Selberg for Γ(N).
- 2026-09-25 — `CoprimeClassRamanujan` (built, wired): |Σ_{r mod n'N, r≡b (N), (r,n')=1} e(nr/(n'N))| ≤ n² uniformly in n'
  (Möbius + CRT + geometric sums). `SelbergEisensteinCuspFourier` (built, wired): `sliceσ` (Poisson for the row c
  at σ∞), `ksumσ`, `norm_ksumσ_le` (|S_σ(0,n;c)| ≤ n²), `norm_etermσ_le`, `differentiableAt_Estarσ`.
  `SelbergEisensteinCuspExpansion` (built, wired, axioms clean): `poincare_smul_expansion` (Re s > 1) and
  `Econt_smul_eq` (N ≥ 3, Re s > 1/2, s ≠ 1): the continued E_∞(σz,s) = count₀ y^s + N^{-s}(y/N)^{1−s}φ_{∞,σ∞}(s)
  + E*_σ(z,s), each term holomorphic; via identity theorem on the punctured half-plane (`isPreconnected_punctured`).
  This is the Fourier expansion of the continued Γ(N) Eisenstein series at every cusp.
  Next: Maass–Selberg relation for Γ(N) (truncated E_∞ norm) using these constant terms.
- 2026-09-25 — `SelbergKernelBessel` (built, wired): `fourier_ker0_eq_bessel`: 𝓕ker₀_{y,s}(ξ) = y^s·2π^s/Γ(s)·(|ξ|/y)^{s−1/2}
  ·K_{s−1/2}(2πy|ξ|) on Re s > 1/2 (from the corpus Gamma–Bessel transform at Re s > 1 + identity theorem); the Bessel
  side `kerBessel` is entire in s. `SelbergKernelBetaIntegral` (built, wired): ∫(1+t²)^{-s} = √πΓ(s−1/2)/Γ(s) on Re s > 1/2.
  PLAN (E on the critical line Re s = 1/2, s ≠ 1/2):
  Q2a  L_u(w) = Σ_{e≡u} μ(e)e^{-w} = φ(N)^{-1}Σ_χ χ̄(u)/L(w,χ); holomorphic near Re w ≥ 1, w ≠ 1 (mathlib nonvanishing).
  Q2b  ksumσ(c,n) = [c≡σ₁₀]Σ_{e|c,(e,N)=1} μ(e)[M|n]·M·ψ((sgn c·n/M)·σ₁₁·ē), M = |c|/e, ψ = std additive char of ℤ/N.
  Q2c  D_n(s) = Σ_c|c|^{-2s}ksumσ(c,n) = Σ_± Σ_{M|n} M^{1−2s} Σ_u F_{±,M}(u) L_u(2s); continuation near the line.
  Q3   E*_ext(z,s) = Σ_{n≠0} N^{-s}kerBessel(y/N,s,n)e(nx/N)D_n(s); locally uniform bounds (K-Bessel decay, d(n)n^{2δ}).
  Q4   identity with Econt on Re s > 1/2; constant term via cBeta and ζ(2s−1)/L(2s,·).
- 2026-09-25 — Q2 done. `CoprimeClassExact` (exact class sums), `SelbergMoebiusUnitClassL` (L_u(w) = φ(N)^{-1}Σ_χ χ̄(u)/L(w,χ),
  holomorphic on Re w ≥ 1, w ≠ 1), `SelbergEisensteinCoefficientSeries` (`tsum_ksumσ_eq_Dn`: Σ_c|c|^{-2s}S_σ(0,n;c) = D_n(s)
  on Re s > 1/2; `differentiableAt_Dn` off zeros of L(2s,χ), 2s ≠ 1; `differentiableAt_Dn_of_half_le` on Re s ≥ 1/2,
  s ≠ 1/2; `norm_Dn_le`). All built, wired, axioms clean. Next: Q3 (E*_ext and its holomorphy near the line).
- 2026-09-25 — Q3/Q4 DONE. `SelbergEisensteinStarCriticalLine` (built, wired): `Wset` (open: Re s > 0, 2s ≠ 1, L(2s,χ) ≠ 0 ∀χ),
  `EstarExt` = Σ_{n≠0} N^{-s}·kerBessel·e(nx/N)·D_n(s), `Estarσ_eq_EstarExt` (Re s > 1/2), `differentiableAt_EstarExt` on W
  (Bessel envelope + D_n growth + Cauchy-dominated tsum). `SelbergEisensteinCriticalLine` (built, wired, axioms clean):
  `phiExt` (continued scattering entry), `EcuspExt`, `Econt_smul_eq_EcuspExt` (N ≥ 3) and
  `differentiableAt_EcuspExt_of_half_le`: every Γ(N) Eisenstein series E_∞(σz,s) is holomorphic on a neighbourhood of
  {Re s ≥ 1/2} \ {1/2, 1}, in particular on the critical line minus s = 1/2.
  Next toward Kuznetsov: (i) behaviour at s = 1/2 and the functional equation/unitarity of the scattering matrix on the line;
  (ii) Maass–Selberg for Γ(N) (truncated L² norms on the line); (iii) spectral decomposition. Very long road.
- 2026-09-25 — PLAN MS-N (Maass–Selberg for Γ(N), coset-sum form over the level-one cell 𝒟 = fd):
  (A) pairing over Γ(N)\ℍ = ∫_𝒟 Σ_{q∈SL₂(ℤ)/Γ(N)} F(q̃z)G(q̃z) (generalize SarnakXueInner/Pretrace from eigenfunctions).
  (B) for z ∈ 𝒟: E_u(q̃z) = count₀(q)y^u + N^{-u}(y/N)^{1−u}φ_q(u) + E*_q(u,z) (= `Ecusp`, σ = q̃).
  (C) Λ^Y at coset level: L_q(u,Y,z) = E_u(q̃z) − [y>Y](count₀(q)y^u + N^{-u}(y/N)^{1−u}φ_q(u)).
  (D) zero mean: Σ_q ∫_{𝒟∩{y>Y}} E*_q(u,z)·c_q(v,y) dμ = 0, grouping q by right T-translates (E*_{qT^j}(u,z) = E*_q(u,z+j),
      count₀ and φ invariant under q ↦ qT^j) so the N width-1 pieces make a full period of e(nx/N), n ≠ 0.
  (E) unfolding: Σ_q Σ_{γ∈Γ∞(N)\Γ(N)} f(γq̃z) = Σ_{δ∈⟨T^N⟩\SL₂(ℤ)} f(δz); ∫_𝒟 Σ_δ = 2∫_{strip width N}.
  (F) slab/cusp integrals → Maass–Selberg in the region Re u > Re v > 1/2, then continuation.
- 2026-09-25 — MS-N (E) generalized: `SelbergSeedUnfolding.seed_unfold` (built, wired): ∫_{cellP}(Σ_q F(qz))g = ∫_{strip} F g
  for any ⟨T^N⟩-invariant seed F. Next: truncation Λ^Y on cellP = ⋃_c R_c·fd via cusp pieces R_c(fd ∩ {y > Y}),
  the row-height bound on fd (rows with c ≠ 0 have height ≤ 1, corpus `rowHeight_le_one_of_mem_fd`), truncation identity.
- 2026-09-25 — MS-N (C/E): `SelbergTruncationIdentity` (built, wired): `truncation_identity`: for w ∈ fd, Y ≥ 1,
  E_∞(σw,u) = rowSumY(u)(σw) + [Im w > Y]·count₀(σ)·(Im w)^u (rows with c ≠ 0 have height ≤ 1 on fd).
  Remaining MS-N steps: coset-sum integral ∫_{cellP} F = Σ_c ∫_fd F(R_c w) (PSL cosets; Deck = 2× PSL cosets for N ≥ 3);
  T-orbit structure c ↦ cT^j (orbits of size N) and E*_{σT^j}(u,w) = E*_σ(u,w+j) ⇒ zero mean of E* over the orbit;
  slab (seed_unfold) and cusp integrals; final formula.
- 2026-09-25 — MS-N (D) infrastructure: `SelbergCellCosetShift` (∫_{cellP} F = ∫_fd Σ_c F(R_c w); right T-shift `shEquiv` on
  cosets; F(R_{cT}w) = F(R_c(w+1)); N-periodicity) and `SelbergCusppieceAveraging` (`finite_cosets`, `avg_sum`,
  `F_out_iterate`, `sum_shift_integral`: the N shifted width-one pieces make one period). Built, wired.
  Next: CT_c(u,y) := N^{-1}∫_0^N E_u(R_c(x+iy))dx (shift-invariant, = count₀y^u + N^{-1}φ(u)y^{1−u}); cusp-tail Fubini on
  fd ∩ {y > Y} = [−1/2,1/2]×(Y,∞); Step 1 zero-mean; slab/cusp integrals.
- 2026-09-25 — `SelbergCuspConstantTerm` (built, wired): `CT` (constant term at R_c∞), `integral_eq_CT`, `CT_sh`, `poincare_sub_CT`
  (E_∞(R_c z,u) − CT_c(u,Im z) = E*_{σ_c}(u,z)). Next: `norm_Estarσ_le` (≤ K y^{−3−Re u}) and Step 1 zero-mean lemma.
- 2026-09-25 — `SelbergCuspZeroMean` (built, wired): `norm_Estarσ_le` (|E*_σ| ≤ S₁S₂·econst(Im z)), `sum_weighted_row_mean_zero`
  (Σ_c g_c(∫_{-1/2}^{1/2}E(R_c(x+iy))dx − CT_c(y)) = 0 for shift-invariant g). Remaining MS-N: the 2D assembly —
  I_Y(u,v) = Σ_c ∫_fd L_c(u)L_c(v), Step 1 via Fubini on cuspRect + zero mean, Step 3–4 (truncation identity + seed_unfold on
  the slab), cusp integrals with CT_c(v), final algebra; econst ≲ y^{−3−σ} for integrability.
- 2026-09-25 — `SelbergMaassSelbergSlab` (built, wired): `norm_poincare_le`, `integral_row_eq`, `integral_norm_row_le`,
  `integrableOn_slabG`, `slab_eq`: ∫_{strip}[y ≤ Y]y^u E(z,v) = N Y^{u+v−1}/(u+v−1) + φ_{∞∞}(v)Y^{u−v}/(u−v) (1 < Re v < Re u).
  Remaining: (i) integrability of seedY·E_v on the strip (for seed_unfold) — follows from slabG integrability;
  (ii) cusp integrals Σ_c b_c(u)∫_{fd,y>Y} y^{1−u}E(R_c w,v) via zero-mean + CT_c(v); (iii) Step 1 in 2D form;
  (iv) assembly of I_Y(u,v) with coset-level truncation L_c.
- 2026-09-25 — built+wired: `SelbergMaassSelbergCuspStep` (Step 1 `sum_cusp_estar_zero`), HTGeometry
  `UpperHalfPlaneCoordIntegrable` (`integrableOn_coord_iff`), `SelbergMaassSelbergBounds` (`coeff_sh`, `Lc`, bounds, four
  integrability lemmas on fd). Next: assembly module (slab via cellP + seed_unfold, cusp CT integrals, final formula).
- 2026-09-25 — MS-N DONE (region): `SelbergMaassSelbergGammaN.maassSelberg_region` (built, wired, axioms clean):
  N ≥ 3, 1 < Re v < Re u, Y ≥ 1: Σ_c ∫_fd Λ^Y_c E_u·Λ^Y_c E_v = N Y^{u+v−1}/(u+v−1) + φ_{∞∞}(v)Y^{u−v}/(u−v)
  − Σ_c b_c(u)(a_c Y^{v−u}/(u−v) + b_c(v)Y^{1−u−v}/(u+v−1)). Next: holomorphy of both sides in (u,v) and continuation
  to the critical line (needs E-continuation bounds on fd, cf. level-one EisensteinTruncatedPairingHolomorphic).
