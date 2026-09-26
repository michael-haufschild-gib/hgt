# Shimura's theorem: holomorphy of twisted symmetric-square L-functions (formal)

- **ID:** shimura-sym2
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — classical (Shimura 1975; Gelbart–Jacquet 1978), formal infrastructure
- **Source:** loop card `selberg-quarter-conjecturing-loop.md`, cycle 71
- **Statement:** for a non-dihedral Hecke–Maass cusp form u of level N and a Dirichlet character ψ,
  L(s, sym²u ⊗ ψ) is entire and satisfies its functional equation with Γ-factor
  Γ_ℝ(s+δ)Γ_ℝ(s+δ±2ν).

## Goal
Shimura's theorem is on the critical path of every known route past Selberg's 3/16: Iwaniec's
GL₂-only 10/49 (forced zeros of square twists with a common Γ-factor) and Gelbart–Jacquet (input to
the GL₃ converse theorem, hence Luo–Rudnick–Sarnak and Kim–Sarnak). No GL(3) automorphy is needed.

## Gates
- [x] 0 → 1  plan fixed (cycle 71)
- [ ] 1 → 2  paper proof assembled per module (below)
- [ ] 2 → 3  Lean: `sym2_twist_entire`, functional equation

## Approach (module plan)
- [x] H1 `HalfWeightTheta`: θ(z) = Σ e(n²z) on Γ₀(4); Γ₀(4) = ⟨T, U, −1⟩ (descent); y^{1/2}|θ|²
  invariant; abstract multiplier J(γ,z) = θ(γz)/θ(z) (θ ≠ 0 on ℍ, corpus `Bottcher`), cocycle,
  |J|² = |cz+d|.
- [ ] H2 cusp evaluation: J(γ,z) = κ(γ)(cz+d)^{1/2}, κ constant (holomorphic, modulus 1);
  Poisson at the cusp −d/c: κ(γ) = c√2 / (G(−d;c)·(ic)^{1/2}), G(a;c) = Σ_{r mod c} e(ar²/c);
  corollary |G(a;c)|² = 2c for 4 | c, (a,c) = 1. No Gauss-sum sign evaluation needed.
- [ ] H3 weight-½ Eisenstein series E(z,w;ψ) = Σ_{Γ_∞\Γ₀(4M)} ψ̄(d) \bar j(γ,z) Im(γz)^w, j = J/|J|:
  convergence Re w > 1, transformation E(γz) = ψ(d) j(γ,z) E(z), holomorphy in w.
- [ ] H4 Fourier expansion: coefficients Σ_c c^{−2w−1/2} Σ_{m mod c} r_c(n − m²)·ψ-weights times
  weight-½ Whittaker integrals (Ramanujan sums appear because κ̄ ∝ G(−d;c)/√c).
- [ ] H5 local densities N_c(n) = #{m mod c : m² ≡ n}: Σ_c N_c(n)c^{−s} = ζ(s)L(s,χ_n)/ζ(2s)·(finite
  corrections); continuation and polynomial bounds |L(σ+it,χ)| ≪ |s| q^{1−σ}/σ (partial summation).
- [ ] H6 continuation of E to an open neighbourhood of {1/2 ≤ Re w ≤ 3/4} minus w = 3/4
  (1/ζ(4w−1) holomorphic there by non-vanishing on Re ≥ 1 and openness).
- [ ] H7 twisted Maass forms u⊗χ on Γ₀(Nr²) with nebentypus χ² (weight 0 conjugation by T_{b/r}).
- [ ] H8 Shimura unfolding: ⟨u_χ(4·) θ̄ y^{1/4}, E(·,w)⟩ = C(w) Σ λ(k²)ψ(k)k^{−(2w−1/2)},
  C(w) from ∫ t^{μ−1}e^{−t}K_ν(t)dt = √π Γ(μ+ν)Γ(μ−ν)/(2^μΓ(μ+1/2)).
- [ ] H9 holomorphy of L(s,sym²u⊗ψ) on a neighbourhood of 1/2 ≤ Re s < 1 (s = 2w − 1/2);
  Re s ≥ 1 from Rankin–Selberg L(s,u×(u⊗ψ)) = L(s,sym²u⊗ψ)L(s,ψ) and L(s,ψ) ≠ 0 there.
- [ ] H10 functional equation of L(s,u×(u⊗ψ)) (weight-0 Eisenstein, nebentypus) ÷ that of
  L(s,ψ) ⇒ functional equation of sym² ⊗ ψ; with H9, entire.
- [ ] H11 Iwaniec–Blomer–Brumley framework F(Y); exponent law; 3/16 via sym² (depth aspect q = p^k
  without Deligne); then the 10/49 gain (mechanism not yet reconstructed; source paywalled).

## Log
- 2026-09-26 — created from loop cycle 71; H1 closed (`RHTower/HalfWeightTheta.lean`, wired, axioms
  propext/choice/Quot.sound).
- 2026-09-26 — H2 closed (`HalfWeightThetaMultiplier`): κ(γ) constant by maximum modulus; Poisson at
  the cusp −d/c (`theta_cusp`); `J_mul_gauss`: J(γ,z)·G(−d;c)·(ic)^{1/2} = c√2(cz+d)^{1/2};
  `norm_sq_gaussQ`: |G(−d;c)|² = 2c for 4 | c, (c,d) = 1. H3 closed (`HalfWeightEisenstein`):
  `eisHalf` on ⟨T⟩\Γ₀(4M) with nebentypus ψ, absolute convergence Re w > 1, `eisHalf_smul`.
  All wired; axioms propext/choice/Quot.sound.
- 2026-09-26 — H4a closed (`HalfWeightKernel`: kerH = e^{-i arg(x+iy)/2}(y/(x²+y²))^s, |kerH| = wt^σ,
  Fourier decay, Poisson for Re s ≥ 3/4). H4b in progress: `star_jU_mul_im_cpow` (c > 0 summand =
  C(c,d) c^{-2w} kerH(y, x + d/c), C unimodular, C(c,d) = G(−d;c)(ic)^{1/2}/(√2 c)).
  **Design decisions for H6/H8 (recorded so they survive compaction):**
  (a) Growth of E at the other cusps is NOT obtained from Eisenstein series at every cusp. Near a
      rational point a, the expansion at ∞ with |𝓕kerH_{y,w}(n)| ≤ min(y^{1−σ}C_σ, D|w|²y^{−1−σ}/n²)
      and |D_n(w)| ≪ n^{1/2+ε}(1+|w|)^A gives |E(ζ,w)| ≪ (Im ζ)^{−A'}: polynomial growth at every
      cusp, enough because F(z) = u(4z)θ̄(z)y^{1/4} decays exponentially at every cusp.
  (b) Continuation across Re w = 1/2 is required (the critical line s = 2w − 1/2, Re s = 1/2, is not
      covered by the functional equation). Non-constant coefficients: integrate 𝓕kerH by parts
      once (converges for Re w > 0). Constant term: ∫kerH(1,w,x)dx = ∫(1+ix)^{−a}(1−ix)^{−b}dx with
      a = w + 1/4, b = w − 1/4, closed form 2^{2−a−b}πΓ(a+b−1)/(Γ(a)Γ(b)) (Beta integral); its
      pole at w = 1/2 cancels the zero of 1/ζ(4w−1).
  (c) Poles at s = 1 are handled by Rankin–Selberg, not by the θ-residue of E at w = 3/4.
- 2026-09-26 — H4 closed (`HalfWeightKernel`, `HalfWeightEisensteinFourier`): `eisHalf_eq_fourier`,
  E(z,w;ψ) = (1+ψ̄(−1))y^w + Σ_{c≠0, 4M|c} |c|^{−2w} Σ_n 𝓕kerH_{y,w}(n) e(nx) klH(n,c), Re w > 1,
  klH(n,c) = Σ_{r mod |c|, (c,r)=1} ψ̄(r) C(|c|, sgn(c) r) e(nr/c), C(c,d) = c√2/(Ḡ(−d;c) conj((ic)^{1/2})).
  Next H5: C(c,d) = G(−d;c)(ic)^{1/2}/(√2 c) (from |G|² = 2c), so klH opens into
  Σ_{m mod c} g_ψ(n − m²; c) with g_ψ(k;c) = Σ_{d∈(ℤ/c)^×} ψ̄(d)e(dk/c); then the Dirichlet series
  D_n(w) = Σ_c |c|^{−2w} klH(n,c) via local densities of m² ≡ n.
- 2026-09-26 — H5 part 1 closed (`HalfWeightEisensteinCoefficients`): `eisHalf_eq_coeffs`
  E = (1+ψ̄(−1))(y^w + Σ_n 𝓕kerH(n)e(nx)D_n(w)); `Dser_one` D_n(w) = i^{1/2}/√2 Σ_{4M|c} c^{1/2−2w}(μ*N(n))(c)
  for trivial ψ; |C(c,d)| = 1, |klH| ≤ c. Next H5 part 2: N_f(n) multiplicative (CRT), local values
  N_{p^a}(n) = 1 + (n/p) for p ∤ 2n (cyclic unit group / Hensel), finite local sums at p | 2Mn,
  Euler product ⇒ Σ_{4M|c}(μ*N)(c)c^{−s} = P_n(s) L(s,χ_n)/ζ(2s).
- 2026-09-26 — H5 part 2a/2b closed: `HalfWeightSquareRoots` (N_{ab} = N_aN_b; N_{p^a}(n) = 1+(n/p) for odd
  p ∤ n via cyclic units, no Hensel; N_{p^a}(n) ≤ 8|n| via ± classes), `HalfWeightKronecker` (kronChar
  (n/·) mod 4|n|M; `fN_eq_mul`: μ*N(n) = (μ²χ) ⍟ e_T). Next: constraint 4M|c passes to e_T (χ(a) ≠ 0 ⇒
  (a,4M) = 1); LSeries factorisation Z_n(s) = L(s,χ)/L(2s,χ²)·LSeries(e_T·[4M|·])(s); e_T part summable
  Re s > 0 (factoredNumbers Euler product, bound (1+16|n|/(2^σ−1))^{|T|}); then n = 0 (ζ(2s−1)/ζ(2s)).
  Design note: sub-exponential growth of D_n suffices once 𝓕kerH decays exponentially (contour shift
  of kerH = y^w (x+iy)^{−w−1/4}(x−iy)^{−w+1/4}, holomorphic on |Im x| < y).
- 2026-09-26 — `HalfWeightCoefficientL` closed: `LSeries_gL` Σ_{4M|c}(μ*N(n))(c)c^{−s} = L(s,χ)/L(2s,χ²)·LSeries(e_L)(s)
  (Re s > 1), `Dser_one_eq_LSeries` D_n(w) = i^{1/2}/√2·LSeries g_L(2w−1/2), e_L summable Re s > 0.
  Remaining for H6: (i) n = 0 constant term (ζ-type); (ii) continuation object D̃_n(w) :=
  i^{1/2}/√2·L(2w−½,χ)·L(4w−1,χ²)^{−1}·LSeries(e_L)(2w−½), holomorphic on a neighbourhood of
  {Re w ≥ 1/2} minus {3/4 if χ = 1} (1/L(·,1_q) near 1 via residue), sub-exponential bounds in n;
  (iii) 𝓕kerH continuation across Re w = 1/2 (integration by parts) + exponential decay (contour shift);
  (iv) assemble Ẽ and identity theorem.
- 2026-09-26 — `HalfWeightKernelContinuation` closed: kerH = y^w h_{w+1/4,w−1/4}; Fourier recursion
  2πiξ𝓕h_{a,b} = −a𝓕h_{a+1,b} − b𝓕h_{a,b+1}; G_k/PhiK holomorphic on Re w > (1−k)/2, independent of k,
  |PhiK| ≤ ((|w+¼|+|w−¼|+2k)/(2π|ξ|))^k e^{2π|Im w|} y^{1−Re w−k} C_{Re w+k/2}. (Design (b), n ≠ 0 done
  without contour shifts.) Next: constant term via J(a,b) = 4ab/((a+b)(a+b−1)) J(a+1,b+1); D̃_n bounds.
- 2026-09-26 — `HalfWeightConstantKernel` closed: aB + bC = 0, C − B = 2iyD, (1−a−b)A = −iayB + ibyC
  ⇒ (a+b)(a+b−1)∫h_{a,b} = 4aby²∫h_{a+1,b+1} (`integral_hab_rec`); J_k recursion, J_k^{(y)} = y^{1−a−b}J_k^{(1)};
  `integral_kerH_eq`: P_k(2w)∫kerH_{y,w} = y^{1−w}c_k(w), c_k holomorphic on Re w > 1/2 − k.
- 2026-09-26 — `HalfWeightConstantCoefficient` closed: μ*N(0) = φ(√·) on squares; m₀(N) = least m with
  N | m² (ideal argument); φ(m₀k) = φ(m₀)h(k), h ⍟ χ₀ = id; `Dser_zero_mul`:
  D_0(w)·ζ(4w−1)∏_{p|2M}(1−p^{1−4w}) = (i^{1/2}/√2)φ(m₀)m₀^{1−4w}ζ(4w−2) (Re w > 3/4).
  Constant term of E: 2(y^w + D_0(w)y^{1−w}c_1(w)/(2w(2w−1))); the 1/(2w−1) pole cancels the zero of
  1/ζ(4w−1). Next: D̃_n for n ≠ 0 with χ_n² principal (L(4w−1,χ²) = ζ(4w−1)∏_{p|4nM}(1−p^{1−4w})),
  polynomial-in-n bounds, then assembly of Ẽ(z,w) on a neighbourhood of Re w ≥ 1/2.
- 2026-09-26 — H6/H7 closed: `HalfWeightCoefficientContinuation` (χ² = 1; invLOne; D̃_n; φ(w)),
  `HalfWeightCoefficientBounds` (N_{p^a}(n) ≤ 2p^{v_p(4n)} ⇒ ‖L(e_L,s)‖ ≤ 4|n|(4|n|M)^{β(σ)};
  ‖∏(1−p^{−u})‖⁻¹ ≤ N^{γ(σ)}), `HalfWeightRegularisedCoefficients` (strip bound for every non-principal χ via
  primitive reduction + corpus CGL strip bound; D*_n = (4w−3)(4w−2)ζ(4w−1)D_n entire on Re w > 1/4 and
  ≤ C|n|^{e(w)}), `HalfWeightEisensteinContinuation`: E*(z,w) = ρ(w)E(z,w) holomorphic on 1/4 < Re w < 5/4
  and automorphic (`Estar_smul`), ρ(w) = (4w−3)(4w−2)ζ(4w−1). Axioms clean.
  Next: moderate growth of E* (polynomial in y and 1/y from the same bounds), level-N Maass forms and
  u(4z), Rankin–Selberg unfolding against u(4z)θ̄(z)y^{1/4}.
- 2026-09-26 — H8/H9 closed: `HalfWeightUnfolding` (posRows reps of ⟨T⟩\Γ₀(4M), repT(p,c) = rowMat p · out c reps of
  ⟨T⟩\PSL₂(ℤ), `unfold_eisHalf`: ∫_𝒟 Σ_c G(c·z)E(c·z,w) = 2∫_strip G y^w for G(γz) = conj(j(γ,z))G(z)),
  `HalfWeightEisensteinRegularity` (Φ scaling y^{1−w}Φ^{(1)}(yξ); `Estar_growth` ‖E*‖ ≤ C(y^A+y^{−A});
  `continuous_Estar`), `HalfWeightRankinSelberg` (`differentiableAt_rsFold` on 1/4 < Re w < 5/4 for G with
  rapid decay of all translates on 𝒟; `rsFold_eq` = 2ρ(w)∫_strip G y^w for Re w > 1).
  Consequence (paper): for G = u(4z)θ̄(z)y^{1/4}, M(w) = ∫_strip G y^w = B̃(w)Z(w), B̃(w) = ∫_0^∞ W(t)e^{−t}t^{w−7/4}dt
  (W the decaying modal solution, unique up to scalar), Z(w) = Σ_k c_k(8πk²)^{3/4−w}. For exceptional
  λ = 1/4 − τ², B̃ has a simple pole at w₀ = 1/4 + τ (leading coefficient of W at 0 nonzero, else W ≡ 0 by
  the corpus energy argument) and ρ(w₀) = (4τ−2)(4τ−1)ζ(4τ) ≠ 0, so the continued Z vanishes at w₀: the
  forced zero. Level caveat: Γ(N) forms need u(4Nz) on Γ₁(4N²), i.e. nebentypus ψ (D_n for general ψ not done).
  Next: modal ODE uniqueness + Mellin of W·e^{−t} (pole at w₀), G's decay on 𝒟 from corpus `maass_decay`,
  forced-zero theorem for Γ₀(M) with trivial character.
- 2026-09-26 — Half-plane extension: bounds extended to Re s > 2 (`norm_LFunction_le_two`), so E*, rsFold are
  holomorphic on all of Re w > 1/4. `HalfWeightWhittaker`: Bessel ODE for the Schläfli K, W = √t K solves the
  modal equation, and ∫_0^∞ K_ν(t)e^{−t}t^{μ−1}dt = 2^{μ−1}Γ(μ)Γ(μ+ν)Γ(μ−ν)/Γ(2μ) (|Re ν| < Re μ).
  **Forced-zero plan (Maass side), modules K2–K6:**
  K2 modal identification for u ∈ MaassCuspEigenform(realImage Γ₀(M)) λ, 0<λ<1/4 (restrict to Γ(M), width-M
     coefficients a_n; a_n = 0 unless M | n; a_{Mk}(y) = c_k Wh_τ(2π|k|y) via Frobenius α + energy rigidity);
  K3 U(z) = u(4z) is a Γ(4M) Maass cusp form (Hermite form of [[4,0],[0,1]]σ), translates decay exponentially
     (corpus maass_decay); |θ(w)| ≤ C(1 + Im w^{−1/2}); ⇒ hdec for G = u(4z)θ̄y^{1/4};
  K4 zeroth coefficient g₀(y) = y^{1/4}Σ_j a_{Mj²}(4y)e^{−8πj²y}; ∫_strip G y^w = ∫_0^∞ g₀ y^{w−2} (Fubini);
  K5 M(w) = 2Mel(w−¼)(8π)^{3/4−w}Z(w), Z(w) = Σ_{j≥1} c_j j^{3/2−2w} (Re w > 5/4);
  K6 Ẑ := rsFold·(8π)^{w−3/4}/(4ρ·Mel(w−¼)), 1/Mel(μ) = Γ(2μ)/(2^{μ−1}Γ(μ)Γ(μ+τ)Γ(μ−τ)) holomorphic on
     Re μ > 0, Ẑ(¼+τ) = 0 (1/Γ(0) = 0), ρ(¼+τ) = (4τ−2)(4τ−1)ζ(4τ) ≠ 0.
- 2026-09-26 — K2–K6 closed. `HalfWeightModalWhittaker` (bounded decaying modal solutions = c·W_τ(ky), W_τ = √t K_τ),
  `HalfWeightShimuraCoefficient` (∫_0^1 f(4z)θ̄ dx = Σ_j coefficient_{4j²}), `HalfWeightExceptionalMaass` (ρ_k bounded,
  zeroth coefficient Σ_j e^{−8πj²y}ρ_{j²}W_τ(8πj²y)), `HalfWeightShimuraKernel` (G(γz) = conj(j)G(z) on Γ₀(4(N+1)),
  rapid decay of all translates on 𝒟 via Hermite form of diag(4,1)g), `HalfWeightForcedZero`:
  `strip_integral_Gsh` ∫_strip G y^w = Z(w)·Mel_τ(w−¼) (Re w > 7/4), `summable_zCoef` (Re w > 5/4),
  **`shimura_forced_zero`**: Ẑ = rsFold·Mel⁻¹/(2ρ) holomorphic on Re w > ¼ off zeros of ρ, = Z on Re w > 7/4,
  Ẑ(¼+τ) = 0. Axioms: propext, Classical.choice, Quot.sound. Lint clean.
  Status: this is Shimura (1975) + the Luo–Rudnick–Sarnak trivial-zero mechanism for sym², level Γ₀(N+1),
  trivial nebentypus. Known mathematics; no new scientific content. Consumers: LRS twisted-nonvanishing (21/100)
  needs the χ-twisted version (θ_χ, E(z,w;ψ) with ψ = χ²-type character) and a GL(3) large sieve / zero density.
- 2026-09-26 — Twisted family closed (7 modules, wired after HalfWeightForcedZero):
  `HalfWeightTwistedTheta` (Gauss-sum invariance G(m+(c/q)k;c)=G(m;c); θ(γz+a/q)=J(γ,z)θ(z+ad²/q) on Γ₀(4q²);
  θ_χ=Σ_a χ̄(a)θ(z+a/q), θ_χ(γz)=χ(d)²Jθ_χ), `HalfWeightTwistedCoefficients` (g_ψ via Gauss expansion,
  klH_ψ = (ic)^{1/2}/√2 τ⁻¹ Σ_b ψ₀(b)(μ*N)(n+bc/q)(c), q-part factorisation T(n,q^αc') = (μ*N(n))(c')ψ̄₀(c')A_α(n),
  D_n = i^{1/2}/(√2τ) L(Q*ψ̄₀g_L, 2w−½)), `HalfWeightTwistedL` (product character χ'=ψ̄₀χ_n, generic
  μ²χ/square split, D*_n = L(4w−1,ψ̄₀²)D_n holomorphic on Re w>¼, A_α(0)=0 so D_0=0, uniform |n|-bound),
  `HalfWeightTwistedEisenstein` (E*_ψ continuation, ψ-automorphy, growth, continuity),
  `HalfWeightTwistedRankinSelberg` (unfolding with even character, rsFoldTw holomorphic, = 2L(4w−1,ψ̄₀²)∫_strip),
  `HalfWeightTwistedKernel` (G_χ = f(4z)θ̄_χ y^{1/4}: law with χ², decay, zeroth coefficient Σ_j conj g_χ(4j²)…,
  strip integral), `HalfWeightTwistedForcedZero`: **`shimura_forced_zero_tw`** — for χ of odd prime conductor
  q∤N+1, χ⁴≠1: Y_χ = L(4w−1,χ̄⁴)Σ_j conj(g_χ(4j²))ρ_{j²}(8πj²)^{3/4−w} holomorphic on Re w>¼, Y_χ(¼+τ)=0;
  `conj_gTw_sq`: weights = conj(χ(4)τ(χ̄))·χ̄(j)². Axioms standard. This is L(2τ, sym²u⊗χ̄²)=0 for the whole
  square-twist family (known: Shimura/LRS/Iwaniec input). Remaining for any family argument past 3/16: the
  functional equation (scattering of E_ψ at all cusps of Γ₀(4(N+1)q²)) and a moduli-averaged dual bound.
