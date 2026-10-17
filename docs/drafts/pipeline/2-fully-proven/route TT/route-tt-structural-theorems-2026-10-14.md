# Structural theorems from the route-TT conjecture loop (rows 238–325)

- **ID:** route-tt-structural-theorems-2026-10-14
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), a collection of six short results
- **Source:** route-tt-loop-2026-10-13 rows 246, 281, 297, 298, 311, 314
- **Statement:** Six unconditional structural theorems (T1–T6). Each bounds or reformulates a route toward RH. None proves RH.

## Goal
These record the dependency-closed positive survivors of failed conjectures (no-go closure discipline), so later cycles do not re-derive them.

## Theorems and proofs

**T1 (cone-existence ladder).** Let μ₊ be any exponent with |ζ(σ+it)| ≪ (1+|t|)^{μ₊} uniformly on σ ≥ ½, e.g. μ₊ = ¼+ε (convexity) or 13/84+ε (Bourgain).
- *Claim.* For every θ > μ₊ there is C > 0 such that λ ≡ 1 on n ≥ 2 lies in the Weil cone whose archimedean density is Ω_ζ + C(1+|t|)^θ, with the same pole and comb.
- *Proof.* With D(s) = ζ(s) − 1, put Φ = P + E_θ − D, where P = 1/s + 1/(s−1) + Γ̃(s) and E_θ is the analytic function on Re s > ½ whose real part is the Poisson extension of C(1+|t|)^θ.
  - Φ is holomorphic on Re s > ½: the poles at s = 1 cancel.
  - Re Φ ≥ 0 on the boundary line and as σ → ∞, because Re D ≤ |ζ| + 1 ≪ (1+|t|)^{μ₊} ≤ C(1+|t|)^θ for large |t|; enlarge C to cover bounded |t|.
  - Phragmén–Lindelöf for the harmonic function Re Φ, which has finite order, gives Re Φ ≥ 0 inside.
  - Herglotz positivity is equivalent to Weil positivity (corpus bridge `weilPositiveFull_iff_exists_herglotz`, with the modified archimedean term). ∎
- *Consequence.* PBAP is the bottom rung E = 0. Known rungs are subconvexity exponents.

**T2 (gap-weighted prime carrier).** Let θ₂ be any exponent with Σ_{p_n ≤ X}(p_{n+1} − p_n)² ≪ X^{1+θ₂}; θ₂ = 5/18 + ε is admissible (Heath-Brown).
- *Claim.* D_gap(s) = Σ_k (p_{k+1} − p_k) p_k^{−s} is holomorphic on Re s > θ₂ except for a simple pole at s = 1 with residue 1.
- *Proof.* Σ_{p ≤ x} gap = x + E(x), where E is a sawtooth with 0 ≤ E(x) ≤ gap(x) + O(1). Then D_gap(s) = s/(s−1) + s∫E(x)x^{−s−1}dx + (constant terms).
  - Since ∫_X^{2X}E ≤ Σ_{X<p≤2X}gap² ≪ X^{1+θ₂}, the integral converges absolutely for Re s > θ₂. ∎
- *Note.* This corrects route-tt row 247, which used the maximal-gap exponent. On the line, |D_gap(½+it)| ≍ |t|, so the archimedean excess is linear.

**T3 (invariant forms on the zero algebra).** Let A = O/(Ξ) be decay-class entire functions modulo Ξ-multiples. ℚ^×_{>0} acts by M_q F = q^{iz}F, and the ρ-component transforms by the character χ_ρ(q) = q^{iγ_ρ}.
- *Claim.* Every M-invariant Hermitian form on A is Σ_{γ_ρ ∈ ℝ} w_ρ |F(γ_ρ)|² + Σ_{off-line pairs} 2Re(w_ρ F(γ_ρ) conj F(γ̄_ρ)) (finite sums on finitely supported data). Hence a positive-definite invariant form exists iff every γ_ρ is real, i.e. RH.
- *Proof.*
  - Invariance gives H(F_ρ, F_{ρ′})(χ_ρ(q) conj χ_{ρ′}(q) − 1) = 0 for all q.
  - Since χ_ρ conj χ_{ρ′} ≡ 1 iff γ_{ρ′} = γ̄_ρ, only such pairs couple.
  - A coupled pair with γ_ρ ∉ ℝ spans a hyperbolic plane. ∎

**T4 (depth blindness).** Let f be entire, real on ℝ, with |f(x+iy)| ≪_K (1+|x|)^{−2} for |y| ≤ K.
- *Claim.* For any zero ρ = β+iγ (|β−½| < ½) and L > 0, ∫_{−∞}^{∞} f((γ − τ + i(β−½))L) dτ = L^{−1}∫_ℝ f(x)dx, independent of β.
- *Proof.* Substitute and shift the horizontal contour by Cauchy's theorem. ∎
- *Consequence.* Translation-averaged one-level densities of zeros cannot detect off-line zeros.

**T5 (Ruelle realization implies quasi-RH).**
- *Claim.* Suppose ζ(s) = Π_γ(1 − e^{−sℓ_γ})^{−1}, the Ruelle zeta of a suspension flow over a mixing subshift of finite type with Hölder roof. Then ζ(s) ≠ 0 for Re s > 1 − ε, for some ε > 0.
- *Proof.* Write ζ_R(s) = exp Σ_n n^{−1} Σ_{x∈Fix σ^n} e^{−sS_n r(x)}.
  - By Ruelle–Pollicott, the transfer operator L_s on C^α is quasi-compact with essential radius ≤ θ^α e^{P(−Re s·r)}.
  - Flat traces satisfy Σ_{Fix σ^n} e^{−sS_n r} = Σ_{|λ_i(s)|>ρ′} λ_i(s)^n + O(ρ′^n) for some ρ′ < 1, where the λ_i are the finitely many eigenvalues outside radius ρ′.
  - Hence ζ_R = Π_i(1 − λ_i(s))^{−1}·exp(holomorphic) on the region θ^α e^{P(−σr)} < ρ′ < 1. This region contains σ > h − ε, with h = 1 the topological entropy (pressure zero).
  - The product of reciprocals and the exponential never vanish. ∎
- *Obstruction.* A bijection between periodic orbits and primes forces π(x) to equal the flow's orbit count, which is Li(x) + O(x^{1−ε′}) (Pollicott–Sharp). So the realization is itself quasi-RH-hard.

**T6 (no real-analytic Ruelle realization of geodesic type).**
- *Claim.* Let T be an orientation-preserving real-analytic expanding Markov map with nuclear transfer operators L_s f = Σ_{Ty=x}|T′(y)|^{−s} f(y), and entropy h = 1. Its Ruelle zeta ζ_R(s) = exp Σ_n n^{−1} Σ_{Fix T^n}|(T^n)′|^{−s} is zero-free on Re s > 0. Hence ζ is not such a Ruelle zeta, since ζ(½ + 14.1347…i) = 0.
- *Proof.*
  - Expanding the nuclear traces Tr L_s^n = Σ_{Fix T^n}|(T^n)′|^{−s}(1 − (T^n)′^{−1})^{−1} = Σ_{k≥0} Z_n(s+k) gives det(1 − L_s)^{−1} = Π_{k≥0} ζ_R(s+k).
  - Hence ζ_R(s) = det(1 − L_{s+1})/det(1 − L_s).
  - For Re s > 0, the spectral radius of L_{s+1} is ≤ e^{P(Re s + 1)} < 1, since P(σ) < 0 for σ > h = 1. So det(1 − L_{s+1}) ≠ 0. ∎

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proofs above; T1 uses Phragmén–Lindelöf and the corpus Herglotz bridge, T2 uses Heath-Brown's gap moment, T5 uses Ruelle–Pollicott, T6 uses Ruelle–Mayer nuclearity)
- [ ] 2 → 3  formalized: T4 is exactly the corpus lemma `RHTower.integral_horizontal_shift_of_upper_inv_one_add_sq_decay` (StripHorizontalShift) applied to τ ↦ f((γ−τ+i(β−½))L), so no new module is needed. T3 is elementary character linear algebra. T1 is formalized at the convexity rung in Herglotz form, without the θ-line bridge: MUST-1448 [L] `RHTower.RelaxedHerglotz.exists_herglotz_trivialWeights_boosted` (boost c(s+½)^θ, ¼ < θ < 1). T2, T5 and T6 need imported analytic and dynamical infrastructure not in the corpus.

## Log
- 2026-10-14 — created from route-tt-loop rows 246, 281, 297, 298, 311, 314.

## Addendum: θ-shifted Weil cones (route-tt rows 345–348)

**T7 (monotone-limit form of RH).** For θ∈(½,1), let cone_θ be the set of real weights λ on n≥2 such that:
- D_λ(s)=Σλ(n)n^{-s} continues holomorphically to Re s≥θ, except for a simple pole at s=1 with residue 1;
- Re(P−D_λ)≥0 on Re s>θ, where P=Γ_∞′/Γ_∞ and Γ_∞=s(s−1)π^{-s/2}Γ(s/2).

*Claim.* RH ⟺ cone_θ≠∅ for every θ>½.

*Status:* paper sketch. It depends on the θ-line analogue of the corpus Herglotz bridge `weilPositiveFull_iff_exists_herglotz`: positivity on tests ⟺ Herglotz continuation to Re s>θ. That analogue is not yet written out.

*Proof.*
- (⟹) Under RH, Λ∈cone_θ for every θ, since Re ξ′/ξ>0 on Re s>½.
- (⟸) The cones are nested: cone_θ⊆cone_{θ′} for θ<θ′.
- Each cone_θ is closed in the product topology. Membership is equivalent to W^θ_λ(g)≥0 for every PD compactly supported test g, and each such inequality depends on finitely many coordinates.
- The coordinates are bounded uniformly in θ (θ-line pair tests). Tychonoff then gives ∩_{θ>½}cone_θ≠∅.
- This intersection is the set of λ with P−D_λ Herglotz on Re s>½, which is the full Weil cone. That cone is ⊆{Λ} unconditionally (corpus `eq_vonMangoldt_of_weilPositiveFull`, via the twisted arc minimum principle).
- Hence Λ is in the full Weil cone, i.e. RH. ∎

**Remarks.**
- quasi-RH(θ) ⟹ cone_θ≠∅. The converse is NOT implied for θ>½: the Ξ-divisible zero face exists only at θ=½, so for θ>½ the cones are fat and certificates decouple from the location of the zeros (rows 346–347).
- Hence the TT core (a zero-free half-plane) has no ζ-free "prime-blind" form by this mechanism. RH does have a ζ-free limit form (T7).
- Building certificates of cone_θ needs a support without multiplicative closure, to avoid smooth-number alignment, together with prime exponential sums at length ≍t with saving t^{-(1-θ)}. Prime exponential sums have only zero-free-region-quality (sub-power) savings, because Type II sums with multiplicative characters factor. So no unconditional certificate is known for any θ<1 (rows 348–349; row 348's VK claim is corrected there).

## Addendum: structural laws for the PBAP lane (route-tt rows 336–357; heuristic, not theorems)
- **Polarity law.** Maximum-principle arguments such as the corpus's twisted arc minimum principle refute positive COMBINATIONS of explicit functions on a compact set; this is how existence results like the Ξ-divisible zero face are reached.
  - PBAP needs a positive combination to EXIST: θ′+pole−Σλ_n n^{−½}2cos(t log n)≥0, i.e. the zero measure is positive.
  - Equivalently, PBAP must refute bad positive MEASURES (blind w≥0 with A(w)<0). This is the opposite polarity.
  - Its LP dual is the thin cone {Λ}, so no soft method (minimax, Kakutani, direct method, Riesz–Haviland) avoids the arithmetic input.
- **Localisation.** Under ¬RH the PBAP violators are theta-like: analytic in the strip, doubly-exponentially decaying, near the zero face, with O(1) normalised energy.
  - Large-support "amplifying" blind tests have positive ζ-free energy, because on-line zeros compensate in the exact explicit formula.
  - Cost-law and routing arguments therefore do not touch RH.
- **Parity.** For even f the pole term is F(i/2)²≥0; for odd f it is −F(i/2)²≤0. Symmetric blindness couples the parts: (f_e⋆f_e)(log n)=(f_o⋆f_o)(log n).
  - The negative pole lives only on odd blind tests. There PBAP is an archimedean-capacity bound for the pole vector sinh(x/2).
- **Arithmetic core.** Every reading reduces to the same input: power-saving self-resonance control of prime sums at zero ordinates. The readings are PBAP_θ certificates, the JAS shell radius law and the near-face programme.
  - Type II sums with multiplicative characters factor, which blocks independent savings.
- **Dictionaries.**
  - The anomaly a₀=½(ψ(¼)−log π) is Beckner's sharp log-uncertainty constant.
  - The Weil local terms are Kantorovich potentials of a multi-marginal transport on the Kronecker line, and the zeros form its contact set.
  - The twisted arc minimum principle is axisymmetric 3D electrostatics: rings on the unit sphere, with integer axial modes.

## Addendum: structural laws, route-tt rows 358–377 (paper level; (L1)–(L3) are exact computations, the rest are named obstructions)

**(L1) Hecke–Maass–Selberg resonance identity.**
- Setting: let ξ(2s)=0, s=σ+iτ, so E*(·,s) has the one-term constant term c·y^{1−s} with c=ξ(2s−1). Let g=Λ^aE* be the truncation at height a, with a ≥ p·Y₀ and a/p>1.
- On functions of y, T_p acts by φ ↦ p^{−½}(φ(py)+pφ(y/p)).
- Claim: ⟨T_pg,g⟩ = |c|²a^{1−2σ}(1−2σ)^{−1}·(p^{s−½}+p^{s̄−½}). This is REAL for every s, so self-adjointness of T_p imposes no condition.
- Proof:
  - The truncation defect of T_p is supported in a/p<y≤pa. Only a/p<y≤a meets the constant term of g, contributing c̄p^{½−s}a^{1−2σ}(1−p^{2σ−1})/(1−2σ).
  - Maass–Selberg with ξ(2s)=0 gives ‖g‖²=|c|²a^{1−2σ}/(1−2σ) exactly.
  - Combining, p^{s−½}+p^{½−s}−p^{½−s}(1−p^{2σ−1}) = p^{s−½}+p^{s̄−½}. ∎

**(L2) Free-family law** (consequence and refinement).
- E*(z,s)=ξ(2s)y^s+ξ(2s−1)y^{1−s}+F_s(z), where F_s is entire in s and ζ-free (σ_{1−2s}(n), K-Bessel).
- Every Laplace, Hecke, Green, Maass–Selberg or Lax–Phillips identity holds uniformly in s. Specialised to ξ(2s)=0 it is consistent for every s, so no such identity locates the zeros.
- Point values at CM points see ζ(s) only through Hecke's factorisation 2ζ(2s)E(i,s)=4ζ(s)L(s,χ₋₄): the zeros appear as zeros of a VALUE, not as spectrum.
- In the 2s-variable the zeros are automatically one-sided relative to Re s=½. This is why Lagarias–Suzuki HB proofs and the Lax–Phillips inner property hold and are RH-blind.

**(L3) Archimedean decomposition and anomaly window.**
- For real f with h=f⋆f̃: A(h)=2(E²−O²)+C₀h(0)+∫_0^∞(h(0)−h(x))·e^{x/2}/sinh x dx.
  - Here E,O = f̂_{even/odd}(i/2) and C₀=ψ(¼)−log π.
  - The kernel e^{x/2}/sinh x = 2Σ_{k≥0}e^{−(2k+½)x} is completely monotone, and the integral is ≥0 for PD h.
- 2πΩ(t)=Re ψ(¼+it/2)−log π<0 exactly on |t|<t₀ with t₀ slightly above 2π (Re ψ(¼+iπ)<log π by about 1.6·10^{−3}).
- Selberg comparison: for compact Γ\ℍ the archimedean density is the Plancherel density r·tanh(πr) ≥ 0, so the analogue of PBAP is trivial there.

**(L4) Exponential sharpness.**
- Under ¬RH, violators built from the zero face carry their spectral mass in the anomaly window.
- Their energy relative to G(0) is of size e^{−(π/2−2a)γ₀}, for an off-line ordinate γ₀ and an R-factor of exponential type a<π/4.
- So no robust (non-exact) splitting inequality can prove PBAP.

**(L5) Polarity bridge and its two breaks.**
- Weil derives Hodge index (non-existence) from Riemann–Roch (existence), which is the polarity of maximum principles.
- Break (i): degree is not numerical, since Ξ(±i/2)=ξ(0)=ξ(1)=½≠0. Principal classes must be (t²+¼)Ξ-divisible.
- Break (ii): linear effectivity is impossible. For a real zero γ₁ and |ε|<2, the measure 2cosh(x/2)+ε·cos(γ₁x) is positive, annihilates every repaired principal class, and pairs with any primitive h having ĥ(γ₁)≠0 with either sign.
- So Riemann–Roch needs a multiplicative ring of sections with growth quadratic in the Weil form.

**(L6) Local pencil obstruction.**
- If Ξ ∝ det(B+tH) with B Hermitian and H>0, RH follows; all the content is in the time metric H.
- H cannot have positive local pieces reproducing the Euler factors: a pencil resolvent trace Tr((B+tH)^{−1}A_p) has only real poles, while −p^{−s}/(1−p^{−s}) has poles at t=2πk/log p+i/2.

**(L7) Anti-deformation.**
- By Davenport–Heilbronn, the Epstein zeta of every positive binary form with class number >1 has infinitely many zeros in Re s>1.
- Along τ=i√N (N ∉ {1,2,3,4,7}) such fibres accumulate at the cusp. So RH is not an open condition in automorphic families.
- Continuity, deformation and first-crossing arguments must run inside Euler-product families, all of whose members are as hard as ζ.

**(L8) Weight mismatch.**
- Arithmetic intersection numbers are log p times integers. The Weil form needs log p·p^{−k/2}, a half Tate twist equal to the local ε-factor (Plancherel) normalisation; |g(χ)|²=p is local Fourier unitarity.
- Arithmetic Hodge index (Faltings–Hriljac via Gillet–Soulé) is available at the integral normalisation.
- The half-twisted normalisation is "global positivity of a form all of whose local normalisations are local unitarities", i.e. Connes's absorption picture.

**(L9) Two classical barriers are one.**
- Linearising n^{it} on blocks of length H ≤ N/√t turns multiplicative Type-II factoring into additive major-arc sums.
- Their main terms reassemble the singular-series approximation of Λ(n)n^{it}. Savings require equidistribution of Λ in progressions to moduli (t/N)^{O(1)}, i.e. GRH-type input at the same height.

## Cross-reference (rh-goal-loop-opus rows 1180–1187, 2026-10-14)
- **T7 is formalized** in Herglotz form, with no θ-line Weil bridge needed: MUST-1442 [L].
  - `RHTower.RelaxedHerglotz.riemannHypothesis_iff_forall_herglotzProducerOn`: RH ⟺ for every δ > 0 some weight with |λ(n)| ≤ log n has a Herglotz continuation of its Weil function to Re s > ½+δ.
  - `exists_herglotzProducerOn_of_forall_gt`: closedness via Tychonoff, Harnack and Vitali.
  - `producerAbscissa_mem_producerLevels`, `riemannHypothesis_iff_producerAbscissa_eq_half`: the abscissa σ* ∈ [½,1] is attained, and RH ⟺ σ* = ½.
  - `not_isHerglotzProducerOn_of_lt_half`: Carlson floor applied to ζ's datum.
  - `herglotzProducerOn_one_vonMangoldt`: Λ is a producer on Re s > 1.
  - The uniqueness step is MUST-1436 `herglotzProducer_eq_vonMangoldt`. Modules: `RHTower/RelaxedHerglotzProducerCompactness`, `RHTower/RelaxedHerglotzProducerFloor`.
- **T2 (gap carrier)** was also found independently in loop row 1181.
- **Pole / degree (L3, L5).** Pole weight β < 1 empties the Weil cone, for weights with linear deviation partial sums. This is MUST-1445 [L] `RHTower.WeilPoleWeight.not_forall_re_weilPoleWeightFunctional_nonneg`. The twisted-arc null test has pole term w₀·2ξ(0)ξ(1) = w₀/2 > 0, so Arch(T) < 0 on a blind test. This is a formal instance of break (i): ξ(0) = ξ(1) = ½ ≠ 0.
- **Pole-free contrast.** CANNOT-539 [L]: for Dirichlet data without a pole and q ≥ 4π (odd) or q ≥ 128π (even), the archimedean symbol is ≥ 0 and λ = 0 is Weil-positive (`RHTower/DirichletArchimedeanSymbolPositivity`).
- **(L4) answers loop row 1190.** "PBAP up to a constant" (∃C: A ≥ −C·h(0) on blind tests) is strictly weaker than RH: violators under ¬RH are exponentially small relative to h(0).

**(L10) Twin RH-rigidity** (route-tt row 390; Lean core `RHTower.WeilConeDegreeTwinRigidity`, axioms: propext, Classical.choice, Quot.sound).
- [L] `weilPositiveDegree_iff`: for d>0, the degree-d Weil functional d·(pole+arch)−Σ_{n≥2}lam(n)n^{−½}(k(log n)+k(−log n)) is nonnegative on every autocorrelation of a compactly supported C² test ⟺ RH ∧ lam=dΛ on n≥2. Proof: W_d(lam)=d·W_1(lam/d), plus the unconditional thin cone.
- [paper] Twin rigidity:
  - Setting: let T=Σa_nn^{−s} have real coefficients and a₁=1, with T*=Γ_ℝ(s)^dT of finite order, poles only at s=0,1 (each of order d), and T*(1−s)=T*(s).
  - Claim: if every zero of T* lies on Re s=½, then RH holds and T=ζ^d.
  - Proof: Weil's explicit formula for T has archimedean part d·arch and polar part d·(ĝ(i/2)+ĝ(−i/2)). With all zeros critical, W_d(λ_T) ≥ 0 for λ_T the coefficients of −T′/T. So λ_T=dΛ, and a₁=1 gives T=ζ^d. ∎
- Unconditional corollary: by the corpus abundance theorem (degree 3), every real twin ζ³+e with e≠0 entire and FE-invariant has a nontrivial zero off the critical line.
- (L10, pole orders; row 393) [L] `weilDegreePoleFunctional_eq_mul` and `not_forall_re_weilDegreePoleFunctional_nonneg`. Paper classification for T with completed Γ_ℝ(s)^dT, conductor 1, FE, real coefficients, a₁=1, pole of order κ at 1:
  - κ<d: never all zeros critical (via the PNT linear bound and the corpus β<1 emptiness).
  - κ=d: all zeros critical only if T=ζ^d and RH holds.
  - κ>d: open.
  - (κ>d status, row 396) The corpus `WeilPoleWeightAboveOneVonMangoldt` excludes only lam=Λ at β>1, because its odd null test Ξ·(iz/2) is not blind. Full emptiness of cone_β for β>1, which would close the classification, needs an ODD BLIND Ξ-divisible family (an odd twisted arc minimum principle).

## Addendum L11 — uniqueness of the twisted-arc dual measure (route-tt row 414)

### Dictionary
- Put Δ₃ = ∂_x² + ∂_y² + y⁻¹∂_y, with y the distance to the x-axis in ℝ³.
- The s=½ eigenfunctions of the hyperbolic Laplacian are √y·Φ with Δ₃Φ = 0.
- The bottom arc {|z| = 1, |x| ≤ ½} is a zone of the unit sphere.
- E = x∂_x + y∂_y is the radial Euler operator. On harmonic Φ, E(E+1) = −Δ_{S²}.
- So the frequency operator D_k = −∂_k k²∂_k acts on the arc Bessel modes cos(ku)K₀(k√(1−u²)) as −L_u, where L_u = −∂_u(1−u²)∂_u.
  - This is formalized in `RHTower.ArcBesselModeLegendreIntertwining`.
- The twisted moments are therefore M_κ(u) = 4√y_u·L_u²(φ_κ)(u), where φ_κ is the arc trace of K₀(2πκy)cos(2πκx).

### Index law (paper)
Let X ⊂ ℤ≥1 be finite. The even signed measures on the arc that annihilate M_κ for every κ ∈ ℤ≥1∖X form a space of dimension exactly |X|.

Proof.
1. In C⁴, the closure of the traces is ker ω₀ ∩ ⋂_{κ∈X} ker ω_κ ∩ ker d. Here:
   - ω₀ is the harmonic measure of the cusp;
   - ω_κ is the cusp-mode-κ functional of the bounded Dirichlet solution above the arc;
   - d is the r^{3/2} coefficient at the corner ρ, where the angle is 2π/3.
2. L² is onto C⁰ with kernel span{1, log(1−u²)}.
3. The rank is 2. Indeed ω₀(1) = 1. Also d(log(1−u²)) ≠ 0, because the cusp Martin function H > 0 has corner germ c·r^{3/2} with c > 0.

Gap: the C⁴ trace closure relies on C^k harmonic approximation up to a convex corner, which is sketched, not proved.

### Consequences
- TMP's probability measure is unique after symmetrisation. The corner density is ~(½−u)^{3/2}, so the law is α ≡ 3/2 (mod 3); this corrects row 408.
- The signed-density route to odd or primitive blind families (row 405) is closed.
- C⁰ case: `ModularArcWhittakerPositivity`'s annihilator is the cusp harmonic measure.

## Addendum L12 — null-face rigidity, the pole-weight window, and the keystone reduction (route-tt rows 415–419)

### 1. Analytic null-face rigidity (paper; same technical lemma as L11)
- Every Kelvin-symmetric off-axis charge witness satisfying the (N1) condition is the TMP arc witness.
  - Runge separation: only supports that separate the cusp from the axis carry constraints.
  - Kelvin pairs off the sphere have a free image part.
- No compactly supported test is Ξ²-divisible: exponential type versus N(T) ~ (T/2π)log T.

### 2. Pole-weight window ([L] `RHTower.WeilPoleWeightWindow`, `RHTower.WeilConeDegreePoleSandwich`)
- On blind tests every Weil functional is A + (β−1)P. Both A (pole + arch) and P (pole term) are ζ-free.
- Farkas at every β: cone_β ≠ ∅ ⟺ PrimeBlindPositiveAt β.
- The admissible β form an interval, with endpoint bounds from blind combinations.
- RH ⟺ 1 ∈ window.
- Paper: window = [1+κ₊, 1+c*], where
  - κ₊ = sup_{P>0}(−A/P) ≥ 0 unconditionally (TMP's G₀ has A = 0 and P > 0), and RH ⟺ κ₊ = 0 (plus c* ≥ 0 and pole-free positivity);
  - c* = inf_{P<0} A/|P|.
- Pole-order sandwich for RH members of C_d: d ≤ κ ≤ d(1+c*) ([L] upper bound mechanism).

### 3. Exact archimedean form
A(g) = (ψ(¼) − log π)·g(0) + ∫_0^∞ [(g(0) − g(x))·e^{x/2}/sinh x + 4g(x)cosh(x/2)] dx.

### 4. Keystone reduction (paper, exact)
- A compact core with Mf(1) = 0 gives the null test Ξ²R_f with pole term P = −(∫f log y)(∫f/y). This corrects the earlier claim that such tests are primitive.
- Within analytic ⊕ compact witnesses: ODD KEYSTONE (c* = 0, full κ>d closure) ⟺ a Ψ-blind compact core with ∫f = 0 and (∫f log y)(∫f/y) > 0.
- With no such cores, the null face is the single ray G₀, c* > 0 under RH, and κ>d is closable by cone methods only for d < 1/c*.

## Addendum L13 — correction to L12 (route-tt row 424)
- L12 §2 claimed c* > 0 under RH (a window of positive width). This is likely FALSE.
- Assume a Herglotz bridge at pole weight β: W_β-positivity on compactly supported tests ⟹ Herglotz Φ_β. This is the analogue of the β = 1 bridge in `HerglotzWeilPositiveBridge`.
  - Then the corpus density ceiling `le_one_of_herglotz_poleWeightFunction` gives cone_β = ∅ for β > 1, unconditionally.
  - So window ⊆ {1}, and c* = 0 under RH.
- Pole-negative near-null blind tests exist only in a non-tight limit (Tauberian scale). The tightness heuristic of route-tt row 416(d) was wrong.
- L12 §4's keystone reduction is correct as a statement about null tests, but the κ>d closure does not need it (see the stage-3 twin card addendum).

## Cross-reference (rh-goal-loop-opus row 1203, 2026-10-14): L13's bridge is a theorem
- The "Herglotz bridge at pole weight β" assumed in L13 is now [L] MUST-1463, in `RHTower/WeilPoleShiftHerglotzBridge` (`exists_herglotz_of_weilPositiveShift`). It needs no hypothesis on the weights, since polar tests give absolute convergence.
- With MUST-1458: `RHTower.eq_one_of_weilPositiveAt` (W_β-positive for some real lam ⟹ β = 1) and `eq_one_of_primeBlindPositiveAt` (window ⊆ {1}, unconditional) [L].
- Also [L]: RH ⟺ ∃β PrimeBlindPositiveAt β; and for every ε ≠ 0 some blind combination has S_A + εS_P < 0.
- Under RH, c* = 0 and κ₊ = 0 are both attained in the limit (`exists_blind_pole_{neg,pos}_of_riemannHypothesis`).

## Correction to T3 (rh-goal-loop-opus, 2026-10-14)
- T3's claim "a positive-definite invariant form exists iff RH" needs simplicity of the zeros as well.
- At a zero `a` of multiplicity `m ≥ 2`, the ρ-component of `A = O/(Ξ)` is the jet space `ℂ[ε]/(ε^m)`, `ε = z − a`. On it `M_q` acts as `q^{ia}·exp(iε log q)`: a character times a nontrivial unipotent one-parameter group.
- An invariant Hermitian form must be invariant under `{I + tN}` with `N ≠ 0` nilpotent (multiplication by `ε`). A positive-definite form is preserved only by a relatively compact group, and `{I + tN}` is not, so no such form exists on that component. Invariance gives `H(Nx, Ny) = 0`, so a positive semidefinite invariant form has all of `image N = span(ε, …, ε^{m−1})` in its radical: it sees only the value `F(a)`.
- Corrected statement: a positive-definite `M`-invariant Hermitian form on `A` exists iff every zero is real (RH) and simple. With multiple zeros, the best possible is a positive semidefinite form whose radical contains every jet of order `≥ 1`.
- This matches the corpus's simplicity-sensitive receivers (Báez-Duarte/Burnol rate at the simple-zero value ⟹ RH ∧ simplicity, MUST-876).

## Addendum L14 — laws from route-tt rows 435–450 (2026-10-14)
Paper unless marked; ζ-free statements are labelled as such.
1. **Strong violators are pole-negative** (row 437, corpus corollary of `weilArchRe_eq_levy_pole`).
   - On blind PD tests arch ≥ Ω(0)·g(0), so A ≥ P + Ω(0)g(0).
   - Any violator with A < −K·g(0) has P < −(K − 5.37)·g(0). PBAP is automatic on the pole-heavy part P ≥ 5.37·g(0).
   - The moment region {(P, arch)/g(0)} is convex. RH ⟺ its lower boundary a(P) satisfies a(P₀) = −P₀ and −1 ∈ ∂a(P₀), where P₀ is the pole of the null ray G₀.
2. **Node-dilation family** (rows 438–441). PBAP(t) means A ≥ 0 on tests blind at t·log n.
   - Theorem (dilation continuity): PBAP(t_k) with t_k → 1 implies RH.
   - PBAP(1) ⟹ PBAP(1/k), since the dilated node set is a superset.
   - Criticality: the null ray breaks one side of t = 1 according to the sign of S = Σ Λ(n)n^{−½}log n·G₀′(log n). Pole-negative near-null tests break every t > 1.
   - Conjectured quasi-RH ladder: PBAP(t) ⟺ the zero-free strip Re s > 1 − t/2 (plus an anomaly fill).
   - The dual of integer compression is Gauss multiplication. PBAP(½) is blind positivity for the weight-½ theta datum Γ_ℂ(s − ¼).
3. **Markov + pole** (rows 442–443). W = M + P. M (archimedean and prime jumps) is Markovian; P = ½⟨2cosh(u/2), f⟩² − ½⟨2sinh(u/2), f⟩² is the only anti-Markovian term (the corpus pole plane).
   - RH at each level ⟺ [M + ½cc* ≥ 0] ∧ [sinh-capacity ⟨s, (M + ½cc*)^{−1}s⟩ ≤ 2].
4. **Cores = ζ-divisible wandering vectors** (rows 444–448). A blind core f is the same as F = Σ_k f(k·) (a Nyman–Beurling sum) being orthogonal to all its integer dilates.
   - Farkas dual: no cores at ratio e^L ⟺ some combination of the pole kernel and the Kelvin chirps φ_n (n ≠ 1) is strictly PD on [−L, L].
   - Bounded separators are impossible beyond ratio ≈ 5.83. The relevant separators are Hurwitz-type combs, and the corpus ratio-2 proof uses the comb δ₀ + δ_½.
   - Dimension count gives threshold ratio 2.
   - Only n ≲ e^{|Ω(0)|} ≈ 215 Voronoi constraints resonate.
   - Core existence is OPEN. Its window consequence is superseded: window ⊆ {1} is already [L] in `WeilPoleWeightForcedOne`.
5. **One constant, three roles.** e^{|Ω(0)|} = 8πe^{γ+π/2} ≈ 215.3 is:
   - the even-character conductor threshold for informative blind positivity;
   - the resonant range of core constraints;
   - tied to the integers' Lévy capacity Cap < |Ω(0)| (row 446). That Cap < |Ω(0)| holds is certified by G₀; Cap ≈ |Ω(0)| itself is a rough estimate.
   - RH says Cap plus the pole covers the anomaly on every blind test.
6. **Pitt/Beckner** (row 450). In log coordinates Beckner's sharp log-uncertainty is exactly Ω ≥ Ω(0): the anomaly is Beckner's constant. The arithmetic half of Weil positivity is the same Pitt monotonicity for the multiplier ζ, which is RH.
- 2026-10-15 (opus loop row 1217): the L10 pole-order case **κ > d is CLOSED [L]** by MUST-1477, `RHTower.forall_re_weilDegreePoleFunctional_nonneg_iff`: W_{d,κ}(lam) ≥ 0 on every autocorrelation ⟺ κ = d ∧ RH ∧ lam = dΛ, for any real weights. It follows from W_{d,κ} = d·W_{κ/d}(lam/d) and `eq_one_of_weilPositiveAt` (MUST-1463). No odd blind family is needed.

## Lean status (formalization programme, 2026-10-17)
All modules below are unconditional (axioms propext, Classical.choice, Quot.sound only), compiled
with `lake env lean`, and wired into `GaloisForLFunctions/RHTower.lean`.
- **T1** [L] `RHTower.TrivialWeightBoostedWeilCone`: `ZetaGrowthExponent μ` (|ζ(σ+it)| ≤ K(1+|t|)^μ on
  σ ≥ ½, |t| ≥ 1; `.nonneg`), parametric producer `exists_herglotz_trivialWeights_boosted_of_growth`,
  `trivialWeights_boostedWeilCone` (∀ θ > μ ∃ C: 0 ≤ Re W_{λ≡1}(f⋆f̃) + (1/2π)∫|f̂|²C(1+|r|)^θ),
  unconditional convexity rung `trivialWeights_boostedWeilCone_of_quarter_lt` (θ > ¼). Infrastructure
  `RHTower.LineShiftHalfPlaneHolomorphic`.
- **T2** [L] `RHTower.PrimeGapDirichletContinuation`: `exists_gapDirichlet_continuation`,
  `tendsto_sub_one_mul_gapDirichletCont`, `norm_gapDirichletCont_critical_le`, unconditional instance
  at θ₂ = 71/100 (`gapDirichlet_continuation_hoheisel`). Heath-Brown's 5/18 is a cited input.
- **T3** [L] `RHTower.ZeroAlgebraJetInvariantForms` (with the multiplicity correction).
- **T4** [L] `RHTower.TranslationAveragedDensityDepthBlindness`.
- **T7** [L] corpus MUST-1442.
- **L3** [L] `ArchimedeanAnomalyConstantLaws`, `DigammaBinetFourthOrder`, `AnomalyWindowTwoPi`
  (`anomaly_window_two_pi`: Ω<0 ⟺ |τ|<t₀ with 2π < t₀ ≤ 2π+1/50).
- **L5** (i),(ii) [L] `ArchimedeanAnomalyConstantLaws.XiC_pole_points`,
  `RHTower.WeilLinearEffectivityObstruction`.
- **L6** [L] `RHTower.HermitianPencilEulerFactorObstruction`.
- **L10** [L] corpus parts (`weilPositiveDegree_iff`, κ>d closure MUST-1477).
- **L12** §1 second clause [L] `RHTower.CompactTestXiDivisibilityObstruction`; §2 corpus; §3 [L]
  `RHTower.WeilArchimedeanExactForm`; §4 computational part [L] `RHTower.CoreNullTestPoleSign`.
- **L13** corpus.
- **L14.1** [L] `ArchimedeanAnomalyConstantLaws` (i),(ii); `RHTower.BlindMomentRegion` (iii).
- **L14.2** [L] `RHTower.WeilNodeDilationFamily` (dilation continuity, PBAP(1)⟹PBAP(1/k), dilated
  data, half-dilation theta datum).
- **L14.3** [L] `RHTower.WeilMarkovPoleCapacity`.
- **L14.4** [L] `RHTower.ArchimedeanResonanceRange` (resonant range n ≤ 8πe^{γ+π/2}, resonances in
  |τ|<2π), `RHTower.KelvinChirpSeparatorBound` (rigorous ratio bound 4+2√2; the card's ≈5.83 is the
  heuristic value).
- **L14.5, L14.6** [L] `ArchimedeanAnomalyConstantLaws`.
- Not theorems on this card (no obligation): the PBAP structural-laws addendum (heuristic), L4, L8,
  L9, L11 index law and L12 §1 first clause (stated gap), the quasi-RH ladder conjecture, core existence.
- **Open formalization items**: T5 (Ruelle–Pollicott), T6 (nuclear Ruelle zeta), L1 (Maass–Selberg
  resonance identity), L2 (E* Fourier expansion, Hecke factorization), L7 (Davenport–Heilbronn),
  L10 twin-rigidity paper theorem + corollary, L14.2 criticality law (sign of S for G₀), L14.4
  NB-wandering reformulation and Farkas dual.
