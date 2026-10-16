# CHMD pointwise generator + threshold Weyl sequence (2026-10-16)

STATUS MUST-1543/1544. Card docs/drafts/pipeline/3-formalized/chmd-pointwise-generator-threshold-weyl-2026-10-16.md.
Four leaves, namespace RHTower.CHMDPolar, wired at EOF of GaloisForLFunctions/RHTower.lean:
- CHMDThetaHarmonicIdentity: theta_harmonic_identity x : primeKernelSum x = cosh(x/2) − 2·archConstantReal·Θ x + ∫_{Ioi 0} symArchTerm x u,
  derived from ThetaSourceWard.literal_complete_theta_source_equation at x and −x (Θ even); polar_halfLine_sum (two half-line polar integrals = cosh(x/2)).
- CHMDPointwiseGenerator: symJump v s y = Θ(y+s)(v y − v(y+s)) + Θ(y−s)(v y − v(y−s)); genArch v y = ∫_{Ioi 0} ω·symJump; genPrime = Σ' a_n symJump (log n);
  inner_edge_compactLift: ⟨edge v, edge w⟩ = ∫ w Θ genTotal v (Fubini on archBase, prime pushforwards, integral_tsum exchange). Bounds: exists_genArch_bound (uniform),
  abs_genPrime_le (≤ 2‖v‖∞ primeKernelSum), exists_primeKernelSum_bound (≤ cosh + K via harmonic identity + abs_gammaSourceTerm_le_bound; NO Chebyshev needed).
- CHMDGeneratorWeilOperator: weilOp f y = −2c f y + ∫_{Ioi}(2ν f y − ω(f(y+u)+f(y−u))) − Σ a_n(f(y±log n)); genTotal_eq_weilOp: genTotal v − cosh·v = weilOp(Θv);
  genImage v = genTotal/cosh − v bounded ⇒ MemLp 2; sourcePair_compactLift: sourcePair (compactLift v) q = ⟨genImageL v, q.fst⟩ ∀ q (density + continuity);
  resolvent_compactLift_source: R v = ½v − ½R(genImage v); norm_resolvent_sub_half_le: ‖(R − ½)v‖ ≤ ½‖genImageL v‖.
- CHMDThresholdWeylSequence: weilOp_translate (covariance); exists_genImage_test_bound (‖G test_T‖² ≤ A + B cosh²(T/2)); inverseMass_translate_lower
  (≥ ∫profile²·exp(πe^{2(T−R)})/(E_U e^{9(T+R)/2}) via HedenmalmThetaSource.thetaEnvelope + CHMDThetaTranslate.theta_upper); resolvent_defect_tendsto_zero;
  exists_weyl_sequence (orthonormal e_n, ‖(R−½)e_n‖ → 0); half_mem_spectrum_resolvent : (1/2) ∈ spectrum ℝ resolvent.

Meaning: the arithmetic generator on compact tests is the explicit pole-free Weil operator in Doob coordinates; the critical value is essential spectrum of the
bounded resolvent R (operator-level version of the "no positive primitive margin"). RH ⟺ σ(R|even prim) ⊆ [0,½] where ½ = top of essential spectrum ⇒ off-line
zeros would be bound states above the essential spectrum.

Lean lessons: `translate` is ambiguous (root vs CHMDTranslation) — qualify; `lift` clashes between CHMDThetaTranslate and CHMDEscape — do not open both;
integral_complex_ofReal (not integral_ofReal via rw) for set integrals of casts; intervalIntegral.integral_Iic_add_Ioi; integral_comp_neg_Ioi;
Measurable.tsum exists (measurability of prime series); StronglyMeasurable.integral_prod_right' for parametric integrals; Integrable.mul_prod needs explicit (μ ν f g);
integral_integral_swap needs the uncurried integrand in exactly `fun t y => ...` form (use simp_rw [← integral_const_mul] first); `dsimp only` to beta-reduce
setIntegral_congr_fun goals; IntegrableOn.congr_fun via explicit `have h : IntegrableOn (f + g) s` (Integrable.add unfolds to And otherwise);
ContinuousLinearMap.mul_apply/one_apply deprecated — use congrArg on the unit equation + rfl; `div_eq_inv_mul` rewrites `1/2` too (use div_eq_mul_inv at the end);
gcongr needs `0 ≤ vonMangoldtAtom n` as a hypothesis in context; `push_neg` deprecated → rw [not_le].

Next conjectures: (1) σ_ess(R) ⊆ [0, ½] unconditionally? (needs: no Weyl sequences of R in (½,1] — equivalent to finiteness of off-line orbits... likely false to prove
unconditionally; the right statement is the Birman–Schwinger count: #eigenvalues of R in (½,1] on even primitives = #nonreal Xi orbits); (2) the eigenvalue equation
R w = λ w for λ > ½ in the explicit form weilOp(Θ v) = (1/λ − 2) cosh·v and its relation to the cardinal frames; (3) [½,1) ∩ σ(R) ≠ ∅ without off-line zeros? no:
under RH σ(R|even prim) ⊆ [0,½].
