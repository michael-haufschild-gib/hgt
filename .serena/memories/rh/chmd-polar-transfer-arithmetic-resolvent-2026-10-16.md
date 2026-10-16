# CHMD polar transfer + bounded arithmetic Weil operator (2026-10-16)

STATUS MUST-1541/MUST-1542. Card docs/drafts/pipeline/3-formalized/chmd-polar-transfer-arithmetic-resolvent-2026-10-16.md.
Three leaves, namespace RHTower.CHMDPolar, wired once each in GaloisForLFunctions/RHTower.lean (EOF):
- RHTower/CHMDPolarJumpForm.lean: polarEnergy v = ∫∫ cosh((x−y)/2)Θ(x)Θ(y)(v(x)−v(y))²; polarEnergy_eq: for MemLp v 2 massMeasure,
  = ∫v²dμ − 2(∫v dμ)² + 2(∫ v tanh(x/2) dμ)². Key: cosh((x−y)/2)ΘΘ = a(x)a(y) − b(x)b(y), a = Θcosh(·/2) (∫a = 1/2), b = Θsinh(·/2) (∫b = 0), six Fubini products.
- RHTower/CHMDPolarTransfer.lean: weilForm p := sourceEnergy p + 2⟨p,oneL⟩² − 2⟨p,tanhL⟩² on SourceGraph; weilForm_eq_edge_sub_polar (= ‖edge‖² − polarEnergy source);
  weilForm_compactLift (= Re zetaZeroConfig.W(Θv,Θv)); continuous; weilForm_critical = 0 (critical modes are even ⇒ ⟨c,tanh⟩ = 0);
  weilForm_normalized_tendsto_zero (cusp escape); weilForm_nonneg_of_riemannHypothesis (density of compactTests + W_re_nonneg_of_riemannHypothesis).
- RHTower/CHMDArithmeticResolvent.lean: Riesz lift of q ↦ ⟨w,q⟩_μ in the graph inner product; resolvent R : Lp →L[ℝ] Lp (‖R‖ ≤ 1, positive, selfadjoint),
  R oneL = oneL, R c = (1/2)c on critical modes; sourceEnergy (rieszLift w) = ⟨w,Rw⟩ − 2‖Rw‖²; weilOperator T = R − 2R∘R + 2 rankOne oneL − 2 rankOne (R tanhL);
  inner_weilOperator: ⟨Tw,w⟩ = weilForm (rieszLift w); T oneL = 0, T c = 0; dense_range_rieszLift; weilOperator_isPositive_iff: T.IsPositive ↔ ∀ p, 0 ≤ weilForm p.

Meaning: the frontier's "negative theta-cosh mass" is the diagonal of the polar jump form (rank-two kernel 2cosh(x/2)cosh(y/2) − 2sinh(x/2)sinh(y/2));
W(Θv) = J_arith(v) − J_polar(v) is a comparison of two Dirichlet forms with the same invariant measure μ (polar generator = 1 − 2|1⟩⟨1| + 2|τ⟩⟨τ|, τ = tanh(x/2)).
RH ⟺ (even sector) Poincaré inequality J_arith ≥ Var_μ with constant exactly 1 (corpus already has riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare);
in resolvent coordinates RH ⟺ R ≤ 1/2 on even primitives; critical band = exact 1/2-eigenspace of R.

Lean lessons: real_inner_smul_left does not rewrite smul inside the Submodule-typed SourceGraph inner product — go through graph_inner and `change` to the Lp components;
innerSL ℝ u x = ⟪u,x⟫ is rfl (innerSL_apply_apply exists); deprecated ContinuousLinearMap.sub_apply/add_apply/smul_apply → root sub_apply/add_apply/smul_apply;
integral_prod_mul needs explicit function arguments; Integrable.mul_prod for f(x)g(y); integral_sub/add need integrands stated as explicit lambdas (Pi-sum forms do not match);
no Real.continuous_tanh in this toolchain (use sinh/cosh quotient); riemannKernelReal_neg lives in RHTower.WeilExcess; `module` tactic closes the smul identities.
Lint: global gate exit 1 only for unrelated untracked RHTower/CHMDTranslatedRelativeGraph (other agent).

Next conjectures (loop): (1) exact essential spectrum of R: is 1/2 ∈ σ_ess(R) (Weyl sequence from the cusp escape needs the pointwise generator on compact tests);
(2) Birman–Schwinger / Hodge-index count: #eigenvalues of R in (1/2,1] on even primitives = #nonreal Xi orbits; (3) polar domination J_polar ≤ J_arith on sectors
beyond the window: fails as a margin statement (prime tail beyond a window costs ε_A cosh(x/2)); (4) the twisted translation flow U_T v = Θ(·−T)v(·−T)/Θ preserves weilForm exactly (W translation invariant) — its generator D = Θ⁻¹∂Θ is weilForm-skew; critical band = U-orbit of the ground state.
