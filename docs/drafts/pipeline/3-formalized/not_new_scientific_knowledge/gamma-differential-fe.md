# The differentiated functional equation of Γ (machinery for the differential Hölder rungs)

- **ID:** gamma-differential-fe
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. The named machinery the order-≥1 rungs of `Hypertranscendental Γ` require.
- **Statements:**
  - `contDiffAt_Gamma (x) (x∉−ℕ) (n) : ContDiffAt ℂ n Γ x` — Γ is C^∞ off the poles (as reciprocal of the entire, locally-nonvanishing 1/Γ). Reusable.
  - `iteratedDeriv_Gamma_add_one (k) (x) (x∉−ℕ) : Γ⁽ᵏ⁾(x+1) = x·Γ⁽ᵏ⁾(x) + k·Γ⁽ᵏ⁻¹⁾(x)` — the differentiated functional equation, all orders.
  - `gamma_prod (k) (s) (no pole among s..s+k) : Γ(s)·∏_{j=0}^{k}(s+j) = Γ(s+k+1)` — finite unwinding of the FE.
  - `gamma_residue (k) : (s+k)·Γ(s) → (−1)^k/k!` — the RESIDUE of Γ at every pole (induction on k).
  - `contDiffAt_deriv_Gamma` (Γ′ continuous off −ℕ) + `continuousAt_digamma` (ψ=Γ′/Γ continuous off −ℕ).
  - `digamma_residue (k) : (s+k)·ψ(s) → −1` — the residue of digamma at every pole is −1 (same induction, additive FE ψ(s+1)=ψ(s)+1/s).
  - `gamma_deriv_residue (k) : (s+k)²·Γ′(s) → −(−1)^k/k!` — the residue of Γ′, as the PRODUCT [(s+k)ψ]·[(s+k)Γ] (using Γ′=ψΓ). This is the derivative-residue the higher-rung pole-counting argument needs; higher orders follow via the polygamma analogues.
  All absent from mathlib; the leading Laurent data for the (k!)-domination Hölder argument.
- **Proof mechanism:** shift Γ(x+1)=iteratedDeriv of s↦Γ(s+1) (`iteratedDeriv_comp_add_const`); Γ(s+1)=s·Γ(s) as an EventuallyEq near x≠0 (`Gamma_add_one` + `EventuallyEq.iteratedDeriv_eq`); Leibniz (`iteratedDeriv_mul`) on s·Γ(s), where only the order-0 and order-1 derivatives of the factor s survive (the rest vanish by `iteratedDeriv_id_add_two`).
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/GammaDifferentialFE.lean`. Axiom-clean, builds standalone.
- **Significance:** this is how the functional equation enters the DIFFERENTIAL structure. mathlib had only k=0 (Gamma_add_one) and k=1 (deriv_Gamma_add_one); the general-k recurrence is new. It is the load-bearing tool for attacking `P(s, Γ, Γ', …) = 0` — the order-≥1 rungs the order-0 pole argument cannot reach.

## Log
- 2026-07-08 — created (built the named next-machinery: general-k differentiated FE + Γ smoothness).

## Update: the GENERAL derivative residue (all orders) — PROVEN
`gamma_iteratedDeriv_residue (j k) : Tendsto (fun s => (s+k)^(j+1) * iteratedDeriv j Γ s) (𝓝[≠]−k) (𝓝 ((−1)^j·j!·((−1)^k/k!)))`. The full Laurent leading datum of EVERY derivative of Γ at EVERY pole, one theorem for all orders. Proof: analytic factorization Γ=G̃·(s+k)⁻¹ (gamma_factor_near_pole) on the open no-pole set, Leibniz (iteratedDeriv_mul) against the simple-pole derivatives (iteratedDeriv_inv_add_const), and s→−k where only the zeroth Leibniz term survives (value G̃(−k)=r_k via gammaExtension_apply_neg; higher terms carry (s+k)^i→0). Supporting: continuousAt_iteratedDeriv_of_contDiffAt, contDiffAt_gammaExtension. Axiom-clean, zero warnings. This is exactly the input the (k!)-domination step of full Hölder consumes.

## Update: first-order LINEAR Hölder — Γ is not D-finite of order 1 — PROVEN
`gamma_no_linear_relation (c0 c1 : ℂ[X]) (c0≠0 ∨ c1≠0) : ∃ s, c0.eval s·Γ s + c1.eval s·Γ′ s ≠ 0`. Γ satisfies no first-order LINEAR differential relation with polynomial coefficients — equivalently Γ′/Γ=digamma is not rational. The LINEAR case of Hölder's theorem, proven DIRECTLY from the residue calculus (no combinatorial weighted-degree machinery): ×(s+k)², the Γ term →0 while the Γ′ term survives (gamma_deriv_residue: (s+k)²Γ′→−r_k), forcing c1(−k)=0 at every pole ⟹ c1≡0 (infinite roots); then c0·Γ=0, Γ≠0 ⟹ c0≡0. Axiom-clean. First genuine differential-non-existence theorem for Γ, validating the residue calculus as a hypertranscendence engine.

## Update: Γ IS NOT HOLONOMIC — full LINEAR Hölder, all orders — PROVEN
`gamma_not_holonomic (n) (c : ℕ→ℂ[X]) (∀s, ∑_{j≤n} (c j).eval s · Γ⁽ʲ⁾ s = 0) : ∀ j≤n, c j = 0`. Γ satisfies NO linear differential equation with polynomial coefficients of ANY order — Γ is not D-finite/holonomic. The ENTIRE linear case of Hölder's hypertranscendence theorem, proved from the residue calculus with NO combinatorial weighted-degree machinery. Crux `gamma_linear_top_zero`: ×(s+k)^{n+1} makes the highest term dominate (factor (s+k)^{n-j}→0 for j<n), forcing top coeff c_n(−k)=0 at every pole ⟹ c_n≡0 (infinite roots); induction down (gamma_iteratedDeriv_residue). Axiom-clean. This is a genuine strong theorem — the linear rungs of Hölder at ALL orders, discharged.

## Update: ABSTRACT not-holonomic engine + digamma unwinding
`not_holonomic_of_residues (f) (L) (hL : ∀ i k, L i k ≠ 0) (hres : (s+k)^{i+1}·f⁽ⁱ⁾ → L i k) : f satisfies no linear ODE with poly coeffs of any order`. The pole-domination argument abstracted — it depends only on the derivative-residue structure, not on Γ. `gamma_not_holonomic` is now a one-line instance (L = (−1)^i i! r_k, hres = gamma_iteratedDeriv_residue). `digamma_unwind` (ψ(s+k+1)=ψ(s)+∑_{j≤k}1/(s+j), the digamma analogue of gamma_prod) sets up the polygamma residues → digamma not holonomic as the SECOND instance (via G_ψ=(s+k)ψ analytic-extension route, G_ψ(−k)=−1). Axiom-clean.

## Update: DIGAMMA is not holonomic — second instance of the abstracted engines
Two abstract engines now built: `iteratedDeriv_residue_of_factor` (any `f=G·(s+k)⁻¹` simple-pole factorization ⟹ all-order derivative residues `(s+k)^{i+1}f⁽ⁱ⁾→G(−k)·(−1)^i i!`) and `not_holonomic_of_residues` (nonvanishing derivative residues ⟹ not holonomic). Digamma instance: `digammaExtension k s = (s+k)(ψ(s+k+1)−∑_{j<k}1/(s+j))−1` (value −1 at −k, from `digamma_unwind`) ⟹ `digamma_iteratedDeriv_residue` ((s+k)^{i+1}ψ⁽ⁱ⁾→(−1)^{i+1}i!, all polygamma residues) ⟹ `digamma_not_holonomic`. Γ and digamma both proven not-D-finite by ONE engine. Axiom-clean.

## Update: FIRST-ORDER NONLINEAR HÖLDER (weighted-homogeneous) — PROVEN
`gamma_no_weightedHomog_firstOrder (N d) (2N≤d) (c) (∀s off-poles, ∑_{b≤N} c_b(s)·Γ^{d-2b}·(Γ')^b = 0) : ∀b≤N, c_b=0`. Γ satisfies NO nontrivial weighted-homogeneous first-order algebraic differential relation — the first genuinely NONLINEAR differential-non-existence theorem for Γ. Analytic layer (per-monomial residue (s+k)^d·Γ^{d-2b}(Γ')^b → r_k^{d-2b}(-r_k)^b via gamma_residue^{d-2b}·gamma_deriv_residue^b) + arithmetic layer (factorial_dirichlet_vanishing: the (Γ,Γ') jet has NO monomial ties, so the leading Laurent coefficient is a factorial-Dirichlet polynomial that must vanish coefficient-wise). Axiom-clean. The nonlinear founding theorem's first rung, DONE — both layers wired.
