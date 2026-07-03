/-
# The `φ_b` bridge: the m-step branch `ψ` has a concrete analytic Kummer root, identified by the FE

The geometric half of the "full finite Böttcher tower" connection.  `U0MStepKummer` proved the
ALGEBRAIC half — `u₀` is independent of any field-theoretic `2^k`-th root of `ψ = bottcherCoord∘f^[N]`.
Here we exhibit such a root CONCRETELY and pin it to the inverse Böttcher branch:

* **Functional-equation identification** (`psiN_eq_bottcherCoord_pow`): on the escape region,
  `ψ_N = (bottcherCoord)^(2^N)` — the committed Böttcher FE `bottcherCoord_iterate`.  So the actual
  window branch `φ_b = bottcherCoord` IS a `2^N`-th root of `ψ_N` on the overlap where it is defined.

* **Analytic root lift** (`exists_analyticOnNhd_pow_eq`): the window disk `ball 0 r` is convex, hence
  simply connected, and `ψ_N` is analytic and nowhere zero on it — so `ψ_N` has a genuine ANALYTIC
  `2^k`-th root there, for every `k`.  The root is `exp(L/2^k)` for an analytic logarithm `L` of
  `ψ_N`; `bottcherLog` cannot serve as `L` (it carries a slit), but the simply-connectedness of the
  disk supplies a slit-free branch.  The upgrade "continuous branch of `log` ⟹ analytic branch"
  is `analyticOnNhd_of_continuousOn_exp_eq`, a reusable lemma proved here by `exp`-injectivity on a
  small ball.

Feeding this concrete analytic root to `u0_mstep_kummer_independence` gives
`u0_mstep_kummer_branch_independence`: a genuine analytic branch — the sub-threshold window branch
`φ_b`, `2^k` levels down the Böttcher tower — that is algebraically independent of `u₀` over `ℂ(z)`.
The Kummer independence is thus NON-VACUOUS: it is about real branches.
-/
import GaloisForLFunctions.U0.U0MStepKummer
import Mathlib.Analysis.Real.Pi.Bounds

open Complex Set Metric Filter Topology Bottcher
open U0MStepBranch U0PhiMStep U0MeroCarrier U0PhiMStepFar U0MStepKummer

namespace U0KummerBranch

/-! ## A continuous branch of `log` of an analytic non-vanishing function is analytic -/

/-- **Continuous `log`-branch ⟹ analytic.**  If `exp ∘ f = g` on an open set `U` with `g` analytic,
then the continuous branch `f` is itself analytic.  (`g` is automatically nowhere zero.)  Proof:
near each `z₀`, `f` agrees with the explicit branch `f z₀ + log(g z / g z₀)` — both are `log`s of `g`
landing in a ball of radius `1 < π` where `exp` is injective, so they coincide; that branch is
differentiable, and `DifferentiableOn ⟹ AnalyticOnNhd`. -/
theorem analyticOnNhd_of_continuousOn_exp_eq {U : Set ℂ} (hUo : IsOpen U)
    {f g : ℂ → ℂ} (hf : ContinuousOn f U) (hg : AnalyticOnNhd ℂ g U)
    (hexp : ∀ z ∈ U, Complex.exp (f z) = g z) :
    AnalyticOnNhd ℂ f U := by
  apply DifferentiableOn.analyticOnNhd _ hUo
  intro z₀ hz₀
  have hz₀mem : U ∈ 𝓝 z₀ := hUo.mem_nhds hz₀
  have hg0 : g z₀ ≠ 0 := by rw [← hexp z₀ hz₀]; exact Complex.exp_ne_zero _
  set h : ℂ → ℂ := fun z => f z₀ + Complex.log (g z / g z₀) with hh
  have hgAt : DifferentiableAt ℂ g z₀ := (hg z₀ hz₀).differentiableAt
  have htend1 : Tendsto (fun z => g z / g z₀) (𝓝 z₀) (𝓝 1) := by
    have hc : ContinuousAt (fun z => g z / g z₀) z₀ := (hgAt.continuousAt).div_const _
    have ht := hc.tendsto
    rwa [div_self hg0] at ht
  have h_slit : ∀ᶠ z in 𝓝 z₀, g z / g z₀ ∈ slitPlane :=
    htend1 (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hlogdiff : DifferentiableAt ℂ (fun z => Complex.log (g z / g z₀)) z₀ := by
    apply (Complex.differentiableAt_log ?_).comp z₀ (hgAt.div_const _)
    show g z₀ / g z₀ ∈ slitPlane
    rw [div_self hg0]; exact Complex.one_mem_slitPlane
  have hhdiff : DifferentiableAt ℂ h z₀ := (differentiableAt_const _).add hlogdiff
  have hexph : ∀ᶠ z in 𝓝 z₀, Complex.exp (h z) = g z := by
    filter_upwards [h_slit, hz₀mem] with z hz hzU
    have hgz : g z ≠ 0 := by rw [← hexp z hzU]; exact Complex.exp_ne_zero _
    rw [hh, Complex.exp_add, Complex.exp_log (div_ne_zero hgz hg0), hexp z₀ hz₀]
    field_simp
  have hfcontAt : ContinuousAt f z₀ := hf.continuousAt hz₀mem
  have hh0 : h z₀ = f z₀ := by simp [hh, div_self hg0]
  have hf_near : ∀ᶠ z in 𝓝 z₀, f z ∈ ball (f z₀) 1 := hfcontAt (ball_mem_nhds _ one_pos)
  have hh_near : ∀ᶠ z in 𝓝 z₀, h z ∈ ball (f z₀) 1 :=
    hhdiff.continuousAt (by rw [hh0]; exact ball_mem_nhds _ one_pos)
  have hfh : f =ᶠ[𝓝 z₀] h := by
    filter_upwards [hexph, hf_near, hh_near, hz₀mem] with z hze hzf hzh hzU
    have hee : Complex.exp (f z) = Complex.exp (h z) := by rw [hexp z hzU, hze]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hee
    have hfhn : f z - h z = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by rw [hn]; ring
    have hdist : ‖f z - h z‖ < 2 := by
      have h1 : ‖f z - f z₀‖ < 1 := by rw [← dist_eq_norm]; exact hzf
      have h2 : ‖h z - f z₀‖ < 1 := by rw [← dist_eq_norm]; exact hzh
      calc ‖f z - h z‖ = ‖(f z - f z₀) - (h z - f z₀)‖ := by ring_nf
        _ ≤ ‖f z - f z₀‖ + ‖h z - f z₀‖ := norm_sub_le _ _
        _ < 2 := by linarith
    have hnormval : ‖f z - h z‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hfhn, norm_mul, norm_mul, norm_mul]
      simp [Complex.norm_I, Complex.norm_real, Complex.norm_intCast, abs_of_pos Real.pi_pos]
    have hn0 : n = 0 := by
      by_contra hne
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (by exact_mod_cast hne)
      nlinarith [hnormval, hdist, hn1, Real.pi_gt_three]
    have hzero : f z - h z = 0 := by rw [hfhn, hn0]; simp
    exact sub_eq_zero.mp hzero
  exact ((hfh.differentiableAt_iff).mpr hhdiff).differentiableWithinAt

/-! ## Analytic `n`-th roots on simply connected domains -/

/-- **Analytic `n`-th root on a simply connected domain.**  A nowhere-zero analytic `g` on an open
simply connected `U ⊆ ℂ` has an analytic, nowhere-zero `n`-th root (`n ≠ 0`).  Combines mathlib's
continuous log branch on simply connected sets with the analytic upgrade above. -/
theorem exists_analyticOnNhd_pow_eq {U : Set ℂ} (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ χ : ℂ → ℂ, AnalyticOnNhd ℂ χ U ∧ (∀ z, χ z ≠ 0) ∧ ∀ z ∈ U, χ z ^ n = g z := by
  have hU0 : (0 : ℂ) ∉ g '' U := by rintro ⟨z, hz, hgz⟩; exact hg0 z hz hgz
  obtain ⟨f, hfc, hfeq⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUsc hUo hg.continuousOn hU0
  have hfan : AnalyticOnNhd ℂ f U :=
    analyticOnNhd_of_continuousOn_exp_eq hUo hfc hg (fun z hz => hfeq hz)
  refine ⟨fun z => Complex.exp (f z / n), ?_, fun z => Complex.exp_ne_zero _, ?_⟩
  · have hdiff : DifferentiableOn ℂ (fun z => Complex.exp (f z / n)) U :=
      fun z hz => (((hfan z hz).differentiableAt.div_const (n : ℂ)).cexp).differentiableWithinAt
    exact hdiff.analyticOnNhd hUo
  · intro z hz
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn : (n : ℂ) ≠ 0)]
    exact hfeq hz

/-! ## The functional-equation identification `ψ_N = φ_b^(2^N)` -/

/-- **The FE identification.**  On the escape region, the m-step branch equals the `2^N`-th power of
the inverse Böttcher coordinate: `ψ_N = (bottcherCoord)^(2^N)`.  So the genuine window branch
`φ_b = bottcherCoord` is a `2^N`-th root of `ψ_N` wherever it is defined — the identification that
ties the abstract Kummer layer to the actual Böttcher tower. -/
theorem psiN_eq_bottcherCoord_pow {b : ℂ} {N : ℕ} {z : ℂ} (hz : z ∈ escapeOpen b) :
    psiN b N z = (bottcherCoord b z) ^ (2 ^ N) := by
  obtain ⟨hc, hz2⟩ := mem_escapeOpen_regime hz
  exact bottcherCoord_iterate hc hz2 N

/-! ## The concrete analytic Kummer branch and its independence from `u₀` -/

/-- **A concrete analytic `2^k`-th root of `ψ_N` on the window** — for every viable parameter.  The
window disk is simply connected and `ψ_N` is analytic and nowhere zero on it, so `ψ_N` has a genuine
analytic branch `2^k` levels down the Böttcher tower. -/
theorem exists_analytic_root_psiN {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) (k : ℕ) :
    ∃ (r : ℝ) (N : ℕ), 1 < r ∧
      ∃ χ : ℂ → ℂ, AnalyticOnNhd ℂ χ (ball (0 : ℂ) r) ∧ (∀ z, χ z ≠ 0) ∧
        ∀ z ∈ ball (0 : ℂ) r, χ z ^ (2 ^ k) = psiN b N z := by
  obtain ⟨r, hr, N, hcl⟩ := exists_clearance_escapeOpen hviab
  have hr0 : 0 < r := lt_trans one_pos hr
  have hUsc : IsSimplyConnected (ball (0 : ℂ) r) := by
    haveI : ContractibleSpace (ball (0 : ℂ) r) := Metric.contractibleSpace_ball hr0
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨χ, hχan, hχ0, hχpow⟩ :=
    exists_analyticOnNhd_pow_eq isOpen_ball hUsc (psiN_analyticOnNhd hcl)
      (fun z _ => psiN_ne_zero b N z) (pow_ne_zero k (two_ne_zero))
  exact ⟨r, N, hr, χ, hχan, hχ0, hχpow⟩

/-- **A concrete analytic Kummer branch of `ψ`, independent of `u₀` — unconditional.**  For every
viable parameter and every `k`, there is a window and a genuine analytic, nowhere-zero branch `χ`
— a `2^k`-th root of `ψ_N = bottcherCoord ∘ f^[N]`, i.e. the sub-threshold window branch `φ_b`
carried `k` Böttcher-levels down the tower — that is algebraically independent of `u₀` over `ℂ(z)`.
The Kummer independence is thereby NON-VACUOUS: it holds of a real analytic branch, not merely of
hypothetical field-theoretic roots.  This is the full `φ_b`-bridge: the FE identifies `χ` with the
inverse Böttcher branch, and the descent gives its independence. -/
theorem u0_mstep_kummer_branch_independence {b : ℂ}
    (hviab : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia b) (k : ℕ) :
    ∃ (r : ℝ) (N : ℕ) (hr : 1 < r) (χ : ℂ → ℂ)
      (hχ : AnalyticOnNhd ℂ χ (ball (0 : ℂ) r)),
      (∀ z, χ z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) r, χ z ^ (2 ^ k) = psiN b N z) ∧
      letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
        (annMB_nonempty hr)
      letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
        (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
          (annMB_infinite hr)).toAlgebra
      NoRelation (RatFunc ℂ)
        (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
          ⟨Germ.coeRingHom (𝓟 (annMB r)) χ, ⟨χ, hχ.mono inter_subset_left, rfl⟩⟩)
        (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
          (u0AnSub annMB_subset_Ext)) := by
  have hc : (0 : ℂ) ∉ filledJulia b := zero_not_mem_of_viable hviab
  obtain ⟨r, hr, N, hN, hcl_far⟩ := exists_clearance_farBound hviab hc
  have hcl : ∀ z : ℂ, ‖z‖ ≤ r → (quadratic b)^[N] z ∈ escapeOpen b := fun z hz => (hcl_far z hz).1
  have hfarbound : ∀ z : ℂ, ‖z‖ ≤ r → bottcherFarBound b hc < ‖(quadratic b)^[N] z‖ :=
    fun z hz => (hcl_far z hz).2
  have hr0 : 0 < r := lt_trans one_pos hr
  have hUsc : IsSimplyConnected (ball (0 : ℂ) r) := by
    haveI : ContractibleSpace (ball (0 : ℂ) r) := Metric.contractibleSpace_ball hr0
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨χ, hχan, hχ0, hχpow⟩ :=
    exists_analyticOnNhd_pow_eq isOpen_ball hUsc (psiN_analyticOnNhd hcl)
      (fun z _ => psiN_ne_zero b N z) (pow_ne_zero k (two_ne_zero))
  refine ⟨r, N, hr, χ, hχan, hχ0, hχpow, ?_⟩
  letI := isDomain_analyticSubring (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr)
    (annMB_nonempty hr)
  letI : Algebra (RatFunc ℂ) (meroField (annMB r)) :=
    (ratfuncToMero (annMB r) (isOpen_annMB r) (isPreconnected_annMB hr) (annMB_nonempty hr)
      (annMB_infinite hr)).toAlgebra
  have hNoRel := u0_psiN_independence hr hcl (psiN_transcendental hr hN hc hcl hfarbound)
  refine noRelation_pow_descent _ _ (2 ^ k) ?_
  have hpoweq :
      (algebraMap (analyticSubring (annMB r)) (meroField (annMB r))
        ⟨Germ.coeRingHom (𝓟 (annMB r)) χ, ⟨χ, hχan.mono inter_subset_left, rfl⟩⟩) ^ (2 ^ k)
        = algebraMap (analyticSubring (annMB r)) (meroField (annMB r)) (psiNAn hcl) := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    show (Germ.coeRingHom (𝓟 (annMB r)) χ) ^ (2 ^ k)
      = (Germ.coeRingHom (𝓟 (annMB r)) (psiN b N))
    have hc1 : (Germ.coeRingHom (𝓟 (annMB r)) χ) = (↑χ : Germ (𝓟 (annMB r)) ℂ) := rfl
    have hc2 : (Germ.coeRingHom (𝓟 (annMB r)) (psiN b N))
        = (↑(psiN b N) : Germ (𝓟 (annMB r)) ℂ) := rfl
    rw [hc1, hc2, ← Germ.coe_pow, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z hz
    exact hχpow z (inter_subset_left hz)
  rw [hpoweq]
  exact hNoRel

end U0KummerBranch
