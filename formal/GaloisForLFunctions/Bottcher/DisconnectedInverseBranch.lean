/-
# Inverse branches of a disconnected quadratic map over a Green sublevel set

Let `c ∉ M`, so the critical point escapes and `t₀ = G_c(0) > 0`.

* **Collars.**  For `t₀ < σ` the basin part `{0 < G_c < σ}` of the sublevel set is connected.  The
  collar `{log r < G_c < σ}` (`t₀ < log r`) is the image of a round annulus under the inverse
  Böttcher section, hence connected, and every component of the band meets it: a component staying
  below the collar would be closed in the connected basin.
* **Inverse branches.**  Fix `D = {G_c < s}` with `t₀ < s < 2t₀`.  The critical value `c` lies above
  `D`, so every closed loop in `D` has winding number zero about `c`.  A component `E` of
  `f_c⁻¹(D) = {G_c < s/2}` contains no pair `z, -z`: a `C¹` path from `z` to `-z` in `E` maps to a
  loop in `D` whose winding integral about `c` is `2∫γ'/γ`, while `exp ∫γ'/γ = -1`.  Hence `f_c` is
  injective on `E` and maps it onto the connected `D`; its inverse `g : D → E` is holomorphic, and
  `f_c⁻¹(D) = E ∪ -E`, so the two inverse branches over `D` are `±g`.
-/
import GaloisForLFunctions.Bottcher.PlanarSmoothPaths
import GaloisForLFunctions.Bottcher.GreenPullback
import GaloisForLFunctions.Bottcher.SectionTowerStep
import GaloisForLFunctions.Bottcher.JuliaBasinCrossing
import GaloisForLFunctions.Bottcher.GreenLogDeriv
import GaloisForLFunctions.Bottcher.GreenSublevel

open Complex Set Filter Topology Metric

namespace Bottcher

/-! ### Collars -/

/-- An open `O` inside a preconnected `X`, missing a point of `X`, containing a preconnected `C`,
and such that limit points in `X` of `O ∖ C` stay in `O`, is preconnected: each of its components
meets `C`. -/
theorem isPreconnected_of_collar {X O C : Set ℂ} (hX : IsPreconnected X) (hOo : IsOpen O)
    (hOX : O ⊆ X) (hout : ∃ z ∈ X, z ∉ O) (hC : IsPreconnected C) (hCO : C ⊆ O)
    (hbelow : ∀ y ∈ X, y ∈ closure (O \ C) → y ∈ O) : IsPreconnected O := by
  have hmeet : ∀ z ∈ O, (connectedComponentIn O z ∩ C).Nonempty := by
    intro z hz
    by_contra hcon
    rw [not_nonempty_iff_eq_empty] at hcon
    have hAO : connectedComponentIn O z ⊆ O := connectedComponentIn_subset _ _
    have hAo : IsOpen (connectedComponentIn O z) := hOo.connectedComponentIn
    have hAC : connectedComponentIn O z ⊆ O \ C := fun y hy =>
      ⟨hAO hy, fun hyC => (eq_empty_iff_forall_notMem.mp hcon) y ⟨hy, hyC⟩⟩
    have hXsub : X ⊆ connectedComponentIn O z ∪ (closure (connectedComponentIn O z))ᶜ := by
      intro y hy
      by_cases h : y ∈ closure (connectedComponentIn O z)
      · exact Or.inl (mem_connectedComponentIn_of_mem_closure_of_isOpen hOo h
          (hbelow y hy (closure_mono hAC h)))
      · exact Or.inr h
    have hdisj : Disjoint (connectedComponentIn O z) (closure (connectedComponentIn O z))ᶜ :=
      (disjoint_compl_right (a := closure (connectedComponentIn O z))).mono_left subset_closure
    have hXA := hX.subset_left_of_subset_union hAo isClosed_closure.isOpen_compl hdisj hXsub
      ⟨z, hOX hz, mem_connectedComponentIn hz⟩
    obtain ⟨w, hwX, hwO⟩ := hout
    exact hwO (hAO (hXA hwX))
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  refine ⟨connectedComponentIn O x, connectedComponentIn_subset _ _, mem_connectedComponentIn hx,
    ?_, isPreconnected_connectedComponentIn⟩
  obtain ⟨a, haA, haC⟩ := hmeet x hx
  obtain ⟨b, hbB, hbC⟩ := hmeet y hy
  have hCa : C ⊆ connectedComponentIn O x := by
    rw [connectedComponentIn_eq haA]; exact hC.subset_connectedComponentIn haC hCO
  have hCb : C ⊆ connectedComponentIn O y := by
    rw [connectedComponentIn_eq hbB]; exact hC.subset_connectedComponentIn hbC hCO
  rw [connectedComponentIn_eq (hCa hbC), ← connectedComponentIn_eq (hCb hbC)]
  exact mem_connectedComponentIn hy

/-- **The collar below a level `σ > G_c(0)`**: a band `{log r < G_c < σ}` with `G_c(0) < log r`,
which is preconnected. -/
theorem exists_green_collar (c : ℂ) {σ : ℝ} (hσ : greenFunctionDyn c 0 < σ) :
    ∃ r : ℝ, greenFunctionDyn c 0 < Real.log r ∧ Real.log r < σ ∧
      IsPreconnected {z : ℂ | Real.log r < greenFunctionDyn c z ∧ greenFunctionDyn c z < σ} := by
  obtain ⟨rlo, -, R₀, -, h1, -, -, -, hR₀, hG0, hGε, -, S, -, hsurj⟩ :=
    exists_tower_deep c (sub_pos.mpr hσ) (Real.exp σ + 1)
  have hrlo0 : 0 < rlo := by linarith
  have hrloσ : Real.log rlo < σ := by linarith
  have hrlo_exp : rlo < Real.exp σ := by
    rw [← Real.log_lt_iff_lt_exp hrlo0]; exact hrloσ
  have hexpR₀ : Real.exp σ < R₀ := by linarith
  refine ⟨rlo, hG0, hrloσ, ?_⟩
  have hsub : annulusSet rlo (Real.exp σ) ⊆ annulusSet rlo R₀ := fun w hw =>
    ⟨hw.1, hw.2.trans hexpR₀⟩
  have hcollar : {z : ℂ | Real.log rlo < greenFunctionDyn c z ∧ greenFunctionDyn c z < σ} =
      S.T '' annulusSet rlo (Real.exp σ) := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      have hσR : σ < Real.log R₀ := by
        rw [Real.lt_log_iff_exp_lt (by linarith)]; exact hexpR₀
      obtain ⟨w, hw, rfl⟩ := hsurj z hz1 (hz2.trans hσR)
      have hlev := S.level w hw
      refine ⟨w, ⟨hw.1, ?_⟩, rfl⟩
      rw [hlev] at hz2
      have hw0 : 0 < ‖w‖ := hrlo0.trans hw.1
      rwa [Real.log_lt_iff_lt_exp hw0] at hz2
    · rintro ⟨w, hw, rfl⟩
      have hw0 : 0 < ‖w‖ := hrlo0.trans hw.1
      show _ ∧ _
      rw [S.level w (hsub hw)]
      exact ⟨Real.log_lt_log hrlo0 hw.1, (Real.log_lt_iff_lt_exp hw0).mpr hw.2⟩
  rw [hcollar]
  exact (isConnected_annulus hrlo0 hrlo_exp).isPreconnected.image _
    (S.an.continuousOn.mono hsub)

/-- A point of the far field lies above every level. -/
theorem exists_green_gt (c : ℂ) (σ : ℝ) : ∃ z : ℂ, σ < greenFunctionDyn c z := by
  refine ⟨((max (‖c‖ + 3) (Real.exp (σ + 2)) + 1 : ℝ) : ℂ), green_far_gt c σ _ ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

/-- **The basin part of a sublevel set above the critical level is connected.** -/
theorem isPreconnected_green_band (c : ℂ) {σ : ℝ} (hσ : greenFunctionDyn c 0 < σ) :
    IsPreconnected {z : ℂ | 0 < greenFunctionDyn c z ∧ greenFunctionDyn c z < σ} := by
  obtain ⟨r, hr0, hrσ, hC⟩ := exists_green_collar c hσ
  have hcont := continuous_greenFunctionDyn c
  have hbasin : (filledJulia c)ᶜ = {z : ℂ | 0 < greenFunctionDyn c z} := by
    ext z
    simp only [mem_compl_iff, mem_setOf_eq]
    rw [← greenFunctionDyn_eq_zero_iff]
    exact ⟨fun h => lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (Ne.symm h), fun h => h.ne'⟩
  have hr : 0 < Real.log r := lt_of_le_of_lt (greenFunctionDyn_nonneg c 0) hr0
  refine isPreconnected_of_collar (isPreconnected_compl_filledJulia c)
    ((isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const))
    (fun z hz => by rw [hbasin]; exact hz.1) ?_ hC (fun z hz => ⟨hr.trans hz.1, hz.2⟩) ?_
  · obtain ⟨z, hz⟩ := exists_green_gt c σ
    refine ⟨z, ?_, fun h => lt_asymm h.2 hz⟩
    rw [hbasin]
    exact lt_of_le_of_lt (greenFunctionDyn_nonneg c 0) (hσ.trans hz)
  · intro y hyX hy
    rw [hbasin] at hyX
    have hsub : {z : ℂ | 0 < greenFunctionDyn c z ∧ greenFunctionDyn c z < σ} \
        {z : ℂ | Real.log r < greenFunctionDyn c z ∧ greenFunctionDyn c z < σ} ⊆
        {z : ℂ | greenFunctionDyn c z ≤ Real.log r} := by
      rintro z ⟨hz1, hz2⟩
      by_contra h
      exact hz2 ⟨lt_of_not_ge h, hz1.2⟩
    have := closure_minimal hsub (isClosed_le hcont continuous_const) hy
    exact ⟨hyX, lt_of_le_of_lt this hrσ⟩

/-! ### Winding of the image of a path from `z` to `-z` -/

/-- `exp ∫₀¹ γ'/γ = γ 1 / γ 0` for a nonvanishing `C¹` path. -/
theorem exp_integral_logDeriv_path {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hne : ∀ t, γ t ≠ 0) :
    Complex.exp (∫ t in (0:ℝ)..1, deriv γ t / γ t) = γ 1 / γ 0 := by
  have hcont : Continuous fun t => deriv γ t / γ t :=
    (hγ.continuous_deriv le_rfl).div hγ.continuous hne
  set E : ℝ → ℂ := fun u => ∫ t in (0:ℝ)..u, deriv γ t / γ t with hEdef
  set H : ℝ → ℂ := fun u => γ u * Complex.exp (-E u) with hHdef
  have hH : ∀ u, HasDerivAt H 0 u := by
    intro u
    have hγd : HasDerivAt γ (deriv γ u) u := (hγ.differentiable one_ne_zero u).hasDerivAt
    have hEd : HasDerivAt E (deriv γ u / γ u) u := (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
    refine (hγd.mul hEd.neg.cexp).congr_deriv ?_
    field_simp [hne u]
    ring
  have hconst : H 1 = H 0 := is_const_of_deriv_eq_zero
    (fun u => (hH u).differentiableAt) (fun u => (hH u).deriv) 1 0
  simp only [hHdef, hEdef, intervalIntegral.integral_same, neg_zero, Complex.exp_zero,
    mul_one] at hconst
  rw [eq_div_iff (hne 0), ← hconst, mul_comm, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

/-- **No path from `z` to `-z` below the critical value.**  If `γ` is a `C¹` path from `z` to `-z`
with `G_c(f_c ∘ γ) ≤ s < G_c(c)`, then `z = 0` or some `γ t = 0`. -/
theorem false_of_path_neg_below {c z : ℂ} {s : ℝ} (hs : 0 < s) (hcs : s < greenFunctionDyn c c)
    (p : PlanarPath z (-z)) (hne : ∀ t, p.γ t ≠ 0)
    (hlev : ∀ t, greenFunctionDyn c (quadratic c (p.γ t)) ≤ s) : False := by
  set T : ℝ := 2 * Real.pi with hTdef
  have hT : 0 < T := by positivity
  have hpd : ∀ u, HasDerivAt p.γ (deriv p.γ u) u := fun u =>
    (p.smooth.differentiable one_ne_zero u).hasDerivAt
  have hdcont : Continuous (deriv p.γ) := p.smooth.continuous_deriv le_rfl
  have hqc : Continuous (quadratic c) := by unfold quadratic; fun_prop
  let ℓ : C1Loop :=
    { γ := fun θ => quadratic c (p.γ (θ / T))
      γ' := fun θ => 2 * p.γ (θ / T) * (T⁻¹ • deriv p.γ (θ / T))
      cont := hqc.comp (p.smooth.continuous.comp (continuous_id.div_const T))
      cont' := by
        have h1 : Continuous fun θ : ℝ => p.γ (θ / T) :=
          p.smooth.continuous.comp (continuous_id.div_const T)
        have h2 : Continuous fun θ : ℝ => deriv p.γ (θ / T) :=
          hdcont.comp (continuous_id.div_const T)
        exact (continuous_const.mul h1).mul (h2.const_smul T⁻¹)
      deriv := by
        intro θ _
        have h1 : HasDerivAt (fun θ : ℝ => θ / T) T⁻¹ θ := by
          simpa [div_eq_mul_inv] using (hasDerivAt_id θ).mul_const T⁻¹
        have h2 := (hpd (θ / T)).scomp θ h1
        have h3 : HasDerivAt (fun w : ℂ => quadratic c w) (2 * p.γ (θ / T)) (p.γ (θ / T)) := by
          unfold quadratic
          simpa using ((hasDerivAt_id (p.γ (θ / T))).pow 2).add_const c
        exact h3.comp θ h2
      closed := by
        change quadratic c (p.γ (T / T)) = quadratic c (p.γ (0 / T))
        rw [div_self hT.ne', zero_div, p.apply_one, p.apply_zero]
        unfold quadratic
        ring }
  have hwind := windInt_eq_zero_of_level_lt c ℓ hs (fun θ => hlev (θ / T)) hcs
  -- the winding integral is twice `∫₀¹ γ'/γ`
  have hint : windInt ℓ c = 2 * ∫ u in (0:ℝ)..1, deriv p.γ u / p.γ u := by
    have hpt : ∀ θ, (ℓ.γ θ - c)⁻¹ * ℓ.γ' θ =
        T⁻¹ * (2 * (deriv p.γ (θ / T) / p.γ (θ / T))) := by
      intro θ
      change (quadratic c (p.γ (θ / T)) - c)⁻¹ * (2 * p.γ (θ / T) * (T⁻¹ • deriv p.γ (θ / T))) = _
      unfold quadratic
      rw [Complex.real_smul]
      push_cast
      field_simp [hne (θ / T)]
      ring
    rw [windInt, intervalIntegral.integral_congr (fun θ _ => hpt θ),
      intervalIntegral.integral_const_mul]
    have hsub := intervalIntegral.integral_comp_div
      (fun u => 2 * (deriv p.γ u / p.γ u)) (a := 0) (b := T) hT.ne'
    rw [hsub, zero_div, div_self hT.ne', intervalIntegral.integral_const_mul, real_smul]
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    push_cast
    field_simp
  rw [hint] at hwind
  have hI : ∫ u in (0:ℝ)..1, deriv p.γ u / p.γ u = 0 := by
    have := hwind; simpa using this
  have hexp := exp_integral_logDeriv_path p.smooth hne
  rw [hI, Complex.exp_zero, p.apply_one, p.apply_zero] at hexp
  have hz : z ≠ 0 := by have := hne 0; rwa [p.apply_zero] at this
  have : (-z) / z = -1 := by field_simp
  rw [this] at hexp
  norm_num at hexp

/-! ### The inverse branch over `D = {G_c < s}` -/

/-- Closed Green sublevel sets are compact. -/
theorem isCompact_green_sublevel (c : ℂ) (σ : ℝ) :
    IsCompact {z : ℂ | greenFunctionDyn c z ≤ σ} := by
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_greenFunctionDyn c) continuous_const)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨max (‖c‖ + 3) (Real.exp (σ + 2)), fun z hz => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact absurd hz (not_le.mpr (green_far_gt c σ z (lt_of_not_ge h)))

/-- The level `s = 3G_c(0)/2` of the base sublevel set, strictly between `G_c(0)` and `G_c(c)`. -/
noncomputable def branchLevel (c : ℂ) : ℝ := 3 / 2 * greenFunctionDyn c 0

/-- The base sublevel set `D = {G_c < s}`. -/
def branchDomain (c : ℂ) : Set ℂ := {z | greenFunctionDyn c z < branchLevel c}

theorem greenFunctionDyn_zero_pos {c : ℂ} (hc : c ∉ mandelbrot) : 0 < greenFunctionDyn c 0 :=
  lt_of_le_of_ne (greenFunctionDyn_nonneg c 0)
    (fun h => hc ((greenFunctionDyn_eq_zero_iff c 0).mp h.symm))

theorem isOpen_branchDomain (c : ℂ) : IsOpen (branchDomain c) :=
  isOpen_lt (continuous_greenFunctionDyn c) continuous_const

theorem filledJulia_subset_branchDomain {c : ℂ} (hc : c ∉ mandelbrot) :
    filledJulia c ⊆ branchDomain c := fun z hz => by
  change greenFunctionDyn c z < branchLevel c
  rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz, branchLevel]
  have := greenFunctionDyn_zero_pos hc
  positivity

theorem isPreconnected_branchDomain {c : ℂ} (hc : c ∉ mandelbrot) :
    IsPreconnected (branchDomain c) :=
  (isConnected_green_sublevel c
    (by rw [branchLevel]; linarith [greenFunctionDyn_zero_pos hc])).isPreconnected

theorem isPreconnected_branchDomain_diff {c : ℂ} (hc : c ∉ mandelbrot) :
    IsPreconnected (branchDomain c \ filledJulia c) := by
  have h := isPreconnected_green_band c
    (σ := branchLevel c) (by rw [branchLevel]; linarith [greenFunctionDyn_zero_pos hc])
  convert h using 1
  ext z
  simp only [branchDomain, Set.mem_sdiff, mem_setOf_eq]
  rw [← greenFunctionDyn_eq_zero_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (Ne.symm h2), h1⟩,
    fun ⟨h1, h2⟩ => ⟨h2, h1.ne'⟩⟩

/-- **The inverse branch.**  For `c ∉ M` there is a holomorphic `g` on `D = {G_c < s}` with
`f_c ∘ g = id`, and every `f_c`-preimage of a point of `D` is `± g`. -/
theorem exists_inverse_branch {c : ℂ} (hc : c ∉ mandelbrot) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (branchDomain c) ∧
      (∀ y ∈ branchDomain c, quadratic c (g y) = y) ∧
      ∀ z, quadratic c z ∈ branchDomain c → z = g (quadratic c z) ∨ z = -g (quadratic c z) := by
  classical
  set t₀ := greenFunctionDyn c 0 with ht₀def
  have ht₀ : 0 < t₀ := greenFunctionDyn_zero_pos hc
  set s := branchLevel c with hsdef
  have hs : s = 3 / 2 * t₀ := rfl
  set D := branchDomain c with hDdef
  set D₁ : Set ℂ := {z | greenFunctionDyn c z < s / 2} with hD₁def
  have hcont := continuous_greenFunctionDyn c
  have hD₁o : IsOpen D₁ := isOpen_lt hcont continuous_const
  have hpre : ∀ z, quadratic c z ∈ D ↔ z ∈ D₁ := by
    intro z
    change greenFunctionDyn c (quadratic c z) < s ↔ greenFunctionDyn c z < s / 2
    rw [greenFunctionDyn_quadratic]
    constructor <;> intro h <;> linarith
  have h0D₁ : (0:ℂ) ∉ D₁ := by
    change ¬ greenFunctionDyn c 0 < s / 2
    rw [hs]; linarith
  obtain ⟨z₀, hz₀⟩ := nonempty_filledJulia c
  have hz₀D₁ : z₀ ∈ D₁ := (hpre z₀).mp
    (filledJulia_subset_branchDomain hc ((quadratic_mem_filledJulia_iff c z₀).mpr hz₀))
  set E := connectedComponentIn D₁ z₀ with hEdef
  have hEo : IsOpen E := hD₁o.connectedComponentIn
  have hED₁ : E ⊆ D₁ := connectedComponentIn_subset _ _
  -- no antipodal pair in `E`
  have hanti : ∀ z ∈ E, -z ∉ E := by
    intro z hz hnz
    obtain ⟨p, hp⟩ := exists_planarPath_of_isPreconnected hEo isPreconnected_connectedComponentIn
      hz hnz
    refine false_of_path_neg_below (c := c) (s := s) (by rw [hs]; positivity) ?_ p
      (fun t h0 => h0D₁ (h0 ▸ hED₁ (hp t))) (fun t => ?_)
    · have hq : quadratic c 0 = c := by simp [quadratic]
      have h := greenFunctionDyn_quadratic c 0
      rw [hq] at h
      rw [h, hs]; linarith
    · have h := hED₁ (hp t)
      change greenFunctionDyn c (p.γ t) < s / 2 at h
      rw [greenFunctionDyn_quadratic]
      linarith
  have hinj : InjOn (quadratic c) E := by
    intro z hz z' hz' h
    unfold quadratic at h
    have h2 : (z' - z) * (z' + z) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exact absurd (show -z ∈ E by rw [show -z = z' by linear_combination -h3]; exact hz')
        (hanti z hz)
  -- `f_c` maps `E` onto `D`
  have hfE_D : quadratic c '' E ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩; exact (hpre z).mpr (hED₁ hz)
  have hfEo : IsOpen (quadratic c '' E) := isOpenMap_quadratic c E hEo
  have hclE : IsCompact (closure E) := (isCompact_green_sublevel c (s / 2)).of_isClosed_subset
    isClosed_closure (closure_minimal
      (fun z hz => le_of_lt (show greenFunctionDyn c z < s / 2 from hED₁ hz))
      (isClosed_le hcont continuous_const))
  have hfEcl : ∀ y ∈ D, y ∈ closure (quadratic c '' E) → y ∈ quadratic c '' E := by
    intro y hyD hy
    have hsub : closure (quadratic c '' E) ⊆ quadratic c '' closure E :=
      closure_minimal (image_mono subset_closure)
        ((hclE.image (show Continuous (quadratic c) by unfold quadratic; fun_prop)).isClosed)
    obtain ⟨e, he, rfl⟩ := hsub hy
    exact ⟨e, mem_connectedComponentIn_of_mem_closure_of_isOpen hD₁o he ((hpre e).mp hyD), rfl⟩
  have hfE : quadratic c '' E = D := by
    refine Subset.antisymm hfE_D ?_
    have hsub : D ⊆ quadratic c '' E ∪ (closure (quadratic c '' E))ᶜ := fun y hy => by
      by_cases h : y ∈ closure (quadratic c '' E)
      · exact Or.inl (hfEcl y hy h)
      · exact Or.inr h
    have hdisj : Disjoint (quadratic c '' E) (closure (quadratic c '' E))ᶜ :=
      (disjoint_compl_right (a := closure (quadratic c '' E))).mono_left subset_closure
    exact (isPreconnected_branchDomain hc).subset_left_of_subset_union hfEo
      isClosed_closure.isOpen_compl hdisj hsub
      ⟨quadratic c z₀, hfE_D ⟨z₀, mem_connectedComponentIn hz₀D₁, rfl⟩,
        ⟨z₀, mem_connectedComponentIn hz₀D₁, rfl⟩⟩
  -- the inverse
  set g := Function.invFunOn (quadratic c) E with hgdef
  have hgE : ∀ y ∈ D, g y ∈ E ∧ quadratic c (g y) = y := fun y hy =>
    Function.invFunOn_pos (by rw [← hfE] at hy; exact hy)
  have hgf : ∀ z ∈ E, g (quadratic c z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hgcont : ∀ y ∈ D, ContinuousAt g y := by
    intro y hy
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨r, hr, hrE⟩ := Metric.isOpen_iff.mp hEo (g y) (hgE y hy).1
    have hmem : quadratic c '' ball (g y) (min ε r) ∈ 𝓝 y := by
      apply (isOpenMap_quadratic c _ isOpen_ball).mem_nhds
      exact ⟨g y, mem_ball_self (lt_min hε hr), (hgE y hy).2⟩
    filter_upwards [hmem] with y' hy'
    obtain ⟨e, he, rfl⟩ := hy'
    have heE : e ∈ E := hrE (ball_subset_ball (min_le_right _ _) he)
    rw [hgf e heE]
    exact lt_of_lt_of_le (mem_ball.mp he) (min_le_left _ _)
  refine ⟨g, fun y hy => ?_, fun y hy => (hgE y hy).2, fun z hz => ?_⟩
  · have hgy0 : g y ≠ 0 := fun h => h0D₁ (h ▸ hED₁ (hgE y hy).1)
    have hfd : HasDerivAt (quadratic c) (2 * g y) (g y) := by
      unfold quadratic
      simpa using ((hasDerivAt_id (g y)).pow 2).add_const c
    have hev : ∀ᶠ y' in 𝓝 y, quadratic c (g y') = y' := by
      filter_upwards [(isOpen_branchDomain c).mem_nhds hy] with y' hy' using (hgE y' hy').2
    exact (HasDerivAt.of_local_left_inverse (hgcont y hy) hfd (mul_ne_zero two_ne_zero hgy0)
      hev).differentiableAt.differentiableWithinAt
  · set w := g (quadratic c z) with hwdef
    have h1 : w ^ 2 + c = z ^ 2 + c := (hgE _ hz).2
    have h2 : (z - w) * (z + w) = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (sub_eq_zero.mp h3)
    · exact Or.inr (by linear_combination h3)

end Bottcher
