/-
# Böttcher tower — the Green-modulus natural boundary (dendrite case)

Assembling the natural-boundary engine (`NaturalBoundary.no_unit_min_of_analytic`) with the Green's
function `G_c = greenFunctionDyn`: **no analytic continuation of `φ_c` across a Julia point can
preserve the Böttcher modulus `‖φ_c‖ = exp(G_c)`.**

The reason is sharp and uses only `G_c ≥ 0` everywhere (`greenFunctionDyn_nonneg`) and `G_c = 0` on
`K_c` (`greenFunctionDyn_eq_zero_iff`): a modulus-preserving continuation `g` would have
`‖g‖ = exp(G_c) ≥ 1` on the whole ball, `‖g z₀‖ = exp(0) = 1` at the Julia point, yet `‖g‖ > 1` on the
basin side — exactly the configuration the minimum principle forbids. For an **empty-interior
(dendrite) Julia set** every continuation is forced to preserve the modulus (the basin is dense, and
`G_c` is continuous by `GreenContinuity`), so this is the full natural boundary there.

New file (hRigid connected lane); consumes `NaturalBoundary` + `GreenContinuity`.
-/
import GaloisForLFunctions.Bottcher.NaturalBoundary
import GaloisForLFunctions.Bottcher.GreenContinuity

open Complex Metric Topology Set Filter

namespace Bottcher

/-- **Green-modulus natural boundary.** No nonvanishing analytic `g` on a ball about a filled-Julia
point `z₀` can satisfy `‖g‖ = exp(G_c)` throughout while the ball meets the basin. Instantiated with
`g` = a hypothetical continuation of `φ_c` across `z₀ ∈ J_c` (which has `‖φ_c‖ = exp(G_c)` on the
basin, extended by continuity), this is the Julia natural boundary for any modulus-preserving
continuation — in particular the whole dendrite case. -/
theorem no_green_modulus_continuation {c z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r))
    (hz₀ : z₀ ∈ filledJulia c)
    (hmod : ∀ z ∈ ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c) :
    False := by
  refine no_unit_min_of_analytic hr hgan (fun z hz => ?_) (fun z hz => ?_) ?_ ?_
  · -- g ≠ 0
    refine norm_pos_iff.mp ?_
    rw [hmod z hz]; exact Real.exp_pos _
  · -- ‖g‖ ≥ 1  (since G_c ≥ 0)
    rw [hmod z hz]
    exact Real.one_le_exp (greenFunctionDyn_nonneg c z)
  · -- ‖g z₀‖ = 1  (since G_c z₀ = 0 on K_c)
    rw [hmod z₀ (mem_ball_self hr), (greenFunctionDyn_eq_zero_iff c z₀).mpr hz₀, Real.exp_zero]
  · -- ‖g‖ > 1 somewhere (basin point: G_c > 0)
    obtain ⟨z, hz, hzK⟩ := hbasin
    refine ⟨z, hz, ?_⟩
    have hgpos : 0 < greenFunctionDyn c z := by
      unfold greenFunctionDyn; rw [if_neg hzK]; exact greenLimit_pos_basin hzK
    rw [hmod z hz]
    exact Real.one_lt_exp_iff.mpr hgpos

/-- **Green-modulus natural boundary, dense form (uses Green continuity, D1).** It suffices that the
continuation preserves `‖φ_c‖ = exp(G_c)` only on the **basin part** of the ball, provided the basin
is dense there (empty-interior / dendrite condition). The modulus identity then extends to the whole
ball because both `‖g‖` and `exp(G_c)` are continuous (`continuous_greenFunctionDyn`), reducing to
`no_green_modulus_continuation`. This is the realistic dendrite natural boundary: a continuation only
sees the basin directly, yet is still ruled out. -/
theorem no_green_modulus_continuation_dense {c z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r)) (hz₀ : z₀ ∈ filledJulia c)
    (hdense : ball z₀ r ⊆ closure (ball z₀ r ∩ (filledJulia c)ᶜ))
    (hmod : ∀ z ∈ ball z₀ r, z ∉ filledJulia c → ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c) :
    False := by
  set s : Set ℂ := ball z₀ r ∩ (filledJulia c)ᶜ with hs
  have hsub : s ⊆ ball z₀ r := inter_subset_left
  have hcN : ContinuousOn (fun w => ‖g w‖) (ball z₀ r) := hgan.continuousOn.norm
  have hcE : ContinuousOn (fun w => Real.exp (greenFunctionDyn c w)) (ball z₀ r) :=
    (Real.continuous_exp.comp (continuous_greenFunctionDyn c)).continuousOn
  have hmod_all : ∀ z ∈ ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz
    have hzcl : z ∈ closure s := hdense hz
    have hne : (𝓝[s] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzcl
    have hf : Tendsto (fun w => ‖g w‖) (𝓝[s] z) (𝓝 (‖g z‖)) := (hcN z hz).mono hsub
    have hh0 : Tendsto (fun w => Real.exp (greenFunctionDyn c w)) (𝓝[s] z)
        (𝓝 (Real.exp (greenFunctionDyn c z))) := (hcE z hz).mono hsub
    have heqs : ∀ w ∈ s, Real.exp (greenFunctionDyn c w) = ‖g w‖ :=
      fun w hw => (hmod w hw.1 hw.2).symm
    have hh : Tendsto (fun w => ‖g w‖) (𝓝[s] z) (𝓝 (Real.exp (greenFunctionDyn c z))) :=
      hh0.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqs)
    exact tendsto_nhds_unique hf hh
  exact no_green_modulus_continuation hr hgan hz₀ hmod_all hbasin

/-- **General topology: complement of a nowhere-dense closed set is dense.** If an open `U` meets the
interior of `K` nowhere (`U ∩ interior K = ∅`), then `U ⊆ closure(U ∖ K)`. -/
theorem subset_closure_inter_compl {U K : Set ℂ} (hUo : IsOpen U)
    (hempty : U ∩ interior K = ∅) : U ⊆ closure (U ∩ Kᶜ) := by
  intro z hz
  rw [_root_.mem_closure_iff]
  intro V hVo hzV
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hsub : V ∩ U ⊆ K := by
    intro w hw
    by_contra hwK
    have hmem : w ∈ V ∩ (U ∩ Kᶜ) := ⟨hw.1, hw.2, hwK⟩
    rw [hcon] at hmem
    exact (Set.mem_empty_iff_false w).mp hmem
  have hint : V ∩ U ⊆ interior K := interior_maximal hsub (hVo.inter hUo)
  have hzmem : z ∈ U ∩ interior K := ⟨hz, hint ⟨hzV, hz⟩⟩
  rw [hempty] at hzmem
  exact hzmem

/-- **Density of the basin** under the empty-interior (dendrite) condition: if `K_c` has empty
interior in `ball z₀ r`, the basin `Ω_c` is dense there — discharging the density hypothesis of
`no_green_modulus_continuation_dense`. -/
theorem density_basin_of_empty_interior {c z₀ : ℂ} {r : ℝ}
    (hempty : ball z₀ r ∩ interior (filledJulia c) = ∅) :
    ball z₀ r ⊆ closure (ball z₀ r ∩ (filledJulia c)ᶜ) :=
  subset_closure_inter_compl isOpen_ball hempty

/-- A point outside the interior of `K_c` has nontrivial basin-side neighbourhood filter. -/
theorem nhdsWithin_compl_filledJulia_neBot_of_not_mem_interior {c z₀ : ℂ}
    (hz₀int : z₀ ∉ interior (filledJulia c)) :
    (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (by
    rw [closure_compl]
    exact hz₀int)

/-- Every ball around a non-interior point of `K_c` contains a basin point. -/
theorem exists_mem_ball_compl_filledJulia_of_not_mem_interior {c z₀ : ℂ} {r : ℝ}
    (hz₀int : z₀ ∉ interior (filledJulia c)) (hr : 0 < r) :
    ∃ z, z ∈ ball z₀ r ∧ z ∈ (filledJulia c)ᶜ := by
  obtain ⟨z, hzcomp, hzball⟩ :=
    (nhdsWithin_compl_filledJulia_neBot_of_not_mem_interior hz₀int).nonempty_of_mem
      (inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hr))
  exact ⟨z, hzball, hzcomp⟩

/-- Empty interior makes every filled-Julia point basin-accumulated. -/
theorem nhdsWithin_compl_filledJulia_neBot_of_mem_emptyInterior {c z₀ : ℂ}
    (hempty : interior (filledJulia c) = ∅) (_hz₀ : z₀ ∈ filledJulia c) :
    (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
  nhdsWithin_compl_filledJulia_neBot_of_not_mem_interior (by
    intro hzint
    rw [hempty] at hzint
    exact hzint)

/-- Empty interior makes every ball around a filled-Julia point contain a basin point. -/
theorem exists_mem_ball_compl_filledJulia_of_mem_emptyInterior {c z₀ : ℂ} {r : ℝ}
    (hempty : interior (filledJulia c) = ∅) (_hz₀ : z₀ ∈ filledJulia c) (hr : 0 < r) :
    ∃ z, z ∈ ball z₀ r ∧ z ∈ (filledJulia c)ᶜ :=
  exists_mem_ball_compl_filledJulia_of_not_mem_interior
    (by
      intro hzint
      rw [hempty] at hzint
      exact hzint)
    hr

/-- Model one-sided local basin: an open Euclidean ball cut by the right half-plane is
preconnected. This is the point-set topology shape needed by local tip arguments. -/
theorem isPreconnected_ball_inter_rightHalfplane (z₀ : ℂ) {ρ : ℝ} :
    IsPreconnected (Metric.ball z₀ ρ ∩ {z | z₀.re < z.re}) := by
  exact ((convex_ball z₀ ρ).inter (convex_halfSpace_re_gt z₀.re)).isPreconnected

/-- The open half-plane strictly to the right of a real-part maximizer of `filledJulia c` lies in
the basin. -/
theorem rightmost_rightHalfplane_subset_compl_filledJulia {c z₀ : ℂ}
    (hz₀max : ∀ w ∈ filledJulia c, w.re ≤ z₀.re) :
    {z : ℂ | z₀.re < z.re} ⊆ (filledJulia c)ᶜ := by
  intro z hz hzK
  exact (not_lt_of_ge (hz₀max z hzK)) hz

/-- The local right-hand sector at a real-part maximizer is contained in the basin. -/
theorem rightmost_ball_inter_rightHalfplane_subset_compl_filledJulia {c z₀ : ℂ} {ρ : ℝ}
    (hz₀max : ∀ w ∈ filledJulia c, w.re ≤ z₀.re) :
    Metric.ball z₀ ρ ∩ {z : ℂ | z₀.re < z.re} ⊆
      Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ := by
  intro z hz
  exact ⟨hz.1, rightmost_rightHalfplane_subset_compl_filledJulia hz₀max hz.2⟩

/-- A real-part maximizer supplies a preconnected local sector lying in the basin. -/
theorem rightmost_ball_inter_rightHalfplane_preconnected_subset_compl_filledJulia {c z₀ : ℂ}
    {ρ : ℝ} (hz₀max : ∀ w ∈ filledJulia c, w.re ≤ z₀.re) :
    IsPreconnected (Metric.ball z₀ ρ ∩ {z : ℂ | z₀.re < z.re}) ∧
      Metric.ball z₀ ρ ∩ {z : ℂ | z₀.re < z.re} ⊆
        Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ := by
  exact ⟨isPreconnected_ball_inter_rightHalfplane z₀,
    rightmost_ball_inter_rightHalfplane_subset_compl_filledJulia hz₀max⟩

/-- A local one-sided complement model supplies the `htip`-style preconnectedness hypothesis at
every scale. The geometric task is to prove such a local model for selected filled-Julia tip
points. -/
theorem local_tip_preconnected_of_eq_rightHalfplane {K : Set ℂ} {z₀ : ℂ}
    (hlocal : ∀ ρ, 0 < ρ →
      Metric.ball z₀ ρ ∩ Kᶜ = Metric.ball z₀ ρ ∩ {z | z₀.re < z.re}) :
    ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ Kᶜ) := by
  intro ρ hρ
  rw [hlocal ρ hρ]
  exact isPreconnected_ball_inter_rightHalfplane z₀

/-- Model endpoint slit basin: a ball centered at the tip, with only the translated negative real
ray removed, is preconnected. -/
theorem isPreconnected_ball_inter_translated_slitPlane (z₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane}) := by
  let w : ℂ := ((ρ / 2 : ℝ) : ℂ)
  let center : ℂ := z₀ + w
  have hw_pos : 0 < ρ / 2 := half_pos hρ
  have hw_slit : w ∈ Complex.slitPlane := by
    dsimp [w]
    exact Complex.ofReal_mem_slitPlane.2 hw_pos
  have hcenter_ball : center ∈ Metric.ball z₀ ρ := by
    dsimp [center, w]
    rw [Metric.mem_ball]
    simp only [dist_eq_norm, add_sub_cancel_left]
    have hnorm : ‖((ρ / 2 : ℝ) : ℂ)‖ = ρ / 2 :=
      Complex.norm_of_nonneg (le_of_lt hw_pos)
    rw [hnorm]
    exact half_lt_self hρ
  have hcenter_slit : center - z₀ ∈ Complex.slitPlane := by
    dsimp [center]
    simpa using hw_slit
  have hstar_ball : StarConvex ℝ center (Metric.ball z₀ ρ) :=
    (convex_ball z₀ ρ).starConvex hcenter_ball
  have hstar_slit : StarConvex ℝ center {z | z - z₀ ∈ Complex.slitPlane} := by
    intro y hy a b ha hb hab
    have h := (Complex.starConvex_ofReal_slitPlane hw_pos) hy ha hb hab
    have heq : (a • center + b • y) - z₀ = a • w + b • (y - z₀) := by
      have haeq : a = 1 - b := by linarith
      rw [haeq]
      dsimp [center]
      norm_num
      ring_nf
    change (a • center + b • y) - z₀ ∈ Complex.slitPlane
    rw [heq]
    simpa [w] using h
  exact
    (((hstar_ball.inter hstar_slit).isPathConnected
      ⟨hcenter_ball, hcenter_slit⟩).isConnected).isPreconnected

/-- A translated real line has empty interior. -/
theorem interior_translated_realLine_eq_empty (z₀ : ℂ) :
    interior {z : ℂ | (z - z₀).im = 0} = ∅ := by
  have hline : {z : ℂ | (z - z₀).im = 0} = {z : ℂ | z.im = z₀.im} := by
    ext z
    constructor <;> intro h <;> simp [sub_im] at h ⊢ <;> linarith
  rw [hline]
  have heq :
      {z : ℂ | z.im = z₀.im} =
        {z : ℂ | z.im ≤ z₀.im} ∩ {z : ℂ | z₀.im ≤ z.im} := by
    ext z
    constructor
    · intro hz
      exact ⟨le_of_eq hz, ge_of_eq hz⟩
    · intro hz
      exact le_antisymm hz.1 hz.2
  rw [heq, interior_inter]
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  simp at hz
  linarith

/-- The translated slit sector is dense in every ball centered at the tip. -/
theorem ball_subset_closure_ball_inter_translated_slitPlane (z₀ : ℂ) {ρ : ℝ} :
    Metric.ball z₀ ρ ⊆
      closure (Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane}) := by
  classical
  let K : Set ℂ := {z | z - z₀ ∈ (Complex.slitPlane)ᶜ}
  have hKsubLine : K ⊆ {z | (z - z₀).im = 0} := by
    intro z hz
    simp [K, Complex.mem_slitPlane_iff] at hz
    exact hz.2
  have hemptyK : interior K = ∅ := by
    have hIntSub : interior K ⊆ interior {z : ℂ | (z - z₀).im = 0} :=
      interior_mono hKsubLine
    rw [interior_translated_realLine_eq_empty z₀] at hIntSub
    exact eq_empty_of_subset_empty hIntSub
  have hcl : Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ Kᶜ) := by
    apply subset_closure_inter_compl (U := Metric.ball z₀ ρ) (K := K) Metric.isOpen_ball
    rw [hemptyK, inter_empty]
  have hset :
      Metric.ball z₀ ρ ∩ Kᶜ =
        Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} := by
    ext y
    constructor
    · intro hy
      refine ⟨hy.1, ?_⟩
      by_contra hys
      exact hy.2 (by simpa [K] using hys)
    · intro hy
      refine ⟨hy.1, ?_⟩
      intro hyK
      exact hyK hy.2
  intro z hz
  rw [← hset]
  exact hcl hz

/-- If a local complement is exactly the translated slit-plane model at every scale, then it
supplies the `htip`-style preconnectedness hypothesis. -/
theorem local_tip_preconnected_of_eq_translated_slitPlane {K : Set ℂ} {z₀ : ℂ}
    (hlocal : ∀ ρ, 0 < ρ →
      Metric.ball z₀ ρ ∩ Kᶜ = Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane}) :
    ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ Kᶜ) := by
  intro ρ hρ
  rw [hlocal ρ hρ]
  exact isPreconnected_ball_inter_translated_slitPlane z₀ hρ

/-- If the translated slit sector lies in the local basin at every scale, then the local basin is
preconnected at every scale. The slit sector is preconnected and dense in the ball, so the full local
basin is sandwiched between a preconnected set and its closure. -/
theorem local_tip_preconnected_of_translated_slitPlane_subset_compl {K : Set ℂ} {z₀ : ℂ}
    (hslit : ∀ ρ, 0 < ρ →
      Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆ Metric.ball z₀ ρ ∩ Kᶜ) :
    ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ Kᶜ) := by
  intro ρ hρ
  exact (isPreconnected_ball_inter_translated_slitPlane z₀ hρ).subset_closure
    (hslit ρ hρ)
    (fun z hz => ball_subset_closure_ball_inter_translated_slitPlane z₀ hz.1)

/-- All-scale translated-slit inclusion is equivalent to putting `K` on the excluded translated
slit ray. This records a useful obstruction: an all-scale slit-sector basin hypothesis is far more
rigid than a genuinely local tip hypothesis. -/
theorem all_scale_translated_slitPlane_subset_compl_iff_subset_nonSlitPlane
    {K : Set ℂ} {z₀ : ℂ} :
    (∀ ρ, 0 < ρ →
      Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
        Metric.ball z₀ ρ ∩ Kᶜ) ↔
    K ⊆ {z | z - z₀ ∉ Complex.slitPlane} := by
  constructor
  · intro h z hzK hzslit
    let ρ : ℝ := dist z z₀ + 1
    have hdist : 0 ≤ dist z z₀ := dist_nonneg
    have hρ : 0 < ρ := by
      dsimp [ρ]
      linarith
    have hzball : z ∈ Metric.ball z₀ ρ := by
      rw [Metric.mem_ball]
      dsimp [ρ]
      rw [dist_comm]
      linarith
    exact (h ρ hρ ⟨hzball, hzslit⟩).2 hzK
  · intro h ρ _hρ z hz
    exact ⟨hz.1, fun hzK => h hzK hz.2⟩

/-- Among points of `K`, the all-scale translated-slit condition can hold at most once. -/
theorem subsingleton_mem_all_scale_translated_slitPlane_subset_compl
    (K : Set ℂ) :
    Set.Subsingleton {z₀ : ℂ | z₀ ∈ K ∧
      ∀ ρ, 0 < ρ →
        Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
          Metric.ball z₀ ρ ∩ Kᶜ} := by
  intro z₀ hz₀ z₁ hz₁
  have h₀ : K ⊆ {z | z - z₀ ∉ Complex.slitPlane} :=
    (all_scale_translated_slitPlane_subset_compl_iff_subset_nonSlitPlane.mp hz₀.2)
  have h₁ : K ⊆ {z | z - z₁ ∉ Complex.slitPlane} :=
    (all_scale_translated_slitPlane_subset_compl_iff_subset_nonSlitPlane.mp hz₁.2)
  have h01 : z₁ - z₀ ∉ Complex.slitPlane := h₀ hz₁.1
  have h10 : z₀ - z₁ ∉ Complex.slitPlane := h₁ hz₀.1
  have h01re : (z₁ - z₀).re ≤ 0 := by
    by_contra h
    exact h01 (Complex.mem_slitPlane_iff.mpr (Or.inl (not_le.mp h)))
  have h10re : (z₀ - z₁).re ≤ 0 := by
    by_contra h
    exact h10 (Complex.mem_slitPlane_iff.mpr (Or.inl (not_le.mp h)))
  have h01im : (z₁ - z₀).im = 0 := by
    by_contra h
    exact h01 (Complex.mem_slitPlane_iff.mpr (Or.inr h))
  apply Complex.ext
  · simp [sub_re] at h01re h10re ⊢
    linarith
  · simp [sub_im] at h01im ⊢
    linarith

/-- The all-scale translated-slit condition is countable on `K` because it is subsingleton. -/
theorem countable_mem_all_scale_translated_slitPlane_subset_compl
    (K : Set ℂ) :
    ({z₀ : ℂ | z₀ ∈ K ∧
      ∀ ρ, 0 < ρ →
        Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
          Metric.ball z₀ ρ ∩ Kᶜ}).Countable :=
  (subsingleton_mem_all_scale_translated_slitPlane_subset_compl K).countable

/-- The filled-Julia frontier points satisfying the all-scale translated-slit basin inclusion are
countable, even after intersecting with an arbitrary local set, off-other condition, and analytic
region. In particular, the corresponding uncountable local-frontier supply hypothesis is impossible
for the all-scale slit-sector model. -/
theorem countable_local_frontier_offOther_all_scale_translated_slitPlane_subset_compl_filledJulia
    (c₁ c₂ : ℂ) (A Ω : Set ℂ) :
    (((((A ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
      {z₀ : ℂ | ∀ ρ, 0 < ρ →
        Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
          Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω)).Countable := by
  exact (countable_mem_all_scale_translated_slitPlane_subset_compl (filledJulia c₁)).mono (by
    intro z hz
    have hzfront : z ∈ frontier (filledJulia c₁) := hz.1.1.1.2
    have hzcl : z ∈ closure (filledJulia c₁) := by
      rw [frontier_eq_closure_inter_closure] at hzfront
      exact hzfront.1
    have hzK : z ∈ filledJulia c₁ := by
      rwa [(isClosed_filledJulia c₁).closure_eq] at hzcl
    exact ⟨hzK, hz.1.2⟩)

private theorem complex_norm_inv_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : ‖u⁻¹‖ = 1 := by
  rw [norm_inv, hu, inv_one]

private theorem complex_ne_zero_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u ≠ 0 := by
  intro h
  rw [h, norm_zero] at hu
  norm_num at hu

private theorem complex_normSq_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) :
    Complex.normSq u = 1 := by
  rw [Complex.normSq_eq_norm_sq, hu]
  norm_num

/-- A rotated translated real line has empty interior. -/
theorem interior_rotated_translated_realLine_eq_empty (u z₀ : ℂ) (hu : ‖u‖ = 1) :
    interior {z : ℂ | (u * (z - z₀)).im = 0} = ∅ := by
  let L : Set ℂ := {z : ℂ | (u * (z - z₀)).im = 0}
  change interior L = ∅
  rw [eq_empty_iff_forall_notMem]
  intro z hzint
  have hzline : z ∈ L := interior_subset hzint
  change (u * (z - z₀)).im = 0 at hzline
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hzint
  obtain ⟨ε, hεpos, hεsub⟩ := hzint
  let v : ℂ := (((ε / 2 : ℝ) : ℂ) * Complex.I) * u⁻¹
  let y : ℂ := z + v
  have hyball : y ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : y - z = v := by
      dsimp [y]
      ring
    rw [hsub]
    dsimp [v]
    rw [norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : 0 ≤ ε / 2), Complex.norm_I,
      complex_norm_inv_of_norm_eq_one hu]
    ring_nf
    linarith
  have hyline : (u * (y - z₀)).im = 0 := hεsub hyball
  have hcalc : (u * (y - z₀)).im = (u * (z - z₀)).im + ε / 2 := by
    dsimp [y, v]
    have hnormSq : Complex.normSq u = 1 := complex_normSq_of_norm_eq_one hu
    have hunit : u.re * u.re + u.im * u.im = 1 := by
      simpa [Complex.normSq_apply] using hnormSq
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    rw [hnormSq]
    nlinarith
  rw [hcalc, hzline] at hyline
  linarith

/-- Rotated model endpoint slit basin: a ball centered at the tip, with a rotated translated ray
removed, is preconnected. -/
theorem isPreconnected_ball_inter_rotated_translated_slitPlane (u z₀ : ℂ) (hu : ‖u‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane}) := by
  let w : ℂ := ((ρ / 2 : ℝ) : ℂ)
  let center : ℂ := z₀ + u⁻¹ * w
  have hune : u ≠ 0 := complex_ne_zero_of_norm_eq_one hu
  have hw_pos : 0 < ρ / 2 := half_pos hρ
  have hw_slit : w ∈ Complex.slitPlane := by
    dsimp [w]
    exact Complex.ofReal_mem_slitPlane.2 hw_pos
  have hcenter_ball : center ∈ Metric.ball z₀ ρ := by
    dsimp [center, w]
    rw [Metric.mem_ball]
    simp only [dist_eq_norm, add_sub_cancel_left]
    rw [norm_mul, complex_norm_inv_of_norm_eq_one hu, one_mul]
    have hnorm : ‖((ρ / 2 : ℝ) : ℂ)‖ = ρ / 2 :=
      Complex.norm_of_nonneg (le_of_lt hw_pos)
    rw [hnorm]
    exact half_lt_self hρ
  have hcenter_slit : u * (center - z₀) ∈ Complex.slitPlane := by
    dsimp [center]
    rw [add_sub_cancel_left]
    rw [← mul_assoc, mul_inv_cancel₀ hune, one_mul]
    exact hw_slit
  have hstar_ball : StarConvex ℝ center (Metric.ball z₀ ρ) :=
    (convex_ball z₀ ρ).starConvex hcenter_ball
  have hstar_slit : StarConvex ℝ center {z | u * (z - z₀) ∈ Complex.slitPlane} := by
    intro y hy a b ha hb hab
    have h := (Complex.starConvex_ofReal_slitPlane hw_pos) hy ha hb hab
    have heq : u * ((a • center + b • y) - z₀) =
        a • w + b • (u * (y - z₀)) := by
      have haeq : a = 1 - b := by
        linarith
      rw [haeq]
      dsimp [center]
      norm_num
      have hinner : (1 - ↑b) * (z₀ + u⁻¹ * w) + ↑b * y - z₀ =
          (1 - ↑b) * (u⁻¹ * w) + ↑b * (y - z₀) := by
        ring_nf
      rw [hinner, mul_add]
      have hterm₁ : u * ((1 - ↑b) * (u⁻¹ * w)) = (1 - ↑b) * w := by
        ring_nf
        have hbterm : u * ↑b * u⁻¹ = ↑b := by
          rw [mul_comm u ↑b, mul_assoc, mul_inv_cancel₀ hune, mul_one]
        rw [hbterm, mul_inv_cancel₀ hune, one_mul]
      have hterm₂ : u * (↑b * (y - z₀)) = ↑b * (u * (y - z₀)) := by
        ring
      rw [hterm₁, hterm₂]
    change u * ((a • center + b • y) - z₀) ∈ Complex.slitPlane
    rw [heq]
    simpa [w] using h
  exact
    (((hstar_ball.inter hstar_slit).isPathConnected
      ⟨hcenter_ball, hcenter_slit⟩).isConnected).isPreconnected

/-- The rotated translated slit sector is dense in every ball centered at the tip. -/
theorem ball_subset_closure_ball_inter_rotated_translated_slitPlane (u z₀ : ℂ) (hu : ‖u‖ = 1)
    {ρ : ℝ} :
    Metric.ball z₀ ρ ⊆
      closure (Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane}) := by
  classical
  let K : Set ℂ := {z | u * (z - z₀) ∈ (Complex.slitPlane)ᶜ}
  have hKsubLine : K ⊆ {z | (u * (z - z₀)).im = 0} := by
    intro z hz
    simp [K, Complex.mem_slitPlane_iff] at hz
    exact hz.2
  have hemptyK : interior K = ∅ := by
    have hIntSub : interior K ⊆ interior {z : ℂ | (u * (z - z₀)).im = 0} :=
      interior_mono hKsubLine
    rw [interior_rotated_translated_realLine_eq_empty u z₀ hu] at hIntSub
    exact eq_empty_of_subset_empty hIntSub
  have hcl : Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ Kᶜ) := by
    apply subset_closure_inter_compl (U := Metric.ball z₀ ρ) (K := K) Metric.isOpen_ball
    rw [hemptyK, inter_empty]
  have hset :
      Metric.ball z₀ ρ ∩ Kᶜ =
        Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
    ext y
    constructor
    · intro hy
      refine ⟨hy.1, ?_⟩
      by_contra hys
      exact hy.2 (by simpa [K] using hys)
    · intro hy
      refine ⟨hy.1, ?_⟩
      intro hyK
      exact hyK hy.2
  intro z hz
  rw [← hset]
  exact hcl hz

/-- If a rotated translated slit sector lies in the local basin at every scale, then the local basin
is preconnected at every scale. -/
theorem local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl {K : Set ℂ}
    {u z₀ : ℂ} (hu : ‖u‖ = 1)
    (hslit : ∀ ρ, 0 < ρ →
      Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
        Metric.ball z₀ ρ ∩ Kᶜ) :
    ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ Kᶜ) := by
  intro ρ hρ
  exact (isPreconnected_ball_inter_rotated_translated_slitPlane u z₀ hu hρ).subset_closure
    (hslit ρ hρ)
    (fun z hz => ball_subset_closure_ball_inter_rotated_translated_slitPlane u z₀ hu hz.1)

/-- Local-radius version of the rotated-slit bridge.  This is the non-global interface: it gives
`htip` only below a prescribed radius, avoiding the all-scale condition that forces a global ray
obstruction. -/
theorem local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le {K : Set ℂ}
    {u z₀ : ℂ} {R : ℝ} (hu : ‖u‖ = 1)
    (hslit : ∀ ρ, 0 < ρ → ρ ≤ R →
      Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
        Metric.ball z₀ ρ ∩ Kᶜ) :
    ∀ ρ, 0 < ρ → ρ ≤ R → IsPreconnected (Metric.ball z₀ ρ ∩ Kᶜ) := by
  intro ρ hρ hρR
  exact (isPreconnected_ball_inter_rotated_translated_slitPlane u z₀ hu hρ).subset_closure
    (hslit ρ hρ hρR)
    (fun z hz => ball_subset_closure_ball_inter_rotated_translated_slitPlane u z₀ hu hz.1)

/-- **Dendrite natural boundary, fully assembled from the empty-interior condition.** For a Julia
point `z₀` where `K_c` has empty interior, no continuation of `φ_c` preserving the Böttcher modulus on
the basin can exist. The only remaining inputs are the empty-interior condition (the dendrite case
hypothesis) and the modulus identity `‖g‖ = exp(G_c)` on the basin part (supplied by `g` = the chain
branch `exp F`, `|exp F| = exp(G_c)`). -/
theorem no_continuation_dendrite {c z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r)) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : ball z₀ r ∩ interior (filledJulia c) = ∅)
    (hmod : ∀ z ∈ ball z₀ r, z ∉ filledJulia c → ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c) :
    False :=
  no_green_modulus_continuation_dense hr hgan hz₀ (density_basin_of_empty_interior hempty) hmod hbasin

end Bottcher
