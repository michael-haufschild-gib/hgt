/-
# Cusp branch of the modular-lambda Montel extraction

This file proves the first boundary alternative for the omitted-values normality proof.  If a
sequence of upper-half-plane lift coordinates escapes uniformly to the cusp `∞`, then the spherical
modular-lambda values converge uniformly to the omitted value `0`.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaInteriorNormal

open Complex Metric Set Filter Topology

namespace Bottcher

noncomputable section

/-- The north pole of the stereographic sphere, i.e. the value representing `∞`. -/
noncomputable def northPole : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 1]

/-- Stereographic projection in the inverse coordinate, continuously extended across `0`.
For `w ≠ 0`, `stereoInvExtended w = stereo w⁻¹`; at `w = 0` it is the north pole. -/
noncomputable def stereoInvExtended (w : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * w.re / (1 + ‖w‖ ^ (2 : ℕ)), -2 * w.im / (1 + ‖w‖ ^ (2 : ℕ)),
    (1 - ‖w‖ ^ (2 : ℕ)) / (1 + ‖w‖ ^ (2 : ℕ))]

@[simp] theorem stereoInvExtended_zero : stereoInvExtended 0 = northPole := by
  ext i
  fin_cases i <;> simp [stereoInvExtended, northPole]

/-- The inverse-coordinate stereographic extension agrees with ordinary stereographic projection
away from the inverse-coordinate origin. -/
theorem stereo_eq_stereoInvExtended_inv {z : ℂ} (hz : z ≠ 0) :
    stereo z = stereoInvExtended z⁻¹ := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  ext i
  fin_cases i
  · simp [stereo, stereoInvExtended, Complex.inv_re, norm_inv, Complex.normSq_eq_norm_sq]
    field_simp [hn]
    ring
  · simp [stereo, stereoInvExtended, Complex.inv_im, norm_inv, Complex.normSq_eq_norm_sq]
    field_simp [hn]
    ring
  · simp [stereo, stereoInvExtended, norm_inv]
    field_simp [hn]
    ring

/-- The inverse-coordinate stereographic extension is continuous. -/
theorem continuous_stereoInvExtended : Continuous stereoInvExtended := by
  have hden : ∀ z : ℂ, (1 : ℝ) + ‖z‖ ^ (2 : ℕ) ≠ 0 := fun z =>
    (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ (2 : ℕ)).ne'
  have hc : Continuous (fun z : ℂ => (1 : ℝ) + ‖z‖ ^ (2 : ℕ)) := by fun_prop
  have hpi : Continuous (fun z : ℂ =>
      (![2 * z.re / (1 + ‖z‖ ^ (2 : ℕ)), -2 * z.im / (1 + ‖z‖ ^ (2 : ℕ)),
        (1 - ‖z‖ ^ (2 : ℕ)) / (1 + ‖z‖ ^ (2 : ℕ))] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Continuous.div (by fun_prop) hc hden
    · exact Continuous.div (by fun_prop) hc hden
    · exact Continuous.div (by fun_prop) hc hden
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp hpi

/-- Uniform convergence to `0` in the inverse coordinate gives uniform spherical convergence to the
north pole, provided the original finite values are eventually nonzero. -/
theorem tendstoUniformlyOn_stereo_of_inv_tendstoUniformlyOn_zero
    {K : Set ℂ} {fseq : ℕ → ℂ → ℂ}
    (hne : ∀ᶠ n in atTop, ∀ z ∈ K, fseq n z ≠ 0)
    (hconv : TendstoUniformlyOn (fun n z => (fseq n z)⁻¹) (fun _z => (0 : ℂ)) atTop K) :
    TendstoUniformlyOn (fun n z => stereo (fseq n z)) (fun _z => northPole) atTop K := by
  have hlim_mem : ∀ z ∈ K, (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    intro z hz
    exact mem_closedBall_self zero_le_one
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, (fseq n z)⁻¹ ∈ closedBall (0 : ℂ) 1 := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv
    filter_upwards [hconv 1 (by norm_num)] with n hn
    intro z hz
    have hdist : dist (0 : ℂ) ((fseq n z)⁻¹) < 1 := hn z hz
    rw [mem_closedBall]
    simpa [dist_comm] using le_of_lt hdist
  have hUC : UniformContinuousOn stereoInvExtended (closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous
      continuous_stereoInvExtended.continuousOn
  have hcomp : TendstoUniformlyOn
      (fun n z => stereoInvExtended ((fseq n z)⁻¹))
      (fun _z => stereoInvExtended (0 : ℂ)) atTop K :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hUC hconv
  have hcomp' : TendstoUniformlyOn
      (fun n z => stereo (fseq n z)) (fun _z => stereoInvExtended (0 : ℂ)) atTop K := by
    refine hcomp.congr ?_
    filter_upwards [hne] with n hn z hz
    exact (stereo_eq_stereoInvExtended_inv (hn z hz)).symm
  simpa using hcomp'

/-- The map `σ ↦ -1/σ` sends the upper half-plane to itself. -/
theorem neg_inv_im_pos {σ : ℂ} (hσ : 0 < σ.im) : 0 < (-1 / σ).im := by
  have hσne : σ ≠ 0 := by
    intro h
    rw [h] at hσ
    simp at hσ
  rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]
  have hden : 0 < Complex.normSq σ := Complex.normSq_pos.mpr hσne
  have hnum : -σ.im < 0 := neg_lt_zero.mpr hσ
  have hquot : -σ.im / Complex.normSq σ < 0 := div_neg_of_neg_of_pos hnum hden
  exact neg_pos.mpr hquot

/-- Uniform escape to the cusp `∞` forces uniform spherical convergence `λ(τₙ) → 0`.

The hypothesis is intentionally stated as a uniform height condition on an arbitrary family `τseq`.
It is the exact form needed after normalising upper-half-plane lifts into a fundamental-domain cusp
sector. -/
theorem tendstoUniformlyOn_stereo_modularLambda_of_im_tendsto_atTop
    {K : Set ℂ} {τseq : ℕ → ℂ → ℂ}
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, M ≤ (τseq n z).im) :
    TendstoUniformlyOn
      (fun n z => stereo (modularLambda (τseq n z)))
      (fun _z => stereo (0 : ℂ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hst := continuous_stereo.continuousAt (x := (0 : ℂ))
  rw [Metric.continuousAt_iff] at hst
  obtain ⟨δ, hδpos, hδ⟩ := hst ε hε
  have hlam_event : ∀ᶠ τ : ℂ in comap Complex.im atTop,
      modularLambda τ ∈ Metric.ball (0 : ℂ) δ :=
    tendsto_modularLambda_atImInfty (Metric.ball_mem_nhds (0 : ℂ) hδpos)
  have hlam : ∀ᶠ τ : ℂ in comap Complex.im atTop, dist (modularLambda τ) (0 : ℂ) < δ := by
    filter_upwards [hlam_event] with τ hτ
    simpa [Metric.mem_ball] using hτ
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hlam
  obtain ⟨M, hM⟩ := hlam
  filter_upwards [hIm M] with n hn
  intro z hz
  have hclose := hδ (x := modularLambda (τseq n z))
    (hM (τseq n z).im (hn z hz) (τseq n z) rfl)
  simpa [dist_comm] using hclose

/-- Disk-coordinate form of the cusp-`∞` branch. -/
theorem tendstoUniformlyOn_stereo_modularDiskTarget_of_cayleyInv_im_tendsto_atTop
    {K : Set ℂ} {gseq : ℕ → ℂ → ℂ}
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, M ≤ (cayleyInv (gseq n z)).im) :
    TendstoUniformlyOn
      (fun n z => stereo (modularLambda (cayleyInv (gseq n z))))
      (fun _z => stereo (0 : ℂ)) atTop K :=
  tendstoUniformlyOn_stereo_modularLambda_of_im_tendsto_atTop hIm

/-- Uniform escape to the cusp `0`, written as `-1 / σ → 0`, forces uniform spherical convergence
`λ(-1/σₙ) → 1`. -/
theorem tendstoUniformlyOn_stereo_modularLambda_neg_inv_of_im_tendsto_atTop
    {K : Set ℂ} {σseq : ℕ → ℂ → ℂ}
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, M ≤ (σseq n z).im) :
    TendstoUniformlyOn
      (fun n z => stereo (modularLambda (-1 / σseq n z)))
      (fun _z => stereo (1 : ℂ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hst := continuous_stereo.continuousAt (x := (1 : ℂ))
  rw [Metric.continuousAt_iff] at hst
  obtain ⟨δ, hδpos, hδ⟩ := hst ε hε
  have hlam_event : ∀ᶠ σ : ℂ in comap Complex.im atTop,
      modularLambda (-1 / σ) ∈ Metric.ball (1 : ℂ) δ :=
    tendsto_modularLambda_neg_inv_atImInfty (Metric.ball_mem_nhds (1 : ℂ) hδpos)
  have hlam : ∀ᶠ σ : ℂ in comap Complex.im atTop, dist (modularLambda (-1 / σ)) (1 : ℂ) < δ := by
    filter_upwards [hlam_event] with σ hσ
    simpa [Metric.mem_ball] using hσ
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hlam
  obtain ⟨M, hM⟩ := hlam
  filter_upwards [hIm M] with n hn
  intro z hz
  have hclose := hδ (x := modularLambda (-1 / σseq n z))
    (hM (σseq n z).im (hn z hz) (σseq n z) rfl)
  simpa [dist_comm] using hclose

/-- At the third cusp, written as `1 - 1/σ` with `Im σ → ∞`, the inverse modular-lambda
coordinate tends uniformly to `0`.  This is the inverse-chart form of spherical convergence to the
north pole (`∞`). -/
theorem tendstoUniformlyOn_inv_modularLambda_one_sub_inv_of_im_tendsto_atTop
    {K : Set ℂ} {σseq : ℕ → ℂ → ℂ}
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, M ≤ (σseq n z).im) :
    TendstoUniformlyOn
      (fun n z => (modularLambda (1 - 1 / σseq n z))⁻¹)
      (fun _z => (0 : ℂ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let F : ℂ → ℂ := fun w => (w - 1) / w
  have hFcont : ContinuousAt F (1 : ℂ) := by
    dsimp [F]
    exact (continuousAt_id.sub continuousAt_const).div continuousAt_id one_ne_zero
  rw [Metric.continuousAt_iff] at hFcont
  obtain ⟨δ, hδpos, hδ⟩ := hFcont ε hε
  have hlam_event : ∀ᶠ σ : ℂ in comap Complex.im atTop,
      modularLambda (-1 / σ) ∈ Metric.ball (1 : ℂ) δ :=
    tendsto_modularLambda_neg_inv_atImInfty (Metric.ball_mem_nhds (1 : ℂ) hδpos)
  have hlam : ∀ᶠ σ : ℂ in comap Complex.im atTop, dist (modularLambda (-1 / σ)) (1 : ℂ) < δ := by
    filter_upwards [hlam_event] with σ hσ
    simpa [Metric.mem_ball] using hσ
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hlam
  obtain ⟨M, hM⟩ := hlam
  let M' : ℝ := max M 1
  filter_upwards [hIm M'] with n hn
  intro z hz
  have hσim : 0 < (σseq n z).im := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans (le_max_right M 1) (hn z hz))
  have hτim : 0 < (-1 / σseq n z).im := neg_inv_im_pos hσim
  have hT : modularLambda (1 - 1 / σseq n z)
      = modularLambda (-1 / σseq n z) / (modularLambda (-1 / σseq n z) - 1) := by
    rw [show 1 - 1 / σseq n z = -1 / σseq n z + 1 by ring]
    exact modularLambda_T_eq' hτim
  have hlam0 : modularLambda (-1 / σseq n z) ≠ 0 :=
    (modularLambda_omits_zero_one' hτim).1
  have hinv_eq : (modularLambda (1 - 1 / σseq n z))⁻¹ =
      (modularLambda (-1 / σseq n z) - 1) / modularLambda (-1 / σseq n z) := by
    rw [hT]
    field_simp [hlam0]
  have hF_one : F 1 = 0 := by
    simp [F]
  have hclose := hδ (x := modularLambda (-1 / σseq n z))
    (hM (σseq n z).im (le_trans (le_max_left M 1) (hn z hz)) (σseq n z) rfl)
  rw [hF_one] at hclose
  rw [hinv_eq]
  simpa [F, dist_comm] using hclose

/-- Spherical form of the third cusp: `1 - 1/σ` with `Im σ → ∞` tends to the north pole under
`stereo ∘ λ`. -/
theorem tendstoUniformlyOn_stereo_modularLambda_one_sub_inv_of_im_tendsto_atTop
    {K : Set ℂ} {σseq : ℕ → ℂ → ℂ}
    (hIm : ∀ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, M ≤ (σseq n z).im) :
    TendstoUniformlyOn
      (fun n z => stereo (modularLambda (1 - 1 / σseq n z)))
      (fun _z => northPole) atTop K := by
  have hne : ∀ᶠ n in atTop, ∀ z ∈ K, modularLambda (1 - 1 / σseq n z) ≠ 0 := by
    filter_upwards [hIm 1] with n hn
    intro z hz
    have hσim : 0 < (σseq n z).im := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hn z hz)
    have hτim : 0 < (-1 / σseq n z).im := neg_inv_im_pos hσim
    have htarget : 0 < (1 - 1 / σseq n z).im := by
      rw [show 1 - 1 / σseq n z = -1 / σseq n z + 1 by ring]
      simpa [Complex.add_im] using hτim
    exact (modularLambda_omits_zero_one' htarget).1
  exact tendstoUniformlyOn_stereo_of_inv_tendstoUniformlyOn_zero hne
    (tendstoUniformlyOn_inv_modularLambda_one_sub_inv_of_im_tendsto_atTop hIm)

end

end Bottcher

open UpperHalfPlane CongruenceSubgroup MulAction
open scoped MatrixGroups UpperHalfPlane

namespace Bottcher

noncomputable section

/-- Fundamental-domain routing for arbitrary modular-lambda base values.  Every sequence in
`ℂ∖{0,1}` has a subsequence whose values either remain in a compact subset of the punctured plane, or
are represented by a high upper-half-plane sequence in one of the six anharmonic cusp charts.  The six
charts correspond to `1`, `S`, `T`, `S*T`, `T*S`, and `S*T*S`; the last is recorded as the reciprocal
`(λ σ)⁻¹`, which is the shifted cusp-one chart used downstream. -/
theorem lambdaPunct_subseq_compact_or_anharmonic_cusp (u : ℕ → Punctured) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∃ K : Set Punctured, IsCompact K ∧ ∀ k, u (ψ k) ∈ K) ∨
        ∃ σseq : ℕ → UpperHalfPlane,
          (∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σseq k : ℂ).im) ∧
          ((∀ k, modularLambda (σseq k : ℂ) = (u (ψ k) : ℂ)) ∨
           (∀ k, modularLambda (-1 / (σseq k : ℂ)) = (u (ψ k) : ℂ)) ∨
           (∀ k, modularLambda ((σseq k : ℂ) + 1) = (u (ψ k) : ℂ)) ∨
           (∀ k, modularLambda (-1 / ((σseq k : ℂ) + 1)) = (u (ψ k) : ℂ)) ∨
           (∀ k, modularLambda (1 - 1 / (σseq k : ℂ)) = (u (ψ k) : ℂ)) ∨
           (∀ k, (modularLambda (σseq k : ℂ))⁻¹ = (u (ψ k) : ℂ)))) := by
  choose τ hτ using fun n => lambdaPunct_surjective (u n)
  choose g hg using fun n => ModularGroup.exists_smul_mem_fd (τ n)
  choose φ hφmem hφeq using fun n => exists_anharm_eq (g n)⁻¹
  let σ : ℕ → UpperHalfPlane := fun n => g n • τ n
  have hun : ∀ n, u n = φ n (lambdaPunct (σ n)) := by
    intro n
    have hτn : τ n = (g n)⁻¹ • σ n := by
      rw [show σ n = g n • τ n from rfl, ← mul_smul, inv_mul_cancel, one_smul]
    rw [← hτ n, hτn, hφeq n (σ n)]
  obtain ⟨⟨φ₀, hφ₀⟩, hinf⟩ :=
    Finite.exists_infinite_fiber (fun n => (⟨φ n, hφmem n⟩ : anharmonicGroup))
  rw [Set.infinite_coe_iff] at hinf
  have hSinf : {n | φ n = φ₀}.Infinite := by
    apply hinf.mono
    intro n hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at hn
    exact hn
  obtain ⟨ρ, hρmono, hρS⟩ :=
    extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hSinf)
  by_cases hb : ∃ M : ℝ, {k | (σ (ρ k)).im ≤ M}.Infinite
  · obtain ⟨M, hM⟩ := hb
    obtain ⟨ρ', hρ'mono, hρ'⟩ :=
      extraction_of_frequently_atTop (Nat.frequently_atTop_iff_infinite.mpr hM)
    let ψ : ℕ → ℕ := fun k => ρ (ρ' k)
    refine ⟨ψ, hρmono.comp hρ'mono, Or.inl ?_⟩
    let Kbase : Set Punctured := lambdaPunct '' ModularGroup.truncatedFundamentalDomain M
    have hKbase : IsCompact Kbase :=
      (ModularGroup.isCompact_truncatedFundamentalDomain M).image continuous_lambdaPunct
    let K : Set Punctured := (fun w : Punctured => φ₀ w) '' Kbase
    have hK : IsCompact K := hKbase.image (continuous_of_mem_anharmonicGroup hφ₀)
    refine ⟨K, hK, ?_⟩
    intro k
    have hmemFD : σ (ρ (ρ' k)) ∈ ModularGroup.truncatedFundamentalDomain M :=
      ⟨hg (ρ (ρ' k)), hρ' k⟩
    have hbaseval : lambdaPunct (σ (ρ (ρ' k))) ∈ Kbase :=
      Set.mem_image_of_mem lambdaPunct hmemFD
    have heqk : u (ψ k) = φ₀ (lambdaPunct (σ (ρ (ρ' k)))) := by
      dsimp [ψ]
      rw [hun, hρS]
    exact ⟨lambdaPunct (σ (ρ (ρ' k))), hbaseval, heqk.symm⟩
  · push Not at hb
    have hImtop : ∀ M : ℝ, ∀ᶠ k in atTop, M ≤ (σ (ρ k) : ℂ).im := by
      have htend : Tendsto (fun k => (σ (ρ k)).im) atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro M
        obtain ⟨N, hN⟩ := (hb M).bddAbove
        refine ⟨N + 1, fun k hk => ?_⟩
        by_contra hlt
        push Not at hlt
        have := hN hlt.le
        omega
      intro M
      rw [tendsto_atTop_atTop] at htend
      obtain ⟨N, hN⟩ := htend M
      exact eventually_atTop.mpr ⟨N, fun k hk => by simpa using hN k hk⟩
    let ψ : ℕ → ℕ := ρ
    let σseq : ℕ → UpperHalfPlane := fun k => σ (ρ k)
    refine ⟨ψ, hρmono, Or.inr ?_⟩
    refine ⟨σseq, ?_, ?_⟩
    · intro M
      simpa [σseq] using hImtop M
    · have h6 := anharmonicGroup_subset_sixSet hφ₀
      simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at h6
      rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
      · left
        intro k
        have h := congrArg Subtype.val (hun (ρ k))
        rw [hρS k] at h
        simp [lambdaPunct_coe] at h
        simpa [lambdaPunct_coe, σseq] using h.symm
      · right; left
        intro k
        have h := congrArg Subtype.val (hun (ρ k))
        rw [hρS k] at h
        simp [lambdaPunct_coe] at h
        have hSrel := modularLambda_S' (τ := (σseq k : ℂ)) (σseq k).2
        calc
          modularLambda (-1 / (σseq k : ℂ)) = 1 - modularLambda (σseq k : ℂ) := hSrel
          _ = (u (ψ k) : ℂ) := by simpa [lambdaPunct_coe, σseq, ψ] using h.symm
      · right; right; left
        intro k
        have h := congrArg Subtype.val (hun (ρ k))
        rw [hρS k] at h
        simp [lambdaPunct_coe] at h
        have hTrel := modularLambda_T_eq' (τ := (σseq k : ℂ)) (σseq k).2
        calc
          modularLambda ((σseq k : ℂ) + 1)
              = modularLambda (σseq k : ℂ) / (modularLambda (σseq k : ℂ) - 1) := hTrel
          _ = (u (ψ k) : ℂ) := by simpa [lambdaPunct_coe, σseq, ψ] using h.symm
      · right; right; right; left
        intro k
        have h := congrArg Subtype.val (hun (ρ k))
        rw [hρS k] at h
        simp [lambdaPunct_coe, Equiv.Perm.mul_apply] at h
        have him : 0 < ((σseq k : ℂ) + 1).im := by
          simpa [Complex.add_im] using (σseq k).2
        have hSrel := modularLambda_S' (τ := (σseq k : ℂ) + 1) him
        have hTrel := modularLambda_T_eq' (τ := (σseq k : ℂ)) (σseq k).2
        calc
          modularLambda (-1 / ((σseq k : ℂ) + 1))
              = 1 - modularLambda ((σseq k : ℂ) + 1) := hSrel
          _ = 1 - modularLambda (σseq k : ℂ) / (modularLambda (σseq k : ℂ) - 1) := by rw [hTrel]
          _ = (u (ψ k) : ℂ) := by simpa [lambdaPunct_coe, σseq, ψ] using h.symm
      · right; right; right; right; left
        intro k
        have h := congrArg Subtype.val (hun (ρ k))
        rw [hρS k] at h
        simp [lambdaPunct_coe, Equiv.Perm.mul_apply] at h
        have hnegim : 0 < (-1 / (σseq k : ℂ)).im := neg_inv_im_pos (σseq k).2
        have hSrel := modularLambda_S' (τ := (σseq k : ℂ)) (σseq k).2
        have hTrel := modularLambda_T_eq' (τ := -1 / (σseq k : ℂ)) hnegim
        calc
          modularLambda (1 - 1 / (σseq k : ℂ))
              = modularLambda (-1 / (σseq k : ℂ) + 1) := by ring_nf
          _ = modularLambda (-1 / (σseq k : ℂ)) /
              (modularLambda (-1 / (σseq k : ℂ)) - 1) := hTrel
          _ = (1 - modularLambda (σseq k : ℂ)) / ((1 - modularLambda (σseq k : ℂ)) - 1) := by rw [hSrel]
          _ = (u (ψ k) : ℂ) := by simpa [lambdaPunct_coe, σseq, ψ] using h.symm
      · right; right; right; right; right
        intro k
        have h := congrArg Subtype.val (hun (ρ k))
        rw [hρS k] at h
        simp [lambdaPunct_coe, Equiv.Perm.mul_apply] at h
        have hlam0 : modularLambda (σseq k : ℂ) ≠ 0 :=
          (modularLambda_omits_zero_one' (σseq k).2).1
        calc
          (modularLambda (σseq k : ℂ))⁻¹
              = 1 - (1 - modularLambda (σseq k : ℂ)) /
                  ((1 - modularLambda (σseq k : ℂ)) - 1) := by
                field_simp [hlam0]
                ring
          _ = (u (ψ k) : ℂ) := by simpa [lambdaPunct_coe, σseq, ψ] using h.symm

end

end Bottcher
