import Mathlib.Analysis.Complex.MeanValue

/-!
# Compact-uniform dilation calculus

Reusable compact-uniform first-order dilation, dilation continuity, quotient stability, and filter
reindexing lemmas for complex-valued functions.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem tendstoUniformlyOn_dilation_differenceQuotient
    {f : ℂ → ℂ} (hf : ContDiff ℂ 1 f)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun ε : ℂ => fun u : ℂ =>
        ε⁻¹ * (f ((1 + ε) * u) - f u))
      (fun u : ℂ => u * deriv f u) (𝓝[≠] 0) K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨u₀, hu₀K, hu₀max⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let R : ℝ := ‖u₀‖ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith [norm_nonneg u₀]
  have huR : ∀ u ∈ K, ‖u‖ < R := by
    intro u hu
    exact lt_of_le_of_lt (hu₀max hu) (lt_add_one _)
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hballCompact : IsCompact (Metric.closedBall (0 : ℂ) (2 * R)) :=
    isCompact_closedBall _ _
  have hdfUC : UniformContinuousOn (deriv f) (Metric.closedBall (0 : ℂ) (2 * R)) :=
    hballCompact.uniformContinuousOn_of_continuous hdf.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨δ, hδ, hderiv⟩ := Metric.uniformContinuousOn_iff.mp hdfUC
    (η / R) (div_pos hη hRpos)
  have hrad : 0 < min 1 (δ / R) := lt_min zero_lt_one (div_pos hδ hRpos)
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hrad)]
    with ε hεne hεball
  intro u hu
  have hε0 : ε ≠ 0 := by simpa using hεne
  have hεnorm : ‖ε‖ < min 1 (δ / R) := by
    simpa [Metric.mem_ball, dist_zero_right] using hεball
  have hεone : ‖ε‖ < 1 := lt_of_lt_of_le hεnorm (min_le_left _ _)
  have hεδR : ‖ε‖ < δ / R := lt_of_lt_of_le hεnorm (min_le_right _ _)
  have huNorm : ‖u‖ < R := huR u hu
  let v : ℂ := (1 + ε) * u
  have hv_sub : v - u = ε * u := by
    dsimp [v]
    ring
  have huBall : u ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
    linarith
  have hsegBall : segment ℝ u v ⊆ Metric.closedBall (0 : ℂ) (2 * R) := by
    intro z hz
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
    have hzu : ‖z - u‖ ≤ ‖v - u‖ := norm_sub_le_of_mem_segment hz
    have hvub : ‖v - u‖ < R := by
      rw [hv_sub, norm_mul]
      have hnonnegε : 0 ≤ ‖ε‖ := norm_nonneg _
      have hnonnegu : 0 ≤ ‖u‖ := norm_nonneg _
      nlinarith
    apply le_of_lt
    calc
      ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - u) u
      _ < R + R := add_lt_add (lt_of_le_of_lt hzu hvub) huNorm
      _ = 2 * R := by ring
  have hsegClose : ∀ z ∈ segment ℝ u v, dist z u < δ := by
    intro z hz
    rw [dist_eq_norm]
    have hzu : ‖z - u‖ ≤ ‖v - u‖ := norm_sub_le_of_mem_segment hz
    have hvudelta : ‖v - u‖ < δ := by
      rw [hv_sub, norm_mul]
      have hnonnegε : 0 ≤ ‖ε‖ := norm_nonneg _
      have hnonnegu : 0 ≤ ‖u‖ := norm_nonneg _
      have hnonnegδR : 0 ≤ δ / R := (div_pos hδ hRpos).le
      calc
        ‖ε‖ * ‖u‖ < (δ / R) * R := by nlinarith
        _ = δ := div_mul_cancel₀ δ hRpos.ne'
    exact lt_of_le_of_lt hzu hvudelta
  let g : ℂ → ℂ := fun z => f z - deriv f u * z
  have hgdiff : ∀ z ∈ segment ℝ u v, DifferentiableAt ℂ g z := by
    intro z hz
    exact (hf.differentiable (by norm_num) z).sub
      ((differentiableAt_const (c := deriv f u)).mul differentiableAt_id)
  have hgderiv : ∀ z ∈ segment ℝ u v,
      ‖deriv g z‖ ≤ η / R := by
    intro z hz
    have hzBall := hsegBall hz
    have hclose := hsegClose z hz
    have hd := hderiv z hzBall u huBall hclose
    rw [dist_eq_norm] at hd
    have hderivg : deriv g z = deriv f z - deriv f u := by
      have hg : HasDerivAt g (deriv f z - deriv f u) z := by
        have hlin : HasDerivAt (fun w : ℂ => deriv f u * w) (deriv f u) z := by
          simpa using (hasDerivAt_id z).const_mul (deriv f u)
        exact (hf.differentiable (by norm_num) z).hasDerivAt.sub hlin
      exact hg.deriv
    rw [hderivg]
    exact hd.le
  have hmv := (convex_segment u v).norm_image_sub_le_of_norm_deriv_le
    hgdiff hgderiv (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
  have hremainder :
      ‖(f v - f u) - ε * (u * deriv f u)‖ ≤
        (η / R) * ‖v - u‖ := by
    have heq :
        (f v - f u) - ε * (u * deriv f u) = g v - g u := by
      dsimp [g]
      rw [show ε * (u * deriv f u) = deriv f u * (ε * u) by ring,
        ← hv_sub]
      ring
    rw [heq]
    exact hmv
  have hremainder_lt :
      ‖(f v - f u) - ε * (u * deriv f u)‖ < η * ‖ε‖ := by
    refine lt_of_le_of_lt hremainder ?_
    rw [hv_sub, norm_mul]
    calc
      (η / R) * (‖ε‖ * ‖u‖) < (η / R) * (‖ε‖ * R) := by
        have hεnormpos : 0 < ‖ε‖ := norm_pos_iff.mpr hε0
        have hηRpos : 0 < η / R := div_pos hη hRpos
        exact mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_left huNorm hεnormpos) hηRpos
      _ = η * ‖ε‖ := by field_simp [hRpos.ne']
  rw [dist_eq_norm]
  change ‖u * deriv f u - ε⁻¹ * (f v - f u)‖ < η
  have hrewrite :
      u * deriv f u - ε⁻¹ * (f v - f u) =
        -ε⁻¹ * ((f v - f u) - ε * (u * deriv f u)) := by
    field_simp [hε0]
    ring
  rw [hrewrite, norm_mul, norm_neg, norm_inv]
  rw [inv_mul_lt_iff₀ (norm_pos_iff.mpr hε0)]
  simpa [mul_comm] using hremainder_lt

theorem tendstoUniformlyOn_dilation
    {f : ℂ → ℂ} (hf : Continuous f)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun ε : ℂ => fun u : ℂ => f ((1 + ε) * u))
      f (𝓝 0) K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨u₀, hu₀K, hu₀max⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let R : ℝ := ‖u₀‖ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    linarith [norm_nonneg u₀]
  have huR : ∀ u ∈ K, ‖u‖ < R := by
    intro u hu
    exact lt_of_le_of_lt (hu₀max hu) (lt_add_one _)
  have hballCompact : IsCompact (Metric.closedBall (0 : ℂ) (2 * R)) :=
    isCompact_closedBall _ _
  have hfUC : UniformContinuousOn f (Metric.closedBall (0 : ℂ) (2 * R)) :=
    hballCompact.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨δ, hδ, hfun⟩ := Metric.uniformContinuousOn_iff.mp hfUC η hη
  have hrad : 0 < min 1 (δ / R) := lt_min zero_lt_one (div_pos hδ hRpos)
  filter_upwards [Metric.ball_mem_nhds 0 hrad] with ε hεball
  intro u hu
  have hεnorm : ‖ε‖ < min 1 (δ / R) := by
    simpa [Metric.mem_ball, dist_zero_right] using hεball
  have hεone : ‖ε‖ < 1 := lt_of_lt_of_le hεnorm (min_le_left _ _)
  have hεδR : ‖ε‖ < δ / R := lt_of_lt_of_le hεnorm (min_le_right _ _)
  have huNorm : ‖u‖ < R := huR u hu
  have huBall : u ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
    linarith
  have hvBall : (1 + ε) * u ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero, norm_mul]
    have hone : ‖(1 : ℂ) + ε‖ ≤ 1 + ‖ε‖ := by
      simpa using norm_add_le (1 : ℂ) ε
    have hnonneg : 0 ≤ ‖(1 : ℂ) + ε‖ := norm_nonneg _
    have hnonnegu : 0 ≤ ‖u‖ := norm_nonneg _
    have htwoR : 0 < 2 * R := by positivity
    nlinarith
  have hdist : dist ((1 + ε) * u) u < δ := by
    rw [dist_eq_norm]
    have heq : (1 + ε) * u - u = ε * u := by ring
    rw [heq, norm_mul]
    have hnonnegε : 0 ≤ ‖ε‖ := norm_nonneg _
    have hnonnegu : 0 ≤ ‖u‖ := norm_nonneg _
    have hnonnegδR : 0 ≤ δ / R := (div_pos hδ hRpos).le
    calc
      ‖ε‖ * ‖u‖ < (δ / R) * R := by nlinarith
      _ = δ := div_mul_cancel₀ δ hRpos.ne'
  simpa [dist_comm] using hfun ((1 + ε) * u) hvBall u huBall hdist

theorem TendstoUniformlyOn.div_of_isCompact_of_ne_zero
    {ι : Type*} {p : Filter ι}
    {q d : ℂ → ℂ} {qseq dseq : ι → ℂ → ℂ}
    {K : Set ℂ} (hK : IsCompact K)
    (hq : TendstoUniformlyOn qseq q p K)
    (hd : TendstoUniformlyOn dseq d p K)
    (hqcont : ContinuousOn q K) (hdcont : ContinuousOn d K)
    (hdne : ∀ u ∈ K, d u ≠ 0) :
    TendstoUniformlyOn
      (fun n u => qseq n u / dseq n u)
      (fun u => q u / d u) p K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨u₀, hu₀K, hu₀min⟩ :=
    hK.exists_isMinOn hKne hdcont.norm
  obtain ⟨v₀, hv₀K, hv₀max⟩ :=
    hK.exists_isMaxOn hKne hqcont.norm
  let c : ℝ := ‖d u₀‖
  let B : ℝ := ‖q v₀‖ + 1
  have hcpos : 0 < c := by
    exact norm_pos_iff.mpr (hdne u₀ hu₀K)
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [norm_nonneg (q v₀)]
  have hdlower : ∀ u ∈ K, c ≤ ‖d u‖ := fun u hu => hu₀min hu
  have hqupper : ∀ u ∈ K, ‖q u‖ < B := by
    intro u hu
    exact lt_of_le_of_lt (hv₀max hu) (lt_add_one _)
  let C : ℝ := 2 / c + 2 * B / c ^ 2
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  rw [Metric.tendstoUniformlyOn_iff] at hq hd ⊢
  intro η hη
  let e : ℝ := min (c / 2) (η / C)
  have hepos : 0 < e := by
    dsimp [e]
    exact lt_min (div_pos hcpos (by norm_num)) (div_pos hη hCpos)
  have hec : e ≤ c / 2 := min_le_left _ _
  have heη : e ≤ η / C := min_le_right _ _
  filter_upwards [hq e hepos, hd e hepos] with n hqn hdn
  intro u hu
  have hqerr := hqn u hu
  have hderr := hdn u hu
  rw [dist_eq_norm] at hqerr hderr ⊢
  have hqerr' : ‖q u - qseq n u‖ < e := hqerr
  have hderr' : ‖dseq n u - d u‖ < e := by
    rw [← norm_neg]
    simpa using hderr
  have hdpos : 0 < ‖d u‖ := lt_of_lt_of_le hcpos (hdlower u hu)
  have hdnLower : c / 2 < ‖dseq n u‖ := by
    have htri : ‖d u‖ ≤ ‖d u - dseq n u‖ + ‖dseq n u‖ := by
      simpa only [sub_add_cancel] using norm_add_le (d u - dseq n u) (dseq n u)
    have herr : ‖d u - dseq n u‖ < e := hderr
    linarith [hdlower u hu]
  have hdnpos : 0 < ‖dseq n u‖ := lt_of_lt_of_le (half_pos hcpos) hdnLower.le
  have hterm1 :
      ‖(q u - qseq n u) / dseq n u‖ < 2 * e / c := by
    rw [norm_div]
    have hdiv : ‖q u - qseq n u‖ / ‖dseq n u‖ < e / (c / 2) :=
      lt_trans (div_lt_div_of_pos_right hqerr' hdnpos)
        (div_lt_div_of_pos_left hepos (half_pos hcpos) hdnLower)
    calc
      ‖q u - qseq n u‖ / ‖dseq n u‖ < e / (c / 2) := hdiv
      _ = 2 * e / c := by field_simp [hcpos.ne']
  have hterm2 :
      ‖q u * (dseq n u - d u) / (dseq n u * d u)‖ <
        2 * B * e / c ^ 2 := by
    rw [norm_div, norm_mul, norm_mul]
    have hnum : ‖q u‖ * ‖dseq n u - d u‖ < B * e := by
      calc
        ‖q u‖ * ‖dseq n u - d u‖ ≤ B * ‖dseq n u - d u‖ :=
          mul_le_mul_of_nonneg_right (hqupper u hu).le (norm_nonneg _)
        _ < B * e := mul_lt_mul_of_pos_left hderr' hBpos
    have hden : c ^ 2 / 2 < ‖dseq n u‖ * ‖d u‖ := by
      have hdlo := hdlower u hu
      nlinarith [mul_lt_mul_of_pos_right hdnLower hcpos]
    have hdenpos : 0 < ‖dseq n u‖ * ‖d u‖ := mul_pos hdnpos hdpos
    have hdiv :
        ‖q u‖ * ‖dseq n u - d u‖ /
            (‖dseq n u‖ * ‖d u‖) <
          (B * e) / (c ^ 2 / 2) :=
      lt_trans (div_lt_div_of_pos_right hnum hdenpos)
        (div_lt_div_of_pos_left (mul_pos hBpos hepos) (by positivity) hden)
    calc
      ‖q u‖ * ‖dseq n u - d u‖ / (‖dseq n u‖ * ‖d u‖) <
          B * e / (c ^ 2 / 2) := hdiv
      _ = 2 * B * e / c ^ 2 := by field_simp [hcpos.ne']
  have hrewrite :
      q u / d u - qseq n u / dseq n u =
        (q u - qseq n u) / dseq n u +
          q u * (dseq n u - d u) / (dseq n u * d u) := by
    have hdnNe : dseq n u ≠ 0 := norm_ne_zero_iff.mp hdnpos.ne'
    field_simp [hdne u hu, hdnNe]
    ring
  rw [hrewrite]
  calc
    ‖(q u - qseq n u) / dseq n u +
        q u * (dseq n u - d u) / (dseq n u * d u)‖
        ≤ ‖(q u - qseq n u) / dseq n u‖ +
            ‖q u * (dseq n u - d u) / (dseq n u * d u)‖ := norm_add_le _ _
    _ < 2 * e / c + 2 * B * e / c ^ 2 := add_lt_add hterm1 hterm2
    _ = C * e := by dsimp [C]; ring
    _ ≤ C * (η / C) := mul_le_mul_of_nonneg_left heη hCpos.le
    _ = η := by field_simp [hCpos.ne']

theorem TendstoUniformlyOn.comp_tendsto_index
    {ι κ α β : Type*} [PseudoMetricSpace β]
    {p : Filter ι} {q : Filter κ} {φ : κ → ι}
    {F : ι → α → β} {f : α → β} {K : Set α}
    (h : TendstoUniformlyOn F f p K) (hφ : Tendsto φ q p) :
    TendstoUniformlyOn (fun k => F (φ k)) f q K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro η hη
  exact hφ.eventually (h η hη)

end GaloisForLFunctions.HTGeometry
