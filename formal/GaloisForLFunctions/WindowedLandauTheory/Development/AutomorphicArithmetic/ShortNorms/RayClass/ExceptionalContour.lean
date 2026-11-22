import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.ContourShift
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.BoundaryLogDerivative

/-! Shift the ray class Perron integral through the principal pole and any simple exceptional zero. -/

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk
open scoped Classical

namespace GlobalTheory.Hk.PsiExc

theorem one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  rw [LFam.ell, Real.le_log_iff_exp_le (by have := 𝓕.B_ge; positivity)]
  have := Real.exp_one_lt_d9
  have := 𝓕.B_ge
  nlinarith [abs_nonneg t]

theorem ell_mono (𝓕 : LFam) {t T : ℝ} (h : |t| ≤ T) : 𝓕.ell t ≤ 𝓕.ell T := by
  have := 𝓕.B_ge
  refine Real.log_le_log (by positivity) ?_
  have h2 : |t| + 2 ≤ |T| + 2 := by linarith [le_abs_self T]
  exact mul_le_mul_of_nonneg_left h2 (by linarith)

theorem norm_term_le {u β σ : ℝ} (hu : 1 ≤ u) (h1 : 1 / 2 ≤ β) (h2 : β ≤ σ) :
    ‖(u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * u ^ σ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]
  have := Real.rpow_le_rpow_of_exponent_le hu h2
  calc _ ≤ u ^ σ / (1 / 2) := by gcongr
    _ = _ := by ring

theorem norm_sum_le_of_card {Z : Finset ℝ} (hZ : Z.card ≤ 1) {f : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ β ∈ Z, ‖f β‖ ≤ b) : ‖∑ β ∈ Z, f β‖ ≤ b := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ b h).trans ?_)
  have : (Z.card : ℝ) ≤ 1 := by exact_mod_cast hZ
  rw [nsmul_eq_mul]
  nlinarith

theorem exists_line {Z : Finset ℝ} (hZ : Z.card ≤ 1) {d : ℝ} (hd : 0 < d) :
    ∃ σ : ℝ, 1 - 4 * d ≤ σ ∧ σ ≤ 1 - 2 * d ∧ ∀ β ∈ Z, d ≤ |σ - β| := by
  rcases Z.eq_empty_or_nonempty with rfl | ⟨β, hβ⟩
  · exact ⟨1 - 2 * d, by linarith, le_rfl, by simp⟩
  have e : ∀ γ ∈ Z, γ = β := fun γ hγ => Finset.card_le_one.1 hZ _ hγ _ hβ
  rcases le_total β (1 - 3 * d) with h | h
  · refine ⟨1 - 2 * d, by linarith, le_rfl, fun γ hγ => ?_⟩
    rw [e γ hγ]
    exact le_abs.2 (Or.inl (by linarith))
  · refine ⟨1 - 4 * d, le_rfl, by linarith, fun γ hγ => ?_⟩
    rw [e γ hγ]
    exact le_abs.2 (Or.inr (by linarith))

theorem logDeriv_simple {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) (h0 : f p = 0)
    (h1 : deriv f p ≠ 0) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p,
      deriv f s / f s = 1 / (s - p) + g s := by
  have ho : analyticOrderAt f p = 1 := hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 h1
  obtain ⟨g, hg, h⟩ := GlobalTheory.ExplicitRect.logDeriv_pole hf (by rw [ho]; simp)
  refine ⟨g, hg, ?_⟩
  simpa [analyticOrderNatAt, ho] using h

theorem contour (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (Z : Finset ℝ) (c₀ C u T d : ℝ) (hc₀ : 0 < c₀)
    (hc₁ : c₀ ≤ 1 / 20) (hC : 0 < C) (hZ : 𝓕.ExcZ χ c₀ Z) (hu : 2 ≤ u) (hT : 1 ≤ T)
    (hd : d = c₀ / (8 * 𝓕.ell T))
    (hb : ∀ s : ℂ, 1 - c₀ / 2 / 𝓕.ell s.im ≤ s.re → s.re ≤ 3 → (∀ β ∈ Z, s ≠ (β : ℂ)) →
      ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ C * 𝓕.ell s.im ^ 2) :
    ‖(1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        LSeries (𝓕.lamChi χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) *
          (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) /
          (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))
      - (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
      18 * ((C * 𝓕.ell T ^ 2 + 2 / d) * u / T) + 4 * (T * (C * 𝓕.ell T ^ 2 + 2 / d) * u ^ (1 - 2 * d))
        + 2 * u ^ (1 - 2 * d) := by
  have hu0 : 0 < u := by linarith
  have hlog : 1 / 2 < Real.log u := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hu
    linarith
  have hc1 : 1 < 1 + 1 / Real.log u := by
    have : 0 < 1 / Real.log u := by apply one_div_pos.2; linarith
    linarith
  have hc3 : 1 + 1 / Real.log u ≤ 3 := by
    have : 1 / Real.log u ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have huc : u ^ (1 + 1 / Real.log u) ≤ 3 * u := by
    rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0,
      mul_one_div_cancel (by linarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  generalize 1 + 1 / Real.log u = c at *
  obtain ⟨hcard, hZ1, hZ2⟩ := hZ
  have hl := one_le_ell 𝓕 T
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 / 160 := by
    rw [hd, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := exists_line hcard hd0
  have hβ : ∀ β ∈ Z, 1 / 2 ≤ β := fun β h => by
    have h1 := (hZ1 β h).1
    have h2 : c₀ / 𝓕.ell 0 ≤ c₀ := div_le_self hc₀.le (one_le_ell 𝓕 0)
    linarith
  have hreg : ∀ s : ℂ, σ ≤ s.re → |s.im| ≤ T → 1 - c₀ / 2 / 𝓕.ell s.im ≤ s.re := by
    intro s h1 h2
    have h3 := ell_mono 𝓕 h2
    have h4 := one_le_ell 𝓕 s.im
    have h5 : c₀ / 2 / 𝓕.ell T ≤ c₀ / 2 / 𝓕.ell s.im := by gcongr
    have h6 : c₀ / 2 / 𝓕.ell T = 4 * d := by rw [hd]; field_simp; ring
    linarith
  have hreg' : ∀ s : ℂ, σ ≤ s.re → |s.im| ≤ T → 1 - c₀ / 𝓕.ell s.im ≤ s.re := by
    intro s h1 h2
    have h3 := hreg s h1 h2
    have h4 := one_le_ell 𝓕 s.im
    have h5 : c₀ / 2 / 𝓕.ell s.im ≤ c₀ / 𝓕.ell s.im := by gcongr; linarith
    linarith
  have han : ∀ s : ℂ, σ ≤ s.re → AnalyticAt ℂ (𝓕.F χ) s := fun s hs =>
    (GlobalTheory.Hk.RayCont.continuation_growth 𝓕 χ).1 s (by simp only [Set.mem_setOf_eq]; linarith)
  set Z' := Z.filter (fun β => σ < β) with hZ'
  have h1Z : (1 : ℂ) ∉ Z'.image (fun β : ℝ => (β : ℂ)) := by
    intro h
    obtain ⟨β, h1, h2⟩ := Finset.mem_image.1 h
    have h3 : β = 1 := by exact_mod_cast h2
    have := (hZ1 β (Finset.mem_filter.1 h1).1).2.1
    linarith
  have hM : 0 ≤ C * 𝓕.ell T ^ 2 + 2 / d := by positivity
  have hite : ∀ s : ℂ, s ≠ 1 →
      AnalyticAt ℂ (fun s : ℂ => if χ = 1 then 1 / (s - 1) else (0 : ℂ)) s := by
    intro s hs
    by_cases h : χ = 1
    · simp only [if_pos h]
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hs)
    · simp only [if_neg h]
      exact analyticAt_const
  have key := shift
    (fun s => deriv (𝓕.F χ) s / 𝓕.F χ s - (if χ = 1 then 1 / (s - 1) else 0))
    (insert 1 (Z'.image (fun β : ℝ => (β : ℂ))))
    (fun p => if p = 1 then (if χ = 1 then -1 else 0) else 1) u σ c T _ (by linarith) (by linarith)
    (by linarith) hc3 huc (by linarith) hM ?_ ?_ ?_ ?_
  · have e1 : ∀ t : ℝ, -(deriv (𝓕.F χ) ((c : ℂ) + t * I) / 𝓕.F χ ((c : ℂ) + t * I) -
        (if χ = 1 then 1 / (((c : ℂ) + t * I) - 1) else 0)) =
        LSeries (𝓕.lamChi χ) ((c : ℂ) + t * I) := fun t => by
      rw [← (GlobalTheory.Hk.LogDeriv.logDeriv_F 𝓕 χ _ (by simpa using hc1)).2.2.2]
      ring
    simp only [e1] at key
    rw [Finset.sum_insert h1Z, Finset.sum_image (fun a _ b _ h => ofReal_injective h)] at key
    have e2 : ∑ β ∈ Z', (if (β : ℂ) = 1 then (if χ = 1 then -1 else 0) else 1) *
        ((u : ℂ) ^ (β : ℂ) / (β : ℂ)) = ∑ β ∈ Z', (u : ℂ) ^ (β : ℂ) / (β : ℂ) :=
      Finset.sum_congr rfl fun β h => by
        have hne : (β : ℂ) ≠ 1 := fun e => h1Z (Finset.mem_image.2 ⟨β, h, e⟩)
        rw [if_neg hne, one_mul]
    have e3 : (if (1 : ℂ) = 1 then (if χ = 1 then -1 else 0) else 1) *
        ((u : ℂ) ^ (1 : ℂ) / (1 : ℂ)) = -(if χ = 1 then (u : ℂ) else 0) := by
      split_ifs <;> simp_all
    rw [e2, e3] at key
    have hs : u ^ σ ≤ u ^ (1 - 2 * d) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
    have n1 : ‖∑ β ∈ Z.filter (fun β => ¬ σ < β), (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        2 * u ^ (1 - 2 * d) :=
      norm_sum_le_of_card ((Finset.card_filter_le _ _).trans hcard) (by positivity) fun β h =>
        norm_term_le (by linarith) (hβ β (Finset.mem_filter.1 h).1)
          ((not_lt.1 (Finset.mem_filter.1 h).2).trans hσ2)
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun β => σ < β), ← add_assoc]
    refine (norm_add_le _ _).trans (add_le_add ?_ n1)
    rw [sub_eq_add_neg, add_assoc]
    refine key.trans ?_
    gcongr
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · simp only [one_re, one_im]
      exact ⟨by linarith, hc1, trivial⟩
    · obtain ⟨β, h1, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h1
      have := (hZ1 β h2).2.1
      simp only [ofReal_re, ofReal_im]
      exact ⟨h3, by linarith, trivial⟩
  · intro s h1 h2 h3 h4
    rw [Finset.mem_insert, not_or] at h4
    have hF : 𝓕.F χ s ≠ 0 := fun h0 => by
      obtain ⟨β, h5, rfl⟩ := hZ2 s (hreg' s h1 h3) h0
      refine h4.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨h5, lt_of_le_of_ne h1 ?_⟩))
      intro e
      have := hσ3 β h5
      rw [e] at this
      simp at this
      linarith
    exact ((han s h1).deriv.div (han s h1) hF).sub (hite s h4.1)
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · have h1 : σ ≤ (1 : ℂ).re := by simp only [one_re]; linarith
      have hF : 𝓕.F χ 1 ≠ 0 := fun h0 => by
        obtain ⟨β, h5, h6⟩ := hZ2 1 (hreg' 1 h1 (by simp; linarith)) h0
        have h3 : (1 : ℝ) = β := by exact_mod_cast h6
        have := (hZ1 β h5).2.1
        linarith
      refine ⟨_, (han 1 h1).deriv.div (han 1 h1) hF, Eventually.of_forall fun s => ?_⟩
      simp only [if_true, Pi.div_apply]
      split_ifs <;> ring
    · have hp1 : p ≠ 1 := fun e => h1Z (e ▸ hp)
      obtain ⟨β, h1, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h1
      obtain ⟨g, hg, h⟩ := logDeriv_simple (han β h3.le) (hZ1 β h2).2.2.1 (hZ1 β h2).2.2.2
      refine ⟨_, hg.sub (hite _ hp1), h.mono fun s hs => ?_⟩
      simp only [if_neg hp1, Pi.sub_apply, hs]
      ring
  · intro s h1 h2 h3 h4
    have far : ∀ x : ℝ, d ≤ |σ - x| → d ≤ ‖s - (x : ℂ)‖ := by
      intro x hx
      rcases h4 with h4 | h4
      · refine hx.trans ?_
        have := Complex.abs_re_le_norm (s - (x : ℂ))
        simpa [h4] using this
      · have := Complex.abs_im_le_norm (s - (x : ℂ))
        simp only [sub_im, ofReal_im, sub_zero, h4] at this
        linarith
    have inv : ∀ x : ℝ, d ≤ |σ - x| → ‖1 / (s - (x : ℂ))‖ ≤ 1 / d := by
      intro x hx
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hd0 (far x hx)
    have b1 := hb s (hreg s h1 h3) (h2.trans hc3) fun β h e => by
      have := far β (hσ3 β h)
      rw [e] at this
      simp at this
      linarith
    have b2 : ‖∑ β ∈ Z, 1 / (s - (β : ℂ))‖ ≤ 1 / d :=
      norm_sum_le_of_card hcard (by positivity) fun β h => inv β (hσ3 β h)
    have b3 : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ ≤ 1 / d := by
      split_ifs
      · simpa using inv 1 (le_abs.2 (Or.inr (by linarith)))
      · simp [hd0.le]
    have b4 : C * 𝓕.ell s.im ^ 2 ≤ C * 𝓕.ell T ^ 2 := by
      have := ell_mono 𝓕 h3
      have := one_le_ell 𝓕 s.im
      gcongr
    have b5 := norm_sub_le (deriv (𝓕.F χ) s / 𝓕.F χ s) (if χ = 1 then 1 / (s - 1) else 0 : ℂ)
    have b6 := norm_add_le (deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ β ∈ Z, 1 / (s - (β : ℂ)))
      (∑ β ∈ Z, 1 / (s - (β : ℂ)))
    rw [sub_add_cancel] at b6
    have b7 : 2 / d = 1 / d + 1 / d := by ring
    linarith

end GlobalTheory.Hk.PsiExc
