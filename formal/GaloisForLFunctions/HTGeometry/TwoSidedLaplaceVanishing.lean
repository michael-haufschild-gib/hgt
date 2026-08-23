import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# A function that is a Laplace transform on both sides of a line vanishes

Let `ψ₁, ψ₂` be `L²` data on `(0,∞)` and let `G` be *continuous* on `ℂ` with

* `G w = 𝓛(ψ₁)(w)` for `Re w > 0`,
* `G w = 𝓛(ψ₂)(−w)` for `Re w < 0`.

Then `ψ₁ = ψ₂ = 0`.  On the line `Re w = σ > 0` the Laplace transform of `ψ₁` is the Fourier
transform of the damped datum `1_{x>0}ψ₁(x)e^{-σx}`; letting `σ ↓ 0` the damped datum converges in
`L²` to `1_{x>0}ψ₁`, and `G` is continuous, so the Fourier transform of `1_{x>0}ψ₁` is the
restriction of `G` to the imaginary axis.  The same computation on the left produces the Fourier
transform of `x ↦ 1_{x<0}ψ₂(−x)`.  The two data therefore have the same Fourier transform, hence
agree; but one is supported on the positive ray and the other on the negative ray.

This is the elementary substitute for the Nevanlinna/Krein theory of functions of bounded
characteristic in two complementary half-planes: it says the two Hardy spaces of the two half-planes
meet only in `0`.

## Main results

* `rayDampRefl`, `fourierIntegral_rayDampRefl`
* `eq_zero_of_two_sided_laplace`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology FourierTransform

noncomputable section

/-! ## The reflected damped datum -/

/-- The damped datum reflected to the negative ray: `x ↦ 1_{x<0}·ψ(−x)·e^{σx}`. -/
def rayDampRefl (ψ : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ := fun x => rayDamp ψ σ (-x)

theorem memLp_two_rayDampRefl {ψ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℝ} (hσ : 0 ≤ σ) : MemLp (rayDampRefl ψ σ) 2 volume := by
  have h : MemLp (rayDamp ψ σ) 2 (volume : Measure ℝ) := memLp_two_rayDamp hψ hσ
  exact MemLp.comp_measurePreserving h (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem integrable_rayDampRefl {ψ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℝ} (hσ : 0 < σ) : Integrable (rayDampRefl ψ σ) volume := by
  have h : Integrable (rayDamp ψ σ) volume := integrable_rayDamp hψ hσ
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have := (memLp_one_iff_integrable.2 h).comp_measurePreserving hmp
  exact memLp_one_iff_integrable.1 this

/-- **The Fourier transform of the reflected damped datum is the Laplace transform at the
reflected frequency.** -/
theorem fourierIntegral_rayDampRefl (ψ : ℝ → ℂ) (σ ξ : ℝ) :
    𝓕 (rayDampRefl ψ σ) ξ = laplaceRay ψ (rayLine σ (-ξ)) := by
  rw [← fourierIntegral_rayDamp ψ σ (-ξ)]
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_neg_eq_self
    (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) •
      rayDampRefl ψ σ v) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [rayDampRefl, neg_neg, smul_eq_mul]
  congr 2
  push_cast
  ring

/-! ## Identifying the `L²` Fourier transform on a line -/

theorem coeFn_fourierTransform_toLp {f : ℝ → ℂ} (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf1 : Integrable f volume) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => 𝓕 f ξ := by
  have hcoe : ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] f :=
    hf2.coeFn_toLp
  have hint : Integrable ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) volume :=
    hf1.congr hcoe.symm
  have hbridge := coeFn_fourierTransform_ae_eq_fourierIntegral (hf2.toLp f) hint
  filter_upwards [hbridge] with ξ hξ
  rw [hξ, Real.Lp.fourierTransform_apply]
  have hcoe1 : (((memLp_one_iff_integrable.mpr hint).toLp
      ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) : ℝ → ℂ) =ᵐ[volume] f :=
    ((memLp_one_iff_integrable.mpr hint).coeFn_toLp).trans hcoe
  exact Real.fourier_congr_ae hcoe1 ξ

/-! ## `L²` continuity of the damping -/
theorem tendsto_integral_norm_sq_rayDamp_sub {ψ : ℝ → ℂ}
    (hψ : MemLp ψ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℕ → ℝ} (hσ0 : ∀ n, 0 ≤ σ n) (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, ‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ^ 2) atTop (𝓝 0) := by
  have hsq : Integrable (fun x : ℝ => ‖rayDamp ψ 0 x‖ ^ 2) volume := by
    have h := memLp_two_rayDamp hψ (le_refl (0 : ℝ))
    exact (memLp_two_iff_integrable_sq_norm h.1).1 h
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x : ℝ => ‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ^ 2) volume := by
    intro n
    exact (((memLp_two_rayDamp hψ (hσ0 n)).sub (memLp_two_rayDamp hψ le_rfl)).1.norm.pow 2)
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      ‖‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ^ 2‖ ≤ 4 * ‖rayDamp ψ 0 x‖ ^ 2 := by
    intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases eq_or_ne (rayDamp ψ 0 x) 0 with h0 | h0
    · have hz : rayDamp ψ (σ n) x = 0 := by
        simp only [rayDamp, Set.indicator_apply] at h0 ⊢
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [if_pos hx] at h0 ⊢
          have hexp : expRay ((0 : ℝ) : ℂ) x ≠ 0 := Complex.exp_ne_zero _
          have hzero : ψ x = 0 := by
            rcases mul_eq_zero.1 h0 with h | h
            · exact h
            · exact absurd h hexp
          rw [hzero, zero_mul]
        · rw [if_neg hx]
      rw [hz, h0]
      simp
    · have hle : ‖rayDamp ψ (σ n) x‖ ≤ ‖rayDamp ψ 0 x‖ := by
        simp only [rayDamp, Set.indicator_apply]
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [if_pos hx, if_pos hx, norm_mul, norm_mul, norm_expRay, norm_expRay]
          simp only [Complex.ofReal_re]
          have hx0 : (0 : ℝ) < x := hx
          have h1 : Real.exp (-(σ n * x)) ≤ Real.exp (-(0 * x)) := by
            refine Real.exp_le_exp.2 ?_
            have : 0 ≤ σ n * x := mul_nonneg (hσ0 n) hx0.le
            simp only [zero_mul, neg_zero]
            linarith
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        · rw [if_neg hx, if_neg hx]
      have h2 : ‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ≤ 2 * ‖rayDamp ψ 0 x‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        linarith
      nlinarith [norm_nonneg (rayDamp ψ (σ n) x - rayDamp ψ 0 x), norm_nonneg (rayDamp ψ 0 x)]
  have hlim : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n : ℕ => ‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards with x
    have hpt : Tendsto (fun n : ℕ => rayDamp ψ (σ n) x) atTop (𝓝 (rayDamp ψ 0 x)) := by
      simp only [rayDamp, Set.indicator_apply]
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · simp only [if_pos hx]
        refine Tendsto.const_mul _ ?_
        have hc : Continuous fun s : ℝ => expRay ((s : ℝ) : ℂ) x := by
          unfold expRay
          fun_prop
        exact (hc.tendsto 0).comp hσ
      · simp only [if_neg hx]
        exact tendsto_const_nhds
    have hsub : Tendsto (fun n : ℕ => rayDamp ψ (σ n) x - rayDamp ψ 0 x) atTop
        (𝓝 (rayDamp ψ 0 x - rayDamp ψ 0 x)) :=
      hpt.sub (tendsto_const_nhds (x := rayDamp ψ 0 x))
    have hn := hsub.norm
    simpa using (hn.pow 2)
  have := tendsto_integral_of_dominated_convergence
    (F := fun n : ℕ => fun x : ℝ => ‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ^ 2)
    (f := fun _ : ℝ => (0 : ℝ)) (bound := fun x : ℝ => 4 * ‖rayDamp ψ 0 x‖ ^ 2)
    hmeas (hsq.const_mul 4) hbound hlim
  simpa using this

/-- Convergence of the `L²` classes follows from convergence of the squared `L²` distances. -/
theorem tendsto_toLp_of_integral_norm_sq {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (h : Tendsto (fun n : ℕ => ∫ x : ℝ, ‖f n x - g x‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hnorm : ∀ n : ℕ, ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2
      = ∫ x : ℝ, ‖f n x - g x‖ ^ 2 := by
    intro n
    rw [← MemLp.toLp_sub, _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp ((hf n).sub hg)] with x hx
    rw [hx]
    rfl
  have hsq : Tendsto (fun n : ℕ => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) :=
    h.congr fun n => (hnorm n).symm
  have hcomp : Tendsto (fun n : ℕ => Real.sqrt (‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Real.sqrt_sq (norm_nonneg _)] using hcomp

theorem tendsto_toLp_rayDamp {ψ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℕ → ℝ} (hσ0 : ∀ n, 0 ≤ σ n) (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (memLp_two_rayDamp hψ (hσ0 n)).toLp (rayDamp ψ (σ n))) atTop
      (𝓝 ((memLp_two_rayDamp hψ le_rfl).toLp (rayDamp ψ 0))) :=
  tendsto_toLp_of_integral_norm_sq (fun n => memLp_two_rayDamp hψ (hσ0 n))
    (memLp_two_rayDamp hψ le_rfl) (tendsto_integral_norm_sq_rayDamp_sub hψ hσ0 hσ)

theorem tendsto_toLp_rayDampRefl {ψ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℕ → ℝ} (hσ0 : ∀ n, 0 ≤ σ n) (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (memLp_two_rayDampRefl hψ (hσ0 n)).toLp (rayDampRefl ψ (σ n))) atTop
      (𝓝 ((memLp_two_rayDampRefl hψ le_rfl).toLp (rayDampRefl ψ 0))) := by
  refine tendsto_toLp_of_integral_norm_sq (fun n => memLp_two_rayDampRefl hψ (hσ0 n))
    (memLp_two_rayDampRefl hψ le_rfl) ?_
  refine (tendsto_integral_norm_sq_rayDamp_sub hψ hσ0 hσ).congr fun n => ?_
  exact (integral_neg_eq_self
    (fun x : ℝ => ‖rayDamp ψ (σ n) x - rayDamp ψ 0 x‖ ^ 2) volume).symm

/-! ## The vanishing theorem -/

/-- **A function that is a half-line Laplace transform on both sides of the imaginary axis
vanishes.**  Only continuity of `G` is used. -/
theorem eq_zero_of_two_sided_laplace {ψ₁ ψ₂ : ℝ → ℂ}
    (h₁ : MemLp ψ₁ 2 (volume.restrict (Ioi (0 : ℝ))))
    (h₂ : MemLp ψ₂ 2 (volume.restrict (Ioi (0 : ℝ))))
    {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ} (hG : ContinuousOn G {w : ℂ | |w.re| < r})
    (hright : ∀ w : ℂ, 0 < w.re → w.re < r → G w = laplaceRay ψ₁ w)
    (hleft : ∀ w : ℂ, -r < w.re → w.re < 0 → G w = laplaceRay ψ₂ (-w)) :
    (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ψ₁ x = 0) ∧
      (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ψ₂ x = 0) := by
  classical
  have hm0 : 0 < min r 1 := lt_min hr one_pos
  set σ : ℕ → ℝ := fun n => min r 1 / (n + 2 : ℝ) with hσdef
  have hσpos : ∀ n, 0 < σ n := by
    intro n
    rw [hσdef]
    have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact div_pos hm0 hd
  have hσ0 : ∀ n, 0 ≤ σ n := fun n => (hσpos n).le
  have hσlt : ∀ n, σ n < r := by
    intro n
    rw [hσdef]
    have hd : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have h1 : min r 1 / ((n : ℝ) + 2) ≤ min r 1 / 2 := by
      refine div_le_div_of_nonneg_left hm0.le (by norm_num) hd
    have h2 : min r 1 ≤ r := min_le_left _ _
    linarith
  have hσlim : Tendsto σ atTop (𝓝 0) := by
    rw [hσdef]
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hstripOpen : IsOpen {w : ℂ | |w.re| < r} := by
    have : {w : ℂ | |w.re| < r} = (fun w : ℂ => |w.re|) ⁻¹' (Set.Iio r) := rfl
    rw [this]
    exact (continuous_abs.comp Complex.continuous_re).isOpen_preimage _ isOpen_Iio
  have hrayCont : ∀ ξ : ℝ, Continuous fun s : ℝ => rayLine s ξ := by
    intro ξ
    unfold rayLine
    fun_prop
  -- the two families of data
  have hAF : ∀ n : ℕ, (((𝓕 ((memLp_two_rayDamp h₁ (hσ0 n)).toLp (rayDamp ψ₁ (σ n))) :
        Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => G (rayLine (σ n) ξ) := by
    intro n
    have hb := coeFn_fourierTransform_toLp (memLp_two_rayDamp h₁ (hσ0 n))
      (integrable_rayDamp h₁ (hσpos n))
    filter_upwards [hb] with ξ hξ
    rw [hξ, fourierIntegral_rayDamp]
    refine (hright _ ?_ ?_).symm
    · simpa using hσpos n
    · simpa using hσlt n
  have hBF : ∀ n : ℕ, (((𝓕 ((memLp_two_rayDampRefl h₂ (hσ0 n)).toLp (rayDampRefl ψ₂ (σ n))) :
        Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => G (rayLine (-(σ n)) ξ) := by
    intro n
    have hb := coeFn_fourierTransform_toLp (memLp_two_rayDampRefl h₂ (hσ0 n))
      (integrable_rayDampRefl h₂ (hσpos n))
    filter_upwards [hb] with ξ hξ
    rw [hξ, fourierIntegral_rayDampRefl]
    have hlt : (rayLine (-(σ n)) ξ).re < 0 := by
      simp only [rayLine_re]
      linarith [hσpos n]
    have hgt : -r < (rayLine (-(σ n)) ξ).re := by
      simp only [rayLine_re]
      linarith [hσlt n]
    rw [hleft _ hgt hlt]
    congr 1
    rw [rayLine, rayLine]
    push_cast
    ring
  -- limits of the `L²` classes
  have hlimA := tendsto_toLp_rayDamp h₁ hσ0 hσlim
  have hlimB := tendsto_toLp_rayDampRefl h₂ hσ0 hσlim
  have hFA : Tendsto (fun n : ℕ =>
      (𝓕 ((memLp_two_rayDamp h₁ (hσ0 n)).toLp (rayDamp ψ₁ (σ n))) :
        Lp ℂ 2 (volume : Measure ℝ))) atTop
      (𝓝 (𝓕 ((memLp_two_rayDamp h₁ le_rfl).toLp (rayDamp ψ₁ 0)))) :=
    ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto _).comp hlimA
  have hFB : Tendsto (fun n : ℕ =>
      (𝓕 ((memLp_two_rayDampRefl h₂ (hσ0 n)).toLp (rayDampRefl ψ₂ (σ n))) :
        Lp ℂ 2 (volume : Measure ℝ))) atTop
      (𝓝 (𝓕 ((memLp_two_rayDampRefl h₂ le_rfl).toLp (rayDampRefl ψ₂ 0)))) :=
    ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto _).comp hlimB
  -- the boundary values
  have hA0 : (((𝓕 ((memLp_two_rayDamp h₁ le_rfl).toLp (rayDamp ψ₁ 0)) :
        Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => G (rayLine 0 ξ) := by
    obtain ⟨ns, hns, hae⟩ :=
      (tendstoInMeasure_of_tendsto_Lp hFA).exists_seq_tendsto_ae
    have hall : ∀ᵐ ξ ∂(volume : Measure ℝ), ∀ i : ℕ,
        (((𝓕 ((memLp_two_rayDamp h₁ (hσ0 (ns i))).toLp (rayDamp ψ₁ (σ (ns i)))) :
          Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ = G (rayLine (σ (ns i)) ξ) :=
      ae_all_iff.2 fun i => hAF (ns i)
    filter_upwards [hae, hall] with ξ hξ hallξ
    have hcont : Tendsto (fun i : ℕ => G (rayLine (σ (ns i)) ξ)) atTop (𝓝 (G (rayLine 0 ξ))) := by
      have h1 : Tendsto (fun i : ℕ => σ (ns i)) atTop (𝓝 0) :=
        hσlim.comp hns.tendsto_atTop
      have hmem : rayLine 0 ξ ∈ {w : ℂ | |w.re| < r} := by
        simp only [Set.mem_setOf_eq, rayLine_re, abs_zero]
        exact hr
      have hca : ContinuousAt G (rayLine 0 ξ) :=
        hG.continuousAt (hstripOpen.mem_nhds hmem)
      exact hca.tendsto.comp (((hrayCont ξ).tendsto 0).comp h1)
    have hrw : (fun i : ℕ =>
        (((𝓕 ((memLp_two_rayDamp h₁ (hσ0 (ns i))).toLp (rayDamp ψ₁ (σ (ns i)))) :
          Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ)
        = fun i : ℕ => G (rayLine (σ (ns i)) ξ) := funext fun i => hallξ i
    rw [hrw] at hξ
    exact tendsto_nhds_unique hξ hcont
  have hB0 : (((𝓕 ((memLp_two_rayDampRefl h₂ le_rfl).toLp (rayDampRefl ψ₂ 0)) :
        Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => G (rayLine 0 ξ) := by
    obtain ⟨ns, hns, hae⟩ :=
      (tendstoInMeasure_of_tendsto_Lp hFB).exists_seq_tendsto_ae
    have hall : ∀ᵐ ξ ∂(volume : Measure ℝ), ∀ i : ℕ,
        (((𝓕 ((memLp_two_rayDampRefl h₂ (hσ0 (ns i))).toLp (rayDampRefl ψ₂ (σ (ns i)))) :
          Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ = G (rayLine (-(σ (ns i))) ξ) :=
      ae_all_iff.2 fun i => hBF (ns i)
    filter_upwards [hae, hall] with ξ hξ hallξ
    have hcont : Tendsto (fun i : ℕ => G (rayLine (-(σ (ns i))) ξ)) atTop
        (𝓝 (G (rayLine 0 ξ))) := by
      have h1 : Tendsto (fun i : ℕ => -(σ (ns i))) atTop (𝓝 (-0)) :=
        (hσlim.comp hns.tendsto_atTop).neg
      rw [neg_zero] at h1
      have hmem : rayLine 0 ξ ∈ {w : ℂ | |w.re| < r} := by
        simp only [Set.mem_setOf_eq, rayLine_re, abs_zero]
        exact hr
      have hca : ContinuousAt G (rayLine 0 ξ) :=
        hG.continuousAt (hstripOpen.mem_nhds hmem)
      exact hca.tendsto.comp (((hrayCont ξ).tendsto 0).comp h1)
    have hrw : (fun i : ℕ =>
        (((𝓕 ((memLp_two_rayDampRefl h₂ (hσ0 (ns i))).toLp (rayDampRefl ψ₂ (σ (ns i)))) :
          Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ)
        = fun i : ℕ => G (rayLine (-(σ (ns i))) ξ) := funext fun i => hallξ i
    rw [hrw] at hξ
    exact tendsto_nhds_unique hξ hcont
  -- the two data have the same Fourier transform
  have hFeq : (𝓕 ((memLp_two_rayDamp h₁ le_rfl).toLp (rayDamp ψ₁ 0)) :
        Lp ℂ 2 (volume : Measure ℝ))
      = 𝓕 ((memLp_two_rayDampRefl h₂ le_rfl).toLp (rayDampRefl ψ₂ 0)) :=
    Lp.ext (hA0.trans hB0.symm)
  have hEq : ((memLp_two_rayDamp h₁ le_rfl).toLp (rayDamp ψ₁ 0) :
        Lp ℂ 2 (volume : Measure ℝ))
      = (memLp_two_rayDampRefl h₂ le_rfl).toLp (rayDampRefl ψ₂ 0) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).injective hFeq
  have hAB : rayDamp ψ₁ 0 =ᵐ[volume] rayDampRefl ψ₂ 0 := by
    have h1 := (memLp_two_rayDamp h₁ (le_refl (0 : ℝ))).coeFn_toLp
    have h2 := (memLp_two_rayDampRefl h₂ (le_refl (0 : ℝ))).coeFn_toLp
    have := hEq ▸ h1
    exact (this.symm.trans h2)
  -- disjoint supports
  have hexp1 : ∀ x : ℝ, expRay ((0 : ℝ) : ℂ) x = 1 := by
    intro x
    unfold expRay
    norm_num
  constructor
  · filter_upwards [ae_restrict_of_ae hAB, self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))]
      with x hx hmem
    have hx0 : (0 : ℝ) < x := hmem
    have hr : rayDampRefl ψ₂ 0 x = 0 := by
      simp only [rayDampRefl, rayDamp, Set.indicator_apply]
      rw [if_neg (by simp; linarith)]
    have hl : rayDamp ψ₁ 0 x = ψ₁ x := by
      simp only [rayDamp, Set.indicator_apply]
      rw [if_pos hmem, hexp1, mul_one]
    rw [hl, hr] at hx
    exact hx
  · have hABneg : ∀ᵐ x ∂(volume : Measure ℝ),
        rayDamp ψ₁ 0 (-x) = rayDampRefl ψ₂ 0 (-x) :=
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving).ae hAB
    filter_upwards [ae_restrict_of_ae hABneg,
      self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with u hu hmem
    have hu0 : (0 : ℝ) < u := hmem
    have hl : rayDamp ψ₁ 0 (-u) = 0 := by
      simp only [rayDamp, Set.indicator_apply]
      rw [if_neg (by simp; linarith)]
    have hr : rayDampRefl ψ₂ 0 (-u) = ψ₂ u := by
      simp only [rayDampRefl, rayDamp, Set.indicator_apply, neg_neg]
      rw [if_pos hmem, hexp1, mul_one]
    rw [hl, hr] at hu
    exact hu.symm


end

end GaloisForLFunctions.HTGeometry
