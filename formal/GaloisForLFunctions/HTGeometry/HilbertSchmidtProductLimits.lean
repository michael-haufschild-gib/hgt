import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity

/-!
# Products, traces and entire determinants along Hilbert--Schmidt limits

The filter formulation admits the net of all finite coordinate compressions,
so determinant multiplication does not require a countability assumption on
the chosen Hilbert basis.
-/

noncomputable section
open Filter Topology

namespace HilbertSchmidt

variable {ι κ : Type*}

theorem isHS_lp (K : lp (fun _ : ι × ι => ℂ) 2) : IsHS (fun p => K p) := by
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp K.property
  simpa [IsHS] using h

theorem tendsto_lp_of_hsNorm_sub {l : Filter κ}
    {K : κ → ι × ι → ℂ} {K₀ : ι × ι → ℂ}
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) l (𝓝 0)) :
    Tendsto (fun n => (⟨K n, (hK n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)) l
      (𝓝 ⟨K₀, hK₀.memℓp⟩) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (n : κ) :
      ‖(⟨K n, (hK n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2) - ⟨K₀, hK₀.memℓp⟩‖ =
        hsNorm (K n - K₀) := (hsNorm_eq_lp_norm (isHS_sub (hK n) hK₀)).symm
  simpa only [he] using hlim

theorem tendsto_hsInner_of_hsNorm_sub {l : Filter κ}
    {A B : κ → ι × ι → ℂ} {A₀ B₀ : ι × ι → ℂ}
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n)) (hA₀ : IsHS A₀) (hB₀ : IsHS B₀)
    (ha : Tendsto (fun n => hsNorm (A n - A₀)) l (𝓝 0))
    (hb : Tendsto (fun n => hsNorm (B n - B₀)) l (𝓝 0)) :
    Tendsto (fun n => hsInner (A n) (B n)) l (𝓝 (hsInner A₀ B₀)) := by
  have h := (tendsto_lp_of_hsNorm_sub hA hA₀ ha).inner (𝕜 := ℂ)
    (tendsto_lp_of_hsNorm_sub hB hB₀ hb)
  simp_rw [hsInner_eq_lp_inner (hA _) (hB _), hsInner_eq_lp_inner hA₀ hB₀]
  exact h

theorem hsNorm_hsComp_sub_le {A B C D : ι × ι → ℂ}
    (hA : IsHS A) (hB : IsHS B) (hC : IsHS C) (hD : IsHS D) :
    hsNorm (hsComp A B - hsComp C D) ≤
      hsNorm (A - C) * hsNorm B + hsNorm C * hsNorm (B - D) := by
  have he : hsComp A B - hsComp C D =
      hsComp (A - C) B + hsComp C (B - D) := by
    rw [hsComp_sub_left hA hC hB, hsComp_sub_right hC hB hD]
    abel
  rw [he]
  exact (hsNorm_add_le (isHS_hsComp (isHS_sub hA hC) hB)
    (isHS_hsComp hC (isHS_sub hB hD))).trans
      (add_le_add (hsNorm_hsComp_le (isHS_sub hA hC) hB)
        (hsNorm_hsComp_le hC (isHS_sub hB hD)))

theorem tendsto_hsNorm_hsComp_sub {l : Filter κ}
    {A B : κ → ι × ι → ℂ} {A₀ B₀ : ι × ι → ℂ}
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n)) (hA₀ : IsHS A₀) (hB₀ : IsHS B₀)
    (ha : Tendsto (fun n => hsNorm (A n - A₀)) l (𝓝 0))
    (hb : Tendsto (fun n => hsNorm (B n - B₀)) l (𝓝 0))
    {M : ℝ} (hM : ∀ n, hsNorm (B n) ≤ M) :
    Tendsto (fun n => hsNorm (hsComp (A n) (B n) - hsComp A₀ B₀)) l (𝓝 0) := by
  have hlim : Tendsto (fun n => hsNorm (A n - A₀) * M +
      hsNorm A₀ * hsNorm (B n - B₀)) l (𝓝 0) := by
    simpa using (ha.mul_const M).add (hb.const_mul (hsNorm A₀))
  refine squeeze_zero (fun n => hsNorm_nonneg _) (fun n => ?_) hlim
  exact (hsNorm_hsComp_sub_le (hA n) (hB n) hA₀ hB₀).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hM n) (hsNorm_nonneg _)) le_rfl)

theorem tendsto_hsNorm_add_sub {l : Filter κ}
    {A B : κ → ι × ι → ℂ} {A₀ B₀ : ι × ι → ℂ}
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n)) (hA₀ : IsHS A₀) (hB₀ : IsHS B₀)
    (ha : Tendsto (fun n => hsNorm (A n - A₀)) l (𝓝 0))
    (hb : Tendsto (fun n => hsNorm (B n - B₀)) l (𝓝 0)) :
    Tendsto (fun n => hsNorm ((A n + B n) - (A₀ + B₀))) l (𝓝 0) := by
  have hlim : Tendsto (fun n => hsNorm (A n - A₀) + hsNorm (B n - B₀)) l (𝓝 0) := by
    simpa using ha.add hb
  refine squeeze_zero (fun n => hsNorm_nonneg _) (fun n => ?_) hlim
  rw [show A n + B n - (A₀ + B₀) = (A n - A₀) + (B n - B₀) by abel]
  exact hsNorm_add_le (isHS_sub (hA n) hA₀) (isHS_sub (hB n) hB₀)

theorem tendsto_hsTrace_hsComp_of_hsNorm_sub {l : Filter κ}
    {A B : κ → ι × ι → ℂ} {A₀ B₀ : ι × ι → ℂ}
    (hA : ∀ n, IsHS (A n)) (hB : ∀ n, IsHS (B n)) (hA₀ : IsHS A₀) (hB₀ : IsHS B₀)
    (ha : Tendsto (fun n => hsNorm (A n - A₀)) l (𝓝 0))
    (hb : Tendsto (fun n => hsNorm (B n - B₀)) l (𝓝 0)) :
    Tendsto (fun n => ∑' i, hsComp (A n) (B n) (i, i)) l
      (𝓝 (∑' i, hsComp A₀ B₀ (i, i))) := by
  have he (n : κ) : hsAdjoint (A n) - hsAdjoint A₀ = hsAdjoint (A n - A₀) := by
    funext p
    simp [hsAdjoint]
  have ha' : Tendsto (fun n => hsNorm (hsAdjoint (A n) - hsAdjoint A₀)) l (𝓝 0) := by
    simpa only [he, hsNorm_hsAdjoint] using ha
  simp_rw [hsTrace_hsComp (hA _) (hB _), hsTrace_hsComp hA₀ hB₀]
  exact tendsto_hsInner_of_hsNorm_sub (fun n => isHS_hsAdjoint (hA n)) hB
    (isHS_hsAdjoint hA₀) hB₀ ha' hb

end HilbertSchmidt

namespace GaloisForLFunctions.HTGeometry
open HilbertSchmidt

variable {ι κ : Type*} [DecidableEq ι]

theorem continuous_entireDet2_lp (z : ℂ) :
    Continuous (fun K : lp (fun _ : ι × ι => ℂ) 2 => entireDet2 (fun p => K p) z) := by
  apply continuous_iff_seqContinuous.mpr
  intro K K₀ hK
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hK
  apply tendsto_entireDet2_of_hsNorm_sub_tendsto_zero
    (fun n p => K n p) (fun p => K₀ p) (fun n => isHS_lp (K n)) (isHS_lp K₀)
  have he (n : ℕ) : hsNorm ((fun p => K n p) - fun p => K₀ p) = ‖K n - K₀‖ :=
    hsNorm_eq_lp_norm (isHS_sub (isHS_lp (K n)) (isHS_lp K₀))
  simpa only [he] using hnorm

theorem tendsto_entireDet2_of_hsNorm_sub_filter {l : Filter κ}
    {K : κ → ι × ι → ℂ} {K₀ : ι × ι → ℂ}
    (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) l (𝓝 0)) (z : ℂ) :
    Tendsto (fun n => entireDet2 (K n) z) l (𝓝 (entireDet2 K₀ z)) := by
  have ht : Tendsto (fun n => (⟨K n, (hK n).memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)) l
      (𝓝 ⟨K₀, hK₀.memℓp⟩) := tendsto_lp_of_hsNorm_sub hK hK₀ hlim
  have hout := ((continuous_entireDet2_lp (ι := ι) z).tendsto
    (⟨K₀, hK₀.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)).comp ht
  simpa only [Function.comp_def] using hout

end GaloisForLFunctions.HTGeometry
