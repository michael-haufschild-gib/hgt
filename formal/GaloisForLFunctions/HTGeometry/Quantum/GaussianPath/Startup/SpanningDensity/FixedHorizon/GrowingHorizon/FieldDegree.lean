import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.AnchoredSublevel

/-! # A geometric detection threshold on increasing time horizons -/
open MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- On horizon L, an entire response bounded by exp(2L|z|) and
calibrated at strength h^L retains a signal s^L off a set of measure δ.
The Taylor degree grows linearly in L. -/
theorem geometric_anchored_sublevel {b h δ : ℝ} (hb : 0<b) (hh : 0<h) (hδ : 0<δ) :
    ∃ s>0, ∀ L : ℕ, 0<L → ∀ f : ℂ→ℂ, Differentiable ℂ f → (∀ x : ℝ, (f x).im=0) →
      (∀ z : ℂ, ‖f z‖≤Real.exp (2*L*‖z‖)) → ∀ u : ℝ, |u|≤b → h^L≤|(f u).re| →
      volume.real {x ∈ Ioo (-b) b | |(f (x:ℂ)).re|≤ s^L} ≤ δ := by
  let q := releaseFactor b δ
  have hq : 0<q := by dsimp only [q,releaseFactor]; positivity
  let B := Real.exp (2*(2*q*b))
  have hB : 0<B := Real.exp_pos _
  obtain ⟨k,hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
    (eventually_gt_atTop (8*B/h))).exists
  refine ⟨h/(4*q^k),by positivity,?_⟩
  intro L hL f hf hr hg u hu hcal
  have h8 : (8:ℝ) ≤ 8^L := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤8) hL)
  have h4 : (4:ℝ) ≤ 4^L := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4) hL)
  let M (R : ℝ) := Real.exp (2*L*R)
  have he : M (2*q*b)=B^L := by
    change Real.exp (2*(L:ℝ)*(2*q*b))=(Real.exp (2*(2*q*b)))^L
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hd : 8*M (2*q*b)/h^L < 2^(k*L) := by
    rw [he,pow_mul]
    calc 8*B^L/h^L ≤ 8^L*B^L/h^L := by gcongr
         _ = (8*B/h)^L := by rw [div_pow,mul_pow]
         _ < ((2:ℝ)^k)^L := pow_lt_pow_left₀ hk (by positivity) hL.ne'
  have hs : (h/(4*q^k))^L ≤ h^L/(4*q^(k*L)) := by
    rw [div_pow,mul_pow,pow_mul]
    apply div_le_div_of_nonneg_left (pow_pos hh _).le (by positivity)
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hfin : volume {x ∈ Ioo (-b) b | |(f (x:ℂ)).re|≤h^L/(4*q^(k*L))}≠⊤ :=
    measure_ne_top_of_subset (fun x hx => hx.1 : {x ∈ Ioo (-b) b | |(f (x:ℂ)).re|≤_} ⊆ Ioo (-b) b) (by simp)
  have hsub : {x ∈ Ioo (-b) b | |(f (x:ℂ)).re| ≤ (h/(4*q^k))^L} ⊆
      {x ∈ Ioo (-b) b | |(f (x:ℂ)).re| ≤ h^L/(4*q^(k*L))} :=
    fun _ hx => ⟨hx.1,hx.2.trans hs⟩
  exact (measureReal_mono hsub hfin).trans
    (anchored_sublevel_at_degree hb (pow_pos hh _) hδ M (fun R => (Real.exp_pos _).le)
      (k*L) hd f hf hr hg u hu hcal)

#print axioms geometric_anchored_sublevel
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
