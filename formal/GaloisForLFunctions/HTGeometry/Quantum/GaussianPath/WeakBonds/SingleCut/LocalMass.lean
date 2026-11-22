import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.BoxMass

/-! # Gaussian cost of shrinking selected coordinates inside a fixed neighborhood -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
noncomputable section

/-- A rectangular neighborhood of a point whose cut components vanish
keeps a fixed positive bulk mass as the cut widths shrink like 1/T. -/
theorem gaussian_local_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x₀ : ι→ℝ) (hz : ∀ i∈S, x₀ i=0) {r : ℝ} (hr : 0 < r) :
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    ∃ c > (0:ℝ), ∀ T ≥ (1:ℝ), ∃ E : Set (ι→ℝ), MeasurableSet E ∧ c ≤ T^S.card*μ.real E ∧
      ∀ x∈E, (∀ i, |x i-x₀ i| < r) ∧ ∀ i∈S, |x i| ≤ 1/(1800*T) := by
  intro μ
  let γ := gaussianReal 0 1
  let b := min (r/2) (1/1800)
  have hb : 0 < b := lt_min (half_pos hr) (by norm_num)
  have hbr : b < r := (min_le_left ..).trans_lt (half_lt_self hr)
  have hb' : b ≤ 1/1800 := min_le_right .. 
  let bulk (i : ι) := Icc (x₀ i-b) (x₀ i+b)
  let P := ∏ i∈Sᶜ, γ.real (bulk i)
  have hp : 0 < P := Finset.prod_pos fun i _ =>
    ENNReal.toReal_pos (gaussianReal_Icc_pos (show x₀ i-b < x₀ i+b by linarith only [hb])).ne' (measure_ne_top _ _)
  let g := 2*gaussianDensityFloor
  have hg : 0 < g := mul_pos two_pos gaussianDensityFloor_pos
  refine ⟨(g*b)^S.card*P,mul_pos (pow_pos (mul_pos hg hb) _) hp,?_⟩
  intro T hT
  have ht := zero_lt_one.trans_le hT
  let δ := b/T
  let F (i : ι) := if i∈S then Icc (-δ) δ else bulk i
  let E := univ.pi F
  have hm : MeasurableSet E := MeasurableSet.pi (Set.to_countable _) (fun i _ => by
    dsimp only [F]; split <;> exact measurableSet_Icc)
  have hδ : 0 < δ := div_pos hb ht
  have hδb : δ ≤ b := div_le_self hb.le hT
  have hmass : μ.real E=γ.real (Icc (-δ) δ)^S.card*P := by
    change ((Measure.pi (fun _ : ι => γ)) (univ.pi F)).toReal=_
    rw [Measure.pi_pi,ENNReal.toReal_prod,←Finset.prod_mul_prod_compl S]
    congr 1
    · calc _ = ∏ _i∈S, γ.real (Icc (-δ) δ) := Finset.prod_congr rfl fun i hi => by simp only [F,if_pos hi,measureReal_def]
           _ = _ := Finset.prod_const _
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [F,if_neg (Finset.mem_compl.mp hi),measureReal_def]
  have hfloor := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ))
    (gaussianReal_Icc_lower (hδb.trans (hb'.trans (by norm_num))))
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (mul_nonneg (by norm_num) hδ.le))] at hfloor
  have hs : g*δ ≤ γ.real (Icc (-δ) δ) := (show g*δ=gaussianDensityFloor*(2*δ) by dsimp only [g]; ring).trans_le hfloor
  refine ⟨E,hm,?_,?_⟩
  · rw [hmass]
    calc _ = T^S.card*((g*δ)^S.card*P) := by rw [←mul_assoc,←mul_pow]; congr 2; dsimp only [δ]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_pos hg hδ).le hs _) hp.le) (pow_nonneg ht.le _)
  · intro x hx
    have hcut (i : ι) (hi : i∈S) : |x i| ≤ δ := abs_le.mpr (by simpa [F,hi] using hx i (mem_univ i))
    refine ⟨fun i => ?_,fun i hi => (hcut i hi).trans ?_⟩
    · by_cases hi : i∈S
      · rw [hz i hi,sub_zero]
        exact (hcut i hi).trans_lt (hδb.trans_lt hbr)
      · have h : x i∈bulk i := by simpa [F,hi] using hx i (mem_univ i)
        apply lt_of_le_of_lt _ hbr
        exact abs_le.mpr ⟨by linarith only [h.1],by linarith only [h.2]⟩
    · dsimp only [δ]
      rw [show 1/(1800*T)=(1/1800)/T by ring]
      exact div_le_div_of_nonneg_right hb' ht.le

#print axioms gaussian_local_box
end
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
