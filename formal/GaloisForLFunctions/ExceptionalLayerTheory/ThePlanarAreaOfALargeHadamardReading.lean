import GaloisForLFunctions.ExceptionalLayerTheory.RecoveringZeroMultiplicityFromParabolicHadamardReadings
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real

/-!
# The area of a large negative Hadamard reading

Near a point of order m the logarithmic derivative of ξ is a simple
pole of residue m plus a bounded function. The real part of the pole
falls below −L precisely inside a disk tangent to the marked point.
Two such disks bound the measured set and give the local area law
πm²/(4L²), with coefficient zero at regular points.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.BacklundConverse
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Observation region of radius s with real reading below −L. -/
def hadamardLevelPatch (ρ : ℂ) (s L : ℝ) : Set ℂ :=
  {z | z ∈ ball ρ s ∧ (logDeriv xi z).re < -L}

private def poleDisk (ρ : ℂ) (m b : ℝ) : Set ℂ :=
  ball (ρ-(m/(2*b):ℝ)) (m/(2*b))

private theorem disk_iff (ρ z : ℂ) {m b : ℝ} (hm : 0 ≤ m) (hb : 0<b) :
    z ∈ poleDisk ρ m b ↔ ((m:ℂ)/(z-ρ)).re < -b := by
  let a := m/(2*b)
  let w := z-ρ
  have ha : 0≤a := div_nonneg hm (by positivity)
  have hba : 2*b*a=m := by dsimp only [a]; field_simp
  have heq : z-(ρ-(a:ℂ))=w+a := by dsimp only [w]; ring
  change dist z (ρ-(a:ℂ))<a ↔ ((m:ℂ)/w).re < -b
  rw [dist_eq_norm,heq,←sq_lt_sq₀ (norm_nonneg _) ha,←Complex.normSq_eq_norm_sq]
  by_cases he : w=0
  · simp only [he,zero_add,div_zero,Complex.zero_re]
    rw [Complex.normSq_apply]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,add_zero]
    constructor <;> intro h <;> linarith only [h,hb,sq_nonneg a]
  · have hw := Complex.normSq_pos.mpr he
    rw [Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,
      div_lt_iff₀ hw]
    have diff : b*(Complex.normSq (w+a)-a^2)=m*w.re+b*Complex.normSq w := by
      rw [←hba,Complex.normSq_apply,Complex.normSq_apply]
      simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,add_zero]
      ring
    constructor
    · intro hs
      have hn := mul_neg_of_pos_of_neg hb (sub_neg.mpr hs)
      rw [diff] at hn
      linarith only [hn]
    · intro hs
      have hn : b*(Complex.normSq (w+a)-a^2)<0 := by rw [diff]; linarith only [hs]
      apply sub_neg.mp
      apply (mul_lt_mul_iff_right₀ hb).mp
      simpa only [mul_zero] using hn

private theorem disk_fits {ρ : ℂ} {m b s : ℝ} (hm : 0 ≤ m) (hb : 0<b)
    (hf : m/b ≤ s) : poleDisk ρ m b ⊆ ball ρ s := by
  let a := m/(2*b)
  have ha : 0≤a := div_nonneg hm (by positivity)
  have hc : dist (ρ-(a:ℂ)) ρ=a := by
    rw [dist_eq_norm,show ρ-(a:ℂ)-ρ= -(a:ℂ) by abel,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg ha]
  intro z hz
  have h := dist_triangle z (ρ-(a:ℂ)) ρ
  rw [hc] at h
  change dist z (ρ-(a:ℂ))<a at hz
  have he : a+a=m/b := by dsimp only [a]; ring
  exact (h.trans_lt (add_lt_add_of_lt_of_le hz (le_refl a))).trans_le (he.le.trans hf)

private theorem disk_area (ρ : ℂ) {m b : ℝ} (hm : 0 ≤ m) (hb : 0<b) :
    volume.real (poleDisk ρ m b)=(m/(2*b))^2*Real.pi := by
  have ha : 0 ≤ m/(2*b) := div_nonneg hm (mul_nonneg (by norm_num) hb.le)
  simp only [Measure.real,poleDisk,Complex.volume_ball,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal ha,
    ENNReal.coe_toReal,NNReal.coe_real_pi]

private theorem shifted_disk_limit (m c : ℝ) :
    Tendsto (fun L : ℝ => L^2*((m/(2*(L+c)))^2*Real.pi)) atTop (𝓝 (Real.pi*m^2/4)) := by
  have ht := (tendsto_const_nhds (x:=c)).div_atTop (tendsto_id (α:=ℝ))
  have hd := (tendsto_const_nhds (x:=(1:ℝ))).add ht
  rw [add_zero] at hd
  have h := (((tendsto_const_nhds (x:=m/2)).div hd one_ne_zero).pow 2).mul_const Real.pi
  rw [div_one,show (m/2)^2*Real.pi=Real.pi*m^2/4 by ring] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop (-c)] with L hL hc
  have hLc : L+c≠0 := ne_of_gt (by linarith only [hc])
  change ((m/2)/(1+c/L))^2*Real.pi = _
  rw [show 1+c/L=(L+c)/L by field_simp]
  field_simp [hL.ne',hLc]

/-- At every marked point all sufficiently small fixed observation disks
recover the squared zero multiplicity from large negative readings. -/
theorem local_hadamard_level_area (ρ : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, 0<s → s ≤ r →
      Tendsto (fun L : ℝ => L^2*volume.real (hadamardLevelPatch ρ s L)) atTop
        (𝓝 (Real.pi*((analyticOrderAt xi ρ).toNat:ℝ)^2/4)) := by
  obtain ⟨r,hr,K,hK,hbound⟩ := local_hadamard_principal_part_bound ρ
  let m : ℝ := hadamardOrder ρ
  have hm : 0 ≤ m := Nat.cast_nonneg _
  refine ⟨r,hr,?_⟩
  intro s hs hsr
  have hbd {z : ℂ} (hz : z∈ball ρ s) :
      |(logDeriv xi z).re-((m:ℂ)/(z-ρ)).re|≤K :=
    hbound z (ball_subset_ball hsr hz)
  have sandwich : ∀ᶠ L : ℝ in atTop,
      poleDisk ρ m (L+K) ⊆ hadamardLevelPatch ρ s L ∧
      hadamardLevelPatch ρ s L ⊆ poleDisk ρ m (L-K) := by
    filter_upwards [eventually_gt_atTop K,eventually_gt_atTop (m/s)] with L hLK hLs
    have hL := hK.trans_lt hLK
    have hp := add_pos_of_pos_of_nonneg hL hK
    have hn := sub_pos.mpr hLK
    have fit : m/(L+K) ≤ s := by
      apply (div_le_iff₀ hp).mpr
      have h := (div_lt_iff₀ hs).mp hLs
      linarith only [h,mul_nonneg hs.le hK]
    constructor
    · intro z hz
      have hball := disk_fits hm hp fit hz
      have hpole := (disk_iff ρ z hm hp).mp hz
      exact ⟨hball,by linarith only [hpole,(abs_le.mp (hbd hball)).2]⟩
    · rintro z ⟨hball,hlev⟩
      apply (disk_iff ρ z hm hn).mpr
      linarith only [hlev,(abs_le.mp (hbd hball)).1]
  have lower := shifted_disk_limit m K
  have upper := shifted_disk_limit m (-K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  · filter_upwards [sandwich,eventually_gt_atTop K] with L h hL
    rw [←disk_area ρ hm (add_pos_of_pos_of_nonneg (hK.trans_lt hL) hK)]
    have hfinite : volume (hadamardLevelPatch ρ s L) ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ball_lt_top.ne) (measure_mono fun _ h => h.1)
    exact mul_le_mul_of_nonneg_left (measureReal_mono h.1 hfinite) (sq_nonneg _)
  · filter_upwards [sandwich,eventually_gt_atTop K] with L h hL
    rw [←sub_eq_add_neg,←disk_area ρ hm (sub_pos.mpr hL)]
    exact mul_le_mul_of_nonneg_left (measureReal_mono h.2 (by
      unfold poleDisk; exact measure_ball_lt_top.ne)) (sq_nonneg _)

#print axioms local_hadamard_level_area
end GaloisForLFunctions.ExceptionalLayerTheory
