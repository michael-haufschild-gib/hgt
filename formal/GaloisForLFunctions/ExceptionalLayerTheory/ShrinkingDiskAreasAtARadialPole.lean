import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real

/-!
# Area of a high reading in a shrinking disk

If distance times a scalar reading tends to C at a puncture, its level u
occupies, to first order, a disk of radius C/u. A receiver of radius a/u
therefore records precisely the smaller of the two disk areas. Irregular
measurability or oscillation of the reading does not affect the bound.
-/

noncomputable section
open Complex Filter Set Metric MeasureTheory Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Punctured aperture of radius a/u on which the reading exceeds u. -/
def radialLevelWindow (f : ℂ → ℝ) (ρ : ℂ) (a u : ℝ) :=
  {z | z∈ball ρ (a/u) ∧ z≠ρ ∧ u<f z}

private theorem scaled_ball_area (ρ : ℂ) {p u : ℝ} (hp : 0≤p) (hu : 0<u) :
    u^2*volume.real (ball ρ (p/u))=Real.pi*p^2 := by
  simp only [Measure.real,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.coe_toReal,NNReal.coe_real_pi,ENNReal.toReal_ofReal (div_nonneg hp hu.le)]
  field_simp

private theorem window_brackets {f : ℂ → ℝ} {ρ : ℂ} {a C : ℝ} (ha : 0≤a) (hC : 0≤C)
    (hf : Tendsto (fun z => dist z ρ*f z) (𝓝[≠] ρ) (𝓝 C)) {e : ℝ} (he : 0<e) :
    ∀ᶠ u : ℝ in atTop,
      Real.pi*(min a (max 0 (C-e)))^2 ≤ u^2*volume.real (radialLevelWindow f ρ a u) ∧
      u^2*volume.real (radialLevelWindow f ρ a u) ≤ Real.pi*(min a (C+e))^2 := by
  have h := hf.eventually (Ioo_mem_nhds (by linarith only [he] : C-e<C)
    (by linarith only [he] : C<C+e))
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h with ⟨U,hU,hlocal⟩
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop (a/d)] with u hu hut
  have had : a/u<d := (div_lt_iff₀ hu).mpr (by
    have h' := (div_lt_iff₀ hd).mp hut
    linarith only [h'])
  let p := min a (max 0 (C-e))
  let q := min a (C+e)
  have hp : 0≤p := le_min ha (le_max_left ..)
  have hq : 0≤q := le_min ha (add_nonneg hC he.le)
  have hat {z : ℂ} (hz : z∈ball ρ (a/u)) (hn : z≠ρ) :
      C-e<dist z ρ*f z ∧ dist z ρ*f z<C+e :=
    hlocal ⟨hdU ((ball_subset_ball had.le) hz),hn⟩
  have low : ball ρ (p/u) \ {ρ} ⊆ radialLevelWindow f ρ a u := by
    rintro z ⟨hz,hn⟩
    have hball := (ball_subset_ball (div_le_div_of_nonneg_right (min_le_left .. : p≤a) hu.le)) hz
    have h₁ := (lt_div_iff₀ hu).mp (mem_ball.mp hz)
    have hdp : 0<dist z ρ := dist_pos.mpr hn
    have hp' := (mul_pos hdp hu).trans h₁
    have hmax : 0<max 0 (C-e) := hp'.trans_le (min_le_right ..)
    have hcen : 0<C-e := (lt_max_iff.mp hmax).resolve_left (lt_irrefl _)
    have hpc : p≤C-e := by
      dsimp only [p]; rw [max_eq_right hcen.le]; exact min_le_right ..
    exact ⟨hball,hn,(mul_lt_mul_iff_right₀ hdp).mp
      ((h₁.trans_le hpc).trans (hat hball hn).1)⟩
  have high : radialLevelWindow f ρ a u ⊆ ball ρ (q/u) := by
    rintro z ⟨hz,hn,hread⟩
    have hdpos := dist_pos.mpr hn
    apply (lt_div_iff₀ hu).mpr
    exact lt_min ((lt_div_iff₀ hu).mp (mem_ball.mp hz))
      ((mul_lt_mul_of_pos_left hread hdpos).trans (hat hz hn).2)
  have hfinit : volume (radialLevelWindow f ρ a u)≠⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (μ:=volume) (x:=ρ) (r:=q/u)).ne (measure_mono high)
  have hlo := measureReal_mono low hfinit
  have hnull : volume ({ρ} : Set ℂ) = 0 := by
    simpa only [Metric.closedBall_zero, ENNReal.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul] using Complex.volume_closedBall ρ 0
  have harea : volume.real (ball ρ (p/u) \ {ρ}) = volume.real (ball ρ (p/u)) := by
    simp only [Measure.real, measure_sdiff_null hnull]
  rw [harea] at hlo
  exact ⟨(scaled_ball_area ρ hp hu).symm.le.trans
      (mul_le_mul_of_nonneg_left hlo (sq_nonneg _)),
    (mul_le_mul_of_nonneg_left (measureReal_mono high measure_ball_lt_top.ne)
      (sq_nonneg _)).trans_eq (scaled_ball_area ρ hq hu)⟩

/-- The scaled area in every fixed aperture has the complete clipped
profile π min(a,C)², including the transition a=C and the zero residue. -/
theorem radial_level_area_profile {f : ℂ → ℝ} {ρ : ℂ} {C : ℝ} (hC : 0≤C)
    (hf : Tendsto (fun z => dist z ρ*f z) (𝓝[≠] ρ) (𝓝 C)) {a : ℝ} (ha : 0≤a) :
    Tendsto (fun u : ℝ => u^2*volume.real (radialLevelWindow f ρ a u))
      atTop (𝓝 (Real.pi*(min a C)^2)) := by
  have hneg : Continuous (fun e : ℝ => Real.pi*(min a (max 0 (C-e)))^2) := by fun_prop
  have hpos : Continuous (fun e : ℝ => Real.pi*(min a (C+e))^2) := by fun_prop
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have h := (hneg.continuousAt (x:=0)).eventually_const_lt
      (by simpa only [sub_zero,max_eq_right hC] using hb)
    obtain ⟨e,hev,he⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] 0, 0<e)).exists
    exact (window_brackets ha hC hf he).mono fun _ hh => hev.trans_le hh.1
  · intro b hb
    have h := (hpos.continuousAt (x:=0)).eventually_lt_const
      (by simpa only [add_zero] using hb)
    obtain ⟨e,hev,he⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] 0, 0<e)).exists
    exact (window_brackets ha hC hf he).mono fun _ hh => hh.2.trans_lt hev

#print axioms radial_level_area_profile

/-- A fixed sufficiently small observation disk captures the entire
limiting area πC². All its high readings eventually fit inside the
shrinking aperture of radius (C+1)/u. -/
theorem fixed_disk_radial_level_area {f : ℂ → ℝ} {ρ : ℂ} {C : ℝ} (hC : 0≤C)
    (hf : Tendsto (fun z => dist z ρ*f z) (𝓝[≠] ρ) (𝓝 C)) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, 0<s → s ≤ r →
      Tendsto (fun u : ℝ => u^2*volume.real {z | z∈ball ρ s ∧ u<f z}) atTop
        (𝓝 (Real.pi*C^2)) := by
  have hu := hf.eventually_lt_const (lt_add_one C)
  obtain ⟨U,hU,hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r,hr,?_⟩
  intro s hs hsr
  have h := radial_level_area_profile hC hf (a:=C+1) (by linarith only [hC])
  rw [min_eq_right (le_add_of_nonneg_right zero_le_one)] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (f ρ),eventually_gt_atTop (0:ℝ),
    eventually_gt_atTop ((C+1)/s)] with u hu₀ hup hus
  have hfit : (C+1)/u < s := (div_lt_iff₀ hup).mpr (by
    have h' := (div_lt_iff₀ hs).mp hus
    linarith only [h'])
  have he : radialLevelWindow f ρ (C+1) u = {z | z∈ball ρ s ∧ u<f z} := by
    ext z
    constructor
    · rintro ⟨hz,_,hread⟩
      exact ⟨ball_subset_ball hfit.le hz,hread⟩
    · rintro ⟨hz,hread⟩
      have hn : z≠ρ := fun he => by subst z; exact hu₀.not_ge hread.le
      have hloc : dist z ρ*f z < C+1 := hsub ⟨hball (ball_subset_ball hsr hz),hn⟩
      exact ⟨(lt_div_iff₀ hup).mpr
        ((mul_lt_mul_of_pos_left hread (dist_pos.mpr hn)).trans hloc),hn,hread⟩
  rw [he]

#print axioms fixed_disk_radial_level_area
end GaloisForLFunctions.ExceptionalLayerTheory
