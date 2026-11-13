import GaloisForLFunctions.HTGeometry.DiskMultiplierInnerOuterFactor
import GaloisForLFunctions.HTGeometry.PoissonKernelBound
import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity
import GaloisForLFunctions.HTGeometry.SzegoWeightOuterMultiplier

/-!
# Local bounds for the canonical inner factor

A zero-free bounded multiplier has a nonnegative harmonic inner log defect.
Any local positive lower bound for the original multiplier bounds that defect,
using only the global bound of its canonical outer factor.
-/

noncomputable section
open Complex MeasureTheory Metric Set Filter Topology InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- The negative logarithm of the canonical inner factor's modulus. -/
def diskMultiplierInnerDefect (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) (z : ℂ) : ℝ :=
  -Real.log ‖(diskMultiplierInnerFactor φ hφ).fn z‖

theorem diskMultiplierInnerFactor_ne_zero (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : φ.fn z ≠ 0) :
    (diskMultiplierInnerFactor φ hφ).fn z ≠ 0 := by
  intro hzero
  have he := diskMultiplierInnerFactor_mul_outerFactor_fn φ hφ z hz
  rw [hzero, zero_mul] at he
  exact hne he.symm

/-- Contractivity of the inner factor gives a nonnegative defect. -/
theorem diskMultiplierInnerDefect_nonneg (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 ≤ diskMultiplierInnerDefect φ hφ z := by
  have hb := (diskMultiplierInnerFactor φ hφ).bd_le z hz
  rw [diskMultiplierInnerFactor_bd] at hb
  exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hb)

/-- Zero-freeness of the original multiplier makes the inner log defect harmonic. -/
theorem harmonicOnNhd_diskMultiplierInnerDefect (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    HarmonicOnNhd (diskMultiplierInnerDefect φ hφ) (ball (0 : ℂ) 1) := by
  have ha := (diskMultiplierInnerFactor φ hφ).diff.analyticOnNhd isOpen_ball
  exact (harmonicOnNhd_log_norm ha
    (fun z hz => diskMultiplierInnerFactor_ne_zero φ hφ hz (hne z hz))).neg

/-- The outer bound controls the inner defect wherever the product is nonzero. -/
theorem diskMultiplierInnerDefect_le_log_outer_bound (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : φ.fn z ≠ 0) :
    diskMultiplierInnerDefect φ hφ z ≤
      Real.log (diskMultiplierOuterFactor φ hφ).bd - Real.log ‖φ.fn z‖ := by
  have hi := diskMultiplierInnerFactor_ne_zero φ hφ hz hne
  have he := diskMultiplierInnerFactor_mul_outerFactor_fn φ hφ z hz
  have ho : (diskMultiplierOuterFactor φ hφ).fn z ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at he
    exact hne he.symm
  have hlog : Real.log ‖φ.fn z‖ =
      Real.log ‖(diskMultiplierInnerFactor φ hφ).fn z‖ +
        Real.log ‖(diskMultiplierOuterFactor φ hφ).fn z‖ := by
    rw [← he, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hi) (norm_ne_zero_iff.mpr ho)]
  have hb := Real.log_le_log (norm_pos_iff.mpr ho)
    ((diskMultiplierOuterFactor φ hφ).bd_le z hz)
  unfold diskMultiplierInnerDefect
  linarith only [hlog, hb]

/-- A local lower bound for the original multiplier bounds its harmonic inner defect. -/
theorem diskMultiplierInnerDefect_le_of_norm_lower_bound (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {m : ℝ} (hm : 0 < m)
    (hlower : m ≤ ‖φ.fn z‖) :
    diskMultiplierInnerDefect φ hφ z ≤
      Real.log (diskMultiplierOuterFactor φ hφ).bd - Real.log m := by
  have hne : φ.fn z ≠ 0 := norm_pos_iff.mp (hm.trans_le hlower)
  have hu := diskMultiplierInnerDefect_le_log_outer_bound φ hφ hz hne
  have hl := Real.log_le_log hm hlower
  linarith only [hu, hl]

/-- Along one cofinal radial subsequence the inner defect tends to zero almost
everywhere on the circle. -/
theorem exists_diskMultiplierInnerDefect_radial_subseq_ae (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ (ζ : Circle) ∂circleLebesgue,
        Tendsto (fun i => diskMultiplierInnerDefect φ hφ
          ((hardyDiskAbelRadius (ns i) : ℂ) * (ζ : ℂ))) atTop (𝓝 0) := by
  obtain ⟨ns, hns, hae⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae (diskMultiplierInnerFactor φ hφ)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, ae_norm_diskMultiplierInnerFactor_boundary_eq_one φ hφ]
    with ζ hζ hb
  have hn : Tendsto
      (fun i => ‖diskMultiplierRadialBoundaryFun (ns i)
        (diskMultiplierInnerFactor φ hφ) ζ‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hb] using hζ.norm
  have hl := ((Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hn).neg
  simpa only [Real.log_one, neg_zero, diskMultiplierRadialBoundaryFun,
    diskMultiplierInnerDefect, Function.comp_apply] using hl

/-- Circle-null exceptional sets pull back to null sets on the entire angular line. -/
theorem ae_angularCircle_of_ae_circle_all {P : Circle → Prop}
    (hP : ∀ᵐ ζ ∂circleLebesgue, P ζ) :
    ∀ᵐ θ ∂volume, P (angularCircle θ) := by
  have hbase := ae_angularCircle_of_ae_circle hP
  have hshift (k : ℤ) : ∀ᵐ θ ∂volume,
      θ - (k : ℝ) * (2 * Real.pi) ∈ Ioc 0 (2 * Real.pi) →
        P (angularCircle (θ - (k : ℝ) * (2 * Real.pi))) :=
    (measurePreserving_sub_right volume ((k : ℝ) * (2 * Real.pi))).quasiMeasurePreserving.ae hbase
  filter_upwards [ae_all_iff.mpr hshift] with θ hθ
  let k : ℤ := ⌈θ / (2 * Real.pi)⌉ - 1
  have hk : (k : ℝ) < θ / (2 * Real.pi) ∧
      θ / (2 * Real.pi) ≤ (k : ℝ) + 1 := by
    dsimp only [k]
    push_cast
    constructor
    · linarith only [Int.ceil_lt_add_one (θ / (2 * Real.pi))]
    · simpa only [sub_add_cancel] using Int.le_ceil (θ / (2 * Real.pi))
  have hmem : θ - (k : ℝ) * (2 * Real.pi) ∈ Ioc 0 (2 * Real.pi) := by
    have hl := (lt_div_iff₀ Real.two_pi_pos).mp hk.1
    have hu := (div_le_iff₀ Real.two_pi_pos).mp hk.2
    constructor <;> linarith only [hl, hu]
  have he : angularCircle (θ - (k : ℝ) * (2 * Real.pi)) = angularCircle θ := by
    have hh := angularCircle_periodic.int_mul k (θ - (k : ℝ) * (2 * Real.pi))
    simpa only [sub_add_cancel] using hh.symm
  rw [← he]
  exact hθ k hmem

/-- The same radial subsequence converges for almost every angle. -/
theorem exists_diskMultiplierInnerDefect_angular_subseq_ae (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ θ ∂volume,
        Tendsto (fun i => diskMultiplierInnerDefect φ hφ
          (circleMap 0 (hardyDiskAbelRadius (ns i)) θ)) atTop (𝓝 0) := by
  obtain ⟨ns, hns, hae⟩ := exists_diskMultiplierInnerDefect_radial_subseq_ae φ hφ
  refine ⟨ns, hns, ?_⟩
  have hang := ae_angularCircle_of_ae_circle_all hae
  filter_upwards [hang] with θ hθ
  simpa only [coe_angularCircle, ← circleMap_zero_eq_mul] using hθ

/-- Nonvanishing and continuity on the punctured closed disk give a uniform positive
lower bound along every compact family of radii whose endpoints avoid the puncture. -/
theorem exists_pos_norm_lower_bound_on_radial_arc {f : ℂ → ℂ}
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1})
    (hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → f z ≠ 0)
    {α β : ℝ} (hαβ : α ≤ β)
    (harc : ∀ θ ∈ Icc α β, circleMap 0 1 θ ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∀ r ∈ Icc (0 : ℝ) 1, ∀ θ ∈ Icc α β,
      m ≤ ‖f (circleMap 0 r θ)‖ := by
  have hmem (p : ℝ × ℝ) (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc α β) :
      ‖circleMap 0 p.1 p.2‖ ≤ 1 ∧ circleMap 0 p.1 p.2 ≠ 1 := by
    have hn : ‖circleMap 0 p.1 p.2‖ = p.1 := by
      rw [norm_circleMap_zero, abs_of_nonneg hp.1.1]
    refine ⟨hn.trans_le hp.1.2, ?_⟩
    intro he
    have hr : p.1 = 1 := by simpa only [hn, norm_one] using congrArg norm he
    exact harc p.2 hp.2 (hr ▸ he)
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => ‖f (circleMap 0 p.1 p.2)‖)
      (Icc (0 : ℝ) 1 ×ˢ Icc α β) :=
    (hf.comp hc.continuousOn hmem).norm
  obtain ⟨p, hp, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ⟨(0, α), ⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hαβ⟩⟩ hcomp
  refine ⟨‖f (circleMap 0 p.1 p.2)‖,
    norm_pos_iff.mpr (hne _ (hmem p hp).1 (hmem p hp).2), ?_⟩
  intro r hr θ hθ
  exact (isMinOn_iff.mp hmin) (r, θ) ⟨hr, hθ⟩

#print axioms harmonicOnNhd_diskMultiplierInnerDefect
#print axioms exists_diskMultiplierInnerDefect_angular_subseq_ae
#print axioms exists_pos_norm_lower_bound_on_radial_arc

end GaloisForLFunctions.HTGeometry
