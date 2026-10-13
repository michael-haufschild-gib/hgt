import GaloisForLFunctions.HTGeometry.L2PhysicalMultiplierObservation
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm

/-! # Magnitude order is exactly observable for continuous multipliers

Norm comparisons on every physical history recover pointwise symbol-magnitude
comparisons. A positive-volume interval witnesses every strict violation.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem l2PhysicalObservation_le_of_ae_mul_norm_le
    (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (w v : α → ℂ)
    (hT : ∀ y, (T y : α → ℂ) =ᵐ[μ] fun t => w t * y t)
    (hS : ∀ y, (S y : α → ℂ) =ᵐ[μ] fun t => v t * y t)
    (h : ∀ᵐ t ∂μ, ‖w t‖ ≤ ‖v t‖) (x : Lp ℂ 2 μ) :
    l2PhysicalObservation T x ≤ l2PhysicalObservation S x := by
  rw [l2PhysicalObservation_eq_norm_of_ae_mul T w hT,
    l2PhysicalObservation_eq_norm_of_ae_mul S v hS]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hT x, hS x, h] with t htx hsx ht
  rw [htx, hsx, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

theorem l2PhysicalObservation_eq_of_ae_mul_norm_eq
    (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (w v : α → ℂ)
    (hT : ∀ y, (T y : α → ℂ) =ᵐ[μ] fun t => w t * y t)
    (hS : ∀ y, (S y : α → ℂ) =ᵐ[μ] fun t => v t * y t)
    (h : ∀ᵐ t ∂μ, ‖w t‖ = ‖v t‖) (x : Lp ℂ 2 μ) :
    l2PhysicalObservation T x = l2PhysicalObservation S x :=
  le_antisymm
    (l2PhysicalObservation_le_of_ae_mul_norm_le T S w v hT hS (h.mono fun _ ht => ht.le) x)
    (l2PhysicalObservation_le_of_ae_mul_norm_le S T v w hS hT (h.mono fun _ ht => ht.ge) x)

private abbrev H := Lp ℂ 2 (volume : Measure ℝ)

theorem norm_symbol_le_of_response_domination {T S : H →L[ℂ] H} {w v : ℝ → ℂ}
    (hw : Continuous w) (hv : Continuous v)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun t => w t * f t)
    (hS : ∀ f, (S f : ℝ → ℂ) =ᵐ[volume] fun t => v t * f t)
    (h : ∀ f, ‖T f‖ ≤ ‖S f‖) (x₀ : ℝ) : ‖w x₀‖ ≤ ‖v x₀‖ := by
  by_contra hbad
  obtain ⟨b, hvb, hbw⟩ := exists_between (lt_of_not_ge hbad)
  obtain ⟨a, hva, hab⟩ := exists_between hvb
  have ha : 0 < a := lt_of_le_of_lt (norm_nonneg _) hva
  have hb : 0 < b := ha.trans hab
  have he := ((hw.norm.tendsto x₀).eventually (eventually_gt_nhds hbw)).and
    ((hv.norm.tendsto x₀).eventually (eventually_lt_nhds hva))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hfin : volume (Metric.ball x₀ r) ≠ ∞ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top
  let f : H := indicatorConstLp 2 measurableSet_ball hfin (1 : ℂ)
  have hfpos : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
      measureReal_def, Real.volume_ball, ENNReal.toReal_ofReal (by positivity)]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hlo : ‖(b : ℂ) • f‖ ≤ ‖T f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul (b : ℂ) f, hT f,
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball) (hμs := hfin) (c := (1 : ℂ))]
      with y hsm hTy hfy
    rw [hsm, hTy, Pi.smul_apply, norm_smul, norm_mul]
    by_cases hy : y ∈ Metric.ball x₀ r
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
      exact mul_le_mul_of_nonneg_right (hball hy).1.le (norm_nonneg _)
    · change f y = _ at hfy
      rw [hfy, indicator_of_notMem hy]
      simp
  have hhi : ‖S f‖ ≤ ‖(a : ℂ) • f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hS f, Lp.coeFn_smul (a : ℂ) f,
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball) (hμs := hfin) (c := (1 : ℂ))]
      with y hSy hsm hfy
    rw [hSy, hsm, Pi.smul_apply, norm_smul, norm_mul]
    by_cases hy : y ∈ Metric.ball x₀ r
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_right (hball hy).2.le (norm_nonneg _)
    · change f y = _ at hfy
      rw [hfy, indicator_of_notMem hy]
      simp
  have hab' : b * ‖f‖ ≤ a * ‖f‖ := by
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb] using
      (hlo.trans (h f)).trans hhi
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hab hfpos)) hab'

theorem forall_l2PhysicalObservation_le_iff {T S : H →L[ℂ] H} {w v : ℝ → ℂ}
    (hw : Continuous w) (hv : Continuous v)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun t => w t * f t)
    (hS : ∀ f, (S f : ℝ → ℂ) =ᵐ[volume] fun t => v t * f t) :
    (∀ x, l2PhysicalObservation T x ≤ l2PhysicalObservation S x) ↔ ∀ t, ‖w t‖ ≤ ‖v t‖ := by
  constructor
  · intro h
    apply norm_symbol_le_of_response_domination hw hv hT hS
    intro x
    simpa only [l2PhysicalObservation_eq_norm_of_ae_mul T w hT,
      l2PhysicalObservation_eq_norm_of_ae_mul S v hS] using h x
  · intro h x
    exact l2PhysicalObservation_le_of_ae_mul_norm_le T S w v hT hS (Eventually.of_forall h) x

theorem forall_l2PhysicalObservation_eq_iff {T S : H →L[ℂ] H} {w v : ℝ → ℂ}
    (hw : Continuous w) (hv : Continuous v)
    (hT : ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun t => w t * f t)
    (hS : ∀ f, (S f : ℝ → ℂ) =ᵐ[volume] fun t => v t * f t) :
    (∀ x, l2PhysicalObservation T x = l2PhysicalObservation S x) ↔ ∀ t, ‖w t‖ = ‖v t‖ := by
  constructor
  · intro h t
    exact le_antisymm
      ((forall_l2PhysicalObservation_le_iff hw hv hT hS).mp (fun x => (h x).le) t)
      ((forall_l2PhysicalObservation_le_iff hv hw hS hT).mp (fun x => (h x).ge) t)
  · intro h x
    exact l2PhysicalObservation_eq_of_ae_mul_norm_eq T S w v hT hS (Eventually.of_forall h) x

end
end GaloisForLFunctions.HTGeometry
