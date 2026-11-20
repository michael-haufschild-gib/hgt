import GaloisForLFunctions.ExceptionalLayerTheory.TheLogarithmicMassOfACriticalTail
import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Critical moments of the logarithmic derivatives of ξ

Clipping the critical power of the j-th derivative of ξ'/ξ at T leaves
a logarithmic divergence. After division by π log T its coefficient is
the sum of m^(2/(j+1)) over the interior zero orders. At j=1 it is the
winding of the observation circle.
-/
noncomputable section
open Complex Filter Metric MeasureTheory Set Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Squared normalized derivative root, whose weak-L¹ coefficient is
the fractional divisor moment times π. -/
def criticalXiDensity (j : ℕ) (z : ℂ) := (logDerivativeRoot xi j z)^2

private theorem measurable_density (j : ℕ) : Measurable (criticalXiDensity j) := by
  have hx : Meromorphic xi := fun z => (xi_differentiable.analyticAt z).meromorphicAt
  have hd : Meromorphic (logDeriv xi) := by rw [logDeriv]; exact hx.deriv.div hx
  have hg : Meromorphic (iteratedDeriv j (logDeriv xi)) := by
    rw [iteratedDeriv_eq_iterate]; exact hd.iterated_deriv
  change Measurable (fun z => (‖iteratedDeriv j (logDeriv xi) z‖^(((j+1:ℕ):ℝ)⁻¹) /
    (j.factorial:ℝ)^(((j+1:ℕ):ℝ)⁻¹))^2)
  exact ((hg.measurable.norm.pow_const _).div_const _).pow_const (2:ℕ)

private theorem density_tail_identity (j : ℕ) (c : ℂ) (R : ℝ) {t : ℝ} (ht : 0<t) :
    t*(volume.restrict (ball c R)).real {z | t<criticalXiDensity j z} =
      Real.pi*xiDerivativeDiskArea j c R (Real.sqrt t) := by
  have hlev (z : ℂ) : t<criticalXiDensity j z ↔
      (j.factorial:ℝ)*(Real.sqrt t)^(j+1)<‖iteratedDeriv j (logDeriv xi) z‖ := by
    have hroot : 0≤logDerivativeRoot xi j z := by
      unfold logDerivativeRoot
      exact div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc t<criticalXiDensity j z ↔ (Real.sqrt t)^2 < (logDerivativeRoot xi j z)^2 := by
           simp only [Real.sq_sqrt ht.le,criticalXiDensity]
         _ ↔ _ := (sq_lt_sq₀ (Real.sqrt_nonneg _) hroot).trans
           (log_derivative_root_level xi j (Real.sqrt_pos.mpr ht) z)
  have he : {z | t<criticalXiDensity j z} ∩ ball c R =
      {z | z∈ball c R ∧ (j.factorial:ℝ)*(Real.sqrt t)^(j+1)<‖iteratedDeriv j (logDeriv xi) z‖} := by
    ext z
    simp only [mem_inter_iff,mem_setOf_eq,hlev,and_comm]
  unfold xiDerivativeDiskArea logDerivativeDiskArea Measure.real
  rw [Measure.restrict_apply' isOpen_ball.measurableSet,he,Real.sq_sqrt ht.le]
  field_simp [Real.pi_ne_zero]

private theorem critical_density_tail {j : ℕ} {c : ℂ} {R A : ℝ}
    (h : Tendsto (xiDerivativeDiskArea j c R) atTop (𝓝 A)) :
    Tendsto (fun u : ℝ => u*(volume.restrict (ball c R)).real {z | u<criticalXiDensity j z})
      atTop (𝓝 (Real.pi*A)) := by
  apply ((h.comp Real.tendsto_sqrt_atTop).const_mul Real.pi).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  exact (density_tail_identity j c R hu).symm

/-- The clipped critical power reads the full fractional divisor moment
at every order, with a single observation disk. -/
theorem xi_critical_logarithmic_moments (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi) =
        ∑ z ∈ t, (hadamardOrder z:ℤ) ∧ ∀ j : ℕ,
      Tendsto (fun T : ℝ => (∫ z in ball c R, min (criticalXiDensity j z) T) / Real.log T) atTop
        (𝓝 (Real.pi*∑ z ∈ t, (hadamardOrder z:ℝ)^(2/((j+1:ℕ):ℝ)))) := by
  obtain ⟨t,ht,hw,ha⟩ := xi_disk_fractional_moments c hR hb
  refine ⟨t,ht,hw,fun j => ?_⟩
  letI : IsFiniteMeasure (volume.restrict (ball c R)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply clipped_moment_of_weak_tail _ _ (measurable_density j) (fun z => sq_nonneg _)
  exact critical_density_tail (ha j)

/-- A fixed multiplicative gap between clipping thresholds isolates the
winding as a finite limit of two first-derivative energy measurements. -/
theorem xi_winding_from_two_clipping_thresholds (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) {a b : ℝ} (ha : 0<a) (hab : a<b) :
    Tendsto (fun T : ℝ => (∫ z in ball c R, min (criticalXiDensity 1 z) (b*T)) -
       ∫ z in ball c R, min (criticalXiDensity 1 z) (a*T)) atTop
      (𝓝 (Real.pi*(windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi):ℝ)*
        Real.log (b/a))) := by
  obtain ⟨t,_,hw,h⟩ := xi_disk_fractional_moments c hR hb
  letI : IsFiniteMeasure (volume.restrict (ball c R)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hl := clipped_moment_band_gap _ _ (measurable_density 1) (fun x => sq_nonneg _)
    (critical_density_tail (h 1)) ha hab
  rw [hw,Int.cast_sum]
  norm_num at hl
  simpa only [Int.cast_natCast] using hl

#print axioms xi_winding_from_two_clipping_thresholds

/-- At the first derivative the logarithmic coefficient is π times
the winding, without a sum over zero locations in the formula. -/
theorem xi_first_critical_logarithmic_winding (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    Tendsto (fun T : ℝ => (∫ z in ball c R, min (criticalXiDensity 1 z) T)/Real.log T)
      atTop (𝓝 (Real.pi*(windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi):ℝ))) := by
  obtain ⟨t,_,hw,ha⟩ := xi_critical_logarithmic_moments c hR hb
  rw [hw,Int.cast_sum]
  have h := ha 1
  norm_num at h
  simpa only [Int.cast_natCast] using h

/-- For every derivative order the critical power is integrable on
a regular disk exactly when ξ has no zero in its interior. -/
theorem integrable_critical_xi_density_iff (j : ℕ) (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    IntegrableOn (criticalXiDensity j) (ball c R) ↔ ∀ z ∈ ball c R, xi z≠0 := by
  constructor
  · intro hi z hz he
    obtain ⟨S,hS,_,ha⟩ := xi_disk_fractional_moments c hR hb
    have hin : z∈S := (hS z).mpr ⟨by simpa only [mem_ball,dist_eq_norm] using hz, he⟩
    have hm : 0<hadamardOrder z := Nat.pos_of_ne_zero
      (fun h => (hadamardOrder_zero_iff z).mp h he)
    have hpos : 0<(hadamardOrder z:ℝ)^(2/((j+1:ℕ):ℝ)) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _
    have hle := Finset.single_le_sum (f:=fun x => (hadamardOrder x:ℝ)^(2/((j+1:ℕ):ℝ)))
      (fun x _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hin
    letI : IsFiniteMeasure (volume.restrict (ball c R)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    exact (mul_pos Real.pi_pos (hpos.trans_le hle)).ne'
      (integrable_weak_tail_residue_zero _ _ (measurable_density j) (fun x => sq_nonneg _)
        (critical_density_tail (ha j)) hi)
  · intro hn
    have hcont : ContinuousOn (criticalXiDensity j) (closedBall c R) := by
      intro z hz
      have hreg : xi z≠0 := by
        obtain hlt|he := (mem_closedBall.mp hz).lt_or_eq
        · exact hn z (mem_ball.mpr hlt)
        · exact hb z (by simpa only [dist_eq_norm] using he)
      have h := (analyticAt_hadamard_derivative hreg j).continuousAt.norm.rpow_const
        (p:=((j+1:ℕ):ℝ)⁻¹) (Or.inr (by positivity))
      exact ((h.div_const _).pow 2).continuousWithinAt
    exact (hcont.integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall

/-- Failure of local critical integrability detects the exact ξ-zero set,
without any boundary assumption or prior choice of observation radius. -/
theorem local_critical_xi_density_iff (j : ℕ) (p : ℂ) :
    (∃ r : ℝ, 0<r ∧ IntegrableOn (criticalXiDensity j) (ball p r)) ↔ xi p≠0 := by
  constructor
  · rintro ⟨r,hr,hi⟩ hz
    obtain ⟨d,hd,h⟩ := analytic_germ_derivative_disk_area
      (xi_differentiable.analyticAt p) (xi_order_ne_top p) j
    let s := min r d
    have hs : 0<s := lt_min hr hd
    have hl : Tendsto (xiDerivativeDiskArea j p s) atTop
        (𝓝 ((hadamardOrder p:ℝ)^(2/((j+1:ℕ):ℝ)))) := h s hs (min_le_right ..)
    letI : IsFiniteMeasure (volume.restrict (ball p s)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hm : 0<hadamardOrder p := Nat.pos_of_ne_zero (fun he => (hadamardOrder_zero_iff p).mp he hz)
    exact (mul_pos Real.pi_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _)).ne'
      (integrable_weak_tail_residue_zero _ _ (measurable_density j) (fun x => sq_nonneg _)
        (critical_density_tail hl) (hi.mono_set (ball_subset_ball (min_le_left ..))))
  · intro hz
    obtain ⟨d,hd,h⟩ := Metric.mem_nhds_iff.mp (xi_differentiable.continuous.continuousAt.eventually_ne hz)
    have hh : 0<d/2 := half_pos hd
    have avoid (z : ℂ) (he : ‖z-p‖=d/2) : xi z≠0 := by
      apply h
      rw [mem_ball,dist_eq_norm,he]
      exact half_lt_self hd
    refine ⟨d/2,hh,(integrable_critical_xi_density_iff j p hh avoid).mpr ?_⟩
    exact fun z hzb => h (ball_subset_ball (half_le_self hd.le) hzb)

/-- At any fixed derivative order, critical local integrability on the
open right half-plane is equivalent to the Riemann hypothesis. -/
theorem rh_iff_right_local_critical_integrability (j : ℕ) :
    RiemannHypothesis ↔ ∀ p : ℂ, 1/2<p.re →
      ∃ r : ℝ, 0<r ∧ IntegrableOn (criticalXiDensity j) (ball p r) := by
  constructor
  · intro hr p hp
    exact (local_critical_xi_density_iff j p).mpr fun hz =>
      hp.ne' ((riemannHypothesis_iff_xi_zero_re_eq_half.mp hr) p hz)
  · intro hi
    apply riemannHypothesis_iff_xi_ne_zero_of_re_lt_half.mpr
    intro z hz
    have hright : (1:ℝ)/2<(1-z).re := by
      rw [Complex.sub_re,Complex.one_re]
      linarith only [hz]
    have h := (local_critical_xi_density_iff j (1-z)).mp (hi _ hright)
    rwa [xi_one_sub] at h

#print axioms local_critical_xi_density_iff
#print axioms rh_iff_right_local_critical_integrability
#print axioms integrable_critical_xi_density_iff
#print axioms xi_critical_logarithmic_moments
#print axioms xi_first_critical_logarithmic_winding
end GaloisForLFunctions.ExceptionalLayerTheory
