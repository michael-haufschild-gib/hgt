import GaloisForLFunctions.ExceptionalLayerTheory.AddingLocalSuperlevelAreasOnAFiniteDivisor
import GaloisForLFunctions.ExceptionalLayerTheory.HighDerivativeAreasOfTheXiDivisor
import GaloisForLFunctions.RHTower.WindingXiCircle

/-!
# Fractional multiplicity moments from derivative areas on a whole disk

Observe the area where the j-th derivative of ξ'/ξ has magnitude above
j! u^(j+1). After normalization by u²/π its limit is the sum of
m^(2/(j+1)) over all interior zeros, for every circle avoiding zeros.
This uses only the total area across the disk, without small observation
windows placed individually at the zeros.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Normalized area of a derivative superlevel set on one fixed disk. -/
def logDerivativeDiskArea (f : ℂ → ℂ) (j : ℕ) (c : ℂ) (R u : ℝ) : ℝ :=
  u^2*volume.real {z | z∈ball c R ∧ (j.factorial:ℝ)*u^(j+1)<‖iteratedDeriv j (logDeriv f) z‖}/Real.pi

abbrev xiDerivativeDiskArea := logDerivativeDiskArea xi

private abbrev exponent (j : ℕ) := ((j+1:ℕ):ℝ)⁻¹
/-- The normalized root of the derivative magnitude has a first-order radial pole. -/
def logDerivativeRoot (f : ℂ → ℂ) (j : ℕ) (z : ℂ) := ‖iteratedDeriv j (logDeriv f) z‖^(exponent j)/
  (j.factorial:ℝ)^(exponent j)

private theorem exponent_pos (j : ℕ) : 0<exponent j := by unfold exponent; positivity
private theorem factorial_root_pos (j : ℕ) : 0<(j.factorial:ℝ)^(exponent j) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr j.factorial_pos) _

private theorem normalized_residue {f : ℂ → ℂ} {p : ℂ} (ha : AnalyticAt ℂ f p)
    (hn : analyticOrderAt f p≠⊤) (j : ℕ) :
    Tendsto (fun z => dist z p*logDerivativeRoot f j z) (𝓝[≠] p)
      (𝓝 (((analyticOrderAt f p).toNat:ℝ)^(exponent j))) := by
  have h := (analytic_log_derivative_radial_residue ha hn j).div_const ((j.factorial:ℝ)^(exponent j))
  change Tendsto _ _ (𝓝 ((((analyticOrderAt f p).toNat:ℝ)*j.factorial)^(exponent j)/_)) at h
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    mul_div_cancel_right₀ _ (factorial_root_pos j).ne'] at h
  exact h.congr fun _ => mul_div_assoc ..

/-- Thresholds of the positive root are exactly thresholds of the original derivative. -/
theorem log_derivative_root_level (f : ℂ → ℂ) (j : ℕ) {u : ℝ} (hu : 0<u) (z : ℂ) :
    u<logDerivativeRoot f j z ↔ (j.factorial:ℝ)*u^(j+1)<‖iteratedDeriv j (logDeriv f) z‖ := by
  rw [logDerivativeRoot,lt_div_iff₀ (factorial_root_pos j)]
  have he : ((j.factorial:ℝ)*u^(j+1))^(exponent j) = u*(j.factorial:ℝ)^(exponent j) := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hu.le _),
      show (u^(j+1))^(exponent j)=u from Real.pow_rpow_inv_natCast hu.le (Nat.succ_ne_zero j),
      mul_comm]
  rw [←he,Real.rpow_lt_rpow_iff (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu.le _))
    (norm_nonneg _) (exponent_pos j)]

private theorem area_coefficient (m j : ℕ) :
    Real.pi*((m:ℝ)^(exponent j))^2/Real.pi=(m:ℝ)^(2/((j+1:ℕ):ℝ)) := by
  rw [mul_div_cancel_left₀ _ Real.pi_ne_zero,←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  unfold exponent
  push_cast
  ring

/-- A fixed disk about a finite-order analytic germ measures the power
m^(2/(j+1)) of its order from the j-th logarithmic derivative. -/
theorem analytic_germ_derivative_disk_area {f : ℂ → ℂ} {p : ℂ}
    (ha : AnalyticAt ℂ f p) (hn : analyticOrderAt f p≠⊤) (j : ℕ) :
    ∃ r : ℝ, 0<r ∧ ∀ s : ℝ, 0<s → s≤r →
      Tendsto (logDerivativeDiskArea f j p s) atTop
        (𝓝 (((analyticOrderAt f p).toNat:ℝ)^(2/((j+1:ℕ):ℝ)))) := by
  obtain ⟨r,hr,h⟩ := fixed_disk_radial_level_area
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (normalized_residue ha hn j)
  refine ⟨r,hr,fun s hs hsr => ?_⟩
  have hl := (h s hs hsr).div_const Real.pi
  rw [area_coefficient] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  simp only [log_derivative_root_level f j hu,logDerivativeDiskArea]

/-- An identically zero germ has empty derivative superlevel sets on
all sufficiently small disks at every positive threshold. -/
theorem zero_germ_derivative_disk_area {f : ℂ → ℂ} {p : ℂ}
    (hf : ∀ᶠ z in 𝓝 p, f z=0) (j : ℕ) :
    ∃ r : ℝ, 0<r ∧ ∀ s : ℝ, s≤r → ∀ u : ℝ, 0<u → logDerivativeDiskArea f j p s u=0 := by
  have hz : logDeriv f =ᶠ[𝓝 p] (0 : ℂ → ℂ) := hf.mono (fun z h => by simp [logDeriv_apply,h])
  obtain ⟨r,hr,h⟩ := Metric.mem_nhds_iff.mp (hz.iteratedDeriv j)
  refine ⟨r,hr,fun s hs u hu => ?_⟩
  have he : {z | z∈ball p s ∧ (j.factorial:ℝ)*u^(j+1)<‖iteratedDeriv j (logDeriv f) z‖} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hball,hbig⟩
    rw [h (ball_subset_ball hs hball),iteratedDeriv_const_zero,norm_zero] at hbig
    exact (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu.le _)).not_gt hbig
  simp only [logDerivativeDiskArea,he,measureReal_empty,mul_zero,zero_div]

/-- Summing the local areas over a disk gives a fractional moment of all
its interior zero orders. Extra regular marked points contribute zero. -/
theorem analytic_disk_fractional_moment (f : ℂ → ℂ) (ha : ∀ z, AnalyticAt ℂ f z)
    (hfinite : ∀ z, analyticOrderAt f z≠⊤) (j : ℕ) (c : ℂ) (R : ℝ) (t : Finset ℂ)
    (ht : ∀ x ∈ t, x∈ball c R) (hregF : ∀ z ∈ closedBall c R, z∉t → f z≠0) :
    Tendsto (logDerivativeDiskArea f j c R) atTop
      (𝓝 (∑ x ∈ t, ((analyticOrderAt f x).toNat:ℝ)^(2/((j+1:ℕ):ℝ)))) := by
  have hreg (z : ℂ) (hz : z∈closedBall c R) (hn : z∉t) : ContinuousAt (logDerivativeRoot f j) z := by
    exact ((analyticAt_iterated_log_derivative (ha z) (hregF z hz hn) j).continuousAt.norm.rpow_const
      (Or.inr (exponent_pos j).le)).div_const _
  have hs := sum_local_superlevel_areas (logDerivativeRoot f j)
    (fun x => Real.pi*(((analyticOrderAt f x).toNat:ℝ)^(exponent j))^2) (fun u => u^2) c R t
    ht hreg (fun x => fixed_disk_radial_level_area (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (normalized_residue (ha x) (hfinite x) j))
  have h := hs.div_const Real.pi
  simp only [Finset.sum_div,area_coefficient] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  simp only [log_derivative_root_level f j hu,logDerivativeDiskArea]

/-- The same finite divisor supplies all derivative-area moments and
the winding number on its enclosing circle. -/
theorem xi_disk_fractional_moments (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi) =
        ∑ z ∈ t, (hadamardOrder z:ℤ) ∧
      ∀ j : ℕ, Tendsto (xiDerivativeDiskArea j c R) atTop
        (𝓝 (∑ z ∈ t, (hadamardOrder z:ℝ)^(2/((j+1:ℕ):ℝ)))) := by
  classical
  obtain ⟨t,ht,hw⟩ := windingNumber_xi_circle c hR hb
  refine ⟨t,ht,hw,?_⟩
  intro j
  have hinside (x : ℂ) (hx : x∈t) : x∈ball c R := by
    simpa only [mem_ball,dist_eq_norm] using ((ht x).mp hx).1
  apply analytic_disk_fractional_moment xi xi_differentiable.analyticAt xi_order_ne_top j c R t hinside
  intro z hz hn
  have hle : ‖z-c‖≤R := by simpa only [dist_eq_norm] using mem_closedBall.mp hz
  exact fun he => hn ((ht z).mpr ⟨hle.lt_of_ne (fun heq => hb z heq he),he⟩)

#print axioms xi_disk_fractional_moments
#print axioms analytic_germ_derivative_disk_area
end GaloisForLFunctions.ExceptionalLayerTheory
