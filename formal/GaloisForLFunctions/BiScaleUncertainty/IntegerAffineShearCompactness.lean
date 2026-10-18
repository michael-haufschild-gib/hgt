import GaloisForLFunctions.BiScaleUncertainty.SummableIntegerAffineShear
import GaloisForLFunctions.HTGeometry.ObserverHorizonStability

/-!
# Signed scale coefficients survive every compact correction

All l1 combinations of integer affine shears have cofinal coefficient readouts.
Compact corrections disappear on these moving coordinates. This gives exact
coefficient recovery modulo compact operators and a quadratic lower bound on
the size remaining after every compact correction.
-/

noncomputable section
open Filter
open scoped Topology RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private theorem unitVector_weaklyNull (z : State) :
    Tendsto (fun n => ⟪z, (lp.single 2 n (1 : ℝ) : State)⟫) atTop (𝓝 0) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) z
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have hs := (Real.continuous_sqrt.tendsto 0).comp h.summable.tendsto_atTop_zero
  rw [Real.sqrt_zero] at hs
  have hz : Tendsto (fun n => z n) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (hs.congr fun n => ?_)
    exact Real.sqrt_sq (norm_nonneg (z n))
  simpa [lp.inner_single_right] using hz

theorem compact_single_tendsto (K : State →L[ℝ] State) (hK : IsCompactOperator K) :
    Tendsto (fun n => K (lp.single 2 n (1 : ℝ))) atTop (𝓝 0) :=
  GaloisForLFunctions.HTGeometry.tendsto_norm_compact_of_weaklyNull K hK
    (fun n => lp.single 2 n (1 : ℝ))
    (fun n => by rw [lp.norm_single (by norm_num), norm_one]) unitVector_weaklyNull

theorem compact_moving_coordinate_tendsto (K : State →L[ℝ] State)
    (hK : IsCompactOperator K) (q : ℕ → ℕ) :
    Tendsto (fun n => K (lp.single 2 n (1 : ℝ)) (q n)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => lp.norm_apply_le_norm (by norm_num) _ (q n))
  simpa only [norm_zero] using (compact_single_tendsto K hK).norm

/-- The positive endpoint recovers its coefficient after every compact correction. -/
theorem series_sub_compact_plus_tendsto (a : Weights) (K : State →L[ℝ] State)
    (hK : IsCompactOperator K) (d : ℕ) :
    Tendsto (fun n => (series a-K) (lp.single 2 n (1 : ℝ)) ((d+2)*n+1))
      atTop (𝓝 (a d)) := by
  have h := (tendsto_const_nhds (x := a d)).sub
    (compact_moving_coordinate_tendsto K hK (fun n => (d+2)*n+1))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (d+2)] with n hn
  simp [series_single_plus a d n hn]

/-- The negative endpoint recovers the opposite coefficient after every compact correction. -/
theorem series_sub_compact_minus_tendsto (a : Weights) (K : State →L[ℝ] State)
    (hK : IsCompactOperator K) (d : ℕ) :
    Tendsto (fun n => (series a-K) (lp.single 2 n (1 : ℝ)) ((d+2)*(n+1)))
      atTop (𝓝 (-a d)) := by
  have h := (tendsto_const_nhds (x := -a d)).sub
    (compact_moving_coordinate_tendsto K hK (fun n => (d+2)*(n+1)))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (d+2)] with n hn
  simp [series_single_minus a d n hn]

/-- No cancellation among any l1 family of scales makes a nonzero shear combination compact. -/
theorem series_compact_iff (a : Weights) : IsCompactOperator (series a) ↔ a=0 := by
  constructor
  · intro hK
    apply lp.ext
    funext d
    have h := series_sub_compact_plus_tendsto a (series a) hK d
    have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (a d)) := by simpa using h
    exact tendsto_nhds_unique hz tendsto_const_nhds
  · rintro rfl
    rw [series_zero]
    exact isCompactOperator_zero

/-- The compact quotient retains the complete signed coefficient sequence. -/
theorem series_sub_compact_iff (a b : Weights) :
    IsCompactOperator (series a-series b : State →L[ℝ] State) ↔ a=b := by
  rw [← series_sub, series_compact_iff, sub_eq_zero]

private theorem standard_orthonormal :
    Orthonormal ℝ (fun n : ℕ => (lp.single 2 n (1 : ℝ) : State)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply]

private theorem two_endpoint_squares_le (F : Finset ℕ) (n : ℕ)
    (hn : ∀ d ∈ F, d+2 ≤ n) (v : State) :
    (∑ d ∈ F, v ((d+2)*n+1)^2) + (∑ d ∈ F, v ((d+2)*(n+1))^2) ≤ ‖v‖^2 := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨d, hd⟩ := hF
    have hnp : 0 < n := by have hh := hn d hd; omega
    let P := F.image (fun d => (d+2)*n+1)
    let M := F.image (fun d => (d+2)*(n+1))
    have hdj : Disjoint P M := by
      rw [Finset.disjoint_left]
      intro k hkP hkM
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hkP
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp hkM
      exact (output_coordinates_disjoint d e n (hn d hd)) he.symm
    have hP : Set.InjOn (fun d => (d+2)*n+1) (F : Set ℕ) := by
      intro d _ e _ h
      have hh := Nat.mul_right_cancel hnp (Nat.add_right_cancel h)
      omega
    have hM : Set.InjOn (fun d => (d+2)*(n+1)) (F : Set ℕ) := by
      intro d _ e _ h
      have hh := Nat.mul_right_cancel (show 0 < n+1 by omega) h
      omega
    have hb : (∑ k ∈ P ∪ M, v k^2) ≤ ‖v‖^2 := by
      simpa [lp.inner_single_left, Real.norm_eq_abs] using
        standard_orthonormal.sum_inner_products_le (s := P ∪ M) v
    rw [Finset.sum_union hdj] at hb
    simpa only [P, M, Finset.sum_image hP, Finset.sum_image hM] using hb
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hF, Finset.sum_empty, zero_add]
    exact sq_nonneg _

/-- Every finite portion of the full signed coefficient energy survives compact correction. -/
theorem finite_coefficient_energy_le (a : Weights) (K : State →L[ℝ] State)
    (hK : IsCompactOperator K) (F : Finset ℕ) :
    2*(∑ d ∈ F, (a d)^2) ≤ ‖series a-K‖^2 := by
  let A := series a-K
  have hp := tendsto_finsetSum F
    (fun d _ => (series_sub_compact_plus_tendsto a K hK d).pow 2)
  have hm := tendsto_finsetSum F
    (fun d _ => (series_sub_compact_minus_tendsto a K hK d).pow 2)
  have hlim : Tendsto (fun n =>
      (∑ d ∈ F, (A (lp.single 2 n (1 : ℝ)) ((d+2)*n+1))^2) +
      (∑ d ∈ F, (A (lp.single 2 n (1 : ℝ)) ((d+2)*(n+1)))^2))
      atTop (𝓝 (2*(∑ d ∈ F, (a d)^2))) := by
    simpa only [A, neg_sq, two_mul] using hp.add hm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (∑ d ∈ F, (d+2))] with n hn
  have hN : ∀ d ∈ F, d+2 ≤ n := by
    intro d hd
    exact (Finset.single_le_sum (fun e _ => Nat.zero_le (e+2)) hd).trans hn
  have hb := two_endpoint_squares_le F n hN (A (lp.single 2 n (1 : ℝ)))
  have hop : ‖A (lp.single 2 n (1 : ℝ))‖ ≤ ‖A‖ := by
    simpa only [lp.norm_single (p := 2) (by norm_num), norm_one, mul_one] using
      A.le_opNorm (lp.single 2 n (1 : ℝ))
  nlinarith only [hb, hop, norm_nonneg (A (lp.single 2 n (1 : ℝ))), norm_nonneg A]

end GaloisForLFunctions.BiScaleUncertainty.IntegerAffineShear
