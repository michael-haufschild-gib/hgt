import Mathlib

/-!
# Real-mesh improper antitone Riemann sums

The existing integer-mesh theorem is not enough when the scale itself is a real analytic
parameter.  This file gives the sharp integral-test squeeze at every positive real mesh:

`I ≤ h ⋅ ∑ f(nh) ≤ I + h f(0)`.

It then sends the mesh to zero.  The theorem is source-neutral and is used below for the exact
large-shift constant of Hurwitz zeta and every positive-order polygamma function.
-/

open MeasureTheory intervalIntegral Filter Topology Set

namespace HTGeometry

/-- Sharp lower and upper integral-test bounds at an arbitrary positive real mesh. -/
theorem realMesh_antitone_Ioi_bounds {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Ici 0)) (hnn : ∀ x ∈ Ici (0 : ℝ), 0 ≤ f x)
    (hint : IntegrableOn f (Ioi 0)) {i : ℝ} (hi : 0 < i) :
    let I := ∫ x in Ioi 0, f x
    I ≤ (1 / i) * ∑' k : ℕ, f ((k : ℝ) / i) ∧
      (1 / i) * ∑' k : ℕ, f ((k : ℝ) / i) ≤ I + f 0 / i := by
  dsimp only
  set I : ℝ := ∫ x in Ioi 0, f x with hI
  have hganti : ∀ N : ℕ,
      AntitoneOn (fun x => f (x / i)) (Icc 0 (0 + (N : ℝ))) := by
    intro N a ha b hb hab
    rw [zero_add] at ha hb
    exact hanti (div_nonneg ha.1 hi.le) (div_nonneg hb.1 hi.le) (by gcongr)
  have hscale : ∀ N : ℕ,
      (∫ x in (0 : ℝ)..(N : ℝ), f (x / i)) =
        i * ∫ x in (0 : ℝ)..((N : ℝ) / i), f x := by
    intro N
    rw [integral_comp_div f (ne_of_gt hi), zero_div, smul_eq_mul]
  have hsum_le : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) / i))
        ≤ i * ∫ x in (0 : ℝ)..((N : ℝ) / i), f x := by
    intro N
    have hsil := (hganti N).sum_le_integral
    simp only [zero_add] at hsil
    rwa [hscale N] at hsil
  have hint_le : ∀ N : ℕ,
      i * ∫ x in (0 : ℝ)..((N : ℝ) / i), f x
        ≤ ∑ k ∈ Finset.range N, f ((k : ℝ) / i) := by
    intro N
    have hils := (hganti N).integral_le_sum
    simp only [zero_add] at hils
    rwa [hscale N] at hils
  have htail : ∀ N : ℕ, ∫ x in (0 : ℝ)..((N : ℝ) / i), f x ≤ I := by
    intro N
    have hNi : (0 : ℝ) ≤ (N : ℝ) / i := by positivity
    rw [intervalIntegral.integral_of_le hNi, hI]
    refine setIntegral_mono_set hint ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hnn x (Set.mem_Ici.mpr (le_of_lt hx))
    · exact Filter.Eventually.of_forall (fun x hx => hx.1)
  have htends :
      Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..((N : ℝ) / i), f x) atTop (nhds I) := by
    rw [hI]
    exact intervalIntegral_tendsto_integral_Ioi 0 hint
      (tendsto_natCast_atTop_atTop.atTop_div_const hi)
  have hpartial : ∀ N : ℕ,
      ∑ k ∈ Finset.range N, f ((k : ℝ) / i) ≤ i * I + f 0 := by
    intro N
    have e1 : (∑ k ∈ Finset.range N, f ((k : ℝ) / i)) + f ((N : ℝ) / i)
        = (∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) / i)) + f 0 := by
      have s1 := Finset.sum_range_succ (fun k => f ((k : ℝ) / i)) N
      have s2 := Finset.sum_range_succ' (fun k => f ((k : ℝ) / i)) N
      rw [s1] at s2
      simpa using s2
    have hshift_le : ∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℝ) / i) ≤ i * I :=
      le_trans (hsum_le N) (mul_le_mul_of_nonneg_left (htail N) hi.le)
    have hNnn : 0 ≤ f ((N : ℝ) / i) := hnn _ (Set.mem_Ici.mpr (by positivity))
    linarith [e1, hshift_le, hNnn]
  have hsummable : Summable (fun k : ℕ => f ((k : ℝ) / i)) :=
    summable_of_sum_range_le (c := i * I + f 0)
      (fun k => hnn _ (Set.mem_Ici.mpr (by positivity))) hpartial
  have hlow : I ≤ (1 / i) * ∑' k : ℕ, f ((k : ℝ) / i) := by
    have hbound : ∀ N : ℕ,
        ∫ x in (0 : ℝ)..((N : ℝ) / i), f x
          ≤ (1 / i) * ∑' k : ℕ, f ((k : ℝ) / i) := by
      intro N
      have h2 : ∑ k ∈ Finset.range N, f ((k : ℝ) / i)
          ≤ ∑' k : ℕ, f ((k : ℝ) / i) :=
        hsummable.sum_le_tsum (Finset.range N)
          (fun k _ => hnn _ (Set.mem_Ici.mpr (by positivity)))
      have hle : i * ∫ x in (0 : ℝ)..((N : ℝ) / i), f x
          ≤ ∑' k : ℕ, f ((k : ℝ) / i) := le_trans (hint_le N) h2
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hi]
      linarith [hle]
    exact le_of_tendsto htends (Filter.Eventually.of_forall hbound)
  have hupp : (1 / i) * ∑' k : ℕ, f ((k : ℝ) / i) ≤ I + f 0 / i := by
    have htsum_le : ∑' k : ℕ, f ((k : ℝ) / i) ≤ i * I + f 0 :=
      Real.tsum_le_of_sum_range_le
        (fun k => hnn _ (Set.mem_Ici.mpr (by positivity))) hpartial
    rw [one_div, inv_mul_le_iff₀ hi]
    have hrw : i * (I + f 0 / i) = i * I + f 0 := by field_simp
    rw [hrw]
    exact htsum_le
  exact ⟨hlow, hupp⟩

/-- As the reciprocal real mesh tends to zero, every nonnegative integrable antitone profile has
its improper Riemann sums converge to the half-line integral. -/
theorem tendsto_realMesh_antitone_Ioi {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Ici 0)) (hnn : ∀ x ∈ Ici (0 : ℝ), 0 ≤ f x)
    (hint : IntegrableOn f (Ioi 0)) :
    Tendsto (fun i : ℝ => (1 / i) * ∑' k : ℕ, f ((k : ℝ) / i)) atTop
      (nhds (∫ x in Ioi 0, f x)) := by
  let I := ∫ x in Ioi 0, f x
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ => I)
    (h := fun i : ℝ => I + f 0 / i) tendsto_const_nhds ?_ ?_ ?_
  · have h0 : Tendsto (fun i : ℝ => f 0 / i) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.const_mul (f 0))
    simpa using tendsto_const_nhds.add h0
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with i hi
    exact (realMesh_antitone_Ioi_bounds hanti hnn hint hi).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with i hi
    exact (realMesh_antitone_Ioi_bounds hanti hnn hint hi).2

end HTGeometry
