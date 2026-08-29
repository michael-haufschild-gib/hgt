import GaloisForLFunctions.HTGeometry.RamificationSubstitution
import GaloisForLFunctions.HTGeometry.LogPolyNegligible

/-!
# A common sequence of good radii for a finite family

The logarithmic-derivative estimate at a Borel-good radius bounds each `m(r, F'/F)` by the logarithm
of a quantity polynomial in the radius and in a common majorant `U` of the characteristics.  Choosing
one majorant for a whole finite family therefore produces one sequence of radii along which every
member's logarithmic-derivative proximity is negligible relative to `U`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn Filter Set

/-- **The logarithmic-derivative error of a finite family is negligible along a common sequence of
radii.** -/
theorem exists_good_radii_family {ι : Type*} [Fintype ι] (F : ι → ℂ → ℂ)
    (hF : ∀ i, Differentiable ℂ (F i))
    (hFo : ∀ i, ∀ z, meromorphicOrderAt (F i) z ≠ ⊤)
    {U : ℝ → ℝ} (hUmono : Monotone U) (hU1 : ∀ s, 1 ≤ U s)
    (hUdom : ∀ i, ∀ s, 1 ≤ s → characteristic (F i) ⊤ s ≤ U s)
    (hUlog : Tendsto (fun r => Real.log r / U r) atTop (nhds 0))
    (hUtop : Tendsto U atTop atTop) :
    ∃ rn : ℕ → ℝ, Tendsto rn atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        (∑ i, proximity (fun z => deriv (F i) z / F i z) ⊤ (rn n)) ≤ ε * U (rn n) := by
  classical
  obtain ⟨rn, hrntop, hrn⟩ := exists_good_radius_seq hUmono hU1
  have hCex : ∀ i : ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → U (r + (U r)⁻¹) < 2 * U r →
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
        Real.posLog ‖logDeriv (F i) ((r : ℂ) * Complex.exp (θ * Complex.I))‖
        ≤ 2 * Real.log (1 + C * (r + 1) ^ 4 * (U r + 1) ^ 4) :=
    fun i => exists_logDeriv_poly_bound (hF i) (hFo i) U hUmono hU1 (hUdom i)
  choose C hC0 hCb using hCex
  set Cmax : ℝ := ∑ i, C i with hCmax
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun i _ => hC0 i
  have hCle : ∀ i, C i ≤ Cmax := fun i =>
    Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)
  set q : ℝ := 2 * (Fintype.card ι : ℝ) + 1 with hq
  have hq0 : 0 < q := by
    have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    rw [hq]; linarith
  refine ⟨rn, hrntop, fun ε hε => ?_⟩
  refine eventually_le_of_log_poly_bound_filter (ρ := fun n => rn n) (C := Cmax) (k := 4)
    (c := q) hCmax0 (by omega) hq0 ?_ ?_ ?_ ?_ ?_ hε
  · filter_upwards [hrntop.eventually_ge_atTop (1 : ℝ)] with n hn
    set r : ℝ := rn n with hrdef
    have hgood := (hrn n).2
    have hU1r : (1 : ℝ) ≤ U r := hU1 r
    have hlogpos : 0 ≤ Real.log (1 + Cmax * (r + 1) ^ 4 * (U r + 1) ^ 4) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ Cmax * (r + 1) ^ 4 * (U r + 1) ^ 4 := by positivity
      linarith
    have hterm : ∀ i : ι, proximity (fun z => deriv (F i) z / F i z) ⊤ r
        ≤ 2 * Real.log (1 + Cmax * (r + 1) ^ 4 * (U r + 1) ^ 4) := by
      intro i
      rw [proximity_logDeriv_eq]
      refine le_trans (hCb i r hn hgood) ?_
      have hpos : (0 : ℝ) < 1 + C i * (r + 1) ^ 4 * (U r + 1) ^ 4 := by
        have h1 : (0 : ℝ) ≤ C i * (r + 1) ^ 4 * (U r + 1) ^ 4 :=
          mul_nonneg (mul_nonneg (hC0 i) (by positivity)) (by positivity)
        linarith
      refine mul_le_mul_of_nonneg_left (Real.log_le_log hpos ?_) (by norm_num)
      have hmono : C i * (r + 1) ^ 4 * (U r + 1) ^ 4
          ≤ Cmax * (r + 1) ^ 4 * (U r + 1) ^ 4 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (hCle i) (by positivity)
      linarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hterm i)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    refine le_trans hsum ?_
    rw [hq]
    nlinarith [hlogpos, Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  · exact Filter.Eventually.of_forall fun n => hU1 (rn n)
  · exact hrntop.eventually_ge_atTop (2 : ℝ)
  · exact hUlog.comp hrntop
  · exact hUtop.comp hrntop

end GaloisForLFunctions.HTGeometry
