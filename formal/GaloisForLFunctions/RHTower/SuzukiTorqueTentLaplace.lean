import GaloisForLFunctions.RHTower.SuzukiTorqueTentSeries
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# The Laplace transform of a single tent

Each tent of the visible prime layer transforms to `c_n e^{-σ log n}/σ²`, which is the corpus's
`integral_suzukiPositionTent_mul_exp` once the tent is cut at its birth point.  The integrand
vanishes before that point, so the whole positive ray contributes only the tail, and the tail's
integrability is the elementary `u e^{-σu}` estimate.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

theorem integrableOn_id_mul_exp_neg {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-σ * u)) (Ioi 0) := by
  have h := GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi
    (σ := (1 : ℝ)) (a := σ) (by norm_num) hσ
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  show u ^ (1 : ℝ) * Real.exp (-(σ * u)) = u * Real.exp (-σ * u)
  rw [Real.rpow_one]
  congr 1
  ring

theorem integrableOn_tent_mul_exp {σ h : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) :
    IntegrableOn (fun L : ℝ => (L - h) * Real.exp (-σ * L)) (Ioi h) := by
  have hbase : IntegrableOn (fun u : ℝ => u * Real.exp (-σ * u)) (Ioi h) :=
    (integrableOn_id_mul_exp_neg hσ).mono_set (Ioi_subset_Ioi hh)
  refine Integrable.mono' hbase
    (((continuous_id.sub continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hLh : h < L := hL
  have hLpos : (0 : ℝ) < L := lt_of_le_of_lt hh hLh
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (L - h) * Real.exp (-σ * L))]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem integrableOn_suzukiTentTerm_mul_exp (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun L : ℝ => suzukiTentTerm n L * Real.exp (-σ * L)) (Ioi 0) := by
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hbase : IntegrableOn (fun u : ℝ => suzukiTentCoeff n * (u * Real.exp (-σ * u))) (Ioi 0) :=
    (integrableOn_id_mul_exp_neg hσ).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun L : ℝ => suzukiTentTerm n L * Real.exp (-σ * L)) (volume.restrict (Ioi 0)) := by
    have hcont : Continuous fun L : ℝ => suzukiTentTerm n L := by
      have : Continuous fun L : ℝ => suzukiTentCoeff n * max (L - Real.log n) 0 :=
        continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
      exact this
    exact (hcont.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  refine Integrable.mono' hbase hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
  have hLpos : (0 : ℝ) < L := hL
  have hc := suzukiTentCoeff_nonneg n
  have hmax : max (L - Real.log n) 0 ≤ L := by
    rcases le_or_gt (L - Real.log n) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (suzukiTentTerm_nonneg n L) (Real.exp_pos _).le), suzukiTentTerm]
  calc suzukiTentCoeff n * max (L - Real.log n) 0 * Real.exp (-σ * L)
      ≤ suzukiTentCoeff n * L * Real.exp (-σ * L) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hmax hc
    _ = suzukiTentCoeff n * (L * Real.exp (-σ * L)) := by ring

/-- **The `n`-th tent's Laplace transform.** -/
theorem integral_suzukiTentTerm_mul_exp (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ L in Ioi (0 : ℝ), suzukiTentTerm n L * Real.exp (-σ * L))
      = suzukiTentCoeff n * (Real.exp (-σ * Real.log n) / σ ^ 2) := by
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hsplit : Ioi (0 : ℝ) = Ioc 0 (Real.log n) ∪ Ioi (Real.log n) :=
    (Ioc_union_Ioi_eq_Ioi hlog).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.log n)) (Ioi (Real.log n)) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have htotal := integrableOn_suzukiTentTerm_mul_exp n hσ
  have h1 : IntegrableOn (fun L : ℝ => suzukiTentTerm n L * Real.exp (-σ * L))
      (Ioc 0 (Real.log n)) := htotal.mono_set (by rw [hsplit]; exact subset_union_left)
  have h2 : IntegrableOn (fun L : ℝ => suzukiTentTerm n L * Real.exp (-σ * L))
      (Ioi (Real.log n)) := htotal.mono_set (by rw [hsplit]; exact subset_union_right)
  have hzero : (∫ L in Ioc (0 : ℝ) (Real.log n), suzukiTentTerm n L * Real.exp (-σ * L)) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun L hL => ?_
    rw [suzukiTentTerm, max_eq_right (by linarith [hL.2]), mul_zero, zero_mul]
  have htail : (∫ L in Ioi (Real.log n), suzukiTentTerm n L * Real.exp (-σ * L))
      = suzukiTentCoeff n * (Real.exp (-σ * Real.log n) / σ ^ 2) := by
    have hcongr : (∫ L in Ioi (Real.log n), suzukiTentTerm n L * Real.exp (-σ * L))
        = ∫ L in Ioi (Real.log n),
            suzukiTentCoeff n * ((L - Real.log n) * Real.exp (-σ * L)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun L hL => ?_
      have hLn : Real.log n < L := hL
      rw [suzukiTentTerm, max_eq_left (by linarith)]
      ring
    rw [hcongr, integral_const_mul, integral_suzukiPositionTent_mul_exp σ (Real.log n) hσ]
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi h1 h2, hzero, zero_add, htail]

end RHTower
