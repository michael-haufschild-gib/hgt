import GaloisForLFunctions.WindowTowerOfSpecZ.TheUniformGammaReserveHasANegativeDirection
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderCannotBeDiscarded
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldRetainsTwoMomentCharges

/-!
# A smooth negative direction after the uniform Gamma reserve

Multiplication by `(1−4x²)/(1−2x²)` converts the smoothed quintic into
approximations of the quadratic endpoint cutoff. The multiplier is smooth
near the unit window; outside it every approximation vanishes locally.
Uniform size and Lipschitz bounds preserve the strict negative retained energy.
Consequently the two-moment first-fold lower form also has a negative direction.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.WindowTowerOfSpecZ

private def cutoffRatio (x : ℝ) : ℝ := (1-4*x^2)/(1-2*x^2)

private theorem unit_square_le {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    x^2 ≤ 1/4 := by
  nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ x+1/2)
    (by linarith only [hx.2] : 0 ≤ 1/2-x)]

private theorem cutoffRatio_bounds {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    0 ≤ cutoffRatio x ∧ cutoffRatio x ≤ 1 := by
  have h := unit_square_le hx
  have hd : 0 < 1-2*x^2 := by linarith only [h]
  constructor
  · exact div_nonneg (by linarith only [h]) hd.le
  · apply (div_le_one hd).mpr
    linarith only [sq_nonneg x]

private theorem cutoffRatio_deriv {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    HasDerivAt cutoffRatio (-4*x/(1-2*x^2)^2) x := by
  have hd : 1-2*x^2 ≠ 0 := by linarith only [unit_square_le hx]
  have ha := ((hasDerivAt_pow 2 x).const_mul 4).const_sub 1
  have hb := ((hasDerivAt_pow 2 x).const_mul 2).const_sub 1
  exact (ha.div hb hd).congr_deriv (by ring)

private theorem cutoffRatio_lipschitz :
    LipschitzOnWith 8 cutoffRatio (Icc (-(1/2 : ℝ)) (1/2)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x hx => (cutoffRatio_deriv hx).differentiableAt) _ (convex_Icc _ _)
  intro x hx
  change ‖deriv cutoffRatio x‖ ≤ (8 : ℝ)
  rw [(cutoffRatio_deriv hx).deriv, Real.norm_eq_abs, abs_div, abs_mul]
  have habs : |(1-2*x^2)^2| = (1-2*x^2)^2 := abs_of_nonneg (sq_nonneg _)
  rw [habs]
  have hd : (1/2 : ℝ) ≤ 1-2*x^2 := by linarith only [unit_square_le hx]
  have hd2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hd 2
  have hdp : 0 < (1-2*x^2)^2 := by nlinarith only [hd2]
  apply (div_le_iff₀ hdp).mpr
  norm_num only [abs_neg]
  nlinarith only [abs_le.mpr hx, hd2]

/-- Smooth unit-window approximations to the quadratic endpoint cutoff. -/
def unitSmoothQuadraticCutoff (n : ℕ) (x : ℝ) : ℝ :=
  unitSmoothQuintic n x * cutoffRatio x

theorem unitSmoothQuadraticCutoff_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (-(1/2 : ℝ)) (1/2)) : unitSmoothQuadraticCutoff n x = 0 := by
  rw [unitSmoothQuadraticCutoff, unitSmoothQuintic_outside n hx, zero_mul]

theorem unitSmoothQuadraticCutoff_contDiff (n : ℕ) :
    ContDiff ℝ 2 (unitSmoothQuadraticCutoff n) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
  · have hd : 1-2*x^2 ≠ 0 := by linarith only [unit_square_le hx]
    exact (unitSmoothQuintic_contDiff n).contDiffAt.mul
      ((contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.pow 2))).div
        (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.pow 2))) hd)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact unitSmoothQuadraticCutoff_outside n hy

theorem unitSmoothQuadraticCutoff_support (n : ℕ) :
    tsupport (unitSmoothQuadraticCutoff n) ⊆ Icc (-(1/2 : ℝ)) (1/2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hi
  exact hx (unitSmoothQuadraticCutoff_outside n hi)

theorem unitSmoothQuadraticCutoff_odd (n : ℕ) (x : ℝ) :
    unitSmoothQuadraticCutoff n (-x) = -unitSmoothQuadraticCutoff n x := by
  simp only [unitSmoothQuadraticCutoff, unitSmoothQuintic_odd, cutoffRatio, neg_sq, neg_mul]

theorem unitSmoothQuadraticCutoff_abs_le_one (n : ℕ) (x : ℝ) :
    |unitSmoothQuadraticCutoff n x| ≤ 1 := by
  by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
  · obtain ⟨h0, h1⟩ := cutoffRatio_bounds hx
    rw [unitSmoothQuadraticCutoff, abs_mul, abs_of_nonneg h0]
    simpa only [one_mul] using mul_le_mul (unitSmoothQuintic_abs_le_one n x) h1 h0
      (by norm_num : (0 : ℝ) ≤ 1)
  · rw [unitSmoothQuadraticCutoff_outside n hx, abs_zero]
    norm_num

theorem unitSmoothQuadraticCutoff_lipschitz (n : ℕ) (x y : ℝ) :
    |unitSmoothQuadraticCutoff n x - unitSmoothQuadraticCutoff n y| ≤ 32*|x-y| := by
  have hon {a b : ℝ} (ha : a ∈ Icc (-(1/2 : ℝ)) (1/2))
      (hb : b ∈ Icc (-(1/2 : ℝ)) (1/2)) :
      |unitSmoothQuadraticCutoff n a - unitSmoothQuadraticCutoff n b| ≤ 32*|a-b| := by
    have hr := cutoffRatio_lipschitz.dist_le_mul a ha b hb
    simp only [Real.dist_eq] at hr
    change |cutoffRatio a-cutoffRatio b| ≤ (8 : ℝ)*|a-b| at hr
    have hq := unitSmoothQuintic_lipschitz n a b
    have h1 := mul_le_mul_of_nonneg_right hq (abs_nonneg (cutoffRatio a))
    have h2 := mul_le_mul_of_nonneg_left hr (abs_nonneg (unitSmoothQuintic n b))
    have h3 := mul_le_mul_of_nonneg_left (cutoffRatio_bounds ha).2
      (show 0 ≤ 24*|a-b| by positivity)
    have h4 := mul_le_mul_of_nonneg_right (unitSmoothQuintic_abs_le_one n b)
      (show 0 ≤ 8*|a-b| by positivity)
    rw [abs_of_nonneg (cutoffRatio_bounds ha).1] at h1
    have he : unitSmoothQuadraticCutoff n a - unitSmoothQuadraticCutoff n b =
        (unitSmoothQuintic n a-unitSmoothQuintic n b)*cutoffRatio a +
          unitSmoothQuintic n b*(cutoffRatio a-cutoffRatio b) := by
      unfold unitSmoothQuadraticCutoff
      ring
    rw [he]
    have ht := abs_add_le ((unitSmoothQuintic n a-unitSmoothQuintic n b)*cutoffRatio a)
      (unitSmoothQuintic n b*(cutoffRatio a-cutoffRatio b))
    rw [abs_mul, abs_mul, abs_of_nonneg (cutoffRatio_bounds ha).1] at ht
    linarith only [ht, h1, h2, h3, h4]
  have hab : -(1/2 : ℝ) ≤ 1/2 := by norm_num
  let c := Set.projIcc (-(1/2 : ℝ)) (1/2) hab
  have he (z : ℝ) : unitSmoothQuadraticCutoff n z = unitSmoothQuadraticCutoff n (c z) := by
    by_cases hl : z < -(1/2 : ℝ)
    · rw [unitSmoothQuadraticCutoff_outside n (fun h => not_lt_of_ge h.1 hl)]
      change 0 = unitSmoothQuadraticCutoff n ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
      rw [Set.projIcc_of_le_left hab hl.le]
      norm_num [unitSmoothQuadraticCutoff, cutoffRatio]
    · by_cases hr : (1/2 : ℝ) < z
      · rw [unitSmoothQuadraticCutoff_outside n (fun h => not_lt_of_ge h.2 hr)]
        change 0 = unitSmoothQuadraticCutoff n ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
        rw [Set.projIcc_of_right_le hab hr.le]
        norm_num [unitSmoothQuadraticCutoff, cutoffRatio]
      · change _ = unitSmoothQuadraticCutoff n ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
        rw [Set.projIcc_of_mem hab ⟨not_lt.mp hl, not_lt.mp hr⟩]
  have hc := (LipschitzWith.projIcc hab).dist_le_mul x y
  change dist (c x : ℝ) (c y : ℝ) ≤ 1*dist x y at hc
  simp only [Real.dist_eq, one_mul] at hc
  rw [he x, he y]
  exact (hon (c x).property (c y).property).trans
    (mul_le_mul_of_nonneg_left hc (by norm_num))

theorem unitSmoothQuadraticCutoff_tendsto (x : ℝ) :
    Tendsto (fun n => unitSmoothQuadraticCutoff n x) atTop (𝓝 (quadraticCutoffWindow x)) := by
  have he : quinticWindow x * cutoffRatio x = quadraticCutoffWindow x := by
    by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
    · rw [quinticWindow_inside hx.1 hx.2, quadraticCutoffWindow_inside hx.1 hx.2]
      have hd : 1-2*x^2 ≠ 0 := by linarith only [unit_square_le hx]
      unfold cutoffRatio
      field_simp
      ring
    · rw [quinticWindow_outside hx, quadraticCutoffWindow_outside hx, zero_mul]
  simpa only [unitSmoothQuadraticCutoff, he] using
    (unitSmoothQuintic_tendsto x).mul_const (cutoffRatio x)

/-- The exterior mass reserve alone cannot restore the retained Gamma form's sign. -/
theorem exists_odd_unit_reservedGamma_neg :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ x, F (-x) = -F x) ∧
      retainedOddGammaLowerForm F + (∫ x, F x^2)/64 < 0 := by
  have hp := retainedOddGammaLowerForm_tendsto_of_unit_window unitSmoothQuadraticCutoff_contDiff
    (fun n _ hx => unitSmoothQuadraticCutoff_outside n hx)
    unitSmoothQuadraticCutoff_abs_le_one unitSmoothQuadraticCutoff_lipschitz
    unitSmoothQuadraticCutoff_tendsto
  have hm := unitWindow_square_mass_tendsto unitSmoothQuadraticCutoff_contDiff
    (fun n _ hx => unitSmoothQuadraticCutoff_outside n hx)
    unitSmoothQuadraticCutoff_abs_le_one unitSmoothQuadraticCutoff_lipschitz
    unitSmoothQuadraticCutoff_tendsto
  obtain ⟨n, hn⟩ := ((hp.add (hm.div_const 64)).eventually
    (Iio_mem_nhds retainedOddGamma_quadraticCutoff_add_reserve_neg)).exists
  exact ⟨_, unitSmoothQuadraticCutoff_contDiff n, unitSmoothQuadraticCutoff_support n,
    unitSmoothQuadraticCutoff_odd n, hn⟩

/-- The sufficient two-moment first-fold form is negative on an actual smooth unit-window test. -/
theorem exists_odd_unit_firstFoldTwoMoment_neg :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ x, F (-x) = -F x) ∧ firstFoldTwoMomentForm (fun u => F ((1/2)*u)) < 0 := by
  obtain ⟨F, hF, hs, ho, hn⟩ := exists_odd_unit_reservedGamma_neg
  exact ⟨F, hF, hs, ho,
    (retainedOddGamma_add_reserve_ge_firstFoldTwoMomentForm hF hs ho).trans_lt hn⟩

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_odd_unit_reservedGamma_neg
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_odd_unit_firstFoldTwoMoment_neg
