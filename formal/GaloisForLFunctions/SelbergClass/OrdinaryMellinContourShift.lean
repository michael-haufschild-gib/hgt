import GaloisForLFunctions.SelbergClass.OrdinaryMellinResidues
import GaloisForLFunctions.SelbergClass.OrdinaryMellinContourBounds

/-!
# Ordinary Mellin contour shift below degree one

Moving from the line at two to a negative half-integer crosses the pole at one
and finitely many Gamma poles. The left integral vanishes for every positive
base, so the resulting Taylor partial sums converge at every positive point.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

/-- Coefficients in the ordinary exponential expansion. -/
def ordinaryTaylorCoeff (F : ExtendedSelbergClass) (k : ℕ) : ℂ :=
  (-1) ^ k / (k.factorial : ℂ) * F (-(k : ℂ))

theorem eventually_ordinaryMellin_contour_identity (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    {x : ℝ} (hx : 0 < x) :
    ∀ᶠ K : ℕ in atTop,
      (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) -
        (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) =
      2 * (Real.pi : ℂ) * (ordinaryPolarPart F (x : ℂ) +
        ∑ k ∈ Finset.range (K + 1), ordinaryTaylorCoeff F k * (x : ℂ) ^ k) := by
  classical
  obtain ⟨B, _, hev⟩ := eventually_integrable_ordinaryMellinIntegrand_left F hd0 hd1 0 hx
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hright := integrable_ordinaryMellinIntegrand_right F hx
  filter_upwards [hev] with K hK
  set a : ℝ := -(K : ℝ) - 1 / 2 with ha
  have ha0 : a < 0 := by dsimp only [a]; have := Nat.cast_nonneg (α := ℝ) K; linarith
  have hac : a < 2 := by linarith
  set P : Finset ℂ := insert 1 ((Finset.range (K + 1)).image fun k : ℕ => -(k : ℂ)) with hP
  have hnotin : (1 : ℂ) ∉ (Finset.range (K + 1)).image fun k : ℕ => -(k : ℂ) := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.1 h
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hPre : ∀ p ∈ P, a < p.re ∧ p.re < 2 := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · simp only [Complex.one_re]
      constructor <;> linarith
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
      have hkK : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      constructor <;> simp only [Complex.neg_re, Complex.natCast_re, a] <;> linarith
  have hmero : ∀ p ∈ P, MeromorphicAt (ordinaryMellinIntegrand F 0 (x : ℂ)) p :=
    fun p _ => meromorphicAt_ordinaryMellinIntegrand F 0 hx0 p
  have hoff : ∀ z : ℂ, a ≤ z.re → z.re ≤ 2 → z ∉ P →
      AnalyticAt ℂ (ordinaryMellinIntegrand F 0 (x : ℂ)) z := by
    intro z hza _ hzP
    refine analyticAt_ordinaryMellinIntegrand F 0 hx0 (fun k hk => ?_) (fun h => hzP ?_)
    · apply hzP
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, Finset.mem_range.2 ?_, hk.symm⟩)
      have hre := congrArg Complex.re hk
      simp at hre
      have : (k : ℝ) < K + 1 := by dsimp only [a] at hza; linarith
      exact_mod_cast this
    · simp only [zero_add] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨htop, hbot⟩ := tendsto_hIntegral_ordinaryMellinIntegrand F hx hac.le
  have hshift := verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq hac hPre hmero
    hoff hK.1 hright hT (htop.comp hT) (hbot.comp hT)
  change (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) -
      (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) = _ at hshift
  rw [hshift]
  congr 1
  rw [hP, Finset.sum_insert hnotin, Finset.sum_image (fun k _ k' _ h => by
    have := congrArg Complex.re h; simp at this; exact_mod_cast this)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [laurentCoeff_ordinaryMellinIntegrand_neg_nat F hx0 k, ordinaryTaylorCoeff]
  ring

/-- Taylor partial sums converge at every positive real argument. -/
theorem tendsto_ordinaryTaylor_partialSum (F : ExtendedSelbergClass)
    (hd0 : 0 < F.gammaData.degree) (hd1 : F.gammaData.degree < 1)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, ordinaryTaylorCoeff F k * (x : ℂ) ^ k)
      atTop (𝓝 ((∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) /
        (2 * (Real.pi : ℂ)) - ordinaryPolarPart F (x : ℂ))) := by
  have hleft := tendsto_integral_ordinaryMellinIntegrand_left F hd0 hd1 0 hx
  have hpi : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hlim : Tendsto (fun K : ℕ =>
      ((∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) /
        (2 * (Real.pi : ℂ)) - ordinaryPolarPart F (x : ℂ)) -
      (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) / (2 * (Real.pi : ℂ)))
      atTop (𝓝 ((∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) /
        (2 * (Real.pi : ℂ)) - ordinaryPolarPart F (x : ℂ))) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds.sub (hleft.div_const (2 * (Real.pi : ℂ))))
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine hlim.congr' ?_
  filter_upwards [eventually_ordinaryMellin_contour_identity F hd0 hd1 hx] with K hK
  field_simp
  linear_combination hK

end GaloisForLFunctions.SelbergClass
