import GaloisForLFunctions.RHTower.SarnakXueCuspTail
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.SelbergMaassBesselRemainder
import GaloisForLFunctions.RHTower.SelbergMaassTailEnergy

open MeasureTheory Set Filter Topology UpperHalfPlane

/-!
# The cusp carries a bounded fraction of the mass of an exceptional Maass form

For a `Γ(p)` Maass cusp form (`p = N + 1 ≥ 2`) with `0 < λ < 1/4`, every nonzero Fourier mode has
frequency `k` with `k² y₁² ≥ 1/4 > λ` for `y₁ = max(1, p/(4π))` (`edge`), so its squared modulus is
nonincreasing beyond `y₁` (`mode_antitone`) and `p ∫_p^∞ |a_n|²/y² ≤ y₁ ∫_1^∞ |a_n|²/y²`
(`mode_tail_fraction`; the constant mode vanishes). Summing by Parseval:
`p ∫_p^∞ mass/y² ≤ y₁ ∫_1^∞ mass/y²` (`mass_tail_fraction`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueCuspMode

open SarnakXueCuspTail SelbergMaassFourier

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The lower edge `max(1, (N+1)/(4π))` beyond which every nonzero mode decays monotonically. -/
noncomputable def edge : ℝ := max 1 (((N + 1 : ℕ) : ℝ) / (4 * Real.pi))

theorem edge_pos : 0 < edge N := lt_of_lt_of_le one_pos (le_max_left _ _)

theorem edge_lt (hN : 1 ≤ N) : edge N < ((N + 1 : ℕ) : ℝ) := by
  unfold edge
  have hpi := Real.pi_gt_three
  have hN' : (2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ N + 1 by omega)
  apply max_lt (by linarith)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem mode_antitone (hlam : lam < 1 / 4) {n : ℤ} (hn : n ≠ 0) :
    AntitoneOn (fun y => Complex.normSq (maassCoefficient N f n y)) (Ici (edge N)) := by
  apply normSq_antitoneOn (k := signedFrequency (N + 1 : ℕ) n) (lam := lam) (edge_pos N)
  · -- `λ ≤ k² y₁²`
    have hk : (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ 2 ≤ signedFrequency (N + 1 : ℕ) n ^ 2 := by
      unfold signedFrequency
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
        exact_mod_cast this
      rw [div_pow, div_pow, mul_pow, mul_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs]; nlinarith
      nlinarith [sq_nonneg (2 : ℝ), sq_nonneg Real.pi]
    have hy : ((N + 1 : ℕ) : ℝ) / (4 * Real.pi) ≤ edge N := le_max_right _ _
    have hpos : 0 < ((N + 1 : ℕ) : ℝ) / (4 * Real.pi) := by positivity
    have h14 : (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ 2 * (((N + 1 : ℕ) : ℝ) / (4 * Real.pi)) ^ 2 = 1 / 4 := by
      field_simp; ring
    calc lam ≤ 1 / 4 := hlam.le
      _ = (2 * Real.pi / ((N + 1 : ℕ) : ℝ)) ^ 2 * (((N + 1 : ℕ) : ℝ) / (4 * Real.pi)) ^ 2 := h14.symm
      _ ≤ signedFrequency (N + 1 : ℕ) n ^ 2 * edge N ^ 2 := by
          gcongr
  · exact fun y hy => maassCoefficient_hasDerivAt N f n hy
  · exact fun y hy => maassCoefficient_second_hasDerivAt N f n hy
  · intro y hy
    have := maassCoefficient_modal_equation N f n hy
    exact_mod_cast this
  · exact maassCoefficient_decay N f n

theorem coeff_continuousOn (n : ℤ) : ContinuousOn (maassCoefficient N f n) (Ioi 0) :=
  fun _ hy => (maassCoefficient_hasDerivAt N f n hy).continuousAt.continuousWithinAt

theorem coeff_bounded (n : ℤ) {y₁ : ℝ} (hy₁ : 0 < y₁) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, y₁ ≤ y → Complex.normSq (maassCoefficient N f n y) ≤ M := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((maassCoefficient_decay N f n).eventually (Metric.ball_mem_nhds 0 one_pos))
  have hcont : ContinuousOn (fun y => Complex.normSq (maassCoefficient N f n y)) (Icc y₁ (max A y₁)) :=
    Complex.continuous_normSq.comp_continuousOn ((coeff_continuousOn N f n).mono
      (fun y hy => lt_of_lt_of_le hy₁ hy.1))
  obtain ⟨M, hM⟩ := (isCompact_Icc.bddAbove_image hcont)
  refine ⟨max M 1, le_max_of_le_right zero_le_one, fun y hy => ?_⟩
  by_cases hyA : y ≤ max A y₁
  · exact (hM ⟨y, ⟨hy, hyA⟩, rfl⟩).trans (le_max_left _ _)
  · push Not at hyA
    have := hA y ((le_max_left A y₁).trans hyA.le)
    rw [dist_zero_right] at this
    rw [Complex.normSq_eq_norm_sq]
    have h0 := norm_nonneg (maassCoefficient N f n y)
    nlinarith [le_max_right M 1]

theorem mode_integrable (n : ℤ) {y₁ : ℝ} (hy₁ : 0 < y₁) :
    IntegrableOn (fun y => Complex.normSq (maassCoefficient N f n y) / y ^ 2) (Ioi y₁) := by
  obtain ⟨M, hM0, hM⟩ := coeff_bounded N f n hy₁
  refine Integrable.mono' ((integrableOn_inv_sq hy₁).const_mul M) ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := hy₁.trans hy
    exact ((Complex.continuous_normSq.continuousAt.comp
      (maassCoefficient_hasDerivAt N f n hy0).continuousAt).div
      (continuousAt_id.pow 2) (pow_pos hy0 2).ne').continuousWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    have hy0 : 0 < y := hy₁.trans hy
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (by positivity))]
    calc Complex.normSq (maassCoefficient N f n y) / y ^ 2
        = Complex.normSq (maassCoefficient N f n y) * (1 / y ^ 2) := by ring
      _ ≤ M * (1 / y ^ 2) := mul_le_mul_of_nonneg_right (hM y (le_of_lt hy)) (by positivity)

/-- **Cusp tail of one nonzero mode.** With `p = N + 1 ≥ 2` and `y₁ = max(1, p/(4π))`,
`(p - y₁) ∫_p^∞ |a_n|²/y² ≤ y₁ ∫_{y₁}^p |a_n|²/y²` for every `n ≠ 0`. -/
theorem mode_tail (hN : 1 ≤ N) (hlam : lam < 1 / 4) {n : ℤ} (hn : n ≠ 0) :
    (((N + 1 : ℕ) : ℝ) - edge N) *
        ∫ y in Ioi ((N + 1 : ℕ) : ℝ), Complex.normSq (maassCoefficient N f n y) / y ^ 2 ≤
      edge N * ∫ y in Ioc (edge N) ((N + 1 : ℕ) : ℝ),
        Complex.normSq (maassCoefficient N f n y) / y ^ 2 :=
  tail_le_bulk (edge_pos N) (edge_lt N hN) (mode_antitone N f hlam hn)
    (fun _ _ => Complex.normSq_nonneg _) (mode_integrable N f n (edge_pos N))

open SelbergMaassFlux SelbergMaassTailEnergy in
/-- The hyperbolic tail mass is the sum of the modal tail masses. -/
theorem tail_hasSum (lam : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    HasSum (fun n : ℤ => ∫ y in Ioi Y, Complex.normSq (maassCoefficient N g n y) / y ^ 2)
      (∫ y in Ioi Y, mass N g y / y ^ (2 : ℕ)) := by
  apply hasSum_integral_of_dominated_convergence
    (fun n y => Complex.normSq (maassCoefficient N g n y) / y ^ 2)
    (fun n => (mode_integrable N g n hY).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ((mass_hasSum N g (hY.trans hy)).div_const _).summable
  · apply (hyperbolicMass_tail_integrable N lam g hY).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (((mass_hasSum N g (hY.trans hy)).div_const (y ^ 2)).tsum_eq).symm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (mass_hasSum N g (hY.trans hy)).div_const (y ^ 2)

/-- One mode: `p ∫_p^∞ |a_n|²/y² ≤ y₁ ∫_1^∞ |a_n|²/y²`, including the vanishing constant mode. -/
theorem mode_tail_fraction (hN : 1 ≤ N) (lam : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (n : ℤ) :
    ((N + 1 : ℕ) : ℝ) * ∫ y in Ioi ((N + 1 : ℕ) : ℝ), Complex.normSq (maassCoefficient N g n y) / y ^ 2 ≤
      edge N * ∫ y in Ioi (1 : ℝ), Complex.normSq (maassCoefficient N g n y) / y ^ 2 := by
  set F : ℝ → ℝ := fun y => Complex.normSq (maassCoefficient N g n y) / y ^ 2
  have hFnn : ∀ y, 0 ≤ F y := fun y => div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
  set p : ℝ := ((N + 1 : ℕ) : ℝ)
  have hp1 : (1 : ℝ) < p := by
    have : (2 : ℝ) ≤ p := by simp only [p]; exact_mod_cast (show 2 ≤ N + 1 by omega)
    linarith
  have hedge1 : 1 ≤ edge N := le_max_left _ _
  have hi1 := mode_integrable N g n (zero_lt_one' ℝ)
  have hsplit : ∫ y in Ioi (1 : ℝ), F y = (∫ y in Ioc 1 p, F y) + ∫ y in Ioi p, F y := by
    rw [← Ioc_union_Ioi_eq_Ioi hp1.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hi1.mono_set Ioc_subset_Ioi_self) (hi1.mono_set (Ioi_subset_Ioi hp1.le))]
  have hTnn : 0 ≤ ∫ y in Ioi p, F y := setIntegral_nonneg measurableSet_Ioi (fun y _ => hFnn y)
  by_cases hn : n = 0
  · subst hn
    have hz : ∫ y in Ioi p, F y = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      simp only [F, SelbergMaassBessel.constant_mode_zero N lam g (zero_lt_one.trans (hp1.trans hy)),
        map_zero, zero_div]
    rw [hz, mul_zero]
    exact mul_nonneg (by linarith) (setIntegral_nonneg measurableSet_Ioi (fun y _ => hFnn y))
  · have h := mode_tail N g hN lam.2.2 hn
    have hB : ∫ y in Ioc (edge N) p, F y ≤ ∫ y in Ioc 1 p, F y :=
      setIntegral_mono_set (hi1.mono_set Ioc_subset_Ioi_self)
        (Filter.Eventually.of_forall (fun y => hFnn y))
        (Filter.Eventually.of_forall (Ioc_subset_Ioc_left hedge1))
    rw [hsplit]
    have hy1 : 0 ≤ edge N := (edge_pos N).le
    nlinarith [mul_le_mul_of_nonneg_left hB hy1]

open SelbergMaassFlux in
/-- **Cusp tail fraction.** For `p = N + 1 ≥ 2` and `0 < λ < 1/4`,
`p ∫_p^∞ mass/y² ≤ max(1, p/(4π)) ∫_1^∞ mass/y²`. -/
theorem mass_tail_fraction (hN : 1 ≤ N) (lam : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    ((N + 1 : ℕ) : ℝ) * ∫ y in Ioi ((N + 1 : ℕ) : ℝ), mass N g y / y ^ (2 : ℕ) ≤
      edge N * ∫ y in Ioi (1 : ℝ), mass N g y / y ^ (2 : ℕ) := by
  have hp : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have h1 := tail_hasSum N lam g hp
  have h2 := tail_hasSum N lam g (zero_lt_one' ℝ)
  rw [← h1.tsum_eq, ← h2.tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
  exact (h1.summable.mul_left _).tsum_le_tsum (fun n => mode_tail_fraction N hN lam g n)
    (h2.summable.mul_left _)

end GaloisForLFunctions.RHTower.SarnakXueCuspMode
