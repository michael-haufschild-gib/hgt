import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalSmoothResponse
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-! Quantitative modular-cell counting and mean-square growth of the actual full-forcing response.
The estimates use the original native Hilbert vector and hyperbolic volume. -/

open Set UpperHalfPlane ModularGroup MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem modular_dist (A : SL(2, ℤ)) (z w : ℍ) :
    dist (A • z) (A • w) = dist z w := by
  change dist ((A.map (Int.castRingHom ℝ)) • z) ((A.map (Int.castRingHom ℝ)) • w) = _
  exact dist_smul _ _ _

private theorem bottom_height (A : SL(2, ℤ)) :
    (A • I).im = 1 / ((A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2) := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_apply]
  simp [Complex.normSq_apply, pow_two, add_comm]

private theorem row_positive (A : SL(2, ℤ)) :
    0 < (A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2 := by
  have h := (A • I).im_pos
  rw [bottom_height] at h
  exact (one_div_pos.mp h)

/-- Height distortion in the original hyperbolic radius. -/
theorem modular_bottom_row_height (A : SL(2, ℤ)) (z : ℍ) :
    ((A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2) * (A • z).im ≤ Real.exp (dist z I) := by
  have h := im_le_im_mul_exp_dist (A • z) (A • I)
  rw [modular_dist, bottom_height] at h
  have hp := row_positive A
  calc
    _ ≤ ((A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2) *
        ((1 / ((A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2)) * Real.exp (dist z I)) :=
      mul_le_mul_of_nonneg_left h hp.le
    _ = _ := by field_simp

/-- Every modular image of a radius-R point has height at most exp(R). -/
theorem modular_ball_height (A : SL(2, ℤ)) (z : ℍ) {R : ℝ} (hz : dist z I ≤ R) :
    (A • z).im ≤ Real.exp R := by
  have hu : z.im ≤ Real.exp R := by
    have h := im_le_im_mul_exp_dist z I
    simp only [I_im, one_mul] at h
    exact h.trans (Real.exp_le_exp.mpr hz)
  have hl : 1 / z.im ≤ Real.exp R := by
    apply (div_le_iff₀ z.im_pos).mpr
    have h := im_le_im_mul_exp_dist I z
    simp only [I_im, dist_comm I z] at h
    exact h.trans (by rw [mul_comm]; gcongr)
  exact (modular_orbit_height_le (QuotientGroup.mk A) z).trans (max_le hu hl)

/-- Quantitative bounds on both integer rows of every cell that meets a hyperbolic ball. -/
theorem modular_cell_row_bounds (A : SL(2, ℤ)) (z : ℍ) {R : ℝ}
    (hz : dist z I ≤ R) (hcell : A • z ∈ fd) :
    (A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2 ≤ 2 * Real.exp R ∧
    (A 0 0 : ℝ)^2 + (A 0 1 : ℝ)^2 ≤ 2 * (Real.exp R)^2 := by
  have hhalf : (1/2 : ℝ) ≤ (A • z).im := by
    have h := three_le_four_mul_im_sq_of_mem_fd hcell
    nlinarith [(A • z).im_pos]
  have hb := (modular_bottom_row_height A z).trans (Real.exp_le_exp.mpr hz)
  have hd : (A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2 ≤ 2 * Real.exp R := by
    nlinarith [row_positive A]
  refine ⟨hd, ?_⟩
  let w := A • z
  have hy : w.im ≤ Real.exp R := modular_ball_height A z hz
  have hn : 0 < w.re^2 + w.im^2 := by nlinarith [w.im_pos, sq_nonneg w.re]
  have hxy : w.re^2 ≤ w.im^2 := by
    have hr := abs_le.mp hcell.2
    change -(1/2 : ℝ) ≤ w.re ∧ w.re ≤ 1/2 at hr
    change (1/2 : ℝ) ≤ w.im at hhalf
    nlinarith [sq_nonneg (w.im - 1/2), sq_nonneg w.im]
  have ht := (modular_bottom_row_height (ModularGroup.S * A) z).trans (Real.exp_le_exp.mpr hz)
  have hr0 : ((ModularGroup.S * A) 1 0 : ℝ) = (A 0 0 : ℝ) := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S]
  have hr1 : ((ModularGroup.S * A) 1 1 : ℝ) = (A 0 1 : ℝ) := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S]
  rw [hr0, hr1, mul_smul] at ht
  change ((A 0 0 : ℝ)^2 + (A 0 1 : ℝ)^2) * (ModularGroup.S • w).im ≤ _ at ht
  rw [ModularGroup.im_smul_eq_div_normSq, denom_S] at ht
  simp only [Complex.normSq_apply, coe_re, coe_im, ← pow_two] at ht
  rw [← mul_div_assoc, div_le_iff₀ hn] at ht
  have ht' : (A 0 0 : ℝ)^2 + (A 0 1 : ℝ)^2 ≤ 2 * Real.exp R * w.im := by
    apply (mul_le_mul_iff_left₀ w.im_pos).mp
    nlinarith [mul_le_mul_of_nonneg_left hxy (Real.exp_pos R).le]
  exact ht'.trans (by nlinarith [mul_le_mul_of_nonneg_left hy (Real.exp_pos R).le])

/-- A fixed integer box contains every cell pullback meeting the radius-R ball. -/
theorem modular_cell_entry_bound (A : SL(2, ℤ)) (z : ℍ) {R : ℝ}
    (hR : 0 ≤ R) (hz : dist z I ≤ R) (hcell : A • z ∈ fd) (i j : Fin 2) :
    |(A i j : ℝ)| ≤ 2 * Real.exp R := by
  have he : 1 ≤ Real.exp R := Real.one_le_exp_iff.mpr hR
  obtain ⟨hb,ht⟩ := modular_cell_row_bounds A z hz hcell
  have hs : (A i j : ℝ)^2 ≤ 2 * (Real.exp R)^2 := by
    fin_cases i <;> fin_cases j
    · change (A 0 0 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 0 1 : ℝ)]
    · change (A 0 1 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 0 0 : ℝ)]
    · change (A 1 0 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 1 1 : ℝ), mul_nonneg (sub_nonneg.mpr he) (Real.exp_pos R).le]
    · change (A 1 1 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 1 0 : ℝ), mul_nonneg (sub_nonneg.mpr he) (Real.exp_pos R).le]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((A i j : ℝ) + 2 * Real.exp R),
    sq_nonneg ((A i j : ℝ) - 2 * Real.exp R)]

private def matrixBox (N : ℕ) : Finset (Fin 2 → Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N))

private theorem matrixBox_card (N : ℕ) : (matrixBox N).card = (2*N+1)^4 := by
  simp only [matrixBox, Fintype.card_piFinset, Fin.prod_univ_two, Int.card_Icc]
  have h : ((N : ℤ)+1-(-N)).toNat = 2*N+1 := by omega
  rw [h]
  ring

/-- The matrix box supplies a uniform exponential bound for all relevant finite cell families. -/
theorem modular_cell_family_card (R : ℝ) (hR : 0 ≤ R) (s : Finset PSL2Z)
    (hs : ∀ γ ∈ s, ∃ z : ℍ, dist z I ≤ R ∧ γ • z ∈ fd) :
    (s.card : ℝ) ≤ (7 * Real.exp R)^4 := by
  classical
  let N : ℕ := ⌈2 * Real.exp R⌉₊
  have hb : 2 * Real.exp R ≤ (N : ℝ) := Nat.le_ceil _
  have hc : s.card ≤ (matrixBox N).card := by
    apply Finset.card_le_card_of_injOn (fun γ : PSL2Z => (fun i j : Fin 2 => γ.out i j))
    · intro γ hγ
      obtain ⟨z,hz,hfd⟩ := hs γ hγ
      have hact : γ.out • z = γ • z := by
        have hrep : (QuotientGroup.mk γ.out : PSL2Z) = γ := Quotient.out_eq γ
        simpa only [PSL2Z_mk_smul] using congrArg (fun η : PSL2Z => η • z) hrep
      change (fun i j : Fin 2 => γ.out i j) ∈ matrixBox N
      simp only [matrixBox, Fintype.mem_piFinset, Finset.mem_Icc]
      intro i j
      have he := (modular_cell_entry_bound γ.out z hR hz (by rwa [hact]) i j).trans hb
      exact_mod_cast abs_le.mp he
    · intro γ _ δ _ he
      apply Quotient.out_injective
      apply Subtype.ext
      exact he
  rw [matrixBox_card] at hc
  have hn : (N : ℝ) < 2 * Real.exp R + 1 := Nat.ceil_lt_add_one (by positivity)
  have hE : 1 ≤ Real.exp R := Real.one_le_exp_iff.mpr hR
  have hsides : (2 * N + 1 : ℝ) ≤ 7 * Real.exp R := by nlinarith
  calc
    (s.card : ℝ) ≤ ((2*N+1 : ℕ) : ℝ)^4 := by exact_mod_cast hc
    _ = (2*(N:ℝ)+1)^4 := by norm_cast
    _ ≤ (7 * Real.exp R)^4 := by gcongr

/-- Every hyperbolic ball has an explicit exponentially bounded set of cell pullbacks. -/
theorem modular_ball_cell_cover (R : ℝ) (hR : 0 ≤ R) :
    ∃ s : Finset PSL2Z, (s.card : ℝ) ≤ (7 * Real.exp R)^4 ∧
      ∀ γ : PSL2Z, ∀ z : ℍ, dist z I ≤ R → γ • z ∈ fd → γ ∈ s := by
  classical
  obtain ⟨s,hs⟩ := compact_cell_pullbacks_finite (Metric.closedBall I R) (isCompact_closedBall I R)
  let t := s.filter (fun γ => ∃ z : ℍ, dist z I ≤ R ∧ γ • z ∈ fd)
  refine ⟨t, modular_cell_family_card R hR t ?_, ?_⟩
  · intro γ hγ
    exact (Finset.mem_filter.mp hγ).2
  · intro γ z hz hfd
    apply Finset.mem_filter.mpr
    refine ⟨?_,z,hz,hfd⟩
    by_contra hn
    exact hs γ hn z hz hfd

/-- The native scalar lift is controlled by the squared zero extensions of any covering cell family. -/
theorem globalLift_square_le_cell_sum (u : Space) (s : Finset PSL2Z) (z : ℍ)
    (hs : ∀ γ : PSL2Z, γ • z ∈ fd → γ ∈ s) :
    ‖globalLift u z‖^2 ≤ ∑ γ ∈ s, ‖cellExtension u (γ • z)‖^2 := by
  classical
  by_cases h : ∃ γ : PSL2Z, γ • z ∈ fdo
  · obtain ⟨γ,hγ⟩ := h
    have he : globalLift u z = cellExtension u (γ • z) := by
      rw [← globalLift_invariant u γ z]
      exact globalLift_eq_on_fd u _ (fdo_subset_fd hγ)
    rw [he]
    exact Finset.single_le_sum (fun δ _ => sq_nonneg (‖cellExtension u (δ • z)‖)) (hs γ (fdo_subset_fd hγ))
  · have hz : globalLift u z = 0 := by
      change (∑' γ : PSL2Z, cellExtension u (γ • z)) = 0
      have he (γ : PSL2Z) : cellExtension u (γ • z) = 0 :=
        Set.indicator_of_notMem (fun hγ => h ⟨γ,hγ⟩) _
      simp only [he, tsum_zero]
    rw [hz, norm_zero, zero_pow (by decide)]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem integral_cell_family_bound (f g : ℍ → ℂ) (s : Finset PSL2Z) (R : ℝ)
    (hf : Integrable (fun z : ℍ => ‖f z‖^2))
    (hg : IntegrableOn (fun z : ℍ => ‖g z‖^2) (Metric.closedBall I R))
    (hp : ∀ z ∈ Metric.closedBall I R, ‖g z‖^2 ≤ ∑ γ ∈ s, ‖f (γ • z)‖^2) :
    (∫ z : ℍ in Metric.closedBall I R, ‖g z‖^2) ≤
      (s.card : ℝ) * (∫ z : ℍ, ‖f z‖^2) := by
  have ht (γ : PSL2Z) : Integrable (fun z : ℍ => ‖f (γ • z)‖^2) :=
    (measurePreserving_smul γ (volume : Measure ℍ)).integrable_comp_of_integrable
      (g := fun z : ℍ => ‖f z‖^2) hf
  have hsum : IntegrableOn (fun z : ℍ => ∑ γ ∈ s, ‖f (γ • z)‖^2)
      (Metric.closedBall I R) := integrable_finsetSum s (fun γ _ => (ht γ).integrableOn)
  calc
    _ ≤ ∫ z : ℍ in Metric.closedBall I R, ∑ γ ∈ s, ‖f (γ • z)‖^2 := by
      apply integral_mono_ae hg hsum
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
      exact hp z hz
    _ = ∑ γ ∈ s, ∫ z : ℍ in Metric.closedBall I R, ‖f (γ • z)‖^2 :=
      integral_finsetSum s (fun γ _ => (ht γ).integrableOn)
    _ ≤ ∑ γ ∈ s, ∫ z : ℍ, ‖f (γ • z)‖^2 := by
      apply Finset.sum_le_sum
      intro γ _
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun z => sq_nonneg (‖f (γ • z)‖))) (ht γ)
    _ = _ := by
      have he (γ : PSL2Z) : (∫ z : ℍ, ‖f (γ • z)‖^2) = ∫ z : ℍ, ‖f z‖^2 :=
        (measurePreserving_smul γ volume).integral_comp
          (measurableEmbedding_const_smul γ) (fun z : ℍ => ‖f z‖^2)
      simp only [he, Finset.sum_const, nsmul_eq_mul]

/-- Uniform exponential mean-square growth of the original modular lift, with no growth premise. -/
theorem globalLift_ball_square_bound (u : Space) (R : ℝ) (hR : 0 ≤ R) :
    (∫ z : ℍ in Metric.closedBall I R, ‖globalLift u z‖^2) ≤
      (7 * Real.exp R)^4 * (∫ z : ℍ, ‖cellExtension u z‖^2) := by
  obtain ⟨s,hcard,hcover⟩ := modular_ball_cell_cover R hR
  have hi : Integrable (fun z : ℍ => ‖cellExtension u z‖^2) :=
    (cellExtension_memLp u).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hlocal : IntegrableOn (fun z : ℍ => ‖globalLift u z‖^2) (Metric.closedBall I R) :=
    (globalLift_memLp_compact u _ (isCompact_closedBall I R)).integrable_norm_pow
      (by norm_num : (2:ℕ) ≠ 0)
  have hb := integral_cell_family_bound (cellExtension u) (globalLift u) s R hi hlocal
    (fun z hz => globalLift_square_le_cell_sum u s z (fun γ hγ => hcover γ z hz hγ))
  exact hb.trans (mul_le_mul_of_nonneg_right hcard
    (integral_nonneg (fun z : ℍ => sq_nonneg (‖cellExtension u z‖))))

/-- The estimate applies to the actual smooth full-forcing response, not an auxiliary representative. -/
theorem globalResponse_ball_square_bound (q : XiZeroCopy) (branch : Bool) (R : ℝ)
    (hR : 0 ≤ R) :
    (∫ z : ℍ in Metric.closedBall I R, ‖globalResponse q branch z‖^2) ≤
      (7 * Real.exp R)^4 *
        (∫ z : ℍ, ‖cellExtension (embedding (weakResponse q branch)) z‖^2) := by
  have he : (∫ z : ℍ in Metric.closedBall I R, ‖globalResponse q branch z‖^2) =
      (∫ z : ℍ in Metric.closedBall I R,
        ‖globalLift (embedding (weakResponse q branch)) z‖^2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (globalResponse_ae_lift q branch)] with z hz
    rw [hz]
  rw [he]
  exact globalLift_ball_square_bound _ R hR

end
end RHTower.D4BMModularCore
