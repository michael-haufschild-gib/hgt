import GaloisForLFunctions.CollectiveDiophantineGeometry.FiniteTimeReturnCounts
import GaloisForLFunctions.CollectiveDiophantineGeometry.WeightedCoordinateSeparation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Weighted heavy-return counts

A positive product of short geometric kernels detects a prescribed returning
weight. Coordinate separation removes all off-diagonal frequencies of every
subproduct. The resulting measure bound depends on total weight divided by
its largest allowed coordinate weight, without a union over returning sets.
-/


set_option autoImplicit false
noncomputable section
open Finset Real MeasureTheory
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open TranscendenceTheoryOfThePrimeOrbit RHTower.Matveev

/-- Normalized geometric kernel, with constant Fourier coefficient `1/(H+1)`. -/
def returnKernel (H : ℕ) (x : ℝ) : ℝ :=
  ‖∑ n : Fin (H + 1), phaseExp x ^ (n : ℕ)‖ ^ 2 / (H + 1 : ℝ) ^ 2

theorem returnKernel_nonneg (H : ℕ) (x : ℝ) : 0 ≤ returnKernel H x := by
  unfold returnKernel
  positivity

theorem continuous_returnKernel (H : ℕ) : Continuous (returnKernel H) := by
  unfold returnKernel phaseExp
  fun_prop

/-- At the stated chord precision the kernel is at least one quarter. -/
theorem returnKernel_ge_quarter {H : ℕ} {x : ℝ}
    (hx : ‖phaseExp x - 1‖ ≤ 1 / (2 * (H + 1 : ℝ))) :
    1 / 4 ≤ returnKernel H x := by
  have h := half_le_norm_phase_average (norm_phaseExp x) hx
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H + 1 : ℝ) / 2) h 2
  unfold returnKernel
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (H + 1 : ℝ) ^ 2)).mpr
  nlinarith only [hs]

private theorem product_returnKernel_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ℓ θ : ι → ℝ) (H : ℕ) (t : ℝ) :
    (∏ j, returnKernel H (ℓ j * t - θ j)) =
      ‖phaseSum (fun a : ι → Fin (H + 1) => ∑ j, (a j : ℝ) * ℓ j)
        (fun a => ∑ j, (a j : ℝ) * θ j) t‖ ^ 2 /
          (H + 1 : ℝ) ^ (2 * Fintype.card ι) := by
  classical
  simp only [returnKernel, Finset.prod_div_distrib, Finset.prod_pow,
    ← norm_prod, Finset.prod_const, Finset.card_univ, ← pow_mul]
  simp only [phaseSum_box_eq_prod, Nat.mul_comm]

/-- Every subproduct of kernels has its diagonal mean-square bound when
all supported coefficient differences satisfy the separation floor. -/
theorem integral_returnKernel_product_le {k H : ℕ}
    (p : Fin k → ℕ) (θ : Fin k → ℝ) (J K : Finset (Fin k)) (hK : K ⊆ J)
    {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ v : Fin k → ℤ, (∀ j, j ∉ J → v j = 0) →
      (∀ j, |(v j : ℝ)| ≤ H) → v ≠ 0 → δ ≤ |primeLogForm p v|)
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    (∫ t in A..A + T, ∏ j ∈ K, returnKernel H (log (p j) * t - θ j)) ≤
      (5 * π / 2) * max (T / 2) δ⁻¹ / (H + 1 : ℝ) ^ K.card := by
  classical
  let ω : (K → Fin (H + 1)) → ℝ := fun a => ∑ j, (a j : ℝ) * log (p j)
  let ψ : (K → Fin (H + 1)) → ℝ := fun a => ∑ j, (a j : ℝ) * θ j
  have hdistinct : ∀ a b : K → Fin (H + 1), a ≠ b → δ ≤ |ω a - ω b| := by
    intro a b hab
    let v : Fin k → ℤ := fun j => if hj : j ∈ K then
      ((a ⟨j, hj⟩ : ℕ) : ℤ) - ((b ⟨j, hj⟩ : ℕ) : ℤ) else 0
    have hsupp : ∀ j, j ∉ J → v j = 0 := by
      intro j hj
      exact dif_neg (fun hjK => hj (hK hjK))
    have hheight : ∀ j, |(v j : ℝ)| ≤ H := by
      intro j
      by_cases hj : j ∈ K
      · have ha := (a ⟨j, hj⟩).isLt
        have hb := (b ⟨j, hj⟩).isLt
        have hi : |((a ⟨j, hj⟩ : ℕ) : ℤ) - ((b ⟨j, hj⟩ : ℕ) : ℤ)| ≤ (H : ℤ) := by
          rw [abs_le]
          constructor <;> omega
        simpa only [v, dif_pos hj, Int.cast_sub, Int.cast_natCast] using
          (show |(((a ⟨j, hj⟩ : ℕ) : ℤ) - ((b ⟨j, hj⟩ : ℕ) : ℤ) : ℝ)| ≤ H by exact_mod_cast hi)
      · simp only [v, dif_neg hj, Int.cast_zero, abs_zero]
        positivity
    have hne : v ≠ 0 := by
      intro hv
      apply hab
      funext j
      apply Fin.ext
      have h := congrFun hv j
      simp only [v, dif_pos j.property, Pi.zero_apply] at h
      change ((a j : ℕ) : ℤ) - ((b j : ℕ) : ℤ) = 0 at h
      omega
    have heval : primeLogForm p v = ω a - ω b := by
      unfold primeLogForm
      calc
        _ = ∑ j ∈ K, (v j : ℝ) * log (p j) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ K)
          intro j _ hj
          simp only [v, dif_neg hj, Int.cast_zero, zero_mul]
        _ = ∑ j : K, (v j : ℝ) * log (p j) := (Finset.sum_coe_sort K _).symm
        _ = _ := by
          simp only [v, dif_pos, Subtype.property, Int.cast_sub, Int.cast_natCast,
            sub_mul, Finset.sum_sub_distrib, ω]
    simpa only [heval] using hsep v hsupp hheight hne
  have hpairs : (univ.filter fun ab : (K → Fin (H + 1)) × (K → Fin (H + 1)) =>
      |ω ab.1 - ω ab.2| < δ).card = (H + 1) ^ K.card := by
    have heq : (univ.filter fun ab : (K → Fin (H + 1)) × (K → Fin (H + 1)) =>
        |ω ab.1 - ω ab.2| < δ) = (univ : Finset (K → Fin (H + 1))).diag := by
      ext ab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_diag]
      constructor
      · intro h
        by_contra hne
        exact (not_lt_of_ge (hdistinct ab.1 ab.2 hne)) h
      · intro h
        simp only [h, sub_self, abs_zero]
        exact hδ
    rw [heq, Finset.diag_card]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hi := integral_phaseSum_norm_sq_le_collision ω ψ hT hδ A
  rw [hpairs] at hi
  have hfun (t : ℝ) : (∏ j ∈ K, returnKernel H (log (p j) * t - θ j)) =
      ‖phaseSum ω ψ t‖ ^ 2 / (H + 1 : ℝ) ^ (2 * K.card) := by
    rw [← Finset.prod_coe_sort]
    simpa only [Fintype.card_coe] using
      product_returnKernel_eq (fun j : K => log (p j)) (fun j : K => θ j) H t
  simp_rw [hfun]
  rw [intervalIntegral.integral_div]
  have hN : (0 : ℝ) < H + 1 := by positivity
  calc
    _ ≤ ((5 * π / 2) * max (T / 2) δ⁻¹ * (H + 1 : ℝ) ^ K.card) /
        (H + 1 : ℝ) ^ (2 * K.card) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hi
    _ = _ := by
      rw [show 2 * K.card = K.card + K.card by omega, pow_add]
      field_simp

/-- Positive product detector with arbitrary nonnegative activation weights. -/
def weightedReturnDetector {k : ℕ} (p : Fin k → ℕ) (θ u : Fin k → ℝ)
    (H : ℕ) (J : Finset (Fin k)) (t : ℝ) : ℝ :=
  ∏ j ∈ J, (1 + u j * returnKernel H (log (p j) * t - θ j))

theorem continuous_weightedReturnDetector {k : ℕ} (p : Fin k → ℕ)
    (θ u : Fin k → ℝ) (H : ℕ) (J : Finset (Fin k)) :
    Continuous (weightedReturnDetector p θ u H J) := by
  unfold weightedReturnDetector
  exact continuous_finsetProd _ fun j _ => continuous_const.add
    (continuous_const.mul ((continuous_returnKernel H).comp (by fun_prop)))

private theorem prod_one_add_eq_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    (∏ j ∈ s, (1 + f j)) = ∑ K ∈ s.powerset, ∏ j ∈ K, f j := by
  simp_rw [add_comm (1 : ℝ)]
  rw [Finset.prod_add]
  simp

/-- The product detector keeps the product of constant coefficients;
there is no enumeration loss for the possible returning coordinate sets. -/
theorem integral_weightedReturnDetector_le {k H : ℕ}
    (p : Fin k → ℕ) (θ u : Fin k → ℝ) (J : Finset (Fin k))
    (hu : ∀ j, 0 ≤ u j) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ v : Fin k → ℤ, (∀ j, j ∉ J → v j = 0) →
      (∀ j, |(v j : ℝ)| ≤ H) → v ≠ 0 → δ ≤ |primeLogForm p v|)
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    (∫ t in A..A + T, weightedReturnDetector p θ u H J t) ≤
      (5 * π / 2) * max (T / 2) δ⁻¹ * ∏ j ∈ J, (1 + u j / (H + 1 : ℝ)) := by
  classical
  let B := (5 * π / 2) * max (T / 2) δ⁻¹
  have hcont (K : Finset (Fin k)) :
      Continuous fun t => ∏ j ∈ K, returnKernel H (log (p j) * t - θ j) :=
    continuous_finsetProd _ fun j _ => (continuous_returnKernel H).comp (by fun_prop)
  have heq (t : ℝ) : weightedReturnDetector p θ u H J t =
      ∑ K ∈ J.powerset, (∏ j ∈ K, u j) * ∏ j ∈ K, returnKernel H (log (p j) * t - θ j) := by
    rw [weightedReturnDetector, prod_one_add_eq_sum]
    simp only [Finset.prod_mul_distrib]
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ ∑ K ∈ J.powerset, (∏ j ∈ K, u j) * (B / (H + 1 : ℝ) ^ K.card) := by
        apply Finset.sum_le_sum
        intro K hK
        exact mul_le_mul_of_nonneg_left
          (integral_returnKernel_product_le p θ J K (Finset.mem_powerset.mp hK) hδ hsep hT A)
          (Finset.prod_nonneg fun j _ => hu j)
      _ = B * ∏ j ∈ J, (1 + u j / (H + 1 : ℝ)) := by
        rw [prod_one_add_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro K _
        rw [Finset.prod_div_distrib, Finset.prod_const]
        ring
  · intro K _
    exact ((hcont K).const_mul _).intervalIntegrable _ _

private theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    exp x - 1 ≤ 2 * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (sub_nonneg.mpr hx1) hx (by ring : 1 - x + x = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, exp_zero] at h
  have hmul := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le hx
  nlinarith only [h, hmul]

/-- A weighted chord-return window; the missing weight is at most one eighth. -/
def weightedChordReturnWindow {k : ℕ} (p : Fin k → ℕ) (θ w : Fin k → ℝ)
    (ε A T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc A (A + T) ∧
    (∑ j, if ‖phaseExp (log (p j) * t - θ j) - 1‖ ≤ ε then 0 else w j) ≤
      (∑ j, w j) / 8}


private theorem activation_product_le {k H : ℕ}
    (w : Fin k → ℝ) {M : ℝ} (hM : 0 < M)
    (hw : ∀ j, 0 ≤ w j) (hwM : ∀ j, w j ≤ M) (hH : 16 ≤ H + 1)
    (J : Finset (Fin k)) :
    (∏ j ∈ J, (1 + 4 * (exp (w j / M) - 1) / (H + 1 : ℝ))) ≤
      exp ((∑ j ∈ J, w j) / (2 * M)) := by
  have hN : (0 : ℝ) < H + 1 := by positivity
  have hN16 : (16 : ℝ) ≤ H + 1 := by exact_mod_cast hH
  have hfactor (j : Fin k) : 1 + 4 * (exp (w j / M) - 1) / (H + 1 : ℝ) ≤
      exp (8 * (w j / M) / (H + 1 : ℝ)) := by
    have hx0 := div_nonneg (hw j) hM.le
    have hx1 : w j / M ≤ 1 := (div_le_one hM).mpr (hwM j)
    have he := exp_sub_one_le_two_mul hx0 hx1
    calc
      _ ≤ 1 + 8 * (w j / M) / (H + 1 : ℝ) := by
        have hcoef : 4 * (exp (w j / M) - 1) ≤ 8 * (w j / M) := by
          nlinarith only [he]
        exact add_le_add (le_refl 1) (div_le_div_of_nonneg_right hcoef hN.le)
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (8 * (w j / M) / (H + 1 : ℝ))
  have hu (j : Fin k) : 0 ≤ 4 * (exp (w j / M) - 1) := by
    have he := (Real.one_le_exp_iff.mpr (div_nonneg (hw j) hM.le))
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr he)
  calc
    _ ≤ ∏ j ∈ J, exp (8 * (w j / M) / (H + 1 : ℝ)) :=
      Finset.prod_le_prod (fun j _ => by have := hu j; positivity) (fun j _ => hfactor j)
    _ = exp (8 * ((∑ j ∈ J, w j) / M) / (H + 1 : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : 0 ≤ (∑ j ∈ J, w j) / M := div_nonneg (Finset.sum_nonneg fun j _ => hw j) hM.le
      have hc : 8 / (H + 1 : ℝ) ≤ 1 / 2 := (div_le_iff₀ hN).mpr (by linarith only [hN16])
      calc
        _ = ((∑ j ∈ J, w j) / M) * (8 / (H + 1 : ℝ)) := by ring
        _ ≤ ((∑ j ∈ J, w j) / M) * (1 / 2) := mul_le_mul_of_nonneg_left hc hs
        _ = _ := by field_simp

private theorem detector_ge_on_weighted_return {k H : ℕ}
    (p : Fin k → ℕ) (θ w : Fin k → ℝ) {M : ℝ} (hM : 0 < M)
    (hw : ∀ j, 0 ≤ w j) (J : Finset (Fin k))
    (hweight : (∑ j, w j) ≤ 2 * ∑ j ∈ J, w j)
    {t : ℝ}
    (hret : (∑ j, if ‖phaseExp (log (p j) * t - θ j) - 1‖ ≤
      1 / (2 * (H + 1 : ℝ)) then 0 else w j) ≤ (∑ j, w j) / 8) :
    exp (3 * (∑ j ∈ J, w j) / (4 * M)) ≤
      weightedReturnDetector p θ (fun j => 4 * (exp (w j / M) - 1)) H J t := by
  classical
  let good : Fin k → Prop := fun j => ‖phaseExp (log (p j) * t - θ j) - 1‖ ≤
    1 / (2 * (H + 1 : ℝ))
  let g : Fin k → ℝ := fun j => if good j then w j else 0
  let b : Fin k → ℝ := fun j => if good j then 0 else w j
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    dsimp [b]
    split_ifs
    · exact le_rfl
    · exact hw j
  have hb : (∑ j ∈ J, b j) ≤ (∑ j, w j) / 8 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun j _ _ => hb0 j)).trans hret
  have hsplit : (∑ j ∈ J, g j) + (∑ j ∈ J, b j) = ∑ j ∈ J, w j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g, b]
    split_ifs <;> ring
  have hgood : 3 * (∑ j ∈ J, w j) / 4 ≤ ∑ j ∈ J, g j := by
    linarith only [hb, hsplit, hweight]
  have hfactor (j : Fin k) : exp (g j / M) ≤
      1 + 4 * (exp (w j / M) - 1) * returnKernel H (log (p j) * t - θ j) := by
    have hexp : 0 ≤ exp (w j / M) - 1 := sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (div_nonneg (hw j) hM.le))
    by_cases hj : good j
    · have hk := returnKernel_ge_quarter hj
      have hm := mul_le_mul_of_nonneg_left hk hexp
      simp only [g, if_pos hj]
      nlinarith only [hm]
    · simp only [g, if_neg hj, zero_div, exp_zero]
      have hk := returnKernel_nonneg H (log (p j) * t - θ j)
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hexp) hk)
  calc
    _ ≤ exp ((∑ j ∈ J, g j) / M) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (3 * (∑ j ∈ J, w j) / 4) / M := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hgood hM.le
    _ = ∏ j ∈ J, exp (g j / M) := by rw [Finset.sum_div, Real.exp_sum]
    _ ≤ _ := Finset.prod_le_prod (fun j _ => (exp_pos _).le) (fun j _ => hfactor j)

/-- Actual weighted prime returns have exponentially small measure in the
ratio of total mass to the maximum coordinate weight. All arithmetic inputs
are discharged by the prime-coordinate separation theorem. -/
theorem measure_weightedChordReturnWindow_le {k H : ℕ}
    (p : Fin (k + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (θ w : Fin (k + 1) → ℝ) {M : ℝ} (hM : 0 < M)
    (hw : ∀ j, 0 ≤ w j) (hwM : ∀ j, w j ≤ M) (hH : 16 ≤ H + 1)
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    volume.real (weightedChordReturnWindow p θ w (1 / (2 * (H + 1 : ℝ))) A T) ≤
      (5 * π / 2) * max (T / 2)
        (hereditaryDepthFloor (k + 1) (collectiveLogBound p) H)⁻¹ *
          exp (-(∑ j, w j) / (8 * M)) := by
  classical
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  let δ := hereditaryDepthFloor (k + 1) (collectiveLogBound p) H
  have hδ : 0 < δ := hereditaryDepthFloor_pos (by omega) (by linarith only [hH1])
  obtain ⟨J, hweight, hsep⟩ := exists_weighted_prime_coordinate_separation p hp hprime hH1 w hw
  let u : Fin (k + 1) → ℝ := fun j => 4 * (exp (w j / M) - 1)
  have hu : ∀ j, 0 ≤ u j := by
    intro j
    have he := (Real.one_le_exp_iff.mpr (div_nonneg (hw j) hM.le))
    dsimp [u]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr he)
  let F := weightedReturnDetector p θ u H J
  let B := (5 * π / 2) * max (T / 2) δ⁻¹
  let S := ∑ j ∈ J, w j
  let c := exp (3 * S / (4 * M))
  have hc : 0 < c := exp_pos _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : Continuous F := continuous_weightedReturnDetector p θ u H J
  have hF0 : ∀ t, 0 ≤ F t := by
    intro t
    apply Finset.prod_nonneg
    intro j _
    have := hu j
    have := returnKernel_nonneg H (log (p j) * t - θ j)
    positivity
  have hi := integral_weightedReturnDetector_le p θ u J hu hδ hsep hT A
  have hupper := mul_le_mul_of_nonneg_left (activation_product_le w hM hw hwM hH J) hB
  have hi' : (∫ t in A..A + T, F t) ≤ B * exp (S / (2 * M)) := hi.trans hupper
  have hle : A ≤ A + T := by linarith only [hT]
  rw [intervalIntegral.integral_of_le hle] at hi'
  have hfi : IntegrableOn F (Set.Ioc A (A + T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp (hF.intervalIntegrable _ _)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hF0) hfi c
  have hvol : volume.real (weightedChordReturnWindow p θ w (1 / (2 * (H + 1 : ℝ))) A T) ≤
      (volume.restrict (Set.Ioc A (A + T))).real {t | c ≤ F t} := by
    rw [measureReal_restrict_apply (measurableSet_le measurable_const hF.measurable)]
    apply measureReal_mono
    · intro t ht
      exact ⟨detector_ge_on_weighted_return p θ w hM hw J hweight ht.2, ht.1⟩
    · exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_Ioc_lt_top (a := A) (b := A + T))).ne
  have hb := ((mul_le_mul_of_nonneg_left hvol hc.le).trans hmark).trans hi'
  calc
    _ ≤ B * exp (S / (2 * M)) / c := by
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hb
    _ = B * exp (-S / (4 * M)) := by
      dsimp [c]
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      have hh : (∑ j, w j) / (8 * M) ≤ S / (4 * M) := by
        calc
          _ ≤ (2 * ∑ j ∈ J, w j) / (8 * M) :=
            div_le_div_of_nonneg_right hweight (by positivity)
          _ = _ := by dsimp [S]; field_simp; ring
      simpa only [neg_div] using neg_le_neg hh

/-- The same weighted window with integer windings and radian precision. -/
def weightedRadianReturnWindow {k : ℕ} (p : Fin k → ℕ) (θ w : Fin k → ℝ)
    (ε A T : ℝ) : Set ℝ := by
  classical
  exact {t | t ∈ Set.Ioc A (A + T) ∧
    (∑ j, if ∃ m : ℤ, |log (p j) * t - θ j - 2 * π * m| ≤ ε then 0 else w j) ≤
      (∑ j, w j) / 8}

theorem weightedRadianReturnWindow_subset {k : ℕ}
    (p : Fin k → ℕ) (θ w : Fin k → ℝ) (hw : ∀ j, 0 ≤ w j) (ε A T : ℝ) :
    weightedRadianReturnWindow p θ w ε A T ⊆ weightedChordReturnWindow p θ w ε A T := by
  classical
  intro t ht
  refine ⟨ht.1, le_trans ?_ ht.2⟩
  apply Finset.sum_le_sum
  intro j _
  by_cases hr : ∃ m : ℤ, |log (p j) * t - θ j - 2 * π * m| ≤ ε
  · obtain ⟨m, hm⟩ := hr
    have hc : ‖phaseExp (log (p j) * t - θ j) - 1‖ ≤ ε :=
      (RHTower.norm_exp_I_mul_real_sub_one_le_mod_two_pi (log (p j) * t - θ j) m).trans hm
    simp only [if_pos hc, if_pos (show ∃ m : ℤ,
      |log (p j) * t - θ j - 2 * π * m| ≤ ε from ⟨m, hm⟩), le_refl]
  · rw [if_neg hr]
    split_ifs
    · exact hw j
    · exact le_rfl

/-- Weighted radian returns satisfy the same arithmetic counting bound. -/
theorem measure_weightedRadianReturnWindow_le {k H : ℕ}
    (p : Fin (k + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (θ w : Fin (k + 1) → ℝ) {M : ℝ} (hM : 0 < M)
    (hw : ∀ j, 0 ≤ w j) (hwM : ∀ j, w j ≤ M) (hH : 16 ≤ H + 1)
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    volume.real (weightedRadianReturnWindow p θ w (1 / (2 * (H + 1 : ℝ))) A T) ≤
      (5 * π / 2) * max (T / 2)
        (hereditaryDepthFloor (k + 1) (collectiveLogBound p) H)⁻¹ *
          exp (-(∑ j, w j) / (8 * M)) := by
  refine (measureReal_mono (weightedRadianReturnWindow_subset p θ w hw _ A T) ?_).trans
    (measure_weightedChordReturnWindow_le p hp hprime θ w hM hw hwM hH hT A)
  exact (lt_of_le_of_lt (measure_mono (fun _ ht => ht.1))
    (measure_Ioc_lt_top (a := A) (b := A + T))).ne

end GaloisForLFunctions.CollectiveDiophantineGeometry
