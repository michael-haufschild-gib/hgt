import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCertificate

/-!
# Finite-head / infinite-tail compensation under Weil positivity

For each finite arithmetic support, a constant independent of the Weil-positive
sequence bounds its head norm by the inverse-square weighted mass of its tail.
All series convergence is derived from the existing Weil-positive contract.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- Exponential autocorrelation decay gives an inverse-square arithmetic
envelope, with the dependence on the real shift displayed explicitly. -/
theorem exists_pairedLogKernel_inverseSquare_envelope :
    ∃ B : ℝ, 0 < B ∧ ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      pairedLogKernel y n ≤ B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ := by
  obtain ⟨C, hC, hK⟩ := exists_riemannAutocorr_le
  refine ⟨2 * (C + 1), by positivity, ?_⟩
  intro y n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog := Real.log_natCast_nonneg n
  have hexp : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [show -(2 * Real.log n) = -(Real.log ((n : ℝ) ^ 2)) by
      rw [Real.log_pow]; push_cast; ring,
      Real.exp_neg, Real.exp_log (by positivity)]
  have hshift (z : ℝ) (hz : Real.log n - |y| ≤ |z|) :
      riemannAutocorr z ≤ (C + 1) * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ := by
    calc
      riemannAutocorr z ≤ C * Real.exp (-(2 * |z|)) := hK z
      _ ≤ (C + 1) * Real.exp (2 * |y| - 2 * Real.log n) := by
        apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith))
          (Real.exp_pos _).le
        positivity
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, hexp]; ring
  have hp := hshift (y + Real.log n) (by
    simpa only [abs_of_nonneg hlog, add_comm] using abs_sub_abs_le_abs_add (Real.log n) y)
  have hm := hshift (y - Real.log n) (by
    simpa only [abs_of_nonneg hlog, abs_sub_comm] using abs_sub_abs_le_abs_sub (Real.log n) y)
  unfold pairedLogKernel
  linarith

/-- The selected actual normalized arithmetic coefficients. -/
def weilFiniteHead (s : Finset ℕ) (lam : ℕ → ℝ) : s → ℝ :=
  fun i => weilDeviation lam ((i : ℕ) + 2)

/-- The actual deviation with precisely the selected head removed. -/
def weilFiniteTail (s : Finset ℕ) (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ∈ s.image (fun k => k + 2) then 0 else weilDeviation lam n

theorem finiteWeilPacket_head_add_tail (s : Finset ℕ) (lam : ℕ → ℝ) (n : ℕ) :
    finiteWeilPacket s (weilFiniteHead s lam) n + weilFiniteTail s lam n =
      weilDeviation lam n := by
  classical
  by_cases hn : n ∈ s.image (fun k => k + 2)
  · simp only [weilFiniteTail, if_pos hn, add_zero]
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    exact finiteWeilPacket_apply_tail s (weilFiniteHead s lam) ⟨k, hk⟩
  · have hp : finiteWeilPacket s (weilFiniteHead s lam) n = 0 := by
      simp only [finiteWeilPacket, Finsupp.finsetSum_apply, Finsupp.single_apply]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hn (Finset.mem_image.mpr ⟨i, i.property, h⟩))
    simp only [weilFiniteTail, if_neg hn, hp, zero_add]

theorem abs_weilFiniteTail_le (s : Finset ℕ) (lam : ℕ → ℝ) (n : ℕ) :
    |weilFiniteTail s lam n| ≤ |weilDeviation lam n| := by
  unfold weilFiniteTail
  split_ifs
  · simpa only [abs_zero] using abs_nonneg (weilDeviation lam n)
  · rfl

private theorem weilFiniteTail_zero (s : Finset ℕ) (lam : ℕ → ℝ) :
    weilFiniteTail s lam 0 = 0 := by
  simp [weilFiniteTail, weilDeviation_zero]

/-- The inverse-square weighted absolute mass outside the selected head. -/
def weilFiniteTailWeight (s : Finset ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, |weilFiniteTail s lam n| * ((n : ℝ) ^ 2)⁻¹

theorem weilFiniteTailWeight_nonneg (s : Finset ℕ) (lam : ℕ → ℝ) :
    0 ≤ weilFiniteTailWeight s lam :=
  tsum_nonneg fun _ => by positivity

theorem summable_weilFiniteTail_weight (s : Finset ℕ) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Summable (fun n : ℕ => |weilFiniteTail s lam n| * ((n : ℝ) ^ 2)⁻¹) := by
  obtain ⟨A, hA, ha⟩ := exists_abs_weilDeviation_le hW
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (summable_log_add_mul_inv_sq hA)
  intro n
  exact mul_le_mul_of_nonneg_right ((abs_weilFiniteTail_le s lam n).trans (ha n))
    (by positivity)

/-- Literal signed tail convergence and its exact subtraction value. -/
theorem hasSum_weilFiniteTail_potential (s : Finset ℕ) {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (y : ℝ) :
    HasSum (fun n : ℕ => weilFiniteTail s lam n * pairedLogKernel y n)
      (deviationPotential lam y - finiteWeilPotential s (weilFiniteHead s lam) y) := by
  let v := finiteWeilPacket s (weilFiniteHead s lam)
  have hh : HasSum (fun n : ℕ => v n * pairedLogKernel y n)
      (finiteWeilPotential s (weilFiniteHead s lam) y) := by
    have h : HasSum (fun n : ℕ => v n * pairedLogKernel y n)
        (v.sum (fun n a => a * pairedLogKernel y n)) :=
      hasSum_sum_of_ne_finset_zero (s := v.support)
        (fun n hn => by rw [Finsupp.notMem_support_iff.mp hn, zero_mul])
    simpa only [v, finiteWeilPacket_synthesis, finiteWeilPotential] using h
  have ht : HasSum (fun n : ℕ => weilDeviation lam n * pairedLogKernel y n)
      (deviationPotential lam y) := (summable_deviationPotential_term hW y).hasSum
  have heq : (fun n : ℕ => weilFiniteTail s lam n * pairedLogKernel y n) =
      (fun n : ℕ => weilDeviation lam n * pairedLogKernel y n -
        v n * pairedLogKernel y n) := by
    funext n
    rw [← finiteWeilPacket_head_add_tail s lam n]
    dsimp only [v]
    ring
  rw [heq]
  exact ht.sub hh

private theorem abs_weilFiniteTail_potential_le
    {B : ℝ}
    (hK : ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      pairedLogKernel y n ≤ B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹)
    (s : Finset ℕ) {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    |deviationPotential lam y - finiteWeilPotential s (weilFiniteHead s lam) y| ≤
      B * Real.exp (2 * |y|) * weilFiniteTailWeight s lam := by
  have hterm (n : ℕ) : ‖weilFiniteTail s lam n * pairedLogKernel y n‖ ≤
      (B * Real.exp (2 * |y|)) * (|weilFiniteTail s lam n| * ((n : ℝ) ^ 2)⁻¹) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [weilFiniteTail_zero, zero_mul, norm_zero, abs_zero, mul_zero, le_refl]
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pairedLogKernel_pos y n)]
      calc
        _ ≤ |weilFiniteTail s lam n| *
            (B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hK y n hn) (abs_nonneg _)
        _ = _ := by ring
  have hs := hasSum_weilFiniteTail_potential s hW y
  have hw := (summable_weilFiniteTail_weight s hW).mul_left (B * Real.exp (2 * |y|))
  calc
    _ = ‖∑' n : ℕ, weilFiniteTail s lam n * pairedLogKernel y n‖ := by
      rw [hs.tsum_eq, Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖weilFiniteTail s lam n * pairedLogKernel y n‖ :=
      norm_tsum_le_tsum_norm hs.summable.norm
    _ ≤ ∑' n : ℕ, (B * Real.exp (2 * |y|)) *
        (|weilFiniteTail s lam n| * ((n : ℝ) ^ 2)⁻¹) :=
      Summable.tsum_le_tsum hterm hs.summable.norm hw
    _ = _ := by rw [tsum_mul_left]; rfl

/-- One envelope constant works for every finite support and every
Weil-positive sequence; the signed tail retains its literal HasSum value. -/
theorem exists_weilFiniteTail_potential_envelope :
    ∃ B : ℝ, 0 < B ∧ ∀ (s : Finset ℕ) (lam : ℕ → ℝ), WeilPositiveFull lam →
      ∀ y : ℝ,
        HasSum (fun n : ℕ => weilFiniteTail s lam n * pairedLogKernel y n)
          (deviationPotential lam y - finiteWeilPotential s (weilFiniteHead s lam) y) ∧
        |deviationPotential lam y - finiteWeilPotential s (weilFiniteHead s lam) y| ≤
          B * Real.exp (2 * |y|) * weilFiniteTailWeight s lam := by
  obtain ⟨B, hB, hK⟩ := exists_pairedLogKernel_inverseSquare_envelope
  exact ⟨B, hB, fun s lam hW y =>
    ⟨hasSum_weilFiniteTail_potential s hW y, abs_weilFiniteTail_potential_le hK s hW y⟩⟩

/-- Explicit translation-and-amplitude cost of a normalized Gram test. -/
def finiteWeilGramTailCost (B : ℝ) : FiniteWeilGramTest → ℝ
  | ⟨N, x, u, a⟩ => (a : ℝ) *
      ∑ i : Fin N, ∑ j : Fin N, |u i * u j| * (B * Real.exp (2 * |x j - x i|))

private theorem finiteWeilGramTailCost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

private theorem finiteWeilGram_head_lower
    {B : ℝ}
    (hK : ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      pairedLogKernel y n ≤ B * Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹)
    (s : Finset ℕ) {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (w : FiniteWeilGramTest) :
    -(finiteWeilGramTailCost B w * weilFiniteTailWeight s lam) ≤
      finiteWeilGramForm s w (weilFiniteHead s lam) := by
  rcases w with ⟨N, x, u, a⟩
  let R (y : ℝ) := deviationPotential lam y - finiteWeilPotential s (weilFiniteHead s lam) y
  let D := weilFiniteTailWeight s lam
  let M := ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))
  have hR (y : ℝ) : |R y| ≤ B * Real.exp (2 * |y|) * D :=
    abs_weilFiniteTail_potential_le hK s hW y
  have hrem : |∑ i, ∑ j, (u i * u j) * R (x j - x i)| ≤ M * D := by
    calc
      _ ≤ ∑ i, |∑ j, (u i * u j) * R (x j - x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(u i * u j) * R (x j - x i)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|) * D) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hR _) (abs_nonneg _)
      _ = M * D := by simp only [M, Finset.sum_mul, mul_assoc]
  have hfull := sum_mul_deviationPotential_nonpos Finset.univ u x hW
  have hsplit : (∑ i, ∑ j, (u i * u j) * R (x j - x i)) =
      (∑ i, ∑ j, (u i * u j) * deviationPotential lam (x j - x i)) -
      ∑ i, ∑ j, (u i * u j) * finiteWeilPotential s (weilFiniteHead s lam) (x j - x i) := by
    simp only [R, mul_sub, Finset.sum_sub_distrib]
  have hhead : (∑ i, ∑ j, (u i * u j) *
      finiteWeilPotential s (weilFiniteHead s lam) (x j - x i)) ≤ M * D := by
    have hneg := neg_le_abs (∑ i, ∑ j, (u i * u j) * R (x j - x i))
    linarith
  rw [finiteWeilGramForm_apply]
  change -((a : ℝ) * M * D) ≤ -(a : ℝ) * _
  have hscaled := mul_le_mul_of_nonneg_left hhead a.property
  nlinarith

/-- Native quantitative compensation: the finite-head constant is independent
of the Weil-positive sequence, and weighted tail convergence is explicit. -/
theorem exists_weilFiniteHead_tail_weight_bound (s : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℕ → ℝ), WeilPositiveFull lam →
      HasSum (fun n : ℕ => |weilFiniteTail s lam n| * ((n : ℝ) ^ 2)⁻¹)
        (weilFiniteTailWeight s lam) ∧
      ‖weilFiniteHead s lam‖ ≤ C * weilFiniteTailWeight s lam := by
  obtain ⟨B, hB, hK⟩ := exists_pairedLogKernel_inverseSquare_envelope
  obtain ⟨tests, htests, _⟩ := exists_finiteWeilGram_stability_certificate s
  let C := 1 + ∑ w ∈ tests, finiteWeilGramTailCost B w
  have hsum : 0 ≤ ∑ w ∈ tests, finiteWeilGramTailCost B w :=
    Finset.sum_nonneg fun w _ => finiteWeilGramTailCost_nonneg hB.le w
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro lam hW
  refine ⟨(summable_weilFiniteTail_weight s hW).hasSum, ?_⟩
  apply htests (weilFiniteHead s lam) (C * weilFiniteTailWeight s lam)
    (mul_nonneg hC.le (weilFiniteTailWeight_nonneg s lam))
  intro w hw
  have hc : finiteWeilGramTailCost B w ≤ C := by
    have h := Finset.single_le_sum (f := finiteWeilGramTailCost B)
      (fun w _ => finiteWeilGramTailCost_nonneg hB.le w) hw
    dsimp only [C]
    linarith
  have h := mul_le_mul_of_nonneg_right hc (weilFiniteTailWeight_nonneg s lam)
  exact (neg_le_neg h).trans (finiteWeilGram_head_lower hK s hW w)

end RHTower
