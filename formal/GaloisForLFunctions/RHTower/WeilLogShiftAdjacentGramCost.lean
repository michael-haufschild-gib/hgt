import GaloisForLFunctions.RHTower.RiemannAutocorrWeightedTranslation
import GaloisForLFunctions.RHTower.WeilLogShiftSingletonGramCost

/-!
# Cubic Gram cost from adjacent arithmetic cancellation

The difference of adjacent paired logarithmic kernels has an inverse-cubic
envelope. Every normalized Gram certificate on two adjacent arithmetic indices
therefore has cubic cost. A common cost normalization makes this obstruction
directly comparable with the quadratic upper bound for singleton supports.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Adjacent arithmetic cancellation gains one inverse power beyond the
individual paired-kernel envelope. -/
theorem exists_pairedLogKernel_adjacent_inverseCube_envelope :
    ∃ B : ℝ, 0 < B ∧ ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      |pairedLogKernel y (n + 1) - pairedLogKernel y n| ≤
        B * Real.exp (2 * |y|) * ((n : ℝ) ^ 3)⁻¹ := by
  obtain ⟨E, hE, htranslate⟩ := exists_riemannAutocorr_translation_envelope
  refine ⟨2 * E, by positivity, ?_⟩
  intro y n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let δ := Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Real.log_le_log hn0 (by linarith))
  have hδ : δ ≤ (n : ℝ)⁻¹ := by
    calc
      δ = Real.log (((n : ℝ) + 1) / n) := by
        rw [Real.log_div (by positivity) hn0.ne']
      _ ≤ ((n : ℝ) + 1) / n - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = _ := by field_simp; ring
  have hδ1 : |δ| ≤ 1 := by
    rw [abs_of_nonneg hδ0]
    exact hδ.trans (inv_le_one_of_one_le₀ hn1)
  have hp : |riemannAutocorr (y + Real.log (n + 1 : ℕ)) -
      riemannAutocorr (y + Real.log n)| ≤
      E * δ * Real.exp (-(2 * |y + Real.log n|)) := by
    have heq : y + Real.log (n + 1 : ℕ) = (y + Real.log n) + δ := by
      dsimp only [δ]
      push_cast
      ring
    rw [heq]
    simpa only [abs_of_nonneg hδ0] using htranslate (y + Real.log n) δ hδ1
  have hm : |riemannAutocorr (y - Real.log (n + 1 : ℕ)) -
      riemannAutocorr (y - Real.log n)| ≤
      E * δ * Real.exp (-(2 * |y - Real.log n|)) := by
    have heq : y - Real.log (n + 1 : ℕ) = (y - Real.log n) + -δ := by
      dsimp only [δ]
      push_cast
      ring
    rw [heq]
    simpa only [abs_neg, abs_of_nonneg hδ0] using
      htranslate (y - Real.log n) (-δ) (by simpa only [abs_neg] using hδ1)
  have hlog := Real.log_natCast_nonneg n
  have hexp : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [show -(2 * Real.log n) = -Real.log ((n : ℝ) ^ 2) by
      rw [Real.log_pow]; norm_num only, Real.exp_neg, Real.exp_log (by positivity)]
  have hterm (z : ℝ) (hz : Real.log n - |y| ≤ |z|) :
      E * δ * Real.exp (-(2 * |z|)) ≤
      E * Real.exp (2 * |y|) * ((n : ℝ) ^ 3)⁻¹ := by
    have he : Real.exp (-(2 * |z|)) ≤
        Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹ := by
      calc
        _ ≤ Real.exp (2 * |y| + -(2 * Real.log n)) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = _ := by rw [Real.exp_add, hexp]
    calc
      _ ≤ (E * (n : ℝ)⁻¹) * (Real.exp (2 * |y|) * ((n : ℝ) ^ 2)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hδ hE.le) he
          (Real.exp_pos _).le (by positivity)
      _ = _ := by field_simp
  have hplus := hterm (y + Real.log n) (by
    simpa only [abs_of_nonneg hlog, add_comm] using abs_sub_abs_le_abs_add (Real.log n) y)
  have hminus := hterm (y - Real.log n) (by
    simpa only [abs_of_nonneg hlog, abs_sub_comm] using abs_sub_abs_le_abs_sub (Real.log n) y)
  calc
    _ = |(riemannAutocorr (y + Real.log (n + 1 : ℕ)) - riemannAutocorr (y + Real.log n)) +
        (riemannAutocorr (y - Real.log (n + 1 : ℕ)) - riemannAutocorr (y - Real.log n))| := by
      congr 1
      unfold pairedLogKernel
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (E * Real.exp (2 * |y|) * ((n : ℝ) ^ 3)⁻¹) +
        (E * Real.exp (2 * |y|) * ((n : ℝ) ^ 3)⁻¹) :=
      add_le_add (hp.trans hplus) (hm.trans hminus)
    _ = _ := by ring

private def adjacentWeilDirection (k : ℕ) : ({k, k + 1} : Finset ℕ) → ℝ :=
  fun i => if (i : ℕ) = k then 1 else -1

private theorem adjacentWeilDirection_norm (k : ℕ) : ‖adjacentWeilDirection k‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    dsimp only [adjacentWeilDirection]
    split_ifs <;> norm_num
  · have h := norm_le_pi_norm (adjacentWeilDirection k) ⟨k, by simp⟩
    simpa [adjacentWeilDirection] using h

private theorem adjacentWeilDirection_potential (k : ℕ) (y : ℝ) :
    finiteWeilPotential {k, k + 1} (adjacentWeilDirection k) y =
      pairedLogKernel y (k + 2) - pairedLogKernel y (k + 3) := by
  classical
  let i : ({k, k + 1} : Finset ℕ) := ⟨k, by simp⟩
  let j : ({k, k + 1} : Finset ℕ) := ⟨k + 1, by simp⟩
  have hne : i ≠ j := by
    intro h
    have := congrArg Subtype.val h
    dsimp only [i, j] at this
    omega
  have hu : (Finset.univ : Finset ({k, k + 1} : Finset ℕ)) = {i, j} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hz := z.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · exact Or.inl (Subtype.ext hz)
    · exact Or.inr (Subtype.ext hz)
  unfold finiteWeilPotential
  rw [hu, Finset.sum_pair hne]
  simp [adjacentWeilDirection, i, j, Nat.add_assoc, sub_eq_add_neg]

private theorem abs_adjacentWeilGramForm_le {B : ℝ}
    (hK : ∀ (y : ℝ) (n : ℕ), 1 ≤ n →
      |pairedLogKernel y (n + 1) - pairedLogKernel y n| ≤
        B * Real.exp (2 * |y|) * ((n : ℝ) ^ 3)⁻¹)
    (k : ℕ) (w : FiniteWeilGramTest) :
    |finiteWeilGramForm {k, k + 1} w (adjacentWeilDirection k)| ≤
      finiteWeilGramTailCost B w * (((k + 2 : ℕ) : ℝ) ^ 3)⁻¹ := by
  let q := (((k + 2 : ℕ) : ℝ) ^ 3)⁻¹
  have hp (y : ℝ) : |finiteWeilPotential {k, k + 1} (adjacentWeilDirection k) y| ≤
      (B * Real.exp (2 * |y|)) * q := by
    rw [adjacentWeilDirection_potential, abs_sub_comm]
    simpa only [Nat.add_assoc] using hK y (k + 2) (by omega)
  rcases w with ⟨N, x, u, a⟩
  let M := ∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))
  have hsum : |∑ i, ∑ j, (u i * u j) *
      finiteWeilPotential {k, k + 1} (adjacentWeilDirection k) (x j - x i)| ≤ M * q := by
    calc
      _ ≤ ∑ i, |∑ j, (u i * u j) *
          finiteWeilPotential {k, k + 1} (adjacentWeilDirection k) (x j - x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(u i * u j) *
          finiteWeilPotential {k, k + 1} (adjacentWeilDirection k) (x j - x i)| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |u i * u j| * ((B * Real.exp (2 * |x j - x i|)) * q) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
      _ = _ := by simp only [M, Finset.sum_mul, mul_assoc]
  rw [finiteWeilGramForm_apply, abs_mul, abs_neg]
  have haabs : |(a : ℝ)| = (a : ℝ) := abs_of_nonneg a.property
  rw [haabs]
  calc
    _ ≤ (a : ℝ) * (M * q) := mul_le_mul_of_nonneg_left hsum a.property
    _ = _ := by dsimp only [finiteWeilGramTailCost, M, q]; ring

private theorem adjacentGramCost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

/-- Every normalized certificate on adjacent arithmetic indices has cubic cost. -/
theorem exists_adjacentWeilGram_cubic_cost_lower_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (k : ℕ) (tests : Finset FiniteWeilGramTest),
      FiniteWeilGramNormCertificate {k, k + 1} tests →
        2 * (((k + 2 : ℕ) : ℝ) ^ 3) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  obtain ⟨B, hB, hK⟩ := exists_pairedLogKernel_adjacent_inverseCube_envelope
  refine ⟨B, hB, ?_⟩
  intro k tests ht
  let e := adjacentWeilDirection k
  let q := (((k + 2 : ℕ) : ℝ) ^ 3)
  have hq : 0 < q := by dsimp only [q]; positivity
  have he : ‖e‖ = 1 := adjacentWeilDirection_norm k
  have hne : e ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at he
  obtain ⟨wp, hwp, hp⟩ := ht e hne
  obtain ⟨wm, hwm, hm⟩ := ht (-e) (neg_ne_zero.mpr hne)
  rw [he] at hp
  rw [map_neg, norm_neg, he] at hm
  have hcost (w : FiniteWeilGramTest) (hw : 1 < |finiteWeilGramForm {k, k + 1} w e|) :
      q < finiteWeilGramTailCost B w := by
    have h := abs_adjacentWeilGramForm_le hK k w
    change |finiteWeilGramForm {k, k + 1} w e| ≤ finiteWeilGramTailCost B w * q⁻¹ at h
    have hmul := mul_lt_mul_of_pos_right (hw.trans_le h) hq
    simpa only [one_mul, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one] using hmul
  have hcp := hcost wp (by linarith [neg_le_abs (finiteWeilGramForm {k, k + 1} wp e)])
  have hcm := hcost wm (by linarith [le_abs_self (finiteWeilGramForm {k, k + 1} wm e)])
  have hne_tests : wp ≠ wm := by intro h; rw [h] at hp; linarith
  have hsubset : ({wp, wm} : Finset FiniteWeilGramTest) ⊆ tests := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hwp
    · exact hwm
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun w _ _ => adjacentGramCost_nonneg hB.le w)
  rw [Finset.sum_pair hne_tests] at hpair
  change 2 * q < _
  linarith

private theorem adjacentGramCost_scale (r B : ℝ) (w : FiniteWeilGramTest) :
    finiteWeilGramTailCost (r * B) w = r * finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- In one common cost metric, singleton supports admit quadratic certificates
while every adjacent-pair certificate has a cubic lower bound. -/
theorem exists_singleton_adjacentWeilGram_cost_separation :
    ∃ B C D : ℝ, 0 < B ∧ 0 < C ∧ 0 < D ∧
      (∀ k : ℕ, ∃ tests : Finset FiniteWeilGramTest, tests.card = 2 ∧
        FiniteWeilGramNormCertificate {k} tests ∧
        (∑ w ∈ tests, finiteWeilGramTailCost B w) ≤ C * (((k + 2 : ℕ) : ℝ) ^ 2)) ∧
      ∀ (k : ℕ) (tests : Finset FiniteWeilGramTest),
        FiniteWeilGramNormCertificate {k, k + 1} tests →
          D * (((k + 2 : ℕ) : ℝ) ^ 3) < ∑ w ∈ tests, finiteWeilGramTailCost B w := by
  classical
  obtain ⟨B, C, hB, hC, _, hsingle⟩ := exists_singletonWeil_quadratic_cost_certificate
  obtain ⟨B₁, hB₁, hpair⟩ := exists_adjacentWeilGram_cubic_cost_lower_bound
  refine ⟨B, C, 2 * (B / B₁), hB, hC, by positivity, hsingle, ?_⟩
  intro k tests ht
  have hscale : (∑ w ∈ tests, finiteWeilGramTailCost B w) =
      (B / B₁) * ∑ w ∈ tests, finiteWeilGramTailCost B₁ w := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have h := adjacentGramCost_scale (B / B₁) B₁ w
    rwa [div_mul_cancel₀ B hB₁.ne'] at h
  rw [hscale]
  have h := mul_lt_mul_of_pos_left (hpair k tests ht) (div_pos hB hB₁)
  nlinarith

end RHTower
