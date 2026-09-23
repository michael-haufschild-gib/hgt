import Mathlib

/-!
# Channel crowding forces oscillation

A separating margin for a finite family of channels is a lower bound for the Gram Rayleigh
quotient.  Testing it on the difference of the two closest channels bounds the margin by half the
squared channel distance, and the mean value inequality bounds that distance by the node spacing
times the supremum of the orbit velocity.

For a unitary translation orbit the velocity is the generator energy `‖Dξ‖`, so a positive
separating margin forces `‖Dξ‖ ≥ √(2σ)/δ`: crowded channels are paid for by oscillation.

Finitely many nodes always contain a consecutive pair at distance at most the total spread divided
by the number of gaps, which is the pigeonhole step behind prime-log crowding.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The difference coefficient vector supported on a pair of nodes. -/
def pairDiffCoeff {k : ℕ} (i j : Fin k) : Fin k → ℂ :=
  fun n => (if n = i then 1 else 0) - (if n = j then 1 else 0)

theorem pairDiffCoeff_normSq {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    ∑ n, ‖pairDiffCoeff i j n‖ ^ (2 : ℕ) = 2 := by
  classical
  have hsupp : ∀ n ∈ (Finset.univ : Finset (Fin k)), n ∉ ({i, j} : Finset (Fin k)) →
      ‖pairDiffCoeff i j n‖ ^ (2 : ℕ) = 0 := by
    intro n _ hn
    have hni : n ≠ i := fun h => hn (by simp [h])
    have hnj : n ≠ j := fun h => hn (by simp [h])
    simp [pairDiffCoeff, hni, hnj]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin k))) hsupp,
    Finset.sum_pair hij]
  simp [pairDiffCoeff, hij, hij.symm]
  norm_num

theorem pairDiffCoeff_combination {k : ℕ} (v : Fin k → E) {i j : Fin k} (hij : i ≠ j) :
    ∑ n, pairDiffCoeff i j n • v n = v i - v j := by
  classical
  have hsupp : ∀ n ∈ (Finset.univ : Finset (Fin k)), n ∉ ({i, j} : Finset (Fin k)) →
      pairDiffCoeff i j n • v n = 0 := by
    intro n _ hn
    have hni : n ≠ i := fun h => hn (by simp [h])
    have hnj : n ≠ j := fun h => hn (by simp [h])
    simp [pairDiffCoeff, hni, hnj]
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin k))) hsupp,
    Finset.sum_pair hij]
  simp [pairDiffCoeff, hij, hij.symm, sub_eq_add_neg]

/-- **Equation (5), Rayleigh step.**  A separating margin is at most half the squared distance
between any two channels. -/
theorem separatingMargin_le_half_dist_sq {k : ℕ} (v : Fin k → E) {σ : ℝ}
    (hσ : ∀ c : Fin k → ℂ, σ * (∑ n, ‖c n‖ ^ (2 : ℕ)) ≤ ‖∑ n, c n • v n‖ ^ (2 : ℕ))
    {i j : Fin k} (hij : i ≠ j) :
    σ ≤ ‖v i - v j‖ ^ (2 : ℕ) / 2 := by
  have h := hσ (pairDiffCoeff i j)
  rw [pairDiffCoeff_normSq hij, pairDiffCoeff_combination v hij] at h
  linarith

/-- **Equation (7).**  The mean value inequality bounds the channel distance by the node spacing
times the orbit velocity. -/
theorem norm_orbit_sub_le {a b M : ℝ} (hab : a ≤ b) (A A' : ℝ → E)
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt A (A' t) (Icc a b) t)
    (hM : ∀ t ∈ Icc a b, ‖A' t‖ ≤ M) :
    ‖A b - A a‖ ≤ M * (b - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' hderiv (fun t ht => hM t (Ico_subset_Icc_self ht))
    b (right_mem_Icc.2 hab)

/-- **Equation (5).**  The crowding inequality: the separating margin of a differentiable channel
orbit is at most half the squared node spacing times the squared orbit velocity. -/
theorem separatingMargin_le_of_orbit {k : ℕ} {σ M : ℝ}
    (A A' : ℝ → E) (h : Fin k → ℝ) (v : Fin k → E) (hv : ∀ n, v n = A (h n))
    (hderiv : ∀ a b : ℝ, ∀ t ∈ Icc a b, HasDerivWithinAt A (A' t) (Icc a b) t)
    (hbound : ∀ t, ‖A' t‖ ≤ M)
    (hσ : ∀ c : Fin k → ℂ, σ * (∑ n, ‖c n‖ ^ (2 : ℕ)) ≤ ‖∑ n, c n • v n‖ ^ (2 : ℕ))
    {i j : Fin k} (hij : i ≠ j) :
    σ ≤ |h i - h j| ^ (2 : ℕ) * M ^ (2 : ℕ) / 2 := by
  have hdist : ‖v i - v j‖ ≤ M * |h i - h j| := by
    rcases le_total (h i) (h j) with hle | hle
    · have hd := norm_orbit_sub_le hle A A' (fun t ht => hderiv (h i) (h j) t ht)
        (fun t _ => hbound t)
      have habs : |h i - h j| = h j - h i := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ h j - h i)]
      rw [hv i, hv j, ← norm_neg, neg_sub, habs]
      exact hd
    · have hd := norm_orbit_sub_le hle A A' (fun t ht => hderiv (h j) (h i) t ht)
        (fun t _ => hbound t)
      have habs : |h i - h j| = h i - h j :=
        abs_of_nonneg (by linarith : (0:ℝ) ≤ h i - h j)
      rw [hv i, hv j, habs]
      exact hd
  have hmar := separatingMargin_le_half_dist_sq v hσ hij
  have hnn : 0 ≤ ‖v i - v j‖ := norm_nonneg _
  nlinarith [hdist, hmar, abs_nonneg (h i - h j)]

/-- **Equation (8).**  The exact resource lower bound: a positive separating margin forces orbit
velocity at least `√(2σ)` divided by the spacing. -/
theorem orbit_velocity_lower_bound {σ M δ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hcrowd : σ ≤ δ ^ (2 : ℕ) * M ^ (2 : ℕ) / 2) :
    Real.sqrt (2 * σ) / δ ≤ M := by
  have h2σ : 2 * σ ≤ (δ * M) ^ (2 : ℕ) := by nlinarith
  have hsq : Real.sqrt (2 * σ) ≤ δ * M := by
    rcases le_or_gt (2 * σ) 0 with hneg | hpos
    · have : Real.sqrt (2 * σ) = 0 := Real.sqrt_eq_zero_of_nonpos hneg
      rw [this]
      positivity
    · have hδM : 0 ≤ δ * M := by positivity
      calc Real.sqrt (2 * σ) ≤ Real.sqrt ((δ * M) ^ (2 : ℕ)) := Real.sqrt_le_sqrt h2σ
        _ = δ * M := by rw [Real.sqrt_sq hδM]
  rw [div_le_iff₀ hδ]
  linarith [hsq]

/-- **Equation (22).**  Combining the crowding inequality with the pigeonhole spacing bound: a
positive margin over `n` gaps in a spread of length `L` forces velocity at least
`√(2σ) n / L`. -/
theorem orbit_velocity_lower_bound_of_spread {σ M L : ℝ} {n : ℕ} (hn : 0 < n) (hL : 0 < L)
    (hM : 0 ≤ M) (hcrowd : σ ≤ (L / n) ^ (2 : ℕ) * M ^ (2 : ℕ) / 2) :
    Real.sqrt (2 * σ) * n / L ≤ M := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : (0 : ℝ) < L / n := by positivity
  have hkey := orbit_velocity_lower_bound hδ hM hcrowd
  calc Real.sqrt (2 * σ) * n / L = Real.sqrt (2 * σ) / (L / n) := by field_simp
    _ ≤ M := hkey

/-! ## Pigeonhole for the node spacing -/

/-- **Equation (17).**  Among `n` consecutive gaps of a real sequence, one is at most the total
spread divided by `n`. -/
theorem exists_small_gap {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) :
    ∃ i < n, f (i + 1) - f i ≤ (f n - f 0) / n := by
  by_contra hcon
  have hcon' : ∀ i, i < n → (f n - f 0) / n < f (i + 1) - f i := by
    intro i hi
    by_contra hle
    exact hcon ⟨i, hi, not_lt.1 hle⟩
  have hsum : ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := Finset.sum_range_sub f n
  have hlt : (f n - f 0) < ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
    calc (f n - f 0) = ∑ _i ∈ Finset.range n, (f n - f 0) / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
      _ < ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
          refine Finset.sum_lt_sum_of_nonempty ?_ fun i hi => ?_
          · exact Finset.nonempty_range_iff.2 (by omega)
          · exact hcon' i (Finset.mem_range.1 hi)
  rw [hsum] at hlt
  exact lt_irrefl _ hlt

end

end GaloisForLFunctions.HTGeometry
