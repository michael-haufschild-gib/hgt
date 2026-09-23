import Mathlib.Tactic

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Real part of the Cauchy resolvent joining two right-half-plane zero modes. -/
def transverseCauchyKernel (a b delta : ℝ) : ℝ :=
  (a + b) / ((a + b) ^ (2 : ℕ) + delta ^ (2 : ℕ))

theorem transverseCauchyKernel_eq_resolvent_re (a b delta : ℝ) :
    transverseCauchyKernel a b delta =
      ((((a + b : ℝ) : ℂ) + (delta : ℂ) * Complex.I)⁻¹).re := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp [transverseCauchyKernel, pow_two]

theorem transverseCauchyKernel_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (delta : ℝ) :
    0 < transverseCauchyKernel a b delta := by
  unfold transverseCauchyKernel
  positivity

theorem transverseCauchyKernel_self
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) :
    transverseCauchyKernel a a (gamma - gamma) = (2 * a)⁻¹ := by
  unfold transverseCauchyKernel
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [ha0]
  ring

/-- The exact real Cauchy-Gram energy of a finite packet of reflected off-line modes. -/
def finiteOfflineCauchyEnergy {n : ℕ}
    (a gamma : Fin n → ℝ) (m : Fin n → ℕ) : ℝ :=
  4 * ∑ j, ∑ k,
    (m j : ℝ) * (m k : ℝ) *
      transverseCauchyKernel (a j) (a k) (gamma j - gamma k)

theorem finiteOfflineCauchyEnergy_eq_resolventGram {n : ℕ}
    (a gamma : Fin n → ℝ) (m : Fin n → ℕ) :
    finiteOfflineCauchyEnergy a gamma m =
      4 * ∑ j, ∑ k, (m j : ℝ) * (m k : ℝ) *
        (((((a j + a k : ℝ) : ℂ) +
          ((gamma j - gamma k : ℝ) : ℂ) * Complex.I)⁻¹).re) := by
  simp only [finiteOfflineCauchyEnergy, transverseCauchyKernel_eq_resolvent_re]

theorem finiteOfflineCauchyEnergy_pos_of_nonempty
    {n : ℕ} (hn : 0 < n) {a gamma : Fin n → ℝ} {m : Fin n → ℕ}
    (ha : ∀ j, 0 < a j) (hm : ∀ j, 1 ≤ m j) :
    0 < finiteOfflineCauchyEnergy a gamma m := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hterm : ∀ j k : Fin n,
      0 < (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    intro j k
    have hmj : 0 < (m j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm j))
    have hmk : 0 < (m k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm k))
    exact mul_pos (mul_pos hmj hmk) (transverseCauchyKernel_pos (ha j) (ha k) _)
  have hinner : ∀ j : Fin n, 0 < ∑ k,
      (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    intro j
    exact Finset.sum_pos (fun k _ => hterm j k) huniv
  have houter : 0 < ∑ j, ∑ k,
      (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) :=
    Finset.sum_pos (fun j _ => hinner j) huniv
  unfold finiteOfflineCauchyEnergy
  nlinarith

theorem finiteOfflineCauchyEnergy_ge_selfDiagonal
    {n : ℕ} {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) :
    4 * ∑ j, (m j : ℝ) * (m j : ℝ) *
        transverseCauchyKernel (a j) (a j) (gamma j - gamma j) ≤
      finiteOfflineCauchyEnergy a gamma m := by
  classical
  have hkernel_nonneg : ∀ j k : Fin n,
      0 ≤ (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    intro j k
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (transverseCauchyKernel_pos (ha j) (ha k) _).le
  have hdiag_le : ∑ j, (m j : ℝ) * (m j : ℝ) *
        transverseCauchyKernel (a j) (a j) (gamma j - gamma j) ≤
      ∑ j, ∑ k, (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.single_le_sum (fun k _ => hkernel_nonneg j k) (Finset.mem_univ j)
  unfold finiteOfflineCauchyEnergy
  exact mul_le_mul_of_nonneg_left hdiag_le (by norm_num)

theorem finiteOfflineCauchyEnergy_ge_two_mul_sum_sq_div
    {n : ℕ} {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) :
    2 * ∑ j, (m j : ℝ) ^ (2 : ℕ) / a j ≤ finiteOfflineCauchyEnergy a gamma m := by
  have hterm : ∀ j : Fin n,
      2 * ((m j : ℝ) ^ (2 : ℕ) / a j) =
        4 * ((m j : ℝ) * (m j : ℝ) *
          transverseCauchyKernel (a j) (a j) (gamma j - gamma j)) := by
    intro j
    rw [transverseCauchyKernel_self (ha j) (gamma j)]
    have haj0 : a j ≠ 0 := ne_of_gt (ha j)
    field_simp [haj0]
    ring
  calc
    2 * ∑ j, (m j : ℝ) ^ (2 : ℕ) / a j =
        ∑ j, 2 * ((m j : ℝ) ^ (2 : ℕ) / a j) := by rw [Finset.mul_sum]
    _ = ∑ j, 4 * ((m j : ℝ) * (m j : ℝ) *
          transverseCauchyKernel (a j) (a j) (gamma j - gamma j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hterm j
    _ = 4 * ∑ j, (m j : ℝ) * (m j : ℝ) *
          transverseCauchyKernel (a j) (a j) (gamma j - gamma j) := by
      rw [Finset.mul_sum]
    _ ≤ finiteOfflineCauchyEnergy a gamma m :=
      finiteOfflineCauchyEnergy_ge_selfDiagonal m ha

theorem finiteOfflineCauchyEnergy_gt_four_card
    {n : ℕ} (hn : 0 < n) {a gamma : Fin n → ℝ} {m : Fin n → ℕ}
    (ha : ∀ j, 0 < a j) (haHalf : ∀ j, a j < (1 / 2 : ℝ))
    (hm : ∀ j, 1 ≤ m j) :
    (4 : ℝ) * n < finiteOfflineCauchyEnergy a gamma m := by
  classical
  let diag : Fin n → ℝ := fun j =>
    (m j : ℝ) * (m j : ℝ) *
      transverseCauchyKernel (a j) (a j) (gamma j - gamma j)
  have hkernel_nonneg : ∀ j k : Fin n,
      0 ≤ (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    intro j k
    have hmj : 0 ≤ (m j : ℝ) := by positivity
    have hmk : 0 ≤ (m k : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg hmj hmk)
      (transverseCauchyKernel_pos (ha j) (ha k) _).le
  have hdiag_le : ∑ j, diag j ≤ ∑ j, ∑ k,
      (m j : ℝ) * (m k : ℝ) *
        transverseCauchyKernel (a j) (a k) (gamma j - gamma k) := by
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.single_le_sum (fun k _ => hkernel_nonneg j k) (Finset.mem_univ j)
  have hdiag_gt_one : ∀ j : Fin n, 1 < diag j := by
    intro j
    have haj := ha j
    have hajHalf := haHalf j
    have hmj : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hm j
    change 1 < (m j : ℝ) * (m j : ℝ) *
      transverseCauchyKernel (a j) (a j) (gamma j - gamma j)
    rw [transverseCauchyKernel_self haj (gamma j)]
    have hsq : (1 : ℝ) ≤ (m j : ℝ) * (m j : ℝ) := by nlinarith
    have htwoa : 0 < 2 * a j := by positivity
    change 1 < ((m j : ℝ) * (m j : ℝ)) / (2 * a j)
    apply (lt_div_iff₀ htwoa).2
    nlinarith
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hcard_diag : (n : ℝ) < ∑ j, diag j := by
    have hsum : ∑ _j : Fin n, (1 : ℝ) < ∑ j, diag j :=
      Finset.sum_lt_sum_of_nonempty huniv (fun j _ => hdiag_gt_one j)
    simpa using hsum
  unfold finiteOfflineCauchyEnergy
  nlinarith

end RHTower
