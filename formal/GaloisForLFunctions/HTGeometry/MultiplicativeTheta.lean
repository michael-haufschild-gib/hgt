import GaloisForLFunctions.HTGeometry.QPochhammer

/-!
# Multiplicative theta from q-Pochhammer products

Exact shift and zero-set infrastructure for the Tate-theta degeneration.
-/

open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Iterating the one-step q-Pochhammer law splits off the first `n` factors. -/
theorem qPochhammerInf_iterate_shift (a : ℂ) (q : EulerNome) :
    ∀ n : ℕ,
      qPochhammerInf a q =
        qPochhammer a q n * qPochhammerInf (a * (q : ℂ) ^ n) q := by
  intro n
  induction n with
  | zero => simp [qPochhammer]
  | succ n ih =>
      calc
        qPochhammerInf a q =
            qPochhammer a q n * qPochhammerInf (a * (q : ℂ) ^ n) q := ih
        _ = qPochhammer a q n *
            ((1 - a * (q : ℂ) ^ n) *
              qPochhammerInf ((a * (q : ℂ) ^ n) * (q : ℂ)) q) := by
              rw [qPochhammerInf_shift]
        _ = qPochhammer a q (n + 1) *
            qPochhammerInf ((a * (q : ℂ) ^ n) * (q : ℂ)) q := by
              rw [qPochhammer_succ]
              ring
        _ = qPochhammer a q (n + 1) *
            qPochhammerInf (a * (q : ℂ) ^ (n + 1)) q := by
              rw [pow_succ]
              congr 2
              ring

/-- Complete zero classification for one q-Pochhammer product. -/
theorem qPochhammerInf_eq_zero_iff (a : ℂ) (q : EulerNome) :
    qPochhammerInf a q = 0 ↔ ∃ n : ℕ, a * (q : ℂ) ^ n = 1 := by
  constructor
  · intro hzero
    by_contra hnot
    have h : ∀ n : ℕ, a * (q : ℂ) ^ n ≠ 1 := by
      intro n hn
      exact hnot ⟨n, hn⟩
    have hne : qPochhammerInf a q ≠ 0 := by
      change (∏' n : ℕ, (1 + -(a * (q : ℂ) ^ n))) ≠ 0
      apply tprod_one_add_ne_zero_of_summable
      · intro n hz
        apply h n
        have hz' : 1 - a * (q : ℂ) ^ n = 0 := by
          simpa [sub_eq_add_neg] using hz
        exact (sub_eq_zero.mp hz').symm
      · simpa only [norm_neg] using (qPochhammer_summable_defect a q).norm
    exact hne hzero
  · rintro ⟨n, hn⟩
    rw [qPochhammerInf_iterate_shift a q n, hn]
    have hone : qPochhammerInf 1 q = 0 := by
      rw [qPochhammerInf_shift]
      simp
    rw [hone, mul_zero]

/-- Multiplicative Jacobi theta product `θ_q(y)=(y;q)_∞(q/y;q)_∞`. -/
def multiplicativeTheta (q : EulerNome) (y : ℂ) : ℂ :=
  qPochhammerInf y q * qPochhammerInf ((q : ℂ) / y) q

/-- Exact quasiperiodicity `θ_q(qy)=-y⁻¹θ_q(y)`. -/
theorem multiplicativeTheta_mul_nome (q : EulerNome) (hq : (q : ℂ) ≠ 0)
    (y : ℂ) (hy : y ≠ 0) :
    multiplicativeTheta q ((q : ℂ) * y) =
      -y⁻¹ * multiplicativeTheta q y := by
  rw [multiplicativeTheta, multiplicativeTheta]
  have hdiv : (q : ℂ) / ((q : ℂ) * y) = 1 / y := by
    field_simp
  rw [hdiv, qPochhammerInf_shift (1 / y) q,
    qPochhammerInf_shift y q]
  field_simp
  ring

/-- Theta vanishes exactly when either q-Pochhammer factor has a zero. -/
theorem multiplicativeTheta_eq_zero_iff (q : EulerNome) (y : ℂ) :
    multiplicativeTheta q y = 0 ↔
      (∃ n : ℕ, y * (q : ℂ) ^ n = 1) ∨
      (∃ n : ℕ, ((q : ℂ) / y) * (q : ℂ) ^ n = 1) := by
  rw [multiplicativeTheta, mul_eq_zero,
    qPochhammerInf_eq_zero_iff, qPochhammerInf_eq_zero_iff]

/-- Every nonpositive integral nome power is a zero of the first q-Pochhammer factor. -/
theorem multiplicativeTheta_eq_zero_of_nome_zpow_nonpos
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (k : ℤ) (hk : k ≤ 0) :
    multiplicativeTheta q ((q : ℂ) ^ k) = 0 := by
  rw [multiplicativeTheta_eq_zero_iff]
  left
  let n : ℕ := (-k).toNat
  have hn : (n : ℤ) = -k := by
    simp only [n, Int.toNat_of_nonneg (neg_nonneg.mpr hk)]
  refine ⟨n, ?_⟩
  rw [← zpow_natCast]
  rw [hn, ← zpow_add₀ hq]
  simp

/-- Every positive integral nome power is a zero of the second q-Pochhammer factor. -/
theorem multiplicativeTheta_eq_zero_of_nome_zpow_pos
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (k : ℤ) (hk : 0 < k) :
    multiplicativeTheta q ((q : ℂ) ^ k) = 0 := by
  rw [multiplicativeTheta_eq_zero_iff]
  right
  refine ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := by omega
  rw [← zpow_natCast, hcast, div_eq_mul_inv, ← zpow_neg]
  nth_rewrite 1 [← zpow_one (q : ℂ)]
  rw [← zpow_add₀ hq, ← zpow_add₀ hq]
  ring_nf
  simp

/-- Every integral nome-orbit point is a theta zero. -/
theorem multiplicativeTheta_nome_zpow_eq_zero
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (k : ℤ) :
    multiplicativeTheta q ((q : ℂ) ^ k) = 0 := by
  rcases le_or_gt k 0 with hk | hk
  · exact multiplicativeTheta_eq_zero_of_nome_zpow_nonpos q hq k hk
  · exact multiplicativeTheta_eq_zero_of_nome_zpow_pos q hq k hk

/-- Complete nome-orbit zero set of multiplicative theta. -/
theorem multiplicativeTheta_eq_zero_iff_nome_zpow
    (q : EulerNome) (hq : (q : ℂ) ≠ 0) (y : ℂ) :
    multiplicativeTheta q y = 0 ↔ ∃ k : ℤ, y = (q : ℂ) ^ k := by
  constructor
  · rw [multiplicativeTheta_eq_zero_iff]
    rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · refine ⟨-(n : ℤ), ?_⟩
      rw [zpow_neg, zpow_natCast]
      have hqn : (q : ℂ) ^ n ≠ 0 := pow_ne_zero n hq
      field_simp [hqn]
      exact hn
    · refine ⟨(n : ℤ) + 1, ?_⟩
      have hy : y ≠ 0 := by
        intro hy
        simp [hy] at hn
      rw [zpow_add₀ hq, zpow_natCast, zpow_one]
      field_simp [hy] at hn
      rw [← hn]
      ring
  · rintro ⟨k, rfl⟩
    exact multiplicativeTheta_nome_zpow_eq_zero q hq k

end

end GaloisForLFunctions.HTGeometry
