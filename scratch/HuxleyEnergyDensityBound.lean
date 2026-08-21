import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityBound

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

theorem scratch_huxley_energy_two_term
    {N : ℕ} (hN : 1 ≤ N) (a : EuclideanSpace ℂ (Fin N))
    {T E sigma : ℝ} (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hmass : ‖a‖ ^ 2 ≤ E / (N : ℝ))
    (hthr : 2400 * E ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma))
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T)
    (hbig : ∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖⟪dyadicDirRow N x, a⟫_ℂ‖) :
    (S.card : ℝ) ≤
      (6594624 * T * E ^ 3 * (N : ℝ) ^ (6 * sigma - 2)
          + 2 * E * (N : ℝ) ^ (2 * sigma)) *
        (1 + 12 * Real.pi * (1 + Real.log (2 * T + 1))) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hEsq : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  have hthresh :
      (E / (N : ℝ)) *
          (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))) ≤
        (((N : ℝ) ^ (-sigma)) ^ 2) / 3 := by
    have hbase := huxley_threshold_of_rpow hN (D := Real.sqrt E) (sigma := sigma) (by
      simpa [hEsq] using hthr)
    simpa [hEsq] using hbase
  have hV : (0 : ℝ) < (N : ℝ) ^ (-sigma) := Real.rpow_pos_of_pos hN0 _
  have hbase := huxley_large_values_finset_explicit_energy hN a
    (delta := 1) (Ttot := 2 * T) (V := (N : ℝ) ^ (-sigma)) (G := E / (N : ℝ))
    one_pos hV (by linarith) hmass S hsep hspread hbig hthresh
  simp only [div_one] at hbase
  set V : ℝ := (N : ℝ) ^ (-sigma) with hVdef
  set A : ℝ := (N : ℝ) ^ (2 * sigma) with hAdef
  have hA0 : (0 : ℝ) < A := Real.rpow_pos_of_pos hN0 _
  have hpowV : ∀ k : ℕ, V ^ k = (N : ℝ) ^ (-(sigma * (k : ℝ))) := by
    intro k
    rw [hVdef, ← Real.rpow_natCast ((N : ℝ) ^ (-sigma)) k,
      ← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hone : V ^ 2 * A = 1 := by
    rw [hpowV 2, hAdef, ← Real.rpow_add hN0,
      show -(sigma * ((2 : ℕ) : ℝ)) + 2 * sigma = 0 by push_cast; ring,
      Real.rpow_zero]
  have hA2 : A ^ 2 = (N : ℝ) ^ (4 * sigma) := by
    rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ (2 * sigma)) 2,
      ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hone4 : V ^ 4 * A ^ 2 = 1 := by
    rw [hpowV 4, hA2, ← Real.rpow_add hN0,
      show -(sigma * ((4 : ℕ) : ℝ)) + 4 * sigma = 0 by push_cast; ring,
      Real.rpow_zero]
  have hV4inv : V ^ 4 = (A ^ 2)⁻¹ := by
    field_simp
    linarith [hone4]
  have hA3 : A ^ 3 = (N : ℝ) ^ (6 * sigma) := by
    rw [hAdef, ← Real.rpow_natCast ((N : ℝ) ^ (2 * sigma)) 3,
      ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hNA : (N : ℝ) ^ (6 * sigma - 2) = A ^ 3 / (N : ℝ) ^ 2 := by
    rw [hA3, eq_div_iff (by positivity), ← Real.rpow_natCast (N : ℝ) 2,
      ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  set L : ℝ := 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) with hLdef
  calc
    (S.card : ℝ) = ((S.card : ℝ) * V ^ 2) * A := by
      rw [mul_assoc, hone, mul_one]
    _ ≤ (2 * T * (1284 * (E / (N : ℝ))) ^ 2 / V ^ 4 + 1) *
          (2 * (E / (N : ℝ)) *
            ((N : ℝ) + 12 * Real.pi * (N : ℝ) *
              (1 + Real.log (2 * T + 1)))) * A :=
      mul_le_mul_of_nonneg_right hbase hA0.le
    _ = (6594624 * T * E ^ 3 * (N : ℝ) ^ (6 * sigma - 2)
          + 2 * E * A) * L := by
      rw [hV4inv, hNA]
      field_simp
      ring

end RHTower.Sieve
