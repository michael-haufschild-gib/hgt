import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityHypothesis

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

theorem scratch_lemma41_huxley_energy
    {T : ℝ} {N : ℕ} {sigma eps Q : ℝ}
    (a : EuclideanSpace ℂ (Fin N)) (S : Finset ℝ)
    (hN : 1 ≤ N) (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) (hT1 : 1 ≤ T)
    (hC : (6594624 : ℝ) ≤ T ^ (eps ^ 2))
    (hL : 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) ≤ T ^ (eps ^ 2))
    (hQ1 : 1 ≤ Q) (hQ3 : Q ^ 3 ≤ T ^ (eps ^ 2))
    (hNlo : T ^ ((9 : ℝ) / 11) ≤ (N : ℝ)) (hNhi : (N : ℝ) ≤ T ^ (1 - eps))
    (hsl : 5 * eps ≤ sigma) (hsh : sigma ≤ 7 / 32 - 5 * eps)
    (hmass : ‖a‖ ^ 2 ≤ Q / (N : ℝ))
    (hthr : 2400 * Q ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T)
    (hbig : ∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖⟪dyadicDirRow N x, a⟫_ℂ‖) :
    (S.card : ℝ) ≤ T ^ (2 * sigma - eps ^ 2 / 5) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT1
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hbase := huxley_energy_two_term hN a hT0.le (by linarith) hmass hthr
    S hsep hspread hbig
  set X : ℝ := T ^ (eps ^ 2) with hXdef
  set L : ℝ := 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) with hLdef
  clear_value X L
  have hX0 : (0 : ℝ) < X := by rw [hXdef]; exact Real.rpow_pos_of_pos hT0 _
  have hL0 : (0 : ℝ) ≤ L := by
    have hlog : (0 : ℝ) ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    have : (0 : ℝ) ≤ 12 * Real.pi * (1 + Real.log (2 * T + 1)) := by positivity
    rw [hLdef]
    linarith
  have hQ : Q ≤ X := by
    have hQpow : Q ≤ Q ^ 3 := by
      calc
        Q = Q ^ 1 := by ring
        _ ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
    linarith
  have hneg : 6 * sigma - 2 ≤ 0 := by linarith
  have hexp1 : (N : ℝ) ^ (6 * sigma - 2) ≤
      T ^ (((9 : ℝ) / 11) * (6 * sigma - 2)) := by
    have hTpos : (0 : ℝ) < T ^ ((9 : ℝ) / 11) := Real.rpow_pos_of_pos hT0 _
    have h := Real.rpow_le_rpow_of_nonpos hTpos hNlo hneg
    rwa [← Real.rpow_mul hT0.le] at h
  have hexp2 : (N : ℝ) ^ (2 * sigma) ≤ T ^ ((1 - eps) * (2 * sigma)) := by
    have h := Real.rpow_le_rpow hN0.le hNhi (by linarith : (0 : ℝ) ≤ 2 * sigma)
    rwa [← Real.rpow_mul hT0.le] at h
  have hterm1 : 6594624 * T * Q ^ 3 * (N : ℝ) ^ (6 * sigma - 2) * L ≤
      X * T * X * T ^ (((9 : ℝ) / 11) * (6 * sigma - 2)) * X := by
    gcongr
  have hterm2 : 2 * Q * (N : ℝ) ^ (2 * sigma) * L ≤
      2 * X * T ^ ((1 - eps) * (2 * sigma)) * X := by
    gcongr
  have hTT : T * T ^ (((9 : ℝ) / 11) * (6 * sigma - 2)) =
      T ^ (1 + ((9 : ℝ) / 11) * (6 * sigma - 2)) := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  have hXXX : X * X * X = T ^ (3 * eps ^ 2) := by
    rw [hXdef, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1
    ring
  have hXX : X * X = T ^ (2 * eps ^ 2) := by
    rw [hXdef, ← Real.rpow_add hT0]
    congr 1
    ring
  have hprod1 : X * T * X * T ^ (((9 : ℝ) / 11) * (6 * sigma - 2)) * X =
      T ^ (3 * eps ^ 2) *
        T ^ (1 + ((9 : ℝ) / 11) * (6 * sigma - 2)) := by
    rw [← hXXX, ← hTT]
    ring
  have hprod2 : 2 * X * T ^ ((1 - eps) * (2 * sigma)) * X =
      2 * (T ^ (2 * eps ^ 2) * T ^ ((1 - eps) * (2 * sigma))) := by
    rw [← hXX]
    ring
  have hcollapse1 : T ^ (3 * eps ^ 2) *
      T ^ (1 + ((9 : ℝ) / 11) * (6 * sigma - 2)) =
      T ^ (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) := by
    rw [← Real.rpow_add hT0]
  have hcollapse2 : T ^ (2 * eps ^ 2) * T ^ ((1 - eps) * (2 * sigma)) =
      T ^ (2 * eps ^ 2 + (1 - eps) * (2 * sigma)) := by
    rw [← Real.rpow_add hT0]
  have heps2 : eps ^ 2 ≤ eps / 1000 := by nlinarith [heps, hepss]
  have hgap1 : eps ^ 2 +
      (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) ≤
      2 * sigma - eps ^ 2 / 5 := by
    linarith
  have hgap2 : eps ^ 2 + (2 * eps ^ 2 + (1 - eps) * (2 * sigma)) ≤
      2 * sigma - eps ^ 2 / 5 := by
    nlinarith [heps2, hsl, heps, mul_le_mul_of_nonneg_right hsl heps.le]
  have hA : 2 * T ^
      (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) ≤
      T ^ (2 * sigma - eps ^ 2 / 5) := by
    have hp : (0 : ℝ) < T ^
        (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) :=
      Real.rpow_pos_of_pos hT0 _
    have h1 : X * T ^
        (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) ≤
        T ^ (2 * sigma - eps ^ 2 / 5) := by
      rw [hXdef, ← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le hT1 hgap1
    have h2 : (2 : ℝ) * T ^
        (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) ≤
        X * T ^
          (3 * eps ^ 2 + (1 + ((9 : ℝ) / 11) * (6 * sigma - 2))) :=
      mul_le_mul_of_nonneg_right (by linarith) hp.le
    linarith
  have hB : 2 * (2 * T ^ (2 * eps ^ 2 + (1 - eps) * (2 * sigma))) ≤
      T ^ (2 * sigma - eps ^ 2 / 5) := by
    have hp : (0 : ℝ) < T ^ (2 * eps ^ 2 + (1 - eps) * (2 * sigma)) :=
      Real.rpow_pos_of_pos hT0 _
    have h1 : X * T ^ (2 * eps ^ 2 + (1 - eps) * (2 * sigma)) ≤
        T ^ (2 * sigma - eps ^ 2 / 5) := by
      rw [hXdef, ← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le hT1 hgap2
    have h2 : (4 : ℝ) * T ^ (2 * eps ^ 2 + (1 - eps) * (2 * sigma)) ≤
        X * T ^ (2 * eps ^ 2 + (1 - eps) * (2 * sigma)) :=
      mul_le_mul_of_nonneg_right (by linarith) hp.le
    linarith
  have hsum : (S.card : ℝ) ≤
      6594624 * T * Q ^ 3 * (N : ℝ) ^ (6 * sigma - 2) * L +
        2 * Q * (N : ℝ) ^ (2 * sigma) * L := by
    calc
      (S.card : ℝ) ≤
          (6594624 * T * Q ^ 3 * (N : ℝ) ^ (6 * sigma - 2) +
            2 * Q * (N : ℝ) ^ (2 * sigma)) * L := hbase
      _ = 6594624 * T * Q ^ 3 * (N : ℝ) ^ (6 * sigma - 2) * L +
          2 * Q * (N : ℝ) ^ (2 * sigma) * L := by ring
  rw [hprod1, hcollapse1] at hterm1
  rw [hprod2, hcollapse2] at hterm2
  linarith [hsum, hterm1, hterm2, hA, hB]

end RHTower.Sieve
