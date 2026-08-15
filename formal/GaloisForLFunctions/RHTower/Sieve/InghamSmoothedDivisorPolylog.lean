import GaloisForLFunctions.RHTower.Sieve.InghamSmoothedDivisorMeanSquare
import GaloisForLFunctions.HTGeometry.DiscreteAbelIcc
import GaloisForLFunctions.RHTower.MellinOrderOneEnvelope

/-!
# Polylogarithmic mean square for Ingham's smoothed divisor carrier

Discrete Abel summation applies the cumulative `d(n)²` average before exponential smoothing.
This removes the fixed `X^(1/200)` loss from the earlier pointwise-divisor treatment and preserves
uniformity as a density line approaches `σ = 1`.
-/

open Complex MeasureTheory Set Finset

namespace RHTower.Sieve

noncomputable section

private theorem one_add_pow_four_le_sixteen (u : ℝ) (hu : 0 ≤ u) :
    (1 + u) ^ 4 ≤ 16 * (1 + u ^ 4) := by
  by_cases h : u ≤ 1
  · have hbase : 1 + u ≤ 2 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + u) hbase 4
    calc
      (1 + u) ^ 4 ≤ 2 ^ 4 := hp
      _ ≤ 16 * (1 + u ^ 4) := by nlinarith [pow_nonneg hu 4]
  · have hbase : 1 + u ≤ 2 * u := by linarith
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + u) hbase 4
    calc
      (1 + u) ^ 4 ≤ (2 * u) ^ 4 := hp
      _ = 16 * u ^ 4 := by ring
      _ ≤ 16 * (1 + u ^ 4) := by nlinarith [pow_nonneg hu 4]

private theorem exists_scaled_exponential_fourth_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ X M : ℕ, 1 ≤ X →
      (∑ m ∈ Finset.Icc 1 M,
        (1 + (m : ℝ) / (X : ℝ)) ^ 4 *
          Real.exp (-((m : ℝ) / (X : ℝ)))) ≤ K * (X : ℝ) := by
  let G0 : ℝ := Real.Gamma 1
  let G5 : ℝ := Real.Gamma 5
  let K : ℝ := 16 * ((1 + Real.exp 1 * G0) +
    (1 + Real.exp 1 * 16 * G5))
  have hG0 : 0 < G0 := by dsimp only [G0]; exact Real.Gamma_pos_of_pos (by norm_num)
  have hG5 : 0 < G5 := by dsimp only [G5]; exact Real.Gamma_pos_of_pos (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X M hX
  let x : ℝ := 1 / (X : ℝ)
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx : 0 < x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := by dsimp only [x]; exact (div_le_one hXR).2 hXR1
  have hinv : 1 / x = (X : ℝ) := by dsimp only [x]; field_simp
  obtain ⟨hs0, hb0⟩ :=
    RHTower.summable_natSucc_rpow_exp_neg_and_tsum_le
      (r := (0 : ℝ)) (x := x) (by norm_num) hx
  obtain ⟨hs4, hb4⟩ :=
    RHTower.summable_natSucc_rpow_exp_neg_and_tsum_le
      (r := (4 : ℝ)) (x := x) (by norm_num) hx
  let a0 : ℕ → ℝ := fun m => Real.exp (-((m : ℝ) * x))
  let a4 : ℕ → ℝ := fun m => ((m : ℝ) + 1) ^ (4 : ℕ) * Real.exp (-((m : ℝ) * x))
  have ha4eq : a4 = fun m : ℕ =>
      ((m : ℝ) + 1) ^ (4 : ℝ) * Real.exp (-((m : ℝ) * x)) := by
    funext m
    dsimp only [a4]
    rw [← Real.rpow_natCast ((m : ℝ) + 1) 4]
    norm_num
  have hs0' : Summable a0 := by
    simpa only [a0, Real.rpow_zero, one_mul] using hs0
  have hs4' : Summable a4 := by
    rw [ha4eq]
    exact hs4
  have hb0' : (∑' m : ℕ, a0 m) ≤ 1 + Real.exp x * (1 / x) * G0 := by
    simpa only [a0, Real.rpow_zero, one_mul, mul_one, zero_add, Real.rpow_one, G0] using hb0
  have hb4' : (∑' m : ℕ, a4 m) ≤
      1 + Real.exp x * 16 * (1 / x) ^ (5 : ℝ) * G5 := by
    rw [ha4eq]
    simpa only [show (2 : ℝ) ^ (4 : ℝ) = 16 by norm_num,
      show (4 : ℝ) + 1 = 5 by norm_num, G5] using hb4
  let b : ℕ → ℝ := fun m => 16 * (a0 m + x ^ 4 * a4 m)
  have hsb : Summable b := by
    exact (hs0'.add (hs4'.mul_left (x ^ 4))).mul_left 16
  have hpoint (m : ℕ) :
      (1 + (m : ℝ) / (X : ℝ)) ^ 4 *
          Real.exp (-((m : ℝ) / (X : ℝ))) ≤ b m := by
    have hmx : (m : ℝ) / (X : ℝ) = (m : ℝ) * x := by
      dsimp only [x]
      ring
    have hu : 0 ≤ (m : ℝ) * x := mul_nonneg (by positivity) hx.le
    rw [hmx]
    have hp := one_add_pow_four_le_sixteen ((m : ℝ) * x) hu
    have hmle : (m : ℝ) ^ 4 ≤ ((m : ℝ) + 1) ^ 4 := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) 4
    have hux : ((m : ℝ) * x) ^ 4 ≤ x ^ 4 * ((m : ℝ) + 1) ^ 4 := by
      rw [mul_pow]
      nlinarith [sq_nonneg (x ^ 2), mul_nonneg (pow_nonneg hx.le 4) (sub_nonneg.mpr hmle)]
    have hexp0 : 0 ≤ Real.exp (-((m : ℝ) * x)) := (Real.exp_pos _).le
    calc
      (1 + (m : ℝ) * x) ^ 4 * Real.exp (-((m : ℝ) * x)) ≤
          (16 * (1 + ((m : ℝ) * x) ^ 4)) * Real.exp (-((m : ℝ) * x)) :=
        mul_le_mul_of_nonneg_right hp hexp0
      _ ≤ 16 * (1 + x ^ 4 * ((m : ℝ) + 1) ^ 4) *
          Real.exp (-((m : ℝ) * x)) := by gcongr
      _ ≤ b m := by
        dsimp only [b, a0, a4]
        ring_nf
        norm_num
  have hfinite :
      (∑ m ∈ Finset.Icc 1 M,
        (1 + (m : ℝ) / (X : ℝ)) ^ 4 *
          Real.exp (-((m : ℝ) / (X : ℝ)))) ≤ ∑' m : ℕ, b m := by
    exact (Finset.sum_le_sum fun m _ => hpoint m).trans
      (hsb.sum_le_tsum _ (fun m _ => by dsimp only [b, a0, a4]; positivity))
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have h0 : (∑' m : ℕ, a0 m) ≤ (1 + Real.exp 1 * G0) * (X : ℝ) := by
    calc
      (∑' m : ℕ, a0 m) ≤ 1 + Real.exp x * (1 / x) * G0 := hb0'
      _ ≤ 1 + Real.exp 1 * (X : ℝ) * G0 := by rw [hinv]; gcongr
      _ ≤ (1 + Real.exp 1 * G0) * (X : ℝ) := by
        nlinarith [mul_nonneg (Real.exp_pos 1).le hG0.le]
  have hxpow : x ^ 4 * (1 / x) ^ (5 : ℝ) = (X : ℝ) := by
    dsimp only [x]
    rw [show (1 / (X : ℝ)) ^ 4 = (X : ℝ) ^ (-(4 : ℝ)) by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hXR.le]; norm_num]
    rw [show (1 / (1 / (X : ℝ))) ^ (5 : ℝ) = (X : ℝ) ^ (5 : ℝ) by field_simp]
    rw [← Real.rpow_add hXR]
    norm_num
  have hx4le : x ^ 4 ≤ (X : ℝ) := by
    have hx4le1 : x ^ 4 ≤ 1 := pow_le_one₀ hx.le hx1
    exact hx4le1.trans hXR1
  have h4 : x ^ 4 * (∑' m : ℕ, a4 m) ≤
      (1 + Real.exp 1 * 16 * G5) * (X : ℝ) := by
    calc
      x ^ 4 * (∑' m : ℕ, a4 m) ≤
          x ^ 4 * (1 + Real.exp x * 16 * (1 / x) ^ (5 : ℝ) * G5) :=
        mul_le_mul_of_nonneg_left hb4' (pow_nonneg hx.le 4)
      _ = x ^ 4 + Real.exp x * 16 * G5 *
          (x ^ 4 * (1 / x) ^ (5 : ℝ)) := by ring
      _ ≤ (X : ℝ) + Real.exp 1 * 16 * G5 * (X : ℝ) := by
        rw [hxpow]
        gcongr
      _ = (1 + Real.exp 1 * 16 * G5) * (X : ℝ) := by ring
  have hbEq : (∑' m : ℕ, b m) =
      16 * ((∑' m : ℕ, a0 m) + x ^ 4 * (∑' m : ℕ, a4 m)) := by
    dsimp only [b]
    rw [tsum_mul_left]
    congr 1
    rw [hs0'.tsum_add (hs4'.mul_left (x ^ 4)), tsum_mul_left]
  calc
    (∑ m ∈ Finset.Icc 1 M,
        (1 + (m : ℝ) / (X : ℝ)) ^ 4 *
          Real.exp (-((m : ℝ) / (X : ℝ)))) ≤ ∑' m : ℕ, b m := hfinite
    _ = 16 * ((∑' m : ℕ, a0 m) + x ^ 4 * (∑' m : ℕ, a4 m)) := hbEq
    _ ≤ 16 * (((1 + Real.exp 1 * G0) * (X : ℝ)) +
        ((1 + Real.exp 1 * 16 * G5) * (X : ℝ))) := by gcongr
    _ = K * (X : ℝ) := by dsimp only [K]; ring

private theorem inghamSmoothedDivisorWeight_succ_le
    (X m : ℕ) (hX : 1 ≤ X) :
    inghamSmoothedDivisorWeight X (m + 1) ≤ inghamSmoothedDivisorWeight X m := by
  unfold inghamSmoothedDivisorWeight
  apply Real.exp_le_exp.mpr
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hm : (m : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (Nat.le_succ m)
  have hdiv : (m : ℝ) / (X : ℝ) ≤ ((m + 1 : ℕ) : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right hm hXR.le
  linarith

private theorem inghamSmoothedDivisorWeight_sub_succ_le
    (X m : ℕ) (hX : 1 ≤ X) :
    inghamSmoothedDivisorWeight X m - inghamSmoothedDivisorWeight X (m + 1) ≤
      (1 / (X : ℝ)) * inghamSmoothedDivisorWeight X m := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  let δ : ℝ := 1 / (X : ℝ)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hexpLoss : 1 - Real.exp (-δ) ≤ δ := by
    have h := Real.add_one_le_exp (-δ)
    linarith
  have hfactor : inghamSmoothedDivisorWeight X (m + 1) =
      inghamSmoothedDivisorWeight X m * Real.exp (-δ) := by
    unfold inghamSmoothedDivisorWeight
    rw [← Real.exp_add]
    congr 1
    dsimp only [δ]
    field_simp
    norm_num [Nat.cast_add]
    ring
  rw [hfactor]
  have hweight : 0 ≤ inghamSmoothedDivisorWeight X m :=
    inghamSmoothedDivisorWeight_nonneg X m
  calc
    inghamSmoothedDivisorWeight X m -
        inghamSmoothedDivisorWeight X m * Real.exp (-δ) =
        inghamSmoothedDivisorWeight X m * (1 - Real.exp (-δ)) := by ring
    _ ≤ inghamSmoothedDivisorWeight X m * δ :=
      mul_le_mul_of_nonneg_left hexpLoss hweight
    _ = (1 / (X : ℝ)) * inghamSmoothedDivisorWeight X m := by
      dsimp only [δ]
      ring

private theorem one_add_log_nat_le_scaled
    (X m : ℕ) (hX : 1 ≤ X) (hm : 1 ≤ m) :
    1 + Real.log (m : ℝ) ≤
      (1 + Real.log (X : ℝ)) * (1 + (m : ℝ) / (X : ℝ)) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 < (m : ℝ) / (X : ℝ) := div_pos hmR hXR
  have hmul : (m : ℝ) = (X : ℝ) * ((m : ℝ) / (X : ℝ)) := by
    field_simp
  have hlog : Real.log ((m : ℝ) / (X : ℝ)) ≤
      (m : ℝ) / (X : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hu
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have hlogm : Real.log (m : ℝ) =
      Real.log (X : ℝ) + Real.log ((m : ℝ) / (X : ℝ)) := by
    calc
      Real.log (m : ℝ) =
          Real.log ((X : ℝ) * ((m : ℝ) / (X : ℝ))) := congrArg Real.log hmul
      _ = Real.log (X : ℝ) + Real.log ((m : ℝ) / (X : ℝ)) :=
        Real.log_mul hXR.ne' hu.ne'
  rw [hlogm]
  nlinarith [mul_nonneg hlogX (le_of_lt hu)]

private theorem scaled_boundary_envelope (u : ℝ) (hu : 0 ≤ u) :
    u * (1 + u) ^ 3 * Real.exp (-u) ≤ 8 * (1 + Real.exp 16) := by
  by_cases hu1 : u ≤ 1
  · have hbase : 1 + u ≤ 2 := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + u) hbase 3
    have hexp : Real.exp (-u) ≤ 1 := by
      simpa using (Real.exp_le_one_iff.mpr (by linarith : -u ≤ 0))
    have hpoly : u * (1 + u) ^ 3 ≤ 8 := by nlinarith
    calc
      u * (1 + u) ^ 3 * Real.exp (-u) ≤ 8 * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ ≤ 8 := by nlinarith
      _ ≤ 8 * (1 + Real.exp 16) := by nlinarith [Real.exp_pos 16]
  · have huOne : 1 ≤ u := le_of_not_ge hu1
    have hbase : 1 + u ≤ 2 * u := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + u) hbase 3
    have hpoly : u * (1 + u) ^ 3 ≤ 8 * u ^ 4 := by
      calc
        u * (1 + u) ^ 3 ≤ u * (2 * u) ^ 3 :=
          mul_le_mul_of_nonneg_left hpow hu
        _ = 8 * u ^ 4 := by ring
    have hrpow := RHTower.rpow_mul_exp_neg_le
      (m := (4 : ℝ)) (c := (1 : ℝ)) (u := u) (by norm_num) (by norm_num) huOne
    have htail : u ^ (4 : ℕ) * Real.exp (-u) ≤ Real.exp 16 := by
      calc
        u ^ (4 : ℕ) * Real.exp (-u) =
            u ^ (((4 : ℕ) : ℝ)) * Real.exp (-u) := by
              rw [Real.rpow_natCast]
        _ ≤ Real.exp 16 := by
          convert hrpow using 1 <;> norm_num
    calc
      u * (1 + u) ^ 3 * Real.exp (-u) ≤ 8 * u ^ 4 * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = 8 * (u ^ 4 * Real.exp (-u)) := by ring
      _ ≤ 8 * Real.exp 16 := by gcongr
      _ ≤ 8 * (1 + Real.exp 16) := by nlinarith [Real.exp_pos 16]

theorem exists_inghamSmoothedDivisorWeightedMass_le_polylog :
    ∃ K : ℝ, 0 < K ∧ ∀ X M : ℕ, 1 ≤ X →
      inghamSmoothedDivisorWeightedMass X M ≤
        K * (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3 := by
  obtain ⟨K₀, hK₀, hscaled⟩ := exists_scaled_exponential_fourth_moment_bound
  let B : ℝ := 8 * (1 + Real.exp 16)
  let K : ℝ := K₀ + B
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro X M hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  let F : ℕ → ℝ := fun n => (n.divisors.card : ℝ) ^ 2
  let g : ℕ → ℝ := fun n => inghamSmoothedDivisorWeight X n
  let A : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 1 m, F k
  let L : ℝ := 1 + Real.log (X : ℝ)
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hpartial (m : ℕ) (hm : 1 ≤ m) :
      let u : ℝ := (m : ℝ) / (X : ℝ)
      A m ≤ (X : ℝ) * L ^ 3 * u * (1 + u) ^ 3 ∧
        A m ≤ (X : ℝ) * L ^ 3 * (1 + u) ^ 4 := by
    let u : ℝ := (m : ℝ) / (X : ℝ)
    have hu : 0 ≤ u := by dsimp only [u]; positivity
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmEq : (m : ℝ) = (X : ℝ) * u := by
      dsimp only [u]
      field_simp
    have hbase : A m ≤
        (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 3 := by
      have h := sum_card_divisors_pow_le_polylog 2 m hm
      simpa only [A, F, show 2 ^ 2 - 1 = 3 by norm_num] using h
    have hlogScale : 1 + Real.log (m : ℝ) ≤ L * (1 + u) := by
      simpa only [L, u] using one_add_log_nat_le_scaled X m hX hm
    have hlogm0 : 0 ≤ 1 + Real.log (m : ℝ) := by
      have : 0 ≤ Real.log (m : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hm)
      linarith
    have hpow : (1 + Real.log (m : ℝ)) ^ 3 ≤ (L * (1 + u)) ^ 3 :=
      pow_le_pow_left₀ hlogm0 hlogScale 3
    have hsharp : A m ≤ (X : ℝ) * L ^ 3 * u * (1 + u) ^ 3 := by
      calc
        A m ≤ (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 3 := hbase
        _ ≤ (m : ℝ) * (L * (1 + u)) ^ 3 :=
          mul_le_mul_of_nonneg_left hpow hmR.le
        _ = (X : ℝ) * L ^ 3 * u * (1 + u) ^ 3 := by rw [hmEq]; ring
    have huPow : u * (1 + u) ^ 3 ≤ (1 + u) ^ 4 := by
      calc
        u * (1 + u) ^ 3 ≤ (1 + u) * (1 + u) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith : u ≤ 1 + u)
            (pow_nonneg (by linarith : 0 ≤ 1 + u) 3)
        _ = (1 + u) ^ 4 := by ring
    refine ⟨hsharp, ?_⟩
    have hcoeff0 : 0 ≤ (X : ℝ) * L ^ 3 :=
      mul_nonneg hXR.le (pow_nonneg hL.le 3)
    have hcoarse : (X : ℝ) * L ^ 3 * u * (1 + u) ^ 3 ≤
        (X : ℝ) * L ^ 3 * (1 + u) ^ 4 := by
      calc
        (X : ℝ) * L ^ 3 * u * (1 + u) ^ 3 =
            ((X : ℝ) * L ^ 3) * (u * (1 + u) ^ 3) := by ring
        _ ≤ ((X : ℝ) * L ^ 3) * (1 + u) ^ 4 :=
          mul_le_mul_of_nonneg_left huPow hcoeff0
    simpa only [u] using hsharp.trans hcoarse
  have hAnonneg (m : ℕ) : 0 ≤ A m := by
    dsimp only [A, F]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      A m * (g m - g (m + 1)) ≤
        L ^ 3 * ((1 + (m : ℝ) / (X : ℝ)) ^ 4 * g m) := by
    intro m hmMem
    have hm : 1 ≤ m := (Finset.mem_Icc.mp hmMem).1
    have hpart := (hpartial m hm).2
    have hdiff0 : 0 ≤ g m - g (m + 1) := by
      dsimp only [g]
      exact sub_nonneg.mpr (inghamSmoothedDivisorWeight_succ_le X m hX)
    have hdiff : g m - g (m + 1) ≤ (1 / (X : ℝ)) * g m := by
      dsimp only [g]
      exact inghamSmoothedDivisorWeight_sub_succ_le X m hX
    have hscaledNonneg :
        0 ≤ (X : ℝ) * L ^ 3 * (1 + (m : ℝ) / (X : ℝ)) ^ 4 := by
      positivity
    calc
      A m * (g m - g (m + 1)) ≤
          ((X : ℝ) * L ^ 3 * (1 + (m : ℝ) / (X : ℝ)) ^ 4) *
            (g m - g (m + 1)) :=
        mul_le_mul_of_nonneg_right hpart hdiff0
      _ ≤ ((X : ℝ) * L ^ 3 * (1 + (m : ℝ) / (X : ℝ)) ^ 4) *
          ((1 / (X : ℝ)) * g m) :=
        mul_le_mul_of_nonneg_left hdiff hscaledNonneg
      _ = L ^ 3 * ((1 + (m : ℝ) / (X : ℝ)) ^ 4 * g m) := by
        field_simp
  have hinterior :
      (∑ m ∈ Finset.Icc 1 M, A m * (g m - g (m + 1))) ≤
        K₀ * (X : ℝ) * L ^ 3 := by
    calc
      (∑ m ∈ Finset.Icc 1 M, A m * (g m - g (m + 1))) ≤
          ∑ m ∈ Finset.Icc 1 M,
            L ^ 3 * ((1 + (m : ℝ) / (X : ℝ)) ^ 4 * g m) :=
        Finset.sum_le_sum hterm
      _ = L ^ 3 * (∑ m ∈ Finset.Icc 1 M,
            (1 + (m : ℝ) / (X : ℝ)) ^ 4 * g m) := by
        rw [Finset.mul_sum]
      _ ≤ L ^ 3 * (K₀ * (X : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL.le 3)
        simpa only [g, inghamSmoothedDivisorWeight] using hscaled X M hX
      _ = K₀ * (X : ℝ) * L ^ 3 := by ring
  have hboundary : A M * g (M + 1) ≤ B * (X : ℝ) * L ^ 3 := by
    by_cases hM : M = 0
    · subst M
      simp [A]
      positivity
    · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
      let u : ℝ := (M : ℝ) / (X : ℝ)
      have hu : 0 ≤ u := by dsimp only [u]; positivity
      have hpart := (hpartial M hM1).1
      have hg0 : 0 ≤ g (M + 1) := by
        dsimp only [g]
        exact inghamSmoothedDivisorWeight_nonneg X (M + 1)
      have hgmono : g (M + 1) ≤ g M := by
        dsimp only [g]
        exact inghamSmoothedDivisorWeight_succ_le X M hX
      have hcore0 : 0 ≤ (X : ℝ) * L ^ 3 * u * (1 + u) ^ 3 := by positivity
      have hgM : g M = Real.exp (-u) := by
        dsimp only [g, u, inghamSmoothedDivisorWeight]
      have henvelope := scaled_boundary_envelope u hu
      calc
        A M * g (M + 1) ≤
            ((X : ℝ) * L ^ 3 * u * (1 + u) ^ 3) * g (M + 1) :=
          mul_le_mul_of_nonneg_right hpart hg0
        _ ≤ ((X : ℝ) * L ^ 3 * u * (1 + u) ^ 3) * g M :=
          mul_le_mul_of_nonneg_left hgmono hcore0
        _ = (X : ℝ) * L ^ 3 *
            (u * (1 + u) ^ 3 * Real.exp (-u)) := by rw [hgM]; ring
        _ ≤ (X : ℝ) * L ^ 3 * B := by
          exact mul_le_mul_of_nonneg_left henvelope
            (mul_nonneg hXR.le (pow_nonneg hL.le 3))
        _ = B * (X : ℝ) * L ^ 3 := by ring
  unfold inghamSmoothedDivisorWeightedMass
  change (∑ n ∈ Finset.Icc 1 M, F n * g n) ≤ _
  rw [HTGeometry.sum_mul_eq_partial_mul_diff F g M]
  change (∑ m ∈ Finset.Icc 1 M, A m * (g m - g (m + 1))) +
      A M * g (M + 1) ≤ _
  calc
    (∑ m ∈ Finset.Icc 1 M, A m * (g m - g (m + 1))) +
        A M * g (M + 1) ≤
        K₀ * (X : ℝ) * L ^ 3 + B * (X : ℝ) * L ^ 3 :=
      add_le_add hinterior hboundary
    _ = K * (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3 := by
      dsimp only [K, L]
      ring

theorem exists_inghamSmoothedDivisorPlainMass_le_polylog :
    ∃ K : ℝ, 0 < K ∧ ∀ X M : ℕ, 1 ≤ X →
      inghamSmoothedDivisorPlainMass X M ≤
        K * (1 + Real.log (X : ℝ)) ^ 4 := by
  obtain ⟨K₀, hK₀, hweighted⟩ := exists_inghamSmoothedDivisorWeightedMass_le_polylog
  let K : ℝ := 1 + K₀
  have hK : 0 < K := by dsimp only [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro X M hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hL1 : (1 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1 : ℝ) ≤ X)
    linarith
  let s : Finset ℕ := Finset.Icc 1 M
  let q : ℕ → ℝ := fun n =>
    ((n.divisors.card : ℝ) ^ 2 / (n : ℝ)) * inghamSmoothedDivisorWeight X n
  let w : ℕ → ℝ := fun n =>
    (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n
  have hhead : ∑ n ∈ s.filter (fun n => n ≤ X), q n ≤
      (1 + Real.log (X : ℝ)) ^ 4 := by
    calc
      ∑ n ∈ s.filter (fun n => n ≤ X), q n ≤
          ∑ n ∈ s.filter (fun n => n ≤ X),
            (n.divisors.card : ℝ) ^ 2 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnmem := (Finset.mem_filter.mp hn).1
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have hexp : inghamSmoothedDivisorWeight X n ≤ 1 := by
          unfold inghamSmoothedDivisorWeight
          rw [Real.exp_le_one_iff]
          exact neg_nonpos.mpr (div_nonneg (by positivity) hXR.le)
        dsimp only [q]
        exact mul_le_of_le_one_right (by positivity) hexp
      _ ≤ ∑ n ∈ Finset.Icc 1 X,
          (n.divisors.card : ℝ) ^ 2 / (n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hnmem, hnX⟩ := Finset.mem_filter.mp hn
          rw [Finset.mem_Icc]
          exact ⟨(Finset.mem_Icc.mp hnmem).1, hnX⟩
        · intro n _ _
          positivity
      _ ≤ (1 + Real.log (X : ℝ)) ^ 4 :=
        sum_card_divisors_sq_div_le_polylog X hX
  have htail : ∑ n ∈ s.filter (fun n => ¬ n ≤ X), q n ≤
      K₀ * (1 + Real.log (X : ℝ)) ^ 4 := by
    have htailPoint : ∀ n ∈ s.filter (fun n => ¬ n ≤ X),
        q n ≤ (1 / (X : ℝ)) * w n := by
      intro n hn
      obtain ⟨hnmem, hnX⟩ := Finset.mem_filter.mp hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hXnR : (X : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hnX))
      have hinv : 1 / (n : ℝ) ≤ 1 / (X : ℝ) :=
        one_div_le_one_div_of_le hXR hXnR
      dsimp only [q, w]
      calc
        ((n.divisors.card : ℝ) ^ 2 / (n : ℝ)) *
            inghamSmoothedDivisorWeight X n =
            (1 / (n : ℝ)) * ((n.divisors.card : ℝ) ^ 2 *
              inghamSmoothedDivisorWeight X n) := by ring
        _ ≤ (1 / (X : ℝ)) * ((n.divisors.card : ℝ) ^ 2 *
              inghamSmoothedDivisorWeight X n) :=
          mul_le_mul_of_nonneg_right hinv
            (mul_nonneg (sq_nonneg _) (inghamSmoothedDivisorWeight_nonneg X n))
    have hsubset : s.filter (fun n => ¬ n ≤ X) ⊆ Finset.Icc 1 M := by
      exact fun _ hn => (Finset.mem_filter.mp hn).1
    have htailWeighted : ∑ n ∈ s.filter (fun n => ¬ n ≤ X), w n ≤
        inghamSmoothedDivisorWeightedMass X M := by
      unfold inghamSmoothedDivisorWeightedMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by
        dsimp only [w]
        exact mul_nonneg (sq_nonneg _) (inghamSmoothedDivisorWeight_nonneg X n))
    have hLpow : (1 + Real.log (X : ℝ)) ^ 3 ≤
        (1 + Real.log (X : ℝ)) ^ 4 := by
      exact pow_le_pow_right₀ hL1 (by omega)
    calc
      ∑ n ∈ s.filter (fun n => ¬ n ≤ X), q n ≤
          ∑ n ∈ s.filter (fun n => ¬ n ≤ X), (1 / (X : ℝ)) * w n :=
        Finset.sum_le_sum htailPoint
      _ = (1 / (X : ℝ)) * ∑ n ∈ s.filter (fun n => ¬ n ≤ X), w n := by
        rw [Finset.mul_sum]
      _ ≤ (1 / (X : ℝ)) * inghamSmoothedDivisorWeightedMass X M :=
        mul_le_mul_of_nonneg_left htailWeighted (by positivity)
      _ ≤ (1 / (X : ℝ)) *
          (K₀ * (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left (hweighted X M hX) (by positivity)
      _ = K₀ * (1 + Real.log (X : ℝ)) ^ 3 := by field_simp
      _ ≤ K₀ * (1 + Real.log (X : ℝ)) ^ 4 :=
        mul_le_mul_of_nonneg_left hLpow hK₀.le
  unfold inghamSmoothedDivisorPlainMass
  change ∑ n ∈ s, q n ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n ≤ X) q]
  calc
    ∑ n ∈ s.filter (fun n => n ≤ X), q n +
        ∑ n ∈ s.filter (fun n => ¬ n ≤ X), q n ≤
        (1 + Real.log (X : ℝ)) ^ 4 +
          K₀ * (1 + Real.log (X : ℝ)) ^ 4 := add_le_add hhead htail
    _ = K * (1 + Real.log (X : ℝ)) ^ 4 := by dsimp only [K]; ring

/-- Uniform affine mean square with no fixed power loss.  Cumulative divisor-square averaging is
performed before exponential smoothing, so both coefficient prices remain polylogarithmic. -/
theorem exists_integral_Icc_normSq_inghamSmoothedCriticalDivisorPolynomial_le_polylog :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
      ∀ X M : ℕ, 1 ≤ X → ∀ T : ℝ, 1 ≤ T →
        (∫ t in Set.Icc (-T) T,
          ‖inghamSmoothedCriticalDivisorPolynomial X M t‖ ^ 2) ≤
            5 * Real.pi * Real.exp 1 *
                (K₁ * (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3) +
              (5 * Real.pi / 2) *
                (K₂ * (1 + Real.log (X : ℝ)) ^ 4) * T := by
  obtain ⟨K₁, hK₁, hweighted⟩ := exists_inghamSmoothedDivisorWeightedMass_le_polylog
  obtain ⟨K₂, hK₂, hplain⟩ := exists_inghamSmoothedDivisorPlainMass_le_polylog
  refine ⟨K₁, K₂, hK₁, hK₂, ?_⟩
  intro X M hX T hT
  have hbase := integral_Icc_normSq_LSeries_le_general_affine
    (a := inghamSmoothedCriticalDivisorSeq X M) (s := Finset.Icc 1 M)
    (by simp) (fun _n hn => inghamSmoothedCriticalDivisorSeq_support hn) 0 hT
  have hconst : generalMeanSquareConst (inghamSmoothedCriticalDivisorSeq X M)
      (Finset.Icc 1 M) 0 ≤
        5 * Real.pi * Real.exp 1 *
          (K₁ * (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 3) := by
    rw [generalMeanSquareConst]
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    rw [inghamSmoothedCriticalDivisorSeq_weighted_mass_eq X M hX]
    exact mul_le_mul_of_nonneg_left (hweighted X M hX) (by positivity)
  have hrate : generalMeanSquareRate (inghamSmoothedCriticalDivisorSeq X M)
      (Finset.Icc 1 M) 0 ≤
        (5 * Real.pi / 2) *
          (K₂ * (1 + Real.log (X : ℝ)) ^ 4) := by
    rw [generalMeanSquareRate]
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    rw [inghamSmoothedCriticalDivisorSeq_plain_mass_eq X M hX]
    exact mul_le_mul_of_nonneg_left (hplain X M hX) (by positivity)
  unfold inghamSmoothedCriticalDivisorPolynomial
  exact hbase.trans (add_le_add hconst
    (mul_le_mul_of_nonneg_right hrate (by linarith)))

end

end RHTower.Sieve
