import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35MiddleA

/-!
# Third-derivative reciprocal-block bound for Matomäki--Teräväinen Lemma 3.5

The general logarithmic `k`-th derivative test is specialized at `k = 3` and transferred through
Abel summation.  On `T/2 ≤ t ≤ T ≤ N³`, the exact reciprocal block satisfies

`|N(1+it)| ≤ 4096 (T^(1/6) N^(-1/2) + N^(1/4) T^(-1/4))`.

All derivative hypotheses are proved from the literal logarithmic phase.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

private theorem rpow_third_first_identity {T N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    (64 * T / N ^ 3) ^ (1 / 6 : ℝ) =
      2 * T ^ (1 / 6 : ℝ) * N ^ (-(1 / 2 : ℝ)) := by
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) hT.le]
  rw [show (64 : ℝ) ^ (1 / 6 : ℝ) = 2 by norm_num]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  norm_num
  rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]

private theorem rpow_third_second_identity {T N : ℝ} (hT : 0 < T) (hN : 0 < N) :
    (T / (4096 * N ^ 3)) ^ (-(1 / 4 : ℝ)) =
      8 * N ^ (3 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ)) := by
  rw [Real.div_rpow hT.le (by positivity), Real.mul_rpow (by norm_num) (by positivity)]
  rw [show (4096 : ℝ) ^ (-(1 / 4 : ℝ)) = (8 : ℝ)⁻¹ by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4096)]
    norm_num]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  rw [Real.rpow_neg hT.le]
  field_simp
  rw [← Real.rpow_add hN]
  norm_num

private theorem rpow_half_mul_inv {N : ℝ} (hN : 0 < N) :
    N ^ (1 / 2 : ℝ) * N⁻¹ = N ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hN]
  congr 1
  norm_num

private theorem rpow_neg_half_mul_three_quarter {N : ℝ} (hN : 0 < N) :
    N ^ (-(1 / 2 : ℝ)) * N ^ (3 / 4 : ℝ) = N ^ (1 / 4 : ℝ) := by
  rw [← Real.rpow_add hN]
  congr 1
  norm_num

/-- Constructed third-derivative bound for the exact reciprocal unit block. -/
theorem norm_mtWattUnitBlock_le_thirdDerivativeWindow
    {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N)
    {T t : ℝ} (hT : 0 < T) (hTcube : T ≤ (N : ℝ) ^ 3)
    (hTt : T / 2 ≤ t) (htT : t ≤ T) :
    ‖mtWattUnitBlock N N' t‖ ≤
      4096 * (T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
        (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) := by
  have ht : 0 < t := (by linarith : 0 < T / 2).trans_le hTt
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hXR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hXle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  let lam : ℝ := t / (2 * Real.pi) * 2 / (2 * ((N : ℝ) + 1)) ^ 3
  have hlam_eq : lam = t / (8 * Real.pi * ((N : ℝ) + 1) ^ 3) := by
    dsimp only [lam]
    field_simp
    ring
  have hlam0 : 0 < lam := by dsimp only [lam]; positivity
  have hNX : (N : ℝ) ^ 3 ≤ ((N : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ hNR.le (by linarith : (N : ℝ) ≤ (N : ℝ) + 1) 3
  have hlam_up : lam ≤ T / (N : ℝ) ^ 3 := by
    rw [hlam_eq]
    have hden : 0 < 8 * Real.pi * ((N : ℝ) + 1) ^ 3 := by positivity
    have hone : 1 ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hfirst : t / (8 * Real.pi * ((N : ℝ) + 1) ^ 3) ≤
        t / ((N : ℝ) + 1) ^ 3 := by
      rw [div_le_div_iff₀ hden (pow_pos hXR 3)]
      have hm := mul_le_mul_of_nonneg_right hone (pow_nonneg hXR.le 3)
      nlinarith
    have hsecond : t / ((N : ℝ) + 1) ^ 3 ≤ T / (N : ℝ) ^ 3 := by
      rw [div_le_div_iff₀ (pow_pos hXR 3) (pow_pos hNR 3)]
      exact mul_le_mul htT hNX (pow_nonneg hNR.le 3) hT.le
    exact hfirst.trans hsecond
  have hlam1 : lam ≤ 1 := by
    exact hlam_up.trans (by
      rw [div_le_one (pow_pos hNR 3)]
      exact hTcube)
  have hXcube : ((N : ℝ) + 1) ^ 3 ≤ 8 * (N : ℝ) ^ 3 := by
    have hp := pow_le_pow_left₀ hXR.le hXle 3
    nlinarith
  have hden : 8 * Real.pi * ((N : ℝ) + 1) ^ 3 ≤ 256 * (N : ℝ) ^ 3 := by
    have hpi : 8 * Real.pi ≤ 32 := by nlinarith [Real.pi_lt_four]
    calc
      8 * Real.pi * ((N : ℝ) + 1) ^ 3 ≤ 32 * ((N : ℝ) + 1) ^ 3 :=
        mul_le_mul_of_nonneg_right hpi (pow_nonneg hXR.le 3)
      _ ≤ 32 * (8 * (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hXcube (by norm_num)
      _ = 256 * (N : ℝ) ^ 3 := by ring
  have hlam_low : T / (4096 * (N : ℝ) ^ 3) ≤ lam := by
    rw [hlam_eq]
    rw [div_le_div_iff₀ (by positivity : 0 < 4096 * (N : ℝ) ^ 3)
      (by positivity : 0 < 8 * Real.pi * ((N : ℝ) + 1) ^ 3)]
    have hleft := mul_le_mul_of_nonneg_left hden hT.le
    have hright := mul_le_mul_of_nonneg_right hTt
      (by positivity : 0 ≤ 4096 * (N : ℝ) ^ 3)
    nlinarith
  rw [mtWattUnitBlock_eq_sum_Ico]
  have hbase := dirichlet_block_one_full t ht 3 (N + 1) (N' + 1)
    (by norm_num) (by omega) (by omega) (by omega) (by
      norm_num [lam] at hlam1 ⊢
      exact hlam1)
  norm_num [Nat.factorial] at hbase
  let L : ℝ := ((N' + 1 - (N + 1) : ℕ) : ℝ)
  let X : ℝ := (N : ℝ) + 1
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hLleN : L ≤ (N : ℝ) := by
    dsimp only [L]
    exact_mod_cast (by omega : N' + 1 - (N + 1) ≤ N)
  have hLleX : L ≤ X := hLleN.trans (by dsimp only [X]; linarith)
  have hratio : L * X⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ (by simpa only [X] using hXR)]
    simpa only [one_mul] using hLleX
  have h64 : 64 * lam ≤ 64 * (T / (N : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hlam_up (by norm_num)
  have hfirstPow := Real.rpow_le_rpow (by positivity) h64
    (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hfirstPow' : (64 * lam) ^ (1 / 6 : ℝ) ≤
      2 * T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ (64 * (T / (N : ℝ) ^ 3)) ^ (1 / 6 : ℝ) := hfirstPow
      _ = (64 * T / (N : ℝ) ^ 3) ^ (1 / 6 : ℝ) := by ring
      _ = _ := rpow_third_first_identity hT hNR
  have hfirst : L * (64 * lam) ^ (1 / 6 : ℝ) * X⁻¹ ≤
      2 * T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      L * (64 * lam) ^ (1 / 6 : ℝ) * X⁻¹ =
          (L * X⁻¹) * (64 * lam) ^ (1 / 6 : ℝ) := by ring
      _ ≤ 1 * (64 * lam) ^ (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := by simpa using hfirstPow'
  have hlowpos : 0 < T / (4096 * (N : ℝ) ^ 3) := by positivity
  have hsecondPow : lam ^ (-(1 / 4 : ℝ)) ≤
      (T / (4096 * (N : ℝ) ^ 3)) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlowpos hlam_low (by norm_num)
  have hsecondPow' : lam ^ (-(1 / 4 : ℝ)) ≤
      8 * (N : ℝ) ^ (3 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ)) :=
    hsecondPow.trans_eq (rpow_third_second_identity hT hNR)
  have hLhalf : L ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hL0 hLleN (by norm_num)
  have hXinv : X⁻¹ ≤ (N : ℝ)⁻¹ :=
    inv_anti₀ hNR (by dsimp only [X]; linarith)
  have hratioHalf : L ^ (1 / 2 : ℝ) * X⁻¹ ≤
      (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ)⁻¹ :=
        mul_le_mul hLhalf hXinv (by positivity) (Real.rpow_nonneg hNR.le _)
      _ = _ := rpow_half_mul_inv hNR
  have hsecond : L ^ (1 / 2 : ℝ) * lam ^ (-(1 / 4 : ℝ)) * X⁻¹ ≤
      8 * (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ)) := by
    calc
      L ^ (1 / 2 : ℝ) * lam ^ (-(1 / 4 : ℝ)) * X⁻¹ =
          (L ^ (1 / 2 : ℝ) * X⁻¹) * lam ^ (-(1 / 4 : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) *
          (8 * (N : ℝ) ^ (3 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul hratioHalf hsecondPow' (Real.rpow_nonneg hlam0.le _)
          (Real.rpow_nonneg hNR.le _)
      _ = 8 * (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ)) := by
        rw [show (N : ℝ) ^ (-(1 / 2 : ℝ)) *
            (8 * (N : ℝ) ^ (3 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) =
          8 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (3 / 4 : ℝ)) *
            T ^ (-(1 / 4 : ℝ)) by ring,
          rpow_neg_half_mul_three_quarter hNR]
  have hsum := add_le_add hfirst hsecond
  calc
    _ ≤ 256 * (L * (64 * lam) ^ (1 / 6 : ℝ) +
          L ^ (1 / 2 : ℝ) * lam ^ (-(1 / 4 : ℝ))) * X⁻¹ := by
      simpa only [L, X, lam] using hbase
    _ = 256 * (L * (64 * lam) ^ (1 / 6 : ℝ) * X⁻¹ +
          L ^ (1 / 2 : ℝ) * lam ^ (-(1 / 4 : ℝ)) * X⁻¹) := by ring
    _ ≤ 256 * (2 * T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
          8 * (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ 4096 * (T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
          (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) := by
      have hx : 0 ≤ T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
      have hy : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ)) := by positivity
      nlinarith

/-- One-unit-factor hybrid driven by the constructed third-derivative bound.  The divisor power
is absorbed from `A,N ≤ T`; only the literal applicability range `T ≤ N³` remains. -/
theorem exists_integral_mtWatt_oneUnit_thirdDerivative_height
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
      T ≤ (N : ℝ) ^ 3 →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) *
          (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
          (1 / (N : ℝ)) *
          (T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
            (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) ^ 2 := by
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨C₀, hC₀, hbase⟩ :=
    exists_integral_normSq_mtWattOneUnitProduct_le hδ
  refine ⟨(4096 : ℝ) ^ 2 * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hAT hNT hTcube
  let V : ℝ :=
    T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
      (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))
  let U : ℝ := 4096 * V
  let B : ℝ :=
    (T + (((2 * A) * N' : ℕ) : ℝ)) *
      (1 / (A : ℝ) ^ 2) *
      (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) *
      (1 / (N : ℝ))
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hpoint : ∀ t ∈ Set.Icc (T / 2) T,
      ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock a A t‖ ^ 2 ≤
        U ^ 2 * ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2 := by
    intro t ht
    have hu := norm_mtWattUnitBlock_le_thirdDerivativeWindow hN hNN' hN'
      hTpos hTcube ht.1 ht.2
    have hu2 := pow_le_pow_left₀ (norm_nonneg _) (show ‖mtWattUnitBlock N N' t‖ ≤ U by
      simpa only [U, V] using hu) 2
    rw [norm_mul, mul_pow]
    nlinarith [sq_nonneg ‖mtWattUnitBlock N N' t‖,
      sq_nonneg ‖mtWattCoefficientBlock a A t‖]
  have hunitCont : Continuous (mtWattUnitBlock N N') := continuous_perronPoly _ _ _
  have hcoeffCont : Continuous (mtWattCoefficientBlock a A) := continuous_perronPoly _ _ _
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖mtWattUnitBlock N N' t‖ ^ 4 *
      ‖mtWattCoefficientBlock a A t‖ ^ 2)
    (g := fun t : ℝ => U ^ 2 *
      ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2)
    (by linarith : T / 2 ≤ T)
    (((hunitCont.norm.pow 4).mul (hcoeffCont.norm.pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul ((hunitCont.mul hcoeffCont).norm.pow 2)).intervalIntegrable _ _)
    hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hprod := hbase a A N N' hA hN hN' T (one_le_two.trans hT)
  have hprodScaled := mul_le_mul_of_nonneg_left hprod (sq_nonneg U)
  have hpre :
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        ((4096 : ℝ) ^ 2 * C₀) *
          (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * B * V ^ 2 := by
    calc
      _ ≤ U ^ 2 *
          (∫ t in (T / 2)..T,
            ‖mtWattUnitBlock N N' t * mtWattCoefficientBlock a A t‖ ^ 2) := hmono
      _ ≤ U ^ 2 *
          (C₀ * (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * B) := by
        simpa only [B, hδ, mul_assoc] using hprodScaled
      _ = ((4096 : ℝ) ^ 2 * C₀) *
          (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * B * V ^ 2 := by
        dsimp only [U]
        ring
  have hN'0 : 0 ≤ (N' : ℝ) := Nat.cast_nonneg _
  have hN'T : (N' : ℝ) ≤ 2 * T := by
    have hcast : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'
    linarith
  have hMquad : (((2 * A) * N' : ℕ) : ℝ) ≤ 4 * T ^ 2 := by
    push_cast
    have hmul := mul_le_mul hAT hN'T hN'0 hT0
    nlinarith
  have hTtwo : 4 ≤ T ^ 2 := by nlinarith
  have hMfour : (((2 * A) * N' : ℕ) : ℝ) ≤ T ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_right hTtwo (sq_nonneg T)
    nlinarith
  have hpow : (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) ≤ T ^ ε := by
    calc
      _ ≤ (T ^ 4) ^ (ε / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hMfour hδ.le
      _ = T ^ ε := by
        have hfour : T ^ (4 : ℕ) = T ^ (4 : ℝ) :=
          (Real.rpow_natCast T 4).symm
        rw [hfour, ← Real.rpow_mul hT0]
        congr 1
        ring
  have hrest0 : 0 ≤ ((4096 : ℝ) ^ 2 * C₀) * (B * V ^ 2) := by positivity
  have hscale := mul_le_mul_of_nonneg_left hpow hrest0
  calc
    _ ≤ ((4096 : ℝ) ^ 2 * C₀) *
        (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * B * V ^ 2 := hpre
    _ ≤ ((4096 : ℝ) ^ 2 * C₀) * T ^ ε * B * V ^ 2 := by
      calc
        ((4096 : ℝ) ^ 2 * C₀) *
            (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) * B * V ^ 2 =
            (((4096 : ℝ) ^ 2 * C₀) * (B * V ^ 2)) *
              (((2 * A) * N' : ℕ) : ℝ) ^ (ε / 4) := by ring
        _ ≤ (((4096 : ℝ) ^ 2 * C₀) * (B * V ^ 2)) * T ^ ε := hscale
        _ = _ := by ring
    _ = _ := by
      dsimp only [B, V]
      ring

private theorem rpow_one_sixth_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 6 : ℝ)) ^ 2 = x ^ (1 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

private theorem rpow_neg_half_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  rw [Real.rpow_neg_one]

private theorem rpow_quarter_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

private theorem rpow_neg_quarter_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (-(1 / 4 : ℝ))) ^ 2 = x ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  norm_num

private theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem rpow_add_pos {x a b : ℝ} (hx : 0 < x) :
    x ^ (a + b) = x ^ a * x ^ b := Real.rpow_add hx a b

/-- Scalar receiver for the one-unit third-derivative hybrid. -/
private theorem mtLemma35_thirdDerivative_scalar_le
    {A N N' : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : N' ≤ 2 * N)
    {T : ℝ} (hT : 2 ≤ T)
    (hAfirst : T ^ (5 / 6 : ℝ) ≤ (A : ℝ) ^ 2)
    (hNfirst : (N : ℝ) ^ (3 / 2 : ℝ) ≤ (A : ℝ) ^ 2)
    (hNsecond : (N : ℝ) ≤ (A : ℝ) * T ^ (1 / 6 : ℝ))
    (hNthird : (N : ℝ) ^ (5 / 2 : ℝ) ≤ (A : ℝ) * T) :
    (T + (((2 * A) * N' : ℕ) : ℝ)) *
        (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) *
        (T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
          (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))) ^ 2 ≤
      20 * (Real.sqrt T / (N : ℝ) ^ 2) := by
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hT0 : 0 ≤ T := hTpos.le
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'R : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'
  have hM : (((2 * A) * N' : ℕ) : ℝ) ≤ 4 * (A : ℝ) * (N : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hN'R (Nat.cast_nonneg A)]
  let x : ℝ := T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ))
  let y : ℝ := (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hV : (x + y) ^ 2 ≤
      2 * (T ^ (1 / 3 : ℝ) * (N : ℝ)⁻¹ +
        (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ))) := by
    have hadd : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
    calc
      _ ≤ 2 * (x ^ 2 + y ^ 2) := hadd
      _ = 2 * (T ^ (1 / 3 : ℝ) * (N : ℝ)⁻¹ +
          (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ))) := by
        dsimp only [x, y]
        rw [mul_pow, mul_pow, rpow_one_sixth_sq hT0,
          rpow_neg_half_sq hNpos.le, rpow_quarter_sq hNpos.le,
          rpow_neg_quarter_sq hT0]
  have hfactor :
      (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ)) ≤
        T / ((A : ℝ) ^ 2 * (N : ℝ)) + 4 / (A : ℝ) := by
    calc
      _ = (T + (((2 * A) * N' : ℕ) : ℝ)) /
          ((A : ℝ) ^ 2 * (N : ℝ)) := by field_simp
      _ ≤ (T + 4 * (A : ℝ) * (N : ℝ)) /
          ((A : ℝ) ^ 2 * (N : ℝ)) :=
        div_le_div_of_nonneg_right (by simpa [add_comm] using add_le_add_left hM T)
          (by positivity)
      _ = _ := by field_simp
  have hThalf : T ^ (1 / 2 : ℝ) = Real.sqrt T := by
    rw [← Real.sqrt_eq_rpow]
  have hterm1 :
      (T / ((A : ℝ) ^ 2 * (N : ℝ))) *
          (T ^ (1 / 3 : ℝ) * (N : ℝ)⁻¹) ≤
        T ^ (1 / 2 : ℝ) / (N : ℝ) ^ 2 := by
    have hpow : T ^ (4 / 3 : ℝ) ≤ (A : ℝ) ^ 2 * T ^ (1 / 2 : ℝ) := by
      have hs := mul_le_mul_of_nonneg_right hAfirst (Real.rpow_nonneg hT0 (1 / 2 : ℝ))
      rw [← rpow_add_pos hTpos] at hs
      norm_num at hs ⊢
      exact hs
    rw [div_eq_mul_inv]
    field_simp
    have hrewrite : T * T ^ (1 / 3 : ℝ) = T ^ (4 / 3 : ℝ) := by
      calc
        T * T ^ (1 / 3 : ℝ) = T ^ (1 : ℝ) * T ^ (1 / 3 : ℝ) := by
          rw [Real.rpow_one]
        _ = T ^ ((1 : ℝ) + 1 / 3) := (Real.rpow_add hTpos _ _).symm
        _ = T ^ (4 / 3 : ℝ) := by norm_num
    rw [hrewrite]
    exact hpow
  have hterm2 :
      (T / ((A : ℝ) ^ 2 * (N : ℝ))) *
          ((N : ℝ) ^ (1 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ))) ≤
        T ^ (1 / 2 : ℝ) / (N : ℝ) ^ 2 := by
    rw [Real.rpow_neg hT0]
    field_simp
    have hNsqrt : (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) =
        (N : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) =
            (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hNpos _ _).symm
        _ = (N : ℝ) ^ (3 / 2 : ℝ) := by norm_num
    have hTsq := rpow_half_sq hT0
    calc
      T * (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) =
          T * (N : ℝ) ^ (3 / 2 : ℝ) := by rw [mul_assoc, hNsqrt]
      _ ≤ T * (A : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hNfirst hT0
      _ = (A : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ)) ^ 2 := by rw [hTsq]; ring
  have hterm3 :
      (4 / (A : ℝ)) * (T ^ (1 / 3 : ℝ) * (N : ℝ)⁻¹) ≤
        4 * (T ^ (1 / 2 : ℝ) / (N : ℝ) ^ 2) := by
    field_simp
    have hs := mul_le_mul_of_nonneg_right hNsecond (Real.rpow_nonneg hT0 (1 / 3 : ℝ))
    have hp : T ^ (1 / 6 : ℝ) * T ^ (1 / 3 : ℝ) = T ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num
    calc
      T ^ (1 / 3 : ℝ) * (N : ℝ) =
          (N : ℝ) * T ^ (1 / 3 : ℝ) := by ring
      _ ≤ ((A : ℝ) * T ^ (1 / 6 : ℝ)) * T ^ (1 / 3 : ℝ) := hs
      _ = (A : ℝ) * T ^ (1 / 2 : ℝ) := by rw [mul_assoc, hp]
  have hterm4 :
      (4 / (A : ℝ)) *
          ((N : ℝ) ^ (1 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ))) ≤
        4 * (T ^ (1 / 2 : ℝ) / (N : ℝ) ^ 2) := by
    rw [Real.rpow_neg hT0]
    field_simp
    have hNpow : (N : ℝ) ^ 2 * (N : ℝ) ^ (1 / 2 : ℝ) =
        (N : ℝ) ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
      norm_num
    have hTsq := rpow_half_sq hT0
    calc
      (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ 2 =
          (N : ℝ) ^ (5 / 2 : ℝ) := by rw [mul_comm, hNpow]
      _ ≤ (A : ℝ) * T := hNthird
      _ = (A : ℝ) * (T ^ (1 / 2 : ℝ)) ^ 2 := by rw [hTsq]
  have hfactor0 : 0 ≤ T / ((A : ℝ) ^ 2 * (N : ℝ)) + 4 / (A : ℝ) := by positivity
  have hmul := mul_le_mul hfactor hV (sq_nonneg _) hfactor0
  calc
    _ = ((T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ))) * (x + y) ^ 2 := by
      dsimp only [x, y]
    _ ≤ (T / ((A : ℝ) ^ 2 * (N : ℝ)) + 4 / (A : ℝ)) *
        (2 * (T ^ (1 / 3 : ℝ) * (N : ℝ)⁻¹ +
          (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ)))) := hmul
    _ ≤ 20 * (T ^ (1 / 2 : ℝ) / (N : ℝ) ^ 2) := by
      nlinarith
    _ = 20 * (Real.sqrt T / (N : ℝ) ^ 2) := by rw [hThalf]

/-- The constructed third-derivative estimate implies the literal Deshouillers--Iwaniec
envelope throughout its scalar applicability range.  No oscillatory or spectral estimate is
retained as a premise. -/
theorem exists_integral_mtDI_lemma35_thirdDerivativeRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
      1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T → (A : ℝ) ≤ T → (N : ℝ) ≤ T →
      T ≤ (N : ℝ) ^ 3 →
      T ^ (5 / 6 : ℝ) ≤ (A : ℝ) ^ 2 →
      (N : ℝ) ^ (3 / 2 : ℝ) ≤ (A : ℝ) ^ 2 →
      (N : ℝ) ≤ (A : ℝ) * T ^ (1 / 6 : ℝ) →
      (N : ℝ) ^ (5 / 2 : ℝ) ≤ (A : ℝ) * T →
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C * T ^ ε *
          (((T + (A : ℝ) ^ 2 * Real.sqrt T +
                  (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                ((N : ℝ) ^ 2 * (A : ℝ)) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
            (1 / (A : ℝ)) *
            (∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2)) := by
  obtain ⟨C₀, hC₀, hbase⟩ :=
    exists_integral_mtWatt_oneUnit_thirdDerivative_height hε
  refine ⟨20 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro a A N N' hA hN hNN' hN' T hT hAT hNT hTcube
    hAfirst hNfirst hNsecond hNthird
  let E : ℝ := ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ 2
  let V : ℝ :=
    T ^ (1 / 6 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
      (N : ℝ) ^ (1 / 4 : ℝ) * T ^ (-(1 / 4 : ℝ))
  let F : ℝ :=
    (T + (((2 * A) * N' : ℕ) : ℝ)) *
      (1 / (A : ℝ) ^ 2) * (1 / (N : ℝ))
  let Q : ℝ :=
    (T + (A : ℝ) ^ 2 * Real.sqrt T +
        (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
      ((N : ℝ) ^ 2 * (A : ℝ)) +
    (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))
  let R : ℝ := Q * (1 / (A : ℝ)) * E
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hTpow0 : 0 ≤ T ^ ε := Real.rpow_nonneg (by positivity) _
  have hraw := hbase a A N N' hA hN hNN' hN' T hT hAT hNT hTcube
  have hscalar := mtLemma35_thirdDerivative_scalar_le hA hN hN' hT
    hAfirst hNfirst hNsecond hNthird
  have hpre :
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        C₀ * T ^ ε * E * (F * V ^ 2) := by
    calc
      _ ≤ C₀ * T ^ ε *
          (T + (((2 * A) * N' : ℕ) : ℝ)) *
          (1 / (A : ℝ) ^ 2) * E * (1 / (N : ℝ)) * V ^ 2 := by
        simpa only [E, V, mul_assoc] using hraw
      _ = C₀ * T ^ ε * E * (F * V ^ 2) := by
        dsimp only [F]
        ac_rfl
  have hscaled := mul_le_mul_of_nonneg_left hscalar
    (mul_nonneg (mul_nonneg hC₀.le hTpow0) hE0)
  have hbranch :
      (∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
        20 * C₀ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E := by
    calc
      _ ≤ C₀ * T ^ ε * E * (F * V ^ 2) := hpre
      _ ≤ C₀ * T ^ ε * E *
          (20 * (Real.sqrt T / (N : ℝ) ^ 2)) := hscaled
      _ = 20 * C₀ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E := by ac_rfl
  have hcarrier : (Real.sqrt T / (N : ℝ) ^ 2) * E ≤ R := by
    have hApos : (0 : ℝ) < A := by exact_mod_cast hA
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hmain : Real.sqrt T / (N : ℝ) ^ 2 ≤ Q * (1 / (A : ℝ)) := by
      dsimp only [Q]
      have hres : 0 ≤ (T + (A : ℝ)) / (T ^ 4 * (A : ℝ)) := by positivity
      calc
        Real.sqrt T / (N : ℝ) ^ 2 =
            ((A : ℝ) ^ 2 * Real.sqrt T /
              ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by
          field_simp [hApos.ne', hNpos.ne']
        _ ≤ ((T + (A : ℝ) ^ 2 * Real.sqrt T +
              (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (A : ℝ))) * (1 / (A : ℝ)) := by
          have hother : 0 ≤
              T + (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
          gcongr
          nlinarith
        _ ≤ (((T + (A : ℝ) ^ 2 * Real.sqrt T +
              (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ 2 * (A : ℝ))) +
              (T + (A : ℝ)) / (T ^ 4 * (A : ℝ))) *
              (1 / (A : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hres) (by positivity)
    exact mul_le_mul_of_nonneg_right hmain hE0
  have htarget :
      20 * C₀ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E ≤
        20 * C₀ * T ^ ε * R := by
    have hcoef : 0 ≤ 20 * C₀ * T ^ ε := by positivity
    calc
      20 * C₀ * T ^ ε * (Real.sqrt T / (N : ℝ) ^ 2) * E =
          (20 * C₀ * T ^ ε) * ((Real.sqrt T / (N : ℝ) ^ 2) * E) := by ac_rfl
      _ ≤ (20 * C₀ * T ^ ε) * R :=
        mul_le_mul_of_nonneg_left hcarrier hcoef
  simpa only [R, Q, mul_assoc] using hbranch.trans htarget

end

end RHTower.Sieve
