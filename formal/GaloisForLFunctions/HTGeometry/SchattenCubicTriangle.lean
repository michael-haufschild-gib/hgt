import GaloisForLFunctions.RHTower.SchattenLogResidueTraceClassPerturbation
import GaloisForLFunctions.HTGeometry.CofinalCapitalDensitySelection
import GaloisForLFunctions.HTGeometry.SchattenNorm

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower ContinuousLinearMap Finset

private theorem rpow_three_eq_cube (x : ℝ) : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by
  convert Real.rpow_natCast x 3 using 1 <;> norm_num

private theorem weighted_sum_le_of_prefix_le
    (a b w : ℕ → ℝ) (N : ℕ)
    (ha : ∀ i < N, 0 ≤ a i) (hb : ∀ i < N, 0 ≤ b i)
    (hw : ∀ i < N, 0 ≤ w i)
    (hwanti : ∀ i j, i ≤ j → j < N → w j ≤ w i)
    (hpref : ∀ k ≤ N, ∑ i ∈ range k, a i ≤ ∑ i ∈ range k, b i) :
    ∑ i ∈ range N, w i * a i ≤ ∑ i ∈ range N, w i * b i := by
  induction N generalizing w with
  | zero => simp
  | succ N ih =>
      let w' : ℕ → ℝ := fun i => w i - w N
      have hwN : 0 ≤ w N := hw N (Nat.lt_succ_self N)
      have hw' : ∀ i < N, 0 ≤ w' i := by
        intro i hi
        exact sub_nonneg.mpr (hwanti i N (Nat.le_of_lt hi) (Nat.lt_succ_self N))
      have hw'anti : ∀ i j, i ≤ j → j < N → w' j ≤ w' i := by
        intro i j hij hj
        dsimp only [w']
        linarith [hwanti i j hij (Nat.lt_trans hj (Nat.lt_succ_self N))]
      have hrec := ih w' (fun i hi => ha i (Nat.lt_trans hi (Nat.lt_succ_self N)))
        (fun i hi => hb i (Nat.lt_trans hi (Nat.lt_succ_self N))) hw' hw'anti
        (fun k hk => hpref k (Nat.le_trans hk (Nat.le_succ N)))
      have hfull := mul_le_mul_of_nonneg_left (hpref (N + 1) le_rfl) hwN
      have hsplit (f : ℕ → ℝ) :
          ∑ i ∈ range N, w i * f i =
            w N * (∑ i ∈ range N, f i) + ∑ i ∈ range N, w' i * f i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [w']
        ring
      have hdecomp_a :
          ∑ i ∈ range (N + 1), w i * a i =
            w N * (∑ i ∈ range (N + 1), a i) +
              ∑ i ∈ range N, w' i * a i := by
        rw [sum_range_succ, sum_range_succ, hsplit a]
        ring
      have hdecomp_b :
          ∑ i ∈ range (N + 1), w i * b i =
            w N * (∑ i ∈ range (N + 1), b i) +
              ∑ i ∈ range N, w' i * b i := by
        rw [sum_range_succ, sum_range_succ, hsplit b]
        ring
      rw [hdecomp_a, hdecomp_b]
      exact add_le_add hfull hrec

theorem weighted_singular_pairing_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hTcpt : IsCompactOperator T)
    {g h : ℕ → H}
    (hg1 : ∀ n, g n = 0 ∨ ‖g n‖ = 1)
    (hgo : ∀ m n, m ≠ n → inner ℂ (g m) (g n) = 0)
    (hh1 : ∀ n, h n = 0 ∨ ‖h n‖ = 1)
    (hho : ∀ m n, m ≠ n → inner ℂ (h m) (h n) = 0)
    (w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i < N, 0 ≤ w i)
    (hwanti : ∀ i j, i ≤ j → j < N → w j ≤ w i) :
    ∑ i ∈ range N, w i * ‖inner ℂ (g i) (T (h i))‖ ≤
      ∑ i ∈ range N, w i * singVal T i := by
  apply weighted_sum_le_of_prefix_le
  · intro i hi
    positivity
  · intro i hi
    exact singVal_nonneg T i
  · exact hw
  · exact hwanti
  · intro k hk
    exact sum_norm_inner_le_sum_singVal hTcpt hg1 hgo hh1 hho
      (range k) (N := k) (by simp)

private theorem finite_holder_two_one
    (x y : ℕ → ℝ) (N : ℕ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    ∑ i ∈ range N, x i ^ 2 * y i ≤
      (∑ i ∈ range N, x i ^ 3) ^ (2 / 3 : ℝ) *
        (∑ i ∈ range N, y i ^ 3) ^ (1 / 3 : ℝ) := by
  let X : Fin N → ℝ := fun i => x i ^ 3
  let Y : Fin N → ℝ := fun i => y i ^ 3
  have h := sum_rpow_mul_rpow_le (X := Fin N)
    (α := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
    (a := X) (b := Y) (fun i => pow_nonneg (hx i) 3) (fun i => pow_nonneg (hy i) 3)
  have hX (i : Fin N) : X i ^ (2 / 3 : ℝ) = x i ^ 2 := by
    dsimp only [X]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (hx i)]; norm_num
  have hY (i : Fin N) : Y i ^ (1 - (2 / 3 : ℝ)) = y i := by
    dsimp only [Y]
    rw [show (1 - (2 / 3 : ℝ)) = 1 / 3 by norm_num]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (hy i)]; norm_num
  dsimp only [X, Y] at h
  have hX' (i : Fin N) : (x i ^ 3) ^ (2 / 3 : ℝ) = x i ^ 2 := hX i
  have hY' (i : Fin N) : (y i ^ 3) ^ (1 - (2 / 3 : ℝ)) = y i := hY i
  have hleft :
      (∑ i : Fin N, (x i ^ 3) ^ (2 / 3 : ℝ) *
        (y i ^ 3) ^ (1 - (2 / 3 : ℝ))) =
        ∑ i : Fin N, x i ^ 2 * y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hX', hY']
  rw [hleft] at h
  norm_num only at h
  change (∑ i : Fin N, x i ^ 2 * y i) ≤
    (∑ i : Fin N, x i ^ 3) ^ (2 / 3 : ℝ) *
      (∑ i : Fin N, y i ^ 3) ^ (1 / 3 : ℝ) at h
  rw [Fin.sum_univ_eq_sum_range (fun i => x i ^ 2 * y i) N,
    Fin.sum_univ_eq_sum_range (fun i => x i ^ 3) N,
    Fin.sum_univ_eq_sum_range (fun i => y i ^ 3) N] at h
  exact h

theorem schattenNorm_three_add_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A B : H →L[ℂ] H} (hA : MemSchattenClass 3 A) (hB : MemSchattenClass 3 B) :
    schattenNorm 3 (A + B) ≤ schattenNorm 3 A + schattenNorm 3 B := by
  let T := A + B
  have hAcpt : IsCompactOperator A := hA.isCompactOperator (by norm_num)
  have hBcpt : IsCompactOperator B := hB.isCompactOperator (by norm_num)
  have hTcpt : IsCompactOperator T := hAcpt.add hBcpt
  let e : ℕ → H := fun n => svVec (energyOp T) n
  let f : ℕ → H := fun n => svdVec T n
  have he : ∀ n, e n = 0 ∨ ‖e n‖ = 1 := by
    intro n
    rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr
        (norm_svVec_of_ne_zero (energyOp_compact hTcpt)
          (energyOp_symmetric T) (energyOp_pos T) hne)
  have hf : ∀ n, f n = 0 ∨ ‖f n‖ = 1 := by
    intro n
    rcases eq_or_ne (singVal T n) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hTcpt hne)
  have heorth : ∀ m n, m ≠ n → inner ℂ (e m) (e n) = 0 := fun m n hmn =>
    inner_svVec_svVec_of_ne _ hmn
  have hforth : ∀ m n, m ≠ n → inner ℂ (f m) (f n) = 0 := fun m n hmn =>
    inner_svdVec_svdVec_of_ne _ hmn
  have hfinite : ∀ N : ℕ,
      (∑ i ∈ range N, singVal T i ^ 3) ^ (1 / 3 : ℝ) ≤
        (∑ i ∈ range N, singVal A i ^ 3) ^ (1 / 3 : ℝ) +
          (∑ i ∈ range N, singVal B i ^ 3) ^ (1 / 3 : ℝ) := by
    intro N
    let w : ℕ → ℝ := fun i => singVal T i ^ 2
    have hw : ∀ i < N, 0 ≤ w i := fun i hi => sq_nonneg _
    have hwanti : ∀ i j, i ≤ j → j < N → w j ≤ w i := by
      intro i j hij hj
      exact pow_le_pow_left₀ (singVal_nonneg T j) (singVal_antitone T hij) 2
    have hdiag :
        ∑ i ∈ range N, singVal T i ^ 3 =
          ∑ i ∈ range N, w i * ‖inner ℂ (f i) (T (e i))‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_svdVec_apply hTcpt]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (singVal_nonneg T i), w]
      ring
    have hsplit :
        ∑ i ∈ range N, w i * ‖inner ℂ (f i) (T (e i))‖ ≤
          (∑ i ∈ range N, w i * ‖inner ℂ (f i) (A (e i))‖) +
            ∑ i ∈ range N, w i * ‖inner ℂ (f i) (B (e i))‖ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have hinner : inner ℂ (f i) (T (e i)) =
          inner ℂ (f i) (A (e i)) + inner ℂ (f i) (B (e i)) := by
        simp only [T, add_apply, inner_add_right]
      rw [hinner]
      calc
        w i * ‖inner ℂ (f i) (A (e i)) + inner ℂ (f i) (B (e i))‖ ≤
            w i * (‖inner ℂ (f i) (A (e i))‖ +
              ‖inner ℂ (f i) (B (e i))‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw i hiN)
        _ = _ := by ring
    have hpairA := weighted_singular_pairing_le hAcpt hf hforth he heorth w N hw hwanti
    have hpairB := weighted_singular_pairing_le hBcpt hf hforth he heorth w N hw hwanti
    have hholderA := finite_holder_two_one (fun i => singVal T i)
      (fun i => singVal A i) N (singVal_nonneg T) (singVal_nonneg A)
    have hholderB := finite_holder_two_one (fun i => singVal T i)
      (fun i => singVal B i) N (singVal_nonneg T) (singVal_nonneg B)
    have hmain :
        (∑ i ∈ range N, singVal T i ^ 3) ≤
          (∑ i ∈ range N, singVal T i ^ 3) ^ (2 / 3 : ℝ) *
            ((∑ i ∈ range N, singVal A i ^ 3) ^ (1 / 3 : ℝ) +
              (∑ i ∈ range N, singVal B i ^ 3) ^ (1 / 3 : ℝ)) := by
      calc
        _ = ∑ i ∈ range N, w i * ‖inner ℂ (f i) (T (e i))‖ := hdiag
        _ ≤ (∑ i ∈ range N, w i * ‖inner ℂ (f i) (A (e i))‖) +
              ∑ i ∈ range N, w i * ‖inner ℂ (f i) (B (e i))‖ := hsplit
        _ ≤ (∑ i ∈ range N, w i * singVal A i) +
              ∑ i ∈ range N, w i * singVal B i := add_le_add hpairA hpairB
        _ ≤ (∑ i ∈ range N, singVal T i ^ 3) ^ (2 / 3 : ℝ) *
              (∑ i ∈ range N, singVal A i ^ 3) ^ (1 / 3 : ℝ) +
            (∑ i ∈ range N, singVal T i ^ 3) ^ (2 / 3 : ℝ) *
              (∑ i ∈ range N, singVal B i ^ 3) ^ (1 / 3 : ℝ) := by
          exact add_le_add hholderA hholderB
        _ = _ := by ring
    set S : ℝ := ∑ i ∈ range N, singVal T i ^ 3 with hS
    set C : ℝ := (∑ i ∈ range N, singVal A i ^ 3) ^ (1 / 3 : ℝ) +
      (∑ i ∈ range N, singVal B i ^ 3) ^ (1 / 3 : ℝ) with hC
    have hS0 : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun i hi => pow_nonneg (singVal_nonneg T i) 3
    rcases eq_or_lt_of_le hS0 with hSz | hSpos
    · rw [← hSz]
      simp only [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
      rw [hC]
      exact add_nonneg
        (Real.rpow_nonneg
          (Finset.sum_nonneg fun i hi => pow_nonneg (singVal_nonneg A i) 3) _)
        (Real.rpow_nonneg
          (Finset.sum_nonneg fun i hi => pow_nonneg (singVal_nonneg B i) 3) _)
    ·
      have hden : 0 < S ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hSpos _
      have hdiv : S / S ^ (2 / 3 : ℝ) ≤ C := (div_le_iff₀ hden).2 (by
        simpa [mul_comm] using hmain)
      have hid : S / S ^ (2 / 3 : ℝ) = S ^ (1 / 3 : ℝ) := by
        calc
          S / S ^ (2 / 3 : ℝ) = S ^ (1 : ℝ) / S ^ (2 / 3 : ℝ) := by
            rw [Real.rpow_one]
          _ = S ^ ((1 : ℝ) - 2 / 3) := (Real.rpow_sub hSpos 1 (2 / 3)).symm
          _ = S ^ (1 / 3 : ℝ) := by norm_num
      rwa [hid] at hdiv
  have hAraw : Summable fun n => approxNumber A n ^ 3 := by
    have h := hA
    unfold RHTower.MemSchattenClass at h
    convert h using 1
    funext n
    exact (Real.rpow_natCast (approxNumber A n) 3).symm
  have hBraw : Summable fun n => approxNumber B n ^ 3 := by
    have h := hB
    unfold RHTower.MemSchattenClass at h
    convert h using 1
    funext n
    exact (Real.rpow_natCast (approxNumber B n) 3).symm
  let C := schattenNorm 3 A + schattenNorm 3 B
  have hC0 : 0 ≤ C := add_nonneg (schattenNorm_nonneg 3 A) (schattenNorm_nonneg 3 B)
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ range N, approxNumber T i ^ 3 ≤ C ^ 3 := by
    intro N
    have hroot := hfinite N
    have hTs (i : ℕ) : singVal T i = approxNumber T i :=
      (approxNumber_eq_singVal hTcpt i).symm
    have hAs (i : ℕ) : singVal A i = approxNumber A i :=
      (approxNumber_eq_singVal hAcpt i).symm
    have hBs (i : ℕ) : singVal B i = approxNumber B i :=
      (approxNumber_eq_singVal hBcpt i).symm
    simp_rw [hTs, hAs, hBs] at hroot
    have hApart : (∑ i ∈ range N, approxNumber A i ^ 3) ^ (1 / 3 : ℝ) ≤
        schattenNorm 3 A := by
      unfold schattenNorm
      rw [tsum_congr fun n => rpow_three_eq_cube (approxNumber A n)]
      apply Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg A i) 3)
      · have hle := hAraw.sum_le_tsum (range N)
          (fun i hi => pow_nonneg (approxNumber_nonneg A i) 3)
        exact hle
      · norm_num
    have hBpart : (∑ i ∈ range N, approxNumber B i ^ 3) ^ (1 / 3 : ℝ) ≤
        schattenNorm 3 B := by
      unfold schattenNorm
      rw [tsum_congr fun n => rpow_three_eq_cube (approxNumber B n)]
      apply Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg B i) 3)
      · have hle := hBraw.sum_le_tsum (range N)
          (fun i hi => pow_nonneg (approxNumber_nonneg B i) 3)
        exact hle
      · norm_num
    have hrootC :
        (∑ i ∈ range N, approxNumber T i ^ 3) ^ (1 / 3 : ℝ) ≤ C :=
      hroot.trans (add_le_add hApart hBpart)
    have hcubed := pow_le_pow_left₀
      (Real.rpow_nonneg (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg T i) 3) _)
      hrootC 3
    have hrootCube :
        ((∑ i ∈ range N, approxNumber T i ^ 3) ^ (1 / 3 : ℝ)) ^ 3 =
          ∑ i ∈ range N, approxNumber T i ^ 3 := by
      convert Real.rpow_inv_natCast_pow
        (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg T i) 3)
        (by norm_num : (3 : ℕ) ≠ 0) using 1 <;> norm_num
    rw [hrootCube] at hcubed
    exact hcubed
  unfold schattenNorm
  have htotal : (∑' n, approxNumber T n ^ 3) ≤ C ^ 3 :=
    Real.tsum_le_of_sum_range_le (fun n => pow_nonneg (approxNumber_nonneg T n) 3) hpartial
  have hpow := Real.rpow_le_rpow (tsum_nonneg fun n => pow_nonneg (approxNumber_nonneg T n) 3)
    htotal (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hCrpow : (C ^ 3) ^ (1 / 3 : ℝ) = C := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC0]
    norm_num
  rw [hCrpow] at hpow
  rw [tsum_congr fun n => rpow_three_eq_cube (approxNumber (A + B) n),
    tsum_congr fun n => rpow_three_eq_cube (approxNumber A n),
    tsum_congr fun n => rpow_three_eq_cube (approxNumber B n)]
  simpa only [T, C, schattenNorm, rpow_three_eq_cube] using hpow

/-- A unit-interval Bochner average contracts the third Schatten norm whenever every
integrand has singular values bounded coordinatewise by a fixed Schatten-three operator. -/
theorem schattenNorm_three_intervalIntegral_le_of_singVal_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : ℝ → H →L[ℂ] H) (C : H →L[ℂ] H)
    (hF : Continuous F) (hFcpt : ∀ t, IsCompactOperator (F t))
    (hC : MemSchattenClass 3 C)
    (hsv : ∀ t i, singVal (F t) i ≤ singVal C i)
    (hKcpt : IsCompactOperator
      (((∫ t : ℝ in 0..1, F t) : H →L[ℂ] H))) :
    schattenNorm 3 (∫ t : ℝ in 0..1, F t) ≤ schattenNorm 3 C := by
  let K : H →L[ℂ] H := ∫ t : ℝ in 0..1, F t
  have hCcpt : IsCompactOperator C := hC.isCompactOperator (by norm_num)
  let e : ℕ → H := fun n => svVec (energyOp K) n
  let f : ℕ → H := fun n => svdVec K n
  have he : ∀ n, e n = 0 ∨ ‖e n‖ = 1 := by
    intro n
    rcases eq_or_ne (svVal (energyOp K) n) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr
        (norm_svVec_of_ne_zero (energyOp_compact hKcpt)
          (energyOp_symmetric K) (energyOp_pos K) hne)
  have hf : ∀ n, f n = 0 ∨ ‖f n‖ = 1 := by
    intro n
    rcases eq_or_ne (singVal K n) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hKcpt hne)
  have heorth : ∀ m n, m ≠ n → inner ℂ (e m) (e n) = 0 := fun m n hmn =>
    inner_svVec_svVec_of_ne _ hmn
  have hforth : ∀ m n, m ≠ n → inner ℂ (f m) (f n) = 0 := fun m n hmn =>
    inner_svdVec_svdVec_of_ne _ hmn
  have hfinite : ∀ N : ℕ,
      (∑ i ∈ range N, singVal K i ^ 3) ^ (1 / 3 : ℝ) ≤
        (∑ i ∈ range N, singVal C i ^ 3) ^ (1 / 3 : ℝ) := by
    intro N
    let w : ℕ → ℝ := fun i => singVal K i ^ 2
    have hw : ∀ i < N, 0 ≤ w i := fun i hi => sq_nonneg _
    have hwanti : ∀ i j, i ≤ j → j < N → w j ≤ w i := by
      intro i j hij hj
      exact pow_le_pow_left₀ (singVal_nonneg K j) (singVal_antitone K hij) 2
    have hdiag :
        ∑ i ∈ range N, singVal K i ^ 3 =
          ∑ i ∈ range N, w i * ‖inner ℂ (f i) (K (e i))‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_svdVec_apply hKcpt]
      change singVal K i ^ 3 = w i * ‖((singVal K i : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (singVal_nonneg K i)]
      dsimp only [w]
      ring
    have hcoord (i : ℕ) :
        ‖inner ℂ (f i) (K (e i))‖ ≤
          ∫ t : ℝ in 0..1, ‖inner ℂ (f i) ((F t) (e i))‖ := by
      let L : (H →L[ℂ] H) →L[ℂ] ℂ :=
        (innerSL ℂ (f i)).comp (ContinuousLinearMap.apply ℂ H (e i))
      have hFint : IntervalIntegrable F MeasureTheory.volume 0 1 :=
        hF.intervalIntegrable 0 1
      have hpull := L.intervalIntegral_comp_comm hFint
      have heq : inner ℂ (f i) (K (e i)) =
          ∫ t : ℝ in 0..1, inner ℂ (f i) ((F t) (e i)) := by
        change L K = ∫ t : ℝ in 0..1, L (F t)
        exact hpull.symm
      rw [heq]
      exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    have htoIntegral :
        ∑ i ∈ range N, w i * ‖inner ℂ (f i) (K (e i))‖ ≤
          ∫ t : ℝ in 0..1,
            ∑ i ∈ range N, w i * ‖inner ℂ (f i) ((F t) (e i))‖ := by
      calc
        _ ≤ ∑ i ∈ range N,
            w i * (∫ t : ℝ in 0..1, ‖inner ℂ (f i) ((F t) (e i))‖) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hcoord i) (hw i (Finset.mem_range.mp hi))
        _ = ∑ i ∈ range N,
            ∫ t : ℝ in 0..1, w i * ‖inner ℂ (f i) ((F t) (e i))‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [intervalIntegral.integral_const_mul]
        _ = _ := by
          rw [intervalIntegral.integral_finsetSum]
          intro i hi
          apply Continuous.intervalIntegrable
          fun_prop
    have hpoint (t : ℝ) :
        ∑ i ∈ range N, w i * ‖inner ℂ (f i) ((F t) (e i))‖ ≤
          ∑ i ∈ range N, w i * singVal C i := by
      calc
        _ ≤ ∑ i ∈ range N, w i * singVal (F t) i :=
          weighted_singular_pairing_le (hFcpt t) hf hforth he heorth w N hw hwanti
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hsv t i) (hw i (Finset.mem_range.mp hi))
    have hIntegralBound :
        (∫ t : ℝ in 0..1,
          ∑ i ∈ range N, w i * ‖inner ℂ (f i) ((F t) (e i))‖) ≤
            ∑ i ∈ range N, w i * singVal C i := by
      calc
        _ ≤ ∫ _t : ℝ in 0..1, ∑ i ∈ range N, w i * singVal C i := by
          apply intervalIntegral.integral_mono (by norm_num)
          · apply Continuous.intervalIntegrable
            fun_prop
          · exact intervalIntegrable_const
          · exact hpoint
        _ = _ := by simp
    have hholder := finite_holder_two_one (fun i => singVal K i)
      (fun i => singVal C i) N (singVal_nonneg K) (singVal_nonneg C)
    have hmain :
        (∑ i ∈ range N, singVal K i ^ 3) ≤
          (∑ i ∈ range N, singVal K i ^ 3) ^ (2 / 3 : ℝ) *
            (∑ i ∈ range N, singVal C i ^ 3) ^ (1 / 3 : ℝ) := by
      calc
        _ = ∑ i ∈ range N, w i * ‖inner ℂ (f i) (K (e i))‖ := hdiag
        _ ≤ ∫ t : ℝ in 0..1,
            ∑ i ∈ range N, w i * ‖inner ℂ (f i) ((F t) (e i))‖ := htoIntegral
        _ ≤ ∑ i ∈ range N, w i * singVal C i := hIntegralBound
        _ ≤ _ := hholder
    set S : ℝ := ∑ i ∈ range N, singVal K i ^ 3 with hS
    set D : ℝ := (∑ i ∈ range N, singVal C i ^ 3) ^ (1 / 3 : ℝ) with hD
    have hS0 : 0 ≤ S := by
      rw [hS]
      exact Finset.sum_nonneg fun i hi => pow_nonneg (singVal_nonneg K i) 3
    rcases eq_or_lt_of_le hS0 with hSz | hSpos
    · have hD0 : 0 ≤ D := by
        rw [hD]
        exact Real.rpow_nonneg
          (Finset.sum_nonneg fun i hi => pow_nonneg (singVal_nonneg C i) 3) _
      rw [← hSz]
      simpa only [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using hD0
    ·
      have hden : 0 < S ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hSpos _
      have hdiv : S / S ^ (2 / 3 : ℝ) ≤ D := (div_le_iff₀ hden).2 (by
        simpa [hS, hD, mul_comm] using hmain)
      have hid : S / S ^ (2 / 3 : ℝ) = S ^ (1 / 3 : ℝ) := by
        calc
          S / S ^ (2 / 3 : ℝ) = S ^ (1 : ℝ) / S ^ (2 / 3 : ℝ) := by
            rw [Real.rpow_one]
          _ = S ^ ((1 : ℝ) - 2 / 3) := (Real.rpow_sub hSpos 1 (2 / 3)).symm
          _ = S ^ (1 / 3 : ℝ) := by norm_num
      rw [hid] at hdiv
      simpa only [hS, hD] using hdiv
  have hCraw : Summable fun n => approxNumber C n ^ 3 := by
    have h := hC
    unfold RHTower.MemSchattenClass at h
    convert h using 1
    funext n
    exact (Real.rpow_natCast (approxNumber C n) 3).symm
  have hpartial : ∀ N : ℕ,
      ∑ i ∈ range N, approxNumber K i ^ 3 ≤ schattenNorm 3 C ^ 3 := by
    intro N
    have hroot := hfinite N
    have hKs (i : ℕ) : singVal K i = approxNumber K i :=
      (approxNumber_eq_singVal hKcpt i).symm
    have hCs (i : ℕ) : singVal C i = approxNumber C i :=
      (approxNumber_eq_singVal hCcpt i).symm
    simp_rw [hKs, hCs] at hroot
    have hCpart : (∑ i ∈ range N, approxNumber C i ^ 3) ^ (1 / 3 : ℝ) ≤
        schattenNorm 3 C := by
      unfold schattenNorm
      rw [tsum_congr fun n => rpow_three_eq_cube (approxNumber C n)]
      apply Real.rpow_le_rpow
        (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg C i) 3)
      · exact hCraw.sum_le_tsum (range N)
          (fun i hi => pow_nonneg (approxNumber_nonneg C i) 3)
      · norm_num
    have hrootC := hroot.trans hCpart
    have hcubed := pow_le_pow_left₀
      (Real.rpow_nonneg
        (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg K i) 3) _)
      hrootC 3
    have hrootCube :
        ((∑ i ∈ range N, approxNumber K i ^ 3) ^ (1 / 3 : ℝ)) ^ 3 =
          ∑ i ∈ range N, approxNumber K i ^ 3 := by
      convert Real.rpow_inv_natCast_pow
        (Finset.sum_nonneg fun i hi => pow_nonneg (approxNumber_nonneg K i) 3)
        (by norm_num : (3 : ℕ) ≠ 0) using 1 <;> norm_num
    rw [hrootCube] at hcubed
    exact hcubed
  have htotal : (∑' n, approxNumber K n ^ 3) ≤ schattenNorm 3 C ^ 3 :=
    Real.tsum_le_of_sum_range_le (fun n => pow_nonneg (approxNumber_nonneg K n) 3) hpartial
  have hpow := Real.rpow_le_rpow
    (tsum_nonneg fun n => pow_nonneg (approxNumber_nonneg K n) 3)
    htotal (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hC0 : 0 ≤ schattenNorm 3 C := schattenNorm_nonneg 3 C
  have hCrpow : (schattenNorm 3 C ^ 3) ^ (1 / 3 : ℝ) = schattenNorm 3 C := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC0]
    norm_num
  rw [hCrpow] at hpow
  unfold schattenNorm
  rw [tsum_congr fun n => rpow_three_eq_cube
    (approxNumber (∫ t : ℝ in 0..1, F t) n)]
  simpa only [K, schattenNorm, rpow_three_eq_cube] using hpow

end

end GaloisForLFunctions.HTGeometry
