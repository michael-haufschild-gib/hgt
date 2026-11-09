import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveExtrapolation

/-!
# Simultaneous bounds for integer forms in prime logarithms

For a rank-`r` family in `k` prime logarithms, the collective auxiliary gives
an explicit lower bound for the largest original form. The exponent uses
`h=floor((k-r)/r)+1`, through the collective parameter choice; coefficient
height enters only through the logarithm of the pivot determinant and an
explicit adjugate factor.

Analytic majorants use `Q=kq`. Integer Siegel and terminal interpolation
retain the actual box `q`, so extrapolation preserves the rank gain.
All stage thresholds are derived from the explicit collective parameters.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Finset Real
open RHTower.Matveev
variable {m d Wb : ℕ}

/-- Enlarged box used only in analytic majorants. -/
abbrev CollectiveFeldmanParams.analyticBox (P : CollectiveFeldmanParams (m + 1) d Wb) : ℕ :=
  (m + 1) * P.q

theorem CollectiveFeldmanParams.one_le_analyticBox (P : CollectiveFeldmanParams (m + 1) d Wb) :
    1 ≤ P.analyticBox :=
  Nat.one_le_iff_ne_zero.mpr (by have := P.one_le_q; unfold analyticBox; positivity)

/-- The exponent `C₀′` of the `Λ`-absorption. -/
def collectiveLambdaExponent (P : CollectiveFeldmanParams (m + 1) d Wb) : ℝ :=
  (m + 1) * P.S * (1 + 2 * P.analyticBox) + 4 * P.a + 2 * (m + 1) * P.analyticBox +
    P.c * (1 + P.analyticBox * Wb) + 2 * (P.a + 1) * (19 + 12 * P.R) +
    (2 ^ P.R * P.c) * (18 + 8 * P.analyticBox * Wb + 16 * P.analyticBox + 10 * P.M ^ 2) +
    5 + P.M * (P.S + Wb + 1)

theorem collectiveLambdaExponent_nonneg (P : CollectiveFeldmanParams (m + 1) d Wb) : 0 ≤ collectiveLambdaExponent P := by
  unfold collectiveLambdaExponent; positivity

/-- The stage order `T_r = S − rM` is at least one. -/
theorem collective_one_le_stageOrder (P : CollectiveFeldmanParams (m + 1) d Wb) {r : ℕ} (hr : r < P.R) :
    1 ≤ P.S - r * P.M := by
  have h := Nat.mul_le_mul_right P.M (show r ≤ P.R by omega)
  rw [P.S_eq]; omega

/-- **The growth term gains.** -/
theorem collective_growth_gain (P : CollectiveFeldmanParams (m + 1) d Wb) {n : ℕ} (r : ℕ) (hn : 1 ≤ n)
    {B W Wt : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (hW : W ≤ Wb)
    (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb) :
    B ^ (P.S - r * P.M) * ((2 / 7 : ℝ) ^ (P.M * (2 ^ r * (P.c * n))) *
      feldmanGrowthFactor m (P.a * n) P.analyticBox P.S (P.S - r * P.M)
        (feldmanCoeffMajorant m (P.a * n) P.analyticBox P.S (P.c * n) B Wt) W
        (8 * ((2 ^ r * (P.c * n) : ℕ) : ℝ))) ≤ 1 / 2 := by
  set T := P.S - r * P.M with hT
  set N := P.a * n with hN
  set X := 2 ^ r * (P.c * n) with hX
  set κ := feldmanKappa P.S with hκ
  set A := feldmanCoeffMajorant m N P.analyticBox P.S (P.c * n) B Wt with hA
  have hq1 : (1 : ℝ) ≤ P.analyticBox := by exact_mod_cast P.one_le_analyticBox
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTS : (T : ℝ) ≤ P.S := by exact_mod_cast Nat.sub_le _ _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hκle : κ ≤ 18 + 12 * P.R := feldmanKappa_le P.logS
  have hκ0 : 0 ≤ κ := feldmanKappa_nonneg _
  have hXr : (X : ℝ) = 2 ^ r * (P.c * n) := by rw [hX]; push_cast; ring
  have hNr : (N : ℝ) = P.a * n := by rw [hN]; push_cast; ring
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hc0 : (0 : ℝ) ≤ P.c := Nat.cast_nonneg _
  have hXc : (P.c : ℝ) * n ≤ X := by
    rw [hXr]
    exact le_mul_of_one_le_left (mul_nonneg hc0 (Nat.cast_nonneg n)) h2r
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  -- the factor bounds
  have hBT := pow_le_exp_mul_of_log_le hB hBn T
  have h27 := two_sevenths_pow_le (P.M * X)
  have hU := natCast_feldman_le_exp N P.analyticBox m
  have hAe : A ≤ Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) +
      (m * P.S : ℕ) * (2 * P.analyticBox + n) + (P.c * n : ℕ) * (P.analyticBox * Wt)) :=
    feldmanCoeffMajorant_le_exp hB hBn
  have h2N := two_pow_le_exp N
  have h2qT : (2 * P.analyticBox : ℝ) ^ T ≤ Real.exp (T * (2 * P.analyticBox)) :=
    pow_le_exp_of_le (by positivity) (le_exp_self' _) T
  have hA0 : 0 ≤ A := le_trans zero_le_one (feldmanCoeffMajorant_one_le hB P.one_le_analyticBox hWt0)
  have hprod : B ^ T * ((2 / 7 : ℝ) ^ (P.M * X) *
      feldmanGrowthFactor m N P.analyticBox P.S T A W (8 * (X : ℝ))) ≤
      Real.exp (T * n) * (Real.exp (-((P.M * X : ℕ) : ℝ)) *
        (Real.exp (N + (m + 1) * P.analyticBox) * (Real.exp (N + (m + 1) * P.analyticBox) *
          Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) + (m * P.S : ℕ) * (2 * P.analyticBox + n) +
            (P.c * n : ℕ) * (P.analyticBox * Wt))) * Real.exp N *
          Real.exp (8 * (X : ℝ) + (N + 1) * (1 + κ)) * Real.exp (T * (2 * P.analyticBox)) *
          Real.exp (8 * (X : ℝ) * (2 * P.analyticBox * W)))) := by
    unfold feldmanGrowthFactor
    rw [← hκ]
    gcongr
  refine hprod.trans ?_
  simp only [← Real.exp_add]
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  refine le_trans (Real.exp_le_exp.mpr ?_) hhalf
  have hE := feldman_growth_exponent_le (n := n) (T := T) (S := P.S) (N := N) (X := X)
    (κ := κ) (M := P.M) (c := P.c) (a := P.a) (q := P.analyticBox) (m := m) (R := P.R) (Wb := Wb) (W := W)
    (Wt := Wt) hn1 hTS hNr (Nat.cast_nonneg _) hXc hc0 hκle (Nat.cast_nonneg _)
    (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hW hWt0 hWt (Nat.cast_nonneg _)
    (by exact_mod_cast P.M_ge) (by exact_mod_cast P.gain)
  refine le_trans (le_of_eq ?_) hE
  push_cast
  ring

/-- **The `Λ` term is `e^{O(n)}`.** -/
theorem collective_error_gain (P : CollectiveFeldmanParams (m + 1) d Wb) {n r : ℕ} (hn : 1 ≤ n) (hr : r < P.R)
    {B W Wt : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (hW0 : 0 ≤ W) (hW : W ≤ Wb)
    (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb) :
    B ^ (P.S - r * P.M) *
      (feldmanErrorFactor m (P.a * n) P.analyticBox P.S (P.S - r * P.M)
          (feldmanCoeffMajorant m (P.a * n) P.analyticBox P.S (P.c * n) B Wt) Wt
          (8 * ((2 ^ r * (P.c * n) : ℕ) : ℝ)) *
        feldmanHermiteFactor (2 ^ r * (P.c * n)) P.M (P.S - r * P.M) W
          (8 * ((2 ^ r * (P.c * n) : ℕ) : ℝ))) ≤
      Real.exp (collectiveLambdaExponent P * n) := by
  set T := P.S - r * P.M with hT
  set N := P.a * n with hN
  set X := 2 ^ r * (P.c * n) with hX
  set κ := feldmanKappa P.S with hκ
  set A := feldmanCoeffMajorant m N P.analyticBox P.S (P.c * n) B Wt with hA
  have hq1 : (1 : ℝ) ≤ P.analyticBox := by exact_mod_cast P.one_le_analyticBox
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTS : (T : ℝ) ≤ P.S := by exact_mod_cast Nat.sub_le _ _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hκle : κ ≤ 18 + 12 * P.R := feldmanKappa_le P.logS
  have hκ0 : 0 ≤ κ := feldmanKappa_nonneg _
  have hNr : (N : ℝ) = P.a * n := by rw [hN]; push_cast; ring
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hXle : (X : ℝ) ≤ (2 ^ P.R * P.c) * n := by
    have h : X ≤ 2 ^ P.R * P.c * n := by
      rw [hX, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) hr.le))
    exact_mod_cast h
  have hBT := pow_le_exp_mul_of_log_le hB hBn T
  have hU := natCast_feldman_le_exp N P.analyticBox m
  have hAe : A ≤ Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) +
      (m * P.S : ℕ) * (2 * P.analyticBox + n) + (P.c * n : ℕ) * (P.analyticBox * Wt)) :=
    feldmanCoeffMajorant_le_exp hB hBn
  have h2N := two_pow_le_exp N
  have h2qT : (2 * P.analyticBox : ℝ) ^ T ≤ Real.exp (T * (2 * P.analyticBox)) :=
    pow_le_exp_of_le (by positivity) (le_exp_self' _) T
  have hA0 : 0 ≤ A := le_trans zero_le_one (feldmanCoeffMajorant_one_le hB P.one_le_analyticBox hWt0)
  have h2ρq : 2 * (8 * (X : ℝ) * P.analyticBox) ≤ Real.exp (2 * (8 * (X : ℝ) * P.analyticBox)) := le_exp_self' _
  have h5 : (5 : ℝ) ≤ Real.exp 5 := le_exp_self' 5
  have hXe : (X : ℝ) ≤ Real.exp X := le_exp_self' _
  have hTW : ((T : ℝ) + W) ^ P.M ≤ Real.exp (P.M * ((T : ℝ) + W)) :=
    pow_le_exp_of_le (by positivity) (le_exp_self' _) P.M
  have h2M := two_pow_le_exp P.M
  have h2X : ((2 : ℝ) ^ X * Real.exp (8 * (X : ℝ) + X)) ^ (P.M * P.M) ≤
      Real.exp ((P.M * P.M : ℕ) * (X + (8 * (X : ℝ) + X))) := by
    refine pow_le_exp_of_le (by positivity) ?_ _
    calc (2 : ℝ) ^ X * Real.exp (8 * (X : ℝ) + X) ≤ Real.exp X * Real.exp (8 * (X : ℝ) + X) :=
          mul_le_mul_of_nonneg_right (two_pow_le_exp X) (Real.exp_pos _).le
      _ = Real.exp (X + (8 * (X : ℝ) + X)) := by rw [← Real.exp_add]
  have hprod : B ^ T * (feldmanErrorFactor m N P.analyticBox P.S T A Wt (8 * (X : ℝ)) *
      feldmanHermiteFactor X P.M T W (8 * (X : ℝ))) ≤
      Real.exp (T * n) * ((Real.exp (N + (m + 1) * P.analyticBox) * (Real.exp (N + (m + 1) * P.analyticBox) *
          Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) + (m * P.S : ℕ) * (2 * P.analyticBox + n) +
            (P.c * n : ℕ) * (P.analyticBox * Wt))) * Real.exp N *
          Real.exp (8 * (X : ℝ) + (N + 1) * (1 + κ)) * Real.exp (T * (2 * P.analyticBox)) *
          Real.exp (8 * (X : ℝ) * (P.analyticBox * Wt)) * Real.exp (2 * (8 * (X : ℝ) * P.analyticBox))) *
        (Real.exp 5 * (Real.exp X * (Real.exp (P.M * ((T : ℝ) + W)) *
          (Real.exp (8 * (X : ℝ) + X) * (Real.exp P.M *
            Real.exp ((P.M * P.M : ℕ) * (X + (8 * (X : ℝ) + X))))))))) := by
    unfold feldmanErrorFactor feldmanHermiteFactor
    rw [← hκ]
    gcongr
  refine hprod.trans ?_
  simp only [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hE := feldman_error_exponent_le (n := n) (T := T) (S := P.S) (N := N) (X := X) (κ := κ)
    (M := P.M) (c := P.c) (a := P.a) (q := P.analyticBox) (m := m) (R := P.R) (Wb := Wb) (W := W) (Wt := Wt)
    (Xc := 2 ^ P.R * P.c) hn1 hT0 hTS hNr (Nat.cast_nonneg _) hX0 hXle (Nat.cast_nonneg _) hκle
    (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hW0 hW hWt0 hWt
    (Nat.cast_nonneg _)
  unfold collectiveLambdaExponent
  convert hE using 1 <;> push_cast <;> ring

/-- **Every stage clears its arithmetic threshold.** -/
theorem collective_stage_threshold (P : CollectiveFeldmanParams (m + 1) d Wb) {n r : ℕ} (hn : 1 ≤ n) (hr : r < P.R)
    {B W Wt lam : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (hW0 : 0 ≤ W) (hW : W ≤ Wb)
    (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb)
    (hlam : |lam| < Real.exp (-((collectiveLambdaExponent P + 1) * n))) :
    B ^ (P.S - r * P.M) * feldmanStepBound m (P.a * n) P.analyticBox (P.S - r * P.M) (2 ^ r * (P.c * n))
      P.M (feldmanCmax m (P.a * n) P.analyticBox P.S (P.c * n) B Wt) W Wt lam <
      feldmanDivisor (P.a * n + 1) P.S := by
  set T := P.S - r * P.M with hT
  set N := P.a * n with hN
  set X := 2 ^ r * (P.c * n) with hX
  set D : ℝ := ((feldmanDivisor (N + 1) P.S : ℕ) : ℝ) with hD
  set Cm := feldmanCmax m N P.analyticBox P.S (P.c * n) B Wt with hCmdef
  set A := feldmanCoeffMajorant m N P.analyticBox P.S (P.c * n) B Wt with hA
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast feldmanDivisor_pos _ _
  have hCm0 : 0 ≤ Cm := feldmanCmax_nonneg
  have hCm : Cm ≤ ((N + 1) * P.analyticBox ^ (m + 1) : ℕ) * A := feldmanCmax_le hB P.one_le_analyticBox hWt0
  have hX1 : 1 ≤ X := by
    rw [hX]; exact Nat.one_le_iff_ne_zero.mpr (by
      have := P.one_le_c; positivity)
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast collective_one_le_stageOrder P hr
  have hTW : (1 : ℝ) ≤ (T : ℝ) + W := by linarith
  have hstep := feldmanStepBound_le (m := m) (N := N) (q := P.analyticBox) (T := T) (X := X) (M := P.M)
    (W := W) (Wt := Wt) (lam := lam) hCm0 hX1 hTW
  have hρ : (0 : ℝ) ≤ 8 * (X : ℝ) := by positivity
  have hG := feldmanGrowthBound_le (S := P.S) (W := W) hCm0 hCm hρ (T := T)
  have hβ := feldmanErrorBound_le (S := P.S) (Wt := Wt) (lam := lam) hCm0 hCm hρ (T := T)
  have hgrowth := collective_growth_gain P r hn hB hBn hW hWt0 hWt
  have herror := collective_error_gain P hn hr hB hBn hW0 hW hWt0 hWt
  rw [← hT, ← hN, ← hX] at hgrowth herror
  rw [← hA] at hgrowth herror
  set Γ := feldmanGrowthFactor m N P.analyticBox P.S T A W (8 * (X : ℝ)) with hΓ
  set E := feldmanErrorFactor m N P.analyticBox P.S T A Wt (8 * (X : ℝ)) with hE
  set H := feldmanHermiteFactor X P.M T W (8 * (X : ℝ)) with hH
  have hH0 : 0 ≤ H := by
    rw [hH]; unfold feldmanHermiteFactor
    have : (0 : ℝ) ≤ (T : ℝ) + W := by linarith
    positivity
  have hB0 : (0 : ℝ) ≤ B ^ T := by positivity
  have h270 : (0 : ℝ) ≤ (2 / 7 : ℝ) ^ (P.M * X) := by positivity
  have hlamexp : |lam| * Real.exp (collectiveLambdaExponent P * n) < 1 / 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc |lam| * Real.exp (collectiveLambdaExponent P * n)
        < Real.exp (-((collectiveLambdaExponent P + 1) * n)) *
            Real.exp (collectiveLambdaExponent P * n) :=
          mul_lt_mul_of_pos_right hlam (Real.exp_pos _)
      _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith [Real.exp_one_gt_d9]
  have hlam0 : 0 ≤ |lam| := abs_nonneg _
  calc B ^ T * feldmanStepBound m N P.analyticBox T X P.M Cm W Wt lam
      ≤ B ^ T * ((2 / 7 : ℝ) ^ (P.M * X) * (D * Γ) + |lam| * (D * E) * H) := by
        refine mul_le_mul_of_nonneg_left (hstep.trans ?_) hB0
        gcongr
    _ = D * (B ^ T * ((2 / 7 : ℝ) ^ (P.M * X) * Γ)) + D * |lam| * (B ^ T * (E * H)) := by ring
    _ ≤ D * (1 / 2) + D * |lam| * Real.exp (collectiveLambdaExponent P * n) := by
        gcongr
    _ < D * (1 / 2) + D * (1 / 2) := by
        have : D * |lam| * Real.exp (collectiveLambdaExponent P * n) =
            D * (|lam| * Real.exp (collectiveLambdaExponent P * n)) := by ring
        rw [this]
        gcongr
    _ = D := by ring


/-- The enlargement `Q=kq` dominates every collective coefficient height. -/
theorem collectiveJetHeight_le_feldmanCoeffBound {r N q Q S X : ℕ}
    (hrQ : (r + 1) * q ≤ 2 * Q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hd : d ≤ m)
    {D W : ℝ} (hD : 1 ≤ |D|) (hW : 0 ≤ W) :
    collectiveJetHeight r d N q S X D W ≤ feldmanCoeffBound m N Q S X |D| W := by
  have hrQR : (r + 1 : ℝ) * q ≤ 2 * Q := by exact_mod_cast hrQ
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hbase : (1 : ℝ) ≤ 2 * Q * |D| := by nlinarith only [hQ1, hD]
  have hpw : ((r + 1 : ℝ) * q * |D|) ^ (d * S) ≤ (2 * Q * |D|) ^ (m * S) :=
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hrQR (abs_nonneg D)) _).trans
      (pow_le_pow_right₀ hbase (Nat.mul_le_mul_right S hd))
  unfold collectiveJetHeight feldmanCoeffBound
  gcongr

theorem sixteen_mul_le_collectiveLambdaExponent (P : CollectiveFeldmanParams (m + 1) d Wb) :
    16 * ((2 : ℝ) ^ P.R * P.c) * P.analyticBox ≤ collectiveLambdaExponent P := by
  have h : 0 ≤ collectiveLambdaExponent P - 16 * ((2 : ℝ) ^ P.R * P.c) * P.analyticBox := by
    unfold collectiveLambdaExponent
    ring_nf
    positivity
  linarith only [h]

/-- The full collective extrapolation yields a lower bound for the
pivot-normalized forms. Its parameters retain the free-direction Siegel count. -/
theorem collective_pivot_bound_of_params (P : CollectiveFeldmanParams (m + 1) d Wb)
    {r : ℕ} (p : Fin (m + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hW : totalLogSum p ≤ Wb)
    (A : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (e : Fin d → Fin (m + 1)) (he : Function.Injective e)
    (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (hr : r ≤ m + 1) (hd : d ≤ m) :
    exp (-((collectiveLambdaExponent P + 1) * (log |((A.submatrix id s).det : ℝ)| + 2))) ≤
      collectiveFormDefect p A s := by
  have hp1 : ∀ j, 1 ≤ p j := fun j => (hprime j).one_lt.le
  set B : ℝ := |((A.submatrix id s).det : ℝ)| with hBdef
  have hB1 : 1 ≤ B := by
    have h := abs_pos.mpr hdet
    have h1 : (1 : ℤ) ≤ |(A.submatrix id s).det| := by omega
    change 1 ≤ |((A.submatrix id s).det : ℝ)|
    exact_mod_cast h1
  have hlogB : 0 ≤ log B := log_nonneg hB1
  set n := ⌈log B⌉₊ + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hBn : log B ≤ n := by
    have := Nat.le_ceil (log B)
    rw [hn]; push_cast; linarith only [this]
  have hnB : (n : ℝ) ≤ log B + 2 := by
    have := Nat.ceil_lt_add_one hlogB
    rw [hn]; push_cast; linarith only [this]
  have hC₀ : 0 ≤ collectiveLambdaExponent P + 1 := by
    linarith only [collectiveLambdaExponent_nonneg P]
  by_contra hcontra
  push Not at hcontra
  set lam := collectiveFormDefect p A s with hlam
  have hlam0 : 0 ≤ lam := collectiveFormDefect_nonneg p A s
  have hlamn : lam < exp (-((collectiveLambdaExponent P + 1) * n)) :=
    hcontra.trans_le (exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hnB hC₀)))
  set N := P.a * n with hN
  set X₀ := P.c * n with hX₀
  have hqQ : P.q ≤ P.analyticBox := by
    unfold CollectiveFeldmanParams.analyticBox
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)
  have hrQ : (r + 1) * P.q ≤ 2 * P.analyticBox := by
    change (r + 1) * P.q ≤ 2 * ((m + 1) * P.q)
    have h := Nat.mul_le_mul_right P.q (show r + 1 ≤ 2 * (m + 1) by omega)
    simpa only [mul_assoc] using h
  have hX₀1 : 1 ≤ X₀ := Nat.mul_pos P.one_le_c hn1
  have hS : 0 < P.S := by rw [P.S_eq]; omega
  have ha1 : 1 ≤ P.a := by
    by_contra h
    have h0 : P.a = 0 := by omega
    have hc := P.siegel
    rw [h0, zero_mul] at hc
    have hpos : 0 < 2 * P.c * P.S ^ (d + 1) := by have := P.one_le_c; positivity
    omega
  have hWt0 := totalLogSum_nonneg p hp1
  have hW0 := collectiveFreeLogSum_nonneg p e hp1
  have hWfree := (collectiveFreeLogSum_le_total p e hp1 he).trans hW
  obtain ⟨C, hC0, hCvan, hCb⟩ := exists_collective_jet_kernel p hp1 A s e hdet hmax
    P.one_le_q hX₀1 hS (collectiveFeldmanParams_jet_count P (n := n))
  have hCbound : ∀ kl, |(C kl : ℝ)| ≤ feldmanCmax m N P.analyticBox P.S X₀ B (totalLogSum p) := by
    intro kl
    refine (hCb kl).trans ?_
    have hb := collectiveJetHeight_le_feldmanCoeffBound (N := N) (S := P.S) (X := X₀)
      (D := ((A.submatrix id s).det : ℝ)) (W := totalLogSum p) hrQ hqQ P.one_le_analyticBox hd hB1 hWt0
    have hcard : (N + 1) * P.q ^ (m + 1) ≤ (N + 1) * P.analyticBox ^ (m + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqQ _)
    have hcardR : (((N + 1) * P.q ^ (m + 1) : ℕ) : ℝ) ≤
        ((N + 1) * P.analyticBox ^ (m + 1) : ℕ) := by exact_mod_cast hcard
    unfold feldmanCmax
    exact mul_le_mul hcardR (max_le_max le_rfl hb) (le_trans zero_le_one (le_max_left _ _))
      (Nat.cast_nonneg _)
  have h0 : ∀ x < X₀, ∀ σ (τ : Fin d → ℕ), σ + ∑ j, τ j < P.S →
      collectiveTrueAux p A s e N P.q C σ τ (x : ℂ) = 0 := by
    intro x hx σ τ hστ
    apply hCvan x hx σ (by omega) τ
    intro j
    have := single_le_sum (f := τ) (fun i _ => Nat.zero_le _) (mem_univ j)
    omega
  have hΛ : 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.analyticBox * lam ≤ 1 := by
    have hy : 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.analyticBox ≤ (collectiveLambdaExponent P + 1) * n := by
      have h16 := sixteen_mul_le_collectiveLambdaExponent P
      have hcast : ((2 ^ P.R * X₀ : ℕ) : ℝ) = (2 : ℝ) ^ P.R * P.c * n := by
        rw [hX₀]; push_cast; ring
      rw [hcast]
      have hpos : (0 : ℝ) ≤ 8 * ((2 : ℝ) ^ P.R * P.c) * P.analyticBox := by positivity
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith only [mul_le_mul_of_nonneg_right h16 hn0, mul_nonneg hpos hn0, hn0]
    calc 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.analyticBox * lam
        ≤ exp ((collectiveLambdaExponent P + 1) * n) * exp (-((collectiveLambdaExponent P + 1) * n)) :=
          mul_le_mul (hy.trans (le_exp_self' _)) hlamn.le hlam0 (exp_pos _).le
      _ = 1 := by rw [← exp_add]; simp only [add_neg_cancel, exp_zero]
  have hext := collective_extrapolation p A s e hp1 hdet hmax he hcover P.one_le_q hqQ hrQ C
    hCbound feldmanCmax_nonneg (X₀ := X₀) (T₀ := P.S) (M := P.M) (R := P.R)
    hX₀1 le_rfl (by rw [P.S_eq]; omega) hΛ h0
    (fun t ht => collective_stage_threshold P hn1 ht hB1 hBn hW0 hWfree hWt0 hW
      (by change |lam| < _; simpa only [abs_of_nonneg hlam0] using hlamn))
  have hterm : (N + 1) * P.q ^ (m + 1) ≤ 2 ^ P.R * X₀ := by
    have h := Nat.mul_le_mul_right n P.terminal
    have hN1 : 1 ≤ N := Nat.mul_pos ha1 hn1
    calc (N + 1) * P.q ^ (m + 1) ≤ 2 * N * P.q ^ (m + 1) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 * P.a * P.q ^ (m + 1) * n := by rw [hN]; ring
      _ ≤ 2 ^ P.R * P.c * n := h
      _ = 2 ^ P.R * X₀ := by rw [hX₀]; ring
  obtain ⟨x, hx, hne⟩ := exists_collectiveTrueAux_ne_zero p hp hprime A s e C hC0
  exact hne (hext x (hx.trans_le hterm) 0 0 (by rw [P.S_eq]; simp))


/-- Determinant and normalized-form bounds for a coefficient box. -/
theorem collectiveFormDefect_height_bounds {n m : ℕ}
    (p : Fin (m + 1) → ℕ) (A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℤ)
    (s : Fin (n + 1) → Fin (m + 1)) (hdet : (A.submatrix id s).det ≠ 0)
    {H ε : ℝ} (hH : 1 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H)
    (hε : ∀ i, |∑ j, (A i j : ℝ) * log (p j)| ≤ ε) :
    |((A.submatrix id s).det : ℝ)| ≤ ((n + 1).factorial : ℝ) * H ^ (n + 1) ∧
      collectiveFormDefect p A s ≤
        (n + 1 : ℝ) * ((n + 1).factorial : ℝ) * H ^ n * ε := by
  have hdetB : |((A.submatrix id s).det : ℝ)| ≤ ((n + 1).factorial : ℝ) * H ^ (n + 1) := by
    have h := Matrix.det_le
      (A := (Int.castRingHom ℝ).mapMatrix (A.submatrix id s))
      (abv := AbsoluteValue.abs) (fun i j => hA i (s j))
    rw [← (Int.castRingHom ℝ).map_det] at h
    simp only [Fintype.card_fin, nsmul_eq_mul] at h
    change |((A.submatrix id s).det : ℝ)| ≤ ((n + 1).factorial : ℝ) * H ^ (n + 1) at h
    exact h
  refine ⟨hdetB, ?_⟩
  have hD1 : (1 : ℝ) ≤ |((A.submatrix id s).det : ℝ)| := by
    have h := abs_pos.mpr hdet
    have : (1 : ℤ) ≤ |(A.submatrix id s).det| := by omega
    exact_mod_cast this
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0)
  have hadj (i j : Fin (n + 1)) :
      |((A.submatrix id s).adjugate i j : ℝ)| ≤ (n.factorial : ℝ) * H ^ n := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have h := Matrix.det_le
      (A := (Int.castRingHom ℝ).mapMatrix ((A.submatrix id s).submatrix j.succAbove i.succAbove))
      (abv := AbsoluteValue.abs) (fun a b => hA _ _)
    rw [← (Int.castRingHom ℝ).map_det] at h
    simp only [Fintype.card_fin, nsmul_eq_mul] at h
    change |(((A.submatrix id s).submatrix j.succAbove i.succAbove).det : ℝ)| ≤
      (n.factorial : ℝ) * H ^ n at h
    exact h
  have hterm (i : Fin (n + 1)) :
      |(∑ a, ((A.submatrix id s).adjugate i a : ℝ) *
          (∑ j, (A a j : ℝ) * log (p j))) / ((A.submatrix id s).det : ℝ)| ≤
        ((n + 1).factorial : ℝ) * H ^ n * ε := by
    rw [abs_div]
    calc _ ≤ |∑ a, ((A.submatrix id s).adjugate i a : ℝ) *
          (∑ j, (A a j : ℝ) * log (p j))| := div_le_self (abs_nonneg _) hD1
      _ ≤ ∑ a, |((A.submatrix id s).adjugate i a : ℝ) *
          (∑ j, (A a j : ℝ) * log (p j))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin (n + 1), (n.factorial : ℝ) * H ^ n * ε := by
        apply sum_le_sum
        intro a ha
        rw [abs_mul]
        exact mul_le_mul (hadj i a) (hε a) (abs_nonneg _) (by positivity)
      _ = ((n + 1).factorial : ℝ) * H ^ n * ε := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
  unfold collectiveFormDefect
  calc _ ≤ ∑ _i : Fin (n + 1), ((n + 1).factorial : ℝ) * H ^ n * ε :=
        sum_le_sum fun i _ => hterm i
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

/-- A lower bound for an original integer form, retaining collective parameters. -/
theorem collective_forms_bound_of_params (P : CollectiveFeldmanParams (m + 1) d Wb)
    {n : ℕ} (p : Fin (m + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hW : totalLogSum p ≤ Wb)
    (A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℤ) (s : Fin (n + 1) → Fin (m + 1))
    (e : Fin d → Fin (m + 1)) (he : Function.Injective e)
    (hcover : ∀ j, (∃ i, s i = j) ∨ ∃ i, e i = j)
    (hdet : (A.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(A.submatrix id s).cramer (fun h => A h j) i| ≤ |(A.submatrix id s).det|)
    (hn : n ≤ m) (hd : d ≤ m) {H : ℝ} (hH : 1 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    ∃ i, exp (-((collectiveLambdaExponent P + 1) *
      (log (((n + 1).factorial : ℝ) * H ^ (n + 1)) + 2))) /
        ((n + 1 : ℝ) * ((n + 1).factorial : ℝ) * H ^ n) ≤
          |∑ j, (A i j : ℝ) * log (p j)| := by
  classical
  obtain ⟨i, hi, htop⟩ := Finset.exists_max_image univ
    (fun i => |∑ j, (A i j : ℝ) * log (p j)|)
    (show (univ : Finset (Fin (n + 1))).Nonempty from ⟨0, mem_univ _⟩)
  have hrows := fun j => htop j (mem_univ j)
  obtain ⟨hD, hlamBound⟩ := collectiveFormDefect_height_bounds p A s hdet hH hA hrows
  have hD0 : 0 < |((A.submatrix id s).det : ℝ)| := abs_pos.mpr (by exact_mod_cast hdet)
  have hC0 : 0 ≤ collectiveLambdaExponent P + 1 := by
    linarith only [collectiveLambdaExponent_nonneg P]
  have hpivot := collective_pivot_bound_of_params P p hp hprime hW A s e he hcover hdet hmax
    (by omega) hd
  have hsmall : exp (-((collectiveLambdaExponent P + 1) *
      (log (((n + 1).factorial : ℝ) * H ^ (n + 1)) + 2))) ≤ collectiveFormDefect p A s := by
    refine le_trans (exp_le_exp.mpr ?_) hpivot
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      (by linarith only [log_le_log hD0 hD]) hC0)
  refine ⟨i, (div_le_iff₀ (by positivity)).mpr ?_⟩
  simpa only [mul_comm] using hsmall.trans hlamBound

/-- Simultaneous prime-logarithm bound with explicit collective parameters.
The parameter choice depends on rank, dimension and prime mass, uniformly
in the height of the independent integer forms. -/
theorem exists_explicit_collective_logarithm_bound (d r : ℕ)
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (A : Matrix (Fin (r + 1)) (Fin (d + r + 1)) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (A i j : ℚ))) :
    ∃ P : CollectiveFeldmanParams (d + r + 1) d (collectiveLogBound p),
      P.R = collectiveSteps (d + r + 1) (collectiveRootDegree d (r + 1)) (collectiveLogBound p) ∧
      P.q = (1000 * collectiveLogBound p * (d + r + 1) * (P.R + 1)) ^
        collectiveRootDegree d (r + 1) * (P.R + 1) ∧
      P.M = 1000 * collectiveLogBound p * ((d + r + 1) * P.q) ∧
      P.c = 16 * (d + r + 1) * (P.R + 1) * ((d + r + 1) * P.q) ∧
      P.a = 2 * P.c * (1000 * collectiveLogBound p * (d + r + 1) * (P.R + 1)) ^
        collectiveRootDegree d (r + 1) ∧
      ∀ H : ℝ, 1 ≤ H → (∀ i j, |(A i j : ℝ)| ≤ H) →
        ∃ i, exp (-((collectiveLambdaExponent P + 1) *
          (log (((r + 1).factorial : ℝ) * H ^ (r + 1)) + 2))) /
            ((r + 1 : ℝ) * ((r + 1).factorial : ℝ) * H ^ r) ≤
              |∑ j, (A i j : ℝ) * log (p j)| := by
  obtain ⟨P, s, e, hPR, hPq, hPM, hPc, hPa, hs, he, hse, hcover, hdet, hmax, haux⟩ :=
    exists_collective_auxiliary d r p hp hprime A hind
  refine ⟨P, hPR, hPq, hPM, hPc, hPa, ?_⟩
  intro H hH hA
  exact collective_forms_bound_of_params P p hp hprime (totalLogSum_le_collectiveLogBound p)
    A s e he hcover hdet hmax (by omega) (by omega) hH hA


end GaloisForLFunctions.CollectiveDiophantineGeometry
