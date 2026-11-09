import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveLogarithmBound
import GaloisForLFunctions.CollectiveDiophantineGeometry.CollectiveRankDepth

/-!
# Reciprocal-rank bounds for prime-logarithm approximation

For `r` independent forms in `k` prime logarithms, the explicit exponent
is bounded by `U^(100h(k+1))`, where `h=floor((k-r)/r)+1` and
`U=10⁴(W+1)(k+1)²`. Its degree multiplied by rank is at most `100k(k+1)`.
At rank at least half the dimension the degree is linear in `k`.

The resulting depth floor is uniform over every coefficient matrix.
All integer near relations below it span at most `r-1` rational dimensions
and number at most `(2H+1)^(r-1)`. Taking the maximum with the earlier
scalar-elimination floor preserves its near-full-rank regimes.
-/

noncomputable section
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open Finset Real Matrix
open RHTower.Matveev TranscendenceTheoryOfThePrimeOrbit

/-- Base for bounds uniform in both the number of primes and the rank. -/
def collectiveBase (k W : ℕ) : ℕ := 10 ^ 4 * (W + 1) * (k + 1) ^ 2

private theorem collectiveBase_bounds (k W : ℕ) (hW : 1 ≤ W) :
    10000 ≤ collectiveBase k W ∧ (k + 1) ^ 2 ≤ collectiveBase k W ∧
      2000 * W * k + 3 ≤ collectiveBase k W ∧ 16 * k ≤ collectiveBase k W ∧
      W ≤ collectiveBase k W := by
  have hsq1 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsqk : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hprod1 : 1 ≤ (W + 1) * (k + 1) ^ 2 := Nat.mul_pos (Nat.succ_pos W) (Nat.pow_pos (Nat.succ_pos k))
  have hprodW := Nat.mul_le_mul_left (W + 1) hsq1
  have hprodK := Nat.mul_le_mul_left (W + 1) hsqk
  have hprodS : (k + 1) ^ 2 ≤ (W + 1) * (k + 1) ^ 2 :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold collectiveBase
  norm_num only [show (10 : ℕ) ^ 4 = 10000 by norm_num]
  constructor
  · nlinarith only [hprod1]
  constructor
  · nlinarith only [hprodS]
  constructor
  · nlinarith only [hprodK, Nat.zero_le (W * k), Nat.zero_le W, Nat.zero_le k]
  constructor
  · nlinarith only [hprodS, hsqk, Nat.zero_le k]
  · nlinarith only [hprodW, Nat.zero_le W]

/-- The logarithms in the explicit step length have polynomial-size arguments. -/
theorem collectiveStepL_add_degree_le {k h W : ℕ} (hk : 1 ≤ k)
    (hh : h ≤ k) (hW : 1 ≤ W) :
    collectiveStepL k h W + collectiveStepD k h + 1 ≤ collectiveBase k W ^ 2 := by
  obtain ⟨hU, hsq, hB, -, -⟩ := collectiveBase_bounds k W hW
  have hB1 : 1 ≤ 1000 * W * k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlog : Nat.log 2 (1000 * W * k) + 1 ≤ 1000 * W * k := log_two_lt_self (by omega)
  have hA : h * (k + 1) ≤ (k + 1) ^ 2 := by
    have hm := Nat.mul_le_mul_right (k + 1) hh
    nlinarith only [hm, Nat.zero_le k]
  have hL : collectiveStepL k h W + collectiveStepD k h + 1 ≤
      (1000 * W * k + 3) * (k + 1) ^ 2 := by
    have hp := Nat.mul_le_mul hA (show Nat.log 2 (1000 * W * k) + 2 ≤ 1000 * W * k + 1 by omega)
    unfold collectiveStepL collectiveStepD
    nlinarith only [hp, hk]
  calc _ ≤ (1000 * W * k + 3) * (k + 1) ^ 2 := hL
    _ ≤ collectiveBase k W * collectiveBase k W := Nat.mul_le_mul (by nlinarith only [hB, Nat.zero_le (W * k)]) hsq
    _ = collectiveBase k W ^ 2 := (pow_two _).symm

/-- The number of extrapolation steps is polynomial in the common base. -/
theorem collectiveSteps_add_one_le {k h W : ℕ} (hk : 1 ≤ k)
    (hh : h ≤ k) (hW : 1 ≤ W) : collectiveSteps k h W + 1 ≤ collectiveBase k W ^ 6 := by
  have hV := collectiveStepL_add_degree_le hk hh hW
  obtain ⟨hU, -, -, -, -⟩ := collectiveBase_bounds k W hW
  set U := collectiveBase k W
  set V := collectiveStepL k h W + collectiveStepD k h + 1
  have hlog : Nat.log 2 V + 1 ≤ V := log_two_lt_self (by dsimp [V]; omega)
  have hD : collectiveStepD k h ≤ V := by dsimp [V]; omega
  have hR : collectiveSteps k h W + 1 ≤ V + 2 * V ^ 2 := by
    have hm := Nat.mul_le_mul hD (show 2 * (Nat.log 2 V + 1) ≤ 2 * V by omega)
    unfold collectiveSteps
    change collectiveStepL k h W + collectiveStepD k h * (2 * (Nat.log 2 V + 1)) + 1 ≤ _
    have hL : collectiveStepL k h W + 1 ≤ V := by dsimp [V]; omega
    nlinarith only [hm, hL]
  have hU1 : 1 ≤ U := by omega
  have h24 : U ^ 2 ≤ U ^ 4 := Nat.pow_le_pow_right hU1 (by norm_num)
  have h3 : 3 ≤ U ^ 2 := by nlinarith only [hU]
  calc _ ≤ V + 2 * V ^ 2 := hR
    _ ≤ U ^ 2 + 2 * (U ^ 2) ^ 2 := by gcongr
    _ ≤ 3 * U ^ 4 := by nlinarith only [h24]
    _ ≤ U ^ 2 * U ^ 4 := Nat.mul_le_mul_right _ h3
    _ = U ^ 6 := by ring

/-- The exponential of the step length retains the root degree `h`. -/
theorem two_pow_collectiveSteps_le {k h W : ℕ} (hk : 1 ≤ k)
    (hh1 : 1 ≤ h) (hhk : h ≤ k) (hW : 1 ≤ W) :
    2 ^ collectiveSteps k h W ≤ collectiveBase k W ^ (19 * h * (k + 1)) := by
  obtain ⟨hU, -, hB, -, -⟩ := collectiveBase_bounds k W hW
  have hV := collectiveStepL_add_degree_le hk hhk hW
  set U := collectiveBase k W
  set L := collectiveStepL k h W
  set D := collectiveStepD k h
  set b := Nat.log 2 (L + D + 1) + 1
  have hU1 : 1 ≤ U := by omega
  have hpowB : 2 ^ (Nat.log 2 (1000 * W * k) + 1) ≤ U := by
    have h := Nat.pow_log_le_self 2 (show 1000 * W * k ≠ 0 by positivity)
    rw [pow_succ]
    nlinarith only [h, hB]
  have hpowL : 2 ^ L ≤ U ^ (1 + h * (k + 1)) := by
    have heq : 2 ^ L = 4 * (2 ^ (Nat.log 2 (1000 * W * k) + 1)) ^ (h * (k + 1)) := by
      dsimp [L, collectiveStepL]
      rw [pow_add, ← pow_mul]
      norm_num only [show (2 : ℕ) ^ 2 = 4 by norm_num]
      congr 2
      ring
    rw [heq]
    calc _ ≤ U * U ^ (h * (k + 1)) := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hpowB _)
      _ = U ^ (1 + h * (k + 1)) := by rw [pow_add, pow_one]
  have hpowb : 2 ^ b ≤ U ^ 3 := by
    have h := Nat.pow_log_le_self 2 (show L + D + 1 ≠ 0 by omega)
    have hV' : L + D + 1 ≤ U ^ 2 := hV
    have h2 : 2 ≤ U := by omega
    calc 2 ^ b = 2 ^ (Nat.log 2 (L + D + 1)) * 2 := by change 2 ^ (Nat.log 2 (L + D + 1) + 1) = _; rw [pow_succ]
      _ ≤ U ^ 2 * 2 := Nat.mul_le_mul_right 2 (h.trans hV')
      _ ≤ U ^ 2 * U := Nat.mul_le_mul_left _ h2
      _ = U ^ 3 := by ring
  have hD : D ≤ 2 * h * (k + 1) := by
    have hkA : k ≤ h * (k + 1) := by
      have hp := Nat.mul_le_mul_right (k + 1) hh1
      omega
    dsimp [D, collectiveStepD]
    nlinarith only [hkA]
  have hA1 : 1 ≤ h * (k + 1) := Nat.mul_pos hh1 (Nat.succ_pos k)
  calc
    2 ^ collectiveSteps k h W = 2 ^ L * (2 ^ b) ^ (2 * D) := by
      change 2 ^ (L + D * (2 * b)) = _
      rw [pow_add, ← pow_mul]
      congr 1
      congr 1
      ring
    _ ≤ U ^ (1 + h * (k + 1)) * (U ^ 3) ^ (2 * D) :=
      Nat.mul_le_mul hpowL (Nat.pow_le_pow_left hpowb _)
    _ = U ^ (1 + h * (k + 1) + 6 * D) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ U ^ (19 * h * (k + 1)) := Nat.pow_le_pow_right hU1 (by nlinarith only [hD, hA1])

/-- Every auxiliary parameter has a common power bound; the exponential
step factor retains the smaller rank-sensitive exponent. -/
theorem collectiveLambdaExponent_add_one_le {m d W h : ℕ}
    (P : CollectiveFeldmanParams (m + 1) d W) (hh1 : 1 ≤ h) (hhk : h ≤ m + 1) (hW : 1 ≤ W)
    (hR : P.R = collectiveSteps (m + 1) h W)
    (hq : P.q = (1000 * W * (m + 1) * (P.R + 1)) ^ h * (P.R + 1))
    (hM : P.M = 1000 * W * ((m + 1) * P.q))
    (hc : P.c = 16 * (m + 1) * (P.R + 1) * ((m + 1) * P.q))
    (ha : P.a = 2 * P.c * (1000 * W * (m + 1) * (P.R + 1)) ^ h) :
    collectiveLambdaExponent P + 1 ≤ (collectiveBase (m + 1) W : ℝ) ^ (100 * h * (m + 2)) := by
  obtain ⟨hU, hsq, hB, hm16, hWU⟩ := collectiveBase_bounds (m + 1) W hW
  have hR1 : P.R + 1 ≤ collectiveBase (m + 1) W ^ 6 :=
    hR ▸ collectiveSteps_add_one_le (by omega) hhk hW
  have h2R : 2 ^ P.R ≤ collectiveBase (m + 1) W ^ (19 * h * (m + 2)) :=
    hR ▸ two_pow_collectiveSteps_le (by omega) hh1 hhk hW
  generalize collectiveBase (m + 1) W = U at hU hsq hB hm16 hWU hR1 h2R ⊢
  have hU1 : 1 ≤ U := by omega
  have hWk : 1000 * W * (m + 1) ≤ U := by nlinarith only [hB, Nat.zero_le (W * (m + 1))]
  have h1000 : 1000 * W ≤ U :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans hWk
  have hkU : m + 1 ≤ U := by omega
  have hE : 1000 * W * (m + 1) * (P.R + 1) ≤ U ^ 7 := by
    calc _ ≤ U * U ^ 6 := Nat.mul_le_mul hWk hR1
      _ = U ^ 7 := by ring
  have hEh : (1000 * W * (m + 1) * (P.R + 1)) ^ h ≤ U ^ (7 * h) := by
    calc _ ≤ (U ^ 7) ^ h := Nat.pow_le_pow_left hE _
      _ = U ^ (7 * h) := (pow_mul _ _ _).symm
  have hq' : P.q ≤ U ^ (13 * h) := by
    rw [hq]
    calc _ ≤ U ^ (7 * h) * U ^ 6 := Nat.mul_le_mul hEh hR1
      _ = U ^ (7 * h + 6) := (pow_add _ _ _).symm
      _ ≤ U ^ (13 * h) := Nat.pow_le_pow_right hU1 (by omega)
  have hQ : P.analyticBox ≤ U ^ (14 * h) := by
    calc _ ≤ U * U ^ (13 * h) := Nat.mul_le_mul hkU hq'
      _ = U ^ (1 + 13 * h) := by rw [pow_add, pow_one]
      _ ≤ U ^ (14 * h) := Nat.pow_le_pow_right hU1 (by omega)
  have hM' : P.M ≤ U ^ (15 * h) := by
    rw [hM]
    calc _ ≤ U * U ^ (14 * h) := Nat.mul_le_mul h1000 hQ
      _ = U ^ (1 + 14 * h) := by rw [pow_add, pow_one]
      _ ≤ U ^ (15 * h) := Nat.pow_le_pow_right hU1 (by omega)
  have hM1 : 1 ≤ P.M := by have := P.M_ge; omega
  have hS' : P.S ≤ U ^ (21 * h) := by
    have hSR : P.S ≤ (P.R + 1) * P.M := by rw [P.S_eq]; nlinarith only [hM1]
    calc _ ≤ (P.R + 1) * P.M := hSR
      _ ≤ U ^ 6 * U ^ (15 * h) := Nat.mul_le_mul hR1 hM'
      _ = U ^ (6 + 15 * h) := (pow_add _ _ _).symm
      _ ≤ U ^ (21 * h) := Nat.pow_le_pow_right hU1 (by omega)
  have hc' : P.c ≤ U ^ (22 * h) := by
    rw [hc]
    calc _ ≤ U * U ^ 6 * U ^ (14 * h) := Nat.mul_le_mul (Nat.mul_le_mul hm16 hR1) hQ
      _ = U ^ (7 + 14 * h) := by rw [pow_add]; ring
      _ ≤ U ^ (22 * h) := Nat.pow_le_pow_right hU1 (by omega)
  have ha' : P.a ≤ U ^ (30 * h) := by
    rw [ha]
    calc _ ≤ U * U ^ (22 * h) * U ^ (7 * h) := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hc') hEh
      _ = U ^ (1 + 22 * h + 7 * h) := by rw [pow_add, pow_add, pow_one]
      _ ≤ U ^ (30 * h) := Nat.pow_le_pow_right hU1 (by omega)
  set V := U ^ (30 * h) with hV
  have hpow : ∀ i, i ≤ 30 * h → U ^ i ≤ V := fun i hi => Nat.pow_le_pow_right hU1 hi
  have hRV : P.R ≤ V := (Nat.le_succ _).trans (hR1.trans (hpow 6 (by omega)))
  have hQV := hQ.trans (hpow _ (by omega))
  have hMV := hM'.trans (hpow _ (by omega))
  have hSV := hS'.trans (hpow _ (by omega))
  have hcV := hc'.trans (hpow _ (by omega))
  have hWV : W ≤ V := hWU.trans (by simpa only [pow_one] using hpow 1 (by omega))
  have hmV : m ≤ V := (show m ≤ U by omega).trans (by simpa only [pow_one] using hpow 1 (by omega))
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (V : ℝ) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (2 : ℝ) ^ P.R := ⟨_, rfl⟩
  have hv1 : 1 ≤ v := by rw [hv]; exact_mod_cast Nat.one_le_pow (30 * h) U hU1
  have hZ1 : 1 ≤ Z := hZ ▸ one_le_pow₀ (by norm_num)
  have rS : (P.S : ℝ) ≤ v := by rw [hv]; exact_mod_cast hSV
  have ra : (P.a : ℝ) ≤ v := by rw [hv]; exact_mod_cast ha'
  have rQ : (P.analyticBox : ℝ) ≤ v := by rw [hv]; exact_mod_cast hQV
  have rc : (P.c : ℝ) ≤ v := by rw [hv]; exact_mod_cast hcV
  have rR : (P.R : ℝ) ≤ v := by rw [hv]; exact_mod_cast hRV
  have rM : (P.M : ℝ) ≤ v := by rw [hv]; exact_mod_cast hMV
  have rW : (W : ℝ) ≤ v := by rw [hv]; exact_mod_cast hWV
  have rm : (m : ℝ) ≤ v := by rw [hv]; exact_mod_cast hmV
  have hpoly : (v + 1) * v * (1 + 2 * v) + 4 * v + 2 * (v + 1) * v +
      v * (1 + v * v) + 2 * (v + 1) * (19 + 12 * v) +
      (Z * v) * (18 + 8 * v * v + 16 * v + 10 * v ^ 2) + 5 + v * (v + v + 1) ≤
        200 * Z * v ^ 3 := by
    convert lambda_polynomial_le hv1 hZ1 using 1; ring
  have hlam : collectiveLambdaExponent P ≤ 200 * Z * v ^ 3 := by
    refine le_trans ?_ hpoly
    unfold collectiveLambdaExponent
    rw [← hZ]
    gcongr
  have hZU : Z ≤ (U : ℝ) ^ (19 * h * (m + 2)) := by rw [hZ]; exact_mod_cast h2R
  have hvU : v ^ 3 = (U : ℝ) ^ (90 * h) := by rw [hv, hV, Nat.cast_pow, ← pow_mul]; congr 1; ring
  have hU201 : (201 : ℝ) ≤ U := by exact_mod_cast (show 201 ≤ U by omega)
  have hUr1 : (1 : ℝ) ≤ U := by exact_mod_cast hU1
  have hZv : 1 ≤ Z * v ^ 3 := one_le_mul_of_one_le_of_one_le hZ1 (one_le_pow₀ hv1)
  have hexp : 1 + 19 * h * (m + 2) + 90 * h ≤ 100 * h * (m + 2) := by
    nlinarith only [hh1, Nat.zero_le (h * m)]
  calc collectiveLambdaExponent P + 1 ≤ 201 * Z * v ^ 3 := by linarith only [hlam, hZv]
    _ ≤ (U : ℝ) * (U : ℝ) ^ (19 * h * (m + 2)) * (U : ℝ) ^ (90 * h) := by rw [hvU]; gcongr
    _ = (U : ℝ) ^ (1 + 19 * h * (m + 2) + 90 * h) := by rw [pow_add, pow_add, pow_one]
    _ ≤ (U : ℝ) ^ (100 * h * (m + 2)) := pow_le_pow_right₀ hUr1 hexp

/-- Exponent with reciprocal-rank dependence through `floor((k-r)/r)+1`. -/
def collectiveExponent (r d W : ℕ) : ℝ :=
  (collectiveBase (d + r) W : ℝ) ^ (100 * collectiveRootDegree d r * (d + r + 1))

/-- Uniform floor excluding rank `r` from a height-`H` approximation body. -/
def collectiveDepthFloor (r d W : ℕ) (H : ℝ) : ℝ :=
  exp (-(collectiveExponent r d W * (log ((r.factorial : ℝ) * H ^ r) + 2))) /
    ((r : ℝ) * (r.factorial : ℝ) * H ^ (r - 1))

theorem collectiveDepthFloor_pos {r d W : ℕ} (hr : 1 ≤ r) {H : ℝ} (hH : 0 < H) :
    0 < collectiveDepthFloor r d W H := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  unfold collectiveDepthFloor
  exact div_pos (exp_pos _) (by positivity)

/-- A simultaneous small-form bound whose constant is uniform over every
independent family in the same prime-coordinate space. -/
theorem exists_large_collective_form (d r : ℕ)
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (A : Matrix (Fin (r + 1)) (Fin (d + r + 1)) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (A i j : ℚ)))
    {H : ℝ} (hH : 1 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    ∃ i, collectiveDepthFloor (r + 1) d (collectiveLogBound p) H ≤
      |∑ j, (A i j : ℝ) * log (p j)| := by
  obtain ⟨P, hPR, hPq, hPM, hPc, hPa, hforms⟩ :=
    exists_explicit_collective_logarithm_bound d r p hp hprime A hind
  have hh1 : 1 ≤ collectiveRootDegree d (r + 1) := Nat.le_add_left 1 _
  have hhk : collectiveRootDegree d (r + 1) ≤ d + r + 1 := by
    have hdiv := Nat.div_le_self d (r + 1)
    unfold collectiveRootDegree
    omega
  have hW : 1 ≤ collectiveLogBound p := Nat.le_add_left 1 _
  have hC := collectiveLambdaExponent_add_one_le P hh1 hhk hW hPR hPq hPM hPc hPa
  have hfac : (1 : ℝ) ≤ (r + 1).factorial := by exact_mod_cast (r + 1).factorial_pos
  have hB1 : (1 : ℝ) ≤ ((r + 1).factorial : ℝ) * H ^ (r + 1) :=
    one_le_mul_of_one_le_of_one_le hfac (one_le_pow₀ hH)
  have hlog : 0 ≤ log (((r + 1).factorial : ℝ) * H ^ (r + 1)) + 2 := by
    linarith only [log_nonneg hB1]
  obtain ⟨i, hi⟩ := hforms H hH hA
  refine ⟨i, le_trans ?_ hi⟩
  unfold collectiveDepthFloor collectiveExponent
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_right hC hlog)

/-- A basis selected from the approximation body cannot have rank exceeding
its uniform simultaneous-form threshold. -/
theorem collective_small_forms_span_finrank_le {d r : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (S : Finset (Fin (d + r + 1) → ℤ)) {H : ℝ} (hH : 1 ≤ H)
    (hheight : ∀ ν ∈ S, ∀ j, |(ν j : ℝ)| ≤ H)
    (hsmall : ∀ ν ∈ S, |primeLogForm p ν| < collectiveDepthFloor (r + 1) d (collectiveLogBound p) H) :
    Module.finrank ℚ (Submodule.span ℚ
      (↑(S.image HTGeometry.intVectorToRat) : Set (Fin (d + r + 1) → ℚ))) ≤ r := by
  classical
  let T : Set (Fin (d + r + 1) → ℚ) := ↑(S.image HTGeometry.intVectorToRat)
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ℚ T
  have hbfin : b.Finite := (S.image HTGeometry.intVectorToRat).finite_toSet.subset hbsub
  letI : Fintype b := hbfin.fintype
  have hdim : Module.finrank ℚ (Submodule.span ℚ T) = Fintype.card b := by
    have h := finrank_span_eq_card hbind
    rw [Subtype.range_coe, hbspan] at h
    exact h
  by_contra hdimle
  have hcard : r + 1 ≤ Fintype.card b := by
    rw [← hdim]
    exact Nat.succ_le_of_lt (lt_of_not_ge hdimle)
  let f : Fin (r + 1) → b := fun i =>
    (Fintype.equivFin b).symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have h := congrArg (fun v : b => (Fintype.equivFin b v).val) hij
    simpa only [f, Equiv.apply_symm_apply] using h
  have hex : ∀ i : Fin (r + 1), ∃ ν ∈ S,
      HTGeometry.intVectorToRat ν = (f i : Fin (d + r + 1) → ℚ) := by
    intro i
    exact Finset.mem_image.mp (hbsub (f i).property)
  choose A hAs hAeq using hex
  have heq : (fun i j => (A i j : ℚ)) = (Subtype.val ∘ f) := funext hAeq
  have hind : LinearIndependent ℚ (fun i j => (A i j : ℚ)) := by
    rw [heq]
    exact hbind.comp f hf
  obtain ⟨i, hi⟩ := exists_large_collective_form d r p hp hprime A hind hH
    (fun i j => hheight (A i) (hAs i) j)
  exact (not_lt_of_ge hi) (hsmall (A i) (hAs i))

/-- All near relations below the collective floor lie in one rational
subspace of dimension at most `r`. -/
theorem nearRelationBox_finrank_le_collective {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ collectiveDepthFloor (r + 1) d (collectiveLogBound p) H) :
    Module.finrank ℚ (Submodule.span ℚ
      (↑((nearRelationBox p H ε).image HTGeometry.intVectorToRat) : Set (Fin (d + r + 1) → ℚ))) ≤ r := by
  apply collective_small_forms_span_finrank_le (H := (H : ℝ)) p hp hprime (nearRelationBox p H ε)
    (by exact_mod_cast hH)
  · intro ν hν j
    have h := ((mem_nearRelationBox p H ε ν).mp hν).1 j
    exact_mod_cast h
  · intro ν hν
    exact (((mem_nearRelationBox p H ε ν).mp hν).2).trans_le hε

/-- The same rank threshold controls the whole coefficient-box count. -/
theorem nearRelationBox_card_le_collective {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ collectiveDepthFloor (r + 1) d (collectiveLogBound p) H) :
    (nearRelationBox p H ε).card ≤ (2 * H + 1) ^ r := by
  have hc := HTGeometry.card_intVectors_le_pow_finrank_span (nearRelationBox p H ε) H
    (fun ν hν => ((mem_nearRelationBox p H ε ν).mp hν).1)
  refine hc.trans ?_
  exact pow_le_pow_right₀ (by omega) (nearRelationBox_finrank_le_collective p hp hprime hH hε)


/-- Multiplying the exponent degree by rank gives at most `100k(k+1)`.
This states the reciprocal-rank law without rounding a real quotient. -/
theorem collective_exponent_degree_mul_rank_le (d r : ℕ) :
    (100 * collectiveRootDegree d r * (d + r + 1)) * r ≤
      100 * (d + r) * (d + r + 1) := by
  have hdiv := Nat.div_mul_le_self d r
  have hhr : collectiveRootDegree d r * r ≤ d + r := by
    unfold collectiveRootDegree
    nlinarith only [hdiv]
  calc _ = 100 * (collectiveRootDegree d r * r) * (d + r + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 100 hhr)

/-- At rank at least half the dimension, the explicit exponent has only
linear degree in the number of prime coordinates. -/
theorem collectiveExponent_le_of_half_rank {d r W : ℕ} (hr : 1 ≤ r) (hdr : d ≤ r) :
    collectiveExponent r d W ≤ (collectiveBase (d + r) W : ℝ) ^ (200 * (d + r + 1)) := by
  have hh : collectiveRootDegree d r ≤ 2 :=
    (collectiveRootDegree_le_iff d hr).mpr (by omega)
  have hbase : (1 : ℝ) ≤ collectiveBase (d + r) W := by
    have h : 1 ≤ collectiveBase (d + r) W := Nat.one_le_iff_ne_zero.mpr (by unfold collectiveBase; positivity)
    exact_mod_cast h
  unfold collectiveExponent
  apply pow_le_pow_right₀ hbase
  have hm := Nat.mul_le_mul_right (d + r + 1) (Nat.mul_le_mul_left 100 hh)
  simpa only [show 100 * 2 = 200 by norm_num] using hm

/-- Strictly above half rank, the root degree is exactly one. -/
theorem collectiveExponent_of_large_rank {d r W : ℕ} (hdr : d < r) :
    collectiveExponent r d W = (collectiveBase (d + r) W : ℝ) ^ (100 * (d + r + 1)) := by
  rw [collectiveExponent, collectiveRootDegree_eq_one hdr, mul_one]

/-- The collective and scalar-elimination floors are complementary; either
one excludes the same rank from the whole approximation body. -/
theorem nearRelationBox_finrank_le_max_floor {d r y H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ max (rankDepthFloor (r + 1) d y H)
      (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)) :
    Module.finrank ℚ (Submodule.span ℚ
      (↑((nearRelationBox p H ε).image HTGeometry.intVectorToRat) : Set (Fin (d + r + 1) → ℚ))) ≤ r := by
  rcases le_total (rankDepthFloor (r + 1) d y H)
    (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H) with h | h
  · rw [max_eq_right h] at hε
    exact nearRelationBox_finrank_le_collective p hp hprime hH hε
  · rw [max_eq_left h] at hε
    apply nearRelationBox_finrank_le p hp hprime hy hH
    simpa only [show d + r + 1 - (r + 1) = d by omega] using hε

/-- Cardinality with both depth regimes retained. -/
theorem nearRelationBox_card_le_max_floor {d r y H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (hy : ∀ j, p j ≤ y) (hH : 1 ≤ H) {ε : ℝ}
    (hε : ε ≤ max (rankDepthFloor (r + 1) d y H)
      (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)) :
    (nearRelationBox p H ε).card ≤ (2 * H + 1) ^ r := by
  have hc := HTGeometry.card_intVectors_le_pow_finrank_span (nearRelationBox p H ε) H
    (fun ν hν => ((mem_nearRelationBox p H ε ν).mp hν).1)
  exact hc.trans (pow_le_pow_right₀ (by omega) (nearRelationBox_finrank_le_max_floor p hp hprime hy hH hε))


end GaloisForLFunctions.CollectiveDiophantineGeometry
