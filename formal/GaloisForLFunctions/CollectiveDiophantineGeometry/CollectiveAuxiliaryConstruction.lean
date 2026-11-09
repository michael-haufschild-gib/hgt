import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.LinearFormsWithExplicitDependenceOnTheirNumber

import GaloisForLFunctions.HTGeometry.LinearIndependenceMinorTransfer

/-!
# Collective auxiliary functions for prime logarithms

A maximal absolute pivot minor gives a projection of sup-norm at most `r+1`
with `r` pivot coordinates identically zero. Its frequency defect is an exact
adjugate-weighted combination of the original linear forms.

The integral jet system keeps all `k` prime-frequency coordinates while using
only `d=k-r` free directions. Its row count is `X S^(d+1)`, against
`(N+1)q^k` coefficients. Explicit parameters use the root degree
`h=floor(d/r)+1`: the polynomial controlling the extrapolation length has
degree `h(k+1)+k`, which is at most `3k+2` when `r≥d`.

Integer Siegel supplies a nonzero coefficient vector with an explicit height
bound. Clearing the pivot determinant gives exact initial jet vanishing;
confluent interpolation gives a nonzero true value before the full
prime-frequency interpolation length. A simultaneous logarithm bound still
requires analytic extrapolation with these free-direction jets.
-/

open Real Matrix Finset
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open RHTower.Matveev TranscendenceTheoryOfThePrimeOrbit

/-- The least positive integer `h` with `d+1 ≤ hr`. -/
def collectiveRootDegree (d r : ℕ) : ℕ := d / r + 1

theorem collectiveRootDegree_spec (d : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    1 ≤ collectiveRootDegree d r ∧ d + 1 ≤ collectiveRootDegree d r * r := by
  have h := (Nat.div_lt_iff_lt_mul (show 0 < r by omega)).mp
    (Nat.lt_succ_self (d / r))
  constructor
  · exact Nat.le_add_left 1 _
  · exact Nat.succ_le_iff.mpr h

/-- Natural parameters for an auxiliary with `k` prime directions and `d`
free directions. The arithmetic system has only `d+1` derivative indices. -/
structure CollectiveFeldmanParams (k d W : ℕ) where
  R : ℕ
  M : ℕ
  q : ℕ
  S : ℕ
  c : ℕ
  a : ℕ
  one_le_R : 1 ≤ R
  one_le_q : 1 ≤ q
  one_le_c : 1 ≤ c
  S_eq : S = R * M + 1
  M_ge : 4 * (9 + 17 * (k * q) * W) ≤ M
  siegel : 2 * c * S ^ (d + 1) ≤ a * q ^ k
  terminal : 2 * a * q ^ k ≤ 2 ^ R * c
  logS : Nat.log 2 S ≤ R
  gain : 4 * (k * S * (1 + 2 * (k * q)) + 4 * a + 2 * k * (k * q) +
    2 * (a + 1) * (19 + 12 * R) + 1) ≤ 3 * M * c

/-- The residual dimension determines the power needed in the exponent box. -/
private theorem collective_siegel_power {d r h E q : ℕ} (hr : 1 ≤ r)
    (hh : d + 1 ≤ h * r) (hE : 1 ≤ E) (hq : E ^ h ≤ q) :
    (E * q) ^ (d + 1) ≤ E ^ h * q ^ (d + r) := by
  have hsplit : d + r = (d + 1) + (r - 1) := by omega
  have hpow : E ^ (d + 1) ≤ E ^ h * q ^ (r - 1) := by
    calc
      E ^ (d + 1) ≤ E ^ (h * r) := Nat.pow_le_pow_right hE hh
      _ = E ^ h * (E ^ h) ^ (r - 1) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        have : r = 1 + (r - 1) := by omega
        conv_lhs => rw [this]
        ring
      _ ≤ E ^ h * q ^ (r - 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq _)
  calc
    (E * q) ^ (d + 1) = E ^ (d + 1) * q ^ (d + 1) := mul_pow _ _ _
    _ ≤ (E ^ h * q ^ (r - 1)) * q ^ (d + 1) := Nat.mul_le_mul_right _ hpow
    _ = E ^ h * q ^ (d + r) := by rw [hsplit, pow_add]; ring

/-- All analytic, arithmetic and terminal inequalities hold at the collective
box size, provided the explicit polynomial in `R` is at most `2^R`. -/
theorem exists_collectiveFeldmanParams_of_R (d r W R h : ℕ)
    (hr : 1 ≤ r) (hW : 1 ≤ W) (hR1 : 1 ≤ R) (hh1 : 1 ≤ h)
    (hhr : d + 1 ≤ h * r)
    (hR : 4 * (1000 * W * (d + r)) ^ (h * (d + r + 1)) *
      (R + 1) ^ (h * (d + r + 1) + (d + r)) ≤ 2 ^ R) :
    ∃ P : CollectiveFeldmanParams (d + r) d W,
      P.R = R ∧
      P.q = (1000 * W * (d + r) * (R + 1)) ^ h * (R + 1) ∧
      P.M = 1000 * W * ((d + r) * P.q) ∧
      P.c = 16 * (d + r) * (R + 1) * ((d + r) * P.q) ∧
      P.a = 2 * P.c * (1000 * W * (d + r) * (R + 1)) ^ h := by
  obtain ⟨k, hk⟩ : ∃ k, k = d + r := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨E, hE⟩ : ∃ E, E = 1000 * W * k * (R + 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = E ^ h * (R + 1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 1000 * W * (k * q) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = R * M + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 16 * k * (R + 1) * (k * q) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * c * E ^ h := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hc1 : 1 ≤ c := by rw [hc]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hEhq : E ^ h ≤ q := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hpoly : 4 * E ^ h * q ^ k ≤ 2 ^ R := by
    calc
      4 * E ^ h * q ^ k = 4 * (1000 * W * k) ^ (h * (k + 1)) *
          (R + 1) ^ (h * (k + 1) + k) := by
        rw [hq, mul_pow, ← pow_mul]
        calc 4 * E ^ h * (E ^ (h * k) * (R + 1) ^ k)
            = 4 * (E ^ h * E ^ (h * k)) * (R + 1) ^ k := by ring
          _ = 4 * E ^ (h * (k + 1)) * (R + 1) ^ k := by
            rw [← pow_add, show h + h * k = h * (k + 1) by ring]
          _ = _ := by rw [hE, mul_pow, pow_add]; ring
      _ ≤ 2 ^ R := by simpa only [hk] using hR
  have hWkq : 1 ≤ W * k * q := by exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hSEq : S ≤ E * q := by
    have h1 : E * q = R * (1000 * W * (k * q)) + 1000 * (W * k * q) := by rw [hE]; ring
    rw [hS, hM, h1]
    omega
  have hEq : E * q ≤ 4 * E ^ h * q ^ k := by
    have h1 : E ≤ E ^ h := Nat.le_self_pow (by omega) E
    have h2 : q ≤ q ^ k := Nat.le_self_pow (by omega) q
    calc E * q ≤ E ^ h * q ^ k := Nat.mul_le_mul h1 h2
      _ ≤ 4 * E ^ h * q ^ k := by
          rw [mul_assoc]
          exact Nat.le_mul_of_pos_left _ (by norm_num)
  have haq : a = 32 * (k * k * q * q) := by rw [ha, hc, hq]; ring
  have hgain : 4 * (k * S * (1 + 2 * (k * q)) + 4 * a + 2 * k * (k * q) +
      2 * (a + 1) * (19 + 12 * R) + 1) ≤ 3 * M * c := by
    obtain ⟨u, hu⟩ : ∃ u, u = k * k * k * W * q * q := ⟨_, rfl⟩
    have hu1 : 1 ≤ u := by rw [hu]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hRWkq : 1 ≤ R * W * k * q := by exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hkq1 : 1 ≤ k * q := by exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hSle : S ≤ 1001 * (R * W * k * q) := by
      have h : R * M = 1000 * (R * W * k * q) := by rw [hM]; ring
      rw [hS, h]; omega
    have h1 : k * S * (1 + 2 * (k * q)) ≤ 3003 * R * u := by
      calc k * S * (1 + 2 * (k * q)) ≤ k * (1001 * (R * W * k * q)) * (3 * (k * q)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hSle) (by omega)
        _ = 3003 * R * u := by rw [hu]; ring
    have hkkqq : k * k * q * q ≤ u := by
      rw [hu]
      calc k * k * q * q = k * k * 1 * 1 * q * q := by ring
        _ ≤ k * k * k * W * q * q := by gcongr
    have h2 : 4 * a ≤ 128 * u := by
      rw [haq]
      calc 4 * (32 * (k * k * q * q)) = 128 * (k * k * q * q) := by ring
        _ ≤ 128 * u := Nat.mul_le_mul_left _ hkkqq
    have h3 : 2 * k * (k * q) ≤ 2 * u := by
      have : k * k * q ≤ k * k * q * q := Nat.le_mul_of_pos_right _ (by omega)
      calc 2 * k * (k * q) = 2 * (k * k * q) := by ring
        _ ≤ 2 * u := Nat.mul_le_mul_left _ (this.trans hkkqq)
    have h4 : 2 * (a + 1) * (19 + 12 * R) ≤ 66 * u * (19 + 12 * R) := by
      have ha1 : a + 1 ≤ 33 * u := by
        rw [haq]
        have := Nat.mul_le_mul_left 32 hkkqq
        omega
      calc 2 * (a + 1) * (19 + 12 * R) ≤ 2 * (33 * u) * (19 + 12 * R) := by gcongr
        _ = 66 * u * (19 + 12 * R) := by ring
    calc 4 * (k * S * (1 + 2 * (k * q)) + 4 * a + 2 * k * (k * q) +
        2 * (a + 1) * (19 + 12 * R) + 1)
        ≤ 4 * (3003 * R * u + 128 * u + 2 * u + 66 * u * (19 + 12 * R) + u) := by gcongr
      _ = u * (15180 * R + 5540) := by ring
      _ ≤ u * (48000 * (R + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * M * c := by rw [hM, hc, hu]; ring
  have hMge : 4 * (9 + 17 * (k * q) * W) ≤ M := by
    have h1 : M = 1000 * (W * k * q) := by rw [hM]; ring
    have h2 : 4 * (9 + 17 * (k * q) * W) = 36 + 68 * (W * k * q) := by ring
    rw [h1, h2]
    omega
  have hsiegel : 2 * c * S ^ (d + 1) ≤ a * q ^ k := by
    have hp := collective_siegel_power hr hhr hE1 hEhq
    calc 2 * c * S ^ (d + 1) ≤ 2 * c * (E * q) ^ (d + 1) := by gcongr
      _ ≤ 2 * c * (E ^ h * q ^ (d + r)) := Nat.mul_le_mul_left _ hp
      _ = a * q ^ k := by rw [ha, hk]; ring
  have hterminal : 2 * a * q ^ k ≤ 2 ^ R * c := by
    calc 2 * a * q ^ k = c * (4 * E ^ h * q ^ k) := by rw [ha]; ring
      _ ≤ c * 2 ^ R := Nat.mul_le_mul_left _ hpoly
      _ = 2 ^ R * c := Nat.mul_comm _ _
  have hlogS : Nat.log 2 S ≤ R := by
    have hlt : S < 2 ^ (R + 1) := by
      calc S ≤ 2 ^ R := hSEq.trans (hEq.trans hpoly)
        _ < 2 ^ (R + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self R)
    have := Nat.log_lt_of_lt_pow (show S ≠ 0 by rw [hS]; omega) hlt
    omega
  let P : CollectiveFeldmanParams k d W :=
    ⟨R, M, q, S, c, a, hR1, hq1, hc1, hS, hMge, hsiegel, hterminal, hlogS, hgain⟩
  subst k
  refine ⟨P, rfl, ?_, ?_, ?_, ?_⟩
  · change q = _; rw [hq, hE]
  · exact hM
  · exact hc
  · change a = _; rw [ha, hE]


/-- A binary-logarithmic bound for the constant coefficient of the parameter inequality. -/
def collectiveStepL (k h W : ℕ) : ℕ :=
  2 + h * (k + 1) * (Nat.log 2 (1000 * W * k) + 1)

/-- Degree of the polynomial that the extrapolation length must dominate. -/
def collectiveStepD (k h : ℕ) : ℕ := h * (k + 1) + k

/-- Explicit extrapolation length; its degree retains the collective factor `h`. -/
def collectiveSteps (k h W : ℕ) : ℕ :=
  collectiveStepL k h W + collectiveStepD k h *
    (2 * (Nat.log 2 (collectiveStepL k h W + collectiveStepD k h + 1) + 1))

/-- The explicit length closes the polynomial-versus-exponential inequality. -/
theorem collectiveSteps_spec (k h W : ℕ) :
    4 * (1000 * W * k) ^ (h * (k + 1)) *
      (collectiveSteps k h W + 1) ^ (h * (k + 1) + k) ≤
        2 ^ collectiveSteps k h W := by
  set L := collectiveStepL k h W
  set D := collectiveStepD k h
  set B := Nat.log 2 (L + D + 1) + 1
  have hK : 4 * (1000 * W * k) ^ (h * (k + 1)) ≤ 2 ^ L := by
    have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (1000 * W * k)
    have hp := Nat.pow_le_pow_left ht.le (h * (k + 1))
    calc
      4 * (1000 * W * k) ^ (h * (k + 1)) ≤
          2 ^ 2 * (2 ^ (Nat.log 2 (1000 * W * k) + 1)) ^ (h * (k + 1)) := by
            simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using Nat.mul_le_mul_left 4 hp
      _ = 2 ^ L := by
        simp only [L, collectiveStepL, ← pow_mul, ← pow_add]
        congr 1
        ring
  have hB1 : 1 ≤ B := by dsimp [B]; omega
  have haB : L + D + 1 < 2 ^ B := Nat.lt_pow_succ_log_self (by norm_num) _
  have hR : collectiveSteps k h W + 1 ≤ 2 ^ (2 * B) := by
    have hs : collectiveSteps k h W + 1 ≤ (L + D + 1) * (2 * B) := by
      change L + D * (2 * B) + 1 ≤ _
      nlinarith only [hB1, Nat.zero_le L]
    calc
      collectiveSteps k h W + 1 ≤ (L + D + 1) * (2 * B) := hs
      _ ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul haB.le (two_mul_le_two_pow hB1)
      _ = 2 ^ (2 * B) := by rw [← pow_add]; congr 1; ring
  calc
    4 * (1000 * W * k) ^ (h * (k + 1)) * (collectiveSteps k h W + 1) ^ D ≤
        2 ^ L * (2 ^ (2 * B)) ^ D := Nat.mul_le_mul hK (Nat.pow_le_pow_left hR _)
    _ = 2 ^ collectiveSteps k h W := by
      rw [← pow_mul, ← pow_add]
      congr 1
      change L + 2 * B * D = L + D * (2 * B)
      ring

/-- The explicit simultaneous parameters exist for every positive rank and
logarithmic mass bound; no asymptotic choice is needed. -/
theorem exists_collectiveFeldmanParams (d r W : ℕ) (hr : 1 ≤ r) (hW : 1 ≤ W) :
    ∃ P : CollectiveFeldmanParams (d + r) d W,
      P.R = collectiveSteps (d + r) (collectiveRootDegree d r) W ∧
      P.q = (1000 * W * (d + r) * (P.R + 1)) ^ collectiveRootDegree d r * (P.R + 1) ∧
      P.M = 1000 * W * ((d + r) * P.q) ∧
      P.c = 16 * (d + r) * (P.R + 1) * ((d + r) * P.q) ∧
      P.a = 2 * P.c * (1000 * W * (d + r) * (P.R + 1)) ^ collectiveRootDegree d r := by
  obtain ⟨hh1, hhr⟩ := collectiveRootDegree_spec d hr
  have hR1 : 1 ≤ collectiveSteps (d + r) (collectiveRootDegree d r) W := by
    unfold collectiveSteps collectiveStepL
    omega
  obtain ⟨P, hPR, hPq, hPM, hPc, hPa⟩ := exists_collectiveFeldmanParams_of_R d r W
    (collectiveSteps (d + r) (collectiveRootDegree d r) W) (collectiveRootDegree d r)
    hr hW hR1 hh1 hhr (collectiveSteps_spec _ _ _)
  exact ⟨P, hPR, by simpa only [hPR] using hPq, hPM,
    by simpa only [hPR] using hPc, by simpa only [hPR] using hPa⟩

/-- A maximal absolute column minor bounds every Cramer numerator by its determinant. -/
theorem exists_bounded_cramer_minor {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (M i j : ℚ))) :
    ∃ s : Fin r → Fin k, (M.submatrix id s).det ≠ 0 ∧
      ∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤
        |(M.submatrix id s).det| := by
  classical
  obtain ⟨s₀, -, h₀⟩ := HTGeometry.exists_injective_det_submatrix_ne_zero
    (M := M.map (Int.castRingHom ℚ)) hind
  have h₀Z : (M.submatrix id s₀).det ≠ 0 := by
    intro hz
    apply h₀
    change ((Int.castRingHom ℚ).mapMatrix (M.submatrix id s₀)).det = 0
    rw [← (Int.castRingHom ℚ).map_det, hz, map_zero]
  obtain ⟨s, -, hs⟩ := Finset.exists_max_image univ
    (fun t : Fin r → Fin k => |(M.submatrix id t).det|)
    (show (univ : Finset (Fin r → Fin k)).Nonempty from ⟨s₀, mem_univ _⟩)
  have hdet : (M.submatrix id s).det ≠ 0 := by
    intro hz
    have hle := hs s₀ (mem_univ _)
    rw [hz, abs_zero] at hle
    exact h₀Z (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
  refine ⟨s, hdet, fun i j => ?_⟩
  have heq : (M.submatrix id s).updateCol i (fun h => M h j) =
      M.submatrix id (Function.update s i j) := by
    ext a b
    by_cases hb : b = i
    · subst b
      simp only [Matrix.updateCol_self, Matrix.submatrix_apply, Function.update_self, id_eq]
    · simp only [Matrix.updateCol_ne hb, Matrix.submatrix_apply,
        Function.update_of_ne hb, id_eq]
  rw [Matrix.cramer_apply, heq]
  exact hs _ (mem_univ _)



/-- Integral coordinates of the projection that kills the selected pivot columns. -/
def collectiveGamma {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (s : Fin r → Fin k) (l : Fin k → ℤ) (j : Fin k) : ℤ :=
  (M.submatrix id s).det * l j -
    ∑ i, l (s i) * (M.submatrix id s).cramer (fun h => M h j) i

/-- Every pivot coordinate is killed exactly, even before dividing by the determinant. -/
theorem collectiveGamma_pivot {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (s : Fin r → Fin k) (l : Fin k → ℤ) (i : Fin r) :
    collectiveGamma M s l (s i) = 0 := by
  classical
  have hcol := Matrix.cramer_row_self (M.submatrix id s) (fun h => M h (s i)) i
    (fun _ => rfl)
  rw [collectiveGamma, hcol]
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- A maximal minor makes the normalized projection height-independent:
its sup-norm is at most `r+1`. -/
theorem collectiveGamma_div_bound {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (s : Fin r → Fin k) (hdet : (M.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤
      |(M.submatrix id s).det|)
    {Q : ℝ} (hQ : 0 ≤ Q) (l : Fin k → ℤ) (hl : ∀ j, |(l j : ℝ)| ≤ Q)
    (j : Fin k) :
    |(collectiveGamma M s l j : ℝ) / ((M.submatrix id s).det : ℝ)| ≤ (r + 1 : ℝ) * Q := by
  have hD : 0 < |((M.submatrix id s).det : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hdet
  rw [abs_div, div_le_iff₀ hD]
  simp only [collectiveGamma, Int.cast_sub, Int.cast_mul, Int.cast_sum]
  calc
    |((M.submatrix id s).det : ℝ) * l j -
        ∑ i, (l (s i) : ℝ) * ((M.submatrix id s).cramer (fun h => M h j) i : ℝ)| ≤
        |((M.submatrix id s).det : ℝ) * l j| +
          |∑ i, (l (s i) : ℝ) * ((M.submatrix id s).cramer (fun h => M h j) i : ℝ)| := abs_sub _ _
    _ ≤ |((M.submatrix id s).det : ℝ)| * Q +
        ∑ _i : Fin r, Q * |((M.submatrix id s).det : ℝ)| := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hl j) hD.le
      · refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        apply mul_le_mul (hl _) ?_ (abs_nonneg _) hQ
        exact_mod_cast hmax i j
    _ = (r + 1 : ℝ) * Q * |((M.submatrix id s).det : ℝ)| := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Independent integer rows have a bounded normalized projection with
exactly the selected `r` coordinates identically zero. -/
theorem exists_bounded_collective_projection {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (M i j : ℚ))) :
    ∃ s : Fin r → Fin k, Function.Injective s ∧ (M.submatrix id s).det ≠ 0 ∧
      (∀ l i, collectiveGamma M s l (s i) = 0) ∧
      ∀ (Q : ℝ), 0 ≤ Q → ∀ (l : Fin k → ℤ), (∀ j, |(l j : ℝ)| ≤ Q) →
        ∀ j, |(collectiveGamma M s l j : ℝ) / ((M.submatrix id s).det : ℝ)| ≤
          (r + 1 : ℝ) * Q := by
  obtain ⟨s, hdet, hmax⟩ := exists_bounded_cramer_minor M hind
  have hs : Function.Injective s := by
    intro i j hij
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne (fun a => congrArg (M a) hij))
  exact ⟨s, hs, hdet, fun l i => collectiveGamma_pivot M s l i,
    fun _ hQ l hl j => collectiveGamma_div_bound M s hdet hmax hQ l hl j⟩

/-- At rank strictly above half the number of directions, only the first power
of the base is needed for the exponent box. -/
theorem collectiveRootDegree_eq_one {d r : ℕ} (h : d < r) :
    collectiveRootDegree d r = 1 := by
  rw [collectiveRootDegree, Nat.div_eq_of_lt h, zero_add]

theorem collectiveStepD_of_large_rank {d r : ℕ} (h : d < r) :
    collectiveStepD (d + r) (collectiveRootDegree d r) = 2 * (d + r) + 1 := by
  rw [collectiveRootDegree_eq_one h, collectiveStepD]
  ring


/-- The least admissible root degree, including its converse. -/
theorem collectiveRootDegree_le_iff (d : ℕ) {r h : ℕ} (hr : 1 ≤ r) :
    collectiveRootDegree d r ≤ h ↔ d + 1 ≤ h * r := by
  change d / r + 1 ≤ h ↔ _
  rw [Nat.succ_le_iff, Nat.div_lt_iff_lt_mul (show 0 < r by omega)]
  exact Nat.succ_le_iff.symm

/-- At rank at least half the dimension, the polynomial degree is linear
in dimension, including the equal-rank boundary. -/
theorem collectiveStepD_of_half_rank {d r : ℕ} (hr : 1 ≤ r) (hdr : d ≤ r) :
    collectiveStepD (d + r) (collectiveRootDegree d r) ≤ 3 * (d + r) + 2 := by
  have hh : collectiveRootDegree d r ≤ 2 :=
    (collectiveRootDegree_le_iff d hr).mpr (by omega)
  rw [collectiveStepD]
  calc
    collectiveRootDegree d r * (d + r + 1) + (d + r) ≤ 2 * (d + r + 1) + (d + r) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hh) _
    _ = 3 * (d + r) + 2 := by ring

/-- Evaluation of the integral projection separates the true frequency
from an adjugate-weighted sum of the original linear forms. -/
theorem collectiveGamma_evaluation {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (s : Fin r → Fin k) (l : Fin k → ℤ) (x : Fin k → ℝ) :
    ∑ j, (collectiveGamma M s l j : ℝ) * x j =
      ((M.submatrix id s).det : ℝ) * (∑ j, (l j : ℝ) * x j) -
        ∑ i, (l (s i) : ℝ) *
          (∑ a, ((M.submatrix id s).adjugate i a : ℝ) * (∑ j, (M a j : ℝ) * x j)) := by
  have hC (i : Fin r) :
      ∑ j, ((M.submatrix id s).cramer (fun h => M h j) i : ℝ) * x j =
        ∑ a, ((M.submatrix id s).adjugate i a : ℝ) * (∑ j, (M a j : ℝ) * x j) := by
    simp_rw [Matrix.cramer_eq_adjugate_mulVec]
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [collectiveGamma, Int.cast_sub, Int.cast_mul, Int.cast_sum,
    sub_mul, Finset.sum_sub_distrib]
  have hfirst : ∑ j, ((M.submatrix id s).det : ℝ) * (l j : ℝ) * x j =
      ((M.submatrix id s).det : ℝ) * ∑ j, (l j : ℝ) * x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  rw [hfirst]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ j, (l (s i) : ℝ) * ((M.submatrix id s).cramer (fun h => M h j) i : ℝ) * x j =
        (l (s i) : ℝ) * ∑ j, ((M.submatrix id s).cramer (fun h => M h j) i : ℝ) * x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    _ = _ := congrArg (fun z => (l (s i) : ℝ) * z) (hC i)

/-- The normalized frequency error is exactly the adjugate-weighted
combination of the original forms, divided by the pivot determinant. -/
theorem collectiveFrequency_defect {r k : ℕ} (M : Matrix (Fin r) (Fin k) ℤ)
    (s : Fin r → Fin k) (hdet : (M.submatrix id s).det ≠ 0)
    (l : Fin k → ℤ) (x : Fin k → ℝ) :
    ∑ j, ((collectiveGamma M s l j : ℝ) / ((M.submatrix id s).det : ℝ)) * x j =
      (∑ j, (l j : ℝ) * x j) -
        (∑ i, (l (s i) : ℝ) *
          (∑ a, ((M.submatrix id s).adjugate i a : ℝ) * (∑ j, (M a j : ℝ) * x j))) /
          ((M.submatrix id s).det : ℝ) := by
  have hD : ((M.submatrix id s).det : ℝ) ≠ 0 := by exact_mod_cast hdet
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, collectiveGamma_evaluation, sub_div]
  congr 1
  field_simp


/-- The normalized weight of a jet in the free coordinates. -/
noncomputable def collectiveGammaWeight {r m d : ℕ}
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) (l : Fin (m + 1) → ℕ) (τ : Fin d → ℕ) : ℂ :=
  ∏ j, ((collectiveGamma M s (fun i => (l i : ℤ)) (t j) : ℂ) /
    ((M.submatrix id s).det : ℂ)) ^ τ j

/-- Companion with the original prime frequencies and only `d` jet coordinates. -/
noncomputable def collectiveTrueAux {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (M : Matrix (Fin r) (Fin (m + 1)) ℤ)
    (s : Fin r → Fin (m + 1)) (t : Fin d → Fin (m + 1))
    (N q : ℕ) (C : FeldmanIndex N q m → ℤ) (σ : ℕ) (τ : Fin d → ℕ) (z : ℂ) : ℂ :=
  ∑ kl, (C kl : ℂ) * feldmanJet N kl.1 σ z *
    collectiveGammaWeight M s t kl.expo τ * Complex.exp (z * (trueFreq p kl.expo : ℂ))

/-- Integer coefficient of the arithmetic jet equation. -/
def collectiveJetCoeff {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (M : Matrix (Fin r) (Fin (m + 1)) ℤ)
    (s : Fin r → Fin (m + 1)) (t : Fin d → Fin (m + 1))
    (N q S σ : ℕ) (τ : Fin d → ℕ) (x : ℕ) (kl : FeldmanIndex N q m) : ℤ :=
  ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℤ) *
    (∏ j, collectiveGamma M s (fun i => (kl.expo i : ℤ)) (t j) ^ τ j) *
      ∏ j, (p j : ℤ) ^ (kl.expo j * x)

/-- Clearing the single pivot determinant makes every free-direction weight integral. -/
theorem det_pow_mul_collectiveGammaWeight {r m d : ℕ}
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) (hdet : (M.submatrix id s).det ≠ 0)
    (l : Fin (m + 1) → ℕ) (τ : Fin d → ℕ) :
    ((M.submatrix id s).det : ℂ) ^ (∑ j, τ j) * collectiveGammaWeight M s t l τ =
      ((∏ j, collectiveGamma M s (fun i => (l i : ℤ)) (t j) ^ τ j : ℤ) : ℂ) := by
  have hD : ((M.submatrix id s).det : ℂ) ≠ 0 := by exact_mod_cast hdet
  rw [collectiveGammaWeight, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  simp only [Int.cast_prod, Int.cast_pow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hD)]

/-- Exact arithmetic identity for the collective jets. The common divisor
is the same Fel'dman divisor; the number of free directions is independent
of the number of prime frequencies. -/
theorem det_pow_mul_collectiveTrueAux_natCast {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (hp : ∀ j, 0 < p j)
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) (hdet : (M.submatrix id s).det ≠ 0)
    {N q S σ : ℕ} (C : FeldmanIndex N q m → ℤ) (hσ : σ < S)
    (τ : Fin d → ℕ) (x : ℕ) :
    ((M.submatrix id s).det : ℂ) ^ (∑ j, τ j) *
      collectiveTrueAux p M s t N q C σ τ (x : ℂ) =
        (feldmanDivisor (N + 1) S : ℂ) *
          ((∑ kl, collectiveJetCoeff p M s t N q S σ τ x kl * C kl : ℤ) : ℂ) := by
  rw [collectiveTrueAux, mul_sum, Int.cast_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro kl hkl
  have hk : (kl.1 : ℕ) ≤ N := Nat.lt_succ_iff.mp kl.1.isLt
  have hjet : feldmanJet N kl.1 σ (x : ℂ) =
      (feldmanDivisor (N + 1) S : ℂ) *
        ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℂ) := by
    rw [feldmanJet_natCast hk, ← Nat.cast_mul,
      Nat.mul_div_cancel' (feldmanDivisor_dvd_feldmanJetNat hσ x)]
  rw [hjet, exp_natCast_mul_trueFreq p hp kl.expo x]
  have hw := det_pow_mul_collectiveGammaWeight M s t hdet kl.expo τ
  simp only [collectiveJetCoeff, Int.cast_mul, Int.cast_natCast] at ⊢
  generalize (feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S) = jd
  generalize collectiveGammaWeight M s t kl.expo τ = w at hw ⊢
  linear_combination ((C kl : ℂ) * (feldmanDivisor (N + 1) S : ℂ) * (jd : ℂ) *
    ((∏ j, (p j : ℤ) ^ (kl.expo j * x) : ℤ) : ℂ)) * hw

/-- At jet order zero the collective companion retains every original frequency. -/
theorem collectiveTrueAux_zero {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (M : Matrix (Fin r) (Fin (m + 1)) ℤ)
    (s : Fin r → Fin (m + 1)) (t : Fin d → Fin (m + 1))
    {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (z : ℂ) :
    collectiveTrueAux p M s t N q C 0 0 z = feldmanTrueAux p 0 N q C 0 0 z := by
  simp only [collectiveTrueAux, feldmanTrueAux, collectiveGammaWeight, gammaWeight,
    Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one]

/-- A nonzero coefficient vector has a nonzero true value before the
full prime-frequency interpolation length, regardless of the jet dimension. -/
theorem exists_collectiveTrueAux_ne_zero {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (hC : C ≠ 0) :
    ∃ x : ℕ, x < (N + 1) * q ^ (m + 1) ∧
      collectiveTrueAux p M s t N q C 0 0 (x : ℂ) ≠ 0 := by
  by_contra h
  push Not at h
  apply hC
  apply eq_zero_of_feldmanTrueAux_eq_zero p 0 hp hprime C
  intro x hx
  rw [← collectiveTrueAux_zero p M s t C]
  exact h x hx


/-- The integer projected coordinates in an exponent box have size
at most `(r+1)q|det B|`. -/
theorem collectiveGamma_expo_bound {r m : ℕ}
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (hdet : (M.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤
      |(M.submatrix id s).det|)
    {N q : ℕ} (kl : FeldmanIndex N q m) (j : Fin (m + 1)) :
    |(collectiveGamma M s (fun i => (kl.expo i : ℤ)) j : ℝ)| ≤
      (r + 1 : ℝ) * q * |((M.submatrix id s).det : ℝ)| := by
  have hl (i : Fin (m + 1)) : |(((kl.expo i : ℕ) : ℤ) : ℝ)| ≤ (q : ℝ) := by
    simp only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (kl.expo i : ℝ) from Nat.cast_nonneg _)]
    exact_mod_cast (expo_lt kl i).le
  have h := collectiveGamma_div_bound M s hdet hmax (Nat.cast_nonneg q)
    (fun i => (kl.expo i : ℤ)) hl j
  have hD : 0 < |((M.submatrix id s).det : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hdet
  rwa [abs_div, div_le_iff₀ hD] at h

/-- Coefficient height of a collective arithmetic jet. Its derivative
factor depends on the free dimension through `|τ|`. -/
theorem abs_collectiveJetCoeff_le {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (hp : ∀ j, 1 ≤ p j)
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) (hdet : (M.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤
      |(M.submatrix id s).det|)
    {N q S σ : ℕ} (hσ : σ < S) (τ : Fin d → ℕ) (x : ℕ)
    (kl : FeldmanIndex N q m) :
    |(collectiveJetCoeff p M s t N q S σ τ x kl : ℝ)| ≤
      2 ^ N * ((x : ℝ) + N + 1) ^ N / (feldmanDivisor (N + 1) S : ℝ) *
        ((r + 1 : ℝ) * q * |((M.submatrix id s).det : ℝ)|) ^ (∑ j, τ j) *
          Real.exp (x * (q * totalLogSum p)) := by
  have hk : (kl.1 : ℕ) ≤ N := Nat.lt_succ_iff.mp kl.1.isLt
  have hD : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hjet : ((feldmanJetNat N kl.1 σ x / feldmanDivisor (N + 1) S : ℕ) : ℝ) =
      (feldmanJetNat N kl.1 σ x : ℝ) / feldmanDivisor (N + 1) S :=
    Nat.cast_div (feldmanDivisor_dvd_feldmanJetNat hσ x) hD.ne'
  have hjetle : (feldmanJetNat N kl.1 σ x : ℝ) ≤ 2 ^ N * ((x : ℝ) + N + 1) ^ N := by
    have h := norm_feldmanJet_le hk σ (x : ℂ)
    rwa [feldmanJet_natCast hk, Complex.norm_natCast, Complex.norm_natCast] at h
  have hprod : |((∏ j, collectiveGamma M s (fun i => (kl.expo i : ℤ)) (t j) ^ τ j : ℤ) : ℝ)| ≤
      ((r + 1 : ℝ) * q * |((M.submatrix id s).det : ℝ)|) ^ (∑ j, τ j) := by
    rw [Int.cast_prod, abs_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro j hj
    rw [Int.cast_pow, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (collectiveGamma_expo_bound M s hdet hmax kl _) _
  have hunit : (0 : ℝ) ≤ ((∏ j, (p j : ℤ) ^ (kl.expo j * x) : ℤ) : ℝ) := by positivity
  rw [collectiveJetCoeff, Int.cast_mul, Int.cast_mul, abs_mul, abs_mul, Int.cast_natCast,
    hjet, abs_of_nonneg hunit, abs_of_nonneg (by positivity)]
  exact mul_le_mul
    (mul_le_mul (div_le_div_of_nonneg_right hjetle hD.le) hprod (abs_nonneg _) (by positivity))
    (prod_pow_expo_le hp kl x) (by positivity) (by positivity)

/-- Uniform height bound for the initial arithmetic system. -/
noncomputable def collectiveJetHeight (r d N q S X : ℕ) (D W : ℝ) : ℝ :=
  2 ^ N * ((X : ℝ) + N + 1) ^ N / (feldmanDivisor (N + 1) S : ℝ) *
    ((r + 1 : ℝ) * q * |D|) ^ (d * S) * Real.exp (X * (q * W))

/-- The whole jet box has the height dictated by `dS`, without replacing
free dimension by the number of primes. -/
theorem abs_collectiveJetCoeff_le_height {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (hp : ∀ j, 1 ≤ p j)
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) (hdet : (M.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤
      |(M.submatrix id s).det|)
    {N q S X σ x : ℕ} (hq : 1 ≤ q) (hσ : σ < S) (hx : x < X)
    (τ : Fin d → ℕ) (hτ : ∀ j, τ j < S) (kl : FeldmanIndex N q m) :
    |(collectiveJetCoeff p M s t N q S σ τ x kl : ℝ)| ≤
      collectiveJetHeight r d N q S X ((M.submatrix id s).det : ℝ) (totalLogSum p) := by
  have hD1 : (1 : ℝ) ≤ |((M.submatrix id s).det : ℝ)| := by
    have h := abs_pos.mpr hdet
    have h1 : (1 : ℤ) ≤ |(M.submatrix id s).det| := by omega
    exact_mod_cast h1
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hbase : (1 : ℝ) ≤ (r + 1 : ℝ) * q * |((M.submatrix id s).det : ℝ)| :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 r) hqR) hD1
  have hτsum : (∑ j, τ j) ≤ d * S := by
    calc (∑ j, τ j) ≤ ∑ _j : Fin d, S := Finset.sum_le_sum fun j _ => (hτ j).le
      _ = d * S := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hW := totalLogSum_nonneg p hp
  have hxR : (x : ℝ) ≤ X := by exact_mod_cast hx.le
  refine (abs_collectiveJetCoeff_le p hp M s t hdet hmax hσ τ x kl).trans ?_
  unfold collectiveJetHeight
  have hfirst : 2 ^ N * ((x : ℝ) + N + 1) ^ N / (feldmanDivisor (N + 1) S : ℝ) ≤
      2 ^ N * ((X : ℝ) + N + 1) ^ N / (feldmanDivisor (N + 1) S : ℝ) := by gcongr
  have hpow := pow_le_pow_right₀ hbase hτsum
  have hexp : Real.exp ((x : ℝ) * (q * totalLogSum p)) ≤
      Real.exp ((X : ℝ) * (q * totalLogSum p)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxR (by positivity))
  exact mul_le_mul (mul_le_mul hfirst hpow (by positivity) (by positivity))
    hexp (by positivity) (by positivity)

/-- A collective jet box of at most half as many equations as coefficients
has a nonzero integer kernel vector of explicitly bounded height. -/
theorem exists_collective_jet_kernel {r m d : ℕ}
    (p : Fin (m + 1) → ℕ) (hp : ∀ j, 1 ≤ p j)
    (M : Matrix (Fin r) (Fin (m + 1)) ℤ) (s : Fin r → Fin (m + 1))
    (t : Fin d → Fin (m + 1)) (hdet : (M.submatrix id s).det ≠ 0)
    (hmax : ∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤
      |(M.submatrix id s).det|)
    {N q S X : ℕ} (hq : 1 ≤ q) (hX : 0 < X) (hS : 0 < S)
    (hcount : 2 * (X * S ^ (d + 1)) ≤ (N + 1) * q ^ (m + 1)) :
    ∃ C : FeldmanIndex N q m → ℤ, C ≠ 0 ∧
      (∀ x < X, ∀ σ < S, ∀ τ : Fin d → ℕ, (∀ j, τ j < S) →
        collectiveTrueAux p M s t N q C σ τ (x : ℂ) = 0) ∧
      ∀ kl, |(C kl : ℝ)| ≤ (((N + 1) * q ^ (m + 1) : ℕ) : ℝ) *
        max 1 (collectiveJetHeight r d N q S X ((M.submatrix id s).det : ℝ) (totalLogSum p)) := by
  classical
  let A : Matrix (Fin X × Fin S × (Fin d → Fin S)) (FeldmanIndex N q m) ℤ :=
    fun i kl => collectiveJetCoeff p M s t N q S i.2.1 (fun j => (i.2.2 j : ℕ)) i.1 kl
  have hrows : Fintype.card (Fin X × Fin S × (Fin d → Fin S)) = X * S ^ (d + 1) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ]
    ring
  have hcols := card_feldmanIndex (m := m) N q
  have hpos : 0 < Fintype.card (Fin X × Fin S × (Fin d → Fin S)) := by
    rw [hrows]
    positivity
  have hlt : Fintype.card (Fin X × Fin S × (Fin d → Fin S)) <
      Fintype.card (FeldmanIndex N q m) := by
    rw [hrows, hcols]
    have : 0 < X * S ^ (d + 1) := by positivity
    omega
  let V := collectiveJetHeight r d N q S X ((M.submatrix id s).det : ℝ) (totalLogSum p)
  have hV : 0 ≤ V := by unfold V collectiveJetHeight; positivity
  letI : SeminormedAddCommGroup (Matrix (Fin X × Fin S × (Fin d → Fin S))
      (FeldmanIndex N q m) ℤ) := Matrix.seminormedAddCommGroup
  obtain ⟨C, hC0, hCA, hCnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hlt hpos
  refine ⟨C, hC0, ?_, ?_⟩
  · intro x hx σ hσ τ hτ
    have hrow := congrFun hCA (⟨x, hx⟩, ⟨σ, hσ⟩, fun j => ⟨τ j, hτ j⟩)
    have hzero : ∑ kl, collectiveJetCoeff p M s t N q S σ τ x kl * C kl = 0 := by
      exact hrow
    have heq := det_pow_mul_collectiveTrueAux_natCast p (fun j => by have := hp j; omega)
      M s t hdet C hσ τ x
    rw [hzero, Int.cast_zero, mul_zero] at heq
    have hD : ((M.submatrix id s).det : ℂ) ≠ 0 := by exact_mod_cast hdet
    exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hD)
  · have hnormA : ‖A‖ ≤ V := (Matrix.norm_le_iff hV).mpr fun i kl => by
      rw [Int.norm_eq_abs]
      exact abs_collectiveJetCoeff_le_height p hp M s t hdet hmax hq i.2.1.isLt i.1.isLt
        (fun j => (i.2.2 j : ℕ)) (fun j => (i.2.2 j).isLt) kl
    set a := Fintype.card (Fin X × Fin S × (Fin d → Fin S))
    set b := Fintype.card (FeldmanIndex N q m)
    have hab : (a : ℝ) ≤ (b : ℝ) - a := by
      have hn : 2 * a ≤ b := by rw [hrows, hcols]; exact hcount
      have hnR : (2 : ℝ) * a ≤ b := by exact_mod_cast hn
      linarith only [hnR]
    have ha : (0 : ℝ) < a := by exact_mod_cast hpos
    have hden : (0 : ℝ) < (b : ℝ) - a := ha.trans_le hab
    have hexp : (a : ℝ) / ((b : ℝ) - a) ≤ 1 := (div_le_one hden).mpr hab
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast hpos.trans hlt
    have hbase : (1 : ℝ) ≤ (b : ℝ) * max 1 ‖A‖ :=
      one_le_mul_of_one_le_of_one_le hb (le_max_left _ _)
    have hC : ‖C‖ ≤ (b : ℝ) * max 1 V := by
      calc ‖C‖ ≤ ((b : ℝ) * max 1 ‖A‖) ^ ((a : ℝ) / ((b : ℝ) - a)) := hCnorm
        _ ≤ ((b : ℝ) * max 1 ‖A‖) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hexp
        _ = (b : ℝ) * max 1 ‖A‖ := Real.rpow_one _
        _ ≤ (b : ℝ) * max 1 V := mul_le_mul_of_nonneg_left (max_le_max le_rfl hnormA)
          (Nat.cast_nonneg _)
    intro kl
    rw [← hcols, ← Int.norm_eq_abs]
    exact (norm_le_pi_norm C kl).trans hC

/-- The explicit collective parameters close the integer-kernel count
at every positive coefficient-height scale. -/
theorem collectiveFeldmanParams_jet_count {k d W n : ℕ}
    (P : CollectiveFeldmanParams k d W) :
    2 * (P.c * n * P.S ^ (d + 1)) ≤ (P.a * n + 1) * P.q ^ k := by
  have h := Nat.mul_le_mul_right n P.siegel
  calc
    2 * (P.c * n * P.S ^ (d + 1)) = 2 * P.c * P.S ^ (d + 1) * n := by ring
    _ ≤ P.a * P.q ^ k * n := h
    _ = (P.a * n) * P.q ^ k := by ring
    _ ≤ (P.a * n + 1) * P.q ^ k := Nat.mul_le_mul_right _ (Nat.le_succ _)


private theorem exists_complement_columns {r d : ℕ}
    (s : Fin (r + 1) → Fin (d + r + 1)) (hs : Function.Injective s) :
    ∃ t : Fin d → Fin (d + r + 1), Function.Injective t ∧
      (∀ i j, s i ≠ t j) ∧
      ∀ j, (∃ i, s i = j) ∨ ∃ i, t i = j := by
  classical
  let F := {j : Fin (d + r + 1) // j ∉ Set.range s}
  have hsCard : Fintype.card (Set.range s) = r + 1 := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (Equiv.ofInjective s hs)).symm
  have hcard : Fintype.card F = d := by
    change Fintype.card ↑(Set.range s)ᶜ = _
    rw [Fintype.card_compl_set, hsCard, Fintype.card_fin]
    omega
  let e : Fin d ≃ F :=
    (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)).symm
  refine ⟨fun j => (e j).val, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i j hij
    exact (e j).property ⟨i, hij⟩
  · intro j
    by_cases hj : j ∈ Set.range s
    · exact Or.inl hj
    · right
      refine ⟨e.symm ⟨j, hj⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)

/-- An integral logarithmic mass bound for the actual prime family. -/
noncomputable def collectiveLogBound {m : ℕ} (p : Fin (m + 1) → ℕ) : ℕ :=
  ⌈totalLogSum p⌉₊ + 1

theorem totalLogSum_le_collectiveLogBound {m : ℕ} (p : Fin (m + 1) → ℕ) :
    totalLogSum p ≤ collectiveLogBound p := by
  have h := Nat.le_ceil (totalLogSum p)
  unfold collectiveLogBound
  push_cast
  linarith only [h]

/-- Every independent family of integer forms in distinct prime logarithms
has a nonzero bounded-height integral auxiliary with `d` free jet directions.
The parameters are explicit, the initial jets vanish exactly, and some true
value before the full interpolation length remains nonzero. -/
theorem exists_collective_auxiliary (d r : ℕ)
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p) (hprime : ∀ j, (p j).Prime)
    (M : Matrix (Fin (r + 1)) (Fin (d + r + 1)) ℤ)
    (hind : LinearIndependent ℚ (fun i j => (M i j : ℚ))) :
    ∃ P : CollectiveFeldmanParams (d + r + 1) d (collectiveLogBound p),
      ∃ s : Fin (r + 1) → Fin (d + r + 1), ∃ t : Fin d → Fin (d + r + 1),
        P.R = collectiveSteps (d + r + 1) (collectiveRootDegree d (r + 1)) (collectiveLogBound p) ∧
        P.q = (1000 * collectiveLogBound p * (d + r + 1) * (P.R + 1)) ^
          collectiveRootDegree d (r + 1) * (P.R + 1) ∧
        P.M = 1000 * collectiveLogBound p * ((d + r + 1) * P.q) ∧
        P.c = 16 * (d + r + 1) * (P.R + 1) * ((d + r + 1) * P.q) ∧
        P.a = 2 * P.c * (1000 * collectiveLogBound p * (d + r + 1) * (P.R + 1)) ^
          collectiveRootDegree d (r + 1) ∧
        Function.Injective s ∧ Function.Injective t ∧
        (∀ i j, s i ≠ t j) ∧ (∀ j, (∃ i, s i = j) ∨ ∃ i, t i = j) ∧
        (M.submatrix id s).det ≠ 0 ∧
        (∀ i j, |(M.submatrix id s).cramer (fun h => M h j) i| ≤ |(M.submatrix id s).det|) ∧
        ∀ n : ℕ, 1 ≤ n → ∃ C : FeldmanIndex (P.a * n) P.q (d + r) → ℤ,
          C ≠ 0 ∧
          (∀ x < P.c * n, ∀ σ < P.S, ∀ τ : Fin d → ℕ, (∀ j, τ j < P.S) →
            collectiveTrueAux p M s t (P.a * n) P.q C σ τ (x : ℂ) = 0) ∧
          (∃ x : ℕ, x < (P.a * n + 1) * P.q ^ (d + r + 1) ∧
            collectiveTrueAux p M s t (P.a * n) P.q C 0 0 (x : ℂ) ≠ 0) ∧
          ∀ kl, |(C kl : ℝ)| ≤ (((P.a * n + 1) * P.q ^ (d + r + 1) : ℕ) : ℝ) *
            max 1 (collectiveJetHeight (r + 1) d (P.a * n) P.q P.S (P.c * n)
              ((M.submatrix id s).det : ℝ) (totalLogSum p)) := by
  have hW : 1 ≤ collectiveLogBound p := Nat.le_add_left 1 _
  obtain ⟨P, hPR, hPq, hPM, hPc, hPa⟩ := exists_collectiveFeldmanParams d (r + 1) (collectiveLogBound p)
    (Nat.le_add_left 1 r) hW
  obtain ⟨s, hdet, hmax⟩ := exists_bounded_cramer_minor M hind
  have hs : Function.Injective s := by
    intro i j hij
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne (fun a => congrArg (M a) hij))
  obtain ⟨t, ht, hst, hcover⟩ := exists_complement_columns s hs
  refine ⟨P, s, t, hPR, hPq, hPM, hPc, hPa, hs, ht, hst, hcover, hdet, hmax, ?_⟩
  intro n hn
  have hX : 0 < P.c * n := Nat.mul_pos P.one_le_c hn
  have hS : 0 < P.S := by rw [P.S_eq]; omega
  obtain ⟨C, hC0, hvan, hheight⟩ := exists_collective_jet_kernel p
    (fun j => (hprime j).one_lt.le) M s t hdet hmax P.one_le_q hX hS
      (collectiveFeldmanParams_jet_count P)
  exact ⟨C, hC0, hvan, exists_collectiveTrueAux_ne_zero p hp hprime M s t C hC0, hheight⟩

end GaloisForLFunctions.CollectiveDiophantineGeometry
