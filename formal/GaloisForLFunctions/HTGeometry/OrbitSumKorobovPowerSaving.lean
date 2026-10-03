import GaloisForLFunctions.HTGeometry.OrbitSumIteratedDifferencing
import GaloisForLFunctions.HTGeometry.OrbitSumKorobovParameters

/-!
# Korobov's power saving for orbit sums modulo odd numbers

Let the primes of a finite set `S` be odd and divide `g − 1`, and fix `r ≥ 1` and `c ≥ 1`.  For
every modulus `Q` with prime factors in `S`, every `u` prime to `Q` and every length `L` with
`L^r ≤ c Q`, `norm_sum_orbit_le` gives

`‖Σ_{i<L} e(u gⁱ/Q)‖ ≤ K Q^{θ_r}` with `θ_r = 1/r − 2^{−r}/(r(r+1))`,

and `K` depends only on `S`, `g`, `r` and `c`.  The proof combines the iterated-differencing bound
(`norm_sum_orbit_sq_le_korobov`) with the parameters of `exists_korobov_parameters`.  It uses the
general estimate `β_d ≤ 5ᵈ (ε + ε^{2^{−d}})` (`korobovBeta_le_general`) and two real-variable error
terms (`termA_le`, `termB_le`).
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.OrbitPowerSaving

open StonehamParityDrift ThreeFiveOrbit OrbitDifferencing OrbitVanishing

theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact Real.rpow_add_le_add_rpow ha hb (by norm_num) (by norm_num)

/-- `β_d ≤ 5ᵈ (ε + ε^{2^{−d}})` for every `ε = N^{r−1}/D + 1/N`, with no size condition. -/
theorem korobovBeta_le_general {N D r : ℕ} (hN : 0 < N) (hD : 0 < D) (d : ℕ) :
    korobovBeta N D r d ≤ 5 ^ d * (((N : ℝ) ^ (r - 1) / D + 1 / N) +
      ((N : ℝ) ^ (r - 1) / D + 1 / N) ^ ((1 / 2 : ℝ) ^ d)) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (N : ℝ) ^ (r - 1) / D + 1 / N := ⟨_, rfl⟩
  rw [← hεdef]
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hNε : 1 / (N : ℝ) ≤ ε := by
    have : (0 : ℝ) ≤ (N : ℝ) ^ (r - 1) / D := by positivity
    rw [hεdef]
    linarith
  induction d with
  | zero =>
    simp only [korobovBeta, pow_zero, Real.rpow_one, one_mul]
    rw [← hεdef]
    linarith
  | succ d ih =>
    simp only [korobovBeta]
    have ha : (0 : ℝ) ≤ ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by positivity
    have hsq_le : Real.sqrt ε ≤ ε + ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by
      rcases le_total ε 1 with h1 | h1
      · rw [Real.sqrt_eq_rpow]
        have : ε ^ (1 / 2 : ℝ) ≤ ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by
          rcases eq_or_lt_of_le hε0 with h0 | h0
          · rw [← h0, Real.zero_rpow (by norm_num), Real.zero_rpow (by positivity)]
          · have hz : ((1 : ℝ) / 2) ^ (d + 1) ≤ 1 / 2 := by
              calc ((1 : ℝ) / 2) ^ (d + 1) = (1 / 2) ^ d * (1 / 2) := pow_succ _ _
                _ ≤ 1 * (1 / 2) := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
                _ = 1 / 2 := one_mul _
            exact Real.rpow_le_rpow_of_exponent_ge h0 h1 hz
        linarith
      · have : Real.sqrt ε ≤ ε := by
          rw [Real.sqrt_le_left hε0]; nlinarith
        linarith
    have hpow : Real.sqrt (ε ^ ((1 / 2 : ℝ) ^ d)) = ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε0, pow_succ]
    have h5 : Real.sqrt ((5 : ℝ) ^ d) ≤ 5 ^ d := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 5) (n := d)]
    have hs : Real.sqrt (korobovBeta N D r d) ≤
        5 ^ d * (Real.sqrt ε + ε ^ ((1 / 2 : ℝ) ^ (d + 1))) := by
      calc Real.sqrt (korobovBeta N D r d) ≤ Real.sqrt (5 ^ d * (ε + ε ^ ((1 / 2 : ℝ) ^ d))) :=
            Real.sqrt_le_sqrt ih
        _ = Real.sqrt (5 ^ d) * Real.sqrt (ε + ε ^ ((1 / 2 : ℝ) ^ d)) :=
            Real.sqrt_mul (by positivity) _
        _ ≤ 5 ^ d * (Real.sqrt ε + ε ^ ((1 / 2 : ℝ) ^ (d + 1))) := by
            gcongr
            rw [← hpow]
            exact sqrt_add_le _ _ hε0 (by positivity)
    have h51 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    calc 1 / (N : ℝ) + 2 * Real.sqrt (korobovBeta N D r d)
        ≤ ε + 2 * (5 ^ d * (Real.sqrt ε + ε ^ ((1 / 2 : ℝ) ^ (d + 1)))) := by gcongr
      _ ≤ ε + 2 * (5 ^ d * (ε + 2 * ε ^ ((1 / 2 : ℝ) ^ (d + 1)))) := by
          have key : Real.sqrt ε + ε ^ ((1 / 2 : ℝ) ^ (d + 1)) ≤
              ε + 2 * ε ^ ((1 / 2 : ℝ) ^ (d + 1)) := by linarith [hsq_le]
          nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 5 ^ d)]
      _ ≤ 5 ^ (d + 1) * (ε + ε ^ ((1 / 2 : ℝ) ^ (d + 1))) := by
          rw [pow_succ (5 : ℝ) d]
          nlinarith [mul_nonneg (sub_nonneg.mpr h51) ha, mul_nonneg (sub_nonneg.mpr h51) hε0]

/-! ### The real-variable core -/

/-- `x ≤ y^{1/n}` from `xⁿ ≤ y`. -/
theorem le_rpow_inv_of_pow_le {x y : ℝ} {n : ℕ} (hn : n ≠ 0) (hx : 0 ≤ x) (h : x ^ n ≤ y) :
    x ≤ y ^ ((n : ℝ)⁻¹) := by
  calc x = (x ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hx hn).symm
    _ ≤ y ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)

/-- `y^{1/n} ≤ x` from `y ≤ xⁿ`. -/
theorem rpow_inv_le_of_le_pow {x y : ℝ} {n : ℕ} (hn : n ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : y ≤ x ^ n) : y ^ ((n : ℝ)⁻¹) ≤ x := by
  calc y ^ ((n : ℝ)⁻¹) ≤ (x ^ n) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hy h (by positivity)
    _ = x := Real.pow_rpow_inv_natCast hx hn

/-- **The first error term.**  With `T N ≤ L`, `L^r ≤ c Q` and `Q^r ≤ C₀ (T^{r−1} D)^{r+1}`,
`T N (N^{r−1}/D)^s ≤ c^{(1+(r−1)s)/r} C₀^{s/(r+1)} Q^{1/r − s/(r(r+1))}`. -/
theorem termA_le {T N D L Q c C₀ s : ℝ} {r : ℕ} (hr : 1 ≤ r) (hT : 0 < T) (hN : 0 < N)
    (hD : 0 < D) (hQ : 0 < Q) (hc : 0 < c) (hC₀ : 0 < C₀) (hs : 0 ≤ s) (hTN : T * N ≤ L)
    (hLQ : L ^ r ≤ c * Q) (hTD : Q ^ r ≤ C₀ * (T ^ (r - 1) * D) ^ (r + 1)) :
    T * N * (N ^ (r - 1) / D) ^ s ≤
      c ^ ((1 + ((r - 1 : ℕ) : ℝ) * s) / r) * C₀ ^ (s / (r + 1)) *
        Q ^ (1 / (r : ℝ) - s / (r * (r + 1))) := by
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hT hN) hTN
  have hr0 : (r : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ r := by exact_mod_cast hr
                               linarith
  set x : ℝ := ((r - 1 : ℕ) : ℝ) * s with hx
  have hx0 : 0 ≤ x := by positivity
  have hTDp : 0 < T ^ (r - 1) * D := by positivity
  have h1 : N ≤ L / T := (le_div_iff₀ hT).mpr (by linarith)
  -- `T N (N^{r−1}/D)^s ≤ L^{1+x} / (T^{r−1} D)^s`
  have hA : T * N * (N ^ (r - 1) / D) ^ s ≤ L ^ (1 + x) / (T ^ (r - 1) * D) ^ s := by
    have e1 : (N ^ (r - 1) / D) ^ s = N ^ x / D ^ s := by
      rw [Real.div_rpow (by positivity) hD.le, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    have e2 : (T ^ (r - 1) * D) ^ s = T ^ x * D ^ s := by
      rw [Real.mul_rpow (by positivity) hD.le, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    have e3 : L ^ (1 + x) = L * L ^ x := by rw [Real.rpow_add hL, Real.rpow_one]
    rw [e1, e2, e3]
    have h3 : N ^ x ≤ (L / T) ^ x := Real.rpow_le_rpow hN.le h1 hx0
    rw [Real.div_rpow hL.le hT.le] at h3
    have hTx : 0 < T ^ x := Real.rpow_pos_of_pos hT x
    have hDs : 0 < D ^ s := Real.rpow_pos_of_pos hD s
    calc T * N * (N ^ x / D ^ s) = (T * N * N ^ x) / D ^ s := by ring
      _ ≤ (L * (L ^ x / T ^ x)) / D ^ s := by gcongr
      _ = L * L ^ x / (T ^ x * D ^ s) := by field_simp
  -- `L ≤ (cQ)^{1/r}` and `(Q^r/C₀)^{1/(r+1)} ≤ T^{r−1} D`
  have h4 : L ≤ (c * Q) ^ ((r : ℝ)⁻¹) := le_rpow_inv_of_pow_le (by omega) hL.le hLQ
  have h5 : (Q ^ r / C₀) ^ (((r + 1 : ℕ) : ℝ)⁻¹) ≤ T ^ (r - 1) * D :=
    rpow_inv_le_of_le_pow (by omega) hTDp.le (by positivity)
      (by rw [div_le_iff₀ hC₀]; linarith)
  have h6 : L ^ (1 + x) ≤ (c * Q) ^ ((1 + x) / r) := by
    calc L ^ (1 + x) ≤ ((c * Q) ^ ((r : ℝ)⁻¹)) ^ (1 + x) :=
          Real.rpow_le_rpow hL.le h4 (by positivity)
      _ = (c * Q) ^ ((1 + x) / r) := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; field_simp
  have h7 : (Q ^ r / C₀) ^ (s / (r + 1)) ≤ (T ^ (r - 1) * D) ^ s := by
    calc (Q ^ r / C₀) ^ (s / (r + 1)) = ((Q ^ r / C₀) ^ (((r + 1 : ℕ) : ℝ)⁻¹)) ^ s := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; push_cast; field_simp
      _ ≤ (T ^ (r - 1) * D) ^ s := Real.rpow_le_rpow (by positivity) h5 hs
  have hpos : 0 < (Q ^ r / C₀) ^ (s / (r + 1)) := Real.rpow_pos_of_pos (by positivity) _
  refine hA.trans ?_
  calc L ^ (1 + x) / (T ^ (r - 1) * D) ^ s
        ≤ (c * Q) ^ ((1 + x) / r) / (Q ^ r / C₀) ^ (s / (r + 1)) :=
        div_le_div₀ (by positivity) h6 hpos h7
    _ = c ^ ((1 + x) / r) * C₀ ^ (s / (r + 1)) * Q ^ (1 / (r : ℝ) - s / (r * (r + 1))) := by
        rw [Real.mul_rpow hc.le hQ.le, Real.div_rpow (by positivity) hC₀.le,
          ← Real.rpow_natCast Q r, ← Real.rpow_mul hQ.le]
        have hexp : 1 / (r : ℝ) - s / (r * (r + 1)) = (1 + x) / r - r * (s / (r + 1)) := by
          rw [hx, Nat.cast_sub hr]
          field_simp
          ring
        rw [hexp, Real.rpow_sub hQ]
        field_simp

/-- **The second error term.**  With `T N ≤ L`, `L^r ≤ c Q` and `T^{r+1} ≤ Q P^r`,
`T N (1/N)^s ≤ c^{(1−s)/r} (P^r)^{s/(r+1)} Q^{1/r − s/(r(r+1))}` for `0 ≤ s ≤ 1`. -/
theorem termB_le {T N L Q c P s : ℝ} {r : ℕ} (hr : 1 ≤ r) (hT : 0 < T) (hN : 0 < N)
    (hQ : 0 < Q) (hc : 0 < c) (hP : 0 < P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hTN : T * N ≤ L)
    (hLQ : L ^ r ≤ c * Q) (hTQ : T ^ (r + 1) ≤ Q * P ^ r) :
    T * N * (1 / N) ^ s ≤
      c ^ ((1 - s) / r) * (P ^ r) ^ (s / (r + 1)) * Q ^ (1 / (r : ℝ) - s / (r * (r + 1))) := by
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hT hN) hTN
  have hr0 : (r : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ r := by exact_mod_cast hr
                               linarith
  have h1 : N ≤ L / T := (le_div_iff₀ hT).mpr (by linarith)
  -- `T N (1/N)^s = T N^{1−s} ≤ T^s L^{1−s}`
  have hA : T * N * (1 / N) ^ s ≤ T ^ s * L ^ (1 - s) := by
    have e1 : T * N * (1 / N) ^ s = T * N ^ (1 - s) := by
      rw [Real.div_rpow zero_le_one hN.le, Real.one_rpow, Real.rpow_sub hN, Real.rpow_one]
      field_simp
    rw [e1]
    have h3 : N ^ (1 - s) ≤ (L / T) ^ (1 - s) := Real.rpow_le_rpow hN.le h1 (by linarith)
    rw [Real.div_rpow hL.le hT.le, Real.rpow_sub hT, Real.rpow_one] at h3
    calc T * N ^ (1 - s) ≤ T * (L ^ (1 - s) / (T / T ^ s)) := by gcongr
      _ = T ^ s * L ^ (1 - s) := by
          have : 0 < T ^ s := Real.rpow_pos_of_pos hT s
          field_simp
  have h4 : L ≤ (c * Q) ^ ((r : ℝ)⁻¹) := le_rpow_inv_of_pow_le (by omega) hL.le hLQ
  have h5 : T ≤ (Q * P ^ r) ^ (((r + 1 : ℕ) : ℝ)⁻¹) := le_rpow_inv_of_pow_le (by omega) hT.le hTQ
  have h6 : L ^ (1 - s) ≤ (c * Q) ^ ((1 - s) / r) := by
    calc L ^ (1 - s) ≤ ((c * Q) ^ ((r : ℝ)⁻¹)) ^ (1 - s) :=
          Real.rpow_le_rpow hL.le h4 (by linarith)
      _ = (c * Q) ^ ((1 - s) / r) := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; field_simp
  have h7 : T ^ s ≤ (Q * P ^ r) ^ (s / (r + 1)) := by
    calc T ^ s ≤ ((Q * P ^ r) ^ (((r + 1 : ℕ) : ℝ)⁻¹)) ^ s := Real.rpow_le_rpow hT.le h5 hs0
      _ = (Q * P ^ r) ^ (s / (r + 1)) := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; push_cast; field_simp
  refine hA.trans ?_
  calc T ^ s * L ^ (1 - s) ≤ (Q * P ^ r) ^ (s / (r + 1)) * (c * Q) ^ ((1 - s) / r) :=
        mul_le_mul h7 h6 (by positivity) (by positivity)
    _ = c ^ ((1 - s) / r) * (P ^ r) ^ (s / (r + 1)) * Q ^ (1 / (r : ℝ) - s / (r * (r + 1))) := by
        rw [Real.mul_rpow hQ.le (by positivity), Real.mul_rpow hc.le hQ.le]
        have hexp : 1 / (r : ℝ) - s / (r * (r + 1)) = s / (r + 1) + (1 - s) / r := by
          field_simp
          ring
        rw [hexp, Real.rpow_add hQ]
        ring

/-! ### The uniform power saving -/

/-- The power-saving exponent `θ_r = 1/r − 2^{−r}/(r(r+1))`. -/
noncomputable def savingExponent (r : ℕ) : ℝ := 1 / (r : ℝ) - (1 / 2 : ℝ) ^ r / (r * (r + 1))

theorem exponent_le_savingExponent {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : (1 / 2 : ℝ) ^ r ≤ s) :
    1 / (r : ℝ) - s / (r * (r + 1)) ≤ savingExponent r := by
  unfold savingExponent
  have : (0 : ℝ) < r * (r + 1) := by positivity
  gcongr

theorem inv_succ_le_savingExponent {r : ℕ} (hr : 1 ≤ r) :
    1 / ((r : ℝ) + 1) ≤ savingExponent r := by
  unfold savingExponent
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : (1 / 2 : ℝ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < r * (r + 1) := by positivity
  rw [show 1 / (r : ℝ) - (1 / 2 : ℝ) ^ r / (r * (r + 1)) =
      ((r + 1) - (1 / 2 : ℝ) ^ r) / (r * (r + 1)) by field_simp,
    div_le_div_iff₀ (by positivity) hpos]
  nlinarith

/-- `√β_{r−1} ≤ 5^r (A^{1/2} + B^{1/2} + A^a + B^a)` with `A = N^{r−1}/D`, `B = 1/N`,
`a = 2^{−r}`. -/
theorem sqrt_korobovBeta_le {N D r : ℕ} (hN : 0 < N) (hD : 0 < D) (hr : 1 ≤ r) :
    Real.sqrt (korobovBeta N D r (r - 1)) ≤
      5 ^ r * (((N : ℝ) ^ (r - 1) / D) ^ (1 / 2 : ℝ) + (1 / (N : ℝ)) ^ (1 / 2 : ℝ) +
        ((N : ℝ) ^ (r - 1) / D) ^ ((1 / 2 : ℝ) ^ r) + (1 / (N : ℝ)) ^ ((1 / 2 : ℝ) ^ r)) := by
  have hβ := korobovBeta_le_general (r := r) hN hD (r - 1)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (N : ℝ) ^ (r - 1) / D := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 / (N : ℝ) := ⟨_, rfl⟩
  rw [← hA, ← hB] at hβ ⊢
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set a : ℝ := (1 / 2 : ℝ) ^ r with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have e : ((1 / 2 : ℝ) ^ (r - 1)) * (1 / 2) = a := by
    rw [ha, ← pow_succ]; congr 1; omega
  have h5 : Real.sqrt ((5 : ℝ) ^ (r - 1)) ≤ 5 ^ r := by
    rw [Real.sqrt_le_left (by positivity)]
    calc (5 : ℝ) ^ (r - 1) ≤ 5 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (5 ^ r) ^ 2 := by nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 5) (n := r)]
  have hs1 : Real.sqrt (A + B) ≤ A ^ (1 / 2 : ℝ) + B ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_add_le_add_rpow hA0 hB0 (by norm_num) (by norm_num)
  have hs2 : Real.sqrt ((A + B) ^ ((1 / 2 : ℝ) ^ (r - 1))) ≤ A ^ a + B ^ a := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), e]
    exact Real.rpow_add_le_add_rpow hA0 hB0 ha0 ha1
  calc Real.sqrt (korobovBeta N D r (r - 1))
      ≤ Real.sqrt (5 ^ (r - 1) * ((A + B) + (A + B) ^ ((1 / 2 : ℝ) ^ (r - 1)))) :=
        Real.sqrt_le_sqrt hβ
    _ = Real.sqrt (5 ^ (r - 1)) *
          Real.sqrt ((A + B) + (A + B) ^ ((1 / 2 : ℝ) ^ (r - 1))) :=
        Real.sqrt_mul (by positivity) _
    _ ≤ 5 ^ r * (Real.sqrt (A + B) + Real.sqrt ((A + B) ^ ((1 / 2 : ℝ) ^ (r - 1)))) := by
        gcongr
        exact sqrt_add_le _ _ (by positivity) (by positivity)
    _ ≤ 5 ^ r * (A ^ (1 / 2 : ℝ) + B ^ (1 / 2 : ℝ) + A ^ a + B ^ a) :=
        mul_le_mul_of_nonneg_left (by linarith [hs1, hs2]) (by positivity)

/-- The constant of the uniform bound. -/
noncomputable def savingConst (S : Finset ℕ) (g r : ℕ) (c : ℝ) : ℝ :=
  let P : ℝ := ((∏ p ∈ S, p : ℕ) : ℝ)
  let C₀ : ℝ := (((g - 1) ^ ((r + 1) ^ 2) * (∏ p ∈ S, p) ^ (r ^ 2) : ℕ) : ℝ)
  let sA : ℝ → ℝ := fun s => c ^ ((1 + ((r - 1 : ℕ) : ℝ) * s) / r) * C₀ ^ (s / (r + 1))
  let sB : ℝ → ℝ := fun s => c ^ ((1 - s) / r) * (P ^ r) ^ (s / (r + 1))
  (P ^ r) ^ (((r + 1 : ℕ) : ℝ)⁻¹) +
    5 ^ r * (sA (1 / 2) + sB (1 / 2) + sA ((1 / 2) ^ r) + sB ((1 / 2) ^ r))

/-- **Korobov's power saving for odd moduli.**  Let the primes of the finite set `S` be odd and
divide `g − 1`, `r ≥ 1`, `c ≥ 1`.  For every `Q ≠ 0` with prime factors in `S`, every `u` prime to
`Q` and every `L` with `L^r ≤ c Q`, `‖Σ_{i<L} e(u gⁱ/Q)‖ ≤ K Q^{θ_r}` with
`θ_r = 1/r − 2^{−r}/(r(r+1))` and `K = savingConst S g r c`. -/
theorem norm_sum_orbit_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) {g : ℕ}
    (hg : 2 ≤ g) (hgS : ∀ p ∈ S, p ∣ g - 1) {r : ℕ} (hr : 1 ≤ r) {c : ℝ} (hc : 1 ≤ c)
    {Q : ℕ} (hQ : Q ≠ 0) (hQS : Q.primeFactors ⊆ S) {u : ℤ} (hu : IsCoprime u (Q : ℤ)) {L : ℕ}
    (hLQ : (L : ℝ) ^ r ≤ c * Q) :
    ‖∑ i ∈ range L, ephase Q (u * (g : ℤ) ^ i)‖ ≤
      savingConst S g r c * (Q : ℝ) ^ savingExponent r := by
  set P : ℝ := ((∏ p ∈ S, p : ℕ) : ℝ) with hP
  set C₀ : ℝ := (((g - 1) ^ ((r + 1) ^ 2) * (∏ p ∈ S, p) ^ (r ^ 2) : ℕ) : ℝ) with hC₀
  have hP1 : 1 ≤ P := by
    rw [hP]; exact_mod_cast Finset.prod_pos fun p hp => (hS p hp).1.pos
  have hC₀1 : 1 ≤ C₀ := by
    rw [hC₀]
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) _)
      (pow_pos (Finset.prod_pos fun p hp => (hS p hp).1.pos) _)
  set a : ℝ := (1 / 2 : ℝ) ^ r with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 / 2 := by
    rw [ha]
    calc (1 / 2 : ℝ) ^ r ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
      _ = 1 / 2 := pow_one _
  set sA : ℝ → ℝ := fun s => c ^ ((1 + ((r - 1 : ℕ) : ℝ) * s) / r) * C₀ ^ (s / (r + 1)) with hsA
  set sB : ℝ → ℝ := fun s => c ^ ((1 - s) / r) * (P ^ r) ^ (s / (r + 1)) with hsB
  set Kt : ℝ := (P ^ r) ^ (((r + 1 : ℕ) : ℝ)⁻¹) with hKt
  have hconst : savingConst S g r c = Kt + 5 ^ r * (sA (1 / 2) + sB (1 / 2) + sA a + sB a) := rfl
  rw [hconst]
  obtain ⟨T₀, D, hT0, hD0, hDX, hQX, hZ, hQT, hTQ, hQD⟩ :=
    exists_korobov_parameters hS hg hgS hQ hQS hr hu
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hTr : (0 : ℝ) < T₀ := by exact_mod_cast hT0
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD0
  have hc0 : (0 : ℝ) < c := by linarith
  set Qθ : ℝ := (Q : ℝ) ^ savingExponent r with hQθ
  have hQθ0 : 0 ≤ Qθ := by positivity
  have hθ : ∀ s, a ≤ s → (Q : ℝ) ^ (1 / (r : ℝ) - s / (r * (r + 1))) ≤ Qθ :=
    fun s hs => Real.rpow_le_rpow_of_exponent_le hQr (exponent_le_savingExponent hr hs)
  have hTQr : (T₀ : ℝ) ^ (r + 1) ≤ Q * P ^ r := by rw [hP]; exact_mod_cast hTQ
  have hT₀le : (T₀ : ℝ) ≤ Kt * Qθ := by
    calc (T₀ : ℝ) ≤ (Q * P ^ r) ^ (((r + 1 : ℕ) : ℝ)⁻¹) :=
          le_rpow_inv_of_pow_le (by omega) hTr.le hTQr
      _ = (Q : ℝ) ^ (1 / ((r : ℝ) + 1)) * Kt := by
          rw [Real.mul_rpow hQ0.le (by positivity), hKt]; push_cast; ring_nf
      _ ≤ Qθ * Kt := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hQr (inv_succ_le_savingExponent hr)) (by positivity)
      _ = Kt * Qθ := mul_comm _ _
  have hK0 : 0 ≤ 5 ^ r * (sA (1 / 2) + sB (1 / 2) + sA a + sB a) := by positivity
  obtain ⟨N, hN⟩ : ∃ N, N = L / T₀ := ⟨_, rfl⟩
  have hL : L = T₀ * N + L % T₀ := by rw [hN]; exact (Nat.div_add_mod L T₀).symm
  have hrest : ‖∑ m ∈ range (L % T₀), ephase Q (u * (g : ℤ) ^ (T₀ * N + m))‖ ≤ T₀ := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_ephase, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (Nat.mod_lt L hT0).le
  have hsplit : ‖∑ i ∈ range L, ephase Q (u * (g : ℤ) ^ i)‖ ≤
      ‖∑ i ∈ range (T₀ * N), ephase Q (u * (g : ℤ) ^ i)‖ + T₀ := by
    conv_lhs => rw [hL, sum_range_add]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hrest)
  refine hsplit.trans ?_
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · rw [hN0, mul_zero, sum_range_zero, norm_zero, zero_add]
    nlinarith [mul_nonneg hK0 hQθ0]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hK := norm_sum_orbit_sq_le_korobov (Q := Q) (T₀ := T₀) (D := D) (N := N) (r := r)
    (g := (g : ℤ)) (X := (g : ℤ) ^ T₀ - 1) (u := u) hQ hD0 hNpos hr hDX hQX (by ring) hZ
  have hsq := sqrt_korobovBeta_le hNpos hD0 hr
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (N : ℝ) ^ (r - 1) / D := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 / (N : ℝ) := ⟨_, rfl⟩
  rw [← hA, ← hB, ← ha] at hsq
  have hblock : ‖∑ i ∈ range (T₀ * N), ephase Q (u * (g : ℤ) ^ i)‖ ≤
      T₀ * N * (5 ^ r * (A ^ (1 / 2 : ℝ) + B ^ (1 / 2 : ℝ) + A ^ a + B ^ a)) := by
    have h1 : ‖∑ i ∈ range (T₀ * N), ephase Q (u * (g : ℤ) ^ i)‖ ≤
        T₀ * N * Real.sqrt (korobovBeta N D r (r - 1)) := by
      have hTN : (0 : ℝ) ≤ T₀ * N := by positivity
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hTN, ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt (hK.trans (le_of_eq ?_))
      ring
    exact h1.trans (by gcongr)
  have hTNL : (T₀ : ℝ) * N ≤ L := by rw [hN]; exact_mod_cast Nat.mul_div_le L T₀
  have hTD : (Q : ℝ) ^ r ≤ C₀ * ((T₀ : ℝ) ^ (r - 1) * D) ^ (r + 1) := by
    have h1 : (Q : ℝ) ≤ (T₀ : ℝ) ^ (r + 1) := by exact_mod_cast hQT
    have h2 : (Q : ℝ) ≤ C₀ * (D : ℝ) ^ (r + 1) := by rw [hC₀]; exact_mod_cast hQD
    calc (Q : ℝ) ^ r = (Q : ℝ) ^ (r - 1) * Q := by rw [← pow_succ]; congr 1; omega
      _ ≤ ((T₀ : ℝ) ^ (r + 1)) ^ (r - 1) * (C₀ * (D : ℝ) ^ (r + 1)) := by gcongr
      _ = C₀ * ((T₀ : ℝ) ^ (r - 1) * D) ^ (r + 1) := by ring
  have tA : ∀ s, 0 ≤ s → a ≤ s → (T₀ : ℝ) * N * A ^ s ≤ sA s * Qθ := by
    intro s hs0 hs
    rw [hA]
    refine (termA_le hr hTr hNr hDr hQ0 hc0 (by linarith) hs0 hTNL hLQ hTD).trans ?_
    exact mul_le_mul_of_nonneg_left (hθ s hs)
      (by positivity : (0 : ℝ) ≤ c ^ ((1 + ((r - 1 : ℕ) : ℝ) * s) / r) * C₀ ^ (s / (r + 1)))
  have tB : ∀ s, 0 ≤ s → s ≤ 1 → a ≤ s → (T₀ : ℝ) * N * B ^ s ≤ sB s * Qθ := by
    intro s hs0 hs1 hs
    rw [hB]
    refine (termB_le hr hTr hNr hQ0 hc0 (by linarith) hs0 hs1 hTNL hLQ hTQr).trans ?_
    exact mul_le_mul_of_nonneg_left (hθ s hs)
      (by positivity : (0 : ℝ) ≤ c ^ ((1 - s) / r) * (P ^ r) ^ (s / (r + 1)))
  have h1 := tA (1 / 2) (by norm_num) ha1
  have h2 := tB (1 / 2) (by norm_num) (by norm_num) ha1
  have h3 := tA a ha0 le_rfl
  have h4 := tB a ha0 (by linarith) le_rfl
  have hsum : (T₀ : ℝ) * N * (5 ^ r * (A ^ (1 / 2 : ℝ) + B ^ (1 / 2 : ℝ) + A ^ a + B ^ a)) ≤
      5 ^ r * (sA (1 / 2) + sB (1 / 2) + sA a + sB a) * Qθ := by
    have e : (T₀ : ℝ) * N * (5 ^ r * (A ^ (1 / 2 : ℝ) + B ^ (1 / 2 : ℝ) + A ^ a + B ^ a)) =
        5 ^ r * ((T₀ * N * A ^ (1 / 2 : ℝ)) + (T₀ * N * B ^ (1 / 2 : ℝ)) + (T₀ * N * A ^ a) +
          (T₀ * N * B ^ a)) := by ring
    rw [e]
    calc (5 : ℝ) ^ r * ((T₀ * N * A ^ (1 / 2 : ℝ)) + (T₀ * N * B ^ (1 / 2 : ℝ)) +
          (T₀ * N * A ^ a) + (T₀ * N * B ^ a))
        ≤ 5 ^ r * ((sA (1 / 2) + sB (1 / 2) + sA a + sB a) * Qθ) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 5 ^ r * (sA (1 / 2) + sB (1 / 2) + sA a + sB a) * Qθ := by ring
  linarith

end GaloisForLFunctions.HTGeometry.OrbitPowerSaving
