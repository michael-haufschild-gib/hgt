import GaloisForLFunctions.RHTower.Sieve.HeathBrownSecondScaleAlgebra

/-!
# Scalar absorption for Heath--Brown's sparse mean value

This module converts the exact two-step square-root expression into the two published off-diagonal
monomials.  Constants remain explicit; no asymptotic notation or regime hypothesis is used.
-/

namespace RHTower.Sieve

noncomputable section

/-- Universal mean-square coefficient occurring in Heath--Brown's iteration. -/
def heathBrownMeanSquareCoefficient : ℝ :=
  (5 * Real.pi * Real.exp 1 + 5 * Real.pi / 4) * (25 * Real.pi / 8) ^ (2 : ℕ)

/-- Universal coefficient after the two-step square-root absorption. -/
def heathBrownTheoremFourUniversalCoefficient : ℝ :=
  15 * Real.pi / 2 +
    3 * (25 * Real.pi / 2) * Real.sqrt (90 * Real.pi) *
      (heathBrownMeanSquareCoefficient + 1) +
    (25 * Real.pi / 2) ^ (2 : ℕ) * heathBrownMeanSquareCoefficient

theorem heathBrown_twoStep_scalar_absorption
    {T R N K D L : ℝ}
    (hT : 2 ≤ T) (hR : 0 < R) (hN : 0 ≤ N) (hK : 1 ≤ K)
    (hheight : T ≤ K ^ (3 : ℕ))
    (hmixed : T * R ^ (2 : ℕ) / K ≤ R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ))
    (hcross : K * R * Real.sqrt (T * R) ≤
      3 * (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)))
    (hD2 : D ^ (2 : ℕ) ≤ L) (hL : 1 ≤ L) :
    let k := heathBrownMeanSquareCoefficient * T * R * D ^ (2 : ℕ)
    let a1 := 75 * Real.pi / 2 * K ^ (4 : ℕ) * R ^ (2 : ℕ) +
      5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ)
    let b1 := 25 * Real.pi / 4 * (K + 1)
    95 * Real.pi / 2 * N ^ (2 : ℕ) * R ^ (2 : ℕ) +
        15 * Real.pi / 2 * N * (T * R ^ (2 : ℕ) / K) +
        (25 * Real.pi / 2) * (N / K) *
          Real.sqrt (k * (2 * a1 + b1 ^ (2 : ℕ) * k)) ≤
      95 * Real.pi / 2 * N ^ (2 : ℕ) * R ^ (2 : ℕ) +
        heathBrownTheoremFourUniversalCoefficient * L *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
  dsimp only
  let Ck : ℝ := heathBrownMeanSquareCoefficient
  let Cb : ℝ := 25 * Real.pi / 2
  let k : ℝ := Ck * T * R * D ^ (2 : ℕ)
  let a1 : ℝ := 75 * Real.pi / 2 * K ^ (4 : ℕ) * R ^ (2 : ℕ) +
    5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ)
  let b1 : ℝ := 25 * Real.pi / 4 * (K + 1)
  let X : ℝ := Real.sqrt (90 * Real.pi) * K ^ (2 : ℕ) * R * Real.sqrt k
  let Y : ℝ := Cb * K * k
  have hT0 : 0 < T := by linarith
  have hR0 : 0 ≤ R := hR.le
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hCk0 : 0 ≤ Ck := by
    dsimp only [Ck, heathBrownMeanSquareCoefficient]
    positivity
  have hk0 : 0 ≤ k := by dsimp only [k]; positivity
  have ha10 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have hb10 : 0 ≤ b1 := by dsimp only [b1]; positivity
  have hCb0 : 0 ≤ Cb := by dsimp only [Cb]; positivity
  have hTK : T * (2 * K + 1) ≤ 3 * K ^ (4 : ℕ) := by
    have hlin : 2 * K + 1 ≤ 3 * K := by linarith
    calc
      T * (2 * K + 1) ≤ K ^ (3 : ℕ) * (2 * K + 1) := by gcongr
      _ ≤ K ^ (3 : ℕ) * (3 * K) := by gcongr
      _ = 3 * K ^ (4 : ℕ) := by ring
  have ha1 : a1 ≤ 45 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) := by
    dsimp only [a1]
    have hsecond :
        5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ) ≤
          5 * Real.pi / 2 * (3 * K ^ (4 : ℕ)) * R ^ (2 : ℕ) := by
      calc
        5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ) =
            (5 * Real.pi / 2) * (T * (2 * K + 1)) * R ^ (2 : ℕ) := by ring
        _ ≤ (5 * Real.pi / 2) * (3 * K ^ (4 : ℕ)) * R ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hTK (by positivity)) (sq_nonneg R)
    calc
      75 * Real.pi / 2 * K ^ (4 : ℕ) * R ^ (2 : ℕ) +
          5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ) ≤
        75 * Real.pi / 2 * K ^ (4 : ℕ) * R ^ (2 : ℕ) +
          5 * Real.pi / 2 * (3 * K ^ (4 : ℕ)) * R ^ (2 : ℕ) := add_le_add le_rfl hsecond
      _ = 45 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) := by ring
  have hb1 : b1 ≤ Cb * K := by
    dsimp only [b1, Cb]
    have : K + 1 ≤ 2 * K := by linarith
    calc
      25 * Real.pi / 4 * (K + 1) ≤ 25 * Real.pi / 4 * (2 * K) := by gcongr
      _ = 25 * Real.pi / 2 * K := by ring
  have hradicand :
      k * (2 * a1 + b1 ^ (2 : ℕ) * k) ≤ (X + Y) ^ (2 : ℕ) := by
    have h90 : 0 ≤ 90 * Real.pi := by positivity
    have hsq90 := Real.sq_sqrt h90
    have hsqk := Real.sq_sqrt hk0
    have hX0 : 0 ≤ X := by dsimp only [X]; positivity
    have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
    have hb1sq : b1 ^ (2 : ℕ) ≤ (Cb * K) ^ (2 : ℕ) := (sq_le_sq₀ hb10 (hb10.trans hb1)).2 hb1
    have h2a1 : 2 * a1 ≤ 90 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) := by linarith
    have hbterm : b1 ^ (2 : ℕ) * k ≤ (Cb * K) ^ (2 : ℕ) * k :=
      mul_le_mul_of_nonneg_right hb1sq hk0
    have hsum : 2 * a1 + b1 ^ (2 : ℕ) * k ≤
        90 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) + (Cb * K) ^ (2 : ℕ) * k :=
      add_le_add h2a1 hbterm
    have hXsq : X ^ (2 : ℕ) = 90 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) * k := by
      dsimp only [X]
      calc
        (Real.sqrt (90 * Real.pi) * K ^ (2 : ℕ) * R * Real.sqrt k) ^ (2 : ℕ) =
            Real.sqrt (90 * Real.pi) ^ (2 : ℕ) * K ^ (4 : ℕ) * R ^ (2 : ℕ) * Real.sqrt k ^ (2 : ℕ) := by ring
        _ = 90 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) * k := by rw [hsq90, hsqk]
    have hYsq : Y ^ (2 : ℕ) = (Cb * K) ^ (2 : ℕ) * k ^ (2 : ℕ) := by
      dsimp only [Y]
      ring
    calc
      k * (2 * a1 + b1 ^ (2 : ℕ) * k) ≤
          k * (90 * Real.pi * K ^ (4 : ℕ) * R ^ (2 : ℕ) + (Cb * K) ^ (2 : ℕ) * k) :=
        mul_le_mul_of_nonneg_left hsum hk0
      _ = X ^ (2 : ℕ) + Y ^ (2 : ℕ) := by
        rw [hXsq, hYsq]
        ring
      _ ≤ (X + Y) ^ (2 : ℕ) := by nlinarith
  have hsqrt : Real.sqrt (k * (2 * a1 + b1 ^ (2 : ℕ) * k)) ≤ X + Y := by
    rw [Real.sqrt_le_iff]
    exact ⟨add_nonneg (by dsimp only [X]; positivity) (by dsimp only [Y]; positivity),
      hradicand⟩
  have hsqrtk : Real.sqrt k ≤ (Ck + 1) * Real.sqrt (T * R) * L := by
    have hTR0 : 0 ≤ T * R := mul_nonneg hT0.le hR0
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hcoeff : Ck ≤ (Ck + 1) ^ (2 : ℕ) := by nlinarith
    have hLL : L ≤ L ^ (2 : ℕ) := by nlinarith
    have hkL : k ≤ Ck * T * R * L := by
      dsimp only [k]
      exact mul_le_mul_of_nonneg_left hD2
        (mul_nonneg (mul_nonneg hCk0 hT0.le) hR0)
    have hcoeffL : Ck * L ≤ (Ck + 1) ^ (2 : ℕ) * L ^ (2 : ℕ) :=
      mul_le_mul hcoeff hLL hL0 (by positivity)
    have hksq : k ≤ ((Ck + 1) * Real.sqrt (T * R) * L) ^ (2 : ℕ) := by
      calc
        k ≤ Ck * T * R * L := hkL
        _ = (T * R) * (Ck * L) := by ring
        _ ≤ (T * R) * ((Ck + 1) ^ (2 : ℕ) * L ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hcoeffL hTR0
        _ = (Ck + 1) ^ (2 : ℕ) * (T * R) * L ^ (2 : ℕ) := by ring
        _ = ((Ck + 1) * Real.sqrt (T * R) * L) ^ (2 : ℕ) := by
          rw [show ((Ck + 1) * Real.sqrt (T * R) * L) ^ (2 : ℕ) =
            (Ck + 1) ^ (2 : ℕ) * Real.sqrt (T * R) ^ (2 : ℕ) * L ^ (2 : ℕ) by ring,
            Real.sq_sqrt hTR0]
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hksq⟩
  have houter :
      Cb * (N / K) * Real.sqrt (k * (2 * a1 + b1 ^ (2 : ℕ) * k)) ≤
        (3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) + Cb ^ (2 : ℕ) * Ck) * L *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
    have hNdiv0 : 0 ≤ N / K := div_nonneg hN hK0.le
    have hfactor0 : 0 ≤ Cb * (N / K) := mul_nonneg hCb0 hNdiv0
    have hsqrt90 : 0 ≤ Real.sqrt (90 * Real.pi) := Real.sqrt_nonneg _
    have hCk1 : 0 ≤ Ck + 1 := by linarith
    have hsum0 : 0 ≤ R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
    calc
      Cb * (N / K) * Real.sqrt (k * (2 * a1 + b1 ^ (2 : ℕ) * k)) ≤
          Cb * (N / K) * (X + Y) := mul_le_mul_of_nonneg_left hsqrt hfactor0
      _ = Cb * Real.sqrt (90 * Real.pi) * N * K * R * Real.sqrt k +
          Cb ^ (2 : ℕ) * N * k := by
        dsimp only [X, Y]
        field_simp
      _ ≤ Cb * Real.sqrt (90 * Real.pi) * N * K * R *
            ((Ck + 1) * Real.sqrt (T * R) * L) + Cb ^ (2 : ℕ) * N * k := by
        gcongr
      _ ≤ 3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) * N *
            (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) * L +
          Cb ^ (2 : ℕ) * N * (Ck * T * R * L) := by
        apply add_le_add
        · calc
          Cb * Real.sqrt (90 * Real.pi) * N * K * R *
              ((Ck + 1) * Real.sqrt (T * R) * L) =
            (Cb * Real.sqrt (90 * Real.pi) * N * (Ck + 1) * L) *
              (K * R * Real.sqrt (T * R)) := by ring
          _ ≤ (Cb * Real.sqrt (90 * Real.pi) * N * (Ck + 1) * L) *
              (3 * (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hcross (by positivity)
          _ = 3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) * N *
              (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) * L := by ring
        · dsimp only [k]
          calc
            Cb ^ (2 : ℕ) * N * (Ck * T * R * D ^ (2 : ℕ)) =
                (Cb ^ (2 : ℕ) * N * Ck * T * R) * D ^ (2 : ℕ) := by ring
            _ ≤ (Cb ^ (2 : ℕ) * N * Ck * T * R) * L :=
              mul_le_mul_of_nonneg_left hD2 (by positivity)
            _ = Cb ^ (2 : ℕ) * N * (Ck * T * R * L) := by ring
      _ ≤ (3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) + Cb ^ (2 : ℕ) * Ck) * L *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
        have hterm : Cb ^ (2 : ℕ) * N * (Ck * T * R * L) ≤
            Cb ^ (2 : ℕ) * Ck * L *
              (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
          have hnmixed0 : 0 ≤ N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
          calc
            Cb ^ (2 : ℕ) * N * (Ck * T * R * L) =
                (Cb ^ (2 : ℕ) * Ck * L) * (N * R * T) := by ring
            _ ≤ (Cb ^ (2 : ℕ) * Ck * L) *
                (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnmixed0) (by positivity)
            _ = Cb ^ (2 : ℕ) * Ck * L *
                (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by ring
        calc
          3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) * N *
                (R * T + R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) * L +
              Cb ^ (2 : ℕ) * N * (Ck * T * R * L) =
            3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) * L *
                (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) +
              Cb ^ (2 : ℕ) * N * (Ck * T * R * L) := by ring
          _ ≤
            3 * Cb * Real.sqrt (90 * Real.pi) * (Ck + 1) * L *
                (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) +
              Cb ^ (2 : ℕ) * Ck * L *
                (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
            exact add_le_add le_rfl hterm
          _ = _ := by ring
  have ha0mixed :
      15 * Real.pi / 2 * N * (T * R ^ (2 : ℕ) / K) ≤
        (15 * Real.pi / 2) * L *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
    have hmixed0 : 0 ≤ R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
    have hbase0 : 0 ≤ N * R * T := by positivity
    have hc0 : 0 ≤ 15 * Real.pi / 2 * N := by positivity
    have hZ0 : 0 ≤ N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
      positivity
    calc
      15 * Real.pi / 2 * N * (T * R ^ (2 : ℕ) / K) ≤
          15 * Real.pi / 2 * N * (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hmixed hc0
      _ ≤ (15 * Real.pi / 2) *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
        have : N * (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) ≤
            N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
          calc
            N * (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) =
                N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by ring
            _ ≤ N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) :=
              le_add_of_nonneg_left hbase0
        calc
          15 * Real.pi / 2 * N *
              (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) =
            (15 * Real.pi / 2) *
              (N * (R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ))) := by ring
          _ ≤ (15 * Real.pi / 2) *
              (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (15 * Real.pi / 2) * L *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
        have hcL : 15 * Real.pi / 2 ≤ (15 * Real.pi / 2) * L := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 15 * Real.pi / 2))
        exact mul_le_mul_of_nonneg_right hcL hZ0
  dsimp only [Ck, Cb, k, a1, b1] at houter
  calc
    95 * Real.pi / 2 * N ^ (2 : ℕ) * R ^ (2 : ℕ) +
          15 * Real.pi / 2 * N * (T * R ^ (2 : ℕ) / K) +
          (25 * Real.pi / 2) * (N / K) *
            Real.sqrt
              (heathBrownMeanSquareCoefficient * T * R * D ^ (2 : ℕ) *
                (2 *
                    (75 * Real.pi / 2 * K ^ (4 : ℕ) * R ^ (2 : ℕ) +
                      5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ)) +
                  (25 * Real.pi / 4 * (K + 1)) ^ (2 : ℕ) *
                    (heathBrownMeanSquareCoefficient * T * R * D ^ (2 : ℕ)))) =
        95 * Real.pi / 2 * N ^ (2 : ℕ) * R ^ (2 : ℕ) +
          (15 * Real.pi / 2 * N * (T * R ^ (2 : ℕ) / K) +
            (25 * Real.pi / 2) * (N / K) *
              Real.sqrt
                (heathBrownMeanSquareCoefficient * T * R * D ^ (2 : ℕ) *
                  (2 *
                      (75 * Real.pi / 2 * K ^ (4 : ℕ) * R ^ (2 : ℕ) +
                        5 * Real.pi / 2 * T * (2 * K + 1) * R ^ (2 : ℕ)) +
                    (25 * Real.pi / 4 * (K + 1)) ^ (2 : ℕ) *
                      (heathBrownMeanSquareCoefficient * T * R * D ^ (2 : ℕ))))) := by ring
    _ ≤
        95 * Real.pi / 2 * N ^ (2 : ℕ) * R ^ (2 : ℕ) +
          ((15 * Real.pi / 2) * L *
              (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) +
            (3 * (25 * Real.pi / 2) * Real.sqrt (90 * Real.pi) *
                (heathBrownMeanSquareCoefficient + 1) +
              (25 * Real.pi / 2) ^ (2 : ℕ) * heathBrownMeanSquareCoefficient) * L *
                (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ))) := by
      exact add_le_add_right (add_le_add ha0mixed houter) _
    _ = 95 * Real.pi / 2 * N ^ (2 : ℕ) * R ^ (2 : ℕ) +
        heathBrownTheoremFourUniversalCoefficient * L *
          (N * R * T + N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) := by
      rw [heathBrownTheoremFourUniversalCoefficient]
      ring

end

end RHTower.Sieve
