import GaloisForLFunctions.RHTower.PolynomialFockNormalizedTangentGaussianOverlap

/-!
# Separation of adapted tangent centers in the polynomial Fock space

For a weight exponent `m ≥ 4` the adapted centers of the normalized tangent vectors are
`x = N^(2/m)` and `y = K^(2/m)`, with local curvatures `c(x) = m (1 + x²)^(m/2 - 1)`. The Gaussian
overlap bound of two tangent vectors decays like `exp(-G)` with the harmonic-curvature gap
`G = c(x) c(y) / (2 (c(x) + c(y))) · (x - y)²`. This module bounds `G` from below in terms of the
original indices `K ≤ N`: quadratically in `N - K` when `N ≤ 2K`, and by `(N - K)^(4/m)` when
`2K ≤ N`.

## Main results

- `adapted_rpow_gap_near`: for `1 ≤ K ≤ N ≤ 2K`,
  `N - K ≤ (m/2) 2^(m/2 - 1) K^(1 - 2/m) (N^(2/m) - K^(2/m))`.
- `adapted_rpow_gap_far`: for `1 ≤ K`, `2K ≤ N`,
  `(1 - 2^(-2/m)) (N - K)^(2/m) ≤ K^(1 - 2/m) (N^(2/m) - K^(2/m))`.
- `polynomialFockHarmonicCurvatureGap_lower_adapted`: `G ≥ (m/4) (K^(1 - 2/m) (N^(2/m) - K^(2/m)))²`.
- `polynomialFockHarmonicCurvatureGap_lower_near`: for `N ≤ 2K`,
  `G ≥ m / (4 ((m/2) 2^(m/2 - 1))²) · (N - K)²`.
- `polynomialFockHarmonicCurvatureGap_lower_far`: for `2K ≤ N`,
  `G ≥ (m/4) (1 - 2^(-2/m))² (N - K)^(4/m)`.

## Hypotheses

All results are unconditional real inequalities. They assume the parameter range `4 ≤ m`,
`1 ≤ K ≤ N`, and, for the near and far regimes respectively, `N ≤ 2K` or `2K ≤ N`.
-/

namespace RHTower

noncomputable section

/-- Near regime: assuming `4 ≤ m` and `1 ≤ K ≤ N ≤ 2K`, the index gap `N - K` is at most
`(m/2) 2^(m/2 - 1) K^(1 - 2/m)` times the adapted-center gap `N^(2/m) - K^(2/m)`. -/
theorem adapted_rpow_gap_near
    {m K N : ℝ} (hm : 4 ≤ m) (hK : 1 ≤ K) (hKN : K ≤ N)
    (hN2 : N ≤ 2 * K) :
    N - K ≤
      (m / 2) * 2 ^ (m / 2 - 1) * K ^ (1 - 2 / m) *
        (N ^ (2 / m) - K ^ (2 / m)) := by
  let α : ℝ := 2 / m
  let p : ℝ := m / 2
  let x : ℝ := N ^ α
  let y : ℝ := K ^ α
  have hm0 : 0 < m := by linarith
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by dsimp [α]; rw [div_le_one hm0]; linarith
  have hp1 : 1 ≤ p := by dsimp [p]; linarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hN0 : 0 < N := hK0.trans_le hKN
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 α
  have hy0 : 0 < y := Real.rpow_pos_of_pos hK0 α
  have hαp : α * p = 1 := by dsimp [α, p]; field_simp
  have hxp : x ^ p = N := by
    dsimp [x]
    rw [← Real.rpow_mul hN0.le, hαp, Real.rpow_one]
  have hyp : y ^ p = K := by
    dsimp [y]
    rw [← Real.rpow_mul hK0.le, hαp, Real.rpow_one]
  have htangent := rpow_tangent_lower hx0 hy0.le hp1
  rw [hxp, hyp] at htangent
  have hgap : N - K ≤ p * x ^ (p - 1) * (x - y) := by
    linarith
  have hxy : y ≤ x := by
    dsimp [x, y]
    exact Real.rpow_le_rpow hK0.le hKN hα0.le
  have htwoPow : (2 : ℝ) ^ α ≤ 2 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1)
  have hxTwo : x ≤ 2 * y := by
    have hpow := Real.rpow_le_rpow hN0.le hN2 hα0.le
    have hfactor : (2 * K) ^ α = 2 ^ α * y := by
      dsimp [y]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hK0.le]
    change x ≤ 2 * y
    calc
      x ≤ (2 * K) ^ α := by simpa [x, α] using hpow
      _ = 2 ^ α * y := hfactor
      _ ≤ 2 * y := mul_le_mul_of_nonneg_right htwoPow hy0.le
  have hpSub : 0 ≤ p - 1 := sub_nonneg.mpr hp1
  have hxpow_le : x ^ (p - 1) ≤ (2 * y) ^ (p - 1) :=
    Real.rpow_le_rpow hx0.le hxTwo hpSub
  have hyPower : y ^ (p - 1) = K ^ (1 - α) := by
    dsimp [y]
    rw [← Real.rpow_mul hK0.le]
    congr 2
    calc
      α * (p - 1) = α * p - α := by ring
      _ = 1 - α := by rw [hαp]
  have htwoFactor : (2 * y) ^ (p - 1) = 2 ^ (p - 1) * K ^ (1 - α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy0.le, hyPower]
  have hgapNonneg : 0 ≤ x - y := sub_nonneg.mpr hxy
  have hcoef : 0 ≤ p := le_trans (by norm_num) hp1
  calc
    N - K ≤ p * x ^ (p - 1) * (x - y) := hgap
    _ ≤ p * (2 * y) ^ (p - 1) * (x - y) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hxpow_le hcoef) hgapNonneg
    _ = (m / 2) * 2 ^ (m / 2 - 1) * K ^ (1 - 2 / m) *
        (N ^ (2 / m) - K ^ (2 / m)) := by
      rw [htwoFactor]
      dsimp [p, α, x, y]
      ring

/-- Far regime: assuming `4 ≤ m`, `1 ≤ K` and `2K ≤ N`,
`(1 - 2^(-2/m)) (N - K)^(2/m) ≤ K^(1 - 2/m) (N^(2/m) - K^(2/m))`. -/
theorem adapted_rpow_gap_far
    {m K N : ℝ} (hm : 4 ≤ m) (hK : 1 ≤ K) (hKN2 : 2 * K ≤ N) :
    (1 - 2 ^ (-(2 / m))) * (N - K) ^ (2 / m) ≤
      K ^ (1 - 2 / m) * (N ^ (2 / m) - K ^ (2 / m)) := by
  let α : ℝ := 2 / m
  let x : ℝ := N ^ α
  let y : ℝ := K ^ α
  let D : ℝ := N - K
  let q : ℝ := 2 ^ (-α)
  have hm0 : 0 < m := by linarith
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by dsimp [α]; rw [div_le_one hm0]; linarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKN : K ≤ N := by linarith
  have hN0 : 0 < N := hK0.trans_le hKN
  have hDge : K ≤ D := by dsimp [D]; linarith
  have hD0 : 0 < D := hK0.trans_le hDge
  have hDleN : D ≤ N := by dsimp [D]; linarith
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 α
  have hy0 : 0 < y := Real.rpow_pos_of_pos hK0 α
  have hxy : y ≤ x := by
    dsimp [x, y]
    exact Real.rpow_le_rpow hK0.le hKN hα0.le
  have htwo : 2 ^ α * y ≤ x := by
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 * K) hKN2 hα0.le
    have hfactor : (2 * K) ^ α = 2 ^ α * y := by
      dsimp [y]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hK0.le]
    simpa [x, hfactor] using hpow
  have hqpos : 0 < q := by dsimp [q]; positivity
  have htwoPos : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hqTwo : q * 2 ^ α = 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by norm_num)]
    exact inv_mul_cancel₀ htwoPos.ne'
  have hyqx : y ≤ q * x := by
    have hmul := mul_le_mul_of_nonneg_left htwo hqpos.le
    calc
      y = q * (2 ^ α * y) := by rw [← mul_assoc, hqTwo, one_mul]
      _ ≤ q * x := hmul
  have hq_lt : q < 1 := by
    dsimp [q]
    rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
    right
    exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2
      (Or.inl ⟨by norm_num, hα0⟩)
  have hδ : 0 < 1 - q := sub_pos.mpr hq_lt
  have hgap : (1 - q) * x ≤ x - y := by nlinarith
  have hDpow : D ^ α ≤ x := by
    dsimp [x]
    exact Real.rpow_le_rpow hD0.le hDleN hα0.le
  have hδD : (1 - q) * D ^ α ≤ x - y :=
    (mul_le_mul_of_nonneg_left hDpow hδ.le).trans hgap
  have hKpow : 1 ≤ K ^ (1 - α) :=
    Real.one_le_rpow hK (by linarith : 0 ≤ 1 - α)
  have hgap0 : 0 ≤ x - y := sub_nonneg.mpr hxy
  calc
    (1 - 2 ^ (-(2 / m))) * (N - K) ^ (2 / m)
        = (1 - q) * D ^ α := by rfl
    _ ≤ x - y := hδD
    _ ≤ K ^ (1 - α) * (x - y) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hKpow hgap0
    _ = K ^ (1 - 2 / m) * (N ^ (2 / m) - K ^ (2 / m)) := by rfl

/-- Assuming `4 ≤ m` and `1 ≤ K ≤ N`, the harmonic-curvature gap of the adapted centers
`N^(2/m)`, `K^(2/m)` is at least `(m/4) (K^(1 - 2/m) (N^(2/m) - K^(2/m)))²`. -/
theorem polynomialFockHarmonicCurvatureGap_lower_adapted
    {m K N : ℝ} (hm : 4 ≤ m) (hK : 1 ≤ K) (hKN : K ≤ N) :
    (m / 4) *
        (K ^ (1 - 2 / m) * (N ^ (2 / m) - K ^ (2 / m))) ^ 2 ≤
      ((m * (1 + (N ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) *
          (m * (1 + (K ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) /
        (2 * ((m * (1 + (N ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) +
          (m * (1 + (K ^ (2 / m)) ^ 2) ^ (m / 2 - 1))))) *
            (N ^ (2 / m) - K ^ (2 / m)) ^ 2 := by
  let α : ℝ := 2 / m
  let β : ℝ := m / 2 - 1
  let x : ℝ := N ^ α
  let y : ℝ := K ^ α
  let cx : ℝ := m * (1 + x ^ 2) ^ β
  let cy : ℝ := m * (1 + y ^ 2) ^ β
  have hm0 : 0 < m := by linarith
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by dsimp [α]; rw [div_le_one hm0]; linarith
  have hβ0 : 0 ≤ β := by dsimp [β]; linarith
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hN0 : 0 < N := hK0.trans_le hKN
  have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 α
  have hy0 : 0 < y := Real.rpow_pos_of_pos hK0 α
  have hxy : y ≤ x := by
    dsimp [x, y]
    exact Real.rpow_le_rpow hK0.le hKN hα0.le
  have hbase : 1 + y ^ 2 ≤ 1 + x ^ 2 := by nlinarith
  have hcycx : cy ≤ cx := by
    dsimp [cy, cx]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hbase hβ0) hm0.le
  have hcx0 : 0 < cx := by dsimp [cx]; positivity
  have hcy0 : 0 < cy := by dsimp [cy]; positivity
  have hsum : 0 < cx + cy := add_pos hcx0 hcy0
  have hharmonic : cy / 4 ≤ cx * cy / (2 * (cx + cy)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
      (mul_pos (by norm_num) hsum)]
    nlinarith [mul_nonneg hcy0.le (sub_nonneg.mpr hcycx)]
  have hcyLower : m * K ^ (2 - 2 * α) ≤ cy := by
    have hpow := Real.rpow_le_rpow
      (show 0 ≤ y ^ 2 by positivity)
      (show y ^ 2 ≤ 1 + y ^ 2 by linarith) hβ0
    have hident : (y ^ 2) ^ β = K ^ (2 - 2 * α) := by
      rw [← Real.rpow_natCast y 2]
      rw [← Real.rpow_mul hy0.le]
      dsimp [y]
      rw [← Real.rpow_mul hK0.le]
      congr 2
      dsimp [α, β]
      field_simp
    dsimp [cy]
    rw [← hident]
    exact mul_le_mul_of_nonneg_left hpow hm0.le
  have hKident : K ^ (2 - 2 * α) = (K ^ (1 - α)) ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hK0.le]
    congr 2
    ring
  have hcoef : (m / 4) * (K ^ (1 - α)) ^ 2 ≤
      cx * cy / (2 * (cx + cy)) := by
    calc
      (m / 4) * (K ^ (1 - α)) ^ 2 = (m * K ^ (2 - 2 * α)) / 4 := by
        rw [hKident]
        ring
      _ ≤ cy / 4 := div_le_div_of_nonneg_right hcyLower (by norm_num)
      _ ≤ cx * cy / (2 * (cx + cy)) := hharmonic
  have hgap0 : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hcoef hgap0
  change (m / 4) * (K ^ (1 - α) * (x - y)) ^ 2 ≤
      (cx * cy / (2 * (cx + cy))) * (x - y) ^ 2
  nlinarith

/-- Assuming `4 ≤ m` and `1 ≤ K ≤ N ≤ 2K`, the harmonic-curvature gap is at least
`m / (4 ((m/2) 2^(m/2 - 1))²) · (N - K)²`. -/
theorem polynomialFockHarmonicCurvatureGap_lower_near
    {m K N : ℝ} (hm : 4 ≤ m) (hK : 1 ≤ K) (hKN : K ≤ N)
    (hN2 : N ≤ 2 * K) :
    (m / (4 * ((m / 2) * 2 ^ (m / 2 - 1)) ^ 2)) * (N - K) ^ 2 ≤
      ((m * (1 + (N ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) *
          (m * (1 + (K ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) /
        (2 * ((m * (1 + (N ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) +
          (m * (1 + (K ^ (2 / m)) ^ 2) ^ (m / 2 - 1))))) *
            (N ^ (2 / m) - K ^ (2 / m)) ^ 2 := by
  let A : ℝ := (m / 2) * 2 ^ (m / 2 - 1)
  let S : ℝ := K ^ (1 - 2 / m) * (N ^ (2 / m) - K ^ (2 / m))
  have hm0 : 0 < m := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hgap := adapted_rpow_gap_near hm hK hKN hN2
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (sub_nonneg.mpr (Real.rpow_le_rpow (by linarith) hKN (by positivity)))
  have hd0 : 0 ≤ N - K := sub_nonneg.mpr hKN
  have hgap' : N - K ≤ A * S := by
    simpa [A, S, mul_assoc] using hgap
  have hsq : (N - K) ^ 2 ≤ A ^ 2 * S ^ 2 := by
    nlinarith
  have hscaled :
      (m / (4 * A ^ 2)) * (N - K) ^ 2 ≤ (m / 4) * S ^ 2 := by
    field_simp [hA.ne']
    nlinarith
  exact hscaled.trans (by
    simpa [S] using polynomialFockHarmonicCurvatureGap_lower_adapted hm hK hKN)

/-- Assuming `4 ≤ m`, `1 ≤ K` and `2K ≤ N`, the harmonic-curvature gap is at least
`(m/4) (1 - 2^(-2/m))² (N - K)^(4/m)`. -/
theorem polynomialFockHarmonicCurvatureGap_lower_far
    {m K N : ℝ} (hm : 4 ≤ m) (hK : 1 ≤ K) (hKN2 : 2 * K ≤ N) :
    (m / 4) * (1 - 2 ^ (-(2 / m))) ^ 2 * (N - K) ^ (4 / m) ≤
      ((m * (1 + (N ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) *
          (m * (1 + (K ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) /
        (2 * ((m * (1 + (N ^ (2 / m)) ^ 2) ^ (m / 2 - 1)) +
          (m * (1 + (K ^ (2 / m)) ^ 2) ^ (m / 2 - 1))))) *
            (N ^ (2 / m) - K ^ (2 / m)) ^ 2 := by
  let α : ℝ := 2 / m
  let δ : ℝ := 1 - 2 ^ (-α)
  let D : ℝ := N - K
  let S : ℝ := K ^ (1 - α) * (N ^ α - K ^ α)
  have hm0 : 0 < m := by linarith
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKN : K ≤ N := by linarith
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    have hlt : (2 : ℝ) ^ (-α) < 1 := by
      rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
      right
      exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2
        (Or.inl ⟨by norm_num, hα0⟩)
    linarith
  have hgap := adapted_rpow_gap_far hm hK hKN2
  change δ * D ^ α ≤ S at hgap
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg (Real.rpow_nonneg hK0.le _)
      (sub_nonneg.mpr (Real.rpow_le_rpow hK0.le hKN hα0.le))
  have hleft0 : 0 ≤ δ * D ^ α :=
    mul_nonneg hδ.le (Real.rpow_nonneg hD0.le α)
  have hsqRaw : (δ * D ^ α) ^ 2 ≤ S ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hgap) (add_nonneg hS0 hleft0)
    nlinarith
  have hsq : δ ^ 2 * (D ^ α) ^ 2 ≤ S ^ 2 := by
    simpa only [mul_pow] using hsqRaw
  have hDpow : (D ^ α) ^ 2 = D ^ (4 / m) := by
    calc
      (D ^ α) ^ 2 = (D ^ α) ^ (2 : ℝ) :=
        (Real.rpow_natCast (D ^ α) 2).symm
      _ = D ^ (α * 2) := by rw [Real.rpow_mul hD0.le]
      _ = D ^ (4 / m) := by
        congr 1
        dsimp [α]
        field_simp
        norm_num
  have hscaled :
      (m / 4) * δ ^ 2 * D ^ (4 / m) ≤ (m / 4) * S ^ 2 := by
    calc
      (m / 4) * δ ^ 2 * D ^ (4 / m) =
          (m / 4) * (δ ^ 2 * (D ^ α) ^ 2) := by rw [hDpow]; ring
      _ ≤ (m / 4) * S ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
  exact hscaled.trans (by
    simpa [S, α] using polynomialFockHarmonicCurvatureGap_lower_adapted hm hK hKN)

end

end RHTower
