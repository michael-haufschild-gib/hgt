import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LocalZeroCount
import GaloisForLFunctions.RHTower.ZetaZeroClassPolynomialPower

/-!
# Detecting the zeros of a Dirichlet `L`-function

With `L_X(s) = Σ_{n ≤ X} χ(n) n^{−s}` and the mollifier `M_y(s) = Σ_{b ≤ y} μ(b) χ(b) b^{−s}`,

`L_X(s) M_y(s) = 1 + Σ_k χ(k) e_k k^{−s}`        (`partialChi_mul_mollChi`),

with the detection coefficients `e_k` of the corpus (`RHTower.detCoeff`, vanishing for `k ≤ y`).
At a zero `ρ` with `Re ρ ≥ ½` and `|Im ρ| ≤ T` the truncation error of `L` makes the right side
`−(L − L_X)(ρ) M_y(ρ)` small as soon as `X + 1 ≥ (4q(2T + 3)y)²`, so the detection polynomial has
modulus at least `½` there (`half_le_norm_detPolyChi`).

Splitting the support into dyadic blocks and the real part into slabs of width `1/Λ`,
`Λ = log(Xy)`, the Taylor transfer of the corpus gives a slab `i`, a block `j` and an order
`m < J + 8` whose companion polynomial is at least `1/(12J)` at `σ + i/Λ + iγ`
(`exists_class_of_zero`).
-/

open Complex Finset RHTower RHTower.Sieve

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- The truncated `L`-function `Σ_{n ≤ X} χ(n) n^{−s}`. -/
def partialChi (X : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 X, χ n * (n : ℂ) ^ (-s)

/-- The twisted Möbius mollifier `Σ_{b ≤ y} μ(b) χ(b) b^{−s}`. -/
def mollChi (y : ℕ) (s : ℂ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 y, χ b * (ArithmeticFunction.moebius b : ℂ) * (b : ℂ) ^ (-s)

/-- The twisted detection coefficient `χ(k) e_k`. -/
def detCoeffChi (X y : ℕ) (k : ℕ) : ℂ := χ k * ((detCoeff X y k : ℝ) : ℂ)

/-- The twisted detection polynomial `Σ_k χ(k) e_k k^{−s}`. -/
def detPolyChi (X y : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ detSupport X y, detCoeffChi χ X y k * (k : ℂ) ^ (-s)

theorem one_mem_detSupport {X y : ℕ} (hX : 1 ≤ X) (hy : 1 ≤ y) : 1 ∈ detSupport X y := by
  unfold detSupport prodSupport
  rw [Finset.mem_image]
  exact ⟨(1, 1), by simp [hX, hy], by simp⟩

omit [NeZero q] in
/-- **The mollified product.**  `L_X(s) M_y(s) = 1 + Σ_k χ(k) e_k k^{−s}`. -/
theorem partialChi_mul_mollChi {X y : ℕ} (hX : 1 ≤ X) (hy : 1 ≤ y) (s : ℂ) :
    partialChi χ X s * mollChi χ y s = 1 + detPolyChi χ X y s := by
  classical
  unfold partialChi mollChi detPolyChi detCoeffChi
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hterm : ∀ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 y,
      χ p.1 * (p.1 : ℂ) ^ (-s) * (χ p.2 * (ArithmeticFunction.moebius p.2 : ℂ) * (p.2 : ℂ) ^ (-s))
        = χ (p.1 * p.2 : ℕ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) * (ArithmeticFunction.moebius p.2 : ℂ) := by
    intro p _
    push_cast
    rw [show ((p.1 : ℂ) * p.2) ^ (-s) = (p.1 : ℂ) ^ (-s) * (p.2 : ℂ) ^ (-s) from
      Complex.natCast_mul_natCast_cpow _ _ _, map_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hmaps : ∀ p ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 y, p.1 * p.2 ∈ detSupport X y := by
    intro p hp
    exact Finset.mem_image_of_mem _ hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ detSupport X y,
      ∑ p ∈ (Finset.Icc 1 X ×ˢ Finset.Icc 1 y).filter (fun p => p.1 * p.2 = k),
        χ (p.1 * p.2 : ℕ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) * (ArithmeticFunction.moebius p.2 : ℂ)
      = χ k * ((detCoeff X y k : ℝ) : ℂ) * (k : ℂ) ^ (-s)
        + (if k = 1 then χ k * (k : ℂ) ^ (-s) else 0) := by
    intro k _
    have h1 : ∀ p ∈ (Finset.Icc 1 X ×ˢ Finset.Icc 1 y).filter (fun p => p.1 * p.2 = k),
        χ (p.1 * p.2 : ℕ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) * (ArithmeticFunction.moebius p.2 : ℂ)
          = χ k * (k : ℂ) ^ (-s) * ((1 * moebiusCoeff p.2 : ℝ) : ℂ) := by
      intro p hp
      rw [(Finset.mem_filter.mp hp).2, moebiusCoeff]
      push_cast
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← Complex.ofReal_sum]
    have hconv : ∑ p ∈ (Finset.Icc 1 X ×ˢ Finset.Icc 1 y).filter (fun p => p.1 * p.2 = k),
        1 * moebiusCoeff p.2 = detCoeff X y k + (if k = 1 then 1 else 0) := by
      unfold detCoeff dpolyConv
      ring
    rw [hconv]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hfib, Finset.sum_add_distrib, Finset.sum_ite_eq'
    (detSupport X y) 1, if_pos (one_mem_detSupport hX hy)]
  simp only [Nat.cast_one, map_one, one_cpow, mul_one]
  ring

omit [NeZero q] in
/-- The mollifier is at most `y` right of the imaginary axis. -/
theorem norm_mollChi_le (y : ℕ) {s : ℂ} (hs : 0 ≤ s.re) : ‖mollChi χ y s‖ ≤ y := by
  unfold mollChi
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b ∈ Finset.Icc 1 y, ‖χ b * (ArithmeticFunction.moebius b : ℂ) * (b : ℂ) ^ (-s)‖
      ≤ ∑ _b ∈ Finset.Icc 1 y, (1 : ℝ) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
        rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_intCast]
        have h1 := DirichletCharacter.norm_le_one χ b
        have h2 : |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have h3 : (b : ℝ) ^ (-s).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb1) (by simp; linarith)
        calc ‖χ b‖ * |(ArithmeticFunction.moebius b : ℝ)| * (b : ℝ) ^ (-s).re ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by ring
    _ = y := by simp

omit [NeZero q] in
/-- `partialChi` is the corpus partial sum. -/
theorem partialChi_eq_dirichletPartialSum (X : ℕ) (s : ℂ) :
    partialChi χ X s = GaloisForLFunctions.RHTower.dirichletPartialSum (fun j => χ (j + 1)) X s := by
  unfold partialChi GaloisForLFunctions.RHTower.dirichletPartialSum
  rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) from rfl, Finset.sum_Ico_eq_sum_range,
    show X + 1 - 1 = X by omega]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring_nf

/-- **Zero detection.**  At a zero `ρ` of `L(s, χ)` with `½ ≤ Re ρ` and `‖ρ‖ ≤ T + 1`, the twisted
detection polynomial has modulus at least `½` once `X + 1 ≥ (4q(2T + 3)y)²`. -/
theorem half_le_norm_detPolyChi {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {X y : ℕ}
    (hX : 1 ≤ X) (hy : 1 ≤ y) {T : ℝ} (hT : 0 ≤ T)
    (hXbig : (4 * q * (2 * T + 3) * y) ^ 2 ≤ (X : ℝ) + 1) {ρ : ℂ} (hβ : 1 / 2 ≤ ρ.re)
    (hρT : ‖ρ‖ ≤ T + 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    1 / 2 ≤ ‖detPolyChi χ X y ρ‖ := by
  have hβ0 : 0 < ρ.re := by linarith
  have hid := partialChi_mul_mollChi χ hX hy ρ
  have herr := norm_LFunction_sub_character_partial_le hχ hβ0 X
  rw [← partialChi_eq_dirichletPartialSum, hz, zero_sub, norm_neg] at herr
  have hM := norm_mollChi_le χ y hβ0.le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  -- the truncation error times the mollifier is at most `1/2`
  have hA : 0 < 4 * (q : ℝ) * (2 * T + 3) * y := by positivity
  have hX0 : (0 : ℝ) < (X : ℝ) + 1 := by positivity
  have hpow : ((X : ℝ) + 1) ^ (-ρ.re) ≤ (4 * q * (2 * T + 3) * y)⁻¹ := by
    calc ((X : ℝ) + 1) ^ (-ρ.re) ≤ ((X : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) X])
            (by linarith)
      _ ≤ ((4 * q * (2 * T + 3) * y) ^ 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hXbig (by norm_num)
      _ = (4 * q * (2 * T + 3) * y)⁻¹ := by
          rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hA.le]
  have hfac : 1 + ‖ρ‖ / ρ.re ≤ 2 * T + 3 := by
    have : ‖ρ‖ / ρ.re ≤ 2 * (T + 1) := by
      rw [div_le_iff₀ hβ0]; nlinarith [norm_nonneg ρ]
    linarith
  have hsmall : ‖partialChi χ X ρ‖ * ‖mollChi χ y ρ‖ ≤ 1 / 2 := by
    calc ‖partialChi χ X ρ‖ * ‖mollChi χ y ρ‖
        ≤ (2 * q * (1 + ‖ρ‖ / ρ.re) * ((X : ℝ) + 1) ^ (-ρ.re)) * y :=
          mul_le_mul herr hM (norm_nonneg _) (by positivity)
      _ ≤ (2 * q * (2 * T + 3) * (4 * q * (2 * T + 3) * y)⁻¹) * y := by
          gcongr
      _ = 1 / 2 := by field_simp; ring
  have h1 : detPolyChi χ X y ρ = partialChi χ X ρ * mollChi χ y ρ - 1 := by rw [hid]; ring
  rw [h1]
  have := norm_sub_norm_le (1 : ℂ) (partialChi χ X ρ * mollChi χ y ρ)
  rw [norm_one, norm_sub_rev, norm_mul] at this
  linarith

/-! ### Blocks, slabs and Taylor orders -/

omit [NeZero q] in
/-- The twisted detection polynomial is the sum of its dyadic blocks. -/
theorem detPolyChi_eq_sum_blocks (X y : ℕ) (σ γ : ℝ) :
    detPolyChi χ X y ((σ : ℂ) + (γ : ℂ) * I)
      = ∑ j ∈ range (detBlockCount X y),
          abscissaDirichletValue (detDyadicBlock X y j) (detCoeffChi χ X y) σ γ := by
  classical
  unfold detPolyChi abscissaDirichletValue detDyadicBlock
  have hmaps : ∀ k ∈ detSupport X y, Nat.log 2 k ∈ range (detBlockCount X y) := by
    intro k hk
    rw [mem_range, detBlockCount, Nat.lt_succ_iff]
    exact Nat.log_mono_right (mem_detSupport_le hk).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]

omit [NeZero q] in
theorem sum_norm_detCoeffChi_block_le (X y j : ℕ) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) :
    ∑ k ∈ detDyadicBlock X y j, ‖detCoeffChi χ X y k‖ * (k : ℝ) ^ (-σ₀)
      ≤ 2 * 4 ^ (detBlockCount X y) := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_norm_detCoeffC_block_le (j := j) hσ₀)
  unfold detCoeffChi detCoeffC
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  calc ‖χ k‖ * ‖((detCoeff X y k : ℝ) : ℂ)‖ ≤ 1 * ‖((detCoeff X y k : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ k) (norm_nonneg _)
    _ = _ := one_mul _

omit [NeZero q] in
/-- **The class of a detected point.**  If the detection polynomial is at least `½` at
`β + iγ` with `σ ≤ β ≤ 1`, then some slab `i ≤ ⌊Λ⌋`, block `j < J` and order `m < J + 8` have
`1/(12J) ≤ |P_{j,m}(σ + i/Λ + iγ)|`. -/
theorem exists_class_of_detected {X y : ℕ} (hXy : 2 ≤ X * y) {σ β γ : ℝ} (hσ : 0 ≤ σ)
    (hσβ : σ ≤ β) (hβ1 : β ≤ 1)
    (hdet : 1 / 2 ≤ ‖detPolyChi χ X y ((β : ℂ) + (γ : ℂ) * I)‖) :
    ∃ i < ⌊Real.log (X * y : ℕ)⌋₊ + 1, ∃ j < detBlockCount X y, ∃ m < detBlockCount X y + 8,
      1 / (12 * detBlockCount X y) ≤
        ‖abscissaTaylorPoly (detDyadicBlock X y j) (detCoeffChi χ X y) (Real.log (X * y : ℕ)) m
          (σ + i / Real.log (X * y : ℕ)) γ‖ := by
  set Λ := Real.log (X * y : ℕ) with hΛ
  set J := detBlockCount X y with hJ
  have hJ1 : 1 ≤ J := by rw [hJ, detBlockCount]; omega
  have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast (show 1 < X * y by omega))
  -- the slab
  set i := ⌊(β - σ) * Λ⌋₊ with hi
  have hiΛ : i < ⌊Λ⌋₊ + 1 := by
    rw [Nat.lt_succ_iff]
    refine Nat.floor_le_floor ?_
    nlinarith
  set σ₀ : ℝ := σ + i / Λ with hσ₀
  have hσ₀β : σ₀ ≤ β := by
    have h1 : (i : ℝ) ≤ (β - σ) * Λ := Nat.floor_le (by nlinarith)
    have h2 : (i : ℝ) / Λ ≤ β - σ := by rw [div_le_iff₀ hΛ0]; linarith
    linarith
  have hβσ₀ : (β - σ₀) * Λ ≤ 1 := by
    have h1 : (β - σ) * Λ < i + 1 := Nat.lt_floor_add_one _
    have h2 : (β - σ₀) * Λ = (β - σ) * Λ - i := by rw [hσ₀]; field_simp; ring
    linarith
  have hσ₀0 : 0 ≤ σ₀ := by rw [hσ₀]; positivity
  -- the block
  rw [detPolyChi_eq_sum_blocks] at hdet
  obtain ⟨j, hj, hjbig⟩ := exists_range_norm_ge_div hJ1 _ hdet
  -- the Taylor transfer
  have hβeq : β = σ₀ + (β - σ₀) := by ring
  rw [hβeq] at hjbig
  have hblock1 : ∀ k ∈ detDyadicBlock X y j, 1 ≤ k :=
    fun k hk => (mem_detSupport_le (Finset.mem_filter.mp hk).1).1
  have hblockΛ : ∀ k ∈ detDyadicBlock X y j, Real.log k ≤ Λ := by
    intro k hk
    have hk := mem_detSupport_le (Finset.mem_filter.mp hk).1
    exact Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hk.2)
  have htail : 2 / ((J + 8).factorial : ℝ) *
      ∑ k ∈ detDyadicBlock X y j, ‖detCoeffChi χ X y k‖ * (k : ℝ) ^ (-σ₀) ≤ 1 / 2 / J / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (sum_norm_detCoeffChi_block_le χ X y j hσ₀0)
      (by positivity)) ?_
    have := taylor_tail_factorial_bound hJ1
    rw [show (1 : ℝ) / 2 / J / 2 = 1 / (2 * J) / 2 by ring]
    exact this
  obtain ⟨m, hm, hmbig⟩ := exists_abscissaTaylorPoly_large hblock1 (detCoeffChi χ X y)
    (sub_nonneg.mpr hσ₀β) hΛ0 hblockΛ hβσ₀ (by omega) hjbig htail
  refine ⟨i, hiΛ, j, hj, m, hm, le_trans (le_of_eq ?_) hmbig⟩
  field_simp
  ring

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
