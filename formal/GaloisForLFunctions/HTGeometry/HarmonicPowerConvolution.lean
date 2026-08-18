import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds
import Mathlib.Analysis.MeanInequalities

/-!
# Decay of a harmonic convolution on the integer lattice

For exponents `1/2 < β ≤ 1` the lattice convolution `∑_l (1+|l|)^{-β} (1+|j-l|)^{-1}` decays in
`j`: it is at most `2^γ (1+|j|)^{-γ}` times a fixed finite constant, for every `0 < γ < β`.

Two ingredients only.  A weighted AM–GM collapses any product `(1+|l|)^{-a} (1+|j-l|)^{-b}` with
positive exponents to the convex combination of the two pure power weights at exponent `a + b`,
so such a convolution is bounded by the fixed translation-invariant total weight
`∑ intPowWeight (a+b)`.  And on the region where `1+|j| ≤ 2(1+|j-l|)` a factor `(1+|j-l|)^{-γ}`
may be exchanged for `2^γ (1+|j|)^{-γ}`; the complementary region exchanges `(1+|l|)^{-γ}`
instead, and one of the two always applies because `|j| ≤ |l| + |j-l|`.
-/

open scoped ENNReal

namespace GaloisForLFunctions

/-- Weighted AM–GM on the lattice: a product of power weights with positive exponents is
dominated by the convex combination of the two pure weights at the summed exponent. -/
theorem powConv_pointwise_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 / (x ^ a * y ^ b)
      ≤ a / (a + b) * (1 / x ^ (a + b)) + b / (a + b) * (1 / y ^ (a + b)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hu : (0 : ℝ) ≤ x ^ (-(a + b)) := (Real.rpow_pos_of_pos hx0 _).le
  have hv : (0 : ℝ) ≤ y ^ (-(a + b)) := (Real.rpow_pos_of_pos hy0 _).le
  have hθ : a / (a + b) + b / (a + b) = 1 := by
    have : a + b ≠ 0 := by positivity
    field_simp
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (by positivity : (0 : ℝ) ≤ a / (a + b)) (by positivity : (0 : ℝ) ≤ b / (a + b)) hu hv hθ
  have hxpow : (x ^ (-(a + b))) ^ (a / (a + b)) = x ^ (-a) := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    have : a + b ≠ 0 := by positivity
    field_simp
  have hypow : (y ^ (-(a + b))) ^ (b / (a + b)) = y ^ (-b) := by
    rw [← Real.rpow_mul hy0.le]
    congr 1
    have : a + b ≠ 0 := by positivity
    field_simp
  rw [hxpow, hypow] at hgm
  calc 1 / (x ^ a * y ^ b) = x ^ (-a) * y ^ (-b) := by
        rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le, one_div, mul_inv]
    _ ≤ a / (a + b) * x ^ (-(a + b)) + b / (a + b) * y ^ (-(a + b)) := hgm
    _ = a / (a + b) * (1 / x ^ (a + b)) + b / (a + b) * (1 / y ^ (a + b)) := by
        rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le, one_div, one_div]

/-- Translation invariance of the total power weight. -/
theorem tsum_intPowWeight_sub (s : ℝ) (j : ℤ) :
    (∑' l : ℤ, intPowWeight s (j - l)) = ∑' l : ℤ, intPowWeight s l :=
  Equiv.tsum_eq (Equiv.subLeft j) (fun x : ℤ => intPowWeight s x)

/-- **Uniform bound for a lattice power convolution.**  For positive exponents the convolution is
at most the fixed translation-invariant total weight at the summed exponent. -/
theorem tsum_powConv_le (j : ℤ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∑' l : ℤ, ENNReal.ofReal
        (1 / ((1 + |(l : ℝ)|) ^ a * (1 + |((j - l : ℤ) : ℝ)|) ^ b))
      ≤ ∑' l : ℤ, intPowWeight (a + b) l := by
  have hpt : ∀ l : ℤ,
      ENNReal.ofReal (1 / ((1 + |(l : ℝ)|) ^ a * (1 + |((j - l : ℤ) : ℝ)|) ^ b))
        ≤ ENNReal.ofReal (a / (a + b)) * intPowWeight (a + b) l +
          ENNReal.ofReal (b / (a + b)) * intPowWeight (a + b) (j - l) := by
    intro l
    have hx : (1 : ℝ) ≤ 1 + |(l : ℝ)| := by
      have := abs_nonneg ((l : ℝ)); linarith
    have hy : (1 : ℝ) ≤ 1 + |((j - l : ℤ) : ℝ)| := by
      have := abs_nonneg (((j - l : ℤ) : ℝ)); linarith
    have hx0 : (0 : ℝ) < 1 + |(l : ℝ)| := by linarith
    have hy0 : (0 : ℝ) < 1 + |((j - l : ℤ) : ℝ)| := by linarith
    have hxp : (0 : ℝ) < (1 + |(l : ℝ)|) ^ (a + b) := Real.rpow_pos_of_pos hx0 _
    have hyp : (0 : ℝ) < (1 + |((j - l : ℤ) : ℝ)|) ^ (a + b) := Real.rpow_pos_of_pos hy0 _
    refine le_trans (ENNReal.ofReal_le_ofReal (powConv_pointwise_le ha hb hx hy)) ?_
    refine le_of_eq ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), intPowWeight, intPowWeight,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    tsum_intPowWeight_sub, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hone : a / (a + b) + b / (a + b) = 1 := by
    have : a + b ≠ 0 := by positivity
    field_simp
  rw [hone, ENNReal.ofReal_one, one_mul]

/-- One power of `γ` moves from a factor to the center of the convolution: whenever
`Z ≤ 2 Y`, the factor `Y^{-γ}` is at most `2^γ Z^{-γ}`. -/
theorem rpow_neg_center_exchange {γ : ℝ} (hγ : 0 < γ) {Y Z : ℝ}
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) (h : Z ≤ 2 * Y) :
    1 / Y ^ γ ≤ 2 ^ γ / Z ^ γ := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hhalf : Z / 2 ≤ Y := by linarith
  have hrpow : (Z / 2) ^ γ ≤ Y ^ γ :=
    Real.rpow_le_rpow (by positivity) hhalf hγ.le
  have hdiv : (Z / 2) ^ γ = Z ^ γ / 2 ^ γ := Real.div_rpow hZ0.le (by norm_num) γ
  have h2 : (0 : ℝ) < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
  have hZp : (0 : ℝ) < Z ^ γ := Real.rpow_pos_of_pos hZ0 γ
  have hYp : (0 : ℝ) < Y ^ γ := Real.rpow_pos_of_pos hY0 γ
  have hkey : Z ^ γ / 2 ^ γ ≤ Y ^ γ := by rw [← hdiv]; exact hrpow
  rw [div_le_div_iff₀ hYp hZp, one_mul]
  calc Z ^ γ = 2 ^ γ * (Z ^ γ / 2 ^ γ) := by field_simp
    _ ≤ 2 ^ γ * Y ^ γ := mul_le_mul_of_nonneg_left hkey h2.le

/-- **Decay of the harmonic power convolution.**  For `1/2 < β ≤ 1` and `0 < γ < β`, the lattice
convolution of `(1+|l|)^{-β}` with the harmonic weight decays like `(1+|j|)^{-γ}`, with twice the
fixed total weight at exponent `β + 1 - γ` as constant. -/
theorem tsum_harmonicPowConv_le (j : ℤ) {β γ : ℝ} (hβone : β ≤ 1)
    (hγ0 : 0 < γ) (hγβ : γ < β) :
    ∑' l : ℤ, ENNReal.ofReal
        (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|)))
      ≤ ENNReal.ofReal (2 ^ γ / (1 + |(j : ℝ)|) ^ γ) *
        (2 * ∑' l : ℤ, intPowWeight (β + 1 - γ) l) := by
  have hγ1 : γ < 1 := lt_of_lt_of_le hγβ hβone
  have hpt : ∀ l : ℤ,
      1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|))
        ≤ 2 ^ γ / (1 + |(j : ℝ)|) ^ γ *
          (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 - γ)) +
            1 / ((1 + |(l : ℝ)|) ^ (β - γ) * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 : ℝ))) := by
    intro l
    set X : ℝ := 1 + |(l : ℝ)| with hXdef
    set Y : ℝ := 1 + |((j - l : ℤ) : ℝ)| with hYdef
    set Z : ℝ := 1 + |(j : ℝ)| with hZdef
    have hX1 : (1 : ℝ) ≤ X := by
      have := abs_nonneg ((l : ℝ)); simp only [hXdef]; linarith
    have hY1 : (1 : ℝ) ≤ Y := by
      have := abs_nonneg (((j - l : ℤ) : ℝ)); simp only [hYdef]; linarith
    have hZ1 : (1 : ℝ) ≤ Z := by
      have := abs_nonneg ((j : ℝ)); simp only [hZdef]; linarith
    have hX0 : (0 : ℝ) < X := by linarith
    have hY0 : (0 : ℝ) < Y := by linarith
    rw [Real.rpow_one]
    have htri : Z ≤ X + Y := by
      have hcast : ((j - l : ℤ) : ℝ) = (j : ℝ) - (l : ℝ) := by push_cast; ring
      have hsum : (j : ℝ) = (l : ℝ) + ((j : ℝ) - (l : ℝ)) := by ring
      have habs : |(j : ℝ)| ≤ |(l : ℝ)| + |(j : ℝ) - (l : ℝ)| := by
        calc |(j : ℝ)| = |(l : ℝ) + ((j : ℝ) - (l : ℝ))| := by rw [← hsum]
          _ ≤ |(l : ℝ)| + |(j : ℝ) - (l : ℝ)| := abs_add_le _ _
      simp only [hXdef, hYdef, hZdef, hcast]
      linarith
    have hXβ : (0 : ℝ) < X ^ β := Real.rpow_pos_of_pos hX0 _
    have hY1γ : (0 : ℝ) < Y ^ (1 - γ) := Real.rpow_pos_of_pos hY0 _
    have hXβγ : (0 : ℝ) < X ^ (β - γ) := Real.rpow_pos_of_pos hX0 _
    have hXγ : (0 : ℝ) < X ^ γ := Real.rpow_pos_of_pos hX0 _
    have hYγ : (0 : ℝ) < Y ^ γ := Real.rpow_pos_of_pos hY0 _
    have hB₁nn : (0 : ℝ) ≤ 1 / (X ^ β * Y ^ (1 - γ)) := by positivity
    have hB₂nn : (0 : ℝ) ≤ 1 / (X ^ (β - γ) * Y) := by positivity
    have hcoef : (0 : ℝ) ≤ 2 ^ γ / Z ^ γ := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
      have hZγ : (0 : ℝ) < Z ^ γ := Real.rpow_pos_of_pos (by linarith) γ
      positivity
    rcases le_total X Y with hXY | hYX
    · -- the moving factor is the large one: exchange `Y^{-γ}`
      have hZY : Z ≤ 2 * Y := by linarith
      have hexch := rpow_neg_center_exchange hγ0 hY1 hZ1 hZY
      have hYsplit : Y ^ (1 - γ) * Y ^ γ = Y := by
        rw [← Real.rpow_add hY0, sub_add_cancel, Real.rpow_one]
      have hmain : 1 / (X ^ β * Y) = 1 / (X ^ β * Y ^ (1 - γ)) * (1 / Y ^ γ) := by
        rw [div_mul_div_comm, one_mul, mul_assoc, hYsplit]
      calc 1 / (X ^ β * Y)
          ≤ 1 / (X ^ β * Y ^ (1 - γ)) * (2 ^ γ / Z ^ γ) := by
            rw [hmain]
            exact mul_le_mul_of_nonneg_left hexch (by positivity)
        _ = 2 ^ γ / Z ^ γ * (1 / (X ^ β * Y ^ (1 - γ))) := by ring
        _ ≤ 2 ^ γ / Z ^ γ *
              (1 / (X ^ β * Y ^ (1 - γ)) + 1 / (X ^ (β - γ) * Y)) := by
            refine mul_le_mul_of_nonneg_left ?_ hcoef
            linarith
    · -- the fixed factor is the large one: exchange `X^{-γ}`
      have hZX : Z ≤ 2 * X := by linarith
      have hexch := rpow_neg_center_exchange hγ0 hX1 hZ1 hZX
      have hXsplit : X ^ (β - γ) * X ^ γ = X ^ β := by
        rw [← Real.rpow_add hX0, sub_add_cancel]
      have hmain : 1 / (X ^ β * Y) = 1 / (X ^ (β - γ) * Y) * (1 / X ^ γ) := by
        rw [div_mul_div_comm, one_mul, mul_right_comm, hXsplit]
      calc 1 / (X ^ β * Y)
          ≤ 1 / (X ^ (β - γ) * Y) * (2 ^ γ / Z ^ γ) := by
            rw [hmain]
            exact mul_le_mul_of_nonneg_left hexch (by positivity)
        _ = 2 ^ γ / Z ^ γ * (1 / (X ^ (β - γ) * Y)) := by ring
        _ ≤ 2 ^ γ / Z ^ γ *
              (1 / (X ^ β * Y ^ (1 - γ)) + 1 / (X ^ (β - γ) * Y)) := by
            refine mul_le_mul_of_nonneg_left ?_ hcoef
            linarith
  -- sum the pointwise bound
  have hcoefnn : (0 : ℝ) ≤ 2 ^ γ / (1 + |(j : ℝ)|) ^ γ := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
    have hZγ : (0 : ℝ) < (1 + |(j : ℝ)|) ^ γ :=
      Real.rpow_pos_of_pos (by have := abs_nonneg ((j : ℝ)); linarith) γ
    positivity
  have hsum : ∑' l : ℤ, ENNReal.ofReal
      (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|)))
      ≤ ENNReal.ofReal (2 ^ γ / (1 + |(j : ℝ)|) ^ γ) *
        ((∑' l : ℤ, ENNReal.ofReal
            (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 - γ)))) +
          ∑' l : ℤ, ENNReal.ofReal
            (1 / ((1 + |(l : ℝ)|) ^ (β - γ) * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 : ℝ)))) := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun l => ?_
    refine le_trans (ENNReal.ofReal_le_ofReal (hpt l)) ?_
    have hB₁nn : (0 : ℝ) ≤
        1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 - γ)) := by
      have h1 : (0 : ℝ) < (1 + |(l : ℝ)|) ^ β :=
        Real.rpow_pos_of_pos (by have := abs_nonneg ((l : ℝ)); linarith) _
      have h2 : (0 : ℝ) < (1 + |((j - l : ℤ) : ℝ)|) ^ (1 - γ) :=
        Real.rpow_pos_of_pos (by have := abs_nonneg (((j - l : ℤ) : ℝ)); linarith) _
      positivity
    have hB₂nn : (0 : ℝ) ≤
        1 / ((1 + |(l : ℝ)|) ^ (β - γ) * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 : ℝ)) := by
      have h1 : (0 : ℝ) < (1 + |(l : ℝ)|) ^ (β - γ) :=
        Real.rpow_pos_of_pos (by have := abs_nonneg ((l : ℝ)); linarith) _
      have h2 : (0 : ℝ) < (1 + |((j - l : ℤ) : ℝ)|) ^ (1 : ℝ) :=
        Real.rpow_pos_of_pos (by have := abs_nonneg (((j - l : ℤ) : ℝ)); linarith) _
      positivity
    rw [ENNReal.ofReal_mul hcoefnn, ENNReal.ofReal_add hB₁nn hB₂nn]
  refine hsum.trans ?_
  refine mul_le_mul_right ?_ _
  have h₁ : (∑' l : ℤ, ENNReal.ofReal
      (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 - γ))))
      ≤ ∑' l : ℤ, intPowWeight (β + 1 - γ) l := by
    have h := tsum_powConv_le j (a := β) (b := 1 - γ) (by linarith) (by linarith)
    have hexp : β + (1 - γ) = β + 1 - γ := by ring
    rwa [hexp] at h
  have h₂ : (∑' l : ℤ, ENNReal.ofReal
      (1 / ((1 + |(l : ℝ)|) ^ (β - γ) * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 : ℝ))))
      ≤ ∑' l : ℤ, intPowWeight (β + 1 - γ) l := by
    have h := tsum_powConv_le j (a := β - γ) (b := 1) (by linarith) (by norm_num)
    have hexp : β - γ + 1 = β + 1 - γ := by ring
    rwa [hexp] at h
  calc (∑' l : ℤ, ENNReal.ofReal
        (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 - γ)))) +
      ∑' l : ℤ, ENNReal.ofReal
        (1 / ((1 + |(l : ℝ)|) ^ (β - γ) * (1 + |((j - l : ℤ) : ℝ)|) ^ (1 : ℝ)))
      ≤ (∑' l : ℤ, intPowWeight (β + 1 - γ) l) +
        ∑' l : ℤ, intPowWeight (β + 1 - γ) l := add_le_add h₁ h₂
    _ = 2 * ∑' l : ℤ, intPowWeight (β + 1 - γ) l := (two_mul _).symm


/-! ## The real-valued form -/

/-- The harmonic power convolution is summable for every positive exponent. -/
theorem summable_harmonicPowConv (j : ℤ) {β : ℝ} (hβ : 0 < β) :
    Summable (fun l : ℤ => 1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|))) := by
  have hβ1 : (1 : ℝ) < β + 1 := by linarith
  have hleft : Summable (fun l : ℤ => β / (β + 1) * (1 / (1 + |(l : ℝ)|) ^ (β + 1))) :=
    (summable_one_div_one_add_abs_rpow hβ1).mul_left _
  have hbase : Summable (fun l : ℤ => 1 / (β + 1) * (1 / (1 + |(l : ℝ)|) ^ (β + 1))) :=
    (summable_one_div_one_add_abs_rpow hβ1).mul_left _
  have hright : Summable
      (fun l : ℤ => 1 / (β + 1) * (1 / (1 + |((j - l : ℤ) : ℝ)|) ^ (β + 1))) := by
    have := (Equiv.subLeft j).summable_iff
      (f := fun l : ℤ => 1 / (β + 1) * (1 / (1 + |(l : ℝ)|) ^ (β + 1)))
    exact this.mpr hbase
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) (hleft.add hright)
  have hx : (1 : ℝ) ≤ 1 + |(l : ℝ)| := by
    have := abs_nonneg ((l : ℝ)); linarith
  have hy : (1 : ℝ) ≤ 1 + |((j - l : ℤ) : ℝ)| := by
    have := abs_nonneg (((j - l : ℤ) : ℝ)); linarith
  have hpt := powConv_pointwise_le hβ (by norm_num : (0 : ℝ) < 1) hx hy
  rw [Real.rpow_one] at hpt
  exact hpt

/-- **Decay of the harmonic power convolution, in real form.**  The same statement as
`tsum_harmonicPowConv_le` with both sides real. -/
theorem tsum_harmonicPowConv_real_le (j : ℤ) {β γ : ℝ} (hβone : β ≤ 1)
    (hγ0 : 0 < γ) (hγβ : γ < β) :
    ∑' l : ℤ, 1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|))
      ≤ 2 ^ γ * (2 * (∑' x : ℤ, intPowWeight (β + 1 - γ) x).toReal)
          / (1 + |(j : ℝ)|) ^ γ := by
  have hβ0 : (0 : ℝ) < β := lt_trans hγ0 hγβ
  have hWtop : (∑' x : ℤ, intPowWeight (β + 1 - γ) x) ≠ ⊤ :=
    tsum_intPowWeight_ne_top (by linarith)
  have hWof : ENNReal.ofReal ((∑' x : ℤ, intPowWeight (β + 1 - γ) x).toReal)
      = ∑' x : ℤ, intPowWeight (β + 1 - γ) x := ENNReal.ofReal_toReal hWtop
  have hWnn : (0 : ℝ) ≤ (∑' x : ℤ, intPowWeight (β + 1 - γ) x).toReal := ENNReal.toReal_nonneg
  have hsummable := summable_harmonicPowConv j hβ0
  have hjpos : (0 : ℝ) < (1 + |(j : ℝ)|) ^ γ := by
    have := abs_nonneg ((j : ℝ))
    exact Real.rpow_pos_of_pos (by linarith) γ
  have h2γ : (0 : ℝ) < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
  have hRHSnn : (0 : ℝ) ≤ 2 ^ γ * (2 * (∑' x : ℤ, intPowWeight (β + 1 - γ) x).toReal)
      / (1 + |(j : ℝ)|) ^ γ := by positivity
  have hconv := tsum_harmonicPowConv_le j hβone hγ0 hγβ
  have hofsum : ENNReal.ofReal
      (∑' l : ℤ, 1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|)))
      = ∑' l : ℤ, ENNReal.ofReal
        (1 / ((1 + |(l : ℝ)|) ^ β * (1 + |((j - l : ℤ) : ℝ)|))) :=
    ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) hsummable
  have hRHS : ENNReal.ofReal (2 ^ γ / (1 + |(j : ℝ)|) ^ γ) *
      (2 * ∑' x : ℤ, intPowWeight (β + 1 - γ) x)
      = ENNReal.ofReal (2 ^ γ * (2 * (∑' x : ℤ, intPowWeight (β + 1 - γ) x).toReal)
          / (1 + |(j : ℝ)|) ^ γ) := by
    have h2W : (2 : ℝ≥0∞) * (∑' x : ℤ, intPowWeight (β + 1 - γ) x)
        = ENNReal.ofReal (2 * (∑' x : ℤ, intPowWeight (β + 1 - γ) x).toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, hWof]
    rw [h2W, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hofsum.symm, hRHS] at hconv
  exact (ENNReal.ofReal_le_ofReal_iff hRHSnn).mp hconv

end GaloisForLFunctions
