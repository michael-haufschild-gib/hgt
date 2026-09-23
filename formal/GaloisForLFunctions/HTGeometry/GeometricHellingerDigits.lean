import GaloisForLFunctions.HTGeometry.EulerBinaryProduct
import GaloisForLFunctions.HTGeometry.PrimeValuationKakutaniSector

/-!
# The Hellinger affinity of a geometric law factorizes over its binary digits

Under the binary-digit isomorphism the geometric law with ratio `a` becomes the product of
independent Bernoulli digits, the `j`-th having success probability `a ^ (2 : ℕ) ^ j / (1 + a ^ (2 : ℕ) ^ j)`.
Hellinger affinity is multiplicative on product measures, so the affinity of two geometric laws is
the product of the affinities of their digits:

`√((1-a)(1-b)) / (1 - √(ab)) = ∏_{j ≥ 0} (1 + √(ab) ^ (2 : ℕ) ^ j) / √((1 + a ^ (2 : ℕ) ^ j)(1 + b ^ (2 : ℕ) ^ j))`.

Both sides are computed from Euler's binary product, and the identity `1 - ab = (1 - √(ab))(1 + √(ab))`
is what makes the two closed forms agree.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Filter Topology

/-- The Hellinger affinity of the `j`-th binary digit of two geometric laws. -/
noncomputable def bitHellingerAffinity (a b : ℝ) (j : ℕ) : ℝ :=
  (1 + Real.sqrt (a * b) ^ (2 : ℕ) ^ j) / Real.sqrt ((1 + a ^ (2 : ℕ) ^ j) * (1 + b ^ (2 : ℕ) ^ j))

theorem prod_sqrt_range {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (J : ℕ) :
    ∏ j ∈ Finset.range J, Real.sqrt (f j) = Real.sqrt (∏ j ∈ Finset.range J, f j) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih,
        Real.sqrt_mul (Finset.prod_nonneg fun j _ => hf j)]

/-- **The digit factorization of the geometric Hellinger affinity.** -/
theorem tendsto_prod_bitHellingerAffinity {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) :
    Tendsto (fun J => ∏ j ∈ Finset.range J, bitHellingerAffinity a b j) atTop
      (nhds (geometricHellingerAffinity a b)) := by
  set s : ℝ := Real.sqrt (a * b) with hs
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hablt : a * b < 1 := by nlinarith
  have hs1 : s < 1 := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hab0 hablt
  have hsden : (1 : ℝ) - s ≠ 0 := by linarith
  have haden : (1 : ℝ) - a ≠ 0 := by linarith
  have hbden : (1 : ℝ) - b ≠ 0 := by linarith
  -- the partial products in closed form
  have hnum : ∀ J : ℕ, ∏ j ∈ Finset.range J, (1 + s ^ (2 : ℕ) ^ j) = (1 - s ^ (2 : ℕ) ^ J) / (1 - s) := by
    intro J
    rw [eq_div_iff hsden, mul_comm]
    exact one_sub_mul_prod_one_add_pow s J
  have hprodpos : ∀ (c : ℝ), 0 ≤ c → ∀ J : ℕ, 0 ≤ ∏ j ∈ Finset.range J, (1 + c ^ (2 : ℕ) ^ j) := by
    intro c hc J
    exact Finset.prod_nonneg fun j _ => by positivity
  have hden : ∀ J : ℕ,
      ∏ j ∈ Finset.range J, Real.sqrt ((1 + a ^ (2 : ℕ) ^ j) * (1 + b ^ (2 : ℕ) ^ j))
        = Real.sqrt (((1 - a ^ (2 : ℕ) ^ J) / (1 - a)) * ((1 - b ^ (2 : ℕ) ^ J) / (1 - b))) := by
    intro J
    rw [prod_sqrt_range (fun j => by positivity) J]
    congr 1
    rw [Finset.prod_mul_distrib]
    have ha := one_sub_mul_prod_one_add_pow a J
    have hb := one_sub_mul_prod_one_add_pow b J
    rw [← ha, ← hb]
    field_simp
  have hpart : ∀ J : ℕ, ∏ j ∈ Finset.range J, bitHellingerAffinity a b j
      = ((1 - s ^ (2 : ℕ) ^ J) / (1 - s))
        / Real.sqrt (((1 - a ^ (2 : ℕ) ^ J) / (1 - a)) * ((1 - b ^ (2 : ℕ) ^ J) / (1 - b))) := by
    intro J
    simp only [bitHellingerAffinity]
    rw [Finset.prod_div_distrib, hnum J, hden J]
  simp only [hpart]
  -- pass to the limit
  have hpow : ∀ c : ℝ, |c| < 1 → Tendsto (fun J : ℕ => c ^ (2 : ℕ) ^ J) atTop (nhds 0) := by
    intro c hc
    have h1 : Tendsto (fun J : ℕ => (2 : ℕ) ^ J) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
    exact (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).comp h1
  have habs : ∀ c : ℝ, 0 ≤ c → c < 1 → |c| < 1 := fun c h0 h1 => by
    rw [abs_of_nonneg h0]; exact h1
  have hnumlim : Tendsto (fun J : ℕ => (1 - s ^ (2 : ℕ) ^ J) / (1 - s)) atTop (nhds ((1 - 0) / (1 - s))) :=
    (tendsto_const_nhds.sub (hpow s (habs s hs0 hs1))).div_const _
  have hdenlim : Tendsto
      (fun J : ℕ => ((1 - a ^ (2 : ℕ) ^ J) / (1 - a)) * ((1 - b ^ (2 : ℕ) ^ J) / (1 - b))) atTop
      (nhds (((1 - 0) / (1 - a)) * ((1 - 0) / (1 - b)))) :=
    ((tendsto_const_nhds.sub (hpow a (habs a ha0 ha1))).div_const _).mul
      ((tendsto_const_nhds.sub (hpow b (habs b hb0 hb1))).div_const _)
  have hsqrtlim := (Real.continuous_sqrt.tendsto _).comp hdenlim
  have hpos : (0 : ℝ) < ((1 - 0) / (1 - a)) * ((1 - 0) / (1 - b)) := by
    have h1 : (0 : ℝ) < 1 - a := by linarith
    have h2 : (0 : ℝ) < 1 - b := by linarith
    positivity
  have hsqrtne : Real.sqrt (((1 - 0) / (1 - a)) * ((1 - 0) / (1 - b))) ≠ 0 := by
    positivity
  have hA : (0 : ℝ) < 1 - a := by linarith
  have hB : (0 : ℝ) < 1 - b := by linarith
  have hval : ((1 - 0) / (1 - s)) / Real.sqrt (((1 - 0) / (1 - a)) * ((1 - 0) / (1 - b)))
      = geometricHellingerAffinity a b := by
    have hrw : ((1 : ℝ) - 0) / (1 - a) * ((1 - 0) / (1 - b)) = ((1 - a) * (1 - b))⁻¹ := by
      rw [sub_zero, one_div, one_div, ← mul_inv]
    have hsq : Real.sqrt ((1 - a) * (1 - b)) ≠ 0 := by positivity
    rw [hrw, Real.sqrt_inv, geometricHellingerAffinity, ← hs]
    field_simp
    ring
  rw [← hval]
  exact hnumlim.div hsqrtlim hsqrtne

/-- **The parity split of the affinity.**  The ratio of the first digit's affinity to the whole
geometric affinity is the closed form whose square is the data-processing comparison. -/
theorem bitHellingerAffinity_zero_div_geometric {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    bitHellingerAffinity a b 0 / geometricHellingerAffinity a b
      = (1 - a * b) / Real.sqrt ((1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ))) := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hs2 : Real.sqrt (a * b) ^ (2 : ℕ) = a * b := Real.sq_sqrt hab0
  have hA : (0 : ℝ) < 1 - a := by linarith
  have hB : (0 : ℝ) < 1 - b := by linarith
  have hden1 : Real.sqrt ((1 + a) * (1 + b)) ≠ 0 := by positivity
  have hden2 : Real.sqrt ((1 - a) * (1 - b)) ≠ 0 := by positivity
  have hablt : a * b < 1 := by nlinarith
  have hs1 : Real.sqrt (a * b) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hab0 hablt
  have hden3 : (1 : ℝ) - Real.sqrt (a * b) ≠ 0 := by linarith
  have h1 : Real.sqrt ((1 + a) * (1 + b)) * Real.sqrt ((1 - a) * (1 - b))
      = Real.sqrt ((1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ))) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hL : bitHellingerAffinity a b 0 / geometricHellingerAffinity a b
      = ((1 + Real.sqrt (a * b)) * (1 - Real.sqrt (a * b)))
        / (Real.sqrt ((1 + a) * (1 + b)) * Real.sqrt ((1 - a) * (1 - b))) := by
    rw [bitHellingerAffinity, geometricHellingerAffinity]
    norm_num
    field_simp
  rw [hL, h1]
  congr 1
  linear_combination -hs2

/-- **The parity data-processing inequality.**  Forgetting the paired part of the valuation cannot
decrease the Hellinger affinity; algebraically the square of the comparison is `(a - b)^(2 : ℕ) ≥ 0`. -/
theorem one_le_parity_affinity_ratio {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) : 1 ≤ (1 - a * b) / Real.sqrt ((1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ))) := by
  have hA : (0 : ℝ) < 1 - a := by linarith
  have hB : (0 : ℝ) < 1 - b := by linarith
  have h1 : (0 : ℝ) < 1 - a ^ (2 : ℕ) := by nlinarith [mul_pos hA (show (0 : ℝ) < 1 + a by linarith)]
  have h2 : (0 : ℝ) < 1 - b ^ (2 : ℕ) := by nlinarith [mul_pos hB (show (0 : ℝ) < 1 + b by linarith)]
  have hprod : (0 : ℝ) < (1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ)) := mul_pos h1 h2
  have hpos : 0 < Real.sqrt ((1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ))) := Real.sqrt_pos.mpr hprod
  have hab : (0 : ℝ) < 1 - a * b := by nlinarith
  have hkey : (1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ)) ≤ (1 - a * b) ^ (2 : ℕ) := by nlinarith [sq_nonneg (a - b)]
  rw [le_div_iff₀ hpos]
  calc (1 : ℝ) * Real.sqrt ((1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ)))
      = Real.sqrt ((1 - a ^ (2 : ℕ)) * (1 - b ^ (2 : ℕ))) := one_mul _
    _ ≤ Real.sqrt ((1 - a * b) ^ (2 : ℕ)) := Real.sqrt_le_sqrt hkey
    _ = 1 - a * b := by rw [Real.sqrt_sq hab.le]

end GaloisForLFunctions.HTGeometry
