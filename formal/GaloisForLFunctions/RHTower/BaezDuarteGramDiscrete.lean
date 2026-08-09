import GaloisForLFunctions.RHTower.FractSqConstSeries

/-!
# The discrete Báez-Duarte Gram matrix, evaluated exactly

`BaezDuarteGramReduction` reduced the Gram diagonal to two scalars and identified the cross tail
`∫₁^∞ {θv}{v}v^{-2}dv` as the obstruction, because the cells of `{θv}` and `{v}` interleave.  That is true of
the *pieces*.  It is not true of the Gram entry itself at `θ = 1/m`, and the reason is the Báez-Duarte
normalisation.

On the cell `(n, n+1)` both fractional parts are linear — `⌊v/m⌋` cannot jump inside an interval between
consecutive integers, since a multiple of `m` is an integer — so with `q = ⌊n/m⌋`,

`{v/m} − (1/m){v} = (v/m − q) − (v − n)/m = (n − mq)/m = (n mod m)/m`,

**a constant.**  The generator `bdGenReal (1/m)` is therefore `(n mod m)/(m·v)` on each cell, the product of
two generators is a constant times `v^{-2}`, and `∫_n^{n+1} v^{-2} = 1/(n(n+1))`.  Summing the cells:

**`hasSum_bdGram_discrete` — `bdGram (1/m₁) (1/m₂) = ∑_{n≥1} (n mod m₁)(n mod m₂) / (m₁ m₂ n(n+1))`.**

Every term is rational and the series converges like `∑1/n²`.  So the *entire* Gram matrix of the discrete
Báez-Duarte system — the system its criterion actually uses — is an explicit convergent series of rationals,
and the last unevaluated object of the reduction is gone for that system.

Two sanity points, both immediate from the formula: at `m = 1` every term vanishes, matching
`bdGen 1 = 0`; and at `m₁ = m₂ = 2` the series is `(1/4)∑_{n odd} 1/(n(n+1))`, whose value `log 2/4` is
above the Cauchy–Schwarz floor `(θ log θ)² = (log 2)²/4 · … ` of `sq_le_bdGram_self`.  Closed forms of these
series carry logarithms — that is where the classical cotangent structure lives — but the series themselves
need nothing beyond cell cutting.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-- Inside a cell between consecutive integers, `⌊v/m⌋` is the integer quotient of the left endpoint. -/
theorem floor_div_eq_of_mem_cell {a m k : ℕ} (hm : 1 ≤ m) (hk : k = a / m) {v : ℝ}
    (hv : v ∈ Ioo ((a : ℝ)) ((a : ℝ) + 1)) :
    ⌊v / (m : ℝ)⌋ = (k : ℤ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkm : k * m ≤ a := by rw [hk]; exact Nat.div_mul_le_self a m
  have hak : a < (k + 1) * m := by
    have h1 : m * k + a % m = a := by rw [hk]; exact Nat.div_add_mod a m
    have h2 : a % m < m := Nat.mod_lt _ hm
    calc a = m * k + a % m := h1.symm
      _ < m * k + m := Nat.add_lt_add_left h2 _
      _ = (k + 1) * m := by ring
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
  · rw [le_div_iff₀ hm0]
    have : ((k * m : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hkm
    push_cast at this ⊢
    linarith [hv.1]
  · rw [div_lt_iff₀ hm0]
    have hint : a + 1 ≤ (k + 1) * m := hak
    have : ((a : ℕ) : ℝ) + 1 ≤ (((k + 1) * m : ℕ) : ℝ) := by exact_mod_cast hint
    push_cast at this ⊢
    linarith [hv.2]

/-- **The generator is piecewise constant.**  On a cell between consecutive integers the Báez-Duarte
generator at `θ = 1/m` is `(a mod m)/(m·v)`. -/
theorem bdGenReal_inv_nat_eq_of_mem_cell {a m : ℕ} (hm : 1 ≤ m) {v : ℝ}
    (hv : v ∈ Ioo ((a : ℝ)) ((a : ℝ) + 1)) :
    bdGenReal (1 / (m : ℝ)) v = ((a % m : ℕ) : ℝ) / ((m : ℝ) * v) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hv0 : (0 : ℝ) < v := lt_of_le_of_lt (Nat.cast_nonneg a) hv.1
  have hfr : Int.fract v = v - (a : ℝ) := by
    have hfloor : ⌊v⌋ = (a : ℤ) := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast
        exact hv.1.le
      · push_cast
        exact hv.2
    rw [Int.fract, hfloor]
    push_cast
    ring
  have hfr2 : Int.fract (1 / (m : ℝ) * v) = v / (m : ℝ) - ((a / m : ℕ) : ℝ) := by
    have hrw : (1 / (m : ℝ)) * v = v / (m : ℝ) := by ring
    rw [hrw, Int.fract, floor_div_eq_of_mem_cell hm rfl hv]
    rw [Int.cast_natCast]

  have hmod : ((a % m : ℕ) : ℝ) = (a : ℝ) - (m : ℝ) * ((a / m : ℕ) : ℝ) := by
    have hdm := Nat.div_add_mod a m
    have hcast : ((m * (a / m) + a % m : ℕ) : ℝ) = ((a : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hdm
    push_cast at hcast
    linarith
  rw [bdGenReal, hfr, hfr2, hmod]
  field_simp
  ring

/-- The product of two discrete generators is a constant multiple of `v^{-2}` on each cell. -/
theorem bdGenReal_mul_eq_of_mem_cell {a m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) {v : ℝ}
    (hv : v ∈ Ioo ((a : ℝ)) ((a : ℝ) + 1)) :
    bdGenReal (1 / (m₁ : ℝ)) v * bdGenReal (1 / (m₂ : ℝ)) v
      = ((a % m₁ : ℕ) : ℝ) * ((a % m₂ : ℕ) : ℝ) / ((m₁ : ℝ) * (m₂ : ℝ)) * (v⁻¹) ^ 2 := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_lt (Nat.cast_nonneg a) hv.1
  have hvne : v ≠ 0 := ne_of_gt hv0
  rw [bdGenReal_inv_nat_eq_of_mem_cell hm₁ hv, bdGenReal_inv_nat_eq_of_mem_cell hm₂ hv]
  field_simp


/-- A crude bound making the Gram integrand integrable on the tail ray. -/
theorem abs_bdGenReal_mul_le {θ₁ θ₂ : ℝ} (h₁ : |θ₁| ≤ 1) (h₂ : |θ₂| ≤ 1) {v : ℝ} (hv : 0 < v) :
    |bdGenReal θ₁ v * bdGenReal θ₂ v| ≤ 4 * (v⁻¹) ^ 2 := by
  have hb : ∀ θ : ℝ, |θ| ≤ 1 → |bdGenReal θ v| ≤ 2 * v⁻¹ := by
    intro θ hθ
    rw [bdGenReal, abs_div, abs_of_pos hv, div_le_iff₀ hv]
    have h1 : |Int.fract (θ * v) - θ * Int.fract v| ≤ 2 := by
      refine le_trans (abs_sub _ _) ?_
      have hA : |Int.fract (θ * v)| ≤ 1 := by
        rw [abs_of_nonneg (Int.fract_nonneg _)]
        exact (Int.fract_lt_one _).le
      have hB : |θ * Int.fract v| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (Int.fract_nonneg v)]
        calc |θ| * Int.fract v ≤ 1 * 1 :=
              mul_le_mul hθ (Int.fract_lt_one _).le (Int.fract_nonneg _) (by positivity)
          _ = 1 := one_mul 1
      linarith
    calc |Int.fract (θ * v) - θ * Int.fract v| ≤ 2 := h1
      _ = 2 * v⁻¹ * v := by field_simp
  rw [abs_mul]
  calc |bdGenReal θ₁ v| * |bdGenReal θ₂ v| ≤ (2 * v⁻¹) * (2 * v⁻¹) :=
        mul_le_mul (hb θ₁ h₁) (hb θ₂ h₂) (abs_nonneg _) (by positivity)
    _ = 4 * (v⁻¹) ^ 2 := by ring

theorem integrableOn_bdGenReal_mul {θ₁ θ₂ : ℝ} (h₁ : |θ₁| ≤ 1) (h₂ : |θ₂| ≤ 1) :
    IntegrableOn (fun v => bdGenReal θ₁ v * bdGenReal θ₂ v) (Ioi 1) := by
  have hmeas : Measurable (fun v : ℝ => bdGenReal θ₁ v * bdGenReal θ₂ v) := by
    have : ∀ θ : ℝ, Measurable (bdGenReal θ) := by
      intro θ
      exact ((measurable_fract.comp (measurable_const_mul θ)).sub
        ((measurable_const).mul measurable_fract)).div measurable_id
    exact (this θ₁).mul (this θ₂)
  refine Integrable.mono' (g := fun v => 4 * v ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 4)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
  rw [Real.norm_eq_abs, ← inv_sq_eq_rpow hv0]
  exact abs_bdGenReal_mul_le h₁ h₂ hv0

/-- **The Gram entry on one cell.** -/
theorem integral_tailCell_bdGenReal_mul {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (n : ℕ) :
    (∫ v in tailCell n, bdGenReal (1 / (m₁ : ℝ)) v * bdGenReal (1 / (m₂ : ℝ)) v)
      = (((n + 1) % m₁ : ℕ) : ℝ) * (((n + 1) % m₂ : ℕ) : ℝ)
          / ((m₁ : ℝ) * (m₂ : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  set a : ℕ := n + 1 with ha
  have haR : ((a : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [ha]; push_cast; ring
  have hcell : tailCell n = Ioc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1) := by
    rw [tailCell, haR, show ((n : ℝ) + 2) = ((n : ℝ) + 1) + 1 from by ring]
  have hcongr : ∀ v ∈ Ioo ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1),
      bdGenReal (1 / (m₁ : ℝ)) v * bdGenReal (1 / (m₂ : ℝ)) v
        = ((a % m₁ : ℕ) : ℝ) * ((a % m₂ : ℕ) : ℝ) / ((m₁ : ℝ) * (m₂ : ℝ)) * (v⁻¹) ^ 2 :=
    fun v hv => bdGenReal_mul_eq_of_mem_cell hm₁ hm₂ hv
  have hpos : (0 : ℝ) < ((a : ℕ) : ℝ) := by rw [haR]; positivity
  have hle : ((a : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) + 1 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle, Set.mem_Icc]
    intro h
    linarith [h.1]
  have hsq : (∫ v in ((a : ℕ) : ℝ)..(((a : ℕ) : ℝ) + 1), (v⁻¹) ^ 2)
      = 1 / ((a : ℕ) : ℝ) - 1 / (((a : ℕ) : ℝ) + 1) := by
    have hcongr2 : ∀ v ∈ Set.uIcc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1), (v⁻¹) ^ 2 = v ^ (-2 : ℤ) := by
      intro v _
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast, ← inv_pow]
    rw [intervalIntegral.integral_congr hcongr2, integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    have hane : ((a : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
    have hane1 : ((a : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [hcell, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul, hsq]
  have hane : ((a : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
  have hm₁R : ((m₁ : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁
    exact ne_of_gt this
  have hm₂R : ((m₂ : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂
    exact ne_of_gt this
  rw [haR] at hane ⊢
  rw [ha]
  field_simp
  ring

/-- **The discrete Báez-Duarte Gram matrix as an explicit series of rationals.** -/
theorem hasSum_bdGram_discrete {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) :
    HasSum (fun n : ℕ => (((n + 1) % m₁ : ℕ) : ℝ) * (((n + 1) % m₂ : ℕ) : ℝ)
        / ((m₁ : ℝ) * (m₂ : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (bdGram (1 / (m₁ : ℝ)) (1 / (m₂ : ℝ))) := by
  have habs : ∀ m : ℕ, 1 ≤ m → |1 / (m : ℝ)| ≤ 1 := by
    intro m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [abs_of_pos (by positivity)]
    rw [div_le_one hm0]
    exact hm1
  have hint : IntegrableOn (fun v => bdGenReal (1 / (m₁ : ℝ)) v * bdGenReal (1 / (m₂ : ℝ)) v)
      (⋃ n : ℕ, tailCell n) := by
    rw [iUnion_tailCell]
    exact integrableOn_bdGenReal_mul (habs m₁ hm₁) (habs m₂ hm₂)
  have h := MeasureTheory.hasSum_integral_iUnion measurableSet_tailCell
    pairwise_disjoint_tailCell hint
  rw [iUnion_tailCell] at h
  rw [bdGram]
  exact (funext (fun n => integral_tailCell_bdGenReal_mul hm₁ hm₂ n)) ▸ h

/-- **The Gram matrix of the criterion's own system.**  `bdDiscrete i = 1/(i+1)`, so every entry of the
Gram matrix appearing in `bdDistDiscrete` is this rational series. -/
theorem hasSum_bdGram_bdDiscrete (i j : ℕ) :
    HasSum (fun n : ℕ => (((n + 1) % (i + 1) : ℕ) : ℝ) * (((n + 1) % (j + 1) : ℕ) : ℝ)
        / (((i : ℝ) + 1) * ((j : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (bdGram (bdDiscrete i) (bdDiscrete j)) := by
  have hi : bdDiscrete i = 1 / (((i + 1 : ℕ) : ℝ)) := by
    rw [bdDiscrete]
    push_cast
    ring
  have hj : bdDiscrete j = 1 / (((j + 1 : ℕ) : ℝ)) := by
    rw [bdDiscrete]
    push_cast
    ring
  have h := hasSum_bdGram_discrete (m₁ := i + 1) (m₂ := j + 1) (by omega) (by omega)
  rw [hi, hj]
  have hcast : ∀ n : ℕ, (((n + 1) % (i + 1) : ℕ) : ℝ) * (((n + 1) % (j + 1) : ℕ) : ℝ)
      / ((((i + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2))
      = (((n + 1) % (i + 1) : ℕ) : ℝ) * (((n + 1) % (j + 1) : ℕ) : ℝ)
        / (((i : ℝ) + 1) * ((j : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    push_cast
    ring
  exact (funext hcast) ▸ h

end RHTower

end
