import GaloisForLFunctions.ArithmeticPositiveDuality.HerglotzBochnerOnThePositiveRationals
import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal

/-!
# Archimedean positive-definite functions live on the Kronecker line

The archimedean characters `u ↦ u^{ix}` of `ℚ_{>0}` are the points `z_x = (x log p/2π)_p` of the
prime torus (`ratChar_archPoint`); `x ↦ z_x` is a continuous injection of `ℝ` (`log 2/log 3` is
irrational), its image is the **Kronecker line**.

**Theorem** (`spectralMeasure_eq_map_archPoint`). If a positive-definite `f` on `ℚ_{>0}` is the
restriction of a continuous function of `log u`, its spectral measure on the prime torus is the
image of a finite measure `ν` on `ℝ` under `x ↦ z_x`, and `f(u) = ∫ u^{ix} dν(x)`; in particular it
is carried by the Kronecker line (`spectralMeasure_compl_range_archPoint`).

Mechanism: `F(t) = f(e^t)` on the dense subgroup `log ℚ_{>0}` of `ℝ`; continuity carries every
Gram form to `ℝ`, Bochner's theorem on `ℝ` gives `ν`, and uniqueness on the prime torus identifies
the spectral measure with `ν ∘ z⁻¹`.

So positivity on the dilations splits into two worlds: archimedean correlations (Weil's among
them, `ratCorr`) are measures on one line of an infinite-dimensional torus, while the arithmetic
successors force spectra elsewhere.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### The Kronecker line -/

/-- The point `(x log p/2π)_p` of the prime torus: the archimedean character `u ↦ u^{ix}`. -/
def archPoint (x : ℝ) : PrimeTorus := fun p =>
  ((x * Real.log (p : ℕ) / (2 * π) : ℝ) : UnitAddCircle)

theorem continuous_archPoint : Continuous archPoint :=
  continuous_pi fun _ => continuous_quotient_mk'.comp ((continuous_id.mul continuous_const).div_const _)

/-- `log u = Σ_p v_p(u) log p`. -/
theorem log_eq_sum_valFinsupp (u : posUnits) :
    Real.log ((u : ℚˣ) : ℚ) = ∑ p ∈ (valFinsupp ((u : ℚˣ) : ℚ)).support,
      (valFinsupp ((u : ℚˣ) : ℚ) p : ℝ) * Real.log (p : ℕ) := by
  have h := congrArg (fun v : posUnits => (((v : ℚˣ) : ℚ) : ℝ)) (finsuppUnit_valFinsupp u)
  simp only [val_finsuppUnit, Rat.cast_prod, Rat.cast_zpow, Rat.cast_natCast] at h
  rw [← h, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => Real.log_zpow _ _
  · intro p _
    exact zpow_ne_zero _ (by exact_mod_cast p.2.ne_zero)

/-- The archimedean point `z_x` is the character `u ↦ u^{ix}`. -/
theorem ratChar_archPoint (u : posUnits) (x : ℝ) :
    ratChar ((u : ℚˣ) : ℚ) (archPoint x) = cexp (Real.log ((u : ℚˣ) : ℚ) * x * I) := by
  rw [ratChar]
  simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Finsupp.prod]
  rw [log_eq_sum_valFinsupp u, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_mul,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [archPoint, fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- `log 2 / log 3` is irrational: `2^b = 3^a` has no solution with `a ≥ 1`. -/
theorem eq_zero_of_mul_log_two_eq {a b : ℤ} (h : (a : ℝ) * Real.log 3 = b * Real.log 2) :
    a = 0 := by
  by_contra ha
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have habs : (a.natAbs : ℝ) * Real.log 3 = b.natAbs * Real.log 2 := by
    have := congrArg abs h
    rw [abs_mul, abs_mul, abs_of_pos hl2, abs_of_pos hl3] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact this
  have hpow : ((3 ^ a.natAbs : ℕ) : ℝ) = ((2 ^ b.natAbs : ℕ) : ℝ) := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    push_cast
    rw [Real.log_pow, Real.log_pow, habs]
  have hnat : 3 ^ a.natAbs = 2 ^ b.natAbs := by exact_mod_cast hpow
  have ha1 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have hb1 : b.natAbs ≠ 0 := by
    intro hb
    rw [hb, pow_zero] at hnat
    exact absurd hnat (Nat.one_lt_pow ha1 (by norm_num)).ne'
  have h2 : 2 ∣ 3 ^ a.natAbs := hnat ▸ dvd_pow_self 2 hb1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  omega

/-- Distinct real exponents give distinct characters: the Kronecker line is injective. -/
theorem injective_archPoint : Function.Injective archPoint := by
  intro x y hxy
  have hcoord : ∀ p : Nat.Primes, ∃ k : ℤ, (x - y) * Real.log (p : ℕ) = 2 * π * k := by
    intro p
    have h := congrFun hxy p
    simp only [archPoint] at h
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ((QuotientAddGroup.eq_iff_sub_mem).mp h)
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    have hπ : (2 * π) ≠ 0 := by positivity
    field_simp at hk
    linarith
  obtain ⟨k₂, h2⟩ := hcoord ⟨2, Nat.prime_two⟩
  obtain ⟨k₃, h3⟩ := hcoord ⟨3, Nat.prime_three⟩
  have h2' : (x - y) * Real.log 2 = 2 * π * k₂ := by exact_mod_cast h2
  have h3' : (x - y) * Real.log 3 = 2 * π * k₃ := by exact_mod_cast h3
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hk : (k₂ : ℝ) * Real.log 3 = k₃ * Real.log 2 := by
    have : 2 * π * ((k₂ : ℝ) * Real.log 3) = 2 * π * (k₃ * Real.log 2) := by
      calc 2 * π * ((k₂ : ℝ) * Real.log 3) = (2 * π * k₂) * Real.log 3 := by ring
        _ = (x - y) * Real.log 2 * Real.log 3 := by rw [← h2']
        _ = (x - y) * Real.log 3 * Real.log 2 := by ring
        _ = 2 * π * k₃ * Real.log 2 := by rw [h3']
        _ = 2 * π * (k₃ * Real.log 2) := by ring
    exact mul_left_cancel₀ hπ.ne' this
  have hk2 := eq_zero_of_mul_log_two_eq hk
  rw [hk2, Int.cast_zero, mul_zero] at h2'
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rcases mul_eq_zero.mp h2' with h | h
  · linarith
  · exact absurd h hl2

theorem measurableEmbedding_archPoint : MeasurableEmbedding archPoint :=
  continuous_archPoint.measurableEmbedding injective_archPoint

/-! ### Archimedean functions are positive definite on `ℝ` -/

/-- A positive rational close to `e^s`: `⌈(k+1)e^s⌉/(k+1)`. -/
def ratApprox (s : ℝ) (k : ℕ) : posUnits :=
  ⟨Units.mk0 ((⌈(k + 1 : ℝ) * Real.exp s⌉ : ℚ) / (k + 1)) (by
      have : (0 : ℝ) < ⌈(k + 1 : ℝ) * Real.exp s⌉ :=
        lt_of_lt_of_le (by positivity) (Int.le_ceil _)
      have h' : (0 : ℤ) < ⌈(k + 1 : ℝ) * Real.exp s⌉ := by exact_mod_cast this
      positivity), by
    show (0 : ℚ) < (⌈(k + 1 : ℝ) * Real.exp s⌉ : ℚ) / (k + 1)
    have : (0 : ℝ) < ⌈(k + 1 : ℝ) * Real.exp s⌉ := lt_of_lt_of_le (by positivity) (Int.le_ceil _)
    have h' : (0 : ℤ) < ⌈(k + 1 : ℝ) * Real.exp s⌉ := by exact_mod_cast this
    positivity⟩

theorem tendsto_log_ratApprox (s : ℝ) :
    Tendsto (fun k => Real.log ((((ratApprox s k : posUnits) : ℚˣ) : ℚ) : ℝ)) atTop (𝓝 s) := by
  have hval : ∀ k : ℕ, ((((ratApprox s k : posUnits) : ℚˣ) : ℚ) : ℝ) =
      (⌈(k + 1 : ℝ) * Real.exp s⌉ : ℝ) / (k + 1) := fun k => by
    simp [ratApprox]
  have hlim : Tendsto (fun k : ℕ => (⌈(k + 1 : ℝ) * Real.exp s⌉ : ℝ) / (k + 1)) atTop
      (𝓝 (Real.exp s)) := by
    have hlo : ∀ k : ℕ, Real.exp s ≤ (⌈(k + 1 : ℝ) * Real.exp s⌉ : ℝ) / (k + 1) := fun k => by
      rw [le_div_iff₀ (by positivity)]
      linarith [Int.le_ceil ((k + 1 : ℝ) * Real.exp s)]
    have hhi : ∀ k : ℕ, (⌈(k + 1 : ℝ) * Real.exp s⌉ : ℝ) / (k + 1) ≤
        Real.exp s + 1 / ((k : ℝ) + 1) := fun k => by
      rw [div_le_iff₀ (by positivity)]
      have e : (Real.exp s + 1 / ((k : ℝ) + 1)) * ((k : ℝ) + 1) = (k + 1) * Real.exp s + 1 := by
        field_simp
      rw [e]
      linarith [Int.ceil_lt_add_one ((k + 1 : ℝ) * Real.exp s)]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlo hhi
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (Real.exp s)
  simp_rw [hval]
  have := ((Real.continuousAt_log (Real.exp_pos s).ne').tendsto).comp hlim
  rwa [Real.log_exp] at this

/-- **Density.** If `f(u) = F(log u)` with `F` continuous and `f` positive definite on `ℚ_{>0}`, then
`F` is positive definite on `ℝ`. -/
theorem positiveDefiniteOnReal_of_posUnits {f : posUnits → ℂ} (hf : IsPosDefOnGroup f)
    {F : ℝ → ℂ} (hF : Continuous F) (hfF : ∀ u : posUnits, f u = F (Real.log ((u : ℚˣ) : ℚ))) :
    PositiveDefiniteOnReal F := by
  intro N t c
  set S : Set ℂ := {z | 0 ≤ z.re ∧ z.im = 0} with hS
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  set G : ℕ → ℂ := fun k => ∑ i, ∑ j, star (c i) *
    F (Real.log ((((ratApprox (t j) k : posUnits) : ℚˣ) : ℚ) : ℝ) -
      Real.log ((((ratApprox (t i) k : posUnits) : ℚˣ) : ℚ) : ℝ)) * c j with hG
  have hGS : ∀ k, G k ∈ S := by
    intro k
    obtain ⟨r, hr, h⟩ := hf N (fun i => ratApprox (t i) k) c
    have e : G k = (r : ℂ) := by
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hfF]
      congr 2
      have hi : (0 : ℝ) < ((((ratApprox (t i) k : posUnits) : ℚˣ) : ℚ) : ℝ) := by
        exact_mod_cast (ratApprox (t i) k).2
      have hj : (0 : ℝ) < ((((ratApprox (t j) k : posUnits) : ℚˣ) : ℚ) : ℝ) := by
        exact_mod_cast (ratApprox (t j) k).2
      push_cast
      rw [Real.log_mul (inv_pos.mpr hi).ne' hj.ne', Real.log_inv]
      ring
    rw [e]
    exact ⟨by simpa using hr, by simp⟩
  have hlim : Tendsto G atTop (𝓝 (∑ i, ∑ j, star (c i) * F (t j - t i) * c j)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    refine (tendsto_const_nhds.mul ?_).mul tendsto_const_nhds
    exact (hF.tendsto _).comp ((tendsto_log_ratApprox (t j)).sub (tendsto_log_ratApprox (t i)))
  have hmem := hclosed.mem_of_tendsto hlim (Eventually.of_forall hGS)
  refine ⟨_, hmem.1, Complex.ext (by simp) ?_⟩
  rw [Complex.ofReal_im]
  exact hmem.2

/-! ### The spectral measure -/

/-- **Archimedean positive-definite functions on `ℚ_{>0}`.** If `f(u) = F(log u)` with `F`
continuous, then `f(u) = ∫ u^{ix} dν(x)` for a finite positive measure `ν` on `ℝ`. -/
theorem exists_measure_cpow_of_continuous {f : posUnits → ℂ} (hf : IsPosDefOnGroup f)
    {F : ℝ → ℂ} (hF : Continuous F) (hfF : ∀ u : posUnits, f u = F (Real.log ((u : ℚˣ) : ℚ))) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      ∀ u : posUnits, f u = ∫ x, cexp (Real.log ((u : ℚˣ) : ℚ) * x * I) ∂ν := by
  have hPD := positiveDefiniteOnReal_of_posUnits hf hF hfF
  obtain ⟨p, hp0, h1⟩ : ∃ p : ℝ, 0 ≤ p ∧ f 1 = p := by
    obtain ⟨r, hr, h⟩ := hf 1 ![1] ![1]
    exact ⟨r, hr, by simpa using h⟩
  have hF0 : F 0 = p := by
    rw [← h1, hfF 1]; simp
  rcases hp0.lt_or_eq with hpos | hzero
  · have hG : PositiveDefiniteOnReal fun t => ((1 / p : ℝ) : ℂ) * F t := by
      intro N t c
      obtain ⟨r, hr, h⟩ := hPD N t c
      refine ⟨(1 / p) * r, mul_nonneg (by positivity) hr, ?_⟩
      push_cast
      rw [← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hG0 : ((1 / p : ℝ) : ℂ) * F 0 = 1 := by
      rw [hF0]; push_cast; field_simp
    obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_charFun_eq hG hG0
      (continuous_const.mul hF)
    refine ⟨ENNReal.ofReal p • (μ : Measure ℝ), ⟨?_⟩, fun u => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    have hu := hμ (Real.log ((u : ℚˣ) : ℚ))
    rw [charFun_apply_real] at hu
    rw [integral_smul_measure, hu, hfF u, ENNReal.toReal_ofReal hpos.le, Complex.real_smul]
    push_cast
    field_simp
  · refine ⟨0, inferInstance, fun u => ?_⟩
    have := hf.norm_le_posUnits u
    rw [h1, ← hzero, Complex.ofReal_re] at this
    rw [norm_le_zero_iff.mp this, integral_zero_measure]

/-- **The spectral measure of an archimedean positive-definite function is carried by the
Kronecker line.** Every finite measure on the prime torus representing `f(u) = F(log u)`, `F`
continuous, is the image of a finite measure on `ℝ` under `x ↦ z_x`. -/
theorem spectralMeasure_eq_map_archPoint {f : posUnits → ℂ} (hf : IsPosDefOnGroup f)
    {F : ℝ → ℂ} (hF : Continuous F) (hfF : ∀ u : posUnits, f u = F (Real.log ((u : ℚˣ) : ℚ)))
    {μ : Measure PrimeTorus} [IsFiniteMeasure μ]
    (hμ : ∀ u : posUnits, f u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ μ = ν.map archPoint := by
  obtain ⟨ν, hν, hfν⟩ := exists_measure_cpow_of_continuous hf hF hfF
  refine ⟨ν, hν, finiteMeasure_ext_of_ratChar fun u => ?_⟩
  rw [← hμ u, hfν u, integral_map continuous_archPoint.aemeasurable
    (continuous_ratChar _).aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun x => (ratChar_archPoint u x).symm)

/-- The spectral measure of an archimedean positive-definite function gives no mass off the
Kronecker line. -/
theorem spectralMeasure_compl_range_archPoint {f : posUnits → ℂ} (hf : IsPosDefOnGroup f)
    {F : ℝ → ℂ} (hF : Continuous F) (hfF : ∀ u : posUnits, f u = F (Real.log ((u : ℚˣ) : ℚ)))
    {μ : Measure PrimeTorus} [IsFiniteMeasure μ]
    (hμ : ∀ u : posUnits, f u = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ) :
    μ (range archPoint)ᶜ = 0 := by
  obtain ⟨ν, -, rfl⟩ := spectralMeasure_eq_map_archPoint hf hF hfF hμ
  rw [Measure.map_apply continuous_archPoint.measurable
    measurableEmbedding_archPoint.measurableSet_range.compl]
  simp

end GaloisForLFunctions.ArithmeticPositiveDuality
