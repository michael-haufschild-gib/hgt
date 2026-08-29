import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The reciprocal `q`-ladder mass spectrum

The reciprocal image of a geometric bound-state ladder is the mass sequence
`M n = m² + A q^(-2n)`.  It is increasing and escapes to infinity, its counting function is
logarithmic — so the associated atomic measure is a polynomially bounded Källén–Lehmann weight —
and with the de Sitter threshold `m² = (9/4)H²` the principal-series frequencies are exactly
geometric, which turns the heavy-particle production sum into a Mahler clock.
-/

namespace GaloisForLFunctions.HTGeometry

open Real

noncomputable section

/-- The reciprocal image of a geometric ladder: the mass sequence `m² + A q^(-2n)`. -/
def reciprocalMass (mstar A q : ℝ) (n : ℕ) : ℝ := mstar + A * (q ^ (2 * n))⁻¹

theorem reciprocalMass_pos {mstar A q : ℝ} (hm : 0 ≤ mstar) (hA : 0 < A) (hq : 0 < q) (n : ℕ) :
    0 < reciprocalMass mstar A q n := by
  have hpow : 0 < q ^ (2 * n) := pow_pos hq _
  have hpos : 0 < A * (q ^ (2 * n))⁻¹ := mul_pos hA (inv_pos.mpr hpow)
  unfold reciprocalMass
  linarith

/-- The masses increase strictly: reciprocal inversion sends an accumulating bound ladder to a
spectrum escaping to infinity. -/
theorem reciprocalMass_strictMono {mstar A q : ℝ} (hA : 0 < A) (hq : 0 < q) (hq1 : q < 1) :
    StrictMono (reciprocalMass mstar A q) := by
  intro m n hmn
  have hpow : q ^ (2 * n) < q ^ (2 * m) := by
    refine pow_lt_pow_right_of_lt_one₀ hq hq1 ?_
    omega
  have hm0 : 0 < q ^ (2 * m) := pow_pos hq _
  have hn0 : 0 < q ^ (2 * n) := pow_pos hq _
  have hinv : (q ^ (2 * m))⁻¹ < (q ^ (2 * n))⁻¹ := by
    exact inv_strictAnti₀ hn0 hpow
  unfold reciprocalMass
  have := mul_lt_mul_of_pos_left hinv hA
  linarith

/-- **The counting function is logarithmic.**  Every shell below a bound has index at most
`log((L - m²)/A) / log(q⁻²)`. -/
theorem index_le_log_of_reciprocalMass_le {mstar A q L : ℝ} (hA : 0 < A) (hq : 0 < q)
    {n : ℕ} (hn : reciprocalMass mstar A q n ≤ L) :
    (n : ℝ) * Real.log (q ^ 2)⁻¹ ≤ Real.log ((L - mstar) / A) := by
  have hpow : 0 < q ^ (2 * n) := pow_pos hq _
  have hstep : A * (q ^ (2 * n))⁻¹ ≤ L - mstar := by
    unfold reciprocalMass at hn
    linarith
  have hposA : 0 < A * (q ^ (2 * n))⁻¹ := mul_pos hA (inv_pos.mpr hpow)
  have hle : (q ^ (2 * n))⁻¹ ≤ (L - mstar) / A := by
    rw [le_div_iff₀ hA, mul_comm]
    exact hstep
  have hlog := Real.log_le_log (inv_pos.mpr hpow) hle
  have hexp : ((q ^ (2 * n))⁻¹ : ℝ) = ((q ^ 2)⁻¹) ^ n := by
    rw [← inv_pow, ← inv_pow, ← pow_mul, mul_comm 2 n]
  rw [hexp, Real.log_pow] at hlog
  exact hlog

/-- **The counting function is finite below every bound**: the reciprocal spectrum is locally
finite, so its atomic measure is an admissible Källén–Lehmann weight. -/
theorem finite_reciprocalMass_le {mstar A q L : ℝ} (hA : 0 < A) (hq : 0 < q) (hq1 : q < 1) :
    {n : ℕ | reciprocalMass mstar A q n ≤ L}.Finite := by
  have hlogpos : 0 < Real.log (q ^ 2)⁻¹ := by
    refine Real.log_pos ?_
    rw [one_lt_inv_iff₀]
    exact ⟨pow_pos hq 2, by nlinarith⟩
  refine Set.Finite.subset (Set.finite_Iic
    (⌊Real.log ((L - mstar) / A) / Real.log (q ^ 2)⁻¹⌋₊)) ?_
  intro n hn
  have hbound := index_le_log_of_reciprocalMass_le hA hq hn
  have hle : (n : ℝ) ≤ Real.log ((L - mstar) / A) / Real.log (q ^ 2)⁻¹ := by
    rw [le_div_iff₀ hlogpos]
    exact hbound
  exact Set.mem_Iic.mpr (Nat.le_floor hle)

/-- **The de Sitter principal-series frequencies of the reciprocal ladder are geometric.**  With
the threshold `m² = (9/4)H²`, the frequency of the `n`-th shell is `μ₀ q^(-n)`. -/
theorem principalFrequency_eq {H g κ q : ℝ} (hH : 0 < H) (hg : 0 < g) (hκ : 0 < κ) (hq : 0 < q)
    (n : ℕ) :
    Real.sqrt (reciprocalMass ((9 / 4) * H ^ 2) ((g / κ) ^ 2) q n / H ^ 2 - 9 / 4)
      = (g / (H * κ)) * (q ^ n)⁻¹ := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hqn : (0 : ℝ) < q ^ n := pow_pos hq n
  have hsq : reciprocalMass ((9 / 4) * H ^ 2) ((g / κ) ^ 2) q n / H ^ 2 - 9 / 4
      = ((g / (H * κ)) * (q ^ n)⁻¹) ^ 2 := by
    unfold reciprocalMass
    have hpow : (q ^ (2 * n))⁻¹ = ((q ^ n)⁻¹) ^ 2 := by
      rw [← inv_pow, ← inv_pow, ← pow_mul, mul_comm n 2]
    rw [hpow]
    field_simp
    ring
  rw [hsq, Real.sqrt_sq]
  positivity

/-- **The heavy-particle production sum of a geometric frequency tower is a Mahler clock.** -/
theorem clock_term_eq (μ₀ u : ℝ) (P n : ℕ) :
    Complex.exp ((μ₀ * (P : ℝ) ^ n : ℝ) * (-(Real.pi : ℂ) + Complex.I * u))
      = Complex.exp ((μ₀ : ℂ) * (-(Real.pi : ℂ) + Complex.I * u)) ^ (P ^ n) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
