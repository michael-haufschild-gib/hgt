import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsTheDirichletSeriesOfTheSpectrum

/-!
# The spectrum of a Ramanujan sum is the unit group

The two derivations of the second-order term of a Ramanujan window agree. Through the energy law
and the autocorrelation `C_{c_m} = c_m`, the window twisted by `c_m` has second-order coefficient
`J_{β+1}(m) βJ/K` (`ram_layer_criticalCurve_of_regularBulk`). Through the spectrum, every mean-zero
twist has coefficient `(βA_φ/(K∫φ²)) · 2M^{β+1} Σ_j |χ̂(j)|² j^{−(β+1)}`
(`periodicTwist_layer_criticalCurve_dirichlet`). For `c_m`:

* **The spectrum of `c_m` is the unit group** (`twistPower_ramTwist`): `S_j = m [(j, m) = 1]`, so
  `|χ̂(j)|²` is the indicator of the units mod `m` (Ramanujan sums are sums over primitive roots,
  and `Σ_{n<m} (ζ e(j/m))^n = m [ζ = e(−j/m)]`).
* **The counting identity** (`twistSpectralSum_ramTwist`):
  `2m^s Σ_{(j,m)=1} j^{−s} = 2 ζ(s) J_s(m)`, by Möbius inversion of the coprimality condition.
* **Agreement** (`ramTwist_spectral_limit_eq`): with `J = (2A_φ/∫φ²) ζ(β+1)` the spectral
  coefficient is `J_{β+1}(m) βJ/K`, the count of `ℙ^β(ℤ/m)` found by the energy law.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- **The Fourier coefficients of a Ramanujan sum**: `S_j(c_m) = m [(j, m) = 1]`. -/
theorem twistCoeff_ramTwist {m : ℕ} (hm : 0 < m) (j : ℕ) :
    twistCoeff (ramTwist m) m j = if Nat.Coprime j m then (m : ℂ) else 0 := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / m) with hω
  have hωp : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have he : ∀ n : ℕ, Complex.exp (2 * Real.pi * Complex.I * (j * n / m)) = (ω ^ j) ^ n := by
    intro n
    rw [← pow_mul, hω, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold twistCoeff
  have hcast : ∀ n : ℕ, ((ramTwist m n : ℝ) : ℂ) = ∑ ζ ∈ primitiveRoots m ℂ, ζ ^ n := fun n => by
    rw [← ramanujanSum_eq_ramTwist hm]; rfl
  simp_rw [hcast, he, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ ζ ∈ primitiveRoots m ℂ, ∑ n ∈ range m, ζ ^ n * (ω ^ j) ^ n =
      if ζ * ω ^ j = 1 then (m : ℂ) else 0 := by
    intro ζ hζ
    have hζp := (mem_primitiveRoots hm).mp hζ
    simp_rw [← mul_pow]
    refine sum_range_pow_root ?_
    rw [mul_pow, hζp.pow_eq_one, ← pow_mul, mul_comm j m, pow_mul, hωp.pow_eq_one, one_pow, one_mul]
  rw [sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hω0 : ω ^ j ≠ 0 := pow_ne_zero _ (hωp.ne_zero hm.ne')
  have hfe : (primitiveRoots m ℂ).filter (fun ζ => ζ * ω ^ j = 1) =
      (primitiveRoots m ℂ).filter (fun ζ => ζ = (ω ^ j)⁻¹) := by
    ext ζ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, eq_inv_of_mul_eq_one_left h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2, inv_mul_cancel₀ hω0]⟩
  have hmem : (ω ^ j)⁻¹ ∈ primitiveRoots m ℂ ↔ Nat.Coprime j m := by
    rw [mem_primitiveRoots hm, IsPrimitiveRoot.inv_iff, hωp.pow_iff_coprime hm]
  rw [hfe, Finset.filter_eq']
  by_cases hc : Nat.Coprime j m
  · rw [if_pos (hmem.mpr hc), if_pos hc, Finset.card_singleton, Nat.cast_one, one_mul]
  · rw [if_neg (fun h => hc (hmem.mp h)), if_neg hc, Finset.card_empty, Nat.cast_zero, zero_mul]

/-- **The spectrum of `c_m` is the unit group**: `|χ̂(j)|² = [(j, m) = 1]`. -/
theorem twistPower_ramTwist {m : ℕ} (hm : 0 < m) (j : ℕ) :
    twistPower (ramTwist m) m j = if Nat.Coprime j m then 1 else 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold twistPower
  rw [twistCoeff_ramTwist hm]
  split_ifs
  · rw [Complex.norm_natCast]; field_simp
  · simp

/-- Möbius inversion of coprimality: `[(j, m) = 1] = Σ_{d ∣ m, d ∣ j} μ(d)`. -/
theorem coprime_indicator_eq_sum {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (if Nat.Coprime j m then (1 : ℝ) else 0) =
      ∑ d ∈ m.divisors, if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  have hfil : m.divisors.filter (fun d => d ∣ j) = (Nat.gcd j m).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdm, hm0⟩, hdj⟩
      exact ⟨Nat.dvd_gcd hdj hdm, Nat.gcd_ne_zero_right hm0⟩
    · rintro ⟨hd, hg⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right j m), by omega⟩, hd.trans (Nat.gcd_dvd_left j m)⟩
  rw [hfil]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f (Nat.gcd j m))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' : ((∑ d ∈ (Nat.gcd j m).divisors, ArithmeticFunction.moebius d : ℤ) : ℝ) =
      if Nat.gcd j m = 1 then 1 else 0 := by
    rw [h]; split_ifs <;> simp
  push_cast at h'
  rw [h']

/-- `Σ_{d ∣ j} j^{−s}` over the multiples of `d`: `Σ_{j} [d ∣ j] j^{−s} = d^{−s} Σ_k k^{−s}`. -/
theorem tsum_dvd_rpow (s : ℝ) {d : ℕ} (hd : 0 < d) :
    ∑' j : ℕ, (if d ∣ j then (j : ℝ) ^ (-s) else 0) = (d : ℝ) ^ (-s) * ∑' k : ℕ, (k : ℝ) ^ (-s) := by
  have hinj : Function.Injective (fun k : ℕ => d * k) := fun a b h => by
    simp only at h; exact Nat.eq_of_mul_eq_mul_left hd h
  rw [← tsum_mul_left, ← hinj.tsum_eq]
  · refine tsum_congr fun k => ?_
    simp only [dvd_mul_right, if_true]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  · intro j hj
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hj
    obtain ⟨⟨k, hk⟩, -⟩ := hj
    exact ⟨k, hk.symm⟩

/-- **The counting identity**: the spectral sum of `c_m` is `2 ζ(s) J_s(m)`. -/
theorem twistSpectralSum_ramTwist {s : ℝ} (hs : 1 < s) {m : ℕ} (hm : 1 < m) :
    twistSpectralSum s (ramTwist m) m =
      2 * ArithmeticDegenerationTheory.zetaSum s * ArithmeticDegenerationTheory.jordanTotient s m := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [twistSpectralSum_eq_dirichlet hs (meanZeroTwist_ramTwist hm)]
  simp_rw [twistPower_ramTwist hm0, coprime_indicator_eq_sum hm0, Finset.sum_mul]
  have hg : Summable fun j : ℕ => (j : ℝ) ^ (-s) := Real.summable_nat_rpow.mpr (by linarith)
  have hsum : ∀ d ∈ m.divisors, Summable fun j : ℕ =>
      (if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0) * (j : ℝ) ^ (-s) := by
    intro d _
    refine (hg.mul_left |(ArithmeticFunction.moebius d : ℝ)|).of_norm_bounded fun j => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (by rw [abs_of_nonneg (by positivity)]) (abs_nonneg _) (abs_nonneg _)
    split_ifs <;> simp
  rw [Summable.tsum_finsetSum hsum]
  have hterm : ∀ d ∈ m.divisors, ∑' j : ℕ,
      (if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0) * (j : ℝ) ^ (-s) =
      (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-s) * ∑' k : ℕ, (k : ℝ) ^ (-s)) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← tsum_dvd_rpow s hd0, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    split_ifs <;> ring
  rw [sum_congr rfl hterm]
  -- `Σ_k k^{−s} = ζ(s)` and `m^s Σ_{d∣m} μ(d) d^{−s} = J_s(m)`
  have hz : ∑' k : ℕ, (k : ℝ) ^ (-s) = ArithmeticDegenerationTheory.zetaSum s := by
    rw [ArithmeticDegenerationTheory.zetaSum, hg.tsum_eq_zero_add]
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    rw [Real.zero_rpow (by linarith), zero_add]
  have hJ : (m : ℝ) ^ s * ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-s) =
      ArithmeticDegenerationTheory.jordanTotient s m := by
    rw [ArithmeticDegenerationTheory.jordanTotient, Finset.mul_sum,
      ← Nat.sum_div_divisors m (fun d => (ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ s)]
    refine sum_congr rfl fun d hd => ?_
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [Nat.div_div_self hdm hm0.ne', Nat.cast_div hdm hd0.ne', Real.div_rpow hmR.le hd0.le,
      Real.rpow_neg hd0.le]
    ring
  rw [← hz, ← hJ]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

/-- **The two derivations agree**: with `J = (2A_φ/∫φ²) ζ(β+1)`, the spectral coefficient of the
Ramanujan window is `J_{β+1}(m) βJ/K`. -/
theorem ramTwist_spectral_limit_eq {β Aφ K I : ℝ} (hβ : 0 < β) {m : ℕ} (hm : 1 < m) :
    β * Aφ / (K * I) * twistSpectralSum (β + 1) (ramTwist m) m =
      ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β *
        (2 / I * Aφ * ArithmeticDegenerationTheory.zetaSum (β + 1)) / K := by
  rw [twistSpectralSum_ramTwist (by linarith) hm]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
