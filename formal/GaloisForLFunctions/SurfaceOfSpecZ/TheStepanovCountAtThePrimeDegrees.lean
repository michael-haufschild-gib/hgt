import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovCountAtThePrimePowerDegrees

/-!
# The Stepanov count at the prime degrees

`TheStepanovCountAtThePrimePowerDegrees` decides RH from one side at the prime powers `pᵏ`. The
higher powers are not needed.

**Theorem** (`riemannHypothesis_iff_bddBelow_primeDegrees`). RH holds iff the traces of the smoothed
Frobenius graphs of prime degree are bounded below, `2 Re S(log p) ≥ −K` for every prime `p`: an upper
bound on the smoothed point counts of the planes `⟨Γ_1, Γ_p⟩` only. Two-sided Hasse–Weil on these
planes gave only `|Re ρ − ½| ≤ 1/12` by the gap method (`HasseWeilAtThePrimeDegreesBoundsTheWidth`).

**Proof.** The gap method from one side already puts the zeros in `Re ρ ≤ 5/8`
(`re_le_of_bddBelow_primeDegrees`). The prime series `Σ_p log p (2 Re S(log p) + K + 1) p^{−s}` is the
prime-power series of `TheStepanovCountAtThePrimePowerDegrees` minus the series over the higher prime
powers, which converges absolutely and is holomorphic for `Re s > 7/8`
(`differentiableOn_gdSeries_higherCoeff`): the higher prime powers are as sparse as the squares,
`Σ_{k≥2} Λ(pᵏ) p^{−kσ} < ∞` for `σ > ½` (`summable_higherWeight`). The Landau argument of the
prime-power case survives a holomorphic correction (`forall_re_le_half_of_gdSeries_eq`).
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open GaloisForLFunctions.HTGeometry ArithmeticFunction

/-! ### The primes and the higher prime powers -/

/-- `Λ(j + 1)` at the primes `j + 1`, `0` elsewhere. -/
def primeWeight (j : ℕ) : ℝ := if (j + 1).Prime then Λ (j + 1) else 0

/-- `Λ(j + 1)` at the prime powers `j + 1 = pᵏ`, `k ≥ 2`, `0` elsewhere. -/
def higherWeight (j : ℕ) : ℝ := if (j + 1).Prime then 0 else Λ (j + 1)

theorem primeWeight_add_higherWeight (j : ℕ) : primeWeight j + higherWeight j = Λ (j + 1) := by
  unfold primeWeight higherWeight; split_ifs <;> ring

theorem primeWeight_nonneg (j : ℕ) : 0 ≤ primeWeight j := by
  unfold primeWeight; split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

theorem higherWeight_nonneg (j : ℕ) : 0 ≤ higherWeight j := by
  unfold higherWeight; split_ifs
  · exact le_rfl
  · exact vonMangoldt_nonneg

theorem primeWeight_le (j : ℕ) : primeWeight j ≤ Λ (j + 1) := by
  rw [← primeWeight_add_higherWeight]; linarith [higherWeight_nonneg j]

theorem higherWeight_le (j : ℕ) : higherWeight j ≤ Λ (j + 1) := by
  rw [← primeWeight_add_higherWeight]; linarith [primeWeight_nonneg j]

/-- **The higher prime powers are sparse.** `Σ_{k ≥ 2} Λ(pᵏ) p^{−kσ} < ∞` for `σ > ½`: indexed by
`(p, k) ↦ p^{k+2}`, the terms are at most `log p · p^{−2σ} (2^{−σ})^k`. -/
theorem summable_higherWeight {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun j : ℕ => higherWeight j * ((j : ℝ) + 1) ^ (-σ) := by
  set i : Nat.Primes × ℕ → ℕ := fun x => (x.1 : ℕ) ^ (x.2 + 2) - 1 with hi
  have hpos : ∀ x : Nat.Primes × ℕ, 1 ≤ (x.1 : ℕ) ^ (x.2 + 2) := fun x =>
    Nat.one_le_pow _ _ x.1.2.pos
  have hinj : Function.Injective i := by
    intro x y hxy
    have h1 : (x.1 : ℕ) ^ (x.2 + 2) = (y.1 : ℕ) ^ (y.2 + 2) := by
      have := hpos x; have := hpos y; simp only [hi] at hxy; omega
    obtain ⟨hp, hk⟩ := Nat.Prime.pow_inj (m := x.2 + 1) (n := y.2 + 1) x.1.2 y.1.2 h1
    exact Prod.ext (Subtype.ext hp) (by omega)
  have hzero : ∀ j ∉ Set.range i, higherWeight j * ((j : ℝ) + 1) ^ (-σ) = 0 := by
    intro j hj
    unfold higherWeight
    split_ifs with hpr
    · simp
    · by_cases hpp : IsPrimePow (j + 1)
      · exfalso; apply hj
        obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).mp hpp
        have hk2 : 2 ≤ k := by
          by_contra h
          have hk1 : k = 1 := by omega
          rw [hk1, pow_one] at hpk
          exact hpr (hpk ▸ hp)
        refine ⟨(⟨p, hp⟩, k - 2), ?_⟩
        simp only [hi]
        rw [show k - 2 + 2 = k by omega, hpk]
        omega
      · rw [vonMangoldt_eq_zero_iff.mpr hpp, zero_mul]
  rw [← hinj.summable_iff hzero]
  set ε := σ - 1 / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hf : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (ε + -2 * σ) / ε :=
    (Nat.Primes.summable_rpow.mpr (by rw [hε]; linarith)).div_const ε
  have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-σ) := by positivity
  have hq1 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hprod := hf.mul_of_nonneg hg (fun p => by positivity) (fun k => by positivity)
  refine Summable.of_nonneg_of_le (fun x => mul_nonneg (higherWeight_nonneg _) (by positivity))
    (fun x => ?_) hprod
  obtain ⟨p, k⟩ := x
  dsimp only
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hpow : (p : ℕ) ^ (k + 2) - 1 + 1 = (p : ℕ) ^ (k + 2) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ p.2.pos)
  simp only [Function.comp_def, hi]
  have hnp : ¬ ((p : ℕ) ^ (k + 2) - 1 + 1).Prime := by
    rw [hpow]; exact Nat.Prime.not_prime_pow (by omega)
  have hval : higherWeight ((p : ℕ) ^ (k + 2) - 1) = Real.log ((p : ℕ) : ℝ) := by
    unfold higherWeight
    rw [if_neg hnp, hpow, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime p.2]
  have hcast : (((p : ℕ) ^ (k + 2) - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) ^ (k + 2) := by
    rw [← Nat.cast_add_one, hpow, Nat.cast_pow]
  rw [hval, hcast]
  have hsplit : (((p : ℕ) : ℝ) ^ (k + 2)) ^ (-σ) =
      ((p : ℕ) : ℝ) ^ (-2 * σ) * (((p : ℕ) : ℝ) ^ (-σ)) ^ k := by
    rw [← Real.rpow_mul_natCast hp0.le, ← Real.rpow_add hp0, ← Real.rpow_natCast,
      ← Real.rpow_mul hp0.le]
    congr 1; push_cast; ring
  have hlog : Real.log ((p : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) ^ ε / ε := Real.log_le_rpow_div hp0.le hε0
  have hpk : (((p : ℕ) : ℝ) ^ (-σ)) ^ k ≤ ((2 : ℝ) ^ (-σ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)) k
  rw [hsplit]
  calc Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-2 * σ) * (((p : ℕ) : ℝ) ^ (-σ)) ^ k)
      ≤ ((p : ℕ) : ℝ) ^ ε / ε * (((p : ℕ) : ℝ) ^ (-2 * σ) * ((2 : ℝ) ^ (-σ)) ^ k) :=
        mul_le_mul hlog (mul_le_mul_of_nonneg_left hpk (by positivity)) (by positivity)
          (by positivity)
    _ = ((p : ℕ) : ℝ) ^ (ε + -2 * σ) / ε * ((2 : ℝ) ^ (-σ)) ^ k := by
        rw [Real.rpow_add hp0]; ring

/-- **`Σ_p log p / p` diverges.** -/
theorem not_summable_primeWeight_div :
    ¬ Summable fun j : ℕ => primeWeight j * ((j : ℝ) + 1) ^ (-1 : ℝ) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    have hp := p.2.one_lt
    have hq := q.2.one_lt
    exact Subtype.ext (by simp only at hpq; omega)
  have h2 := h.comp_injective hinj
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (h2.div_const (Real.log 2))
  have hp1 : 1 ≤ (p : ℕ) := p.2.one_lt.le
  have hpp : (p : ℕ) - 1 + 1 = p := Nat.sub_add_cancel hp1
  have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = ((p : ℕ) : ℝ) := by
    rw [← Nat.cast_add_one, hpp]
  simp only [Function.comp_def, primeWeight]
  rw [hpp, if_pos p.2, hcast, vonMangoldt_apply_prime p.2, Real.rpow_neg_one]
  have hlogp : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  rw [le_div_iff₀ hlog2, one_div]
  calc ((p : ℕ) : ℝ)⁻¹ * Real.log 2 ≤ ((p : ℕ) : ℝ)⁻¹ * Real.log ((p : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlogp (by positivity)
    _ = Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ)⁻¹ := by ring

/-! ### The prime series and its correction -/

/-- The coefficients `Λ(p)(2 Re S(log p) + K + 1)` at the primes `p = j + 1`, `0` elsewhere. -/
def primeCoeff (K : ℝ) (j : ℕ) : ℝ :=
  primeWeight j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re + K + 1)

/-- The same coefficients at the higher prime powers. -/
def higherCoeff (K : ℝ) (j : ℕ) : ℝ :=
  higherWeight j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re + K + 1)

theorem primeCoeff_add_higherCoeff (K : ℝ) (j : ℕ) :
    primeCoeff K j + higherCoeff K j = primePowerCoeff K j := by
  unfold primeCoeff higherCoeff primePowerCoeff
  rw [← primeWeight_add_higherWeight]; ring

/-- `|2 Re S(log n) + K + 1| ≤ (E + |K| + 1) n^{1/8}` once every exponent has `|Re z| ≤ 1/8`. -/
theorem abs_trace_add_le (hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ 1 / 8) (K : ℝ) (j : ℕ) :
    |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re + K + 1| ≤
      ((∑' z : ℂ, ‖traceCoeff 3 z‖) + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have habs := abs_two_re_lagStructure_le_of_width hw (Real.log_nonneg hj1)
  have hexp : Real.exp (1 / 8 * Real.log ((j : ℝ) + 1)) = ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := by
    rw [Real.rpow_def_of_pos hj0]; ring_nf
  rw [hexp] at habs
  have hp8 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hj1 (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hp8 (by linarith [abs_nonneg K] : (0 : ℝ) ≤ |K| + 1)
  calc |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re + K + 1|
      ≤ |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re| + |K| + 1 := by
        have := abs_add_le (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
          (Real.log ((j : ℝ) + 1))).re + K) 1
        have := abs_add_le (2 * (lagStructure zetaZeroConfig (boxSpline 1 3)
          (Real.log ((j : ℝ) + 1))).re) K
        rw [abs_one] at *
        linarith
    _ ≤ _ := by nlinarith

/-- A Dirichlet series with `|a_j| ≤ C Λ(j + 1)(j + 1)^{1/8}` converges absolutely for
`Re s > 9/8`. -/
theorem summable_gdTerm_of_abs_le {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ j, |a j| ≤ C * (Λ (j + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8))) {s : ℂ}
    (hs : 9 / 8 < s.re) :
    Summable fun j : ℕ => ((a j : ℝ) : ℂ) * cexp (-(s * (powerFreq j : ℂ))) := by
  have hσ : 1 < s.re - 1 / 8 := by linarith
  have hΛ : Summable fun j : ℕ => Λ (j + 1) * ((j : ℝ) + 1) ^ (-(s.re - 1 / 8)) := by
    have h := (summable_tsum_vonMangoldt (w := ((s.re - 1 / 8 : ℝ) : ℂ)) (by simpa using hσ)).1.norm
    refine h.congr fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
      norm_natCast_add_one_cpow]
    simp
  refine Summable.of_norm_bounded (hΛ.mul_left C) fun j => ?_
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cexp_neg_mul_powerFreq,
    norm_natCast_add_one_cpow]
  have hre : (-s).re = -s.re := by simp
  rw [hre]
  have hp : 0 ≤ ((j : ℝ) + 1) ^ (-s.re) := by positivity
  calc |a j| * ((j : ℝ) + 1) ^ (-s.re)
      ≤ C * (Λ (j + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) * ((j : ℝ) + 1) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (ha j) hp
    _ = C * (Λ (j + 1) * (((j : ℝ) + 1) ^ ((1 : ℝ) / 8) * ((j : ℝ) + 1) ^ (-s.re))) := by ring
    _ = C * (Λ (j + 1) * ((j : ℝ) + 1) ^ (-(s.re - 1 / 8))) := by
        rw [← Real.rpow_add hj0]; congr 3; ring

/-- **The correction is holomorphic.** The series over the higher prime powers is holomorphic on
`Re s > 7/8` once every zero has `Re ρ ≤ 5/8`. -/
theorem differentiableOn_gdSeries_higherCoeff (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8)
    (K : ℝ) : DifferentiableOn ℂ (gdSeries (higherCoeff K) powerFreq) {s | 7 / 8 < s.re} := by
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ 1 / 8 := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le (fun ρ hρ => by linarith [hzf ρ hρ]) hz
  set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
  have hsum := (summable_higherWeight (σ := 3 / 4) (by norm_num)).mul_left (E + |K| + 1)
  unfold gdSeries
  refine differentiableOn_tsum_of_summable_norm hsum (fun j => ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun j s hs => ?_)
  · exact ((differentiable_id.mul_const _).neg.cexp.const_mul _).differentiableOn
  · have hs' : 7 / 8 < s.re := hs
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, cexp_neg_mul_powerFreq,
      norm_natCast_add_one_cpow]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    have h1 : |higherCoeff K j| ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) := by
      unfold higherCoeff
      rw [abs_mul, abs_of_nonneg (higherWeight_nonneg j)]
      exact mul_le_mul_of_nonneg_left (abs_trace_add_le hw K j) (higherWeight_nonneg j)
    have h2 : ((j : ℝ) + 1) ^ (-s.re) ≤ ((j : ℝ) + 1) ^ (-(7 / 8) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
    have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
    have hc0 : 0 ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) :=
      mul_nonneg (higherWeight_nonneg j) (mul_nonneg (by linarith [abs_nonneg K]) (by positivity))
    calc |higherCoeff K j| * ((j : ℝ) + 1) ^ (-s.re)
        ≤ higherWeight j * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) *
            ((j : ℝ) + 1) ^ (-(7 / 8) : ℝ) :=
          mul_le_mul h1 h2 (by positivity) hc0
      _ = (E + |K| + 1) * (higherWeight j *
            (((j : ℝ) + 1) ^ ((1 : ℝ) / 8) * ((j : ℝ) + 1) ^ (-(7 / 8) : ℝ))) := by ring
      _ = (E + |K| + 1) * (higherWeight j * ((j : ℝ) + 1) ^ (-(3 / 4) : ℝ)) := by
          rw [← Real.rpow_add hj0]; norm_num

/-! ### Landau with a holomorphic correction -/

/-- **The Landau argument with a holomorphic correction.** Let `b ≥ 0`, `Σ b_j/(j + 1) = ∞`,
convergent for `σ > 9/8`, have Dirichlet series `primePowerZeta K − N` right of `9/8`, with `N`
holomorphic on `Re s > 7/8`. If every zero has `Re ρ ≤ 5/8`, none lies right of the line. -/
theorem forall_re_le_half_of_gdSeries_eq (hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8)
    {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j)
    (hdiv1 : ¬ Summable fun j : ℕ => b j * ((j : ℝ) + 1) ^ (-1 : ℝ))
    (hconv : ∀ σ : ℝ, 9 / 8 < σ → Summable fun j : ℕ => b j * ((j : ℝ) + 1) ^ (-σ))
    {N : ℂ → ℂ} (hN : DifferentiableOn ℂ N {s | 7 / 8 < s.re}) (K : ℝ)
    (heq : ∀ s : ℂ, 9 / 8 < s.re → gdSeries b powerFreq s = primePowerZeta K s - N s) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 := by
  classical
  intro ρ₁ hρ₁
  by_contra hρ₁re
  push Not at hρ₁re
  have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ 1 / 8 := fun z hz =>
    abs_re_le_of_traceCoeff_ne_zero_of_re_le (fun ρ hρ => by linarith [hzf ρ hρ]) hz
  have hlam : ∀ j, 0 ≤ powerFreq j := powerFreq_nonneg
  have htw : ∀ σ j, gdTwistTerm b powerFreq σ 0 j = b j * ((j : ℝ) + 1) ^ (-σ) := by
    intro σ j; rw [gdTwistTerm, pow_zero, mul_one, real_exp_neg_mul_powerFreq]
  have hsumHigh : ∀ σ : ℝ, 9 / 8 < σ → Summable (gdTwistTerm b powerFreq σ 0) := fun σ hσ =>
    (hconv σ hσ).congr fun j => (htw σ j).symm
  have hdivLow : ∀ σ : ℝ, σ ≤ 1 → ¬ Summable (gdTwistTerm b powerFreq σ 0) := by
    intro σ hσ hs
    apply hdiv1
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hb j) (by positivity)) (fun j => ?_) hs
    rw [htw]
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)) (hb j)
  -- the abscissa
  set S : Set ℝ := {σ | Summable (gdTwistTerm b powerFreq σ 0)} with hSdef
  have hS2 : (5 / 4 : ℝ) ∈ S := hsumHigh _ (by norm_num)
  have hSne : S.Nonempty := ⟨_, hS2⟩
  have hSbdd : BddBelow S := ⟨1, fun σ hσ => by
    by_contra h; exact hdivLow σ (le_of_lt (not_le.mp h)) hσ⟩
  set σc := sInf S with hσcdef
  have hsum : ∀ σ, σc < σ → Summable (gdTwistTerm b powerFreq σ 0) := by
    intro σ hσ
    obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hSne hσ
    exact summable_gdTwistTerm_of_le hb hlam hσ'S hlt.le
  have hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm b powerFreq σ 0) := fun σ hσ hs =>
    absurd (csInf_le hSbdd hs) (not_le.mpr hσ)
  have hσc2 : σc ≤ 5 / 4 := csInf_le hSbdd hS2
  -- analyticity
  have hgdAn : ∀ s : ℂ, σc < s.re → AnalyticAt ℂ (gdSeries b powerFreq) s := by
    intro s hs
    have hopen : IsOpen {w : ℂ | σc < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticAt (s := {w : ℂ | σc < w.re}) (fun w hw => ?_)
      (hopen.mem_nhds hs)
    have hw' : σc < w.re := hw
    exact (RHTower.differentiableAt_gdSeries hb hlam (hsum ((σc + w.re) / 2) (by linarith))
      (by linarith)).differentiableWithinAt
  have hNAn : ∀ s : ℂ, 7 / 8 < s.re → AnalyticAt ℂ N s := fun s hs =>
    hN.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  set G : ℂ → ℂ := fun s => primePowerZeta K s - N s with hGdef
  have hGball : ∀ s₀ : ℂ, 1 < s₀.re → s₀.re < 15 / 8 →
      (∀ z, traceCoeff 3 z ≠ 0 → s₀ ≠ 1 + z) →
        ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ G (ball s₀ ρ) := by
    intro s₀ h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := exists_ball_differentiableOn_primePowerZeta hzf K h1 h2 hp
    refine ⟨min ρ (s₀.re - 1), lt_min hρ (by linarith), ?_⟩
    refine (hd.mono (ball_subset_ball (min_le_left _ _))).sub (hN.mono fun s hs => ?_)
    rw [mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| < s₀.re - 1 :=
      lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (s - s₀))
        (hs.trans_le (min_le_right _ _))
    show 7 / 8 < s.re
    linarith [(abs_lt.mp hre).1]
  have hGAn : ∀ s : ℂ, 1 < s.re → s.re < 15 / 8 →
      (∀ z, traceCoeff 3 z ≠ 0 → s ≠ 1 + z) → AnalyticAt ℂ G s := by
    intro s h1 h2 hp
    obtain ⟨ρ, hρ, hd⟩ := hGball s h1 h2 hp
    exact hd.analyticAt (ball_mem_nhds s hρ)
  have hrealNoPole : ∀ t : ℝ, ∀ z, traceCoeff 3 z ≠ 0 → (t : ℂ) ≠ 1 + z := by
    intro t z hz h
    have him := congrArg Complex.im h
    simp only [Complex.ofReal_im, Complex.add_im, Complex.one_im, zero_add] at him
    exact traceCoeff_im_ne_zero hz him.symm
  have hagreeHigh : ∀ s : ℂ, 9 / 8 < s.re → gdSeries b powerFreq s = G s := heq
  -- Landau: the abscissa is at most `1`
  have hσc : σc ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h2 : σc < 15 / 8 := by linarith
    obtain ⟨ρ, hρ, hG⟩ := hGball (σc : ℂ) (by simpa using hgt) (by simpa using h2)
      (fun z hz => hrealNoPole σc z hz)
    have hreal : ∀ t ∈ Ioo σc (15 / 8),
        gdSeries b powerFreq ((0 : ℂ) + t) = G ((0 : ℂ) + t) := by
      refine eqOn_ray_of_eventually (a := σc) (c := 3 / 2) (b := 15 / 8)
        (by linarith) (by norm_num) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
      · rw [zero_add]; exact hgdAn _ (by simpa using ht.1)
      · rw [zero_add]
        exact hGAn _ (by simpa using hgt.trans ht.1) (by simpa using ht.2)
          (fun z hz => hrealNoPole t z hz)
      · rw [zero_add]; exact hagreeHigh _ (by simp; linarith [ht.1])
    have hhalf := eqOn_halfBall (f := G) (g := gdSeries b powerFreq) hρ
      (fun s hs _ => hG.analyticAt (isOpen_ball.mem_nhds hs))
      (fun s _ hs => hgdAn s hs)
      (fun t ht1 _ => by
        rcases lt_or_ge t (15 / 8) with htb | htb
        · have := hreal t ⟨ht1, htb⟩; rw [zero_add] at this; exact this.symm
        · exact (hagreeHigh _ (by simp; linarith)).symm)
    exact RHTower.gdSeries_no_continuation_at_abscissa hb hlam hsum hdiv hρ hG
      (fun s hs hre => hhalf s hs hre)
  -- the off-line zero, rightmost on its line
  set z₁ := ρ₁ - 1 / 2 with hz₁def
  have hz₁ : traceCoeff 3 z₁ ≠ 0 := traceCoeff_sees (le_refl 3) hρ₁ hρ₁re
  set Lset := (finite_evenCoeff_line zetaZeroConfig (boxSpline 1 3) z₁.im).toFinset with hLset
  obtain ⟨z₀, hz₀L, hmax⟩ := Lset.exists_max_image Complex.re
    ⟨z₁, (Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩⟩
  obtain ⟨hz₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hz₀L
  have hre₀ : z₁.re ≤ z₀.re := hmax z₁ ((Set.Finite.mem_toFinset _).mpr ⟨hz₁, rfl⟩)
  have hz₁re : 0 < z₁.re := by simp [hz₁def]; linarith
  have hz₀re : z₀.re ≤ 1 / 8 := (abs_le.mp (hw z₀ hz₀)).2
  set s₀ : ℂ := 1 + z₀ with hs₀def
  have hs₀re : s₀.re = 1 + z₀.re := by simp [hs₀def]
  have hs₀1 : 1 < s₀.re := by rw [hs₀re]; linarith
  have hs₀2 : s₀.re ≤ 9 / 8 := by rw [hs₀re]; linarith
  set T : ℝ := 15 / 8 - s₀.re with hTdef
  have hT : 3 / 4 ≤ T := by rw [hTdef]; linarith
  have hqre : ∀ t : ℝ, (s₀ + t).re = s₀.re + t := fun t => by simp
  have hray : ∀ t : ℝ, 0 < t → ∀ z, traceCoeff 3 z ≠ 0 → s₀ + t ≠ 1 + z := by
    intro t ht z hz h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [hs₀def] at him hre
    have hle := hmax z ((Set.Finite.mem_toFinset _).mpr ⟨hz, him.symm.trans him₀⟩)
    linarith
  have hGray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ G (s₀ + t) := fun t ht =>
    hGAn _ (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2]) (hray t ht.1)
  have hgdray : ∀ t ∈ Ioo 0 T, AnalyticAt ℂ (gdSeries b powerFreq) (s₀ + t) := fun t ht =>
    hgdAn _ (by rw [hqre]; linarith [ht.1])
  have hagreeRay : ∀ t ∈ Ioo 0 T, gdSeries b powerFreq (s₀ + t) = G (s₀ + t) :=
    eqOn_ray_of_eventually (c := 9 / 8 - s₀.re + 1 / 2) (by linarith) (by linarith)
      hgdray hGray (fun t ht => hagreeHigh _ (by rw [hqre]; linarith [ht.1]))
  -- split off the pole
  set c' : ℂ → ℂ := fun z => if z = z₀ then 0 else traceCoeff 3 z with hc'def
  have hc' : ∀ z, ‖c' z‖ ≤ ‖traceCoeff 3 z‖ := fun z => by
    simp only [hc'def]; split_ifs <;> simp
  set R : ℂ → ℂ := fun s => -traceLogDerivOf c' s - ((K + 1 : ℝ) : ℂ) * logDeriv riemannZeta s -
    N s with hRdef
  have hsplit : ∀ t ∈ Ioo 0 T,
      G (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) + R (s₀ + t) := by
    intro t ht
    have hsm := summable_traceLogDerivOf_terms hzf (c := traceCoeff 3) (fun _ => le_rfl)
      (s := s₀ + t) (by rw [hqre]; linarith [ht.1]) (by rw [hqre]; linarith [ht.2])
    simp only [hGdef, hRdef]
    unfold primePowerZeta traceLogDerivOf
    rw [hsm.tsum_eq_add_tsum_ite z₀]
    have h1 : (s₀ + t) - z₀ = 1 + t := by rw [hs₀def]; ring
    have h2 : ∑' z, (if z = z₀ then 0 else traceCoeff 3 z * logDeriv riemannZeta (s₀ + t - z)) =
        ∑' z, c' z * logDeriv riemannZeta (s₀ + t - z) :=
      tsum_congr fun z => by simp only [hc'def]; split_ifs <;> simp
    rw [h1, h2]
    ring
  have hs₀ne : s₀ ≠ 1 := fun h => by rw [h] at hs₀1; simp at hs₀1
  have hRcont : ContinuousAt R s₀ := by
    have hp : ∀ z, c' z ≠ 0 → s₀ ≠ 1 + z := by
      intro z hz h
      have hzz : z ≠ z₀ := fun e => hz (by simp [hc'def, e])
      exact hzz (by rw [hs₀def] at h; linear_combination -h)
    have h1 := differentiableAt_traceLogDerivOf hzf hc' hs₀1 (by linarith) hp
    have h2 := differentiableAt_logDeriv_riemannZeta hs₀ne
      (riemannZeta_ne_zero_of_one_le_re hs₀1.le)
    exact ((h1.neg.sub (h2.const_mul _)).continuousAt).sub
      (hNAn s₀ (by linarith)).continuousAt
  have hgdcont : ContinuousAt (gdSeries b powerFreq) s₀ := (hgdAn s₀ (by linarith)).continuousAt
  set H : ℂ → ℂ := fun s => gdSeries b powerFreq s - R s with hHdef
  have hHcont : ContinuousAt H s₀ := hgdcont.sub hRcont
  have hHray : ∀ t ∈ Ioo 0 T, H (s₀ + t) = -(traceCoeff 3 z₀ * logDeriv riemannZeta (1 + t)) := by
    intro t ht
    simp only [hHdef]
    rw [hagreeRay t ht, hsplit t ht]
    ring
  -- the pole of `ζ'/ζ` at `1` against continuity
  obtain ⟨δ₁, hδ₁, hδ₁H⟩ := Metric.continuousAt_iff.mp hHcont 1 one_pos
  set A := ‖traceCoeff 3 z₀‖ with hAdef
  have hA : 0 < A := norm_pos_iff.mpr hz₀
  obtain ⟨t, ht0, htδ, htB⟩ := exists_norm_logDeriv_zeta_one_add_gt ((‖H s₀‖ + 1) / A)
    (lt_min hδ₁ (by linarith : (0 : ℝ) < T))
  have htδ₁ : t < δ₁ := htδ.trans_le (min_le_left _ _)
  have htT : t < T := htδ.trans_le (min_le_right _ _)
  have h1 := hHray t ⟨ht0, htT⟩
  have h2 : dist (H (s₀ + t)) (H s₀) < 1 := hδ₁H (by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact htδ₁)
  have h4 : ‖H s₀‖ + 1 < ‖H (s₀ + t)‖ := by
    rw [h1, norm_neg, norm_mul]
    rw [div_lt_iff₀ hA] at htB
    linarith
  have h5 : ‖H (s₀ + t)‖ < ‖H s₀‖ + 1 := by
    have := norm_sub_norm_le (H (s₀ + t)) (H s₀)
    rw [dist_eq_norm] at h2
    linarith
  linarith

/-! ### The theorem -/

/-- **The Stepanov count at the prime degrees.** RH holds iff the traces `2 Re S(log p)` of the
smoothed Frobenius graphs of prime degree are bounded below. -/
theorem riemannHypothesis_iff_bddBelow_primeDegrees :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_bddBelow_primePowerDegrees.mp hRH
    exact ⟨K, fun p hp => hK p hp.isPrimePow⟩
  · rintro ⟨K, hK⟩
    have hzf : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 5 / 8 :=
      re_le_of_bddBelow_primeDegrees (K := K / 2) fun p hp => by
        have := hK p hp
        rw [orbitCorr_eq_re_lagStructure_spline]; linarith
    have hw : ∀ z, traceCoeff 3 z ≠ 0 → |z.re| ≤ 1 / 8 := fun z hz =>
      abs_re_le_of_traceCoeff_ne_zero_of_re_le (fun ρ hρ => by linarith [hzf ρ hρ]) hz
    set E := ∑' z : ℂ, ‖traceCoeff 3 z‖ with hE
    have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
    -- at a prime the inner factor is at least `1`
    have hinner : ∀ j : ℕ, (j + 1).Prime → 1 ≤
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re + K + 1 := by
      intro j hj
      have := hK (j + 1) hj
      push_cast at this
      linarith
    have hge : ∀ j, primeWeight j ≤ primeCoeff K j := by
      intro j
      unfold primeCoeff
      by_cases hj : (j + 1).Prime
      · have h0 : 0 ≤ primeWeight j := primeWeight_nonneg j
        have := mul_le_mul_of_nonneg_left (hinner j hj) h0
        linarith
      · simp [primeWeight, hj]
    have hb : ∀ j, 0 ≤ primeCoeff K j := fun j => (primeWeight_nonneg j).trans (hge j)
    -- `|a_j| ≤ (E + |K| + 1) Λ(j + 1)(j + 1)^{1/8}` for the three coefficient sequences
    have hbound : ∀ (w : ℕ → ℝ), (∀ j, 0 ≤ w j) → (∀ j, w j ≤ Λ (j + 1)) → ∀ j,
        |w j * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log (j + 1))).re + K + 1)|
          ≤ (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) := by
      intro w hw0 hwΛ j
      rw [abs_mul, abs_of_nonneg (hw0 j)]
      have h1 := abs_trace_add_le hw K j
      have hP : 0 ≤ ((j : ℝ) + 1) ^ ((1 : ℝ) / 8) := by positivity
      have hC : 0 ≤ E + |K| + 1 := by linarith [abs_nonneg K]
      calc w j * |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re +
            K + 1| ≤ Λ (j + 1) * ((E + |K| + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) :=
            mul_le_mul (hwΛ j) h1 (abs_nonneg _) vonMangoldt_nonneg
        _ = _ := by ring
    have hΛle : ∀ j, Λ (j + 1) ≤ Λ (j + 1) := fun _ => le_rfl
    have hbP : ∀ j, |primeCoeff K j| ≤ (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) :=
      hbound primeWeight primeWeight_nonneg primeWeight_le
    have hbH : ∀ j, |higherCoeff K j| ≤
        (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) :=
      hbound higherWeight higherWeight_nonneg higherWeight_le
    have hbA : ∀ j, |primePowerCoeff K j| ≤
        (E + |K| + 1) * (Λ (j + 1) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 8)) :=
      hbound (fun j => Λ (j + 1)) (fun _ => vonMangoldt_nonneg) hΛle
    apply riemannHypothesis_of_forall_re_le
    refine forall_re_le_half_of_gdSeries_eq hzf hb ?_ ?_ (differentiableOn_gdSeries_higherCoeff hzf K)
      K ?_
    · -- divergence at `σ = 1`
      intro hs
      apply not_summable_primeWeight_div
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (primeWeight_nonneg j) (by positivity))
        (fun j => mul_le_mul_of_nonneg_right (hge j) (by positivity)) hs
    · -- convergence right of `9/8`
      intro σ hσ
      have h := summable_gdTerm_of_abs_le hbP (s := (σ : ℂ)) (by simpa using hσ)
      refine h.norm.congr fun j => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb j),
        cexp_neg_mul_powerFreq, norm_natCast_add_one_cpow]
      simp
    · -- the prime series is the prime-power series minus the correction
      intro s hs
      have hA := summable_gdTerm_of_abs_le hbA hs
      have hH := summable_gdTerm_of_abs_le hbH hs
      rw [← gdSeries_primePowerCoeff_eq hzf K hs]
      unfold gdSeries
      rw [← hA.tsum_sub hH]
      refine tsum_congr fun j => ?_
      rw [← primeCoeff_add_higherCoeff K j]
      push_cast
      ring

/-- The same statement for the orbit correlation `c_B = Re S` of the cubic spline. -/
theorem riemannHypothesis_iff_bddBelow_primeDegrees' :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      -K ≤ zetaScalingDatum.orbitCorr splineCycle (Real.log p) := by
  rw [riemannHypothesis_iff_bddBelow_primeDegrees]
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K / 2, fun p hp => by rw [orbitCorr_eq_re_lagStructure_spline]; linarith [hK p hp]⟩
  · rintro ⟨K, hK⟩
    exact ⟨2 * K, fun p hp => by
      have := hK p hp; rw [orbitCorr_eq_re_lagStructure_spline] at this; linarith⟩

end GaloisForLFunctions.SurfaceOfSpecZ
