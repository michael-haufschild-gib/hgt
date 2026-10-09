import GaloisForLFunctions.RHTower.WeilLogShiftExcessControl
import GaloisForLFunctions.RHTower.WeilNullPotentialSignPartRigidity

/-!
# Deficit translation bounds from logarithmic shift tests

Asymptotic positivity of the countable logarithmic panels and summable excess
bound deficit mass in every unit logarithmic block. Consequently the deficit
potential is bounded at every real shift, and the deficit is Cauchy-bounded.
These conclusions require neither full Weil positivity nor summable deficit.
-/

namespace RHTower

open Set MeasureTheory
open WeilExcess

/-- The explicit probe `floor(exp j)+1` has its logarithm in the j-th unit interval. -/
theorem integer_log_probe_bounds (j : ℕ) :
    2 ≤ ⌊Real.exp (j : ℝ)⌋₊ + 1 ∧
    (j : ℝ) ≤ Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ) ∧
    Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ) ≤ (j : ℝ) + 1 := by
  let m : ℕ := ⌊Real.exp (j : ℝ)⌋₊ + 1
  have he1 : 1 ≤ Real.exp (j : ℝ) := Real.one_le_exp (Nat.cast_nonneg _)
  have hf1 : 1 ≤ ⌊Real.exp (j : ℝ)⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast he1
  have hm2 : 2 ≤ m := by omega
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hml : Real.exp (j : ℝ) ≤ (m : ℝ) := by
    exact le_of_lt (by simpa only [m, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.exp (j : ℝ))))
  have hmu : (m : ℝ) ≤ Real.exp (j : ℝ) + 1 := by
    have hf := Nat.floor_le (Real.exp_pos (j : ℝ)).le
    dsimp [m]
    push_cast
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hmexp : (m : ℝ) ≤ Real.exp ((j : ℝ) + 1) := by
    rw [Real.exp_add]
    calc
      (m : ℝ) ≤ Real.exp (j : ℝ) + 1 := hmu
      _ ≤ Real.exp (j : ℝ) * 2 := by linarith
      _ ≤ Real.exp (j : ℝ) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left he2 (Real.exp_pos _).le
  have hlogl : (j : ℝ) ≤ Real.log m := by
    apply Real.exp_le_exp.mp
    simpa only [Real.exp_log hm0] using hml
  have hlogu : Real.log m ≤ (j : ℝ) + 1 :=
    (Real.log_le_iff_le_exp hm0).mpr hmexp
  exact ⟨hm2, hlogl, hlogu⟩

/-- The explicit exponentially spaced probe covers every logarithm in its block. -/
theorem integer_log_probe_covers_block (j n : ℕ) (hn : ⌊Real.log n⌋₊ = j) :
    |Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ) - Real.log n| ≤ 1 := by
  obtain ⟨_, hlogl, hlogu⟩ := integer_log_probe_bounds j
  have hnl : (j : ℝ) ≤ Real.log n := by
    rw [← hn]
    exact Nat.floor_le (Real.log_natCast_nonneg n)
  have hnu : Real.log n < (j : ℝ) + 1 := by
    rw [← hn]
    exact Nat.lt_floor_add_one _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every unit logarithmic block is within distance one of an integer-log probe. -/
theorem exists_integer_log_probe_for_block (j : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ n : ℕ, ⌊Real.log n⌋₊ = j →
      |Real.log m - Real.log n| ≤ 1 :=
  ⟨⌊Real.exp (j : ℝ)⌋₊ + 1, (integer_log_probe_bounds j).1,
    integer_log_probe_covers_block j⟩

private theorem deficit_log_growth {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, |deviationDeficit lam n| ≤ 2 * Real.log n + A := by
  let A := 100 * ∑' n, deviationExcess lam n
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (tsum_nonneg fun n => deviationExcess_nonneg lam n)
  refine ⟨A, hA, fun n => ?_⟩
  rw [abs_of_nonneg (deviationDeficit_nonneg _ _)]
  have ha := abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive hpos hexc n
  have hv : deviationDeficit lam n ≤ A := max_le ((neg_le_abs _).trans ha) hA
  linarith [Real.log_natCast_nonneg n]

/-- Every unit logarithmic block has uniformly bounded deficit mass. The finite-set
form includes arbitrary subsets of a block and does not assume summable deficit. -/
theorem exists_deficit_logBlock_bound_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ∀ F : Finset ℕ,
      (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, deviationDeficit lam n ≤ B := by
  obtain ⟨A, hA, ha⟩ := deficit_log_growth hpos hexc
  obtain ⟨κ, hκ, hκK⟩ := exists_riemannAutocorr_ge
  obtain ⟨_, hsample⟩ := deficit_potential_control_of_summable_excess hpos hexc
  let S := 2 * riemannAutocorr 0 * (∑' n, deviationExcess lam n) - deviationPotential lam 0
  have hS : 0 ≤ S := by
    have hnonneg : 0 ≤ kernelPotential (deviationDeficit lam) (Real.log 2) :=
      tsum_nonneg fun n => mul_nonneg (deviationDeficit_nonneg _ _)
        (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))
    exact hnonneg.trans (hsample 2 (by omega))
  refine ⟨S / κ, div_nonneg hS hκ.le, fun j F hF => ?_⟩
  obtain ⟨m, hm2, hm⟩ := exists_integer_log_probe_for_block j
  have hlocal : κ * ∑ n ∈ F, deviationDeficit lam n ≤
      kernelPotential (deviationDeficit lam) (Real.log m) := by
    apply WeilAbscissa.mul_sum_le_nullPotential (deviationDeficit_zero lam) hA ha
      (deviationDeficit_nonneg lam)
    · intro y hy
      exact hκK y (abs_le.mp hy)
    · intro n hn
      exact hm n (hF n hn)
  apply (le_div_iff₀ hκ).mpr
  simpa only [mul_comm] using hlocal.trans (hsample m hm2)

/-- Sampled log-shift positivity controls the deficit potential at all real shifts. -/
theorem exists_deficit_kernelPotential_bound_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, kernelPotential (deviationDeficit lam) y ≤ B := by
  obtain ⟨A, hA, ha⟩ := deficit_log_growth hpos hexc
  obtain ⟨B, hB, hblock⟩ :=
    exists_deficit_logBlock_bound_of_logShiftAsymptoticPositive hpos hexc
  obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le
  refine ⟨6 * C * Real.exp 2 * B, by positivity, fun y => ?_⟩
  exact WeilAbscissa.nullPotential_le_of_block (deviationDeficit_nonneg lam)
    (deviationDeficit_zero lam) hA ha hB hblock hC0 hC y

/-- Uniform mass bounds on unit logarithmic blocks imply Cauchy control.
The singleton blocks supply the growth bound needed by the potential estimates. -/
theorem exists_cauchyBounded_of_logBlock {w : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hw0 : w 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (hblock : ∀ j : ℕ, ∀ F : Finset ℕ,
      (∀ n ∈ F, ⌊Real.log n⌋₊ = j) → ∑ n ∈ F, w n ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ CauchyBounded w D := by
  have hpoint (n : ℕ) : w n ≤ A := by
    have h := hblock ⌊Real.log n⌋₊ {n} (by
      intro m hm
      have hmn := Finset.mem_singleton.mp hm
      subst m
      rfl)
    simpa only [Finset.sum_singleton] using h
  have hgrowth (n : ℕ) : |w n| ≤ 2 * Real.log n + A := by
    rw [abs_of_nonneg (hw n)]
    linarith only [hpoint n, Real.log_natCast_nonneg n]
  have hsD := WeilAbscissa.summable_nullPotential_term hw0 hA hgrowth
  obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le
  let B := 6 * C * Real.exp 2 * A
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB (y : ℝ) : kernelPotential w y ≤ B :=
    WeilAbscissa.nullPotential_le_of_block hw hw0 hA hgrowth hA hblock hC0 hC y
  obtain ⟨κ, hκ, hκK⟩ := exists_riemannAutocorr_ge
  let c := 3 / (2 * κ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c * (B * Real.pi), mul_nonneg hc (mul_nonneg hB0 Real.pi_pos.le), ?_⟩
  intro δ hδ0 hδ1 s
  obtain ⟨hsum, hle⟩ := tsum_mul_kernelSmooth_le hw hsD hB
    (cauchyProfile_nonneg hδ0.le s) (continuous_cauchyProfile δ s)
    (integrable_cauchyProfile hδ0 s)
  rw [integral_cauchyProfile hδ0 s] at hle
  have hdom (n : ℕ) : w n *
      (cauchyProfile δ s (Real.log n) + cauchyProfile δ s (-Real.log n)) ≤
      c * (w n *
        (kernelSmooth (cauchyProfile δ s) (Real.log n) +
          kernelSmooth (cauchyProfile δ s) (-Real.log n))) := by
    have hp := cauchyProfile_le_kernelSmooth hκ hκK hδ0 hδ1 s (Real.log n)
    have hn := cauchyProfile_le_kernelSmooth hκ hκK hδ0 hδ1 s (-Real.log n)
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hp hn)
      (hw n)
    dsimp [c]
    nlinarith only [hmul]
  have hnonneg (n : ℕ) : 0 ≤ w n *
      (cauchyProfile δ s (Real.log n) + cauchyProfile δ s (-Real.log n)) :=
    mul_nonneg (hw n)
      (add_nonneg (cauchyProfile_nonneg hδ0.le s _) (cauchyProfile_nonneg hδ0.le s _))
  have hs := Summable.of_nonneg_of_le hnonneg hdom (hsum.mul_left c)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, c * (w n *
        (kernelSmooth (cauchyProfile δ s) (Real.log n) +
          kernelSmooth (cauchyProfile δ s) (-Real.log n))) :=
      Summable.tsum_le_tsum hdom hs (hsum.mul_left c)
    _ = c * ∑' n, w n *
        (kernelSmooth (cauchyProfile δ s) (Real.log n) +
          kernelSmooth (cauchyProfile δ s) (-Real.log n)) := tsum_mul_left
    _ ≤ c * (B * Real.pi) := mul_le_mul_of_nonneg_left hle hc

/-- Full Weil positivity is unnecessary for the deficit Cauchy bound: asymptotic
positivity of logarithmic panels and summable excess suffice. -/
theorem exists_deficit_cauchyBounded_of_logShiftAsymptoticPositive {lam : ℕ → ℝ}
    (hpos : WeilLogShiftAsymptoticPositive lam) (hexc : Summable (deviationExcess lam)) :
    ∃ D : ℝ, 0 ≤ D ∧ CauchyBounded (deviationDeficit lam) D := by
  obtain ⟨B, hB0, hB⟩ := exists_deficit_logBlock_bound_of_logShiftAsymptoticPositive hpos hexc
  exact exists_cauchyBounded_of_logBlock (deviationDeficit_nonneg lam)
    (deviationDeficit_zero lam) hB0 hB

/-- Original countable log-shift tests, with raw normalized excess summable,
already force a uniform Cauchy-profile bound for the deficit. -/
theorem exists_deficit_cauchyBounded_of_logShiftTests {lam : ℕ → ℝ}
    (hpos : WeilLogShiftTestsPositive lam)
    (hexc : Summable fun n => max (lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) 0 /
      Real.sqrt n) :
    ∃ D : ℝ, 0 ≤ D ∧ CauchyBounded (deviationDeficit lam) D := by
  have ha : WeilLogShiftAsymptoticPositive lam := by
    intro ε hε
    refine ⟨0, fun k _ m => ?_⟩
    have hm2 := (Finset.mem_Icc.mp m.2).1
    have hmN := (Finset.mem_Icc.mp m.2).2
    have hmE : (m.1 : ℝ) ≤ Real.exp (2 * (k : ℝ)) :=
      (by exact_mod_cast hmN : (m.1 : ℝ) ≤ (⌊Real.exp (2 * (k : ℝ))⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.exp_pos _).le)
    exact (neg_nonpos.mpr hε.le).trans (hpos k m.1 hm2 hmE)
  exact exists_deficit_cauchyBounded_of_logShiftAsymptoticPositive ha
    (summable_deviationExcess hexc)

end RHTower
