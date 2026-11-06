import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheThreeQuartersScaleOfTheRate
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheParityProducerHasAQuantitativeCost

/-!
# The bracket of the best rate

`bestRate K` is the infimum of the rates of producers on alphabets in `[1, K]`. It is the exact rate
`A(K) − 1` asked for by the programme. For all large `K`,

`c₁ K^{-3/4} ≤ bestRate K ≤ C / log log K`.

The lower side is the three-quarters floor, and it is unconditional. The upper side is the Möbius–Farkas
producer, whose alphabet is a factorial period and so is doubly exponential in `1/ε`. The gap between the
two sides is what a construction has to close: polynomial rates give a zero-free strip, and they would
need alphabets polynomial in `1/ε`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The set of rates of producers on an alphabet in `[1, K]`. -/
def rateSet (K : ℕ) : Set ℝ :=
  {ε | ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧ rate c m B = ε}

/-- The best rate at alphabet size `K`: the exact value of `A(K) − 1`. -/
def bestRate (K : ℕ) : ℝ := sInf (rateSet K)

/-- **The upper side.** There is a `C > 0` with `HasRate (C / log log K)`. -/
theorem exists_hasRate_log_log :
    ∃ C : ℝ, 0 < C ∧ HasRate fun K => C / Real.log (Real.log K) := by
  obtain ⟨C, hC, hprod⟩ := exists_producer_with_double_exp_cost
  refine ⟨C, hC, ?_⟩
  have hlim : Tendsto (fun K : ℕ => Real.log (Real.log (K : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually_ge_atTop C, eventually_ge_atTop 3] with K hK hK3
  have hKR : (3 : ℝ) ≤ K := by exact_mod_cast hK3
  have hL0 : 0 < Real.log (Real.log (K : ℝ)) := lt_of_lt_of_le hC hK
  have hlogK : 0 < Real.log (K : ℝ) := Real.log_pos (by linarith)
  set ε : ℝ := C / Real.log (Real.log K) with hε
  have hε0 : 0 < ε := div_pos hC hL0
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hL0]
    exact hK
  obtain ⟨c, m, B, hP, hA, hal, _⟩ := hprod ε hε0 hε1
  refine ⟨c, m, B, hP, fun k hk => ?_, ?_⟩
  · have h := hal k hk
    have hval : C / ε = Real.log (Real.log K) := by
      rw [hε]
      field_simp
    rw [hval, Real.exp_log hlogK, Real.exp_log (by linarith)] at h
    exact_mod_cast h
  · rw [rate]
    linarith

/-- **The bracket of the best rate.** For all large `K`,
`c₁ K^{-3/4} ≤ bestRate K ≤ C / log log K`. -/
theorem exists_bracket_bestRate :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ᶠ K : ℕ in atTop,
      c₁ * (K : ℝ) ^ (-(3 / 4) : ℝ) ≤ bestRate K ∧ bestRate K ≤ C / Real.log (Real.log K) := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_three_quarters_floor
  obtain ⟨C, hC, hrate⟩ := exists_hasRate_log_log
  refine ⟨c₁, C, hc₁, hC, ?_⟩
  filter_upwards [hrate, eventually_ge_atTop 1] with K hK hK1
  obtain ⟨c, m, B, hP, hKa, hr⟩ := hK
  have hmem : rate c m B ∈ rateSet K := ⟨c, m, B, hP, hKa, rfl⟩
  have hbdd : BddBelow (rateSet K) := by
    refine ⟨0, ?_⟩
    rintro ε ⟨c', m', B', hP', _, rfl⟩
    exact hP'.rate_pos.le
  refine ⟨le_csInf ⟨_, hmem⟩ ?_, (csInf_le hbdd hmem).trans hr⟩
  rintro ε ⟨c', m', B', hP', hKa', rfl⟩
  exact hfloor K c' m' B' hK1 hP' hKa'

/-- **Every producer family has a rate that tends to zero, and none is ever zero.** -/
theorem tendsto_bestRate_zero : Tendsto bestRate atTop (𝓝 0) := by
  obtain ⟨c₁, C, hc₁, hC, hb⟩ := exists_bracket_bestRate
  have hlim : Tendsto (fun K : ℕ => C / Real.log (Real.log (K : ℝ))) atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_div_atTop C
  refine squeeze_zero' ?_ (hb.mono fun K hK => hK.2) hlim
  filter_upwards [hb, eventually_ge_atTop 1] with K hK hK1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  exact (mul_nonneg hc₁.le (Real.rpow_pos_of_pos hK0 _).le).trans hK.1

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
