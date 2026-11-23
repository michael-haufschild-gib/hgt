import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ResponseRange

/-! # Relative Gibbs costs, including positive exponents at and below the zeta pole -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

abbrev GibbsExponent := Ioi (0:ℝ)

def powerResponse (β : GibbsExponent) : SpectralResponse where
  value x := x^β.val
  cont := (Real.continuous_rpow_const β.property.le).continuousOn
  inc := by intro x hx y _ h; exact Real.rpow_lt_rpow hx.1 h β.property

def shellPower (β : GibbsExponent) (n : ℕ) : ℝ := 1/((n:ℝ)+1)^β.val

def gibbsHead (β : GibbsExponent) (r : ℕ) : ℝ := ∑ n ∈ Finset.range r, shellPower β n

theorem power_head_eq (β : GibbsExponent) (r : ℕ) : relativeHead (powerResponse β) r = gibbsHead β r := by
  apply Finset.sum_congr rfl
  intro n _
  change occupationWeight n ^ β.val-(0:ℝ)^β.val = 1/((n:ℝ)+1)^β.val
  rw [Real.zero_rpow β.property.ne',sub_zero,occupationWeight_eq,Real.inv_rpow (by positivity),one_div]

/-- The ordinary individual sums may diverge. The series of paired singular-value differences always converges. -/
theorem summable_relative_powers (β : GibbsExponent) {r : ℕ} (b : SpectralBand r) :
    Summable (fun n => occupationWeight n^β.val-(b n).val^β.val) :=
  summable_spectralDrop (powerResponse β) b

theorem gibbs_range_at_rank (β : GibbsExponent) (r : ℕ) :
    responseAtRank (powerResponse β) (r+1) = Ioo 0 (gibbsHead β (r+1)) := by
  rw [responseAtRank_succ,power_head_eq]

/-- The set of costs when any finite number of directions may be omitted. -/
def finiteGibbsLosses (β : GibbsExponent) := ⋃ r, responseAtRank (powerResponse β) r

theorem finiteGibbsLosses_iff (β : GibbsExponent) (y : ℝ) :
    y ∈ finiteGibbsLosses β ↔ y = 0 ∨ (0 < y ∧ ∃ r, y < gibbsHead β (r+1)) := by
  constructor
  · intro hy
    obtain ⟨r,hr⟩ := mem_iUnion.mp hy
    cases r with
    | zero => exact Or.inl (by simpa only [responseAtRank_zero,mem_singleton_iff] using hr)
    | succ k =>
      rw [gibbs_range_at_rank] at hr
      exact Or.inr ⟨hr.1,k,hr.2⟩
  · rintro (rfl | ⟨hy,r,hr⟩)
    · apply mem_iUnion.mpr
      exact ⟨0,by simpa only [responseAtRank_zero] using (mem_singleton (0:ℝ))⟩
    · exact mem_iUnion.mpr ⟨r+1,by rw [gibbs_range_at_rank]; exact ⟨hy,hr⟩⟩

#print axioms summable_relative_powers
#print axioms gibbs_range_at_rank
#print axioms finiteGibbsLosses_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
