import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum.Calibration

/-! # Isometric composition from a single calibrated depth on all integer labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open Finset Filter Real InverseSpectrum.ShellMixing
open scoped Topology

/-- The contribution of label two gives a strict gap at every larger cutoff. -/
private theorem incompatible {b c v : ℝ} (hbc : b<c)
    (hb : Tendsto (prefixMass b) atTop (𝓝 v)) (hc : Tendsto (prefixMass c) atTop (𝓝 v)) : False := by
  have less : occupationWeight 1 < 1 := (occupationWeight_strictAnti Nat.zero_lt_one).trans_eq occupationWeight_zero
  have pos := sub_pos.mpr (rpow_lt_rpow_of_exponent_gt (occupationWeight_pos 1) less hbc)
  have h := hb.sub hc
  rw [sub_self] at h
  have gap : occupationWeight 1^b - occupationWeight 1^c ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds h
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    change _ ≤ prefixMass b N-prefixMass c N
    rw [prefixMass,prefixMass,←sum_sub_distrib]
    apply single_le_sum (f := fun i => occupationWeight i^b - occupationWeight i^c) _
      (mem_range.mpr (by omega : 1<N+1))
    intro i _
    exact sub_nonneg.mpr (rpow_le_rpow_of_exponent_ge (occupationWeight_pos i)
      ((occupationWeight_antitone (Nat.zero_le i)).trans_eq occupationWeight_zero) hbc.le)
  exact pos.not_ge gap

/-- At any chosen positive depth, observing its single zeta value is
equivalent to norm preservation by the input divisor split on the full gas. -/
theorem isometric_iff (k : ℕ) (s : ℂ) (z : ℕ → ℕ → SplitParameter) :
    Tendsto (fun N => calibrated (z N) s N (k+1)) atTop (𝓝 (riemannZeta ((k+2:ℕ):ℂ)).re) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x,T f x=split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro measured
    have known := prefix_limit ⟨((k+2:ℕ):ℝ),by exact_mod_cast (show 1<k+2 by omega)⟩
    simp only [Complex.ofReal_natCast] at known
    have obs : Tendsto (prefixMass (2*s.re+((k+1:ℕ):ℝ))) atTop (𝓝 (riemannZeta ((k+2:ℕ):ℂ)).re) :=
      measured.congr fun N => calibrated_eq (z N) s N (k+1)
    rcases lt_trichotomy (2*s.re+((k+1:ℕ):ℝ)) ((k+2:ℕ):ℝ) with lt|eq|gt
    · exact False.elim (incompatible lt obs known)
    · push_cast at eq
      linarith only [eq]
    · exact False.elim (incompatible gt known obs)
  · intro hs
    exact critical_limit k (fun _ => ⟨s,hs⟩) z

#print axioms isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
