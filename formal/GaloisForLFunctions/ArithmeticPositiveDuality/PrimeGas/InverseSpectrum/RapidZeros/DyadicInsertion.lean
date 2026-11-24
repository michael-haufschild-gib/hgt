import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.VacuumBlend
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.NaturalBoundary

/-! # Geometric occupation weights at doubly exponential prime labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift
open U0NaturalBoundary

def dyadicWave (p : Nat.Primes) := insertedWave (primePNat p) (vacuumBlend (lacunaryOmission p))

def dyadicLabel (p : Nat.Primes) (j : ℕ) := primeRayLabel p (2^j)

private theorem exponent_split (p : Nat.Primes) (j : ℕ) :
    dyadicLabel p (j+1) = primePNat p*primeRayLabel p (2^(j+1)-1) := by
  change primePNat p^(2^(j+1)) = primePNat p * primePNat p^(2^(j+1)-1)
  rw [← pow_succ']
  congr 1
  have : 1 ≤ 2^(j+1) := Nat.one_le_two_pow
  omega

private theorem lacunary_vacuum (p : Nat.Primes) : lacunaryLaw p 1 = 0 := by
  have h0 : primeRayLabel p 0 = 1 := pow_zero _
  rw [← h0,lacunaryLaw_at,lacunaryMass,lacCoeff_zero,norm_zero]
  intro j
  have h : 1 ≤ 2^j := Nat.one_le_two_pow
  rw [pow_succ]
  omega

/-- At p^(2^j) the Born probabilities are the exact geometric weights. -/
theorem dyadicWave_probability (p : Nat.Primes) (j : ℕ) :
    occupationProbability (dyadicWave p) (dyadicLabel p j) = (1/2:ℝ)^(j+1) := by
  rw [dyadicWave,insertedWave_probability]
  cases j with
  | zero =>
    have he : dyadicLabel p 0 = primePNat p*1 := by simp [dyadicLabel,primeRayLabel]
    rw [he,insertedMass_at,vacuumBlend_probability,lacunary_probability,lacunary_vacuum]
    norm_num [vacuumMass]
  | succ j =>
    have hn : primeRayLabel p (2^(j+1)-1) ≠ 1 := by
      intro h
      have hh := (primeRayLabel_injective p) (h.trans (show primeRayLabel p 0 = 1 from pow_zero _).symm)
      have hpos : 1 ≤ 2^j := Nat.one_le_two_pow
      rw [pow_succ] at hh
      omega
    rw [exponent_split,insertedMass_at,vacuumBlend_probability,lacunary_probability,lacunaryLaw_at,
      vacuumMass,if_neg hn,add_zero,lacunaryMass,lacCoeff_emb,norm_zpow,Complex.norm_two,zpow_neg]
    have hi : (j:ℤ)+1 = ((j+1:ℕ):ℤ) := by push_cast; rfl
    rw [hi,zpow_natCast,pow_succ (1/2:ℝ) (j+1),one_div,inv_pow]
    ring

theorem dyadicWave_off (p : Nat.Primes) {n : ℕ+} (hn : n ∉ Set.range (dyadicLabel p)) :
    occupationProbability (dyadicWave p) n = 0 := by
  rw [dyadicWave,insertedWave_probability]
  by_cases h : n ∈ Set.range (fun x : ℕ+ => primePNat p*x)
  · obtain ⟨x,rfl⟩ := h
    have hx : x ≠ 1 := by
      rintro rfl
      exact hn ⟨0,by simp [dyadicLabel,primeRayLabel]⟩
    rw [insertedMass_at,vacuumBlend_probability,lacunary_probability,vacuumMass,if_neg hx,add_zero]
    have hz : lacunaryLaw p x = 0 := by
      by_cases hr : x ∈ Set.range (primeRayLabel p)
      · obtain ⟨k,rfl⟩ := hr
        rw [lacunaryLaw_at,lacunaryMass,lacCoeff_zero,norm_zero]
        rintro j rfl
        exact hn ⟨j+1,exponent_split p j⟩
      · exact lacunaryLaw_off p hr
    rw [hz,zero_div]
  · exact insertedMass_off _ _ _ h

theorem dyadicWave_finiteSplit_iff (p : Nat.Primes) (s : ℂ) :
    finiteSplit (dyadicWave p) s ↔ 1/2 ≤ s.re := by
  rw [dyadicWave,inserted_finiteSplit_iff,vacuumBlend_finiteSplit_iff,lacunary_split_iff]

theorem dyadicWave_natural_boundary (p : Nat.Primes) (s : ℂ) (hs : s.re = 1/2) :
    ¬ ContinuesAcross (compositionResponse (dyadicWave p)) compositionRight s := by
  rw [dyadicWave,inserted_continues_iff,vacuumBlend_continues_iff]
  · exact lacunary_response_natural_boundary p s hs
  · intro z hz
    exact (lacunary_split_iff p z).mpr (show 1/2 < z.re from hz).le

/-- Mixing with the vacuum and inserting one prime preserves the isometry test by a finite but noncontinuable response. -/
theorem dyadic_finite_singular_iff_isometry (p : Nat.Primes) (s : ℂ) :
    (finiteSplit (dyadicWave p) s ∧ ¬ ContinuesAcross (compositionResponse (dyadicWave p)) compositionRight s) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  have hD (z : ℂ) (hz : z ∈ compositionRight) : finiteSplit (lacunaryOmission p) z :=
    (lacunary_split_iff p z).mpr (show 1/2 < z.re from hz).le
  rw [dyadicWave,inserted_finiteSplit_iff,vacuumBlend_finiteSplit_iff,inserted_continues_iff,
    vacuumBlend_continues_iff _ _ _ hD]
  exact finite_singular_iff_split_isometric p s

#print axioms dyadic_finite_singular_iff_isometry
#print axioms dyadicWave_probability
#print axioms dyadicWave_off
#print axioms dyadicWave_finiteSplit_iff
#print axioms dyadicWave_natural_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
