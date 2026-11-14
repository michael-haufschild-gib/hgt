import GaloisForLFunctions.EisensteinDegeneration.MulticoverCoefficients
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittGhost

/-!
# Multicover coefficients as integral Witt ghosts

Signed Euler-factor exponents are allowed over the integers: negative
exponents use the formal unit inverse. Their logarithmic ghosts recover
the multicover divisor transform. Each positive coefficient is already
determined by a finite Euler product, with no analytic convergence input.
-/

noncomputable section

namespace GaloisForLFunctions.EisensteinDegeneration

open PowerSeries _root_.RHTower

/-- An integral power of the constant-one Euler factor, including negative powers. -/
def signedEulerFactor (m : ℕ) : ℤ → PowerSeries ℤ
  | .ofNat e => deningerBigWittFactor 1 (m + 1) ^ e
  | .negSucc e => (invOfUnit (deningerBigWittFactor 1 (m + 1)) 1) ^ (e + 1)

@[simp] theorem signedEulerFactor_constantCoeff (m : ℕ) (e : ℤ) :
    constantCoeff (signedEulerFactor m e) = 1 := by
  cases e <;> simp [signedEulerFactor, deningerBigWittFactor_constantCoeff]

private theorem inverseFactor_ghost (m : ℕ) :
    deningerBigWittLogGhost (invOfUnit (deningerBigWittFactor (1 : ℤ) (m + 1)) 1)
        (by simp) =
      -deningerBigWittLogGhost (deningerBigWittFactor (1 : ℤ) (m + 1)) (by simp) := by
  let f := deningerBigWittFactor (1 : ℤ) (m + 1)
  have hf : constantCoeff f = 1 := by simp [f]
  have hi : constantCoeff (invOfUnit f 1) = 1 := by simp
  have h := deningerBigWittLogGhost_mul f (invOfUnit f 1) hf hi
  have hu := PowerSeries.mul_invOfUnit f 1 hf
  have he := deningerBigWittLogGhost_congr (by simp [hf, hi]) (by simp) hu
  have hone : deningerBigWittLogGhost (1 : PowerSeries ℤ) (by simp) = 0 := by
    simp [deningerBigWittLogGhost]
  have hs := h.symm.trans (he.trans hone)
  change deningerBigWittLogGhost (invOfUnit f 1) hi = -deningerBigWittLogGhost f hf
  linear_combination hs

/-- Signed Euler exponents become integer multiples under the ghost map. -/
theorem signedEulerFactor_ghost (m : ℕ) (e : ℤ) :
    deningerBigWittLogGhost (signedEulerFactor m e) (by simp) =
      e • deningerBigWittLogGhost (deningerBigWittFactor (1 : ℤ) (m + 1)) (by simp) := by
  cases e with
  | ofNat e =>
      simpa [signedEulerFactor] using
        deningerBigWittLogGhost_pow (deningerBigWittFactor (1 : ℤ) (m + 1)) (by simp) e
  | negSucc e =>
      have h := deningerBigWittLogGhost_pow
        (invOfUnit (deningerBigWittFactor (1 : ℤ) (m + 1)) 1) (by simp) (e + 1)
      rw [inverseFactor_ghost] at h
      simpa [signedEulerFactor] using h

/-- The finite product carrying every multicover coefficient through its cutoff. -/
def multicoverEulerProduct (k : ℕ) (w : ℕ → ℤ) (N : ℕ) : PowerSeries ℤ :=
  ∏ m ∈ Finset.range N, signedEulerFactor m ((m + 1 : ℤ) ^ k * w (m + 1))

@[simp] theorem multicoverEulerProduct_constantCoeff (k : ℕ) (w : ℕ → ℤ) (N : ℕ) :
    constantCoeff (multicoverEulerProduct k w N) = 1 := by
  simp [multicoverEulerProduct]

/-- The positive ghost coefficients are precisely the divisor sums of signed Euler weights. -/
theorem multicoverEulerProduct_ghost_coefficient (k : ℕ) (w : ℕ → ℤ) (n : ℕ) :
    coeff (n + 1)
      (deningerBigWittLogGhost (multicoverEulerProduct k w (n + 1)) (by simp)) =
      multicover (k + 1) w (n + 1) := by
  simp only [multicoverEulerProduct]
  rw [deningerBigWittLogGhost_finset_prod _ _ (fun m => signedEulerFactor_constantCoeff m _)]
  simp only [map_sum, signedEulerFactor_ghost, map_zsmul]
  simp only [deningerBigWittLogGhost_factor_coeff (1 : ℤ) (Nat.succ_pos _) (Nat.succ_pos n),
    one_pow, mul_one, zsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hsum : (∑ m ∈ Finset.range (n + 1),
      (m + 1 : ℤ) ^ k * w (m + 1) * (if m + 1 ∣ n + 1 then (m + 1 : ℤ) else 0)) =
      ∑ d ∈ (n + 1).divisors, (d : ℤ) ^ (k + 1) * w d := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hs : (Finset.range (n + 1)).filter (fun m => m + 1 ∣ n + 1) =
        (n + 1).divisors.image (fun d => d - 1) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨hm, hd⟩
        exact ⟨m + 1, ⟨hd, Nat.succ_ne_zero n⟩, by omega⟩
      · rintro ⟨d, ⟨hd, _⟩, he⟩
        have hp := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, Nat.succ_ne_zero n⟩)
        have hl := Nat.le_of_dvd (Nat.succ_pos n) hd
        have hm : m + 1 = d := by omega
        exact ⟨by omega, by rwa [hm]⟩
    rw [hs, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro d hd
      have hpos := Nat.pos_of_mem_divisors hd
      have hcast : ((d - 1 : ℕ) : ℤ) + 1 = (d : ℤ) := by
        exact_mod_cast Nat.sub_add_cancel hpos
      rw [Nat.sub_add_cancel hpos, hcast, pow_succ]
      ring
    · intro a ha b hb h
      have hpa := Nat.pos_of_mem_divisors ha
      have hpb := Nat.pos_of_mem_divisors hb
      omega
  exact hsum

end GaloisForLFunctions.EisensteinDegeneration

#print axioms GaloisForLFunctions.EisensteinDegeneration.signedEulerFactor_constantCoeff
#print axioms GaloisForLFunctions.EisensteinDegeneration.signedEulerFactor_ghost
#print axioms GaloisForLFunctions.EisensteinDegeneration.multicoverEulerProduct_constantCoeff
#print axioms GaloisForLFunctions.EisensteinDegeneration.multicoverEulerProduct_ghost_coefficient
