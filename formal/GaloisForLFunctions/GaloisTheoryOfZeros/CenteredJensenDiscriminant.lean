import GaloisForLFunctions.FiniteFreeProbability.NonRealRootCount
import GaloisForLFunctions.FiniteFreeProbability.BulkHyperbolicity
import GaloisForLFunctions.RHTower.RiemannKernelMomentsNotMultiplier
import GaloisForLFunctions.HTGeometry.EigenLogDerivNormalization
import GaloisForLFunctions.GaloisTheoryOfZeros.FoldedDiscriminant

/-!
# Discriminants of the centered Jensen equations

After positive monic normalization, the even equation is `E_n(X²)` and the
odd equation is `X O_n(X²)`. Their quotient constant terms are signed positive
Riemann-kernel moments. The full discriminants are therefore positive moment
factors times the squares of the quotient discriminants, at every degree.

This proves nonnegativity for the actual centered Jensen discriminants,
including collisions. Vanishing is exactly failure of quotient separability;
the forced odd-degree zero is simple. The quotient equations retain the
root information discarded by the full discriminant square.
-/

noncomputable section
open Polynomial Complex
open FiniteFreeProbability RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros

private theorem centered_map (d : ℕ) :
    (xiJensenReal d).map Complex.ofRealHom = xiJensen (1/2) d := by
  rw [xiJensen, mk_xiShiftCoeff_half, jensenRev_xiSeries]
  rfl

private theorem centered_leadingCoeff (d : ℕ) :
    (xiJensenReal d).leadingCoeff = xiMoment (1/2) 0 := by
  apply Complex.ofReal_injective
  calc
    ((xiJensenReal d).leadingCoeff : ℂ) =
        ((xiJensenReal d).map Complex.ofRealHom).coeff d := by
      rw [coeff_map, leadingCoeff, natDegree_xiJensenReal]
      rfl
    _ = (xiJensen (1/2) d).coeff d := congrArg (fun p => p.coeff d) (centered_map d)
    _ = (xiMoment (1/2) 0 : ℂ) := by
      rw [xiJensen, coeff_jensenRev_self, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_mk, xiShiftCoeff_eq_moment]
      simp

/-- Monic centered reversed Jensen equation. -/
def monicCenteredJensen (d : ℕ) : ℝ[X] :=
  xiJensenReal d * C (xiMoment (1/2) 0)⁻¹

private theorem monicCenteredJensen_monic (d : ℕ) :
    (monicCenteredJensen d).Monic := by
  rw [monicCenteredJensen, ← centered_leadingCoeff d]
  apply monic_mul_leadingCoeff_inv
  intro hzero
  have h := congrArg Polynomial.leadingCoeff hzero
  rw [centered_leadingCoeff, leadingCoeff_zero] at h
  exact (xiMoment_zero_pos _).ne' h

private theorem monicCenteredJensen_natDegree (d : ℕ) :
    (monicCenteredJensen d).natDegree = d := by
  rw [monicCenteredJensen, natDegree_mul_C
    (inv_ne_zero (xiMoment_zero_pos _).ne'), natDegree_xiJensenReal]

private theorem centered_comp_neg (d : ℕ) :
    (xiJensenReal d).comp (-X) = C ((-1 : ℝ)^d) * xiJensenReal d := by
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
  rw [Polynomial.map_comp, Polynomial.map_neg, map_X, Polynomial.map_mul, map_C,
    centered_map, map_pow, map_neg, map_one]
  apply Polynomial.funext
  intro z
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C]
  exact eval_xiJensen_half_neg d z

private theorem monicCenteredJensen_comp_neg (d : ℕ) :
    (monicCenteredJensen d).comp (-X) = C ((-1 : ℝ)^d) * monicCenteredJensen d := by
  rw [monicCenteredJensen, mul_comp, C_comp, centered_comp_neg, mul_assoc]

/-- The even coefficient part, with exponents divided by two. -/
def squareQuotient (P : ℝ[X]) : ℝ[X] := P.contract 2

private theorem squareQuotient_comp {P : ℝ[X]} (heven : P.comp (-X) = P) :
    (squareQuotient P).comp (X^2) = P := by
  have hodd : ∀ k, ¬ 2 ∣ k → P.coeff k = 0 := by
    intro k hk
    have h := congrArg (fun p : ℝ[X] => p.coeff k) heven
    have hx : (-X : ℝ[X]) = C (-1) * X := by simp
    rw [hx, GaloisForLFunctions.HTGeometry.coeff_comp_C_mul_X] at h
    rw [(Nat.odd_iff.mpr (by omega) : Odd k).neg_one_pow] at h
    linarith
  ext k
  rw [← expand_eq_comp_X_pow, coeff_expand (by norm_num : 0 < 2)]
  split_ifs with hk
  · rw [squareQuotient, coeff_contract (by decide : 2 ≠ 0), Nat.div_mul_cancel hk]
  · exact (hodd k hk).symm

private theorem centered_even_moment_pos (n : ℕ) :
    0 < xiMoment (1/2) (2*n) := by
  simpa only [xiMoment, kernelEvenMoment, sub_self, zero_mul, mul_zero, Real.exp_zero,
    mul_one, one_mul, mul_comm] using evenMoment_pos RHTower.DeBruijn.riemannKernel_superExp n




/-- The equation of the squared roots in even degree. -/
def evenCenteredQuotient (n : ℕ) : ℝ[X] :=
  squareQuotient (monicCenteredJensen (2*n))

/-- The equation of the squared nonzero roots in odd degree. -/
def oddCenteredQuotient (n : ℕ) : ℝ[X] :=
  squareQuotient (monicCenteredJensen (2*n+1)).divX

private theorem monicCenteredJensen_even (n : ℕ) :
    (monicCenteredJensen (2*n)).comp (-X) = monicCenteredJensen (2*n) := by
  rw [monicCenteredJensen_comp_neg, pow_mul, neg_one_sq, one_pow, C_1, one_mul]

private theorem monicCenteredJensen_odd (n : ℕ) :
    (monicCenteredJensen (2*n+1)).comp (-X) = -monicCenteredJensen (2*n+1) := by
  rw [monicCenteredJensen_comp_neg, pow_succ, pow_mul, neg_one_sq, one_pow,
    one_mul, map_neg, C_1, neg_one_mul]

private theorem coeff_comp_neg (P : ℝ[X]) (k : ℕ) :
    (P.comp (-X)).coeff k = (-1)^k * P.coeff k := by
  have hx : (-X : ℝ[X]) = C (-1) * X := by simp
  rw [hx, GaloisForLFunctions.HTGeometry.coeff_comp_C_mul_X]

private theorem monicCenteredJensen_odd_zero (n : ℕ) :
    (monicCenteredJensen (2*n+1)).coeff 0 = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.coeff 0) (monicCenteredJensen_odd n)
  rw [coeff_comp_neg, pow_zero, one_mul, coeff_neg] at h
  linarith

private theorem centered_odd_divX_even (n : ℕ) :
    ((monicCenteredJensen (2*n+1)).divX).comp (-X) =
      (monicCenteredJensen (2*n+1)).divX := by
  ext k
  have h := congrArg (fun p : ℝ[X] => p.coeff (k+1)) (monicCenteredJensen_odd n)
  rw [coeff_comp_neg, pow_succ, coeff_neg] at h
  rw [coeff_comp_neg, coeff_divX]
  linarith

theorem evenCenteredQuotient_factor (n : ℕ) :
    (evenCenteredQuotient n).comp (X^2) = monicCenteredJensen (2*n) :=
  squareQuotient_comp (monicCenteredJensen_even n)

theorem oddCenteredQuotient_factor (n : ℕ) :
    X * (oddCenteredQuotient n).comp (X^2) = monicCenteredJensen (2*n+1) := by
  rw [oddCenteredQuotient, squareQuotient_comp (centered_odd_divX_even n)]
  have h := X_mul_divX_add (monicCenteredJensen (2*n+1))
  simpa only [monicCenteredJensen_odd_zero, C_0, add_zero] using h

private theorem squareQuotient_monic {P : ℝ[X]} (hm : P.Monic)
    (he : P.comp (-X) = P) : (squareQuotient P).Monic := by
  rw [← monic_expand_iff (by decide : 0 < 2), expand_eq_comp_X_pow,
    squareQuotient_comp he]
  exact hm

theorem evenCenteredQuotient_monic (n : ℕ) : (evenCenteredQuotient n).Monic :=
  squareQuotient_monic (monicCenteredJensen_monic _) (monicCenteredJensen_even n)

theorem oddCenteredQuotient_monic (n : ℕ) : (oddCenteredQuotient n).Monic := by
  apply squareQuotient_monic _ (centered_odd_divX_even n)
  have h := X_mul_divX_add (monicCenteredJensen (2*n+1))
  rw [monicCenteredJensen_odd_zero, C_0, add_zero] at h
  have hm := (monicCenteredJensen_monic (2*n+1)).leadingCoeff
  rw [← h, leadingCoeff_mul, leadingCoeff_X, one_mul] at hm
  exact hm

theorem evenCenteredQuotient_natDegree (n : ℕ) :
    (evenCenteredQuotient n).natDegree = n := by
  have h := congrArg Polynomial.natDegree (evenCenteredQuotient_factor n)
  rw [← expand_eq_comp_X_pow, natDegree_expand, monicCenteredJensen_natDegree] at h
  omega

theorem oddCenteredQuotient_natDegree (n : ℕ) :
    (oddCenteredQuotient n).natDegree = n := by
  have h := congrArg Polynomial.natDegree (oddCenteredQuotient_factor n)
  have hne := ((oddCenteredQuotient_monic n).comp (monic_X_pow 2)
    (by simp)).ne_zero
  rw [natDegree_X_mul hne, ← expand_eq_comp_X_pow, natDegree_expand,
    monicCenteredJensen_natDegree] at h
  omega



private theorem centered_even_coeff_zero (n : ℕ) :
    (monicCenteredJensen (2*n)).coeff 0 =
      (-1)^n * (xiMoment (1/2) (2*n) / xiMoment (1/2) 0) := by
  have hc := congrArg (fun p : ℂ[X] => p.coeff 0) (centered_map (2*n))
  rw [coeff_map, xiJensen, coeff_jensenRev _ _ (Nat.zero_le _), Nat.sub_zero,
    PowerSeries.coeff_mk, xiShiftCoeff_eq_moment, Nat.descFactorial_self,
    pow_mul, I_sq] at hc
  have hf : (((2*n).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [div_mul_cancel₀ _ hf] at hc
  change ((xiJensenReal (2*n)).coeff 0 : ℂ) =
    (-1)^n * (xiMoment (1/2) (2*n) : ℂ) at hc
  apply Complex.ofReal_injective
  rw [monicCenteredJensen, coeff_mul_C]
  push_cast
  rw [hc]
  simp only [div_eq_mul_inv]
  ring

private theorem derivative_monicCenteredJensen (d : ℕ) :
    (monicCenteredJensen (d+1)).derivative = C ((d : ℝ)+1) * monicCenteredJensen d := by
  have hd : (xiJensenReal (d+1)).derivative = C ((d : ℝ)+1) * xiJensenReal d := by
    rw [xiJensenReal_eq, xiJensenReal_eq]
    exact derivative_jensenRev d _
  rw [monicCenteredJensen, derivative_mul, derivative_C, mul_zero, add_zero,
    hd, mul_assoc, monicCenteredJensen]

private theorem centered_odd_coeff_one (n : ℕ) :
    (monicCenteredJensen (2*n+1)).coeff 1 =
      ((2*n : ℕ) + 1 : ℝ) *
        ((-1)^n * (xiMoment (1/2) (2*n) / xiMoment (1/2) 0)) := by
  have h := congrArg (fun p : ℝ[X] => p.coeff 0) (derivative_monicCenteredJensen (2*n))
  simpa only [coeff_derivative, Nat.zero_add, Nat.cast_zero, zero_add, mul_one,
    coeff_C_mul, centered_even_coeff_zero] using h

theorem evenCenteredQuotient_coeff_zero (n : ℕ) :
    (evenCenteredQuotient n).coeff 0 =
      (-1)^n * (xiMoment (1/2) (2*n) / xiMoment (1/2) 0) := by
  rw [evenCenteredQuotient, squareQuotient, coeff_contract (by decide : 2 ≠ 0),
    Nat.zero_mul, centered_even_coeff_zero]

theorem oddCenteredQuotient_coeff_zero (n : ℕ) :
    (oddCenteredQuotient n).coeff 0 =
      (-1)^n * (((2*n : ℕ)+1 : ℝ) * xiMoment (1/2) (2*n) / xiMoment (1/2) 0) := by
  rw [oddCenteredQuotient, squareQuotient, coeff_contract (by decide : 2 ≠ 0),
    Nat.zero_mul, coeff_divX, Nat.zero_add, centered_odd_coeff_one]
  ring




private theorem discr_C_mul_real {P : ℝ[X]} {c : ℝ} (hc : c ≠ 0) :
    (C c * P).discr = c ^ (2 * P.natDegree - 2) * P.discr := by
  by_cases hz : P.natDegree = 0
  · have hp := eq_C_of_natDegree_eq_zero hz
    rw [hp, ← C_mul, discr_C, discr_C, natDegree_C]
    simp
  have hn : 0 < P.natDegree := Nat.pos_of_ne_zero hz
  have hPn : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hn
  have hscaled : 0 < (C c * P).degree := by
    rw [← natDegree_pos_iff_degree_pos, natDegree_C_mul hc]
    exact hn
  have h := resultant_deriv hscaled
  rw [natDegree_C_mul hc, leadingCoeff_mul, leadingCoeff_C, derivative_C_mul,
    resultant_C_mul_left, resultant_C_mul_right, resultant_deriv hPn] at h
  have hp0 : P ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hn
    exact Nat.lt_irrefl _ hn
  have hl : P.leadingCoeff ≠ 0 := mt leadingCoeff_eq_zero.mp hp0
  have hs : (-1 : ℝ)^(P.natDegree*(P.natDegree-1)/2) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ (mul_ne_zero hs (mul_ne_zero hc hl))
  calc
    ((-1 : ℝ)^(P.natDegree*(P.natDegree-1)/2) * (c * P.leadingCoeff)) *
        (C c * P).discr =
        c^(P.natDegree-1) *
          (c^P.natDegree * ((-1 : ℝ)^(P.natDegree*(P.natDegree-1)/2) *
            P.leadingCoeff * P.discr)) := h.symm
    _ = ((-1 : ℝ)^(P.natDegree*(P.natDegree-1)/2) * (c * P.leadingCoeff)) *
        (c^(2*P.natDegree-2) * P.discr) := by
      have he : P.natDegree-1+P.natDegree = (2*P.natDegree-2)+1 := by omega
      rw [← mul_assoc, ← pow_add, he, pow_succ]
      ring


/-- Positive normalization preserves every root occurrence. -/
theorem roots_monicCenteredJensen (d : ℕ) :
    ((monicCenteredJensen d).map Complex.ofRealHom).roots =
      (xiJensen (1/2) d).roots := by
  rw [monicCenteredJensen, Polynomial.map_mul, map_C, centered_map, mul_comm]
  exact roots_C_mul _ (Complex.ofReal_ne_zero.mpr
    (inv_ne_zero (xiMoment_zero_pos _).ne'))

/-- The even-degree full discriminant is a positive moment factor times a square. -/
theorem discr_even_monicCenteredJensen (n : ℕ) :
    (monicCenteredJensen (2*n)).discr =
      4^n * (xiMoment (1/2) (2*n) / xiMoment (1/2) 0) *
        (evenCenteredQuotient n).discr^2 := by
  rw [← evenCenteredQuotient_factor, discr_comp_square_real (evenCenteredQuotient_monic n),
    evenCenteredQuotient_natDegree, evenCenteredQuotient_coeff_zero]
  have hs : ((-1 : ℝ)^n) * ((-1)^n) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc ((-1 : ℝ)^n) ((-1)^n) _, hs, one_mul]

/-- The odd-degree full discriminant has an additional squared branch value. -/
theorem discr_odd_monicCenteredJensen (n : ℕ) :
    (monicCenteredJensen (2*n+1)).discr =
      4^n * (((2*n : ℕ)+1 : ℝ) * xiMoment (1/2) (2*n) / xiMoment (1/2) 0)^3 *
        (oddCenteredQuotient n).discr^2 := by
  rw [← oddCenteredQuotient_factor,
    discr_X_mul_comp_square_real (oddCenteredQuotient_monic n),
    oddCenteredQuotient_natDegree, oddCenteredQuotient_coeff_zero]
  have hs : ((-1 : ℝ)^n) * ((-1)^n) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsign (b : ℝ) : (-1)^n * ((-1)^n*b)^3 = b^3 := by
    calc _ = (((-1 : ℝ)^n) * ((-1)^n))^2 * b^3 := by ring
         _ = b^3 := by rw [hs, one_pow, one_mul]
  rw [hsign]

/-- Every centered Jensen discriminant is nonnegative, including repeated-root equations. -/
theorem monicCenteredJensen_discr_nonneg (d : ℕ) :
    0 ≤ (monicCenteredJensen d).discr := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n : ℕ, d = 2*n ∨ d = 2*n+1 := ⟨d/2, by omega⟩
  · rw [discr_even_monicCenteredJensen]
    exact mul_nonneg
      (mul_pos (pow_pos (by norm_num) _)
        (div_pos (centered_even_moment_pos n) (xiMoment_zero_pos _))).le (sq_nonneg _)
  · rw [discr_odd_monicCenteredJensen]
    have hb : 0 < (((2*n : ℕ)+1 : ℝ) * xiMoment (1/2) (2*n) / xiMoment (1/2) 0) :=
      div_pos (mul_pos (by positivity) (centered_even_moment_pos n)) (xiMoment_zero_pos _)
    exact mul_nonneg (mul_pos (pow_pos (by norm_num) _) (pow_pos hb 3)).le (sq_nonneg _)

/-- The unnormalized centered equations have the same nonnegative discriminant sign. -/
theorem xiJensenReal_discr_nonneg (d : ℕ) : 0 ≤ (xiJensenReal d).discr := by
  have h := monicCenteredJensen_discr_nonneg d
  have hc : (xiMoment (1/2) 0)⁻¹ ≠ 0 := inv_ne_zero (xiMoment_zero_pos _).ne'
  rw [monicCenteredJensen, mul_comm (xiJensenReal d), discr_C_mul_real hc] at h
  exact (mul_nonneg_iff_of_pos_left
    (pow_pos (inv_pos.mpr (xiMoment_zero_pos _)) _)).mp h

private theorem monicCenteredJensen_discr_zero_iff (d : ℕ) :
    (monicCenteredJensen d).discr = 0 ↔ (xiJensenReal d).discr = 0 := by
  have hc : (xiMoment (1/2) 0)⁻¹ ≠ 0 := inv_ne_zero (xiMoment_zero_pos _).ne'
  rw [monicCenteredJensen, mul_comm (xiJensenReal d), discr_C_mul_real hc,
    mul_eq_zero]
  simp only [pow_ne_zero _ hc, false_or]

/-- Only collisions in the quotient can make an even centered discriminant vanish. -/
theorem evenJensen_discr_zero_iff (n : ℕ) :
    (xiJensenReal (2*n)).discr = 0 ↔ ¬(evenCenteredQuotient n).Separable := by
  rw [← monicCenteredJensen_discr_zero_iff, discr_even_monicCenteredJensen]
  have ha : 4^n * (xiMoment (1/2) (2*n) / xiMoment (1/2) 0) ≠ (0 : ℝ) :=
    (mul_pos (pow_pos (by norm_num) _) (div_pos (centered_even_moment_pos n)
      (xiMoment_zero_pos _))).ne'
  rw [mul_eq_zero, or_iff_right ha, pow_eq_zero_iff (by decide : 2 ≠ 0)]
  exact GaloisForLFunctions.HTGeometry.monic_discr_eq_zero_iff_not_separable
    (evenCenteredQuotient_monic n)

/-- The forced zero in odd degree is simple; any discriminant zero comes from the quotient. -/
theorem oddJensen_discr_zero_iff (n : ℕ) :
    (xiJensenReal (2*n+1)).discr = 0 ↔ ¬(oddCenteredQuotient n).Separable := by
  rw [← monicCenteredJensen_discr_zero_iff, discr_odd_monicCenteredJensen]
  have hb : 0 < (((2*n : ℕ)+1 : ℝ) * xiMoment (1/2) (2*n) / xiMoment (1/2) 0) :=
    div_pos (mul_pos (by positivity) (centered_even_moment_pos n)) (xiMoment_zero_pos _)
  have ha : 4^n * (((2*n : ℕ)+1 : ℝ) * xiMoment (1/2) (2*n) / xiMoment (1/2) 0)^3
      ≠ (0 : ℝ) := (mul_pos (pow_pos (by norm_num) _) (pow_pos hb 3)).ne'
  rw [mul_eq_zero, or_iff_right ha, pow_eq_zero_iff (by decide : 2 ≠ 0)]
  exact GaloisForLFunctions.HTGeometry.monic_discr_eq_zero_iff_not_separable
    (oddCenteredQuotient_monic n)


end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.xiJensenReal_discr_nonneg
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.evenJensen_discr_zero_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.oddJensen_discr_zero_iff
