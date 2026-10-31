import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicSieveMassIsControlledByItsEulerCorrection

/-!
# Ramanujan approximation controlled by the logarithmic class moment

Retaining the weighted class moment in the spectral tail avoids replacing it
by the largest class in the support. Harmonic comparison preserves this moment
with a universal factor, removing one accuracy loss in conductor confinement.
-/

noncomputable section
open Finset
open scoped Classical InnerProductSpace
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry

private def prefixProfileVector (Q : Finset Nat.Primes) (A : ℕ)
    (f : SieveClass Q → ℝ) : SieveClassL2 Q :=
  sieveClassVector (fun a : sieveClassPrefix Q A => a.val)
    (fun a => Real.sqrt (sieveClassDensity Q a.val) * f a.val)

private theorem prefixProfileVector_apply (Q : Finset Nat.Primes) (A : ℕ)
    (f : SieveClass Q → ℝ) (a : SieveClass Q) :
    prefixProfileVector Q A f a =
      ((Real.sqrt (sieveClassDensity Q a) * (if (a : ℕ) ≤ A then f a else 0) : ℝ) : ℂ) := by
  by_cases ha : (a : ℕ) ≤ A
  · rw [if_pos ha]
    exact sieveClassVector_at (d := fun a : sieveClassPrefix Q A => a.val)
      Subtype.val_injective (fun a => Real.sqrt (sieveClassDensity Q a.val) * f a.val)
      (⟨a, (mem_sieveClassPrefix Q A a).mpr ha⟩ : sieveClassPrefix Q A)
  · rw [if_neg ha, mul_zero, Complex.ofReal_zero]
    rw [prefixProfileVector, sieveClassVector_apply]
    apply sum_eq_zero
    intro i _
    have hne : a ≠ (i : SieveClass Q) := by
      intro h
      exact ha ((mem_sieveClassPrefix Q A a).mp (h.symm ▸ i.property))
    rw [if_neg hne, mul_zero]

private def sieveConductorProjection (Q : Finset Nat.Primes) (R : ℕ)
    (x : SieveClassL2 Q) : SieveClassL2 Q :=
  ∑ m ∈ sieveClassPrefix Q R, (sieveAdjunctionBasis Q).repr x m • sieveAdjunctionBasis Q m

private theorem repr_sieveConductorProjection (Q : Finset Nat.Primes) (R : ℕ)
    (x : SieveClassL2 Q) (m : SieveClass Q) :
    (sieveAdjunctionBasis Q).repr (sieveConductorProjection Q R x) m =
      if (m : ℕ) ≤ R then (sieveAdjunctionBasis Q).repr x m else 0 := by
  have hij (i j : SieveClass Q) :
      inner ℂ (sieveAdjunctionBasis Q i) (sieveAdjunctionBasis Q j) =
        if i = j then (1 : ℂ) else 0 :=
    (orthonormal_iff_ite.mp (sieveAdjunctionBasis Q).orthonormal) i j
  rw [sieveConductorProjection, HilbertBasis.repr_apply_apply, inner_sum]
  simp only [inner_smul_right, hij, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [mem_sieveClassPrefix]

private theorem norm_sq_sub_sieveConductorProjection (Q : Finset Nat.Primes) (R : ℕ)
    (x : SieveClassL2 Q) :
    ‖x - sieveConductorProjection Q R x‖ ^ 2 =
      ∑' m : SieveClass Q, if (R : ℝ) < (m : ℕ) then
        ‖(sieveAdjunctionBasis Q).repr x m‖ ^ 2 else 0 := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num)
    ((sieveAdjunctionBasis Q).repr (x - sieveConductorProjection Q R x))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two,
    LinearIsometryEquiv.norm_map] at hs
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro m
  simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_sieveConductorProjection]
  by_cases hm : (m : ℕ) ≤ R
  · rw [if_pos hm, if_neg (by exact_mod_cast not_lt.mpr hm), sub_self, norm_zero, zero_pow (by decide)]
  · rw [if_neg hm, if_pos (by exact_mod_cast not_le.mp hm), sub_zero]

private theorem re_sub_sieveConductorProjection (Q : Finset Nat.Primes)
    (A R : ℕ) (f : SieveClass Q → ℝ) (a : SieveClass Q) :
    ((prefixProfileVector Q A f - sieveConductorProjection Q R (prefixProfileVector Q A f)) a).re =
      Real.sqrt (sieveClassDensity Q a) *
        ((if (a : ℕ) ≤ A then f a else 0) -
          ∑ m ∈ sieveClassPrefix Q R,
            ((sieveAdjunctionBasis Q).repr (prefixProfileVector Q A f) m).re *
              normalizedRamanujanMode m a) := by
  simp only [lp.coeFn_sub, Pi.sub_apply, Complex.sub_re, prefixProfileVector_apply,
    Complex.ofReal_re, sieveConductorProjection, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.re_sum,
    sieveAdjunctionBasis_eq_normalizedRamanujan, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [mul_sub, mul_sum]
  congr 1
  exact sum_congr rfl fun _ _ => by ring

/-- Conductor truncation costs the actual logarithmic class moment divided by `log R`. -/
theorem exists_sieveProfile_ramanujan_approximation_logMoment
    (Q : Finset Nat.Primes) {A R N : ℕ} (hR : 1 < R)
    (hA : A ^ 2 ≤ N + 1)
    (hN : 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4 ≤ Real.log (N + 1 : ℕ))
    (f : SieveClass Q → ℝ) :
    ∃ b : SieveClass Q → ℝ,
      (∑ a ∈ sieveClassPrefix Q N, sieveClassMass Q a N *
        ((if (a : ℕ) ≤ A then f a else 0) -
          ∑ m ∈ sieveClassPrefix Q R, b m * normalizedRamanujanMode m a) ^ 2) ≤
        (16 / Real.log R) *
          ∑ a ∈ sieveClassPrefix Q A,
            (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
              sieveClassMass Q a N * f a ^ 2 := by
  let x := prefixProfileVector Q A f
  let y := x - sieveConductorProjection Q R x
  let C : ℝ := 2 / Real.log R
  have hTR : (1 : ℝ) < R := by exact_mod_cast hR
  have hC : 0 ≤ C := div_nonneg zero_le_two (Real.log_pos hTR).le
  have hlogN : 0 ≤ Real.log (N + 1 : ℕ) := Real.log_natCast_nonneg _
  let b : SieveClass Q → ℝ := fun m => ((sieveAdjunctionBasis Q).repr x m).re
  refine ⟨b, ?_⟩
  have htail : ‖y‖ ^ 2 ≤ C *
      ∑ a ∈ sieveClassPrefix Q A,
        (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
          sieveClassDensity Q a * f a ^ 2 := by
    rw [norm_sq_sub_sieveConductorProjection]
    have h := tsum_sieveClassVector_conductorTail_le
      (Q := Q) (d := fun a : sieveClassPrefix Q A => a.val) Subtype.val_injective
      (fun a => Real.sqrt (sieveClassDensity Q a.val) * f a.val) hTR
    refine h.trans_eq ?_
    rw [← Finset.sum_coe_sort (s := sieveClassPrefix Q A)]
    dsimp only [C]
    rw [div_mul_eq_mul_div]
    apply congrArg (fun t : ℝ => 2 * t / Real.log R)
    refine sum_congr rfl fun a _ => ?_
    rw [mul_pow, Real.sq_sqrt (sieveClassDensity_pos a.val.property).le]
    ring
  have hpoint (a : SieveClass Q) :
      sieveClassDensity Q a *
        ((if (a : ℕ) ≤ A then f a else 0) -
          ∑ m ∈ sieveClassPrefix Q R, b m * normalizedRamanujanMode m a) ^ 2 ≤ ‖y a‖ ^ 2 := by
    calc
      _ = (Real.sqrt (sieveClassDensity Q a) *
          ((if (a : ℕ) ≤ A then f a else 0) -
            ∑ m ∈ sieveClassPrefix Q R, b m * normalizedRamanujanMode m a)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (sieveClassDensity_pos a.property).le]
      _ = (y a).re ^ 2 := congrArg (fun z : ℝ => z ^ 2)
        (re_sub_sieveConductorProjection Q A R f a).symm
      _ ≤ _ := by
        simpa only [pow_two, Complex.normSq_eq_norm_sq] using Complex.re_sq_le_normSq (y a)
  have hysum : HasSum (fun a : SieveClass Q => ‖y a‖ ^ 2) (‖y‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := 2) (by norm_num) y
  have hysmall : (∑ a ∈ sieveClassPrefix Q N, ‖y a‖ ^ 2) ≤ ‖y‖ ^ 2 := by
    have h := Summable.sum_le_tsum (sieveClassPrefix Q N) (fun a _ => sq_nonneg ‖y a‖)
      hysum.summable
    rwa [hysum.tsum_eq] at h
  have hupper (a : SieveClass Q) : sieveClassMass Q a N ≤
      4 * Real.log (N + 1 : ℕ) * sieveClassDensity Q a := by
    calc
      _ ≤ 2 * sieveClassDensity Q a *
          (Real.log (N + 1 : ℕ) + 2 * (sieveEuler Q - Real.eulerMascheroniConstant) + 4) :=
        sieveClassMass_le_density_log_euler a N
      _ ≤ 2 * sieveClassDensity Q a * (2 * Real.log (N + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hN])
          (mul_nonneg (by norm_num) (sieveClassDensity_pos a.property).le)
      _ = _ := by ring
  have hlower : (Real.log (N + 1 : ℕ) / 2) *
      (∑ a ∈ sieveClassPrefix Q A,
        (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
          sieveClassDensity Q a * f a ^ 2) ≤
        ∑ a ∈ sieveClassPrefix Q A,
          (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
            sieveClassMass Q a N * f a ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have haA : (a : ℕ) ≤ A := (mem_sieveClassPrefix Q A a).mp ha
    have haN : (a : ℕ) ^ 2 ≤ N + 1 := by
      calc
        _ = (a : ℕ) * (a : ℕ) := pow_two _
        _ ≤ A * A := Nat.mul_le_mul haA haA
        _ = A ^ 2 := (pow_two _).symm
        _ ≤ _ := hA
    have hw : 0 ≤ Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant) :=
      add_nonneg (Real.log_natCast_nonneg _) (sieveEuler_correction_nonneg Q)
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (sieveClassMass_comparable_to_density_log a haN hN).1 (sq_nonneg (f a))) hw
    nlinarith only [h]
  have hpaid : Real.log (N + 1 : ℕ) *
      (∑ a ∈ sieveClassPrefix Q A,
        (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
          sieveClassDensity Q a * f a ^ 2) ≤
        2 * ∑ a ∈ sieveClassPrefix Q A,
          (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
            sieveClassMass Q a N * f a ^ 2 := by
    linarith only [hlower]
  calc
    _ ≤ 4 * Real.log (N + 1 : ℕ) * ∑ a ∈ sieveClassPrefix Q N, ‖y a‖ ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun a _ => ?_
      calc
        _ ≤ (4 * Real.log (N + 1 : ℕ) * sieveClassDensity Q a) *
            ((if (a : ℕ) ≤ A then f a else 0) -
              ∑ m ∈ sieveClassPrefix Q R, b m * normalizedRamanujanMode m a) ^ 2 :=
          mul_le_mul_of_nonneg_right (hupper a) (sq_nonneg _)
        _ = (4 * Real.log (N + 1 : ℕ)) *
            (sieveClassDensity Q a *
              ((if (a : ℕ) ≤ A then f a else 0) -
                ∑ m ∈ sieveClassPrefix Q R, b m * normalizedRamanujanMode m a) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpoint a) (mul_nonneg (by norm_num) hlogN)
    _ ≤ 4 * Real.log (N + 1 : ℕ) * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hysmall (mul_nonneg (by norm_num) hlogN)
    _ ≤ 4 * Real.log (N + 1 : ℕ) *
        (C * ∑ a ∈ sieveClassPrefix Q A,
          (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
            sieveClassDensity Q a * f a ^ 2) :=
      mul_le_mul_of_nonneg_left htail (mul_nonneg (by norm_num) hlogN)
    _ = (4 * C) * (Real.log (N + 1 : ℕ) *
        ∑ a ∈ sieveClassPrefix Q A,
          (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
            sieveClassDensity Q a * f a ^ 2) := by ring
    _ ≤ (4 * C) * (2 * ∑ a ∈ sieveClassPrefix Q A,
          (Real.log (a : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
            sieveClassMass Q a N * f a ^ 2) :=
      mul_le_mul_of_nonneg_left hpaid (mul_nonneg (by norm_num) hC)
    _ = _ := by dsimp only [C]; ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.exists_sieveProfile_ramanujan_approximation_logMoment
