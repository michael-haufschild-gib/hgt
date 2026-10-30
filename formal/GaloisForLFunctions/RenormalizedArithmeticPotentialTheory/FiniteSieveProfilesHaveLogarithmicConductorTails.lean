import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveHorizonDefectIsTheAdjunctionOperator

/-!
# Logarithmic conductor tails of finite sieve profiles

The actual sieve operator controls its high-conductor coefficients by the
logarithmic size of the supported integers. Positivity on absolute values
pays the signed prime kernel without a conductor-modulus cost.
-/

noncomputable section
open Finset
open scoped Classical InnerProductSpace LinearPMap
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open ArithmeticIntersectionTheory ArithmeticElectrostatics ArithmeticEffectivityTheory HTGeometry

/-- The exact spectral energy above the common Euler ground level. -/
theorem hasSum_sieveConductorEnergy (Q : Finset Nat.Primes)
    (x : (sieveAdjunctionOperator Q).domain) :
    HasSum (fun m : SieveClass Q =>
      (Real.log (m : ℕ) + tameDifferent (m : ℕ)) *
        ‖(sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) m‖ ^ 2)
      ((inner ℂ (x : SieveClassL2 Q) (sieveAdjunctionOperator Q x)).re -
        Real.eulerMascheroniConstant * ‖(x : SieveClassL2 Q)‖ ^ 2) := by
  let R := (sieveAdjunctionBasis Q).repr
  let y := sieveAdjunctionOperator Q x -
    (Real.eulerMascheroniConstant : ℂ) • (x : SieveClassL2 Q)
  have hrepr (m : SieveClass Q) : R y m =
      ((Real.log (m : ℕ) + tameDifferent (m : ℕ) : ℝ) : ℂ) *
        R (x : SieveClassL2 Q) m := by
    dsimp only [y, R]
    simp only [map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [sieveAdjunctionOperator_spectral_action]
    simp only [matchedSieveEnergy, Complex.ofReal_add]
    ring
  have hterm (m : SieveClass Q) :
      (inner ℂ (R (x : SieveClassL2 Q) m) (R y m)).re =
        (Real.log (m : ℕ) + tameDifferent (m : ℕ)) *
          ‖R (x : SieveClassL2 Q) m‖ ^ 2 := by
    rw [hrepr]
    change (inner ℂ (R (x : SieveClassL2 Q) m)
      (((Real.log (m : ℕ) + tameDifferent (m : ℕ) : ℝ) : ℂ) •
        R (x : SieveClassL2 Q) m)).re = _
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hs := (lp.hasSum_inner (R (x : SieveClassL2 Q)) (R y)).mapL Complex.reCLM
  change HasSum (fun m => (inner ℂ (R (x : SieveClassL2 Q) m) (R y m)).re)
    (inner ℂ (R (x : SieveClassL2 Q)) (R y)).re at hs
  simp only [hterm] at hs
  rw [R.inner_map_map] at hs
  dsimp only [y] at hs
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at hs
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re] at hs
  exact hs

private theorem sieveExcitation_nonneg (m : SieveClass Q) :
    0 ≤ Real.log (m : ℕ) + tameDifferent (m : ℕ) :=
  add_nonneg (Real.log_natCast_nonneg _) (tameDifferent_nonneg _)

/-- The logarithmic conductor moment is summable on the original operator domain. -/
theorem summable_sieveConductor_logMoment (Q : Finset Nat.Primes)
    (x : (sieveAdjunctionOperator Q).domain) :
    Summable (fun m : SieveClass Q => Real.log (m : ℕ) *
      ‖(sieveAdjunctionBasis Q).repr (x : SieveClassL2 Q) m‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _))
    (fun m => mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (tameDifferent_nonneg _)) (sq_nonneg _))
  exact (hasSum_sieveConductorEnergy Q x).summable

private theorem norm_sieveClassVector_sq {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) :
    ‖sieveClassVector d b‖ ^ 2 = ∑ i, b i ^ 2 := by
  have hinner : inner ℂ (sieveClassVector d b) (sieveClassVector d b) =
      ((∑ i, b i ^ 2 : ℝ) : ℂ) := by
    change inner ℂ (∑ i, (b i : ℂ) • lp.single 2 (d i) (1 : ℂ))
      (sieveClassVector d b) = _
    rw [sum_inner]
    simp only [inner_smul_left, Complex.conj_ofReal, lp.inner_single_left,
      RCLike.inner_apply, map_one, mul_one, sieveClassVector_at hd]
    push_cast
    exact sum_congr rfl fun _ _ => by ring
  have h := congrArg Complex.re hinner
  rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_re] at h
  exact h

/-- The arithmetic eigenbasis resolves the exact finite class form above its Euler ground. -/
theorem hasSum_sieveClassVector_conductorEnergy {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) :
    HasSum (fun m : SieveClass Q =>
      (Real.log (m : ℕ) + tameDifferent (m : ℕ)) *
        ‖(sieveAdjunctionBasis Q).repr (sieveClassVector d b) m‖ ^ 2)
      ((∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2) -
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i : ℕ) (d j : ℕ)) := by
  have hs := hasSum_sieveConductorEnergy Q
    ⟨sieveClassVector d b, sieveClassVector_mem_domain d b⟩
  rw [inner_sieveClassVector_adjunction hd b, Complex.ofReal_re,
    norm_sieveClassVector_sq hd b] at hs
  have hdiag :
      (∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2) =
        (∑ i, (sieveEuler Q + Real.log (d i : ℕ)) * b i ^ 2) -
          Real.eulerMascheroniConstant * ∑ i, b i ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  convert hs using 1
  rw [hdiag]
  ring

private theorem sieveClassVector_excitation_nonneg {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) :
    0 ≤ (∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2) -
      ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i : ℕ) (d j : ℕ) := by
  rw [← (hasSum_sieveClassVector_conductorEnergy hd b).tsum_eq]
  exact tsum_nonneg fun m => mul_nonneg (sieveExcitation_nonneg m) (sq_nonneg _)

private theorem sieveClassVector_excitation_le {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) :
    (∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2) -
        (∑ i, ∑ j, b i * b j * weilPrimeKernel (d i : ℕ) (d j : ℕ)) ≤
      2 * ∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2 := by
  have habs := sieveClassVector_excitation_nonneg hd (fun i => |b i|)
  simp only [sq_abs] at habs
  have hprime : -(∑ i, ∑ j, b i * b j * weilPrimeKernel (d i : ℕ) (d j : ℕ)) ≤
      ∑ i, ∑ j, |b i| * |b j| * weilPrimeKernel (d i : ℕ) (d j : ℕ) := by
    calc
      _ = ∑ i, ∑ j, -(b i * b j) * weilPrimeKernel (d i : ℕ) (d j : ℕ) := by
        simp only [neg_mul, sum_neg_distrib]
      _ ≤ _ := sum_le_sum fun i _ => sum_le_sum fun j _ => by
        simpa only [abs_mul] using mul_le_mul_of_nonneg_right
          (neg_le_abs (b i * b j)) (weilPrimeKernel_nonneg _ _)
  linarith only [habs, hprime]

/-- Conductor energy is paid by logarithmic class size, independently of the sieve modulus. -/
theorem tsum_log_mul_sieveClassVector_repr_sq_le {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) :
    (∑' m : SieveClass Q, Real.log (m : ℕ) *
      ‖(sieveAdjunctionBasis Q).repr (sieveClassVector d b) m‖ ^ 2) ≤
        2 * ∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2 := by
  have hs := hasSum_sieveClassVector_conductorEnergy hd b
  have hlog := summable_sieveConductor_logMoment Q
    ⟨sieveClassVector d b, sieveClassVector_mem_domain d b⟩
  have hle := tsum_le_tsum
    (fun m : SieveClass Q => mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (tameDifferent_nonneg _))
      (sq_nonneg ‖(sieveAdjunctionBasis Q).repr (sieveClassVector d b) m‖))
    hlog hs.summable
  rw [hs.tsum_eq] at hle
  exact hle.trans (sieveClassVector_excitation_le hd b)

/-- The actual high-conductor spectral tail costs only the inverse logarithm of its cutoff. -/
theorem tsum_sieveClassVector_conductorTail_le {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) {R : ℝ} (hR : 1 < R) :
    (∑' m : SieveClass Q, if R < (m : ℕ) then
      ‖(sieveAdjunctionBasis Q).repr (sieveClassVector d b) m‖ ^ 2 else 0) ≤
        (2 * ∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) *
          b i ^ 2) / Real.log R := by
  let a : SieveClass Q → ℝ := fun m =>
    ‖(sieveAdjunctionBasis Q).repr (sieveClassVector d b) m‖ ^ 2
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hsum := (summable_sieveConductor_logMoment Q
    ⟨sieveClassVector d b, sieveClassVector_mem_domain d b⟩).div_const (Real.log R)
  have hdom (m : SieveClass Q) : (if R < (m : ℕ) then a m else 0) ≤
      Real.log (m : ℕ) * a m / Real.log R := by
    by_cases hm : R < (m : ℕ)
    · rw [if_pos hm]
      apply (le_div_iff₀ hlogR).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (Real.log_le_log (zero_lt_one.trans hR) hm.le) (sq_nonneg _)
    · rw [if_neg hm]
      exact div_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _)) hlogR.le
  have htail := Summable.of_nonneg_of_le
    (fun m => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl) hdom hsum
  calc
    _ ≤ ∑' m : SieveClass Q, Real.log (m : ℕ) * a m / Real.log R :=
      tsum_le_tsum hdom htail hsum
    _ = (∑' m : SieveClass Q, Real.log (m : ℕ) * a m) / Real.log R := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right (tsum_log_mul_sieveClassVector_repr_sq_le hd b) hlogR.le

/-- Bounded class support gives an explicit conductor-tail estimate. -/
theorem tsum_sieveClassVector_conductorTail_le_of_support {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) {A R : ℝ}
    (hdA : ∀ i, ((d i : ℕ) : ℝ) ≤ A) (hR : 1 < R) :
    (∑' m : SieveClass Q, if R < (m : ℕ) then
      ‖(sieveAdjunctionBasis Q).repr (sieveClassVector d b) m‖ ^ 2 else 0) ≤
        (2 * (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) / Real.log R) *
          ∑ i, b i ^ 2 := by
  have hdiag : (∑ i, (Real.log (d i : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * b i ^ 2) ≤
      (Real.log A + (sieveEuler Q - Real.eulerMascheroniConstant)) * ∑ i, b i ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (add_le_add_right (Real.log_le_log (by exact_mod_cast (d i).property.pos) (hdA i)) _)
      (sq_nonneg _)
  have h := (tsum_sieveClassVector_conductorTail_le hd b hR).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiag (by norm_num))
      (Real.log_pos hR).le)
  convert h using 1 <;> ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.hasSum_sieveConductorEnergy
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tsum_log_mul_sieveClassVector_repr_sq_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tsum_sieveClassVector_conductorTail_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tsum_sieveClassVector_conductorTail_le_of_support

