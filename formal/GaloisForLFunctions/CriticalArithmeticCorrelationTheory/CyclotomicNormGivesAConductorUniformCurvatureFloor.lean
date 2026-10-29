import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimitiveRootPrefixEnergyIsAMobiusQuadraticRemainder
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheArchimedeanIntersectionIsALogOrder
import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation

/-!
# A conductor-uniform floor from the cyclotomic norm

A nonvanishing geometric prefix is an actual cyclotomic integer. Its norm
forces the product of all primitive-root magnitudes to be at least one.
The arithmetic–geometric mean then bounds the square energy below by the
totient. Interpolation transfers this arithmetic quantum to real overlap.
-/

noncomputable section

open Finset Polynomial NumberField

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticIntersectionTheory

private theorem card_le_sum_of_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) (hp : 1 ≤ ∏ i ∈ s, f i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
  have hl : 0 ≤ ∑ i ∈ s, Real.log (f i) := by
    rw [← Real.log_prod (fun i hi => (hf i hi).ne')]
    exact Real.log_nonneg hp
  have hb := sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (hf i hi))
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one] at hb
  linarith only [hl, hb]

private theorem primitive_prefix_ne_zero {m k : ℕ} (hkm : ¬ m ∣ k)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) : (∑ j ∈ range k, ζ ^ j) ≠ 0 := by
  intro hz
  have h := geom_sum_mul ζ k
  rw [hz, zero_mul] at h
  exact hkm (hζ.dvd_of_pow_eq_one k (sub_eq_zero.mp h.symm))

/-- The product is the magnitude of the norm of a nonzero cyclotomic integer,
including every primitive embedding exactly once. -/
theorem one_le_prod_primitive_prefix_norm {m k : ℕ} (hm : 1 < m) (hkm : ¬ m ∣ k) :
    1 ≤ ∏ ζ ∈ primitiveRoots m ℂ, ‖∑ j ∈ range k, ζ ^ j‖ := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  letI : NeZero m := ⟨hm0.ne'⟩
  let K := CyclotomicField m ℚ
  letI : IsCyclotomicExtension {m} ℚ K := CyclotomicField.isCyclotomicExtension m ℚ
  let β : 𝓞 K := ∑ j ∈ range k, (zetaN_spec m).toInteger ^ j
  have hcoe : (β : K) = ∑ j ∈ range k, zetaN m ^ j := by
    change (algebraMap (𝓞 K) K) β = _
    simp only [β, map_sum, map_pow]
    rfl
  have hβ : β ≠ 0 := by
    intro hz
    have hzero := congrArg (fun z : 𝓞 K => (z : K)) hz
    rw [hcoe] at hzero
    have h := geom_sum_mul (zetaN m) k
    rw [hzero, zero_mul] at h
    exact hkm ((zetaN_spec m).dvd_of_pow_eq_one k (sub_eq_zero.mp h.symm))
  have hp := HTGeometry.one_le_prod_norm_embeddings β hβ
  have hemb (σ : K →ₐ[ℚ] ℂ) :
      σ (β : K) = ∑ j ∈ range k, σ (zetaN m) ^ j := by
    rw [hcoe]
    simp only [map_sum, map_pow]
  have he : (∏ σ : K →+* ℂ, ‖σ (β : K)‖) =
      ∏ ζ ∈ primitiveRoots m ℂ, ‖∑ j ∈ range k, ζ ^ j‖ := by
    calc
      _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ (β : K)‖ :=
        Fintype.prod_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)
      _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖∑ j ∈ range k, σ (zetaN m) ^ j‖ := by
        exact prod_congr rfl fun σ _ => congrArg norm (hemb σ)
      _ = _ := by
        rw [← prod_coe_sort (primitiveRoots m ℂ)]
        exact Fintype.prod_equiv
          ((zetaN_spec m).embeddingsEquivPrimitiveRoots ℂ (cyclotomic.irreducible_rat hm0))
          _ _ (fun σ => by rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe])
  rwa [he] at hp

/-- Every nonvanishing primitive prefix has mean square at least one,
uniformly in its conductor and length. -/
theorem totient_le_primitiveRootPrefixEnergy {m k : ℕ} (hm : 1 < m) (hkm : ¬ m ∣ k) :
    (m.totient : ℝ) ≤ primitiveRootPrefixEnergy m k := by
  have hm0 : 0 < m := zero_lt_one.trans hm
  have hp := one_le_prod_primitive_prefix_norm hm hkm
  have hp2 : 1 ≤ ∏ ζ ∈ primitiveRoots m ℂ,
      Complex.normSq (∑ j ∈ range k, ζ ^ j) := by
    simp_rw [← Complex.sq_norm]
    rw [← prod_pow]
    nlinarith only [hp]
  have hb := card_le_sum_of_one_le_prod (primitiveRoots m ℂ)
    (fun ζ => Complex.normSq (∑ j ∈ range k, ζ ^ j))
    (fun ζ hζ => Complex.normSq_pos.mpr
      (primitive_prefix_ne_zero hkm ((mem_primitiveRoots hm0).mp hζ))) hp2
  have hcard : (primitiveRoots m ℂ).card = m.totient :=
    (Complex.isPrimitiveRoot_exp m hm0.ne').card_primitiveRoots
  simpa only [hcard, primitiveRootPrefixEnergy] using hb

/-- The totient-normalized arithmetic curvature dominates the conductor-one
quadratic on every cell, with one bound for all conductors. -/
theorem totient_mul_cell_quadratic_le_curvature {m : ℕ} (hm : 1 < m) (k : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (m.totient : ℝ) * (u * (1 - u)) ≤ arithmeticOverlapCurvature m ((k : ℝ) + u) := by
  rw [arithmeticOverlapCurvature_eq_interpolation hm k hu0 hu1]
  have hφ : (0 : ℝ) ≤ m.totient := Nat.cast_nonneg _
  by_cases hkm : m ∣ k
  · have hnext : ¬ m ∣ k + 1 := by
      intro h
      have hm1 : m ∣ 1 := (Nat.dvd_add_iff_right hkm).mp h
      exact (by omega : m ≠ 1) (Nat.dvd_one.mp hm1)
    have hE := totient_le_primitiveRootPrefixEnergy hm hnext
    have hmul := mul_le_mul_of_nonneg_left hE hu0
    have hn := mul_nonneg (sub_nonneg.mpr hu1.le) (primitiveRootPrefixEnergy_nonneg m k)
    have hsq := mul_nonneg hφ (sq_nonneg u)
    nlinarith only [hmul, hn, hsq]
  · have hE := totient_le_primitiveRootPrefixEnergy hm hkm
    have hmul := mul_le_mul_of_nonneg_left hE (sub_nonneg.mpr hu1.le)
    have hn := mul_nonneg hu0 (primitiveRootPrefixEnergy_nonneg m (k + 1))
    have hsq := mul_nonneg hφ (sq_nonneg (1 - u))
    nlinarith only [hmul, hn, hsq]

/-- The conductor-normalized curvature has a uniform nonnegative floor on
the full nonnegative real axis. -/
theorem fract_quadratic_le_normalized_arithmeticOverlapCurvature {m : ℕ} (hm : 1 < m)
    {t : ℝ} (ht : 0 ≤ t) :
    Int.fract t * (1 - Int.fract t) ≤ arithmeticOverlapCurvature m t / m.totient := by
  let k : ℕ := ⌊t⌋₊
  let u : ℝ := t - k
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Nat.floor_le ht)
  have hu1 : u < 1 := by
    have h := Nat.lt_floor_add_one t
    dsimp only [u, k]
    linarith only [h]
  have he : t = (k : ℝ) + u := by dsimp only [u]; ring
  have hf : Int.fract t = u := by
    rw [he, add_comm, Int.fract_add_natCast]
    exact Int.fract_eq_self.mpr ⟨hu0, hu1⟩
  have hφ : (0 : ℝ) < m.totient := by
    exact_mod_cast Nat.totient_pos.mpr (zero_lt_one.trans hm)
  rw [le_div_iff₀ hφ, hf, he, mul_comm]
  exact totient_mul_cell_quadratic_le_curvature hm k hu0 hu1

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.one_le_prod_primitive_prefix_norm
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.totient_le_primitiveRootPrefixEnergy
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.fract_quadratic_le_normalized_arithmeticOverlapCurvature
