import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitRadicalReciprocity
import GaloisForLFunctions.RHTower.Artin.InvariantDivisorsDescendOutsideALargeSetOfPrimes

/-! A power class whose divisor is divisible by the exponent outside a
set representing the ideal classes has a representative in the S-units. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions

namespace GlobalTheory.Kummer

variable {K : Type} [Field K] [NumberField K]

attribute [local instance] primeMulAction

/-- A divisor with prescribed exponents at finitely many primes outside S
is the divisor of a scalar outside S when those primes are principal up to S. -/
private theorem exists_with_ordAt_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K))))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w ∈ T, w ∉ S)
    (b : HeightOneSpectrum (𝓞 K) → ℤ) (hb : ∀ w, w ∉ S → w ∉ T → b w = 0) :
    ∃ c : Additive Kˣ, ∀ w, w ∉ S → ordAt K w c = b w := by
  classical
  let d (w : HeightOneSpectrum (𝓞 K)) : Additive Kˣ :=
    if h : w ∉ S then (hS w h).choose else 0
  refine ⟨∑ w ∈ T, b w • d w, fun v hv => ?_⟩
  rw [map_sum]
  have hterm (w) (hw : w ∈ T) :
      ordAt K v (b w • d w) = if w = v then b w else 0 := by
    have ed : d w = (hS w (hT w hw)).choose := dif_pos (hT w hw)
    rw [map_zsmul, ed]
    split_ifs with h
    · subst w
      rw [(hS v (hT v hw)).choose_spec.1, smul_eq_mul, mul_one]
    · rw [(hS w (hT w hw)).choose_spec.2 v hv (Ne.symm h), smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T v b]
  split_ifs with h
  · rfl
  · exact (hb v hv h).symm

theorem mem_sUnitRadicalClasses_of_dvd_ordAt
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K))))
    {n : ℕ} (a : Kˣ)
    (ha : ∀ w ∉ S, (n : ℤ) ∣ ordAt K w (Additive.ofMul a)) :
    (a : PowerClasses K n) ∈ sUnitRadicalClasses K Gal(K/K) (sUnitPrimeSet K S) n := by
  classical
  let T := (finite_ordAt_ne_zero K a).toFinset.filter (fun w => w ∉ S)
  let b (w : HeightOneSpectrum (𝓞 K)) := ordAt K w (Additive.ofMul a) / (n : ℤ)
  have hT (w) (hw : w ∈ T) : w ∉ S := (Finset.mem_filter.mp hw).2
  have hb (w) (hw : w ∉ S) (hwT : w ∉ T) : b w = 0 := by
    have hz : ordAt K w (Additive.ofMul a) = 0 := by
      by_contra h
      exact hwT (Finset.mem_filter.mpr ⟨(finite_ordAt_ne_zero K a).mem_toFinset.mpr h, hw⟩)
    simp only [b, hz, Int.zero_ediv]
  obtain ⟨c, hc⟩ := exists_with_ordAt_outside S hS T hT b hb
  let u := Additive.ofMul a - n • c
  have hu : u ∈ sUnits K Gal(K/K) (sUnitPrimeSet K S) := by
    intro w hw
    change w ∉ S at hw
    change ordAt K w (Additive.ofMul a - n • c) = 0
    rw [map_sub, map_nsmul, hc w hw, nsmul_eq_mul]
    change ordAt K w (Additive.ofMul a) - (n : ℤ) * (ordAt K w (Additive.ofMul a) / (n : ℤ)) = 0
    rw [mul_comm (n : ℤ), Int.ediv_mul_cancel (ha w hw), sub_self]
  refine ⟨Multiplicative.ofAdd ⟨u, hu⟩, ?_⟩
  change ((Additive.toMul u : Kˣ) : PowerClasses K n) = (a : PowerClasses K n)
  apply QuotientGroup.eq.mpr
  refine ⟨Additive.toMul c, ?_⟩
  change (Additive.toMul c) ^ n = (a / (Additive.toMul c) ^ n)⁻¹ * a
  rw [inv_div, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]

end GlobalTheory.Kummer

#print axioms GlobalTheory.Kummer.mem_sUnitRadicalClasses_of_dvd_ordAt
