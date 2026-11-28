import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.DivisibleDivisorPowerClasses
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitLocalPowers
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteDegreeOneFrobenius

/-! Divisor divisibility outside a set representing the ideal classes
leaves finitely many power classes. Finitely many further completions
detect the nontrivial classes by arithmetic Frobenius. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Kummer

variable {K : Type} [Field K] [NumberField K]
variable {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

attribute [local instance] primeMulAction

private theorem exists_nonpower_place_of_sUnit
    (S T : Finset (HeightOneSpectrum (𝓞 K))) {a : Kˣ}
    (ha : Additive.ofMul a ∈ sUnits K Gal(K/K) (sUnitPrimeSet K S))
    (ha' : ¬ ∃ x : K, x ^ n = a) :
    ∃ v ∉ T, ¬ ∃ x : v.adicCompletion K, x ^ n = algebraMap K _ (a : K) := by
  classical
  obtain ⟨M, hfin, hab, α, hα⟩ := exists_finite_abelian_extension_with_sUnit_root (n := n) S ha
  let E := K⟮α⟯
  let e := AdjoinSimple.gen K α
  have he : e ^ n = algebraMap K E (a : K) := Subtype.ext hα
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  letI : NumberField E := NumberField.of_module_finite K E
  letI : Fintype Gal(E/K) := Fintype.ofFinite _
  letI : CommGroup Gal(E/K) :=
    { (inferInstance : Group Gal(E/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  have hnot : ¬ ∀ σ : Gal(E/K), σ e = e := by
    intro h
    obtain ⟨z, hz⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) e).mpr h
    exact ha' ⟨z, (algebraMap K E).injective (by rw [map_pow, hz, he])⟩
  obtain ⟨σ, hσ⟩ := not_forall.mp hnot
  let B : Set (HeightOneSpectrum (𝓞 K)) := {v | ¬ IsUnramifiedPrime K E Gal(E/K) v}
  have hB : B.Finite := finite_not_isUnramifiedPrime (K := K) (L := E) (G := Gal(E/K))
  obtain ⟨v, hv, -, P, hP, hPv, hF⟩ := GlobalTheory.DegreeOneFrobenius.exists_arithmeticFrobenius_away
    K E σ ((T : Set (HeightOneSpectrum (𝓞 K))) ∪ B) (T.finite_toSet.union hB)
  have hur : IsUnramifiedPrime K E Gal(E/K) v := not_not.mp (fun h => hv (Or.inr h))
  refine ⟨v, fun h => hv (Or.inl h), ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨j⟩ := nonempty_simpleAlgHom_of_local_power (K := K) hα hx
  have hs := (isUnramifiedPrime_and_frobenius_eq_one_of_completion_embedding
    (K := K) (L := E) Gal(E/K) v j).2
  letI := hP
  letI := hPv
  have hmem := (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(E/K) P).mul_inv_mem_inertia hF
  rw [hur P hP hPv, Subgroup.mem_bot, arithFrobAt_eq_frobeniusElement hur P,
    hs, one_mul, inv_eq_one] at hmem
  exact hσ (congrArg (fun τ : Gal(E/K) => τ e) hmem)

/-- For global elements with n-divisible divisor away from S, a finite
set of completions disjoint from any prescribed set detects n-th powers. -/
theorem exists_finite_power_detection_primes
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : PrincipalOutside K (S : Set (HeightOneSpectrum (𝓞 K)))) :
    ∃ D : Finset (HeightOneSpectrum (𝓞 K)), Disjoint D T ∧
      ∀ a : Kˣ, (∀ v ∉ S, (n : ℤ) ∣ ordAt K v (Additive.ofMul a)) →
        (∀ v ∈ D, ∃ x : v.adicCompletion K, x ^ n = algebraMap K _ (a : K)) →
        ∃ b : Kˣ, b ^ n = a := by
  classical
  let C := sUnitRadicalClasses K Gal(K/K) (sUnitPrimeSet K S) n
  let C' := {δ : C // δ.val ≠ 1}
  letI : Fintype C' := Fintype.ofFinite _
  have hrep (δ : C') : ∃ a : Kˣ,
      Additive.ofMul a ∈ sUnits K Gal(K/K) (sUnitPrimeSet K S) ∧
      (a : PowerClasses K n) = δ.val.val := by
    obtain ⟨u, hu⟩ := δ.val.property
    exact ⟨Additive.toMul (Multiplicative.toAdd u).val, (Multiplicative.toAdd u).property, hu⟩
  choose a ha haC using hrep
  have hn (δ : C') : ¬ ∃ x : K, x ^ n = a δ := by
    rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h
      exact (a δ).ne_zero (by rw [← hx, h, zero_pow (NeZero.ne n)])
    apply δ.property
    rw [← haC δ]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.mk0 x hx0, Units.ext hx⟩
  choose v hv hvpow using fun δ : C' => exists_nonpower_place_of_sUnit S T (ha δ) (hn δ)
  let D := Finset.univ.image v
  refine ⟨D, Finset.disjoint_left.mpr ?_, fun x hx hloc => ?_⟩
  · intro w hw
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hw
    exact hv δ
  have hxC : (x : PowerClasses K n) ∈ C := mem_sUnitRadicalClasses_of_dvd_ordAt S hS x hx
  change x ∈ (powMonoidHom n : Kˣ →* Kˣ).range
  apply (QuotientGroup.eq_one_iff x).mp
  by_contra h
  let δ : C' := ⟨⟨x, hxC⟩, h⟩
  have he : (a δ : PowerClasses K n) = (x : PowerClasses K n) := haC δ
  obtain ⟨u, hu⟩ := QuotientGroup.eq.mp he
  change u ^ n = (a δ)⁻¹ * x at hu
  have he' : a δ = x / u ^ n := by
    rw [hu, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, inv_inv]
  obtain ⟨y, hy⟩ := hloc (v δ) (Finset.mem_image.mpr ⟨δ, Finset.mem_univ _, rfl⟩)
  apply hvpow δ
  refine ⟨y / algebraMap K _ (u : K), ?_⟩
  rw [div_pow, hy, he', Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, map_div₀, map_pow]

end GlobalTheory.Kummer

#print axioms GlobalTheory.Kummer.exists_finite_power_detection_primes
