import GaloisForLFunctions.EffectiveScalingGeometry.PrimeWeightedContraction
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeIntegralCoefficients
import Mathlib.CategoryTheory.Whiskering

/-!
# A height-preserving two-prime chain normal form

Over every commutative ring, the arithmetic prime-weighted complex is naturally
isomorphic to the complex whose boundary functional is supported at two and
three, with values two and three. Let `t` contract the remaining prime weights
and let `h` adjoin `e₃−e₂`. Cartan's identity makes `ht` square-zero, so
`1−ht` and `1+ht` are inverse chain gauges. A tail deletion pays for the cone,
hence both maps preserve every prime-product cutoff. The isomorphism commutes
with height inclusions and canonical integral coefficient extension.
-/

noncomputable section
open CategoryTheory RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

section Contractions
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Koszul contraction is additive in its vertex functional. -/
theorem koszulDifferential_add (k : ℕ) (φ ψ : V →ₗ[R] R) :
    physicalKoszulDifferential k (φ + ψ) =
      physicalKoszulDifferential k φ + physicalKoszulDifferential k ψ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, physicalKoszulDifferential_ιMulti,
    LinearMap.add_apply, add_smul, smul_add, Finset.sum_add_distrib]

/-- Subtracting vertex weights subtracts the corresponding contraction. -/
theorem koszulDifferential_sub (k : ℕ) (φ ψ : V →ₗ[R] R) :
    physicalKoszulDifferential k (φ - ψ) =
      physicalKoszulDifferential k φ - physicalKoszulDifferential k ψ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, physicalKoszulDifferential_ιMulti,
    LinearMap.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (congrArg (fun z : ⋀[R]^k V => ((-1 : ℤ) ^ (i : ℕ)) • z)
    (sub_smul (φ (v i)) (ψ (v i)) _)).trans (smul_sub _ _ _)

/-- Polarizing the square-zero identity shows that any two contractions anticommute. -/
theorem koszulDifferential_anticommute (k : ℕ) (φ ψ : V →ₗ[R] R) :
    (physicalKoszulDifferential k φ).comp (physicalKoszulDifferential (k+1) ψ) +
      (physicalKoszulDifferential k ψ).comp (physicalKoszulDifferential (k+1) φ) = 0 := by
  have h := physicalKoszulDifferential_sq k (φ + ψ)
  rw [koszulDifferential_add, koszulDifferential_add,
    LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add,
    physicalKoszulDifferential_sq, physicalKoszulDifferential_sq,
    zero_add, add_zero] at h
  exact h
end Contractions

/-- The large-prime part of the arithmetic vertex functional. -/
def primeTailFunctional : (Nat.Primes →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun p : Nat.Primes => if p.val ≤ 3 then 0 else (p.val : R))

theorem primeTailFunctional_single (p : Nat.Primes) :
    primeTailFunctional R (Finsupp.single p 1) = if p.val ≤ 3 then 0 else (p.val : R) := by
  simp only [primeTailFunctional, Finsupp.linearCombination_single, one_smul]

abbrev primeTailBoundary (k : ℕ) := physicalKoszulDifferential k (primeTailFunctional R)

/-- The functional supported at the two smallest primes. -/
def primeTwoPrimeFunctional := primeValueFunctional R - primeTailFunctional R

theorem primeTwoPrimeFunctional_single (p : Nat.Primes) :
    primeTwoPrimeFunctional R (Finsupp.single p 1) =
      if p.val = 2 ∨ p.val = 3 then (p.val : R) else 0 := by
  have hp := p.property.two_le
  simp only [primeTwoPrimeFunctional, LinearMap.sub_apply,
    primeValueFunctional_single, primeTailFunctional_single]
  by_cases h : p.val ≤ 3
  · rw [if_pos h, if_pos (by omega), sub_zero]
  · rw [if_neg h, if_neg (by omega), sub_self]

/-- Tail contraction anticommutes with the arithmetic Bézout cone. -/
theorem primeTailBoundary_cartan (k : ℕ) :
    (primeTailBoundary R (k+1)).comp (primeBezoutCone R (k+1)) +
      (primeBezoutCone R k).comp (primeTailBoundary R k) = 0 := by
  have h3 := koszul_cartan_succ k (primeTailFunctional R)
    (Finsupp.single ⟨3,Nat.prime_three⟩ (1 : R))
  have h2 := koszul_cartan_succ k (primeTailFunctional R)
    (Finsupp.single ⟨2,Nat.prime_two⟩ (1 : R))
  simp only [primeTailFunctional_single, show (3 : ℕ) ≤ 3 from le_rfl,
    show (2 : ℕ) ≤ 3 from by omega, if_true, zero_smul] at h3 h2
  apply LinearMap.ext
  intro x
  have h3x := LinearMap.congr_fun h3 x
  have h2x := LinearMap.congr_fun h2 x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h3x h2x
  change primeTailBoundary R (k+1)
      (primeChainCone R (k+1) ⟨3,Nat.prime_three⟩ x - primeChainCone R (k+1) ⟨2,Nat.prime_two⟩ x) +
    (primeChainCone R k ⟨3,Nat.prime_three⟩ (primeTailBoundary R k x) -
      primeChainCone R k ⟨2,Nat.prime_two⟩ (primeTailBoundary R k x)) = 0
  rw [map_sub]
  calc
    _ = (primeTailBoundary R (k+1) (primeChainCone R (k+1) ⟨3,Nat.prime_three⟩ x) +
        primeChainCone R k ⟨3,Nat.prime_three⟩ (primeTailBoundary R k x)) -
      (primeTailBoundary R (k+1) (primeChainCone R (k+1) ⟨2,Nat.prime_two⟩ x) +
        primeChainCone R k ⟨2,Nat.prime_two⟩ (primeTailBoundary R k x)) := by abel
    _ = 0 := by rw [h3x,h2x,sub_self]

theorem primeTailBoundary_cartan_zero :
    (primeTailBoundary R 0).comp (primeBezoutCone R 0) = 0 := by
  have h3 := koszul_cartan_zero_map (primeTailFunctional R)
    (Finsupp.single ⟨3,Nat.prime_three⟩ (1 : R))
  have h2 := koszul_cartan_zero_map (primeTailFunctional R)
    (Finsupp.single ⟨2,Nat.prime_two⟩ (1 : R))
  simp only [primeTailFunctional_single, show (3 : ℕ) ≤ 3 from le_rfl,
    show (2 : ℕ) ≤ 3 from by omega, if_true, zero_smul] at h3 h2
  change (primeTailBoundary R 0).comp
    (primeChainCone R 0 ⟨3,Nat.prime_three⟩ - primeChainCone R 0 ⟨2,Nat.prime_two⟩) = 0
  rw [LinearMap.comp_sub, h3, h2]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.zero_apply, sub_self]

/-- Nonzero tail deletions more than pay for adjoining either small prime. -/
theorem primeTailBoundary_third_cutoff (k N : ℕ) :
    primeChainCutoff R (k+1) N ≤
      (primeChainCutoff R k (N/3)).comap (primeTailBoundary R k) := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  change primeTailBoundary R k (primeChainAtom R v) ∈ primeChainCutoff R k (N/3)
  rw [primeChainAtom, physicalKoszulDifferential_ιMulti]
  apply Submodule.sum_mem
  intro i _
  rw [primeTailFunctional_single]
  by_cases hi : (v i).val ≤ 3
  · rw [if_pos hi, zero_smul, smul_zero]
    exact Submodule.zero_mem _
  · rw [if_neg hi]
    apply (primeChainCutoff R k (N/3)).toAddSubgroup.zsmul_mem
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨fun j => v (i.succAbove j), ?_, rfl⟩
    have hh : 3 * ∏ j, (v (i.succAbove j) : ℕ) ≤ N := calc
      _ ≤ (v i : ℕ) * ∏ j, (v (i.succAbove j) : ℕ) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = ∏ j, (v j : ℕ) := (Fin.prod_univ_succAbove (fun j => (v j : ℕ)) i).symm
      _ ≤ N := hv
    change (∏ j, (v (i.succAbove j) : ℕ)) ≤ N/3
    omega

/-- The square-zero correction which removes all large-prime boundary weights. -/
def primeTailShear : (k : ℕ) → PrimeChainSpace R k →ₗ[R] PrimeChainSpace R k
  | 0 => 0
  | k+1 => (primeBezoutCone R k).comp (primeTailBoundary R k)

/-- Tail contraction kills the correction because its own square is zero. -/
theorem primeTailBoundary_shear (k : ℕ) :
    (primeTailBoundary R k).comp (primeTailShear R (k+1)) = 0 := by
  apply LinearMap.ext
  intro x
  cases k with
  | zero =>
    exact LinearMap.congr_fun (primeTailBoundary_cartan_zero R)
      (primeTailBoundary R 0 x)
  | succ k =>
    have h := LinearMap.congr_fun (primeTailBoundary_cartan R k)
      (primeTailBoundary R (k+1) x)
    have hz : primeTailBoundary R k (primeTailBoundary R (k+1) x) = 0 :=
      LinearMap.congr_fun (physicalKoszulDifferential_sq k (primeTailFunctional R)) x
    simpa only [primeTailShear, LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero,
      add_zero, LinearMap.zero_apply] using h

/-- The correction is nilpotent of order two in every augmented degree. -/
theorem primeTailShear_sq (k : ℕ) :
    (primeTailShear R k).comp (primeTailShear R k) = 0 := by
  cases k with
  | zero => simp only [primeTailShear, LinearMap.zero_comp]
  | succ k =>
    change ((primeBezoutCone R k).comp (primeTailBoundary R k)).comp
      (primeTailShear R (k+1)) = 0
    rw [LinearMap.comp_assoc, primeTailBoundary_shear, LinearMap.comp_zero]

theorem primeTailShear_cutoff (k N : ℕ) :
    primeChainCutoff R k N ≤ (primeChainCutoff R k N).comap (primeTailShear R k) := by
  intro x hx
  cases k with
  | zero =>
    change (0 : PrimeChainSpace R 0) ∈ primeChainCutoff R 0 N
    exact Submodule.zero_mem _
  | succ k =>
    exact primeChainCutoff_mono R (k+1) (show 3*(N/3) ≤ N by omega)
      (primeBezoutCone_cutoff R k (N/3) (primeTailBoundary_third_cutoff R k N hx))

#print axioms primeTailShear_sq
#print axioms primeTailShear_cutoff

/-- Forward shear from the two-prime complex to the prime-valued complex. -/
def primeTwoPrimeGauge (k : ℕ) : PrimeChainSpace R k →ₗ[R] PrimeChainSpace R k :=
  LinearMap.id - primeTailShear R k

/-- Adding the same square-zero correction gives the inverse gauge. -/
def primeTwoPrimeGaugeInv (k : ℕ) : PrimeChainSpace R k →ₗ[R] PrimeChainSpace R k :=
  LinearMap.id + primeTailShear R k

theorem primeTwoPrimeGauge_inverse (k : ℕ) :
    (primeTwoPrimeGauge R k).comp (primeTwoPrimeGaugeInv R k) = LinearMap.id ∧
    (primeTwoPrimeGaugeInv R k).comp (primeTwoPrimeGauge R k) = LinearMap.id := by
  constructor <;> apply LinearMap.ext <;> intro x
  all_goals
    have hz := LinearMap.congr_fun (primeTailShear_sq R k) x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    simp only [primeTwoPrimeGauge, primeTwoPrimeGaugeInv, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_add, map_sub, hz]
    abel

/-- The commutator of the arithmetic boundary with the correction is tail deletion. -/
theorem primeValueBoundary_tailShear (k : ℕ) (x : PrimeChainSpace R (k+1)) :
    primeValueBoundary R k (primeTailShear R (k+1) x) =
      primeTailBoundary R k x + primeTailShear R k (primeValueBoundary R k x) := by
  cases k with
  | zero =>
    have h := LinearMap.congr_fun (primeBezoutCone_contracts_zero R)
      (primeTailBoundary R 0 x)
    simpa only [primeTailShear, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.zero_apply, add_zero] using h
  | succ k =>
    have h := LinearMap.congr_fun (primeBezoutCone_contracts R k)
      (primeTailBoundary R (k+1) x)
    have ha := LinearMap.congr_fun
      (koszulDifferential_anticommute R k (primeValueFunctional R) (primeTailFunctional R)) x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at ha
    have he : primeValueBoundary R k (primeTailBoundary R (k+1) x) =
        -primeTailBoundary R k (primeValueBoundary R (k+1) x) :=
      eq_neg_of_add_eq_zero_left ha
    change primeValueBoundary R (k+1)
      (primeBezoutCone R (k+1) (primeTailBoundary R (k+1) x)) =
      primeTailBoundary R (k+1) x +
      primeBezoutCone R k (primeTailBoundary R k (primeValueBoundary R (k+1) x))
    rw [he, map_neg] at h
    exact (eq_sub_of_add_eq h).trans (sub_neg_eq_add _ _)

/-- The shear conjugates the actual differential to the one supported at two and three. -/
theorem primeTwoPrimeGauge_boundary (k : ℕ) :
    (primeValueBoundary R k).comp (primeTwoPrimeGauge R (k+1)) =
      (primeTwoPrimeGauge R k).comp
        (physicalKoszulDifferential k (primeTwoPrimeFunctional R)) := by
  apply LinearMap.ext
  intro x
  have hz : primeTailShear R k (primeTailBoundary R k x) = 0 := by
    cases k with
    | zero => rfl
    | succ k =>
      have hs := LinearMap.congr_fun (physicalKoszulDifferential_sq k (primeTailFunctional R)) x
      change primeBezoutCone R k (primeTailBoundary R k (primeTailBoundary R (k+1) x)) = 0
      rw [show primeTailBoundary R k (primeTailBoundary R (k+1) x) = 0 from hs, map_zero]
  simp only [LinearMap.comp_apply, primeTwoPrimeGauge, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, primeValueBoundary_tailShear, primeTwoPrimeFunctional,
    koszulDifferential_sub, hz]
  abel

theorem primeTwoPrimeGauge_cutoff (k N : ℕ) :
    primeChainCutoff R k N ≤ (primeChainCutoff R k N).comap (primeTwoPrimeGauge R k) := by
  intro x hx
  exact Submodule.sub_mem _ hx (primeTailShear_cutoff R k N hx)

theorem primeTwoPrimeGaugeInv_cutoff (k N : ℕ) :
    primeChainCutoff R k N ≤ (primeChainCutoff R k N).comap (primeTwoPrimeGaugeInv R k) := by
  intro x hx
  exact Submodule.add_mem _ hx (primeTailShear_cutoff R k N hx)

/-- The full inverse shear preserves exactly the original product cutoff. -/
def primeTwoPrimeCutoffEquiv (k N : ℕ) :
    primeChainCutoff R k N ≃ₗ[R] primeChainCutoff R k N :=
  LinearEquiv.ofLinear
    ((primeTwoPrimeGauge R k).restrict (fun _ hx => primeTwoPrimeGauge_cutoff R k N hx))
    ((primeTwoPrimeGaugeInv R k).restrict (fun _ hx => primeTwoPrimeGaugeInv_cutoff R k N hx))
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (primeTwoPrimeGauge_inverse R k).1 x.val)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (primeTwoPrimeGauge_inverse R k).2 x.val)

/-- Actual augmented cutoff complexes have the same two-prime chain normal form. -/
def primeTwoPrimeCutoffComplexIso (N : ℕ) :
    primeCutoffComplex R (primeTwoPrimeFunctional R) N ≅
      primeCutoffComplex R (primeValueFunctional R) N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (primeTwoPrimeCutoffEquiv R k N).toModuleIso)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      simp only [primeCutoffComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (primeTwoPrimeGauge_boundary R j) x.val)

/-- The two-prime normal form commutes with every height inclusion. -/
def primeTwoPrimePersistenceIso :
    primeCutoffPersistence R (primeTwoPrimeFunctional R) ≅
      primeCutoffPersistence R (primeValueFunctional R) :=
  NatIso.ofComponents (primeTwoPrimeCutoffComplexIso R) (fun h => by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl)

/-- The comparison retains the actual augmented homology persistence maps. -/
def primeTwoPrimeHomologyPersistenceIso (k : ℕ) :
    primeCutoffHomology R (primeTwoPrimeFunctional R) k ≅
      primeCutoffHomology R (primeValueFunctional R) k :=
  Functor.isoWhiskerRight (primeTwoPrimePersistenceIso R)
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k)

#print axioms primeTwoPrimeGauge_boundary
#print axioms primeTwoPrimeCutoffEquiv
#print axioms primeTwoPrimePersistenceIso
#print axioms primeTwoPrimeHomologyPersistenceIso


local instance primeNormalFormIntegerModule (k : ℕ) : Module ℤ (PrimeChainSpace ℤ k) :=
  (PrimeChainSpace ℤ k).module

/-- Arithmetic tail deletion commutes with canonical integral coefficient extension. -/
theorem primeIntegralChainMap_tailBoundary (k : ℕ) :
    ((primeTailBoundary R k).restrictScalars ℤ).comp (primeIntegralChainMap R (k+1)) =
      (primeIntegralChainMap R k).comp (primeTailBoundary ℤ k) := by
  apply (primeChainBasis ℤ (k+1)).ext
  intro s
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    primeChainBasis_eq_atom, primeIntegralChainMap_atom]
  simp only [primeTailBoundary, primeChainAtom, physicalKoszulDifferential_ιMulti,
    map_sum, map_zsmul, primeTailFunctional_single]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  split_ifs with hi
  · simp only [zero_smul, map_zero]
  · rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
    congr 1
    exact (primeIntegralChainMap_atom R _).symm

/-- The Bézout cone uses the same two integral vertices over every coefficient ring. -/
theorem primeIntegralChainMap_bezoutCone (k : ℕ) (x : PrimeChainSpace ℤ k) :
    primeIntegralChainMap R (k+1) (primeBezoutCone ℤ k x) =
      primeBezoutCone R k (primeIntegralChainMap R k x) := by
  have h3 := LinearMap.congr_fun (primeIntegralChainMap_cone R k ⟨3,Nat.prime_three⟩) x
  have h2 := LinearMap.congr_fun (primeIntegralChainMap_cone R k ⟨2,Nat.prime_two⟩) x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h3 h2
  simp only [primeBezoutCone, LinearMap.sub_apply, map_sub]
  rw [h3,h2]

/-- The normal form is defined over the integers and survives every coefficient extension. -/
theorem primeIntegralChainMap_twoPrimeGauge (k : ℕ) (x : PrimeChainSpace ℤ k) :
    primeIntegralChainMap R k (primeTwoPrimeGauge ℤ k x) =
      primeTwoPrimeGauge R k (primeIntegralChainMap R k x) := by
  simp only [primeTwoPrimeGauge, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  congr 1
  cases k with
  | zero => simp only [primeTailShear, LinearMap.zero_apply, map_zero]
  | succ k =>
    simp only [primeTailShear, LinearMap.comp_apply, primeIntegralChainMap_bezoutCone]
    congr 1
    exact (LinearMap.congr_fun (primeIntegralChainMap_tailBoundary R k) x).symm

/-- Coefficient extension and the restricted normal form agree on actual cutoff chains. -/
theorem primeIntegralCutoffMap_twoPrimeGauge (k N : ℕ) (x : primeChainCutoff ℤ k N) :
    primeIntegralCutoffMap R k N (primeTwoPrimeCutoffEquiv ℤ k N x) =
      primeTwoPrimeCutoffEquiv R k N (primeIntegralCutoffMap R k N x) := by
  apply Subtype.ext
  exact primeIntegralChainMap_twoPrimeGauge R k x.val

#print axioms primeIntegralChainMap_twoPrimeGauge
#print axioms primeIntegralCutoffMap_twoPrimeGauge
end GaloisForLFunctions.EffectiveScalingGeometry
