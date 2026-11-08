import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeNormalForm

/-!
# The transformed face basis and two-prime block differentials

Transporting the exterior basis through the arithmetic shear preserves its
prime-product cutoffs. In this basis the actual prime-valued differential
deletes only two and three. A face supported on primes above three is closed;
its two small-prime cones have coefficients two and three, and their joint
cone has boundary `2 e₃ − 3 e₂`. These are identities in the original chain
complex over every commutative coefficient ring.
-/

noncomputable section
open CategoryTheory RHTower GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry
attribute [local instance] primeLabelLinearOrder
variable (R : Type*) [CommRing R]

/-- The arithmetic gauge on all finite exterior chains. -/
def primeTwoPrimeChainEquiv (k : ℕ) : PrimeChainSpace R k ≃ₗ[R] PrimeChainSpace R k :=
  LinearEquiv.ofLinear (primeTwoPrimeGauge R k) (primeTwoPrimeGaugeInv R k)
    (primeTwoPrimeGauge_inverse R k).1 (primeTwoPrimeGauge_inverse R k).2

/-- Gauge-transformed prime faces give a basis over every commutative ring. -/
def primeTwoPrimeBasis (k : ℕ) :
    Module.Basis (Set.powersetCard Nat.Primes k) R (PrimeChainSpace R k) :=
  (primeChainBasis R k).map (primeTwoPrimeChainEquiv R k)

/-- The transformed wedge with its original prime support label. -/
def primeTwoPrimeAtom {k : ℕ} (v : Fin k → Nat.Primes) : PrimeChainSpace R k :=
  primeTwoPrimeGauge R k (primeChainAtom R v)

theorem primeTwoPrimeBasis_eq_atom {k : ℕ} (s : Set.powersetCard Nat.Primes k) :
    primeTwoPrimeBasis R k s = primeTwoPrimeAtom R (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  rw [primeTwoPrimeBasis,Module.Basis.map_apply,primeChainBasis_eq_atom]
  rfl

/-- The same support products describe the cutoff in the transformed basis. -/
theorem primeChainCutoff_eq_span_twoPrimeBasis (k N : ℕ) :
    primeChainCutoff R k N = Submodule.span R
      (primeTwoPrimeBasis R k '' {s | primeFaceProduct s ≤ N}) := by
  apply le_antisymm
  · intro x hx
    have hpre := primeTwoPrimeGaugeInv_cutoff R k N hx
    have hmap : primeChainCutoff R k N ≤
        (Submodule.span R (primeTwoPrimeBasis R k '' {s | primeFaceProduct s ≤ N})).comap
          (primeTwoPrimeGauge R k) := by
      rw [primeChainCutoff_eq_span_basis]
      apply Submodule.span_le.mpr
      rintro y ⟨s,hs,rfl⟩
      exact Submodule.subset_span ⟨s,hs,rfl⟩
    have hh := hmap hpre
    have he := LinearMap.congr_fun (primeTwoPrimeGauge_inverse R k).1 x
    change primeTwoPrimeGauge R k (primeTwoPrimeGaugeInv R k x) = x at he
    change primeTwoPrimeGauge R k (primeTwoPrimeGaugeInv R k x) ∈
      Submodule.span R (primeTwoPrimeBasis R k '' {s | primeFaceProduct s ≤ N}) at hh
    simpa only [he] using hh
  · apply Submodule.span_le.mpr
    rintro x ⟨s,hs,rfl⟩
    exact primeTwoPrimeGauge_cutoff R k N (primeChainBasis_mem_cutoff R s hs)

/-- In the transformed basis every deletion of a prime above three vanishes. -/
theorem primeTwoPrimeAtom_boundary {k : ℕ} (v : Fin (k+1) → Nat.Primes) :
    primeValueBoundary R k (primeTwoPrimeAtom R v) =
      ∑ i : Fin (k+1), ((-1 : ℤ) ^ (i : ℕ)) •
        ((if (v i).val = 2 ∨ (v i).val = 3 then ((v i).val : R) else 0) •
          primeTwoPrimeAtom R (fun j => v (i.succAbove j))) := by
  have h := LinearMap.congr_fun (primeTwoPrimeGauge_boundary R k) (primeChainAtom R v)
  simp only [LinearMap.comp_apply] at h
  change primeValueBoundary R k (primeTwoPrimeAtom R v) = _ at h
  rw [h,primeChainAtom,physicalKoszulDifferential_ιMulti]
  simp only [map_sum,map_zsmul,map_smul,primeTwoPrimeFunctional_single]
  rfl

/-- Transformed faces supported on large primes are actual arithmetic cycles. -/
theorem primeTwoPrimeAtom_boundary_zero {k : ℕ} (v : Fin (k+1) → Nat.Primes)
    (hv : ∀ i, 3 < (v i).val) :
    primeValueBoundary R k (primeTwoPrimeAtom R v) = 0 := by
  rw [primeTwoPrimeAtom_boundary]
  apply Finset.sum_eq_zero
  intro i _
  have hi : ¬ ((v i).val = 2 ∨ (v i).val = 3) := by have h := hv i; omega
  simp only [if_neg hi,zero_smul,smul_zero]

/-- Small-prime coning of a closed core has the expected scalar boundary. -/
theorem primeTwoPrimeAtom_boundary_cons {k : ℕ} (v : Fin k → Nat.Primes)
    (hv : ∀ i, 3 < (v i).val) (p : Nat.Primes) (hp : p.val = 2 ∨ p.val = 3) :
    primeValueBoundary R k (primeTwoPrimeAtom R (Fin.cons p v)) =
      (p.val : R) • primeTwoPrimeAtom R v := by
  rw [primeTwoPrimeAtom_boundary,Fin.sum_univ_succ]
  simp only [Fin.cons_succ]
  have hz : ∑ i : Fin k, ((-1 : ℤ) ^ (i.succ : ℕ)) •
      ((if (v i).val = 2 ∨ (v i).val = 3
          then ((v i).val : R) else 0) •
        primeTwoPrimeAtom R (fun j => (Fin.cons p v : Fin (k+1) → Nat.Primes) (i.succ.succAbove j))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ ((v i).val = 2 ∨ (v i).val = 3) := by have h := hv i; omega
    simp only [if_neg hi,zero_smul,smul_zero]
  rw [hz,add_zero]
  simp only [Fin.val_zero,pow_zero,one_smul,Fin.cons_zero,if_pos hp,
    Fin.succAbove_zero,Fin.cons_succ]

/-- Each large-prime core has the exact two-prime Koszul top differential. -/
theorem primeTwoPrimeAtom_topBoundary {k : ℕ} (v : Fin k → Nat.Primes)
    (hv : ∀ i, 3 < (v i).val) :
    primeValueBoundary R (k+1)
        (primeTwoPrimeAtom R (Fin.cons ⟨2,Nat.prime_two⟩ (Fin.cons ⟨3,Nat.prime_three⟩ v))) =
      (2 : R) • primeTwoPrimeAtom R (Fin.cons ⟨3,Nat.prime_three⟩ v) -
      (3 : R) • primeTwoPrimeAtom R (Fin.cons ⟨2,Nat.prime_two⟩ v) := by
  let y := primeChainAtom R v
  let p2 : Nat.Primes := ⟨2,Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3,Nat.prime_three⟩
  have h3 : physicalKoszulDifferential k (primeTwoPrimeFunctional R)
      (primeChainCone R k p3 y) = (3 : R) • y := by
    apply (primeTwoPrimeChainEquiv R k).injective
    change primeTwoPrimeGauge R k
      (physicalKoszulDifferential k (primeTwoPrimeFunctional R) (primeChainCone R k p3 y)) =
      primeTwoPrimeGauge R k ((3 : R) • y)
    have hg := LinearMap.congr_fun (primeTwoPrimeGauge_boundary R k) (primeChainCone R k p3 y)
    simp only [LinearMap.comp_apply] at hg
    rw [← hg,map_smul]
    change primeValueBoundary R k
      (primeTwoPrimeGauge R (k+1) (primeChainCone R k p3 (primeChainAtom R v))) = _
    rw [primeChainCone_atom]
    exact primeTwoPrimeAtom_boundary_cons R v hv p3 (Or.inr rfl)
  have hc := LinearMap.congr_fun
    (koszul_cartan_succ k (primeTwoPrimeFunctional R) (Finsupp.single p2 (1 : R)))
    (primeChainCone R k p3 y)
  simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.id_apply,primeTwoPrimeFunctional_single] at hc
  change physicalKoszulDifferential (k+1) (primeTwoPrimeFunctional R)
      (primeChainCone R (k+1) p2 (primeChainCone R k p3 y)) +
    primeChainCone R k p2 (physicalKoszulDifferential k (primeTwoPrimeFunctional R)
      (primeChainCone R k p3 y)) = (2 : R) • primeChainCone R k p3 y at hc
  rw [h3,map_smul] at hc
  have he := congrArg (primeTwoPrimeGauge R (k+1)) (eq_sub_of_add_eq hc)
  simp only [map_sub,map_smul] at he
  have hg := LinearMap.congr_fun (primeTwoPrimeGauge_boundary R (k+1))
    (primeChainCone R (k+1) p2 (primeChainCone R k p3 y))
  simp only [LinearMap.comp_apply] at hg
  rw [← hg] at he
  simpa only [y,primeChainCone_atom,primeTwoPrimeAtom,p2,p3] using he

#print axioms primeTwoPrimeBasis
#print axioms primeChainCutoff_eq_span_twoPrimeBasis
#print axioms primeTwoPrimeAtom_boundary
#print axioms primeTwoPrimeAtom_boundary_cons
#print axioms primeTwoPrimeAtom_topBoundary
end GaloisForLFunctions.EffectiveScalingGeometry
