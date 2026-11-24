import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Repetition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.ExactFactors
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.PrimeTower

/-! # Finite tensor factors supported on one prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

/-- Occupations of all species except the selected prime. -/
abbrev Core (q : Nat.Primes) := {u : Nat.Primes →₀ ℕ // u q = 0}

private theorem label_single_ray (q : Nat.Primes) (k : ℕ) : label (Finsupp.single q k) = primeRayLabel q k := by
  apply PNat.coe_injective
  exact Finsupp.prod_single_index (h := fun p n => (p : Nat.Primes).val^n) (pow_zero _)

/-- Disentangle a single prime occupation and the unaltered other species. -/
def primeCoordinates (q : Nat.Primes) : ℕ+ ≃ ℕ × Core q where
  toFun n := ((label.symm n) q,⟨(label.symm n).erase q,Finsupp.erase_same⟩)
  invFun v := label (Finsupp.single q v.1 + v.2.val)
  left_inv n := (congrArg label (Finsupp.single_add_erase q (label.symm n))).trans (label.apply_symm_apply n)
  right_inv := by
    rintro ⟨k,c⟩
    apply Prod.ext
    · simp only [Equiv.symm_apply_apply,Finsupp.add_apply,Finsupp.single_eq_same,c.property,add_zero]
    · apply Subtype.ext
      simp only [Equiv.symm_apply_apply,Finsupp.erase_add,Finsupp.erase_single,zero_add]
      exact Finsupp.erase_of_notMem_support (by simpa only [Finsupp.mem_support_iff,not_not] using c.property)

theorem primeCoordinates_ray (q : Nat.Primes) (k : ℕ) :
    primeCoordinates q (primeRayLabel q k) = (k,⟨0,rfl⟩) := by
  rw [← label_single_ray]
  apply Prod.ext
  · simp only [primeCoordinates,Equiv.coe_fn_mk,Equiv.symm_apply_apply,Finsupp.single_eq_same]
  · apply Subtype.ext
    simp only [primeCoordinates,Equiv.coe_fn_mk,Equiv.symm_apply_apply,Finsupp.erase_single]

theorem primeCoordinates_mul_ray (q : Nat.Primes) (k : ℕ) (n : ℕ+) :
    primeCoordinates q (primeRayLabel q k * n) =
      (k+(primeCoordinates q n).1,(primeCoordinates q n).2) := by
  have he : label.symm (primeRayLabel q k*n) = Finsupp.single q k + label.symm n := by
    apply label.injective
    rw [Equiv.apply_symm_apply,label_add,label_single_ray,Equiv.apply_symm_apply]
  apply Prod.ext
  · simp only [primeCoordinates,Equiv.coe_fn_mk,he,Finsupp.add_apply,Finsupp.single_eq_same]
  · apply Subtype.ext
    simp only [primeCoordinates,Equiv.coe_fn_mk,he,Finsupp.erase_add,Finsupp.erase_single,zero_add]

/-- Recombine a complementary exponent with the other prime occupations. -/
def liftLabel {κ : Type*} (q : Nat.Primes) (c : κ → ℕ) (v : κ × Core q) : ℕ+ :=
  (primeCoordinates q).symm (c v.1,v.2)

theorem lift_exact {ι κ : Type*} (q : Nat.Primes) {a : ι → ℕ} {c : κ → ℕ}
    (h : Function.Bijective (fun u : ι × κ => a u.1+c u.2)) :
    exactLabelProduct (fun i => primeRayLabel q (a i)) (liftLabel q c) := by
  let e := (((Equiv.prodAssoc ι κ (Core q)).symm.trans
    ((Equiv.ofBijective _ h).prodCongr (Equiv.refl (Core q)))).trans (primeCoordinates q).symm)
  have he (u : ι × (κ × Core q)) : primeRayLabel q (a u.1)*liftLabel q c u.2 = e u := by
    apply (primeCoordinates q).injective
    change _ = primeCoordinates q ((primeCoordinates q).symm (a u.1+c u.2.1,u.2.2))
    rw [primeCoordinates_mul_ray,liftLabel,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  change Function.Bijective (fun u : ι × (κ × Core q) => _)
  rw [funext he]
  exact e.bijective

/-- Removing state names preserves an exact product because every label in either factor has multiplicity one. -/
theorem exact_range_right {ι κ : Type*} {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    exactLabelProduct a (fun j : Set.range b => j.val) := by
  constructor
  · rintro ⟨i,⟨_,⟨j,rfl⟩⟩⟩ ⟨i',⟨_,⟨j',rfl⟩⟩⟩ he
    have hh := h.1 (a₁ := (i,j)) (a₂ := (i',j')) he
    cases hh
    rfl
  · intro n
    obtain ⟨⟨i,j⟩,he⟩ := h.2 n
    exact ⟨(i,⟨b j,j,rfl⟩),he⟩

/-- A proposed finite digit set occurs in the full arithmetic gas with an independent complement. -/
def extractable (q : Nat.Primes) (A : Finset ℕ) :=
  ∃ B : Set ℕ+, exactLabelProduct (fun i : A => primeRayLabel q i.val) (fun b : B => b.val)

/-- Restricting an exact product to the prime ray gives an additive tiling of all exponents. -/
theorem ray_of_extraction {q : Nat.Primes} {A : Finset ℕ} (h : extractable q A) :
    ∃ C : Set ℕ, tilesRay A C := by
  obtain ⟨B,hB⟩ := h
  let C := {k : ℕ | primeRayLabel q k ∈ B}
  refine ⟨C,?_,?_⟩
  · intro u v he
    have hh := hB.1 (a₁ := (u.1,⟨primeRayLabel q u.2.val,u.2.property⟩))
      (a₂ := (v.1,⟨primeRayLabel q v.2.val,v.2.property⟩)) (by
        change primeRayLabel q _ * primeRayLabel q _ = primeRayLabel q _ * primeRayLabel q _
        simpa only [primeRayLabel,pow_add] using congrArg (primeRayLabel q) he)
    exact Prod.ext (congrArg (fun x : A × B => x.1) hh)
      (Subtype.ext (primeRayLabel_injective q (congrArg (fun x : A × B => x.2.val) hh)))
  · intro n
    obtain ⟨⟨a,b⟩,he⟩ := hB.2 (primeRayLabel q n)
    have hc := congrArg (primeCoordinates q) he
    change primeCoordinates q (primeRayLabel q a.val*b.val) = _ at hc
    rw [primeCoordinates_mul_ray,primeCoordinates_ray] at hc
    let k := (primeCoordinates q b.val).1
    have hb : primeRayLabel q k = b.val := by
      apply (primeCoordinates q).injective
      rw [primeCoordinates_ray]
      exact Prod.ext rfl (congrArg Prod.snd hc).symm
    have hk : primeRayLabel q k ∈ B := hb.symm ▸ b.property
    exact ⟨(a,⟨k,hk⟩),congrArg Prod.fst hc⟩

/-- The bounded finite interval certificate characterizes all extractable one-prime spectra. -/
theorem extractable_iff_interval (q : Nat.Primes) (A : Finset ℕ) (hA : A.Nonempty) :
    extractable q A ↔ ∃ L : ℕ+, L.val ≤ 2^(A.max' hA) ∧ ∃ T : Finset ℕ, tilesInterval A T L.val := by
  constructor
  · intro h
    obtain ⟨C,hC⟩ := ray_of_extraction h
    exact finite_interval_of_ray hC hA
  · rintro ⟨L,_,T,hT⟩
    have hp := lift_exact q (a := fun i : A => i.val) (c := fun v : T × ℕ => v.1.val+L.val*v.2)
      (repeated_interval_exact hT)
    exact ⟨_,exact_range_right hp⟩

#print axioms primeCoordinates_ray
#print axioms primeCoordinates_mul_ray
#print axioms lift_exact
#print axioms exact_range_right
#print axioms ray_of_extraction
#print axioms extractable_iff_interval

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
