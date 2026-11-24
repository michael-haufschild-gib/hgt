import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.PrimeRay

/-! # Exact extraction of contiguous prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

private theorem first_vacuum {ι : Type*} {a : ι → ℕ+} {B : Set ℕ+}
    (h : exactLabelProduct a (fun b : B => b.val)) : ∃ i, a i = 1 := by
  obtain ⟨⟨i,b⟩,he⟩ := h.2 1
  have hv : (a i).val*b.val.val = 1 := congrArg PNat.val he
  exact ⟨i,PNat.coe_injective (Nat.eq_one_of_mul_eq_one_right hv)⟩

private theorem transfer_label {ι : Type*} {a : ι → ℕ+} {B C : Set ℕ+}
    (hB : exactLabelProduct a (fun b : B => b.val)) (hC : exactLabelProduct a (fun c : C => c.val))
    {n : ℕ+} (hsmall : ∀ m : ℕ+, m.val < n.val → m ∈ C → m ∈ B) (hn : n ∈ B) : n ∈ C := by
  obtain ⟨i₀,h₀⟩ := first_vacuum hB
  obtain ⟨⟨i,c⟩,he⟩ := hC.2 n
  change a i*c.val = n at he
  by_cases h1 : a i = 1
  · rw [h1,one_mul] at he
    exact he ▸ c.property
  · have ha : 1 < (a i).val := by
      have hne : (a i).val ≠ 1 := fun e => h1 (PNat.coe_injective e)
      have hp := (a i).pos
      omega
    have hc : c.val.val < n.val := by
      rw [← he,PNat.mul_coe]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right ha c.val.pos
    have hcol := hB.1 (a₁ := (i,⟨c.val,hsmall c.val hc c.property⟩)) (a₂ := (i₀,⟨n,hn⟩))
      (he.trans (show n = a i₀*n by rw [h₀,one_mul]))
    exact False.elim (h1 ((congrArg (fun v : ι × B => a v.1) hcol).trans h₀))

/-- Every exact first factor determines the complementary label set, even for infinite spectra. -/
theorem complement_unique {ι : Type*} {a : ι → ℕ+} {B C : Set ℕ+}
    (hB : exactLabelProduct a (fun b : B => b.val)) (hC : exactLabelProduct a (fun c : C => c.val)) :
    B = C := by
  have hall (k : ℕ) : ∀ n : ℕ+, n.val = k → (n ∈ B ↔ n ∈ C) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rintro n rfl
      exact ⟨transfer_label hB hC (fun m hm => (ih m.val hm m rfl).2),
        transfer_label hC hB (fun m hm => (ih m.val hm m rfl).1)⟩
  exact Set.ext (fun n => hall n.val n rfl)

/-- The remaining occupation at the selected prime is a multiple of the digit length. -/
def radixComplement (q : Nat.Primes) (d : ℕ+) : Set ℕ+ := {n | d.val ∣ (primeCoordinates q n).1}

theorem radix_exact (q : Nat.Primes) (d : ℕ+) :
    exactLabelProduct (fun i : Fin d.val => primeRayLabel q i.val) (fun n : radixComplement q d => n.val) := by
  let b := liftLabel q (fun k : ℕ => d.val*k)
  have h := exact_range_right (lift_exact q (a := fun i : Fin d.val => i.val)
    (c := fun k => d.val*k) (radixEquiv d).bijective)
  have hr : Set.range b = radixComplement q d := by
    ext n
    constructor
    · rintro ⟨⟨k,c⟩,rfl⟩
      change d.val ∣ (primeCoordinates q ((primeCoordinates q).symm (d.val*k,c))).1
      rw [Equiv.apply_symm_apply]
      exact dvd_mul_right _ _
    · rintro ⟨k,hk⟩
      refine ⟨(k,(primeCoordinates q n).2),(primeCoordinates q).injective ?_⟩
      change primeCoordinates q ((primeCoordinates q).symm _) = _
      rw [Equiv.apply_symm_apply]
      exact Prod.ext hk.symm rfl
  change exactLabelProduct _ (fun n : Set.range b => n.val) at h
  rwa [hr] at h

theorem radix_complement_iff (q : Nat.Primes) (d : ℕ+) (B : Set ℕ+) :
    exactLabelProduct (fun i : Fin d.val => primeRayLabel q i.val) (fun n : B => n.val) ↔ B = radixComplement q d :=
  ⟨fun h => complement_unique h (radix_exact q d),fun e => e ▸ radix_exact q d⟩

/-- A vacuum together with g distinguishable states at one quantum of energy. -/
def levelLabel (q : Nat.Primes) (g : ℕ) (i : Fin (g+1)) := primeRayLabel q (min i.val 1)

theorem two_level_extractable_iff (q : Nat.Primes) (g : ℕ) :
    (∃ B : Set ℕ+, exactLabelProduct (levelLabel q g) (fun n : B => n.val)) ↔ g ≤ 1 := by
  constructor
  · rintro ⟨B,h⟩
    by_contra! hg
    obtain ⟨v,_⟩ := h.2 1
    let i : Fin (g+1) := ⟨1,by omega⟩
    let j : Fin (g+1) := ⟨2,by omega⟩
    have he : levelLabel q g i = levelLabel q g j := rfl
    have hc := h.1 (a₁ := (i,v.2)) (a₂ := (j,v.2)) (congrArg (· * v.2.val) he)
    have hn : (1:ℕ) = 2 := congrArg (fun u : Fin (g+1) × B => u.1.val) hc
    omega
  · intro hg
    let d : ℕ+ := ⟨g+1,Nat.succ_pos _⟩
    refine ⟨radixComplement q d,?_⟩
    have he : levelLabel q g = fun i : Fin (g+1) => primeRayLabel q i.val := by
      funext i
      exact congrArg (primeRayLabel q) (min_eq_left ((Nat.le_of_lt_succ i.isLt).trans hg))
    rw [he]
    exact radix_exact q d

#print axioms complement_unique
#print axioms radix_exact
#print axioms radix_complement_iff
#print axioms two_level_extractable_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
