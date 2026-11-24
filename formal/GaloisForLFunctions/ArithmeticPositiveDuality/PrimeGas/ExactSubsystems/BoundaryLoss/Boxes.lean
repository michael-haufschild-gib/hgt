import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Envelope

/-! # Exact independent boxes of prime occupation digits -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

abbrev BoxDigits (P : Finset Nat.Primes) (d : ℕ+) := (p : P) → Fin d.val

def boxOccupation {P : Finset Nat.Primes} {d : ℕ+} (i : BoxDigits P d) : Nat.Primes →₀ ℕ :=
  ∑ p : P, Finsupp.single p.val (i p).val

def boxLabel (P : Finset Nat.Primes) (d : ℕ+) (i : BoxDigits P d) : ℕ+ := label (boxOccupation i)

/-- Occupations remaining after all digits of one box have been extracted. -/
abbrev BoxTail (P : Finset Nat.Primes) (d : ℕ+) :=
  {v : Nat.Primes →₀ ℕ // ∀ p ∈ P, d.val ∣ v p}

private theorem digit_inside {P : Finset Nat.Primes} {d : ℕ+} (i : BoxDigits P d) (p : P) :
    boxOccupation i p.val = (i p).val := by
  classical
  rw [boxOccupation,Finsupp.finsetSum_apply,Finset.sum_eq_single p]
  · exact Finsupp.single_eq_same
  · intro q _ hq
    exact Finsupp.single_eq_of_ne' (fun he => hq (Subtype.ext he))
  · simp

private theorem digit_outside {P : Finset Nat.Primes} {d : ℕ+} (i : BoxDigits P d)
    {p : Nat.Primes} (hp : p ∉ P) : boxOccupation i p = 0 := by
  rw [boxOccupation,Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun q _ => Finsupp.single_eq_of_ne' (fun e => hp (e ▸ q.property)))

/-- Euclidean division in each selected occupation is a tensor decomposition of the full gas. -/
theorem box_exact (P : Finset Nat.Primes) (d : ℕ+) :
    exactLabelProduct (boxLabel P d) (fun v : BoxTail P d => label v.val) := by
  classical
  constructor
  · rintro ⟨i,u⟩ ⟨j,v⟩ he
    have h : boxOccupation i+u.val = boxOccupation j+v.val := label.injective
      ((label_add _ _).trans (he.trans (label_add _ _).symm))
    have hij : i = j := by
      funext p
      apply Fin.ext
      have hp := DFunLike.congr_fun h p.val
      simp only [Finsupp.add_apply,digit_inside] at hp
      have hm := congrArg (· % d.val) hp
      simpa only [Nat.add_mod,Nat.mod_eq_zero_of_dvd (u.property p p.property),
        Nat.mod_eq_zero_of_dvd (v.property p p.property),Nat.add_zero,Nat.mod_mod,
        Nat.mod_eq_of_lt (i p).isLt,Nat.mod_eq_of_lt (j p).isLt] using hm
    subst j
    exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
  · intro n
    let ν := label.symm n
    let i : BoxDigits P d := fun p => ⟨ν p.val % d.val,Nat.mod_lt _ d.pos⟩
    have hi : boxOccupation i ≤ ν := by
      intro p
      by_cases hp : p ∈ P
      · rw [digit_inside i (⟨p,hp⟩ : P)]
        exact Nat.mod_le _ _
      · rw [digit_outside i hp]
        exact Nat.zero_le _
    let v := ν-boxOccupation i
    have hv (p : Nat.Primes) (hp : p ∈ P) : d.val ∣ v p := by
      change d.val ∣ ν p - boxOccupation i p
      rw [digit_inside i (⟨p,hp⟩ : P)]
      refine ⟨ν p/d.val,?_⟩
      change ν p - ν p % d.val = d.val*(ν p/d.val)
      have := Nat.mod_add_div (ν p) d.val
      omega
    refine ⟨(i,⟨v,hv⟩),(label_add _ _).symm.trans ?_⟩
    rw [show boxOccupation i+v = ν from add_tsub_cancel_of_le hi]
    exact label.apply_symm_apply n

theorem boxLabel_product (P : Finset Nat.Primes) (d : ℕ+) (i : BoxDigits P d) :
    boxLabel P d i = ∏ p : P, (primePNat p.val)^(i p).val := by
  classical
  have h (S : Finset P) : label (∑ p ∈ S, Finsupp.single p.val (i p).val) =
      ∏ p ∈ S, (primePNat p.val)^(i p).val := by
    induction S using Finset.induction_on with
    | empty =>
      apply PNat.coe_injective
      simp [label,primeOccupationEquivPNat,primeProduct]
    | insert p S hp ih =>
      rw [Finset.sum_insert hp,Finset.prod_insert hp,label_add,ih]
      congr 1
      exact PNat.coe_injective (Finsupp.prod_single_index (h := fun q k => (q : Nat.Primes).val^k) (pow_zero _))
  exact h Finset.univ

theorem box_supported (P : Finset Nat.Primes) (d : ℕ+) (i : BoxDigits P d) :
    (boxLabel P d i).val ∈ Nat.factoredNumbers (primeWindow P) := by
  have h1 : 1 ∈ Nat.factoredNumbers (primeWindow P) := Nat.mem_factoredNumbers.mpr ⟨one_ne_zero,by simp⟩
  have hp (p : P) : p.val.val ∈ Nat.factoredNumbers (primeWindow P) := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset p.val.property.ne_zero
    rw [p.val.property.primeFactors]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_map.mpr ⟨p.val,p.property,rfl⟩)
  have hpow (p : P) (k : ℕ) : p.val.val^k ∈ Nat.factoredNumbers (primeWindow P) := by
    induction k with
    | zero => simpa only [pow_zero] using h1
    | succ k ih => rw [pow_succ]; exact Nat.mul_mem_factoredNumbers ih (hp p)
  rw [boxLabel_product]
  change ((∏ p : P, (primePNat p.val)^(i p).val) : ℕ+).val ∈ _
  have hv (S : Finset P) : (∏ p ∈ S, (primePNat p.val)^(i p).val).val = ∏ p ∈ S, p.val.val^(i p).val := by
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert p S hp' ih => simp only [Finset.prod_insert hp',PNat.mul_coe,ih]; rfl
  rw [hv]
  exact Finset.prod_induction _ _ (fun _ _ => Nat.mul_mem_factoredNumbers) h1
    (fun p _ => hpow p _)

#print axioms box_exact
#print axioms boxLabel_product
#print axioms box_supported

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
