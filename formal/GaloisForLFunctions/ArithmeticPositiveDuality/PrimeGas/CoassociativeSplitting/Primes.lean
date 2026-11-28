import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting.Classification

/-! # Orientation of primes and the obstruction for cyclic-order splitting -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting

def primeLabel (p : Nat.Primes) : ℕ+ := ⟨p.val,p.property.pos⟩

/-- On each prime shell exactly one endpoint survives with the vacuum phase. -/
theorem prime_orientation (F : Kernel) (p : Nat.Primes) (h : isometric F ∧ coassociative F) :
    (F (primeLabel p) 1=F 1 1 ∧ F 1 (primeLabel p)=0) ∨
    (F (primeLabel p) 1=0 ∧ F 1 (primeLabel p)=F 1 1) := by
  let n := primeLabel p
  have hn : n≠1 := fun e => p.property.ne_one (congrArg PNat.val e)
  have normed := (classification F).mp h
  obtain ⟨a,b,prod,nz⟩ := occupied F normed.1 n
  have dvd : a.val∣p.val := ⟨b.val,(congrArg PNat.val prod).symm⟩
  obtain one|self := p.property.eq_one_or_self_of_dvd _ dvd
  · have ae : a=1 := PNat.coe_injective one
    subst a
    rw [one_mul] at prod
    subst b
    have anchor := (normed.2 1 n nz).2
    refine Or.inr ⟨?_,anchor⟩
    by_contra other
    have unit : ‖F 1 n‖^2=1 := by rw [anchor,vacuum_unit F normed.1]
    have e := exclusive F normed.1 (show 1*n=n*1 by rw [one_mul,mul_one]) unit other
    exact hn (congrArg Prod.fst e)
  · have ae : a=n := PNat.coe_injective self
    have be : b=1 := mul_left_cancel (show a*b=a*1 by rw [prod,ae,mul_one])
    subst b
    rw [mul_one] at prod
    subst a
    have anchor := (normed.2 n 1 nz).1
    refine Or.inl ⟨anchor,?_⟩
    by_contra other
    have unit : ‖F n 1‖^2=1 := by rw [anchor,vacuum_unit F normed.1]
    have e := exclusive F normed.1 (show n*1=1*n by rw [one_mul,mul_one]) unit other
    exact hn (congrArg Prod.snd e)

/-- Exchange-symmetric magnitudes are incompatible with a coassociative
isometry, already on the energy log 2. -/
theorem no_symmetric : ¬ ∃ F : Kernel, isometric F ∧ coassociative F ∧ ∀ a b, ‖F a b‖=‖F b a‖ := by
  rintro ⟨F,iso,assoc,symm⟩
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  have unit := vacuum_unit F ((isometric_iff F).mp iso)
  have eqn := symm (primeLabel p) 1
  obtain ⟨a,b⟩|⟨a,b⟩ := prime_orientation F p ⟨iso,assoc⟩
  · rw [a,b,norm_zero] at eqn
    rw [eqn,zero_pow (two_ne_zero : (2:ℕ)≠0)] at unit
    exact zero_ne_one unit
  · rw [a,b,norm_zero] at eqn
    rw [←eqn,zero_pow (two_ne_zero : (2:ℕ)≠0)] at unit
    exact zero_ne_one unit

def cyclic (s : ℂ) : Kernel := fun a b => channel s (a*b) a.val

theorem cyclic_isometric_iff (s : ℂ) : isometric (cyclic s) ↔ s.re=1/2 := split_isometric_iff s

private theorem cyclic_ne_zero (s : ℂ) (a b : ℕ+) : cyclic s a b≠0 := by
  have pos : 0 < (a.val.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr a.pos)
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr pos).ne') (Complex.exp_ne_zero _)

/-- Every isometric cyclic-order splitter fails strict coassociativity,
independently of the clock height. -/
theorem cyclic_obstruction (s : {s : ℂ // s.re=1/2}) : ¬ coassociative (cyclic s.val) := by
  intro h
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  have orientation := prime_orientation (cyclic s.val) p ⟨(cyclic_isometric_iff _).mpr s.property,h⟩
  rcases orientation with ⟨_,zero⟩|⟨zero,_⟩
  · exact cyclic_ne_zero _ _ _ zero
  · exact cyclic_ne_zero _ _ _ zero

#print axioms prime_orientation
#print axioms no_symmetric
#print axioms cyclic_isometric_iff
#print axioms cyclic_obstruction

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting
