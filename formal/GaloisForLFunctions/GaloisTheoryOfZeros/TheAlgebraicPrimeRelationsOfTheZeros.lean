import GaloisForLFunctions.GaloisTheoryOfZeros.ThePrimeSpectralFieldOfTheZeros
import GaloisForLFunctions.HTGeometry.KroneckerFlow

/-!
# Algebraic prime monomial relations of the zeros

For each exponent, the integer prime vectors whose monomials are algebraic form
a saturated subgroup. At every actual zero this subgroup has rational rank at
most two; irrational real part lowers the bound to one. A fixed finite union
of relation supports therefore contains every algebraic monomial support.
Any monomial involving a prime outside that union is transcendental.

The six-exponentials theorem gives both rank bounds. Unique factorization
identifies independent prime vectors with independent logarithmic frequencies;
conjugation supplies the extra exponent for the sharper bound.

Compatible arithmetic embeddings preserve this entire lattice. Conjugation and
functional reflection also preserve it, so algebraicity of monomials alone
cannot separate horizontally reflected zeros. Exact algebraic values and
non-binomial relations carry additional information not retained by the lattice.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The injective prime logarithm character on the full integer prime group. -/
def primeRelationFrequency : (Nat.Primes →₀ ℤ) →+ ℝ where
  toFun := primeLogFrequency
  map_zero' := by simp [primeLogFrequency]
  map_add' m n := by
    apply Finsupp.sum_add_index'
    · intro p; simp
    · intro p a b; simp [add_mul]

theorem primeRelationFrequency_injective : Function.Injective primeRelationFrequency := by
  intro m n h
  apply sub_eq_zero.mp
  apply (primeLogFrequency_eq_zero_iff (m-n)).mp
  change primeRelationFrequency (m-n) = 0
  rw [map_sub,h,sub_self]

/-- The prime monomial attached to a complex exponent and an integer prime vector. -/
def primeRelationValue (z : ℂ) (m : Nat.Primes →₀ ℤ) : ℂ :=
  Complex.exp (z * (primeRelationFrequency m : ℂ))

theorem primeRelationValue_zero (z : ℂ) : primeRelationValue z 0 = 1 := by
  simp [primeRelationValue]

theorem primeRelationValue_add (z : ℂ) (m n : Nat.Primes →₀ ℤ) :
    primeRelationValue z (m+n) = primeRelationValue z m * primeRelationValue z n := by
  simp only [primeRelationValue,map_add,Complex.ofReal_add,mul_add,Complex.exp_add]

theorem primeRelationValue_neg (z : ℂ) (m : Nat.Primes →₀ ℤ) :
    primeRelationValue z (-m) = (primeRelationValue z m)⁻¹ := by
  simp only [primeRelationValue,map_neg,Complex.ofReal_neg,mul_neg,Complex.exp_neg]

theorem primeRelationValue_nsmul (z : ℂ) (n : ℕ) (m : Nat.Primes →₀ ℤ) :
    primeRelationValue z (n • m) = primeRelationValue z m ^ n := by
  simp only [primeRelationValue,map_nsmul,nsmul_eq_mul,Complex.ofReal_mul,
    Complex.ofReal_natCast]
  rw [mul_left_comm,Complex.exp_nat_mul]

theorem primeRelationValue_single (z : ℂ) (p : Nat.Primes) (n : ℤ) :
    primeRelationValue z (Finsupp.single p n) =
      Complex.exp (z*(Real.log (p : ℕ) : ℂ)) ^ n := by
  change Complex.exp (z*(primeLogFrequency (Finsupp.single p n) : ℂ)) = _
  rw [primeLogFrequency_single,Complex.ofReal_mul,Complex.ofReal_intCast,
    mul_left_comm,Complex.exp_int_mul]

private theorem algebraic_integer_power {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℤ) :
    IsAlgebraic ℚ (z ^ n) := by
  cases n with
  | ofNat n => simpa using hz.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hz.pow (n+1)).inv

/-- At exponent one every prime monomial is algebraic. -/
theorem primeRelationValue_one_algebraic (m : Nat.Primes →₀ ℤ) :
    IsAlgebraic ℚ (primeRelationValue 1 m) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => rw [primeRelationValue_zero]; exact isAlgebraic_one
  | add m n hm hn => rw [primeRelationValue_add]; exact hm.mul hn
  | single p n =>
    rw [primeRelationValue_single,one_mul,
      GaloisForLFunctions.RHTower.SixExponentials.exp_log_nat p.2.pos]
    exact algebraic_integer_power (isAlgebraic_nat (p : ℕ)) n

/-- Integer prime products with algebraic value at the given exponent. -/
def algebraicPrimeRelations (z : ℂ) : AddSubgroup (Nat.Primes →₀ ℤ) where
  carrier := {m | IsAlgebraic ℚ (primeRelationValue z m)}
  zero_mem' := by rw [Set.mem_setOf_eq,primeRelationValue_zero]; exact isAlgebraic_one
  add_mem' := by
    intro m n hm hn
    change IsAlgebraic ℚ (primeRelationValue z (m+n))
    rw [primeRelationValue_add]
    exact hm.mul hn
  neg_mem' := by
    intro m hm
    change IsAlgebraic ℚ (primeRelationValue z (-m))
    rw [primeRelationValue_neg]
    exact hm.inv

/-- Algebraic prime relations are saturated in the entire free prime group. -/
theorem algebraicPrimeRelations_saturated (z : ℂ) (m : Nat.Primes →₀ ℤ)
    (n : ℕ) (hn : 0<n) :
    n • m ∈ algebraicPrimeRelations z ↔ m ∈ algebraicPrimeRelations z := by
  constructor
  · intro h
    change IsAlgebraic ℚ (primeRelationValue z m)
    apply IsAlgebraic.of_pow hn
    change IsAlgebraic ℚ (primeRelationValue z (n • m)) at h
    rwa [primeRelationValue_nsmul] at h
  · intro h; exact (algebraicPrimeRelations z).nsmul_mem h n

/-- Independence of two integer prime relations. -/
def PrimeRelationsIndependent (m n : Nat.Primes →₀ ℤ) : Prop :=
  ∀ a b : ℤ, a • m + b • n = 0 → a=0 ∧ b=0

/-- Three algebraic monomials at a nonrational exponent have an integer relation. -/
theorem algebraicPrimeRelations_three_dependent (z : ℂ)
    (hz : ¬ ∃ a : ℚ, z = (a : ℂ))
    (m n k : Nat.Primes →₀ ℤ)
    (hm : m ∈ algebraicPrimeRelations z) (hn : n ∈ algebraicPrimeRelations z)
    (hk : k ∈ algebraicPrimeRelations z) :
    ∃ a b c : ℤ, a • m + b • n + c • k = 0 ∧ ¬ (a=0 ∧ b=0 ∧ c=0) := by
  by_contra hdep
  have hx : ∀ a b : ℤ, (a : ℂ)*1+(b : ℂ)*z=0 → a=0 ∧ b=0 := by
    intro a b h
    by_cases hb : b=0
    · subst b
      have ha : (a : ℂ)=0 := by simpa using h
      exact ⟨by exact_mod_cast ha,rfl⟩
    · exfalso
      apply hz
      refine ⟨-(a : ℚ)/(b : ℚ),?_⟩
      have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
      push_cast
      apply (eq_div_iff hbC).mpr
      linear_combination h
  have hy : ∀ a b c : ℤ,
      (a : ℂ)*(primeRelationFrequency m : ℂ)+
        (b : ℂ)*(primeRelationFrequency n : ℂ)+
        (c : ℂ)*(primeRelationFrequency k : ℂ)=0 → a=0 ∧ b=0 ∧ c=0 := by
    intro a b c h
    have he : a • m + b • n + c • k = 0 := by
      apply primeRelationFrequency_injective
      simp only [map_add,map_zsmul,map_zero,zsmul_eq_mul]
      exact_mod_cast h
    by_contra hne
    exact hdep ⟨a,b,c,he,hne⟩
  apply GaloisForLFunctions.RHTower.SixExponentials.six_exponentials hx hy
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.cons_val_two,Matrix.tail_cons,one_mul,Fin.mk_one,Fin.isValue,
    Fin.reduceFinMk]
  · simpa only [primeRelationValue,one_mul] using primeRelationValue_one_algebraic m
  · simpa only [primeRelationValue,one_mul] using primeRelationValue_one_algebraic n
  · simpa only [primeRelationValue,one_mul] using primeRelationValue_one_algebraic k
  · exact hm
  · exact hn
  · exact hk


theorem primeRelationValue_conjugation (z : ℂ) (m : Nat.Primes →₀ ℤ) :
    primeRelationValue (starRingEnd ℂ z) m = starRingEnd ℂ (primeRelationValue z m) := by
  simp only [primeRelationValue,← Complex.exp_conj,map_mul,Complex.conj_ofReal]

/-- Ordinary conjugation preserves precisely the same algebraic monomials. -/
theorem algebraicPrimeRelations_conjugation (z : ℂ) :
    algebraicPrimeRelations (starRingEnd ℂ z) = algebraicPrimeRelations z := by
  apply AddSubgroup.ext
  intro m
  change IsAlgebraic ℚ (primeRelationValue (starRingEnd ℂ z) m) ↔ _
  rw [primeRelationValue_conjugation]
  exact isAlgebraic_algHom_iff primeSpectralScalarConjugation
    primeSpectralScalarConjugation.injective

private theorem conjugate_exponents_independent (z : ℂ) (him : z.im ≠ 0)
    (hre : ¬ ∃ r : ℚ, z.re = (r : ℝ)) :
    ∀ a b c : ℤ, (a : ℂ)*1+(b : ℂ)*z+(c : ℂ)*(starRingEnd ℂ z)=0 →
      a=0 ∧ b=0 ∧ c=0 := by
  intro a b c h
  have hi : (b : ℝ)*z.im - (c : ℝ)*z.im = 0 := by
    simpa [Complex.mul_im,sub_eq_add_neg] using congrArg Complex.im h
  have hbc : b=c := by
    have he : ((b : ℝ)-(c : ℝ))*z.im=0 := by linear_combination hi
    exact_mod_cast (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right him))
  subst c
  have hr : (a : ℝ)+(b : ℝ)*z.re+(b : ℝ)*z.re=0 := by
    simpa [Complex.mul_re] using congrArg Complex.re h
  by_cases hb : b=0
  · subst b
    have ha : a=0 := by exact_mod_cast (by simpa using hr : (a : ℝ)=0)
    exact ⟨ha,rfl,rfl⟩
  · exfalso
    apply hre
    refine ⟨-(a : ℚ)/(2*(b : ℚ)),?_⟩
    push_cast
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply (eq_div_iff (mul_ne_zero (by norm_num) hbR)).mpr
    linear_combination hr

/-- Irrational real part lowers the algebraic prime-relation rank to at most one. -/
theorem algebraicPrimeRelations_two_dependent (z : ℂ) (him : z.im ≠ 0)
    (hre : ¬ ∃ r : ℚ, z.re = (r : ℝ))
    (m n : Nat.Primes →₀ ℤ)
    (hm : m ∈ algebraicPrimeRelations z) (hn : n ∈ algebraicPrimeRelations z) :
    ¬ PrimeRelationsIndependent m n := by
  intro hind
  have hx : ∀ a b : ℤ, (a : ℂ)*(primeRelationFrequency m : ℂ)+
      (b : ℂ)*(primeRelationFrequency n : ℂ)=0 → a=0 ∧ b=0 := by
    intro a b h
    apply hind a b
    apply primeRelationFrequency_injective
    simp only [map_add,map_zsmul,map_zero,zsmul_eq_mul]
    exact_mod_cast h
  apply GaloisForLFunctions.RHTower.SixExponentials.six_exponentials hx
    (conjugate_exponents_independent z him hre)
  have hmc : m ∈ algebraicPrimeRelations (starRingEnd ℂ z) := by
    rwa [algebraicPrimeRelations_conjugation]
  have hnc : n ∈ algebraicPrimeRelations (starRingEnd ℂ z) := by
    rwa [algebraicPrimeRelations_conjugation]
  change IsAlgebraic ℚ (primeRelationValue z m) at hm
  change IsAlgebraic ℚ (primeRelationValue z n) at hn
  change IsAlgebraic ℚ (primeRelationValue (starRingEnd ℂ z) m) at hmc
  change IsAlgebraic ℚ (primeRelationValue (starRingEnd ℂ z) n) at hnc
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.cons_val_two,Matrix.tail_cons,mul_one,Fin.mk_one,Fin.isValue,
    Fin.reduceFinMk]
  · simpa only [primeRelationValue,one_mul] using primeRelationValue_one_algebraic m
  · simpa only [primeRelationValue,mul_comm] using hm
  · simpa only [primeRelationValue,mul_comm] using hmc
  · simpa only [primeRelationValue,one_mul] using primeRelationValue_one_algebraic n
  · simpa only [primeRelationValue,mul_comm] using hn
  · simpa only [primeRelationValue,mul_comm] using hnc

theorem primeRelationValue_reflection (z : ℂ) (m : Nat.Primes →₀ ℤ) :
    primeRelationValue (1-z) m = primeRelationValue 1 m / primeRelationValue z m := by
  simp only [primeRelationValue,sub_mul,Complex.exp_sub]

/-- Algebraicity of a monomial does not separate functional-reflection partners. -/
theorem algebraicPrimeRelations_reflection (z : ℂ) :
    algebraicPrimeRelations (1-z) = algebraicPrimeRelations z := by
  have hf (w : ℂ) (m : Nat.Primes →₀ ℤ) (hm : m ∈ algebraicPrimeRelations w) :
      m ∈ algebraicPrimeRelations (1-w) := by
    change IsAlgebraic ℚ (primeRelationValue (1-w) m)
    rw [primeRelationValue_reflection,div_eq_mul_inv]
    exact (primeRelationValue_one_algebraic m).mul hm.inv
  apply AddSubgroup.ext
  intro m
  constructor
  · intro hm
    simpa only [sub_sub_cancel] using hf (1-z) m hm
  · exact hf z m

/-- Reflection across the critical line preserves the algebraic-monomial lattice. -/
theorem algebraicPrimeRelations_horizontal_reflection (z : ℂ) :
    algebraicPrimeRelations (1-starRingEnd ℂ z) = algebraicPrimeRelations z := by
  rw [algebraicPrimeRelations_reflection,algebraicPrimeRelations_conjugation]


private theorem primeRelations_support_one (H : AddSubgroup (Nat.Primes →₀ ℤ))
    (hdep : ∀ m ∈ H, ∀ n ∈ H, ¬ PrimeRelationsIndependent m n) :
    ∃ m ∈ H, ∀ n ∈ H, n.support ⊆ m.support := by
  classical
  by_cases hex : ∃ m ∈ H, m ≠ 0
  · obtain ⟨m,hm,hm0⟩ := hex
    refine ⟨m,hm,?_⟩
    intro n hn p hp
    have h := hdep m hm n hn
    have hrel : ∃ a b : ℤ, a • m + b • n = 0 ∧ ¬ (a=0 ∧ b=0) := by
      by_contra hnone
      apply h
      intro a b he
      by_contra hne
      exact hnone ⟨a,b,he,hne⟩
    obtain ⟨a,b,he,hne⟩ := hrel
    have hb : b ≠ 0 := by
      intro hb
      subst b
      have ha : a=0 := (smul_eq_zero.mp (by simpa using he)).resolve_right hm0
      exact hne ⟨ha,rfl⟩
    by_contra hpm
    have hmP : m p=0 := Finsupp.notMem_support_iff.mp hpm
    have hnP : n p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have heP := congrArg (fun f : Nat.Primes →₀ ℤ => f p) he
    have hmul : b*n p=0 := by
      simpa only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,hmP,
        mul_zero,zero_add,Finsupp.zero_apply] using heP
    exact hnP ((mul_eq_zero.mp hmul).resolve_left hb)
  · refine ⟨0,H.zero_mem,?_⟩
    intro n hn
    have hn0 : n=0 := by
      by_contra hne
      exact hex ⟨n,hn,hne⟩
    simp [hn0]

/-- A fixed union of two relation supports contains every algebraic monomial. -/
theorem algebraicPrimeRelations_finite_support (z : ℂ)
    (hz : ¬ ∃ a : ℚ, z = (a : ℂ)) :
    ∃ m ∈ algebraicPrimeRelations z, ∃ n ∈ algebraicPrimeRelations z,
      ∀ k ∈ algebraicPrimeRelations z, k.support ⊆ m.support ∪ n.support := by
  classical
  by_cases hex : ∃ m ∈ algebraicPrimeRelations z, ∃ n ∈ algebraicPrimeRelations z,
      PrimeRelationsIndependent m n
  · obtain ⟨m,hm,n,hn,hind⟩ := hex
    refine ⟨m,hm,n,hn,?_⟩
    intro k hk p hp
    obtain ⟨a,b,c,he,hne⟩ := algebraicPrimeRelations_three_dependent z hz m n k hm hn hk
    have hc : c ≠ 0 := by
      intro hc
      subst c
      have hab := hind a b (by simpa using he)
      exact hne ⟨hab.1,hab.2,rfl⟩
    by_contra hpm
    have hmp : m p=0 := Finsupp.notMem_support_iff.mp
      (fun h => hpm (Finset.mem_union.mpr (Or.inl h)))
    have hnp : n p=0 := Finsupp.notMem_support_iff.mp
      (fun h => hpm (Finset.mem_union.mpr (Or.inr h)))
    have hkp : k p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have heP := congrArg (fun f : Nat.Primes →₀ ℤ => f p) he
    have hmul : c*k p=0 := by
      simpa only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,hmp,hnp,
        mul_zero,zero_add,Finsupp.zero_apply] using heP
    exact hkp ((mul_eq_zero.mp hmul).resolve_left hc)
  · have hdep : ∀ m ∈ algebraicPrimeRelations z, ∀ n ∈ algebraicPrimeRelations z,
        ¬ PrimeRelationsIndependent m n := by
      intro m hm n hn hind
      exact hex ⟨m,hm,n,hn,hind⟩
    obtain ⟨m,hm,hs⟩ := primeRelations_support_one (algebraicPrimeRelations z) hdep
    refine ⟨m,hm,0,(algebraicPrimeRelations z).zero_mem,?_⟩
    intro k hk
    simpa using hs k hk

/-- With irrational real part, one relation support contains all others. -/
theorem algebraicPrimeRelations_irrational_finite_support (z : ℂ) (him : z.im ≠ 0)
    (hre : ¬ ∃ r : ℚ, z.re = (r : ℝ)) :
    ∃ m ∈ algebraicPrimeRelations z,
      ∀ n ∈ algebraicPrimeRelations z, n.support ⊆ m.support := by
  apply primeRelations_support_one
  intro m hm n hn
  exact algebraicPrimeRelations_two_dependent z him hre m n hm hn

/-- Every actual zero has one finite prime support for all its algebraic monomials. -/
theorem zero_algebraicPrimeRelations_finite_support (q : XiZeroCopy) :
    ∃ m ∈ algebraicPrimeRelations (q.1 : ℂ),
      ∃ n ∈ algebraicPrimeRelations (q.1 : ℂ),
        ∀ k ∈ algebraicPrimeRelations (q.1 : ℂ), k.support ⊆ m.support ∪ n.support := by
  apply algebraicPrimeRelations_finite_support
  rintro ⟨a,ha⟩
  have him := xi_divisor_support_im_ne_zero q.1
  apply him
  rw [ha]
  simp

/-- The sharper single-support alternative for actual zeros with irrational real part. -/
theorem zero_algebraicPrimeRelations_irrational_finite_support (q : XiZeroCopy)
    (hre : ¬ ∃ r : ℚ, (q.1 : ℂ).re = (r : ℝ)) :
    ∃ m ∈ algebraicPrimeRelations (q.1 : ℂ),
      ∀ n ∈ algebraicPrimeRelations (q.1 : ℂ), n.support ⊆ m.support :=
  algebraicPrimeRelations_irrational_finite_support (q.1 : ℂ)
    (xi_divisor_support_im_ne_zero q.1) hre


/-- A compatible scalar embedding transports every mixed-prime monomial. -/
theorem primeRelationValue_arithmetic (σ : ℂ →ₐ[ℚ] ℂ)
    (hσ : PreservesAllPrimeZeroSpectrum σ) (z : rawZeroRelationGroup)
    (m : Nat.Primes →₀ ℤ) :
    primeRelationValue (allPrimeExponentHom σ hσ z : ℂ) m =
      σ (primeRelationValue (z : ℂ) m) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp only [primeRelationValue_zero,map_one]
  | add m n hm hn => rw [primeRelationValue_add,primeRelationValue_add,hm,hn,map_mul]
  | single p n =>
    rw [primeRelationValue_single,primeRelationValue_single,map_zpow₀]
    have he := allPrimeExponentHom_eigenvalue σ hσ p p.2 z
    have hv : Complex.exp ((allPrimeExponentHom σ hσ z : ℂ)*(Real.log (p : ℕ) : ℂ)) =
        σ (Complex.exp ((z : ℂ)*(Real.log (p : ℕ) : ℂ))) := by
      simpa only [zeroPrimeEigenvalue,mul_comm] using he
    rw [hv]

/-- The full algebraic-monomial lattice is invariant along arithmetic exponent orbits. -/
theorem algebraicPrimeRelations_arithmetic (σ : ℂ →ₐ[ℚ] ℂ)
    (hσ : PreservesAllPrimeZeroSpectrum σ) (z : rawZeroRelationGroup) :
    algebraicPrimeRelations (allPrimeExponentHom σ hσ z : ℂ) =
      algebraicPrimeRelations (z : ℂ) := by
  apply AddSubgroup.ext
  intro m
  change IsAlgebraic ℚ (primeRelationValue (allPrimeExponentHom σ hσ z : ℂ) m) ↔ _
  rw [primeRelationValue_arithmetic]
  exact isAlgebraic_algHom_iff σ σ.injective

/-- Outside one fixed finite set, every nonzero mixed prime monomial is transcendental. -/
theorem zero_prime_monomials_transcendental_off_finite (q : XiZeroCopy) :
    ∃ S : Finset Nat.Primes, ∀ m : Nat.Primes →₀ ℤ,
      ¬ m.support ⊆ S → ¬ IsAlgebraic ℚ (primeRelationValue (q.1 : ℂ) m) := by
  obtain ⟨m,hm,n,hn,hs⟩ := zero_algebraicPrimeRelations_finite_support q
  exact ⟨m.support ∪ n.support,fun k hk halg => hk (hs k halg)⟩

/-- Two distinct prime axes are independent in the integer prime group. -/
theorem primeRelations_axes_independent (p q : Nat.Primes) (hpq : p ≠ q) :
    PrimeRelationsIndependent (Finsupp.single p 1) (Finsupp.single q 1) := by
  intro a b h
  have ha := congrArg (fun f : Nat.Primes →₀ ℤ => f p) h
  have hb := congrArg (fun f : Nat.Primes →₀ ℤ => f q) h
  exact ⟨by simpa [hpq,hpq.symm] using ha,by simpa [hpq,hpq.symm] using hb⟩

/-- Two algebraic prime values at an actual zero force its real part to be rational. -/
theorem zero_two_algebraic_prime_values_real_rational (q : XiZeroCopy)
    (p r : Nat.Primes) (hpr : p ≠ r)
    (hp : IsAlgebraic ℚ (Complex.exp ((q.1 : ℂ)*(Real.log (p : ℕ) : ℂ))))
    (hr : IsAlgebraic ℚ (Complex.exp ((q.1 : ℂ)*(Real.log (r : ℕ) : ℂ)))) :
    ∃ a : ℚ, (q.1 : ℂ).re = (a : ℝ) := by
  by_contra hre
  have hm : Finsupp.single p 1 ∈ algebraicPrimeRelations (q.1 : ℂ) := by
    change IsAlgebraic ℚ (primeRelationValue (q.1 : ℂ) (Finsupp.single p 1))
    simpa only [primeRelationValue_single,zpow_one] using hp
  have hn : Finsupp.single r 1 ∈ algebraicPrimeRelations (q.1 : ℂ) := by
    change IsAlgebraic ℚ (primeRelationValue (q.1 : ℂ) (Finsupp.single r 1))
    simpa only [primeRelationValue_single,zpow_one] using hr
  exact algebraicPrimeRelations_two_dependent (q.1 : ℂ)
    (xi_divisor_support_im_ne_zero q.1) hre _ _ hm hn
    (primeRelations_axes_independent p r hpr)

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeRelationFrequency_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeRelationValue_one_algebraic
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_saturated
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_three_dependent
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_two_dependent
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_conjugation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_reflection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_horizontal_reflection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_finite_support
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zero_algebraicPrimeRelations_finite_support
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zero_algebraicPrimeRelations_irrational_finite_support
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeRelationValue_arithmetic
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.algebraicPrimeRelations_arithmetic
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zero_prime_monomials_transcendental_off_finite
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.zero_two_algebraic_prime_values_real_rational
