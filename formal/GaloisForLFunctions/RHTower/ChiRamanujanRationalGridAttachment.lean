import GaloisForLFunctions.RHTower.ChiRamanujanRationalCofactors

/-!
# Exact rational attachment to the literal critical prime-square grid

At every positive integer lift a/R², the rational valuation coefficients
are exactly the already identified finite critical grid weights. The complete
distinguished-label sum equals the actual grouped atom mass, including lifts
of the zero residue class. No rational coefficient survives outside the
prime-square denominator grid, and every allowed positive rational has a
positive integer lift on that grid.

Together with the complete rational/cofactor HasSum, this identifies the
positive multiplicative-cone source without suppressing numerator primes.
The full physical profile, remaining frequency sectors and the growing
near-cone/tail cancellation are separate mathematical obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def criticalPrimeImage (P : Finset Nat.Primes) : Finset ℕ := P.image (fun p : Nat.Primes => (p : ℕ))

private lemma image_filter (P : Finset Nat.Primes) :
    (criticalPrimeImage P).filter Nat.Prime=criticalPrimeImage P := by
  apply Finset.filter_eq_self.mpr
  intro n hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  exact p.property

theorem criticalPrimeImage_modulus (P : Finset Nat.Primes) :
    ramanujanGridModulus (criticalPrimeImage P)=criticalPrimeLevel P^2 := by
  unfold ramanujanGridModulus ramanujanPrimeRadical
  rw [image_filter]
  congr 1
  unfold criticalPrimeImage criticalPrimeLevel
  rw [Finset.prod_image]
  intro p hp q hq he
  exact Subtype.ext he

private lemma level_pos (P : Finset Nat.Primes) : 0 < criticalPrimeLevel P :=
  Finset.prod_pos (fun p _ => p.property.pos)

private lemma level_factorization (P : Finset Nat.Primes) (p : P) :
    (criticalPrimeLevel P).factorization p=1 := by
  rw [criticalPrimeLevel,Nat.factorization_prod_apply (fun q _ => q.property.ne_zero)]
  have he (q : Nat.Primes) : (q : ℕ).factorization p=if q=p.val then 1 else 0 := by
    rw [q.property.factorization]
    by_cases h : q=p.val
    · subst q
      simp
    · have hn : (q : ℕ) ≠ ((p : Nat.Primes) : ℕ) := fun he => h (Subtype.ext he)
      simp [h,Ne.symm hn]
  simp only [he]
  simp [p.property]

def criticalGridRational (P : Finset Nat.Primes) (a : ℕ+) : PositiveRational :=
  ⟨(a.val : ℚ)/((criticalPrimeLevel P^2 : ℕ) : ℚ),
    div_pos (by exact_mod_cast a.property) (by exact_mod_cast pow_pos (level_pos P) 2)⟩

theorem criticalGridRational_valuation (P : Finset Nat.Primes) (a : ℕ+) (p : P) :
    positiveRationalValuations (criticalGridRational P a) p=(a.val.factorization p : ℤ)-2 := by
  letI : Fact (Nat.Prime ((p : Nat.Primes) : ℕ)) := ⟨p.val.property⟩
  rw [← padicValRat_rationalOfValuations,rationalOfValuations_positive]
  change padicValRat ((p : Nat.Primes) : ℕ)
    ((a.val : ℚ)/((criticalPrimeLevel P^2 : ℕ) : ℚ))=_
  rw [padicValRat.div (by exact_mod_cast a.property.ne')
      (by exact_mod_cast (pow_pos (level_pos P) 2).ne'),
    padicValRat.of_nat,padicValRat.of_nat,
    ← Nat.factorization_def _ p.val.property,← Nat.factorization_def _ p.val.property,
    Nat.factorization_pow]
  simp only [Finsupp.smul_apply,smul_eq_mul,level_factorization,mul_one,Nat.cast_ofNat]

private lemma base_one (p : Nat.Primes) : cubicPrimeBase p 1=(p : ℂ)⁻¹ := by
  simp [cubicPrimeBase,Complex.cpow_neg_one]

def criticalIntegerBase (p n : ℕ) : ℝ :=
  ramanujanTorsionIndicator (p^2) n-(p : ℝ)⁻¹*ramanujanTorsionIndicator p n

def criticalIntegerTag (p n : ℕ) : ℝ :=
  (p : ℝ)⁻¹*ramanujanTorsionIndicator p n-((p^2 : ℕ) : ℝ)⁻¹

theorem criticalGridRational_base (P : Finset Nat.Primes) (a : ℕ+) (p : P) :
    (1-cubicPrimeBase p 1)*complexCoefficient (cubicPrimeBase p 1)
      (positiveRationalValuations (criticalGridRational P a) p)=
      (criticalIntegerBase p a.val : ℂ) := by
  rw [criticalGridRational_valuation,base_one]
  have hpow (k : ℕ) : ((p : Nat.Primes) : ℕ)^k ∣ a.val ↔ k ≤ a.val.factorization p :=
    p.val.property.pow_dvd_iff_le_factorization a.property.ne'
  have hd : ((p : Nat.Primes) : ℕ) ∣ a.val ↔ 1 ≤ a.val.factorization p := by simpa using hpow 1
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by exact_mod_cast p.val.property.ne_zero
  have hp1 : (1 : ℂ)-((p : Nat.Primes) : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have he : ((p : Nat.Primes) : ℂ)=1 := by
      have he := congrArg Inv.inv h
      simpa using he.symm
    exact p.val.property.ne_one (by exact_mod_cast he)
  have hpm : ((p : Nat.Primes) : ℂ)-1 ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast p.val.property.ne_one)
  unfold criticalIntegerBase ramanujanTorsionIndicator
  push_cast
  by_cases h0 : a.val.factorization p=0
  · simp [h0,complexCoefficient,hd,hpow]
  by_cases h1 : a.val.factorization p=1
  · simp [h1,complexCoefficient,hd,hpow]
    field_simp [hpm]
  have h2 : 2 ≤ a.val.factorization p := by omega
  have hz : (a.val.factorization p : ℤ)-2 ≠ -1 := by omega
  simp [complexCoefficient,hz,hd,hpow,h2,
    show 1 ≤ a.val.factorization p by omega]

theorem criticalGridRational_tag (P : Finset Nat.Primes) (a : ℕ+) (p : P) :
    (1-cubicPrimeBase p 1)*cubicPrimeBase p 1*complexCoefficient (cubicPrimeBase p 1)
      (positiveRationalValuations (criticalGridRational P a) p+1)=
      (criticalIntegerTag p a.val : ℂ) := by
  rw [criticalGridRational_valuation,base_one]
  have hpow (k : ℕ) : ((p : Nat.Primes) : ℕ)^k ∣ a.val ↔ k ≤ a.val.factorization p :=
    p.val.property.pow_dvd_iff_le_factorization a.property.ne'
  have hd : ((p : Nat.Primes) : ℕ) ∣ a.val ↔ 1 ≤ a.val.factorization p := by simpa using hpow 1
  have hp0 : ((p : Nat.Primes) : ℂ) ≠ 0 := by exact_mod_cast p.val.property.ne_zero
  have hp1 : (1 : ℂ)-((p : Nat.Primes) : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have he : ((p : Nat.Primes) : ℂ)=1 := by
      have he := congrArg Inv.inv h
      simpa using he.symm
    exact p.val.property.ne_one (by exact_mod_cast he)
  have hpm : ((p : Nat.Primes) : ℂ)-1 ≠ 0 := sub_ne_zero.mpr
    (by exact_mod_cast p.val.property.ne_one)
  unfold criticalIntegerTag ramanujanTorsionIndicator
  push_cast
  by_cases h0 : a.val.factorization p=0
  · simp [h0,complexCoefficient,hd]
    field_simp [hpm]
  · have h1 : 1 ≤ a.val.factorization p := by omega
    have hnn : (0 : ℤ) ≤ (a.val.factorization p : ℤ)-2+1 := by omega
    simp [complexCoefficient,show (a.val.factorization p : ℤ)-2+1 ≠ -1 by omega,hnn,hd,h1]
    ring

def criticalIntegerSource (P : Finset Nat.Primes) (n : ℕ) : ℝ :=
  ∑ p : P, Real.log ((p : Nat.Primes) : ℝ)*
    ∏ q : P, if q=p then criticalIntegerTag q n else criticalIntegerBase q n

theorem criticalGridRational_label (P : Finset Nat.Primes) (a : ℕ+) (p : P) :
    criticalRationalLabelCoefficient P p (criticalGridRational P a)=
      (Real.log ((p : Nat.Primes) : ℝ) : ℂ)*
        ∏ q : P, if q=p then (criticalIntegerTag q a.val : ℂ) else (criticalIntegerBase q a.val : ℂ) := by
  have hloc (q : P) :
      (if q=p then (criticalIntegerTag q a.val : ℂ) else (criticalIntegerBase q a.val : ℂ))=
      (if q=p then cubicPrimeBase q 1 else 1)*
        ((1-cubicPrimeBase q 1)*complexCoefficient (cubicPrimeBase q 1)
          (positiveRationalValuations (criticalGridRational P a) q+criticalLabelShift p q)) := by
    by_cases h : q=p
    · subst q
      rw [if_pos rfl,if_pos rfl,← criticalGridRational_tag]
      simp only [criticalLabelShift,if_true]
      ring
    · rw [if_neg h,if_neg h,← criticalGridRational_base]
      simp [criticalLabelShift,h]
  simp_rw [hloc]
  rw [Finset.prod_mul_distrib,Finset.prod_ite_eq',if_pos (Finset.mem_univ p),Finset.prod_mul_distrib]
  unfold criticalRationalLabelCoefficient criticalPrimeNormalization criticalPrimeLabelWeight
  simp only [base_one]
  push_cast
  simp only [one_div]
  ring

theorem criticalGridRational_source (P : Finset Nat.Primes) (a : ℕ+) :
    (∑ p : P, criticalRationalLabelCoefficient P p (criticalGridRational P a))=
      (criticalIntegerSource P a.val : ℂ) := by
  simp only [criticalGridRational_label,criticalIntegerSource,Complex.ofReal_sum,Complex.ofReal_mul,
    Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  split_ifs <;> rfl

private lemma prod_prime_image (P : Finset Nat.Primes) (f : ℕ → ℝ) :
    (∏ p : P, f p)=∏ p ∈ criticalPrimeImage P, f p := by
  rw [Finset.prod_coe_sort P (fun p : Nat.Primes => f p),criticalPrimeImage,Finset.prod_image]
  intro p hp q hq he
  exact Subtype.ext he

private lemma sum_prime_image (P : Finset Nat.Primes) (f : ℕ → ℝ) :
    (∑ p : P, f p)=∑ p ∈ criticalPrimeImage P, f p := by
  rw [Finset.sum_coe_sort P (fun p : Nat.Primes => f p),criticalPrimeImage,Finset.sum_image]
  intro p hp q hq he
  exact Subtype.ext he

private lemma integer_label_product (P : Finset Nat.Primes) (n : ℕ) (p : P) :
    (∏ q : P, if q=p then criticalIntegerTag q n else criticalIntegerBase q n)=
      criticalIntegerTag p n*∏ q ∈ (criticalPrimeImage P).erase p.val.val, criticalIntegerBase q n := by
  have he (q : P) : q=p ↔ ((q : Nat.Primes) : ℕ)=((p : Nat.Primes) : ℕ) := by
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext (Subtype.ext h)
  simp_rw [he]
  rw [prod_prime_image P (fun q : ℕ => if q=p.val.val then criticalIntegerTag q n else criticalIntegerBase q n),← Finset.mul_prod_erase _ _
    (show ((p : Nat.Primes) : ℕ) ∈ criticalPrimeImage P from Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩)]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [if_neg (Finset.mem_erase.mp hq).1]

private lemma torsion_mod {Q d : ℕ} (hd : d ∣ Q) (n : ℕ) :
    ramanujanTorsionIndicator d (n : ZMod Q).val=ramanujanTorsionIndicator d n := by
  have he : d ∣ (n : ZMod Q).val ↔ d ∣ n := by
    rw [ZMod.val_natCast,Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero,Nat.mod_mod_of_dvd n hd]
  simp only [ramanujanTorsionIndicator,he]

theorem criticalIntegerSource_grid (P : Finset Nat.Primes) (n : ℕ) :
    criticalIntegerSource P n=
      ramanujanCriticalGridWeight (criticalPrimeImage P)
        (n : ZMod (ramanujanGridModulus (criticalPrimeImage P))) := by
  unfold criticalIntegerSource
  simp_rw [integer_label_product]
  rw [sum_prime_image P (fun p : ℕ => Real.log p*
    (criticalIntegerTag p n*∏ q ∈ (criticalPrimeImage P).erase p, criticalIntegerBase q n)),
    ramanujanCriticalGridWeight,image_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hsquare (q : ℕ) (hq : q ∈ criticalPrimeImage P) :
      q^2 ∣ ramanujanGridModulus (criticalPrimeImage P) := by
    unfold ramanujanGridModulus ramanujanPrimeRadical
    rw [image_filter]
    exact pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ hq) 2
  have hprime (q : ℕ) (hq : q ∈ criticalPrimeImage P) :
      q ∣ ramanujanGridModulus (criticalPrimeImage P) :=
    (dvd_pow_self q (by omega : 2 ≠ 0)).trans (hsquare q hq)
  rw [torsion_mod (hprime p hp)]
  unfold criticalIntegerTag
  rw [mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [torsion_mod (hsquare q (Finset.mem_erase.mp hq).2),torsion_mod (hprime q (Finset.mem_erase.mp hq).2)]
  rfl

/-- Every positive lift of every literal finite grid node has precisely the
rational distinguished-source mass, including the zero residue class. -/
theorem criticalGridRational_actualMass (P : Finset Nat.Primes) (a : ℕ+) :
    (∑ p : P, criticalRationalLabelCoefficient P p (criticalGridRational P a))=
      ∑ b : RamanujanPrimeOnlyAtomIndex (criticalPrimeImage P),
        if ramanujanCriticalGridIndex b=(a.val : ZMod (ramanujanGridModulus (criticalPrimeImage P)))
          then (ramanujanCriticalPrimeAtomWeight (criticalPrimeImage P) b : ℂ) else 0 := by
  rw [criticalGridRational_source,criticalIntegerSource_grid,ramanujanCriticalPrimeAtomWeight_grid]

/-- No distinguished rational coefficient survives outside the actual
prime-square grid; arbitrary numerator factors remain unrestricted. -/
theorem criticalRationalLabelCoefficient_off_grid (P : Finset Nat.Primes)
    (r : P) (q : DenominatorRational P) (hq : ¬q.val.val.den ∣ criticalPrimeLevel P^2) :
    criticalRationalLabelCoefficient P r q.val=0 := by
  have hn : ¬q.val.val.den.factorization ≤ (criticalPrimeLevel P^2).factorization :=
    fun h => hq ((Nat.factorization_le_iff_dvd q.val.val.den_ne_zero
      (pow_pos (level_pos P) 2).ne').mp h)
  change ¬∀ p, q.val.val.den.factorization p ≤ (criticalPrimeLevel P^2).factorization p at hn
  obtain ⟨l,hl⟩ := not_forall.mp hn
  have hl' : (criticalPrimeLevel P^2).factorization l < q.val.val.den.factorization l := lt_of_not_ge hl
  have hlp : l.Prime := by
    by_contra hp
    rw [Nat.factorization_eq_zero_of_not_prime q.val.val.den hp] at hl'
    omega
  have hld : l ∣ q.val.val.den := Nat.dvd_of_factorization_pos (by omega : q.val.val.den.factorization l ≠ 0)
  let p : P := ⟨⟨l,hlp⟩,q.property ⟨l,hlp⟩ hld⟩
  have hf : (criticalPrimeLevel P^2).factorization l=2 := by
    change (criticalPrimeLevel P^2).factorization p=2
    simp only [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul,level_factorization,mul_one]
  rw [hf] at hl'
  have hnum : ¬l ∣ q.val.val.num.natAbs := fun h =>
    Nat.not_coprime_of_dvd_of_dvd hlp.one_lt h hld q.val.val.reduced
  have hv : positiveRationalValuations q.val p < -2 := by
    change (q.val.val.num.natAbs.factorization l : ℤ)-(q.val.val.den.factorization l : ℤ) < -2
    rw [Nat.factorization_eq_zero_of_not_dvd hnum]
    omega
  have hs : criticalLabelShift r p ≤ 1 := by
    unfold criticalLabelShift
    split_ifs <;> omega
  unfold criticalRationalLabelCoefficient
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  rw [complexCoefficient,if_neg (by omega),if_neg (by omega)]

theorem criticalGridRational_exists (P : Finset Nat.Primes) (q : PositiveRational)
    (hq : q.val.den ∣ criticalPrimeLevel P^2) :
    ∃ a : ℕ+, criticalGridRational P a=q := by
  let Q := criticalPrimeLevel P^2
  let k := Q/q.val.den
  have hQ : 0 < Q := pow_pos (level_pos P) 2
  have hd : 0 < q.val.den := Nat.pos_of_ne_zero q.val.den_ne_zero
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd hQ hq) hd
  have hn : 0 < q.val.num.natAbs := by
    apply Nat.pos_of_ne_zero
    intro h
    exact (Rat.num_pos.mpr q.property).ne' (Int.natAbs_eq_zero.mp h)
  let a : ℕ+ := ⟨q.val.num.natAbs*k,mul_pos hn hk⟩
  refine ⟨a,Subtype.ext ?_⟩
  have hnum : (q.val.num.natAbs : ℚ)=(q.val.num : ℚ) := by
    have h : (q.val.num.natAbs : ℤ)=q.val.num := by
      rw [Int.natCast_natAbs,abs_of_nonneg (Rat.num_nonneg.mpr q.property.le)]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) h
  have hkQ : k*q.val.den=Q := Nat.div_mul_cancel hq
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd0 : (q.val.den : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  change ((q.val.num.natAbs*k : ℕ) : ℚ)/(Q : ℚ)=q.val
  calc
    _ = (q.val.num.natAbs : ℚ)/(q.val.den : ℚ) := by
      rw [← hkQ]
      push_cast
      field_simp
    _ = q.val := by rw [hnum]; exact q.val.num_div_den

/-- Every nonzero rational distinguished coefficient lies on the literal
finite denominator grid, with all positive integer lifts retained. -/
theorem criticalRationalLabelCoefficient_support (P : Finset Nat.Primes)
    (r : P) (q : DenominatorRational P)
    (hq : criticalRationalLabelCoefficient P r q.val ≠ 0) :
    ∃ a : ℕ+, criticalGridRational P a=q.val := by
  apply criticalGridRational_exists
  by_contra hd
  exact hq (criticalRationalLabelCoefficient_off_grid P r q hd)

end RHTower.BAGTrace
