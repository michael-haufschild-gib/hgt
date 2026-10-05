import GaloisForLFunctions.RHTower.ChiRamanujanCofactorPole
import GaloisForLFunctions.RHTower.ChiRamanujanPositiveRationalTrace

/-!
# Complete rational cone with unrestricted numerator cofactors

An explicit bijection separates retained-prime valuations from every positive
coprime numerator. The target consists exactly of positive rationals whose
denominator primes are retained. Both complex powers and the signed shifted
coefficient tensor are preserved. The resulting full rational-pair HasSum
includes arbitrary numerator primes and both physical label exclusions.

Matching the valuation-defined coefficient to every literal finite grid mass
and bounding the complete growing physical action remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

private lemma natural_nonneg (n : ℕ) (p : Nat.Primes) : 0 ≤ naturalValuations n p :=
  Int.natCast_nonneg _

private lemma natural_injective {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : naturalValuations m=naturalValuations n) : m=n := by
  have he := congrArg rationalOfValuations h
  rw [rationalOfValuations_natural hm,rationalOfValuations_natural hn] at he
  exact_mod_cast he

private lemma exists_natural (v : PrimeValuations) (hv : ∀ p, 0 ≤ v p) :
    ∃ n : ℕ, n ≠ 0 ∧ naturalValuations n=v := by
  let n := v.prod (fun p i => (p : ℕ)^i.toNat)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ p.property.ne_zero)
  refine ⟨n,hn,rationalOfValuations_injective ?_⟩
  rw [rationalOfValuations_natural hn]
  change ((v.prod (fun p i => (p : ℕ)^i.toNat) : ℕ) : ℚ)=v.prod (fun p i => (p : ℚ)^i)
  simp only [Finsupp.prod,Nat.cast_prod,Nat.cast_pow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← zpow_natCast]
  exact congrArg (fun i : ℤ => (p : ℚ)^i) (Int.toNat_of_nonneg (hv p))

private lemma natural_coprime_iff (P : Finset Nat.Primes) {n : ℕ} (hn : n ≠ 0) :
    n.Coprime (criticalPrimeLevel P) ↔ ∀ p ∈ P, naturalValuations n p=0 := by
  rw [criticalPrimeLevel,Nat.coprime_prod_right_iff]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [Nat.coprime_comm,p.property.coprime_iff_not_dvd,naturalValuations_apply]
  simp only [Int.natCast_eq_zero,Nat.factorization_eq_zero_iff,p.property,not_true_eq_false,
    hn,false_or,or_false]

abbrev CriticalNumerator (P : Finset Nat.Primes) :=
  {n : ℕ // n ≠ 0 ∧ n.Coprime (criticalPrimeLevel P)}

abbrev DenominatorValuations (P : Finset Nat.Primes) :=
  {v : PrimeValuations // ∀ p, p ∉ P → 0 ≤ v p}

def retainedValuations (P : Finset Nat.Primes) (v : P → ℤ) : PrimeValuations :=
  Finsupp.onFinset P (fun p => if hp : p ∈ P then v ⟨p,hp⟩ else 0)
    (by intro p hp; by_contra hn; exact hp (dif_neg hn))

theorem retainedValuations_apply (P : Finset Nat.Primes) (v : P → ℤ) (p : Nat.Primes) :
    retainedValuations P v p=(if hp : p ∈ P then v ⟨p,hp⟩ else 0) := rfl

def mixedValuations (P : Finset Nat.Primes) (w : (P → ℤ) × CriticalNumerator P) :
    DenominatorValuations P :=
  ⟨retainedValuations P w.1+naturalValuations w.2.val,by
    intro p hp
    simpa only [Finsupp.add_apply,retainedValuations_apply,dif_neg hp,zero_add] using
      natural_nonneg w.2.val p⟩

theorem mixedValuations_retained (P : Finset Nat.Primes)
    (w : (P → ℤ) × CriticalNumerator P) (p : P) :
    (mixedValuations P w).val p=w.1 p := by
  change retainedValuations P w.1 p+naturalValuations w.2.val p=w.1 p
  rw [(natural_coprime_iff P w.2.property.1).mp w.2.property.2 p p.property]
  simp [retainedValuations_apply]

theorem mixedValuations_outside (P : Finset Nat.Primes)
    (w : (P → ℤ) × CriticalNumerator P) (p : Nat.Primes) (hp : p ∉ P) :
    (mixedValuations P w).val p=naturalValuations w.2.val p := by
  simp [mixedValuations,retainedValuations_apply,hp]

theorem mixedValuations_injective (P : Finset Nat.Primes) : Function.Injective (mixedValuations P) := by
  intro v w h
  have hi : v.1=w.1 := by
    funext p
    have he := congrArg (fun u : DenominatorValuations P => u.val p) h
    simpa only [mixedValuations_retained] using he
  have hn : v.2=w.2 := by
    apply Subtype.ext
    apply natural_injective v.2.property.1 w.2.property.1
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ P
    · rw [(natural_coprime_iff P v.2.property.1).mp v.2.property.2 p hp,
        (natural_coprime_iff P w.2.property.1).mp w.2.property.2 p hp]
    · have he := congrArg (fun u : DenominatorValuations P => u.val p) h
      simpa only [mixedValuations_outside P _ p hp] using he
  exact Prod.ext hi hn

theorem mixedValuations_surjective (P : Finset Nat.Primes) : Function.Surjective (mixedValuations P) := by
  intro v
  let u := v.val.filter (fun p => p ∉ P)
  have hu : ∀ p, 0 ≤ u p := by
    intro p
    by_cases hp : p ∈ P
    · simp [u,hp]
    · simpa only [u,Finsupp.filter_apply,if_pos hp] using v.property p hp
  obtain ⟨n,hn,he⟩ := exists_natural u hu
  have hc : n.Coprime (criticalPrimeLevel P) := by
    apply (natural_coprime_iff P hn).mpr
    intro p hp
    rw [he]
    simp [u,hp]
  refine ⟨(fun p => v.val p,⟨n,hn,hc⟩),?_⟩
  apply Subtype.ext
  apply Finsupp.ext
  intro p
  change retainedValuations P (fun p => v.val p) p+naturalValuations n p=v.val p
  rw [he]
  by_cases hp : p ∈ P <;> simp [retainedValuations_apply,u,hp]

def mixedValuationsEquiv (P : Finset Nat.Primes) :
    ((P → ℤ) × CriticalNumerator P) ≃ DenominatorValuations P :=
  Equiv.ofBijective (mixedValuations P) ⟨mixedValuations_injective P,mixedValuations_surjective P⟩


abbrev DenominatorRational (P : Finset Nat.Primes) :=
  {q : PositiveRational // ∀ p : Nat.Primes, (p : ℕ) ∣ q.val.den → p ∈ P}

theorem denominatorValuations_iff (P : Finset Nat.Primes) (q : PositiveRational) :
    (∀ p, p ∉ P → 0 ≤ positiveRationalValuations q p) ↔
      ∀ p : Nat.Primes, (p : ℕ) ∣ q.val.den → p ∈ P := by
  constructor
  · intro h p hp
    by_contra hn
    have hc : ¬ (p : ℕ) ∣ q.val.num.natAbs := fun hd =>
      Nat.not_coprime_of_dvd_of_dvd p.property.one_lt hd hp q.val.reduced
    have he := h p hn
    have hd := p.property.factorization_pos_of_dvd q.val.den_ne_zero hp
    simp only [positiveRationalValuations,Finsupp.sub_apply,naturalValuations_apply,
      Nat.factorization_eq_zero_of_not_dvd hc,Int.natCast_zero,zero_sub] at he
    omega
  · intro h p hp
    have hd : ¬ (p : ℕ) ∣ q.val.den := fun hd => hp (h p hd)
    simp only [positiveRationalValuations,Finsupp.sub_apply,naturalValuations_apply,
      Nat.factorization_eq_zero_of_not_dvd hd,Int.natCast_zero,sub_zero]
    exact Int.natCast_nonneg _

def denominatorRationalEquiv (P : Finset Nat.Primes) :
    DenominatorValuations P ≃ DenominatorRational P where
  toFun v := ⟨positiveRationalEquiv v.val,(denominatorValuations_iff P _).mp
    (by simpa only [positiveRationalValuations_equiv] using v.property)⟩
  invFun q := ⟨positiveRationalValuations q.val,(denominatorValuations_iff P q.val).mpr q.property⟩
  left_inv v := Subtype.ext (positiveRationalValuations_equiv v.val)
  right_inv q := Subtype.ext (positiveRationalEquiv.right_inv q.val)

def mixedRationalEquiv (P : Finset Nat.Primes) :
    ((P → ℤ) × CriticalNumerator P) ≃ DenominatorRational P :=
  (mixedValuationsEquiv P).trans (denominatorRationalEquiv P)

theorem mixedRationalEquiv_valuations (P : Finset Nat.Primes)
    (w : (P → ℤ) × CriticalNumerator P) :
    positiveRationalValuations (mixedRationalEquiv P w).val=
      retainedValuations P w.1+naturalValuations w.2.val :=
  positiveRationalValuations_equiv _

theorem mixedRationalEquiv_value (P : Finset Nat.Primes)
    (w : (P → ℤ) × CriticalNumerator P) :
    (mixedRationalEquiv P w).val.val=
      (w.2.val : ℚ)*∏ p : P, ((p : Nat.Primes) : ℚ)^(w.1 p) := by
  change rationalOfValuations (retainedValuations P w.1+naturalValuations w.2.val)=_
  rw [rationalOfValuations_add,rationalOfValuations_natural w.2.property.1,mul_comm]
  congr 1
  have hp : (retainedValuations P w.1).support ⊆ P := Finsupp.support_onFinset_subset
  rw [rationalOfValuations,(retainedValuations P w.1).prod_of_support_subset hp _
    (fun p _ => zpow_zero (p : ℚ)),
    ← Finset.prod_coe_sort P (fun p : Nat.Primes => (p : ℚ)^(retainedValuations P w.1 p))]
  apply Finset.prod_congr rfl
  intro p hp
  simp [retainedValuations_apply]

theorem mixedRationalEquiv_retained (P : Finset Nat.Primes)
    (w : (P → ℤ) × CriticalNumerator P) (p : P) :
    positiveRationalValuations (mixedRationalEquiv P w).val p=w.1 p := by
  rw [mixedRationalEquiv_valuations]
  exact mixedValuations_retained P w p

theorem mixedRationalEquiv_character (P : Finset Nat.Primes)
    (w : (P → ℤ) × CriticalNumerator P) (s : ℂ) :
    rationalCharacter s (mixedRationalEquiv P w).val=
      (∏ p : P, cubicPrimeBase p s^(w.1 p))*(w.2.val : ℂ)^(-s) := by
  change (rationalOfValuations (retainedValuations P w.1+naturalValuations w.2.val) : ℂ)^(-s)=_
  rw [cpow_rationalOfValuations,Finsupp.prod_add_index'
    (fun p => zpow_zero (cubicPrimeBase p s))
    (fun p i j => zpow_add₀ (cubicPrimeBase_ne_zero p s) i j)]
  congr 1
  · have hp : (retainedValuations P w.1).support ⊆ P := Finsupp.support_onFinset_subset
    rw [(retainedValuations P w.1).prod_of_support_subset hp _ (fun p _ => zpow_zero _),
      ← Finset.prod_coe_sort P (fun p : Nat.Primes => cubicPrimeBase p s^(retainedValuations P w.1 p))]
    apply Finset.prod_congr rfl
    intro p hp
    simp [retainedValuations_apply]
  · rw [← cpow_rationalOfValuations,rationalOfValuations_natural w.2.property.1]
    norm_cast

private def mixedPairPacking (P : Finset Nat.Primes) :
    ((P → ℤ × ℤ) × (CriticalNumerator P × CriticalNumerator P)) ≃
      (((P → ℤ) × CriticalNumerator P) × ((P → ℤ) × CriticalNumerator P)) where
  toFun w := ((fun p => (w.1 p).1,w.2.1),(fun p => (w.1 p).2,w.2.2))
  invFun w := (fun p => (w.1.1 p,w.2.1 p),(w.1.2,w.2.2))
  left_inv w := by
    apply Prod.ext
    · funext p
      rfl
    · rfl
  right_inv w := rfl

def mixedRationalPairEquiv (P : Finset Nat.Primes) :
    ((P → ℤ × ℤ) × (CriticalNumerator P × CriticalNumerator P)) ≃
      (DenominatorRational P × DenominatorRational P) :=
  (mixedPairPacking P).trans ((mixedRationalEquiv P).prodCongr (mixedRationalEquiv P))

def criticalRationalLabelCoefficient (P : Finset Nat.Primes) (p : P) (q : PositiveRational) : ℂ :=
  ((criticalPrimeNormalization P*criticalPrimeLabelWeight p : ℝ) : ℂ)*
    ∏ ℓ : P, complexCoefficient (cubicPrimeBase ℓ 1)
      (positiveRationalValuations q ℓ+criticalLabelShift p ℓ)

def criticalRationalLabelCone (P : Finset Nat.Primes) (p q r : P) (s t : ℂ)
    (w : PositiveRational × PositiveRational) : ℂ :=
  criticalRationalLabelCoefficient P p w.1*criticalRationalLabelCoefficient P q w.2*
    criticalRationalLabelCoefficient P r ⟨w.1.val*w.2.val,mul_pos w.1.property w.2.property⟩*
      rationalCharacter s w.1*rationalCharacter t w.2

private lemma rational_label_equiv (P : Finset Nat.Primes) (p q r : P) (s t : ℂ)
    (w : (P → ℤ × ℤ) × (CriticalNumerator P × CriticalNumerator P)) :
    criticalRationalLabelCone P p q r s t
      ((mixedRationalPairEquiv P w).1.val,(mixedRationalPairEquiv P w).2.val)=
      criticalWeightedLabelCone P p q r s t w.1*
        ((w.2.1.val : ℂ)^(-s)*(w.2.2.val : ℂ)^(-t)) := by
  change criticalRationalLabelCone P p q r s t
    ((mixedRationalEquiv P (fun p => (w.1 p).1,w.2.1)).val,
      (mixedRationalEquiv P (fun p => (w.1 p).2,w.2.2)).val)=_
  unfold criticalRationalLabelCone
  simp only [mixedRationalEquiv_character,criticalRationalLabelCoefficient,
    positiveRationalValuations_mul,Finsupp.add_apply,mixedRationalEquiv_retained]
  unfold criticalWeightedLabelCone weightedShiftedLocal
  simp only [Finset.prod_mul_distrib]
  push_cast
  ring

def criticalRationalCone (P : Finset Nat.Primes) (s t : ℂ)
    (w : DenominatorRational P × DenominatorRational P) : ℂ :=
  ∑ r : P, ∑ p : P, ∑ q : P, if p=r ∨ q=r then 0 else
    criticalRationalLabelCone P p q r s t (w.1.val,w.2.val)

theorem criticalRationalCone_equiv (P : Finset Nat.Primes) (s t : ℂ)
    (w : (P → ℤ × ℤ) × (CriticalNumerator P × CriticalNumerator P)) :
    criticalRationalCone P s t (mixedRationalPairEquiv P w)=
      criticalWeightedCone P s t w.1*
        ((w.2.1.val : ℂ)^(-s)*(w.2.2.val : ℂ)^(-t)) := by
  unfold criticalRationalCone criticalWeightedCone
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : p=r ∨ q=r
  · simp only [if_pos h,zero_mul]
  · simp only [if_neg h]
    exact rational_label_equiv P p q r s t w

private lemma numerator_hasSum (P : Finset Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : CriticalNumerator P => (n.val : ℂ)^(-s)) (criticalCofactor P s) := by
  have hsupport : Function.support (criticalCofactorTerm P s) ⊆
      {n | n ≠ 0 ∧ n.Coprime (criticalPrimeLevel P)} := by
    intro n hn
    by_contra h
    have he : n=0 ∨ ¬n.Coprime (criticalPrimeLevel P) := by tauto
    exact hn (by rw [criticalCofactorTerm_eq,if_pos he])
  have h := (hasSum_subtype_iff_of_support_subset hsupport).mpr (criticalCofactor_hasSum P hs)
  apply h.congr_fun
  intro n
  simp only [Function.comp_apply,criticalCofactorTerm_eq]
  rw [if_neg (not_or.mpr ⟨n.property.1,not_not.mpr n.property.2⟩)]

private lemma rational_mul_hasSum {X Y : Type} {f : X → ℂ} {g : Y → ℂ} {a b : ℂ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun w : X × Y => f w.1*g w.2) (a*b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

/-- Every positive rational pair with denominator primes retained is included;
no restriction is placed on either numerator. -/
theorem criticalRationalCone_hasSum (P : Finset Nat.Primes) {s t : ℂ}
    (hs : 1 < s.re) (ht : 1 < t.re) :
    HasSum (criticalRationalCone P s t) (criticalCompletedConeEuler P s t) := by
  have hn : HasSum
      (fun n : CriticalNumerator P × CriticalNumerator P => (n.1.val : ℂ)^(-s)*(n.2.val : ℂ)^(-t))
      (criticalCofactor P s*criticalCofactor P t) :=
    @rational_mul_hasSum (CriticalNumerator P) (CriticalNumerator P)
      (fun n => (n.val : ℂ)^(-s)) (fun n => (n.val : ℂ)^(-t))
      (criticalCofactor P s) (criticalCofactor P t) (numerator_hasSum P hs) (numerator_hasSum P ht)
  have h := @rational_mul_hasSum (P → ℤ × ℤ) (CriticalNumerator P × CriticalNumerator P)
    (criticalWeightedCone P s t)
    (fun n => (n.1.val : ℂ)^(-s)*(n.2.val : ℂ)^(-t))
    (criticalWeightedConeEuler P s t) (criticalCofactor P s*criticalCofactor P t)
    (criticalWeightedCone_hasSum P (zero_lt_one.trans hs) (zero_lt_one.trans ht)) hn
  exact (mixedRationalPairEquiv P).hasSum_iff.mp
    (h.congr_fun (fun w => criticalRationalCone_equiv P s t w))

end RHTower.BAGTrace
