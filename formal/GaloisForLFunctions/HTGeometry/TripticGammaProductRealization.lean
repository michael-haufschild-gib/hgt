import GaloisForLFunctions.HTGeometry.TripticSourceDivisorFinsupp

/-!
# Every finite integral divisor is realized by a gamma product in the class

A finite product of translated elliptic gamma functions with integer exponents is a member of the
multiplicative triptic class, and its orbital charge at a base point is the prescribed divisor
coefficient of that point's class: each translate contributes its exponent on its own class and
nothing elsewhere.

* `tripticOrbitCharge_one`, `tripticOrbitCharge_zpow`, `tripticOrbitCharge_finsetProd`;
* `tripticOrbitCharge_ellipticGammaConeTranslate_indicator`;
* `gammaDivisorSource`, `tripticMultiplicativeSource_gammaDivisorSource`,
  `tripticOrbitCharge_gammaDivisorSource`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {τ σ : ℂ}

/-! ### The charge of the unit, of integer powers, and of finite products -/

theorem shiftOrder_one (σ w : ℂ) : shiftOrder (fun _ : ℂ ↦ (1 : ℂ)) σ w = 0 := by
  classical
  have hone : ∀ u : ℂ, meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) u = 0 := by
    intro u
    rw [meromorphicOrderAt_const]
    simp
  simp [shiftOrder, hone]

theorem tripticOrbitCharge_one (σ p : ℂ) :
    tripticOrbitCharge (fun _ : ℂ ↦ (1 : ℂ)) σ p = 0 := by
  rw [tripticOrbitCharge]
  exact finsum_eq_zero_of_forall_eq_zero fun m ↦ shiftOrder_one σ _

theorem finiteShiftSupport_one (σ p : ℂ) :
    FiniteShiftSupport (fun _ : ℂ ↦ (1 : ℂ)) σ p := by
  refine Set.Finite.subset Set.finite_empty fun m hm ↦ ?_
  simp only [Set.mem_setOf_eq] at hm
  exact absurd (shiftOrder_one σ _) hm

/-- **The orbital charge of an integer power is the multiple of the charge.** -/
theorem tripticOrbitCharge_zpow {Y : ℂ → ℂ} {Cst : ℂ}
    (hY : TripticMultiplicativeSource τ σ Y Cst) (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ)
    (n : ℤ) (p : ℂ) :
    tripticOrbitCharge (fun z ↦ Y z ^ n) σ p = n * tripticOrbitCharge Y σ p := by
  cases n with
  | ofNat k =>
      have hfun : (fun z : ℂ ↦ Y z ^ (Int.ofNat k : ℤ)) = fun z : ℂ ↦ Y z ^ k := by
        funext z
        simp
      rw [hfun, tripticOrbitCharge_pow hY.mero hY.finOrd k]
      simp
  | negSucc k =>
      have hfun : (fun z : ℂ ↦ Y z ^ (Int.negSucc k)) = fun z : ℂ ↦ 1 / Y z ^ (k + 1) := by
        funext z
        rw [zpow_negSucc, one_div]
      have hpow := hY.pow (k + 1)
      rw [hfun, tripticOrbitCharge_div (fun z _ ↦ analyticAt_const.meromorphicAt) hpow.mero
        (by
          intro w
          classical
          rw [meromorphicOrderAt_const]
          simp) hpow.finOrd (finiteShiftSupport_one σ p)
        (finiteShiftSupport_of_source hpow hτ hindep p),
        tripticOrbitCharge_one σ p, tripticOrbitCharge_pow hY.mero hY.finOrd (k + 1)]
      rw [Int.negSucc_eq]
      push_cast
      ring

/-- **The class is closed under finite pointwise products**, with the mixed constants adding. -/
theorem TripticMultiplicativeSource.finsetProd {ι : Type*} (s : Finset ι)
    {f : ι → ℂ → ℂ} {C : ι → ℂ}
    (h : ∀ i ∈ s, TripticMultiplicativeSource τ σ (f i) (C i)) :
    TripticMultiplicativeSource τ σ (fun z ↦ ∏ i ∈ s, f i z) (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tripticMultiplicativeSource_one τ σ
  | insert a s ha ih =>
      have hfun : (fun z : ℂ ↦ ∏ i ∈ insert a s, f i z)
          = fun z : ℂ ↦ f a z * ∏ i ∈ s, f i z := by
        funext z
        rw [Finset.prod_insert ha]
      rw [hfun, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- **The orbital charge of a finite product of class members is the sum of the charges.** -/
theorem tripticOrbitCharge_finsetProd {ι : Type*} (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ)
    (s : Finset ι) {f : ι → ℂ → ℂ} {C : ι → ℂ}
    (h : ∀ i ∈ s, TripticMultiplicativeSource τ σ (f i) (C i)) (p : ℂ) :
    tripticOrbitCharge (fun z ↦ ∏ i ∈ s, f i z) σ p
      = ∑ i ∈ s, tripticOrbitCharge (f i) σ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hfun : (fun z : ℂ ↦ ∏ i ∈ (∅ : Finset ι), f i z) = fun _ : ℂ ↦ (1 : ℂ) := by
        funext z
        simp
      rw [hfun]
      simpa using tripticOrbitCharge_one σ p
  | insert a s ha ih =>
      have ha' := h a (Finset.mem_insert_self a s)
      have hrest := TripticMultiplicativeSource.finsetProd s
        (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
      have hfun : (fun z : ℂ ↦ ∏ i ∈ insert a s, f i z)
          = fun z : ℂ ↦ f a z * ∏ i ∈ s, f i z := by
        funext z
        rw [Finset.prod_insert ha]
      rw [hfun, Finset.sum_insert ha,
        tripticOrbitCharge_mul ha'.mero hrest.mero ha'.finOrd hrest.finOrd
          (finiteShiftSupport_of_source ha' hτ hindep p)
          (finiteShiftSupport_of_source hrest hτ hindep p),
        ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))]

/-! ### The charge of a translate at an arbitrary base point -/

/-- The orbital charge of a translate is the charge of the elliptic gamma at the translated base
point. -/
theorem tripticOrbitCharge_ellipticGammaConeTranslate_eq (g p : ℂ) :
    tripticOrbitCharge (ellipticGammaConeTranslate τ σ g) σ p
      = tripticOrbitCharge (ellipticGammaCone τ σ) σ (p - g) := by
  rw [tripticOrbitCharge, tripticOrbitCharge]
  refine finsum_congr fun m ↦ ?_
  rw [shiftOrder_ellipticGammaConeTranslate]
  congr 1
  ring

/-- **A gamma translate charges its own class with weight one.** -/
theorem tripticOrbitCharge_ellipticGammaConeTranslate_of_mem
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ) {g p : ℂ}
    (hmem : PeriodGroupMem τ σ (p - g)) :
    tripticOrbitCharge (ellipticGammaConeTranslate τ σ g) σ p = 1 := by
  obtain ⟨c, d, e, hcde⟩ := hmem
  rw [tripticOrbitCharge_ellipticGammaConeTranslate_eq, hcde]
  exact tripticOrbitCharge_ellipticGammaCone_periodPoint hτ hσ hindep c d e

/-- **A gamma translate charges no other class.** -/
theorem tripticOrbitCharge_ellipticGammaConeTranslate_of_notMem
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) {g p : ℂ}
    (hmem : ¬ PeriodGroupMem τ σ (p - g)) :
    tripticOrbitCharge (ellipticGammaConeTranslate τ σ g) σ p = 0 := by
  rw [tripticOrbitCharge_ellipticGammaConeTranslate_eq]
  exact tripticOrbitCharge_ellipticGammaCone_of_notMem hτ hσ hmem

/-! ### The realizing gamma product of a prescribed divisor -/

/-- **The gamma product realizing a prescribed finite integral divisor**: one translated elliptic
gamma factor per charged class, with the divisor coefficient as integer exponent. -/
def gammaDivisorSource (τ σ : ℂ) (E : (ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ) : ℂ → ℂ :=
  fun z ↦ ∏ g ∈ E.support, ellipticGammaConeTranslate τ σ (Quotient.out g) z ^ (E g)

/-- **The realizing gamma product is a member of the class.** -/
theorem tripticMultiplicativeSource_gammaDivisorSource (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (E : (ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ) :
    TripticMultiplicativeSource τ σ (gammaDivisorSource τ σ E)
      (∑ g ∈ E.support, (E g : ℂ) * -(2 * (Real.pi : ℂ) * Complex.I)) :=
  TripticMultiplicativeSource.finsetProd E.support fun g _ ↦
    (tripticMultiplicativeSource_ellipticGammaConeTranslate hτ hσ (Quotient.out g)).zpow (E g)

/-- Membership in the period group of a difference against a chosen representative is equality of
classes. -/
theorem periodGroupMem_sub_out_iff (p : ℂ) (g : ℂ ⧸ tripticPeriodGroup τ σ) :
    PeriodGroupMem τ σ (p - Quotient.out g) ↔ QuotientAddGroup.mk p = g := by
  constructor
  · intro hmem
    have h0 : p - Quotient.out g ∈ tripticPeriodGroup τ σ := hmem
    have hmem' : -p + Quotient.out g ∈ tripticPeriodGroup τ σ := by
      have hneg := neg_mem (s := tripticPeriodGroup τ σ) h0
      rwa [neg_sub, sub_eq_add_neg, add_comm] at hneg
    calc (QuotientAddGroup.mk p : ℂ ⧸ tripticPeriodGroup τ σ)
        = QuotientAddGroup.mk (Quotient.out g) := (QuotientAddGroup.eq).mpr hmem'
      _ = g := QuotientAddGroup.out_eq' g
  · intro hclass
    have hmem' : -p + Quotient.out g ∈ tripticPeriodGroup τ σ :=
      (QuotientAddGroup.eq).mp (hclass.trans (QuotientAddGroup.out_eq' g).symm)
    have hneg := neg_mem (s := tripticPeriodGroup τ σ) hmem'
    have h0 : p - Quotient.out g ∈ tripticPeriodGroup τ σ := by
      rwa [neg_add_rev, neg_neg, add_comm, ← sub_eq_add_neg] at hneg
    exact h0

/-- **The realizing gamma product has exactly the prescribed divisor**: its orbital charge at any
base point is the divisor coefficient of that point's class. -/
theorem tripticOrbitCharge_gammaDivisorSource (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : IndepPeriods τ σ) (E : (ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ) (p : ℂ) :
    tripticOrbitCharge (gammaDivisorSource τ σ E) σ p = E (QuotientAddGroup.mk p) := by
  classical
  have hfun : gammaDivisorSource τ σ E
      = fun z ↦ ∏ g ∈ E.support, ellipticGammaConeTranslate τ σ (Quotient.out g) z ^ (E g) :=
    rfl
  rw [hfun, tripticOrbitCharge_finsetProd hτ hindep E.support
    (fun g _ ↦ (tripticMultiplicativeSource_ellipticGammaConeTranslate hτ hσ
      (Quotient.out g)).zpow (E g)) p]
  have hterm : ∀ g ∈ E.support,
      tripticOrbitCharge
        (fun z ↦ ellipticGammaConeTranslate τ σ (Quotient.out g) z ^ (E g)) σ p
      = if QuotientAddGroup.mk p = g then E g else 0 := by
    intro g hg
    rw [tripticOrbitCharge_zpow
      (tripticMultiplicativeSource_ellipticGammaConeTranslate hτ hσ (Quotient.out g))
      hτ hindep (E g) p]
    by_cases hclass : QuotientAddGroup.mk p = g
    · rw [tripticOrbitCharge_ellipticGammaConeTranslate_of_mem hτ hσ hindep
        ((periodGroupMem_sub_out_iff p g).mpr hclass), if_pos hclass, mul_one]
    · rw [tripticOrbitCharge_ellipticGammaConeTranslate_of_notMem hτ hσ
        (fun hmem ↦ hclass ((periodGroupMem_sub_out_iff p g).mp hmem)), if_neg hclass, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq E.support (QuotientAddGroup.mk p) E]
  by_cases hsupp : (QuotientAddGroup.mk p : ℂ ⧸ tripticPeriodGroup τ σ) ∈ E.support
  · rw [if_pos hsupp]
  · rw [if_neg hsupp, (Finsupp.notMem_support_iff.mp hsupp)]

end

end GaloisForLFunctions.HTGeometry
