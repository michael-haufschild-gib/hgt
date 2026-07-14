import Mathlib

open scoped BigOperators

namespace HTGeometry

noncomputable section

def finiteSignedFunctional {P : Type*} [Fintype P]
    (mu : P → ℝ) (f : P → ℝ) : ℝ :=
  ∑ p, mu p * f p

def finiteSignedFiberMass {P K : Type*} [Fintype P] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) (k : K) : ℝ :=
  ∑ p, if kappa p = k then mu p else 0

def finiteQuotientObservable {P K : Type*}
    (kappa : P → K) (f : K → ℝ) : P → ℝ :=
  fun p => f (kappa p)

theorem finiteSignedFunctional_quotient_eq_fiberMass
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) (f : K → ℝ) :
    finiteSignedFunctional mu (finiteQuotientObservable kappa f) =
      ∑ k, finiteSignedFiberMass mu kappa k * f k := by
  classical
  simp [finiteSignedFunctional, finiteSignedFiberMass, finiteQuotientObservable,
    Finset.sum_mul, Finset.sum_comm]

theorem finiteSignedFunctional_annihilates_quotient_iff
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) :
    (∀ f : K → ℝ,
        finiteSignedFunctional mu (finiteQuotientObservable kappa f) = 0) ↔
      ∀ k, finiteSignedFiberMass mu kappa k = 0 := by
  classical
  constructor
  · intro h k
    let delta : K → ℝ := fun x => if x = k then 1 else 0
    have hk := h delta
    rw [finiteSignedFunctional_quotient_eq_fiberMass] at hk
    simpa [delta] using hk
  · intro h f
    rw [finiteSignedFunctional_quotient_eq_fiberMass]
    simp [h]

theorem finiteSignedFiberMass_eq_single_of_injective
    {P K : Type*} [Fintype P] [DecidableEq K]
    (mu : P → ℝ) {kappa : P → K} (hkappa : Function.Injective kappa) (p : P) :
    finiteSignedFiberMass mu kappa (kappa p) = mu p := by
  classical
  rw [finiteSignedFiberMass]
  change (∑ q, if kappa q = kappa p then mu q else 0) = mu p
  calc
    _ = if kappa p = kappa p then mu p else 0 := by
      apply Finset.sum_eq_single p
      · intro q hq hqp
        simp only [ite_eq_right_iff]
        intro hqk
        exact (hqp (hkappa hqk)).elim
      · simp
    _ = mu p := by simp

theorem finiteSignedFiberMass_zero_injective_iff
    {P K : Type*} [Fintype P] [DecidableEq K]
    (mu : P → ℝ) {kappa : P → K} (hkappa : Function.Injective kappa) :
    (∀ k, finiteSignedFiberMass mu kappa k = 0) ↔ mu = 0 := by
  constructor
  · intro h
    funext p
    have hp := h (kappa p)
    rw [finiteSignedFiberMass_eq_single_of_injective mu hkappa p] at hp
    exact hp
  · rintro rfl k
    simp [finiteSignedFiberMass]

theorem exists_two_in_fiber_of_balanced_nonzero
    {P K : Type*} [Fintype P] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K)
    (hmu : ∀ p, mu p ≠ 0)
    (hbalance : ∀ k, finiteSignedFiberMass mu kappa k = 0)
    {k : K} (hk : k ∈ Set.range kappa) :
    ∃ p q, kappa p = k ∧ kappa q = k ∧ p ≠ q := by
  classical
  obtain ⟨p, hp⟩ := hk
  by_contra h
  push Not at h
  have hunique : ∀ q, kappa q = k → q = p := by
    intro q hq
    by_contra hqp
    exact hqp (h q p hq hp)
  have hmass : finiteSignedFiberMass mu kappa k = mu p := by
    rw [finiteSignedFiberMass]
    change (∑ q, if kappa q = k then mu q else 0) = mu p
    calc
      _ = if kappa p = k then mu p else 0 := by
        apply Finset.sum_eq_single p
        · intro q hq hqp
          simp only [ite_eq_right_iff]
          intro hqk
          exact (hqp (hunique q hqk)).elim
        · simp
      _ = mu p := by simp [hp]
  have hb := hbalance k
  rw [hmass] at hb
  exact hmu p hb

theorem twice_card_le_card_of_balanced_nonzero
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K)
    (hmu : ∀ p, mu p ≠ 0)
    (hkappa : Function.Surjective kappa)
    (hbalance : ∀ k, finiteSignedFiberMass mu kappa k = 0) :
    2 * Fintype.card K ≤ Fintype.card P := by
  classical
  have hpairs : ∀ k : K, ∃ p q, kappa p = k ∧ kappa q = k ∧ p ≠ q := by
    intro k
    exact exists_two_in_fiber_of_balanced_nonzero mu kappa hmu hbalance
      ⟨Classical.choose (hkappa k), Classical.choose_spec (hkappa k)⟩
  choose left right hleft hright hne using hpairs
  let embed : K × Bool → P := fun x => if x.2 then right x.1 else left x.1
  have hembed_fiber : ∀ x, kappa (embed x) = x.1 := by
    intro x
    cases hx : x.2 <;> simp [embed, hx, hleft, hright]
  have hembed : Function.Injective embed := by
    intro x y hxy
    have hfirst : x.1 = y.1 := by
      have := congrArg kappa hxy
      simpa only [hembed_fiber] using this
    rcases x with ⟨k, bx⟩
    rcases y with ⟨l, cy⟩
    change k = l at hfirst
    subst l
    cases bx <;> cases cy
    · rfl
    · have hbad : left k = right k := by simpa [embed] using hxy
      exact (hne k hbad).elim
    · have hbad : right k = left k := by simpa [embed] using hxy
      exact (hne k hbad.symm).elim
    · rfl
  have hcard := Fintype.card_le_of_injective embed hembed
  simpa [Fintype.card_prod, Nat.mul_comm] using hcard

def finiteSignedCharge {P : Type*} [Fintype P] (mu : P → ℝ) : ℝ :=
  ∑ p, mu p

def finiteSignedQuotientState {P K : Type*} [Fintype P]
    (mu : P → ℝ) (kappa : P → K) (f : K → ℝ) : ℝ :=
  finiteSignedFunctional mu (finiteQuotientObservable kappa f) /
    finiteSignedCharge mu

theorem finiteSignedCharge_eq_sum_fiberMass
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) :
    finiteSignedCharge mu = ∑ k, finiteSignedFiberMass mu kappa k := by
  simpa [finiteSignedCharge, finiteSignedFunctional, finiteQuotientObservable] using
    (finiteSignedFunctional_quotient_eq_fiberMass mu kappa (fun _ => 1))

theorem finiteSignedQuotientState_positive_iff
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) :
    (∀ f : K → ℝ, 0 ≤ finiteSignedQuotientState mu kappa (fun k => f k ^ 2)) ↔
      ∀ k, 0 ≤ finiteSignedFiberMass mu kappa k / finiteSignedCharge mu := by
  classical
  constructor
  · intro h k
    let delta : K → ℝ := fun x => if x = k then 1 else 0
    have hk := h delta
    rw [finiteSignedQuotientState, finiteSignedFunctional_quotient_eq_fiberMass] at hk
    simpa [delta] using hk
  · intro h f
    rw [finiteSignedQuotientState, finiteSignedFunctional_quotient_eq_fiberMass,
      Finset.sum_div]
    apply Finset.sum_nonneg
    intro k hk
    rw [← div_mul_eq_mul_div]
    exact mul_nonneg (h k) (sq_nonneg _)

/-- Total variation cannot increase under a finite observational quotient. -/
theorem sum_abs_finiteSignedFiberMass_le
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K) :
    (∑ k, |finiteSignedFiberMass mu kappa k|) ≤ ∑ p, |mu p| := by
  classical
  calc
    (∑ k, |finiteSignedFiberMass mu kappa k|) ≤
        ∑ k, ∑ p, |if kappa p = k then mu p else 0| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [finiteSignedFiberMass]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p, |mu p| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        (∑ x : K, |if kappa p = x then mu p else 0|) =
            ∑ x : K, if kappa p = x then |mu p| else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : kappa p = x <;> simp [h]
        _ = |mu p| := by simp

/-- A quotient whose normalized signed functional is positive has output total variation exactly
equal to the absolute conserved charge. Thus all excess variation of the signed source has been
erased by the quotient. -/
theorem sum_abs_finiteSignedFiberMass_eq_abs_charge_of_positive
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (mu : P → ℝ) (kappa : P → K)
    (hcharge : finiteSignedCharge mu ≠ 0)
    (hpositive : ∀ k,
      0 ≤ finiteSignedFiberMass mu kappa k / finiteSignedCharge mu) :
    (∑ k, |finiteSignedFiberMass mu kappa k|) = |finiteSignedCharge mu| := by
  rcases lt_or_gt_of_ne hcharge with hneg | hpos
  · have hnonpos : ∀ k, finiteSignedFiberMass mu kappa k ≤ 0 := by
      intro k
      rcases div_nonneg_iff.mp (hpositive k) with h | h
      · exact (not_le_of_gt hneg h.2).elim
      · exact h.1
    simp_rw [abs_of_nonpos (hnonpos _)]
    calc
      (∑ k, -finiteSignedFiberMass mu kappa k) =
          -(∑ k, finiteSignedFiberMass mu kappa k) := by
        simp
      _ = -finiteSignedCharge mu := by
        rw [← finiteSignedCharge_eq_sum_fiberMass mu kappa]
      _ = |finiteSignedCharge mu| := (abs_of_neg hneg).symm
  · have hnonneg : ∀ k, 0 ≤ finiteSignedFiberMass mu kappa k := by
      intro k
      rcases div_nonneg_iff.mp (hpositive k) with h | h
      · exact h.1
      · exact (not_le_of_gt hpos h.2).elim
    simp_rw [abs_of_nonneg (hnonneg _)]
    rw [← finiteSignedCharge_eq_sum_fiberMass mu kappa, abs_of_pos hpos]

/-- Signed product mass on two independent finite source systems. -/
def finiteProductSignedMass {P Q : Type*}
    (mu : P → ℝ) (nu : Q → ℝ) : P × Q → ℝ :=
  fun x => mu x.1 * nu x.2

/-- Product of two observational quotients. -/
def finiteProductQuotient {P Q K L : Type*}
    (kappa : P → K) (lambda : Q → L) : P × Q → K × L :=
  fun x => (kappa x.1, lambda x.2)

/-- Fiber charges factor exactly under independent products. -/
theorem finiteSignedFiberMass_product
    {P Q K L : Type*}
    [Fintype P] [Fintype Q] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (mu : P → ℝ) (nu : Q → ℝ) (kappa : P → K) (lambda : Q → L)
    (k : K) (l : L) :
    finiteSignedFiberMass (finiteProductSignedMass mu nu)
        (finiteProductQuotient kappa lambda) (k, l) =
      finiteSignedFiberMass mu kappa k * finiteSignedFiberMass nu lambda l := by
  classical
  rw [finiteSignedFiberMass, finiteSignedFiberMass, finiteSignedFiberMass,
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpk : kappa p = k <;> by_cases hql : lambda q = l <;>
    simp [finiteProductSignedMass, finiteProductQuotient, hpk, hql]

/-- The signed charge is multiplicative under independent products. -/
theorem finiteSignedCharge_product
    {P Q : Type*} [Fintype P] [Fintype Q]
    (mu : P → ℝ) (nu : Q → ℝ) :
    finiteSignedCharge (finiteProductSignedMass mu nu) =
      finiteSignedCharge mu * finiteSignedCharge nu := by
  rw [finiteSignedCharge, finiteSignedCharge, finiteSignedCharge,
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  rfl

/-- Exact cancellation in either factor is absorbing for the product quotient. -/
theorem finiteSignedFiberMass_product_eq_zero_of_left
    {P Q K L : Type*}
    [Fintype P] [Fintype Q] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (mu : P → ℝ) (nu : Q → ℝ) (kappa : P → K) (lambda : Q → L)
    (hleft : ∀ k, finiteSignedFiberMass mu kappa k = 0) :
    ∀ x, finiteSignedFiberMass (finiteProductSignedMass mu nu)
      (finiteProductQuotient kappa lambda) x = 0 := by
  intro x
  rw [finiteSignedFiberMass_product]
  simp [hleft]

/-- Right-factor version of absorption of exact cancellation. -/
theorem finiteSignedFiberMass_product_eq_zero_of_right
    {P Q K L : Type*}
    [Fintype P] [Fintype Q] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (mu : P → ℝ) (nu : Q → ℝ) (kappa : P → K) (lambda : Q → L)
    (hright : ∀ l, finiteSignedFiberMass nu lambda l = 0) :
    ∀ x, finiteSignedFiberMass (finiteProductSignedMass mu nu)
      (finiteProductQuotient kappa lambda) x = 0 := by
  intro x
  rw [finiteSignedFiberMass_product]
  simp [hright]

/-- Real sign attached to one orientation bit. -/
def finiteOrientationSign (b : Bool) : ℝ :=
  if b then -1 else 1

/-- Signed mass of an oriented atom with positive underlying mass. -/
def finiteOrientedMass {P : Type*}
    (base : P → ℝ) (orientation : P → Bool) (p : P) : ℝ :=
  finiteOrientationSign (orientation p) * base p

/-- If the total charge is positive and the normalized quotient is positive, every observable
fiber contains a positive-orientation atom. Hence the quotient has at most as many points as the
positive orientation sector. -/
theorem card_quotient_le_card_positiveOrientation_of_positive
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (base : P → ℝ) (orientation : P → Bool) (kappa : P → K)
    (hbase : ∀ p, 0 < base p)
    (hkappa : Function.Surjective kappa)
    (hcharge : 0 < finiteSignedCharge (finiteOrientedMass base orientation))
    (hpositive : ∀ k,
      0 ≤ finiteSignedFiberMass (finiteOrientedMass base orientation) kappa k /
        finiteSignedCharge (finiteOrientedMass base orientation)) :
    Fintype.card K ≤ Fintype.card {p : P // orientation p = false} := by
  classical
  have hexists : ∀ k : K, ∃ p, kappa p = k ∧ orientation p = false := by
    intro k
    have hmass_nonneg :
        0 ≤ finiteSignedFiberMass (finiteOrientedMass base orientation) kappa k := by
      rcases (div_nonneg_iff.mp (hpositive k)) with h | h
      · exact h.1
      · exact (not_le_of_gt hcharge h.2).elim
    by_contra hex
    have hall : ∀ p, kappa p = k → orientation p = true := by
      intro p hp
      cases horient : orientation p with
      | false => exact (hex ⟨p, hp, horient⟩).elim
      | true => rfl
    have hmass_neg :
        finiteSignedFiberMass (finiteOrientedMass base orientation) kappa k < 0 := by
      rw [finiteSignedFiberMass]
      apply Finset.sum_neg'
      · intro p hp
        by_cases hpk : kappa p = k
        · simp [hpk, finiteOrientedMass, finiteOrientationSign, hall p hpk,
            (hbase p).le]
        · simp [hpk]
      · obtain ⟨p, hp⟩ := hkappa k
        refine ⟨p, Finset.mem_univ p, ?_⟩
        simp [hp, finiteOrientedMass, finiteOrientationSign, hall p hp, hbase p]
    exact (not_lt_of_ge hmass_nonneg hmass_neg).elim
  choose representative hrepresentative horientation using hexists
  let embed : K → {p : P // orientation p = false} :=
    fun k => ⟨representative k, horientation k⟩
  have hembed : Function.Injective embed := by
    intro k l hkl
    have hval : representative k = representative l := congrArg Subtype.val hkl
    have := congrArg kappa hval
    simpa only [hrepresentative] using this
  exact Fintype.card_le_of_injective embed hembed

/-- Negative-charge counterpart of the minority-confinement capacity law. -/
theorem card_quotient_le_card_negativeOrientation_of_negative
    {P K : Type*} [Fintype P] [Fintype K] [DecidableEq K]
    (base : P → ℝ) (orientation : P → Bool) (kappa : P → K)
    (hbase : ∀ p, 0 < base p)
    (hkappa : Function.Surjective kappa)
    (hcharge : finiteSignedCharge (finiteOrientedMass base orientation) < 0)
    (hpositive : ∀ k,
      0 ≤ finiteSignedFiberMass (finiteOrientedMass base orientation) kappa k /
        finiteSignedCharge (finiteOrientedMass base orientation)) :
    Fintype.card K ≤ Fintype.card {p : P // orientation p = true} := by
  classical
  have hexists : ∀ k : K, ∃ p, kappa p = k ∧ orientation p = true := by
    intro k
    have hmass_nonpos :
        finiteSignedFiberMass (finiteOrientedMass base orientation) kappa k ≤ 0 := by
      rcases (div_nonneg_iff.mp (hpositive k)) with h | h
      · exact (not_le_of_gt hcharge h.2).elim
      · exact h.1
    by_contra hex
    have hall : ∀ p, kappa p = k → orientation p = false := by
      intro p hp
      cases horient : orientation p with
      | false => rfl
      | true => exact (hex ⟨p, hp, horient⟩).elim
    have hmass_pos :
        0 < finiteSignedFiberMass (finiteOrientedMass base orientation) kappa k := by
      rw [finiteSignedFiberMass]
      apply Finset.sum_pos'
      · intro p hp
        by_cases hpk : kappa p = k
        · simp [hpk, finiteOrientedMass, finiteOrientationSign, hall p hpk,
            (hbase p).le]
        · simp [hpk]
      · obtain ⟨p, hp⟩ := hkappa k
        refine ⟨p, Finset.mem_univ p, ?_⟩
        simp [hp, finiteOrientedMass, finiteOrientationSign, hall p hp, hbase p]
    exact (not_lt_of_ge hmass_nonpos hmass_pos).elim
  choose representative hrepresentative horientation using hexists
  let embed : K → {p : P // orientation p = true} :=
    fun k => ⟨representative k, horientation k⟩
  have hembed : Function.Injective embed := by
    intro k l hkl
    have hval : representative k = representative l := congrArg Subtype.val hkl
    have := congrArg kappa hval
    simpa only [hrepresentative] using this
  exact Fintype.card_le_of_injective embed hembed

/-- **Exposed sign-coherence law.** If atomwise normalized signed masses are nonnegative, then the
orientation is constant. Thus a positive state on the point-separating observable algebra cannot
retain both signs on one exposed face. -/
theorem orientation_constant_of_normalized_orientedMass_nonneg
    {P : Type*} [Fintype P]
    (base : P → ℝ) (orientation : P → Bool)
    (hbase : ∀ p, 0 < base p)
    (hcharge : finiteSignedCharge (finiteOrientedMass base orientation) ≠ 0)
    (hpositive : ∀ p,
      0 ≤ finiteOrientedMass base orientation p /
        finiteSignedCharge (finiteOrientedMass base orientation)) :
    ∀ p q, orientation p = orientation q := by
  rcases lt_or_gt_of_ne hcharge with hneg | hpos
  · have hall : ∀ p, orientation p = true := by
      intro p
      cases hp : orientation p with
      | false =>
          have hratio :
              finiteOrientedMass base orientation p /
                  finiteSignedCharge (finiteOrientedMass base orientation) < 0 := by
            simpa [finiteOrientedMass, finiteOrientationSign, hp] using
              div_neg_of_pos_of_neg (hbase p) hneg
          exact (not_lt_of_ge (hpositive p) hratio).elim
      | true => rfl
    intro p q
    rw [hall p, hall q]
  · have hall : ∀ p, orientation p = false := by
      intro p
      cases hp : orientation p with
      | false => rfl
      | true =>
          have hratio :
              finiteOrientedMass base orientation p /
                  finiteSignedCharge (finiteOrientedMass base orientation) < 0 := by
            simpa [finiteOrientedMass, finiteOrientationSign, hp] using
              div_neg_of_neg_of_pos (neg_neg_of_pos (hbase p)) hpos
          exact (not_lt_of_ge (hpositive p) hratio).elim
    intro p q
    rw [hall p, hall q]

end

end HTGeometry
