import GaloisForLFunctions.RHTower.AcyclicFiniteFibersDerivedLimit
import GaloisForLFunctions.RHTower.WeldChargeFaithfulness

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Multiplication by two as an additive endomorphism of the integers. -/
def integerDoubling : ℤ →+ ℤ where
  toFun x := 2 * x
  map_zero' := by simp
  map_add' x y := by ring

/-- The stationary inverse tower `ℤ ←² ℤ ←² ⋯`. -/
def integerDoublingTower : ∀ _n : ℕ, ℤ →+ ℤ := fun _ => integerDoubling

theorem integerDoublingTower_compatibility
    (x : RHTower.towerLim (A := fun _ => ℤ) integerDoublingTower) (n : ℕ) :
    x.1 n = 2 * x.1 (n + 1) := by
  have h := congrFun x.2 n
  simpa [RHTower.towerLim, RHTower.towerDiff, integerDoublingTower,
    integerDoubling] using sub_eq_zero.mp h

theorem integerDoublingTower_iterate
    (x : RHTower.towerLim (A := fun _ => ℤ) integerDoublingTower) (n k : ℕ) :
    x.1 n = (2 : ℤ) ^ k * x.1 (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        x.1 n = (2 : ℤ) ^ k * x.1 (n + k) := ih
        _ = (2 : ℤ) ^ k * (2 * x.1 ((n + k) + 1)) := by
          rw [integerDoublingTower_compatibility x (n + k)]
        _ = (2 : ℤ) ^ (k + 1) * x.1 (n + (k + 1)) := by
          have hi : (n + k) + 1 = n + (k + 1) := by omega
          rw [hi, pow_succ]
          ring

/-- The ordinary inverse limit of `ℤ ←² ℤ ←² ⋯` is zero. -/
theorem integerDoublingTower_lim_subsingleton :
    Subsingleton (RHTower.towerLim (A := fun _ => ℤ) integerDoublingTower) := by
  constructor
  intro x y
  apply Subtype.ext
  funext n
  have hx : x.1 n = 0 := by
    apply RHTower.eq_zero_of_forall_two_pow_dvd
    intro k
    refine ⟨x.1 (n + k), ?_⟩
    exact integerDoublingTower_iterate x n k
  have hy : y.1 n = 0 := by
    apply RHTower.eq_zero_of_forall_two_pow_dvd
    intro k
    refine ⟨y.1 (n + k), ?_⟩
    exact integerDoublingTower_iterate y n k
  rw [hx, hy]

/-- Alternating binary digit sequence `1,0,1,0,…`. -/
def alternatingBinaryDigits : ℕ → ℤ := fun n => if n % 2 = 0 then 1 else 0

theorem alternatingBinaryDigits_even (m : ℕ) : alternatingBinaryDigits (2 * m) = 1 := by
  simp [alternatingBinaryDigits]

theorem alternatingBinaryDigits_odd (m : ℕ) : alternatingBinaryDigits (2 * m + 1) = 0 := by
  simp [alternatingBinaryDigits]

theorem alternatingBinaryDigits_not_mem_range :
    alternatingBinaryDigits ∉ (RHTower.towerDiff integerDoublingTower).range := by
  intro h
  rcases h with ⟨x, hx⟩
  have heven (m : ℕ) : x (2 * m) = 1 + 2 * x (2 * m + 1) := by
    have hc := congrFun hx (2 * m)
    change x (2 * m) - 2 * x (2 * m + 1) = alternatingBinaryDigits (2 * m) at hc
    rw [alternatingBinaryDigits_even] at hc
    omega
  have hodd (m : ℕ) : x (2 * m + 1) = 2 * x (2 * m + 2) := by
    have hc := congrFun hx (2 * m + 1)
    change x (2 * m + 1) - 2 * x (2 * m + 2) =
      alternatingBinaryDigits (2 * m + 1) at hc
    rw [alternatingBinaryDigits_odd] at hc
    omega
  have hstep (m : ℕ) : x (2 * m) = 1 + 4 * x (2 * (m + 1)) := by
    rw [heven m, hodd m]
    have hi : 2 * m + 2 = 2 * (m + 1) := by omega
    rw [hi]
    ring
  have hiterate (m : ℕ) :
      3 * x 0 + 1 = (4 : ℤ) ^ m * (3 * x (2 * m) + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [ih, hstep m]
        rw [pow_succ]
        ring
  have hdiv : ∀ k : ℕ, (2 : ℤ) ^ k ∣ 3 * x 0 + 1 := by
    intro k
    refine dvd_trans ?_ ⟨3 * x (2 * k) + 1, hiterate k⟩
    refine ⟨(2 : ℤ) ^ k, ?_⟩
    rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
  have hz : 3 * x 0 + 1 = 0 := RHTower.eq_zero_of_forall_two_pow_dvd hdiv
  omega

/-- The explicit alternating-digit class in the derived inverse limit. -/
def alternatingBinaryLimOneClass :
    RHTower.towerLimOne (A := fun _ => ℤ) integerDoublingTower :=
  (QuotientAddGroup.mk'
      (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range)
    alternatingBinaryDigits

/-- The first derived inverse limit of `ℤ ←² ℤ ←² ⋯` is nonzero. -/
theorem alternatingBinaryLimOneClass_ne_zero : alternatingBinaryLimOneClass ≠ 0 := by
  intro h
  change (QuotientAddGroup.mk'
      (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range)
        alternatingBinaryDigits = 0 at h
  have hmem : alternatingBinaryDigits ∈
      (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range :=
    (QuotientAddGroup.eq_zero_iff alternatingBinaryDigits).mp h
  exact alternatingBinaryDigits_not_mem_range hmem

theorem integerDoublingTower_limOne_nontrivial :
    Nontrivial (RHTower.towerLimOne (A := fun _ => ℤ) integerDoublingTower) :=
  ⟨⟨alternatingBinaryLimOneClass, 0, alternatingBinaryLimOneClass_ne_zero⟩⟩

/-! ### Exact identification with the dyadic completion modulo integers -/

/-- Integer lifts of compatible residues modulo `2^(n+1)`.  Quotienting by sequences congruent
to zero at every depth gives the standard inverse-limit model of the dyadic integers. -/
def DyadicCompatible : AddSubgroup (ℕ → ℤ) where
  carrier s := ∀ ⦃m n : ℕ⦄, m ≤ n → (2 : ℤ) ^ (m + 1) ∣ s n - s m
  zero_mem' := by
    intro m n hmn
    simp
  add_mem' := by
    intro a b ha hb m n hmn
    rcases ha hmn with ⟨u, hu⟩
    rcases hb hmn with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    simp only [Pi.add_apply]
    calc
      a n + b n - (a m + b m) = (a n - a m) + (b n - b m) := by ring
      _ = (2 : ℤ) ^ (m + 1) * u + (2 : ℤ) ^ (m + 1) * v := by rw [hu, hv]
      _ = (2 : ℤ) ^ (m + 1) * (u + v) := by ring
  neg_mem' := by
    intro a ha m n hmn
    rcases ha hmn with ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    simp only [Pi.neg_apply]
    calc
      -a n - -a m = -(a n - a m) := by ring
      _ = -((2 : ℤ) ^ (m + 1) * u) := by rw [hu]
      _ = (2 : ℤ) ^ (m + 1) * -u := by ring

/-- Compatible residue lifts representing embedded ordinary integers.  The witness `z` says the
sequence is congruent to the same integer modulo every `2^(n+1)`. -/
def dyadicIntegerSequences : AddSubgroup DyadicCompatible where
  carrier s := ∃ z : ℤ, ∀ n : ℕ, (2 : ℤ) ^ (n + 1) ∣ s.1 n - z
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro a b
    rintro ⟨za, ha⟩ ⟨zb, hb⟩
    refine ⟨za + zb, fun n => ?_⟩
    rcases ha n with ⟨u, hu⟩
    rcases hb n with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply]
    calc
      a.1 n + b.1 n - (za + zb) = (a.1 n - za) + (b.1 n - zb) := by ring
      _ = (2 : ℤ) ^ (n + 1) * u + (2 : ℤ) ^ (n + 1) * v := by rw [hu, hv]
      _ = (2 : ℤ) ^ (n + 1) * (u + v) := by ring
  neg_mem' := by
    intro a
    rintro ⟨z, hz⟩
    refine ⟨-z, fun n => ?_⟩
    rcases hz n with ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply]
    calc
      -a.1 n - -z = -(a.1 n - z) := by ring
      _ = -((2 : ℤ) ^ (n + 1) * u) := by rw [hu]
      _ = (2 : ℤ) ^ (n + 1) * -u := by ring

/-- Concrete inverse-limit presentation of `ℤ₂/ℤ`: compatible integer lifts of residues
modulo all positive powers of two, modulo the diagonally embedded ordinary integers. -/
abbrev DyadicCompletionModuloIntegers : Type :=
  DyadicCompatible ⧸ dyadicIntegerSequences

/-- Partial dyadic sum through digit `n`. -/
def dyadicPartialSum (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => a 0
  | n + 1 => dyadicPartialSum a n + (2 : ℤ) ^ (n + 1) * a (n + 1)

@[simp] theorem dyadicPartialSum_zero (a : ℕ → ℤ) : dyadicPartialSum a 0 = a 0 := rfl

theorem dyadicPartialSum_succ (a : ℕ → ℤ) (n : ℕ) :
    dyadicPartialSum a (n + 1) =
      dyadicPartialSum a n + (2 : ℤ) ^ (n + 1) * a (n + 1) := rfl

theorem dyadicPartialSum_add (a b : ℕ → ℤ) (n : ℕ) :
    dyadicPartialSum (a + b) n = dyadicPartialSum a n + dyadicPartialSum b n := by
  induction n with
  | zero => simp [dyadicPartialSum]
  | succ n ih =>
      rw [dyadicPartialSum_succ, dyadicPartialSum_succ, dyadicPartialSum_succ, ih]
      simp only [Pi.add_apply]
      ring

theorem dyadicPartialSum_sub_dvd (a : ℕ → ℤ) (m k : ℕ) :
    (2 : ℤ) ^ (m + 1) ∣ dyadicPartialSum a (m + k) - dyadicPartialSum a m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by omega, dyadicPartialSum_succ]
      rcases ih with ⟨u, hu⟩
      refine ⟨u + (2 : ℤ) ^ k * a (m + k + 1), ?_⟩
      rw [show m + k + 1 = (m + 1) + k by omega, pow_add]
      calc
        dyadicPartialSum a (m + k) +
              (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ k * a (m + 1 + k) -
            dyadicPartialSum a m =
          (dyadicPartialSum a (m + k) - dyadicPartialSum a m) +
            (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ k * a (m + 1 + k) := by ring
        _ = (2 : ℤ) ^ (m + 1) * u +
            (2 : ℤ) ^ (m + 1) * (2 : ℤ) ^ k * a (m + 1 + k) := by rw [hu]
        _ = (2 : ℤ) ^ (m + 1) *
            (u + (2 : ℤ) ^ k * a (m + 1 + k)) := by ring

/-- Additive partial-sum map into compatible dyadic residue lifts. -/
def dyadicPartialSumHom : (ℕ → ℤ) →+ DyadicCompatible where
  toFun a := ⟨dyadicPartialSum a, by
    change ∀ ⦃m n : ℕ⦄, m ≤ n →
      (2 : ℤ) ^ (m + 1) ∣ dyadicPartialSum a n - dyadicPartialSum a m
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact dyadicPartialSum_sub_dvd a m k⟩
  map_zero' := by
    apply Subtype.ext
    change dyadicPartialSum (0 : ℕ → ℤ) = 0
    funext n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [dyadicPartialSum_succ, ih]
        simp
  map_add' a b := by
    apply Subtype.ext
    funext n
    exact dyadicPartialSum_add a b n

noncomputable def dyadicDigitOfCompatible (s : DyadicCompatible) : ℕ → ℤ
  | 0 => s.1 0
  | n + 1 => Classical.choose (s.2 (Nat.le_succ n))

theorem dyadicDigitOfCompatible_spec (s : DyadicCompatible) (n : ℕ) :
    s.1 (n + 1) - s.1 n =
      (2 : ℤ) ^ (n + 1) * dyadicDigitOfCompatible s (n + 1) :=
  Classical.choose_spec (s.2 (Nat.le_succ n))

theorem dyadicPartialSum_digit_eq (s : DyadicCompatible) (n : ℕ) :
    dyadicPartialSum (dyadicDigitOfCompatible s) n = s.1 n := by
  induction n with
  | zero => simp [dyadicPartialSum, dyadicDigitOfCompatible]
  | succ n ih =>
      rw [dyadicPartialSum_succ, ih, ← dyadicDigitOfCompatible_spec]
      ring

theorem dyadicPartialSumHom_surjective : Function.Surjective dyadicPartialSumHom := by
  intro s
  refine ⟨dyadicDigitOfCompatible s, ?_⟩
  apply Subtype.ext
  funext n
  exact dyadicPartialSum_digit_eq s n

theorem dyadicPartialSum_towerDiff (x : ℕ → ℤ) (n : ℕ) :
    dyadicPartialSum
        (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower x) n =
      x 0 - (2 : ℤ) ^ (n + 1) * x (n + 1) := by
  induction n with
  | zero =>
      change x 0 - 2 * x 1 = x 0 - 2 ^ 1 * x 1
      ring
  | succ n ih =>
      rw [dyadicPartialSum_succ, ih]
      change x 0 - 2 ^ (n + 1) * x (n + 1) +
          2 ^ (n + 1) * (x (n + 1) - 2 * x (n + 2)) =
        x 0 - 2 ^ (n + 2) * x (n + 2)
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      ring

theorem dyadicPartialSum_mem_integer_iff_mem_towerDiff_range (a : ℕ → ℤ) :
    dyadicPartialSumHom a ∈ dyadicIntegerSequences ↔
      a ∈ (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range := by
  constructor
  · rintro ⟨z, hz⟩
    let q : ℕ → ℤ := fun n => Classical.choose (hz n)
    have hq (n : ℕ) : dyadicPartialSum a n - z = (2 : ℤ) ^ (n + 1) * q n :=
      Classical.choose_spec (hz n)
    let x : ℕ → ℤ := fun n => n.casesOn z (fun k => -q k)
    refine ⟨x, ?_⟩
    funext n
    cases n with
    | zero =>
        change z - 2 * (-q 0) = a 0
        have h0 := hq 0
        rw [dyadicPartialSum_zero] at h0
        norm_num at h0 ⊢
        omega
    | succ n =>
        change -q n - 2 * (-q (n + 1)) = a (n + 1)
        have hn := hq n
        have hsn := hq (n + 1)
        have hmul : (2 : ℤ) ^ (n + 1) * a (n + 1) =
            (2 : ℤ) ^ (n + 1) * (2 * q (n + 1) - q n) := by
          calc
            (2 : ℤ) ^ (n + 1) * a (n + 1) =
                dyadicPartialSum a (n + 1) - dyadicPartialSum a n := by
                  rw [dyadicPartialSum_succ]
                  ring
            _ = (dyadicPartialSum a (n + 1) - z) -
                (dyadicPartialSum a n - z) := by ring
            _ = (2 : ℤ) ^ (n + 2) * q (n + 1) -
                (2 : ℤ) ^ (n + 1) * q n := by rw [hsn, hn]
            _ = (2 : ℤ) ^ (n + 1) * (2 * q (n + 1) - q n) := by
                  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
                  ring
        have hp : (2 : ℤ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        have := mul_left_cancel₀ hp hmul
        omega
  · rintro ⟨x, rfl⟩
    refine ⟨x 0, fun n => ?_⟩
    refine ⟨-x (n + 1), ?_⟩
    change dyadicPartialSum
        (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower x) n - x 0 =
      (2 : ℤ) ^ (n + 1) * (-x (n + 1))
    rw [dyadicPartialSum_towerDiff]
    ring

/-- The canonical homomorphism from the derived inverse limit to `ℤ₂/ℤ`. -/
def integerDoublingLimOneToDyadicQuotient :
    RHTower.towerLimOne (A := fun _ => ℤ) integerDoublingTower →+
      DyadicCompletionModuloIntegers :=
  QuotientAddGroup.map
    (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range
    dyadicIntegerSequences dyadicPartialSumHom (by
      intro a ha
      change dyadicPartialSumHom a ∈ dyadicIntegerSequences
      exact (dyadicPartialSum_mem_integer_iff_mem_towerDiff_range a).2 ha)

theorem integerDoublingLimOneToDyadicQuotient_mk (a : ℕ → ℤ) :
    integerDoublingLimOneToDyadicQuotient
        ((QuotientAddGroup.mk'
          (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range) a) =
      (QuotientAddGroup.mk' dyadicIntegerSequences) (dyadicPartialSumHom a) := by
  rfl

theorem integerDoublingLimOneToDyadicQuotient_bijective :
    Function.Bijective integerDoublingLimOneToDyadicQuotient := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      change integerDoublingLimOneToDyadicQuotient
        ((QuotientAddGroup.mk'
          (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range) a) = 0 at hq
      change (QuotientAddGroup.mk'
        (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range) a = 0
      rw [integerDoublingLimOneToDyadicQuotient_mk] at hq
      have htarget : dyadicPartialSumHom a ∈ dyadicIntegerSequences :=
        (QuotientAddGroup.eq_zero_iff (dyadicPartialSumHom a)).mp hq
      have hsource : a ∈
          (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range :=
        (dyadicPartialSum_mem_integer_iff_mem_towerDiff_range a).1 htarget
      exact (QuotientAddGroup.eq_zero_iff a).2 hsource
  · intro q
    induction q using QuotientAddGroup.induction_on with
    | H s =>
      obtain ⟨a, ha⟩ := dyadicPartialSumHom_surjective s
      refine ⟨(QuotientAddGroup.mk'
        (RHTower.towerDiff (A := fun _ => ℤ) integerDoublingTower).range) a, ?_⟩
      rw [integerDoublingLimOneToDyadicQuotient_mk, ha]
      rfl

/-- Exact standard identification
`lim¹(ℤ ←² ℤ ←² ⋯) ≃+ ℤ₂/ℤ`. -/
noncomputable def integerDoublingTower_limOne_equiv_dyadicCompletionModuloIntegers :
    RHTower.towerLimOne (A := fun _ => ℤ) integerDoublingTower ≃+
      DyadicCompletionModuloIntegers :=
  AddEquiv.ofBijective integerDoublingLimOneToDyadicQuotient
    integerDoublingLimOneToDyadicQuotient_bijective

end

end GaloisForLFunctions.HTGeometry
