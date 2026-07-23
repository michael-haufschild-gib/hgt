import GaloisForLFunctions.RHTower.MertensFirst
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Weighted Euler coefficient spaces: critical summable and Marcinkiewicz layers

This file builds three prime coefficient topologies for the weighted Euler
tangent and proves the exact
boundary facts the decoupling argument consumes:

* the critical summable layer `T_1` with norm `∑_p (log p / p)·|b_p|`;
* the logarithmic Marcinkiewicz layer `M_log` with cutoff quotients
  `(1/log X)·∑_{p ≤ X} (log p / p)·|b_p|`;
* the vanishing-tail layer `M_0`, stated by uniform vanishing of truncation
  tails in the Marcinkiewicz quotient;
* the exact coordinate value: the quotient family of `e_p` has greatest value
  `1/p`, attained at the cutoff `X = p`;
* the actual unit field `b ≡ 1` lies in `M_log` (Mertens' first theorem) but
  neither in `T_1` (Mertens divergence) nor in `M_0` (its tail quotients stay
  above `1/4` at arbitrarily late cutoffs);
* the inclusions `T_1 ⊆ M_0 ⊆ M_log`, both strict: `b_p = 1/log p` lies in
  `M_0 \ T_1`, and the unit field lies in `M_log \ M_0`.

Everything is unconditional.  The only arithmetic inputs are Mertens' first
theorem in prime form (`RHTower.Mertens.mertens_first_prime`, elementary, no
prime number theorem) and Euler's divergence of `∑ 1/p` (mathlib).
-/

noncomputable section

namespace RHTower

open Finset Set

/-- Prime-log weighted mass of a coefficient field at cutoff `X`:
`∑_{p ≤ X} (log p / p)·|b_p|`. -/
def primeLogMass (b : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n * |b n|

/-- Logarithmic Marcinkiewicz quotient at cutoff `X`. -/
def marcinkiewiczLogQuotient (b : ℕ → ℝ) (X : ℕ) : ℝ :=
  primeLogMass b X / Real.log X

/-- Membership in the critical summable layer `T_1`. -/
def MemCriticalSummableLayer (b : ℕ → ℝ) : Prop :=
  Summable ({p : ℕ | p.Prime}.indicator fun n => Real.log n / n * |b n|)

/-- Membership in the logarithmic Marcinkiewicz layer `M_log`: the cutoff
quotients are uniformly bounded. -/
def MemMarcinkiewiczLogLayer (b : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C

/-- The tail of a coefficient field beyond the truncation point `P`. -/
def primeCoefficientTail (b : ℕ → ℝ) (P : ℕ) : ℕ → ℝ :=
  fun n => if P < n then b n else 0

/-- The head of a coefficient field up to the truncation point `P`. -/
def primeCoefficientHead (b : ℕ → ℝ) (P : ℕ) : ℕ → ℝ :=
  fun n => if P < n then 0 else b n

/-- Membership in the vanishing-tail layer `M_0`: truncation tails vanish
uniformly in the Marcinkiewicz quotient. -/
def MemVanishingTailLayer (b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P : ℕ,
    ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient (primeCoefficientTail b P) X ≤ ε

/-- Every prime-log summand is nonnegative. -/
theorem primeLog_term_nonneg (b : ℕ → ℝ) (n : ℕ) :
    0 ≤ Real.log n / n * |b n| :=
  mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))
    (abs_nonneg _)

theorem primeLogMass_nonneg (b : ℕ → ℝ) (X : ℕ) : 0 ≤ primeLogMass b X :=
  Finset.sum_nonneg fun n _ => primeLog_term_nonneg b n

/-- The tail mass is the mass restricted to primes past the truncation. -/
theorem primeLogMass_tail (b : ℕ → ℝ) (P X : ℕ) :
    primeLogMass (primeCoefficientTail b P) X
      = ∑ n ∈ Finset.Icc 1 X with (n.Prime ∧ P < n), Real.log n / n * |b n| := by
  unfold primeLogMass primeCoefficientTail
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime <;> by_cases hP : P < n <;> simp [hp, hP]

/-- The head mass is the mass restricted to primes up to the truncation. -/
theorem primeLogMass_head (b : ℕ → ℝ) (P X : ℕ) :
    primeLogMass (primeCoefficientHead b P) X
      = ∑ n ∈ Finset.Icc 1 X with (n.Prime ∧ ¬ P < n), Real.log n / n * |b n| := by
  unfold primeLogMass primeCoefficientHead
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime <;> by_cases hP : P < n <;> simp [hp, hP]

/-- Mass splits exactly into head and tail. -/
theorem primeLogMass_head_add_tail (b : ℕ → ℝ) (P X : ℕ) :
    primeLogMass b X
      = primeLogMass (primeCoefficientHead b P) X
        + primeLogMass (primeCoefficientTail b P) X := by
  unfold primeLogMass primeCoefficientHead primeCoefficientTail
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hP : P < n <;> simp [hP]

/-- The head mass at any cutoff is dominated by the full mass at the
truncation point. -/
theorem primeLogMass_head_le (b : ℕ → ℝ) (P X : ℕ) :
    primeLogMass (primeCoefficientHead b P) X ≤ primeLogMass b P := by
  rw [primeLogMass_head]
  unfold primeLogMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, not_lt.1 hn.2.2⟩, hn.2.1⟩
  · intro n _ _
    exact primeLog_term_nonneg b n

/-- The head mass equals the truncation-point mass once the cutoff has
passed the truncation point. -/
theorem primeLogMass_head_eq (b : ℕ → ℝ) {P X : ℕ} (hPX : P ≤ X) :
    primeLogMass (primeCoefficientHead b P) X = primeLogMass b P := by
  rw [primeLogMass_head]
  unfold primeLogMass
  apply Finset.sum_congr _ fun n _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
  constructor
  · rintro ⟨⟨h1, _⟩, hp, h2⟩
    exact ⟨⟨h1, h2⟩, hp⟩
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨h1, le_trans h2 hPX⟩, hp, h2⟩

/-- Exact tail identity beyond the truncation point. -/
theorem primeLogMass_tail_eq_sub (b : ℕ → ℝ) {P X : ℕ} (hPX : P ≤ X) :
    primeLogMass (primeCoefficientTail b P) X
      = primeLogMass b X - primeLogMass b P := by
  have hsplit := primeLogMass_head_add_tail b P X
  have hhead := primeLogMass_head_eq b hPX
  linarith

/-- Later truncations have smaller tails. -/
theorem primeLogMass_tail_anti (b : ℕ → ℝ) {P Q : ℕ} (hPQ : P ≤ Q) (X : ℕ) :
    primeLogMass (primeCoefficientTail b Q) X
      ≤ primeLogMass (primeCoefficientTail b P) X := by
  rw [primeLogMass_tail, primeLogMass_tail]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, lt_of_le_of_lt hPQ hn.2.2⟩
  · intro n _ _
    exact primeLog_term_nonneg b n

/-- Cutoffs at or past `2` have positive logarithm. -/
theorem log_cutoff_pos {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log X :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hX)

/-- Cutoffs at or past `2` dominate `log 2`. -/
theorem log_two_le_log_cutoff {X : ℕ} (hX : 2 ≤ X) :
    Real.log 2 ≤ Real.log X :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hX)

/-- There are natural cutoffs with arbitrarily large logarithm. -/
theorem exists_nat_two_le_log_ge (c : ℝ) :
    ∃ X : ℕ, 2 ≤ X ∧ c ≤ Real.log X := by
  refine ⟨max 2 ⌈Real.exp c⌉₊, le_max_left _ _, ?_⟩
  have h1 : Real.exp c ≤ (⌈Real.exp c⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈Real.exp c⌉₊ : ℕ) : ℝ) ≤ ((max 2 ⌈Real.exp c⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 2 ⌈Real.exp c⌉₊
  calc c = Real.log (Real.exp c) := (Real.log_exp c).symm
    _ ≤ Real.log (max 2 ⌈Real.exp c⌉₊ : ℕ) :=
        Real.log_le_log (Real.exp_pos c) (le_trans h1 h2)

/-! ## The unit field and Mertens' first theorem -/

/-- The explicit Mertens constant of the corpus prime-form first theorem. -/
def mertensPrimeConstant : ℝ := (Real.log 4 + 4) + (8 + Mertens.mertensTail)

theorem mertensPrimeConstant_nonneg : 0 ≤ mertensPrimeConstant := by
  have htail : 0 ≤ Mertens.mertensTail := by
    unfold Mertens.mertensTail
    refine tsum_nonneg fun i => ?_
    exact mul_nonneg (by norm_num)
      (div_nonneg (Real.log_natCast_nonneg i) (Real.rpow_nonneg (Nat.cast_nonneg i) _))
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertensPrimeConstant
  linarith

/-- The unit-field mass is the plain Mertens prime sum. -/
theorem primeLogMass_unit (X : ℕ) :
    primeLogMass (fun _ => (1:ℝ)) X
      = ∑ n ∈ Finset.Icc 1 X with n.Prime, Real.log n / n := by
  unfold primeLogMass
  exact Finset.sum_congr rfl fun n _ => by simp

/-- Mertens upper bound for the unit-field mass. -/
theorem primeLogMass_unit_le (X : ℕ) (hX : 1 ≤ X) :
    primeLogMass (fun _ => (1:ℝ)) X ≤ Real.log X + mertensPrimeConstant := by
  have h := (abs_le.1 (Mertens.mertens_first_prime X hX)).2
  rw [primeLogMass_unit]
  unfold mertensPrimeConstant
  linarith

/-- Mertens lower bound for the unit-field mass. -/
theorem le_primeLogMass_unit (X : ℕ) (hX : 1 ≤ X) :
    Real.log X - mertensPrimeConstant ≤ primeLogMass (fun _ => (1:ℝ)) X := by
  have h := (abs_le.1 (Mertens.mertens_first_prime X hX)).1
  rw [primeLogMass_unit]
  unfold mertensPrimeConstant
  linarith

/-- **The actual unit field lies in the Marcinkiewicz layer** with the
explicit bound `1 + C/log 2`. -/
theorem unitField_memMarcinkiewiczLogLayer :
    MemMarcinkiewiczLogLayer (fun _ => (1:ℝ)) := by
  refine ⟨1 + mertensPrimeConstant / Real.log 2, fun X hX => ?_⟩
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  have h2X : Real.log 2 ≤ Real.log X := log_two_le_log_cutoff hX
  have hmass := primeLogMass_unit_le X (by omega)
  have h1 : mertensPrimeConstant / Real.log 2 * Real.log 2
      ≤ mertensPrimeConstant / Real.log 2 * Real.log X := by
    apply mul_le_mul_of_nonneg_left h2X
    exact div_nonneg mertensPrimeConstant_nonneg hlog2.le
  rw [div_mul_cancel₀ _ hlog2.ne'] at h1
  unfold marcinkiewiczLogQuotient
  rw [div_le_iff₀ hlogX]
  have hexp : (1 + mertensPrimeConstant / Real.log 2) * Real.log X
      = Real.log X + mertensPrimeConstant / Real.log 2 * Real.log X := by ring
  linarith

/-- **The actual unit field is not critically summable**: `∑_p log p / p`
diverges (Mertens divergence, Mertens boundary). -/
theorem unitField_not_memCriticalSummableLayer :
    ¬ MemCriticalSummableLayer (fun _ => (1:ℝ)) := by
  intro h
  unfold MemCriticalSummableLayer at h
  apply not_summable_one_div_on_primes
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun m _ => by positivity) n)
    (fun n => ?_) (h.mul_left (1 / Real.log 2))
  by_cases hn : n.Prime
  · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hn),
      Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hn)]
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    calc 1 / (n:ℝ) = 1 * (1 / n) := (one_mul _).symm
      _ ≤ Real.log n / Real.log 2 * (1 / n) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [le_div_iff₀ hlog2]
          simpa using hlogn
      _ = 1 / Real.log 2 * (Real.log n / n * |(1:ℝ)|) := by
          rw [abs_one]; ring
  · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hn),
      Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hn)]
    simp

/-! ## Exact coordinate norm -/

/-- The coordinate field `e_p`. -/
def primeCoordinateField (p : ℕ) : ℕ → ℝ := fun n => if n = p then 1 else 0

theorem coordinate_quotient_value {p : ℕ} (hp : p.Prime) :
    Real.log p / p / Real.log p = 1 / p := by
  have hlogp : Real.log (p:ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [div_div, mul_comm (p:ℝ) (Real.log p), ← div_div, div_self hlogp]

theorem primeLogMass_coordinate_of_le {p X : ℕ} (hp : p.Prime) (hpX : p ≤ X) :
    primeLogMass (primeCoordinateField p) X = Real.log p / p := by
  unfold primeLogMass
  rw [Finset.sum_eq_single_of_mem p]
  · simp [primeCoordinateField]
  · rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hp.one_lt.le, hpX⟩, hp⟩
  · intro n _ hnp
    simp [primeCoordinateField, hnp]

theorem primeLogMass_coordinate_of_lt {p X : ℕ} (hXp : X < p) :
    primeLogMass (primeCoordinateField p) X = 0 := by
  unfold primeLogMass
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  have : n ≠ p := by omega
  simp [primeCoordinateField, this]

/-- **Exact coordinate norm**: the Marcinkiewicz quotient
family of the coordinate field `e_p` has greatest value exactly `1/p`,
attained at the cutoff `X = p`. -/
theorem isGreatest_marcinkiewiczLogQuotient_coordinate {p : ℕ} (hp : p.Prime) :
    IsGreatest
      {y : ℝ | ∃ X : ℕ, 2 ≤ X ∧ marcinkiewiczLogQuotient (primeCoordinateField p) X = y}
      (1 / p) := by
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hppos : (0:ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · refine ⟨p, hp.two_le, ?_⟩
    unfold marcinkiewiczLogQuotient
    rw [primeLogMass_coordinate_of_le hp le_rfl]
    exact coordinate_quotient_value hp
  · rintro y ⟨X, hX, rfl⟩
    unfold marcinkiewiczLogQuotient
    rcases lt_or_ge X p with hXp | hpX
    · rw [primeLogMass_coordinate_of_lt hXp, zero_div]
      positivity
    · rw [primeLogMass_coordinate_of_le hp hpX]
      have hlogX : Real.log p ≤ Real.log X := by
        apply Real.log_le_log (by exact_mod_cast hp.pos)
        exact_mod_cast hpX
      calc Real.log p / p / Real.log X
          ≤ Real.log p / p / Real.log p := by
            apply div_le_div_of_nonneg_left _ hlogp hlogX
            exact div_nonneg hlogp.le hppos.le
        _ = 1 / p := coordinate_quotient_value hp

/-! ## Layer inclusions -/

/-- **`T_1 ⊆ M_0`**: critical summability forces uniformly vanishing
truncation tails. -/
theorem memVanishingTailLayer_of_memCriticalSummableLayer {b : ℕ → ℝ}
    (hb : MemCriticalSummableLayer b) : MemVanishingTailLayer b := by
  unfold MemCriticalSummableLayer at hb
  intro ε hε
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := hb.nat_tsum_vanishing (Iio_mem_nhds (mul_pos hε hlog2))
  refine ⟨N, fun X hX => ?_⟩
  have hlogX : (0:ℝ) < Real.log X := log_cutoff_pos hX
  have h2X : Real.log 2 ≤ Real.log X := log_two_le_log_cutoff hX
  have hmass_lt : primeLogMass (primeCoefficientTail b N) X
      < ε * Real.log 2 := by
    rw [primeLogMass_tail]
    have hsub : (↑((Finset.Icc 1 X).filter fun n => n.Prime ∧ N < n) : Set ℕ)
        ⊆ {n : ℕ | N ≤ n} := by
      intro n hn
      rw [Finset.coe_filter, Set.mem_setOf_eq] at hn
      exact le_of_lt hn.2.2
    have hmem := hN _ hsub
    rw [Set.mem_Iio, Finset.tsum_subtype'] at hmem
    refine lt_of_le_of_lt (le_of_eq ?_) hmem
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_filter] at hn
    exact (Set.indicator_of_mem
      (show n ∈ {p : ℕ | p.Prime} from hn.2.1)
      (fun n => Real.log n / n * |b n|)).symm
  unfold marcinkiewiczLogQuotient
  rw [div_le_iff₀ hlogX]
  have : ε * Real.log 2 ≤ ε * Real.log X :=
    mul_le_mul_of_nonneg_left h2X hε.le
  linarith

/-- **`M_0 ⊆ M_log`**: vanishing tails give a uniform Marcinkiewicz bound. -/
theorem memMarcinkiewiczLogLayer_of_memVanishingTailLayer {b : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) : MemMarcinkiewiczLogLayer b := by
  obtain ⟨P, hP⟩ := hb 1 one_pos
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨primeLogMass b P / Real.log 2 + 1, fun X hX => ?_⟩
  have hlogX : 0 < Real.log X := log_cutoff_pos hX
  have h2X : Real.log 2 ≤ Real.log X := log_two_le_log_cutoff hX
  have hsplit := primeLogMass_head_add_tail b P X
  have hhead := primeLogMass_head_le b P X
  have htail := hP X hX
  unfold marcinkiewiczLogQuotient at htail ⊢
  rw [div_le_iff₀ hlogX] at htail ⊢
  have h1 : primeLogMass b P / Real.log 2 * Real.log 2
      ≤ primeLogMass b P / Real.log 2 * Real.log X := by
    apply mul_le_mul_of_nonneg_left h2X
    exact div_nonneg (primeLogMass_nonneg b P) hlog2.le
  rw [div_mul_cancel₀ _ hlog2.ne'] at h1
  have hexp : (primeLogMass b P / Real.log 2 + 1) * Real.log X
      = primeLogMass b P / Real.log 2 * Real.log X + Real.log X := by ring
  linarith

/-- Finitely supported fields are critically summable; in particular every
coordinate field is. -/
theorem memCriticalSummableLayer_of_finite_support {b : ℕ → ℝ} (s : Finset ℕ)
    (hs : ∀ n ∉ s, b n = 0) : MemCriticalSummableLayer b := by
  unfold MemCriticalSummableLayer
  apply summable_of_ne_finset_zero (s := s)
  intro n hn
  by_cases hp : n.Prime
  · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp), hs n hn]
    simp
  · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]

theorem primeCoordinateField_memCriticalSummableLayer {p : ℕ} :
    MemCriticalSummableLayer (primeCoordinateField p) :=
  memCriticalSummableLayer_of_finite_support {p} fun n hn => by
    have : n ≠ p := by simpa using hn
    simp [primeCoordinateField, this]

/-! ## Strictness witnesses -/

/-- **The unit field has non-vanishing tails**: it lies in `M_log \ M_0`.
This is the Mertens corona exclusion. -/
theorem unitField_not_memVanishingTailLayer :
    ¬ MemVanishingTailLayer (fun _ => (1:ℝ)) := by
  intro h
  obtain ⟨P, hP⟩ := h 4⁻¹ (by norm_num)
  set Q : ℕ := max P 1 with hQ
  have hQ1 : 1 ≤ Q := le_max_right _ _
  obtain ⟨X₀, hX₀2, hX₀log⟩ := exists_nat_two_le_log_ge
    (2 * (Real.log Q + 2 * mertensPrimeConstant) + 1)
  set X : ℕ := max X₀ Q with hXdef
  have hX2 : 2 ≤ X := le_trans hX₀2 (le_max_left _ _)
  have hQX : Q ≤ X := le_max_right _ _
  have hlogmono : Real.log X₀ ≤ Real.log X := by
    apply Real.log_le_log (by exact_mod_cast lt_of_lt_of_le two_pos hX₀2)
    exact_mod_cast le_max_left X₀ Q
  have hXlog : 2 * (Real.log Q + 2 * mertensPrimeConstant) + 1 ≤ Real.log X :=
    le_trans hX₀log hlogmono
  have hlogQ : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  have hC := mertensPrimeConstant_nonneg
  have hlogX : 0 < Real.log X := by linarith
  have hsub : primeLogMass (primeCoefficientTail (fun _ => (1:ℝ)) Q) X
      = primeLogMass (fun _ => (1:ℝ)) X - primeLogMass (fun _ => (1:ℝ)) Q :=
    primeLogMass_tail_eq_sub _ hQX
  have hanti := primeLogMass_tail_anti (fun _ => (1:ℝ)) (le_max_left P 1) X
  have hXlo := le_primeLogMass_unit X (by omega)
  have hQup := primeLogMass_unit_le Q hQ1
  have hquot := hP X hX2
  unfold marcinkiewiczLogQuotient at hquot
  rw [div_le_iff₀ hlogX] at hquot
  rw [← hQ] at hanti
  linarith

/-- The reciprocal-log field, the strictness witness for `T_1 ⊊ M_0`. -/
def invLogField : ℕ → ℝ := fun n => 1 / Real.log n

/-- The prime-log summand of the reciprocal-log field is exactly `1/n`. -/
theorem invLogField_term {n : ℕ} (hn1 : (1:ℝ) < n) :
    Real.log n / n * |invLogField n| = 1 / (n:ℝ) := by
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  unfold invLogField
  rw [abs_of_pos (one_div_pos.2 hlogn), mul_one_div, div_div,
    mul_comm (n:ℝ) (Real.log n), ← div_div, div_self hlogn.ne']

/-- **`1/log p` has uniformly vanishing tails**: it lies in `M_0`.  Uses only
Mertens' first theorem. -/
theorem invLogField_memVanishingTailLayer :
    MemVanishingTailLayer invLogField := by
  intro ε hε
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC := mertensPrimeConstant_nonneg
  set K : ℝ := 1 + mertensPrimeConstant / Real.log 2 with hK
  have hK0 : 0 < K := by
    have := div_nonneg hC hlog2.le
    rw [hK]; linarith
  obtain ⟨P, hP2, hPlog⟩ := exists_nat_two_le_log_ge (K / ε)
  have hlogP : 0 < Real.log P := lt_of_lt_of_le (div_pos hK0 hε) hPlog
  refine ⟨P, fun X hX => ?_⟩
  have hlogX : (0:ℝ) < Real.log X := log_cutoff_pos hX
  have h2X : Real.log 2 ≤ Real.log X := log_two_le_log_cutoff hX
  have hmass : Real.log P * primeLogMass (primeCoefficientTail invLogField P) X
      ≤ primeLogMass (fun _ => (1:ℝ)) X := by
    rw [primeLogMass_tail, primeLogMass_unit, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨-, hprime, hPn⟩ := hn
      have hn1 : (1:ℝ) < n := by exact_mod_cast hprime.one_lt
      have hP0 : (0:ℝ) < P := by exact_mod_cast lt_of_lt_of_le two_pos hP2
      have hPn' : Real.log P ≤ Real.log n := by
        apply Real.log_le_log hP0
        exact_mod_cast le_of_lt hPn
      have hn0 : (0:ℝ) < n := lt_trans one_pos hn1
      rw [invLogField_term hn1, mul_one_div, div_le_iff₀ hn0,
        div_mul_cancel₀ _ hn0.ne']
      exact hPn'
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.1⟩
    · intro n _ _
      exact div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
  have hmassU : Real.log P * primeLogMass (primeCoefficientTail invLogField P) X
      ≤ Real.log X + mertensPrimeConstant :=
    le_trans hmass (primeLogMass_unit_le X (by omega))
  have hεP : K ≤ ε * Real.log P := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).1 hPlog
  have h1 : mertensPrimeConstant / Real.log 2 * Real.log 2
      ≤ mertensPrimeConstant / Real.log 2 * Real.log X := by
    apply mul_le_mul_of_nonneg_left h2X
    exact div_nonneg hC hlog2.le
  rw [div_mul_cancel₀ _ hlog2.ne'] at h1
  unfold marcinkiewiczLogQuotient
  rw [div_le_iff₀ hlogX]
  have hgoal : Real.log P * primeLogMass (primeCoefficientTail invLogField P) X
      ≤ Real.log P * (ε * Real.log X) := by
    calc Real.log P * primeLogMass (primeCoefficientTail invLogField P) X
        ≤ Real.log X + mertensPrimeConstant := hmassU
      _ ≤ Real.log X + mertensPrimeConstant / Real.log 2 * Real.log X := by linarith
      _ = Real.log X * (1 + mertensPrimeConstant / Real.log 2) := by ring
      _ ≤ Real.log X * (ε * Real.log P) := by
          apply mul_le_mul_of_nonneg_left _ hlogX.le
          rw [← hK]; exact hεP
      _ = Real.log P * (ε * Real.log X) := by ring
  exact le_of_mul_le_mul_left hgoal hlogP

/-- **`1/log p` is not critically summable**: its critical norm is the
divergent prime-harmonic sum. -/
theorem invLogField_not_memCriticalSummableLayer :
    ¬ MemCriticalSummableLayer invLogField := by
  intro h
  unfold MemCriticalSummableLayer at h
  apply not_summable_one_div_on_primes
  have heq : ({p : ℕ | p.Prime}.indicator
      fun n => Real.log n / n * |invLogField n|)
      = {p : ℕ | p.Prime}.indicator fun n => 1 / (n:ℝ) := by
    funext n
    by_cases hn : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hn),
        Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hn)]
      exact invLogField_term (by exact_mod_cast hn.one_lt)
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hn),
        Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hn)]
  rwa [heq] at h

/-- **Strictness of `T_1 ⊆ M_0`.** -/
theorem exists_memVanishingTail_not_memCriticalSummable :
    ∃ b : ℕ → ℝ, MemVanishingTailLayer b ∧ ¬ MemCriticalSummableLayer b :=
  ⟨invLogField, invLogField_memVanishingTailLayer,
    invLogField_not_memCriticalSummableLayer⟩

/-- **Strictness of `M_0 ⊆ M_log`.**  The separating field is the actual
Euler unit source itself. -/
theorem exists_memMarcinkiewiczLog_not_memVanishingTail :
    ∃ b : ℕ → ℝ, MemMarcinkiewiczLogLayer b ∧ ¬ MemVanishingTailLayer b :=
  ⟨fun _ => 1, unitField_memMarcinkiewiczLogLayer,
    unitField_not_memVanishingTailLayer⟩

end RHTower
