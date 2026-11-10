import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.TeichmullerCarries
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.TruncatedLogarithmFibres

/-!
# A power saving for Heilbronn sums

The bound `#L_p⁻¹(z)³ ≤ 100³p²` controls additive energy of the Teichmüller image
in `Z/p²`. Character orthogonality gives its fourth Fourier moment, and multiplication
by nonzero Teichmüller lifts repeats every unit-frequency value `p−1` times.
Thus `|Σ_{n=1}^p exp(2πian^p/p²)| ≤ 5p^(11/12)` whenever `p` is prime and `p∤a`.
The prime two is covered by the trivial bound.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

variable {N : ℕ} [NeZero N] {ι : Type*} [Fintype ι]

/-- Fourier sum of a parametrized subset of a finite cyclic group. -/
def cyclicSum (φ : ι → ZMod N) (a : ZMod N) : ℂ :=
  ∑ x, ZMod.stdAddChar (a * φ x)

/-- Number of additive quadruples, with multiplicity in the parameter space. -/
def cyclicEnergy (φ : ι → ZMod N) : ℕ :=
  (univ.filter fun q : ι × ι × ι × ι => φ q.1 + φ q.2.1 = φ q.2.2.1 + φ q.2.2.2).card

theorem cyclicSum_fourth (φ : ι → ZMod N) (a : ZMod N) :
    cyclicSum φ a * cyclicSum φ a * starRingEnd ℂ (cyclicSum φ a) *
        starRingEnd ℂ (cyclicSum φ a) =
      ∑ q : ι × ι × ι × ι,
        ZMod.stdAddChar (a * (φ q.2.2.1 + φ q.2.2.2 - φ q.1 - φ q.2.1)) := by
  have hconj : starRingEnd ℂ (cyclicSum φ a) =
      ∑ x, ZMod.stdAddChar (-(a * φ x)) := by
    unfold cyclicSum
    rw [map_sum]
    exact sum_congr rfl fun x _ => (AddChar.map_neg_eq_conj _ _).symm
  rw [hconj]
  unfold cyclicSum
  simp only [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  refine sum_congr rfl fun s1 _ => sum_congr rfl fun s2 _ => sum_congr rfl fun s3 _ =>
    sum_congr rfl fun s4 _ => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Character orthogonality identifies the fourth moment with additive energy. -/
theorem cyclicSum_fourth_moment (φ : ι → ZMod N) :
    ∑ a : ZMod N, ‖cyclicSum φ a‖ ^ 4 = N * (cyclicEnergy φ : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have hn : ∀ a : ZMod N, ((‖cyclicSum φ a‖ ^ 4 : ℝ) : ℂ) =
      cyclicSum φ a * cyclicSum φ a * starRingEnd ℂ (cyclicSum φ a) *
        starRingEnd ℂ (cyclicSum φ a) := by
    intro a
    have h := Complex.mul_conj (cyclicSum φ a)
    rw [Complex.normSq_eq_norm_sq] at h
    calc ((‖cyclicSum φ a‖ ^ 4 : ℝ) : ℂ) = ((‖cyclicSum φ a‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
          push_cast
          ring
      _ = _ := by rw [← h]; ring
  simp_rw [← Complex.ofReal_pow] at hn ⊢
  rw [Finset.sum_congr rfl fun a _ => hn a]
  simp_rw [cyclicSum_fourth]
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  rw [cyclicEnergy, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine sum_congr rfl fun q _ => ?_
  have hiff : (φ q.2.2.1 + φ q.2.2.2 - φ q.1 - φ q.2.1 = 0) ↔
      (φ q.1 + φ q.2.1 = φ q.2.2.1 + φ q.2.2.2) := by
    constructor <;> intro h <;> linear_combination -h
  by_cases hq : φ q.1 + φ q.2.1 = φ q.2.2.1 + φ q.2.2.2
  · rw [if_pos (hiff.mpr hq), if_pos hq]; push_cast; ring
  · rw [if_neg (fun h => hq (hiff.mp h)), if_neg hq]; push_cast; ring
variable {p : ℕ} [Fact p.Prime]

/-- Additive energy is bounded by the count of pair collisions with prescribed residue sum. -/
theorem teichLift_energy_le_triples :
    cyclicEnergy (teichLift p) ≤
      (univ.filter fun r : ZMod p × ZMod p × ZMod p =>
        teichLift p r.2.1 + teichLift p (r.1 - r.2.1) =
          teichLift p r.2.2 + teichLift p (r.1 - r.2.2)).card := by
  classical
  unfold cyclicEnergy
  let Q := (univ : Finset (ZMod p × ZMod p × ZMod p × ZMod p)).filter fun q =>
    teichLift p q.1 + teichLift p q.2.1 = teichLift p q.2.2.1 + teichLift p q.2.2.2
  have hred (q : ZMod p × ZMod p × ZMod p × ZMod p) (hq : q ∈ Q) :
      q.1 + q.2.1 = q.2.2.1 + q.2.2.2 := by
    have h := congrArg (primeSquareReduction p) (mem_filter.mp hq).2
    simpa only [map_add, primeSquareReduction_teichLift] using h
  refine card_le_card_of_injOn (fun q => (q.1 + q.2.1, q.1, q.2.2.1)) ?_ ?_
  · intro q hq
    have hr := hred q hq
    have hq' := (mem_filter.mp hq).2
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and]
    rw [add_sub_cancel_left, show q.1 + q.2.1 - q.2.2.1 = q.2.2.2 by linear_combination hr]
    exact hq'
  · intro u hu v hv huv
    have h1 : u.1 = v.1 := congrArg (fun r : ZMod p × ZMod p × ZMod p => r.2.1) huv
    have h3 : u.2.2.1 = v.2.2.1 := congrArg (fun r : ZMod p × ZMod p × ZMod p => r.2.2) huv
    have hs : u.1 + u.2.1 = v.1 + v.2.1 := congrArg (fun r : ZMod p × ZMod p × ZMod p => r.1) huv
    have h2 : u.2.1 = v.2.1 := by rw [h1] at hs; exact add_left_cancel hs
    have h4 : u.2.2.2 = v.2.2.2 := by
      have hur := hred u hu
      have hvr := hred v hv
      linear_combination -hur + hvr + hs - h3
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

/-- A uniform finite-logarithm fibre bound controls prime-square additive energy. -/
theorem teichLift_energy_le (hp2 : p ≠ 2) {M : ℕ}
    (hM : ∀ z : ZMod p, (truncatedLogFullFibre p z).card ≤ M) :
    cyclicEnergy (teichLift p) ≤ p ^ 2 + p ^ 2 * M := by
  classical
  refine teichLift_energy_le_triples.trans ?_
  rw [card_filter]
  simp only [Fintype.sum_prod_type]
  have hinner (s x : ZMod p) :
      (∑ y : ZMod p, if teichLift p x + teichLift p (s - x) =
        teichLift p y + teichLift p (s - y) then 1 else 0) ≤
          (if s = 0 then p else 0) + M := by
    by_cases hs : s = 0
    · rw [if_pos hs]
      calc (∑ y : ZMod p, if teichLift p x + teichLift p (s - x) =
              teichLift p y + teichLift p (s - y) then 1 else 0)
          ≤ ∑ _y : ZMod p, 1 := sum_le_sum fun y _ => by split_ifs <;> omega
        _ = p := by simp only [sum_const, card_univ, ZMod.card, smul_eq_mul, mul_one]
        _ ≤ p + M := Nat.le_add_right _ _
    · rw [if_neg hs, zero_add, ← card_filter]
      let S := (univ : Finset (ZMod p)).filter fun y =>
        teichLift p x + teichLift p (s - x) = teichLift p y + teichLift p (s - y)
      have hcard : S.card ≤ (truncatedLogFullFibre p ((truncatedLog (ZMod p) p).eval (x / s))).card := by
        refine card_le_card_of_injOn (fun y => y / s) ?_ ?_
        · intro y hy
          simp only [truncatedLogFullFibre, Finset.mem_coe, mem_filter, mem_univ, true_and]
          exact ((teichLift_scaled_pair_eq_iff hp2 hs x y).mp (mem_filter.mp hy).2).symm
        · intro u _ v _ huv
          exact (div_left_inj' hs).mp huv
      exact hcard.trans (hM _)
  calc (∑ s : ZMod p, ∑ x : ZMod p, ∑ y : ZMod p,
        if teichLift p x + teichLift p (s - x) =
          teichLift p y + teichLift p (s - y) then 1 else 0)
      ≤ ∑ s : ZMod p, ∑ _x : ZMod p, ((if s = 0 then p else 0) + M) :=
        sum_le_sum fun s _ => sum_le_sum fun x _ => hinner s x
    _ = p ^ 2 + p ^ 2 * M := by
      simp only [sum_add_distrib, sum_const, card_univ, ZMod.card, smul_eq_mul,
        mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
      ring

/-- The Heilbronn sum, including the zero Teichmüller representative. -/
def heilbronnSum (p : ℕ) [Fact p.Prime] (a : ZMod (p ^ 2)) : ℂ :=
  cyclicSum (teichLift p) a

theorem heilbronnSum_mul_teichLift (a : ZMod (p ^ 2)) {u : ZMod p} (hu : u ≠ 0) :
    heilbronnSum p (a * teichLift p u) = heilbronnSum p a := by
  unfold heilbronnSum cyclicSum
  simp_rw [mul_assoc, ← teichLift_mul]
  exact Equiv.sum_comp (Equiv.mulLeft₀ u hu) (fun x => ZMod.stdAddChar (a * teichLift p x))

/-- A unit frequency has `p−1` distinct translates with the same Heilbronn sum. -/
theorem heilbronnSum_orbit_bound {a : ZMod (p ^ 2)} (ha : IsUnit a) :
    ((p - 1 : ℕ) : ℝ) * ‖heilbronnSum p a‖ ^ 4 ≤
      (p : ℝ) ^ 2 * cyclicEnergy (teichLift p) := by
  classical
  let U := (univ : Finset (ZMod p)).erase 0
  have himg : ∑ u ∈ U, ‖heilbronnSum p (a * teichLift p u)‖ ^ 4 ≤
      ∑ b : ZMod (p ^ 2), ‖heilbronnSum p b‖ ^ 4 := by
    rw [← Finset.sum_image (f := fun b => ‖heilbronnSum p b‖ ^ 4)
      (s := U) (g := fun u => a * teichLift p u)]
    · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => by positivity
    · intro u _ v _ huv
      apply teichLift_injective
      obtain ⟨w, hw⟩ := ha
      rw [← hw] at huv
      have h := congrArg (fun z : ZMod (p ^ 2) => (↑w⁻¹ : ZMod (p ^ 2)) * z) huv
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using h
  have hleft : (∑ u ∈ U, ‖heilbronnSum p (a * teichLift p u)‖ ^ 4) =
      ((p - 1 : ℕ) : ℝ) * ‖heilbronnSum p a‖ ^ 4 := by
    calc (∑ u ∈ U, ‖heilbronnSum p (a * teichLift p u)‖ ^ 4)
        = ∑ _u ∈ U, ‖heilbronnSum p a‖ ^ 4 := by
          refine sum_congr rfl fun u hu => ?_
          rw [heilbronnSum_mul_teichLift a (mem_erase.mp hu).1]
      _ = _ := by simp only [sum_const, nsmul_eq_mul, U, card_erase_of_mem (mem_univ (0 : ZMod p)),
          card_univ, ZMod.card]
  rw [hleft] at himg
  simpa only [heilbronnSum, cyclicSum_fourth_moment, Nat.cast_pow] using himg

theorem norm_heilbronnSum_le (a : ZMod (p ^ 2)) : ‖heilbronnSum p a‖ ≤ p := by
  unfold heilbronnSum cyclicSum
  calc ‖∑ x : ZMod p, ZMod.stdAddChar (a * teichLift p x)‖
      ≤ ∑ x : ZMod p, ‖ZMod.stdAddChar (a * teichLift p x)‖ := norm_sum_le _ _
    _ = p := by simp only [ZMod.stdAddChar_apply, Circle.norm_coe, sum_const,
        card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-- A uniform power saving for every unit-frequency Heilbronn sum. -/
theorem heilbronnSum_pow_twelve_bound {a : ZMod (p ^ 2)} (ha : IsUnit a) :
    ‖heilbronnSum p a‖ ^ 12 ≤ 5 ^ 12 * (p : ℝ) ^ 11 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases hp2 : p = 2
  · subst p
    have h := pow_le_pow_left₀ (norm_nonneg (heilbronnSum 2 a)) (norm_heilbronnSum_le a) 12
    norm_num at h ⊢
    linarith only [h]
  let M := Nat.nthRoot 3 (100 ^ 3 * p ^ 2)
  have hM (z : ZMod p) : (truncatedLogFullFibre p z).card ≤ M :=
    (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (truncatedLog_fibre_cubic_bound p z)
  have hM3 : M ^ 3 ≤ 100 ^ 3 * p ^ 2 := Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0))
  have hM1 : 1 ≤ M := by
    apply (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr
    have hpos : 0 < 100 ^ 3 * p ^ 2 := by positivity
    norm_num only [one_pow]
    omega
  have hE : (cyclicEnergy (teichLift p) : ℝ) ≤ (p : ℝ) ^ 2 + (p : ℝ) ^ 2 * M := by
    exact_mod_cast teichLift_energy_le hp2 hM
  have hO := heilbronnSum_orbit_bound ha
  have hMp : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMr : (M : ℝ) ^ 3 ≤ 100 ^ 3 * (p : ℝ) ^ 2 := by exact_mod_cast hM3
  have htw : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show p ≤ 2 * (p - 1) by omega)
  have h4 : ‖heilbronnSum p a‖ ^ 4 ≤ 4 * (p : ℝ) ^ 3 * M := by
    apply le_of_mul_le_mul_left (a := (p : ℝ)) _ hpR
    calc (p : ℝ) * ‖heilbronnSum p a‖ ^ 4
        ≤ 2 * (((p - 1 : ℕ) : ℝ) * ‖heilbronnSum p a‖ ^ 4) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right htw
            (pow_nonneg (norm_nonneg (heilbronnSum p a)) 4)
      _ ≤ 2 * ((p : ℝ) ^ 2 * cyclicEnergy (teichLift p)) := by linarith only [hO]
      _ ≤ 2 * ((p : ℝ) ^ 2 * ((p : ℝ) ^ 2 + (p : ℝ) ^ 2 * M)) := by
          nlinarith only [mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * (p : ℝ) ^ 2)]
      _ ≤ (p : ℝ) * (4 * (p : ℝ) ^ 3 * M) := by
          have h := mul_le_mul_of_nonneg_left hMp (by positivity : 0 ≤ 2 * (p : ℝ) ^ 4)
          nlinarith only [h]
  calc ‖heilbronnSum p a‖ ^ 12 = (‖heilbronnSum p a‖ ^ 4) ^ 3 := by ring
    _ ≤ (4 * (p : ℝ) ^ 3 * M) ^ 3 := pow_le_pow_left₀ (by positivity) h4 3
    _ = 64 * (p : ℝ) ^ 9 * (M : ℝ) ^ 3 := by ring
    _ ≤ 64 * (p : ℝ) ^ 9 * (100 ^ 3 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hMr (by positivity)
    _ ≤ 5 ^ 12 * (p : ℝ) ^ 11 := by
      nlinarith only [pow_nonneg hpR.le 11]
/-- Heilbronn's sum has a uniform saving of one twelfth in its exponent. -/
theorem norm_heilbronnSum_le_power {a : ZMod (p ^ 2)} (ha : IsUnit a) :
    ‖heilbronnSum p a‖ ≤ 5 * (p : ℝ) ^ (11 / 12 : ℝ) := by
  have hr : ((p : ℝ) ^ (11 / 12 : ℝ)) ^ (12 : ℕ) = (p : ℝ) ^ (11 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    norm_num
  apply le_of_pow_le_pow_left₀ (n := 12) (by decide) (by positivity)
  rw [mul_pow, hr]
  exact heilbronnSum_pow_twelve_bound ha

/-- The usual coprimality condition on the integer frequency gives the unit-frequency bound. -/
theorem norm_heilbronnSum_natCast_le_power (a : ℕ) (ha : ¬ p ∣ a) :
    ‖heilbronnSum p (a : ZMod (p ^ 2))‖ ≤ 5 * (p : ℝ) ^ (11 / 12 : ℝ) := by
  apply norm_heilbronnSum_le_power
  apply (ZMod.isUnit_iff_coprime a (p ^ 2)).mpr
  exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ha).symm).pow_right 2

/-- The standard additive-character definition is the classical exponential sum modulo p². -/
theorem heilbronnSum_natCast_eq (a : ℕ) :
    heilbronnSum p (a : ZMod (p ^ 2)) =
      ∑ x : ZMod p, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (x.val : ℂ) ^ p /
        (p : ℂ) ^ 2) := by
  unfold heilbronnSum cyclicSum
  refine sum_congr rfl fun x _ => ?_
  have h := ZMod.stdAddChar_coe (N := p ^ 2) ((a * x.val ^ p : ℕ) : ℤ)
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow,
    teichLift, mul_assoc] using h

/-- The representatives `1,…,p` give the classical Heilbronn sum. -/
theorem heilbronnSum_natCast_eq_sum_range (a : ℕ) :
    heilbronnSum p (a : ZMod (p ^ 2)) =
      ∑ n ∈ range p, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) *
        ((n + 1 : ℕ) : ℂ) ^ p / (p : ℂ) ^ 2) := by
  classical
  have hr : heilbronnSum p (a : ZMod (p ^ 2)) =
      ∑ x : ZMod p, ZMod.stdAddChar ((a : ZMod (p ^ 2)) * teichLift p (x + 1)) :=
    (Equiv.sum_comp (Equiv.addRight (1 : ZMod p))
      (fun x => ZMod.stdAddChar ((a : ZMod (p ^ 2)) * teichLift p x))).symm
  rw [hr]
  calc (∑ x : ZMod p, ZMod.stdAddChar ((a : ZMod (p ^ 2)) * teichLift p (x + 1)))
      = ∑ n ∈ range p, ZMod.stdAddChar ((a : ZMod (p ^ 2)) * teichLift p ((n : ZMod p) + 1)) := by
        refine sum_nbij' (fun x : ZMod p => x.val) (fun n : ℕ => (n : ZMod p)) ?_ ?_ ?_ ?_ ?_
        · intro x _; simpa using ZMod.val_lt x
        · intro n _; exact mem_univ _
        · intro x _; exact ZMod.natCast_zmod_val x
        · intro n hn; exact ZMod.val_natCast_of_lt (mem_range.mp hn)
        · intro x _; rw [ZMod.natCast_zmod_val]
    _ = _ := by
      refine sum_congr rfl fun n _ => ?_
      have ht : teichLift p ((n : ZMod p) + 1) = ((n : ZMod (p ^ 2)) + 1) ^ p := by
        simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
          (teichLift_intCast (p := p) ((n : ℤ) + 1))
      rw [ht]
      have h := ZMod.stdAddChar_coe (N := p ^ 2) ((a : ℤ) * ((n : ℤ) + 1) ^ p)
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_assoc] using h

/-- Uniform power saving for `Σ_{n=1}^p exp(2πian^p/p²)` when `p∤a`. -/
theorem norm_classicalHeilbronnSum_le_power (a : ℕ) (ha : ¬ p ∣ a) :
    ‖∑ n ∈ range p, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ p / (p : ℂ) ^ 2)‖ ≤ 5 * (p : ℝ) ^ (11 / 12 : ℝ) := by
  rw [← heilbronnSum_natCast_eq_sum_range]
  exact norm_heilbronnSum_natCast_le_power a ha

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.cyclicSum_fourth_moment
#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.teichLift_energy_le
#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.norm_heilbronnSum_natCast_le_power

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.norm_classicalHeilbronnSum_le_power
