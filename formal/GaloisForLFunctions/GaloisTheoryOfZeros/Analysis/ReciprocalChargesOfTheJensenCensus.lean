import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ArbitraryJumpsOfCumulativeMass
import GaloisForLFunctions.FiniteFreeProbability.JensenCountsOffLineZeros

/-!
# Charging new nonreal Jensen roots along sparse degrees

Starting from zero, charge each newly observed nonreal root the reciprocal
of one plus the new observed count. Convergence at the critical power
detects finite off-line support even if arbitrarily many degrees are
skipped. Optimizing the sampling degrees recovers each integer divisor
bound with its exact fractional budget m/(1+m).
-/

noncomputable section
open Filter Finset
open scoped Topology
open GaloisForLFunctions.CumulativeQuadrature
open RHTower RHTower.DeBruijn RHTower.WindowNonrealBudget FiniteFreeProbability

namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Zero before the first reading, then the multiplicity count at each
selected degree. -/
def sampledJensenMass (u : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | i+1 => jensenNonrealCount (u i)

private theorem sampled_mono {u : ℕ → ℕ} (hu : Monotone u) : Monotone (sampledJensenMass u) := by
  apply monotone_nat_of_le_succ
  intro i
  cases i with
  | zero => exact Nat.cast_nonneg _
  | succ i => exact Nat.cast_le.mpr (jensenNonrealCount_mono (hu (Nat.le_succ i)))

private theorem sampled_bdd {u : ℕ → ℕ} (hu : StrictMono u) :
    BddAbove (Set.range (sampledJensenMass u)) ↔ ∃ K : ℕ, ∀ d, jensenNonrealCount d ≤ K := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨⌈B⌉₊,fun d => ?_⟩
    have hh : (jensenNonrealCount (u d):ℝ) ≤ B := hB ⟨d+1,rfl⟩
    exact (jensenNonrealCount_mono (hu.id_le d)).trans (Nat.cast_le.mp (hh.trans (Nat.le_ceil B)))
  · rintro ⟨K,hK⟩
    refine ⟨K,?_⟩
    rintro _ ⟨i,rfl⟩
    cases i with
    | zero => exact Nat.cast_nonneg _
    | succ i => exact Nat.cast_le.mpr (hK _)

/-- A cofinal sequence of degrees, with any gaps, has the same sharp
discount threshold. Any subcritical convergence detects finite off-line
support for the actual Xi function. -/
theorem sparse_jensen_charge_summable_iff {u : ℕ → ℕ} (hu : StrictMono u) (p : ℝ) :
    Summable (powerCharge (sampledJensenMass u) p) ↔
      1 < p ∨ {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite := by
  rw [summable_power_charge_arbitrary_jumps (sampled_mono hu.monotone) (by rfl : 0 ≤ sampledJensenMass u 0),
    sampled_bdd hu,bddAbove_jensenNonrealCount_iff]

private theorem fraction_le_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a/(1+a) ≤ b/(1+b) ↔ a ≤ b := by
  rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one ha) (add_pos_of_pos_of_nonneg zero_lt_one hb)]
  constructor <;> intro h <;> linarith only [h]

/-- The entire off-line divisor has multiplicity at most m precisely when
some cofinal observation schedule meets the budget m/(1+m) arbitrarily
late. If the divisor is finite, placing the first sample after its last
arrival attains the lower block bound. -/
theorem off_line_count_iff_sparse_charge_budget (m : ℕ) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m ↔
      ∃ u : ℕ → ℕ, StrictMono u ∧ ∃ᶠ n : ℕ in atTop,
        (∑ i ∈ range (n+1), powerCharge (sampledJensenMass u) 1 i) ≤ (m:ℝ)/(1+m) := by
  constructor
  · intro h
    have hfin := Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.coe_ne_top m) h)
    obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_jensenNonrealCount_eq_of_finite hfin)
    let u := fun i : ℕ => K+i
    have hcount (i : ℕ) : jensenNonrealCount (u i) = hfin.toFinset.card := hK _ (Nat.le_add_right _ _)
    have hm : hfin.toFinset.card ≤ m := by
      rw [hfin.encard_eq_coe_toFinset_card] at h
      exact_mod_cast h
    refine ⟨u,fun _ _ hab => Nat.add_lt_add_left hab K,(Eventually.of_forall fun n => ?_).frequently⟩
    rw [sum_range_succ']
    have he (i : ℕ) : powerCharge (sampledJensenMass u) 1 (i+1) = 0 := by
      simp only [powerCharge,sampledJensenMass,hcount,sub_self,zero_mul]
    simp only [he,sum_const_zero,zero_add,powerCharge,sampledJensenMass,hcount,sub_zero,Real.rpow_neg_one,
      ← div_eq_mul_inv]
    exact (fraction_le_iff (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (Nat.cast_le.mpr hm)
  · rintro ⟨u,hu,h⟩
    apply encard_offLine_le_iff_forall.mpr
    intro d
    obtain ⟨n,hn,hn'⟩ := (h.and_eventually (eventually_ge_atTop d)).exists
    have hh := (reciprocal_block_bounds (sampled_mono hu.monotone) (by rfl : 0 ≤ sampledJensenMass u 0) 0 (n+1)).1
    simp only [Nat.zero_add,sampledJensenMass,sub_zero] at hh
    have bound := (fraction_le_iff (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp (hh.trans hn)
    exact (jensenNonrealCount_mono (hn'.trans (hu.id_le n))).trans (Nat.cast_le.mp bound)

#print axioms sparse_jensen_charge_summable_iff
#print axioms off_line_count_iff_sparse_charge_budget

end GaloisForLFunctions.GaloisTheoryOfZeros
