import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant
import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOne
import GaloisForLFunctions.HTGeometry.TorusConditionalProductL2

/-!
# The zero–one law for the gauge exponent

The Möbius gauge exponent does not change when finitely many prime coordinates of a gauge point
change (`gaugeExponent_moebius_eq_of_agree_off_finset`), and twists ignore the coordinates that are
not prime. So every sublevel set of the exponent is invariant under finite modification; the same
holds for every tail-invariant source. Haar measure
on the gauge torus is the product of the circle Haar measures (`HTGeometry.torusHaar_eq_infinitePi`),
and the finite-modification zero–one law (`HTGeometry.measure_infinitePi_eq_zero_or_one_of_invariant`)
applies.

* **Measurability** (`measurableSet_gaugePowerBound`, `measurableSet_gaugeExponent_le`). Sublevel sets
  are countable intersections of countable unions of closed sets.
* **Tail invariance** (`IsTailInvariant`, `isTailInvariant_of_one_prime`). A source whose exponent
  ignores one prime coordinate at a time ignores finitely many; the Möbius source is tail invariant
  (`isTailInvariant_moebius`), so points that differ in finitely many coordinates have the same
  exponent (`gaugeExponent_moebius_eq_of_finite_diff`).
* **Zero–one law** (`gaugeHaar_gaugeExponent_le_eq_zero_or_one'`). For a bounded tail-invariant
  source and every `θ`, the set of gauge points of exponent at most `θ` has Haar measure `0` or `1`.
* **The typical exponent** (`ae_gaugeExponent_eq_typical`, `ae_gaugeExponent_moebius_eq_typical`).
  There is a constant `θ_typ(a) ≤ 1/2` equal to the exponent at Haar-almost every point.

So the gauge torus has a single typical exponent, as `ℝ` has the almost-sure irrationality exponent
`2`. The trivial point's exponent is `Θ`; RH says `Θ ≤ 1/2`. The typical value is exactly `1/2`
(`TheTypicalExponentIsOneHalf`).
-/

open MeasureTheory Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

variable {a : ℕ → ℂ}

/-! ### Measurability -/

/-- Twisted partial sums are continuous in the gauge point. -/
theorem continuous_partialSum (a : ℕ → ℂ) (N : ℕ) :
    Continuous fun x : GaugeTorus => ∑ n ∈ range (N + 1), a n * twist x n :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_twist n)

theorem continuous_moebiusPartialSum (N : ℕ) :
    Continuous fun x : GaugeTorus => ∑ n ∈ range (N + 1), moebiusSource n * twist x n :=
  continuous_partialSum moebiusSource N

/-- The power-bound set is a countable union of closed sets. -/
theorem setOf_gaugePowerBound_eq (a : ℕ → ℂ) (θ : ℝ) :
    {x : GaugeTorus | GaugePowerBound a x θ} =
      ⋃ C : ℕ, ⋂ N : ℕ, {x : GaugeTorus |
        ‖∑ n ∈ range (N + 1), a n * twist x n‖ ≤ (C : ℝ) * ((N : ℝ) + 1) ^ θ} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, GaugePowerBound]
  constructor
  · rintro ⟨C, -, hb⟩
    refine ⟨⌈C⌉₊, fun N => (hb N).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)
  · rintro ⟨C, hb⟩
    exact ⟨C, by positivity, hb⟩

theorem measurableSet_gaugePowerBound (a : ℕ → ℂ) (θ : ℝ) :
    MeasurableSet {x : GaugeTorus | GaugePowerBound a x θ} := by
  rw [setOf_gaugePowerBound_eq]
  refine MeasurableSet.iUnion fun C => MeasurableSet.iInter fun N => ?_
  exact (isClosed_le (continuous_partialSum a N).norm continuous_const).measurableSet

/-- Sublevel sets of the exponent, through the power bounds just above the level. -/
theorem setOf_gaugeExponent_le_eq (ha : ∀ n, ‖a n‖ ≤ 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    {x : GaugeTorus | gaugeExponent a x ≤ θ} =
      ⋂ k : ℕ, {x : GaugeTorus | GaugePowerBound a x (θ + 1 / ((k : ℝ) + 1))} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h k
    exact gaugePowerBound_of_gaugeExponent_lt ha
      (lt_of_le_of_lt h (by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
                            linarith))
  · intro h
    refine gaugeExponent_le_of_forall hθ fun δ hδ => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    exact (h k).mono (by linarith)

theorem measurableSet_gaugeExponent_le (ha : ∀ n, ‖a n‖ ≤ 1) (θ : ℝ) :
    MeasurableSet {x : GaugeTorus | gaugeExponent a x ≤ θ} := by
  rcases lt_or_ge θ 0 with hθ | hθ
  · have hempty : {x : GaugeTorus | gaugeExponent a x ≤ θ} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hθ (gaugeExponent_nonneg ha)
    rw [hempty]
    exact MeasurableSet.empty
  · rw [setOf_gaugeExponent_le_eq ha hθ]
    exact MeasurableSet.iInter fun k => measurableSet_gaugePowerBound a _

/-! ### Tail invariance -/

/-- Gauge points with the same twists have the same exponent. -/
theorem gaugeExponent_congr {x x' : GaugeTorus} (h : ∀ n, twist x' n = twist x n) :
    gaugeExponent a x' = gaugeExponent a x := by
  unfold gaugeExponent exponentSet
  congr 1
  ext θ
  simp only [Set.mem_setOf_eq, GaugePowerBound, h]

/-- Gauge points that agree at every prime have the same twists. -/
theorem twist_eq_of_forall_primes {x x' : GaugeTorus} (h : ∀ q, q.Prime → twist x' q = twist x q)
    (n : ℕ) : twist x' n = twist x n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [twist_at_zero, twist_at_zero]
  · exact twist_eq_of_primes hn.ne' fun q hq _ => h q hq

/-- A source is **tail invariant** if its exponent ignores finitely many prime coordinates. -/
def IsTailInvariant (a : ℕ → ℂ) : Prop :=
  ∀ (F : Finset ℕ) (x x' : GaugeTorus), (∀ q, q.Prime → q ∉ F → twist x' q = twist x q) →
    gaugeExponent a x' = gaugeExponent a x

/-- Invariance under one prime at a time gives tail invariance. -/
theorem isTailInvariant_of_one_prime
    (h1 : ∀ p, p.Prime → ∀ x x' : GaugeTorus,
      (∀ q, q.Prime → q ≠ p → twist x' q = twist x q) → gaugeExponent a x' = gaugeExponent a x) :
    IsTailInvariant a := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro x x' h
    exact gaugeExponent_congr (twist_eq_of_forall_primes fun q hq => h q hq (notMem_empty q))
  | insert p F hpF ih =>
    intro x x' h
    -- Move `x'` to `x` at the coordinate `p` first.
    set z : GaugeTorus := Function.update x' p (x p) with hz
    have hzx : ∀ q, q.Prime → q ∉ F → twist z q = twist x q := by
      intro q hq hqF
      by_cases hqp : q = p
      · subst hqp
        rw [twist_prime_apply z hq, twist_prime_apply x hq, hz, Function.update_self]
      · rw [twist_prime_apply z hq, hz, Function.update_of_ne hqp, ← twist_prime_apply x' hq]
        exact h q hq (by simp [hqp, hqF])
    have hzx' : ∀ q, q.Prime → q ≠ p → twist x' q = twist z q := by
      intro q hq hqp
      rw [twist_prime_apply z hq, twist_prime_apply x' hq, hz, Function.update_of_ne hqp]
    have hstep : gaugeExponent a x' = gaugeExponent a z := by
      by_cases hp : p.Prime
      · exact h1 p hp z x' hzx'
      · exact gaugeExponent_congr (twist_eq_of_forall_primes fun q hq =>
          hzx' q hq fun hqp => hp (hqp ▸ hq))
    rw [hstep, ih x z hzx]

theorem isTailInvariant_moebius : IsTailInvariant moebiusSource :=
  fun F _ _ h => gaugeExponent_moebius_eq_of_agree_off_finset F h

/-! ### Finite modifications and the zero–one law -/

/-- **Finite modifications preserve the exponent** of a tail-invariant source. -/
theorem gaugeExponent_eq_of_finite_diff (ht : IsTailInvariant a) {x y : GaugeTorus}
    (h : {m | x m ≠ y m}.Finite) : gaugeExponent a y = gaugeExponent a x := by
  refine ht h.toFinset x y fun q hq hqF => ?_
  have hxy : x q = y q := by
    by_contra hne
    exact hqF (h.mem_toFinset.mpr hne)
  rw [twist_prime_apply y hq, twist_prime_apply x hq, hxy]

theorem gaugeExponent_moebius_eq_of_finite_diff {x y : GaugeTorus}
    (h : {m | x m ≠ y m}.Finite) :
    gaugeExponent moebiusSource y = gaugeExponent moebiusSource x :=
  gaugeExponent_eq_of_finite_diff isTailInvariant_moebius h

/-- **The zero–one law.** For a bounded tail-invariant source, every sublevel set of the exponent
has Haar measure `0` or `1`. -/
theorem gaugeHaar_gaugeExponent_le_eq_zero_or_one' (ha : ∀ n, ‖a n‖ ≤ 1) (ht : IsTailInvariant a)
    (θ : ℝ) : gaugeHaar {x : GaugeTorus | gaugeExponent a x ≤ θ} = 0 ∨
      gaugeHaar {x : GaugeTorus | gaugeExponent a x ≤ θ} = 1 := by
  have hHaar : gaugeHaar = Measure.infinitePi (fun _ : ℕ => AddCircle.haarAddCircle) :=
    HTGeometry.torusHaar_eq_infinitePi
  rw [hHaar]
  refine HTGeometry.measure_infinitePi_eq_zero_or_one_of_invariant _ (0 : GaugeTorus)
    (measurableSet_gaugeExponent_le ha θ) fun x y hxy => ?_
  simp only [Set.mem_setOf_eq, gaugeExponent_eq_of_finite_diff ht hxy]

theorem gaugeHaar_gaugeExponent_le_eq_zero_or_one (θ : ℝ) :
    gaugeHaar {x : GaugeTorus | gaugeExponent moebiusSource x ≤ θ} = 0 ∨
      gaugeHaar {x : GaugeTorus | gaugeExponent moebiusSource x ≤ θ} = 1 :=
  gaugeHaar_gaugeExponent_le_eq_zero_or_one' norm_moebiusSource_le isTailInvariant_moebius θ

/-- The levels at which the sublevel set is almost everything. -/
def typicalLevels (a : ℕ → ℂ) : Set ℝ :=
  {θ | gaugeHaar {x : GaugeTorus | gaugeExponent a x ≤ θ} = 1}

/-- **The typical exponent** of a source. -/
def typicalExponent (a : ℕ → ℂ) : ℝ := sInf (typicalLevels a)

/-- A measurable set of Haar measure one is almost everything. -/
theorem ae_mem_of_measure_eq_one {S : Set GaugeTorus} (hS : MeasurableSet S) (h1 : gaugeHaar S = 1) :
    ∀ᵐ x ∂gaugeHaar, x ∈ S :=
  mem_ae_iff.mpr ((prob_compl_eq_zero_iff hS).mpr h1)

theorem half_mem_typicalLevels (ha : ∀ n, ‖a n‖ ≤ 1) : (1 / 2 : ℝ) ∈ typicalLevels a := by
  have hae := ae_gaugeExponent_le_half ha
  rw [typicalLevels, Set.mem_setOf_eq,
    ← prob_compl_eq_zero_iff (measurableSet_gaugeExponent_le ha (1 / 2))]
  exact ae_iff.mp hae

theorem typicalLevels_nonneg (ha : ∀ n, ‖a n‖ ≤ 1) {θ : ℝ} (hθ : θ ∈ typicalLevels a) :
    0 ≤ θ := by
  by_contra hneg
  push Not at hneg
  have hempty : {x : GaugeTorus | gaugeExponent a x ≤ θ} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hneg (gaugeExponent_nonneg ha)
  rw [typicalLevels, Set.mem_setOf_eq, hempty, measure_empty] at hθ
  exact zero_ne_one hθ

theorem bddBelow_typicalLevels (ha : ∀ n, ‖a n‖ ≤ 1) : BddBelow (typicalLevels a) :=
  ⟨0, fun _ h => typicalLevels_nonneg ha h⟩

theorem typicalExponent_le_half (ha : ∀ n, ‖a n‖ ≤ 1) : typicalExponent a ≤ 1 / 2 :=
  csInf_le (bddBelow_typicalLevels ha) (half_mem_typicalLevels ha)

/-- **The exponent is almost surely equal to the typical exponent.** -/
theorem ae_gaugeExponent_eq_typical (ha : ∀ n, ‖a n‖ ≤ 1) (ht : IsTailInvariant a) :
    ∀ᵐ x ∂gaugeHaar, gaugeExponent a x = typicalExponent a := by
  have hne : (typicalLevels a).Nonempty := ⟨_, half_mem_typicalLevels ha⟩
  -- Above the typical exponent every level is typical.
  have hup : ∀ k : ℕ, ∀ᵐ x ∂gaugeHaar,
      gaugeExponent a x ≤ typicalExponent a + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨θ, hθT, hθlt⟩ := exists_lt_of_csInf_lt hne
      (show typicalExponent a < typicalExponent a + 1 / ((k : ℝ) + 1) by linarith)
    have hmeas : gaugeHaar {x : GaugeTorus |
        gaugeExponent a x ≤ typicalExponent a + 1 / ((k : ℝ) + 1)} = 1 :=
      le_antisymm prob_le_one (le_of_eq_of_le hθT.symm
        (measure_mono fun x (hx : gaugeExponent a x ≤ θ) => hx.trans hθlt.le))
    exact ae_mem_of_measure_eq_one (measurableSet_gaugeExponent_le ha _) hmeas
  -- Below the typical exponent no level is typical, so the sublevel set is null.
  have hdown : ∀ k : ℕ, ∀ᵐ x ∂gaugeHaar,
      typicalExponent a - 1 / ((k : ℝ) + 1) < gaugeExponent a x := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hnot : typicalExponent a - 1 / ((k : ℝ) + 1) ∉ typicalLevels a := fun hmem => by
      have := csInf_le (bddBelow_typicalLevels ha) hmem
      rw [typicalExponent] at *
      linarith
    have h0 : gaugeHaar {x : GaugeTorus |
        gaugeExponent a x ≤ typicalExponent a - 1 / ((k : ℝ) + 1)} = 0 :=
      (gaugeHaar_gaugeExponent_le_eq_zero_or_one' ha ht _).resolve_right hnot
    refine ae_iff.mpr ?_
    simpa only [not_lt] using h0
  filter_upwards [ae_all_iff.mpr hup, ae_all_iff.mpr hdown] with x hx1 hx2
  refine le_antisymm (le_of_forall_pos_lt_add fun δ hδ => ?_) (le_of_forall_pos_lt_add fun δ hδ => ?_)
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    linarith [hx1 k]
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    linarith [hx2 k]

theorem ae_gaugeExponent_moebius_eq_typical :
    ∀ᵐ x ∂gaugeHaar, gaugeExponent moebiusSource x = typicalExponent moebiusSource :=
  ae_gaugeExponent_eq_typical norm_moebiusSource_le isTailInvariant_moebius

end GaloisForLFunctions.ArithmeticGaugeTheory
