import GaloisForLFunctions.SignedArithmeticEnergyIncidence.SignedIncidenceForms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Balanced incidence is locally payable

**Theorem** (`locallyPayable_of_nonneg_of_nonpositiveOverlaps`).  A nonnegative signed incidence form
whose overlap charges are all nonpositive is locally payable: there is one allocation of the
budgets that pays every overlap once.  With switching (`nonneg_iff_locallyPayable_of_isBalanced`):
for a **balanced** form, global positivity and local payment are the same property.

The proof is the discrete Allegretto–Piepenbrink principle.

1. *Inverse positivity* (`exists_pos_solution_of_coercive`): a coercive form with nonpositive
   overlaps has a strictly positive solution of `Cv = 1`.  The solution minimizes
   `E(f) − 2 Σ f_i`; replacing `v` by `|v|` does not raise the energy when the overlaps are
   nonpositive, so `|v| = v` by strict convexity, and `Cv = 1` then forces `v_i > 0`.
2. The positive solution is a positive supersolution, hence a local allocation of the regularized
   form `c + t δ` (`SignedIncidenceForms.locallyPayable_of_supersolution`).
3. The allocations of `c + δ/(n+1)` lie in a fixed compact box; a convergent subsequence is a local
   allocation of `c` itself, because every defining inequality is closed.

The theorem is the positive half of the signed local–global principle; the frustrated triangle of
`FrustrationIsTheLocalGlobalGap` shows that balance cannot be dropped.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The form `c + t δ`: every budget raised by `t`. -/
def regularizedCoupling (c : ι → ι → ℝ) (t : ℝ) : ι → ι → ℝ :=
  fun i j => if i = j then c i j + t else c i j

theorem incidenceEnergy_regularized (c : ι → ι → ℝ) (t : ℝ) (f : ι → ℝ) :
    incidenceEnergy (regularizedCoupling c t) f = incidenceEnergy c f + t * ∑ i, f i ^ 2 := by
  have e : ∀ i j, regularizedCoupling c t i j * f i * f j =
      c i j * f i * f j + if i = j then t * f i ^ 2 else 0 := by
    intro i j
    unfold regularizedCoupling
    split_ifs with h
    · subst h; ring
    · ring
  unfold incidenceEnergy
  simp only [e, sum_add_distrib, sum_ite_eq, mem_univ, if_true, mul_sum]

omit [Fintype ι] in
theorem IsSymmetricCoupling.regularized {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (t : ℝ) :
    IsSymmetricCoupling (regularizedCoupling c t) := by
  intro i j
  unfold regularizedCoupling
  by_cases h : i = j
  · subst h; rfl
  · simp only [h, Ne.symm h, if_false]
    exact hc i j

omit [Fintype ι] in
theorem HasNonpositiveOverlaps.regularized {c : ι → ι → ℝ} (hz : HasNonpositiveOverlaps c)
    (t : ℝ) : HasNonpositiveOverlaps (regularizedCoupling c t) := by
  intro i j hij
  simp only [regularizedCoupling, hij, if_false]
  exact hz i j hij

omit [DecidableEq ι] in
/-- The coupling action as a linear map. -/
def couplingActionLinear (c : ι → ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v i := couplingAction c v i
  map_add' f g := by
    funext i
    simp only [couplingAction, Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' r f := by
    funext i
    simp only [couplingAction, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- Replacing a profile by its absolute value does not raise the energy of a form with nonpositive
overlaps. -/
theorem incidenceEnergy_abs_le {c : ι → ι → ℝ} (hz : HasNonpositiveOverlaps c) (f : ι → ℝ) :
    incidenceEnergy c (fun i => |f i|) ≤ incidenceEnergy c f := by
  unfold incidenceEnergy
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  by_cases h : i = j
  · subst h
    rw [mul_assoc, mul_assoc, abs_mul_abs_self]
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonpos_left (by rw [← abs_mul]; exact le_abs_self _) (hz i j h)

/-- **Inverse positivity.**  A form with nonpositive overlaps and coercivity `t Σ f_i² ≤ E(f)`,
`t > 0`, has a strictly positive solution of `Cv = 1`. -/
theorem exists_pos_solution_of_coercive {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hz : HasNonpositiveOverlaps c) {t : ℝ} (ht : 0 < t)
    (hcoer : ∀ f, t * ∑ i, f i ^ 2 ≤ incidenceEnergy c f) :
    ∃ v : ι → ℝ, (∀ i, 0 < v i) ∧ ∀ i, couplingAction c v i = 1 := by
  set L := couplingActionLinear c
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hE : incidenceEnergy c f = 0 := by
      rw [incidenceEnergy_eq_sum_mul_couplingAction]
      refine sum_eq_zero fun i _ => ?_
      have : couplingAction c f i = 0 := congrFun hf i
      rw [this, mul_zero]
    have hsum : ∑ i, f i ^ 2 = 0 := by
      have h1 := hcoer f
      rw [hE] at h1
      have h2 : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (f i)).mp hsum i (mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun _ => 1)
  have hCv : ∀ i, couplingAction c v i = 1 := fun i => congrFun hv i
  -- `v ≥ 0`: the absolute value is an equally good minimizer
  have hEv : incidenceEnergy c v = ∑ i, v i := by
    rw [incidenceEnergy_eq_sum_mul_couplingAction]
    simp [hCv]
  have hdiff := incidenceEnergy_sub hc (fun i => |v i|) v
  have hpair : ∑ i, |v i| * couplingAction c v i = ∑ i, |v i| := by simp [hCv]
  have hle : incidenceEnergy c (fun i => |v i| - v i) ≤ 0 := by
    rw [hdiff, hpair, hEv]
    have h1 := incidenceEnergy_abs_le hz v
    have h2 : ∑ i, v i ≤ ∑ i, |v i| := sum_le_sum fun i _ => le_abs_self _
    rw [hEv] at h1
    linarith
  have hsq : ∑ i, (|v i| - v i) ^ 2 = 0 := by
    have h1 := hcoer (fun i => |v i| - v i)
    have h2 : 0 ≤ ∑ i, (|v i| - v i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  have hnn : ∀ i, 0 ≤ v i := by
    intro i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (|v i| - v i)).mp hsq i (mem_univ i)
    have h0 : |v i| - v i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have : v i = |v i| := by linarith
    rw [this]
    exact abs_nonneg _
  -- `v > 0`: the equation at `i` would fail at `v_i = 0`
  refine ⟨v, fun i => ?_, hCv⟩
  have hact : couplingAction c v i = c i i * v i + ∑ j ∈ univ.erase i, c i j * v j := by
    unfold couplingAction
    rw [← add_sum_erase _ _ (mem_univ i)]
  have hoff : ∑ j ∈ univ.erase i, c i j * v j ≤ 0 :=
    sum_nonpos fun j hj => mul_nonpos_of_nonpos_of_nonneg (hz i j (ne_of_mem_erase hj).symm) (hnn j)
  rcases (hnn i).eq_or_lt with h0 | hpos
  · have := hCv i
    rw [hact, ← h0, mul_zero, zero_add] at this
    linarith
  · exact hpos

/-- A coercive form with nonpositive overlaps is locally payable. -/
theorem locallyPayable_of_coercive {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hz : HasNonpositiveOverlaps c) {t : ℝ} (ht : 0 < t)
    (hcoer : ∀ f, t * ∑ i, f i ^ 2 ≤ incidenceEnergy c f) : LocallyPayable c := by
  obtain ⟨v, hv, hCv⟩ := exists_pos_solution_of_coercive hc hz ht hcoer
  exact locallyPayable_of_supersolution hc hz hv fun i => by rw [hCv i]; norm_num

/-- **Balanced incidence is locally payable.**  A nonnegative form whose overlap charges are all
nonpositive admits a local allocation. -/
theorem locallyPayable_of_nonneg_of_nonpositiveOverlaps {c : ι → ι → ℝ}
    (hc : IsSymmetricCoupling c) (hz : HasNonpositiveOverlaps c)
    (h : ∀ f, 0 ≤ incidenceEnergy c f) : LocallyPayable c := by
  -- allocations of the regularized forms `c + δ/(n+1)`, normalized off the diagonal
  have hreg : ∀ n : ℕ, LocallyPayable (regularizedCoupling c (1 / ((n : ℝ) + 1))) := by
    intro n
    have ht : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine locallyPayable_of_coercive (hc.regularized _) (hz.regularized _) ht fun f => ?_
    rw [incidenceEnergy_regularized]
    linarith [h f]
  have A : ∀ n : ℕ, PairAllocation (regularizedCoupling c (1 / ((n : ℝ) + 1))) :=
    fun n => (hreg n).some
  set a : ℕ → ι → ι → ℝ := fun n => (A n).offDiagonal.share with ha
  have ha_nonneg : ∀ n i j, 0 ≤ a n i j := fun n i j => (A n).offDiagonal.share_nonneg i j
  have ha_diag : ∀ n i, a n i i = 0 := fun n i => (A n).offDiagonal_share_self i
  have ha_pays : ∀ n i j, i ≠ j → c i j ^ 2 ≤ a n i j * a n j i := by
    intro n i j hij
    have := (A n).offDiagonal.pays i j hij
    simpa only [regularizedCoupling, hij, if_false] using this
  have ha_budget : ∀ n i, ∑ j ∈ univ.erase i, a n i j ≤ c i i + 1 / ((n : ℝ) + 1) := by
    intro n i
    have := (A n).offDiagonal.within_budget i
    simpa only [regularizedCoupling, if_true] using this
  -- a fixed compact box contains every normalized allocation
  set K : Set (ι → ι → ℝ) := Set.univ.pi fun i => Set.univ.pi fun _ => Set.Icc 0 (|c i i| + 1)
    with hK
  have hKc : IsCompact K := isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_Icc
  have haK : ∀ n, a n ∈ K := by
    intro n
    simp only [hK, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i j
    refine ⟨ha_nonneg n i j, ?_⟩
    by_cases hij : j = i
    · subst hij; rw [ha_diag]; positivity
    · have h1 : a n i j ≤ ∑ k ∈ univ.erase i, a n i k :=
        single_le_sum (fun k _ => ha_nonneg n i k) (mem_erase.mpr ⟨hij, mem_univ j⟩)
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h3 := ha_budget n i
      have h4 := le_abs_self (c i i)
      linarith
  obtain ⟨a₀, -, φ, hφ, hlim⟩ := hKc.tendsto_subseq haK
  have hcoord : ∀ i j, Tendsto (fun n => a (φ n) i j) atTop (𝓝 (a₀ i j)) := by
    intro i j
    have h1 := tendsto_pi_nhds.mp hlim i
    exact tendsto_pi_nhds.mp h1 j
  refine ⟨{ share := a₀
            share_nonneg := fun i j =>
              ge_of_tendsto' (hcoord i j) fun n => ha_nonneg (φ n) i j
            pays := fun i j hij =>
              ge_of_tendsto' ((hcoord i j).mul (hcoord j i)) fun n => ha_pays (φ n) i j hij
            within_budget := fun i => ?_ }⟩
  have hsum : Tendsto (fun n => ∑ j ∈ univ.erase i, a (φ n) i j) atTop
      (𝓝 (∑ j ∈ univ.erase i, a₀ i j)) :=
    tendsto_finsetSum _ fun j _ => hcoord i j
  have hdecay' : Tendsto (fun n => c i i + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (c i i)) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add (h0.comp hφ.tendsto_atTop)
  exact le_of_tendsto_of_tendsto' hsum hdecay' fun n => ha_budget (φ n) i

/-- **Signed local–global principle, balanced half.**  For a balanced form, nonnegativity is
equivalent to local payability. -/
theorem nonneg_iff_locallyPayable_of_isBalanced {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hb : IsBalanced c) : (∀ f, 0 ≤ incidenceEnergy c f) ↔ LocallyPayable c := by
  obtain ⟨s, hs, hz⟩ := hb
  constructor
  · intro h
    have h' : ∀ f, 0 ≤ incidenceEnergy (switchCoupling s c) f := (nonneg_switch_iff hs).mpr h
    exact (locallyPayable_switch_iff hs).mp
      (locallyPayable_of_nonneg_of_nonpositiveOverlaps (hc.switch s) hz h')
  · exact incidenceEnergy_nonneg_of_locallyPayable hc

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
