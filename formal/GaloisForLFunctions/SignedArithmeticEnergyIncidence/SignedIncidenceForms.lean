import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Signed incidence forms and local payment

A **signed incidence form** on a finite set `ι` of incidence points is a symmetric coupling
`c : ι → ι → ℝ`; its energy at a profile `f` is `Σ_{i,j} c_ij f_i f_j`.  The diagonal `c_ii` is
the budget owned by the point `i`; an off-diagonal `c_ij` is the signed charge of the overlap of
`i` and `j`.

A **local allocation** (`PairAllocation`) lets every point lend nonnegative shares of its own budget
to the overlaps it meets, `Σ_{j ≠ i} a_ij ≤ c_ii`, so that every overlap is paid by the shares it
receives from its two ends, `c_ij² ≤ a_ij a_ji`.  Nothing is spent twice: a share leaves exactly one
budget and enters exactly one overlap.  A locally payable form has nonnegative energy
(`incidenceEnergy_nonneg_of_pairAllocation`); the converse is the local–global problem.

Two tools fix the language:

* **switching** (`switchCoupling`) by signs `s_i = ±1` changes the coupling to `s_i s_j c_ij`
  without changing the energy landscape or the payability; a form is **balanced** when some
  switching makes every overlap charge nonpositive;
* the **ground-state transform** (`incidenceEnergy_mul_eq`): for any gauge `v`,
  `E(v g) = Σ_i v_i (Cv)_i g_i² − ½ Σ_{i,j} c_ij v_i v_j (g_i − g_j)²`.  A strictly positive gauge
  whose weighted overlaps are dominated by the weighted budget pays every overlap
  (`locallyPayable_of_weightedDominance`); for nonpositive overlaps this is a positive
  supersolution `Cv ≥ 0` (`locallyPayable_of_supersolution`).
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Objects -/

/-- The coupling of a signed incidence form is symmetric. -/
def IsSymmetricCoupling (c : ι → ι → ℝ) : Prop := ∀ i j, c i j = c j i

/-- The energy `Σ_{i,j} c_ij f_i f_j` of the profile `f`. -/
def incidenceEnergy (c : ι → ι → ℝ) (f : ι → ℝ) : ℝ := ∑ i, ∑ j, c i j * f i * f j

/-- The action `(Cv)_i = Σ_j c_ij v_j` of the coupling on a gauge. -/
def couplingAction (c : ι → ι → ℝ) (v : ι → ℝ) (i : ι) : ℝ := ∑ j, c i j * v j

/-- A **local allocation**: every point lends nonnegative shares of its own budget to the overlaps
it meets, every overlap is paid by the two shares it receives, and no point lends more than its
budget. -/
structure PairAllocation (c : ι → ι → ℝ) where
  /-- The share `a_ij` that the point `i` lends to the overlap `{i, j}`. -/
  share : ι → ι → ℝ
  share_nonneg : ∀ i j, 0 ≤ share i j
  pays : ∀ i j, i ≠ j → c i j ^ 2 ≤ share i j * share j i
  within_budget : ∀ i, ∑ j ∈ univ.erase i, share i j ≤ c i i

/-- A form is **locally payable** when it admits a local allocation. -/
def LocallyPayable (c : ι → ι → ℝ) : Prop := Nonempty (PairAllocation c)

/-- All overlap charges are nonpositive: the aligned sign pattern. -/
def HasNonpositiveOverlaps (c : ι → ι → ℝ) : Prop := ∀ i j, i ≠ j → c i j ≤ 0

/-- Switching by a sign vector `s`. -/
def switchCoupling (s : ι → ℝ) (c : ι → ι → ℝ) : ι → ι → ℝ := fun i j => s i * s j * c i j

/-- A form is **balanced** when some switching by signs `s_i = ±1` aligns every overlap. -/
def IsBalanced (c : ι → ι → ℝ) : Prop :=
  ∃ s : ι → ℝ, (∀ i, s i ^ 2 = 1) ∧ HasNonpositiveOverlaps (switchCoupling s c)

/-! ### Elementary algebra of the energy -/

/-- A binary form `a x² + 2 c x y + b y²` with `a, b ≥ 0` and `c² ≤ a b` is nonnegative. -/
theorem binaryForm_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ^ 2 ≤ a * b) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * c * x * y + b * y ^ 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with h0 | hpos
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    have hc : c = 0 := by nlinarith [sq_nonneg c]
    subst hc
    simp
  · have key : (a + b) * (a * x ^ 2 + 2 * c * x * y + b * y ^ 2) =
        (a * x + c * y) ^ 2 + (c * x + b * y) ^ 2 + (a * b - c ^ 2) * (x ^ 2 + y ^ 2) := by ring
    have hk : 0 ≤ (a + b) * (a * x ^ 2 + 2 * c * x * y + b * y ^ 2) := by
      rw [key]
      have := sub_nonneg.mpr h
      positivity
    exact (mul_nonneg_iff_of_pos_left hpos).mp hk

/-- The energy splits into the budgets and the off-diagonal overlaps. -/
theorem incidenceEnergy_eq_diag_add_offDiag (c : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy c f =
      ∑ i, c i i * f i ^ 2 + ∑ i, ∑ j ∈ univ.erase i, c i j * f i * f j := by
  unfold incidenceEnergy
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← add_sum_erase _ _ (mem_univ i)]
  ring

/-- Summing over ordered pairs of distinct points is invariant under swapping the pair. -/
theorem sum_offDiag_swap (p : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, p i j = ∑ i, ∑ j ∈ univ.erase i, p j i := by
  have h (q : ι → ι → ℝ) :
      ∑ i, ∑ j ∈ univ.erase i, q i j = ∑ i, ∑ j, q i j - ∑ i, q i i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_erase_eq_sub (mem_univ i)
  rw [h, h, sum_comm]

omit [DecidableEq ι] in
/-- The energy of a symmetric form is the polarization of its bilinear pairing. -/
theorem incidenceEnergy_sub {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (f g : ι → ℝ) :
    incidenceEnergy c (fun i => f i - g i) =
      incidenceEnergy c f - 2 * ∑ i, f i * couplingAction c g i + incidenceEnergy c g := by
  have hswap : ∑ i, ∑ j, c i j * g i * f j = ∑ i, ∑ j, c i j * f i * g j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hc j i]; ring
  have hact : ∑ i, f i * couplingAction c g i = ∑ i, ∑ j, c i j * f i * g j := by
    unfold couplingAction
    exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  unfold incidenceEnergy
  rw [hact]
  have e : ∀ i j, c i j * (f i - g i) * (f j - g j) =
      c i j * f i * f j - c i j * f i * g j - c i j * g i * f j + c i j * g i * g j := by
    intro i j; ring
  simp only [e, sum_add_distrib, sum_sub_distrib]
  rw [hswap]
  ring

omit [DecidableEq ι] in
/-- `E(f) = Σ_i f_i (Cf)_i`. -/
theorem incidenceEnergy_eq_sum_mul_couplingAction (c : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy c f = ∑ i, f i * couplingAction c f i := by
  unfold incidenceEnergy couplingAction
  exact sum_congr rfl fun i _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring

/-! ### Local payment implies positivity -/

/-- **Local payment implies positivity.**  The energy is the unspent budget
`Σ_i (c_ii − Σ_{j≠i} a_ij) f_i²` plus, over unordered overlaps, the binary forms
`a_ij f_i² + 2 c_ij f_i f_j + a_ji f_j²`, each nonnegative because the overlap is paid. -/
theorem incidenceEnergy_nonneg_of_pairAllocation {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (A : PairAllocation c) (f : ι → ℝ) : 0 ≤ incidenceEnergy c f := by
  set p : ι → ι → ℝ := fun i j => A.share i j * f i ^ 2 + c i j * f i * f j with hp
  have e1 : ∀ i, ∑ j ∈ univ.erase i, p i j =
      (∑ j ∈ univ.erase i, A.share i j) * f i ^ 2 + ∑ j ∈ univ.erase i, c i j * f i * f j := by
    intro i
    simp only [hp, sum_add_distrib, sum_mul]
  have hsplit : incidenceEnergy c f =
      ∑ i, (c i i - ∑ j ∈ univ.erase i, A.share i j) * f i ^ 2 +
        ∑ i, ∑ j ∈ univ.erase i, p i j := by
    rw [incidenceEnergy_eq_diag_add_offDiag, sum_congr rfl fun i _ => e1 i]
    simp only [sub_mul, sum_sub_distrib, sum_add_distrib]
    ring
  have hdiag : 0 ≤ ∑ i, (c i i - ∑ j ∈ univ.erase i, A.share i j) * f i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (A.within_budget i)) (sq_nonneg _)
  have hpair2 : 0 ≤ ∑ i, ∑ j ∈ univ.erase i, (p i j + p j i) := by
    refine sum_nonneg fun i _ => sum_nonneg fun j hj => ?_
    have hij : i ≠ j := (ne_of_mem_erase hj).symm
    have e : p i j + p j i =
        A.share i j * f i ^ 2 + 2 * c i j * f i * f j + A.share j i * f j ^ 2 := by
      simp only [hp]
      rw [hc j i]
      ring
    rw [e]
    exact binaryForm_nonneg (A.share_nonneg i j) (A.share_nonneg j i) (A.pays i j hij) _ _
  have hpair : 0 ≤ ∑ i, ∑ j ∈ univ.erase i, p i j := by
    have h2 : ∑ i, ∑ j ∈ univ.erase i, (p i j + p j i) = 2 * ∑ i, ∑ j ∈ univ.erase i, p i j := by
      simp only [sum_add_distrib]
      rw [← sum_offDiag_swap p]
      ring
    linarith
  linarith

theorem incidenceEnergy_nonneg_of_locallyPayable {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (h : LocallyPayable c) (f : ι → ℝ) : 0 ≤ incidenceEnergy c f :=
  let ⟨A⟩ := h
  incidenceEnergy_nonneg_of_pairAllocation hc A f

/-- A local allocation can be normalized to lend nothing to the diagonal. -/
def PairAllocation.offDiagonal {c : ι → ι → ℝ} (A : PairAllocation c) : PairAllocation c where
  share i j := if i = j then 0 else A.share i j
  share_nonneg i j := by split_ifs <;> simp [A.share_nonneg]
  pays i j hij := by
    simp only [hij, if_false, Ne.symm hij]
    exact A.pays i j hij
  within_budget i := by
    refine le_trans (le_of_eq (sum_congr rfl fun j hj => ?_)) (A.within_budget i)
    simp [(ne_of_mem_erase hj).symm]

theorem PairAllocation.offDiagonal_share_self {c : ι → ι → ℝ} (A : PairAllocation c) (i : ι) :
    A.offDiagonal.share i i = 0 := by
  simp [PairAllocation.offDiagonal]

/-! ### Switching -/

omit [DecidableEq ι] in
theorem incidenceEnergy_switch (s : ι → ℝ) (c : ι → ι → ℝ) (f : ι → ℝ) :
    incidenceEnergy (switchCoupling s c) f = incidenceEnergy c (fun i => s i * f i) := by
  unfold incidenceEnergy switchCoupling
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

omit [Fintype ι] [DecidableEq ι] in
theorem IsSymmetricCoupling.switch {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (s : ι → ℝ) :
    IsSymmetricCoupling (switchCoupling s c) := by
  intro i j
  simp only [switchCoupling]
  rw [hc i j]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem switchCoupling_switchCoupling {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) (c : ι → ι → ℝ) :
    switchCoupling s (switchCoupling s c) = c := by
  funext i j
  simp only [switchCoupling]
  calc s i * s j * (s i * s j * c i j) = s i ^ 2 * s j ^ 2 * c i j := by ring
    _ = c i j := by rw [hs i, hs j]; ring

/-- Switching transports local allocations: the same shares pay the switched overlaps. -/
def PairAllocation.switch {c : ι → ι → ℝ} {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1)
    (A : PairAllocation c) : PairAllocation (switchCoupling s c) where
  share := A.share
  share_nonneg := A.share_nonneg
  pays i j hij := by
    have h : (switchCoupling s c i j) ^ 2 = c i j ^ 2 := by
      simp only [switchCoupling]
      calc (s i * s j * c i j) ^ 2 = s i ^ 2 * s j ^ 2 * c i j ^ 2 := by ring
        _ = c i j ^ 2 := by rw [hs i, hs j]; ring
    rw [h]
    exact A.pays i j hij
  within_budget i := by
    have h : switchCoupling s c i i = c i i := by
      simp only [switchCoupling]
      rw [← sq, hs i, one_mul]
    rw [h]
    exact A.within_budget i

theorem locallyPayable_switch_iff {c : ι → ι → ℝ} {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) :
    LocallyPayable (switchCoupling s c) ↔ LocallyPayable c := by
  constructor
  · rintro ⟨A⟩
    exact ⟨switchCoupling_switchCoupling hs c ▸ A.switch hs⟩
  · rintro ⟨A⟩
    exact ⟨A.switch hs⟩

omit [DecidableEq ι] in
/-- Positivity is switching invariant: a sign change of the profile is a bijection. -/
theorem nonneg_switch_iff {c : ι → ι → ℝ} {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) :
    (∀ f, 0 ≤ incidenceEnergy (switchCoupling s c) f) ↔ ∀ f, 0 ≤ incidenceEnergy c f := by
  constructor
  · intro h f
    have hf : (fun i => s i * (s i * f i)) = f := by
      funext i
      calc s i * (s i * f i) = s i ^ 2 * f i := by ring
        _ = f i := by rw [hs i, one_mul]
    have := h (fun i => s i * f i)
    rwa [incidenceEnergy_switch, hf] at this
  · intro h f
    rw [incidenceEnergy_switch]
    exact h _

/-! ### The ground-state transform -/

omit [DecidableEq ι] in
/-- **Ground-state transform.**  For any gauge `v` and profile `g`,
`E(v g) = Σ_i v_i (Cv)_i g_i² − ½ Σ_{i,j} c_ij v_i v_j (g_i − g_j)²`. -/
theorem incidenceEnergy_mul_eq {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (v g : ι → ℝ) :
    incidenceEnergy c (fun i => v i * g i) =
      ∑ i, v i * couplingAction c v i * g i ^ 2 -
        (1 / 2) * ∑ i, ∑ j, c i j * v i * v j * (g i - g j) ^ 2 := by
  have hS : ∑ i, ∑ j, c i j * v i * v j * g j ^ 2 = ∑ i, ∑ j, c i j * v i * v j * g i ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hc j i]; ring
  have hA : ∑ i, v i * couplingAction c v i * g i ^ 2 = ∑ i, ∑ j, c i j * v i * v j * g i ^ 2 := by
    unfold couplingAction
    exact sum_congr rfl fun i _ => by rw [mul_sum, sum_mul]; exact sum_congr rfl fun j _ => by ring
  have e : ∀ i j, c i j * v i * v j * (g i - g j) ^ 2 =
      c i j * v i * v j * g i ^ 2 + c i j * v i * v j * g j ^ 2 -
        2 * (c i j * (v i * g i) * (v j * g j)) := by
    intro i j; ring
  unfold incidenceEnergy
  rw [hA]
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hS]
  ring

/-- **Weighted dominance pays locally.**  If a strictly positive gauge `v` satisfies
`Σ_{j≠i} |c_ij| v_j ≤ c_ii v_i` at every point, the shares `a_ij = |c_ij| v_j / v_i` form a local
allocation. -/
theorem locallyPayable_of_weightedDominance {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hdom : ∀ i, ∑ j ∈ univ.erase i, |c i j| * v j ≤ c i i * v i) : LocallyPayable c := by
  refine ⟨{ share := fun i j => |c i j| * v j / v i
            share_nonneg := fun i j => div_nonneg (mul_nonneg (abs_nonneg _) (hv j).le) (hv i).le
            pays := fun i j _ => ?_
            within_budget := fun i => ?_ }⟩
  · have hi := (hv i).ne'
    have hj := (hv j).ne'
    rw [hc j i]
    have : |c i j| * v j / v i * (|c i j| * v i / v j) = |c i j| ^ 2 := by
      field_simp
    rw [this, sq_abs]
  · rw [← sum_div, div_le_iff₀ (hv i)]
    exact hdom i

/-- **Positive supersolutions pay locally.**  For a form whose overlaps are nonpositive, a
strictly positive gauge with `Cv ≥ 0` is a local allocation in disguise. -/
theorem locallyPayable_of_supersolution {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hz : HasNonpositiveOverlaps c) {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hsup : ∀ i, 0 ≤ couplingAction c v i) : LocallyPayable c := by
  refine locallyPayable_of_weightedDominance hc hv fun i => ?_
  have hact : couplingAction c v i = c i i * v i + ∑ j ∈ univ.erase i, c i j * v j := by
    unfold couplingAction
    rw [← add_sum_erase _ _ (mem_univ i)]
  have habs : ∑ j ∈ univ.erase i, |c i j| * v j = -∑ j ∈ univ.erase i, c i j * v j := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [abs_of_nonpos (hz i j (ne_of_mem_erase hj).symm)]
    ring
  have := hsup i
  rw [hact] at this
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
