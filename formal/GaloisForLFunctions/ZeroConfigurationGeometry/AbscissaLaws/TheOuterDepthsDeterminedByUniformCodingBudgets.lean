import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.RecoveringThePositiveDepthsFromFiniteCodebooks

/-!
# What uniform coding budgets determine about infinite zero configurations

Once a depth has only finitely many points beyond it, those points form
one extremal sample simultaneously for every larger error tolerance.
Its full displacement multiset is recovered from the uniform budgets on
rational radii above that depth. This works for configurations with
infinitely many points approaching the critical line.
-/

noncomputable section
open Finset Set Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

/-- The same number of codewords suffices for every finite sample. -/
def uniformCodebookBudget (Z : ZeroConfig) (h : ℝ) (b : ℕ) : Prop :=
  ∀ S : Finset ℂ, (S : Set ℂ) ⊆ Z.carrier → zeroSampleCodeCount S h ≤ b

private theorem code_count_mono {S T : Finset ℂ} (hST : S ⊆ T) (h : ℝ) :
    zeroSampleCodeCount S h ≤ zeroSampleCodeCount T h :=
  Finset.prod_le_prod_of_subset_of_one_le hST (fun _ _ => Nat.zero_le _) (fun _ _ _ => le_max_left _ _)

private theorem code_count_above (S : Finset ℂ) {a h : ℝ} (hah : a ≤ h) (hh : 0 < h) :
    zeroSampleCodeCount (S.filter (fun z => a < rightDisplacement z)) h = zeroSampleCodeCount S h := by
  classical
  apply Finset.prod_subset (filter_subset _ _)
  intro z hz hn
  have he : rightDisplacement z ≤ a := le_of_not_gt (fun hd => hn (mem_filter.mpr ⟨hz,hd⟩))
  exact max_eq_left (Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using (div_le_one hh).mpr (he.trans hah)))

private theorem mem_layer {Z : ZeroConfig} {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z ∈ Z.carrier) :
    z ∈ rightOf Z a ↔ a < rightDisplacement z := by
  change (z ∈ Z.carrier ∧ 1/2+a < z.re) ↔ a < max (z.re-1/2) 0
  rw [and_iff_right hz,lt_max_iff,or_iff_left (not_lt.mpr ha)]
  constructor <;> intro hx <;> linarith only [hx]

/-- A finite outer layer is simultaneously extremal at every coarser
radius. This statement includes exact ties at the upper radius. -/
theorem uniform_budget_on_finite_layer (Z : ZeroConfig) {a h : ℝ} (ha : 0 ≤ a)
    (hZ : (rightOf Z a).Finite) (hah : a ≤ h) (hh : 0 < h) (b : ℕ) :
    uniformCodebookBudget Z h b ↔ zeroSampleCodeCount hZ.toFinset h ≤ b := by
  classical
  constructor
  · intro H
    exact H hZ.toFinset (fun z hz => (hZ.mem_toFinset.mp hz).1)
  · intro H S hS
    rw [← code_count_above S hah hh]
    apply (code_count_mono _ h).trans H
    intro z hz
    obtain ⟨hz,hd⟩ := mem_filter.mp hz
    exact hZ.mem_toFinset.mpr ((mem_layer ha (hS hz)).mpr hd)

/-- Uniform budgets at all rational radii above a finite layer identify
the complete multiset of displacements beyond it. -/
theorem uniform_budgets_recover_outer_depths (Z W : ZeroConfig) {a : ℝ} (ha : 0 ≤ a)
    (hZ : (rightOf Z a).Finite) (hW : (rightOf W a).Finite) :
    (∀ q : ℚ, a < (q:ℝ) → ∀ b : ℕ, uniformCodebookBudget Z q b ↔ uniformCodebookBudget W q b) ↔
      sampleDepthsAbove hZ.toFinset a = sampleDepthsAbove hW.toFinset a := by
  rw [←rational_code_curve_above_iff _ _ ha]
  constructor
  · intro H q hq
    have h (b : ℕ) := (uniform_budget_on_finite_layer Z ha hZ hq.le (ha.trans_lt hq) b).symm.trans
      ((H q hq b).trans (uniform_budget_on_finite_layer W ha hW hq.le (ha.trans_lt hq) b))
    exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)
  · intro H q hq b
    rw [uniform_budget_on_finite_layer Z ha hZ hq.le (ha.trans_lt hq),
      uniform_budget_on_finite_layer W ha hW hq.le (ha.trans_lt hq), H q hq]

/-- For configurations approaching the line, uniform coding at positive
rational tolerances captures the displacement multiset on every
positive depth layer, even for infinite off-line support. -/
theorem uniform_coding_of_approaching_configurations (Z W : ZeroConfig)
    (hZ : ApproachesLine Z) (hW : ApproachesLine W) :
    (∀ q : ℚ, 0 < q → ∀ b : ℕ, uniformCodebookBudget Z q b ↔ uniformCodebookBudget W q b) ↔
      ∀ a : ℝ, ∀ ha : 0 < a,
        sampleDepthsAbove (hZ a ha).toFinset a = sampleDepthsAbove (hW a ha).toFinset a := by
  constructor
  · intro H a ha
    exact (uniform_budgets_recover_outer_depths Z W ha.le (hZ a ha) (hW a ha)).mp
      (fun q hq => H q (by exact_mod_cast ha.trans hq))
  · intro H q hq
    have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
    have hh := half_pos hqr
    exact (uniform_budgets_recover_outer_depths Z W hh.le (hZ _ hh) (hW _ hh)).mpr
      (H _ hh) q (half_lt_self hqr)


end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
