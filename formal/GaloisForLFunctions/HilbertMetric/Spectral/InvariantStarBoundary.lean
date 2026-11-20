import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Spectral separation in a permutation-invariant star boundary

This finite Dirichlet-to-Neumann model applies the invariant restriction of
Longa (arXiv:2611.22168). Each edge is subdivided at its harmonic midpoint.
The boundary mass and total effective conductance are both normalized to one.
The leaf contrasts retain a bounded level as the central mass shrinks, while
the first positive invariant level diverges.
-/

namespace GaloisForLFunctions.HilbertMetric.InvariantStarBoundary

noncomputable section

open scoped BigOperators

abbrev Boundary (k : ℕ) := Option (Fin (k + 1)) → ℝ

/-- Fraction of the boundary mass placed at the central vertex. -/
abbrev CenterMass := Set.Ioo (0 : ℝ) (1 / 2)

private theorem leafCount_pos (k : ℕ) : 0 < ((k + 1 : ℕ) : ℝ) := by positivity

private theorem mass_pos (ε : CenterMass) : 0 < (ε : ℝ) := ε.2.1

private theorem leafMass_pos (ε : CenterMass) : 0 < 1 - (ε : ℝ) := by
  have h : (ε : ℝ) < 1 / 2 := ε.2.2
  linarith

/-- Equal masses are assigned to the leaves. -/
def mass (ε : CenterMass) {k : ℕ} : Option (Fin (k + 1)) → ℝ
  | none => ε
  | some _ => (1 - (ε : ℝ)) / ((k + 1 : ℕ) : ℝ)

theorem mass_sum (ε : CenterMass) (k : ℕ) :
    (∑ i : Option (Fin (k + 1)), mass ε i) = 1 := by
  rw [Fintype.sum_option]
  simp only [mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [(leafCount_pos k).ne']
  ring

theorem effective_conductance_sum (k : ℕ) :
    (∑ _ : Fin (k + 1), (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel₀ _ (leafCount_pos k).ne'

/-- Average boundary value over the leaves. -/
def leafMean (k : ℕ) : Boundary k →ₗ[ℝ] ℝ where
  toFun x := (∑ i, x (some i)) / ((k + 1 : ℕ) : ℝ)
  map_add' x y := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum, mul_div_assoc]

private theorem leafMean_eq_const {k : ℕ} (x : Boundary k) (c : ℝ)
    (h : ∀ i, x (some i) = c) : leafMean k x = c := by
  change (∑ i : Fin (k + 1), x (some i)) / _ = _
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (leafCount_pos k).ne'

/-- Restriction of the mass-normalized conormal flux to the boundary. -/
def response (ε : CenterMass) (k : ℕ) : Boundary k →ₗ[ℝ] Boundary k where
  toFun x
    | none => (x none - leafMean k x) / (ε : ℝ)
    | some i => (x (some i) - x none) / (1 - (ε : ℝ))
  map_add' x y := by
    funext i
    cases i <;> simp only [Pi.add_apply, map_add] <;> ring
  map_smul' a x := by
    funext i
    cases i <;> simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul] <;> ring

@[simp] theorem response_center (ε : CenterMass) {k : ℕ} (x : Boundary k) :
    response ε k x none = (x none - leafMean k x) / (ε : ℝ) := rfl

@[simp] theorem response_leaf (ε : CenterMass) {k : ℕ} (x : Boundary k) (i : Fin (k + 1)) :
    response ε k x (some i) = (x (some i) - x none) / (1 - (ε : ℝ)) := rfl

/-- Harmonic extension to the midpoint of a subdivided edge. Both half edges
have conductance `2/(k+1)`. -/
def midpoint {k : ℕ} (x : Boundary k) (i : Fin (k + 1)) : ℝ :=
  (x none + x (some i)) / 2

theorem midpoint_harmonic {k : ℕ} (x : Boundary k) (i : Fin (k + 1)) :
    (2 / ((k + 1 : ℕ) : ℝ)) * (midpoint x i - x none) +
      (2 / ((k + 1 : ℕ) : ℝ)) * (midpoint x i - x (some i)) = 0 := by
  unfold midpoint
  ring

/-- Normalized response equals flux of the actual harmonic extension at
each leaf and at the central boundary vertex. -/
theorem response_is_conormal (ε : CenterMass) {k : ℕ} (x : Boundary k) :
    mass ε (k := k) none * response ε k x none =
      ∑ i : Fin (k + 1), (2 / ((k + 1 : ℕ) : ℝ)) * (x none - midpoint x i) ∧
    ∀ i : Fin (k + 1), mass ε (some i) * response ε k x (some i) =
      (2 / ((k + 1 : ℕ) : ℝ)) * (x (some i) - midpoint x i) := by
  constructor
  · rw [response_center, mass, mul_div_cancel₀ _ (mass_pos ε).ne']
    change x none - (∑ i : Fin (k + 1), x (some i)) / _ = _
    calc
      _ = ∑ i : Fin (k + 1), (x none - x (some i)) / ((k + 1 : ℕ) : ℝ) := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp [(leafCount_pos k).ne']
      _ = _ := Finset.sum_congr rfl fun i _ => by unfold midpoint; ring
  · intro i
    rw [response_leaf, mass]
    unfold midpoint
    field_simp [(leafMass_pos ε).ne', (leafCount_pos k).ne']
    ring

/-- Relabeling leaves acts on boundary data and fixes the center. -/
def permute {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (x : Boundary k) : Boundary k
  | none => x none
  | some i => x (some (σ i))

private theorem leafMean_permute {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (x : Boundary k) :
    leafMean k (permute σ x) = leafMean k x := by
  change (∑ i, x (some (σ i))) / _ = (∑ i, x (some i)) / _
  rw [Equiv.sum_comp σ (fun i => x (some i))]

/-- Harmonic boundary response commutes with every leaf permutation. -/
theorem response_equivariant (ε : CenterMass) {k : ℕ} (σ : Equiv.Perm (Fin (k + 1)))
    (x : Boundary k) :
    response ε k (permute σ x) = permute σ (response ε k x) := by
  funext i
  cases i <;> simp only [response_center, response_leaf, permute, leafMean_permute]

def Invariant {k : ℕ} (x : Boundary k) : Prop := ∀ σ, permute σ x = x

/-- The invariant sector consists exactly of data constant across leaves. -/
theorem invariant_iff {k : ℕ} (x : Boundary k) :
    Invariant x ↔ ∀ i, x (some i) = leafMean k x := by
  classical
  constructor
  · intro h
    have he (i : Fin (k + 1)) : x (some i) = x (some 0) := by
      have hi := congrFun (h (Equiv.swap 0 i)) (some 0)
      simpa only [permute, Equiv.swap_apply_left] using hi
    rw [leafMean_eq_const x (x (some 0)) he]
    exact he
  · intro h σ
    funext i
    cases i with
    | none => rfl
    | some i => exact (h (σ i)).trans (h i).symm

/-- The symmetry projection retains the center and averages the leaves. -/
def symmetrize (k : ℕ) : Boundary k →ₗ[ℝ] Boundary k where
  toFun x
    | none => x none
    | some _ => leafMean k x
  map_add' x y := by
    funext i
    cases i <;> simp only [Pi.add_apply, map_add]
  map_smul' r x := by
    funext i
    cases i <;> simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

private theorem leafMean_response (ε : CenterMass) {k : ℕ} (x : Boundary k) :
    leafMean k (response ε k x) = (leafMean k x - x none) / (1 - (ε : ℝ)) := by
  change (∑ i, response ε k x (some i)) / ((k + 1 : ℕ) : ℝ) = _
  simp only [response_leaf]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  change _ = ((∑ i : Fin (k + 1), x (some i)) / ((k + 1 : ℕ) : ℝ) - x none) / _
  field_simp [(leafCount_pos k).ne', (leafMass_pos ε).ne']

/-- Response measured in the invariant sector equals response to the projected data. -/
theorem symmetrize_response (ε : CenterMass) {k : ℕ} (x : Boundary k) :
    symmetrize k (response ε k x) = response ε k (symmetrize k x) := by
  have hm : leafMean k (symmetrize k x) = leafMean k x :=
    leafMean_eq_const _ _ fun _ => rfl
  funext i
  cases i with
  | none =>
    change response ε k x none = response ε k (symmetrize k x) none
    rw [response_center, response_center, hm]
    rfl
  | some i =>
    change leafMean k (response ε k x) = response ε k (symmetrize k x) (some i)
    rw [leafMean_response, response_leaf]
    rfl

def contrast {k : ℕ} (x : Boundary k) : Boundary k
  | none => 0
  | some i => x (some i) - leafMean k x

/-- The invariant positive mode has zero mean for the normalized boundary mass. -/
def invariantMode (ε : CenterMass) {k : ℕ} : Boundary k
  | none => 1 - (ε : ℝ)
  | some _ => -(ε : ℝ)

def lowLevel (ε : CenterMass) : ℝ := 1 / (1 - (ε : ℝ))

def invariantLevel (ε : CenterMass) : ℝ := 1 / ((ε : ℝ) * (1 - (ε : ℝ)))

/-- Exact resolution into the constant, leaf-contrast, and invariant positive modes. -/
theorem spectral_split (ε : CenterMass) {k : ℕ} (x : Boundary k) (i : Option (Fin (k + 1))) :
    response ε k x i = lowLevel ε * contrast x i +
      invariantLevel ε * (x none - leafMean k x) * invariantMode ε i := by
  cases i <;> simp only [response_center, response_leaf, contrast, invariantMode,
    lowLevel, invariantLevel] <;> field_simp [(mass_pos ε).ne', (leafMass_pos ε).ne'] <;> ring

private theorem invariantMode_mean (ε : CenterMass) (k : ℕ) :
    leafMean k (invariantMode ε) = -(ε : ℝ) :=
  leafMean_eq_const _ _ fun _ => rfl

theorem invariantMode_eigen (ε : CenterMass) (k : ℕ) :
    response ε k (invariantMode ε) = invariantLevel ε • invariantMode ε := by
  funext i
  rw [spectral_split, invariantMode_mean]
  cases i <;> simp only [contrast, invariantMode_mean, invariantMode, sub_self, mul_zero,
    zero_add, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Classification of positive invariant eigenvalues, including attainment. -/
theorem invariant_positive_level_iff (ε : CenterMass) (k : ℕ) (r : ℝ) :
    (0 < r ∧ ∃ x : Boundary k, x ≠ 0 ∧ Invariant x ∧ response ε k x = r • x) ↔
      r = invariantLevel ε := by
  constructor
  · rintro ⟨hr, x, hx, hsym, heig⟩
    have hm := (invariant_iff x).mp hsym
    have hd : x none - leafMean k x ≠ 0 := by
      intro hz
      apply hx
      funext i
      have h := congrFun heig i
      rw [spectral_split, hz, mul_zero, zero_mul, add_zero] at h
      cases i with
      | none =>
        simp only [contrast, mul_zero, Pi.smul_apply, smul_eq_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hr.ne'
      | some i =>
        simp only [contrast, hm i, sub_self, mul_zero, Pi.smul_apply, smul_eq_mul] at h
        rw [hm i]
        exact (mul_eq_zero.mp h.symm).resolve_left hr.ne'
    have hc := congrFun heig none
    have hl := congrFun heig (some 0)
    rw [spectral_split] at hc hl
    simp only [contrast, invariantMode, mul_zero, zero_add, Pi.smul_apply, smul_eq_mul] at hc
    simp only [contrast, invariantMode, hm 0, sub_self, mul_zero, zero_add,
      Pi.smul_apply, smul_eq_mul] at hl
    exact mul_right_cancel₀ hd (show r * (x none - leafMean k x) =
      invariantLevel ε * (x none - leafMean k x) by linear_combination hl - hc)
  · intro h
    subst r
    refine ⟨div_pos one_pos (mul_pos (mass_pos ε) (leafMass_pos ε)),
      invariantMode ε, ?_, (invariant_iff _).mpr ?_, invariantMode_eigen ε k⟩
    · intro hz
      exact (leafMass_pos ε).ne' (congrFun hz none)
    · intro i
      rw [invariantMode_mean]
      rfl

/-- Independent leaf contrasts anchored at the last leaf. -/
def contrastBasis {k : ℕ} (j : Fin k) : Boundary k
  | none => 0
  | some i => (if i = j.castSucc then 1 else 0) - if i = Fin.last k then 1 else 0

private theorem contrastBasis_mean {k : ℕ} (j : Fin k) :
    leafMean k (contrastBasis j) = 0 := by
  change (∑ i : Fin (k + 1), ((if i = j.castSucc then (1 : ℝ) else 0) -
    (if i = Fin.last k then 1 else 0))) / _ = _
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sub_self, zero_div]

theorem contrastBasis_eigen (ε : CenterMass) {k : ℕ} (j : Fin k) :
    response ε k (contrastBasis j) = lowLevel ε • contrastBasis j := by
  funext i
  cases i <;> simp [contrastBasis, contrastBasis_mean, lowLevel, div_eq_mul_inv, mul_comm]

theorem contrastBasis_independent (k : ℕ) :
    LinearIndependent ℝ (contrastBasis (k := k)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  have hj := congrFun ha (some j.castSucc)
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, contrastBasis,
    Fin.castSucc_inj, if_neg (Fin.castSucc_ne_last j), sub_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] using hj

theorem contrastBasis_not_invariant {k : ℕ} (j : Fin k) : ¬ Invariant (contrastBasis j) := by
  intro h
  have hh := (invariant_iff _).mp h j.castSucc
  rw [contrastBasis_mean] at hh
  simp [contrastBasis, Fin.castSucc_ne_last] at hh

/-- Every low contrast is completely invisible after symmetry projection. -/
theorem symmetrize_contrastBasis {k : ℕ} (j : Fin k) :
    symmetrize k (contrastBasis j) = 0 := by
  funext i
  cases i with
  | none => rfl
  | some i => exact contrastBasis_mean j

/-- The only zero-response data on the connected star are constants. -/
theorem response_eq_zero_iff (ε : CenterMass) {k : ℕ} (x : Boundary k) :
    response ε k x = 0 ↔ ∀ i, x i = x none := by
  constructor
  · intro h i
    cases i with
    | none => rfl
    | some i =>
      have hi := congrFun h (some i)
      rw [response_leaf, Pi.zero_apply, div_eq_iff (leafMass_pos ε).ne', zero_mul] at hi
      exact sub_eq_zero.mp hi
  · intro h
    have hm := leafMean_eq_const x (x none) (fun i => h (some i))
    funext i
    cases i with
    | none => simp [hm]
    | some i => simp [h (some i)]

/-- The full positive spectrum has only the invariant level and, when there is
more than one leaf, the independent contrast level. -/
theorem positive_level_iff (ε : CenterMass) (k : ℕ) (r : ℝ) :
    (0 < r ∧ ∃ x : Boundary k, x ≠ 0 ∧ response ε k x = r • x) ↔
      (0 < k ∧ r = lowLevel ε) ∨ r = invariantLevel ε := by
  constructor
  · rintro ⟨hr, x, hx, heig⟩
    by_cases h : 0 < k ∧ r = lowLevel ε
    · exact Or.inl h
    right
    apply (invariant_positive_level_iff ε k r).mp
    refine ⟨hr, x, hx, (invariant_iff x).mpr ?_, heig⟩
    intro i
    by_cases hk : k = 0
    · subst k
      have hsame (j : Fin (0 + 1)) : j = i := Fin.ext (by
        have hi := i.isLt
        have hj := j.isLt
        omega)
      exact (leafMean_eq_const x (x (some i))
        (fun j => congrArg (fun j => x (some j)) (hsame j))).symm
    · have hm := congrArg (leafMean k) heig
      have hi := congrFun heig (some i)
      rw [leafMean_response, map_smul, smul_eq_mul] at hm
      simp only [response_leaf, Pi.smul_apply, smul_eq_mul] at hi
      by_contra hne
      apply h
      refine ⟨Nat.pos_of_ne_zero hk, mul_right_cancel₀ (sub_ne_zero.mpr hne) ?_⟩
      unfold lowLevel
      linear_combination hm - hi
  · rintro (⟨hk, rfl⟩ | h)
    · let j : Fin k := ⟨0, hk⟩
      refine ⟨div_pos one_pos (leafMass_pos ε), contrastBasis j, ?_, contrastBasis_eigen ε j⟩
      intro hz
      have he := congrFun hz (some j.castSucc)
      simp [contrastBasis, Fin.castSucc_ne_last] at he
    · obtain ⟨hr, x, hx, _, heig⟩ := (invariant_positive_level_iff ε k r).mpr h
      exact ⟨hr, x, hx, heig⟩

/-- With both normalizations fixed, arbitrarily many independent low modes
are symmetry breaking while the invariant positive level grows without bound. -/
theorem exists_unbounded_invariant_gap_with_bounded_contrasts (k : ℕ) (R : ℝ) :
    ∃ ε : CenterMass, R < invariantLevel ε ∧ 0 < lowLevel ε ∧ lowLevel ε < 2 ∧
      ∃ v : Fin k → Boundary k, LinearIndependent ℝ v ∧
        ∀ j, response ε k (v j) = lowLevel ε • v j ∧
          ¬ Invariant (v j) ∧ symmetrize k (v j) = 0 := by
  let a := |R| + 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hhalf : a⁻¹ < (1 : ℝ) / 2 := by
    rw [inv_eq_one_div, div_lt_div_iff₀ ha (by norm_num)]
    dsimp [a]
    linarith only [abs_nonneg R]
  let ε : CenterMass := ⟨a⁻¹, inv_pos.mpr ha, hhalf⟩
  refine ⟨ε, ?_, div_pos one_pos (leafMass_pos ε), ?_, contrastBasis,
    contrastBasis_independent k, fun j => ⟨contrastBasis_eigen ε j,
      contrastBasis_not_invariant j, symmetrize_contrastBasis j⟩⟩
  · have hh : (ε : ℝ)⁻¹ ≤ invariantLevel ε := by
      rw [inv_eq_one_div, invariantLevel]
      exact div_le_div_of_nonneg_left zero_le_one
        (mul_pos (mass_pos ε) (leafMass_pos ε))
        (mul_le_of_le_one_right (mass_pos ε).le (sub_le_self _ (mass_pos ε).le))
    have hR : R < a := by dsimp [a]; linarith only [le_abs_self R]
    exact hR.trans_le (by simpa only [ε, inv_inv] using hh)
  · rw [lowLevel, div_lt_iff₀ (leafMass_pos ε)]
    change 1 < 2 * (1 - a⁻¹)
    linarith only [hhalf]

#print axioms response_is_conormal
#print axioms response_equivariant
#print axioms invariant_positive_level_iff
#print axioms positive_level_iff
#print axioms symmetrize_contrastBasis
#print axioms exists_unbounded_invariant_gap_with_bounded_contrasts

end

end GaloisForLFunctions.HilbertMetric.InvariantStarBoundary
