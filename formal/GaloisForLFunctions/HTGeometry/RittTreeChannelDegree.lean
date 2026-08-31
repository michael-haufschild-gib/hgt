import GaloisForLFunctions.HTGeometry.RittSubstitutionFixed
import GaloisForLFunctions.HTGeometry.RittTreeChannelMap

/-!
# The degree of the tree channel map

Degree multiplies along substitution, and a rational function that generates the whole rational
function field has degree one.  The conjugating Möbius coordinate and the Möbius factor of the
symmetric form are both generators, so the degree of the channel map can be read off the conjugacy:

`deg R · deg Φ = deg (R ∘ Φ) = deg ((t^p − 1)/(t^p + 1)) = deg M · deg (t^p) = p`,

with `deg Φ = deg M = 1`.  So the channel map has degree `p ≥ 2`, which is what makes a
substitution-fixed rational function constant.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial
open scoped IntermediateField

variable {K : Type*} [Field K]

/-- A generator of the rational function field has degree one. -/
theorem ratFuncDegree_eq_one_of_adjoin_eq_top {a : RatFunc K} (h : K⟮a⟯ = ⊤) :
    ratFuncDegree a = 1 := by
  have hf := RatFunc.finrank_eq_max_natDegree a
  rw [h, IntermediateField.finrank_top] at hf
  exact hf.symm

/-- The degree of the image of a polynomial is its degree. -/
theorem ratFuncDegree_algebraMap (P : K[X]) :
    ratFuncDegree (algebraMap K[X] (RatFunc K) P) = P.natDegree := by
  rw [ratFuncDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_one]
  exact Nat.max_eq_left (Nat.zero_le _)

/-- A rational function whose coordinate is a rational expression in it generates. -/
theorem adjoin_eq_top_of_X_mem {a : RatFunc K} (h : (RatFunc.X : RatFunc K) ∈ K⟮a⟯) :
    K⟮a⟯ = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← RatFunc.adjoin_X]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr h)

/-- **The conjugating Möbius coordinate generates.** -/
theorem adjoin_treeConj_eq_top {u v : K} (huv : u ≠ v) :
    K⟮treeConj u v⟯ = ⊤ := by
  have hd0 : algebraMap K[X] (RatFunc K) (C u - C v * X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (treeConjDen_ne_zero huv)
  have hrel : treeConj u v * (RatFunc.C u - RatFunc.C v * RatFunc.X)
      = RatFunc.X - 1 := by
    have h : treeConj u v * algebraMap K[X] (RatFunc K) (C u - C v * X)
        = algebraMap K[X] (RatFunc K) (X - 1) := by
      rw [treeConj, div_mul_cancel₀ _ hd0]
    rw [map_sub, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X] at h
    simpa using h
  have hden : (1 : RatFunc K) + RatFunc.C v * treeConj u v ≠ 0 := by
    intro h
    have hnum : RatFunc.C u * treeConj u v + 1 = 0 := by
      have hx : RatFunc.X * (1 + RatFunc.C v * treeConj u v)
          = RatFunc.C u * treeConj u v + 1 := by linear_combination -hrel
      rw [h, mul_zero] at hx
      exact hx.symm
    have hzero : (RatFunc.C u - RatFunc.C v) * treeConj u v = 0 := by
      linear_combination hnum - h
    have hwne : u - v ≠ 0 := sub_ne_zero.mpr huv
    have huvR : (RatFunc.C u - RatFunc.C v : RatFunc K) ≠ 0 := by
      rw [← map_sub]
      set w := u - v with hw
      simpa using hwne
    have hc0 : treeConj u v = 0 := by
      rcases mul_eq_zero.mp hzero with hh | hh
      · exact absurd hh huvR
      · exact hh
    rw [hc0, mul_zero, add_zero] at h
    exact one_ne_zero h
  refine adjoin_eq_top_of_X_mem ?_
  have hmem : treeConj u v ∈ K⟮treeConj u v⟯ := IntermediateField.mem_adjoin_simple_self K _
  have hX : (RatFunc.X : RatFunc K)
      = (RatFunc.C u * treeConj u v + 1) * (1 + RatFunc.C v * treeConj u v)⁻¹ := by
    rw [eq_comm, mul_inv_eq_iff_eq_mul₀ hden]
    linear_combination hrel
  rw [hX]
  refine mul_mem (add_mem (mul_mem ?_ hmem) (one_mem _)) (inv_mem (add_mem (one_mem _)
    (mul_mem ?_ hmem)))
  · exact IntermediateField.algebraMap_mem _ u
  · exact IntermediateField.algebraMap_mem _ v

/-- The Möbius factor of the symmetric form is the conjugating coordinate with parameters `1, −1`. -/
theorem treeConj_one_neg_one [CharZero K] :
    treeConj (1 : K) (-1) = algebraMap K[X] (RatFunc K) (X - 1)
      / algebraMap K[X] (RatFunc K) (X + 1) := by
  rw [treeConj]
  congr 2
  rw [map_one, map_neg, map_one]
  ring

/-- **Substituting a power into the Möbius factor gives the symmetric form.** -/
theorem subst_pow_treeConj [CharZero K] {p : ℕ}
    (hP : ¬ ∃ c : K, algebraMap K[X] (RatFunc K) (X ^ p) = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) (X ^ p)) hP (treeConj (1 : K) (-1))
      = algebraMap K[X] (RatFunc K) (X ^ p - 1)
        / algebraMap K[X] (RatFunc K) (X ^ p + 1) := by
  rw [treeConj_one_neg_one, map_div₀, ratFuncSubstitutionAlgHom_aeval,
    ratFuncSubstitutionAlgHom_aeval]
  congr 1
  · rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_one, ← map_one
      (algebraMap K[X] (RatFunc K)), ← map_sub]
  · rw [map_add, Polynomial.aeval_X, Polynomial.aeval_one, ← map_one
      (algebraMap K[X] (RatFunc K)), ← map_add]

/-- **The degree of the tree channel map is the branching number.** -/
theorem ratFuncDegree_treeRG [CharZero K] {p : ℕ} (hp : 0 < p) {u v : K} (huv : u ≠ v) :
    ratFuncDegree (treeRG p u v) = p := by
  have hPhi : ¬ ∃ c : K, treeConj u v = RatFunc.C c := treeConj_not_isConst huv
  have hdegPhi : ratFuncDegree (treeConj u v) = 1 :=
    ratFuncDegree_eq_one_of_adjoin_eq_top (adjoin_treeConj_eq_top huv)
  have hone : (1 : K) ≠ -1 := by
    intro h
    have : (2 : K) = 0 := by linear_combination h
    exact two_ne_zero this
  have hdegMob : ratFuncDegree (treeConj (1 : K) (-1)) = 1 :=
    ratFuncDegree_eq_one_of_adjoin_eq_top (adjoin_treeConj_eq_top hone)
  have hXp : ratFuncDegree (algebraMap K[X] (RatFunc K) (X ^ p)) = p := by
    rw [ratFuncDegree_algebraMap, natDegree_X_pow]
  have hPnc : ¬ ∃ c : K, algebraMap K[X] (RatFunc K) (X ^ p) = RatFunc.C c := by
    intro hc
    obtain ⟨c, hcc⟩ := hc
    have := hXp
    rw [hcc, ratFuncDegree, RatFunc.num_C, RatFunc.denom_C] at this
    simp at this
    omega
  have h1 := ratFuncDegree_substitution (treeConj u v) (treeRG p u v) hPhi
  rw [subst_treeConj_treeRG hp huv hPhi, hdegPhi, mul_one] at h1
  have h2 := ratFuncDegree_substitution (algebraMap K[X] (RatFunc K) (X ^ p))
    (treeConj (1 : K) (-1)) hPnc
  rw [subst_pow_treeConj hPnc, hdegMob, hXp, one_mul] at h2
  exact h1.symm.trans h2

/-- **A rational function fixed by substituting a tree channel map is constant.** -/
theorem eq_C_of_substitution_fixed_treeRG [CharZero K] {p : ℕ} (hp : 2 ≤ p) {u v : K}
    (huv : u ≠ v) {hR : ¬ ∃ c : K, treeRG p u v = RatFunc.C c} {a : RatFunc K}
    (hfix : ratFuncSubstitutionAlgHom (treeRG p u v) hR a = a) :
    ∃ c : K, a = RatFunc.C c := by
  refine eq_C_of_substitution_fixed hR ?_ hfix
  rw [ratFuncDegree_treeRG (by omega) huv]
  exact hp

end GaloisForLFunctions.HTGeometry
