import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Permutation-invariant subspaces of a coordinate space

A subspace of `ι → K` invariant under all coordinate permutations is one of exactly four things:
zero, the constants, the sum-zero hyperplane, or everything.  No hypothesis on the characteristic
is needed.

Either every vector of the subspace is constant, in which case it sits inside a line; or some
vector separates two coordinates, and then transposing those two coordinates and subtracting
produces a difference of basis vectors, which propagates to all of them and fills the sum-zero
hyperplane.

The classification is what makes a Galois-invariant rational relation space among the roots of a
polynomial with full symmetric Galois group collapse to the trace relation:
`eq_constLine_of_le_of_ne_top`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace PermSubspace

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The sum of the coordinates, as a linear functional. -/
def sumForm : (ι → K) →ₗ[K] K := ∑ i, LinearMap.proj i

omit [DecidableEq ι] in
@[simp]
theorem sumForm_apply (v : ι → K) : sumForm v = ∑ i, v i := by
  simp [sumForm, LinearMap.sum_apply]

/-- The line of constant vectors. -/
def constLine : Submodule K (ι → K) := K ∙ (fun _ => (1 : K))

omit [Fintype ι] [DecidableEq ι] in
theorem const_mem_constLine (c : K) : (fun _ => c) ∈ constLine (K := K) (ι := ι) := by
  refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
  funext i
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem eq_const_of_mem_constLine {v : ι → K} (hv : v ∈ constLine (K := K) (ι := ι)) :
    ∃ c : K, v = fun _ => c := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  exact ⟨c, by funext i; rw [← hc]; simp⟩

/-- A subspace is permutation invariant when permuting coordinates preserves it. -/
def IsPermInvariant (R : Submodule K (ι → K)) : Prop :=
  ∀ σ : Equiv.Perm ι, ∀ v ∈ R, (fun i => v (σ i)) ∈ R

omit [Fintype ι] in
/-- Separating two coordinates produces a difference of basis vectors. -/
theorem single_sub_single_mem {R : Submodule K (ι → K)} (hR : IsPermInvariant R) {v : ι → K}
    (hv : v ∈ R) {i j : ι} (hij : v i ≠ v j) :
    (Pi.single i (1 : K) - Pi.single j (1 : K)) ∈ R := by
  have hswap : (fun k => v (Equiv.swap i j k)) ∈ R := hR (Equiv.swap i j) v hv
  have hdiff : (fun k => v (Equiv.swap i j k)) - v ∈ R := R.sub_mem hswap hv
  have hne : v j - v i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  have hval : (fun k => v (Equiv.swap i j k)) - v
      = (v j - v i) • (Pi.single i (1 : K) - Pi.single j (1 : K)) := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_sub]
    by_cases hki : k = i
    · subst hki
      by_cases hkj : k = j
      · rw [hkj]; simp
      · rw [Equiv.swap_apply_left]
        simp [hkj]
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right]
        simp [hki]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        simp [hki, hkj]
  rw [hval] at hdiff
  have hscaled := R.smul_mem (v j - v i)⁻¹ hdiff
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at hscaled

omit [Fintype ι] in
/-- One difference of basis vectors produces every difference sharing its first index. -/
theorem single_sub_single_mem_of_mem {R : Submodule K (ι → K)} (hR : IsPermInvariant R) {i j : ι}
    (hij : i ≠ j) (hmem : (Pi.single i (1 : K) - Pi.single j (1 : K)) ∈ R) (k : ι) (hki : k ≠ i) :
    (Pi.single i (1 : K) - Pi.single k (1 : K)) ∈ R := by
  by_cases hkj : k = j
  · subst hkj; exact hmem
  · have hperm := hR (Equiv.swap j k) _ hmem
    have hval : (fun m => (Pi.single i (1 : K) - Pi.single j (1 : K) : ι → K) (Equiv.swap j k m))
        = (Pi.single i (1 : K) - Pi.single k (1 : K) : ι → K) := by
      funext m
      simp only [Pi.sub_apply, Pi.single_apply]
      have hji : j ≠ i := Ne.symm hij
      have hik : i ≠ k := Ne.symm hki
      have hjk : j ≠ k := Ne.symm hkj
      by_cases hmi : m = i
      · subst hmi
        rw [Equiv.swap_apply_of_ne_of_ne hji.symm hik]
        simp [hij, hik]
      · by_cases hmk : m = k
        · subst hmk
          rw [Equiv.swap_apply_right]
          simp [hji, hki]
        · by_cases hmj : m = j
          · subst hmj
            rw [Equiv.swap_apply_left]
            simp [hki, hkj, hji, hjk]
          · rw [Equiv.swap_apply_of_ne_of_ne hmj hmk]
            simp [hmi, hmj, hmk]
    rwa [hval] at hperm

omit [Fintype ι] in
/-- Every difference of basis vectors lies in a permutation-invariant subspace containing one. -/
theorem all_single_sub_single_mem {R : Submodule K (ι → K)} (hR : IsPermInvariant R) {i j : ι}
    (hij : i ≠ j) (hmem : (Pi.single i (1 : K) - Pi.single j (1 : K)) ∈ R) (k l : ι) :
    (Pi.single k (1 : K) - Pi.single l (1 : K)) ∈ R := by
  by_cases hki : k = i
  · subst hki
    by_cases hlk : l = k
    · subst hlk; simp
    · exact single_sub_single_mem_of_mem hR hij hmem l hlk
  · by_cases hli : l = i
    · subst hli
      have hik := single_sub_single_mem_of_mem hR hij hmem k hki
      have hneg := R.neg_mem hik
      rwa [neg_sub] at hneg
    · have h1 := single_sub_single_mem_of_mem hR hij hmem k hki
      have h2 := single_sub_single_mem_of_mem hR hij hmem l hli
      have hsub := R.sub_mem h2 h1
      rwa [sub_sub_sub_cancel_left] at hsub

/-- A sum-zero vector is a combination of differences of basis vectors. -/
theorem eq_sum_single_sub_single {v : ι → K} (hv : ∑ i, v i = 0) (i : ι) :
    v = ∑ k, v k • (Pi.single k (1 : K) - Pi.single i (1 : K)) := by
  funext m
  rw [Finset.sum_apply]
  have hterm : ∀ k : ι, (v k • (Pi.single k (1 : K) - Pi.single i (1 : K)) : ι → K) m
      = (if m = k then v k else 0) - v k * (if m = i then (1 : K) else 0) := by
    intro k
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, mul_ite,
      mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
  have h1 : ∑ k : ι, (if m = k then v k else 0) = v m := by
    rw [Finset.sum_ite_eq Finset.univ m v]
    simp
  have h2 : ∑ k : ι, v k * (if m = i then (1 : K) else 0) = 0 := by
    rw [← Finset.sum_mul, hv, zero_mul]
  rw [h1, h2, sub_zero]

/-- **The classification.**  A permutation-invariant subspace is zero, the constants, the sum-zero
hyperplane, or everything. -/
theorem classification (R : Submodule K (ι → K)) (hR : IsPermInvariant R) :
    R = ⊥ ∨ R = constLine ∨ R = LinearMap.ker (sumForm (K := K) (ι := ι)) ∨ R = ⊤ := by
  by_cases hconst : ∀ v ∈ R, ∃ c : K, v = fun _ => c
  · -- every vector is constant, so `R` sits in a line
    by_cases hzero : ∀ v ∈ R, v = 0
    · left
      exact Submodule.eq_bot_iff R |>.mpr hzero
    · right; left
      obtain ⟨w, hwR, hwne⟩ : ∃ w ∈ R, w ≠ 0 := by
        by_contra hcon
        refine hzero fun w hw => ?_
        by_contra hw0
        exact hcon ⟨w, hw, hw0⟩
      obtain ⟨c, rfl⟩ := hconst w hwR
      have hc : c ≠ 0 := by
        intro h
        exact hwne (by rw [h]; funext i; simp)
      refine le_antisymm (fun v hv => ?_) ?_
      · obtain ⟨d, rfl⟩ := hconst v hv
        exact const_mem_constLine d
      · intro v hv
        obtain ⟨d, rfl⟩ := eq_const_of_mem_constLine hv
        have hscaled := R.smul_mem (d * c⁻¹) hwR
        have : (d * c⁻¹) • (fun _ => c : ι → K) = (fun _ => d) := by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
        rwa [this] at hscaled
  · -- some vector separates two coordinates
    obtain ⟨v, hvR, hvnc⟩ : ∃ v ∈ R, ∀ c : K, v ≠ fun _ => c := by
      by_contra hcon
      refine hconst fun v hv => ?_
      by_contra hc2
      exact hcon ⟨v, hv, fun c hvc => hc2 ⟨c, hvc⟩⟩
    have hex : ∃ i j : ι, v i ≠ v j := by
      by_contra hcon
      have hall : ∀ i j : ι, v i = v j := by
        intro i j
        by_contra hne
        exact hcon ⟨i, j, hne⟩
      rcases isEmpty_or_nonempty ι with hι | hι
      · exact hvnc 0 (funext fun i => (hι.false i).elim)
      · obtain ⟨i₀⟩ := hι
        exact hvnc (v i₀) (funext fun i => hall i i₀)
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := fun h => hij (by rw [h])
    have hdiff := single_sub_single_mem hR hvR hij
    have hker : LinearMap.ker (sumForm (K := K) (ι := ι)) ≤ R := by
      intro w hw
      have hw' : ∑ k, w k = 0 := by
        have := LinearMap.mem_ker.mp hw
        rwa [sumForm_apply] at this
      rw [eq_sum_single_sub_single hw' i]
      exact Submodule.sum_mem _ fun k _ =>
        R.smul_mem _ (all_single_sub_single_mem hR hne hdiff k i)
    by_cases htop : ∀ w ∈ R, sumForm w = 0
    · right; right; left
      exact le_antisymm (fun w hw => LinearMap.mem_ker.mpr (htop w hw)) hker
    · right; right; right
      obtain ⟨w, hwR, hwne⟩ : ∃ w ∈ R, sumForm w ≠ 0 := by
        by_contra hcon
        refine htop fun w hw => ?_
        by_contra hw0
        exact hcon ⟨w, hw, hw0⟩
      refine le_antisymm le_top fun u _ => ?_
      have hcorr : u - (sumForm u * (sumForm w)⁻¹) • w
          ∈ LinearMap.ker (sumForm (K := K) (ι := ι)) := by
        refine LinearMap.mem_ker.mpr ?_
        rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hwne, mul_one, sub_self]
      have := R.add_mem (hker hcorr) (R.smul_mem (sumForm u * (sumForm w)⁻¹) hwR)
      rwa [sub_add_cancel] at this

/-- **The trace relation is the only one.**  A permutation-invariant subspace that contains the
constants but is not everything is exactly the constants, provided the coordinate count is
invertible. -/
theorem eq_constLine_of_le_of_ne_top (R : Submodule K (ι → K)) (hR : IsPermInvariant R)
    (hcard : (Fintype.card ι : K) ≠ 0) (hconst : constLine (K := K) (ι := ι) ≤ R) (htop : R ≠ ⊤) :
    R = constLine := by
  have hone : (fun _ => (1 : K)) ∈ R := hconst (const_mem_constLine 1)
  rcases classification R hR with h | h | h | h
  · rw [h] at hone
    exact absurd (Submodule.mem_bot K |>.mp hone) (by
      intro hc
      have := congrFun hc (Classical.choice (by
        by_contra hemp
        simp only [not_nonempty_iff] at hemp
        exact hcard (by simp [Fintype.card_eq_zero])))
      simp at this)
  · exact h
  · exfalso
    rw [h] at hone
    have := LinearMap.mem_ker.mp hone
    rw [sumForm_apply] at this
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at this
    exact hcard this
  · exact absurd h htop

end PermSubspace

end GaloisForLFunctions.HTGeometry
