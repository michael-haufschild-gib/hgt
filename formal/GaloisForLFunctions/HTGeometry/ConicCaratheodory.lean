import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Conic Carathéodory

A positive combination of finitely many vectors is already a positive combination of a linearly
independent subfamily.  The proof is the standard elimination: a linear dependence among the
generators can be added with the largest admissible multiple, which drives one coefficient to zero
without making any other coefficient negative, and the support strictly shrinks.

In a space of finite dimension `r` the surviving family therefore has at most `r` members: a finite
positive cone in `r` dimensions needs at most `r` generators to represent any of its points, one
fewer than the affine Carathéodory bound.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [DecidableEq ι] {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Conic Carathéodory.**  Every positive combination of a finite family is a positive
combination of a linearly independent subfamily. -/
theorem exists_linearIndependent_pos_combination (v : ι → V) :
    ∀ F : Finset ι, ∀ b : ι → ℝ, (∀ i ∈ F, 0 < b i) →
      ∃ (G : Finset ι) (c : ι → ℝ), G ⊆ F ∧ (∀ i ∈ G, 0 < c i) ∧
        LinearIndependent ℝ (fun i : G => v i) ∧
        ∑ i ∈ F, b i • v i = ∑ i ∈ G, c i • v i := by
  intro F
  induction F using Finset.strongInduction with
  | _ F ih =>
    intro b hb
    by_cases hli : LinearIndependent ℝ (fun i : F => v i)
    · exact ⟨F, b, Finset.Subset.refl F, hb, hli, rfl⟩
    · classical
      obtain ⟨g, hg0, j, hjne⟩ := Fintype.not_linearIndependent_iff.1 hli
      set lam : ι → ℝ := fun i => if h : i ∈ F then g ⟨i, h⟩ else 0 with hlam
      have hlamsum : ∑ i ∈ F, lam i • v i = 0 := by
        rw [← hg0, ← Finset.sum_coe_sort F fun i => lam i • v i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hlam]
        simp
      have hjF : (j : ι) ∈ F := j.2
      have hlamj : lam (j : ι) ≠ 0 := by
        rw [hlam]
        simpa using hjne
      obtain ⟨mu, hmusum, i₂, hi₂F, hi₂pos⟩ :
          ∃ mu : ι → ℝ, (∑ i ∈ F, mu i • v i = 0) ∧ ∃ i ∈ F, 0 < mu i := by
        rcases lt_trichotomy (lam (j : ι)) 0 with hneg | hzero | hpos
        · refine ⟨fun i => -lam i, ?_, (j : ι), hjF, by simpa using hneg⟩
          rw [← neg_eq_zero.2 hlamsum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [neg_smul]
        · exact absurd hzero hlamj
        · exact ⟨lam, hlamsum, (j : ι), hjF, hpos⟩
      set S : Finset ι := F.filter (fun i => 0 < mu i) with hS
      have hSne : S.Nonempty := ⟨i₂, by rw [hS, Finset.mem_filter]; exact ⟨hi₂F, hi₂pos⟩⟩
      obtain ⟨i₀, hi₀S, hi₀min⟩ := Finset.exists_min_image S (fun i => b i / mu i) hSne
      have hi₀mem : i₀ ∈ F ∧ 0 < mu i₀ := by
        have hmem := hi₀S
        rw [hS, Finset.mem_filter] at hmem
        exact hmem
      have hi₀F : i₀ ∈ F := hi₀mem.1
      have hi₀mu : 0 < mu i₀ := hi₀mem.2
      set theta : ℝ := b i₀ / mu i₀ with htheta
      have hthetapos : 0 < theta := div_pos (hb i₀ hi₀F) hi₀mu
      set c : ι → ℝ := fun i => b i - theta * mu i with hc
      have hci₀ : c i₀ = 0 := by
        rw [hc, htheta]
        field_simp
        ring
      have hcnonneg : ∀ i ∈ F, 0 ≤ c i := by
        intro i hi
        by_cases hmui : 0 < mu i
        · have hiS : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hi, hmui⟩
          have hmin := hi₀min i hiS
          rw [hc]
          have : theta * mu i ≤ b i := by
            rw [htheta]
            rw [div_le_div_iff₀ hi₀mu hmui] at hmin
            rw [div_mul_eq_mul_div, div_le_iff₀ hi₀mu]
            linarith
          linarith
        · have hmule : mu i ≤ 0 := not_lt.1 hmui
          have hprod : theta * mu i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hthetapos.le hmule
          rw [hc]
          linarith [hb i hi]
      have hcsum : ∑ i ∈ F, c i • v i = ∑ i ∈ F, b i • v i := by
        have hexpand : ∀ i ∈ F, c i • v i = b i • v i - theta • (mu i • v i) := by
          intro i _
          rw [hc, sub_smul, smul_smul]
        rw [Finset.sum_congr rfl hexpand, Finset.sum_sub_distrib, ← Finset.smul_sum, hmusum,
          smul_zero, sub_zero]
      set F' : Finset ι := F.filter (fun i => 0 < c i) with hF'
      have hF'sub : F' ⊆ F := Finset.filter_subset _ _
      have hF'ssub : F' ⊂ F := by
        refine Finset.ssubset_iff_of_subset hF'sub |>.2 ⟨i₀, hi₀F, ?_⟩
        rw [hF', Finset.mem_filter]
        rintro ⟨-, hpos⟩
        rw [hci₀] at hpos
        exact lt_irrefl 0 hpos
      have hF'sum : ∑ i ∈ F', c i • v i = ∑ i ∈ F, c i • v i := by
        refine Finset.sum_subset hF'sub fun i hi hnot => ?_
        have hle : ¬ (0 < c i) := by
          intro hpos
          exact hnot (by rw [hF', Finset.mem_filter]; exact ⟨hi, hpos⟩)
        have hzero : c i = 0 := le_antisymm (not_lt.1 hle) (hcnonneg i hi)
        rw [hzero, zero_smul]
      have hF'pos : ∀ i ∈ F', 0 < c i := by
        intro i hi
        rw [hF', Finset.mem_filter] at hi
        exact hi.2
      obtain ⟨G, d, hGF', hdpos, hdli, hdsum⟩ := ih F' hF'ssub c hF'pos
      exact ⟨G, d, hGF'.trans hF'sub, hdpos, hdli, by rw [← hcsum, ← hF'sum, hdsum]⟩

/-- **Conic Carathéodory with the dimension bound.**  In a space of finite dimension `r` at most
`r` generators are needed. -/
theorem exists_pos_combination_card_le_finrank [Module.Finite ℝ V] (v : ι → V) (F : Finset ι)
    (b : ι → ℝ) (hb : ∀ i ∈ F, 0 < b i) :
    ∃ (G : Finset ι) (c : ι → ℝ), G ⊆ F ∧ (∀ i ∈ G, 0 < c i) ∧
      LinearIndependent ℝ (fun i : G => v i) ∧
      G.card ≤ Module.finrank ℝ V ∧
      ∑ i ∈ F, b i • v i = ∑ i ∈ G, c i • v i := by
  obtain ⟨G, c, hGF, hcpos, hli, hsum⟩ := exists_linearIndependent_pos_combination v F b hb
  refine ⟨G, c, hGF, hcpos, hli, ?_, hsum⟩
  have hcard := LinearIndependent.fintype_card_le_finrank hli
  simpa using hcard

end GaloisForLFunctions.HTGeometry
