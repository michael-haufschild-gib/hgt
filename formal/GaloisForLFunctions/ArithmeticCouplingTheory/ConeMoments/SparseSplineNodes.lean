import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineHeightCorrection

/-!
# Sparse nodes survive spline correction

The reciprocal primitive bounds the spatial Lipschitz constant of real node
corrections. Small corrections preserve order even when stratified nodes are
arbitrarily close. Displacement by at most one quarter leaves at most three
nodes in every unit interval.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
variable {ι : Type*} [Fintype ι]

/-- Spatial Lipschitz bound for the real spline node displacement. -/
lemma abs_splineHeightCorrection_space_sub_le {δ : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (y : ι → ℂ) (u v : ℝ) :
    |splineHeightCorrection δ t y v-splineHeightCorrection δ t y u| ≤
      (2*(Fintype.card ι:ℝ)*inverseSplineBound δ)*‖y‖*|v-u| := by
  have hi : 0 ≤ inverseSplineBound δ :=
    (norm_nonneg _).trans (norm_inverseSplineNumerator_le hδ 0)
  have he : splineHeightCorrection δ t y v-splineHeightCorrection δ t y u=
      2*(∑ i, (splineDual δ (t i) v-splineDual δ (t i) u)*y i).re := by
    simp only [splineHeightCorrection,sub_mul,sum_sub_distrib,Complex.sub_re]
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*‖∑ i, (splineDual δ (t i) v-splineDual δ (t i) u)*y i‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 2*∑ i, ‖(splineDual δ (t i) v-splineDual δ (t i) u)*y i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ 2*∑ _i : ι, (inverseSplineBound δ*|v-u|)*‖y‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (norm_splineDual_sub_le hδ (ht i) u v)
        (norm_le_pi_norm y i) (norm_nonneg _) (mul_nonneg hi (abs_nonneg _))
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

/-- Small spline corrections preserve order even when adjacent selected
nodes lie arbitrarily close to their shared cell boundary. -/
lemma strictMono_corrected_spline_height {δ : ℝ} (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) (y : ι → ℂ)
    (hsmall : (2*(Fintype.card ι:ℝ)*inverseSplineBound δ)*‖y‖ ≤ 1/2) :
    StrictMono (fun x => x+splineHeightCorrection δ t y x) := by
  intro u v huv
  have hd := abs_splineHeightCorrection_space_sub_le hδ ht y u v
  rw [abs_of_pos (sub_pos.mpr huv)] at hd
  have hh := mul_le_mul_of_nonneg_right hsmall (sub_pos.mpr huv).le
  have hl := (abs_le.mp (hd.trans hh)).1
  linarith only [hl,huv]

lemma strictMono_stratified_nodes {n : ℕ} {a : ℝ} {x : Fin n → ℝ}
    (hx : ∀ j, x j ∈ Set.Ioo (a+j.val) (a+j.val+1)) : StrictMono x := by
  intro j k hjk
  have hnat : j.val+1 ≤ k.val := hjk
  have hreal : (j.val:ℝ)+1 ≤ k.val := by exact_mod_cast hnat
  have hj := (hx j).2
  have hk := (hx k).1
  linarith only [hj,hk,hreal]

/-- A perturbation by at most one quarter preserves a three-cell local bound. -/
lemma stratified_perturbation_index_le_add_two {n : ℕ} {a T : ℝ}
    {x e : Fin n → ℝ} (hx : ∀ j, x j ∈ Set.Ioo (a+j.val) (a+j.val+1))
    (he : ∀ j, |e j| ≤ 1/4) {j k : Fin n}
    (hj : x j+e j ∈ Set.Icc T (T+1)) (hk : x k+e k ∈ Set.Icc T (T+1)) :
    j.val ≤ k.val+2 := by
  by_contra hn
  have hnat : k.val+3 ≤ j.val := by omega
  have hreal : (k.val:ℝ)+3 ≤ j.val := by exact_mod_cast hnat
  have hxj := (hx j).1
  have hxk := (hx k).2
  have hej := (abs_le.mp (he j)).1
  have hek := (abs_le.mp (he k)).2
  linarith only [hreal,hxj,hxk,hej,hek,hj.2,hk.1]

/-- Unit intervals contain at most three perturbed stratified nodes. -/
theorem card_stratified_perturbation_unit_le {n : ℕ} {a T : ℝ}
    {x e : Fin n → ℝ} (hx : ∀ j, x j ∈ Set.Ioo (a+j.val) (a+j.val+1))
    (he : ∀ j, |e j| ≤ 1/4) :
    ((univ : Finset (Fin n)).filter (fun j => x j+e j ∈ Set.Icc T (T+1))).card ≤ 3 := by
  classical
  let S := (univ : Finset (Fin n)).filter (fun j => x j+e j ∈ Set.Icc T (T+1))
  by_cases hS : S.Nonempty
  · let j₀ := S.min' hS
    have hj₀ : j₀ ∈ S := S.min'_mem hS
    have hmin (j) (hj : j ∈ S) : j₀.val ≤ j.val := S.min'_le j hj
    have hmax (j) (hj : j ∈ S) : j.val ≤ j₀.val+2 :=
      stratified_perturbation_index_le_add_two hx he
        (mem_filter.mp hj).2 (mem_filter.mp hj₀).2
    have hcard : S.card ≤ (range 3).card := by
      apply card_le_card_of_injOn (fun j : Fin n => j.val-j₀.val)
      · intro j hj
        change j.val-j₀.val ∈ range 3
        rw [mem_range]
        have h1 := hmin j hj
        have h2 := hmax j hj
        omega
      · intro j hj k hk heq
        change j.val-j₀.val=k.val-j₀.val at heq
        apply Fin.ext
        have h1 := hmin j hj
        have h2 := hmin k hk
        omega
    simpa only [card_range] using hcard
  · have hs : S=∅ := not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ 3
    rw [hs,card_empty]
    omega

#print axioms strictMono_corrected_spline_height
#print axioms card_stratified_perturbation_unit_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
