import GaloisForLFunctions.ArithmeticHarmonicAnalysis.HardyEnergyOnAFiniteMesh

/-!
# Dependence on the relative cell width in the quadratic mesh Hardy inequality

Write the threshold as 1−q². A square completion at the ratio of two
consecutive heights pays for the selected inner value exactly once the
ratio is at most q². The remaining flux telescopes even across unselected
cells, so large gaps between the selected cells cause no extra loss.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem cell_residue {q s : ℝ} (hq : 0<q) (h1 : q<1) (hs : 0<s) (small : s≤q^2) :
    (1+q)*((1-q)^2/q^2) ≤ q*(1-s)^2/(s*(q+s)) := by
  have q2 := sq_pos_of_pos hq
  have qcap : q^2≤1 := by nlinarith only [mul_lt_mul_of_pos_right h1 hq,h1]
  have num := pow_le_pow_left₀ (sub_nonneg.mpr qcap) (sub_le_sub_left small 1) 2
  have den := mul_le_mul small (add_le_add (le_refl q) small) (add_pos hq hs).le q2.le
  calc _ = q*(1-q^2)^2/(q^2*(q+q^2)) := by
             field_simp [q2.ne',(add_pos hq q2).ne']
             ring
       _ ≤ _ := by
             apply (div_le_div_iff₀ (mul_pos q2 (add_pos hq q2)) (mul_pos hs (add_pos hq hs))).mpr
             exact (mul_le_mul_of_nonneg_left den (mul_nonneg hq.le (sq_nonneg _))).trans
               (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left num hq.le)
                 (mul_pos q2 (add_pos hq q2)).le)

private theorem normalized_hardy_cell {q s w : ℝ} (hq : 0<q) (h1 : q<1) (hs : 0<s)
    (how : w=0 ∨ s≤q^2 ∧ w=(1+q)*((1-q)^2/q^2)) (x y : ℝ) :
    w*x^2+(1-s)*y^2 ≤ (1+q)*(y-x)^2+(1-s)/s*x^2 := by
  let R := q*(1-s)^2/(s*(q+s))
  have price : w≤R := by
    rcases how with rfl|⟨small,rfl⟩
    · exact div_nonneg (mul_nonneg hq.le (sq_nonneg _)) (mul_pos hs (add_pos hq hs)).le
    · exact cell_residue hq h1 hs small
  have id : (1+q)*(y-x)^2+(1-s)/s*x^2-(1-s)*y^2 =
      (q+s)*(y-(1+q)*x/(q+s))^2+R*x^2 := by
    dsimp only [R]
    field_simp [hs.ne',(add_pos hq hs).ne']
    ring
  have residual := mul_nonneg (add_pos hq hs).le (sq_nonneg (y-(1+q)*x/(q+s)))
  linarith only [id,residual,mul_le_mul_of_nonneg_right price (sq_nonneg x)]

private theorem hardy_cell_with_price {q a b w x y : ℝ} (hq : 0<q) (h1 : q<1)
    (ha : 0≤a) (ab : a<b) (ground : a=0 → x=0)
    (price : w=0 ∨ (1-q^2)*b≤b-a ∧ w=(1-q)^2/q^2) :
    w*(x^2/(b-a)) + y^2/((1+q)*b) ≤ (y-x)^2/(b-a) + x^2/((1+q)*a) := by
  have bp := ha.trans_lt ab
  have qp := add_pos zero_lt_one hq
  rcases ha.eq_or_lt with zero|apos
  · have a0 := zero.symm
    rw [ground a0,a0]
    simp only [zero_pow (by norm_num : 2≠0),zero_div,mul_zero,zero_add,sub_zero,div_zero,add_zero]
    apply (div_le_div_iff₀ (mul_pos qp bp) bp).mpr
    have grow : b≤(1+q)*b := by linarith only [mul_nonneg hq.le bp.le]
    exact mul_le_mul_of_nonneg_left grow (sq_nonneg y)
  · have how : (1+q)*w=0 ∨ a/b≤q^2 ∧ (1+q)*w=(1+q)*((1-q)^2/q^2) := by
      rcases price with rfl|⟨chosen,rfl⟩
      · exact Or.inl (mul_zero _)
      · exact Or.inr ⟨(div_le_iff₀ bp).mpr (by linarith only [chosen]),rfl⟩
    have cert := normalized_hardy_cell hq h1 (div_pos apos bp) how x y
    have factor := mul_pos qp (sub_pos.mpr ab)
    apply le_of_mul_le_mul_left (a:=(1+q)*(b-a)) ?_ factor
    calc _ = (1+q)*w*x^2+(1-a/b)*y^2 := by
               field_simp [bp.ne',qp.ne',(sub_pos.mpr ab).ne']
         _ ≤ _ := cert
         _ = _ := by field_simp [apos.ne',bp.ne',qp.ne',(sub_pos.mpr ab).ne']

/-- At threshold 1−q² the cost of sampling inner values is at most
q²/(1−q)² times the difference energy. The outer boundary flux is retained. -/
theorem selected_hardy_cells_at_fixed_ratio {q : ℝ} (hq : 0<q) (h1 : q<1)
    (h z : ℕ → ℝ) (m : ℕ) (G : Finset ℕ) (endz : z m=0)
    (mesh : ∀ i∈range m, 0≤h (i+1) ∧ h (i+1)<h i) (sub : G⊆range m)
    (selected : ∀ i∈G, (1-q^2)*h i≤h i-h (i+1)) :
    (1-q)^2/q^2*(∑ i ∈ G,z (i+1)^2/(h i-h (i+1)))+z 0^2/((1+q)*h 0) ≤
      ∑ i ∈ range m,(z i-z (i+1))^2/(h i-h (i+1)) := by
  let flux (i : ℕ) := z i^2/((1+q)*h i)
  let α := (1-q)^2/q^2
  have point (i : ℕ) (hi : i∈range m) :
      (if i∈G then α*(z (i+1)^2/(h i-h (i+1))) else 0) ≤
        (z i-z (i+1))^2/(h i-h (i+1)) + (flux (i+1)-flux i) := by
    have ground (zero : h (i+1)=0) : z (i+1)=0 := by
      by_cases last : i+1=m
      · rwa [last]
      · have next := mesh (i+1) (mem_range.mpr (by have := mem_range.mp hi; omega))
        exact False.elim ((next.1.trans_lt next.2).ne' zero)
    dsimp only [flux]
    by_cases hit : i∈G
    · rw [if_pos hit]
      have cell := hardy_cell_with_price (w:=α) (y:=z i) hq h1 (mesh i hi).1 (mesh i hi).2 ground
        (Or.inr ⟨selected i hit,rfl⟩)
      linarith only [cell]
    · rw [if_neg hit]
      have cell := hardy_cell_with_price (w:=0) (y:=z i) hq h1 (mesh i hi).1 (mesh i hi).2 ground (Or.inl rfl)
      rw [zero_mul,zero_add] at cell
      linarith only [cell]
  have all := sum_le_sum point
  have rows : (range m).filter (·∈G)=G := by
    ext i
    exact ⟨fun hi => (mem_filter.mp hi).2,fun hi => mem_filter.mpr ⟨sub hi,hi⟩⟩
  rw [←sum_filter,rows,←mul_sum,sum_add_distrib,sum_range_sub] at all
  have fm : flux m=0 := by simp [flux,endz]
  rw [fm,zero_sub] at all
  exact (le_sub_iff_add_le.mp (by simpa only [sub_eq_add_neg] using all) : _)

#print axioms selected_hardy_cells_at_fixed_ratio
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
