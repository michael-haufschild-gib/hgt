import GaloisForLFunctions.ArithmeticHarmonicAnalysis.HardyEnergyOnAFiniteMesh

/-!
# Joint cell and boundary estimates for the quadratic Hardy inequality

The square remainder at one cell leaves a telescoping boundary term.
A free nonnegative parameter sets the relative prices of inner samples
and the outer trace. Geometric meshes test both terms simultaneously.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Bulk price when the outer trace has coefficient 1/(1+q). -/
def meshHardyCellPrice (q Q : ℝ) : ℝ := q*(1-Q)^2/((1+q)*Q*(q+Q))

private theorem cell_residue {q Q s : ℝ} (hq : 0≤q) (hQ : 0<Q) (h1 : Q≤1)
    (hs : 0<s) (small : s≤Q) : (1+q)*meshHardyCellPrice q Q ≤ q*(1-s)^2/(s*(q+s)) := by
  have num := pow_le_pow_left₀ (sub_nonneg.mpr h1) (sub_le_sub_left small 1) 2
  have den := mul_le_mul small (add_le_add (le_refl q) small) (add_nonneg hq hs.le) hQ.le
  have sumQ := add_pos_of_nonneg_of_pos hq hQ
  have sums := add_pos_of_nonneg_of_pos hq hs
  calc _ = q*(1-Q)^2/(Q*(q+Q)) := by
             unfold meshHardyCellPrice
             field_simp [(add_pos_of_pos_of_nonneg zero_lt_one hq).ne',hQ.ne',sumQ.ne']
         _ ≤ _ := by
             apply (div_le_div_iff₀ (mul_pos hQ sumQ) (mul_pos hs sums)).mpr
             exact (mul_le_mul_of_nonneg_left den (mul_nonneg hq (sq_nonneg _))).trans
               (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left num hq) (mul_pos hQ sumQ).le)

private theorem normalized_hardy_cell {q Q s w : ℝ} (hq : 0≤q) (hQ : 0<Q) (h1 : Q≤1) (hs : 0<s)
    (how : w=0 ∨ s≤Q ∧ w=(1+q)*(meshHardyCellPrice q Q)) (x y : ℝ) :
    w*x^2+(1-s)*y^2 ≤ (1+q)*(y-x)^2+(1-s)/s*x^2 := by
  let R := q*(1-s)^2/(s*(q+s))
  have price : w≤R := by
    rcases how with rfl|⟨small,rfl⟩
    · exact div_nonneg (mul_nonneg hq (sq_nonneg _)) (mul_pos hs (add_pos_of_nonneg_of_pos hq hs)).le
    · exact cell_residue hq hQ h1 hs small
  have id : (1+q)*(y-x)^2+(1-s)/s*x^2-(1-s)*y^2 =
      (q+s)*(y-(1+q)*x/(q+s))^2+R*x^2 := by
    dsimp only [R]
    field_simp [hs.ne',(add_pos_of_nonneg_of_pos hq hs).ne']
    ring
  have residual := mul_nonneg (add_pos_of_nonneg_of_pos hq hs).le (sq_nonneg (y-(1+q)*x/(q+s)))
  linarith only [id,residual,mul_le_mul_of_nonneg_right price (sq_nonneg x)]

private theorem hardy_cell_with_price {q Q a b w x y : ℝ} (hq : 0≤q) (hQ : 0<Q) (h1 : Q≤1)
    (ha : 0≤a) (ab : a<b) (ground : a=0 → x=0)
    (price : w=0 ∨ (1-Q)*b≤b-a ∧ w=meshHardyCellPrice q Q) :
    w*(x^2/(b-a)) + y^2/((1+q)*b) ≤ (y-x)^2/(b-a) + x^2/((1+q)*a) := by
  have bp := ha.trans_lt ab
  have qp := add_pos_of_pos_of_nonneg zero_lt_one hq
  rcases ha.eq_or_lt with zero|apos
  · have a0 := zero.symm
    rw [ground a0,a0]
    simp only [zero_pow (by norm_num : 2≠0),zero_div,mul_zero,zero_add,sub_zero,div_zero,add_zero]
    apply (div_le_div_iff₀ (mul_pos qp bp) bp).mpr
    have grow : b≤(1+q)*b := by linarith only [mul_nonneg hq bp.le]
    exact mul_le_mul_of_nonneg_left grow (sq_nonneg y)
  · have how : (1+q)*w=0 ∨ a/b≤Q ∧ (1+q)*w=(1+q)*(meshHardyCellPrice q Q) := by
      rcases price with rfl|⟨chosen,rfl⟩
      · exact Or.inl (mul_zero _)
      · exact Or.inr ⟨(div_le_iff₀ bp).mpr (by linarith only [chosen]),rfl⟩
    have cert := normalized_hardy_cell hq hQ h1 (div_pos apos bp) how x y
    have factor := mul_pos qp (sub_pos.mpr ab)
    apply le_of_mul_le_mul_left (a:=(1+q)*(b-a)) ?_ factor
    calc _ = (1+q)*w*x^2+(1-a/b)*y^2 := by
               field_simp [bp.ne',qp.ne',(sub_pos.mpr ab).ne']
         _ ≤ _ := cert
         _ = _ := by field_simp [apos.ne',bp.ne',qp.ne',(sub_pos.mpr ab).ne']

/-- At relative width at least 1−Q the selected inner samples and the outer
boundary value have a joint energy bound for every nonnegative parameter q. -/
theorem selected_hardy_cells_with_trace {q Q : ℝ} (hq : 0≤q) (hQ : 0<Q) (h1 : Q≤1)
    (h z : ℕ → ℝ) (m : ℕ) (G : Finset ℕ) (endz : z m=0)
    (mesh : ∀ i∈range m, 0≤h (i+1) ∧ h (i+1)<h i) (sub : G⊆range m)
    (selected : ∀ i∈G, (1-Q)*h i≤h i-h (i+1)) :
    meshHardyCellPrice q Q*(∑ i ∈ G,z (i+1)^2/(h i-h (i+1)))+z 0^2/((1+q)*h 0) ≤
      ∑ i ∈ range m,(z i-z (i+1))^2/(h i-h (i+1)) := by
  let flux (i : ℕ) := z i^2/((1+q)*h i)
  let α := meshHardyCellPrice q Q
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
      have cell := hardy_cell_with_price (w:=α) (y:=z i) hq hQ h1 (mesh i hi).1 (mesh i hi).2 ground
        (Or.inr ⟨selected i hit,rfl⟩)
      linarith only [cell]
    · rw [if_neg hit]
      have cell := hardy_cell_with_price (Q:=Q) (w:=0) (y:=z i) hq hQ h1 (mesh i hi).1 (mesh i hi).2 ground (Or.inl rfl)
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

/-- A geometric sequence of finite cell widths realizes the weighted
inner samples and differences of any sequence grounded at its last index. -/
theorem exists_grounded_geometric_hardy_mesh {q : ℝ} (hq : 0<q) (hq1 : q<1)
    {m : ℕ} (x : ℕ → ℝ) (endx : x m=0) : ∃ h z : ℕ → ℝ, h m=0 ∧ z m=0 ∧
      (∀ i∈range m, 0≤h (i+1) ∧ h (i+1)<h i) ∧
      (∀ i∈range m, (1-q^2)*h i≤h i-h (i+1)) ∧
      h 0=(1-(q^m)^2)/(1-q^2) ∧ z 0=x 0 ∧
      (∑ i ∈ range m,z (i+1)^2/(h i-h (i+1)))=(∑ i ∈ range m,(q*x (i+1))^2) ∧
      (∑ i ∈ range m,(z i-z (i+1))^2/(h i-h (i+1)))=∑ i ∈ range m,(x i-q*x (i+1))^2 := by
  let β := 1-q^2
  let r (i : ℕ) := (q^i)^2
  let h (i : ℕ) := (r i-r m)/β
  let z (i : ℕ) := q^i*x i
  have βpos : 0<β := by
    have sq := mul_lt_mul_of_pos_right hq1 hq
    dsimp only [β]
    nlinarith only [sq,hq1]
  have width (i : ℕ) : h i-h (i+1)=r i := by
    dsimp only [h,r]
    rw [pow_succ q]
    field_simp [βpos.ne']
    dsimp only [β]
    ring
  have ground (i : ℕ) (le : i≤m) : 0≤h i :=
    div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (pow_pos hq m).le
      (pow_le_pow_of_le_one hq.le hq1.le le) 2)) βpos.le
  have mesh (i : ℕ) (hi : i∈range m) : 0≤h (i+1) ∧ h (i+1)<h i :=
    ⟨ground (i+1) (mem_range.mp hi),sub_pos.mp ((width i).symm ▸ sq_pos_of_pos (pow_pos hq i))⟩
  have selected (i : ℕ) (_ : i∈range m) : β*h i≤h i-h (i+1) := by
    rw [width,show β*h i=r i-r m by dsimp only [h]; field_simp [βpos.ne']]
    exact sub_le_self _ (sq_nonneg (q^m))
  have readout (i : ℕ) : z (i+1)^2/(h i-h (i+1))=(q*x (i+1))^2 := by
    rw [width]
    dsimp only [z,r]
    rw [pow_succ q]
    field_simp [pow_ne_zero i hq.ne']
  have loss (i : ℕ) : (z i-z (i+1))^2/(h i-h (i+1))=(x i-q*x (i+1))^2 := by
    rw [width]
    dsimp only [z,r]
    rw [pow_succ q]
    field_simp [pow_ne_zero i hq.ne']
  exact ⟨h,z,by simp [h],by simp [z,endx],mesh,selected,by simp [h,r,β],by simp [z],
    sum_congr rfl (fun i _ => readout i),sum_congr rfl (fun i _ => loss i)⟩

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
