import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceSquares

/-!
# The complete positive trace-one slice in the simplest cubic order

Write an element of trace one as 1 − u/X − v/(X−1). If r is the largest
root, positivity places (u,v) in the open triangle with vertices
(r−1,1−1/r), (−1−1/(r−1),r), and (−1/r,−1/(r−1)). The outer strips
of this triangle leave only three exceptional lattice points. They give
the three unit squares; all other points fill one integral triangle.
-/

noncomputable section
namespace RHTower.OrbitCubic

/-- Strict positivity of the reciprocal-basis trace-one element at all real roots. -/
def positiveSlice (m : ℤ) (p : ℤ × ℤ) := ∀ x : ℝ, binary ((m:ℝ)-1/2) x 1 = 0 →
  0 < traceBasis 1 (-(p.1:ℝ)) (-(p.2:ℝ)) x

private theorem right_between {m : ℝ} (hm : 2 ≤ m) :
    ∃ r : ℝ, m < r ∧ r < m+1 ∧ r = m+r⁻¹+(r-1)⁻¹ ∧ binary (m-1/2) r 1 = 0 := by
  let f := fun x : ℝ => binary (m-1/2) x 1
  have hf (x : ℝ) : f x = (x-m)*x*(x-1)-(x-1)-x := by simp only [f,arrowhead_secular,sub_add_cancel]
  have h0 : f m < 0 := by rw [hf]; nlinarith only [hm]
  have h1 : 0 < f (m+1) := by rw [hf]; nlinarith only [hm,mul_nonneg (sub_nonneg.mpr hm) (by linarith only [hm] : 0 ≤ m+1)]
  have hc : Continuous f := by simp only [funext hf]; fun_prop
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (show m ≤ m+1 by linarith) hc.continuousOn
    (show 0 ∈ Set.Icc (f m) (f (m+1)) from ⟨h0.le,h1.le⟩)
  have hm' : m < r := lt_of_le_of_ne hr.1 (fun h => h0.ne (h.symm ▸ he))
  have hr' : r < m+1 := lt_of_le_of_ne hr.2 (fun h => h1.ne' (h ▸ he))
  have h := he
  rw [hf] at h
  refine ⟨r,hm',hr',?_,he⟩
  field_simp [(by linarith only [hm',hm] : r ≠ 0),(by linarith only [hm',hm] : r-1 ≠ 0)]
  linear_combination h

private theorem root_triple {m r : ℝ} (hr : 1 < r) (he : r = m+r⁻¹+(r-1)⁻¹) (x : ℝ) :
    binary (m-1/2) x 1 = (x-r)*(x+(r-1)⁻¹)*(x-(1-r⁻¹)) := by
  rw [arrowhead_secular,sub_add_cancel,show m = r-r⁻¹-(r-1)⁻¹ by linarith only [he]]
  field_simp [(by linarith only [hr] : r ≠ 0),(sub_pos.mpr hr).ne']
  ring

private def first (r u v : ℝ) := 1+(r-1)*u+(1-r⁻¹)*v
private def second (r u v : ℝ) := 1+(-1-(r-1)⁻¹)*u+r*v
private def third (r u v : ℝ) := 1-r⁻¹*u-(r-1)⁻¹*v

private theorem orbit_values {r : ℝ} (hr : 1 < r) (u v : ℝ) :
    traceBasis 1 (-u) (-v) (-(r-1)⁻¹) = first r u v ∧
    traceBasis 1 (-u) (-v) (1-r⁻¹) = second r u v ∧
    traceBasis 1 (-u) (-v) r = third r u v := by
  have h0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have h1 := (sub_pos.mpr hr).ne'
  have ha : -(r-1)⁻¹-1 = -r/(r-1) := by field_simp [h1]; ring
  have hb : 1-r⁻¹ = (r-1)/r := by field_simp [h0]
  refine ⟨?_,?_,?_⟩
  · simp only [traceBasis,first,ha,inv_neg,inv_inv,inv_div]
    field_simp [h0]
  · simp only [traceBasis,second,hb,inv_div]
    field_simp [h1]
    ring
  · unfold traceBasis third
    ring

private theorem convex_vertices {r u v : ℝ} (hr : 1 < r)
    (ha : 0 < first r u v) (hb : 0 < second r u v) (hc : 0 < third r u v) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a+b+c = 1 ∧
      a*(r-1)+b*(-1-(r-1)⁻¹)+c*(-r⁻¹) = u ∧
      a*(1-r⁻¹)+b*r+c*(-(r-1)⁻¹) = v := by
  let D := r^2-r+1
  have hg : 0 < D := by dsimp only [D]; nlinarith only [sq_nonneg (r-1),hr]
  have h0 := zero_lt_one.trans hr
  have h1 := sub_pos.mpr hr
  refine ⟨r^2*first r u v/D^2,(r-1)^2*second r u v/D^2,r^2*(r-1)^2*third r u v/D^2,
    by positivity,by positivity,by positivity,?_,?_,?_⟩ <;>
    unfold first second third <;> field_simp [hg.ne',h0.ne',h1.ne'] <;> dsimp only [D] <;> ring

private theorem mix_lt {a b c s t u k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : a+b+c = 1) (hs : s < k) (ht : t < k) (hu : u < k) : a*s+b*t+c*u < k := calc
  _ < a*k+b*k+c*k := add_lt_add (add_lt_add (mul_lt_mul_of_pos_left hs ha) (mul_lt_mul_of_pos_left ht hb))
    (mul_lt_mul_of_pos_left hu hc)
  _ = k := by rw [← add_mul,← add_mul,he,one_mul]

private theorem affine_coordinates (a b c p q x y X Y z w : ℝ) (hs : a+b+c = 1) :
    1+p*(a*x+b*X+c*z)+q*(a*y+b*Y+c*w) =
      a*(1+p*x+q*y)+b*(1+p*X+q*Y)+c*(1+p*z+q*w) := by linear_combination -hs

/-- The continuous positive slice in reciprocal coordinates is exactly the
open triangle, with the three embeddings as its barycentric functionals. -/
theorem positive_slice_triangle (n : ℕ) :
    let m := (n:ℝ)+2
    ∃ r, m < r ∧ r < m+1 ∧ r = m+r⁻¹+(r-1)⁻¹ ∧ ∀ u v : ℝ,
      (∀ x, binary (m-1/2) x 1 = 0 → 0 < traceBasis 1 (-u) (-v) x) ↔
      ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a+b+c = 1 ∧
        a*(r-1)+b*(-1-(r-1)⁻¹)+c*(-r⁻¹) = u ∧ a*(1-r⁻¹)+b*r+c*(-(r-1)⁻¹) = v := by
  intro m
  have hm : 2 ≤ m := by dsimp [m]; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨r,hr,hr',he,er⟩ := right_between hm
  have h1 : 1 < r := by linarith only [hr,hm]
  have h0 := (zero_lt_one.trans h1).ne'
  have hR := (sub_pos.mpr h1).ne'
  refine ⟨r,hr,hr',he,fun u v => ?_⟩
  obtain ⟨ea,eb,ec⟩ := orbit_values h1 u v
  constructor
  · intro h
    apply convex_vertices h1
    · rw [← ea]; apply h; rw [root_triple h1 he]; ring
    · rw [← eb]; apply h; rw [root_triple h1 he]; ring
    · rw [← ec]; exact h _ er
  · rintro ⟨a,b,c,ap,bp,cp,hs,hu,hv⟩ x hx
    let A := r-1
    let B := 1-r⁻¹
    let C := -1-(r-1)⁻¹
    let D := -r⁻¹
    let E := -(r-1)⁻¹
    have zeroes : 1+A*C+B*r = 0 ∧ 1+A*D+B*E = 0 ∧ 1+C*D+r*E = 0 := by
      dsimp only [A,B,C,D,E]; refine ⟨?_,?_,?_⟩ <;> field_simp [h0,hR] <;> ring
    obtain ⟨z1,z2,z3⟩ := zeroes
    have val (p q : ℝ) : 1+p*u+q*v =
        a*(1+p*A+q*B)+b*(1+p*C+q*r)+c*(1+p*D+q*E) := by
      rw [← hu,← hv]; exact affine_coordinates _ _ _ _ _ _ _ _ _ _ _ hs
    have pos (s t : ℝ) : 0 < 1+s*s+t*t := by nlinarith only [sq_nonneg s,sq_nonneg t]
    rw [root_triple h1 he,mul_eq_zero,mul_eq_zero,sub_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg] at hx
    rcases hx with (hx|rfl)|rfl
    · subst x
      rw [ec]
      change 0 < 1-r⁻¹*u-(r-1)⁻¹*v
      rw [show 1-r⁻¹*u-(r-1)⁻¹*v = 1+D*u+E*v by dsimp [D,E]; ring,val]
      rw [mul_comm D A,mul_comm E B,mul_comm D C,mul_comm E r,z2,z3]
      simpa only [mul_zero,zero_add] using mul_pos cp (pos D E)
    · rw [ea]
      change 0 < 1+A*u+B*v
      rw [val,z1,z2]
      simpa only [mul_zero,add_zero] using mul_pos ap (pos A B)
    · rw [eb]
      change 0 < 1+C*u+r*v
      rw [val,mul_comm C A,mul_comm r B,z1,z3]
      simpa only [mul_zero,zero_add,add_zero] using mul_pos bp (pos C r)

private theorem positive_strips {m r u v : ℝ} (hm : 2 ≤ m) (hr : m < r) (hr' : r < m+1)
    (he : r = m+r⁻¹+(r-1)⁻¹)
    (ha : 0 < first r u v) (hb : 0 < second r u v) (hc : 0 < third r u v) :
    -2 < u ∧ -1 < v ∧ v < m+1 ∧ u+v < m+1 := by
  have hR : 1 < r := by linarith only [hm,hr]
  have e : 0 < r⁻¹ := inv_pos.mpr (zero_lt_one.trans hR)
  have f : 0 < (r-1)⁻¹ := inv_pos.mpr (sub_pos.mpr hR)
  have e' : r⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hR)).mpr hR
  have f' : (r-1)⁻¹ < 1 := (inv_lt_one₀ (sub_pos.mpr hR)).mpr (by linarith only [hr,hm])
  obtain ⟨a,b,c,ap,bp,cp,hs,hx,hy⟩ := convex_vertices hR ha hb hc
  have mix := @mix_lt a b c
  have hu := mix (s := -(r-1)) (t := -(-1-(r-1)⁻¹)) (u := r⁻¹) (k := 2)
    ap bp cp hs (by linarith only [hR]) (by linarith only [f']) (by linarith only [e'])
  have hv := mix (s := -(1-r⁻¹)) (t := -r) (u := (r-1)⁻¹) (k := 1)
    ap bp cp hs (by linarith only [e']) (by linarith only [hR]) f'
  have hv' := mix (s := 1-r⁻¹) (t := r) (u := -(r-1)⁻¹) (k := m+1)
    ap bp cp hs (by linarith only [e,hm]) hr' (by linarith only [f,hm])
  have huv := mix (s := (r-1)+(1-r⁻¹)) (t := (-1-(r-1)⁻¹)+r) (u := -r⁻¹+(-(r-1)⁻¹)) (k := m+1)
    ap bp cp hs (by linarith only [he,f']) (by linarith only [hr',f]) (by linarith only [e,f,hm])
  exact ⟨by linarith only [hu,hx],by linarith only [hv,hy],hy ▸ hv',by linarith only [huv,hx,hy]⟩

private theorem boundary_faces {m r : ℝ} (hr : 2 < r) (he : r = m+r⁻¹+(r-1)⁻¹) :
    (∀ v, 0 < first r (-1) v → m-1 < v) ∧
    (∀ u, 0 < second r u 0 → u < 1) ∧
    (∀ v, 0 < third r (m-v) v → v < 2) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r-1 := by linarith
  have hrinv := inv_pos.mpr hr0
  refine ⟨?_,?_,?_⟩
  · intro v hv
    have hmul := mul_pos hr0 hv
    unfold first at hmul
    have he' : r-1-(r-1)⁻¹ = m-1+r⁻¹ := by linarith only [he]
    have hprd : (r-1)*(v-(r-1-(r-1)⁻¹)) = r*(1+(r-1)*(-1)+(1-r⁻¹)*v) := by
      field_simp [hr0.ne',hr1.ne']
      ring
    rw [← hprd] at hmul
    have hs := pos_of_mul_pos_right hmul hr1.le
    linarith only [hs,he',hrinv]
  · intro u hu
    have hu' : 0 < (r-1)*second r u 0 := mul_pos hr1 hu
    have e : (r-1)*second r u 0 = (r-1)-r*u := by
      unfold second
      field_simp [hr1.ne']
      ring
    rw [e] at hu'
    exact (lt_of_mul_lt_mul_left (show r*u < r*1 by linarith only [hu']) hr0.le)
  · intro v hv
    have hmul := mul_pos (mul_pos hr0 hr1) hv
    have ha : r*(r-1)*third r (m-v) v = 2-r⁻¹-v := by
      rw [show m = r-r⁻¹-(r-1)⁻¹ by linarith only [he]]
      unfold third
      field_simp [hr0.ne',hr1.ne']
      ring
    rw [ha] at hmul
    linarith only [hmul,hrinv]

/-- For m = n+2, every positive integral trace-one element is either one
of the three unit squares or belongs to the displayed integral triangle. -/
theorem exact_positive_slice (n : ℕ) (u v : ℤ) :
    positiveSlice ((n:ℤ)+2) (u,v) ↔
      (u = 0 ∧ v = 0) ∨ (u = (n:ℤ)+1 ∧ v = 1) ∨ (u = -1 ∧ v = (n:ℤ)+2) ∨
      (0 ≤ u ∧ 1 ≤ v ∧ u+v ≤ (n:ℤ)+1) := by
  let m : ℝ := (n:ℝ)+2
  have hm : 2 ≤ m := by dsimp only [m]; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  unfold positiveSlice
  simp only [Int.cast_add,Int.cast_natCast,Int.cast_ofNat]
  change (∀ x, binary (m-1/2) x 1 = 0 → 0 < traceBasis 1 (-(u:ℝ)) (-(v:ℝ)) x) ↔ _
  constructor
  · intro h
    obtain ⟨r,hr,hr',he,hroot⟩ := right_between hm
    have h2 : 2 < r := hm.trans_lt hr
    have h1 : 1 < r := by linarith only [h2]
    have ha : binary (m-1/2) (-(r-1)⁻¹) 1 = 0 := by rw [root_triple h1 he]; ring
    have hb : binary (m-1/2) (1-r⁻¹) 1 = 0 := by rw [root_triple h1 he]; ring
    obtain ⟨ea,eb,ec⟩ := orbit_values h1 (u:ℝ) (v:ℝ)
    have A := ea ▸ h _ ha
    have B := eb ▸ h _ hb
    have C := ec ▸ h _ hroot
    obtain ⟨hu,hv,hv',hs⟩ := positive_strips hm hr hr' he A B C
    obtain ⟨fa,fb,fc⟩ := boundary_faces h2 he
    have huZ : (-2:ℤ) < u := by exact_mod_cast hu
    have hvZ : (-1:ℤ) < v := by exact_mod_cast hv
    have hvZ' : v < (n:ℤ)+2+1 := by dsimp only [m] at hv'; exact_mod_cast hv'
    have hsZ : u+v < (n:ℤ)+2+1 := by dsimp only [m] at hs; exact_mod_cast hs
    by_cases hU : u = -1
    · subst u
      have hgt := fa (v:ℝ) (by simpa only [Int.cast_neg,Int.cast_one] using A)
      have hgt' : (n:ℤ)+2-1 < v := by dsimp only [m] at hgt; exact_mod_cast hgt
      exact Or.inr (Or.inr (Or.inl ⟨rfl,by omega⟩))
    by_cases hV : v = 0
    · subst v
      have hlt := fb (u:ℝ) (by simpa only [Int.cast_zero] using B)
      have hlt' : u < (1:ℤ) := by exact_mod_cast hlt
      exact Or.inl ⟨by omega,rfl⟩
    by_cases hS : u+v = (n:ℤ)+2
    · have heq : (u:ℝ) = m-v := by
        have : (u:ℝ)+(v:ℝ) = (n:ℝ)+2 := by exact_mod_cast hS
        dsimp only [m]; linarith
      have hlt := fc (v:ℝ) (heq ▸ C)
      have hlt' : v < (2:ℤ) := by exact_mod_cast hlt
      exact Or.inr (Or.inl ⟨by omega,by omega⟩)
    exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega⟩))
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨hu,hv,hs⟩) x hx
    · simp [traceBasis]
    · have h0 : x ≠ 0 := by rintro rfl; rw [arrowhead_secular] at hx; norm_num at hx
      have hU := (reciprocal_square_coordinates m x hx).1
      rw [show -(((n:ℤ)+1:ℤ):ℝ) = 1-m by dsimp [m]; push_cast; ring,Int.cast_one,← hU]
      exact sq_pos_of_ne_zero (inv_ne_zero h0)
    · have h1 : x-1 ≠ 0 := by intro H; rw [sub_eq_zero.mp H,arrowhead_secular] at hx; norm_num at hx
      have hV := (reciprocal_square_coordinates m x hx).2
      rw [show -((-1:ℤ):ℝ) = 1 by norm_num,show (((n:ℤ)+2:ℤ):ℝ) = m by simp [m],← hV]
      exact sq_pos_of_ne_zero (inv_ne_zero h1)
    · apply positive_triangle hm (by exact_mod_cast hu) (by exact_mod_cast hv) _ hx
      dsimp only [m]
      have ht : (u:ℝ)+(v:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast hs
      linarith only [ht]

/-- The first three points are the square directions; the other points are
indexed in successive rows of lengths one through n+1. -/
def slicePoint (n : ℕ) : Fin 3 ⊕ TriangleIndex n → ℤ × ℤ
  | .inl k => if k = 0 then (0,0) else if k = 1 then ((n:ℤ)+1,1) else (-1,(n:ℤ)+2)
  | .inr s => ((s.2.val:ℤ),(s.1.val:ℤ)+1-s.2.val)

private theorem slicePoint_injective (n : ℕ) : Function.Injective (slicePoint n) := by
  rintro (k|⟨i,j⟩) (l|⟨i',j'⟩) h
  · fin_cases k <;> fin_cases l <;> simp [slicePoint] at h ⊢ <;> omega
  · have hi := i'.isLt
    have hj := j'.isLt
    fin_cases k <;> simp [slicePoint] at h <;> omega
  · have hi := i.isLt
    have hj := j.isLt
    fin_cases l <;> simp [slicePoint] at h <;> omega
  · change (_,_) = (_,_) at h
    have hu := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    change (j.val : ℤ) = j'.val at hu
    change (i.val : ℤ) + 1 - j.val = (i'.val : ℤ) + 1 - j'.val at hv
    have hi : i = i' := Fin.ext (by omega)
    subst i'
    have hj : j = j' := Fin.ext (by omega)
    subst j'
    rfl

theorem slicePoint_range (n : ℕ) : Set.range (slicePoint n) = {p | positiveSlice ((n:ℤ)+2) p} := by
  ext p
  rcases p with ⟨u,v⟩
  change (∃ s, slicePoint n s = (u,v)) ↔ _
  rw [Set.mem_setOf_eq,exact_positive_slice]
  constructor
  · rintro ⟨(k|⟨i,j⟩),he⟩
    · fin_cases k <;> simp [slicePoint] at he <;> omega
    · have hi := i.isLt
      have hj := j.isLt
      simp [slicePoint] at he
      omega
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨hu,hv,hs⟩)
    · exact ⟨.inl 0,rfl⟩
    · exact ⟨.inl 1,rfl⟩
    · exact ⟨.inl 2,rfl⟩
    · let i : Fin (n+1) := ⟨(u+v-1).toNat,by omega⟩
      let j : Fin (i.val+1) := ⟨u.toNat,by dsimp [i]; omega⟩
      exact ⟨.inr ⟨i,j⟩,Prod.ext (by dsimp [slicePoint,i,j]; omega) (by dsimp [slicePoint,i,j]; omega)⟩

/-- Enumeration of the entire positive trace-one slice by three unit
squares and one finite triangle. -/
def enumeratePositiveSlice (n : ℕ) : (Fin 3 ⊕ TriangleIndex n) ≃
    {p : ℤ × ℤ // positiveSlice ((n:ℤ)+2) p} :=
  (Equiv.ofInjective (slicePoint n) (slicePoint_injective n)).trans (Equiv.setCongr (slicePoint_range n))

/-- Exact positive trace-one lattice count for the nonnegative simplest
cubic parameter n. The three exceptional squares are included. -/
theorem card_positive_slice (n : ℕ) :
    Nat.card {p : ℤ × ℤ // positiveSlice ((n:ℤ)+2) p} = 3+(n+2)*(n+1)/2 := by
  calc
    _ = Nat.card (Fin 3 ⊕ TriangleIndex n) := Nat.card_congr (enumeratePositiveSlice n).symm
    _ = _ := by simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin,card_triangleIndex]

/-- Oriented twice-area of the triangle of real embedding coordinates. -/
def twiceSliceArea (r : ℝ) :=
  ((r-1)-(-r⁻¹))*(r-(-(r-1)⁻¹))-((-1-(r-1)⁻¹)-(-r⁻¹))*((1-r⁻¹)-(-(r-1)⁻¹))

/-- The twice-area equals the square root of the cubic discriminant.
The number of interior lattice points differs from the area by exactly one half. -/
theorem slice_area_discriminant (n : ℕ) :
    let m := (n:ℝ)+2
    let q := m-1/2
    let N := Nat.card {p : ℤ × ℤ // positiveSlice ((n:ℤ)+2) p}
    ∃ r : ℝ, m < r ∧ r < m+1 ∧ binary q r 1 = 0 ∧
      twiceSliceArea r = Real.sqrt (chebyshevRealOrbitCubic q).discr ∧
      twiceSliceArea r = 2*(N:ℝ)+1 := by
  intro m q N
  have hm : 2 ≤ m := by dsimp [m]; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨r,hr,hr',he,er⟩ := right_between hm
  have hR : 1 < r := by linarith only [hr,hm]
  have H : twiceSliceArea r = m^2-m+7 := by
    rw [show m = r-r⁻¹-(r-1)⁻¹ by linarith only [he]]
    unfold twiceSliceArea
    field_simp [(zero_lt_one.trans hR).ne',(sub_pos.mpr hR).ne']
    ring
  have hD : 0 ≤ q^2+27/4 := by positivity
  obtain ⟨k,hk⟩ := Nat.even_mul_succ_self (n+1)
  change (n+1)*(n+2) = k+k at hk
  have hp : (n+2)*(n+1) = 2*k := by rw [Nat.mul_comm,hk,two_mul]
  have hN : N = 3+k := by rw [show N = _ from card_positive_slice n,hp]; omega
  have heq : ((n:ℝ)+2)*((n:ℝ)+1) = 2*(k:ℝ) := by exact_mod_cast hp
  refine ⟨r,hr,hr',er,?_,?_⟩
  · rw [H,chebyshevRealOrbitCubic_discr,Real.sqrt_sq hD]
    dsimp only [q]; ring
  · rw [H,hN]
    push_cast
    dsimp only [m]
    linear_combination heq

#print axioms exact_positive_slice
#print axioms positive_slice_triangle
#print axioms slicePoint_range
#print axioms card_positive_slice
#print axioms slice_area_discriminant
end RHTower.OrbitCubic
