import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceMoments

/-!
# The two-node Gaussian quadrature of the orbit-cubic trace

Moment matching for the positive derivative residues gives a unique
two-point law up to exchange. Like the cubic, it has centered variance two
and third moment −2q. Its fourth moment misses by exactly one half. The
same defect is the constant numerator of the difference of the Jacobi
resolvent fractions.
-/

noncomputable section
namespace RHTower.OrbitCubic

def gaussLeft (q : ℝ) := (-q-Real.sqrt (q^2+8))/2
def gaussRight (q : ℝ) := (-q+Real.sqrt (q^2+8))/2

/-- Moments of a normalized two-point rule, with p the coefficient of u. -/
def twoMoment (u v p : ℝ) (k : ℕ) := p*u^k+(1-p)*v^k

private theorem gauss_nodes (q : ℝ) :
    gaussLeft q < 0 ∧ 0 < gaussRight q ∧ gaussLeft q+gaussRight q = -q ∧
      gaussLeft q*gaussRight q = -2 := by
  have hs := Real.sq_sqrt (show 0 ≤ q^2+8 by positivity)
  have ha : |q| < Real.sqrt (q^2+8) := by
    apply (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,hs]
    linarith
  unfold gaussLeft gaussRight
  exact ⟨by linarith only [ha,neg_abs_le q],by linarith only [ha,le_abs_self q],
    by ring,by linear_combination -hs/4⟩

private theorem two_recurrence (u v p : ℝ) (k : ℕ) :
    twoMoment u v p (k+2) = (u+v)*twoMoment u v p (k+1)-u*v*twoMoment u v p k := by
  simp only [twoMoment,pow_succ]
  ring

private theorem match_iff (q u v p : ℝ) :
    (twoMoment u v p 1 = 0 ∧ twoMoment u v p 2 = 2 ∧ twoMoment u v p 3 = -2*q) ↔
      u+v = -q ∧ u*v = -2 ∧ p*(u-v) = -v := by
  have h0 : twoMoment u v p 0 = 1 := by simp [twoMoment]
  have h2 := two_recurrence u v p 0
  have h3 := two_recurrence u v p 1
  change twoMoment u v p 2 = (u+v)*twoMoment u v p 1-u*v*twoMoment u v p 0 at h2
  change twoMoment u v p 3 = (u+v)*twoMoment u v p 2-u*v*twoMoment u v p 1 at h3
  rw [h0,mul_one] at h2
  constructor
  · rintro ⟨h1,H2,H3⟩
    rw [h1,H2] at h2
    rw [h1,H2,H3] at h3
    refine ⟨by linarith only [h3],by linarith only [h2],?_⟩
    simp only [twoMoment,pow_one] at h1
    linear_combination h1
  · rintro ⟨hs,hp,hw⟩
    have h1 : twoMoment u v p 1 = 0 := by
      simp only [twoMoment,pow_one]
      linear_combination hw
    rw [h1,hp] at h2
    simp only [mul_zero,zero_sub,neg_neg] at h2
    rw [h1,h2,hs,mul_zero,sub_zero] at h3
    exact ⟨h1,h2,by linarith only [h3]⟩

/-- Any real two-node quadrature matching the first three centered moments
is the explicit Gauss rule, including both possible orderings of its nodes.
Positivity of its weights follows from the moment constraints. -/
theorem two_node_quadrature_unique (q u v p : ℝ) :
    (twoMoment u v p 1 = 0 ∧ twoMoment u v p 2 = 2 ∧ twoMoment u v p 3 = -2*q) ↔
      ((u = gaussLeft q ∧ v = gaussRight q) ∨ (u = gaussRight q ∧ v = gaussLeft q)) ∧
        p = v/(v-u) := by
  obtain ⟨hl,hr,hs,hp⟩ := gauss_nodes q
  rw [match_iff]
  constructor
  · rintro ⟨hS,hP,hw⟩
    have hroot : (u-gaussLeft q)*(u-gaussRight q) = 0 := by
      linear_combination u*hS - hP - u*hs + hp
    have nodes : (u = gaussLeft q ∧ v = gaussRight q) ∨ (u = gaussRight q ∧ v = gaussLeft q) := by
      rcases mul_eq_zero.mp hroot with h | h
      · exact Or.inl ⟨sub_eq_zero.mp h,by linarith only [h,hS,hs]⟩
      · exact Or.inr ⟨sub_eq_zero.mp h,by linarith only [h,hS,hs]⟩
    have hne : v-u ≠ 0 := by rcases nodes with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> linarith only [hl,hr]
    exact ⟨nodes,(eq_div_iff hne).mpr (by linear_combination -hw)⟩
  · rintro ⟨hn,rfl⟩
    rcases hn with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · refine ⟨hs,hp,?_⟩
      field_simp [(sub_pos.mpr (hl.trans hr)).ne'] <;> ring
    · refine ⟨by rwa [add_comm],by rwa [mul_comm],?_⟩
      field_simp [(sub_neg.mpr (hl.trans hr)).ne] <;> ring

/-- The normalized positive trace on three actual roots and its two-node
quadrature agree through degree three. The first missed moment has the
same positive defect on every cubic in the family. -/
theorem trace_quadrature_fourth_gap (q : ℝ) :
    let u := gaussLeft q
    let v := gaussRight q
    let p := v/(v-u)
    ∃ a b c : ℝ, binary q a 1 = 0 ∧ binary q b 1 = 0 ∧ binary q c 1 = 0 ∧
      0 < p ∧ p < 1 ∧
      (∀ k ≤ 3, moment a b c (q+1/2) k = twoMoment u v p k) ∧
      moment a b c (q+1/2) 4 = twoMoment u v p 4+1/2 := by
  intro u v p
  obtain ⟨hl,hr,hs,hp⟩ := gauss_nodes q
  obtain ⟨a,b,c,ha,hb,hc,_,_,_,h0,h1,h2,h3,h4,_⟩ := centered_trace_invariants q
  obtain ⟨e1,e2,e3⟩ := (two_node_quadrature_unique q u v p).mpr ⟨Or.inl ⟨rfl,rfl⟩,rfl⟩
  have hgap : 0 < v-u := sub_pos.mpr (hl.trans hr)
  refine ⟨a,b,c,ha,hb,hc,div_pos hr hgap,(div_lt_one hgap).mpr (by linarith only [hl]),?_,?_⟩
  · intro k hk
    interval_cases k
    · simp [h0,twoMoment]
    · exact h1.trans e1.symm
    · exact h2.trans e2.symm
    · exact h3.trans e3.symm
  · have h := two_recurrence u v p 2
    change twoMoment u v p 4 = (u+v)*twoMoment u v p 3-u*v*twoMoment u v p 2 at h
    rw [e2,e3,hs,hp] at h
    rw [h4,h]
    ring

/-- Removing the final Jacobi site produces a constant cross determinant
of one half. Thus the quadratic and cubic denominators have no shared pole. -/
theorem jacobi_quadrature_bezout (q z : ℝ) :
    ((z+q)^2-1/4)*(z*(z+q)-2) - (z+q)*binary q (z+(q+1/2)) 1 = 1/2 := by
  rw [arrowhead_secular]
  ring

/-- At a two-node pole, the original centered cubic has value −z/4,
with opposite signs at the left and right quadrature nodes. -/
theorem cubic_at_quadrature_nodes (q : ℝ) :
    let F := fun z => binary q (z+(q+1/2)) 1
    F (gaussLeft q) = -gaussLeft q/4 ∧ F (gaussRight q) = -gaussRight q/4 ∧
      F (gaussRight q) < 0 ∧ 0 < F (gaussLeft q) := by
  intro F
  obtain ⟨hl,hr,hs,hp⟩ := gauss_nodes q
  have eval (x y : ℝ) (hs : x+y = -q) (hp : x*y = -2) : F x = -x/4 := by
    have hz : x*(x+q)-2 = 0 := by linear_combination x*hs - hp
    unfold F
    rw [arrowhead_secular]
    linear_combination (x+q)*hz
  have hL := eval _ _ hs hp
  have hR := eval _ _ ((add_comm _ _).trans hs) ((mul_comm _ _).trans hp)
  exact ⟨hL,hR,by rw [hR]; linarith only [hr],by rw [hL]; linarith only [hl]⟩

/-- Exact rational quadrature error, with both pole sets explicitly covered. -/
theorem jacobi_resolvent_error (q z : ℝ) :
    let f := binary q (z+(q+1/2)) 1
    let g := z*(z+q)-2
    (f = 0 ∧ g ≠ 0) ∨ (g = 0 ∧ f ≠ 0) ∨
      ((z+q)^2-1/4)/f - (z+q)/g = 1/(2*f*g) := by
  intro f g
  have h := jacobi_quadrature_bezout q z
  change _*g-_*f = 1/2 at h
  by_cases hf : f = 0
  · left
    exact ⟨hf,fun hg => by rw [hf,hg] at h; norm_num at h⟩
  by_cases hg : g = 0
  · exact Or.inr (Or.inl ⟨hg,hf⟩)
  right
  rw [div_sub_div _ _ hf hg,mul_comm f (z+q),h]
  ring

#print axioms two_node_quadrature_unique
#print axioms trace_quadrature_fourth_gap
#print axioms jacobi_quadrature_bezout
#print axioms cubic_at_quadrature_nodes
#print axioms jacobi_resolvent_error
end RHTower.OrbitCubic
