import GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchyResonance

/-!
# The three-soliton identity at every odd cubic multiplicity

For three signed cubic momenta, the graph equation at their sum times
their Vandermonde is a product of differences of squares. It survives
every sign change. This pulls every even extra power of the graph
equation outside the cleared Hirota residual. The remaining alternating
identity for the five simple dispersions is linear in their cofactors.
This is the sufficiency direction of Shi, arXiv:2611.22194, Theorem 6.1(a),
for the real cubic hierarchy.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy

def vandermonde (a b c : ℝ) : ℝ := (a-b)*(a-c)*(b-c)

private def common (a b c : ℝ) : ℝ := 3*(a^2-b^2)*(a^2-c^2)*(b^2-c^2)

theorem triple_graph_factor (a b c : ℝ) :
    graph (a+b+c) (a^3+b^3+c^3) * vandermonde a b c = common a b c := by
  unfold graph vandermonde common
  ring

/-- Simultaneous sign reversal is redundant for even dispersion, so four
relative sign patterns give the cleared three-wave coefficient. -/
def paritySum (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  F a b c + F a (-b) (-c) + F (-a) b (-c) + F (-a) (-b) c

/-- q additional graph pairs raise the squared phase to power q+1.
This form is polynomial even when two momenta coincide or sum to zero. -/
def threeWave (P : ℝ → ℝ → ℝ) (q : ℕ) (a b c : ℝ) : ℝ :=
  paritySum (fun x y z =>
    let u := x+y+z
    let v := x^3+y^3+z^3
    graph u v^(2*q) * P u v * (vandermonde x y z ^ 2)^(q+1)) a b c

private theorem multiplicity_term (P : ℝ → ℝ → ℝ) (q : ℕ) (a b c : ℝ) :
    let u := a+b+c
    let v := a^3+b^3+c^3
    graph u v^(2*q) * P u v * (vandermonde a b c^2)^(q+1) =
      (common a b c)^(2*q) * (P u v * vandermonde a b c^2) := by
  dsimp only
  rw [← triple_graph_factor, mul_pow, pow_mul, pow_mul, pow_succ]
  ring

/-- Multiplicity changes the whole three-wave residual by one scalar,
even for a dispersion outside the integrable hierarchy. -/
theorem threeWave_multiplicity (P : ℝ → ℝ → ℝ) (q : ℕ) (a b c : ℝ) :
    threeWave P q a b c = common a b c ^ (2*q) * threeWave P 0 a b c := by
  simp only [threeWave,paritySum,multiplicity_term,common,even_two.neg_pow,
    mul_zero,pow_zero,one_mul,mul_add]

private def alternant (H : ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  paritySum (fun x y z => vandermonde x y z * H (x+y+z) (x^3+y^3+z^3)) a b c

private theorem alternant_linear (f g : ℝ → ℝ → ℝ) (h a b c : ℝ) :
    alternant (fun u v => h*f u v+g u v) a b c =
      h*alternant f a b c + alternant g a b c := by
  unfold alternant paritySum
  ring

private def H₄ (u _ : ℝ) := u
private def H₆ (u v : ℝ) := u^3+2*v
private def H₈ (u v : ℝ) := u^2*(u^3-4*v)
private def H₁₀ (u v : ℝ) := u*(u^3-4*v)*(u^3+2*v)
private def H₁₂ (u v : ℝ) := (u^3-4*v)*(u^6+28*u^3*v+16*v^2)

private theorem alternants (a b c : ℝ) :
    alternant H₄ a b c = 0 ∧ alternant H₆ a b c = 0 ∧ alternant H₈ a b c = 0 ∧
    alternant H₁₀ a b c = 0 ∧ alternant H₁₂ a b c = 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    simp only [alternant,paritySum,vandermonde,H₄,H₆,H₈,H₁₀,H₁₂] <;> ring

private def cofactor (w : Weights) (u v : ℝ) :=
  w.w4*H₄ u v+(w.w6*H₆ u v+(w.w8*H₈ u v+(w.w10*H₁₀ u v+(w.w12*H₁₂ u v+0))))

private theorem simple_term (w : Weights) (a b c : ℝ) :
    dispersion w (a+b+c) (a^3+b^3+c^3)*vandermonde a b c^2 =
      common a b c * (vandermonde a b c * cofactor w (a+b+c) (a^3+b^3+c^3)) := by
  rw [← triple_graph_factor]
  unfold dispersion cofactor H₄ H₆ H₈ H₁₀ H₁₂
  generalize graph (a+b+c) (a^3+b^3+c^3) = G
  generalize vandermonde a b c = V
  generalize a+b+c = u
  generalize a^3+b^3+c^3 = v
  ring

/-- Every real linear combination of the five symbols passes Hirota's
three-body test at every odd multiplicity, including collision configurations. -/
theorem threeWave_vanishes (w : Weights) (q : ℕ) (a b c : ℝ) :
    threeWave (dispersion w) q a b c = 0 := by
  obtain ⟨h4,h6,h8,h10,h12⟩ := alternants a b c
  have hz : alternant (cofactor w) a b c = 0 := by
    simp only [cofactor,alternant_linear,h4,h6,h8,h10,h12,mul_zero,zero_add]
    simp [alternant,paritySum]
  rw [threeWave_multiplicity]
  suffices h : threeWave (dispersion w) 0 a b c = common a b c * alternant (cofactor w) a b c by
    rw [h,hz,mul_zero,mul_zero]
  simp only [threeWave,alternant,paritySum,mul_zero,pow_zero,one_mul,zero_add,pow_one,simple_term,
    common,even_two.neg_pow,mul_add]

#print axioms triple_graph_factor
#print axioms threeWave_multiplicity
#print axioms threeWave_vanishes
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicHierarchy
