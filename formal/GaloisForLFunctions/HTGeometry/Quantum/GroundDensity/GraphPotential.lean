import GaloisForLFunctions.HTGeometry.WeightedGraphSpectralGap
import Mathlib.Tactic.FieldSimp

/-!
# Ground density and inverse potential on a weighted graph

The variational cancellation in Csirik (arXiv:2611.23062, Proposition 4.2)
gives common ground states for the same density. The graph ground-state
transform supplies an inverse potential for any positive normalized
amplitude and identifies all its ground states, including on disconnected graphs.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.WeightedGraph

noncomputable section

variable {V : Type*} [Fintype V]

/-- The diagonal part of a graph Hamiltonian in the site basis. -/
def potentialForm (a x : V → ℝ) : ℝ := ∑ v, a v * (x v * x v)

/-- The graph Laplacian plus a site potential. -/
def schrodingerForm (G : WeightedGraph V) (a x : V → ℝ) : ℝ :=
  G.dirichlet x x + potentialForm a x

/-- The variational ground-state condition on a normalized amplitude. -/
def IsGroundAt (G : WeightedGraph V) (a : V → ℝ) (E : ℝ) (x : V → ℝ) : Prop :=
  potentialForm (fun _ => 1) x = 1 ∧ G.schrodingerForm a x = E ∧
    ∀ y, E * potentialForm (fun _ => 1) y ≤ G.schrodingerForm a y

private theorem schrodingerForm_sub (G : WeightedGraph V) (a b x : V → ℝ) :
    G.schrodingerForm a x - G.schrodingerForm b x =
      potentialForm (fun v => a v - b v) x := by
  simp only [schrodingerForm, potentialForm, sub_mul, Finset.sum_sub_distrib,
    add_sub_add_left_eq_sub]

/-- Equal site densities force the two variational ground states to be common.
The difference of ground energies is exactly the potential difference paired
against that density. -/
theorem commonGround_of_eq_density (G : WeightedGraph V) (a b x y : V → ℝ) (E F : ℝ) :
    G.IsGroundAt a E x ∧ G.IsGroundAt b F y ∧ (∀ v, x v * x v = y v * y v) →
      G.IsGroundAt a E y ∧ G.IsGroundAt b F x ∧
        E - F = potentialForm (fun v => a v - b v) x := by
  rintro ⟨⟨hx, hxa, hboundA⟩, ⟨hy, hyb, hboundB⟩, hdensity⟩
  have hdiff : potentialForm (fun v => a v - b v) x =
      potentialForm (fun v => a v - b v) y := by
    simp only [potentialForm, hdensity]
  have h₁ := G.schrodingerForm_sub a b x
  have h₂ := G.schrodingerForm_sub a b y
  rw [hxa, hdiff] at h₁
  rw [hyb] at h₂
  have hAY := hboundA y
  have hBX := hboundB x
  rw [hy, mul_one] at hAY
  rw [hx, mul_one] at hBX
  have hyA : G.schrodingerForm a y = E := by linarith only [h₁, h₂, hAY, hBX]
  have hxB : G.schrodingerForm b x = F := by linarith only [h₁, h₂, hAY, hBX]
  refine ⟨⟨hy, hyA, hboundA⟩, ⟨hx, hxB, hboundB⟩, ?_⟩
  rw [← G.schrodingerForm_sub, hxa, hxB]

/-- A strictly positive amplitude, which can be used as a change of density. -/
abbrev PositiveAmplitude (V : Type*) := {f : V → ℝ // ∀ v, 0 < f v}

/-- The canonical inverse potential at ground energy E for a positive amplitude. -/
def inversePotential (G : WeightedGraph V) (f : PositiveAmplitude V) (E : ℝ) (v : V) : ℝ :=
  E - G.mass v + (∑ u, G.w v u * f.1 u) / f.1 v

/-- Edge conductances weighted by the product of the endpoint amplitudes. -/
def groundConductance (G : WeightedGraph V) (f : PositiveAmplitude V) : WeightedGraph V where
  w v u := G.w v u * (f.1 v * f.1 u)
  w_symm v u := by rw [G.w_symm v u, mul_comm (f.1 v) (f.1 u)]
  w_nonneg v u := mul_nonneg (G.w_nonneg v u) (mul_nonneg (f.2 v).le (f.2 u).le)
  w_diag v := by rw [G.w_diag v, zero_mul]

private theorem groundConductance_mass (G : WeightedGraph V) (f : PositiveAmplitude V) (v : V) :
    (G.groundConductance f).mass v = f.1 v * ∑ u, G.w v u * f.1 u := by
  rw [mass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by change G.w v u * (f.1 v * f.1 u) = _; ring

/-- The energy defect at the inverse potential is a nonnegative Dirichlet form
of the test amplitude divided by the reference amplitude. -/
theorem inversePotential_defect (G : WeightedGraph V) (f : PositiveAmplitude V)
    (E : ℝ) (x : V → ℝ) :
    G.schrodingerForm (G.inversePotential f E) x -
      E * potentialForm (fun _ => 1) x =
        (G.groundConductance f).dirichlet (fun v => x v / f.1 v) (fun v => x v / f.1 v) := by
  let r : V → ℝ := fun v => x v / f.1 v
  let H := G.groundConductance f
  have hcross : H.averaging r r = G.averaging x x := by
    unfold averaging
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro u _
    change G.w v u * (f.1 v * f.1 u) * ((x v / f.1 v) * (x u / f.1 u)) = _
    field_simp [(f.2 v).ne', (f.2 u).ne'] <;> ring
  have hdiag : G.massInner x x + potentialForm (G.inversePotential f E) x =
      E * potentialForm (fun _ => 1) x + H.massInner r r := by
    simp only [massInner, potentialForm, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    change G.mass v * (x v * x v) + G.inversePotential f E v * (x v * x v) =
      E * (x v * x v) + (G.groundConductance f).mass v *
        ((x v / f.1 v) * (x v / f.1 v))
    rw [inversePotential, groundConductance_mass]
    field_simp [(f.2 v).ne'] <;> ring
  change _ = H.dirichlet r r
  rw [schrodingerForm, G.dirichlet_self_eq_sub, H.dirichlet_self_eq_sub, hcross]
  linarith only [hdiag]

/-- Any normalized positive reference amplitude realizes a ground state for
the explicit recovered potential. -/
theorem inversePotential_ground (G : WeightedGraph V)
    (f : {f : PositiveAmplitude V // potentialForm (fun _ => 1) f.1 = 1}) (E : ℝ) :
    G.IsGroundAt (G.inversePotential f.1 E) E f.1.1 := by
  have hdef := G.inversePotential_defect f.1 E f.1.1
  have hzero : (G.groundConductance f.1).dirichlet (fun _ => 1) (fun _ => 1) = 0 := by
    simp only [dirichlet, sub_self, mul_zero, Finset.sum_const_zero, zero_div]
  have hconst : (fun v => f.1.1 v / f.1.1 v) = (fun _ => (1 : ℝ)) :=
    funext fun v => div_self (f.1.2 v).ne'
  rw [f.2, mul_one, hconst, hzero] at hdef
  refine ⟨f.2, sub_eq_zero.mp hdef, fun x => sub_nonneg.mp ?_⟩
  rw [G.inversePotential_defect]
  exact (G.groundConductance f.1).dirichlet_self_nonneg _

/-- Vanishing Dirichlet energy means equality at both endpoints of every edge
of positive weight. -/
theorem dirichlet_self_zero_iff_edges (G : WeightedGraph V) (x : V → ℝ) :
    G.dirichlet x x = 0 ↔ ∀ v u, 0 < G.w v u → x v = x u := by
  rw [dirichlet, div_eq_zero_iff, or_iff_left (two_ne_zero : (2 : ℝ) ≠ 0)]
  constructor
  · intro h v u hw
    have hnn (a b : V) : 0 ≤ G.w a b * ((x a - x b) * (x a - x b)) :=
      mul_nonneg (G.w_nonneg a b) (mul_self_nonneg _)
    have hv := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun b _ => hnn a b)).mp h v (Finset.mem_univ v)
    have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn v b)).mp hv u
      (Finset.mem_univ u)
    exact sub_eq_zero.mp ((mul_self_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left hw.ne')))
  · intro h
    refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun u _ => ?_
    rcases (G.w_nonneg v u).eq_or_lt with hw | hw
    · rw [← hw, zero_mul]
    · rw [h v u hw, sub_self, mul_zero, mul_zero]

/-- The inverse potential's full equality case. The ratio of the test amplitude
to the reference amplitude must be constant along each positive edge. -/
theorem inversePotential_eq_groundEnergy_iff (G : WeightedGraph V)
    (f : PositiveAmplitude V) (E : ℝ) (x : V → ℝ) :
    G.schrodingerForm (G.inversePotential f E) x =
      E * potentialForm (fun _ => 1) x ↔
      ∀ v u, 0 < G.w v u → x v / f.1 v = x u / f.1 u := by
  rw [← sub_eq_zero, G.inversePotential_defect, dirichlet_self_zero_iff_edges]
  refine forall_congr' fun v => forall_congr' fun u => ?_
  change (0 < G.w v u * (f.1 v * f.1 u) → _) ↔ _
  rw [mul_pos_iff_of_pos_right (mul_pos (f.2 v) (f.2 u))]

#print axioms commonGround_of_eq_density
#print axioms inversePotential_defect
#print axioms inversePotential_ground
#print axioms inversePotential_eq_groundEnergy_iff

end

end GaloisForLFunctions.HTGeometry.WeightedGraph
