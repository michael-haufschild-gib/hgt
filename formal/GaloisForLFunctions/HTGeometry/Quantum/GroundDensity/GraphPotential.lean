import GaloisForLFunctions.HTGeometry.WeightedGraphSpectralGap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
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
    field_simp [(f.2 v).ne', (f.2 u).ne']
  have hdiag : G.massInner x x + potentialForm (G.inversePotential f E) x =
      E * potentialForm (fun _ => 1) x + H.massInner r r := by
    simp only [massInner, potentialForm, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    change G.mass v * (x v * x v) + G.inversePotential f E v * (x v * x v) =
      E * (x v * x v) + (G.groundConductance f).mass v *
        ((x v / f.1 v) * (x v / f.1 v))
    rw [inversePotential, groundConductance_mass]
    field_simp [(f.2 v).ne']
    ring
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

/-- A strictly positive ground amplitude determines its site potential at
fixed ground energy. Varying one coordinate reads the corresponding diagonal
coefficient, since the transformed Dirichlet energy has zero first variation. -/
theorem isGroundAt_positive_iff (G : WeightedGraph V)
    (f : {f : PositiveAmplitude V // potentialForm (fun _ => 1) f.1 = 1})
    (a : V → ℝ) (E : ℝ) :
    G.IsGroundAt a E f.1.1 ↔ a = G.inversePotential f.1 E := by
  classical
  constructor
  · intro h
    funext i
    let H := G.groundConductance f.1
    let b := G.inversePotential f.1 E
    let d : V → ℝ := fun v => if v = i then 1 else 0
    let r : V → ℝ := fun v => d v / f.1.1 v
    let x : ℝ → V → ℝ := fun t v => f.1.1 v + t * d v
    let defect : ℝ → ℝ := fun t =>
      G.schrodingerForm a (x t) - E * potentialForm (fun _ => 1) (x t)
    have htrans (t : ℝ) : (fun v => x t v / f.1.1 v) = fun v => 1 + t * r v := by
      funext v
      change (f.1.1 v + t * d v) / f.1.1 v = 1 + t * (d v / f.1.1 v)
      rw [add_div, div_self (f.1.2 v).ne', mul_div_assoc]
    have hd (t : ℝ) :
        H.dirichlet (fun v => 1 + t * r v) (fun v => 1 + t * r v) =
          (t * t) * H.dirichlet r r := by
      rw [dirichlet, dirichlet, ← mul_div_assoc, Finset.mul_sum]
      apply congrArg (· / 2)
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    have hform (t : ℝ) : defect t = (t * t) * H.dirichlet r r +
        potentialForm (fun v => a v - b v) (x t) := by
      have hb := G.inversePotential_defect f.1 E (x t)
      rw [htrans, hd] at hb
      change G.schrodingerForm b (x t) - _ = _ at hb
      change G.schrodingerForm a (x t) - _ = _
      linarith only [hb, G.schrodingerForm_sub a b (x t)]
    have hmin : IsMinOn defect Set.univ 0 := by
      have hx0 : x 0 = f.1.1 := by funext v; simp only [x, zero_mul, add_zero]
      apply isMinOn_univ_iff.mpr
      intro t
      change G.schrodingerForm a (x 0) - E * potentialForm (fun _ => 1) (x 0) ≤ _
      rw [hx0, h.2.1, f.2, mul_one, sub_self]
      exact sub_nonneg.mpr (h.2.2 (x t))
    have hc : HasDerivAt (fun t : ℝ => (t * t) * H.dirichlet r r) 0 0 := by
      simpa only [Pi.mul_apply, id_eq, zero_mul, mul_zero, add_zero] using
        (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const
          (H.dirichlet r r))
    have hp : HasDerivAt (fun t => potentialForm (fun v => a v - b v) (x t))
        (∑ v, (a v - b v) * (d v * f.1.1 v + f.1.1 v * d v)) 0 := by
      apply HasDerivAt.fun_sum
      intro v _
      have hxv : HasDerivAt (fun t => x t v) (d v) 0 := by
        simpa only [x, id_eq, one_mul] using
          (((hasDerivAt_id (0 : ℝ)).mul_const (d v)).const_add (f.1.1 v))
      simpa only [Pi.mul_apply, x, zero_mul, add_zero] using
        ((hxv.mul hxv).const_mul (a v - b v))
    have hderiv : HasDerivAt defect
        (∑ v, (a v - b v) * (d v * f.1.1 v + f.1.1 v * d v)) 0 := by
      rw [show defect = (fun t => (t * t) * H.dirichlet r r) +
        (fun t => potentialForm (fun v => a v - b v) (x t)) from funext hform]
      simpa only [zero_add] using hc.add hp
    have hz := (hmin.isLocalMin (Filter.univ_mem)).hasDerivAt_eq_zero hderiv
    rw [Finset.sum_eq_single i] at hz
    · simp only [d, if_true, one_mul, mul_one] at hz
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
        (add_pos (f.1.2 i) (f.1.2 i)).ne')
    · intro v _ hv
      simp only [d, if_neg hv, zero_mul, mul_zero, add_zero]
    · exact fun hi => (hi (Finset.mem_univ i)).elim
  · rintro rfl
    exact G.inversePotential_ground f E

/-- Equal positive ground densities determine the same potential up to an
additive shift, and the shift equals the difference in ground energies. -/
theorem eq_density_potential_shift (G : WeightedGraph V)
    (x y : {f : PositiveAmplitude V // potentialForm (fun _ => 1) f.1 = 1})
    (a b : V → ℝ) (E F : ℝ) :
    G.IsGroundAt a E x.1.1 ∧ G.IsGroundAt b F y.1.1 ∧
      (∀ v, x.1.1 v * x.1.1 v = y.1.1 v * y.1.1 v) →
      ∀ v, a v - b v = E - F := by
  rintro ⟨ha, hb, hρ⟩
  have hcommon := (G.commonGround_of_eq_density a b x.1.1 y.1.1 E F
    ⟨ha, hb, hρ⟩).2.1
  rw [(G.isGroundAt_positive_iff x a E).mp ha,
    (G.isGroundAt_positive_iff x b F).mp hcommon]
  intro v
  unfold inversePotential
  ring

#print axioms commonGround_of_eq_density
#print axioms inversePotential_defect
#print axioms inversePotential_ground
#print axioms inversePotential_eq_groundEnergy_iff
#print axioms isGroundAt_positive_iff
#print axioms eq_density_potential_shift

end

end GaloisForLFunctions.HTGeometry.WeightedGraph
