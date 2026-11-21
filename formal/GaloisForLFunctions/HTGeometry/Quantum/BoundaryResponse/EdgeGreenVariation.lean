import GaloisForLFunctions.HTGeometry.LinearAlgebra.PositiveRankOneUpdate
import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.LayeredGreen

/-!
# Green response to an added conductance

An edge with increased conductance changes the grounded inverse through
the voltage induced by a unit dipole across that edge. A parallel edge on
the boundary leaves the harmonic midpoint extension unchanged.
-/

open Matrix
open scoped Matrix NNReal

namespace GaloisForLFunctions.HTGeometry.WeightedGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unit current injected at `a` and withdrawn at `b`. -/
def edgeDipole (a b : V) : V → ℝ := Pi.single a 1 - Pi.single b 1

theorem edgeDipole_dotProduct (a b : V) (x : V → ℝ) :
    edgeDipole a b ⬝ᵥ x = x a - x b := by
  simp only [edgeDipole, sub_dotProduct, single_dotProduct, one_mul]

private def extraWeight (a b : V) (t : ℝ≥0) (v u : V) : ℝ :=
  if a = b then 0 else
    (if v = a ∧ u = b then (t : ℝ) else 0) + (if v = b ∧ u = a then (t : ℝ) else 0)

/-- Add a parallel edge of the given conductance between two vertices. -/
def addConductance (G : WeightedGraph V) (a b : V) (t : ℝ≥0) : WeightedGraph V where
  w v u := G.w v u + extraWeight a b t v u
  w_symm v u := by
    rw [G.w_symm v u]
    congr 1
    by_cases hab : a = b
    · simp only [extraWeight, if_pos hab]
    · have h₁ : (v = a ∧ u = b) = (u = b ∧ v = a) := propext and_comm
      have h₂ : (v = b ∧ u = a) = (u = a ∧ v = b) := propext and_comm
      simp only [extraWeight, if_neg hab, h₁, h₂]
      exact add_comm _ _
  w_nonneg v u := by
    apply add_nonneg (G.w_nonneg v u)
    unfold extraWeight
    split_ifs <;> positivity
  w_diag v := by
    rw [G.w_diag, zero_add]
    by_cases hab : a = b
    · simp only [extraWeight, if_pos hab]
    · have ha : ¬ (v = a ∧ v = b) := fun h => hab (h.1.symm.trans h.2)
      have hb : ¬ (v = b ∧ v = a) := fun h => ha ⟨h.2, h.1⟩
      simp only [extraWeight, if_neg hab, if_neg ha, if_neg hb, add_zero]

/-- Extra current is the edge voltage drop times its added conductance,
injected with opposite signs at the two endpoints. -/
theorem networkFlux_addConductance (G : WeightedGraph V) (a b : V) (t : ℝ≥0)
    (x : V → ℝ) (v : V) :
    (G.addConductance a b t).networkFlux x v =
      G.networkFlux x v + (t : ℝ) * edgeDipole a b v * (x a - x b) := by
  simp only [networkFlux, addConductance, add_mul, Finset.sum_add_distrib]
  congr 1
  by_cases hab : a = b
  · subst b
    simp only [extraWeight, if_true, zero_mul, Finset.sum_const_zero, sub_self, mul_zero]
  · by_cases ha : v = a
    · subst v
      simp only [extraWeight, hab, true_and, false_and, if_false, add_zero,
        ite_mul, zero_mul, Fintype.sum_ite_eq', edgeDipole, Pi.sub_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne hab, sub_zero, mul_one]
    · by_cases hb : v = b
      · subst v
        simp only [extraWeight, hab, ha, false_and, true_and, if_false,
          zero_add, ite_mul, zero_mul, Fintype.sum_ite_eq', edgeDipole, Pi.sub_apply,
          Pi.single_eq_same, Pi.single_eq_of_ne ha, zero_sub]
        ring
      · simp only [extraWeight, hab, ha, hb, false_and, if_false,
          add_zero, zero_mul, Finset.sum_const_zero, edgeDipole, Pi.sub_apply,
          Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb, sub_self, mul_zero]

theorem networkLaplacian_addConductance (G : WeightedGraph V) (a b : V) (t : ℝ≥0) :
    (G.addConductance a b t).networkLaplacian =
      G.networkLaplacian + (t : ℝ) • vecMulVec (edgeDipole a b) (edgeDipole a b) := by
  apply Matrix.mulVec_injective
  funext x v
  rw [networkLaplacian_mulVec, networkFlux_addConductance,
    Matrix.add_mulVec, Pi.add_apply, networkLaplacian_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, edgeDipole_dotProduct]
  change _ + (t : ℝ) * edgeDipole a b v * (x a - x b) =
    _ + (t : ℝ) * (edgeDipole a b v * (x a - x b))
  ring

/-- Attach the same positive conductance to ground at every vertex. -/
def groundedLaplacian (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ)) : Matrix V V ℝ :=
  G.networkLaplacian + (g : ℝ) • 1

theorem posDef_groundedLaplacian (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ)) :
    (G.groundedLaplacian g).PosDef := by
  have hL : G.networkLaplacian.PosSemidef :=
    .of_dotProduct_mulVec_nonneg G.isHermitian_networkLaplacian fun x => by
      simpa only [star_trivial, dotProduct, G.networkLaplacian_mulVec,
        ← G.dirichlet_self_eq_sum_mul_networkFlux x] using G.dirichlet_self_nonneg x
  have hI : ((g : ℝ) • (1 : Matrix V V ℝ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal fun _ => g.2
  rw [groundedLaplacian, add_comm]
  exact hI.add_posSemidef hL

/-- Grounded voltage response matrix. -/
def groundedGreen (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ)) : Matrix V V ℝ :=
  (G.groundedLaplacian g)⁻¹

/-- Grounded voltage profile produced by the edge dipole. -/
def dipoleVoltage (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ)) (a b : V) : V → ℝ :=
  G.groundedGreen g *ᵥ edgeDipole a b

/-- Voltage drop across the dipole endpoints under unit current. -/
def groundedResistance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ)) (a b : V) : ℝ :=
  edgeDipole a b ⬝ᵥ G.dipoleVoltage g a b

theorem groundedResistance_nonneg (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ)) (a b : V) :
    0 ≤ G.groundedResistance g a b := by
  simpa only [groundedResistance, dipoleVoltage, groundedGreen, star_trivial] using
    (G.posDef_groundedLaplacian g).inv.posSemidef.dotProduct_mulVec_nonneg (edgeDipole a b)

private theorem groundedLaplacian_addConductance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) :
    (G.addConductance a b t).groundedLaplacian g =
      G.groundedLaplacian g + (t : ℝ) • vecMulVec (edgeDipole a b) (edgeDipole a b) := by
  rw [groundedLaplacian, networkLaplacian_addConductance, groundedLaplacian, add_right_comm]

/-- The change in every grounded Green entry factors through the two
dipole voltages and the grounded resistance. -/
theorem groundedGreen_addConductance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) :
    (G.addConductance a b t).groundedGreen g =
      G.groundedGreen g - ((t : ℝ) / (1 + (t : ℝ) * G.groundedResistance g a b)) •
        vecMulVec (G.dipoleVoltage g a b) (G.dipoleVoltage g a b) := by
  rw [groundedGreen, groundedLaplacian_addConductance]
  exact inv_add_smul_vecMulVec (G.posDef_groundedLaplacian g) (edgeDipole a b) t
    (rankOneUpdate_denominator_pos (G.posDef_groundedLaplacian g) (edgeDipole a b) t).ne'

/-- The derivative for a physical conductance increase, including the
right derivative at zero. -/
theorem hasDerivWithinAt_groundedGreen_addConductance_apply (G : WeightedGraph V)
    (g : Set.Ioi (0 : ℝ)) (a b : V) (t : ℝ≥0) (i j : V) :
    HasDerivWithinAt (fun s : ℝ => (G.addConductance a b s.toNNReal).groundedGreen g i j)
      (-(G.dipoleVoltage g a b i * G.dipoleVoltage g a b j) /
        (1 + (t : ℝ) * G.groundedResistance g a b) ^ 2)
      (Set.Ici 0) (t : ℝ) := by
  let hA := G.posDef_groundedLaplacian g
  let d := edgeDipole a b
  have h := hasDerivAt_inv_add_smul_vecMulVec_apply hA d t
    (rankOneUpdate_denominator_pos hA d t).ne' i j
  refine h.hasDerivWithinAt.congr_of_mem (fun s hs => ?_) t.coe_nonneg
  rw [groundedGreen, groundedLaplacian_addConductance, Real.coe_toNNReal s hs]

private theorem dotProduct_dipoleVoltage (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (x : V → ℝ) :
    x ⬝ᵥ G.dipoleVoltage g a b =
      (G.groundedGreen g *ᵥ x) a - (G.groundedGreen g *ᵥ x) b := by
  have hsymm : (G.groundedGreen g)ᵀ = G.groundedGreen g := by
    ext i j
    simpa only [Matrix.transpose_apply, groundedGreen, star_trivial] using
      (G.posDef_groundedLaplacian g).isHermitian.inv.apply i j
  rw [← edgeDipole_dotProduct a b, dipoleVoltage, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]

/-- The inverse energy drops by the squared voltage across the perturbed
edge, times the exact finite-update coefficient. -/
theorem groundedGreen_energy_addConductance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) (x : V → ℝ) :
    x ⬝ᵥ ((G.addConductance a b t).groundedGreen g *ᵥ x) =
      x ⬝ᵥ (G.groundedGreen g *ᵥ x) - ((t : ℝ) / (1 + (t : ℝ) * G.groundedResistance g a b)) *
        ((G.groundedGreen g *ᵥ x) a - (G.groundedGreen g *ᵥ x) b) ^ 2 := by
  rw [← G.dotProduct_dipoleVoltage g a b x, groundedGreen, groundedLaplacian_addConductance]
  exact dotProduct_inv_add_smul_vecMulVec (G.posDef_groundedLaplacian g) (edgeDipole a b) x t

/-- A nonzero conductance increase leaves the inverse energy unchanged
exactly when the original source gives equal endpoint voltages. -/
theorem groundedGreen_energy_addConductance_eq_iff (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) (x : V → ℝ) :
    x ⬝ᵥ ((G.addConductance a b t).groundedGreen g *ᵥ x) = x ⬝ᵥ (G.groundedGreen g *ᵥ x) ↔
      t = 0 ∨ (G.groundedGreen g *ᵥ x) a = (G.groundedGreen g *ᵥ x) b := by
  rw [groundedGreen_energy_addConductance]
  have hden : 1 + (t : ℝ) * G.groundedResistance g a b ≠ 0 :=
    (add_pos_of_pos_of_nonneg one_pos (mul_nonneg t.coe_nonneg (G.groundedResistance_nonneg g a b))).ne'
  constructor
  · intro h
    have hz : ((t : ℝ) / (1 + (t : ℝ) * G.groundedResistance g a b)) *
        ((G.groundedGreen g *ᵥ x) a - (G.groundedGreen g *ᵥ x) b) ^ 2 = 0 := by
      linarith only [h]
    rcases mul_eq_zero.mp hz with hc | hv
    · exact Or.inl (NNReal.coe_eq_zero.mp ((div_eq_zero_iff.mp hc).resolve_right hden))
    · rw [pow_two] at hv
      exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp hv).elim id id))
  · rintro (rfl | hx)
    · simp
    · simp [hx]

/-- Adding a parallel conductance gives the exact resistance division law. -/
theorem groundedResistance_addConductance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) :
    (G.addConductance a b t).groundedResistance g a b =
      G.groundedResistance g a b / (1 + (t : ℝ) * G.groundedResistance g a b) := by
  let q := G.groundedResistance g a b
  have hden : 1 + (t : ℝ) * q ≠ 0 :=
    (add_pos_of_pos_of_nonneg one_pos (mul_nonneg t.coe_nonneg (G.groundedResistance_nonneg g a b))).ne'
  change edgeDipole a b ⬝ᵥ (((G.addConductance a b t).groundedLaplacian g)⁻¹ *ᵥ edgeDipole a b) = _
  rw [groundedLaplacian_addConductance,
    dotProduct_inv_add_smul_vecMulVec (G.posDef_groundedLaplacian g)]
  change q - ((t : ℝ) / (1 + (t : ℝ) * q)) * q ^ 2 = q / (1 + (t : ℝ) * q)
  apply (eq_div_iff hden).mpr
  rw [sub_mul, mul_right_comm ((t : ℝ) / (1 + (t : ℝ) * q)) (q ^ 2),
    div_mul_cancel₀ _ hden]
  ring

/-- At distinct endpoints the reciprocal resistance increases by exactly
the added conductance. -/
theorem inv_groundedResistance_addConductance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) :
    ((G.addConductance a b t).groundedResistance g a b)⁻¹ =
      (G.groundedResistance g a b)⁻¹ + if a = b then 0 else (t : ℝ) := by
  rw [groundedResistance_addConductance]
  by_cases hab : a = b
  · subst b
    simp [groundedResistance, edgeDipole]
  · have hd : edgeDipole a b ≠ 0 := by
      intro h
      have ha := congrFun h a
      simp [edgeDipole, Pi.single_eq_of_ne hab] at ha
    have hq : 0 < G.groundedResistance g a b := by
      simpa only [groundedResistance, dipoleVoltage, groundedGreen, star_trivial] using
        (G.posDef_groundedLaplacian g).inv.dotProduct_mulVec_pos hd
    rw [if_neg hab, inv_div]
    field_simp [hq.ne']

/-- Adding a parallel edge entirely on the boundary preserves every
interior current, for arbitrary potentials. -/
theorem seriesNetwork_addBoundaryEdge_interior_flux (G : WeightedGraph V) (B : SimpleGraph V)
    (a b : V) (t : ℝ≥0) (x : V ⊕ SeriesInterior V → ℝ) (p : SeriesInterior V) :
    ((G.seriesNetwork B).addConductance (.inl a) (.inl b) t).networkFlux x (.inr p) =
      (G.seriesNetwork B).networkFlux x (.inr p) := by
  simp only [networkFlux_addConductance, edgeDipole, Pi.sub_apply,
    Pi.single_eq_of_ne Sum.inr_ne_inl, sub_self, mul_zero, zero_mul, add_zero]

/-- The new response of the full series network is the effective network
with the same parallel boundary edge added. -/
theorem seriesNetwork_addBoundaryEdge_response (G : WeightedGraph V) (B : SimpleGraph V)
    (a b : V) (t : ℝ≥0) (x : V → ℝ) (v : V) :
    ((G.seriesNetwork B).addConductance (.inl a) (.inl b) t).networkFlux
      (seriesMidpointExtension x) (.inl v) = (G.addConductance a b t).networkFlux x v := by
  rw [networkFlux_addConductance, G.seriesNetwork_boundary_flux, networkFlux_addConductance]
  simp only [seriesMidpointExtension, edgeDipole, Pi.sub_apply, Pi.single_apply, Sum.inl.injEq]

/-- Green voltage at a boundary or interior vertex of the series network
under grounded forcing at a boundary vertex. -/
def groundedMidpointGreen (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (z : V ⊕ SeriesInterior V) (j : V) : ℝ :=
  seriesMidpointExtension (fun i => G.groundedGreen g i j) z

/-- The finite change at an interior readout factors through the harmonic
extension of the dipole voltage. -/
theorem groundedMidpointGreen_addConductance (G : WeightedGraph V) (g : Set.Ioi (0 : ℝ))
    (a b : V) (t : ℝ≥0) (z : V ⊕ SeriesInterior V) (j : V) :
    (G.addConductance a b t).groundedMidpointGreen g z j =
      G.groundedMidpointGreen g z j -
        ((t : ℝ) / (1 + (t : ℝ) * G.groundedResistance g a b)) *
          (seriesMidpointExtension (G.dipoleVoltage g a b) z * G.dipoleVoltage g a b j) := by
  cases z <;> simp only [groundedMidpointGreen, seriesMidpointExtension, groundedGreen_addConductance,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

#print axioms networkFlux_addConductance
#print axioms networkLaplacian_addConductance
#print axioms posDef_groundedLaplacian
#print axioms groundedGreen_addConductance
#print axioms hasDerivWithinAt_groundedGreen_addConductance_apply
#print axioms groundedGreen_energy_addConductance_eq_iff
#print axioms inv_groundedResistance_addConductance
#print axioms seriesNetwork_addBoundaryEdge_response
#print axioms groundedMidpointGreen_addConductance

end

end GaloisForLFunctions.HTGeometry.WeightedGraph
