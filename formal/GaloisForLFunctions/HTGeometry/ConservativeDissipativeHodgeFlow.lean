import GaloisForLFunctions.HTGeometry.ConservativeDissipativeHodge
import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Attractor

set_option autoImplicit false

/-!
# Global conservative–dissipative Hodge dynamics

The energy construction from Schaffer–Exl (arXiv:2609.04530) supplies the
cancellation and coercivity required by the existing Hodge evolution theory.
Arbitrary raw coefficients produce actual global nonlinear trajectories,
exponential unforced decay, and forced compact invariant attracting sets.
-/

open scoped InnerProductSpace NNReal
open Set
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
open HodgeEdgeCochain
variable {ι : Type*} [Fintype ι]
  (W : Submodule ℝ (EuclideanSpace ℝ ι))
  (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)

/-- Unit-regularized observation damping on the nonlinear phase space. -/
def hodgeDamping (L : W →L[ℝ] W) : W →L[ℝ] W :=
  damping L + ContinuousLinearMap.id ℝ W

/-- The regularization has coercivity one, independently of observation nullspaces. -/
theorem hodgeDamping_power (L : W →L[ℝ] W) (x : W) :
    ⟪hodgeDamping W L x, x⟫_ℝ = ‖L x‖ ^ 2 + ‖x‖ ^ 2 := by
  rw [real_inner_comm]
  have hd := damping_power L x
  simp only [RCLike.re_to_real] at hd
  simp [hodgeDamping, inner_add_right, hd]

theorem hodgeDamping_coercive (L : W →L[ℝ] W) (x : W) :
    1 * ‖x‖ ^ 2 ≤ ⟪hodgeDamping W L x, x⟫_ℝ := by
  rw [hodgeDamping_power]
  nlinarith [sq_nonneg ‖L x‖]

/-- A concrete admissible nonlinear system with arbitrary operator, forcing, and viscosity parameters. -/
def hodgeSystem (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) : AdmissibleSystem W where
  A := hodgeDamping W L
  B := hodgeInteraction W A
  nu := 1 + nu ^ 2
  eta := 1 + eta ^ 2
  f := f
  g := g
  cancelling := hodgeInteraction_cancelling W A
  nonneg x := by rw [hodgeDamping_power]; exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  nu_pos := by nlinarith [sq_nonneg nu]
  eta_pos := by nlinarith [sq_nonneg eta]

/-- Global solutions now follow with every admissibility premise discharged. -/
theorem hodgeSystem_global_solution (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) (x : W × W) :
    ∃ α : ℝ → W × W, α 0 = x ∧
      IsSolutionOn (hodgeDamping W L) (hodgeInteraction W A) (1 + nu ^ 2) (1 + eta ^ 2)
        f g (fun t => (α t).1) (fun t => (α t).2) (Ici 0) :=
  (hodgeSystem W A L f g nu eta).exists_pair_isSolutionOn_Ici x

/-- The actual global semiflow, obtained from the corpus existence theorem. -/
def hodgeFlow (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) (t : ℝ≥0) (x : W × W) : W × W :=
  (hodgeSystem W A L f g nu eta).flow t x

theorem hodgeFlow_zero (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) (x : W × W) :
    hodgeFlow W A L f g nu eta 0 x = x :=
  (hodgeSystem W A L f g nu eta).flow_zero x

theorem hodgeFlow_add (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) (s t : ℝ≥0) (x : W × W) :
    hodgeFlow W A L f g nu eta (s + t) x =
      hodgeFlow W A L f g nu eta s (hodgeFlow W A L f g nu eta t x) :=
  (hodgeSystem W A L f g nu eta).flow_add s t x

theorem hodgeFlow_continuous (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) (t : ℝ≥0) :
    Continuous (hodgeFlow W A L f g nu eta t) :=
  (hodgeSystem W A L f g nu eta).continuous_flow' t

/-- The actual unforced nonlinear orbit decays exponentially at its constructed coercive rate. -/
theorem hodgeFlow_energy_decay (L : W →L[ℝ] W) (nu eta : ℝ) (t : ℝ≥0) (x : W × W) :
    ‖(hodgeFlow W A L 0 0 nu eta t x).1‖ ^ 2 +
        ‖(hodgeFlow W A L 0 0 nu eta t x).2‖ ^ 2 ≤
      (‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) *
        Real.exp (-(2 * decayRate (1 + nu ^ 2) (1 + eta ^ 2) 1) * (t : ℝ)) := by
  let S := hodgeSystem W A L 0 0 nu eta
  have hs : IsSolutionOn S.A S.B S.nu S.eta 0 0
      (fun s => (S.orbit x s).1) (fun s => (S.orbit x s).2) (Icc 0 (t : ℝ)) :=
    fun s h => S.orbit_isSolution x s h.1
  have hb := energy_le_unforced_of_coercive S.cancelling (hodgeDamping_coercive W L)
    S.nu_pos S.eta_pos (show (0 : ℝ) < 1 from zero_lt_one) hs t ⟨t.coe_nonneg, le_rfl⟩
  simpa only [energy, AdmissibleSystem.orbit_zero, hodgeFlow, AdmissibleSystem.flow,
    S, hodgeSystem] using hb

/-- A chosen absorbing radius strictly exceeds the forcing-to-damping ratio. -/
def hodgeAbsorbingRadius (f g : W) (nu eta : ℝ) : ℝ :=
  1 + Real.sqrt (‖f‖ ^ 2 + ‖g‖ ^ 2) / decayRate (1 + nu ^ 2) (1 + eta ^ 2) 1

/-- Canonical compact global attractor of the constructed forced dynamics. -/
def hodgeAttractor (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) : Set (W × W) :=
  (hodgeSystem W A L f g nu eta).attractor (hodgeAbsorbingRadius W f g nu eta)

theorem hodgeAttractor_compact (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) :
    IsCompact (hodgeAttractor W A L f g nu eta) := by
  apply (hodgeSystem W A L f g nu eta).isCompact_attractor
    (hodgeDamping_coercive W L) zero_lt_one
  dsimp [hodgeSystem, hodgeAbsorbingRadius]
  linarith

theorem hodgeAttractor_nonempty (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) :
    (hodgeAttractor W A L f g nu eta).Nonempty := by
  apply (hodgeSystem W A L f g nu eta).attractor_nonempty
    (hodgeDamping_coercive W L) zero_lt_one
  dsimp [hodgeSystem, hodgeAbsorbingRadius]
  linarith

theorem hodgeAttractor_invariant (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ) :
    IsInvariant (hodgeFlow W A L f g nu eta) (hodgeAttractor W A L f g nu eta) :=
  (hodgeSystem W A L f g nu eta).isInvariant_attractor _

/-- Every bounded energy ball enters the absorbing ball after a uniform finite time. -/
theorem hodgeFlow_absorbs (L : W →L[ℝ] W) (f g : W) (nu eta rho : ℝ) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      MapsTo (fun x => (hodgeSystem W A L f g nu eta).orbit x t)
        {x : W × W | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ rho ^ 2}
        (AdmissibleSystem.energyBall W (hodgeAbsorbingRadius W f g nu eta)) := by
  apply (hodgeSystem W A L f g nu eta).exists_absorbing
    (hodgeDamping_coercive W L) zero_lt_one _ (sq_nonneg rho)
  dsimp [hodgeSystem, hodgeAbsorbingRadius]
  linarith

/-- Exact accumulated dissipation along the actual forced nonlinear orbit. -/
theorem hodgeFlow_energy_balance (L : W →L[ℝ] W) (f g : W) (nu eta : ℝ)
    (T : ℝ≥0) (x : W × W) :
    2 * ∫ t in (0 : ℝ)..(T : ℝ),
      ((1 + nu ^ 2) * (‖L ((hodgeSystem W A L f g nu eta).orbit x t).1‖ ^ 2 +
          ‖((hodgeSystem W A L f g nu eta).orbit x t).1‖ ^ 2) +
        (1 + eta ^ 2) * (‖L ((hodgeSystem W A L f g nu eta).orbit x t).2‖ ^ 2 +
          ‖((hodgeSystem W A L f g nu eta).orbit x t).2‖ ^ 2)) =
      (‖x.1‖ ^ 2 + ‖x.2‖ ^ 2) -
        (‖(hodgeFlow W A L f g nu eta T x).1‖ ^ 2 +
          ‖(hodgeFlow W A L f g nu eta T x).2‖ ^ 2) +
      2 * ∫ t in (0 : ℝ)..(T : ℝ),
        (⟪f, ((hodgeSystem W A L f g nu eta).orbit x t).1⟫_ℝ +
          ⟪g, ((hodgeSystem W A L f g nu eta).orbit x t).2⟫_ℝ) := by
  let S := hodgeSystem W A L f g nu eta
  have hs : IsSolutionOn S.A S.B S.nu S.eta S.f S.g
      (fun t => (S.orbit x t).1) (fun t => (S.orbit x t).2) (uIcc 0 (T : ℝ)) := by
    rw [uIcc_of_le T.coe_nonneg]
    exact fun t ht => S.orbit_isSolution x t ht.1
  have hb := integral_dissipation_identity S.cancelling hs
  simpa only [energy, dissipation, forcingPower, AdmissibleSystem.orbit_zero,
    hodgeFlow, AdmissibleSystem.flow, S, hodgeSystem, hodgeDamping_power] using hb

end
end GaloisForLFunctions.HTGeometry.SchafferExl
