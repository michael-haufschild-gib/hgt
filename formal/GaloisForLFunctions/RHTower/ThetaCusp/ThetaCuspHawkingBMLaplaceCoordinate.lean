import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamWaveOperator
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalMonodromyMaster

/-! The actual original radial coordinate and physical BM differential expression. -/

open Complex
namespace RHTower.D4BMLaplaceRadial
noncomputable section

/-- The original BM coordinate, as a holomorphic radial map. -/
def radialCoordinate (r : ℂ) : ℂ := 1-r⁻¹^(2 : ℕ)

theorem radialCoordinate_original (x : Fin 4 → ℝ) :
    radialCoordinate (x 1) = D4BMMetricReconstruction.bmCoordinate x := rfl

/-- The coordinate derivatives are derived before transporting the wave operator. -/
theorem radialCoordinate_derivatives {r : ℂ} (hr : r ≠ 0) :
    HasDerivAt radialCoordinate (2/r^(3 : ℕ)) r ∧
    HasDerivAt (fun u : ℂ => 2/u^(3 : ℕ)) (-6/r^(4 : ℕ)) r := by
  constructor
  · convert! (((hasDerivAt_id r).inv hr).pow 2).const_sub 1 using 1
    dsimp
    field_simp
  · convert! ((hasDerivAt_const r (2:ℂ)).div ((hasDerivAt_id r).pow 3)
      (pow_ne_zero 3 hr)) using 1
    dsimp
    field_simp
    ring

/-- The independent-frequency original wave expression in radial jets. -/
def radialWave (w lambda r v d dd : ℂ) : ℂ :=
  w^(2 : ℕ)*v-(r^(2 : ℕ)-1)^(2 : ℕ)*dd-2*r*(r^(2 : ℕ)-1)*d+(r^(2 : ℕ)-1)/r^(2 : ℕ)*lambda*v

/-- Exact coordinate transport to the physical BM master, retaining frequency,
angular value, both coordinate derivatives and the source multiplier. -/
theorem radialWave_physical (w chi r v d dd : ℂ) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    radialWave w (1/4+chi^(2 : ℕ)) r v ((2/r^(3 : ℕ))*d) ((2/r^(3 : ℕ))^(2 : ℕ)*dd-(6/r^(4 : ℕ))*d) =
      -4*radialCoordinate r*D4BMPhysicalMaster.radialJet (Complex.I*w) chi
        (radialCoordinate r) v d dd := by
  have hz : radialCoordinate r ≠ 0 := by
    unfold radialCoordinate
    field_simp
    exact div_ne_zero hf (pow_ne_zero 2 hr)
  dsimp [radialWave,D4BMPhysicalMaster.radialJet,radialCoordinate] at hz ⊢
  field_simp [hr,hz]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The full forced wave's current is divided by the same original coordinate
factor when entering the physical radial equation. -/
theorem radial_source_normalization (r C : ℂ) (hr : r ≠ 0) :
    -2*(r^(2 : ℕ)-1)/r^(3 : ℕ)*C = -4*radialCoordinate r*(C/(2*r)) := by
  dsimp [radialCoordinate]
  field_simp
  ring

end
end RHTower.D4BMLaplaceRadial
