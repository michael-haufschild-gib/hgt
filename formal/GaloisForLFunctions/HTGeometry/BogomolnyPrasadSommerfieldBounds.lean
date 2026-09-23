import GaloisForLFunctions.HTGeometry.AbstractSpectralCharge
import GaloisForLFunctions.HTGeometry.ConstitutiveBalancedDefectZeroIndex
import GaloisForLFunctions.HTGeometry.ObserverFieldEquation
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue
import GaloisForLFunctions.HTGeometry.StokesEnergyTree

/-!
# Bogomolny--Prasad--Sommerfield bounds in HT geometry

Unconditional energy--charge bounds already forced by corpus structures.
-/

namespace HTGeometry.AbstractSpectralFamily

noncomputable section

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- Spectral height as BPS energy. -/
def spectralBPSEnergy (i : ι) : ℝ := (F.pt i).re

/-- Displacement charge in BPS notation. -/
def spectralBPSCharge (i : ι) : ℝ := F.charge i

/-- Admissibility gives a strict spectral BPS bound. -/
theorem abs_spectralBPSCharge_lt_energy (i : ι) :
    |F.spectralBPSCharge i| < F.spectralBPSEnergy i := by
  exact F.abs_charge_lt_re i

/-- Weak spectral BPS bound. -/
theorem abs_spectralBPSCharge_le_energy (i : ι) :
    |F.spectralBPSCharge i| ≤ F.spectralBPSEnergy i :=
  (F.abs_spectralBPSCharge_lt_energy i).le

/-- Open-strip admissibility forbids spectral BPS saturation. -/
theorem spectralBPSEnergy_ne_abs_charge (i : ι) :
    F.spectralBPSEnergy i ≠ |F.spectralBPSCharge i| :=
  ne_of_gt (F.abs_spectralBPSCharge_lt_energy i)

end


end HTGeometry.AbstractSpectralFamily

namespace HTGeometry

noncomputable section

/-- Mass-weighted scalar-shifted tangent energy. -/
def quantumTangentBPSEnergy
    (mass overlap speedSq c : ℝ) : ℝ :=
  mass * scalarShiftedQuantumTangentValue mass overlap speedSq c

/-- Gauge-invariant projective tangent charge. -/
def quantumTangentBPSCharge (mass overlap speedSq : ℝ) : ℝ :=
  projectiveQuantumTangentValue mass overlap speedSq

/-- Scalar-phase square measuring distance from the canonical connection. -/
def quantumTangentBPSDefect (mass overlap c : ℝ) : ℝ :=
  (mass * c - overlap) ^ (2 : ℕ)

/-- Exact quotient-free quantum-Fisher BPS decomposition. -/
theorem quantumTangentBPSEnergy_eq_charge_add_defect
    (mass overlap speedSq c : ℝ) :
    quantumTangentBPSEnergy mass overlap speedSq c =
      quantumTangentBPSCharge mass overlap speedSq +
        quantumTangentBPSDefect mass overlap c :=
  mass_mul_scalarShiftedQuantumTangentValue mass overlap speedSq c

/-- Projective tangent charge is the sharp lower bound over scalar-phase recenterings. -/
theorem quantumTangentBPSCharge_le_energy
    (mass overlap speedSq c : ℝ) :
    quantumTangentBPSCharge mass overlap speedSq ≤
      quantumTangentBPSEnergy mass overlap speedSq c :=
  projectiveQuantumTangentValue_le_mass_mul_shifted mass overlap speedSq c

/-- Quantum-Fisher BPS saturation fixes the canonical scalar connection. -/
theorem quantumTangentBPSSaturation_iff
    (mass overlap speedSq c : ℝ) :
    quantumTangentBPSEnergy mass overlap speedSq c =
        quantumTangentBPSCharge mass overlap speedSq ↔
      mass * c = overlap := by
  rw [quantumTangentBPSEnergy_eq_charge_add_defect]
  constructor
  · intro h
    have hzero : quantumTangentBPSDefect mass overlap c = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  · intro h
    rw [quantumTangentBPSDefect, h, sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero]

end

end HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Balanced Toeplitz defects -/

/-- Signed topological BPS charge: doubled Fredholm defect class. -/
def balancedSignedBPSCharge (n : ℕ) : ℤ := defectClass n

/-- Unsigned chiral BPS charge retaining both defect sectors. -/
def balancedUnsignedBPSCharge (n : ℕ) : ℕ := 2 * n

/-- Signed index bound.  Cancellation leaves zero charge below nonzero energy. -/
theorem abs_balancedSignedBPSCharge_le_energy (n : ℕ) :
    |balancedSignedBPSCharge n| ≤ (defectEnergy n : ℤ) := by
  rw [balancedSignedBPSCharge, defectClass_eq_zero, abs_zero]
  exact Int.natCast_nonneg _

/-- Signed-charge saturation occurs only for the zero defect. -/
theorem balancedSignedBPSSaturation_iff (n : ℕ) :
    (defectEnergy n : ℤ) = |balancedSignedBPSCharge n| ↔ n = 0 := by
  rw [balancedSignedBPSCharge, defectClass_eq_zero, abs_zero, defectEnergy_eq]
  norm_num

/-- Unsigned defect energy exactly saturates the two-chirality charge. -/
theorem defectEnergy_eq_balancedUnsignedBPSCharge (n : ℕ) :
    defectEnergy n = balancedUnsignedBPSCharge n := by
  exact defectEnergy_eq n

/-! ## Observer-field vacuum bound -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {C : Type*} [Fintype C]

/-- Observer residual energy obeys the zero-charge BPS bound. -/
theorem holonomyEnergy_bps_nonneg
    (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) (x : E) :
    0 ≤ holonomyEnergy Hol c x := by
  exact sq_nonneg _

/-- Observer BPS saturation is exactly affine holonomy integrability. -/
theorem holonomyEnergy_bpsSaturation_iff
    (Hol : C → (E ≃ₗᵢ[𝕜] E)) (c : C → E) (x : E) :
    holonomyEnergy Hol c x = 0 ↔ ∀ e : C, x - Hol e x = c e := by
  exact (exact_iff_energy_eq_zero Hol c x).symm

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.IrregularStokes.RootedCutContact

variable {n m : ℕ}

/-- Total positive length of cuts separating two leaves. -/
def stokesBPSCharge (c : RootedCutContact n m) (i j : Fin n) : ℝ :=
  ∑ e, c.length e * |c.side e i - c.side e j|

/-- Stokes energy exactly saturates its separating-cut charge. -/
theorem energy_eq_stokesBPSCharge (c : RootedCutContact n m) (i j : Fin n) :
    c.energy i j = c.stokesBPSCharge i j := by
  exact c.energy_eq_absDist i j

/-- Stokes BPS saturation at zero charge detects coincident leaves. -/
theorem stokesBPSCharge_eq_zero_iff (c : RootedCutContact n m) (i j : Fin n) :
    c.stokesBPSCharge i j = 0 ↔ i = j := by
  rw [← c.energy_eq_stokesBPSCharge i j]
  exact c.energy_eq_zero_iff i j

end GaloisForLFunctions.IrregularStokes.RootedCutContact
