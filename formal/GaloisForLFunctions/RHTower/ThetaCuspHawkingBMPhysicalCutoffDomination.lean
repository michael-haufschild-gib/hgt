import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCutoffLaplacian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalVerticalAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCorePairingLimit

/-! Uniform original cutoff-Laplacian bounds and integrability against the height-admitted response. -/
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A single scale-independent bound controls the full native physical cutoff Laplacian, including both commutators. -/
theorem physicalCoreCutoff_laplacian_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane), z ∈ ModularGroup.fd →
      ‖(physicalCoreCutoff q n).laplacian.field z‖ ≤
        (‖physicalAngularParameter q^2-1/4‖+C)*‖scalar (physicalAngularParameter q) (coordinates z)‖+
        2*C*z.im*‖coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z)‖ := by
  obtain ⟨C,hC,hb⟩ := scaledCuspCutoff_derivative_bounds
  refine ⟨C,hC,?_⟩
  intro q n z hz
  let N : ℝ := (n:ℝ)+1
  let E := scalar (physicalAngularParameter q) (coordinates z)
  let D := coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z)
  let L := physicalAngularParameter q^2-1/4
  have hchi : ‖(scaledCuspCutoff N z.im:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    change |baseCuspCutoff (z.im/N)| ≤ 1
    rw [abs_of_nonneg (baseCuspCutoff_bounds _).1]
    exact (baseCuspCutoff_bounds _).2
  have h0 : ‖(scaledCuspCutoff N z.im:ℂ)*conj (L*E)‖ ≤ ‖L‖*‖E‖ := by
    rw [norm_mul,norm_conj,norm_mul]
    exact (mul_le_mul_of_nonneg_right hchi (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (one_mul _)
  have h1 : ‖2*((z.im*deriv (scaledCuspCutoff N) z.im:ℝ):ℂ)*(z.im:ℂ)*conj D‖ ≤
      2*C*z.im*‖D‖ := by
    simp only [norm_mul,norm_conj,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos]
    gcongr
    simpa only [abs_mul,abs_of_pos z.im_pos] using (hb N z.im).1
  have h2 : ‖((z.im^2*deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ)*conj E‖ ≤ C*‖E‖ := by
    simp only [norm_mul,norm_conj,Complex.norm_real,Real.norm_eq_abs]
    have ht : |z.im^2| * |deriv (deriv (scaledCuspCutoff N)) z.im| ≤ C := by
      simpa only [abs_mul] using (hb N z.im).2
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)
  rw [physicalCoreCutoff_laplacian q n z hz]
  change ‖(scaledCuspCutoff N z.im:ℂ)*conj (L*E)+
      2*((z.im*deriv (scaledCuspCutoff N) z.im:ℝ):ℂ)*(z.im:ℂ)*conj D+
      ((z.im^2*deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ)*conj E‖ ≤ _
  calc
    _ ≤ (‖(scaledCuspCutoff N z.im:ℂ)*conj (L*E)‖+
        ‖2*((z.im*deriv (scaledCuspCutoff N) z.im:ℝ):ℂ)*(z.im:ℂ)*conj D‖)+
        ‖((z.im^2*deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ)*conj E‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖L‖*‖E‖+2*C*z.im*‖D‖+C*‖E‖ := add_le_add (add_le_add h0 h1) h2
    _ = _ := by change _ = (‖L‖+C)*‖E‖+2*C*z.im*‖D‖; ring

/-- The ordinary vertical derivative couples integrably to every actual height-admitted joint response. -/
theorem physical_vertical_pairing_integrable (q : XiZeroCopy) (h : RadialSpace) (u : SpatialSpace)
    (hu : MemLp (fun p : ℝ × UpperHalfPlane => (p.2.im:ℂ)*u p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    Integrable (fun p : ℝ × UpperHalfPlane => h p.1*
      coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates p.2)*((p.2.im:ℂ)*u p))
      (radialMeasure.prod D4BMModularCore.measure) := by
  let d : UpperHalfPlane → ℂ := fun z => coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z)
  have hd : MemLp d 2 D4BMModularCore.measure := physicalScalar_vertical_memLp q
  have hm : MemLp (fun p : ℝ × UpperHalfPlane => h p.1*d p.2) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
    apply (l2SeparatedFun_memLp h (hd.toLp d)).ae_eq
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp hd.coeFn_toLp] with p hp
    change hd.toLp d p.2 = d p.2 at hp
    change h p.1*hd.toLp d p.2 = h p.1*d p.2
    rw [hp]
  exact hm.integrable_mul hu

end
end RHTower.D4BMJointSource
