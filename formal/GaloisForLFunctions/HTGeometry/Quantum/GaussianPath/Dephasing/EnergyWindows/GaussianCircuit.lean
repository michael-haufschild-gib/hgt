import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.EnergyWindows.AbelField
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenChain
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # Finite energy resolution on physical circuit dates -/

open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.EnergyWindows
open PairedFields
noncomputable section

local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private theorem mix {n : ℕ} (a b : ℝ) (f j : Coeff n) :
    (generator (fun i => a*f i+b*j i)).val = a • (generator f).val+b • (generator j).val := by
  change pathHamiltonianLM n _=a • pathHamiltonianLM n _+b • pathHamiltonianLM n _
  rw [←map_smul,←map_smul,←map_add]
  apply congrArg (pathHamiltonianLM n)
  apply WithLp.ofLp_injective 2
  rfl

/-- The two Gaussian inputs are independent under the product prefix law.
The second field is filtered in the energy basis of the scaled first field. -/
def filteredGenerator {n : ℕ} (a b : ℝ) (η : Ioi (0:ℝ)) (x : FieldPair n) :=
  let A := a • generator (base x)
  let Z := generator (fun i => (x i).2)
  A.val+b • hamiltonianDampedGapResponse A.2.isHermitian 0 η Z.val

private theorem phase_bound {u M g t : ℝ} (hu : 1 ≤ u) (hM : 1 ≤ M)
    (hg : 0 ≤ g) (hgm : g ≤ M) (ht : |t| ≤ u^4) :
    2*|1/u^3| *g*(1+|t| *|1/u^3| *g)/(1/u) ≤ 4*M^2/u := by
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  rw [abs_of_pos (by positivity : 0 < 1/u^3)]
  calc
    _ ≤ 2*(1/u^3)*M*(1+u^4*(1/u^3)*M)/(1/u) := by gcongr
    _ = 2*M/u^2 + 2*M^2/u := by field_simp
    _ ≤ 4*M^2/u := by
      have hmu : 1 ≤ M*u := one_le_mul_of_one_le_of_one_le hM hu
      have hM₀ := zero_lt_one.trans_le hM
      field_simp [hu₀.ne']
      linarith only [hmu]

/-- For one physical draw and one auxiliary draw, all circuit budgets at
all dates through u⁴ have best projective errors within C K²/u of those
for the Abel-filtered Gaussian field of width 1/u and displacement u⁻³.
The same draws work simultaneously for every u ≥ 1. -/
theorem gaussian_circuit_energy_window :
    ∃ C : ℝ, 0<C ∧ ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop,
      ∀ u : ℝ, ∀ hu : 1 ≤ u,
      let η : Ioi (0:ℝ) := ⟨1/u,one_div_pos.mpr (zero_lt_one.trans_le hu)⟩
      let b := 1/u^3
      let a := Real.sqrt (1-b^2)
      let x := observationPair n a b ω
      let F := pathHamiltonian (pathPauliDisorderShell ω.1 n)
      ∀ t : ℝ, |t| ≤ u^4 → ∀ s : ℕ,
        let S := phaseCircuitMatrixImageAtMost (n+2) s
        |Metric.infDist (unitaryEvolution F t) S -
          Metric.infDist (unitaryEvolution (filteredGenerator a b η x) t) S| ≤ C*((n+2:ℕ):ℝ)^2/u := by
  obtain ⟨c,hc,hchain⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let m := max 1 (2*c)
  have hm : 1 ≤ m := le_max_left ..
  refine ⟨4*m^2,by positivity,?_⟩
  filter_upwards [(measurePreserving_fst (μ:=pathPauliDisorderLaw) (ν:=pathPauliDisorderLaw)).quasiMeasurePreserving.ae hchain,
    (measurePreserving_snd (μ:=pathPauliDisorderLaw) (ν:=pathPauliDisorderLaw)).quasiMeasurePreserving.ae hchain] with ω hf hj
  filter_upwards [hf,hj] with n hF hJ
  intro u hu η b a x F t ht s S
  let J := pathHamiltonian (pathPauliDisorderShell ω.2 n)
  let K : ℝ := (n+2:ℕ)
  let A := a • generator (base x)
  let Z := generator (fun i => (x i).2)
  have hu₀ : 0<u := zero_lt_one.trans_le hu
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hb' : b ≤ 1 := (div_le_one (pow_pos hu₀ 3)).mpr (one_le_pow₀ hu)
  have hb₂ : b^2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hb hb' 2
  have hab : a^2+b^2=1 := by rw [Real.sq_sqrt (sub_nonneg.mpr hb₂)]; ring
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha' : a ≤ 1 := (Real.sqrt_le_iff).mpr ⟨zero_le_one,by nlinarith only [sq_nonneg b]⟩
  have hphys : A.val+b • Z.val=F := by
    rw [show A.val+b • Z.val=(generator (rotated a b x)).val from (mix a b _ _).symm,
      recover_physical n hab ω]
    rfl
  have hZ : Z.val=b • F+(-a) • J := by
    have he (i : PathLabel n) : (x i).2=b*pathPauliDisorderShell ω.1 n i+(-a)*pathPauliDisorderShell ω.2 n i := by
      dsimp only [x,observationPair]
      ring
    change (generator (fun i => (x i).2)).val=_
    simp_rw [he]
    exact mix b (-a) _ _
  have hk : 1 ≤ K := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hbound : ‖Z.val‖ ≤ m*K := by
    rw [hZ]
    apply (norm_add_le ..).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_neg,abs_of_nonneg hb,abs_of_nonneg ha]
    calc
      _ ≤ 1*(c*K)+1*(c*K) := add_le_add (mul_le_mul hb' hF (norm_nonneg _) zero_le_one)
        (mul_le_mul ha' hJ (norm_nonneg _) zero_le_one)
      _ = (2*c)*K := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans hk)
  have h := abel_field_evolution A Z η b t
  change ‖unitaryEvolution (A.val+b • Z.val) t-unitaryEvolution (filteredGenerator a b η x) t‖ ≤ _ at h
  rw [hphys] at h
  have hd := (Metric.lipschitz_infDist_pt S).dist_le_mul (unitaryEvolution F t)
    (unitaryEvolution (filteredGenerator a b η x) t)
  simp only [one_mul,NNReal.coe_one,dist_eq_norm] at hd
  exact ((hd.trans h).trans (phase_bound hu (one_le_mul_of_one_le_of_one_le hm hk)
    (norm_nonneg Z.val) hbound ht)).trans_eq (by dsimp only [K]; ring)

#print axioms gaussian_circuit_energy_window
end
end GaloisForLFunctions.HTGeometry.Dephasing.EnergyWindows
