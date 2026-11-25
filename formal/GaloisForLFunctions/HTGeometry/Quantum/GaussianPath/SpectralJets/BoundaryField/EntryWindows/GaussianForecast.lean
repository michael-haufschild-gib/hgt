import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.ShellScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.WitnessValues
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.Extrapolation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.GaussianShells
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.OriginalWindow

/-! # A short-window law for first scalar returns with one Gaussian field unrevealed -/

open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
open PrecisionReturns SharpOccupation PrefixCouplings
noncomputable section

private theorem pencil_forecast {N : ℕ} (A Z : Register N)
    (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian) (hP : ∀ b : ℝ, b≠0 → (gapPencil A Z b).det≠0)
    {T ε : ℝ} (hT : 0<T) (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let D := Fintype.card (Fin N → Bool)^2
    let H (y : ℝ) : selfAdjoint (Register N) := ⟨A+(y:ℂ) • Z,(hH y).isSelfAdjoint⟩
    ∃ K : ℝ, ∀ r∈Ioc (0:ℝ) 1, (gaussianReal 0 1).real {y : ℝ | ∃ a> (0:ℝ),
      ε<orbitCircuitDistance (H y) 0 a ∧ |firstVisit (H y) a 0 ε-T|<r^D}≤K*r := by
  classical
  intro D H
  let x := physicalArc ε
  let b (m : ℤ) := 2*π*((m:ℝ)+x)/T
  let P (m : ℤ) := (gapPencil A Z (b m)).det
  have hx := (physicalArc_spec he.1 he.2).1
  have hn (m : ℤ) : b m≠0 := by
    apply div_ne_zero _ hT.ne'
    apply mul_ne_zero two_pi_pos.ne'
    by_cases hm : 0≤m
    · exact (add_pos_of_nonneg_of_pos (by exact_mod_cast hm : (0:ℝ)≤m) hx.1).ne'
    · have hu : (m:ℝ)≤-1 := by exact_mod_cast (show m≤-1 by omega)
      linarith only [hu,hx.2]
  have hA : A.IsHermitian := by simpa only [Complex.ofReal_zero,zero_smul,add_zero] using hH 0
  obtain ⟨B,hB,c,hc,hw⟩ := winding_witnesses A Z hA hT
    (show x∈Icc (0:ℝ) 1 from ⟨hx.1.le,hx.2.le.trans (by norm_num)⟩) (fun m => hP _ (hn m))
  choose z hz hval using hw
  obtain ⟨L,hL,C,hC,hs⟩ := shell_entry_sublevel A Z hH hT he hc
  obtain ⟨G,hG⟩ := gaussian_of_shell_covers 4
  let F := 2*(T+1)*L+5
  let J := 4*exp 1*(B+2)*C
  have hF : 0<F := by dsimp only [F]; positivity
  have hJ : 0<J := by dsimp only [J]; positivity
  refine ⟨F*J*G,fun r hr => ?_⟩
  refine (hG _ (F*J*r) (by positivity) ?_).trans_eq (by ring)
  intro n
  let S := 1+(n:ℝ)
  have hS : 1≤S := by dsimp only [S]; linarith only [Nat.cast_nonneg n]
  have hS₀ : 0<S := zero_lt_one.trans_le hS
  let W := windingBox T (L*S)
  let u := C*S^2*r
  have hu : 0<u := mul_pos (mul_pos hC (pow_pos hS₀ _)) hr.1
  let V (m : W) := {y∈Ioo (-S) S | ‖(P m.val).eval (y:ℂ)‖≤‖(P m.val).eval (z m.val:ℂ)‖/2*u^D}
  have hm (m : W) : MeasurableSet (V m) := measurableSet_Ioo.inter
    (measurableSet_le (((P m.val).continuous.comp Complex.continuous_ofReal).norm.measurable) measurable_const)
  let U := ⋃ m : W, V m
  refine ⟨shell n∩U,(shell_measurable n).inter (MeasurableSet.iUnion hm),inter_subset_left,?_,?_⟩
  · rintro y ⟨⟨a,ha,hout,ht⟩,hy⟩
    have hyS : |y|<S := by simpa only [S,add_comm] using hy.2
    obtain ⟨m,hmW,hsub⟩ := hs S hS r hr y hyS.le a ha hout ht
    refine ⟨hy,mem_iUnion.mpr ⟨⟨m,hmW⟩,abs_lt.mp hyS,hsub.trans ?_⟩⟩
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hval m) (by norm_num)) (pow_nonneg hu.le _)
  · have hsize (m : W) : volume (V m)≤ENNReal.ofReal (J*S^3*r) := by
      have h := field_sublevel_length A Z hH (b m.val) (z m.val) S u hS₀.le hu (hc.trans_le (hval m.val))
      have hv : volume (V m)≠⊤ := ((measure_mono (show V m⊆Ioo (-S) S from fun _ hy => hy.1)).trans_lt
        measure_Ioo_lt_top).ne
      rw [←ENNReal.ofReal_toReal hv]
      apply ENNReal.ofReal_le_ofReal
      apply h.trans
      have hh : |z m.val|+S+1≤(B+2)*S := by
        linarith only [hz m.val,mul_le_mul_of_nonneg_left hS hB,hS]
      calc
        _ ≤ 4*exp 1*((B+2)*S)*u := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hh (by positivity)) hu.le
        _ = J*S^3*r := by dsimp only [J,u]; ring
    have hcard : (W.card:ℝ)≤F*S := (windingBox_card hT.le (mul_nonneg hL.le hS₀.le)).trans
      (by dsimp only [F]; linarith only [hS])
    refine (measure_mono (inter_subset_right : shell n∩U⊆U)).trans
      ((measure_iUnion_fintype_le volume V).trans ((Finset.sum_le_sum fun m _ => hsize m).trans ?_))
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,←ENNReal.ofReal_natCast,
      ←ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    apply (mul_le_mul_of_nonneg_right hcard (by positivity : 0≤J*S^3*r)).trans_eq
    change F*S*(J*S^3*r)=F*J*r*S^4
    ring

/-- At any positive forecast based on the revealed couplings the entire
unrestricted terminal Gaussian field has conditional entry probability
O(h^(1/D²)). The same window tests all genuine first scalar entries at
once, even if the starting date uses the unrevealed coefficient. -/
theorem gaussian_first_entry_window :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∀ T> (0:ℝ), ∀ ε∈Ioo (0:ℝ) (sqrt 2),
      let D := 2^(k+3)
      ∃ K : ℝ, ∀ r∈Ioc (0:ℝ) 1,
        (gaussianReal 0 1).real {y : ℝ | ∃ a> (0:ℝ), let H := replacedGenerator ω k y
          ε<orbitCircuitDistance H 0 a ∧ |firstVisit H a 0 ε-T|<r^(D^2)}≤K*r := by
  filter_upwards [gaussian_gapPencil_nonzero] with ω hω
  intro k T hT ε he D
  let A := boundaryHamiltonian ω k (-ω (terminalCoordinate k))
  let Z := SpinExtension.lastPauli (k+2) 2
  have hH (y : ℝ) : (A+(y:ℂ) • Z).IsHermitian := by
    rw [←replaced_affine ω k y]
    exact (replacedGenerator ω k y).2.isHermitian
  let H (y : ℝ) : selfAdjoint (Register (k+3)) := ⟨A+(y:ℂ) • Z,(hH y).isSelfAdjoint⟩
  have heq (y : ℝ) : replacedGenerator ω k y=H y := Subtype.ext (replaced_affine ω k y)
  obtain ⟨K,hK⟩ := pencil_forecast A Z hH (hω k _) hT he
  exact ⟨K,fun r hr => by simpa only [heq,H,D,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hK r hr⟩

#print axioms gaussian_first_entry_window
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
