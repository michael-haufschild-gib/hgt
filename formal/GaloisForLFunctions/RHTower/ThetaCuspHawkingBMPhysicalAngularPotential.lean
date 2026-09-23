import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarSourceIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticAngularCorrection

/-!
# Source-produced angular potentials for the physical Einstein coefficient

The original scalar/vector metric jet and the existing zero tensor remainder
identify both trace-free angular components of its actual quadratic coefficient.
All scalar/scalar, scalar/vector and vector/vector amplitude terms survive as
Hessians of the literal square and its constructed shift-two inverse. Polarization
allows independent amplitudes in the two source slots at the same Xi occurrence.

The explicit angular correction leaves a determined inverse-response Hessian.
It is not identified here with the complete causal ++ or +- correction. Neither
boundary vanishing nor fixed-Hawking-clock extinction is assumed or proved.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMPhysicalAngularPotential
open D4BMHorizon D4BMAngularTwoTensor D4BMAngularTwo
open D4BMModularCore D4BMScalarSourceIdentification D4BMQuadraticAngularSource
noncomputable section
set_option autoImplicit false

private theorem source_syy (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    coordDeriv 1 (coordDeriv 1 (source q)) z =
      (physicalRate q branch+1)*(physicalRate q branch+2)*source q z/(z 1:ℂ)^(2 : ℕ)-
        coordDeriv 0 (coordDeriv 0 (source q)) z := by
  have he := scalar_physical_equation q branch z hz
  change scalarLaplacian (source q) z =
    (physicalRate q branch+1)*(physicalRate q branch+2)*source q z at he
  rw [scalarLaplacian_eq _ z hz] at he
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  linear_combination he

private theorem source_sxyy (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    coordDeriv 0 (coordDeriv 1 (coordDeriv 1 (source q))) z =
      (physicalRate q branch+1)*(physicalRate q branch+2)*coordDeriv 0 (source q) z/(z 1:ℂ)^(2 : ℕ)-
        coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z := by
  have hs : ContDiffAt ℝ 3 (source q) z :=
    D4BMLiteralCusp.scalar_contDiffAt (D4BMGlobalAngularResponse.center q) 3 z hz
  have he : scalarLaplacian (source q) =ᶠ[𝓝 z]
      (fun w => (physicalRate q branch+1)*(physicalRate q branch+2)*source q w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact scalar_physical_equation q branch w hw
  have hd := congrArg (fun L => L (Pi.single 0 1)) (he.fderiv_eq (𝕜 := ℝ))
  change coordDeriv 0 (scalarLaplacian (source q)) z = _ at hd
  rw [scalarLaplacian_partial _ z hz hs 0] at hd
  rw [((hs.differentiableAt (by norm_num)).hasFDerivAt.const_mul
    ((physicalRate q branch+1)*(physicalRate q branch+2))).fderiv] at hd
  change (0:ℂ)*_+(z 1:ℂ)^(2 : ℕ)*(_+_) =
    (physicalRate q branch+1)*(physicalRate q branch+2)*coordDeriv 0 (source q) z at hd
  have hy : (z 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  field_simp
  linear_combination hd

private theorem ofField_congr_germ {f g : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (h : f =ᶠ[nhds x] g) : ofField f x = ofField g x := by
  have hD : fderiv ℝ f =ᶠ[nhds x] fderiv ℝ g := h.fderiv
  have hd (k : Fin 4) : coordDeriv k f =ᶠ[nhds x] coordDeriv k g := by
    filter_upwards [hD] with y hy
    exact congrArg (fun L => L (Pi.single k 1)) hy
  ext i j
  · exact h.self_of_nhds
  · change fderiv ℝ f x (Pi.single i 1) = fderiv ℝ g x (Pi.single i 1)
    rw [h.fderiv_eq]
  · change fderiv ℝ (coordDeriv j f) x (Pi.single i 1) =
      fderiv ℝ (coordDeriv j g) x (Pi.single i 1)
    rw [(hd j).fderiv_eq]

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k,
    fun k l i j => (J i j).second k l⟩

/-- The original physical vector perturbation has its reconstructed field's full jet. -/
theorem physical_vector_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    D4BMMetricReconstruction.ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch 0 a) p.val =
      D4BMMetricReconstruction.ofMetricField (D4BMVectorLinearEquation.field (physicalRate q branch) a
        (D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q))) p.val := by
  change assemble _ = assemble _
  congr 1
  funext i j
  apply ofField_congr_germ
  have hO : IsOpen {x : Fin 4 → ℝ | 1 < x 1 ∧ 0 < x 3} :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (continuous_apply 3))
  filter_upwards [hO.mem_nhds p.property] with x hx
  exact congrArg (fun M => M i j) (D4BMVectorLinearEquation.reconstruction_eq
    (physicalRate q branch) a (D4BMLiteralCusp.scalarQ (D4BMGlobalAngularResponse.center q))
    (source q) _ ⟨x,hx⟩)

private theorem partial_neg (i : Fin 2) (F : Field) :
    coordDeriv i (fun z => -F z) = fun z => -coordDeriv i F z := by
  funext z
  simp [coordDeriv]

/-- The complete coexact jet is derived from the literal scalar equation, including its third jets. -/
theorem physical_coexact_jet (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.angularPoint p.val
    D4BMMetricReconstruction.ofMetricField (D4BMLiteralCusp.physicalPerturbation q branch 0 a) p.val =
      coexactJet (physicalRate q branch) (p.val 1) (p.val 3)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a p.val)
        (source q z) (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
        (coordDeriv 0 (coordDeriv 0 (source q)) z) (coordDeriv 0 (coordDeriv 1 (source q)) z)
        (coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z)
        (coordDeriv 0 (coordDeriv 0 (coordDeriv 1 (source q))) z) := by
  let z := D4BMMetricReconstruction.angularPoint p.val
  have hv (i : Fin 2) : D4BMHorizon.roughLaplacian
      (D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q)) i z =
      ((physicalRate q branch+1)*(physicalRate q branch+2)-1)*
        D4BMLiteralCusp.vector (D4BMGlobalAngularResponse.center q) i z := by
    rw [D4BMLiteralCusp.vector_equation _ z p.property.2 i]
    have he := eigenvalue_physicalRate q branch
    dsimp [eigenvalue] at he
    unfold d4HyperbolicHodgePairedVectorEigenvalue
    rw [← he]
    ring
  rw [physical_vector_jet,D4BMVectorLinearEquation.field_jet _ _ _ p
    (D4BMLiteralCusp.vector_contDiffAt _ 2 _ p.property.2)
    (D4BMLiteralCusp.vector_divergence _) hv]
  simp only [D4BMLiteralCusp.vector,coexact,Matrix.cons_val_zero,Matrix.cons_val_one,
    coexactJet]
  have hyy := source_syy q branch z p.property.2
  have hxyy := source_sxyy q branch z p.property.2
  dsimp only [source,z] at hyy hxyy
  simp only [source]
  rw [hyy,hxyy,partial_neg]
  rfl

/-- The full original physical scalar/vector jet, with independent amplitudes. -/
theorem physical_combined_space (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.angularPoint p.val
    ComplexCoordinateMetricTwoJet.toSpace (D4BMMetricReconstruction.ofMetricField
      (D4BMLiteralCusp.physicalPerturbation q branch aS aV) p.val) =
      ComplexCoordinateMetricTwoJet.toSpace (combinedJet (physicalRate q branch) (p.val 1) (p.val 3)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) 1 p.val) aS aV
        (source q z) (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
        (coordDeriv 0 (coordDeriv 0 (source q)) z) (coordDeriv 0 (coordDeriv 1 (source q)) z)
        (coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z)
        (coordDeriv 0 (coordDeriv 0 (coordDeriv 1 (source q))) z)) := by
  have hsplit : D4BMLiteralCusp.physicalPerturbation q branch aS aV = fun x =>
      D4BMLiteralCusp.physicalPerturbation q branch aS 0 x+
        D4BMLiteralCusp.physicalPerturbation q branch 0 aV x :=
    D4BMFullLinearEquation.literal_perturbation_split _ _ _ _
  have hS : ∀ i j, ContDiffAt ℝ 2
      (fun x => D4BMLiteralCusp.physicalPerturbation q branch aS 0 x i j) p.val :=
    D4BMFullLinearEquation.literal_contDiffAt p _ _ aS 0
  have hV : ∀ i j, ContDiffAt ℝ 2
      (fun x => D4BMLiteralCusp.physicalPerturbation q branch 0 aV x i j) p.val :=
    D4BMFullLinearEquation.literal_contDiffAt p _ _ 0 aV
  have hs : ContDiffAt ℝ 2 (source q) (D4BMMetricReconstruction.angularPoint p.val) :=
    D4BMLiteralCusp.scalar_contDiffAt _ 2 _ p.property.2
  have he : scalarLaplacian (source q) (D4BMMetricReconstruction.angularPoint p.val) =
      (physicalRate q branch+1)*(physicalRate q branch+2)*
        source q (D4BMMetricReconstruction.angularPoint p.val) :=
    scalar_physical_equation q branch _ p.property.2
  rw [hsplit,D4BMFullLinearEquation.fieldSpace_add p _ _ hS hV,
    physical_coexact_jet,physical_scalar_jet,
    D4BMScalarLinearEquation.field_jet _ _ _ p hs he]
  have hB (a : ℂ) : D4BMFundamentalScalarMetric.envelope (physicalRate q branch) a p.val =
      a*D4BMFundamentalScalarMetric.envelope (physicalRate q branch) 1 p.val := by
    simp only [D4BMFundamentalScalarMetric.envelope,one_mul,mul_assoc]
  rw [hB aS,hB aV]
  rfl

/-- Trace-free hyperbolic Hessian in the source's diagonal-difference/off-diagonal convention. -/
def hessianComponents (F : Field) (z : Point) : ℂ × ℂ :=
  (coordDeriv 0 (coordDeriv 0 F) z-coordDeriv 1 (coordDeriv 1 F) z-
      2*coordDeriv 1 F z/(z 1:ℂ),
   coordDeriv 0 (coordDeriv 1 F) z+coordDeriv 0 F z/(z 1:ℂ))

/-- The complete gradient source is the Hessian of the constructed response, with its forced sign. -/
theorem gradientPair_eq_response (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    gradientPair (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z) =
      (-eigenvalue q) • hessianComponents (coordinateResponse q) z := by
  have h := D4BMAngularTwoCuspDecay.actual_components_zero q z hz
  apply Prod.ext
  · dsimp [gradientPair,hessianComponents]
    dsimp [defectA,componentA] at h
    linear_combination 2*h.1
  · dsimp [gradientPair,hessianComponents]
    dsimp [defectB,componentB] at h
    linear_combination h.2

private theorem half_square_hessian (q : XiZeroCopy) (branch : Bool) (z : Point) (hz : 0 < z 1) :
    hessianPair (physicalRate q branch) (z 1) (source q z)
      (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
      (coordDeriv 0 (coordDeriv 0 (source q)) z) (coordDeriv 0 (coordDeriv 1 (source q)) z)+
      gradientPair (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z) =
      (1/2:ℂ) • hessianComponents (squareSource q) z := by
  apply Prod.ext
  · dsimp only [hessianPair,gradientPair,hessianComponents,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    rw [squareSource_first q z hz,squareSource_second q z hz,squareSource_second q z hz,
      source_syy q branch z hz]
    ring
  · dsimp only [hessianPair,gradientPair,hessianComponents,Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    rw [squareSource_first q z hz,squareSource_second q z hz]
    ring

/-- All three source channels expressed through two original scalar potentials; no tensor is dropped. -/
def potentialSource (q : XiZeroCopy) (branch : Bool) (r B aS aV : ℂ) (z : Point) : ℂ × ℂ :=
  B^(2 : ℕ) • ((aS^(2 : ℕ)*scalarWeight (physicalRate q branch) r) • hessianComponents (squareSource q) z+
    (aS*aV*mixedWeight (physicalRate q branch) r/2) •
      rotatePair (hessianComponents (squareSource q) z)+
    (eigenvalue q*(aS^(2 : ℕ)*scalarWeight (physicalRate q branch) r-
      aV^(2 : ℕ)*vectorWeight (physicalRate q branch) r)) • hessianComponents (coordinateResponse q) z)

/-- Source-level angular potential identity for the actual literal scalar/vector jets. -/
theorem literal_angular_potential (q : XiZeroCopy) (branch : Bool) (r B aS aV : ℂ)
    (z : Point) (hz : 0 < z 1) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    angularCoefficient (physicalRate q branch) r (z 1) B aS aV
      (source q z) (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
      (coordDeriv 0 (coordDeriv 0 (source q)) z) (coordDeriv 0 (coordDeriv 1 (source q)) z)
      (coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z)
      (coordDeriv 0 (coordDeriv 0 (coordDeriv 1 (source q))) z) =
        potentialSource q branch r B aS aV z := by
  rw [angularCoefficient_decomposition _ _ _ _ _ _ _ _ _ _ _ _ _ hr
    (Complex.ofReal_ne_zero.mpr hz.ne') hf]
  rw [half_square_hessian q branch z hz,gradientPair_eq_response q z hz]
  apply Prod.ext <;> dsimp [potentialSource,rotatePair] <;> ring

/-- The angular coefficient of the original nonlinear metric source. -/
def physicalAngularSource (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) : ℂ × ℂ :=
  let E := D4BMQuadraticConservation.physicalQuadraticSource q branch aS aV p.val
  (E 2 2-E 3 3,E 2 3)

/-- Unconditional identification of both independent physical angular source components. -/
theorem physical_angular_potential (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    physicalAngularSource q branch aS aV p =
      potentialSource q branch (p.val 1)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) 1 p.val) aS aV
        (D4BMMetricReconstruction.angularPoint p.val) := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have h := literal_angular_potential q branch (p.val 1)
    (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) 1 p.val) aS aV
    (D4BMMetricReconstruction.angularPoint p.val) p.property.2 hr hf
  have hycoord : D4BMMetricReconstruction.angularPoint p.val 1 = p.val 3 := rfl
  rw [hycoord] at h
  rw [← h]
  unfold physicalAngularSource
  let J := ComplexCoordinateMetricTwoJet.toSpace (D4BMBackground.actualJet p)
  let K := ComplexCoordinateMetricTwoJet.toSpace (D4BMMetricReconstruction.ofMetricField
    (D4BMLiteralCusp.physicalPerturbation q branch aS aV) p.val)
  change ((1/2:ℂ)*ComplexCoordinateMetricTwoJet.secondVariation J 2 2 K K-
    (1/2:ℂ)*ComplexCoordinateMetricTwoJet.secondVariation J 3 3 K K,
    (1/2:ℂ)*ComplexCoordinateMetricTwoJet.secondVariation J 2 3 K K) = _
  dsimp only [J,K]
  rw [physical_combined_space]
  unfold angularCoefficient
  rw [D4BMBackground.actualJet_eq]
  apply Prod.ext <;> dsimp <;> ring

/-- The explicitly corrected angular source retains a fixed response Hessian in the SS and VV channels. -/
theorem corrected_angular_potential (q : XiZeroCopy) (branch : Bool) (B aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.angularPoint p.val
    D4BMQuadraticAngularCorrection.correctedAngularCoefficient (physicalRate q branch)
      (p.val 1) (p.val 3) B aS aV
      (source q z) (coordDeriv 0 (source q) z) (coordDeriv 1 (source q) z)
      (coordDeriv 0 (coordDeriv 0 (source q)) z) (coordDeriv 0 (coordDeriv 1 (source q)) z)
      (coordDeriv 0 (coordDeriv 0 (coordDeriv 0 (source q))) z)
      (coordDeriv 0 (coordDeriv 0 (coordDeriv 1 (source q))) z) =
      (B^(2 : ℕ)*eigenvalue q*(aS^(2 : ℕ)*scalarWeight (physicalRate q branch) (p.val 1)-
        aV^(2 : ℕ)*vectorWeight (physicalRate q branch) (p.val 1))) •
        hessianComponents (coordinateResponse q) z := by
  have hr : (p.val 1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  dsimp only
  rw [D4BMQuadraticAngularCorrection.correctedAngularCoefficient_eq _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hf,
    gradientPair_eq_response q _ p.property.2]
  apply Prod.ext <;> dsimp <;> ring

/-- Polarization retains independently chosen scalar/vector amplitudes in both source slots. -/
theorem physical_angular_polarization (q : XiZeroCopy) (branch : Bool) (aS aV cS cV : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    let z := D4BMMetricReconstruction.angularPoint p.val
    let B := D4BMFundamentalScalarMetric.envelope (physicalRate q branch) 1 p.val
    (1/2:ℂ) • (physicalAngularSource q branch (aS+cS) (aV+cV) p-
      physicalAngularSource q branch aS aV p-physicalAngularSource q branch cS cV p) =
      B^(2 : ℕ) • ((aS*cS*scalarWeight (physicalRate q branch) (p.val 1)) •
          hessianComponents (squareSource q) z+
        ((aS*cV+aV*cS)*mixedWeight (physicalRate q branch) (p.val 1)/4) •
          rotatePair (hessianComponents (squareSource q) z)+
        (eigenvalue q*(aS*cS*scalarWeight (physicalRate q branch) (p.val 1)-
          aV*cV*vectorWeight (physicalRate q branch) (p.val 1))) •
          hessianComponents (coordinateResponse q) z) := by
  rw [physical_angular_potential,physical_angular_potential,physical_angular_potential]
  apply Prod.ext <;> dsimp [potentialSource] <;> ring

/-- The potential formula is the original nonlinear Einstein source's actual second Taylor coefficient. -/
theorem physical_angular_coefficient (q : XiZeroCopy) (branch : Bool) (aS aV : ℂ)
    (p : D4BMBackground.ExteriorPoint) :
    let E := D4BMActualMetricSource.source p (D4BMLiteralCusp.physicalPerturbation q branch aS aV)
    (iteratedDeriv 2 (E 2 2) 0/2-iteratedDeriv 2 (E 3 3) 0/2,iteratedDeriv 2 (E 2 3) 0/2) =
      potentialSource q branch (p.val 1)
        (D4BMFundamentalScalarMetric.envelope (physicalRate q branch) 1 p.val) aS aV
        (D4BMMetricReconstruction.angularPoint p.val) := by
  dsimp only
  rw [← D4BMQuadraticConservation.physicalQuadraticSource_eq p q branch aS aV 2 2,
    ← D4BMQuadraticConservation.physicalQuadraticSource_eq p q branch aS aV 3 3,
    ← D4BMQuadraticConservation.physicalQuadraticSource_eq p q branch aS aV 2 3]
  exact physical_angular_potential q branch aS aV p

end
end RHTower.D4BMPhysicalAngularPotential
