import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricSourceJets

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalMetricSourceTransfers
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalCausalPotential
open D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent D4BMOriginalReaderEquation
open D4BMOriginalAngularReaderBounds D4BMOriginalReaderCuspBounds D4BMOriginalAngularProducts
open D4BMOriginalPrincipalHorizonBounds D4BMOriginalMetricForcingMatch D4BMOriginalMetricSourceJets
open D4BMOriginalBaseCircleJets D4BMOriginalCuspFlux D4BMOriginalCompactBoundary
noncomputable section
set_option autoImplicit false

/-- Canonical source coefficients retain the exact radius reconstruction. -/
theorem source_coefficient_collar (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p L : ℝ) (hL : 0<L) (i : Fin 3) :
    D4BMOriginalOrbitCusp.principalCoefficient q br amp p (tortoiseRadius (-L/2)) i=
      (tortoiseRadius (-L/2):ℂ)*coefficient q br amp i p L := by
  unfold D4BMOriginalOrbitCusp.principalCoefficient coefficient
  rw [tortoise_original_inverse (-L/2) (by linarith),show p-2*(-L/2)=p+L by ring]

private theorem reader_operations (q : XiZeroCopy) (w : ℂ) (hwi : w.im≠0)
    (p L x k : ℝ) (hL : 0<L) :
    modeScalar q w true ![p,tortoiseRadius (-L/2),x,Real.exp k]=
      (tortoiseRadius (-L/2):ℂ)*Complex.exp (-w*(p:ℂ))*reader q w L*angularJet q false x k ∧
    coordDeriv 3 (modeScalar q w true) ![p,tortoiseRadius (-L/2),x,Real.exp k]=
      (tortoiseRadius (-L/2):ℂ)*Complex.exp (-w*(p:ℂ))*reader q w L*angularJet q true x k := by
  constructor
  · change modeAmplitude q w true ![p,tortoiseRadius (-L/2)]*angularJet q false x k=_
    rw [mode_amplitude_collar q w p L hL]
  · have h := physical_mode_normal q w hwi true ![p,tortoiseRadius (-L/2),x,Real.exp k]
      (tortoiseRadius_exterior (-L/2) (by linarith)) (Real.exp_pos k)
    simp only [Matrix.cons_val] at h
    rw [h,mode_amplitude_collar q w p L hL]
    rfl

private theorem normal_principal_product (q : XiZeroCopy) (a : Fin 3 → ℂ) (k : ℝ) :
    (∑ i : Fin 3,a i*Complex.exp (principalExponent q i*(k:ℂ)))*angularPrincipal q true k=
      ∑ i : Fin 3,a i*readerCoefficient q*readerExponent q*Complex.exp (fluxExponent q q i*(k:ℂ)) := by
  simp only [angularPrincipal,↓reduceIte,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Complex.exp (fluxExponent q q i*(k:ℂ))=
      Complex.exp (principalExponent q i*(k:ℂ))*Complex.exp ((readerExponent q-1)*(k:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold fluxExponent
    ring
  rw [he]
  ring

private theorem source_normal_principal_product (q : XiZeroCopy) (a : Fin 3 → ℂ) (k : ℝ) :
    Complex.exp (-(k:ℂ))*(∑ i : Fin 3,a i*Complex.exp (principalExponent q i*(k:ℂ)))*angularPrincipal q false k=
      ∑ i : Fin 3,a i*readerCoefficient q*Complex.exp (fluxExponent q q i*(k:ℂ)) := by
  simp only [angularPrincipal, Bool.false_eq_true, if_false,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Complex.exp (fluxExponent q q i*(k:ℂ))=
      Complex.exp (-(k:ℂ))*Complex.exp (principalExponent q i*(k:ℂ))*Complex.exp (readerExponent q*(k:ℂ)) := by
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    unfold fluxExponent
    ring
  rw [he]
  ring

/-- All four actual physical transfers with the unchanged complete-boundary counterterms. -/
def transferCut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (j : Fin 4) (p L x k : ℝ) : ℂ :=
  let U := sourceScalar q br amp
  let W := modeScalar q w true
  transfer (![U,W,angularLap U,D4BMOriginalSourceContact.originalForcing q br amp] j)
    (![W,U,W,W] j) 1 ![p,tortoiseRadius (-L/2),x,Real.exp k]-
      ∑ i : Fin 3,modeTransferCoefficient q q br true amp w j p (tortoiseRadius (-L/2)) i*
        Complex.exp (fluxExponent q q i*(k:ℂ))

/-- The three evolved-source transfers are exactly the already-controlled
source products, with their physical radius, time and height factors. -/
theorem physical_source_transfer_products (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (p L x k : ℝ) (hp : 0<p) (hL : 0<L) :
    transferCut q br amp w 0 p L x k=
      (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*Complex.exp (-w*(p:ℂ))*angularProduct q br amp w 0 true p L x k ∧
    transferCut q br amp w 1 p L x k=
      (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*Complex.exp (-w*(p:ℂ))*Complex.exp (-(k:ℂ))*
        angularProduct q br amp w 1 false p L x k ∧
    transferCut q br amp w 2 p L x k=
      (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*Complex.exp (-w*(p:ℂ))*
        (Complex.exp (2*(k:ℂ))*angularProduct q br amp w 2 true p L x k+
          angularProduct q br amp w 3 true p L x k-angularProduct q br amp w 1 true p L x k) := by
  have hs := physical_source_operations q br amp p L x k hp hL
  dsimp only at hs
  have hm := reader_operations q w hwi p L x k hL
  have hP0 := normal_principal_product q (fun i => coefficient q br amp i p L) k
  have hP1 := source_normal_principal_product q (fun i => coefficient q br amp i p L*principalExponent q i) k
  have hP2 := normal_principal_product q
    (fun i => coefficient q br amp i p L*principalExponent q i*(principalExponent q i-1)) k
  refine ⟨?_,?_,?_⟩
  · unfold transferCut transfer
    simp only [Matrix.cons_val,angularIndex]
    rw [hs.1,hm.2]
    simp only [modeTransferCoefficient,Matrix.cons_val,source_coefficient_collar q br amp p L hL,
      mode_amplitude_collar q w p L hL,angularProduct,D4BMOriginalAngularProducts.principalJet,jetMultiplier,mul_one]
    simp only [Fin.sum_univ_three] at hP0 ⊢
    linear_combination (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*Complex.exp (-w*(p:ℂ))*reader q w L*hP0
  · unfold transferCut transfer
    simp only [Matrix.cons_val,angularIndex]
    rw [hm.1,hs.2.1]
    simp only [modeTransferCoefficient,Matrix.cons_val,source_coefficient_collar q br amp p L hL,
      mode_amplitude_collar q w p L hL,angularProduct,D4BMOriginalAngularProducts.principalJet,jetMultiplier]
    simp only [Fin.sum_univ_three] at hP1 ⊢
    linear_combination (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*Complex.exp (-w*(p:ℂ))*reader q w L*hP1
  · unfold transferCut transfer
    simp only [Matrix.cons_val,angularIndex]
    rw [hs.2.2,hm.2]
    simp only [modeTransferCoefficient,Matrix.cons_val,source_coefficient_collar q br amp p L hL,
      mode_amplitude_collar q w p L hL,angularProduct,D4BMOriginalAngularProducts.principalJet,jetMultiplier]
    simp only [Fin.sum_univ_three] at hP2 ⊢
    linear_combination (tortoiseRadius (-L/2):ℂ)^(2 : ℕ)*Complex.exp (-w*(p:ℂ))*reader q w L*hP2

/-- The fourth member is exactly the previously matched original forcing transfer. -/
theorem physical_forcing_transfer_product (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hwi : w.im≠0)
    (p L x k : ℝ) (hL : 0<L) :
    transferCut q br amp w 3 p L x k=
      (tortoiseRadius (-L/2):ℂ)*Complex.exp (-w*(p:ℂ))*
        D4BMOriginalForcingProductBounds.rawProduct q br amp w true p L x k :=
  forcing_transfer_cut q br amp w hwi p L x k hL

end
end RHTower.D4BMOriginalMetricSourceTransfers
