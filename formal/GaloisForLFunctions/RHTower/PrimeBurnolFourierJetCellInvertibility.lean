import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetCellCoupling
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetCellCubic

/-!
# Actual complete cubic on a prime-depth tail

The one-column packet Gram, including both physical outputs, is identified with
its normalized two-channel matrix. Its canonical modular inverse is transported
exactly. At every nonzero unbalanced prime parameter, the complete cubic is
invertible at every sufficiently late depth.
-/

open Complex Filter Topology Matrix
open scoped InnerProductSpace
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def primeBurnolSingletonPacket (pe : Nat.Primes × ℕ) : Fin 1 ↪ Nat.Primes × ℕ where
  toFun _ := pe
  inj' _ _ _ := Subsingleton.elim _ _

def burnolJetCellReindex : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ ≃ₐ[ℂ]
    Matrix (Fin 2) (Fin 2) ℂ := Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv

private theorem cellIndex_zero : (finSumFinEquiv.symm (0 : Fin 2) : Fin 1 ⊕ Fin 1)=Sum.inl 0 := rfl
private theorem cellIndex_one : (finSumFinEquiv.symm (1 : Fin 2) : Fin 1 ⊕ Fin 1)=Sum.inr 0 := rfl
private theorem squareColumn_coe (pe : Nat.Primes × ℕ) :
    (primeBurnolSquareColumn pe : SoninL2)=primeBurnolEvenFeatureLp pe := rfl

private theorem cross_real {f : SoninL2} (hf : f ∈ evenSubspace) :
    ((⟪f,fourierUnitary f⟫_ℂ).re : ℂ)=⟪f,fourierUnitary f⟫_ℂ := by
  apply Complex.conj_eq_iff_re.mp
  rw [inner_conj_symm]
  have h := fourierUnitary.inner_map_map f (fourierUnitary f)
  rwa [fourierUnitary_fourierUnitary_of_mem_evenSubspace hf] at h

private theorem cell_coupling_real (pe : Nat.Primes × ℕ) :
    (burnolJetCellCoupling pe : ℂ)=
      ⟪primeBurnolEvenFeatureLp pe,fourierUnitary (primeBurnolEvenFeatureLp pe)⟫_ℂ+
      ⟪burnolSquarePosition (primeBurnolSquareColumn pe),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn pe))⟫_ℂ := by
  rw [burnolJetCellCoupling,Complex.add_re,Complex.ofReal_add,
    cross_real (primeBurnolEvenFeatureLp_mem_evenSubspace pe),
    cross_real (burnolSquarePosition_mem_evenSubspace _ (primeBurnolEvenFeatureLp_mem_evenSubspace pe))]

theorem primeBurnolFourierJetGram_singleton (pe : Nat.Primes × ℕ) :
    burnolJetCellReindex (primeBurnolFourierJetGram (primeBurnolSingletonPacket pe)) =
      (burnolJetCellMass pe : ℂ) •
        burnolJetCellNormalizedGram (burnolJetCellNormalizedCoupling pe : ℂ) := by
  have hm : (burnolJetCellMass pe : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (burnolJetCellMass_pos pe).ne'
  have hc := cell_coupling_real pe
  have hquot : (burnolJetCellMass pe : ℂ)*
      ((burnolJetCellCoupling pe : ℂ)/(burnolJetCellMass pe : ℂ))=(burnolJetCellCoupling pe : ℂ) := by
    field_simp
  simp only [burnolJetCellMass] at hquot
  have hf := fourierUnitary.inner_map_map (primeBurnolEvenFeatureLp pe)
    (fourierUnitary (primeBurnolEvenFeatureLp pe))
  rw [fourierUnitary_fourierUnitary_of_mem_evenSubspace
    (primeBurnolEvenFeatureLp_mem_evenSubspace pe)] at hf
  have hj := fourierUnitary.inner_map_map (burnolSquarePosition (primeBurnolSquareColumn pe))
    (fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn pe)))
  rw [fourierUnitary_fourierUnitary_of_mem_evenSubspace
    (burnolSquarePosition_mem_evenSubspace _ (primeBurnolEvenFeatureLp_mem_evenSubspace pe))] at hj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnolJetCellReindex,Matrix.reindex_apply,primeBurnolFourierJetGram,
      primeBurnolSingletonPacket,primeBurnolJetGraphColumn,burnolJetOutputPairing,
      burnolJetGraphVector,primeBurnolFourierJetSynthesis,burnolJetCellNormalizedGram,
      burnolJetCellSwap,burnolJetCellNormalizedCoupling,inner_self_eq_norm_sq_to_K,
      burnolJetCellMass,← Complex.ofReal_pow,← Complex.ofReal_add,hf,hj,
      cellIndex_zero,cellIndex_one,squareColumn_coe,hquot,← hc]

theorem burnolJetCellReindex_neutral :
    burnolJetCellReindex (burnolJetNeutralMatrix 1)=burnolJetCellNeutral := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnolJetCellReindex,Matrix.reindex_apply,burnolJetNeutralMatrix,burnolJetCellNeutral,
      cellIndex_zero,cellIndex_one]

theorem burnolJetCellReindex_theta (p : Nat.Primes) (a : ℝ) :
    burnolJetCellReindex (burnolJetThetaMatrix 1 p a)=
      burnolJetCellPolarization ((primeBurnolThetaVisibility a p : ℂ)^2)
        ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) := by
  have h : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 :=
    by exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnolJetCellReindex,Matrix.reindex_apply,burnolJetThetaMatrix,burnolJetCellPolarization,
      cellIndex_zero,cellIndex_one]
  linear_combination h

private theorem cell_inverse_scale {m t : ℂ} (hm : m≠0) (ht : 1-t^2≠0) :
    (m • burnolJetCellNormalizedGram t)⁻¹=m⁻¹ • (burnolJetCellNormalizedGram t)⁻¹ := by
  have hc : IsUnit (burnolJetCellNormalizedGram t).det := by
    apply isUnit_iff_ne_zero.mpr
    simpa [burnolJetCellNormalizedGram,burnolJetCellSwap,Matrix.det_fin_two,pow_two] using ht
  apply Matrix.inv_eq_left_inv
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Matrix.nonsing_inv_mul _ hc,mul_inv_cancel₀ hm,one_smul]

theorem primeBurnolFourierJetConstantThetaCubic_singleton (pe : Nat.Primes × ℕ)
    (p : Nat.Primes) (a : ℝ)
    (ht : 1-(burnolJetCellNormalizedCoupling pe : ℂ)^2≠0) :
    burnolJetCellReindex (primeBurnolFourierJetConstantThetaCubic (primeBurnolSingletonPacket pe) p a)=
      cubicProjectionAssociatorAlgebra
        ((burnolJetCellNormalizedGram (burnolJetCellNormalizedCoupling pe : ℂ))⁻¹*
          burnolJetCellPolarization ((primeBurnolThetaVisibility a p : ℂ)^2)
            ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ))*
          burnolJetCellNormalizedGram (burnolJetCellNormalizedCoupling pe : ℂ))
        (burnolJetCellPolarization ((primeBurnolThetaVisibility a p : ℂ)^2)
          ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)))
        burnolJetCellNeutral := by
  let U := primeBurnolFourierJetGramUnit (primeBurnolSingletonPacket pe)
  have hi : (burnolJetCellReindex (U : Matrix _ _ ℂ))⁻¹=
      burnolJetCellReindex (↑(U⁻¹) : Matrix _ _ ℂ) := by
    apply Matrix.inv_eq_left_inv
    rw [← map_mul,Units.inv_mul,map_one]
  have hm : (burnolJetCellMass pe : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (burnolJetCellMass_pos pe).ne'
  unfold primeBurnolFourierJetConstantThetaCubic cubicProjectionAssociatorAlgebra
  change burnolJetCellReindex (((↑(U⁻¹) : Matrix _ _ ℂ)*(burnolJetThetaMatrix 1 p a)*(↑U : Matrix _ _ ℂ)-
    burnolJetNeutralMatrix 1)^3-((↑(U⁻¹) : Matrix _ _ ℂ)*(burnolJetThetaMatrix 1 p a)*(↑U : Matrix _ _ ℂ)-
    burnolJetThetaMatrix 1 p a)^3-(burnolJetThetaMatrix 1 p a-burnolJetNeutralMatrix 1)^3)=_
  simp only [map_sub,map_pow,map_mul,← hi,burnolJetCellReindex_theta,burnolJetCellReindex_neutral]
  dsimp only [U]
  rw [coe_primeBurnolFourierJetGramUnit,primeBurnolFourierJetGram_singleton,cell_inverse_scale hm ht]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hm,one_smul]

theorem primeBurnolFourierJetSingletonCubic_eventually_isUnit (p : Nat.Primes) {a : ℝ}
    (ha : a≠0) (hb : primeBurnolThetaVisibility a p^2≠primeBurnolThetaContrast a p^2) :
    ∀ᶠ n in atTop,
      IsUnit (primeBurnolFourierJetConstantThetaCubic (primeBurnolSingletonPacket (p,n)) p a) := by
  let v : ℂ := primeBurnolThetaVisibility a p
  let c : ℂ := primeBurnolThetaContrast a p
  have hsum : v^2+c^2=1 := by
    dsimp only [v,c]
    exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hc : c≠0 := Complex.ofReal_ne_zero.mpr ((primeBurnolThetaContrast_eq_zero_iff p a).not.mpr ha)
  have hu : 1-v^2≠0 := by
    rw [show 1-v^2=c^2 by linear_combination -hsum]
    exact pow_ne_zero _ hc
  have hbal : 2*v^2-1≠0 := by
    intro h
    apply hb
    have he : v^2=c^2 := by linear_combination h-hsum
    dsimp only [v,c] at he
    exact_mod_cast he
  have hw : (v*c)^2=v^2*(1-v^2) := by
    rw [show 1-v^2=c^2 by linear_combination -hsum,mul_pow]
  have ht : Tendsto (fun n => (burnolJetCellNormalizedCoupling (p,n) : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast (Complex.continuous_ofReal.tendsto 0).comp (burnolJetCellNormalizedCoupling_tendsto p)
  have hden : ∀ᶠ t in 𝓝 (0 : ℂ), 1-t^2≠0 :=
    (show ContinuousAt (fun t : ℂ => 1-t^2) 0 by fun_prop).eventually_ne (by norm_num)
  filter_upwards [ht.eventually (burnolJetCellCubic_eventually_isUnit hw hu hbal),
    ht.eventually hden,burnolJetCellNormalizedCoupling_eventually_ne_zero p] with n hn hd hn0
  have hh := hn (Complex.ofReal_ne_zero.mpr hn0)
  rw [← primeBurnolFourierJetConstantThetaCubic_singleton (p,n) p a hd] at hh
  exact (isUnit_map_iff burnolJetCellReindex _).mp hh

/-- The surviving skew boundary symbol of the actual complete singleton cubic. -/
theorem primeBurnolFourierJetSingletonCubic_scaled_tendsto (p : Nat.Primes) (a : ℝ) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) •
      burnolJetCellReindex (primeBurnolFourierJetConstantThetaCubic
        (primeBurnolSingletonPacket (p,n)) p a)) atTop
      (𝓝 ((8*((2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*
        (1-(primeBurnolThetaVisibility a p : ℂ)^2))) • burnolJetCellSkew)) := by
  let u := (primeBurnolThetaVisibility a p : ℂ)^2
  let w := (primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)
  have hsum : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 :=
    by exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hw : w^2=u*(1-u) := by
    dsimp only [w,u]
    rw [show 1-(primeBurnolThetaVisibility a p : ℂ)^2=(primeBurnolThetaContrast a p : ℂ)^2
      by linear_combination -hsum,mul_pow]
  have ht : Tendsto (fun n => (burnolJetCellNormalizedCoupling (p,n) : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast (Complex.continuous_ofReal.tendsto 0).comp (burnolJetCellNormalizedCoupling_tendsto p)
  have hscaled : Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ)*
      (burnolJetCellNormalizedCoupling (p,n) : ℂ)) atTop (𝓝 (8 : ℂ)) := by
    simpa only [Function.comp_def,Complex.ofReal_mul,Complex.ofReal_ofNat] using!
      (Complex.continuous_ofReal.tendsto 8).comp (burnolJetCellNormalizedCoupling_scaled_tendsto p)
  have hlim := hscaled.smul ((burnolJetCellCubicVariation_continuousAt u w).tendsto.comp ht)
  rw [burnolJetCellCubicVariation_zero hw,smul_smul] at hlim
  apply hlim.congr'
  have hden : ∀ᶠ t in 𝓝 (0 : ℂ), 1-t^2≠0 :=
    (show ContinuousAt (fun t : ℂ => 1-t^2) 0 by fun_prop).eventually_ne (by norm_num)
  filter_upwards [ht.eventually hden] with n hn
  rw [primeBurnolFourierJetConstantThetaCubic_singleton _ p a hn,burnolJetCell_cubic_factor hn,
    smul_smul]
  rfl


end RHTower
