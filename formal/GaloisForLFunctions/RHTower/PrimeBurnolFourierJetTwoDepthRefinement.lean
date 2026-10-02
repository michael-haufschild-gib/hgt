import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetTwoDepthSymbol
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetCellInvertibility

/-!
# Invertible refinement defect of actual two-depth complete cubics

The two singleton actions are assembled in their exact source coordinates.
Subtracting them from the complete two-depth action leaves a refinement defect
whose amplitude-conjugated frequency-scaled limit is invertible away from the
neutral and single-prime balancing parameters. Thus the original defect is
invertible at every sufficiently late depth.
-/

open Complex Filter Topology Matrix
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def burnolJetCellAssembly {N : ℕ} (S : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal fun i => S i 0 0) (Matrix.diagonal fun i => S i 0 1)
    (Matrix.diagonal fun i => S i 1 0) (Matrix.diagonal fun i => S i 1 1)

theorem burnolJetCellAssembly_continuous (N : ℕ) : Continuous (@burnolJetCellAssembly N) := by
  have hc (i j : Fin 2) : Continuous (fun S : Fin N → Matrix (Fin 2) (Fin 2) ℂ =>
      Matrix.diagonal fun k => S k i j) :=
    (continuous_pi fun k => (continuous_apply k).matrix_elem i j).matrix_diagonal
  exact (hc 0 0).matrix_fromBlocks (hc 0 1) (hc 1 0) (hc 1 1)

theorem burnolJetCellAssembly_smul {N : ℕ} (s : ℂ) (S : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    burnolJetCellAssembly (fun i => s • S i)=s • burnolJetCellAssembly S := by
  ext (i|i) (j|j) <;> simp [burnolJetCellAssembly,Matrix.diagonal]

def primeBurnolTwoDepthSingletonAssembly (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  burnolJetCellAssembly (fun i => burnolJetCellReindex
    (primeBurnolFourierJetConstantThetaCubic (primeBurnolSingletonPacket (primeBurnolTwoDepthPacket p n i)) p a))

theorem primeBurnolTwoDepthSingleton_scaled_tendsto (p : Nat.Primes) (a : ℝ) (i : Fin 2) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) •
      burnolJetCellReindex (primeBurnolFourierJetConstantThetaCubic
        (primeBurnolSingletonPacket (primeBurnolTwoDepthPacket p n i)) p a)) atTop
      (𝓝 (((8/(burnolTwoDepthRatio i : ℂ))*((2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*
        (1-(primeBurnolThetaVisibility a p : ℂ)^2))) • burnolJetCellSkew)) := by
  have hdepth : Tendsto (fun n => (primeBurnolTwoDepthPacket p n i).2) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    fin_cases i <;> simp [primeBurnolTwoDepthPacket]
    omega
  have hi : (burnolTwoDepthRatio i : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (burnolTwoDepthRatio_pos i).ne'
  have h := ((primeBurnolFourierJetSingletonCubic_scaled_tendsto p a).comp hdepth).const_smul
    (burnolTwoDepthRatio i : ℂ)⁻¹
  change Tendsto (fun n => (burnolTwoDepthRatio i : ℂ)⁻¹ •
    ((primeBurnolLogFrequency (primeBurnolTwoDepthPacket p n i) : ℂ) •
      burnolJetCellReindex (primeBurnolFourierJetConstantThetaCubic
        (primeBurnolSingletonPacket (primeBurnolTwoDepthPacket p n i)) p a))) _ _ at h
  simp only [primeBurnolTwoDepthPacket_frequency,Complex.ofReal_mul,smul_smul,
    ← mul_assoc,inv_mul_cancel₀ hi,one_mul] at h
  convert h using 1
  congr 2
  ring

theorem primeBurnolTwoDepthSingletonAssembly_scaled_tendsto (p : Nat.Primes) (a : ℝ) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) •
      primeBurnolTwoDepthSingletonAssembly p n a) atTop
      (𝓝 (((2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*
        (1-(primeBurnolThetaVisibility a p : ℂ)^2)) • burnolJetBlockSkew burnolTwoDepthSingletonScale)) := by
  have hcells := tendsto_pi_nhds.mpr (primeBurnolTwoDepthSingleton_scaled_tendsto p a)
  have h := (burnolJetCellAssembly_continuous 2).tendsto _ |>.comp hcells
  simp only [Function.comp_def,burnolJetCellAssembly_smul] at h
  let k := (2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*(1-(primeBurnolThetaVisibility a p : ℂ)^2)
  have he : burnolJetCellAssembly (fun i => ((8/(burnolTwoDepthRatio i : ℂ))*k) • burnolJetCellSkew)=
      k • burnolJetBlockSkew burnolTwoDepthSingletonScale := by
    ext (i|i) (j|j) <;>
      simp [burnolJetCellAssembly,burnolJetCellSkew,burnolJetBlockSkew,
        burnolTwoDepthSingletonScale,Matrix.diagonal] <;> split_ifs <;> ring
  rw [he] at h
  exact h

def primeBurnolTwoDepthRefinement (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  primeBurnolFourierJetConstantThetaCubic (primeBurnolTwoDepthPacket p n) p a-
    primeBurnolTwoDepthSingletonAssembly p n a

def primeBurnolTwoDepthNormalizedRefinement (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  primeBurnolTwoDepthNormalizedCubic p n a-primeBurnolTwoDepthSingletonAssembly p n a

theorem primeBurnolTwoDepthSingletonAssembly_conjugate (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    sourceModularAutomorphism ((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹)
      (primeBurnolTwoDepthSingletonAssembly p n a)=primeBurnolTwoDepthSingletonAssembly p n a := by
  change (↑(primeBurnolTwoDepthAmplitudeUnit p n) : Matrix _ _ ℂ)*
    primeBurnolTwoDepthSingletonAssembly p n a*(↑((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹) : Matrix _ _ ℂ)=_
  change Matrix.diagonal (primeBurnolTwoDepthChannelAmplitude p n)*
    primeBurnolTwoDepthSingletonAssembly p n a*
      Matrix.diagonal (fun i => (primeBurnolTwoDepthChannelAmplitude p n i)⁻¹)=_
  ext (i|i) (j|j) <;>
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul] <;>
    simp [primeBurnolTwoDepthSingletonAssembly,burnolJetCellAssembly,primeBurnolTwoDepthChannelAmplitude,
      Matrix.diagonal] <;> split_ifs <;> simp_all <;> field_simp [primeBurnolAmplitude_ne_zero]

theorem primeBurnolTwoDepthNormalizedRefinement_conjugate (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    primeBurnolTwoDepthNormalizedRefinement p n a=
      sourceModularAutomorphism ((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹)
        (primeBurnolTwoDepthRefinement p n a) := by
  simp only [primeBurnolTwoDepthNormalizedRefinement,primeBurnolTwoDepthRefinement,map_sub,
    primeBurnolTwoDepthNormalizedCubic_conjugate,primeBurnolTwoDepthSingletonAssembly_conjugate]

theorem primeBurnolTwoDepthNormalizedRefinement_scaled_tendsto (p : Nat.Primes) (a : ℝ) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) •
      primeBurnolTwoDepthNormalizedRefinement p n a) atTop
      (𝓝 (((2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*
        (1-(primeBurnolThetaVisibility a p : ℂ)^2)) • burnolJetBlockSkew burnolTwoDepthLimitRefinement)) := by
  have h := (primeBurnolTwoDepthNormalizedCubic_scaled_tendsto p a).sub
    (primeBurnolTwoDepthSingletonAssembly_scaled_tendsto p a)
  have he : burnolJetBlockSkew (burnolTwoDepthLimitGram⁻¹*burnolTwoDepthLimitCross)-
      burnolJetBlockSkew burnolTwoDepthSingletonScale=burnolJetBlockSkew burnolTwoDepthLimitRefinement := by
    ext (i|i) (j|j) <;> simp [burnolJetBlockSkew,burnolTwoDepthLimitRefinement]
    ring
  simp only [← smul_sub,he] at h
  exact h

theorem primeBurnolThetaCubicSymbol_ne_zero (p : Nat.Primes) {a : ℝ} (ha : a≠0)
    (hb : primeBurnolThetaVisibility a p^2≠primeBurnolThetaContrast a p^2) :
    (2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*(1-(primeBurnolThetaVisibility a p : ℂ)^2)≠0 := by
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
  exact mul_ne_zero hbal hu

theorem primeBurnolTwoDepthRefinement_eventually_isUnit (p : Nat.Primes) {a : ℝ}
    (ha : a≠0) (hb : primeBurnolThetaVisibility a p^2≠primeBurnolThetaContrast a p^2) :
    ∀ᶠ n in atTop, IsUnit (primeBurnolTwoDepthRefinement p n a) := by
  let k := (2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*(1-(primeBurnolThetaVisibility a p : ℂ)^2)
  have hk : k≠0 := primeBurnolThetaCubicSymbol_ne_zero p ha hb
  have hD := burnolJetBlockSkew_isUnit burnolTwoDepthLimitRefinement burnolTwoDepthLimitRefinement_isUnit
  have hd : (k • burnolJetBlockSkew burnolTwoDepthLimitRefinement).det≠0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hk)
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hD))
  have h := continuous_id.matrix_det.tendsto _ |>.comp
    (primeBurnolTwoDepthNormalizedRefinement_scaled_tendsto p a)
  filter_upwards [h.eventually_ne hd] with n hn
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  intro hf
  have hconj : (primeBurnolTwoDepthNormalizedRefinement p n a).det=
      (primeBurnolTwoDepthRefinement p n a).det := by
    rw [primeBurnolTwoDepthNormalizedRefinement_conjugate]
    exact Matrix.det_units_conj (primeBurnolTwoDepthAmplitudeUnit p n) _
  apply hn
  simp only [Function.comp_def,id_eq]
  rw [Matrix.det_smul,hconj,hf,mul_zero]

end RHTower
