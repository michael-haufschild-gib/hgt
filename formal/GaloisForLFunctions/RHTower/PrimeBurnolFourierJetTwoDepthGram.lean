import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetCellCoupling

/-!
# Actual two-depth Fourier-jet Gram and refinement symbol

The packet at frequencies lambda and twice lambda retains both physical outputs.
After exact Euler-amplitude normalization, its diagonal block converges to G and
its frequency-scaled cross block converges to H. The limiting refinement residual
G⁻¹H minus the two singleton symbols is invertible.
-/

open Complex MeasureTheory Filter Topology Matrix
open scoped InnerProductSpace
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def primeBurnolTwoDepthPacket (p : Nat.Primes) (n : ℕ) : Fin 2 ↪ Nat.Primes × ℕ where
  toFun i := (p, ![n,2*n+1] i)
  inj' i j h := by
    have h := congrArg Prod.snd h
    fin_cases i <;> fin_cases j <;> simp at * <;> omega

def burnolTwoDepthRatio : Fin 2 → ℝ := ![1,2]

theorem burnolTwoDepthRatio_pos (i : Fin 2) : 0<burnolTwoDepthRatio i := by
  fin_cases i <;> norm_num [burnolTwoDepthRatio]

theorem primeBurnolTwoDepthPacket_frequency (p : Nat.Primes) (n : ℕ) (i : Fin 2) :
    primeBurnolLogFrequency (primeBurnolTwoDepthPacket p n i)=
      burnolTwoDepthRatio i*primeBurnolLogFrequency (p,n) := by
  fin_cases i <;>
    simp [primeBurnolTwoDepthPacket,burnolTwoDepthRatio,primeBurnolLogFrequency,
      primeBurnolValuation,Real.log_pow]
  ring

def burnolTwoDepthLimitGram : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => 4/(burnolTwoDepthRatio i+burnolTwoDepthRatio j : ℂ)^3

def burnolTwoDepthLimitCross : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => 4/((burnolTwoDepthRatio i : ℂ)^2*(burnolTwoDepthRatio j : ℂ)^2)

def primeBurnolTwoDepthGramBlock (p : Nat.Primes) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (primeBurnolLogFrequency (p,n) : ℂ)^3 /
    (primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i)*primeBurnolAmplitude (primeBurnolTwoDepthPacket p n j)) *
      (⟪primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n i),
        primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n j)⟫_ℂ+
      ⟪burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n i)),
        burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n j))⟫_ℂ)

def primeBurnolTwoDepthCrossBlock (p : Nat.Primes) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (primeBurnolLogFrequency (p,n) : ℂ)^3 /
    (primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i)*primeBurnolAmplitude (primeBurnolTwoDepthPacket p n j)) *
      (⟪primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n i),
        fourierUnitary (primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n j))⟫_ℂ+
      ⟪burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n i)),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n j)))⟫_ℂ)

theorem primeBurnolTwoDepthGramBlock_eq (p : Nat.Primes) (n : ℕ) (i j : Fin 2) :
    primeBurnolTwoDepthGramBlock p n i j=burnolTwoDepthLimitGram i j+
      1440/(burnolTwoDepthRatio i+burnolTwoDepthRatio j : ℂ)^7 *
        ((primeBurnolLogFrequency (p,n) : ℂ)⁻¹)^4 := by
  have hl : (primeBurnolLogFrequency (p,n) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne'
  have hA := primeBurnolAmplitude_ne_zero (primeBurnolTwoDepthPacket p n i)
  have hB := primeBurnolAmplitude_ne_zero (primeBurnolTwoDepthPacket p n j)
  have hr : (burnolTwoDepthRatio i+burnolTwoDepthRatio j : ℂ)≠0 := by
    exact_mod_cast (add_pos (burnolTwoDepthRatio_pos i) (burnolTwoDepthRatio_pos j)).ne'
  rw [primeBurnolTwoDepthGramBlock,primeBurnolEvenFeatureLp_inner_pair,
    burnolSquarePosition_primeBurnolSquareColumn_inner_pair]
  simp only [primeBurnolTwoDepthPacket_frequency,Complex.ofReal_mul]
  unfold burnolTwoDepthLimitGram
  rw [← add_mul]
  field_simp

theorem primeBurnolTwoDepthGramBlock_tendsto (p : Nat.Primes) :
    Tendsto (primeBurnolTwoDepthGramBlock p) atTop (𝓝 burnolTwoDepthLimitGram) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp_rw [primeBurnolTwoDepthGramBlock_eq]
  have hi : Tendsto (fun n => ((primeBurnolLogFrequency (p,n) : ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using!
      (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p))
  convert ((hi.pow 4).const_mul
    (1440/(burnolTwoDepthRatio i+burnolTwoDepthRatio j : ℂ)^7)).const_add
      (burnolTwoDepthLimitGram i j) using 1
  norm_num

private theorem twoDepth_fourier_cross_normalized (p : Nat.Primes) (n : ℕ) (i j : Fin 2) :
    (primeBurnolLogFrequency (p,n) : ℂ)^4 /
      (primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i)*primeBurnolAmplitude (primeBurnolTwoDepthPacket p n j)) *
      ⟪primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n i),
        fourierUnitary (primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n j))⟫_ℂ =
      (2/((burnolTwoDepthRatio i : ℂ)^2*(burnolTwoDepthRatio j : ℂ)^2)) *
        (burnolFourierCrossIntegral ((burnolTwoDepthRatio i*burnolTwoDepthRatio j)⁻¹*
          (primeBurnolLogFrequency (p,n))⁻¹^2) : ℝ) := by
  have hl : (primeBurnolLogFrequency (p,n) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne'
  have hA := primeBurnolAmplitude_ne_zero (primeBurnolTwoDepthPacket p n i)
  have hB := primeBurnolAmplitude_ne_zero (primeBurnolTwoDepthPacket p n j)
  have hi : (burnolTwoDepthRatio i : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (burnolTwoDepthRatio_pos i).ne'
  have hj : (burnolTwoDepthRatio j : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (burnolTwoDepthRatio_pos j).ne'
  rw [primeBurnolFourierCross_inner_pair]
  simp only [primeBurnolTwoDepthPacket_frequency,Complex.ofReal_mul]
  have he : (burnolTwoDepthRatio i*primeBurnolLogFrequency (p,n)*
      (burnolTwoDepthRatio j*primeBurnolLogFrequency (p,n)))⁻¹=
      (burnolTwoDepthRatio i*burnolTwoDepthRatio j)⁻¹*(primeBurnolLogFrequency (p,n))⁻¹^2 := by
    field_simp
  rw [he]
  field_simp

private theorem twoDepth_fourier_cross_tendsto (p : Nat.Primes) (i j : Fin 2) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ)^4 /
      (primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i)*primeBurnolAmplitude (primeBurnolTwoDepthPacket p n j)) *
      ⟪primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n i),
        fourierUnitary (primeBurnolEvenFeatureLp (primeBurnolTwoDepthPacket p n j))⟫_ℂ)
      atTop (𝓝 (burnolTwoDepthLimitCross i j)) := by
  simp_rw [twoDepth_fourier_cross_normalized]
  have hi := tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p)
  have ht : Tendsto (fun n => (burnolTwoDepthRatio i*burnolTwoDepthRatio j)⁻¹*
      (primeBurnolLogFrequency (p,n))⁻¹^2) atTop (𝓝 0) := by
    simpa using (hi.pow 2).const_mul (burnolTwoDepthRatio i*burnolTwoDepthRatio j)⁻¹
  have hI := (Complex.continuous_ofReal.tendsto 2).comp (burnolFourierCrossIntegral_tendsto.comp ht)
  convert hI.const_mul (2/((burnolTwoDepthRatio i : ℂ)^2*(burnolTwoDepthRatio j : ℂ)^2)) using 1
  · rfl
  · congr 1
    unfold burnolTwoDepthLimitCross
    push_cast
    ring

private theorem twoDepth_jet_cross_bound (p : Nat.Primes) (n : ℕ) (i j : Fin 2) :
    ‖(primeBurnolLogFrequency (p,n) : ℂ)^4 /
      (primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i)*primeBurnolAmplitude (primeBurnolTwoDepthPacket p n j)) *
      ⟪burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n i)),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n j)))⟫_ℂ‖ ≤
      (45/(8*burnolTwoDepthRatio i^7)+45/(8*burnolTwoDepthRatio j^7))*
        (primeBurnolLogFrequency (p,n))⁻¹^3 := by
  have hl := primeBurnolLogFrequency_pos (p,n)
  have hi := burnolTwoDepthRatio_pos i
  have hj := burnolTwoDepthRatio_pos j
  rw [div_mul_eq_mul_div,mul_div_assoc,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hl]
  calc
    _ ≤ primeBurnolLogFrequency (p,n)^4 *
        (45/(8*primeBurnolLogFrequency (primeBurnolTwoDepthPacket p n i)^7)+
          45/(8*primeBurnolLogFrequency (primeBurnolTwoDepthPacket p n j)^7)) :=
      mul_le_mul_of_nonneg_left (burnolSquarePosition_normalized_fourier_cross_bound _ _) (by positivity)
    _ = _ := by
      simp only [primeBurnolTwoDepthPacket_frequency,mul_pow]
      field_simp

theorem primeBurnolTwoDepthCrossBlock_scaled_tendsto (p : Nat.Primes) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) • primeBurnolTwoDepthCrossBlock p n)
      atTop (𝓝 burnolTwoDepthLimitCross) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hjet : Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ)^4 /
      (primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i)*primeBurnolAmplitude (primeBurnolTwoDepthPacket p n j)) *
      ⟪burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n i)),
        fourierUnitary (burnolSquarePosition (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n j)))⟫_ℂ)
        atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => twoDepth_jet_cross_bound p n i j)
    have hi := tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p)
    simpa using (hi.pow 3).const_mul (45/(8*burnolTwoDepthRatio i^7)+45/(8*burnolTwoDepthRatio j^7))
  have h := (twoDepth_fourier_cross_tendsto p i j).add hjet
  rw [add_zero] at h
  convert h using 1
  funext n
  simp only [Matrix.smul_apply,smul_eq_mul,primeBurnolTwoDepthCrossBlock]
  ring

theorem primeBurnolTwoDepthCrossBlock_tendsto (p : Nat.Primes) :
    Tendsto (primeBurnolTwoDepthCrossBlock p) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => ((primeBurnolLogFrequency (p,n) : ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using!
      (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p))
  have h := hi.smul (primeBurnolTwoDepthCrossBlock_scaled_tendsto p)
  rw [zero_smul] at h
  apply h.congr'
  filter_upwards with n
  rw [smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne'),one_smul]

def primeBurnolTwoDepthChannelAmplitude (p : Nat.Primes) (n : ℕ) : Fin 2 ⊕ Fin 2 → ℂ :=
  Sum.elim (fun i => primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i))
    (fun i => primeBurnolAmplitude (primeBurnolTwoDepthPacket p n i))

def primeBurnolTwoDepthNormalizedGram (p : Nat.Primes) (n : ℕ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fun i j => (primeBurnolLogFrequency (p,n) : ℂ)^3 /
    (primeBurnolTwoDepthChannelAmplitude p n i*primeBurnolTwoDepthChannelAmplitude p n j) *
      primeBurnolFourierJetGram (primeBurnolTwoDepthPacket p n) i j

private theorem cross_adjoint (f g : SoninL2) (hg : g ∈ evenSubspace) :
    ⟪fourierUnitary f,g⟫_ℂ=⟪f,fourierUnitary g⟫_ℂ := by
  have h := fourierUnitary.inner_map_map f (fourierUnitary g)
  rwa [fourierUnitary_fourierUnitary_of_mem_evenSubspace hg] at h

private theorem squareColumn_coe (pe : Nat.Primes × ℕ) :
    (primeBurnolSquareColumn pe : SoninL2)=primeBurnolEvenFeatureLp pe := rfl

theorem primeBurnolTwoDepthNormalizedGram_blocks (p : Nat.Primes) (n : ℕ) :
    primeBurnolTwoDepthNormalizedGram p n=
      Matrix.fromBlocks (primeBurnolTwoDepthGramBlock p n) (primeBurnolTwoDepthCrossBlock p n)
        (primeBurnolTwoDepthCrossBlock p n) (primeBurnolTwoDepthGramBlock p n) := by
  have hf (i : Fin 2) := primeBurnolEvenFeatureLp_mem_evenSubspace (primeBurnolTwoDepthPacket p n i)
  have hj (i : Fin 2) := burnolSquarePosition_mem_evenSubspace
    (primeBurnolSquareColumn (primeBurnolTwoDepthPacket p n i)) (hf i)
  ext (i|i) (j|j) <;>
    simp [primeBurnolTwoDepthNormalizedGram,primeBurnolTwoDepthChannelAmplitude,
      primeBurnolFourierJetGram,primeBurnolJetGraphColumn,burnolJetOutputPairing,
      burnolJetGraphVector,primeBurnolFourierJetSynthesis,primeBurnolTwoDepthGramBlock,
      primeBurnolTwoDepthCrossBlock,squareColumn_coe,cross_adjoint _ _ (hf j),cross_adjoint _ _ (hj j)]

def burnolTwoDepthLimitFullGram : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks burnolTwoDepthLimitGram 0 0 burnolTwoDepthLimitGram

theorem primeBurnolTwoDepthNormalizedGram_tendsto (p : Nat.Primes) :
    Tendsto (primeBurnolTwoDepthNormalizedGram p) atTop (𝓝 burnolTwoDepthLimitFullGram) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hG := tendsto_pi_nhds.mp (primeBurnolTwoDepthGramBlock_tendsto p)
  have hH := tendsto_pi_nhds.mp (primeBurnolTwoDepthCrossBlock_tendsto p)
  cases i <;> cases j <;>
    simp only [primeBurnolTwoDepthNormalizedGram_blocks,burnolTwoDepthLimitFullGram,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂]
  · exact tendsto_pi_nhds.mp (hG _) _
  · exact tendsto_pi_nhds.mp (hH _) _
  · exact tendsto_pi_nhds.mp (hH _) _
  · exact tendsto_pi_nhds.mp (hG _) _

theorem burnolTwoDepthLimitGram_isUnit : IsUnit burnolTwoDepthLimitGram := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  norm_num [burnolTwoDepthLimitGram,burnolTwoDepthRatio,Matrix.det_fin_two]

theorem burnolTwoDepthLimitFullGram_isUnit : IsUnit burnolTwoDepthLimitFullGram := by
  rw [Matrix.isUnit_iff_isUnit_det,burnolTwoDepthLimitFullGram,Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp burnolTwoDepthLimitGram_isUnit).mul
    ((Matrix.isUnit_iff_isUnit_det _).mp burnolTwoDepthLimitGram_isUnit)

theorem primeBurnolTwoDepthNormalizedGram_inv_tendsto (p : Nat.Primes) :
    Tendsto (fun n => (primeBurnolTwoDepthNormalizedGram p n)⁻¹) atTop (𝓝 burnolTwoDepthLimitFullGram⁻¹) := by
  apply (continuousAt_matrix_inv burnolTwoDepthLimitFullGram ?_).tendsto.comp
    (primeBurnolTwoDepthNormalizedGram_tendsto p)
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp burnolTwoDepthLimitFullGram_isUnit))

def burnolTwoDepthSingletonScale : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => 8/(burnolTwoDepthRatio i : ℂ))

def burnolTwoDepthLimitRefinement : Matrix (Fin 2) (Fin 2) ℂ :=
  burnolTwoDepthLimitGram⁻¹*burnolTwoDepthLimitCross-burnolTwoDepthSingletonScale

theorem burnolTwoDepthLimitRefinement_source_identity :
    burnolTwoDepthLimitGram*burnolTwoDepthLimitRefinement=!![0,11/27;-5/27,0] := by
  rw [burnolTwoDepthLimitRefinement,mul_sub,← mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp burnolTwoDepthLimitGram_isUnit),one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [burnolTwoDepthLimitCross,burnolTwoDepthLimitGram,burnolTwoDepthSingletonScale,
      burnolTwoDepthRatio,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]

theorem burnolTwoDepthLimitRefinement_isUnit : IsUnit burnolTwoDepthLimitRefinement := by
  rw [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero]
  intro h
  have he := congrArg Matrix.det burnolTwoDepthLimitRefinement_source_identity
  rw [Matrix.det_mul,h,mul_zero] at he
  norm_num [Matrix.det_fin_two] at he

end RHTower
