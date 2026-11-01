import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfRightZeros
import GaloisForLFunctions.SquareRootThreshold.TwoBumpLagStructureLaw

/-!
# Immediate visibility above the lattice Nyquist aperture

A difference of translates separated by the lattice period kills every on-line
Fourier sample. Fixed-support interpolation assigns opposite values at the
off-line pair, producing Weil energy exactly `-2` at every aperture above `L/2`.
-/

noncomputable section
set_option autoImplicit false
open Complex Set
open scoped ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private def latticeDifferenceFactor (L : ℝ) (z : ℂ) : ℂ :=
  exp (-(I * z * (L / 2))) - exp (I * z * (L / 2))

private theorem latticeDifferenceFactor_ne_zero {L : ℝ} (hL : 0 < L)
    {z : ℂ} (hz : z.im ≠ 0) : latticeDifferenceFactor L z ≠ 0 := by
  intro h
  have hh := congrArg norm (sub_eq_zero.mp h)
  simp only [norm_exp, neg_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, zero_sub, div_ofNat_re, div_ofNat_im] at hh
  have he := Real.exp_injective hh
  apply mul_ne_zero hz hL.ne'
  linarith only [he]

private theorem latticeDifferenceFactor_lattice {L : ℝ} (hL : 0 < L) (k : ℤ) :
    latticeDifferenceFactor L ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ)) = 0 := by
  apply sub_eq_zero.mpr
  apply exp_eq_exp_iff_exists_int.mpr
  refine ⟨-k, ?_⟩
  push_cast
  have hLc : (L : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL.ne'
  field_simp [hLc]
  ring

/-- A lattice-null test of arbitrarily small excess aperture has exact pair energy `-2`. -/
theorem exists_isolatedPair_test_eq_neg_two_above_nyquist {L δ a : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ : ℝ) (ha : L / 2 < a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (isolatedPairConfig hL hδ hδ' γ).W f f = -2 := by
  let w := a - L / 2
  have hw : 0 < w := sub_pos.mpr ha
  let z : Fin 2 → ℂ := ![(γ : ℂ) - I * δ, (γ : ℂ) + I * δ]
  have hz : Function.Injective z := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hh := congrArg Complex.im hij
      simp [z] at hh
      linarith only [hh, hδ]
    · have hh := congrArg Complex.im hij
      simp [z] at hh
      linarith only [hh, hδ]
    · rfl
  have hD0 : latticeDifferenceFactor L (z 0) ≠ 0 :=
    latticeDifferenceFactor_ne_zero hL (by simp [z, hδ.ne'])
  have hD1 : latticeDifferenceFactor L (z 1) ≠ 0 :=
    latticeDifferenceFactor_ne_zero hL (by simp [z, hδ.ne'])
  let val : Fin 2 → ℂ := ![(latticeDifferenceFactor L (z 0))⁻¹,
    -(latticeDifferenceFactor L (z 1))⁻¹]
  obtain ⟨b, hb, hbs, hbval⟩ := exists_test_interpolating_Icc hw z hz val
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hbs
  have hbabs : ∀ u, b u ≠ 0 → |u| ≤ w := by
    intro u hu
    exact abs_le.mpr (hbs (subset_tsupport b hu))
  let f := twoBump b L (-1)
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest hb L ![1, -1]
  have hfs : tsupport f ⊆ Icc (-a) a :=
    tsupport_bumpTest_subset hbabs hL.le (n := 2) (by dsimp only [w]; norm_num; linarith) ![1, -1]
  have hFT (s : ℂ) : paperFT f s = latticeDifferenceFactor L s * paperFT b s := by
    rw [paperFT_twoBump hb.continuous hbc]
    simp only [latticeDifferenceFactor, neg_one_mul, sub_eq_add_neg]
  have hminus : paperFT f ((γ : ℂ) - I * δ) = 1 := by
    change paperFT f (z 0) = 1
    rw [hFT, hbval 0]
    exact mul_inv_cancel₀ hD0
  have hplus : paperFT f ((γ : ℂ) + I * δ) = -1 := by
    change paperFT f (z 1) = -1
    rw [hFT, hbval 1]
    change latticeDifferenceFactor L (z 1) * -(latticeDifferenceFactor L (z 1))⁻¹ = -1
    rw [mul_neg, mul_inv_cancel₀ hD1]
  have hlattice (k : ℤ) : paperFT f (gammaOf (verticalLatticePoint L 0 k)) = 0 := by
    rw [gammaOf_verticalLatticePoint]
    simp only [ofReal_zero, mul_zero, sub_zero]
    rw [hFT, latticeDifferenceFactor_lattice hL k, zero_mul]
  let Z := isolatedPairConfig hL hδ hδ' γ
  have hsum0 : HasSum (fun ρ : range (verticalLatticePoint L 0) => Z.Wsummand f f ρ) 0 := by
    convert (hasSum_zero : HasSum (fun _ : range (verticalLatticePoint L 0) => (0 : ℂ)) 0) using 1
    funext ρ
    obtain ⟨k, hk⟩ := ρ.2
    rw [← hk, ZeroConfig.Wsummand, hlattice, mul_zero, zero_mul]
  have hconjminus : conj ((γ : ℂ) - I * δ) = (γ : ℂ) + I * δ := by simp
  have hconjplus : conj ((γ : ℂ) + I * δ) = (γ : ℂ) - I * δ := by simp [sub_eq_add_neg]
  have hmultminus : Z.mult (offLinePoint δ γ) = 1 := by
    change (if (offLinePoint δ γ).re = 1 / 2 then 2 else 1) = 1
    rw [if_neg (by simp only [offLinePoint]; linarith only [hδ])]
  have hmultplus : Z.mult (offLinePoint (-δ) γ) = 1 := by
    change (if (offLinePoint (-δ) γ).re = 1 / 2 then 2 else 1) = 1
    rw [if_neg (by simp only [offLinePoint]; linarith only [hδ])]
  have htermminus : Z.Wsummand f f (offLinePoint δ γ) = -1 := by
    rw [ZeroConfig.Wsummand, hmultminus, gammaOf_offLinePoint, hconjminus, hminus, hplus]
    norm_num
  have htermplus : Z.Wsummand f f (offLinePoint (-δ) γ) = -1 := by
    rw [ZeroConfig.Wsummand, hmultplus, gammaOf_offLinePoint]
    simp only [ofReal_neg, mul_neg, sub_neg_eq_add]
    rw [hconjplus, hminus, hplus]
    norm_num
  have hp := hasSum_singleton (offLinePoint δ γ) (Z.Wsummand f f)
  have hq := hasSum_singleton (offLinePoint (-δ) γ) (Z.Wsummand f f)
  rw [htermminus] at hp
  rw [htermplus] at hq
  have hd₁ : Disjoint (range (verticalLatticePoint L 0)) {offLinePoint δ γ} := by
    rw [disjoint_singleton_right]
    rintro ⟨k, hk⟩
    have hh := congrArg Complex.re hk
    simp only [verticalLatticePoint, offLinePoint] at hh
    linarith only [hh, hδ]
  have hd₂ : Disjoint (range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ})
      {offLinePoint (-δ) γ} := by
    rw [disjoint_singleton_right]
    rintro (⟨k, hk⟩ | hk)
    · have hh := congrArg Complex.re hk
      simp only [verticalLatticePoint, offLinePoint] at hh
      linarith only [hh, hδ]
    · rw [mem_singleton_iff] at hk
      have hh := congrArg Complex.re hk
      simp only [offLinePoint] at hh
      linarith only [hh, hδ]
  have hall := HasSum.add_disjoint (f := Z.Wsummand f f) hd₂
    (HasSum.add_disjoint (f := Z.Wsummand f f) hd₁ hsum0 hp) hq
  refine ⟨f, hf, hfs, ?_⟩
  change Z.W f f = -2
  rw [ZeroConfig.W]
  have hsum := hall.tsum_eq
  norm_num at hsum
  exact hsum

/-- Every aperture strictly beyond Nyquist detects the pair, regardless of its depth. -/
theorem hodgeDefectAt_isolatedPair_eq_one_of_nyquist_lt {L δ a : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ : ℝ) (ha : L / 2 < a) :
    hodgeDefectAt (isolatedPairConfig hL hδ hδ' γ) a = 1 := by
  obtain ⟨f, hf, hfs, hW⟩ := exists_isolatedPair_test_eq_neg_two_above_nyquist hL hδ hδ' γ ha
  have hZ := temperedConfig_isolatedPairConfig hL hδ hδ' γ
  have hne : hodgeDefectAt (isolatedPairConfig hL hδ hδ' γ) a ≠ 0 := by
    intro hzero
    have hh := (hodgeDefectAt_eq_zero_iff _ hZ a).mp hzero f hf hfs
    rw [hW] at hh
    norm_num at hh
  exact le_antisymm
    ((hodgeDefectAt_le _ hZ a).trans_eq (encard_rightZeros_isolatedPair hL hδ hδ' γ))
    (Order.one_le_iff_ne_zero.mpr hne)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_isolatedPair_test_eq_neg_two_above_nyquist
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.hodgeDefectAt_isolatedPair_eq_one_of_nyquist_lt
