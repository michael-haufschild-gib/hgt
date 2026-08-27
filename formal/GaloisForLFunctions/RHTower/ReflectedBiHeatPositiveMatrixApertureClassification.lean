import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityLeadingJetBalance

/-!
# Reflected bi-heat positive-matrix aperture classification

At arbitrary apertures `x > 1`, multiplicity-leading left and right bi-heat jet norms have a
common nonzero coefficient and respective powers `x ^ ((Re rho - 1) / 2)` and
`x ^ (-Re rho / 2)`.  Strict monotonicity of real powers therefore orients every aperture in the
same direction away from the critical wall.

This file proves the stronger finite cross-aperture statement: every nonzero entrywise-nonnegative
matrix aggregate has strictly signed left-minus-right gap off the wall and balances exactly on it.
Thus positive finite cross-aperture mixing remains an exact RH receiver, not a source-first proof.

`[NEW] [CLASSIFICATION] [NO-GO] [EXACT RECEIVER] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Norm of the left multiplicity-leading bi-heat jet at aperture `x`. -/
def reflectedBiHeatLeftLeadingJetNorm (rho : XiDivisorSupport) (x : ℝ) : ℝ :=
  ‖iteratedDeriv (xiSupportMultiplicity rho)
      (reflectedBiHeatLeftResponse x) (rho : ℂ)‖

/-- Norm of the right multiplicity-leading bi-heat jet at aperture `x`. -/
def reflectedBiHeatRightLeadingJetNorm (rho : XiDivisorSupport) (x : ℝ) : ℝ :=
  ‖iteratedDeriv (xiSupportMultiplicity rho)
      (reflectedBiHeatRightResponse x) (rho : ℂ)‖

/-- Exact left leading-jet norm at every positive aperture. -/
theorem reflectedBiHeatLeftLeadingJetNorm_eq
    (rho : XiDivisorSupport) {x : ℝ} (hx : 0 < x) :
    reflectedBiHeatLeftLeadingJetNorm rho x =
      ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
        x ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) := by
  rw [reflectedBiHeatLeftLeadingJetNorm,
    iteratedDeriv_reflectedBiHeatLeftResponse_at_supportMultiplicity hx]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp [reflectedBiHeatLeftScaleOrder]

/-- Exact right leading-jet norm at every positive aperture. -/
theorem reflectedBiHeatRightLeadingJetNorm_eq
    (rho : XiDivisorSupport) {x : ℝ} (hx : 0 < x) :
    reflectedBiHeatRightLeadingJetNorm rho x =
      ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
        x ^ reflectedBiHeatRightScaleOrder (rho : ℂ) := by
  rw [reflectedBiHeatRightLeadingJetNorm,
    iteratedDeriv_reflectedBiHeatRightResponse_at_supportMultiplicity hx]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp [reflectedBiHeatRightScaleOrder]

/-- Above the critical wall, every aperture `x > 1` makes the left norm strictly larger. -/
theorem reflectedBiHeatRightLeadingJetNorm_lt_left
    (rho : XiDivisorSupport) {x : ℝ} (hx : 1 < x)
    (hre : 1 / 2 < (rho : ℂ).re) :
    reflectedBiHeatRightLeadingJetNorm rho x <
      reflectedBiHeatLeftLeadingJetNorm rho x := by
  rw [reflectedBiHeatLeftLeadingJetNorm_eq rho (lt_trans zero_lt_one hx),
    reflectedBiHeatRightLeadingJetNorm_eq rho (lt_trans zero_lt_one hx)]
  have hcoef : 0 < ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ :=
    norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  apply mul_lt_mul_of_pos_left _ hcoef
  apply Real.strictMono_rpow_of_base_gt_one hx
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  linarith

/-- Below the critical wall, every aperture `x > 1` makes the right norm strictly larger. -/
theorem reflectedBiHeatLeftLeadingJetNorm_lt_right
    (rho : XiDivisorSupport) {x : ℝ} (hx : 1 < x)
    (hre : (rho : ℂ).re < 1 / 2) :
    reflectedBiHeatLeftLeadingJetNorm rho x <
      reflectedBiHeatRightLeadingJetNorm rho x := by
  rw [reflectedBiHeatLeftLeadingJetNorm_eq rho (lt_trans zero_lt_one hx),
    reflectedBiHeatRightLeadingJetNorm_eq rho (lt_trans zero_lt_one hx)]
  have hcoef : 0 < ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ :=
    norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  apply mul_lt_mul_of_pos_left _ hcoef
  apply Real.strictMono_rpow_of_base_gt_one hx
  rw [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  linarith

/-- At any aperture `x > 1`, the two leading-jet norms balance exactly on the wall. -/
theorem reflectedBiHeatLeadingJetNorms_eq_iff
    (rho : XiDivisorSupport) {x : ℝ} (hx : 1 < x) :
    reflectedBiHeatLeftLeadingJetNorm rho x =
        reflectedBiHeatRightLeadingJetNorm rho x ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatLeftLeadingJetNorm_eq rho (lt_trans zero_lt_one hx),
    reflectedBiHeatRightLeadingJetNorm_eq rho (lt_trans zero_lt_one hx)]
  have hcoef : 0 < ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ :=
    norm_pos_iff.mpr (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)
  constructor
  · intro h
    have hpowers : x ^ reflectedBiHeatLeftScaleOrder (rho : ℂ) =
        x ^ reflectedBiHeatRightScaleOrder (rho : ℂ) :=
      mul_left_cancel₀ hcoef.ne' h
    have horders := (Real.strictMono_rpow_of_base_gt_one hx).injective hpowers
    exact (reflectedBiHeat_scaleOrders_eq_iff (rho : ℂ)).mp horders
  · intro hre
    rw [(reflectedBiHeat_scaleOrders_eq_iff (rho : ℂ)).mpr hre]

/-- Entrywise-positive finite matrix self-interactions strictly preserve pointwise positive order. -/
theorem finite_positiveMatrix_selfInteraction_lt
    {N : ℕ} {M : Fin N → Fin N → ℝ} {a b : Fin N → ℝ}
    (hapos : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hMnonneg : ∀ i j, 0 ≤ M i j) (hMpos : ∃ i j, 0 < M i j) :
    (∑ i, ∑ j, M i j * a i * a j) <
      ∑ i, ∑ j, M i j * b i * b j := by
  rw [← sub_pos]
  simp_rw [← Finset.sum_sub_distrib]
  obtain ⟨i0, j0, hMij⟩ := hMpos
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    have hpair : a i * a j < b i * b j := calc
      a i * a j < b i * a j := mul_lt_mul_of_pos_right (hab i) (hapos j)
      _ < b i * b j := mul_lt_mul_of_pos_left (hab j) (lt_trans (hapos i) (hab i))
    exact sub_nonneg.mpr <| by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hpair.le (hMnonneg i j)
  · refine ⟨i0, Finset.mem_univ i0, ?_⟩
    apply Finset.sum_pos'
    · intro j _
      have hpair : a i0 * a j < b i0 * b j := calc
        a i0 * a j < b i0 * a j := mul_lt_mul_of_pos_right (hab i0) (hapos j)
        _ < b i0 * b j := mul_lt_mul_of_pos_left (hab j) (lt_trans (hapos i0) (hab i0))
      exact sub_nonneg.mpr <| by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hpair.le (hMnonneg i0 j)
    · refine ⟨j0, Finset.mem_univ j0, ?_⟩
      have hpair : a i0 * a j0 < b i0 * b j0 := calc
        a i0 * a j0 < b i0 * a j0 := mul_lt_mul_of_pos_right (hab i0) (hapos j0)
        _ < b i0 * b j0 :=
          mul_lt_mul_of_pos_left (hab j0) (lt_trans (hapos i0) (hab i0))
      exact sub_pos.mpr <| by
        simpa [mul_assoc] using mul_lt_mul_of_pos_left hpair hMij

/-- Finite matrix aggregate of left leading-jet norms across apertures. -/
def reflectedBiHeatLeftMatrixApertureEnergy
    {N : ℕ} (M : Fin N → Fin N → ℝ) (x : Fin N → ℝ)
    (rho : XiDivisorSupport) : ℝ :=
  ∑ i, ∑ j, M i j * reflectedBiHeatLeftLeadingJetNorm rho (x i) *
    reflectedBiHeatLeftLeadingJetNorm rho (x j)

/-- Finite matrix aggregate of right leading-jet norms across apertures. -/
def reflectedBiHeatRightMatrixApertureEnergy
    {N : ℕ} (M : Fin N → Fin N → ℝ) (x : Fin N → ℝ)
    (rho : XiDivisorSupport) : ℝ :=
  ∑ i, ∑ j, M i j * reflectedBiHeatRightLeadingJetNorm rho (x i) *
    reflectedBiHeatRightLeadingJetNorm rho (x j)

/-- Left-minus-right finite matrix aperture gap. -/
def reflectedBiHeatMatrixApertureGap
    {N : ℕ} (M : Fin N → Fin N → ℝ) (x : Fin N → ℝ)
    (rho : XiDivisorSupport) : ℝ :=
  ∑ i, ∑ j, M i j *
    (reflectedBiHeatLeftLeadingJetNorm rho (x i) *
        reflectedBiHeatLeftLeadingJetNorm rho (x j) -
      reflectedBiHeatRightLeadingJetNorm rho (x i) *
        reflectedBiHeatRightLeadingJetNorm rho (x j))

/-- The explicit aperture gap is the difference of the two matrix energies. -/
theorem reflectedBiHeatMatrixApertureGap_eq_sub
    {N : ℕ} (M : Fin N → Fin N → ℝ) (x : Fin N → ℝ)
    (rho : XiDivisorSupport) :
    reflectedBiHeatMatrixApertureGap M x rho =
      reflectedBiHeatLeftMatrixApertureEnergy M x rho -
        reflectedBiHeatRightMatrixApertureEnergy M x rho := by
  rw [reflectedBiHeatMatrixApertureGap,
    reflectedBiHeatLeftMatrixApertureEnergy,
    reflectedBiHeatRightMatrixApertureEnergy]
  simp_rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Above the wall, every nonzero positive matrix aperture gap is strictly positive. -/
theorem reflectedBiHeatMatrixApertureGap_pos_of_re_gt_half
    {N : ℕ} {M : Fin N → Fin N → ℝ} {x : Fin N → ℝ}
    (rho : XiDivisorSupport) (hx : ∀ i, 1 < x i)
    (hMnonneg : ∀ i j, 0 ≤ M i j) (hMpos : ∃ i j, 0 < M i j)
    (hre : 1 / 2 < (rho : ℂ).re) :
    0 < reflectedBiHeatMatrixApertureGap M x rho := by
  rw [reflectedBiHeatMatrixApertureGap_eq_sub]
  exact sub_pos.mpr <| finite_positiveMatrix_selfInteraction_lt
    (fun i => by
      rw [reflectedBiHeatRightLeadingJetNorm]
      exact norm_pos_iff.mpr
        (iteratedDeriv_reflectedBiHeatRightResponse_ne_zero_at_supportMultiplicity
          (lt_trans zero_lt_one (hx i)) rho))
    (fun i => reflectedBiHeatRightLeadingJetNorm_lt_left rho (hx i) hre)
    hMnonneg hMpos

/-- Below the wall, every nonzero positive matrix aperture gap is strictly negative. -/
theorem reflectedBiHeatMatrixApertureGap_neg_of_re_lt_half
    {N : ℕ} {M : Fin N → Fin N → ℝ} {x : Fin N → ℝ}
    (rho : XiDivisorSupport) (hx : ∀ i, 1 < x i)
    (hMnonneg : ∀ i j, 0 ≤ M i j) (hMpos : ∃ i j, 0 < M i j)
    (hre : (rho : ℂ).re < 1 / 2) :
    reflectedBiHeatMatrixApertureGap M x rho < 0 := by
  rw [reflectedBiHeatMatrixApertureGap_eq_sub]
  exact sub_neg.mpr <| finite_positiveMatrix_selfInteraction_lt
    (fun i => by
      rw [reflectedBiHeatLeftLeadingJetNorm]
      exact norm_pos_iff.mpr
        (iteratedDeriv_reflectedBiHeatLeftResponse_ne_zero_at_supportMultiplicity
          (lt_trans zero_lt_one (hx i)) rho))
    (fun i => reflectedBiHeatLeftLeadingJetNorm_lt_right rho (hx i) hre)
    hMnonneg hMpos

/-- Positive finite matrix aperture energies balance exactly on the critical wall. -/
theorem reflectedBiHeatMatrixApertureEnergies_eq_iff
    {N : ℕ} {M : Fin N → Fin N → ℝ} {x : Fin N → ℝ}
    (rho : XiDivisorSupport) (hx : ∀ i, 1 < x i)
    (hMnonneg : ∀ i j, 0 ≤ M i j) (hMpos : ∃ i j, 0 < M i j) :
    reflectedBiHeatLeftMatrixApertureEnergy M x rho =
        reflectedBiHeatRightMatrixApertureEnergy M x rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro heq
    by_contra hwall
    rcases lt_or_gt_of_ne hwall with hre | hre
    · have hneg := reflectedBiHeatMatrixApertureGap_neg_of_re_lt_half
        rho hx hMnonneg hMpos hre
      rw [reflectedBiHeatMatrixApertureGap_eq_sub, heq, sub_self] at hneg
      exact lt_irrefl 0 hneg
    · have hpos := reflectedBiHeatMatrixApertureGap_pos_of_re_gt_half
        rho hx hMnonneg hMpos hre
      rw [reflectedBiHeatMatrixApertureGap_eq_sub, heq, sub_self] at hpos
      exact lt_irrefl 0 hpos
  · intro hre
    rw [reflectedBiHeatLeftMatrixApertureEnergy,
      reflectedBiHeatRightMatrixApertureEnergy]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(reflectedBiHeatLeadingJetNorms_eq_iff rho (hx i)).mpr hre,
      (reflectedBiHeatLeadingJetNorms_eq_iff rho (hx j)).mpr hre]

/-- Universal positive-matrix cross-aperture balance on Xi support is exactly RH. -/
theorem riemannHypothesis_iff_reflectedBiHeatPositiveMatrixApertureEnergy_eq
    {N : ℕ} {M : Fin N → Fin N → ℝ} {x : Fin N → ℝ}
    (hx : ∀ i, 1 < x i)
    (hMnonneg : ∀ i j, 0 ≤ M i j) (hMpos : ∃ i j, 0 < M i j) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatLeftMatrixApertureEnergy M x rho =
          reflectedBiHeatRightMatrixApertureEnergy M x rho := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatMatrixApertureEnergies_eq_iff
      rho hx hMnonneg hMpos).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatMatrixApertureEnergies_eq_iff
        rho hx hMnonneg hMpos).mp (h rho)

end

end RHTower
