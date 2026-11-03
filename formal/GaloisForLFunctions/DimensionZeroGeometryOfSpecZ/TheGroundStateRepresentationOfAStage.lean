import GaloisForLFunctions.WindowTowerOfSpecZ.TheTransferAcrossAStage
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheDominationQuestionIsFirstOrder

/-!
# The ground-state representation of a stage

On a window of level `N + 1` crossing the stage `N + 1` adds one collar-to-collar correlation
(`weilQuad_eq_stageForm_sub_corr`, from WTZ's `markovForm_succ`):

`Q(H) = Q_N(H) − 2w c_H(ℓ)`, `ℓ = log(N + 1)`, `w = Λ(N+1)(N+1)^{−1/2}`,

and the correlation lives on the left collar `[−A, −ℓ]` (`corr_eq_intervalIntegral`). For every weight
`φ > 0` on the window the pointwise Doob identity

`−2ab = pq(a/p − b/q)² − (q/p)a² − (p/q)b²`

turns the new fold into a sum of squares of jump differences of `H/φ` minus a potential on the two
collars (`weilQuad_eq_groundState`):

`Q(H) = Q_N(H) − w E_φ(H) + w ∫_{−A}^{−ℓ} φ(u)φ(u+ℓ)(H(u)/φ(u) − H(u+ℓ)/φ(u+ℓ))² du`,

`E_φ(H) = ∫_{−A}^{−ℓ} (φ(u+ℓ)/φ(u))H(u)² du + ∫_{ℓ−A}^{0} (φ(v−ℓ)/φ(v))H(v)² dv` (`foldPotential`).

* `φ ≡ 1` is WTZ's transfer identity (fold energy minus end mass).
* **Weighted transfer criterion** (`weilQuad_nonneg_of_foldPotential_le`): if the previous stage datum pays
  the collar potential of *some* positive weight, `w E_φ(H) ≤ Q_N(H)`, the window is positive on `H`.
  The weight can move the cost between the collars: `φ(u+ℓ)/φ(u)` on the left collar is paid by its
  reciprocal on the right.
* **Losslessness** (`weilQuad_eq_stageForm_sub_foldPotential`): the representation drops nothing on the
  tests whose ratio `H/φ` takes the same value at the two ends of every new fold. Choosing for `φ` a
  ground state of the stage datum makes the payment exact along it; this is the exact form in which a
  supersolution passes a stage: a correction lives only on the two collars and is measured by `E_φ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23 intervalIntegral

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open WindowTowerOfSpecZ CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
open RHTower.WeilMarkovPole

variable {A : ℝ} {H : ℝ → ℝ}

/-- **Crossing a stage adds one collar-to-collar correlation**: `Q(H) = Q_N(H) − 2w c_H(log(N+1))`. -/
theorem weilQuad_eq_stageForm_sub_corr (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) :
    weilQuad H = stageForm N H - 2 * primeJumpWeight (N + 1) * corr H (Real.log (N + 1 : ℕ)) := by
  rw [weilQuad_eq_markovForm_windowLevel hH, hA,
    markovForm_succ hH.continuous hH.hasCompactSupport hN, stageForm, corr]
  ring

/-- The correlation at lag `ℓ ∈ [0, A]` lives on the left collar `[−A, −ℓ]`. -/
theorem corr_eq_intervalIntegral (hH : IsWindowTest A H) {ℓ : ℝ} (hℓA : ℓ ≤ A) :
    corr H ℓ = ∫ u in (-A)..(-ℓ), H u * H (u + ℓ) := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc, corr]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · rw [hH.vanish u fun hm => by linarith [hm.1], zero_mul]
  · rw [hH.vanish (u + ℓ) fun hm => by linarith [hm.2], mul_zero]

/-- The **collar potential of a weight**: `∫_{−A}^{−ℓ}(φ(u+ℓ)/φ(u))H² + ∫_{ℓ−A}^{0}(φ(v−ℓ)/φ(v))H²`. -/
def foldPotential (A ℓ : ℝ) (φ H : ℝ → ℝ) : ℝ :=
  (∫ u in (-A)..(-ℓ), φ (u + ℓ) / φ u * H u ^ 2) +
    ∫ v in (-A + ℓ)..0, φ (v - ℓ) / φ v * H v ^ 2

/-- The **Doob energy of the fold** in the gauge `φ`: `∫_{−A}^{−ℓ}φ(u)φ(u+ℓ)(H/φ(u) − H/φ(u+ℓ))²`. -/
def foldDoobEnergy (A ℓ : ℝ) (φ H : ℝ → ℝ) : ℝ :=
  ∫ u in (-A)..(-ℓ), φ u * φ (u + ℓ) * (H u / φ u - H (u + ℓ) / φ (u + ℓ)) ^ 2

/-- **The fold in a gauge**: `−2c_H(ℓ) = (Doob energy) − (collar potential)` for every weight `φ > 0`
continuous on the window. -/
theorem neg_two_mul_corr_eq (hH : IsWindowTest A H) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓA : ℓ ≤ A)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (-A) 0)) (hφpos : ∀ u ∈ Icc (-A) 0, 0 < φ u) :
    -2 * corr H ℓ = foldDoobEnergy A ℓ φ H - foldPotential A ℓ φ H := by
  have hle : -A ≤ -ℓ := by linarith
  have hI : uIcc (-A) (-ℓ) = Icc (-A) (-ℓ) := uIcc_of_le hle
  have hsub : Icc (-A) (-ℓ) ⊆ Icc (-A) 0 := Icc_subset_Icc le_rfl (by linarith)
  have hmaps : MapsTo (fun u => u + ℓ) (Icc (-A) (-ℓ)) (Icc (-A) 0) :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hφL : ContinuousOn φ (Icc (-A) (-ℓ)) := hφ.mono hsub
  have hφR : ContinuousOn (fun u => φ (u + ℓ)) (Icc (-A) (-ℓ)) :=
    hφ.comp (continuousOn_id.add continuousOn_const) hmaps
  have hne : ∀ u ∈ Icc (-A) (-ℓ), φ u ≠ 0 := fun u hu => (hφpos u (hsub hu)).ne'
  have hne' : ∀ u ∈ Icc (-A) (-ℓ), φ (u + ℓ) ≠ 0 := fun u hu => (hφpos _ (hmaps hu)).ne'
  have hHc := hH.continuous
  have hHs : Continuous fun u => H (u + ℓ) := hHc.comp (continuous_add_const ℓ)
  -- the three pieces are interval integrable
  have i1 : IntervalIntegrable (fun u => φ u * φ (u + ℓ) *
      (H u / φ u - H (u + ℓ) / φ (u + ℓ)) ^ 2) volume (-A) (-ℓ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    exact (hφL.mul hφR).mul (((hHc.continuousOn.div hφL hne).sub
      (hHs.continuousOn.div hφR hne')).pow 2)
  have i2 : IntervalIntegrable (fun u => φ (u + ℓ) / φ u * H u ^ 2) volume (-A) (-ℓ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    exact (hφR.div hφL hne).mul (hHc.continuousOn.pow 2)
  have i3 : IntervalIntegrable (fun u => φ u / φ (u + ℓ) * H (u + ℓ) ^ 2) volume (-A) (-ℓ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    exact (hφL.div hφR hne').mul (hHs.continuousOn.pow 2)
  -- the pointwise Doob identity
  have hpt : ∫ u in (-A)..(-ℓ), -2 * (H u * H (u + ℓ)) =
      ∫ u in (-A)..(-ℓ), (φ u * φ (u + ℓ) * (H u / φ u - H (u + ℓ) / φ (u + ℓ)) ^ 2 -
        φ (u + ℓ) / φ u * H u ^ 2 - φ u / φ (u + ℓ) * H (u + ℓ) ^ 2) := by
    refine integral_congr fun u hu => ?_
    rw [hI] at hu
    have hp := hne u hu
    have hq := hne' u hu
    field_simp
    ring
  -- the right-collar term, moved by `ℓ`
  have hshift : ∫ u in (-A)..(-ℓ), φ u / φ (u + ℓ) * H (u + ℓ) ^ 2 =
      ∫ v in (-A + ℓ)..0, φ (v - ℓ) / φ v * H v ^ 2 := by
    have := intervalIntegral.integral_comp_add_right
      (fun v => φ (v - ℓ) / φ v * H v ^ 2) (a := -A) (b := -ℓ) ℓ
    simp only [add_sub_cancel_right, neg_add_cancel] at this
    exact this
  rw [corr_eq_intervalIntegral hH hℓA, ← intervalIntegral.integral_const_mul, hpt,
    intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2, hshift,
    foldDoobEnergy, foldPotential]
  ring

/-- `log(N+1) ≤ A` on a window of level `N + 1`. -/
theorem log_succ_le_of_windowLevel {N : ℕ} (hA : windowLevel A = N + 1) :
    Real.log (N + 1 : ℕ) ≤ A := by
  have hmem : N + 1 ∈ Finset.Icc 1 (windowLevel A) := Finset.mem_Icc.mpr ⟨by omega, hA.ge⟩
  exact (log_le_of_mem_Icc_one hmem).2

/-- **The ground-state representation of a stage.** On a window of level `N + 1`, for every weight
`φ > 0` continuous on the window,
`Q(H) = Q_N(H) − w E_φ(H) + w·(Doob energy of the fold in the gauge φ)`. -/
theorem weilQuad_eq_groundState (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (-A) 0))
    (hφpos : ∀ u ∈ Icc (-A) 0, 0 < φ u) :
    weilQuad H = stageForm N H - primeJumpWeight (N + 1) * foldPotential A (Real.log (N + 1 : ℕ)) φ H +
      primeJumpWeight (N + 1) * foldDoobEnergy A (Real.log (N + 1 : ℕ)) φ H := by
  have h := neg_two_mul_corr_eq hH (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 1)))
    (log_succ_le_of_windowLevel hA) hφ hφpos
  rw [weilQuad_eq_stageForm_sub_corr hH hN hA]
  linear_combination primeJumpWeight (N + 1) * h

theorem foldDoobEnergy_nonneg (A ℓ : ℝ) (hℓA : ℓ ≤ A) (φ H : ℝ → ℝ)
    (hφpos : ∀ u ∈ Icc (-A) 0, 0 < φ u) (hℓ : 0 ≤ ℓ) : 0 ≤ foldDoobEnergy A ℓ φ H := by
  refine intervalIntegral.integral_nonneg (by linarith) fun u hu => ?_
  exact mul_nonneg (mul_nonneg (hφpos u ⟨hu.1, by linarith [hu.2]⟩).le
    (hφpos (u + ℓ) ⟨by linarith [hu.1], by linarith [hu.2]⟩).le) (sq_nonneg _)

/-- **Weighted transfer criterion**: if the previous stage datum pays the collar potential of some
positive weight, the window of the next stage is positive on the test. -/
theorem weilQuad_nonneg_of_foldPotential_le (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (-A) 0))
    (hφpos : ∀ u ∈ Icc (-A) 0, 0 < φ u)
    (hpay : primeJumpWeight (N + 1) * foldPotential A (Real.log (N + 1 : ℕ)) φ H ≤ stageForm N H) :
    0 ≤ weilQuad H := by
  rw [weilQuad_eq_groundState hH hN hA hφ hφpos]
  have := foldDoobEnergy_nonneg A _ (log_succ_le_of_windowLevel hA) φ H hφpos
    (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 1)))
  have := primeJumpWeight_nonneg (N + 1)
  nlinarith

/-- **Losslessness**: when `H/φ` takes the same value at the two ends of every new fold, the
weighted transfer is an identity, `Q(H) = Q_N(H) − w E_φ(H)`. -/
theorem weilQuad_eq_stageForm_sub_foldPotential (hH : IsWindowTest A H) {N : ℕ} (hN : 1 ≤ N)
    (hA : windowLevel A = N + 1) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (-A) 0))
    (hφpos : ∀ u ∈ Icc (-A) 0, 0 < φ u)
    (hmatch : ∀ u ∈ Icc (-A) (-Real.log (N + 1 : ℕ)),
      H u / φ u = H (u + Real.log (N + 1 : ℕ)) / φ (u + Real.log (N + 1 : ℕ))) :
    weilQuad H = stageForm N H -
      primeJumpWeight (N + 1) * foldPotential A (Real.log (N + 1 : ℕ)) φ H := by
  have hD : foldDoobEnergy A (Real.log (N + 1 : ℕ)) φ H = 0 := by
    rw [foldDoobEnergy]
    have hle : -A ≤ -Real.log (N + 1 : ℕ) := by linarith [log_succ_le_of_windowLevel hA]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => by
      rw [uIcc_of_le hle] at hu
      simp only [hmatch u hu, sub_self]
      ring]
    simp
  rw [weilQuad_eq_groundState hH hN hA hφ hφpos, hD, mul_zero, add_zero]

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
