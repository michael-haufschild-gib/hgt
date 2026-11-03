import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ

/-!
# Margins are bounded by recurrence

The margin `E_p` of a lattice window is the minimum of the Toeplitz form over vectors with first
coordinate `1`; testing it on `e_0 − e_p` gives an exact upper bound by the **recurrence defect** of
the sequence (`levinsonErr_le_recurrence`):

`E_p ≤ T_{p+1}(e_0 − e_p) = 2(κ(0) − κ(p))`.

For Spec ℤ (`levinsonErr_weilSeq_le`): `E_p(φ, h) ≤ Q(φ − φ(· + ph))`, the Weil energy of the
difference between a bump and its translate by `ph` — the Hasse–Weil defect of the orbit of `φ` at
scale `ph` (AOG). The margins of the lattice canonical system therefore collapse along every
sequence of steps at which the orbit correlation of `φ` returns to its value at `0`: exact margin
collapse is recurrence of the orbit correlation. Under RH the orbit correlation is the almost
periodic sum `Σ_γ |φ̂(γ)|²e^{iphγ}`, which recurs; the margins of every lattice of Spec ℤ then tend
to `0`, which is the no-slack wall in the language of growing windows.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri

variable {κ : ℤ → ℝ}

/-- The vector `(0, …, 0, c)` of size `m + 1` has Toeplitz energy `κ(0)c²`. -/
theorem toeplitzForm_snoc_zero (m : ℕ) (c : ℝ) :
    toeplitzForm κ (m + 1) (Fin.snoc (fun _ : Fin m => (0 : ℝ)) c) = κ 0 * c ^ 2 := by
  simp only [toeplitzForm, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, mul_zero,
    zero_mul, sum_const_zero, zero_add, sub_self]
  ring

/-- **The recurrence test**: `T_{p+1}(e_0 − e_p) = 2(κ(0) − κ(p))` for `p ≥ 1`. -/
theorem toeplitzForm_recurrence (hκ : IsEvenSeq κ) (m : ℕ) :
    toeplitzForm κ (m + 2) (Fin.cons 1 (Fin.snoc (fun _ : Fin m => (0 : ℝ)) (-1))) =
      2 * κ 0 - 2 * κ ((m : ℤ) + 1) := by
  rw [toeplitzForm_cons_expand hκ, toeplitzForm_snoc_zero, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, sum_const_zero, zero_add, Fin.val_last]
  ring

/-- **Margins are bounded by recurrence**: if the lattice window of size `m + 1` is positive definite,
`E_{m+1} ≤ 2(κ(0) − κ(m + 1))`. -/
theorem levinsonErr_le_recurrence (hκ : IsEvenSeq κ) {m : ℕ} (hpd : ToeplitzPosDef κ (m + 1)) :
    levinsonErr κ (m + 1) ≤ 2 * κ 0 - 2 * κ ((m : ℤ) + 1) := by
  have hlow := (toeplitzForm_posDef_iff hκ m).mp hpd
  have hne : ∀ k < m + 1, levinsonErr κ k ≠ 0 := fun k hk => (hlow k (by omega)).ne'
  have hp := levinson_isPredictor hκ hne
  rw [← toeplitzForm_recurrence hκ m, toeplitzForm_cons hκ hp, predErr_levinson hκ hne, one_pow,
    mul_one]
  have hnn : 0 ≤ toeplitzForm κ (m + 1) (fun k => (Fin.snoc (fun _ : Fin m => (0 : ℝ)) (-1) :
      Fin (m + 1) → ℝ) k - 1 * levinsonPred κ (m + 1) k) := by
    by_cases h0 : (fun k => (Fin.snoc (fun _ : Fin m => (0 : ℝ)) (-1) : Fin (m + 1) → ℝ) k -
        1 * levinsonPred κ (m + 1) k) = 0
    · rw [h0]; simp [toeplitzForm]
    · exact (hpd _ h0).le
  linarith

/-- The recurrence defect of a Weil sequence is the Weil energy of a Frobenius difference:
`2(κ(0) − κ(p)) = Q(φ − φ(· + ph))`. -/
theorem two_mul_weilSeq_sub (hφ : φ ∈ realTests) (h : ℝ) (p : ℤ) :
    2 * weilSeq φ h 0 - 2 * weilSeq φ h p = weilQuad (fun u => 1 * φ u + -1 * latticeTranslate φ h p u) := by
  rw [weilQuad_plane hφ (latticeTranslate_mem hφ h p)]
  have hQ : weilQuad (latticeTranslate φ h p) = weilQuad φ := by
    have := weilQuad_comp_sub φ (-((p : ℝ) * h))
    simp only [sub_neg_eq_add] at this
    exact this
  rw [hQ]
  simp only [weilSeq, latticeTranslate_zero]
  show 2 * weilQuad φ - 2 * weilPair φ (latticeTranslate φ h p) = _
  ring

/-- **The margins of Spec ℤ are bounded by the Hasse–Weil defect of the orbit**: if the lattice
window of size `m + 1` is positive definite, `E_{m+1}(φ, h) ≤ Q(φ − φ(· + (m + 1)h))`. -/
theorem levinsonErr_weilSeq_le (hφ : φ ∈ realTests) {h : ℝ} {m : ℕ}
    (hpd : ToeplitzPosDef (weilSeq φ h) (m + 1)) :
    levinsonErr (weilSeq φ h) (m + 1) ≤
      weilQuad (fun u => 1 * φ u + -1 * latticeTranslate φ h ((m : ℤ) + 1) u) := by
  rw [← two_mul_weilSeq_sub hφ h]
  exact levinsonErr_le_recurrence (weilSeq_isEven φ h) hpd

end GaloisForLFunctions.GrowingWindowsOfSpecZ
