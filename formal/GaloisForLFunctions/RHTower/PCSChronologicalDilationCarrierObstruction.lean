import GaloisForLFunctions.RHTower.PrimeCoShiftKernelProjection
import GaloisForLFunctions.HTGeometry.HalfLineMellinMultiplier

/-!
# PCS shifts and the actual chronological dilation carrier

The unilateral prime shift has a nonzero defect. Its native intertwining identification with invertible physical dilation is impossible. The physical logarithmic and Mellin isometries, and the exact shift/defect decomposition, survive unconditionally.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section


namespace RHTower.PrimeCoShift

private theorem pnat_not_dvd_one (p : ℕ+) (hp : 1 < (p : ℕ)) : ¬ (p : ℕ) ∣ 1 := by
  intro h
  have := Nat.dvd_one.mp h
  omega

theorem primeShift_not_surjective (p : ℕ+) (hp : 1 < (p : ℕ)) :
    ¬ Function.Surjective (primeShift p) := by
  intro h
  obtain ⟨x, hx⟩ := h (lp.single 2 (1 : ℕ+) (1 : ℂ))
  have hc := congrArg (fun y : H => y 1) hx
  have hz := Vop_apply_of_not_dvd p x 1 (pnat_not_dvd_one p hp)
  change primeShift p x 1 = 0 at hz
  rw [hz, lp.single_apply_self] at hc
  exact zero_ne_one hc

theorem primeCoShift_basis_one (p : ℕ+) (hp : 1 < (p : ℕ)) :
    primeCoShift p (lp.single 2 (1 : ℕ+) (1 : ℂ)) = 0 := by
  apply lp.ext
  funext n
  rw [primeCoShift_apply, lp.single_apply_ne]
  · rfl
  · intro h
    apply pnat_not_dvd_one p hp
    exact ⟨(n : ℕ), congrArg (fun z : ℕ+ => (z : ℕ)) h.symm⟩

theorem primeCoShift_not_injective (p : ℕ+) (hp : 1 < (p : ℕ)) :
    ¬ Function.Injective (primeCoShift p) := by
  intro hi
  have he := hi ((primeCoShift_basis_one p hp).trans (map_zero (primeCoShift p)).symm)
  have hc := congrArg (fun y : H => y 1) he
  rw [lp.single_apply_self] at hc
  change (1 : ℂ) = 0 at hc
  exact one_ne_zero hc

/-- The omitted PCS sector is a concrete nonzero projection, not a missing coordinate convention. -/
theorem Eop_basis_one (p : ℕ+) (hp : 1 < (p : ℕ)) :
    Eop p (lp.single 2 (1 : ℕ+) (1 : ℂ)) = lp.single 2 1 1 := by
  change _ - Vop p (primeCoShift p (lp.single 2 (1 : ℕ+) (1 : ℂ))) = _
  rw [primeCoShift_basis_one p hp, map_zero, sub_zero]
  rfl

theorem source_eq_shift_add_defect (p : ℕ+) (x : H) :
    x = primeShift p (primeCoShift p x) + Eop p x := by
  change x = Vop p (primeCoShift p x) + (x - Vop p (primeCoShift p x))
  abel

theorem coShift_defect_zero (p : ℕ+) (x : H) : primeCoShift p (Eop p x) = 0 := by
  exact congrArg (fun T : H →L[ℂ] H => T x) (coShift_mul_Eop p)

/-- The exact logarithmic translation, with inverse translation by the opposite amount. -/
def chronologicalLogTranslation (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (translateL2 a) (fun x =>
    ⟨translateL2 (-a) x, by simpa only [neg_neg] using translateL2_neg_translateL2 (-a) x⟩)

/-- The actual half-line unitary; its underlying map is the original physical dilation. -/
def chronologicalDilationEquiv (κ : ℝ) : HalfLineL2 ≃ₗᵢ[ℂ] HalfLineL2 :=
  halfLineExpUnitary.trans ((chronologicalLogTranslation (Real.log κ)).trans halfLineExpUnitary.symm)

@[simp] theorem chronologicalDilationEquiv_apply (κ : ℝ) (x : HalfLineL2) :
    chronologicalDilationEquiv κ x = halfLineDilation κ x := rfl

theorem chronologicalDilationEquiv_mellin (κ : ℝ) (x : HalfLineL2) :
    halfLineMellinUnitary (chronologicalDilationEquiv κ x) =
      modulationMul (Real.log κ) (halfLineMellinUnitary x) :=
  halfLineMellinUnitary_halfLineDilation κ x

/-- Full native PCS and chronological carriers cannot be identified while preserving a prime shift. -/
theorem no_PCS_CTF_shift_equivalence (p : ℕ+) (hp : 1 < (p : ℕ)) :
    ¬ ∃ U : H ≃ₗᵢ[ℂ] HalfLineL2, ∀ x,
      U (primeShift p x) = halfLineDilation (p : ℝ) (U x) := by
  rintro ⟨U, hU⟩
  apply primeShift_not_surjective p hp
  intro y
  obtain ⟨v, hv⟩ := (chronologicalDilationEquiv (p : ℝ)).surjective (U y)
  obtain ⟨x, rfl⟩ := U.surjective v
  refine ⟨x, U.injective ?_⟩
  exact (hU x).trans hv

/-- Even an injective linear map cannot carry the native co-shift to invertible physical dilation. -/
theorem no_PCS_CTF_coShift_injective_intertwiner (p : ℕ+) (hp : 1 < (p : ℕ)) :
    ¬ ∃ U : H →ₗ[ℂ] HalfLineL2, Function.Injective U ∧ ∀ x,
      U (primeCoShift p x) = halfLineDilation (p : ℝ) (U x) := by
  rintro ⟨U, hi, hU⟩
  apply primeCoShift_not_injective p hp
  intro x y hxy
  apply hi
  apply (chronologicalDilationEquiv (p : ℝ)).injective
  change halfLineDilation (p : ℝ) (U x) = halfLineDilation (p : ℝ) (U y)
  rw [← hU, ← hU, hxy]

end RHTower.PrimeCoShift

end
