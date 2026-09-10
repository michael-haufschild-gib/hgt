import GaloisForLFunctions.HTGeometry.GomesFiniteFockExponentialCoordinate
import GaloisForLFunctions.RHTower.TruncatedJetWeylBoundary

/-!
# Existing geometric jet clocks intertwine finite formal symbols

The actual diagonal clock from the truncated Weyl boundary transports arbitrary
formal symbols by rescaling. The law survives at zero scale as an intertwiner,
without assuming the geometric clock is invertible.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The existing geometric jet clock intertwines rescaled and original formal symbols at every phase. -/
theorem gomesTruncatedJetClock_formal_covariance (n : ℕ) (z : ℂ) (F : PowerSeries ℂ) :
    RHTower.truncatedJetClock n z *
        gomesFiniteFockFormalHom (n + 1) (PowerSeries.rescale z F) =
      gomesFiniteFockFormalHom (n + 1) F * RHTower.truncatedJetClock n z := by
  ext i j
  simp only [RHTower.truncatedJetClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
    gomesFiniteFockFormalHom_apply]
  by_cases h : i.val ≤ j.val
  · rw [if_pos h, if_pos h, PowerSeries.coeff_rescale, ← mul_assoc, ← pow_add,
      Nat.add_sub_of_le h]
    exact mul_comm _ _
  · simp only [if_neg h, mul_zero, zero_mul]

/-- Geometric jet clocks intertwine the literal Taylor translations at every scale and translation. -/
theorem gomesTruncatedJetClock_taylor_covariance (n : ℕ) (z w : ℂ) :
    RHTower.truncatedJetClock n z * fockTaylorMatrix (n + 1) (w * z) =
      fockTaylorMatrix (n + 1) w * RHTower.truncatedJetClock n z := by
  have h := gomesTruncatedJetClock_formal_covariance n z
    (PowerSeries.rescale w (PowerSeries.exp ℂ))
  simpa only [PowerSeries.rescale_rescale, gomesFiniteFockFormalHom_exp] using h

/-- The zero-phase geometric clock removes exactly the nonconstant formal clock symmetries. -/
theorem gomesTruncatedJetClock_zero_commute_iff (n : ℕ) (F : PowerSeries ℂ) :
    Commute (gomesFiniteFockFormalHom (n + 1) F) (RHTower.truncatedJetClock n 0) ↔
      gomesFiniteFockFormalHom (n + 1) F =
        algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (PowerSeries.constantCoeff F) := by
  constructor
  · intro h
    rw [← (gomesFiniteFockFormalHom (n + 1)).commutes]
    apply (gomesFiniteFockFormalHom_eq_iff (n + 1) _ _).mpr
    intro j
    change PowerSeries.coeff j.val F =
      PowerSeries.coeff j.val (PowerSeries.C (PowerSeries.constantCoeff F))
    by_cases hj : j.val = 0
    · simp only [hj, PowerSeries.coeff_C, if_true,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · have he := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M 0 j) h.eq
      simp only [RHTower.truncatedJetClock, Matrix.diagonal_mul, Matrix.mul_diagonal,
        gomesFiniteFockFormalHom_apply, Fin.val_zero, Nat.sub_zero,
        zero_pow hj, pow_zero, one_mul, mul_zero] at he
      rw [PowerSeries.coeff_C, if_neg hj]
      exact he.symm
  · intro h
    rw [h]
    exact Algebra.commutes _ _

/-- Supplying the actual zero-phase geometric clock reduces the full derivative-clock commutant to scalars. -/
theorem gomesTruncatedJetClock_joint_commute_iff (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (Commute M (fockShiftMatrix (n + 1)) ∧ Commute M (RHTower.truncatedJetClock n 0)) ↔
      ∃ c : ℂ, M = algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) c := by
  constructor
  · rintro ⟨hd, hc⟩
    obtain ⟨F, hF⟩ := gomesFiniteFockFormalSymbolHom_surjective (n + 1)
      ⟨M, (gomesFiniteFockCommutant_mem_iff (n + 1) M).mpr hd⟩
    have hfm : gomesFiniteFockFormalHom (n + 1) F = M := congrArg Subtype.val hF
    refine ⟨PowerSeries.constantCoeff F, ?_⟩
    rw [← hfm] at hc ⊢
    exact (gomesTruncatedJetClock_zero_commute_iff n F).mp hc
  · rintro ⟨c, rfl⟩
    exact ⟨Algebra.commutes _ _, Algebra.commutes _ _⟩

/-- The complete centralizer of the two actual supplied structures is precisely the scalar algebra. -/
theorem gomesTruncatedJetClock_joint_centralizer (n : ℕ) :
    Subalgebra.centralizer ℂ {fockShiftMatrix (n + 1), RHTower.truncatedJetClock n 0} = ⊥ := by
  ext M
  rw [Subalgebra.mem_centralizer_iff, Algebra.mem_bot]
  change (∀ a ∈ {fockShiftMatrix (n + 1), RHTower.truncatedJetClock n 0}, a * M = M * a) ↔
    ∃ c : ℂ, algebraMap ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) c = M
  constructor
  · intro h
    have hd : Commute M (fockShiftMatrix (n + 1)) :=
      (h _ (by simp)).symm
    have hc : Commute M (RHTower.truncatedJetClock n 0) :=
      (h _ (by simp)).symm
    obtain ⟨c, hc⟩ := (gomesTruncatedJetClock_joint_commute_iff n M).mp ⟨hd, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩ a _
    exact (Algebra.commutes c a).symm

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
