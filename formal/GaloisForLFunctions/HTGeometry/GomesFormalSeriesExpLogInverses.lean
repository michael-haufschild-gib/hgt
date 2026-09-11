import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalLogarithm
import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalSubstitution

/-!
# Full formal exponential and logarithmic coordinates

The existing complex logarithm of the exponential supplies one composition
identity. The formal inverse of the logarithm supplies the other. Substitution
then extends both identities from the linear clock to every based formal series.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The exponential increment is also a left compositional inverse of the formal logarithm. -/
theorem gomesFormalSeries_exp_sub_one_subst_log :
    PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ - 1) = PowerSeries.X := by
  have hL : PowerSeries.subst (PowerSeries.exp ℂ - 1) (PowerSeries.log ℂ) = PowerSeries.X := by
    simpa [PowerSeries.logOf, PowerSeries.rescale_one] using
      gomesFormalSeries_logOf_rescale_exp (1 : ℂ)
  have recover (Q : PowerSeries ℂ)
      (hQ : PowerSeries.subst (PowerSeries.log ℂ) Q = PowerSeries.X) : PowerSeries.exp ℂ - 1 = Q := by
    calc
      _ = PowerSeries.subst (PowerSeries.exp ℂ - 1) (PowerSeries.X : PowerSeries ℂ) :=
        (PowerSeries.subst_X (R := ℂ) PowerSeries.HasSubst.exp_sub_one).symm
      _ = PowerSeries.subst (PowerSeries.exp ℂ - 1) (PowerSeries.subst (PowerSeries.log ℂ) Q) := by
        rw [hQ]
      _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.exp ℂ - 1) (PowerSeries.log ℂ)) Q :=
        PowerSeries.subst_comp_subst_apply (R := ℂ) (S := ℂ) (T := ℂ)
          (a := PowerSeries.log ℂ) (b := PowerSeries.exp ℂ - 1)
          PowerSeries.HasSubst.log PowerSeries.HasSubst.exp_sub_one Q
      _ = Q := by rw [hL, PowerSeries.X_subst]
  have hunit : IsUnit (PowerSeries.coeff 1 (PowerSeries.log ℂ)) := by
    simp [PowerSeries.coeff_log]
  have hQ := PowerSeries.subst_substInvOfIsUnit_left
    (PowerSeries.log ℂ) PowerSeries.constantCoeff_log hunit
  have hEQ := recover (PowerSeries.substInvOfIsUnit (PowerSeries.log ℂ) hunit) hQ
  rw [hEQ]
  exact hQ

/-- The formal exponential evaluated at the universal logarithm is exactly one plus the clock. -/
theorem gomesFormalSeries_exp_subst_log :
    PowerSeries.subst (PowerSeries.log ℂ) (PowerSeries.exp ℂ) = 1 + PowerSeries.X := by
  have h := gomesFormalSeries_exp_sub_one_subst_log
  have h1 : PowerSeries.subst (PowerSeries.log ℂ) (1 : PowerSeries ℂ) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
    simp
  rw [PowerSeries.subst_sub PowerSeries.HasSubst.log, h1] at h
  exact (eq_add_of_sub_eq h).trans (add_comm _ _)

/-- The logarithm recovers every based formal coordinate from its formal exponential. -/
theorem gomesFormalSeries_logOf_exp_subst (G : GomesBasedFormalSeries) :
    PowerSeries.logOf (PowerSeries.subst G.val (PowerSeries.exp ℂ)) = G.val := by
  have hg := gomesBasedFormalSeries_hasSubst G
  have h1 : PowerSeries.subst G.val (1 : PowerSeries ℂ) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
    simp
  have hL : PowerSeries.subst (PowerSeries.exp ℂ - 1) (PowerSeries.log ℂ) = PowerSeries.X := by
    simpa [PowerSeries.logOf, PowerSeries.rescale_one] using
      gomesFormalSeries_logOf_rescale_exp (1 : ℂ)
  rw [PowerSeries.logOf_eq, ← h1, ← PowerSeries.subst_sub hg,
    ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.exp_sub_one hg,
    hL, PowerSeries.subst_X hg]

/-- Exponentiating the logarithm recovers every formal series based at one. -/
theorem gomesFormalSeries_exp_subst_logOf_one_add (G : GomesBasedFormalSeries) :
    PowerSeries.subst (PowerSeries.logOf (1 + G.val)) (PowerSeries.exp ℂ) = 1 + G.val := by
  have hg := gomesBasedFormalSeries_hasSubst G
  have h1 : PowerSeries.subst G.val (1 : PowerSeries ℂ) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
    simp
  rw [PowerSeries.logOf_eq, add_sub_cancel_left,
    ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.log hg,
    gomesFormalSeries_exp_subst_log, PowerSeries.subst_add hg, h1, PowerSeries.subst_X hg]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
