import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspLogTest

/-!
Exact intertwining of the original unbounded modular operator with the free logarithmic cusp expression, including residual norms.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- The exact shifted free cusp expression; every derivative is retained. -/
def CuspLogTest.shiftedField (f : CuspLogTest) (lam : ℂ) (t : ℝ) : ℂ :=
  (5/4-lam)*f.field t-deriv (deriv f.field) t

private theorem CuspLogTest.shiftedField_support (f : CuspLogTest) (lam : ℂ) :
    tsupport (f.shiftedField lam) ⊆ tsupport f.field := by
  apply closure_minimal _ isClosed_closure
  intro t ht
  by_contra hn
  have hf : f.field t = 0 := image_eq_zero_of_notMem_tsupport hn
  have hd : deriv (deriv f.field) t = 0 := image_eq_zero_of_notMem_tsupport
    (fun hs => hn (tsupport_deriv_subset (tsupport_deriv_subset hs)))
  exact ht (by simp [CuspLogTest.shiftedField,hf,hd])

/-- The shifted free differential expression is itself an admitted compact cusp test. -/
def CuspLogTest.shiftedTest (f : CuspLogTest) (lam : ℂ) : CuspLogTest where
  field := f.shiftedField lam
  smooth := (contDiff_const.mul f.smooth).sub
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp f.smooth).2).2
  compact := f.compact.of_isClosed_subset isClosed_closure (f.shiftedField_support lam)
  support := (f.shiftedField_support lam).trans f.support

private theorem CuspLogTest.shifted_heightField (f : CuspLogTest) (lam : ℂ)
    (y : ℝ) (hy : 0 < y) :
    (f.shiftedTest lam).heightField y = f.heightField y-(y:ℂ)^2*
      deriv (deriv f.heightField) y-lam*f.heightField y := by
  have he := f.heightTest.log_operator_identity (Real.log y)
  rw [f.logProfile_heightTest,Real.exp_log hy] at he
  change cuspLogWeight (Real.log y)*(f.heightField y-(y:ℂ)^2*
    deriv (deriv f.heightField) y) = (5/4:ℂ)*f.field (Real.log y)-
      deriv (deriv f.field) (Real.log y) at he
  have hinv : (Real.exp (Real.log y/2):ℂ)*cuspLogWeight (Real.log y) = 1 := by
    rw [cuspLogWeight,← Complex.ofReal_mul,← Real.exp_add]
    rw [show Real.log y/2 + -Real.log y/2=0 by ring,Real.exp_zero,Complex.ofReal_one]
  have hs := congrArg (fun a : ℂ => (Real.exp (Real.log y/2):ℂ)*a) he
  rw [← mul_assoc,hinv,one_mul] at hs
  change (if 0<y then (Real.exp (Real.log y/2):ℂ)*f.shiftedField lam (Real.log y) else 0) = _
  rw [if_pos hy]
  unfold CuspLogTest.shiftedField
  rw [show (5/4-lam)*f.field (Real.log y)-deriv (deriv f.field) (Real.log y) =
    ((5/4:ℂ)*f.field (Real.log y)-deriv (deriv f.field) (Real.log y))-
      lam*f.field (Real.log y) by ring,mul_sub,← hs]
  congr 1
  rw [CuspLogTest.heightField,if_pos hy]
  ring

/-- Exact intertwining in the original unbounded modular operator domain:
the shifted operator on a reconstructed cusp packet is the reconstruction of
its free one-dimensional differential expression. -/
theorem CuspLogTest.shifted_operator (f : CuspLogTest) (lam : ℂ) :
    energyOperator f.operatorVector-lam • (f.operatorVector : Space) =
      ((f.shiftedTest lam).operatorVector : Space) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (energyOperator f.operatorVector) (lam • (f.operatorVector:Space)),
    Lp.coeFn_smul lam (f.operatorVector : Space),f.heightTest.energyOperator_coe,
    f.heightTest.operatorVector_coe,(f.shiftedTest lam).heightTest.operatorVector_coe] with z hs hm he hf hg
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hm]
  simp only [Pi.smul_apply,smul_eq_mul]
  change (energyOperator f.heightTest.operatorVector : UpperHalfPlane → ℂ) z-
    lam*((f.heightTest.operatorVector : Space) : UpperHalfPlane → ℂ) z =
      (((f.shiftedTest lam).heightTest.operatorVector : Space) : UpperHalfPlane → ℂ) z
  rw [he,hf,hg]
  exact (f.shifted_heightField lam z.im z.im_pos).symm

/-- The exact squared residual norm in the actual modular Hilbert space is the
flat squared norm of the free cusp residual. No spectral approximation premise is supplied. -/
theorem CuspLogTest.shifted_operator_inner (f : CuspLogTest) (lam : ℂ) :
    inner ℂ (energyOperator f.operatorVector-lam • (f.operatorVector : Space))
      (energyOperator f.operatorVector-lam • (f.operatorVector : Space)) =
      ∫ t in Ioi (Real.log 2), conj ((5/4-lam)*f.field t-deriv (deriv f.field) t)*
        ((5/4-lam)*f.field t-deriv (deriv f.field) t) := by
  rw [f.shifted_operator,(f.shiftedTest lam).operatorVector_inner]
  rfl

end
end RHTower.D4BMModularCore
