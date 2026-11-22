import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Canonical

/-!
# Full-space factorization of conserving propagation

The square-root shell count turns every conserving map into a Hilbert-space
isometry. The resulting isometry can have a proper closed range.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-- Exact cyclic-order probabilities after arbitrary bounded propagation. -/
def Conserving (G : GasOp) : Prop :=
  ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split 0 (G f) x

private def renormalize (G : GasOp) (f : Gas) (n : ℕ+) := (gain n:ℂ)*G f n

private theorem renormalize_sq (G : GasOp) (f : Gas) (n : ℕ+) :
    ‖renormalize G f n‖^2 = shellMass 0 n*‖G f n‖^2 := by
  rw [renormalize,norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (gain_pos n).le,
    gain_sq,shellMass_eq]
  simp only [heat,neg_zero,zero_mul,Complex.exp_zero,norm_one,one_pow,mul_one]

private theorem mass_sum {G : GasOp} (h : Conserving G) (f : Gas) :
    HasSum (fun n => ‖renormalize G f n‖^2) (‖f‖^2) := by
  obtain ⟨T,hT⟩ := h
  simp_rw [renormalize_sq]
  apply (split_hasSum_iff ..).mp
  simp_rw [← hT]
  rw [← T.norm_map f,lp_norm_sq_eq_tsum]
  exact (lp_summable_norm_sq (T f)).hasSum

private def normalizedIsometry {G : GasOp} (h : Conserving G) : Gas →ₗᵢ[ℂ] Gas := by
  let image (f : Gas) : Gas := ⟨renormalize G f,HilbertSchmidt.memℓp_of_sq (mass_sum h f).summable⟩
  exact
    { toFun := image
      map_add' := fun f g => lp.ext (funext fun n => by
        change (gain n:ℂ)*G (f+g) n = (gain n:ℂ)*G f n+(gain n:ℂ)*G g n
        rw [map_add,lp.coeFn_add,Pi.add_apply,mul_add])
      map_smul' := fun c f => lp.ext (funext fun n => by
        change (gain n:ℂ)*G (c • f) n = c*((gain n:ℂ)*G f n)
        rw [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
        ring)
      norm_map' := fun f => by
        change ‖image f‖ = ‖f‖
        have he : ‖image f‖^2 = ‖f‖^2 := (lp_norm_sq_eq_tsum (image f)).trans (mass_sum h f).tsum_eq
        nlinarith only [he,norm_nonneg (image f),norm_nonneg f] }

private theorem normalized_factor {G : GasOp} (h : Conserving G) :
    G = criticalOperator*(normalizedIsometry h).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  change G f n = (attenuation n:ℂ)*((gain n:ℂ)*G f n)
  rw [attenuation,Complex.ofReal_inv,← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (gain_pos n).ne'),one_mul]

theorem conserves_factor (U : Gas →ₗᵢ[ℂ] Gas) : Conserving (criticalOperator*U.toContinuousLinearMap) := by
  let s : {z : ℂ // z.re = 1/2} := ⟨1/2,by norm_num⟩
  refine ⟨(splitIsometry s).comp U,fun f x => ?_⟩
  change split (1/2) (U f) x = split 0 (criticalOperator (U f)) x
  rw [split,split,channel,channel,critical_apply,critical_heat]
  simp only [heat,neg_zero,zero_mul,Complex.exp_zero,mul_one,mul_assoc]

/-- The range isometry and its amplitudes are determined by the measured propagator. -/
theorem full_isometry_iff (G : GasOp) :
    Conserving G ↔ ∃! U : Gas →ₗᵢ[ℂ] Gas, G = criticalOperator*U.toContinuousLinearMap := by
  constructor
  · intro h
    refine ⟨normalizedIsometry h,normalized_factor h,fun V hV => ?_⟩
    apply LinearIsometry.ext
    intro f
    apply critical_injective
    exact congrArg (fun K : GasOp => K f) (hV.symm.trans (normalized_factor h))
  · rintro ⟨U,rfl,_⟩
    exact conserves_factor U

#print axioms full_isometry_iff
#print axioms conserves_factor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
