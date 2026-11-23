import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.MomentLoss
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant

/-! # An eigenbasis of the surviving gas after a conserving omission -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap _root_.RHTower
open scoped InnerProductSpace

private theorem conserving_injective {G : GasOp} (hc : Conserving G) : Function.Injective G := by
  obtain ⟨T,hT⟩ := hc
  intro x y he
  apply T.injective
  apply Subtype.ext
  funext i
  change T x i = T y i
  rw [hT,hT,he]

theorem projected_square_positive (P : Projection) : (projected P^2).IsPositive := by
  have he : projected P^2 = star (projected P)*projected P := by rw [(projected_positive P).isSelfAdjoint.star_eq,pow_two]
  rw [he]
  exact isPositive_adjoint_comp_self _

theorem projected_square_sgVal (P : Projection) {r : ℕ} (dim : MissingDimension P r) (hc : Conserving (projected P)) (n : ℕ) :
    sgVal (projected P^2) n = (physicalSpectrum P dim hc n).val := by
  have hhs := conserving_square_hs ⟨projected P,projected_positive P,hc⟩
  have hp := projected_square_positive P
  change _ = approxNumber (projected P^2) n
  rw [approxNumber_eq_singVal hhs.isCompactOperator,← abs_sgVal_eq_singVal hhs.isCompactOperator hp.isSymmetric,
    abs_of_nonneg (sgVal_nonneg_of_isPositive hp n)]

/-- Conservation eliminates the kernel, so the ordered positive interlacing levels index a complete eigenbasis on the original gas. -/
theorem exists_physical_heat_basis (P : Projection) {r : ℕ} (dim : MissingDimension P r) (hc : Conserving (projected P)) :
    ∃ e : HilbertBasis ℕ ℂ Gas, ∀ n, (projected P^2) (e n) = ((physicalSpectrum P dim hc n).val:ℂ) • e n := by
  let S := projected P^2
  have hp := projected_square_positive P
  have hhs := conserving_square_hs ⟨projected P,projected_positive P,hc⟩
  have hn (n : ℕ) : ‖sgVec S n‖ = 1 := by
    rcases norm_sgVec_zero_or_one S n with h | h
    · have hz := sgVal_zero_of_dead h
      change sgVal (projected P^2) n = 0 at hz
      rw [projected_square_sgVal P dim hc n] at hz
      exact False.elim ((band_pos (physicalSpectrum P dim hc) n).ne' hz)
    · exact h
  have ho : Orthonormal ℂ (sgVec S) := ⟨hn,fun _ _ h => inner_sgVec_sgVec_of_ne S h⟩
  have hspan : (Submodule.span ℂ (Set.range (sgVec S)))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hz := apply_eq_zero_of_forall_inner_sgVec hhs.isCompactOperator hp.isSymmetric
      (fun n => (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨n,rfl⟩))
    change projected P (projected P x) = 0 at hz
    have hi := conserving_injective hc
    exact hi ((hi (hz.trans (map_zero _).symm)).trans (map_zero _).symm)
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot ho hspan,?_⟩
  intro n
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot,← projected_square_sgVal P dim hc n]
  exact apply_sgVec S n

#print axioms projected_square_sgVal
#print axioms exists_physical_heat_basis

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
