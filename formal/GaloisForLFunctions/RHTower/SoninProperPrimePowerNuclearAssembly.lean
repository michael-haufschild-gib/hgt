import GaloisForLFunctions.RHTower.SoninPrimeSquareCorrectionNuclear
import GaloisForLFunctions.RHTower.SoninDeeperPrimePowerAbsoluteSummability
import GaloisForLFunctions.RHTower.SoninRegularizedNuclearBudget

noncomputable section
namespace RHTower

/-- The original deeper residuals are jointly absolutely summable in trace norm. -/
theorem summable_norm_soninDeeperPrimePowerNuclearSource (a : ℝ) (ha : 0 < a) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ‖soninWeightedPrimePowerNuclearSource a ha (pk.1, pk.2+1)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pk => ?_)
    (summable_norm_soninLogPrimePowerCoefficient_deeper.mul_left
      (4 * traceNorm SoninL2 (centralSoninProjectionCorrection a)))
  exact traceNorm_centralSoninWeightedPrimePowerResidual_le_source a ha (pk.1, pk.2+1)

/-- All original proper prime-power residuals assemble unconditionally in the
actual trace-norm carrier. No coefficient, index or correction leg is removed. -/
theorem summable_soninWeightedPrimePowerNuclearSource (a : ℝ) (ha : 0 < a) :
    Summable (soninWeightedPrimePowerNuclearSource a ha) := by
  let P : Set (Nat.Primes × ℕ) := {pk | pk.2 = 0}
  apply (summable_subtype_and_compl (s := P)).mp
  constructor
  · have hi : Function.Injective (fun x : P => x.val.1) := by
      intro x y h
      apply Subtype.ext
      exact Prod.ext h ((show x.val.2 = 0 from x.property).trans
        (show y.val.2 = 0 from y.property).symm)
    have h := (summable_soninPrimeSquareNuclearResidual a ha).comp_injective hi
    apply h.congr
    intro x
    exact congrArg (soninWeightedPrimePowerNuclearSource a ha)
      (Prod.ext rfl (show 0 = x.val.2 from x.property.symm))
  · have hi : Function.Injective (fun x : {pk : Nat.Primes × ℕ // pk ∉ P} => (x.val.1, x.val.2-1)) := by
      intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      change x.val.1 = y.val.1 at h₁
      change x.val.2 - 1 = y.val.2 - 1 at h₂
      have hx : x.val.2 ≠ 0 := x.property
      have hy : y.val.2 ≠ 0 := y.property
      apply Subtype.ext
      apply Prod.ext
      · exact h₁
      · omega
    have h := (summable_norm_soninDeeperPrimePowerNuclearSource a ha).of_norm.comp_injective hi
    apply h.congr
    intro x
    have hx : x.val.2 ≠ 0 := x.property
    exact congrArg (soninWeightedPrimePowerNuclearSource a ha)
      (Prod.ext rfl (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hx)))
end RHTower
