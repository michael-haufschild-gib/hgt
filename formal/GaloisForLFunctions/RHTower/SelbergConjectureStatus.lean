import GaloisForLFunctions.RHTower.SelbergThreeSixteenths
import GaloisForLFunctions.RHTower.SelbergConjectureLevelTwentyFive
import GaloisForLFunctions.RHTower.HalfWeightThetaExceptionalEigenvalue

/-!
# Selberg's eigenvalue conjecture: what is proved

`selberg_status` collects the unconditional results on exceptional eigenvalues of congruence
subgroups.
* The uniform bound `λ₁ ≥ 3/16` holds for every congruence subgroup.
* The full conjecture `λ₁ ≥ 1/4` holds for every subgroup containing some `Γ(N)` with
  `N ≤ 25`, and for every `Γ₀(M)` with `M ∣ N²`, `N ≤ 25`.
* The weight-`1/2` analogue fails: `y^{1/4} θ` has eigenvalue `3/16`.

The last item bounds the method. Kloosterman sums with the theta multiplier satisfy the same
Weil-type bounds, so any argument whose inputs are also valid in weight `1/2` cannot improve on
`3/16`.
-/

open Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.SelbergConjectureStatus

noncomputable section

/-- **The formal status of Selberg's eigenvalue conjecture.**
1. Every congruence subgroup has no exceptional eigenvalue below `3/16`.
2. Every subgroup containing some `Γ(N)` with `1 ≤ N ≤ 25`, and every `Γ₀(M)` with
   `M ∣ N²`, `1 ≤ N ≤ 25`, has no exceptional eigenvalue at all in `(0, 1/4)`.
3. The weight-`1/2` analogue fails: `y^{1/4} θ` on `Γ₀(4)` with the theta multiplier is a
   nowhere-zero, square-integrable eigenfunction of the weight-`1/2` Laplacian with eigenvalue
   `3/16 < 1/4`. So `3/16` is sharp for every argument whose inputs also hold in weight `1/2`. -/
theorem selberg_status :
    (∀ {Γ : Subgroup SL2Z} {N : ℕ}, 1 ≤ N → CongruenceSubgroup.Gamma N ≤ Γ →
      ∀ {lam : ℝ}, 0 < lam → lam < 3 / 16 → IsEmpty (MaassCuspEigenform (realImage Γ) lam)) ∧
    (∀ {Γ : Subgroup SL2Z} {N : ℕ}, 1 ≤ N → N ≤ 25 → CongruenceSubgroup.Gamma N ≤ Γ →
      ∀ {lam : ℝ}, lam ∈ Ioo (0 : ℝ) (1 / 4) → IsEmpty (MaassCuspEigenform (realImage Γ) lam)) ∧
    (∀ {M N : ℕ}, 1 ≤ N → N ≤ 25 → M ∣ N ^ 2 →
      ∀ {lam : ℝ}, lam ∈ Ioo (0 : ℝ) (1 / 4) →
        IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 M)) lam)) ∧
    ((∀ z : ℍ, HalfWeight.thetaMaass z ≠ 0) ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 4, ∀ z : ℍ,
        HalfWeight.thetaMaass (γ • z) = HalfWeight.jU γ z * HalfWeight.thetaMaass z) ∧
      (∀ z : ℂ, 0 < z.im → WeightMaassLaplacian.weightLaplacian (1 / 2) HalfWeight.thetaMaassC z =
        (3 / 16 : ℂ) * HalfWeight.thetaMaassC z) ∧
      (∀ γ : SL(2, ℤ), MeasureTheory.IntegrableOn
        (fun z : ℍ => ((‖HalfWeight.thetaMaass (γ • z)‖ ^ 2 : ℝ) : ℂ)) ModularGroup.fd) ∧
      (3 / 16 : ℝ) < 1 / 4) :=
  ⟨fun hN hΓ _ h0 h1 => SelbergThreeSixteenths.selberg_three_sixteenths_congruence hN hΓ h0 h1,
    fun hN1 hN hΓ _ hlam => SelbergLevelTwentyFive.no_exceptional_of_principal_le hN1 hN hΓ hlam,
    fun hN1 hN hM _ hlam => SelbergLevelTwentyFive.gamma0_sq_no_exceptional hN1 hN hM hlam,
    HalfWeight.weight_half_exceptional⟩

end

end GaloisForLFunctions.RHTower.SelbergConjectureStatus
