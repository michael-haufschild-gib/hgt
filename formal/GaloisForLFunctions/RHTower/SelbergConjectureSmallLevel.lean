import GaloisForLFunctions.RHTower.SelbergMaassStripHardyGap

/-!
# Selberg's eigenvalue conjecture for congruence subgroups of level at most fourteen

A Maass cusp form for a subgroup `Γ ⊇ Γ'` is a Maass cusp form for `Γ'`: invariance
restricts, and the eigen-equation, cusp decay and nonvanishing do not depend on the group
(`restrictMaass`). So the Hardy strip bound for `Γ(N+1)`,
`α(1+α) ≤ 2λ` with `α = π√3/(N+1)`, holds for every subgroup containing `Γ(N+1)`
(`hardy_bound_of_principal_le`). It excludes eigenvalues in `(0, 1/4)` when `N + 1 ≤ 14`.

Consequently every subgroup of `SL₂(ℤ)` containing some `Γ(N)` with `1 ≤ N ≤ 14` has no
exceptional eigenvalue (`no_exceptional_of_principal_le`). This covers `Γ₀(N)` and `Γ₁(N)` for
`N ≤ 14` (`gamma0_no_exceptional`, `gamma1_no_exceptional`).
-/

open Set UpperHalfPlane

namespace GaloisForLFunctions.RHTower.SelbergSmallLevel

open SelbergMaassStripHardyGap

noncomputable section

/-- A Maass cusp form for a subgroup `Γ ⊇ Γ'` is a Maass cusp form for `Γ'`. -/
def restrictMaass {Γ Γ' : Subgroup SL2Z} (hle : Γ' ≤ Γ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage Γ) lam) : MaassCuspEigenform (realImage Γ') lam :=
  ⟨⟨f.1.1, fun γ z => f.1.2 ⟨γ.1, Subgroup.map_mono hle γ.2⟩ z⟩, by
    refine ⟨fun h0 => f.2.1 ?_, f.2.2.1, f.2.2.2⟩
    ext z
    have := congrArg (fun g => (g : upperHalfPlaneInvariantFunctions (realImage Γ')).1 z) h0
    simpa using this⟩

/-- **Selberg's eigenvalue conjecture at levels one through fourteen.** Every subgroup of
`SL₂(ℤ)` containing a principal congruence subgroup `Γ(N)` with `1 ≤ N ≤ 14` has no Maass cusp
form with eigenvalue in `(0, 1/4)`. -/
theorem no_exceptional_of_principal_le {Γ : Subgroup SL2Z} {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 14)
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage Γ) lam) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  constructor
  intro f
  exact (level_le_fourteen_no_exceptional ⟨n, by omega⟩ ⟨lam, hlam⟩).false (restrictMaass hΓ f)

/-- The Hardy strip bound for every subgroup containing `Γ(N+1)`:
`α(1+α) ≤ 2λ` with `α = π√3/(N+1)` for every exceptional Maass cusp form. -/
theorem hardy_bound_of_principal_le {Γ : Subgroup SL2Z} {N : ℕ}
    (hΓ : CongruenceSubgroup.Gamma (N + 1) ≤ Γ) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage Γ) lam) :
    hardyExponent N * (1 + hardyExponent N) ≤ 2 * lam :=
  hardy_eigenvalue_bound N ⟨lam, hlam⟩ (restrictMaass hΓ f)

theorem gamma_le_gamma1 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma1 N :=
  fun A hA => by simp_all [CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma_mem]

theorem gamma_le_gamma0 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ CongruenceSubgroup.Gamma0 N :=
  (gamma_le_gamma1 N).trans (CongruenceSubgroup.Gamma1_in_Gamma0 N)

/-- Selberg's conjecture for `Γ₀(N)`, `1 ≤ N ≤ 14`. -/
theorem gamma0_no_exceptional {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 14) {lam : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 N)) lam) :=
  no_exceptional_of_principal_le hN1 hN (gamma_le_gamma0 N) hlam

/-- Selberg's conjecture for `Γ₁(N)`, `1 ≤ N ≤ 14`. -/
theorem gamma1_no_exceptional {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 14) {lam : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma1 N)) lam) :=
  no_exceptional_of_principal_le hN1 hN (gamma_le_gamma1 N) hlam

end

end GaloisForLFunctions.RHTower.SelbergSmallLevel
