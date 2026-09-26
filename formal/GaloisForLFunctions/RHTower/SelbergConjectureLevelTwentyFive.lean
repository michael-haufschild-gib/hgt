import GaloisForLFunctions.RHTower.SelbergMaassFloorOneGap
import GaloisForLFunctions.RHTower.SelbergConjectureSmallLevel
import GaloisForLFunctions.RHTower.Gamma0MaassHeckeOperator

/-!
# Selberg's eigenvalue conjecture for congruence subgroups of level at most 25

The floor-one Hardy argument (`SelbergMaassFloorOneGap`) excludes exceptional eigenvalues for
`Γ(N)`, `1 ≤ N ≤ 25`. Maass cusp forms restrict to subgroups, so every subgroup containing
some `Γ(N)` with `N ≤ 25` has no exceptional eigenvalue (`no_exceptional_of_principal_le`). This
includes `Γ₀(N)` and `Γ₁(N)`.

Conjugation by `diag(1, N)` maps `Γ(N)` into `Γ₀(N²)`: for `γ = (a b; c d) ∈ Γ(N)`,
`γz/N = δ(z/N)` with `δ = (a, b/N; Nc, d) ∈ Γ₀(N²)`. So a Maass cusp form `u` on `Γ₀(N²)` gives
the Maass cusp form `u(z/N)` on `Γ(N)` with the same eigenvalue (`conjMaass`). Hence `Γ₀(M)` has
no exceptional eigenvalue whenever `M ∣ N²` for some `N ≤ 25` (`gamma0_sq_no_exceptional`).
Examples are `M = 625, 576, 529, 484`.
-/

open Set UpperHalfPlane

namespace GaloisForLFunctions.RHTower.SelbergLevelTwentyFive

open SelbergSmallLevel Gamma0MaassHecke

noncomputable section

/-- **Selberg's eigenvalue conjecture for every subgroup containing `Γ(N)`, `1 ≤ N ≤ 25`.** -/
theorem no_exceptional_of_principal_le {Γ : Subgroup SL2Z} {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 25)
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage Γ) lam) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  constructor
  intro f
  exact (SelbergMaassFloorOneGap.level_le_twentyfive_no_exceptional n hN ⟨lam, hlam⟩).false
    (restrictMaass hΓ f)

theorem gamma0_no_exceptional {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 25) {lam : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 N)) lam) :=
  no_exceptional_of_principal_le hN1 hN (gamma_le_gamma0 N) hlam

theorem gamma1_no_exceptional {N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 25) {lam : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma1 N)) lam) :=
  no_exceptional_of_principal_le hN1 hN (gamma_le_gamma1 N) hlam

/-! ### Transfer to `Γ₀(M)`, `M ∣ N²`: conjugation by `diag(1, N)` -/

section Conjugation

variable (N : ℕ) [NeZero N]

/-- The rational matrix `diag(1, N)`, acting by `z ↦ z/N`. -/
def divMat : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (N : ℚ)]
    (by simp [Matrix.det_fin_two_of, NeZero.ne N])

theorem divMat_det_pos : 0 < ((divMat N).map (algebraMap ℚ ℝ)).val.det := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  simp [divMat, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two, hN]

theorem divMat_smul (z : ℍ) : (((divMat N).map (algebraMap ℚ ℝ) • z : ℍ) : ℂ) = (z : ℂ) / N := by
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det ((divMat N).map (algebraMap ℚ ℝ)) : ℝˣ) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact divMat_det_pos N
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [divMat, Matrix.GeneralLinearGroup.mkOfDetNeZero, UpperHalfPlane.num, UpperHalfPlane.denom]

/-- The pullback `v(z) = u(z/N)`. -/
def conjPull (u : ℍ → ℂ) : ℍ → ℂ := fun z => u ((divMat N).map (algebraMap ℚ ℝ) • z)

omit [NeZero N] in
theorem gamma_entries {σ : SL2Z} (hσ : σ ∈ CongruenceSubgroup.Gamma N) :
    ∃ k m : ℤ, σ 0 1 = N * k ∧ σ 1 0 = N * m := by
  rw [CongruenceSubgroup.Gamma_mem] at hσ
  obtain ⟨-, h01, h10, -⟩ := hσ
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 h01
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 h10
  exact ⟨k, m, hk, hm⟩

/-- `u(z/N)` is `Γ(N)`-invariant when `u` is `Γ₀(N²)`-invariant: for `γ = (a b; c d) ∈ Γ(N)`,
`γz/N = δ(z/N)` with `δ = (a, b/N; Nc, d) ∈ Γ₀(N²)`. -/
theorem conjPull_mem {u : ℍ → ℂ}
    (hu : u ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 (N ^ 2)))) :
    conjPull N u ∈ upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N)) := by
  intro γ z
  obtain ⟨σ, hσ, hγ⟩ := Subgroup.mem_map.1 γ.2
  obtain ⟨k, m, hk, hm⟩ := gamma_entries N hσ
  have hdet : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rwa [Matrix.det_fin_two] at this
  have hdet' : σ 0 0 * σ 1 1 - k * (N * σ 1 0) = 1 := by linear_combination hdet + σ 1 0 * hk
  have hmem : ((N : ℕ) ^ 2 : ℤ) ∣ N * σ 1 0 := ⟨m, by rw [hm]; ring⟩
  set δ := mkSL (σ 0 0) k (N * σ 1 0) (σ 1 1) hdet'
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 (N ^ 2) := mkSL_mem _ _ _ _ hdet' (by exact_mod_cast hmem)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hpt : (divMat N).map (algebraMap ℚ ℝ) • ((γ : SL2R) • z) =
      integralSL2ToReal δ • ((divMat N).map (algebraMap ℚ ℝ) • z) := by
    apply UpperHalfPlane.ext
    rw [divMat_smul, ← hγ]
    change ((σ • z : ℍ) : ℂ) / N = ((δ • ((divMat N).map (algebraMap ℚ ℝ) • z) : ℍ) : ℂ)
    rw [mkSL_smul, divMat_smul, UpperHalfPlane.coe_specialLinearGroup_apply]
    have hden : (σ 1 0 : ℂ) * z + σ 1 1 ≠ 0 := den_ne_zero _ _ _ _ hdet z.2
    have hkC : (σ 0 1 : ℂ) = N * k := by exact_mod_cast hk
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    rw [hkC]
    push_cast
    field_simp
  simp only [conjPull]
  rw [hpt]
  exact hu ⟨integralSL2ToReal δ, Subgroup.mem_map_of_mem _ hδ⟩ _

/-- The conjugated Maass cusp form on `Γ(N)`. -/
def conjMaass {lam : ℝ} (u : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N ^ 2))) lam) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam :=
  ⟨⟨conjPull N u.1.1, conjPull_mem N u.1.2⟩, by
    have hpb := rationalGL_maass_eigenfunction_cuspidal_pullback (divMat N) (divMat_det_pos N) lam
      u.1.1 u.2.2.1 u.2.2.2
    refine ⟨fun h0 => u.2.1 ?_, hpb.1, hpb.2⟩
    ext w
    have hw : 0 < ((N : ℂ) * w).im := by
      have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      simpa using mul_pos hN w.2
    have := congrArg (fun g => (g : upperHalfPlaneInvariantFunctions
      (realImage (CongruenceSubgroup.Gamma N))).1 ⟨(N : ℂ) * w, hw⟩) h0
    simp only [conjPull] at this
    have heq : (divMat N).map (algebraMap ℚ ℝ) • (⟨(N : ℂ) * w, hw⟩ : ℍ) = w := by
      apply UpperHalfPlane.ext
      rw [divMat_smul]
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
      change (N : ℂ) * w / N = w
      field_simp
    rw [heq] at this
    simpa using this⟩

end Conjugation

theorem gamma0_le_of_dvd {M K : ℕ} (h : M ∣ K) :
    CongruenceSubgroup.Gamma0 K ≤ CongruenceSubgroup.Gamma0 M := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ K).1 hA
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).2 ((Int.natCast_dvd_natCast.2 h).trans this)

/-- **Selberg's eigenvalue conjecture for `Γ₀(M)` whenever `M ∣ N²` for some `N ≤ 25`.** -/
theorem gamma0_sq_no_exceptional {M N : ℕ} (hN1 : 1 ≤ N) (hN : N ≤ 25) (hM : M ∣ N ^ 2)
    {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 M)) lam) := by
  haveI : NeZero N := ⟨by omega⟩
  constructor
  intro u
  have u' : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N ^ 2))) lam :=
    restrictMaass (gamma0_le_of_dvd hM) u
  exact (no_exceptional_of_principal_le hN1 hN le_rfl hlam).false (conjMaass N u')

end

end GaloisForLFunctions.RHTower.SelbergLevelTwentyFive
