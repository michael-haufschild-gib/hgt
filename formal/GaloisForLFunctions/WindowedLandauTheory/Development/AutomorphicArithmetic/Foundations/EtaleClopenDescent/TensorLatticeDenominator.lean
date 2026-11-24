import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeCoordinates

/-! Localization in the left factor of a chart tensor lattice clears
denominators by a common power of the same coordinate ratio. -/

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F V W : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower k F W]
  {P P' : Submodule k V} {Q : Submodule k W} {a : F}

/-- Every tensor generated over a localized left lattice can be
regularized by a power of the left localization denominator. -/
theorem exists_pow_left_mem_tensorChartLattice
    (hst : ∀ v ∈ P, a • v ∈ P)
    (hden : ∀ v ∈ P', ∃ n : ℕ, a ^ n • v ∈ P)
    {t : V ⊗[k] W} (ht : t ∈ tensorChartLattice P' Q) :
    ∃ n : ℕ, tensorScalarAction ((a ^ n) ⊗ₜ[k] (1 : F)) t ∈ tensorChartLattice P Q := by
  let B := tensorChartLattice P Q
  let L : Module.End k (V ⊗[k] W) := tensorScalarAction (a ⊗ₜ[k] (1 : F))
  have hL : B ≤ B.comap L := Submodule.map₂_le.mpr fun v hv w hw => by
    change tensorScalarAction (a ⊗ₜ[k] (1 : F)) (v ⊗ₜ[k] w) ∈ B
    rw [tensorScalarAction_tmul, one_smul]
    exact Submodule.apply_mem_map₂ _ (hst v hv) hw
  have hp (n : ℕ) {z : V ⊗[k] W} (hz : z ∈ B) : (L ^ n) z ∈ B := by
    induction n with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hz
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hL ih
  let U : Submodule k (V ⊗[k] W) := {
    carrier := {z | ∃ n : ℕ, (L ^ n) z ∈ B}
    zero_mem' := ⟨0, by rw [map_zero]; exact B.zero_mem⟩
    add_mem' := by
      rintro x y ⟨m, hm⟩ ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      rw [map_add]
      apply B.add_mem
      · rw [add_comm m n, pow_add, Module.End.mul_apply]
        exact hp n hm
      · rw [pow_add, Module.End.mul_apply]
        exact hp m hn
    smul_mem' := by
      rintro c z ⟨n, hn⟩
      exact ⟨n, by rw [map_smul]; exact B.smul_mem c hn⟩ }
  have hpow (n : ℕ) : L ^ n = tensorScalarAction ((a ^ n) ⊗ₜ[k] (1 : F)) := by
    show tensorScalarAction (a ⊗ₜ[k] (1 : F)) ^ n = _
    rw [← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  have hle : tensorChartLattice P' Q ≤ U := Submodule.map₂_le.mpr fun v hv w hw => by
    obtain ⟨n, hn⟩ := hden v hv
    refine ⟨n, ?_⟩
    change (L ^ n) (v ⊗ₜ[k] w) ∈ B
    rw [hpow, tensorScalarAction_tmul, one_smul]
    exact Submodule.apply_mem_map₂ _ hn hw
  obtain ⟨n, hn⟩ := hle ht
  rw [hpow] at hn
  exact ⟨n, hn⟩

end GlobalTheory.PD
