import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Schreier
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.IntegralDomain

/-! Character decomposition for a module whose torsion weight spaces
are each identified with the same section module. -/

namespace GlobalTheory.MulSplit

variable {R G M : Type} [CommRing R] [CommGroup G] [Fintype G]
  [AddCommGroup M] [Module R M]

private noncomputable def project (ρ : Representation R G M) (u : R)
    (χ : G →* Rˣ) : M →ₗ[R] M :=
  u • ∑ g : G, (((χ g)⁻¹ : Rˣ) : R) • ρ g

private theorem project_apply (ρ : Representation R G M) (u : R) (χ : G →* Rˣ) (v : M) :
    project ρ u χ v = u • ∑ g : G, (((χ g)⁻¹ : Rˣ) : R) • ρ g v := by
  simp [project, LinearMap.sum_apply]

private theorem project_weight (ρ : Representation R G M) (u : R)
    (χ : G →* Rˣ) (s : G) (v : M) :
    ρ s (project ρ u χ v) = (χ s : R) • project ρ u χ v := by
  simp only [project_apply, map_smul, map_sum]
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
  congr 1
  rw [← Units.val_mul]
  congr 1
  rw [mul_inv, mul_inv_cancel_left]

private theorem project_of_weight (ρ : Representation R G M) {u : R}
    (hu : u * (Fintype.card G : R) = 1) (χ : G →* Rˣ) (v : M)
    (hv : ∀ g, ρ g v = (χ g : R) • v) : project ρ u χ v = v := by
  simp only [project_apply, hv, smul_smul, Units.inv_mul, one_smul, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hu, one_smul]

private theorem project_of_other_weight [IsDomain R]
    (ρ : Representation R G M) (u : R) (χ ψ : G →* Rˣ)
    (hne : ψ ≠ χ) (v : M) (hv : ∀ g, ρ g v = (ψ g : R) • v) :
    project ρ u χ v = 0 := by
  simp only [project_apply, hv, smul_smul, ← Finset.sum_smul]
  let f : G →* R := (Units.coeHom R).comp (χ⁻¹ * ψ)
  have hf : f ≠ 1 := by
    intro he
    apply hne
    apply MonoidHom.ext
    intro g
    have hg := DFunLike.congr_fun he g
    have heq : χ g = ψ g := by
      simpa only [f, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        Units.coeHom_apply, MonoidHom.one_apply, Units.val_eq_one, inv_mul_eq_one] using hg
    exact heq.symm
  have hsum : (∑ g : G, (((χ g)⁻¹ : Rˣ) : R) * (ψ g : R)) = 0 :=
    sum_hom_units_eq_zero f hf
  simp only [hsum, mul_zero, zero_smul]

private theorem sum_project [IsDomain R] [Fintype (G →* Rˣ)]
    [HasEnoughRootsOfUnity R (Monoid.exponent G)]
    (ρ : Representation R G M) {u : R} (hu : u * (Fintype.card G : R) = 1) (v : M) :
    ∑ χ : G →* Rˣ, project ρ u χ v = v := by
  classical
  have hcard : Fintype.card (G →* Rˣ) = Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G R
  simp only [project_apply, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single (1 : G)]
  · simp [hcard, smul_smul, hu]
  · intro g _ hg
    let f : (G →* Rˣ) →* R := (Units.coeHom R).comp ((CommGroup.monoidHomMonoidHomEquiv G R).symm g⁻¹)
    have hf : f ≠ 1 := by
      obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G R (inv_ne_one.mpr hg)
      intro he
      apply hχ
      have h := DFunLike.congr_fun he χ
      simpa [f] using h
    have hsum : (∑ χ : G →* Rˣ, (((χ g)⁻¹ : Rˣ) : R)) = 0 := by
      simpa [f] using sum_hom_units_eq_zero f hf
    rw [hsum, zero_smul]
  · simp

/-- If each character weight space in an invariant submodule is the injective
image of the same module, the submodule is a product of copies of that module. -/
theorem nonempty_equiv_pi_of_weights {R G M N : Type} [CommRing R] [IsDomain R] [CommGroup G]
    [Finite G] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity R n] (hn : IsUnit (n : R))
    (hG : ∀ g : G, g ^ n = 1) (ρ : Representation R G M) (W : Submodule R M)
    (hW : ∀ g v, v ∈ W → ρ g v ∈ W)
    (h : ∀ χ : G →* Rˣ, ∃ f : N →ₗ[R] M, Function.Injective f ∧
      ∀ v, (∃ x, f x = v) ↔ v ∈ W ∧ ∀ g, ρ g v = (χ g : R) • v) :
    Nonempty (W ≃ₗ[R] (G → N)) := by
  classical
  letI : HasEnoughRootsOfUnity R (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd R (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R
  letI : Finite (G →* Rˣ) := Finite.of_equiv G e.toEquiv.symm
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (G →* Rˣ)
  have hdvd : (Fintype.card G : R) ∣ (n : R) ^ Group.rank G := by
    exact_mod_cast Nat.cast_dvd_cast (α := R)
      (by simpa only [Nat.card_eq_fintype_card] using card_dvd_exponent_pow_rank' G hG)
  obtain ⟨u, hu⟩ := (isUnit_of_dvd_unit hdvd (hn.pow _)).exists_left_inv
  choose f hf hr using h
  let F : ((G →* Rˣ) → N) →ₗ[R] M := ∑ χ, (f χ).comp (LinearMap.proj χ)
  have hF (x : (G →* Rˣ) → N) : F x = ∑ χ, f χ (x χ) := by simp [F, LinearMap.sum_apply]
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext χ
    apply hf χ
    have hp := congrArg (project ρ u χ) hx
    rw [hF, map_sum, map_zero, Finset.sum_eq_single χ,
      project_of_weight ρ hu χ _ ((hr χ _).1 ⟨_, rfl⟩).2] at hp
    · simpa using hp
    · exact fun ψ _ hψ => project_of_other_weight ρ u χ ψ hψ _ ((hr ψ _).1 ⟨_, rfl⟩).2
    · simp
  have hrange : LinearMap.range F = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hF]
      exact W.sum_mem fun χ _ => ((hr χ _).1 ⟨_, rfl⟩).1
    · intro v hv
      have hpre (χ : G →* Rˣ) : ∃ x, f χ x = project ρ u χ v :=
        (hr χ _).2 ⟨by
          rw [project_apply]
          exact W.smul_mem _ (W.sum_mem fun g _ => W.smul_mem _ (hW g v hv)),
          fun g => project_weight ρ u χ g v⟩
      choose x hx using hpre
      refine ⟨x, ?_⟩
      rw [hF, Finset.sum_congr rfl fun χ _ => hx χ, sum_project ρ hu]
  exact ⟨(LinearEquiv.ofEq _ _ hrange).symm.trans ((LinearEquiv.ofInjective F hinj).symm.trans
    (LinearEquiv.funCongrLeft R N e.toEquiv.symm))⟩

end GlobalTheory.MulSplit
