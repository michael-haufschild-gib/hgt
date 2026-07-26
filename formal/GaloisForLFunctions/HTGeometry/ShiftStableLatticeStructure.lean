import GaloisForLFunctions.HTGeometry.DerivInvariantSuperspace
import GaloisForLFunctions.HTGeometry.QuasiPeriodLatticeNoZeros

/-!
# A shift-stable finite-dimensional space of entire functions is differential

Without any discreteness assumption on the step group, a finite-dimensional space `H` of entire
functions stable under two translations with `ℚ`-independent steps is contained in a
finite-dimensional **derivation-invariant** space.  The corpus's finite observable-model boundary
then gives every member a nonzero constant-coefficient annihilator.

The induction is on `dim H`.  A common eigenvector `h₀` of the two shift operators is a scalar
constant-multiplier carrier, hence a nowhere-zero exponential with `h₀' = ν h₀`
(`eq_mul_exp_of_quasiperiods_entire`).  Dividing by it gives a shift-stable `H'` containing the
constant `1`, so the derivative image `D(H')` has strictly smaller dimension; the inductive
superspace `W₀ ⊇ D(H')` yields the derivation-invariant `H' ⊔ W₀`, and multiplying back by `h₀`
produces a derivation-invariant superspace of `H`.

* `translateL` — translation as a linear map, and `shiftEnd` its restriction to a stable subspace;
* **`exists_derivInvariant_superspace`** — the structure theorem;
* **`differentiallyAlgebraic_of_translationStable`** — every member is differentially algebraic,
  with a *constant-coefficient* annihilator, and no discreteness hypothesis on the steps.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Translation as an endomorphism of a stable subspace -/

/-- Translation as a `ℂ`-linear map on functions. -/
def translateL (w : ℂ) : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun := translate w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem translateL_apply (w : ℂ) (u : ℂ → ℂ) (z : ℂ) : translateL w u z = u (z + w) := rfl

/-- The translation endomorphism of a stable subspace. -/
noncomputable def shiftEnd (H : Submodule ℂ (ℂ → ℂ)) {w : ℂ} (hs : TranslationStable H w) :
    Module.End ℂ H :=
  (translateL w).restrict (fun x hx => hs x hx)

@[simp]
theorem shiftEnd_coe (H : Submodule ℂ (ℂ → ℂ)) {w : ℂ} (hs : TranslationStable H w) (u : H) :
    ((shiftEnd H hs u : H) : ℂ → ℂ) = translate w (u : ℂ → ℂ) := rfl

/-- Two translation endomorphisms of a stable subspace commute. -/
theorem shiftEnd_comm (H : Submodule ℂ (ℂ → ℂ)) {w₁ w₂ : ℂ}
    (hs₁ : TranslationStable H w₁) (hs₂ : TranslationStable H w₂) (u : H) :
    shiftEnd H hs₁ (shiftEnd H hs₂ u) = shiftEnd H hs₂ (shiftEnd H hs₁ u) := by
  refine Subtype.ext (funext fun z => ?_)
  show (u : ℂ → ℂ) (z + w₁ + w₂) = (u : ℂ → ℂ) (z + w₂ + w₁)
  ring_nf

/-- The image of a finite-dimensional subspace under a linear map is finite-dimensional. -/
theorem finiteDimensional_submodule_map (f : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ))
    (H : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ H] : FiniteDimensional ℂ (H.map f) := by
  have hres : ∀ x ∈ H, f x ∈ H.map f := fun x hx => Submodule.mem_map_of_mem hx
  refine FiniteDimensional.of_surjective (f.restrict hres) ?_
  rintro ⟨g, hg⟩
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
  exact ⟨⟨u, hu⟩, rfl⟩

/-! ### The structure theorem -/

private theorem exists_derivInvariant_superspace_aux {w₁ w₂ : ℂ}
    (hindepQ : LinearIndependent ℚ ![w₁, w₂]) :
    ∀ (n : ℕ) (H : Submodule ℂ (ℂ → ℂ)) (_ : FiniteDimensional ℂ H),
      Module.finrank ℂ H ≤ n → (∀ g ∈ H, Differentiable ℂ g) →
      TranslationStable H w₁ → TranslationStable H w₂ →
      ∃ W : Submodule ℂ (ℂ → ℂ), FiniteDimensional ℂ W ∧ H ≤ W ∧
        (∀ g ∈ W, Differentiable ℂ g) ∧ _root_.HTGeometry.DerivInvariantObservableSpace W := by
  intro n
  induction n with
  | zero =>
      intro H _ hrank _ _ _
      have hbot : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hrank)
      refine ⟨⊥, inferInstance, hbot.le, ?_, ?_⟩
      · intro g hg
        rw [Submodule.mem_bot] at hg
        subst hg
        exact differentiable_const 0
      · intro g hg
        rw [Submodule.mem_bot] at hg
        subst hg
        have : deriv (0 : ℂ → ℂ) = 0 := by
          funext z; simp
        rw [this]
        exact Submodule.zero_mem _
  | succ n ih =>
      intro H hHfin hrank hent hs₁ hs₂
      rcases Nat.eq_zero_or_pos (Module.finrank ℂ H) with hzero | hpos
      · have hbot : H = ⊥ := Submodule.finrank_eq_zero.mp hzero
        refine ⟨⊥, inferInstance, hbot.le, ?_, ?_⟩
        · intro g hg
          rw [Submodule.mem_bot] at hg
          subst hg
          exact differentiable_const 0
        · intro g hg
          rw [Submodule.mem_bot] at hg
          subst hg
          have : deriv (0 : ℂ → ℂ) = 0 := by funext z; simp
          rw [this]
          exact Submodule.zero_mem _
      -- a common eigenvector of the two shifts
      haveI : Nontrivial H := by
        rw [Submodule.nontrivial_iff_ne_bot]
        intro hbot
        rw [hbot] at hpos
        simp at hpos
      obtain ⟨v, lam, mu, hvne, hv₁, hv₂⟩ :=
        exists_common_eigenvector (shiftEnd H hs₁) (shiftEnd H hs₂) (shiftEnd_comm H hs₁ hs₂)
      set h₀ : ℂ → ℂ := (v : ℂ → ℂ) with hh₀def
      have hh₀mem : h₀ ∈ H := v.2
      have hh₀ent : Differentiable ℂ h₀ := hent h₀ hh₀mem
      have hq₁ : ∀ z, h₀ (z + w₁) = lam * h₀ z := by
        intro z
        have := congrArg (fun x : H => (x : ℂ → ℂ) z) hv₁
        simpa [translate] using this
      have hq₂ : ∀ z, h₀ (z + w₂) = mu * h₀ z := by
        intro z
        have := congrArg (fun x : H => (x : ℂ → ℂ) z) hv₂
        simpa [translate] using this
      obtain ⟨c, hc⟩ := eq_mul_exp_of_quasiperiods_entire hh₀ent hindepQ hq₁ hq₂
      have hh₀zero : h₀ 0 ≠ 0 := by
        intro h0
        apply hvne
        refine Subtype.ext (funext fun z => ?_)
        show h₀ z = 0
        rw [hc z, h0, zero_mul]
      have hh₀ne : ∀ z, h₀ z ≠ 0 := by
        intro z
        rw [hc z]
        exact mul_ne_zero hh₀zero (Complex.exp_ne_zero _)
      obtain ⟨ν, hν⟩ := exists_deriv_eq_const_mul_of_quasiperiods_entire hh₀ent hindepQ hq₁ hq₂
      -- divide the space by the eigenvector
      set inv₀ : ℂ → ℂ := fun z => (h₀ z)⁻¹ with hinv₀def
      set H' : Submodule ℂ (ℂ → ℂ) := H.map (mulByL inv₀) with hH'def
      haveI : FiniteDimensional ℂ H' := finiteDimensional_submodule_map _ H
      have hH'ent : ∀ g ∈ H', Differentiable ℂ g := by
        intro g hg
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
        have : (fun z => inv₀ z * u z) = fun z => u z / h₀ z := by
          funext z
          rw [hinv₀def]
          field_simp
        show Differentiable ℂ fun z => inv₀ z * u z
        rw [this]
        exact (hent u hu).div hh₀ent hh₀ne
      have hH's₁ : TranslationStable H' w₁ := translationStable_map_mulBy_inv hq₁ hs₁
      have hH's₂ : TranslationStable H' w₂ := translationStable_map_mulBy_inv hq₂ hs₂
      have hone : (1 : ℂ → ℂ) ∈ H' := by
        refine Submodule.mem_map.mpr ⟨h₀, hh₀mem, ?_⟩
        funext z
        show inv₀ z * h₀ z = 1
        rw [hinv₀def]
        exact inv_mul_cancel₀ (hh₀ne z)
      -- the derivative image
      let D' : H' →ₗ[ℂ] (ℂ → ℂ) :=
        { toFun := fun u => deriv (u : ℂ → ℂ)
          map_add' := by
            intro a b
            funext z
            exact deriv_add ((hH'ent a a.2) z) ((hH'ent b b.2) z)
          map_smul' := by
            intro c a
            funext z
            simpa using deriv_const_smul (𝕜 := ℂ) c ((hH'ent a a.2) z) }
      set K : Submodule ℂ (ℂ → ℂ) := LinearMap.range D' with hKdef
      haveI : FiniteDimensional ℂ K := by
        rw [hKdef]
        exact FiniteDimensional.of_surjective D'.rangeRestrict D'.surjective_rangeRestrict
      have hKent : ∀ g ∈ K, Differentiable ℂ g := by
        intro g hg
        obtain ⟨u, rfl⟩ := hg
        exact fun z => (((hH'ent u u.2).analyticAt z).deriv).differentiableAt
      have hKs : ∀ w : ℂ, TranslationStable H' w → TranslationStable K w := by
        intro w hw g hg
        obtain ⟨u, rfl⟩ := hg
        refine ⟨⟨translate w (u : ℂ → ℂ), hw _ u.2⟩, ?_⟩
        show deriv (translate w (u : ℂ → ℂ)) = translate w (deriv (u : ℂ → ℂ))
        funext z
        exact deriv_comp_add_const (u : ℂ → ℂ) w z
      -- the dimension drops
      have hrankK : Module.finrank ℂ K ≤ n := by
        have hker : (⟨1, hone⟩ : H') ∈ LinearMap.ker D' := by
          rw [LinearMap.mem_ker]
          funext z
          show deriv (fun _ : ℂ => (1 : ℂ)) z = 0
          simp
        have hkerne : LinearMap.ker D' ≠ ⊥ := by
          intro hbot
          rw [hbot, Submodule.mem_bot] at hker
          have h1 : (1 : ℂ → ℂ) = 0 := congrArg Subtype.val hker
          have hval := congrFun h1 0
          simp at hval
        have hkerpos : 0 < Module.finrank ℂ (LinearMap.ker D') := by
          rcases Nat.eq_zero_or_pos (Module.finrank ℂ (LinearMap.ker D')) with h0 | hp
          · exact absurd (Submodule.finrank_eq_zero.mp h0) hkerne
          · exact hp
        have hsum := LinearMap.finrank_range_add_finrank_ker D'
        have hKrange : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.range D') := by
          rw [hKdef]
        have hH'rank : Module.finrank ℂ H' ≤ n + 1 := le_trans (by
          have : Module.finrank ℂ H' ≤ Module.finrank ℂ H := by
            exact Submodule.finrank_map_le (mulByL inv₀) H
          exact this) hrank
        omega
      obtain ⟨W₀, hW₀fin, hW₀le, hW₀ent, hW₀D⟩ :=
        ih K inferInstance hrankK hKent (hKs w₁ hH's₁) (hKs w₂ hH's₂)
      -- assemble
      have hDH' : ∀ g ∈ H', deriv g ∈ W₀ := by
        intro g hg
        exact hW₀le ⟨⟨g, hg⟩, rfl⟩
      haveI : FiniteDimensional ℂ (H' ⊔ W₀ : Submodule ℂ (ℂ → ℂ)) :=
        Submodule.finiteDimensional_sup H' W₀
      have hAent : ∀ g ∈ (H' ⊔ W₀ : Submodule ℂ (ℂ → ℂ)), Differentiable ℂ g := by
        intro g hg
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hg
        exact (hH'ent a ha).add (hW₀ent b hb)
      have hAD : _root_.HTGeometry.DerivInvariantObservableSpace (H' ⊔ W₀) :=
        derivInvariantObservableSpace_sup hH'ent hW₀ent hDH' hW₀D
      refine ⟨(H' ⊔ W₀).map (mulByL h₀), finiteDimensional_submodule_map _ _, ?_,
        differentiable_of_mem_map_mulBy hAent hh₀ent,
        derivInvariantObservableSpace_map_mulBy hAent hAD hh₀ent hν⟩
      intro g hg
      refine Submodule.mem_map.mpr ⟨mulByL inv₀ g, Submodule.mem_sup_left
        (Submodule.mem_map_of_mem hg), ?_⟩
      funext z
      show h₀ z * (inv₀ z * g z) = g z
      rw [hinv₀def, ← mul_assoc, mul_inv_cancel₀ (hh₀ne z), one_mul]

/-- **A finite-dimensional shift-stable space of entire functions sits inside a
finite-dimensional derivation-invariant space.**  No discreteness hypothesis on the two steps. -/
theorem exists_derivInvariant_superspace {H : Submodule ℂ (ℂ → ℂ)} [FiniteDimensional ℂ H]
    (hent : ∀ g ∈ H, Differentiable ℂ g) {w₁ w₂ : ℂ}
    (hindepQ : LinearIndependent ℚ ![w₁, w₂])
    (hs₁ : TranslationStable H w₁) (hs₂ : TranslationStable H w₂) :
    ∃ W : Submodule ℂ (ℂ → ℂ), FiniteDimensional ℂ W ∧ H ≤ W ∧
      (∀ g ∈ W, Differentiable ℂ g) ∧ _root_.HTGeometry.DerivInvariantObservableSpace W :=
  exists_derivInvariant_superspace_aux hindepQ (Module.finrank ℂ H) H inferInstance le_rfl
    hent hs₁ hs₂

/-- **Every member of a finite-dimensional shift-stable space of entire functions is differentially
algebraic**, with a constant-coefficient annihilator, for any two `ℚ`-independent steps. -/
theorem differentiallyAlgebraic_of_translationStable {H : Submodule ℂ (ℂ → ℂ)}
    [FiniteDimensional ℂ H] (hent : ∀ g ∈ H, Differentiable ℂ g) {w₁ w₂ : ℂ}
    (hindepQ : LinearIndependent ℚ ![w₁, w₂])
    (hs₁ : TranslationStable H w₁) (hs₂ : TranslationStable H w₂)
    {f : ℂ → ℂ} (hf : f ∈ H) : DifferentiallyAlgebraic f := by
  obtain ⟨W, hWfin, hWle, _, hWD⟩ :=
    exists_derivInvariant_superspace hent hindepQ hs₁ hs₂
  exact _root_.HTGeometry.differentiallyAlgebraic_of_mem_derivInvariantObservableSpace W
    (hWle hf) hWD


/-! ### Constant internal monodromy, with no discreteness hypothesis -/

/-- **The finite-state period-rank law in full generality.**  A `ℂ^m`-valued entire function
reproduced by two translations with `ℚ`-independent steps up to *constant* matrices has every
component differentially algebraic.  Neither invertibility of the matrices nor non-discreteness of
the step group is assumed: the lattice case is covered by the structure theorem above. -/
theorem differentiallyAlgebraic_component_of_matrix_monodromy_two {m : ℕ} (G : ℂ → (Fin m → ℂ))
    (hdiff : ∀ i, Differentiable ℂ (fun z => G z i)) {w₁ w₂ : ℂ}
    (hindepQ : LinearIndependent ℚ ![w₁, w₂]) (A B : Matrix (Fin m) (Fin m) ℂ)
    (h₁ : ∀ z, G (z + w₁) = A.mulVec (G z)) (h₂ : ∀ z, G (z + w₂) = B.mulVec (G z))
    (i : Fin m) : DifferentiallyAlgebraic (fun z => G z i) := by
  set g : Fin m → (ℂ → ℂ) := fun j z => G z j with hg
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  exact differentiallyAlgebraic_of_translationStable (differentiable_of_mem_span g hdiff)
    hindepQ (translationStable_span_components h₁) (translationStable_span_components h₂)
    (Submodule.subset_span ⟨i, rfl⟩)

end GaloisForLFunctions.HTGeometry
