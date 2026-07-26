import GaloisForLFunctions.HTGeometry.SmallTranslationDerivInvariance

/-!
# Building derivation-invariant superspaces

Infrastructure for the lattice case of the finite-state period-rank law, where the step group is
discrete and the difference-quotient argument of `SmallTranslationDerivInvariance` is unavailable.

The replacement plan is an induction on dimension: a common eigenvector of the two commuting shift
operators on a finite-dimensional shift-stable space of entire functions is a scalar
constant-multiplier carrier, hence a nowhere-zero exponential; dividing the space by it produces a
shift-stable space containing the constant `1`, whose derivative image has strictly smaller
dimension.  This file supplies the closure operations that assemble the resulting superspace.

* `mulByL` — pointwise multiplication by a fixed function, as a linear map;
* `derivInvariantObservableSpace_sup` — a sum of a space mapped into a derivation-invariant space
  with that space is derivation-invariant;
* `derivInvariantObservableSpace_map_mulBy` — multiplying a derivation-invariant space by a solution
  of `h' = ν·h` preserves derivation invariance;
* `translationStable_map_mulBy_inv` — dividing a shift-stable space by a nowhere-zero
  quasi-periodic function preserves shift stability;
* **`exists_common_eigenvector`** — two commuting endomorphisms of a nonzero finite-dimensional
  complex space have a common eigenvector.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Multiplication as a linear map -/

/-- Pointwise multiplication by a fixed function, as a `ℂ`-linear map. -/
def mulByL (h : ℂ → ℂ) : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun u := fun z => h z * u z
  map_add' u v := by funext z; simp only [Pi.add_apply]; ring
  map_smul' c u := by funext z; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp]
theorem mulByL_apply (h u : ℂ → ℂ) (z : ℂ) : mulByL h u z = h z * u z := rfl

/-- Every member of a space multiplied by an entire function is entire. -/
theorem differentiable_of_mem_map_mulBy {A : Submodule ℂ (ℂ → ℂ)} {h₀ : ℂ → ℂ}
    (hA : ∀ u ∈ A, Differentiable ℂ u) (hh₀ : Differentiable ℂ h₀) :
    ∀ g ∈ A.map (mulByL h₀), Differentiable ℂ g := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
  exact hh₀.mul (hA u hu)

/-! ### Closure operations for derivation invariance -/

/-- **Sum with a derivation-invariant space.**  If `V` differentiates into `W` and `W` is
derivation-invariant, then `V ⊔ W` is derivation-invariant. -/
theorem derivInvariantObservableSpace_sup {V W : Submodule ℂ (ℂ → ℂ)}
    (hV : ∀ g ∈ V, Differentiable ℂ g) (hW : ∀ g ∈ W, Differentiable ℂ g)
    (hDVW : ∀ g ∈ V, deriv g ∈ W)
    (hDW : _root_.HTGeometry.DerivInvariantObservableSpace W) :
    _root_.HTGeometry.DerivInvariantObservableSpace (V ⊔ W) := by
  intro g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hg
  have hdv : Differentiable ℂ v := hV v hv
  have hdw : Differentiable ℂ w := hW w hw
  have hderiv : deriv (v + w) = deriv v + deriv w := by
    funext z
    exact deriv_add (hdv z) (hdw z)
  rw [hderiv]
  exact Submodule.mem_sup_right (Submodule.add_mem _ (hDVW v hv) (hDW w hw))

/-- **Multiplying by an exponential preserves derivation invariance.**  If `h₀' = ν·h₀` then
`h₀ · A` is derivation-invariant whenever `A` is, because `(h₀ u)' = h₀ (ν u + u')`. -/
theorem derivInvariantObservableSpace_map_mulBy {A : Submodule ℂ (ℂ → ℂ)} {h₀ : ℂ → ℂ} {ν : ℂ}
    (hA : ∀ u ∈ A, Differentiable ℂ u)
    (hDA : _root_.HTGeometry.DerivInvariantObservableSpace A)
    (hh₀ : Differentiable ℂ h₀) (hd₀ : ∀ z, deriv h₀ z = ν * h₀ z) :
    _root_.HTGeometry.DerivInvariantObservableSpace (A.map (mulByL h₀)) := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
  have hdu : Differentiable ℂ u := hA u hu
  have hkey : deriv (mulByL h₀ u) = mulByL h₀ (ν • u + deriv u) := by
    funext z
    have hprod : HasDerivAt (fun y => h₀ y * u y) (deriv h₀ z * u z + h₀ z * deriv u z) z :=
      (hh₀ z).hasDerivAt.mul (hdu z).hasDerivAt
    show deriv (fun y => h₀ y * u y) z = h₀ z * ((ν • u + deriv u) z)
    rw [hprod.deriv, hd₀ z]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hkey]
  exact Submodule.mem_map_of_mem (Submodule.add_mem _ (Submodule.smul_mem _ ν hu) (hDA u hu))

/-! ### Dividing a shift-stable space by a quasi-periodic factor -/

/-- **Division by a nowhere-zero quasi-periodic factor preserves shift stability.** -/
theorem translationStable_map_mulBy_inv {H : Submodule ℂ (ℂ → ℂ)} {h₀ : ℂ → ℂ} {w lam : ℂ}
    (hshift : ∀ z, h₀ (z + w) = lam * h₀ z)
    (hH : TranslationStable H w) :
    TranslationStable (H.map (mulByL (fun z => (h₀ z)⁻¹))) w := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
  have hfun : translate w (mulByL (fun z => (h₀ z)⁻¹) u)
      = lam⁻¹ • (mulByL (fun z => (h₀ z)⁻¹) (translate w u)) := by
    funext z
    show (h₀ (z + w))⁻¹ * u (z + w) = lam⁻¹ * ((h₀ z)⁻¹ * u (z + w))
    rw [hshift z, mul_inv]
    ring
  rw [hfun]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hH u hu))

/-- Dividing by a nowhere-zero factor and multiplying back recovers the original space. -/
theorem map_mulBy_map_mulBy_inv {H : Submodule ℂ (ℂ → ℂ)} {h₀ : ℂ → ℂ}
    (hne : ∀ z, h₀ z ≠ 0) :
    (H.map (mulByL (fun z => (h₀ z)⁻¹))).map (mulByL h₀) = H := by
  refine le_antisymm ?_ ?_
  · rintro g hg
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hg
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    have hcancel : mulByL h₀ (mulByL (fun z => (h₀ z)⁻¹) u) = u := by
      funext z
      show h₀ z * ((h₀ z)⁻¹ * u z) = u z
      rw [← mul_assoc, mul_inv_cancel₀ (hne z), one_mul]
    rw [hcancel]
    exact hu
  · intro u hu
    refine Submodule.mem_map.mpr ⟨mulByL (fun z => (h₀ z)⁻¹) u,
      Submodule.mem_map_of_mem hu, ?_⟩
    funext z
    show h₀ z * ((h₀ z)⁻¹ * u z) = u z
    rw [← mul_assoc, mul_inv_cancel₀ (hne z), one_mul]

/-! ### A common eigenvector of two commuting endomorphisms -/

/-- **Two commuting endomorphisms of a nonzero finite-dimensional complex space have a common
eigenvector.**  Take an eigenspace of the first; it is invariant under the second, whose restriction
to it has an eigenvector. -/
theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (S T : Module.End ℂ V)
    (hcomm : ∀ v, S (T v) = T (S v)) :
    ∃ (v : V) (lam mu : ℂ), v ≠ 0 ∧ S v = lam • v ∧ T v = mu • v := by
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue S
  set E := Module.End.eigenspace S lam with hE
  have hEne : E ≠ ⊥ := hlam
  haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hEne
  haveI : FiniteDimensional ℂ E := FiniteDimensional.finiteDimensional_submodule E
  have hinv : ∀ x ∈ E, T x ∈ E := by
    intro x hx
    have hSx : S x = lam • x := by
      have := Module.End.mem_eigenspace_iff.mp hx
      exact this
    rw [Module.End.mem_eigenspace_iff, hcomm x, hSx, map_smul]
  let T' : E →ₗ[ℂ] E := T.restrict hinv
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue T'
  obtain ⟨v, hv⟩ := hmu.exists_hasEigenvector
  refine ⟨(v : V), lam, mu, ?_, ?_, ?_⟩
  · intro hzero
    exact hv.2 (Subtype.ext hzero)
  · exact Module.End.mem_eigenspace_iff.mp v.2
  · have hTv : T' v = mu • v := Module.End.mem_eigenspace_iff.mp hv.1
    have := congrArg (Subtype.val : E → V) hTv
    simpa [T', LinearMap.restrict_apply] using this

end GaloisForLFunctions.HTGeometry
