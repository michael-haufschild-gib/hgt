import GaloisForLFunctions.RHTower.SarnakXueRepresentationBound
import GaloisForLFunctions.RHTower.SelbergMaassHeckeEigenspace
import GaloisForLFunctions.RHTower.SelbergMaassStripHardyGap
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

open Module Matrix CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

/-!
# Exceptional Maass eigenspaces carry large `SL(2, 𝔽_p)`-representations

For `p = N + 1` prime and `0 < λ < 1/4`, `SL(2,ℤ)` acts on the zero-inclusive space of `Γ(p)`-invariant
Maass cusp eigenfunctions with eigenvalue `λ` by `f ↦ f ∘ A⁻¹`, and `Γ(p)` acts trivially. The span of the
translates of a nonzero `f` is finite-dimensional (the translates are indexed by `SL(2,ℤ)/Γ(p)`), has no
nonzero invariant vector (level one carries no exceptional eigenvalue), and therefore has dimension at
least `(p-1)/2` (`exceptional_translateSpan_dim`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXue

open GaloisForLFunctions.RHTower SelbergMaassCuspTransport

noncomputable section

variable (N : ℕ) (lam : ℝ)

theorem gl_action (γ : principalCongruenceGL N) (z : ℍ) :
    ∃ A ∈ Gamma (N + 1), γ.1 • z = A • z := by
  obtain ⟨A, hA, hγ⟩ := γ.2
  exact ⟨A, hA, by rw [← hγ]; rfl⟩

theorem mem_of_sl {f : ℍ → ℂ} (hinv : ∀ A ∈ Gamma (N + 1), ∀ z : ℍ, f (A • z) = f z)
    (he : IsMaassEigenfunction lam f) (hc : IsCuspidalAtIntegralCusps f) :
    f ∈ glMaassCuspEigenspace (principalCongruenceGL N) lam := by
  refine ⟨fun γ z => ?_, he, hc⟩
  obtain ⟨A, hA, h⟩ := gl_action N γ z
  rw [h]; exact hinv A hA z

theorem sl_inv {f : ℍ → ℂ} (hf : f ∈ glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    ∀ A ∈ Gamma (N + 1), ∀ z : ℍ, f (A • z) = f z := by
  intro A hA z
  have := hf.1 ⟨_, ⟨A, hA, rfl⟩⟩ z
  exact this

/-- Left translation `f ↦ f ∘ A⁻¹` preserves the zero-inclusive principal Maass eigenspace. -/
theorem pullback_mem (A : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : f ∈ glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    (fun z => f (A⁻¹ • z)) ∈ glMaassCuspEigenspace (principalCongruenceGL N) lam := by
  apply mem_of_sl N lam
  · intro B hB z
    have hconj := (Gamma_normal (N + 1)).conj_mem B hB A⁻¹
    rw [inv_inv] at hconj
    have := sl_inv N lam hf _ hconj (A⁻¹ • z)
    simpa only [mul_smul, smul_inv_smul] using this
  · exact eigenfunction_pullback A⁻¹ lam f hf.2.1
  · exact cuspidal_pullback A⁻¹ f hf.2.2

/-- The translation representation of `SL(2,ℤ)` on the principal Maass eigenspace. -/
def translationRep : Representation ℂ SL(2, ℤ) (glMaassCuspEigenspace (principalCongruenceGL N) lam) where
  toFun A :=
    { toFun := fun f => ⟨fun z => f.1 (A⁻¹ • z), pullback_mem N lam A f.2⟩
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  map_one' := by
    apply LinearMap.ext; intro f; apply Subtype.ext; funext z
    simp
  map_mul' A B := by
    apply LinearMap.ext; intro f; apply Subtype.ext; funext z
    simp [mul_smul]

@[simp] theorem translationRep_apply (A : SL(2, ℤ))
    (f : glMaassCuspEigenspace (principalCongruenceGL N) lam) (z : ℍ) :
    (translationRep N lam A f).1 z = f.1 (A⁻¹ • z) := rfl

theorem translationRep_Gamma (A : SL(2, ℤ)) (hA : A ∈ Gamma (N + 1)) :
    translationRep N lam A = 1 := by
  apply LinearMap.ext; intro f; apply Subtype.ext; funext z
  exact sl_inv N lam f.2 _ (inv_mem hA) z

/-- The span of the `SL(2,ℤ)`-translates of one eigenspace vector. -/
def translateSpan (f : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    Submodule ℂ (glMaassCuspEigenspace (principalCongruenceGL N) lam) :=
  Submodule.span ℂ (Set.range fun A : SL(2, ℤ) => translationRep N lam A f)

theorem translateSpan_invariant (f : glMaassCuspEigenspace (principalCongruenceGL N) lam)
    (A : SL(2, ℤ)) : ∀ x ∈ translateSpan N lam f, translationRep N lam A x ∈ translateSpan N lam f := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨B, rfl⟩ := hy
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨A * B, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

theorem translateSpan_finiteDimensional (f : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    FiniteDimensional ℂ (translateSpan N lam f) := by
  apply FiniteDimensional.span_of_finite
  let g : SL(2, ℤ) ⧸ Gamma (N + 1) → glMaassCuspEigenspace (principalCongruenceGL N) lam :=
    Quotient.lift (fun A => translationRep N lam A f) (by
      intro A B h
      have hAB : A⁻¹ * B ∈ Gamma (N + 1) := QuotientGroup.leftRel_apply.mp h
      change translationRep N lam A f = translationRep N lam B f
      have hB : B = A * (A⁻¹ * B) := by group
      rw [hB, map_mul, Module.End.mul_apply, translationRep_Gamma N lam _ hAB, Module.End.one_apply])
  apply (Set.finite_range g).subset
  rintro _ ⟨A, rfl⟩
  exact ⟨QuotientGroup.mk A, rfl⟩

/-- The translation representation restricted to a translate span. -/
def spanRep (f : glMaassCuspEigenspace (principalCongruenceGL N) lam) :
    Representation ℂ SL(2, ℤ) (translateSpan N lam f) where
  toFun A := (translationRep N lam A).restrict (translateSpan_invariant N lam f A)
  map_one' := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    simp [LinearMap.restrict_apply]
  map_mul' A B := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    simp [LinearMap.restrict_apply, map_mul]

open SelbergMaassStripHardyGap in
/-- **No invariant vectors.** An `SL(2,ℤ)`-invariant vector of the principal eigenspace at an
eigenvalue in `(0, 1/4)` is zero, because level one carries no exceptional Maass cusp form. -/
theorem invariant_eq_zero (hlam : lam ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (w : glMaassCuspEigenspace (principalCongruenceGL N) lam)
    (hw : ∀ A, translationRep N lam A w = w) : w = 0 := by
  by_contra hne
  have hinv : ∀ (A : SL(2, ℤ)) (z : ℍ), w.1 (A • z) = w.1 z := by
    intro A z
    have := congrArg (fun v => v.1 z) (hw A⁻¹)
    simpa using this
  let g : MaassCuspEigenform (realImage (Gamma 1)) lam :=
    ⟨⟨w.1, fun γ z => by
        obtain ⟨A, -, hA⟩ := γ.2
        rw [← hA]
        exact hinv A z⟩,
      fun h => hne (Subtype.ext (by
        have := congrArg Subtype.val h
        simpa using this)),
      w.2.2.1, w.2.2.2⟩
  exact (level_le_fourteen_no_exceptional ⟨0, by norm_num⟩ ⟨lam, hlam⟩).false g

/-- **Lower multiplicity bound (Sarnak–Xue, first half).** Let `p = N + 1` be prime and
`0 < λ < 1/4`. Every nonzero `Γ(p)`-invariant Maass cusp eigenfunction with eigenvalue `λ` spans, with
its `SL(2,ℤ)`-translates, a finite-dimensional space of such eigenfunctions of dimension at least
`(p-1)/2`. -/
theorem exceptional_translateSpan_dim (hp : (N + 1).Prime)
    (hlam : lam ∈ Set.Ioo (0 : ℝ) (1 / 4))
    (f : glMaassCuspEigenspace (principalCongruenceGL N) lam) (hf : f ≠ 0) :
    FiniteDimensional ℂ (translateSpan N lam f) ∧ N ≤ 2 * finrank ℂ (translateSpan N lam f) := by
  haveI := translateSpan_finiteDimensional N lam f
  haveI : Fact (N + 1).Prime := ⟨hp⟩
  refine ⟨inferInstance, ?_⟩
  have hnt : Nontrivial (translateSpan N lam f) := by
    refine ⟨⟨0, ⟨f, Submodule.subset_span ⟨1, by simp⟩⟩, ?_⟩⟩
    intro h
    exact hf (congrArg Subtype.val h).symm
  have h := half_pred_le_finrank (N + 1) (spanRep N lam f)
    (fun γ hγ => by
      apply LinearMap.ext; intro x; apply Subtype.ext
      simp [spanRep, LinearMap.restrict_apply, translationRep_Gamma N lam γ hγ])
    (fun w hw => by
      have := invariant_eq_zero N lam hlam w.1 (fun A => congrArg Subtype.val (hw A))
      exact Subtype.ext this)
    hnt
  simpa using h

end
end GaloisForLFunctions.RHTower.SarnakXue
