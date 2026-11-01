import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeDirections
import GaloisForLFunctions.HTGeometry.WeakHilbertCompactness
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Weak compactness of normalized nonpositive directions

Use the weak topology on the positive Hilbert factor and the norm topology
on the finite negative factor. Closed linear subspaces remain closed, while
normalizing the negative coordinate makes nonpositive directions compact.
-/

noncomputable section
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Forget the weak topology on the positive coordinate. -/
def mixedWeakEquiv : (WeakSpace ℂ H × E) ≃ₗ[ℂ] (H × E) :=
  LinearEquiv.prodCongr (toWeakSpace ℂ H).symm (LinearEquiv.refl ℂ E)

/-- Nonpositive directions with negative coordinate of norm one. -/
def normalizedNonpositiveSet : Set (WeakSpace ℂ H × E) :=
  weakHilbertBall (H := H) 1 ×ˢ Metric.sphere (0 : E) 1

theorem mem_normalizedNonpositiveSet (x : WeakSpace ℂ H × E) :
    x ∈ normalizedNonpositiveSet ↔
      ‖(mixedWeakEquiv x : H × E).1‖ ≤ 1 ∧ ‖x.2‖ = 1 := by
  simp only [normalizedNonpositiveSet, Set.mem_prod, weakHilbertBall,
    Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right]
  rfl

theorem isCompact_normalizedNonpositiveSet [CompleteSpace H] [FiniteDimensional ℂ E] :
    IsCompact (normalizedNonpositiveSet (H := H) (E := E)) := by
  letI : ProperSpace E := FiniteDimensional.proper ℂ E
  exact (isCompact_weakHilbertBall 1).prod (isCompact_sphere (0 : E) 1)

/-- Norm-closed linear subspaces are closed for the mixed weak topology. -/
theorem isClosed_mixedWeakPreimage [CompleteSpace H] [CompleteSpace E]
    (W : Submodule ℂ (H × E)) (hW : IsClosed (W : Set (H × E))) :
    IsClosed (mixedWeakEquiv (H := H) (E := E) ⁻¹' (W : Set (H × E))) := by
  let A := WithLp 2 (H × E)
  let e : A ≃L[ℂ] H × E := WithLp.prodContinuousLinearEquiv 2 ℂ H E
  let K : Submodule ℂ A := W.comap e.toLinearMap
  have hK : IsClosed (K : Set A) := hW.preimage e.continuous
  letI : CompleteSpace K := hK.completeSpace_coe
  have heq : mixedWeakEquiv (H := H) (E := E) ⁻¹' (W : Set (H × E)) =
      ⋂ u : Kᗮ, {x | inner ℂ (u : A) (e.symm (mixedWeakEquiv x)) = 0} := by
    ext x
    rw [Set.mem_iInter]
    have hh : e.symm (mixedWeakEquiv x) ∈ Kᗮᗮ ↔ mixedWeakEquiv x ∈ W := by
      rw [K.orthogonal_orthogonal]
      change e (e.symm (mixedWeakEquiv x)) ∈ W ↔ _
      rw [e.apply_symm_apply]
    change mixedWeakEquiv x ∈ W ↔ ∀ u : Kᗮ,
      inner ℂ (u : A) (e.symm (mixedWeakEquiv x)) = 0
    rw [← hh, Submodule.mem_orthogonal]
    exact ⟨fun h u => h u u.property, fun h u hu => h ⟨u, hu⟩⟩
  rw [heq]
  apply isClosed_iInter
  intro u
  apply isClosed_eq _ continuous_const
  change Continuous (fun x : WeakSpace ℂ H × E =>
    inner ℂ (u : A).fst ((toWeakSpace ℂ H).symm x.1) + inner ℂ (u : A).snd x.2)
  exact ((WeakBilin.eval_continuous (topDualPairing ℂ H).flip
    (InnerProductSpace.toDual ℂ H (u : A).fst)).comp continuous_fst).add
      (continuous_const.inner continuous_snd)

/-- Every nonzero nonpositive vector has a normalized representative in its subspace. -/
theorem exists_normalizedNonpositive_of_mem (W : Submodule ℂ (H × E))
    {v : H × E} (hvW : v ∈ W) (hv : v ≠ 0) (hq : (pairing v v).re ≤ 0) :
    ∃ x ∈ normalizedNonpositiveSet (H := H) (E := E), mixedWeakEquiv x ∈ W := by
  have hs : v.2 ≠ 0 := fun h => hv (eq_zero_of_nonpositive_snd_eq_zero hq h)
  have hn : 0 < ‖v.2‖ := norm_pos_iff.mpr hs
  let a : ℂ := (‖v.2‖⁻¹ : ℝ)
  have ha : ‖a‖ = ‖v.2‖⁻¹ := by
    change ‖((‖v.2‖⁻¹ : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  refine ⟨mixedWeakEquiv.symm (a • v), ?_, ?_⟩
  · rw [mem_normalizedNonpositiveSet]
    change ‖a • v.1‖ ≤ 1 ∧ ‖a • v.2‖ = 1
    rw [norm_smul, norm_smul, ha]
    constructor
    · calc
        ‖v.2‖⁻¹ * ‖v.1‖ ≤ ‖v.2‖⁻¹ * ‖v.2‖ :=
          mul_le_mul_of_nonneg_left ((pairing_self_nonpos_iff v).mp hq) (inv_nonneg.mpr hn.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hn)
    · exact inv_mul_cancel₀ (ne_of_gt hn)
  · rw [LinearEquiv.apply_symm_apply]
    exact W.smul_mem a hvW

/-- A decreasing chain of closed subspaces cannot lose every nonpositive direction. -/
theorem exists_nonpositive_mem_sInf [CompleteSpace H] [FiniteDimensional ℂ E]
    (c : Set (Submodule ℂ (H × E))) (hne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    (hclosed : ∀ W ∈ c, IsClosed (W : Set (H × E)))
    (hdir : ∀ W ∈ c, ∃ v ∈ W, v ≠ 0 ∧ (pairing v v).re ≤ 0) :
    ∃ v ∈ sInf c, v ≠ 0 ∧ (pairing v v).re ≤ 0 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  let K := normalizedNonpositiveSet (H := H) (E := E)
  let D := (fun W : Submodule ℂ (H × E) =>
    K ∩ mixedWeakEquiv ⁻¹' (W : Set (H × E))) '' c
  have hK : IsCompact K := isCompact_normalizedNonpositiveSet
  have hDclosed : ∀ S ∈ D, IsClosed S := by
    rintro S ⟨W, hW, rfl⟩
    exact hK.isClosed.inter (isClosed_mixedWeakPreimage W (hclosed W hW))
  have hDcompact : ∀ S ∈ D, IsCompact S := by
    rintro S ⟨W, hW, rfl⟩
    exact hK.inter_right (isClosed_mixedWeakPreimage W (hclosed W hW))
  have hDne : ∀ S ∈ D, S.Nonempty := by
    rintro S ⟨W, hW, rfl⟩
    obtain ⟨v, hvW, hv, hq⟩ := hdir W hW
    obtain ⟨x, hxK, hxW⟩ := exists_normalizedNonpositive_of_mem W hvW hv hq
    exact ⟨x, hxK, hxW⟩
  have hDdir : DirectedOn (· ⊇ ·) D := by
    rintro S₁ ⟨W₁, hW₁, rfl⟩ S₂ ⟨W₂, hW₂, rfl⟩
    rcases hchain.total hW₁ hW₂ with h | h
    · exact ⟨_, ⟨W₁, hW₁, rfl⟩, subset_rfl, fun x hx => ⟨hx.1, h hx.2⟩⟩
    · exact ⟨_, ⟨W₂, hW₂, rfl⟩, (fun x hx => ⟨hx.1, h hx.2⟩), subset_rfl⟩
  obtain ⟨W₀, hW₀⟩ := hne
  letI : Nonempty ↥D := ⟨⟨_, ⟨W₀, hW₀, rfl⟩⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    hDdir hDne hDcompact hDclosed
  have hxK : x ∈ K := (Set.mem_sInter.mp hx _ ⟨W₀, hW₀, rfl⟩).1
  have hxnorm := (mem_normalizedNonpositiveSet x).mp hxK
  refine ⟨mixedWeakEquiv x, ?_, ?_, ?_⟩
  · exact Submodule.mem_sInf.mpr fun W hW => (Set.mem_sInter.mp hx _ ⟨W, hW, rfl⟩).2
  · intro hz
    have hs : x.2 = 0 := congrArg Prod.snd hz
    rw [hs, norm_zero] at hxnorm
    exact zero_ne_one hxnorm.2
  · rw [pairing_self_nonpos_iff]
    change ‖(mixedWeakEquiv x : H × E).1‖ ≤ ‖x.2‖
    rw [hxnorm.2]
    exact hxnorm.1

#print axioms isClosed_mixedWeakPreimage
#print axioms exists_normalizedNonpositive_of_mem
#print axioms exists_nonpositive_mem_sInf

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
