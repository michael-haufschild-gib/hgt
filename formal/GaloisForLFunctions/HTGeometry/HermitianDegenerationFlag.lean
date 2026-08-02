import GaloisForLFunctions.HTGeometry.SimpleSpectrumEigenline
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The degeneration flag of a Hermitian direction

A traceless Hermitian operator `T` on a finite-dimensional complex inner product space is the
direction of a ray `t ↦ exp (t • T)` of observer metrics.  Its asymptotics are recorded by the
family of subspaces

```
eigenSum T c = ⨆_{μ > c} eigenspace T μ,
```

the sum of the eigenspaces whose eigenvalue is above a threshold.  These subspaces form a chain,
they depend only on the direction of `T` — positive rescaling and adding a scalar leave them
unchanged — and their dimensions count the eigenvalues above the threshold.

Everything here is the spectral theorem for a self-adjoint operator, read as a flag.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Module.End

universe u

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The degeneration flag of a Hermitian direction**: the sum of the eigenspaces of `T` with
eigenvalue above `c`. -/
def eigenSum (T : E →ₗ[ℂ] E) (c : ℝ) : Submodule ℂ E :=
  ⨆ μ : ℝ, ⨆ _ : c < μ, Module.End.eigenspace T (μ : ℂ)

variable {T : E →ₗ[ℂ] E}

theorem eigenspace_le_eigenSum {c μ : ℝ} (h : c < μ) :
    Module.End.eigenspace T (μ : ℂ) ≤ eigenSum T c :=
  le_iSup₂ (f := fun (μ : ℝ) (_ : c < μ) => Module.End.eigenspace T (μ : ℂ)) μ h

/-- **The flag is a chain**: a higher threshold gives a smaller subspace. -/
theorem eigenSum_antitone (T : E →ₗ[ℂ] E) : Antitone (eigenSum T) :=
  fun _ _ h => iSup₂_le fun _ hμ => eigenspace_le_eigenSum (lt_of_le_of_lt h hμ)

theorem isChain_range_eigenSum (T : E →ₗ[ℂ] E) :
    IsChain (· ≤ ·) (Set.range (eigenSum T)) := by
  rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ _
  rcases le_total c c' with h | h
  · exact Or.inr (eigenSum_antitone T h)
  · exact Or.inl (eigenSum_antitone T h)

/-! ## The flag depends only on the direction -/

theorem eigenspace_smul {r : ℝ} (hr : r ≠ 0) (μ : ℝ) :
    Module.End.eigenspace ((r : ℂ) • T) ((r * μ : ℝ) : ℂ)
      = Module.End.eigenspace T (μ : ℂ) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  ext x
  simp only [mem_eigenspace_iff, LinearMap.smul_apply, Complex.ofReal_mul, mul_smul]
  exact ⟨fun h => smul_right_injective E hr' h, fun h => congrArg (fun y => (r : ℂ) • y) h⟩

/-- **Positive rescaling does not move the flag.**  The degeneration flag is an invariant of the
direction of the ray, not of its speed. -/
theorem eigenSum_smul {r : ℝ} (hr : 0 < r) (c : ℝ) :
    eigenSum ((r : ℂ) • T) (r * c) = eigenSum T c := by
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => ?_)
  · have hkey : Module.End.eigenspace ((r : ℂ) • T) (μ : ℂ)
        = Module.End.eigenspace T ((r⁻¹ * μ : ℝ) : ℂ) := by
      have := eigenspace_smul (T := T) (ne_of_gt hr) (r⁻¹ * μ)
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul] at this
    rw [hkey]
    exact eigenspace_le_eigenSum ((lt_inv_mul_iff₀ hr).2 hμ)
  · have hkey : Module.End.eigenspace T (μ : ℂ)
        = Module.End.eigenspace ((r : ℂ) • T) ((r * μ : ℝ) : ℂ) :=
      (eigenspace_smul (T := T) (ne_of_gt hr) μ).symm
    rw [hkey]
    exact eigenspace_le_eigenSum (mul_lt_mul_of_pos_left hμ hr)

theorem eigenspace_add_smul_id (a μ : ℝ) :
    Module.End.eigenspace (T + (a : ℂ) • LinearMap.id) ((μ + a : ℝ) : ℂ)
      = Module.End.eigenspace T (μ : ℂ) := by
  ext x
  simp only [mem_eigenspace_iff, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Complex.ofReal_add, add_smul]
  constructor
  · intro h
    exact add_right_cancel h
  · intro h
    rw [h]

/-- **Adding a scalar does not move the flag.**  So normalizing the direction to be traceless — the
determinant-one condition on the observer metrics — loses nothing. -/
theorem eigenSum_add_smul_id (a c : ℝ) :
    eigenSum (T + (a : ℂ) • LinearMap.id) (c + a) = eigenSum T c := by
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => ?_)
  · have hkey : Module.End.eigenspace (T + (a : ℂ) • LinearMap.id) (μ : ℂ)
        = Module.End.eigenspace T ((μ - a : ℝ) : ℂ) := by
      have := eigenspace_add_smul_id (T := T) a (μ - a)
      rwa [sub_add_cancel] at this
    rw [hkey]
    exact eigenspace_le_eigenSum (by linarith)
  · have hkey : Module.End.eigenspace T (μ : ℂ)
        = Module.End.eigenspace (T + (a : ℂ) • LinearMap.id) ((μ + a : ℝ) : ℂ) :=
      (eigenspace_add_smul_id (T := T) a μ).symm
    rw [hkey]
    exact eigenspace_le_eigenSum (by linarith)

/-! ## The flag through an eigenbasis -/

/-- **An eigenspace is spanned by the eigenbasis vectors carrying that eigenvalue.** -/
theorem eigenspace_eq_span_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ E)
    {w : ι → ℝ} (hd : ∀ i, T (b i) = (w i : ℂ) • b i) (μ : ℝ) :
    Module.End.eigenspace T (μ : ℂ) = Submodule.span ℂ (b '' {i | w i = μ}) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hTx : T x = (μ : ℂ) • x := mem_eigenspace_iff.1 hx
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : w i = μ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · have hne : ((w i : ℝ) : ℂ) ≠ (μ : ℂ) := fun hcon => hi (by exact_mod_cast hcon)
      rw [repr_eq_zero_of_eigenvalue_ne b (T := T) (μ := fun i => ((w i : ℝ) : ℂ)) hd hTx hne,
        zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    refine mem_eigenspace_iff.2 ?_
    rw [hd i, show ((w i : ℝ) : ℂ) = (μ : ℂ) from congrArg _ (show w i = μ from hi)]

/-- **The degeneration flag through an eigenbasis**: the subspace at threshold `c` is spanned by the
eigenbasis vectors whose eigenvalue is above `c`. -/
theorem eigenSum_eq_span_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ E)
    {w : ι → ℝ} (hd : ∀ i, T (b i) = (w i : ℂ) • b i) (c : ℝ) :
    eigenSum T c = Submodule.span ℂ (b '' {i | c < w i}) := by
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) ?_
  · rw [eigenspace_eq_span_of_eigenbasis b hd μ]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨i, by simp only [Set.mem_setOf_eq] at hi ⊢; rw [hi]; exact hμ, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact eigenspace_le_eigenSum hi (mem_eigenspace_iff.2 (hd i))

/-! ## The flag through the eigenvector basis of a symmetric operator -/

variable [FiniteDimensional ℂ E]

theorem apply_toBasis_eigenvectorBasis (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (i : Fin n) :
    T ((hT.eigenvectorBasis hn).toBasis i) = ((hT.eigenvalues hn i : ℝ) : ℂ)
      • (hT.eigenvectorBasis hn).toBasis i := by
  rw [OrthonormalBasis.coe_toBasis]
  exact hT.apply_eigenvectorBasis hn i

/-- **An eigenspace is spanned by the eigenvectors of the basis with that eigenvalue.** -/
theorem eigenspace_eq_span (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (μ : ℝ) :
    Module.End.eigenspace T (μ : ℂ)
      = Submodule.span ℂ (hT.eigenvectorBasis hn '' {i | hT.eigenvalues hn i = μ}) := by
  classical
  rw [eigenspace_eq_span_of_eigenbasis (hT.eigenvectorBasis hn).toBasis
    (apply_toBasis_eigenvectorBasis hT hn) μ, OrthonormalBasis.coe_toBasis]

/-- **The degeneration flag through the eigenvector basis**: the subspace at threshold `c` is
spanned by the eigenvectors whose eigenvalue is above `c`. -/
theorem eigenSum_eq_span (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (c : ℝ) :
    eigenSum T c
      = Submodule.span ℂ (hT.eigenvectorBasis hn '' {i | c < hT.eigenvalues hn i}) := by
  classical
  rw [eigenSum_eq_span_of_eigenbasis (hT.eigenvectorBasis hn).toBasis
    (apply_toBasis_eigenvectorBasis hT hn) c, OrthonormalBasis.coe_toBasis]

/-- **The dimension of a member of the flag counts the eigenvalues above the threshold.** -/
theorem finrank_eigenSum (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (c : ℝ) :
    finrank ℂ (eigenSum T c)
      = (Finset.univ.filter fun i : Fin n => c < hT.eigenvalues hn i).card := by
  classical
  rw [eigenSum_eq_span hT hn c]
  have himg : (hT.eigenvectorBasis hn) '' {i | c < hT.eigenvalues hn i}
      = Set.range (fun i : {i : Fin n // c < hT.eigenvalues hn i} => hT.eigenvectorBasis hn i) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [himg]
  have hli : LinearIndependent ℂ
      (fun i : {i : Fin n // c < hT.eigenvalues hn i} => hT.eigenvectorBasis hn i) :=
    ((hT.eigenvectorBasis hn).toBasis.linearIndependent).comp _ Subtype.val_injective
  rw [finrank_span_eq_card hli]
  simp [Fintype.card_subtype]

/-! ## The ends of the flag -/

theorem eigenSum_eq_top_iff (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (c : ℝ) :
    eigenSum T c = ⊤ ↔ ∀ i, c < hT.eigenvalues hn i := by
  classical
  constructor
  · intro h i
    by_contra hcon
    have hcard : (Finset.univ.filter fun j : Fin n => c < hT.eigenvalues hn j).card < n := by
      have hsub : (Finset.univ.filter fun j : Fin n => c < hT.eigenvalues hn j) ⊂ Finset.univ :=
        Finset.ssubset_univ_iff.2 fun hcon' => hcon (by
          have : i ∈ Finset.univ.filter fun j : Fin n => c < hT.eigenvalues hn j := by
            rw [hcon']; exact Finset.mem_univ i
          simpa using this)
      simpa using Finset.card_lt_card hsub
    have hfin : finrank ℂ (eigenSum T c) = n := by rw [h, finrank_top, hn]
    rw [finrank_eigenSum hT hn c] at hfin
    omega
  · intro h
    have hfin : finrank ℂ (eigenSum T c) = n := by
      rw [finrank_eigenSum hT hn c]
      simp [Finset.filter_true_of_mem fun i _ => h i]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfin, hn])

theorem eigenSum_eq_bot_iff (hT : T.IsSymmetric) (hn : finrank ℂ E = n) (c : ℝ) :
    eigenSum T c = ⊥ ↔ ∀ i, hT.eigenvalues hn i ≤ c := by
  classical
  rw [← Submodule.finrank_eq_zero, finrank_eigenSum hT hn c, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  exact ⟨fun h i => not_lt.1 (h (Finset.mem_univ i)), fun h i _ => not_lt.2 (h i)⟩

/-- **Strict descent of the flag**: crossing an eigenvalue strictly shrinks the subspace. -/
theorem eigenSum_lt_eigenSum (hT : T.IsSymmetric) (hn : finrank ℂ E = n) {c c' : ℝ} (h : c ≤ c')
    {i : Fin n} (hi : c < hT.eigenvalues hn i) (hi' : hT.eigenvalues hn i ≤ c') :
    eigenSum T c' < eigenSum T c := by
  classical
  refine Submodule.lt_of_le_of_finrank_lt_finrank (eigenSum_antitone T h) ?_
  rw [finrank_eigenSum hT hn c', finrank_eigenSum hT hn c]
  refine Finset.card_lt_card ⟨Finset.filter_subset_filter _ (Finset.Subset.refl _) |>.trans ?_, ?_⟩
  · exact fun j hj => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact lt_of_le_of_lt h hj
  · intro hsub
    have := hsub (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact absurd hi' (not_le.2 this)

end GaloisForLFunctions.HTGeometry
