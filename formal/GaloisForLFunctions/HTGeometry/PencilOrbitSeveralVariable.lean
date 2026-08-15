import GaloisForLFunctions.HTGeometry.PencilLineRestriction

/-!
# The periodic-pencil orbit lemma in several variables

A pencil carrier is a source composed with the exponential of a linear form.  Along the line
`z = z₀ + s·w` it becomes the one-variable orbit carrier with frequency `L(w)` and shift
`L(z₀) + sh`, so the several-variable statement follows from the one-variable orbit lemma applied to
the *union* of the shift classes over a countable set of base points — a countable member set,
indexed by the classes themselves so that distinctness is automatic.

Restricting the base points to a box with rational-Gaussian sides keeps the member set countable
while leaving enough base points to detect a nonzero relation.
-/

open MvPolynomial Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The rational Gaussian numbers: a countable infinite subset of `ℂ`. -/
def gaussianRat : Set ℂ := {z | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * Complex.I}

theorem infinite_gaussianRat : gaussianRat.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun q : ℚ => ((q : ℂ))) ?_ ?_
  · intro a b hab
    simp only at hab
    exact_mod_cast hab
  · intro q
    exact ⟨q, 0, by simp⟩

theorem countable_gaussianRat : gaussianRat.Countable := by
  have himg : gaussianRat = (fun p : ℚ × ℚ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) '' Set.univ := by
    ext z
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a, b), Set.mem_univ _, rfl⟩
    · rintro ⟨p, -, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
  rw [himg]
  exact Set.Countable.image Set.countable_univ _

variable {d L : ℕ} {ι : Type}

/-- The carrier of a pencil member: the source along the exponential of its linear form. -/
def pencilFam (Lf : Fin L → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (src : ι → Fin L) (sh : ι → ℂ)
    (C : Fin L → sourceBox) : ι → (Fin d → ℂ) → ℂ :=
  fun i z => jetSeriesFun (boxSeq (C (src i))) 0 (Complex.exp (Lf (src i) z + sh i))

/-- **The periodic-pencil orbit lemma.**  For finitely many linear forms nonvanishing on the
derivation direction, and a countable set of members with pairwise distinct translation classes on
each form, there are entire sources whose pencil family satisfies no algebraic differential equation
over `ℂ(z₁,…,z_d)` for the constant derivation `D_w`. -/
theorem exists_source_pencil_jointlyDirHypertranscendental [Countable ι] [DecidableEq ι]
    [Nonempty ι] (w : Fin d → ℂ) (Lf : Fin L → ((Fin d → ℂ) →ₗ[ℂ] ℂ))
    (hw : ∀ j, Lf j w ≠ 0) (src : ι → Fin L) (sh : ι → ℂ)
    (hdist : ∀ i i' : ι, src i = src i' → i ≠ i' → Complex.exp (sh i) ≠ Complex.exp (sh i')) :
    ∃ C : Fin L → sourceBox, JointlyDirHypertranscendental w (pencilFam Lf src sh C) := by
  classical
  set Z : Set (Fin d → ℂ) := Set.pi Set.univ fun _ => gaussianRat with hZ
  have hZcount : Z.Countable := Set.countable_univ_pi fun _ => countable_gaussianRat
  have hZne : Z.Nonempty := ⟨fun _ => 0, fun k _ => ⟨0, 0, by simp⟩⟩
  set node : ι × ↥Z → Fin L × ℂ :=
    fun p => (src p.1, Complex.exp (Lf (src p.1) (p.2 : Fin d → ℂ) + sh p.1)) with hnode
  set Tset : Set (Fin L × ℂ) := Set.range node with hT
  haveI : Countable ↥Z := hZcount.to_subtype
  have hTcount : Tset.Countable := Set.countable_range node
  haveI : Countable ↥Tset := hTcount.to_subtype
  haveI : Nonempty ↥Tset := by
    obtain ⟨z₀, hz₀⟩ := hZne
    exact ⟨⟨node (Classical.arbitrary ι, ⟨z₀, hz₀⟩), Set.mem_range_self _⟩⟩
  haveI : DecidableEq ↥Tset := Classical.decEq _
  have hexp_ne : ∀ p : ↥Tset, (p : Fin L × ℂ).2 ≠ 0 := by
    intro p
    obtain ⟨q, hq⟩ := p.2
    rw [← hq]
    exact Complex.exp_ne_zero _
  set src' : ↥Tset → Fin L := fun p => (p : Fin L × ℂ).1 with hsrc'
  set sh' : ↥Tset → ℂ := fun p => Complex.log (p : Fin L × ℂ).2 with hsh'
  have hexp_sh' : ∀ p : ↥Tset, Complex.exp (sh' p) = (p : Fin L × ℂ).2 := by
    intro p
    rw [hsh', Complex.exp_log (hexp_ne p)]
  have hdist' : ∀ p q : ↥Tset, src' p = src' q → p ≠ q →
      Complex.exp (sh' p) ≠ Complex.exp (sh' q) := by
    intro p q hsrc hne
    rw [hexp_sh', hexp_sh']
    intro hval
    exact hne (Subtype.ext (Prod.ext hsrc hval))
  obtain ⟨C, hC⟩ := exists_source_jointlyHypertranscendental_countable
    (fun j => Lf j w) (fun j => hw j) src' sh' hdist'
  refine ⟨C, ?_⟩
  refine jointlyDirHypertranscendental_of_lines_mem w (pencilFam Lf src sh C)
    (fun _ => gaussianRat) (fun _ => infinite_gaussianRat) ?_
  intro z₀ hz₀
  set φ : ι → ↥Tset := fun i => ⟨node (i, ⟨z₀, hz₀⟩), Set.mem_range_self _⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro i i' h
    have hval := congrArg (fun p : ↥Tset => (p : Fin L × ℂ)) h
    rw [hφ] at hval
    simp only [hnode] at hval
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hval
    by_contra hne
    refine hdist i i' h1 hne ?_
    have hcancel : Complex.exp (Lf (src i) z₀) * Complex.exp (sh i) =
        Complex.exp (Lf (src i') z₀) * Complex.exp (sh i') := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      exact h2
    rw [h1] at hcancel
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hcancel
  have hfun : lineRestrict w (pencilFam Lf src sh C) z₀ =
      (orbFun (fun j => Lf j w) src' sh' C) ∘ φ := by
    funext i s
    show jetSeriesFun (boxSeq (C (src i))) 0
        (Complex.exp (Lf (src i) (z₀ + s • w) + sh i)) =
      jetSeriesFun (boxSeq (C (src' (φ i)))) 0
        (Complex.exp ((fun j => Lf j w) (src' (φ i)) * s + sh' (φ i)))
    have hsrceq : src' (φ i) = src i := rfl
    rw [hsrceq]
    congr 1
    have hlin : Lf (src i) (z₀ + s • w) = Lf (src i) z₀ + s * Lf (src i) w := by
      rw [map_add, map_smul, smul_eq_mul]
    rw [hlin]
    have hexpφ : Complex.exp (sh' (φ i)) =
        Complex.exp (Lf (src i) z₀ + sh i) := by
      rw [hexp_sh' (φ i)]
    have h1 : Complex.exp (Lf (src i) w * s + sh' (φ i))
        = Complex.exp (Lf (src i) w * s) * Complex.exp (sh' (φ i)) := Complex.exp_add _ _
    have h2 : Complex.exp (Lf (src i) z₀ + s * Lf (src i) w + sh i)
        = Complex.exp (Lf (src i) w * s) * Complex.exp (Lf (src i) z₀ + sh i) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [h1, hexpφ, h2]
  rw [hfun]
  exact jointlyHypertranscendental_comp_injective _ φ hφinj hC

end

end GaloisForLFunctions.HTGeometry
