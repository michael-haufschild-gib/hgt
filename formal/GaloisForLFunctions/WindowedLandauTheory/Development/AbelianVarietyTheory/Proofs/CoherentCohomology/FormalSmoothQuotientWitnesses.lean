import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Span

/-! Finite polynomial equations witness formal smoothness of a presented quotient. -/

open MvPolynomial
open scoped Pointwise

namespace GlobalTheory.SmoothDescent

private theorem exists_sum_mul_of_mem_span_range_sq {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]

/-- A formally smooth quotient supplies polynomial formulas for a section of
its first infinitesimal thickening. -/
theorem exists_witnesses_of_formallySmooth_quotient {ι R : Type} [CommRing R] {r : ℕ}
    (g : Fin r → MvPolynomial ι R)
    (hs : Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g))) :
    ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R),
      ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) =
        ∑ k, ∑ l, b j k l * (g k * g l) := by
  let I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g)
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I

  obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs
  have hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I := by
    ext x
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

  have hlift : ∀ i : ι, ∃ y : MvPolynomial ι R,
      Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i)) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hlift

  have hdiff : ∀ i, y i - X i ∈ I := by
    intro i
    have h1 := congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)
    rw [AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at h1
    exact Ideal.Quotient.eq.1 h1
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)
  have hy' : ∀ i, X i + ∑ k, a i k * g k = y i := by
    intro i
    have := ha i
    simp only [smul_eq_mul] at this
    rw [this]
    ring

  have hcomp : (Ideal.Quotient.mkₐ R _).comp
      (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) =
      σ.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]
    rfl

  have hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I := by
    intro j
    have hgj : Ideal.Quotient.mkₐ R I (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := AlgHom.congr_fun hcomp (g j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, hK, pow_two] at h2
    exact h2
  choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)
  exact ⟨a, b, hb⟩

/-- Polynomial formulas respecting the defining equations to second order
give formal smoothness of the quotient. -/
theorem formallySmooth_quotient_of_aeval_shift_mem_sq {ι R : Type} [CommRing R] {r : ℕ}
    (g : Fin r → MvPolynomial ι R) (a : ι → Fin r → MvPolynomial ι R)
    (b : Fin r → Fin r → Fin r → MvPolynomial ι R)
    (h : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) :
    Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) := by
  let I := Ideal.span (Set.range g)
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I := Ideal.Quotient.mkₐ R I
  have hkerf : RingHom.ker f.toRingHom = I := Ideal.Quotient.mkₐ_ker R I
  let x : ι → MvPolynomial ι R := fun i => X i + ∑ k, a i k * g k
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ R _).comp (aeval x)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hφ : ∀ p ∈ I, φ p = 0 := by
    have hle : I ≤ RingHom.ker φ := by
      show Ideal.span (Set.range g) ≤ RingHom.ker φ
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      show Ideal.Quotient.mk _ (aeval x (g j)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hkerf, h j, pow_two]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hgI k) (hgI l))
    exact fun p hp => hle hp
  let s := Ideal.Quotient.liftₐ I φ hφ
  refine Algebra.FormallySmooth.of_split f s ?_
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hs : s (Ideal.Quotient.mkₐ R I (X i)) = Ideal.Quotient.mk _ (x i) := by
    show (Ideal.Quotient.liftₐ I φ hφ) (Ideal.Quotient.mk I (X i)) = _
    rw [Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
    show (Ideal.Quotient.mkₐ R _) (aeval x (X i)) = _
    rw [aeval_X]
    rfl
  change f.kerSquareLift (s (f (X i))) = f (X i)
  refine (congrArg f.kerSquareLift hs).trans ((AlgHom.kerSquareLift_mk f (x i)).trans ?_)
  have hv : f (∑ k, a i k * g k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hgI k))
  exact (map_add f _ _).trans ((congrArg (f (X i) + ·) hv).trans (add_zero _))

end GlobalTheory.SmoothDescent
