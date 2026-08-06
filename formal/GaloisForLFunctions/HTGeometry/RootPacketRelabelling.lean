import GaloisForLFunctions.HTGeometry.SeparableInteractionTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.SiteFactorLiftedSpectrum

/-!
# Root packets of a Hermitian matrix differ by a relabelling

The canonical eigenvalue enumeration of a Hermitian matrix is one root packet
among many.  Any other real packet with the same characteristic root multiset is
a relabelling of it, so projective spectral properties transfer between the two.

This is what lets a spectrum assembled by hand — the concatenation of the
spectra of several non-interacting blocks — inherit maximal projective
independence from the canonical enumeration of the block-diagonal matrix.
-/

open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The characteristic roots of a Hermitian matrix are exactly its canonical
eigenvalues, with multiplicity. -/
theorem hermitianEigenvalues_rootMultiset {I : Type*} [Fintype I]
    [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    Finset.univ.val.map (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) =
      H.charpoly.roots := by
  rw [hH.charpoly_eq]
  rw [← Polynomial.roots_multiset_prod_X_sub_C
    (Finset.univ.val.map (fun i => ((hH.eigenvalues i : ℝ) : ℂ)))]
  congr 1
  rw [Multiset.map_map]
  rfl

/-- **Relabelling of root packets.**  A real packet with the same
characteristic root multiset as the canonical eigenvalues inherits maximal
projective independence from them. -/
theorem maximallyProjectiveEnergy_of_rootMultiset {I : Type*} [Fintype I]
    [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) (e : I → ℝ)
    (hroots : Finset.univ.val.map (fun i => ((e i : ℝ) : ℂ)) =
      H.charpoly.roots) :
    MaximallyProjectiveEnergy e := by
  classical
  have hinjEig : Function.Injective hH.eigenvalues :=
    MaximallyProjectiveEnergy.injective hmax
  have heq : Finset.univ.val.map (fun i => ((e i : ℝ) : ℂ)) =
      Finset.univ.val.map (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [hroots, hermitianEigenvalues_rootMultiset hH]
  have hnodup :
      (Finset.univ.val.map (fun i => ((e i : ℝ) : ℂ))).Nodup := by
    rw [heq]
    refine Finset.univ.nodup.map ?_
    intro a b hab
    exact hinjEig (Complex.ofReal_injective hab)
  have hinjE : Function.Injective e := by
    intro a b hab
    refine Multiset.inj_on_of_nodup_map hnodup a (Finset.mem_univ a) b
      (Finset.mem_univ b) ?_
    exact_mod_cast hab
  have hrange : Set.range e = Set.range hH.eigenvalues := by
    ext x
    have hmem : ∀ (f : I → ℝ) (y : ℝ),
        ((y : ℝ) : ℂ) ∈ Finset.univ.val.map (fun i => ((f i : ℝ) : ℂ)) ↔
          y ∈ Set.range f := by
      intro f y
      simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
        Set.mem_range]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Complex.ofReal_injective hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    rw [← hmem e x, ← hmem hH.eigenvalues x, heq]
  let σ : I ≃ I :=
    (Equiv.ofInjective e hinjE).trans
      ((Equiv.setCongr hrange).trans
        (Equiv.ofInjective hH.eigenvalues hinjEig).symm)
  have hcomp : ∀ i, hH.eigenvalues (σ i) = e i := by
    intro i
    show hH.eigenvalues
      ((Equiv.ofInjective hH.eigenvalues hinjEig).symm
        ((Equiv.setCongr hrange) ((Equiv.ofInjective e hinjE) i))) = e i
    rw [Equiv.apply_ofInjective_symm hinjEig]
    rfl
  have htransfer := maximallyProjectiveEnergy_equiv σ hmax
  have hfun : (fun i => hH.eigenvalues (σ i)) = e := funext hcomp
  rwa [hfun] at htransfer

end

end GaloisForLFunctions.HTGeometry
