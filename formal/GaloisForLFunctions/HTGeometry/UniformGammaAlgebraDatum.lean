import GaloisForLFunctions.HTGeometry.UniformGammaPresentationNonzero
import GaloisForLFunctions.HTGeometry.GammaFieldRatDatum

/-!
# The datum of an element of the Gamma jet algebra, uniformly on a tube

Clearing a nonzero element of the differential algebra generated over `ℂ(s)` by `Γ` presents it as an
analytic germ that is a `Γ`-polynomial with jet-polynomial coefficients.  Such a germ has a residue
against an integer Gamma shape, and the residue is nonzero — uniformly for `0 < σ ≤ M`.

The per-line statement holds for one abscissa at a time and lets the height threshold depend on it;
here one threshold serves the whole tube.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance uniformGammaAlgebraDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance uniformGammaAlgebraIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance uniformGammaAlgebraDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance uniformGammaAlgebraComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance uniformGammaAlgebraRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- **The datum of a nonzero element of the Gamma jet algebra, uniformly on a tube.**  Its cleared
analytic germ has a nonzero residue against one integer Gamma shape, with a single height threshold
for all abscissas in `(0, M]`. -/
theorem exists_tubeLimit_gammaAlgebra_datum {M : ℝ} (hM : 0 < M) {y : upperEndMeroField}
    (hy : y ∈ differentialJetAlgebra (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hy0 : y ≠ 0) :
    ∃ (q : Polynomial ℂ) (W : upperEndAnalyticSubring) (G : ℂ → ℂ) (k A e : ℤ) (r : ℂ),
      q ≠ 0 ∧ r ≠ 0
        ∧ upperEndPolyToMero q * y = algebraMap upperEndAnalyticSubring upperEndMeroField W
        ∧ upperEndAnalyticSubring.subtype W = Germ.coeRingHom upperEndFilter G
        ∧ TubeLimit M (fun σ t => G ((σ : ℂ) + (t : ℂ) * Complex.I)
            / gammaShapeZ σ k A e t) r := by
  classical
  obtain ⟨q, N, u, C, hq, huinj, heq, hCdata⟩ := exists_gammaAlgebra_clearing hy
  choose Mm Kf p E hEinj hCgerm using hCdata
  set G : ℂ → ℂ := fun z => ∑ j : Fin N, Complex.Gamma z ^ u j
    * ∑ α : Fin (Mm j), (p j α).eval z
      * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i with hG
  have hgammaSub : upperEndAnalyticSubring.subtype gammaUpperAnalytic
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => Complex.Gamma z) := rfl
  have hWgerm : upperEndAnalyticSubring.subtype (∑ j : Fin N, gammaUpperAnalytic ^ u j * C j)
      = Germ.coeRingHom upperEndFilter G := by
    have hterm : ∀ j : Fin N,
        upperEndAnalyticSubring.subtype (gammaUpperAnalytic ^ u j * C j)
          = Germ.coeRingHom upperEndFilter (fun z : ℂ => Complex.Gamma z ^ u j
            * ∑ α : Fin (Mm j), (p j α).eval z
              * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i) := by
      intro j
      rw [map_mul, map_pow, hCgerm j, hgammaSub, ← map_pow, ← map_mul]
      refine congrArg _ ?_
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply]
    rw [map_sum, Finset.sum_congr rfl fun j _ => hterm j, ← map_sum, hG]
    refine congrArg _ ?_
    funext z
    simp only [Finset.sum_apply]
  have hWne : (∑ j : Fin N, gammaUpperAnalytic ^ u j * C j) ≠ 0 := by
    intro h
    rw [h, map_zero] at heq
    exact mul_ne_zero (fun hz => hq (upperEndPolyToMero_injective (by rw [hz, map_zero]))) hy0 heq
  -- some coefficient survives, else the whole germ vanishes
  have hne : ∃ (j : Fin N) (α : Fin (Mm j)), p j α ≠ 0 := by
    by_contra hcon
    have hall : ∀ (j : Fin N) (α : Fin (Mm j)), p j α = 0 := by
      intro j α
      by_contra hne'
      exact hcon ⟨j, α, hne'⟩
    refine hWne (Finset.sum_eq_zero fun j _ => ?_)
    have hzerofun : (fun z : ℂ => ∑ α : Fin (Mm j), (p j α).eval z
        * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i)
        = (0 : ℂ → ℂ) := by
      funext z
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [hall j α]
      simp
    have h0 : upperEndAnalyticSubring.subtype (C j) = 0 := by
      rw [hCgerm j, hzerofun, map_zero]
    have hCj : C j = 0 := Subtype.ext (by simpa using h0)
    rw [hCj, mul_zero]
  -- one jet range and one degree bound for all coefficients
  set Kmax : ℕ := Finset.univ.sup Kf with hKmax
  have hKle : ∀ j : Fin N, Kf j ≤ Kmax := fun j => Finset.le_sup (Finset.mem_univ j)
  set dmax : ℕ := Finset.univ.sup
    (fun j : Fin N => Finset.univ.sup (fun α : Fin (Mm j) => (p j α).natDegree)) with hdmax
  have hdegle : ∀ (j : Fin N) (α : Fin (Mm j)), (p j α).natDegree ≤ dmax := by
    intro j α
    refine le_trans ?_ (Finset.le_sup (f := fun j : Fin N =>
      Finset.univ.sup (fun α : Fin (Mm j) => (p j α).natDegree)) (Finset.mem_univ j))
    exact Finset.le_sup (f := fun α : Fin (Mm j) => (p j α).natDegree) (Finset.mem_univ α)
  obtain ⟨k, A, e, r, hr, hlim⟩ := exists_tubeLimit_gammaPresentation_residue_prune hM Mm Kf
    Kmax dmax hKle u huinj p E hdegle hEinj hne
  refine ⟨q, ∑ j : Fin N, gammaUpperAnalytic ^ u j * C j, G, k, A, e, r, hq, hr, heq, hWgerm, ?_⟩
  refine hlim.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ k A e t) ?_
  simp only [hG, gammaLine]

end

end GaloisForLFunctions.HTGeometry
