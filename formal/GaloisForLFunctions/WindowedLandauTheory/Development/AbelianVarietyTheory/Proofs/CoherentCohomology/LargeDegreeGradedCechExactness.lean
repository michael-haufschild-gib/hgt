import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGradedGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FreeGradedCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialCechContraction
import GaloisForLFunctions.HTGeometry.PolynomialTwistedCech
import Mathlib.RingTheory.Polynomial.Basic

/-! The augmented Čech complex of a finite graded polynomial module is exact in large twists. -/

noncomputable section

open DirectSum HTGeometry MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [CommRing R] [IsNoetherianRing R]

private theorem gradedCech_exactAt_quotient
    {M N : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {D : ℤ → Submodule R M} {E : ℤ → Submodule R N} [PolyGradedSMul ι D] [PolyGradedSMul ι E]
    {g : M →ₗ[MvPolynomial ι R] N} (hg : IsGradedMap D E g) (hs : Function.Surjective g)
    (n : ℤ) (q : ℕ)
    (hK : (homLocDatum (ι := ι) (grSub D (LinearMap.ker g)) n).ExactAt (q + 1))
    (hD : (homLocDatum (ι := ι) D n).ExactAt q) :
    (homLocDatum (ι := ι) E n).ExactAt q := by
  let K := LinearMap.ker g
  let A := grSub D K
  have hi : IsGradedMap A D K.subtype := fun _ _ hz => hz
  have he : Function.Exact K.subtype g := by
    intro x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  refine FinsetCechDatum.exactAt_of_chase (homLocDatumMap hi n) (homLocDatumMap hg n) q
    (fun s _ x => (homLocMap_exact hi hg he s n).apply_apply_eq_zero x)
    (fun _ _ => homLocMap_surjective_of hg (fun y => ⟨0, by
      rw [pow_zero, one_smul]
      exact hs y⟩) n)
    (fun s _ y hy => (homLocMap_exact hi hg he s n y).mp hy)
    (fun _ _ => homLocMap_injective_of hi (fun x hx => ⟨0, by
      have ex : x = 0 := K.injective_subtype (hx.trans (map_zero K.subtype).symm)
      rw [ex, smul_zero]⟩) n)
    hK hD

/-- Resolve successively by finite homogeneous free covers. At each step the required
exactness of the kernel is one cochain degree higher. -/
theorem exists_gradedCech_exactAt_of_largeDegree {M : Type} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D]
    [Module.Finite (MvPolynomial ι R) M] :
    ∃ b : ℤ, ∀ n, b ≤ n → ∀ q, (homLocDatum (ι := ι) D n).ExactAt q := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    exact ⟨0, fun n _ q => FinsetCechDatum.exactAt_of_card_lt (homLocDatum D n) (by simp)⟩
  letI := hι
  suffices aux : ∀ j : ℕ, ∀ (N : Type) [AddCommGroup N] [Module R N]
      [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N]
      (E : ℤ → Submodule R N) [PolyGradedSMul ι E] [Decomposition E]
      [Module.Finite (MvPolynomial ι R) N], ∃ b : ℤ, ∀ n, b ≤ n → ∀ q : ℕ,
        Fintype.card ι ≤ q + j → (homLocDatum (ι := ι) E n).ExactAt q by
    obtain ⟨b, hb⟩ := aux (Fintype.card ι) M D
    exact ⟨b, fun n hn q => hb n hn q (by omega)⟩
  intro j
  induction j with
  | zero =>
    intro N _ _ _ _ E _ _ _
    exact ⟨0, fun n _ q h => FinsetCechDatum.exactAt_of_card_lt (homLocDatum E n) (by omega)⟩
  | succ j ih =>
    intro N _ _ _ _ E _ _ _
    obtain ⟨a, d, g, hg, hs⟩ := exists_graded_surjection (ι := ι) E
    let F := grFree ι R d
    let K := LinearMap.ker g
    let A := grSub F K
    letI : Decomposition A := grSubDecomposition hg.isHomogeneous_ker
    letI : Module.Finite (MvPolynomial ι R) K := inferInstance
    obtain ⟨b, hb⟩ := ih K A
    let c : ℤ := ∑ k, max (d k) 0
    have hc (k : Fin a) : d k ≤ c :=
      (le_max_left _ _).trans (Finset.single_le_sum (fun l _ => le_max_right (d l) 0) (Finset.mem_univ k))
    refine ⟨max b c, fun n hn q hq => gradedCech_exactAt_quotient hg hs n q
      (hb n (le_of_max_le_left hn) (q + 1) (by omega)) ?_⟩
    refine freeGradedCech_exactAt d n q fun k => polynomialCech_exactAt_of_nonneg (R := R) ?_ q
    have e := (hc k).trans (le_of_max_le_right hn)
    omega

end GlobalTheory
