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

omit [Fintype ι] [IsNoetherianRing R] in
private theorem gradedCech_exactAt_quotient
    {M N : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {D : ℤ → Submodule R M} {E : ℤ → Submodule R N} [PolyGradedSMul ι D] [PolyGradedSMul ι E]
    [Decomposition D] [Decomposition E]
    {g : M →ₗ[MvPolynomial ι R] N} (hg : IsGradedMap D E g) (hs : Function.Surjective g)
    (n : ℤ) (q : ℕ)
    (hK : (homLocDatum (ι := ι) (grSub D (LinearMap.ker g)) n).ExactAt (q + 1))
    (hD : (homLocDatum (ι := ι) D n).ExactAt q) :
    (homLocDatum (ι := ι) E n).ExactAt q := by
  let K := LinearMap.ker g
  let A := grSub D K
  letI : Decomposition A := grSubDecomposition hg.isHomogeneous_ker
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

private theorem exists_surjective_homLocMap_empty_of_saturating
    {M N : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {D : ℤ → Submodule R M} {E : ℤ → Submodule R N} [PolyGradedSMul ι D] [PolyGradedSMul ι E]
    [Decomposition D] [Decomposition E] [Module.Finite (MvPolynomial ι R) M]
    {g : M →ₗ[MvPolynomial ι R] N} (hg : IsGradedMap D E g)
    (hsat : ∀ (i : ι) (y : N), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range g)
    (hsep : ∀ n : ℤ, (homLocDatum (ι := ι) E n).ExactBot) :
    ∃ b : ℤ, ∀ n, b ≤ n → Function.Surjective (homLocMap hg ∅ n) := by
  let K := LinearMap.ker g
  let A := grSub D K
  letI : Decomposition A := grSubDecomposition hg.isHomogeneous_ker
  letI : Module.Finite (MvPolynomial ι R) K := inferInstance
  obtain ⟨a, ha⟩ := exists_gradedCech_exactAt_of_largeDegree (ι := ι) (R := R) A
  obtain ⟨b, hb⟩ := exists_gradedCech_exactAt_of_largeDegree (ι := ι) (R := R) D
  have hi : IsGradedMap A D K.subtype := fun _ _ hz => hz
  have he : Function.Exact K.subtype g := by
    intro x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
  refine ⟨max a b, fun n hn y => ?_⟩
  classical
  let C := homLocDatum (ι := ι) D n
  let Q := homLocDatum (ι := ι) E n
  let p := homLocDatumMap hg n
  have liftChart (s : Finset ι) (hs : s.card = 1) :
      ∃ x : C.obj s, p.app s x = Q.res (Finset.empty_subset s) y := by
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    have surj : Function.Surjective (homLocMap hg {i} n) :=
      homLocMap_surjective_of hg (fun z => (hsat i z).imp fun k hk => by
        simpa only [xProd, Finset.prod_singleton] using hk) n
    exact surj (Q.res (Finset.empty_subset {i}) y)
  choose x hx using liftChart
  let c : C.Cochain := fun s => if hs : s.card = 1 then x s hs else 0
  have hc : C.IsDeg c 0 := fun _ hs => dif_neg hs
  exact FinsetCechDatum.lift_bot_of_chase (homLocDatumMap hi n) p
    (fun s _ z => (homLocMap_exact hi hg he s n).apply_apply_eq_zero z)
    (fun s _ z hz => (homLocMap_exact hi hg he s n z).mp hz)
    (fun _ _ => homLocMap_injective_of hi (fun z hz => ⟨0, by
      have e : z = 0 := K.injective_subtype (hz.trans (map_zero K.subtype).symm)
      rw [e, smul_zero]⟩) n)
    (ha n (le_of_max_le_left hn) 1) (hb n (le_of_max_le_right hn) 0)
    (hsep n) y c hc (fun s hs => by
      change p.app s (if h : s.card = 1 then x s h else 0) = _
      rw [dif_pos hs]
      exact hx s hs)

/-- A graded map from a finite module that is surjective on the coordinate charts
is eventually surjective in each degree when the target sections are separated. -/
theorem exists_largeDegree_preimage_of_saturating
    {M N : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {D : ℤ → Submodule R M} {E : ℤ → Submodule R N} [PolyGradedSMul ι D] [PolyGradedSMul ι E]
    [Decomposition D] [Decomposition E] [Module.Finite (MvPolynomial ι R) M]
    {g : M →ₗ[MvPolynomial ι R] N} (hg : IsGradedMap D E g)
    (hsat : ∀ (i : ι) (y : N), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range g)
    (hsep : ∀ n : ℤ, (homLocDatum (ι := ι) E n).ExactBot) :
    ∃ b : ℤ, ∀ n, b ≤ n → ∀ y ∈ E n, ∃ x ∈ D n, g x = y := by
  obtain ⟨b, hb⟩ := exists_surjective_homLocMap_empty_of_saturating hg hsat hsep
  refine ⟨b, fun n hn y hy => ?_⟩
  let z := homLocMk E (∅ : Finset ι) n 0 ⟨y, by simpa only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
    using hy⟩
  obtain ⟨v, hv⟩ := hb n hn z
  obtain ⟨k, x, hx⟩ := exists_homLocMk D v
  have e := (congrArg (homLocMap hg ∅ n) hx).trans hv
  rw [homLocMap_mk] at e
  have ef : ModuleFraction.frac (xProd R (∅ : Finset ι)) k (g x.1) =
      ModuleFraction.frac (xProd R (∅ : Finset ι)) 0 y := congrArg Subtype.val e
  obtain ⟨_, he⟩ := ModuleFraction.frac_eq_iff.mp ef
  exact ⟨x.1, by simpa only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] using x.2,
    by simpa only [xProd, Finset.prod_empty, one_pow, one_smul] using he⟩

end GlobalTheory
