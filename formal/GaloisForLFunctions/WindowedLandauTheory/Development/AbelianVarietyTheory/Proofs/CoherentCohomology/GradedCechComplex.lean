import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.HomogeneousModuleLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechComplex

/-! Taking one degree of the coordinate localizations gives a scalar-linear Čech complex. -/

noncomputable section

open CategoryTheory DirectSum HTGeometry MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (D : ℤ → Submodule R M) [PolyGradedSMul ι D]

def homLocMk (s : Finset ι) (n : ℤ) (k : ℕ) :
    D (n + k * s.card) →ₗ[R] homLoc D s n :=
  ((ModuleFraction.frac (xProd R s) k).restrictScalars R).restrict
    fun _ hm => frac_mem_homLoc D hm rfl

theorem exists_homLocMk {s : Finset ι} {n : ℤ} (z : homLoc D s n) :
    ∃ k m, homLocMk D s n k m = z := by
  obtain ⟨_, k, m, hm, rfl⟩ := z
  exact ⟨k, ⟨m, hm⟩, rfl⟩

def homLocRes {s t : Finset ι} (h : s ⊆ t) (n : ℤ) : homLoc D s n →ₗ[R] homLoc D t n :=
  ((ModuleFraction.restrict (xProd_dvd R h)).restrictScalars R).restrict
    fun _ hm => isGradedMap_localizationRestrict D h hm

/-- The Čech datum for the degree-`n` parts of the coordinate localizations. -/
def homLocDatum (n : ℤ) : FinsetCechDatum ι where
  obj s := homLoc D s n
  res h := (homLocRes D h n).toAddMonoidHom
  res_refl s x := Subtype.ext (LinearMap.congr_fun (ModuleFraction.restrict_self (xProd R s)) x.1)
  res_res h h' x := Subtype.ext (LinearMap.congr_fun
    (ModuleFraction.restrict_comp (xProd_dvd R h) (xProd_dvd R h')) x.1)

instance homLocDatumModule (n : ℤ) (s : Finset ι) : Module R ((homLocDatum D n).obj s) :=
  inferInstanceAs (Module R (homLoc D s n))

theorem homLocDatum_res_smul {s t : Finset ι} (h : s ⊆ t) (n : ℤ) (r : R)
    (x : (homLocDatum D n).obj s) :
    (homLocDatum D n).res h (r • x) = r • (homLocDatum D n).res h x :=
  (homLocRes D h n).map_smul r x

def gradedCech [DecidableEq ι] [LinearOrder ι] (n : ℤ) : CochainComplex (ModuleCat R) ℕ :=
  (homLocDatum (ι := ι) D n).linearComplex (R := R) (fun h => homLocDatum_res_smul D h n)

variable {D} {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N] {E : ℤ → Submodule R N} [PolyGradedSMul ι E]
  {f : M →ₗ[MvPolynomial ι R] N}

def homLocMap (hf : IsGradedMap D E f) (s : Finset ι) (n : ℤ) : homLoc D s n →ₗ[R] homLoc E s n :=
  ((ModuleFraction.map (xProd R s) f).restrictScalars R).restrict
    fun _ hm => hf.localizationMap s hm

theorem homLocMap_mk (hf : IsGradedMap D E f) (s : Finset ι) (n : ℤ) (k : ℕ)
    (m : D (n + k * s.card)) :
    homLocMap hf s n (homLocMk D s n k m) = homLocMk E s n k ⟨f m, hf m.2⟩ :=
  Subtype.ext (ModuleFraction.map_frac (xProd R s) f k m)

def homLocDatumMap (hf : IsGradedMap D E f) (n : ℤ) :
    (homLocDatum (ι := ι) D n).Hom (homLocDatum (ι := ι) E n) where
  app s := (homLocMap hf s n).toAddMonoidHom
  comm h x := Subtype.ext (ModuleFraction.map_restrict (xProd_dvd R h) f x.1).symm

theorem homLocMap_injective_of (hf : IsGradedMap D E f) {s : Finset ι}
    (h : ∀ m, f m = 0 → ∃ k : ℕ, xProd R s ^ k • m = 0) (n : ℤ) :
    Function.Injective (homLocMap hf s n) :=
  fun _ _ e => Subtype.ext (ModuleFraction.map_injective_of h (congrArg Subtype.val e))

variable [Decomposition D] [Decomposition E]

theorem homLocMap_surjective_of (hf : IsGradedMap D E f) {s : Finset ι}
    (h : ∀ y, ∃ k : ℕ, xProd R s ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    Function.Surjective (homLocMap hf s n) := by
  intro y
  obtain ⟨x, hx⟩ := ModuleFraction.map_surjective_of h y.1
  refine ⟨⟨gradedProj (homLoc D s) n x, gradedProj_mem _ n x⟩, Subtype.ext ?_⟩
  have e := (hf.localizationMap s).proj_apply n x
  rw [hx, gradedProj_of_mem _ y.2] at e
  exact e.symm

theorem homLocMap_exact {P : Type} [AddCommGroup P] [Module R P]
    [Module (MvPolynomial ι R) P] [IsScalarTower R (MvPolynomial ι R) P]
    {C : ℤ → Submodule R P} [PolyGradedSMul ι C] {g : N →ₗ[MvPolynomial ι R] P}
    (hf : IsGradedMap D E f) (hg : IsGradedMap E C g) (h : Function.Exact f g)
    (s : Finset ι) (n : ℤ) : Function.Exact (homLocMap hf s n) (homLocMap hg s n) := by
  have he := ModuleFraction.map_exact (xProd R s) h
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (he y.1).1 (congrArg Subtype.val hy)
    refine ⟨⟨gradedProj (homLoc D s) n x, gradedProj_mem _ n x⟩, Subtype.ext ?_⟩
    have e := (hf.localizationMap s).proj_apply n x
    rw [hx, gradedProj_of_mem _ y.2] at e
    exact e.symm
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (he.apply_apply_eq_zero x.1)

/-- Killing kernel and cokernel by powers of a coordinate makes the Čech map
bijective on every intersection containing that coordinate. -/
theorem homLocMap_bijective_of_X (hf : IsGradedMap D E f) {s : Finset ι} {i : ι} (hi : i ∈ s)
    (hker : ∀ m, f m = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • m = 0)
    (hrange : ∀ y, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ LinearMap.range f) (n : ℤ) :
    Function.Bijective (homLocMap hf s n) := by
  obtain ⟨c, hc⟩ : ∃ c, xProd R s = c * X i :=
    exists_eq_mul_left_of_dvd (Finset.dvd_prod_of_mem _ hi)
  refine ⟨homLocMap_injective_of hf (fun m hm => (hker m hm).imp fun k hk => ?_) n,
    homLocMap_surjective_of hf (fun y => (hrange y).imp fun k hk => ?_) n⟩
  · rw [hc, mul_pow, mul_smul, hk, smul_zero]
  · rw [hc, mul_pow, mul_smul]
    exact (LinearMap.range f).smul_mem _ hk

end GlobalTheory
