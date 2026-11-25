import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedPresentations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ModuleFractionLocalization

/-! Localizing at a product of coordinates preserves the integer grading. -/

noncomputable section

open DirectSum MvPolynomial

namespace GlobalTheory

open ModuleFraction (frac frac_eq_zero_iff frac_add_pow_smul)

variable {ι : Type*} {R : Type*} [CommRing R]

variable (R) in
abbrev xProd (s : Finset ι) : MvPolynomial ι R := ∏ i ∈ s, X i

variable (R) in
theorem xProd_mem (s : Finset ι) : xProd R s ∈ polyGrading ι R s.card := by
  simpa using SetLike.prod_mem_graded (polyGrading ι R) (fun _ => 1) X
    (F := s) fun i _ => X_mem_polyGrading i

variable (R) in
theorem xProd_pow_mem (s : Finset ι) (k : ℕ) :
    xProd R s ^ k ∈ polyGrading ι R (k * s.card) := by
  simpa using SetLike.pow_mem_graded k (xProd_mem R s)

variable {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M] (D : ℤ → Submodule R M) [PolyGradedSMul ι D]

omit [IsScalarTower R (MvPolynomial ι R) M] in
theorem xProd_pow_smul_mem {s : Finset ι} {n : ℤ} {k : ℕ} {m : M} (hm : m ∈ D (n + k * s.card))
    (j : ℕ) : xProd R s ^ j • m ∈ D (n + (k + j : ℕ) * s.card) := by
  have h := grSMul_mem D (xProd_pow_mem R s j) hm
  rw [show n + ((k + j : ℕ) : ℤ) * s.card = n + k * s.card + j * s.card by push_cast; ring]
  exact h

/-- The degree-`n` part, whose fractions with denominator power `k` have
numerators in degree `n + k * s.card`. -/
def homLoc (s : Finset ι) (n : ℤ) : Submodule R (LocalizedModule.Away (xProd R s) M) where
  carrier := {z | ∃ k : ℕ, ∃ m ∈ D (n + k * s.card), frac (xProd R s) k m = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨k, m, hm, rfl⟩ ⟨j, m', hm', rfl⟩
    refine ⟨k + j, xProd R s ^ j • m + xProd R s ^ k • m',
      add_mem (xProd_pow_smul_mem D hm j) (add_comm j k ▸ xProd_pow_smul_mem D hm' k), ?_⟩
    rw [map_add, frac_add_pow_smul, add_comm k j, frac_add_pow_smul]
  smul_mem' := by
    rintro r _ ⟨k, m, hm, rfl⟩
    exact ⟨k, r • m, Submodule.smul_mem _ r hm, LinearMap.map_smul_of_tower _ r m⟩

theorem frac_mem_homLoc {s : Finset ι} {n d : ℤ} {k : ℕ} {m : M} (hm : m ∈ D d)
    (h : d = n + k * s.card) : frac (xProd R s) k m ∈ homLoc D s n :=
  ⟨k, m, h ▸ hm, rfl⟩

theorem exists_frac_of_mem_homLoc {s : Finset ι} {n : ℤ} {z : LocalizedModule.Away (xProd R s) M}
    (hz : z ∈ homLoc D s n) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ m ∈ D (n + k * s.card), frac (xProd R s) k m = z := by
  obtain ⟨k₀, m, hm, rfl⟩ := hz
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨_, xProd_pow_smul_mem D hm j, frac_add_pow_smul _ _ _ _⟩

instance homLoc.polyGradedSMul (s : Finset ι) : PolyGradedSMul ι (homLoc D s) where
  smul_mem := by
    rintro d n p _ hp ⟨k, m, hm, rfl⟩
    rw [← map_smul]
    exact frac_mem_homLoc D (grSMul_mem D hp hm) (by rw [vadd_eq_add]; ring)

instance homLoc.decomposition [Decomposition D] (s : Finset ι) : Decomposition (homLoc D s) :=
  IsInternal.chooseDecomposition _ <| gradedIsInternal _
    (fun T v hv h j hj => by
      choose! k hk using fun i hi => exists_frac_of_mem_homLoc D (hv i hi)
      choose! m hm e using fun i hi => hk i hi (T.sup k) (Finset.le_sup hi)
      rw [← Finset.sum_congr rfl e, ← map_sum, frac_eq_zero_iff] at h
      obtain ⟨l, hl⟩ := h
      rw [← e j hj, frac_eq_zero_iff]
      refine ⟨l, ?_⟩
      let d : ℤ := ((T.sup k + l : ℕ) : ℤ) * s.card
      have hproj : gradedProj D (j + d) (∑ i ∈ T, xProd R s ^ l • m i) =
          xProd R s ^ l • m j := by
        rw [map_sum, Finset.sum_eq_single j
          (fun i hi ne => gradedProj_of_mem_ne D (xProd_pow_smul_mem D (hm i hi) l) (by omega))
          (fun hn => absurd hj hn), gradedProj_of_mem D (xProd_pow_smul_mem D (hm j hj) l)]
      rw [← hproj, ← Finset.smul_sum, hl, map_zero])
    fun z => by
      obtain ⟨k, m, rfl⟩ := ModuleFraction.exists_frac z
      induction m using Decomposition.inductionOn D with
      | zero => rw [map_zero]; exact zero_mem _
      | @homogeneous n m =>
        exact Submodule.mem_iSup_of_mem (n - k * s.card) (frac_mem_homLoc D m.2 (by ring))
      | add a b ha hb => rw [map_add]; exact add_mem ha hb

variable (R) in
theorem xProd_dvd {s t : Finset ι} (h : s ⊆ t) : xProd R s ∣ xProd R t :=
  Finset.prod_dvd_prod_of_subset _ _ _ h

theorem isGradedMap_localizationRestrict {s t : Finset ι} (h : s ⊆ t) :
    IsGradedMap (homLoc D s) (homLoc D t) (ModuleFraction.restrict (xProd_dvd R h)) := by
  classical
  rintro n _ ⟨k, m, hm, rfl⟩
  have ht : xProd R t = xProd R (t \ s) * xProd R s := (Finset.prod_sdiff h).symm
  rw [ModuleFraction.restrict_frac _ ht]
  refine frac_mem_homLoc D (grSMul_mem D (xProd_pow_mem R (t \ s) k) hm) ?_
  rw [← Finset.card_sdiff_add_card_eq_card h]
  push_cast
  ring

variable {D}
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N] {E : ℤ → Submodule R N} [PolyGradedSMul ι E]
  {f : M →ₗ[MvPolynomial ι R] N}

theorem IsGradedMap.localizationMap (hf : IsGradedMap D E f) (s : Finset ι) :
    IsGradedMap (homLoc D s) (homLoc E s) (ModuleFraction.map (xProd R s) f) := by
  rintro n _ ⟨k, m, hm, rfl⟩
  rw [ModuleFraction.map_frac]
  exact frac_mem_homLoc E (hf hm) rfl

end GlobalTheory
