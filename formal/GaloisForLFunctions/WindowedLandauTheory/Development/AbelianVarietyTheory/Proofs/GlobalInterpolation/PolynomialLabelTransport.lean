import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialLabels

/-! A degree-preserving permutation of prime labels extends by normalized
factorization to monic labels with nonzero constant coefficient. -/

noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

private theorem normalizedFactor_isPrimeLab {f P : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0)
    (hP : P ∈ normalizedFactors f) : IsPrimeLab P.natDegree P := by
  have h := irreducible_of_normalized_factor P hP
  refine ⟨?_, h, ?_, rfl⟩
  · rw [← normalize_normalized_factor P hP]
    exact monic_normalize h.ne_zero
  · intro he
    exact h0 (X_dvd_iff.mp ((X_dvd_iff.mpr he).trans (dvd_of_mem_normalizedFactors hP)))

private theorem prod_normalizedFactors_of_monic {f : (ZMod g)[X]} (hf : f.Monic) :
    (normalizedFactors f).prod = f := by
  have he := Polynomial.leadingCoeff_mul_prod_normalizedFactors f
  rwa [hf.leadingCoeff, C_1, one_mul] at he

private theorem normalizedFactors_prod_prime (M : Multiset (ZMod g)[X])
    (hM : ∀ P ∈ M, IsPrimeLab P.natDegree P) : normalizedFactors M.prod = M := by
  calc
    normalizedFactors M.prod = M.map normalize :=
      normalizedFactors_prod_eq M (fun P hP => (hM P hP).2.1)
    _ = M.map id := Multiset.map_congr rfl fun P hP => (hM P hP).1.normalize_eq_self
    _ = M := Multiset.map_id M

/-- Relabel each normalized irreducible factor and multiply with multiplicity. -/
def relabelPolynomial (σ : (ZMod g)[X] → (ZMod g)[X]) (f : (ZMod g)[X]) : (ZMod g)[X] :=
  ((normalizedFactors f).map σ).prod

theorem relabelPolynomial_id {f : (ZMod g)[X]} (hf : f.Monic) : relabelPolynomial id f = f := by
  rw [relabelPolynomial, Multiset.map_id, prod_normalizedFactors_of_monic hf]

variable {σ π : (ZMod g)[X] → (ZMod g)[X]}

private theorem relabel_factor_mem {f P : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0)
    (hσ : ∀ d Q, IsPrimeLab d Q → IsPrimeLab d (σ Q)) (hP : P ∈ (normalizedFactors f).map σ) :
    IsPrimeLab P.natDegree P := by
  obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hP
  have h := hσ _ Q (normalizedFactor_isPrimeLab h0 hQ)
  rw [h.2.2.2]
  exact h

/-- The factors of a relabelled polynomial are exactly the relabelled factors. -/
theorem normalizedFactors_relabel {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0)
    (hσ : ∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P)) :
    normalizedFactors (relabelPolynomial σ f) = (normalizedFactors f).map σ :=
  normalizedFactors_prod_prime _ (fun _ hP => relabel_factor_mem h0 hσ hP)

theorem relabelPolynomial_list_prod (M : List (ZMod g)[X])
    (hM : ∀ P ∈ M, IsPrimeLab P.natDegree P) :
    relabelPolynomial σ M.prod = (M.map σ).prod := by
  unfold relabelPolynomial
  rw [← Multiset.prod_coe, normalizedFactors_prod_prime (M : Multiset _) (fun P hP =>
    hM P (Multiset.mem_coe.mp hP)), Multiset.map_coe, Multiset.prod_coe]

/-- A degree-preserving relabelling leaves every product indexed by factor degrees unchanged. -/
theorem normalizedFactors_relabel_prod_degree {A : Type*} [CommMonoid A] (c : ℕ → A)
    {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0)
    (hσ : ∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P)) :
    ((normalizedFactors (relabelPolynomial σ f)).map (fun P => c P.natDegree)).prod =
      ((normalizedFactors f).map (fun P => c P.natDegree)).prod := by
  rw [normalizedFactors_relabel h0 hσ, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun P hP =>
    congrArg c (hσ _ P (normalizedFactor_isPrimeLab h0 hP)).2.2.2)

/-- An inverse on the prime labels gives an inverse on their monic products. -/
theorem relabelPolynomial_left_inv (hσ : ∀ d P, IsPrimeLab d P →
    IsPrimeLab d (σ P) ∧ π (σ P) = P) {f : (ZMod g)[X]} (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    relabelPolynomial π (relabelPolynomial σ f) = f := by
  change ((normalizedFactors (relabelPolynomial σ f)).map π).prod = f
  rw [normalizedFactors_relabel h0 (fun d P h => (hσ d P h).1), Multiset.map_map]
  have he : (normalizedFactors f).map (π ∘ σ) = normalizedFactors f := calc
    _ = (normalizedFactors f).map id := Multiset.map_congr rfl fun P hP =>
      (hσ _ P (normalizedFactor_isPrimeLab h0 hP)).2
    _ = _ := Multiset.map_id _
  rw [he]
  exact prod_normalizedFactors_of_monic hf

/-- Relabelling with a prime-label permutation preserves the rank and squarefreeness. -/
theorem relabelPolynomial_properties (hσ : ∀ d P, IsPrimeLab d P →
    IsPrimeLab d (σ P) ∧ π (σ P) = P) {f : (ZMod g)[X]} (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (relabelPolynomial σ f).Monic ∧ (relabelPolynomial σ f).natDegree = f.natDegree ∧
      (relabelPolynomial σ f).coeff 0 ≠ 0 ∧ (Squarefree f → Squarefree (relabelPolynomial σ f)) := by
  let T := (normalizedFactors f).map σ
  have hT (P : (ZMod g)[X]) (hP : P ∈ T) : IsPrimeLab P.natDegree P :=
    relabel_factor_mem h0 (fun d Q hQ => (hσ d Q hQ).1) hP
  have hm : (relabelPolynomial σ f).Monic := by
    change T.prod.Monic
    simpa only [Multiset.map_id] using
      monic_multiset_prod_of_monic T id (fun P hP => (hT P hP).1)
  refine ⟨hm, ?_, ?_, ?_⟩
  · change T.prod.natDegree = f.natDegree
    rw [natDegree_multiset_prod_of_monic T (fun P hP => (hT P hP).1)]
    conv_rhs => rw [← prod_normalizedFactors_of_monic hf,
      natDegree_multiset_prod_of_monic _ (fun P hP => (normalizedFactor_isPrimeLab h0 hP).1)]
    dsimp only [T]
    rw [Multiset.map_map]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun P hP =>
      (hσ _ P (normalizedFactor_isPrimeLab h0 hP)).1.2.2.2)
  · change T.prod.coeff 0 ≠ 0
    rw [coeff_zero_multiset_prod]
    apply Multiset.prod_ne_zero
    intro he
    obtain ⟨P, hP, hzero⟩ := Multiset.mem_map.mp he
    exact (hT P hP).2.2.1 hzero
  · intro hs
    rw [squarefree_iff_nodup_normalizedFactors hm.ne_zero,
      normalizedFactors_relabel h0 (fun d P hP => (hσ d P hP).1)]
    refine Multiset.Nodup.map_on (fun P hP Q hQ he => ?_)
      ((squarefree_iff_nodup_normalizedFactors hf.ne_zero).mp hs)
    rw [← (hσ _ P (normalizedFactor_isPrimeLab h0 hP)).2, he,
      (hσ _ Q (normalizedFactor_isPrimeLab h0 hQ)).2]

end GlobalTheory.GLq
