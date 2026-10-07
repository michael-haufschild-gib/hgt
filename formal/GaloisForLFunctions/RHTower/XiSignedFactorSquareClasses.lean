import GaloisForLFunctions.RHTower.XiSignedFactorZeroSeparation
import GaloisForLFunctions.HTGeometry.EntireOddDivisorSquareClass

/-!
# Exact independence of the signed global Xi square classes

Xi and every factor `1 ± n^(-s)*xi`, for integer labels at least two, are
independent modulo global meromorphic squares. Positive companions have
odd-order zeros separated from Xi and every other signed factor. After all
marked roots are adjoined, Xi and every positive companion remain independent;
the theorem states an exact square criterion in the actual infinite marked field.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.XiGlobalKummer
open GaloisForLFunctions.HTGeometry

/-- Each positive source companion has an odd-order zero. -/
theorem exists_odd_zero_augmentationFactor {n : ℕ} (hn : 2 ≤ n) :
    ∃ z : ℂ, augmentationFactor n z = 0 ∧
      Odd (analyticOrderAt (augmentationFactor n) z).toNat := by
  exact exists_odd_zero_of_not_isSquare_plane (augmentationFactor_differentiable n)
    (by norm_num [augmentationFactor, deletionFactor, xi_zero])
    (augmentationElement_not_isSquare hn)

private def planeGermHom : K →+* Germ planeCodiscrete ℂ where
  toFun := MeromorphicPlane.germ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private theorem signedPacket_differentiable (S T : Finset ℕ) (e : ℕ) :
    Differentiable ℂ (fun z => packet S e z * ∏ n ∈ T, augmentationFactor n z) := by
  apply (packet_differentiable S e).mul
  induction T using Finset.induction_on with
  | empty => simp
  | @insert n T hn ih =>
    simp_rw [Finset.prod_insert hn]
    exact (augmentationFactor_differentiable n).mul ih

private theorem signedPacket_element_eq (S T : Finset ℕ) (e : ℕ) :
    ofMeromorphic (fun z => packet S e z * ∏ n ∈ T, augmentationFactor n z)
      (fun z => ((signedPacket_differentiable S T e).analyticAt z).meromorphicAt) =
      xiElement ^ e * (∏ n ∈ S, factorElement n) * ∏ n ∈ T, augmentationElement n := by
  rw [← packetElement_eq]
  apply MeromorphicPlane.germ_injective
  change Germ.coeRingHom planeCodiscrete
    (fun z => packet S e z * ∏ n ∈ T, augmentationFactor n z) =
    planeGermHom (packetElement S e * ∏ n ∈ T, augmentationElement n)
  have hp : (fun z => packet S e z * ∏ n ∈ T, augmentationFactor n z) =
      packet S e * ∏ n ∈ T, augmentationFactor n := by
    ext z
    simp
  rw [hp, map_mul, map_prod, map_mul, map_prod]
  rfl

/-- Any nonempty positive-label packet remains nonsquare after arbitrary Xi and negative-label twists. -/
theorem signed_factor_packet_not_isSquare (S T : Finset ℕ) (e : ℕ)
    (hne : T.Nonempty) (hT : ∀ n ∈ T, 2 ≤ n) :
    ¬ IsSquare (xiElement ^ e * (∏ n ∈ S, factorElement n) *
      ∏ n ∈ T, augmentationElement n) := by
  classical
  obtain ⟨n, hn⟩ := hne
  obtain ⟨z, hz, hodd⟩ := exists_odd_zero_augmentationFactor (hT n hn)
  have hunit : packet S e z * (∏ m ∈ T.erase n, augmentationFactor m z) ≠ 0 := by
    apply mul_ne_zero
    · dsimp [packet]
      apply mul_ne_zero (pow_ne_zero _ (xi_ne_zero_of_augmentationFactor_zero hz))
      exact Finset.prod_ne_zero_iff.mpr
        (fun m _ => deletionFactor_ne_zero_of_augmentationFactor_zero hz)
    · apply Finset.prod_ne_zero_iff.mpr
      intro m hm hw
      have hmn := augmentationFactor_label_injective_at_zero
        (by have := hT m (Finset.mem_of_mem_erase hm); omega)
        (by have := hT n hn; omega) hw hz
      exact (Finset.mem_erase.mp hm).1 hmn
  have hns := not_isSquare_plane_mul_of_odd_order (augmentationFactor_differentiable n)
    (signedPacket_differentiable S (T.erase n) e) hodd hunit
  rw [signedPacket_element_eq] at hns
  have he : xiElement ^ e * (∏ m ∈ S, factorElement m) * (∏ m ∈ T, augmentationElement m) =
      augmentationElement n *
        (xiElement ^ e * (∏ m ∈ S, factorElement m) * ∏ m ∈ T.erase n, augmentationElement m) := by
    rw [← Finset.mul_prod_erase T augmentationElement hn]
    ring
  rw [he]
  exact hns

private theorem isSquare_pow_iff_even_of_not_isSquare {F : Type*} [Field F]
    {a : F} (ha : ¬ IsSquare a) (e : ℕ) : IsSquare (a ^ e) ↔ Even e := by
  have ha0 : a ≠ 0 := fun hz => ha (hz ▸ IsSquare.zero)
  constructor
  · intro hs
    by_contra he
    obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp he
    have h := hs.div (IsSquare.sq (a ^ k))
    have heq : a ^ (2 * k + 1) / (a ^ k) ^ 2 = a := by
      rw [pow_add, pow_one, show 2 * k = k * 2 by omega, pow_mul]
      field_simp
    rw [heq] at h
    exact ha h
  · exact fun he => he.isSquare_pow a

/-- Exact square criterion: Xi and every signed integer factor form a free square-class family. -/
theorem signed_factor_packet_isSquare_iff (S T : Finset ℕ) (e : ℕ)
    (hS : ∀ n ∈ S, 2 ≤ n) (hT : ∀ n ∈ T, 2 ≤ n) :
    IsSquare (xiElement ^ e * (∏ n ∈ S, factorElement n) *
      ∏ n ∈ T, augmentationElement n) ↔ Even e ∧ S = ∅ ∧ T = ∅ := by
  constructor
  · intro hs
    have ht : T = ∅ := by
      by_contra hne
      exact signed_factor_packet_not_isSquare S T e (Finset.nonempty_iff_ne_empty.mpr hne) hT hs
    subst T
    simp only [Finset.prod_empty, mul_one] at hs
    have hs0 : S = ∅ := by
      by_contra hne
      exact xi_pow_mul_prod_factors_not_isSquare S e (Finset.nonempty_iff_ne_empty.mpr hne) hS hs
    subst S
    simp only [Finset.prod_empty, mul_one] at hs
    exact ⟨(isSquare_pow_iff_even_of_not_isSquare xiElement_not_isSquare e).mp hs, rfl, rfl⟩
  · rintro ⟨he, rfl, rfl⟩
    simpa using he.isSquare_pow xiElement

/-- Every finite nonempty packet of positive labels survives all marked radical adjunctions. -/
theorem augmentation_packet_not_isSquare_markedExtension (T : Finset ℕ) (e : ℕ)
    (hne : T.Nonempty) (hT : ∀ n ∈ T, 2 ≤ n) :
    ¬ IsSquare (algebraMap K markedExtension (xiElement ^ e *
      ∏ n ∈ T, augmentationElement n)) := by
  apply not_isSquare_markedExtension_of_twists
  intro U
  have h := signed_factor_packet_not_isSquare (U.image (fun n => n + 2)) T
    (e + U.card) hne hT
  rw [Finset.prod_image] at h
  · rw [prod_radicand]
    have he : (xiElement ^ e * ∏ n ∈ T, augmentationElement n) *
        (xiElement ^ U.card * ∏ n ∈ U, factorElement (n + 2)) =
        xiElement ^ (e + U.card) * (∏ n ∈ U, factorElement (n + 2)) *
          ∏ n ∈ T, augmentationElement n := by
      rw [pow_add]
      ring
    rw [he]
    exact h
  · intro a _ b _ hab
    dsimp at hab
    omega

/-- The surviving source classes retain every label in the actual infinite marked field. -/
theorem sourceLambda_packet_isSquare_iff (T : Finset ℕ) (e : ℕ) :
    IsSquare (xiMarked ^ e * ∏ n ∈ T, (1 + sourceParameter n)) ↔ Even e ∧ T = ∅ := by
  have hxi : ¬ IsSquare xiMarked := xi_not_isSquare_markedExtension
  constructor
  · intro hs
    have ht : T = ∅ := by
      by_contra hne
      have h := augmentation_packet_not_isSquare_markedExtension (T.image (fun n => n + 2)) e
        ((Finset.nonempty_iff_ne_empty.mpr hne).image _)
        (by intro n hn; obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hn; omega)
      rw [Finset.prod_image] at h
      · rw [map_mul, map_pow, map_prod] at h
        simp_rw [augmentationElement_map_eq_sourceLambda] at h
        exact h hs
      · intro a _ b _ hab
        dsimp at hab
        omega
    subst T
    simp only [Finset.prod_empty, mul_one] at hs
    exact ⟨(isSquare_pow_iff_even_of_not_isSquare hxi e).mp hs, rfl⟩
  · rintro ⟨he, rfl⟩
    simpa using he.isSquare_pow xiMarked

end RHTower.XiGlobalKummer
