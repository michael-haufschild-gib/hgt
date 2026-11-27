import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCharacter

/-! A normalized character average on a finite multiplicatively closed
set of matrix units is idempotent in the group algebra. -/

noncomputable section
open scoped Classical
open WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- The idempotent law and identity coefficient for the average used in `eDat`. -/
theorem eDat_mul_self_coeff_one (P : Mt g n → Prop) (φ : Mt g n → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (h1 : P 1)
    (hmul : ∀ A B, P A → P B → P (A * B))
    (hφ : ∀ A B, P A → P B → φ (A * B) = φ A + φ B) :
    eDat g n P φ ψ * eDat g n P φ ψ = eDat g n P φ ψ ∧
      (eDat g n P φ ψ).coeff 1 =
        ((Finset.univ.filter fun u : Gn g n => P u.val).card : ℂ)⁻¹ := by
  classical
  let S := Finset.univ.filter fun u : Gn g n => P u.val
  let A (u : Gn g n) : MonoidAlgebra ℂ (Gn g n) := MonoidAlgebra.single u (ψ (φ u.val))⁻¹
  have he : eDat g n P φ ψ = (S.card : ℂ)⁻¹ • ∑ u ∈ S, A u := rfl
  have h1S : (1 : Gn g n) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  have hc : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, h1S⟩)
  have hP (u : Gn g n) (hu : u ∈ S) : P u.val := (Finset.mem_filter.mp hu).2
  have hm (u v : Gn g n) (hu : u ∈ S) (hv : v ∈ S) : u * v ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmul u.val v.val (hP u hu) (hP v hv)⟩
  have hA (u v : Gn g n) (hu : u ∈ S) (hv : v ∈ S) : A u * A v = A (u * v) := by
    dsimp only [A]
    rw [MonoidAlgebra.single_mul_single, Units.val_mul, hφ _ _ (hP u hu) (hP v hv),
      AddChar.map_add_eq_mul, mul_inv]
  have ht (u : Gn g n) (hu : u ∈ S) : (∑ v ∈ S, A (u * v)) = ∑ v ∈ S, A v := by
    have hinj : Function.Injective (fun v : Gn g n => u * v) := mul_right_injective u
    have hset : S.image (fun v => u * v) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        exact hm u w hu hw
      · rw [Finset.card_image_of_injective S hinj]
    exact (Finset.sum_image hinj.injOn).symm.trans (congrArg (fun T => ∑ v ∈ T, A v) hset)
  have hsq : (∑ u ∈ S, ∑ v ∈ S, A u * A v) = ∑ _u ∈ S, ∑ v ∈ S, A v := by
    refine Finset.sum_congr rfl fun u hu => ?_
    exact (Finset.sum_congr rfl fun v hv => hA u v hu hv).trans (ht u hu)
  have hz : φ 1 = 0 := by
    have h := hφ 1 1 h1 h1
    rw [mul_one] at h
    linear_combination -h
  constructor
  · rw [he, smul_mul_smul_comm, Finset.sum_mul_sum, hsq, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · rw [he]
    change ((S.card : ℂ)⁻¹ • ∑ u ∈ S, A u).coeff 1 = (S.card : ℂ)⁻¹
    simp only [A, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
      Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (1 : Gn g n)]
    · simp [hz]
    · intro u _ hu
      simp [hu]
    · exact fun h => (h h1S).elim

end GlobalTheory.GLq
