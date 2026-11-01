import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupPositivePart
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialCorrection

/-!
# Canonical relative split for every nonzero proper subgroup successor

Let `H` be a nonzero proper additive subgroup of `ℚ` and `k` a Hermitian kernel on `Aff(ℚ)` of
finite negative index with translation reading `1_H`. Then `k` splits uniquely as

`k = p + ψ ∘ slope + q`,

with `p` positive definite of successor `1_H`, `ψ` Hermitian on `ℚˣ`, and `q` a finite-rank
Hermitian kernel with polynomial translation fibres vanishing on all translations and dilations.
Moreover `κ(k) = κ(ψ ∘ slope + q) ≥ κ(ψ)`.

Mechanism. Conjugating by a dilation by a nonzero `a ∈ H` moves `H` to a subgroup containing `1`.
The zero-axis polynomial correction removes the integer period defect, and the factorial moving
limit (`SubgroupPositivePart`) splits the integer-invariant remainder into its positive part and a
slope kernel. Uniqueness and the index law come from rigidity and index preservation of positive
proper-subgroup carriers under polynomial-fibre perturbations.
-/

open Complex Module Polynomial
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Elementary transport facts -/

/-- A sum of polynomial-fibre kernels has polynomial fibres. -/
theorem HasPolynomialTranslationFibres.add' {k l : AffineGroupQ → ℂ}
    (hk : HasPolynomialTranslationFibres k) (hl : HasPolynomialTranslationFibres l) :
    HasPolynomialTranslationFibres (fun g => k g + l g) := by
  intro u
  obtain ⟨P, hP⟩ := hk u
  obtain ⟨Q, hQ⟩ := hl u
  refine ⟨P + Q, fun b => ?_⟩
  change k (translation b * dilation u) + l (translation b * dilation u) = _
  rw [hP, hQ, eval_add]

/-- Pulling a kernel back along a group homomorphism keeps finite column rank. -/
theorem finite_kernelColumnSpan_comp {G G' : Type*} [Group G] [Group G'] (k : G → ℂ)
    (F : G' →* G) [Module.Finite ℂ (kernelColumnSpan k)] :
    Module.Finite ℂ (kernelColumnSpan (k ∘ F)) := by
  have hle : kernelColumnSpan (k ∘ F) ≤ (kernelColumnSpan k).map (LinearMap.funLeft ℂ ℂ F) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    refine ⟨kernelColumn k (F g), Submodule.subset_span ⟨F g, rfl⟩, ?_⟩
    funext y
    simp only [kernelColumn, LinearMap.funLeft_apply, Function.comp_apply, map_mul, map_inv]
  exact Submodule.finiteDimensional_of_le hle

/-- A subgroup containing `1` has integer-periodic indicator readings. -/
theorem hasSubgroupSuccessor_translation_periodic' {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {k : AffineGroupQ → ℂ} (hs : HasSubgroupSuccessor H k) (b : ℚ) :
    k (translation (b + 1)) = k (translation b) := by
  classical
  have hmem : b + 1 ∈ H ↔ b ∈ H :=
    ⟨fun hb => by simpa only [add_sub_cancel_right] using H.sub_mem hb h1,
      fun hb => H.add_mem hb h1⟩
  rw [hs (b + 1), hs b]
  by_cases hb : b ∈ H
  · rw [if_pos (hmem.mpr hb), if_pos hb]
  · rw [if_neg (fun h => hb (hmem.mp h)), if_neg hb]

/-- Conjugation by a dilation, `g ↦ d_u g d_u⁻¹`. -/
def dilationConjugation (u : ℚˣ) : AffineGroupQ →* AffineGroupQ where
  toFun g := dilation u * g * (dilation u)⁻¹
  map_one' := by rw [mul_one, mul_inv_cancel]
  map_mul' g h := by simp only [mul_assoc, inv_mul_cancel_left]

theorem dilationConjugation_translation (u : ℚˣ) (b : ℚ) :
    dilationConjugation u (translation b) = translation ((u : ℚ) * b) := by
  have harith : (u : ℚ) * b / (u : ℚ) = b := by field_simp [u.ne_zero]
  have he : translation ((u : ℚ) * b) * dilation u = dilation u * translation b := by
    rw [translation_mul_affine_eq, affSlope_dilation, harith]
  change (dilation u * translation b) * (dilation u)⁻¹ = _
  rw [← he, mul_assoc, mul_inv_cancel, mul_one]

theorem dilationConjugation_dilation (u a : ℚˣ) :
    dilationConjugation u (dilation a) = dilation a := by
  change (dilation u * dilation a) * (dilation u)⁻¹ = dilation a
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_comm u a, mul_assoc, mul_inv_cancel, mul_one]

/-- Conjugation by `u⁻¹` undoes conjugation by `u`. -/
theorem dilationConjugation_inv_apply (u : ℚˣ) (g : AffineGroupQ) :
    dilationConjugation u (dilationConjugation u⁻¹ g) = g := by
  change dilation u * (dilation u⁻¹ * g * (dilation u⁻¹)⁻¹) * (dilation u)⁻¹ = g
  rw [map_inv, inv_inv]
  group

/-- Conjugation by a dilation preserves the slope. -/
theorem slopeUnit_dilationConjugation (u : ℚˣ) (g : AffineGroupQ) :
    slopeUnit (dilationConjugation u g) = slopeUnit g := by
  change slopeUnit (dilation u * g * (dilation u)⁻¹) = slopeUnit g
  rw [map_mul, map_mul, map_inv, slopeUnit_dilation', mul_comm u, mul_assoc, mul_inv_cancel,
    mul_one]

/-! ### Uniqueness and the index law -/

/-- **Uniqueness.** Two splits of the same kernel with positive `1_H` parts and polynomial-fibre
corrections vanishing on dilations coincide. -/
theorem subgroup_relative_split_unique {H : AddSubgroup ℚ} (hH : H ≠ ⊤)
    {k p p' q q' : AffineGroupQ → ℂ} {ψ ψ' : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hp' : IsPosDefKernel p')
    (hs : HasSubgroupSuccessor H p) (hs' : HasSubgroupSuccessor H p')
    (hq : HasPolynomialTranslationFibres q) (hq' : HasPolynomialTranslationFibres q')
    (hqd : ∀ u : ℚˣ, q (dilation u) = 0) (hqd' : ∀ u : ℚˣ, q' (dilation u) = 0)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g)
    (he' : ∀ g, k g = p' g + ψ' (slopeUnit g) + q' g) :
    p' = p ∧ ψ' = ψ ∧ q' = q := by
  have hpoly : HasPolynomialTranslationFibres (fun g => p' g - p g) := by
    have h := (HasPolynomialTranslationFibres.add' (hasPolynomialTranslationFibres_slope ψ) hq).sub
      (HasPolynomialTranslationFibres.add' (hasPolynomialTranslationFibres_slope ψ') hq')
    refine fun u => ?_
    obtain ⟨P, hP⟩ := h u
    refine ⟨P, fun b => ?_⟩
    rw [← hP b]
    have h1 := he (translation b * dilation u)
    have h2 := he' (translation b * dilation u)
    change p' _ - p _ = (ψ _ + q _) - (ψ' _ + q' _)
    linear_combination h1 - h2
  have hpp : p' = p := positive_subgroup_carriers_polynomial_rigid H hH hp' hp hs' hs hpoly
  have hψ : ψ' = ψ := by
    funext u
    have h1 := he (dilation u)
    have h2 := he' (dilation u)
    rw [slopeUnit_dilation', hqd] at h1
    rw [slopeUnit_dilation', hqd', hpp] at h2
    linear_combination h1 - h2
  refine ⟨hpp, hψ, ?_⟩
  funext g
  have h1 := he g
  have h2 := he' g
  rw [hpp, hψ] at h2
  linear_combination h1 - h2

/-- **Index law.** A split carries the whole index in `ψ ∘ slope + q`, which dominates `ψ`. -/
theorem negIndex_subgroup_relative_split {H : AddSubgroup ℚ} (hH : H ≠ ⊤)
    {k p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasSubgroupSuccessor H p) (hψ : IsHermKernel ψ)
    (hqH : IsHermKernel q) (hq : HasPolynomialTranslationFibres q)
    (hqd : ∀ u : ℚˣ, q (dilation u) = 0) (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g) :
    negIndex k = negIndex (fun g => ψ (slopeUnit g) + q g) ∧
      negIndex ψ ≤ negIndex k := by
  let h : AffineGroupQ → ℂ := fun g => ψ (slopeUnit g) + q g
  have hh : IsHermKernel h := by
    intro g
    change ψ (slopeUnit g⁻¹) + q g⁻¹ = starRingEnd ℂ (ψ (slopeUnit g) + q g)
    rw [map_inv, hψ, hqH, map_add]
  have hk : k = fun g => p g + h g := funext fun g => by
    rw [he g]
    ring
  have hidx := negIndex_add_positive_subgroup_polynomial H hH hp hs hh
    (HasPolynomialTranslationFibres.add' (hasPolynomialTranslationFibres_slope ψ) hq)
  rw [← hk] at hidx
  refine ⟨hidx, ?_⟩
  have hres : h ∘ dilation = ψ := by
    funext u
    change ψ (slopeUnit (dilation u)) + q (dilation u) = ψ u
    rw [slopeUnit_dilation', hqd, add_zero]
  calc negIndex ψ = negIndex (h ∘ dilation) := by rw [hres]
    _ ≤ negIndex h := negIndex_comp_le h dilation
    _ = negIndex k := hidx.symm

/-! ### Existence -/

/-- **Existence when `1 ∈ H`.** -/
theorem exists_subgroup_relative_split_of_one_mem {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) (hH : H ≠ ⊤) {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k) :
    ∃ p : AffineGroupQ → ℂ, ∃ ψ : ℚˣ → ℂ, ∃ q : AffineGroupQ → ℂ,
      IsPosDefKernel p ∧ HasSubgroupSuccessor H p ∧ IsHermKernel ψ ∧
      Module.Finite ℂ (kernelColumnSpan q) ∧ HasPolynomialTranslationFibres q ∧
      IsHermKernel q ∧ (∀ b : ℚ, q (translation b) = 0) ∧ (∀ u : ℚˣ, q (dilation u) = 0) ∧
      ∀ g, k g = p g + ψ (slopeUnit g) + q g := by
  obtain ⟨q, hfinite, hqpoly, hqHerm, hqt, hqd, hrem, hindex, hperiod, _⟩ :=
    exists_zero_axis_polynomial_correction hk hi (hasSubgroupSuccessor_translation_periodic' h1 hs)
  have hsrem : HasSubgroupSuccessor H (fun g => k g - q g) := by
    intro b
    change k (translation b) - q (translation b) = _
    rw [hqt, sub_zero]
    exact hs b
  have hib : negIndex (fun g => k g - q g) ≤
      ((r + finrank ℂ (kernelColumnSpan q) : ℕ) : ℕ∞) := by
    simpa only [Nat.cast_add] using hindex
  refine ⟨haarPositivePart (fun g => k g - q g) hperiod,
    haarSlopePart (fun g => k g - q g) hperiod, q,
    subgroup_haarPositivePart_posDef h1 hrem hib hsrem hperiod,
    subgroup_haarPositivePart_hasSubgroupSuccessor h1 hH hrem hib hsrem hperiod,
    subgroup_haarSlopePart_hermitian h1 hrem hib hsrem hperiod,
    hfinite, hqpoly, hqHerm, hqt, hqd, fun g => ?_⟩
  have h := subgroup_haarPositivePart_add_slope h1 hrem hib hsrem hperiod g
  change k g - q g = _ at h
  linear_combination h

/-- **The canonical relative split for every nonzero proper subgroup successor.** -/
theorem exists_unique_subgroup_relative_split {H : AddSubgroup ℚ}
    (hnz : H ≠ ⊥) (hH : H ≠ ⊤) {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) (hs : HasSubgroupSuccessor H k) :
    ∃ p : AffineGroupQ → ℂ, ∃ ψ : ℚˣ → ℂ, ∃ q : AffineGroupQ → ℂ,
      IsPosDefKernel p ∧ HasSubgroupSuccessor H p ∧ IsHermKernel ψ ∧
      Module.Finite ℂ (kernelColumnSpan q) ∧ HasPolynomialTranslationFibres q ∧
      IsHermKernel q ∧ (∀ b : ℚ, q (translation b) = 0) ∧ (∀ u : ℚˣ, q (dilation u) = 0) ∧
      (∀ g, k g = p g + ψ (slopeUnit g) + q g) ∧
      negIndex k = negIndex (fun g => ψ (slopeUnit g) + q g) ∧ negIndex ψ ≤ negIndex k ∧
      ∀ (p' : AffineGroupQ → ℂ) (ψ' : ℚˣ → ℂ) (q' : AffineGroupQ → ℂ),
        IsPosDefKernel p' → HasSubgroupSuccessor H p' → HasPolynomialTranslationFibres q' →
        (∀ u : ℚˣ, q' (dilation u) = 0) → (∀ g, k g = p' g + ψ' (slopeUnit g) + q' g) →
        p' = p ∧ ψ' = ψ ∧ q' = q := by
  classical
  -- choose a nonzero `a ∈ H` and rescale `H` to `H' = a⁻¹H ∋ 1`
  have hex : ∃ a : ℚ, a ∈ H ∧ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (le_antisymm (fun x hx => AddSubgroup.mem_bot.mpr (h x hx)) bot_le)
  obtain ⟨a, haH, ha⟩ := hex
  let u := Units.mk0 a ha
  let S : ℚ →+ ℚ :=
    { toFun := fun b => a * b
      map_zero' := mul_zero a
      map_add' := mul_add a }
  let H' := H.comap S
  have hmem (b : ℚ) : b ∈ H' ↔ a * b ∈ H := Iff.rfl
  have h1 : (1 : ℚ) ∈ H' := by rw [hmem, mul_one]; exact haH
  have hH' : H' ≠ ⊤ := by
    intro he
    apply hH
    apply top_unique
    intro x _
    have hx : x / a ∈ H' := by rw [he]; exact AddSubgroup.mem_top _
    rw [hmem, mul_div_cancel₀ x ha] at hx
    exact hx
  let F := dilationConjugation u
  let G := dilationConjugation u⁻¹
  have hs' : HasSubgroupSuccessor H' (k ∘ F) := by
    intro b
    change k (dilationConjugation u (translation b)) = _
    rw [dilationConjugation_translation]
    simpa only [u, Units.val_mk0, hmem] using hs (a * b)
  have hi' : negIndex (k ∘ F) ≤ r := (negIndex_comp_le k F).trans hi
  obtain ⟨p₀, ψ, q₀, hp₀, hps₀, hψ, hfin₀, hpoly₀, hqH₀, hqt₀, hqd₀, he₀⟩ :=
    exists_subgroup_relative_split_of_one_mem h1 hH' (hk.comp F) hi' hs'
  -- transport back along the inverse conjugation
  have hGtr (b : ℚ) : G (translation b) = translation (b / a) := by
    change dilationConjugation u⁻¹ (translation b) = _
    rw [dilationConjugation_translation, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_eq_div]
  have hGdil (v : ℚˣ) : G (dilation v) = dilation v := dilationConjugation_dilation u⁻¹ v
  let p := p₀ ∘ G
  let q := q₀ ∘ G
  have hp : IsPosDefKernel p := hp₀.comp G
  have hps : HasSubgroupSuccessor H p := by
    intro b
    change p₀ (G (translation b)) = _
    rw [hGtr, hps₀, hmem, mul_div_cancel₀ b ha]
  have hqH : IsHermKernel q := hqH₀.comp G
  have hqt (b : ℚ) : q (translation b) = 0 := by
    change q₀ (G (translation b)) = 0
    rw [hGtr, hqt₀]
  have hqd (v : ℚˣ) : q (dilation v) = 0 := by
    change q₀ (G (dilation v)) = 0
    rw [hGdil, hqd₀]
  have hpoly : HasPolynomialTranslationFibres q := by
    intro v
    obtain ⟨P, hP⟩ := hpoly₀ v
    refine ⟨P.comp (C ((a : ℂ)⁻¹) * X), fun b => ?_⟩
    change q₀ (G (translation b * dilation v)) = _
    rw [map_mul, hGtr, hGdil, hP (b / a), eval_comp, eval_mul, eval_C, eval_X]
    congr 1
    push_cast
    ring
  have hfin : Module.Finite ℂ (kernelColumnSpan q) := by
    letI := hfin₀
    exact finite_kernelColumnSpan_comp q₀ G
  have he (g : AffineGroupQ) : k g = p g + ψ (slopeUnit g) + q g := by
    have h := he₀ (G g)
    change k (dilationConjugation u (dilationConjugation u⁻¹ g)) = _ at h
    rw [dilationConjugation_inv_apply, slopeUnit_dilationConjugation] at h
    exact h
  obtain ⟨hidx, hψk⟩ := negIndex_subgroup_relative_split hH hp hps hψ hqH hpoly hqd he
  refine ⟨p, ψ, q, hp, hps, hψ, hfin, hpoly, hqH, hqt, hqd, he, hidx, hψk, ?_⟩
  intro p' ψ' q' hp' hs'' hq' hqd' he'
  exact subgroup_relative_split_unique hH hp hp' hps hs'' hpoly hq' hqd hqd' he he'

#print axioms exists_unique_subgroup_relative_split
#print axioms subgroup_relative_split_unique
#print axioms negIndex_subgroup_relative_split
end GaloisForLFunctions.AdelicKreinGeometry
