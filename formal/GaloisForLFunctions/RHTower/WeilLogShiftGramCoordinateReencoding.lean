import GaloisForLFunctions.RHTower.WeilLogShiftGramAntipodal

/-! Transfer an entire canonical coordinate system through replacements of its tests
that preserve their actual Gram forms. No injectivity premise is needed. -/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace RHTower
namespace FiniteWeilGramCoordinates

variable {s : Finset ℕ} (D : FiniteWeilGramCoordinates s)

theorem atom_form_injective :
    Function.Injective (fun w : D.tests => finiteWeilGramForm s w.1) := by
  intro v w he
  by_contra hne
  have h := congrArg (fun L : (s → ℝ) →ₗ[ℝ] ℝ => D.weights L v) he
  simp [D.weights_atom, hne] at h

/-- Form-preserving replacements transport the certificate, minimal cardinality,
positive balance, canonical weights, support bound, and entire representation ray. -/
theorem exists_form_preserving_reencoding (f : D.tests → FiniteWeilGramTest)
    (hf : ∀ w, finiteWeilGramForm s (f w) = finiteWeilGramForm s w.1) :
    ∃ E : FiniteWeilGramCoordinates s, ∃ e : D.tests ≃ E.tests,
      (∀ w, (e w).1 = f w) ∧
      (∀ w, E.balance (e w) = D.balance w) ∧
      ∀ L w, E.weights L (e w) = D.weights L w := by
  have hfi : Function.Injective f := by
    intro v w he
    apply D.atom_form_injective
    change finiteWeilGramForm s v.1 = finiteWeilGramForm s w.1
    rw [← hf v, ← hf w, he]
  let tests : Finset FiniteWeilGramTest := Finset.univ.image f
  let g : D.tests → tests := fun w => ⟨f w, Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩⟩
  have hgi : Function.Injective g := by
    intro v w he
    exact hfi (congrArg Subtype.val he)
  have hgs : Function.Surjective g := by
    intro v
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp v.2
    exact ⟨w, Subtype.ext hw⟩
  let e : D.tests ≃ tests := Equiv.ofBijective g ⟨hgi, hgs⟩
  have heval (w : D.tests) : (e w).1 = f w := rfl
  have hcard : tests.card = (if s = ∅ then 0 else s.card + 1) := by
    have hc : tests.card = D.tests.card := by
      simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm
    exact hc.trans D.cardinality
  have hcert : FiniteWeilGramNormCertificate s tests := by
    intro c hc
    obtain ⟨w, hw, hneg⟩ := D.certificate c hc
    refine ⟨f ⟨w, hw⟩, Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hf ⟨w, hw⟩]
    exact hneg
  have hsum (b : tests → ℝ) (c : s → ℝ) :
      (∑ v, b v * finiteWeilGramForm s v.1 c) =
        ∑ w, b (e w) * finiteWeilGramForm s w.1 c := by
    calc
      (∑ v, b v * finiteWeilGramForm s v.1 c) =
          ∑ w, b (e w) * finiteWeilGramForm s (e w).1 c :=
        (e.sum_comp (fun v => b v * finiteWeilGramForm s v.1 c)).symm
      _ = ∑ w, b (e w) * finiteWeilGramForm s w.1 c := by
        apply Finset.sum_congr rfl
        intro w _
        rw [heval w, hf w]
  have hbal (c : s → ℝ) :
      (∑ v, D.balance (e.symm v) * finiteWeilGramForm s v.1 c) = 0 := by
    rw [hsum]
    simpa only [e.symm_apply_apply] using D.balance_zero c
  have hrep (L : (s → ℝ) →ₗ[ℝ] ℝ) (c : s → ℝ) :
      L c = ∑ v, D.weights L (e.symm v) * finiteWeilGramForm s v.1 c := by
    rw [hsum]
    simpa only [e.symm_apply_apply] using D.represents L c
  have hsupport (L : (s → ℝ) →ₗ[ℝ] ℝ) :
      (Finset.univ.filter fun v => D.weights L (e.symm v) ≠ 0).card ≤ s.card := by
    have hcount := e.symm.sum_comp (fun w => if D.weights L w ≠ 0 then (1 : ℕ) else 0)
    have heq : (Finset.univ.filter fun v => D.weights L (e.symm v) ≠ 0).card =
        (Finset.univ.filter fun w => D.weights L w ≠ 0).card := by
      simpa only [Finset.sum_boole, Nat.cast_id] using hcount
    rw [heq]
    exact D.weights_support_card L
  have hray (L : (s → ℝ) →ₗ[ℝ] ℝ) (b : tests → ℝ) :
      ((∀ v, 0 ≤ b v) ∧ ∀ c, L c = ∑ v, b v * finiteWeilGramForm s v.1 c) ↔
        ∃ t : ℝ, 0 ≤ t ∧ ∀ v, b v = D.weights L (e.symm v) + t * D.balance (e.symm v) := by
    constructor
    · rintro ⟨hb, hbr⟩
      have ho : (∀ w, 0 ≤ b (e w)) ∧
          ∀ c, L c = ∑ w, b (e w) * finiteWeilGramForm s w.1 c :=
        ⟨fun w => hb (e w), fun c => (hbr c).trans (hsum b c)⟩
      obtain ⟨t, ht, hw⟩ := (D.ray L (fun w => b (e w))).mp ho
      refine ⟨t, ht, fun v => ?_⟩
      simpa only [e.apply_symm_apply] using hw (e.symm v)
    · rintro ⟨t, ht, hv⟩
      have ho := (D.ray L (fun w => b (e w))).mpr
        ⟨t, ht, fun w => by simpa only [e.symm_apply_apply] using hv (e w)⟩
      refine ⟨fun v => ?_, fun c => (ho.2 c).trans (hsum b c).symm⟩
      simpa only [e.apply_symm_apply] using ho.1 (e.symm v)
  let E : FiniteWeilGramCoordinates s :=
    { tests := tests
      certificate := hcert
      cardinality := hcard
      balance := fun v => D.balance (e.symm v)
      balance_pos := fun v => D.balance_pos (e.symm v)
      balance_zero := hbal
      weights := fun L v => D.weights L (e.symm v)
      weights_nonneg := fun L v => D.weights_nonneg L (e.symm v)
      weights_support_card := hsupport
      represents := hrep
      ray := hray }
  refine ⟨E, e, heval, ?_, ?_⟩
  · intro w
    change D.balance (e.symm (e w)) = D.balance w
    rw [e.symm_apply_apply]
  · intro L w
    change D.weights L (e.symm (e w)) = D.weights L w
    rw [e.symm_apply_apply]

end FiniteWeilGramCoordinates
end RHTower
