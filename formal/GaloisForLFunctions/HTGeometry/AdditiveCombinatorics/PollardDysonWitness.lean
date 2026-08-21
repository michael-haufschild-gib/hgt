import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardDeletion

/-!
# Choosing the Dyson witness

The Dyson transform of `(A, B)` at `x` is useful only when its small part
`dysonSmall A B x = (x • B) ∩ A` is a proper nonempty subset of `B`.  `exists_dyson_witness`
produces such an `x` whenever `#S(A) < #B`: otherwise every translate of `B` meeting `A` lies
inside `A`, which forces `b₀⁻¹ · B ⊆ S(A)` and hence `#B ≤ #S(A)`.

`exists_max_dyson_witness` then selects a witness with the largest possible small part, which is
what Grynkiewicz's STEP 3 and CASE 4 use.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **Existence of a proper Dyson witness.**  If the stabiliser of `A` is smaller than `B`, some
translate of `B` meets `A` without being contained in it. -/
theorem exists_dyson_witness {A B : Finset G} (hB : B.Nonempty)
    (hstab : (mulStab A).card < B.card) :
    ∃ x : G, ((x • B) ∩ A).Nonempty ∧ ((x • B) ∩ A).card < B.card := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨b₀, hb₀⟩ := hB
  -- every translate of `B` that meets `A` lies inside `A`
  have hall : ∀ x : G, ((x • B) ∩ A).Nonempty → x • B ⊆ A := by
    intro x hx
    have hle := hcon x hx
    have hcard : (x • B).card = B.card := Finset.card_smul_finset _ _
    have hsub : (x • B) ∩ A ⊆ x • B := Finset.inter_subset_left
    have heq : (x • B) ∩ A = x • B := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← heq]
    exact Finset.inter_subset_right
  -- hence every `b₀⁻¹ b'` stabilises `A`
  have hmem : ∀ b' ∈ B, b₀⁻¹ * b' ∈ mulStab A := by
    intro b' hb'
    rw [mem_mulStab]
    have hsub : (b₀⁻¹ * b') • A ⊆ A := by
      intro z hz
      rw [Finset.mem_smul_finset] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      have hne : (((a * b₀⁻¹) • B) ∩ A).Nonempty := by
        refine ⟨a, Finset.mem_inter.2 ⟨?_, ha⟩⟩
        rw [Finset.mem_smul_finset]
        exact ⟨b₀, hb₀, by simp [smul_eq_mul, inv_mul_cancel_right]⟩
      have := hall (a * b₀⁻¹) hne
      have hmm : (a * b₀⁻¹) • b' ∈ (a * b₀⁻¹) • B := Finset.smul_mem_smul_finset hb'
      have hres := this hmm
      simp only [smul_eq_mul] at hres ⊢
      have hcomm : b₀⁻¹ * b' * a = a * b₀⁻¹ * b' := by
        rw [mul_comm (b₀⁻¹ * b') a, ← mul_assoc]
      rw [hcomm]
      exact hres
    have hcard : ((b₀⁻¹ * b') • A).card = A.card := Finset.card_smul_finset _ _
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have hinj : Function.Injective (fun b' : G => b₀⁻¹ * b') := by
    intro u v huv
    simpa using huv
  have hcardle : B.card ≤ (mulStab A).card := by
    have himg : B.image (fun b' => b₀⁻¹ * b') ⊆ mulStab A := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨b', hb', rfl⟩ := hz
      exact hmem b' hb'
    calc B.card = (B.image (fun b' => b₀⁻¹ * b')).card :=
          (Finset.card_image_of_injective B hinj).symm
      _ ≤ (mulStab A).card := Finset.card_le_card himg
  omega


/-- A Dyson witness of maximal small part. -/
theorem exists_max_dyson_witness {A B : Finset G} (hB : B.Nonempty)
    (hstab : (mulStab A).card < B.card) :
    ∃ x : G, (dysonSmall A B x).Nonempty ∧ (dysonSmall A B x).card < B.card
      ∧ ∀ y : G, (dysonSmall A B y).Nonempty → (dysonSmall A B y).card < B.card →
          (dysonSmall A B y).card ≤ (dysonSmall A B x).card := by
  classical
  obtain ⟨x₀, hx₀ne, hx₀lt⟩ := exists_dyson_witness hB hstab
  set W : Finset G := Finset.univ.filter
    (fun x => (dysonSmall A B x).Nonempty ∧ (dysonSmall A B x).card < B.card) with hWdef
  have hWne : W.Nonempty := ⟨x₀, by
    rw [hWdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₀ne, hx₀lt⟩⟩
  obtain ⟨x, hxW, hxmax⟩ :=
    Finset.exists_max_image W (fun x => (dysonSmall A B x).card) hWne
  rw [hWdef, Finset.mem_filter] at hxW
  refine ⟨x, hxW.2.1, hxW.2.2, fun y hy1 hy2 => ?_⟩
  exact hxmax y (by rw [hWdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy1, hy2⟩)

end GaloisForLFunctions.HTGeometry.AddComb
