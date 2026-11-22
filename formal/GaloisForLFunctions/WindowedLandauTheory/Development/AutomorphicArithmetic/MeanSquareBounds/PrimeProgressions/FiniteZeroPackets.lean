import Mathlib

/-! Group a finite set of zero copies by its points without losing multiplicities. -/

open Finset

noncomputable section

namespace QH.PrimeProgressions

private theorem sum_eq_packet {ι α : Type*} [AddCommMonoid α] (F : Finset ι) (point : ι → ℂ)
    (m : ℂ → ℕ) (hm : ∀ ρ ∈ F.image point, (F.filter (fun q => point q = ρ)).card = m ρ)
    (f : ℂ → α) : (∑ q ∈ F, f (point q)) = ∑ ρ ∈ F.image point, m ρ • f ρ := by
  classical
  rw [← sum_fiberwise_of_maps_to (fun q hq => mem_image_of_mem point hq)]
  refine sum_congr rfl fun ρ hρ => ?_
  rw [← hm ρ hρ, ← sum_const]
  exact sum_congr rfl fun q hq => congrArg f (mem_filter.mp hq).2

/-- Summing over a cutoff set of zeros with their multiplicities is the same as
retaining exactly those copies in the full zero sum. -/
theorem finite_zero_packet {ι : Type*} (point : ι → ℂ) (P : ℂ → Prop) [DecidablePred P]
    (hfin : {q | P (point q)}.Finite) (m : ℂ → ℕ)
    (hm : ∀ ρ, P ρ → (∃ q, point q = ρ) → {q | point q = ρ}.ncard = m ρ) :
    ∃ Z : Finset ℂ,
      (∀ ρ, ρ ∈ Z ↔ P ρ ∧ ∃ q, point q = ρ) ∧ (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ t : ℝ, ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), m ρ =
        (hfin.toFinset.filter (fun q => |(point q).im - t| ≤ 1)).card) ∧
      ∀ f : ℂ → ℂ, Summable (fun q => f (point q)) →
        (∑' q, f (point q)) = (∑ ρ ∈ Z, (m ρ : ℂ) * f ρ) +
          ∑' q, if P (point q) then 0 else f (point q) := by
  classical
  let F := hfin.toFinset
  let Z := F.image point
  have hF (q : ι) : q ∈ F ↔ P (point q) := hfin.mem_toFinset
  have hZ (ρ : ℂ) : ρ ∈ Z ↔ P ρ ∧ ∃ q, point q = ρ := by
    dsimp only [Z]
    rw [mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(hF q).mp hq, q, rfl⟩
    · rintro ⟨hρ, q, rfl⟩
      exact ⟨q, (hF q).mpr hρ, rfl⟩
  have hc (ρ : ℂ) (hρ : ρ ∈ Z) : (F.filter (fun q => point q = ρ)).card = m ρ := by
    obtain ⟨hP, hex⟩ := (hZ ρ).mp hρ
    have hset : (↑(F.filter (fun q => point q = ρ)) : Set ι) = {q | point q = ρ} := by
      ext q
      rw [mem_coe, mem_filter, hF, Set.mem_setOf_eq]
      exact ⟨And.right, fun h => ⟨h.symm ▸ hP, h⟩⟩
    rw [← Set.ncard_coe_finset, hset, hm ρ hP hex]
  refine ⟨Z, hZ, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hρ
    rw [← hc _ hρ]
    exact card_pos.mpr ⟨q, mem_filter.mpr ⟨hq, rfl⟩⟩
  · intro t
    have h := sum_eq_packet F point m hc (fun ρ => if |ρ.im - t| ≤ 1 then (1 : ℕ) else 0)
    have hterm (ρ : ℂ) : m ρ • (if |ρ.im - t| ≤ 1 then (1 : ℕ) else 0) =
        if |ρ.im - t| ≤ 1 then m ρ else 0 := by split_ifs <;> simp
    rw [sum_congr rfl (fun ρ _ => hterm ρ), ← sum_filter, ← sum_filter, sum_const, nsmul_eq_mul, mul_one] at h
    exact h.symm
  · intro f hs
    let g (q : ι) := if P (point q) then f (point q) else 0
    let tail (q : ι) := if P (point q) then 0 else f (point q)
    have hsupport : ∀ q ∉ F, g q = 0 := fun q hq => if_neg (mt (hF q).mpr hq)
    have hg : Summable g := summable_of_ne_finset_zero (s := F) hsupport
    have ht : Summable tail := (hs.sub hg).congr fun q => by
      dsimp only [tail, g]
      split_ifs <;> simp
    have he : (∑' q, g q) = ∑ ρ ∈ Z, (m ρ : ℂ) * f ρ := by
      rw [tsum_eq_sum (s := F) hsupport]
      calc (∑ q ∈ F, g q) = ∑ q ∈ F, f (point q) :=
            sum_congr rfl (fun q hq => if_pos ((hF q).mp hq))
        _ = _ := by simpa only [nsmul_eq_mul] using sum_eq_packet F point m hc f
    change (∑' q, f (point q)) = (∑ ρ ∈ Z, (m ρ : ℂ) * f ρ) + ∑' q, tail q
    rw [← he, ← hg.tsum_add ht]
    exact tsum_congr fun q => by dsimp only [g, tail]; split_ifs <;> simp

end QH.PrimeProgressions
