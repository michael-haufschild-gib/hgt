import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Orthogonality bounds the support of a difference of character sums.
If a twist is trivial on that support, it preserves both disjoint
character families. -/

open Finset ComplexConjugate

namespace GlobalTheory.EllipticCharacters

variable {G : Type} [CommGroup G] [Fintype G]

private theorem norm_char (χ : G →* ℂˣ) (z : G) : ‖((χ z : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ z : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

private theorem sum_char (χ : G →* ℂˣ) (h : χ ≠ 1) : ∑ z, ((χ z : ℂˣ) : ℂ) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : G, χ a ≠ 1 := by
    by_contra! hAll
    exact h (MonoidHom.ext hAll)
  let S := ∑ z : G, (χ z : ℂ)
  have hshift : S = S * (χ a : ℂ) := by
    calc
      S = ∑ z : G, (χ (z * a) : ℂ) := (Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun _ => rfl)).symm
      _ = S * (χ a : ℂ) := by simp only [S, map_mul, Units.val_mul, Finset.sum_mul]
  have hz : S * ((χ a : ℂ) - 1) = 0 := by rw [mul_sub, mul_one, ← hshift, sub_self]
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr fun e => ha (Units.ext e))

private theorem conj_char (χ : G →* ℂˣ) (z : G) : conj ((χ z : ℂˣ) : ℂ) = (((χ⁻¹) z : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Complex.inv_eq_conj (norm_char χ z)]

open Classical in
private theorem sum_mul_conj (χ ψ : G →* ℂˣ) :
    ∑ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  have : ∀ z, ((χ z : ℂˣ) : ℂ) * conj ((ψ z : ℂˣ) : ℂ) = (((χ * ψ⁻¹) z : ℂˣ) : ℂ) := by
    intro z
    rw [conj_char, MonoidHom.mul_apply, Units.val_mul]
  simp_rw [this]
  split_ifs with h
  · subst h
    simp
  · exact sum_char _ (fun hh => h (mul_inv_eq_one.mp hh))

noncomputable def orbitSumDifference (A B : Finset (G →* ℂˣ)) (z : G) : ℂ :=
  ∑ χ ∈ A, ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, ((χ z : ℂˣ) : ℂ)

open Classical in
private theorem inner_dif (A B : Finset (G →* ℂˣ)) (ψ : G →* ℂˣ) :
    ∑ z, orbitSumDifference A B z * conj ((ψ z : ℂˣ) : ℂ) =
      (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0)) := by
  have key : ∀ C : Finset (G →* ℂˣ),
      ∑ z, (∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)) * conj ((ψ z : ℂˣ) : ℂ) =
        (Fintype.card G : ℂ) * (if ψ ∈ C then 1 else 0) := by
    intro C
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [sum_mul_conj]
    rw [Finset.sum_ite_eq' C ψ]
    split_ifs <;> simp
  simp only [orbitSumDifference, sub_mul, Finset.sum_sub_distrib, key]
  ring

private theorem parseval (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) :
    ∑ z, orbitSumDifference A B z * conj (orbitSumDifference A B z) = (Fintype.card G : ℂ) * ((#A : ℂ) + #B) := by
  classical
  have hc : ∀ z, conj (orbitSumDifference A B z) =
      ∑ χ ∈ A, conj ((χ z : ℂˣ) : ℂ) - ∑ χ ∈ B, conj ((χ z : ℂˣ) : ℂ) := by
    intro z
    simp [orbitSumDifference, map_sub, map_sum]
  simp_rw [hc, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  rw [Finset.sum_comm (s := Finset.univ) (t := B)]
  simp_rw [inner_dif]
  have hA : ∑ ψ ∈ A, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0))
      = (Fintype.card G : ℂ) * #A := by
    rw [Finset.sum_congr rfl (g := fun _ => (Fintype.card G : ℂ))]
    · simp [mul_comm]
    · intro ψ hψ
      have : ψ ∉ B := Finset.disjoint_left.mp hd hψ
      simp [hψ, this]
  have hB : ∑ ψ ∈ B, (Fintype.card G : ℂ) * ((if ψ ∈ A then 1 else 0) - (if ψ ∈ B then 1 else 0))
      = - ((Fintype.card G : ℂ) * #B) := by
    rw [Finset.sum_congr rfl (g := fun _ => - (Fintype.card G : ℂ))]
    · simp [mul_comm]
    · intro ψ hψ
      have : ψ ∉ A := Finset.disjoint_right.mp hd hψ
      simp [hψ, this]
  rw [hA, hB]
  ring

private theorem norm_dif_le (A B : Finset (G →* ℂˣ)) (z : G) : ‖orbitSumDifference A B z‖ ≤ (#A : ℝ) + #B := by
  have h : ∀ C : Finset (G →* ℂˣ), ‖∑ χ ∈ C, ((χ z : ℂˣ) : ℂ)‖ ≤ #C := by
    intro C
    refine (norm_sum_le _ _).trans ?_
    simp [norm_char]
  exact (norm_sub_le _ _).trans (add_le_add (h A) (h B))

theorem card_le_of_difference_supported (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) (D : Finset G)
    (hD : ∀ z, z ∉ D → orbitSumDifference A B z = 0) (hne : 0 < #A + #B) :
    Fintype.card G ≤ #D * (#A + #B) := by
  have h1 : ∑ z, ‖orbitSumDifference A B z‖ ^ 2 = (Fintype.card G : ℝ) * ((#A : ℝ) + #B) := by
    have := parseval A B hd
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    exact_mod_cast this
  have h2 : ∑ z, ‖orbitSumDifference A B z‖ ^ 2 = ∑ z ∈ D, ‖orbitSumDifference A B z‖ ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)
    simp [hD z hz]
  have h3 : ∑ z ∈ D, ‖orbitSumDifference A B z‖ ^ 2 ≤ (#D : ℝ) * ((#A : ℝ) + #B) ^ 2 := by
    have : ∀ z ∈ D, ‖orbitSumDifference A B z‖ ^ 2 ≤ ((#A : ℝ) + #B) ^ 2 := fun z _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_dif_le A B z) 2
    simpa using Finset.sum_le_sum this
  have hpos : (0 : ℝ) < (#A : ℝ) + #B := by exact_mod_cast hne
  have h4 : (Fintype.card G : ℝ) ≤ (#D : ℝ) * ((#A : ℝ) + #B) := by
    have : (Fintype.card G : ℝ) * ((#A : ℝ) + #B) ≤ ((#D : ℝ) * ((#A : ℝ) + #B)) * ((#A : ℝ) + #B) := by
      rw [← h1, h2]
      simpa only [pow_two, mul_assoc] using h3
    exact le_of_mul_le_mul_right this hpos
  exact_mod_cast h4

theorem translate_mem_of_difference_supported (A B : Finset (G →* ℂˣ)) (hd : Disjoint A B) (D : Finset G)
    (hD : ∀ z, z ∉ D → orbitSumDifference A B z = 0) (η : G →* ℂˣ) (hη : ∀ z ∈ D, η z = 1) (ψ : G →* ℂˣ) :
    (ψ ∈ A → ψ * η ∈ A) ∧ (ψ ∈ B → ψ * η ∈ B) := by
  classical
  have h1 : ∑ z, orbitSumDifference A B z * conj (((ψ * η) z : ℂˣ) : ℂ) = ∑ z, orbitSumDifference A B z * conj ((ψ z : ℂˣ) : ℂ) := by
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : z ∈ D
    · simp [hη z hz]
    · simp [hD z hz]
  rw [inner_dif, inner_dif] at h1
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 := mul_left_cancel₀ hc h1
  constructor
  · intro hψ
    have hB : ψ ∉ B := Finset.disjoint_left.mp hd hψ
    by_contra hn
    by_cases hb : ψ * η ∈ B <;> simp [hn, hψ, hB, hb] at h2
    norm_num at h2
  · intro hψ
    have hA : ψ ∉ A := Finset.disjoint_right.mp hd hψ
    by_contra hn
    by_cases ha : ψ * η ∈ A <;> simp [hn, hψ, hA, ha] at h2
    norm_num at h2

end GlobalTheory.EllipticCharacters
