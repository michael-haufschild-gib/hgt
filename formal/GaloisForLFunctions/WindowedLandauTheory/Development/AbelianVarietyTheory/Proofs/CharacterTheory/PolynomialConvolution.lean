import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacteristicPolynomialMass
import Mathlib.Algebra.Polynomial.Monic

/-! Algebra of convolution over monic polynomial factorizations. -/

open Polynomial

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem finite_monic_factorisations (P : F[X]) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  by_cases hP : P = 0
  · convert Set.finite_empty
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2, h3⟩
    exact (h1.mul h2).ne_zero (h3.trans hP)
  · have hfin : {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
      letI : Fintype {D : F[X] | D.Monic ∧ D ∣ P} := Polynomial.fintypeSubtypeMonicDvd P hP
      exact Set.toFinite _
    refine (hfin.prod hfin).subset ?_
    rintro x ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3 ▸ dvd_mul_right _ _⟩, ⟨h2, h3 ▸ dvd_mul_left _ _⟩⟩

theorem conv_eq_sum (a b : F[X] → ℂ) (P : F[X]) :
    conv a b P = ∑ x ∈ (finite_monic_factorisations P).toFinset, a x.1 * b x.2 :=
  finsum_mem_eq_finite_toFinset_sum _ (finite_monic_factorisations P)

theorem conv_comm (a b : F[X] → ℂ) (P : F[X]) : conv a b P = conv b a P := by
  rw [conv_eq_sum, conv_eq_sum]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.2.1, hx.1, by rw [← hx.2.2]; exact mul_comm _ _⟩
  · intro x _; rfl
  · intro x _; rfl
  · intro x _; exact mul_comm _ _

/-- Reassociate the two orders of grouping an ordered triple of monic factors. -/
theorem conv_assoc (a b c : F[X] → ℂ) (P : F[X]) :
    conv (conv a b) c P = conv a (conv b c) P := by
  rw [conv_eq_sum, conv_eq_sum]
  simp only [conv_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun z => ⟨(z.2.1, z.2.2 * z.1.2), (z.2.2, z.1.2)⟩)
    (fun z => ⟨(z.1.1 * z.2.1, z.2.2), (z.1.1, z.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h4, h5.mul h2, by rw [← mul_assoc, h6, h3]⟩, h5, h2, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    exact ⟨⟨h1.mul h4, h5, by rw [mul_assoc, h6, h3]⟩, h1, h4, trivial⟩
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ hx
    simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := hx
    subst h6
    rfl
  · rintro ⟨⟨D, E⟩, ⟨A, B⟩⟩ _
    exact mul_assoc _ _ _

theorem conv_add_left (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a + b) c P = conv a c P + conv b c P := by
  simp only [conv_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem conv_sub_left (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a - b) c P = conv a c P - conv b c P := by
  simp only [conv_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem conv_basic : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P :=
  fun _ _ P _ => ⟨finite_monic_factorisations P, fun a b c =>
    ⟨conv_comm a b P, conv_assoc a b c P, conv_add_left a b c P, conv_sub_left a b c P⟩⟩

/-- Convolution by a function with value one at the unit cancels by induction on degree. -/
theorem conv_cancel : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 →
    (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  intro F _ a b m hm h P
  classical
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    have hfin := finite_monic_factorisations P
    have h1 := h P hP
    unfold conv at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have hmem : ((P, 1) : F[X] × F[X]) ∈ hfin.toFinset := by
      simp [hP]
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at h1
    have h2 : ∑ x ∈ hfin.toFinset.erase (P, 1), a x.1 * m x.2
        = ∑ x ∈ hfin.toFinset.erase (P, 1), b x.1 * m x.2 := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨D, E⟩ hx
      rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hx
      obtain ⟨hne, hD, hE, hDE⟩ := hx
      simp only at hD hE hDE ⊢
      have hE1 : E ≠ 1 := by
        rintro rfl
        apply hne
        rw [← hDE, mul_one]
      have hdeg : D.natDegree < n := by
        rw [← hn, ← hDE, hD.natDegree_mul hE]
        have : E.natDegree ≠ 0 := fun h0 => hE1 (hE.natDegree_eq_zero.mp h0)
        omega
      rw [ih _ hdeg D rfl hD]
    rw [h2] at h1
    simpa [hm] using h1

end GlobalTheory.CuspGL
