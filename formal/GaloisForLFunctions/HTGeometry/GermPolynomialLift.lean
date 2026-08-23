import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Lifting germs and polynomials over germs

Finitely many germs at a point lift to sections over a common open neighbourhood, because the
stalk is a filtered colimit.  Consequently a polynomial over the stalk is the image of a
polynomial over the sections on some neighbourhood, and a normalising condition on the constant
term can be arranged after shrinking further.
-/

namespace HTGeometry

open CategoryTheory TopologicalSpace Opposite TopCat

universe u

variable {X : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} X) (x : X)

set_option backward.isDefEq.respectTransparency false in
/-- Finitely many germs at a point lift to sections over a common open neighbourhood. -/
theorem exists_germ_lift_range (n : ℕ) (a : ℕ → (F.stalk x : Type u)) :
    ∃ (U : Opens X) (hx : x ∈ U) (b : ℕ → (F.obj (op U) : Type u)),
      ∀ i < n, F.germ U x hx (b i) = a i := by
  classical
  induction n with
  | zero => exact ⟨⊤, trivial, fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
      obtain ⟨U, hxU, b, hb⟩ := ih
      obtain ⟨V, hxV, c, hc⟩ := F.exists_germ_eq (a n)
      refine ⟨U ⊓ V, ⟨hxU, hxV⟩, fun i => if i = n then F.map (homOfLE inf_le_right).op c
        else F.map (homOfLE inf_le_left).op (b i), ?_⟩
      intro i hi
      dsimp only
      by_cases hin : i = n
      · subst hin
        rw [if_pos rfl, TopCat.Presheaf.germ_res_apply]
        exact hc
      · have hi' : i < n := by omega
        rw [if_neg hin, TopCat.Presheaf.germ_res_apply]
        exact hb i hi'

set_option backward.isDefEq.respectTransparency false in
/-- A polynomial over the stalk is the image of a polynomial over the sections on some
neighbourhood. -/
theorem exists_germ_lift_polynomial (P : Polynomial (F.stalk x : Type u)) :
    ∃ (U : Opens X) (hx : x ∈ U) (Q : Polynomial (F.obj (op U) : Type u)),
      Q.map (F.germ U x hx).hom = P := by
  classical
  obtain ⟨U, hx, b, hb⟩ := exists_germ_lift_range F x (P.natDegree + 1) (fun i => P.coeff i)
  refine ⟨U, hx, ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (b i), ?_⟩
  ext m
  rw [Polynomial.coeff_map]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hm : m ≤ P.natDegree
  · have hmem : m ∈ Finset.range (P.natDegree + 1) := Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl]
      exact hb m (by omega)
    · intro i _ hine
      exact if_neg hine
    · intro hc
      exact absurd hmem hc
  · have hzero : ∀ i ∈ Finset.range (P.natDegree + 1), (if i = m then b i else 0) = 0 := by
      intro i hi
      refine if_neg ?_
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

set_option backward.isDefEq.respectTransparency false in
/-- A normalised polynomial over the stalk is the image of a normalised polynomial over the
sections on some neighbourhood. -/
theorem exists_germ_lift_normalized_polynomial (P : Polynomial (F.stalk x : Type u))
    (hP : P.coeff 0 = 1) :
    ∃ (U : Opens X) (hx : x ∈ U) (Q : Polynomial (F.obj (op U) : Type u)),
      Q.coeff 0 = 1 ∧ Q.map (F.germ U x hx).hom = P := by
  obtain ⟨U, hx, Q, hQ⟩ := exists_germ_lift_polynomial F x P
  have hcoeff : F.germ U x hx (Q.coeff 0) = F.germ U x hx (1 : (F.obj (op U) : Type u)) := by
    rw [map_one]
    have := congrArg (fun R : Polynomial (F.stalk x : Type u) => R.coeff 0) hQ
    simpa [Polynomial.coeff_map, hP] using this
  obtain ⟨W, hxW, iWU, iWU', hW⟩ := F.germ_eq x hx hx (Q.coeff 0) 1 hcoeff
  refine ⟨W, hxW, Q.map (F.map iWU.op).hom, ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    rw [show (F.map iWU.op).hom (Q.coeff 0) = F.map iWU.op (Q.coeff 0) from rfl, hW]
    exact map_one _
  · rw [Polynomial.map_map]
    rw [show (F.germ W x hxW).hom.comp (F.map iWU.op).hom
        = (F.map iWU.op ≫ F.germ W x hxW).hom from rfl]
    rw [TopCat.Presheaf.germ_res F iWU x hxW]
    exact hQ

set_option backward.isDefEq.respectTransparency false in
/-- Finitely many equalities of germs hold already on a common smaller neighbourhood. -/
theorem exists_res_eq_of_germ_eq_range (U : Opens X) (hx : x ∈ U) (n : ℕ)
    (a b : ℕ → (F.obj (op U) : Type u))
    (h : ∀ i < n, F.germ U x hx (a i) = F.germ U x hx (b i)) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
      ∀ k < n, F.map i.op (a k) = F.map i.op (b k) := by
  induction n with
  | zero => exact ⟨U, hx, 𝟙 U, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
      obtain ⟨V₀, hxV₀, i₀, hi₀⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨W, hxW, iW, iW', hW⟩ := F.germ_eq x hx hx (a n) (b n) (h n (by omega))
      rw [Subsingleton.elim iW' iW] at hW
      refine ⟨V₀ ⊓ W, ⟨hxV₀, hxW⟩, homOfLE (le_trans inf_le_left i₀.le), ?_⟩
      intro k hk
      have hfac : ∀ c : (F.obj (op U) : Type u),
          F.map (homOfLE (le_trans (inf_le_left : V₀ ⊓ W ≤ V₀) i₀.le)).op c
            = F.map (homOfLE (inf_le_left : V₀ ⊓ W ≤ V₀)).op (F.map i₀.op c) := by
        intro c
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        congr 2
      have hfacW : ∀ c : (F.obj (op U) : Type u),
          F.map (homOfLE (le_trans (inf_le_left : V₀ ⊓ W ≤ V₀) i₀.le)).op c
            = F.map (homOfLE (inf_le_right : V₀ ⊓ W ≤ W)).op (F.map iW.op c) := by
        intro c
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        congr 2
      by_cases hkn : k = n
      · subst hkn
        rw [hfacW (a k), hfacW (b k), hW]
      · have hk' : k < n := by omega
        rw [hfac (a k), hfac (b k), hi₀ k hk']

set_option backward.isDefEq.respectTransparency false in
/-- Two polynomials with the same image in the stalk already agree over a smaller
neighbourhood. -/
theorem exists_res_eq_of_germ_eq_polynomial (U : Opens X) (hx : x ∈ U)
    (P Q : Polynomial (F.obj (op U) : Type u))
    (h : P.map (F.germ U x hx).hom = Q.map (F.germ U x hx).hom) :
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ⟶ U),
      P.map (F.map i.op).hom = Q.map (F.map i.op).hom := by
  set n := max P.natDegree Q.natDegree + 1 with hn
  have hcoeff : ∀ i < n, F.germ U x hx (P.coeff i) = F.germ U x hx (Q.coeff i) := by
    intro i _
    have := congrArg (fun R : Polynomial (F.stalk x : Type u) => R.coeff i) h
    simpa [Polynomial.coeff_map] using this
  obtain ⟨V, hxV, i, hi⟩ := exists_res_eq_of_germ_eq_range F x U hx n _ _ hcoeff
  refine ⟨V, hxV, i, ?_⟩
  ext m
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  by_cases hm : m < n
  · exact hi m hm
  · have hP : P.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hQ : Q.coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hP, hQ]

end HTGeometry
