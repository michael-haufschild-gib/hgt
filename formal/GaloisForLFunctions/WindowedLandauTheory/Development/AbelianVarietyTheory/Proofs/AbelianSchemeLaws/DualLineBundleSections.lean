import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback
import Mathlib.AlgebraicGeometry.Properties

/-! On an integral scheme with a field of global functions, sections of a line bundle
and its dual detect a global generator. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X Y : Scheme.{0}} (L : LB X)

/-- The dual line bundle uses the same opens and inverse transition functions. -/
def dual : LB X where
  ι := L.ι
  U := L.U
  g i j := (L.g i j)⁻¹

theorem dual_isLB (hL : L.IsLB) : (dual L).IsLB where
  cover := hL.cover
  g_self i := by
    change res _ ((L.g i i)⁻¹) = 1
    rw [map_inv, hL.g_self i, inv_one]
  cocycle i j k := by
    have e := congrArg (fun u => u⁻¹) (hL.cocycle i j k)
    simpa only [dual, map_inv, mul_inv] using e

theorem pull_dual (π : Y ⟶ X) : (dual L).pull π = dual (L.pull π) := by
  refine congrArg (LB.mk (L.pull π).ι (L.pull π).U) ?_
  funext i j
  change (∏ k : PUnit, (res _ (pullU π _ ((L.g (i k) (j k))⁻¹))) ^ (1 : ℤ)) =
    (∏ k : PUnit, (res _ (pullU π _ (L.g (i k) (j k)))) ^ (1 : ℤ))⁻¹
  simp only [map_inv, zpow_one, Finset.prod_inv_distrib]

private def zeroSection : L.Sec where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

theorem nontrivial_sections_iff :
    Nontrivial (Γ(toMod L, ⊤)) ↔ ∃ (s : L.Sec) (i : L.ι), s.f i ≠ 0 := by
  rw [globalCoordinates.nontrivial_congr, nontrivial_iff_exists_ne (zeroSection L)]
  refine exists_congr fun s => ?_
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    cases s with
    | mk vals compat =>
      have he : vals = fun _ => 0 := funext hn
      subst vals
      exact h rfl
  · rintro ⟨i, hi⟩ h
    exact hi (congrArg (fun s => s.f i) h)

private theorem nonempty_of_section_ne_zero {U : X.Opens} {x : Γ(X, U)} (hx : x ≠ 0) :
    (U : Set X).Nonempty := by
  by_contra h
  have hU : U = ⊥ := Opens.ext (Set.not_nonempty_iff_eq_empty.1 h)
  subst U
  exact hx (Subsingleton.elim _ _)

/-- A line bundle and its dual both have a nonzero global section exactly when the bundle
is trivial, provided the scheme is integral and its nonzero global functions are units. -/
theorem exists_gen_iff_nontrivial_sections_and_dual [IsIntegral X]
    (hL : L.IsLB) (hΓ : ∀ x : Γ(X, ⊤), x ≠ 0 → IsUnit x) :
    (∃ t : L.Gen, t.IsGen) ↔ Nontrivial (Γ(toMod L, ⊤)) ∧ Nontrivial (Γ(toMod (dual L), ⊤)) := by
  rw [nontrivial_sections_iff, nontrivial_sections_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hL.cover.ge (Set.mem_univ x))
    haveI : Nonempty (L.U i) := ⟨⟨x, hi⟩⟩
    refine ⟨⟨⟨fun j => (t.s j).val, fun j k => congrArg Units.val (ht j k)⟩, i, (t.s i).ne_zero⟩,
      ⟨⟨fun j => ((t.s j)⁻¹).val, fun j k => ?_⟩, i, ((t.s i)⁻¹).ne_zero⟩⟩
    have e := congrArg (fun u => u⁻¹) (ht j k)
    simp only [mul_inv, ← map_inv] at e
    exact congrArg Units.val e
  · rintro ⟨⟨s, i, hi⟩, ⟨t, j, hj⟩⟩
    let b (k : L.ι) : Γ(X, L.U k) := t.f k
    change b j ≠ 0 at hj
    have hcompat (k l : L.ι) : resG X inf_le_left (s.f k * b k) =
        resG X inf_le_right (s.f l * b l) := by
      have e₁ : resG X inf_le_left (s.f k) = (L.g k l).val * resG X inf_le_right (s.f l) :=
        s.compat k l
      have e₂ : resG X inf_le_left (b k) = ((L.g k l)⁻¹).val * resG X inf_le_right (b l) :=
        t.compat k l
      rw [map_mul, map_mul, e₁, e₂, mul_mul_mul_comm, Units.mul_inv, one_mul]
    obtain ⟨a, ha⟩ := exists_fun_of_cover L.U (fun _ => le_top) hL.cover.ge
      (fun k => s.f k * b k) hcompat
    have hne : (↑(L.U i ⊓ L.U j) : Set X).Nonempty :=
      nonempty_preirreducible_inter (L.U i).isOpen (L.U j).isOpen
        (nonempty_of_section_ne_zero hi) (nonempty_of_section_ne_zero hj)
    haveI : Nonempty (L.U i ⊓ L.U j : X.Opens) := hne.to_subtype
    have hsj : s.f j ≠ 0 := by
      intro hz
      have e : resG X inf_le_left (s.f i) = (L.g i j).val * resG X inf_le_right (s.f j) := s.compat i j
      rw [hz, map_zero, mul_zero] at e
      exact hi (Scheme.map_injective_of_isIntegral X (homOfLE inf_le_left) (e.trans (map_zero _).symm))
    haveI : Nonempty (L.U j) := (nonempty_of_section_ne_zero hsj).to_subtype
    have ha₀ : a ≠ 0 := by
      intro hz
      have e := ha j
      rw [hz, map_zero] at e
      exact mul_ne_zero hsj hj e.symm
    let s' := globalCoordinates.symm s
    refine exists_gen_of_unit_coordinates s' fun k => ?_
    change IsUnit ((globalCoordinates (globalCoordinates.symm s)).f k)
    rw [Equiv.apply_symm_apply]
    exact isUnit_of_mul_isUnit_left (ha k ▸ (hΓ a ha₀).map (resG X le_top))

end GlobalTheory.LineBundleSections
