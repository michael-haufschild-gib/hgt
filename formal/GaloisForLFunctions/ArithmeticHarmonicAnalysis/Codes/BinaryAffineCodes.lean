import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FourDivisibleEuclidean
import Mathlib.Algebra.Module.ZMod

/-!
# Affine binary codes on finite groups

Translation by a point where a nonzero binary character is one interchanges
its two fibers. Every affine word therefore has weight zero, half the group
order, or the group order. Groups of order divisible by eight give doubly
even self-orthogonal codes, including every binary affine cube of dimension
at least three.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes

variable (G : Type*) [AddCommGroup G]

/-- Constants plus additive binary characters. -/
def binaryAffineCode : Submodule (ZMod 2) (G → ZMod 2) where
  carrier := {c | ∃ b : ZMod 2, ∃ f : G →+ ZMod 2, ∀ x, c x = b + f x}
  zero_mem' := ⟨0, 0, fun _ => (add_zero 0).symm⟩
  add_mem' := by
    rintro c d ⟨b, f, hf⟩ ⟨e, g, hg⟩
    refine ⟨b + e, f + g, fun x => ?_⟩
    change c x + d x = (b + e) + (f x + g x)
    rw [hf, hg]
    ring
  smul_mem' := by
    rintro a c ⟨b, f, hf⟩
    refine ⟨a * b, a • f, fun x => ?_⟩
    change a * c x = a * b + a * f x
    rw [hf, mul_add]

variable {G} [Fintype G]

/-- A nonzero binary character has equal fibers, even after adding a constant. -/
theorem binaryAffine_weight_balanced (b : ZMod 2) (f : G →+ ZMod 2) (hf : f ≠ 0) :
    2 * weight (fun x => b + f x) = Fintype.card G := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra! h
    exact hf (AddMonoidHom.ext h)
  have ha1 : f a = 1 := (binary_eq_zero_or_one (f a)).resolve_left ha
  have hplus (x : G) : b + f (x + a) = (b + f x) + 1 := by
    rw [map_add, ha1, add_assoc]
  have hminus (x : G) : b + f (x - a) = (b + f x) + 1 := by
    rw [map_sub, ha1, sub_eq_add_neg, CharTwo.neg_eq, add_assoc]
  have heq : weight (fun x => b + f x) = symbolCount (fun x => b + f x) 0 := by
    unfold weight symbolCount
    apply Finset.card_nbij' (fun x => x + a) (fun x => x - a)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hx1 := (binary_eq_zero_or_one (b + f x)).resolve_left hx
      change b + f (x + a) = 0
      rw [hplus, hx1, CharTwo.add_self_eq_zero]
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hminus, hx, zero_add]
      exact one_ne_zero
    · intro x _
      exact add_sub_cancel_right x a
    · intro x _
      exact sub_add_cancel x a
  have hpartition := symbolCount_add_weight_sub (fun x => b + f x) 0
  simp only [sub_zero] at hpartition
  rw [← heq] at hpartition
  simpa only [two_mul] using hpartition

/-- The weight distribution of affine binary words has only three possible values. -/
theorem binaryAffine_weight_cases (c : G → ZMod 2) (hc : c ∈ binaryAffineCode G) :
    weight c = 0 ∨ weight c = Fintype.card G ∨ 2 * weight c = Fintype.card G := by
  obtain ⟨b, f, hf⟩ := hc
  have hword : c = fun x => b + f x := funext hf
  rw [hword]
  by_cases hz : f = 0
  · rw [hz]
    rcases binary_eq_zero_or_one b with hb | hb
    · left
      simp only [hb, AddMonoidHom.zero_apply, add_zero, weight, ne_eq,
        not_true_eq_false, Finset.filter_false, Finset.card_empty]
    · right; left
      simpa only [hb, AddMonoidHom.zero_apply, add_zero] using
        (weight_one (K := ZMod 2) (ι := G))
  · exact Or.inr (Or.inr (binaryAffine_weight_balanced b f hz))

/-- Order divisible by eight makes every affine binary word doubly even. -/
theorem binaryAffineCode_divisible (hG : 8 ∣ Fintype.card G) :
    Divisible 4 (binaryAffineCode G) := by
  intro c hc
  rcases binaryAffine_weight_cases c hc with h | h | h
  · rw [h]; exact dvd_zero 4
  · rw [h]
    exact dvd_trans (show 4 ∣ 8 from ⟨2, rfl⟩) hG
  · have hdiv : 2 * 4 ∣ 2 * weight c := by rw [h]; exact hG
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdiv

/-- All affine binary functions are mutually orthogonal when eight divides the group order. -/
theorem binaryAffineCode_selfOrthogonal (hG : 8 ∣ Fintype.card G) :
    SelfOrthogonal (RingHom.id _) (binaryAffineCode G) :=
  binary_divisible_selfOrthogonal _ (binaryAffineCode_divisible hG)

section Dimension
variable [Module (ZMod 2) G]

/-- Evaluating a constant and a linear functional gives an affine word. -/
def binaryAffineEvaluation :
    ((ZMod 2) × (G →ₗ[ZMod 2] ZMod 2)) →ₗ[ZMod 2] (G → ZMod 2) where
  toFun v x := v.1 + v.2 x
  map_add' u v := by
    funext x
    change (u.1 + v.1) + (u.2 x + v.2 x) = (u.1 + u.2 x) + (v.1 + v.2 x)
    ring
  map_smul' a v := by
    funext x
    change a * v.1 + a * v.2 x = a * (v.1 + v.2 x)
    rw [mul_add]

omit [Fintype G] in
/-- The constant term and linear part of an affine function are unique. -/
theorem binaryAffineEvaluation_injective : Function.Injective (binaryAffineEvaluation (G := G)) := by
  intro u v h
  have h0 : u.1 = v.1 := by
    have hzero := congrFun h 0
    change u.1 + u.2 0 = v.1 + v.2 0 at hzero
    simpa only [map_zero, add_zero] using hzero
  apply Prod.ext h0
  ext x
  have hx := congrFun h x
  change u.1 + u.2 x = v.1 + v.2 x at hx
  rw [h0] at hx
  exact add_left_cancel hx

omit [Fintype G] in
/-- Additive binary characters are precisely binary linear functionals. -/
theorem binaryAffineEvaluation_range :
    LinearMap.range (binaryAffineEvaluation (G := G)) = binaryAffineCode G := by
  ext c
  constructor
  · rintro ⟨⟨b, f⟩, rfl⟩
    exact ⟨b, f.toAddMonoidHom, fun _ => rfl⟩
  · rintro ⟨b, f, hf⟩
    exact ⟨(b, f.toZModLinearMap 2), funext fun x => (hf x).symm⟩

/-- Affine binary functions have one constant coefficient and one coefficient per dimension. -/
theorem binaryAffineCode_finrank :
    Module.finrank (ZMod 2) (binaryAffineCode G) = 1 + Module.finrank (ZMod 2) G := by
  rw [← binaryAffineEvaluation_range,
    LinearMap.finrank_range_of_inj binaryAffineEvaluation_injective,
    Module.finrank_prod, Module.finrank_self, Module.finrank_linearMap_self]

end Dimension

/-- First-order binary Reed–Muller codes on cubes of dimension at least three. -/
def binaryCubeAffineCode (n : ℕ) :
    Submodule (ZMod 2) ((Fin (n + 3) → ZMod 2) → ZMod 2) :=
  binaryAffineCode (Fin (n + 3) → ZMod 2)

private theorem binaryCube_card_dvd_eight (n : ℕ) :
    8 ∣ Fintype.card (Fin (n + 3) → ZMod 2) := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  refine ⟨2 ^ n, ?_⟩
  rw [pow_add]
  ring

/-- Every affine cube code in this family is four-divisible, without extra premises. -/
theorem binaryCubeAffineCode_divisible (n : ℕ) : Divisible 4 (binaryCubeAffineCode n) :=
  binaryAffineCode_divisible (binaryCube_card_dvd_eight n)

/-- Every affine cube code in this family is Euclidean self-orthogonal. -/
theorem binaryCubeAffineCode_selfOrthogonal (n : ℕ) :
    SelfOrthogonal (RingHom.id _) (binaryCubeAffineCode n) :=
  binary_divisible_selfOrthogonal _ (binaryCubeAffineCode_divisible n)

/-- The length-`2^(n+3)` affine cube code has dimension `n+4`. -/
theorem binaryCubeAffineCode_finrank (n : ℕ) :
    Module.finrank (ZMod 2) (binaryCubeAffineCode n) = n + 4 := by
  change Module.finrank (ZMod 2) (binaryAffineCode (Fin (n + 3) → ZMod 2)) = n + 4
  rw [binaryAffineCode_finrank, Module.finrank_pi, Fintype.card_fin]
  omega

/-- Exact minimum nonzero weight of the affine cube code: a coordinate function attains it. -/
theorem binaryCubeAffineCode_distance (n : ℕ) :
    (∀ c ∈ binaryCubeAffineCode n, c ≠ 0 → 2 ^ (n + 2) ≤ weight c) ∧
      ∃ c ∈ binaryCubeAffineCode n, weight c = 2 ^ (n + 2) := by
  have hn : Fintype.card (Fin (n + 3) → ZMod 2) = 2 * 2 ^ (n + 2) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin,
      show n + 3 = (n + 2) + 1 from by omega, pow_succ, mul_comm]
  constructor
  · intro c hc hc0
    obtain ⟨x, hx⟩ : ∃ x, c x ≠ 0 := by
      by_contra! h
      exact hc0 (funext h)
    have hw : 0 < weight c := by
      apply Finset.card_pos.mpr
      refine ⟨x, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx
    rcases binaryAffine_weight_cases c hc with h | h | h
    · omega
    · rw [h, hn]
      omega
    · rw [hn] at h
      omega
  · let f : (Fin (n + 3) → ZMod 2) →+ ZMod 2 :=
      { toFun := fun x => x 0
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hf : f ≠ 0 := by
      intro h
      have h1 := congrArg (fun g : (Fin (n + 3) → ZMod 2) →+ ZMod 2 => g (fun _ => 1)) h
      exact one_ne_zero h1
    refine ⟨(fun x => f x), ⟨0, f, fun _ => (zero_add _).symm⟩, ?_⟩
    have hw := binaryAffine_weight_balanced 0 f hf
    simp only [zero_add, hn] at hw
    omega

#print axioms binaryCubeAffineCode_divisible
#print axioms binaryCubeAffineCode_selfOrthogonal
#print axioms binaryCubeAffineCode_finrank
#print axioms binaryCubeAffineCode_distance

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
