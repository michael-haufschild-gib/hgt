import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentHypersurface
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Kloosterman moments as differences of torus point counts

Scaling a nonzero parameter preserves the global moment. Orthogonality in both
parameters therefore expresses it as the difference of two explicit point counts:
one imposes vanishing coordinate sum, the other also vanishing reciprocal sum.
-/

open Finset AddChar
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

open SignedSuccessorArithmetic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Torus tuples whose coordinate sum vanishes. -/
def coordinateZeroTorus (m : ℕ) : Finset (MomentTorus F m) :=
  univ.filter (fun x => ∑ j, (x j : F) = 0)

/-- Torus tuples whose coordinate and reciprocal coordinate sums both vanish. -/
def doubleZeroTorus (m : ℕ) : Finset (MomentTorus F m) :=
  (coordinateZeroTorus m).filter (fun x => ∑ j, (x j : F)⁻¹ = 0)

/-- Scaling the summation variable moves a nonzero parameter into the first slot. -/
theorem kloosterman_rescale_nonzero (ψ : AddChar F ℂ) (a : F) {b : F} (hb : b ≠ 0) :
    kloosterman ψ a b = kloosterman ψ (a * b) 1 := by
  unfold kloosterman
  refine sum_nbij' (fun x : F => x / b) (fun x : F => b * x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact div_ne_zero hx hb
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact mul_ne_zero hb hx
  · intro x _
    exact mul_div_cancel₀ x hb
  · intro x _
    simp [hb]
  · intro x hx
    have hx0 := (mem_filter.mp hx).2
    congr 1
    field_simp

/-- The global tensor moment is independent of the nonzero second parameter. -/
theorem kloosterman_moment_nonzero_parameter (ψ : AddChar F ℂ) {b : F} (hb : b ≠ 0)
    (m : ℕ) :
    ∑ a : F, kloosterman ψ a b ^ m = ∑ a : F, kloosterman ψ a 1 ^ m := by
  simp_rw [kloosterman_rescale_nonzero ψ _ hb]
  exact sum_nbij' (fun a : F => a * b) (fun a : F => a / b)
    (by simp) (by simp) (by simp [hb]) (by simp [hb]) (by intros; rfl)

/-- Orthogonality in both parameters counts the intersection of the two hypersurfaces. -/
theorem kloosterman_double_moment_count {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (m : ℕ) :
    ∑ b : F, ∑ a : F, kloosterman ψ a b ^ m =
      (Fintype.card F : ℂ) ^ 2 * (doubleZeroTorus (F := F) m).card := by
  unfold doubleZeroTorus coordinateZeroTorus
  rw [sum_congr rfl (fun b _ => kloosterman_moment_hypersurface hψ b m)]
  rw [← mul_sum, sum_comm]
  simp_rw [sum_mulShift _ hψ]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  ring

/-- At the zero parameter only the coordinate-sum constraint remains. -/
theorem kloosterman_zero_parameter_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (m : ℕ) :
    ∑ a : F, kloosterman ψ a 0 ^ m =
      (Fintype.card F : ℂ) * (coordinateZeroTorus (F := F) m).card := by
  rw [kloosterman_moment_hypersurface hψ]
  simp [coordinateZeroTorus]

/-- Every nonzero-parameter moment is a difference of explicit torus point counts. -/
theorem kloosterman_moment_count_identity {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ((Fintype.card F : ℂ) - 1) * (∑ a : F, kloosterman ψ a b ^ m) =
      (Fintype.card F : ℂ) ^ 2 * (doubleZeroTorus (F := F) m).card -
        (Fintype.card F : ℂ) * (coordinateZeroTorus (F := F) m).card := by
  have h := kloosterman_double_moment_count hψ m
  rw [← sum_filter_add_sum_filter_not univ (fun t : F => t ≠ 0)] at h
  have hz : (univ : Finset F).filter (fun t => ¬ t ≠ 0) = {0} := by ext; simp
  have hc : ((univ.filter (fun t : F => t ≠ 0)).card : ℂ) = (Fintype.card F : ℂ) - 1 := by
    rw [card_units_filter, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hconst : (∑ t ∈ univ.filter (fun t : F => t ≠ 0), ∑ a : F, kloosterman ψ a t ^ m) =
      ((Fintype.card F : ℂ) - 1) * (∑ a : F, kloosterman ψ a b ^ m) := by
    rw [sum_congr rfl (fun t ht =>
      (kloosterman_moment_nonzero_parameter ψ (mem_filter.mp ht).2 m).trans
        (kloosterman_moment_nonzero_parameter ψ hb m).symm), sum_const, nsmul_eq_mul, hc]
  rw [hconst, hz, sum_singleton, kloosterman_zero_parameter_moment hψ] at h
  exact eq_sub_iff_add_eq.mpr h

/-- The projective chart with leading coordinate one and vanishing coordinate sum. -/
def normalizedCoordinateZeroTorus (m : ℕ) : Finset (MomentTorus F m) :=
  univ.filter (fun x => 1 + ∑ j, (x j : F) = 0)

/-- The same chart with vanishing reciprocal coordinate sum. -/
def normalizedDoubleZeroTorus (m : ℕ) : Finset (MomentTorus F m) :=
  (normalizedCoordinateZeroTorus m).filter (fun x => 1 + ∑ j, (x j : F)⁻¹ = 0)

/-- A nonempty torus tuple splits uniquely into its leading scale and normalized tail. -/
def torusScaleSplit (m : ℕ) :
    MomentTorus F (m + 1) ≃ {r : F // r ≠ 0} × MomentTorus F m where
  toFun x := (x 0, fun j =>
    ⟨(x j.succ : F) / (x 0 : F), div_ne_zero (x j.succ).property (x 0).property⟩)
  invFun p := Fin.cons p.1 (fun j =>
    ⟨(p.1 : F) * (p.2 j : F), mul_ne_zero p.1.property (p.2 j).property⟩)
  left_inv := by
    intro x
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact Subtype.ext (mul_div_cancel₀ _ (x 0).property)
  right_inv := by
    intro p
    apply Prod.ext
    · rfl
    · funext j
      apply Subtype.ext
      change (p.1 : F) * (p.2 j : F) / (p.1 : F) = (p.2 j : F)
      field_simp [p.1.property]

omit [Fintype F] [DecidableEq F] in
private theorem torusScaleSplit_symm_zero (m : ℕ) (r : {r : F // r ≠ 0})
    (x : MomentTorus F m) : ((torusScaleSplit m).symm (r, x) 0 : F) = r := rfl

omit [Fintype F] [DecidableEq F] in
private theorem torusScaleSplit_symm_succ (m : ℕ) (r : {r : F // r ≠ 0})
    (x : MomentTorus F m) (j : Fin m) :
    ((torusScaleSplit m).symm (r, x) j.succ : F) = (r : F) * (x j : F) := rfl

omit [Fintype F] [DecidableEq F] in
private theorem coordinate_sum_chart (m : ℕ) (r : {r : F // r ≠ 0}) (x : MomentTorus F m) :
    (∑ j, ((torusScaleSplit m).symm (r, x) j : F)) = (r : F) * (1 + ∑ j, (x j : F)) := by
  simp only [Fin.sum_univ_succ, torusScaleSplit_symm_zero, torusScaleSplit_symm_succ]
  rw [← mul_sum]
  ring

omit [Fintype F] [DecidableEq F] in
private theorem reciprocal_sum_chart (m : ℕ) (r : {r : F // r ≠ 0}) (x : MomentTorus F m) :
    (∑ j, ((torusScaleSplit m).symm (r, x) j : F)⁻¹) =
      (r : F)⁻¹ * (1 + ∑ j, (x j : F)⁻¹) := by
  simp only [Fin.sum_univ_succ, torusScaleSplit_symm_zero, torusScaleSplit_symm_succ, mul_inv_rev]
  rw [← sum_mul]
  ring

private theorem card_nonzero_field : Fintype.card {r : F // r ≠ 0} = Fintype.card F - 1 := by
  have h := sum_subtype (F := inferInstance) (p := fun r : F => r ≠ 0)
    (univ.filter (fun r : F => r ≠ 0)) (by simp) (fun _ => (1 : ℕ))
  simpa only [sum_const, nsmul_eq_mul, mul_one, card_univ, card_units_filter, Nat.cast_id] using h.symm

/-- A scalar-invariant tuple set has `q−1` copies of its normalized chart. -/
private theorem card_via_torus_chart (m : ℕ) (S : Finset (MomentTorus F (m + 1)))
    (T : Finset (MomentTorus F m))
    (h : ∀ r x, (torusScaleSplit m).symm (r, x) ∈ S ↔ x ∈ T) :
    S.card = (Fintype.card F - 1) * T.card := by
  let e : S ≃ {r : F // r ≠ 0} × T :=
    { toFun := fun x =>
        ((torusScaleSplit m x.val).1,
          ⟨(torusScaleSplit m x.val).2,
            (h (torusScaleSplit m x.val).1 (torusScaleSplit m x.val).2).mp
              (by
                change (torusScaleSplit m).symm (torusScaleSplit m x.val) ∈ S
                rw [Equiv.symm_apply_apply]
                exact x.property)⟩)
      invFun := fun p => ⟨(torusScaleSplit m).symm (p.1, p.2.val),
        (h p.1 p.2.val).mpr p.2.property⟩
      left_inv := fun x => Subtype.ext ((torusScaleSplit m).symm_apply_apply x.val)
      right_inv := by
        intro p
        have hp := (torusScaleSplit m).apply_symm_apply (p.1, p.2.val)
        exact Prod.ext
          (congrArg (fun q : {r : F // r ≠ 0} × MomentTorus F m => q.1) hp)
          (Subtype.ext (congrArg (fun q : {r : F // r ≠ 0} × MomentTorus F m => q.2) hp)) }
  simpa only [Fintype.card_coe, Fintype.card_prod, card_nonzero_field] using Fintype.card_congr e

/-- Dividing by simultaneous scalar multiplication gives the coordinate-zero chart. -/
theorem coordinateZeroTorus_card (m : ℕ) :
    (coordinateZeroTorus (F := F) (m + 1)).card =
      (Fintype.card F - 1) * (normalizedCoordinateZeroTorus (F := F) m).card := by
  apply card_via_torus_chart
  intro r x
  simp only [coordinateZeroTorus, normalizedCoordinateZeroTorus, mem_filter, mem_univ,
    true_and, coordinate_sum_chart, mul_eq_zero, r.property, false_or]

/-- Dividing the intersection by scalar multiplication gives the double-zero chart. -/
theorem doubleZeroTorus_card (m : ℕ) :
    (doubleZeroTorus (F := F) (m + 1)).card =
      (Fintype.card F - 1) * (normalizedDoubleZeroTorus (F := F) m).card := by
  apply card_via_torus_chart
  intro r x
  simp only [doubleZeroTorus, coordinateZeroTorus, normalizedDoubleZeroTorus,
    normalizedCoordinateZeroTorus, mem_filter, mem_univ, true_and,
    coordinate_sum_chart, reciprocal_sum_chart, mul_eq_zero, inv_eq_zero,
    r.property, false_or]

/-- Every positive tensor degree is exactly `q(q A − B)` for two projective torus counts. -/
theorem kloosterman_moment_projective_counts {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ∑ a : F, kloosterman ψ a b ^ (m + 1) =
      (Fintype.card F : ℂ) *
        ((Fintype.card F : ℂ) * (normalizedDoubleZeroTorus (F := F) m).card -
          (normalizedCoordinateZeroTorus (F := F) m).card) := by
  have h := kloosterman_moment_count_identity hψ hb (m + 1)
  rw [doubleZeroTorus_card, coordinateZeroTorus_card, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub Fintype.card_pos, Nat.cast_one] at h
  have hq : (Fintype.card F : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast (ne_of_gt (Fintype.one_lt_card (α := F))))
  apply mul_left_cancel₀ hq
  calc ((Fintype.card F : ℂ) - 1) * (∑ a : F, kloosterman ψ a b ^ (m + 1))
      = (Fintype.card F : ℂ) ^ 2 *
          (((Fintype.card F : ℂ) - 1) * (normalizedDoubleZeroTorus (F := F) m).card) -
        (Fintype.card F : ℂ) *
          (((Fintype.card F : ℂ) - 1) * (normalizedCoordinateZeroTorus (F := F) m).card) := h
    _ = _ := by ring

omit [DecidableEq F] in
private theorem exists_primitive_complex_character : ∃ ψ : AddChar F ℂ, ψ.IsPrimitive := by
  let p := ringChar F
  letI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  let ψ : AddChar F ℂ := (ZMod.stdAddChar (N := p)).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom
  refine ⟨ψ, IsPrimitive.of_ne_one ?_⟩
  obtain ⟨x, hx⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
  rw [one_mul] at hx
  refine ne_one_iff.mpr ⟨x, fun h => hx ?_⟩
  exact ((ZMod.isPrimitive_stdAddChar p).zmod_char_eq_one_iff p
    (Algebra.trace (ZMod p) F x)).mp h

/-- In every even tensor degree, the double-zero chart has at least `1/q` of the
coordinate-zero chart's points. This is a point-count inequality over every finite field. -/
theorem normalized_even_incidence (k : ℕ) :
    (normalizedCoordinateZeroTorus (F := F) (2 * k + 1)).card ≤
      Fintype.card F * (normalizedDoubleZeroTorus (F := F) (2 * k + 1)).card := by
  obtain ⟨ψ, hψ⟩ := exists_primitive_complex_character (F := F)
  have h := kloosterman_moment_projective_counts hψ (b := 1) one_ne_zero (2 * k + 1)
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at h
  have hre := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, mul_zero, sub_zero, add_zero] at hre
  have hpos := kloosterman_even_moment_nonneg ψ 1 (k + 1) univ
  rw [hre] at hpos
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hi : 0 ≤ (Fintype.card F : ℝ) *
      (normalizedDoubleZeroTorus (F := F) (2 * k + 1)).card -
        (normalizedCoordinateZeroTorus (F := F) (2 * k + 1)).card := by
    by_contra hi
    exact (not_lt_of_ge hpos) (mul_neg_of_pos_of_neg hq (lt_of_not_ge hi))
  exact_mod_cast (sub_nonneg.mp hi)

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
