import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Data.ZMod.Basic

/-! Approximating a local element by principal ideles that are arbitrarily
congruent to one away from its place forces its valuation to be one. -/

noncomputable section

open NumberField IsDedekindDomain WithZero

namespace GlobalTheory.Reciprocity

variable {E : Type} [Field E] [NumberField E]

/-- The finite-coordinate approximation conditions from the closure of principal ideles. -/
def HasCongruentGlobalApproximants (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : Prop :=
  ∀ (a : ℕ), 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
    (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
      v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
    Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t

private theorem integerNorm_eq_one_mod_nat (a : ℕ) (y : 𝓞 E) :
    ((Algebra.norm ℤ (1 + (a : 𝓞 E) * y) : ℤ) : ZMod a) = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det b, ← eq_intCast (Int.castRingHom (ZMod a)), RingHom.map_det]
  have h : (Int.castRingHom (ZMod a)).mapMatrix
      (Algebra.leftMulMatrix b (1 + (a : 𝓞 E) * y)) = 1 := by
    rw [map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast,
      ← map_natCast (algebraMap (ZMod a) (Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (ZMod a))), ZMod.natCast_self, map_zero, zero_mul, add_zero]
  rw [h, Matrix.det_one]

theorem exists_integerUnit_of_valuation_eq_one (z : E) (hz : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E z = 1)
    (hz₀ : z ≠ 0) : ∃ u : (𝓞 E)ˣ, algebraMap (𝓞 E) E (u : 𝓞 E) = z := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z (fun v => (hz v).le)
  obtain ⟨y', hy'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E z⁻¹
    (fun v => by rw [map_inv₀, hz v, inv_one])
  have hyy : y * y' = 1 := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, hy, hy', mul_inv_cancel₀ hz₀, map_one]
  exact ⟨⟨y, y', hyy, by simpa only [mul_comm] using hyy⟩, hy⟩

theorem valuation_sub_one_le_one_of_ray (v : HeightOneSpectrum (𝓞 E)) (a : ℕ) (ha : 0 < a) (k : E)
    (h : v.valuation E ((k - 1) / (a : E)) ≤ 1) : v.valuation E (k - 1) ≤ 1 := by
  have hva : v.valuation E (a : E) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E)]
    exact v.valuation_le_one _
  have he := div_mul_cancel₀ (k - 1) (Nat.cast_ne_zero.mpr ha.ne' : (a : E) ≠ 0)
  rw [← he, map_mul]
  exact mul_le_one' h hva

theorem valuation_eq_one_of_ray (v : HeightOneSpectrum (𝓞 E)) (a : ℕ) (ha : 0 < a) (k : Eˣ)
    (h : v.valuation E (((k : E) - 1) / (a : E)) ≤ 1) (hi : v.valuation E ((k : E)⁻¹) ≤ 1) :
    v.valuation E (k : E) = 1 := by
  have hdiff := valuation_sub_one_le_one_of_ray v a ha (k : E) h
  have hk : v.valuation E (k : E) ≤ 1 := by
    simpa only [sub_add_cancel] using
      (Valuation.map_add_le (v.valuation E) hdiff (show v.valuation E 1 ≤ 1 by rw [map_one]))
  refine le_antisymm hk ?_
  calc 1 = v.valuation E ((k : E) * (k : E)⁻¹) := by rw [mul_inv_cancel₀ k.ne_zero, map_one]
    _ = v.valuation E (k : E) * v.valuation E ((k : E)⁻¹) := map_mul _ _ _
    _ ≤ v.valuation E (k : E) * 1 := mul_le_mul' le_rfl hi
    _ = v.valuation E (k : E) := mul_one _

private theorem exists_large_nat_unit_at (w : HeightOneSpectrum (𝓞 E)) (B : ℕ) :
    ∃ a : ℕ, B < a ∧ w.valuation E (a : E) = 1 := by
  let q := Ideal.absNorm w.asIdeal
  have hq : 0 < q := Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  refine ⟨q * B + 1, Nat.lt_succ_of_le ?_, ?_⟩
  · exact Nat.le_mul_of_pos_left B hq
  · rw [← map_natCast (algebraMap (𝓞 E) E), HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro ha
    have hm : (q : 𝓞 E) * (B : 𝓞 E) ∈ w.asIdeal := w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    have h1 := w.asIdeal.sub_mem ha hm
    push_cast at h1
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa only [add_sub_cancel_left] using h1))

theorem congruent_integer_of_valuations (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (ha : 0 < a) (hwa : w.valuation E (a : E) = 1) (k : Eˣ) (z : 𝓞 E)
    (hz : algebraMap (𝓞 E) E z = (k : E))
    (hoff : ∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
      v.valuation E (((k : E) - 1) / (a : E)) ≤ 1) :
    ∃ y : 𝓞 E, z = 1 + (a : 𝓞 E) * y := by
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (((k : E) - 1) / (a : E))
    (fun v => by
      by_cases hv : v = w
      · subst v
        rw [map_div₀, hwa, div_one, ← hz, ← map_one (algebraMap (𝓞 E) E), ← map_sub]
        exact w.valuation_le_one _
      · exact hoff v hv)
  refine ⟨y, (IsFractionRing.injective (𝓞 E) E) ?_⟩
  rw [map_add, map_one, map_mul, map_natCast, hy, hz, mul_comm (a : E),
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr ha.ne')]
  ring

private theorem integerNorm_eq_one_of_large_modulus (a : ℕ) (z : 𝓞 E)
    (hlarge : (Algebra.norm ℤ z).natAbs + 1 < a)
    (hmod : ((Algebra.norm ℤ z : ℤ) : ZMod a) = 1) : Algebra.norm ℤ z = 1 := by
  by_contra hne
  have hdvd : (a : ℤ) ∣ Algebra.norm ℤ z - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ a).mp (by rw [hmod, Int.cast_one])
  have hd : a ∣ (Algebra.norm ℤ z - 1).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdvd
  have hpos := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hle := (Nat.le_of_dvd hpos hd).trans (Int.natAbs_sub_le (Algebra.norm ℤ z) 1)
  exact (not_le_of_gt hlarge) hle

/-- Two approximating elements generate the same ideal when their valuations
agree. Taking the second congruent to one modulo a large integer forces that
ideal to be the unit ideal. -/
theorem valuation_eq_one_of_congruent_global_approximants (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) (hx₀ : x ≠ 0) (hx₁ : Valued.v x ≤ 1)
    (hap : HasCongruentGlobalApproximants w x) : Valued.v x = 1 := by
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx₁ hne
  have hxpos : 0 < Valued.v x := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hx₀)
  have htx : Valued.v (x * x) < Valued.v x := by
    rw [map_mul]
    exact mul_lt_of_lt_one_left hxpos hlt
  have hw_eq (k : E) (hk : Valued.v (algebraMap E (w.adicCompletion E) k - x) ≤ Valued.v (x * x)) :
      w.valuation E k = Valued.v x := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact Valuation.map_eq_of_sub_lt _ (hk.trans_lt htx)
  have exists_integral (a : ℕ) (ha : 0 < a) : ∃ k : Eˣ, ∃ z : 𝓞 E,
      algebraMap (𝓞 E) E z = (k : E) ∧ w.valuation E (k : E) = Valued.v x ∧
      ∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E (k : E) = 1 := by
    obtain ⟨k, hoff, hkw⟩ := hap a ha (x * x) (mul_ne_zero hx₀ hx₀)
    have hw := hw_eq (k : E) hkw
    have hv v (hv : v ≠ w) := valuation_eq_one_of_ray v a ha k (hoff v hv).1 (hoff v hv).2
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (k : E) (fun v => by
      by_cases h : v = w
      · subst v; exact hw.le.trans hx₁
      · exact (hv v h).le)
    exact ⟨k, z, hz, hw, fun v h => ⟨(hoff v h).1, hv v h⟩⟩
  obtain ⟨k₀, z₀, hz₀, hw₀, hoff₀⟩ := exists_integral 1 one_pos
  let B := (Algebra.norm ℤ z₀).natAbs + 1
  obtain ⟨a, ha, hwa⟩ := exists_large_nat_unit_at w B
  have ha₀ : 0 < a := Nat.zero_le B |>.trans_lt ha
  obtain ⟨k, z, hz, hw, hoff⟩ := exists_integral a ha₀
  obtain ⟨u, hu⟩ := exists_integerUnit_of_valuation_eq_one ((k : E) / k₀) (fun v => by
    rw [map_div₀]
    by_cases h : v = w
    · subst v; rw [hw, hw₀, div_self hxpos.ne']
    · rw [(hoff v h).2, (hoff₀ v h).2, div_one])
    (div_ne_zero k.ne_zero k₀.ne_zero)
  have hzu : z = (u : 𝓞 E) * z₀ := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, hz, hu, hz₀, div_mul_cancel₀ _ k₀.ne_zero]
  have hnorm : (Algebra.norm ℤ z).natAbs = (Algebra.norm ℤ z₀).natAbs := by
    rw [hzu, map_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.mp (u.isUnit.map _), one_mul]
  obtain ⟨y, hy⟩ := congruent_integer_of_valuations w a ha₀ hwa k z hz (fun v hv => (hoff v hv).1)
  have hN := integerNorm_eq_one_of_large_modulus a z (by rwa [hnorm])
    (by rw [hy]; exact integerNorm_eq_one_mod_nat a y)
  have hu : IsUnit z := by
    rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, Ideal.absNorm_span_singleton, hN]
    rfl
  have hmem : z ∈ w.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E z) < 1
    rwa [hz, hw]
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.valuation_eq_one_of_congruent_global_approximants
