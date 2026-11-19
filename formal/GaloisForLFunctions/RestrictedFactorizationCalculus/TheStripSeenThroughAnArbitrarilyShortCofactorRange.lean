import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSharpHeightOfARemovablePrimeHead

/-!
# The zero abscissa on an arbitrarily short power range of cofactors

The omitted head has exponent at most αΘ. Since α < 1, it cannot carry
the leading exponent Θ of the full reading. The cutoff may oscillate
and the weights on proper prime powers may change with every observation.
-/

noncomputable section
open Filter Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev interior (a : ℕ → ArithmeticFunction ℝ) (T : ℕ → ℕ) (X : ℕ) :=
  roughInteriorReading (a X) (logSquareCutoff X) X (T X)

private theorem full_as_terminal (a : ℕ → ArithmeticFunction ℝ) (X : ℕ) :
    roughCofactorReading (logSquareCutoff X) X (quotientReading (a X)) =
      terminalPrimeHead 1 a X := by
  simpa only [terminalPrimeHead,Real.rpow_one,Nat.floor_natCast] using
    rough_action_as_a_coefficient_prefix (logSquareCutoff X) X (a X)

private theorem transfer_interior {α s : ℝ} (ap : 0 < α) (sp : 0 < s)
    (head : α*RHTower.zetaZeroAbscissa < s) (a : ℕ → ArithmeticFunction ℝ) (T : ℕ → ℕ)
    (height : ∀ᶠ X : ℕ in atTop, (T X : ℝ) ≤ (X : ℝ)^α)
    (dom : ∀ X q, |a X q| ≤ vonMangoldt q)
    (fix : ∀ X p, p.Prime → a X p = roughMangoldtWeight (logSquareCutoff X) p) :
    PrefixPower s (interior a T) ↔ PrefixPower s (terminalPrimeHead 1 a) := by
  obtain ⟨K,hK,bound⟩ := shrinking_the_cofactor_range_for_prime_readings ap head
  have small : ∀ᶠ X : ℕ in atTop,
      |terminalPrimeHead 1 a X - interior a T X| ≤ K*(X:ℝ)^s := by
    filter_upwards [bound,height] with X h hx
    rw [←full_as_terminal]
    exact h _ hx _ (dom X) (fix X)
  constructor <;> rintro ⟨D,_,hd⟩
  · apply prefixPower_of_eventual (C := K+D) (by simp [terminalPrimeHead,quotientReading]) sp
    filter_upwards [small] with X hx
    have tri := abs_add_le (terminalPrimeHead 1 a X-interior a T X) (interior a T X)
    rw [sub_add_cancel] at tri
    exact tri.trans ((add_le_add hx (hd X)).trans_eq (add_mul ..).symm)
  · apply prefixPower_of_eventual (C := K+D) (by simp [interior,roughInteriorReading]) sp
    filter_upwards [small] with X hx
    have tri := abs_sub (terminalPrimeHead 1 a X) (terminalPrimeHead 1 a X-interior a T X)
    rw [sub_sub_cancel] at tri
    linarith only [tri,hx,hd X]

/-- A reading at any eventually sublinear power cutoff recovers the full
zero abscissa, even with independent signed changes on proper prime powers. -/
theorem adaptive_cofactor_interior_detects_the_strip {α b : ℝ}
    (ap : 0 < α) (a1 : α < 1) (hb : 1/2 ≤ b)
    (a : ℕ → ArithmeticFunction ℝ) (T : ℕ → ℕ)
    (height : ∀ᶠ X : ℕ in atTop, (T X : ℝ) ≤ (X:ℝ)^α)
    (dom : ∀ X q, |a X q| ≤ vonMangoldt q)
    (fix : ∀ X p, p.Prime → a X p = roughMangoldtWeight (logSquareCutoff X) p) :
    (∀ ε : ℝ, 0 < ε → PrefixPower (b+ε) (fun X =>
      roughInteriorReading (a X) (logSquareCutoff X) X (T X))) ↔ RHTower.zetaZeroAbscissa ≤ b := by
  let θ := RHTower.zetaZeroAbscissa
  have θp : 0 < θ := (by norm_num : (0:ℝ)<1/2).trans_le RHTower.half_le_zetaZeroAbscissa
  have drop : α*θ < θ := (mul_lt_mul_of_pos_right a1 θp).trans_eq (one_mul _)
  have full (c : ℝ) (hc : 1/2 ≤ c) :
      (∀ ε : ℝ, 0 < ε → PrefixPower (c+ε) (terminalPrimeHead 1 a)) ↔ θ ≤ c := by
    simpa only [one_mul] using one_perturbed_terminal_head_detects_the_strip
      (α := 1) zero_lt_one le_rfl hc a dom fix
  constructor
  · intro h
    by_contra! hθ
    let c := max b (α*θ)
    have bc : b ≤ c := le_max_left _ _
    have ac : α*θ ≤ c := le_max_right _ _
    have cc := (full c (hb.trans bc)).mp (fun ε ep => by
      have cs : c < c+ε := lt_add_of_pos_right _ ep
      have es := transfer_interior ap ((by norm_num : (0:ℝ)<1/2).trans_le
        ((hb.trans bc).trans cs.le)) (ac.trans_lt cs) a T height dom fix
      have e : 0 < c+ε-b := sub_pos.mpr (bc.trans_lt cs)
      have hi := h _ e
      rw [show b+(c+ε-b)=c+ε by ring] at hi
      exact es.mp hi)
    exact (max_lt hθ drop).not_ge cc
  · intro h ε ep
    have bs := lt_add_of_pos_right b ep
    exact (transfer_interior ap ((by norm_num : (0:ℝ)<1/2).trans_le (hb.trans bs.le))
      (drop.trans (h.trans_lt bs)) a T height dom fix).mpr ((full b hb).mpr h ε ep)

/-- For every fixed positive retained cofactor exponent 1−α, the sharp
growth criterion is unchanged, including cutoffs arbitrarily close to X. -/
theorem prime_power_interior_detects_the_strip {α b : ℝ}
    (ap : 0 < α) (a1 : α < 1) (hb : 1/2 ≤ b) :
    (∀ ε : ℝ, 0 < ε → PrefixPower (b+ε) (primePowerInteriorAtExponent α)) ↔
      RHTower.zetaZeroAbscissa ≤ b :=
  adaptive_cofactor_interior_detects_the_strip ap a1 hb _ _
    (.of_forall fun X => Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) α))
    (fun X => mangoldt_dominated (logSquareCutoff X)) (fun _ _ _ => rfl)

/-- At the endpoint α=1 the interior vanishes at every observation. -/
theorem prime_power_interior_at_one (X : ℕ) : primePowerInteriorAtExponent 1 X = 0 := by
  simp [primePowerInteriorAtExponent,roughInteriorReading,Nat.div_eq_of_lt (Nat.lt_succ_self X)]

#print axioms adaptive_cofactor_interior_detects_the_strip
#print axioms prime_power_interior_detects_the_strip
#print axioms prime_power_interior_at_one

end GaloisForLFunctions.RestrictedFactorizationCalculus
