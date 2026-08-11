import GaloisForLFunctions.RHTower.Sieve.MaynardGreedyGroupSelection
import GaloisForLFunctions.RHTower.Sieve.MaynardBoxFactorization
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Dyadic realization of the robust greedy group

Weights are exact logarithmic exponents `log_{T0}(2^q)`.  Therefore group mass is not a proxy:
the literal dyadic lower edge equals `T0` raised to that mass.  This file specializes the robust
packing to one selected Heath--Brown box and returns the literal subtype required by Huxley.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Exact exponent of a dyadic lower edge relative to height base `T0`. -/
def dyadicLogExponent (T0 : ℝ) (q : ℕ) : ℝ :=
  Real.logb T0 (((2 ^ q : ℕ) : ℝ))

/-- A dyadic edge is exactly the height base raised to its logarithmic exponent. -/
theorem rpow_dyadicLogExponent {T0 : ℝ} (hT0 : 1 < T0) (q : ℕ) :
    T0 ^ dyadicLogExponent T0 q = (((2 ^ q : ℕ) : ℝ)) := by
  exact Real.rpow_logb (by linarith) hT0.ne' (by positivity)

/-- Product form: group lower edge equals `T0` raised to sum of exact factor exponents. -/
theorem cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent
    {ι : Type*} [DecidableEq ι] {T0 : ℝ} (hT0 : 1 < T0)
    (q : ι → ℕ) (u : Finset ι) :
    (((∏ i ∈ u, 2 ^ q i : ℕ) : ℕ) : ℝ) =
      T0 ^ ∑ i ∈ u, dyadicLogExponent T0 (q i) := by
  rw [Real.rpow_sum_of_pos (by linarith)]
  push_cast
  apply Finset.prod_congr rfl
  intro i _hi
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (rpow_dyadicLogExponent hT0 (q i)).symm

/-- **Dyadic robust-group selection.**  The selected group has exact exponent in `[t,4t)`, exact
lower edge `T0^alpha`, and inherits the literal product threshold. -/
theorem exists_dyadic_robust_greedy_large_group
    {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (z : ι → ℂ) {T0 t e : ℝ}
    (hT0 : 1 < T0) (ht : 0 < t)
    (hshort : ∀ i, dyadicLogExponent T0 (q i) ≤ 2 * t)
    (htotal : t ≤ ∑ i, dyadicLogExponent T0 (q i))
    (hlarge : (groupedDyadicLower q : ℝ) ^ e ≤ ‖∏ i, z i‖) :
    ∃ u : Finset ι, u.Nonempty ∧
      let alpha := ∑ i ∈ u, dyadicLogExponent T0 (q i)
      t ≤ alpha ∧ alpha < 4 * t ∧ u.card ≤ Fintype.card ι ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) = T0 ^ alpha ∧
        ((groupedDyadicLower (fun i : {i // i ∈ u} => q i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, z i‖ := by
  classical
  have hlarge' : (∏ i ∈ (Finset.univ : Finset ι), (((2 ^ q i : ℕ) : ℝ))) ^ e ≤
      ‖∏ i ∈ (Finset.univ : Finset ι), z i‖ := by
    simpa [groupedDyadicLower] using hlarge
  obtain ⟨u, hune, _hus, hulower, huupper, hgroup⟩ :=
    exists_robust_greedy_large_group_subtype
      (fun i => dyadicLogExponent T0 (q i)) t (Finset.univ : Finset ι)
      ht (fun i _ => hshort i) htotal
      (fun i => (((2 ^ q i : ℕ) : ℝ))) z e (fun i _ => by positivity) hlarge'
  refine ⟨u, hune, hulower, huupper, Finset.card_le_univ u, ?_, ?_⟩
  · change (((∏ i : {i // i ∈ u}, 2 ^ q i : ℕ) : ℕ) : ℝ) =
      T0 ^ ∑ i ∈ u, dyadicLogExponent T0 (q i)
    rw [← Finset.prod_subtype u (fun _ => Iff.rfl) (fun i => 2 ^ q i)]
    exact cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT0 q u
  · simpa [groupedDyadicLower] using hgroup

/-- Literal one-box specialization, including the heterogeneous Möbius/zeta/log factor family. -/
theorem exists_heathBrown_box_dyadic_robust_group
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ)
    {T0 t e : ℝ} (hT0 : 1 < T0) (ht : 0 < t)
    (hshort : ∀ i : HeathBrownBoxFactorIndex k m,
      dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i) ≤ 2 * t)
    (htotal : t ≤ ∑ i : HeathBrownBoxFactorIndex k m,
      dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i))
    (s : ℂ)
    (hlarge :
      (groupedDyadicLower (heathBrownBoxFactorExponent a b q) : ℝ) ^ e ≤
        ‖heathBrownDyadicCoreProduct L X k m a b q s‖) :
    ∃ u : Finset (HeathBrownBoxFactorIndex k m), u.Nonempty ∧
      let alpha := ∑ i ∈ u,
        dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i)
      t ≤ alpha ∧ alpha < 4 * t ∧
        u.card ≤ Fintype.card (HeathBrownBoxFactorIndex k m) ∧
        ((groupedDyadicLower
          (fun i : {i // i ∈ u} => heathBrownBoxFactorExponent a b q i) : ℕ) : ℝ) =
            T0 ^ alpha ∧
        ((groupedDyadicLower
          (fun i : {i // i ∈ u} => heathBrownBoxFactorExponent a b q i) : ℕ) : ℝ) ^ e ≤
          ‖∏ i : {i // i ∈ u}, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
              (heathBrownBoxFactorExponent a b q i))) s‖ := by
  let z : HeathBrownBoxFactorIndex k m → ℂ := fun i =>
    LSeries (complexCoeff (arithmeticDyadicBlock
      (heathBrownFactorBase L X (heathBrownBoxFactorKind k m i))
      (heathBrownBoxFactorExponent a b q i))) s
  apply exists_dyadic_robust_greedy_large_group
    (heathBrownBoxFactorExponent a b q) z hT0 ht hshort htotal
  dsimp [z]
  rwa [heathBrownBoxFactorProduct_eq_core]

/-- At packet order `k=60`, every robust selected group still has width at most 120. -/
theorem card_selected_heathBrown_group_le_120
    {m : ℕ} (hm : m < 60) {u : Finset (HeathBrownBoxFactorIndex 60 m)} :
    u.card ≤ 120 := by
  calc
    u.card ≤ Fintype.card (HeathBrownBoxFactorIndex 60 m) := Finset.card_le_univ u
    _ = 2 * (60 - m) := card_heathBrownBoxFactorIndex hm
    _ ≤ 120 := by omega

end RHTower.Sieve
