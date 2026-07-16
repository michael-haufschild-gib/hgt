import GaloisForLFunctions.HTGeometry.RationalShiftOrbitPole
import GaloisForLFunctions.HTGeometry.RationalShiftHypertranscendence

/-!
# Rational shift increments of separated Gamma orbits

The logarithmic derivative of a signed common-scale Gamma product translates by a rational
function.  This module proves the exact multi-orbit discrete-residue statement required by the
parameterized Hölder eliminator: if one separated orbit has nonzero charge, no nonzero constant
linear combination of the complete rational increment jet can be a rational shift coboundary.
-/

namespace GaloisForLFunctions

noncomputable section

open Polynomial

def gammaOrbitFactor {d : ℕ} (b : Fin d → ℂ) (c : Fin d) : Polynomial ℂ :=
  Polynomial.X + Polynomial.C (b c)

def gammaOrbitIncrement {d : ℕ} (b M : Fin d → ℂ) (j : ℕ) : RatFunc ℂ :=
  ∑ c : Fin d,
    RatFunc.C (M c * ((-1 : ℂ) ^ j * (j.factorial : ℂ))) /
      (RatFunc.X + RatFunc.C (b c)) ^ (j + 1)

def gammaOrbitCommonDenominator {d : ℕ} (b : Fin d → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∏ c : Fin d, gammaOrbitFactor b c ^ (N + 1)

def gammaOrbitCommonNumerator {d : ℕ} (b M : Fin d → ℂ)
    (N : ℕ) (delta : Fin (N + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (N + 1), ∑ c : Fin d,
    Polynomial.C (delta j * (M c * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ)))) *
      gammaOrbitFactor b c ^ (N - (j : ℕ)) *
        ∏ c' ∈ (Finset.univ.erase c), gammaOrbitFactor b c' ^ (N + 1)

theorem gammaOrbitIncrement_commonDenominator {d : ℕ} (b M : Fin d → ℂ)
    (N : ℕ) (delta : Fin (N + 1) → ℂ) :
    ∑ j : Fin (N + 1),
        algebraMap ℂ (RatFunc ℂ) (delta j) * gammaOrbitIncrement b M (j : ℕ) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (gammaOrbitCommonNumerator b M N delta) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (gammaOrbitCommonDenominator b N) := by
  classical
  rw [gammaOrbitCommonNumerator, gammaOrbitCommonDenominator, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gammaOrbitIncrement, Finset.mul_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_mul, map_pow, map_prod]
  simp only [map_mul, map_pow, map_prod, gammaOrbitFactor, map_add,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hfac : RatFunc.X + RatFunc.C (b c) ≠ 0 := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (b c))
  have hsplit :
      (∏ x : Fin d, (RatFunc.X + RatFunc.C (b x)) ^ (N + 1)) =
        (RatFunc.X + RatFunc.C (b c)) ^ (N + 1) *
          ∏ x ∈ Finset.univ.erase c,
            (RatFunc.X + RatFunc.C (b x)) ^ (N + 1) := by
    exact (Finset.mul_prod_erase Finset.univ
      (fun x : Fin d => (RatFunc.X + RatFunc.C (b x)) ^ (N + 1))
      (Finset.mem_univ c)).symm
  have hrest :
      (∏ x ∈ Finset.univ.erase c,
        (RatFunc.X + RatFunc.C (b x)) ^ (N + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x _
    apply pow_ne_zero
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (b x))
  rw [hsplit]
  have hj : (j : ℕ) + 1 + (N - (j : ℕ)) = N + 1 := by omega
  rw [show (RatFunc.X + RatFunc.C (b c)) ^ (N + 1) =
      (RatFunc.X + RatFunc.C (b c)) ^ ((j : ℕ) + 1) *
        (RatFunc.X + RatFunc.C (b c)) ^ (N - (j : ℕ)) by rw [← pow_add, hj]]
  field_simp [hfac, hrest]
  simp [RatFunc.algebraMap_eq_C, mul_comm, mul_left_comm]

theorem gammaOrbitCommonDenominator_ne_zero {d : ℕ} (b : Fin d → ℂ) (N : ℕ) :
    gammaOrbitCommonDenominator b N ≠ 0 := by
  classical
  rw [gammaOrbitCommonDenominator, Finset.prod_ne_zero_iff]
  intro c _
  exact pow_ne_zero _ (Polynomial.X_add_C_ne_zero (b c))

theorem gammaOrbitCommonDenominator_orbit_zero_iff
    {d : ℕ} (b : Fin d → ℂ) (c0 : Fin d)
    (hsep : ∀ c, c ≠ c0 → ∀ n : ℤ, b c - b c0 ≠ (n : ℂ))
    (N : ℕ) (n : ℤ) :
    (gammaOrbitCommonDenominator b N).eval (-b c0 + (n : ℂ)) = 0 ↔ n = 0 := by
  classical
  rw [gammaOrbitCommonDenominator, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨c, _, hc⟩
    simp only [Polynomial.eval_pow, gammaOrbitFactor, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, pow_eq_zero_iff (by omega : N + 1 ≠ 0)] at hc
    by_cases hcc : c = c0
    · subst c
      have hcast : (n : ℂ) = 0 := by linear_combination hc
      exact Int.cast_injective (by simpa using hcast)
    · exfalso
      apply hsep c hcc (-n)
      push_cast
      linear_combination hc
  · intro hn
    subst n
    refine ⟨c0, Finset.mem_univ c0, ?_⟩
    simp [gammaOrbitFactor]

theorem gammaOrbitCommonNumerator_eval_center_ne_zero
    {d : ℕ} (b M : Fin d → ℂ) (c0 : Fin d) (hM : M c0 ≠ 0)
    (hsep : ∀ c, c ≠ c0 → ∀ n : ℤ, b c - b c0 ≠ (n : ℂ))
    (N : ℕ) (delta : Fin (N + 1) → ℂ)
    (hdelta : delta ⟨N, Nat.lt_succ_self N⟩ ≠ 0) :
    (gammaOrbitCommonNumerator b M N delta).eval (-b c0) ≠ 0 := by
  classical
  rw [gammaOrbitCommonNumerator]
  change (Polynomial.evalRingHom (-b c0))
      (∑ j : Fin (N + 1), ∑ c : Fin d,
        Polynomial.C
            (delta j * (M c * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ)))) *
          gammaOrbitFactor b c ^ (N - (j : ℕ)) *
            ∏ c' ∈ Finset.univ.erase c, gammaOrbitFactor b c' ^ (N + 1)) ≠ 0
  rw [map_sum]
  have hterm : ∀ j : Fin (N + 1),
      (Polynomial.evalRingHom (-b c0))
        (∑ c : Fin d,
          Polynomial.C
              (delta j * (M c * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ)))) *
            gammaOrbitFactor b c ^ (N - (j : ℕ)) *
              ∏ c' ∈ Finset.univ.erase c, gammaOrbitFactor b c' ^ (N + 1)) =
        if (j : ℕ) = N then
          delta j * (M c0 * ((-1 : ℂ) ^ N * (N.factorial : ℂ))) *
            ∏ c' ∈ Finset.univ.erase c0, (b c' - b c0) ^ (N + 1)
        else 0 := by
    intro j
    rw [map_sum]
    change (∑ c : Fin d,
        (Polynomial.C
              (delta j * (M c * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ)))) *
            gammaOrbitFactor b c ^ (N - (j : ℕ)) *
              ∏ c' ∈ Finset.univ.erase c, gammaOrbitFactor b c' ^ (N + 1)).eval
          (-b c0)) = _
    have hprodZero : ∀ c : Fin d, c ≠ c0 →
        (∏ c' ∈ Finset.univ.erase c, (-b c0 + b c') ^ (N + 1)) = 0 := by
      intro c hcc
      rw [Finset.prod_eq_zero_iff]
      refine ⟨c0, by simp [Ne.symm hcc], ?_⟩
      rw [show -b c0 + b c0 = 0 by ring, zero_pow (by omega : N + 1 ≠ 0)]
    by_cases hj : (j : ℕ) = N
    · rw [if_pos hj]
      have hjeq : j = ⟨N, Nat.lt_succ_self N⟩ := Fin.ext hj
      subst j
      rw [Finset.sum_eq_single c0]
      · simp [Polynomial.eval_prod, gammaOrbitFactor, sub_eq_add_neg, add_comm]
      · intro c _ hcc
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_prod, gammaOrbitFactor, Polynomial.eval_add, Polynomial.eval_X]
        rw [hprodZero c hcc, mul_zero]
      · intro hc
        exact (hc (Finset.mem_univ c0)).elim
    · rw [if_neg hj]
      refine Finset.sum_eq_zero fun c _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_prod, gammaOrbitFactor, Polynomial.eval_add, Polynomial.eval_X]
      by_cases hcc : c = c0
      · subst c
        have hpos : 0 < N - (j : ℕ) := by omega
        rw [show -b c0 + b c0 = 0 by ring, zero_pow hpos.ne']
        simp
      · rw [hprodZero c hcc, mul_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_eq_single ⟨N, Nat.lt_succ_self N⟩]
  · simp only [if_true]
    apply mul_ne_zero
    · exact mul_ne_zero hdelta (mul_ne_zero hM
        (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero N)))
    · rw [Finset.prod_ne_zero_iff]
      intro c hc
      have hcc : c ≠ c0 := Finset.ne_of_mem_erase hc
      exact pow_ne_zero _ (by simpa using hsep c hcc 0)
  · intro j _ hj
    rw [if_neg]
    exact fun hval => hj (Fin.ext hval)
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Constant linear combinations of a separated nonzero-charge orbit increment are rationally
shift-summable only when every coefficient vanishes. -/
theorem ratShift_sub_gammaOrbitIncrement_combination
    {d : ℕ} (b M : Fin d → ℂ) (c0 : Fin d) (hM : M c0 ≠ 0)
    (hsep : ∀ c, c ≠ c0 → ∀ n : ℤ, b c - b c0 ≠ (n : ℂ))
    {m : ℕ} {w : RatFunc ℂ} {delta : Fin m → ℂ}
    (h : ratShift w - w =
      ∑ j : Fin m,
        algebraMap ℂ (RatFunc ℂ) (delta j) * gammaOrbitIncrement b M (j : ℕ)) :
    ∀ j, delta j = 0 := by
  induction m with
  | zero => exact fun j => absurd j.isLt (by omega)
  | succ N ih =>
      have htop : delta ⟨N, Nat.lt_succ_self N⟩ = 0 := by
        by_contra hdelta
        have hfrac := gammaOrbitIncrement_commonDenominator b M N delta
        apply ratShift_sub_ne_of_single_orbit_pole (-b c0)
          (gammaOrbitCommonDenominator_ne_zero b N)
          (gammaOrbitCommonNumerator_eval_center_ne_zero b M c0 hM hsep N delta hdelta)
          (fun n => by simpa [add_comm] using
            gammaOrbitCommonDenominator_orbit_zero_iff b c0 hsep N n)
          w
        rw [h, hfrac]
      let delta' : Fin N → ℂ := fun j => delta j.castSucc
      have hlast : delta (Fin.last N) = 0 := by simpa using htop
      have hlower : ratShift w - w =
          ∑ j : Fin N,
            algebraMap ℂ (RatFunc ℂ) (delta' j) *
              gammaOrbitIncrement b M (j : ℕ) := by
        rw [h]
        rw [Fin.sum_univ_castSucc]
        simp [delta', hlast]
      have hz := ih (delta := delta') hlower
      intro j
      by_cases hj : (j : ℕ) = N
      · have hjeq : j = Fin.last N := Fin.ext (by simpa using hj)
        simpa [hjeq] using htop
      · have hjlt : (j : ℕ) < N := by omega
        let k : Fin N := ⟨j, hjlt⟩
        simpa [delta', k] using hz k

end

end GaloisForLFunctions
