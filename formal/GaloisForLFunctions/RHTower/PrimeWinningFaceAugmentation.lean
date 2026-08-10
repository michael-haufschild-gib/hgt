import GaloisForLFunctions.RHTower.PrimeWinningFaceSeries
import GaloisForLFunctions.RHTower.HighExponentShellZeroFree

/-!
# Euler augmentation of the prime-winning faces

The alternating sum of face transition products over all nonempty subsets of a finite prime set is
the complementary product `1 - ∏ (1 - R_{p,m})`, and each complementary factor is again a ratio of
geometric factors, `1 - R_{p,m}(s) = (1 - p^{-ms})/(1 - p^{-(m+1)s})`.  Over all primes the
complementary product is `ζ((m+1)s)/ζ(ms)`, so the augmentation of the prime-winning faces is
exactly the shell multiplier `ζ((m+1)s)⁻¹ - ζ(ms)⁻¹`.
-/

open Complex

noncomputable section

namespace RHTower

/-! ## The complementary transition factor -/

/-- The complementary transition factor is again a ratio of geometric factors. -/
theorem one_sub_faceTransitionUnit {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re)
    (p : Nat.Primes) :
    1 - faceTransitionUnit p m s =
      (1 - ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))) /
        (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s))) := by
  have hden : (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s))) ≠ 0 := by
    refine one_sub_primeCpow_neg_ne_zero ?_ p
    have := one_lt_re_succ_mul hm hs
    linarith
  rw [faceTransitionUnit, primeCpow_neg_natMul, primeCpow_neg_succ_mul]
  rw [primeCpow_neg_succ_mul] at hden
  field_simp
  ring

/-! ## Finite augmentation -/

/-- The alternating face sum over all nonempty subsets of a finite prime set is the complementary
product. -/
theorem sum_alternating_prod_faceTransitionUnit (S : Finset Nat.Primes) (m : ℕ) (s : ℂ) :
    ∑ t ∈ S.powerset.erase ∅,
        (-1 : ℂ) ^ (t.card + 1) * ∏ p ∈ t, faceTransitionUnit p m s
      = 1 - ∏ p ∈ S, (1 - faceTransitionUnit p m s) := by
  classical
  have hkey := Finset.prod_add (fun p => -faceTransitionUnit p m s)
    (fun _ : Nat.Primes => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one, neg_add_eq_sub, Finset.prod_neg] at hkey
  have hsplit :
      ∑ t ∈ S.powerset.erase ∅, (-1 : ℂ) ^ t.card * ∏ p ∈ t, faceTransitionUnit p m s
        + (-1 : ℂ) ^ (∅ : Finset Nat.Primes).card * ∏ p ∈ (∅ : Finset Nat.Primes),
            faceTransitionUnit p m s
        = ∑ t ∈ S.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, faceTransitionUnit p m s :=
    Finset.sum_erase_add _ _ (Finset.empty_mem_powerset S)
  simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one] at hsplit
  have hneg : ∀ t : Finset Nat.Primes,
      (-1 : ℂ) ^ (t.card + 1) * ∏ p ∈ t, faceTransitionUnit p m s
        = -((-1 : ℂ) ^ t.card * ∏ p ∈ t, faceTransitionUnit p m s) := by
    intro t
    rw [pow_succ]
    ring
  rw [Finset.sum_congr rfl fun t _ => hneg t, Finset.sum_neg_distrib, hkey, ← hsplit]
  ring

/-- **Finite face-unit augmentation.**  The alternating sum of face units over the nonempty subsets
of a finite prime set is the complementary product against the doubled zeta factor. -/
theorem sum_alternating_faceUnit (S : Finset Nat.Primes) (m : ℕ) (s : ℂ) :
    ∑ t ∈ S.powerset.erase ∅, (-1 : ℂ) ^ (t.card + 1) * faceUnit t m s
      = (riemannZeta (((m : ℂ) + 1) * s))⁻¹ *
          (1 - ∏ p ∈ S, (1 - faceTransitionUnit p m s)) := by
  classical
  rw [← sum_alternating_prod_faceTransitionUnit S m s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [faceUnit]
  ring

/-! ## The complementary Euler product over all primes -/

theorem summable_norm_primeCpow_neg {w : ℂ} (hw : 1 < w.re) :
    Summable fun p : Nat.Primes => ‖((p : ℕ) : ℂ) ^ (-w)‖ := by
  have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ w.re := Real.summable_one_div_nat_rpow.mpr hw
  refine (h.subtype Nat.Prime).congr fun p => ?_
  show 1 / ((p : ℕ) : ℝ) ^ w.re = ‖((p : ℕ) : ℂ) ^ (-w)‖
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos, neg_re,
    Real.rpow_neg (Nat.cast_nonneg _), one_div]

theorem multipliable_one_sub_primeCpow_neg {w : ℂ} (hw : 1 < w.re) :
    Multipliable fun p : Nat.Primes => 1 - ((p : ℕ) : ℂ) ^ (-w) := by
  have h : Multipliable fun p : Nat.Primes => 1 + -(((p : ℕ) : ℂ) ^ (-w)) := by
    refine Complex.multipliable_one_add_of_summable (Summable.of_norm ?_)
    simpa using summable_norm_primeCpow_neg hw
  simpa [sub_eq_add_neg] using h

/-- **The reciprocal zeta Euler product.**  On the Euler half-plane the product of the reciprocal
local factors converges to `ζ(w)⁻¹`. -/
theorem hasProd_one_sub_primeCpow_neg {w : ℂ} (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes => 1 - ((p : ℕ) : ℂ) ^ (-w)) (riemannZeta w)⁻¹ := by
  obtain ⟨M, hM⟩ := multipliable_one_sub_primeCpow_neg hw
  have hcomb := hM.mul (riemannZeta_eulerProduct_hasProd hw)
  have hone : (fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℂ) ^ (-w)) * (1 - ((p : ℕ) : ℂ) ^ (-w))⁻¹)
      = fun _ : Nat.Primes => (1 : ℂ) := by
    funext p
    exact mul_inv_cancel₀ (one_sub_primeCpow_neg_ne_zero (by linarith) p)
  rw [hone] at hcomb
  have hval : M * riemannZeta w = 1 := hcomb.unique hasProd_one
  have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw
  have hM' : M = 1 / riemannZeta w := eq_div_of_mul_eq hζ hval
  rw [one_div] at hM'
  exact hM' ▸ hM

theorem one_lt_re_natMul {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re) : 1 < (((m : ℂ)) * s).re := by
  have hcast : (((m : ℂ)) * s).re = (m : ℝ) * s.re := by
    simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  rw [hcast]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- **The complementary face product.**  Over all primes the complementary transition factors
multiply to the zeta quotient. -/
theorem hasProd_one_sub_faceTransitionUnit {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1 - faceTransitionUnit p m s)
      (riemannZeta (((m : ℂ) + 1) * s) / riemannZeta ((m : ℂ) * s)) := by
  have hA := hasProd_one_sub_primeCpow_neg (one_lt_re_natMul hm hs)
  have hB := riemannZeta_eulerProduct_hasProd (one_lt_re_succ_mul_of_one_lt m hs)
  have hcomb := hA.mul hB
  have hfam : (fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))) *
        (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹)
      = fun p : Nat.Primes => 1 - faceTransitionUnit p m s := by
    funext p
    rw [one_sub_faceTransitionUnit hm (by linarith) p, div_eq_mul_inv]
  rw [hfam] at hcomb
  rw [div_eq_inv_mul]
  exact hcomb

/-- **The shell multiplier is the Euler augmentation of the prime-winning faces.**  The
complementary product of all face transition factors, corrected by the doubled zeta factor, is the
high-exponent shell multiplier. -/
theorem faceAugmentation_eq_shellMultiplier {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta (((m : ℂ) + 1) * s))⁻¹ *
        (1 - ∏' p : Nat.Primes, (1 - faceTransitionUnit p m s)) = shellMultiplier m s := by
  have hζ2 : riemannZeta (((m : ℂ) + 1) * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (one_lt_re_succ_mul_of_one_lt m hs)
  have hζ1 : riemannZeta ((m : ℂ) * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (one_lt_re_natMul hm hs)
  rw [(hasProd_one_sub_faceTransitionUnit hm hs).tprod_eq, shellMultiplier]
  field_simp

end RHTower
