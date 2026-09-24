import GaloisForLFunctions.RHTower.EstermannKloostermanTwist
import GaloisForLFunctions.RHTower.EstermannExponentialMellin
import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# Square-root cancellation in the modulus aspect of the Estermann family

The inverse twist turns the family `{D(s, a/q)}_{a ∈ (ZMod q)ˣ}` into a divisor series weighted by
complete Kloosterman sums.  For a prime modulus and a nonzero second frequency Weil's bound
`|S(m,n;p)| ≤ 2√p` holds for **every** first frequency: when `m` is a unit the sum reduces to the
normalisation `Σ_{x ≠ 0} ψ(x + mn/x)` covered by the bound, and when `m = 0` the sum collapses to
the Ramanujan value `−1`.  Hence

`‖∑_{a ∈ (ZMod p)ˣ} e(a⁻¹ b/p) D(s, a/p)‖ ≤ 2√p · ∑_N d(N) N^{-σ}`,

whereas the trivial estimate, which uses only `|S(m,n;p)| ≤ φ(p)`, gives `(p−1) ∑_N d(N)N^{-σ}`.
The twist average of `p−1` functions each of size `≍ 1` is therefore of size `≍ √p`, not `≍ p`:
the modulus aspect of the family really does cancel, and the saving is exactly the square root of
the number of terms.
-/

open Complex Finset
open RHTower.Sieve

namespace RHTower

noncomputable section

/-- A sum over the units of a finite field is the sum over the field with the zero term dropped. -/
theorem sum_units_eq_sum_ite {F : Type*} [Field F] [Fintype F] [DecidableEq F] (g : F → ℂ) :
    ∑ x : Fˣ, g (x : F) = ∑ x : F, if x = 0 then (0 : ℂ) else g x := by
  classical
  have h0 : (if (0 : F) = 0 then (0 : ℂ) else g 0) = 0 := by simp
  rw [← Finset.sum_erase (Finset.univ : Finset F) h0]
  have hcong : ∑ x ∈ (Finset.univ : Finset F).erase 0, (if x = 0 then (0 : ℂ) else g x)
      = ∑ x ∈ (Finset.univ : Finset F).erase 0, g x :=
    Finset.sum_congr rfl (fun x hx => if_neg (Finset.ne_of_mem_erase hx))
  rw [hcong, Finset.sum_subtype (s := (Finset.univ : Finset F).erase 0)
      (p := fun x : F => x ≠ 0) (fun x => by simp) g]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun x => rfl)

/-- The complete sum of a primitive additive character over the units of a prime field. -/
theorem sum_units_stdAddChar (p : ℕ) [Fact p.Prime] :
    ∑ x : (ZMod p)ˣ, (ZMod.stdAddChar ((x : ZMod p)) : ℂ) = -1 := by
  classical
  have hzero : ∑ x : ZMod p, (ZMod.stdAddChar (N := p) x : ℂ) = 0 := by
    have h1 := ZMod.isPrimitive_stdAddChar p
    have h2 := h1 (one_ne_zero (α := ZMod p))
    rw [AddChar.mulShift_one] at h2
    exact AddChar.sum_eq_zero_of_ne_one h2
  have hsub : ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, (ZMod.stdAddChar x : ℂ)
      = ∑ x : ZMod p, (ZMod.stdAddChar x : ℂ) - (ZMod.stdAddChar (0 : ZMod p) : ℂ) :=
    Finset.sum_erase_eq_sub (Finset.mem_univ 0)
  have heq : ∑ x : (ZMod p)ˣ, (ZMod.stdAddChar ((x : ZMod p)) : ℂ)
      = ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, (ZMod.stdAddChar x : ℂ) := by
    rw [Finset.sum_subtype (s := (Finset.univ : Finset (ZMod p)).erase 0)
      (p := fun x : ZMod p => x ≠ 0) (fun x => by simp) (fun x => (ZMod.stdAddChar x : ℂ))]
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun x => rfl)
  rw [heq, hsub, hzero, AddChar.map_zero_eq_one]
  ring

/-- The classical Kloosterman sum at first frequency one is the normalisation `Σ_{x ≠ 0} ψ(x + n/x)`
in which Weil's bound is stated. -/
theorem kloostermanSum_one_eq_kloosterman (p : ℕ) [Fact p.Prime] (n : ZMod p) :
    kloostermanSum p 1 n
      = GaloisForLFunctions.RHTower.WeilKloosterman.kloosterman (ZMod.stdAddChar (N := p)) n := by
  classical
  rw [kloostermanSum, GaloisForLFunctions.RHTower.WeilKloosterman.kloosterman,
    ← sum_units_eq_sum_ite (fun x : ZMod p => (ZMod.stdAddChar (x + n / x) : ℂ))]
  refine Fintype.sum_congr _ _ (fun x => ?_)
  have harg : (1 : ZMod p) * (x : ZMod p) + n * ((x⁻¹ : (ZMod p)ˣ) : ZMod p)
      = (x : ZMod p) + n / (x : ZMod p) := by
    rw [one_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  rw [kloostermanPhase, harg]

/-- At zero first frequency the complete sum is the Ramanujan value `−1`. -/
theorem kloostermanSum_zero_left (p : ℕ) [Fact p.Prime] {n : ZMod p} (hn : n ≠ 0) :
    kloostermanSum p 0 n = -1 := by
  classical
  have hcomm : kloostermanSum p 0 n = kloostermanSum p n 0 := kloostermanSum_comm p 0 n
  have hunit : kloostermanSum p n (0 : ZMod p) = kloostermanSum p 1 (0 : ZMod p) := by
    have h := kloostermanSum_unit_left p (Units.mk0 n hn) (0 : ZMod p)
    simpa using h
  have hval : kloostermanSum p 1 (0 : ZMod p)
      = ∑ x : (ZMod p)ˣ, (ZMod.stdAddChar ((x : ZMod p)) : ℂ) := by
    rw [kloostermanSum]
    refine Fintype.sum_congr _ _ (fun x => ?_)
    have harg : (1 : ZMod p) * (x : ZMod p) + (0 : ZMod p) * ((x⁻¹ : (ZMod p)ˣ) : ZMod p)
        = (x : ZMod p) := by ring
    rw [kloostermanPhase, harg]
  rw [hcomm, hunit, hval, sum_units_stdAddChar]

/-- **Weil's bound in the classical normalisation.**  For an odd prime modulus and a nonzero second
frequency, every complete Kloosterman sum is at most `2√p`. -/
theorem norm_kloostermanSum_le_weil (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (m : ZMod p) {n : ZMod p} (hn : n ≠ 0) :
    ‖kloostermanSum p m n‖ ≤ 2 * Real.sqrt p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt p := by
    have := Real.sqrt_le_sqrt hp1
    rwa [Real.sqrt_one] at this
  rcases eq_or_ne m 0 with hm | hm
  · subst hm
    rw [kloostermanSum_zero_left p hn]
    rw [norm_neg, norm_one]
    linarith
  · have hmu : kloostermanSum p m n = kloostermanSum p 1 (m * n) := by
      have h := kloostermanSum_unit_left p (Units.mk0 m hm) n
      simpa using h
    rw [hmu, kloostermanSum_one_eq_kloosterman]
    exact GaloisForLFunctions.RHTower.WeilKloosterman.kloosterman_weil_bound hp2 _
      (ZMod.isPrimitive_stdAddChar p) (mul_ne_zero hm hn)

/-- The divisor mass right of the abscissa, `∑_N d(N) N^{-σ}`. -/
def divisorMass (σ : ℝ) : ℝ := ∑' N : ℕ, (N.divisors.card : ℝ) * (N : ℝ) ^ (-σ)

theorem divisorMass_nonneg (σ : ℝ) : 0 ≤ divisorMass σ :=
  tsum_nonneg (fun N => by positivity)

/-- **The inverse twist inherits any uniform bound on the Kloosterman coefficients.** -/
theorem norm_estermann_invTwist_le_of_bound (q : ℕ) [NeZero q] (b : ZMod q) {B : ℝ}
    (hB : ∀ m : ZMod q, ‖kloostermanSum q m b‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    ‖∑ a : (ZMod q)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
        estermannZeta q ((a : ZMod q)) s‖ ≤ B * divisorMass s.re := by
  classical
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hsum := hasSum_kloosterman_estermannZeta q b hs
  set f : ℕ → ℂ := fun N =>
    (N.divisors.card : ℂ) * (kloostermanSum q (N : ZMod q) b / (N : ℂ) ^ s) with hf
  have hmaj : ∀ N : ℕ, ‖f N‖ ≤ B * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re)) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [hf]
    · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hnorm : ‖(N : ℂ) ^ s‖ = (N : ℝ) ^ s.re := Complex.norm_natCast_cpow_of_pos hN _
      have hpos : (0 : ℝ) < (N : ℝ) ^ s.re := Real.rpow_pos_of_pos hNpos _
      have hd0 : (0 : ℝ) ≤ (N.divisors.card : ℝ) := Nat.cast_nonneg _
      rw [hf]
      simp only
      rw [norm_mul, norm_div, hnorm, Complex.norm_natCast,
        Real.rpow_neg hNpos.le, div_eq_mul_inv]
      have hinv : (0 : ℝ) ≤ ((N : ℝ) ^ s.re)⁻¹ := by positivity
      have key : (N.divisors.card : ℝ) *
          (‖kloostermanSum q (N : ZMod q) b‖ * ((N : ℝ) ^ s.re)⁻¹)
          ≤ (N.divisors.card : ℝ) * (B * ((N : ℝ) ^ s.re)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hB ((N : ZMod q))) hinv) hd0
      calc (N.divisors.card : ℝ) *
            (‖kloostermanSum q (N : ZMod q) b‖ * ((N : ℝ) ^ s.re)⁻¹)
          ≤ (N.divisors.card : ℝ) * (B * ((N : ℝ) ^ s.re)⁻¹) := key
        _ = B * ((N.divisors.card : ℝ) * ((N : ℝ) ^ s.re)⁻¹) := by ring
  have hmajsum : Summable
      (fun N : ℕ => B * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re))) :=
    (summable_divisorCount_rpow hs).mul_left B
  have hfsum : Summable (fun N : ℕ => ‖f N‖) :=
    Summable.of_nonneg_of_le (fun N => norm_nonneg _) hmaj hmajsum
  rw [← hsum.tsum_eq]
  calc ‖∑' N : ℕ, f N‖ ≤ ∑' N : ℕ, ‖f N‖ := norm_tsum_le_tsum_norm hfsum
    _ ≤ ∑' N : ℕ, B * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re)) :=
        Summable.tsum_le_tsum hmaj hfsum hmajsum
    _ = B * divisorMass s.re := by rw [divisorMass, tsum_mul_left]

/-- **The trivial bound on the inverse twist**: `φ(q)` terms, each of size at most the divisor
mass. -/
theorem norm_estermann_invTwist_trivial_le (q : ℕ) [NeZero q] (b : ZMod q) {s : ℂ}
    (hs : 1 < s.re) :
    ‖∑ a : (ZMod q)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod q)ˣ) : ZMod q) * b) : ℂ) *
        estermannZeta q ((a : ZMod q)) s‖ ≤ (Nat.totient q : ℝ) * divisorMass s.re :=
  norm_estermann_invTwist_le_of_bound q b (fun m => norm_kloostermanSum_le_totient q m b) hs

/-- **The modulus-aspect saving.**  For an odd prime modulus and a nonzero frequency the inverse
twist of the Estermann family is bounded by `2√p` times the divisor mass. -/
theorem norm_estermann_invTwist_le_weil (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    ‖∑ a : (ZMod p)ˣ, (ZMod.stdAddChar (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * b) : ℂ) *
        estermannZeta p ((a : ZMod p)) s‖ ≤ 2 * Real.sqrt p * divisorMass s.re :=
  norm_estermann_invTwist_le_of_bound p b
    (fun m => norm_kloostermanSum_le_weil p hp2 m hb) hs

/-- The saving is genuine: beyond the first few primes the Weil bound is strictly smaller than the
trivial one, and the ratio is `≍ √p`. -/
theorem two_sqrt_lt_totient (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    2 * Real.sqrt p < (Nat.totient p : ℝ) := by
  have hprime : p.Prime := Fact.out
  have hp7 : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt (by positivity)
  have hsnn : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hr : (5 : ℝ) / 2 ≤ Real.sqrt p := by
    have hle : ((5 : ℝ) / 2) ^ 2 ≤ (p : ℝ) := by nlinarith
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (5:ℝ)/2)] at this
  have htot : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hprime]
    have : (1 : ℕ) ≤ p := hprime.one_lt.le
    push_cast [Nat.cast_sub this]
    ring
  rw [htot]
  nlinarith [hsq, hr, hsnn]

end

end RHTower
