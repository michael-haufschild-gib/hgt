import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeNormalFrame
import GaloisForLFunctions.HTGeometry.KroneckerApproxRecurrence

/-!
# The prime frame has no Hilbert frame lower bound

After removing the common first-order decay the prime multipliers are the pure sines
`b_p(t) = 2 p^{-1/2} sin(t log p / 2)`.  Unique factorization makes the prime logarithms
rationally independent, so Kronecker recurrence returns all of their phases simultaneously to
zero at arbitrarily large times.  Hence for every finite set of primes the diagonal sum
`∑ b_p(t)²` has infimum zero along arbitrarily large times: the algebraic prime rank of the `Xi`
normal line is not a Hilbert frame rank.
-/

open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions

namespace HedenmalmThetaSource

/-- The sine is dominated by the distance of the character from one. -/
theorem abs_sin_le_norm_expChar_sub_one (x : ℝ) :
    |Real.sin x| ≤ ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ := by
  have h := norm_expChar_sub_sq x 0
  have h0 : Complex.exp (((0 : ℝ) : ℝ) * Complex.I) = 1 := by simp
  rw [h0, sub_zero] at h
  have hpyth := Real.sin_sq_add_cos_sq x
  have hnn : (0 : ℝ) ≤ ‖Complex.exp ((x : ℝ) * Complex.I) - 1‖ := norm_nonneg _
  nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x, abs_nonneg (Real.sin x),
    sq_abs (Real.sin x)]

theorem sq_frameSymbol_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : |Real.sin (t * Real.log n / 2)| ≤ ε) :
    frameSymbol n t ^ 2 ≤ 4 * ε ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : ((n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have habs : |frameSymbol n t| ≤ 2 * ε := by
    rw [frameSymbol, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (n:ℝ) ^ (-(1/2:ℝ)))]
    nlinarith [abs_nonneg (Real.sin (t * Real.log n / 2))]
  nlinarith [abs_nonneg (frameSymbol n t), sq_abs (frameSymbol n t)]

/-- **The finite prime frame has no uniform lower bound.**  For every finite set of primes and
every tolerance there are arbitrarily large times at which the whole diagonal sum of squares is
below the tolerance. -/
theorem exists_gt_sum_sq_frameSymbol_lt (P : Finset Nat.Primes) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ ∑ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2 < δ := by
  classical
  set ε : ℝ := Real.sqrt (δ / (4 * ((P.card : ℝ) + 1))) with hεdef
  have hden : (0 : ℝ) < 4 * ((P.card : ℝ) + 1) := by positivity
  have hquot : (0 : ℝ) < δ / (4 * ((P.card : ℝ) + 1)) := div_pos hδ hden
  have hε : 0 < ε := Real.sqrt_pos.mpr hquot
  have hεsq : ε ^ 2 = δ / (4 * ((P.card : ℝ) + 1)) := Real.sq_sqrt hquot.le
  have hind : LinearIndependent ℚ (fun p : {x // x ∈ P} => Real.log ((p : Nat.Primes) : ℕ)) :=
    linearIndependent_log_primes.comp (fun p : {x // x ∈ P} => (p : Nat.Primes))
      Subtype.val_injective
  obtain ⟨s, hs, hclose⟩ := kronecker_approx_atTop hind (fun _ => (0 : ℝ)) hε (T / 2)
  refine ⟨2 * s, by linarith, ?_⟩
  have hbound : ∀ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) (2 * s) ^ 2 ≤ 4 * ε ^ 2 := by
    intro p hp
    have hj := hclose ⟨p, hp⟩
    have h0 : Complex.exp (((0 : ℝ) : ℝ) * Complex.I) = 1 := by simp
    rw [h0] at hj
    have hexp : expChar (Real.log ((p : Nat.Primes) : ℕ)) s
        = Complex.exp (((Real.log ((p : Nat.Primes) : ℕ) * s : ℝ) : ℝ) * Complex.I) := rfl
    rw [hexp] at hj
    have hsin : |Real.sin (Real.log ((p : Nat.Primes) : ℕ) * s)| ≤ ε :=
      le_of_lt (lt_of_le_of_lt (abs_sin_le_norm_expChar_sub_one _) hj)
    have hn : 1 ≤ ((p : Nat.Primes) : ℕ) := (p : Nat.Primes).2.one_lt.le
    refine sq_frameSymbol_le hn (2 * s) hε.le ?_
    rw [show 2 * s * Real.log ((p : Nat.Primes) : ℕ) / 2
        = Real.log ((p : Nat.Primes) : ℕ) * s by ring]
    exact hsin
  calc ∑ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) (2 * s) ^ 2
      ≤ ∑ _p ∈ P, 4 * ε ^ 2 := Finset.sum_le_sum hbound
    _ = (P.card : ℝ) * (4 * ε ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ < δ := by
        rw [hεsq]
        have hcard : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
        rw [div_eq_inv_mul]
        field_simp
        nlinarith


/-! ### The summably weighted all-prime obstruction -/

theorem sq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast (x ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hx]
  norm_num
  rw [Real.rpow_neg_one]

/-- The pointwise ceiling of the frame symbol square. -/
theorem sq_frameSymbol_le_four_div {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    frameSymbol n t ^ 2 ≤ 4 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : frameSymbol n t ^ 2
      = 4 * (n : ℝ)⁻¹ * Real.sin (t * Real.log n / 2) ^ 2 := by
    rw [frameSymbol, mul_pow, mul_pow, sq_rpow_neg_half hn0.le]
    ring
  have hsin : Real.sin (t * Real.log n / 2) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (t * Real.log n / 2),
      sq_nonneg (Real.cos (t * Real.log n / 2))]
  rw [hsq]
  have h4inv : (0 : ℝ) ≤ 4 * (n : ℝ)⁻¹ := by positivity
  calc 4 * (n : ℝ)⁻¹ * Real.sin (t * Real.log n / 2) ^ 2 ≤ 4 * (n : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hsin h4inv
    _ = 4 / (n : ℝ) := by rw [mul_one, div_eq_mul_inv]

theorem summable_weighted_frameSymbol {ω : Nat.Primes → ℝ} (hω : ∀ p, 0 ≤ ω p)
    (hsum : Summable fun p : Nat.Primes => ω p / ((p : ℕ) : ℝ)) (t : ℝ) :
    Summable fun p : Nat.Primes => ω p * frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hω p) (sq_nonneg _)) (fun p => ?_)
    (hsum.mul_left 4)
  have hn : 1 ≤ ((p : Nat.Primes) : ℕ) := p.2.one_lt.le
  have hle := sq_frameSymbol_le_four_div hn t
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  calc ω p * frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2
      ≤ ω p * (4 / ((p : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hle (hω p)
    _ = 4 * (ω p / ((p : ℕ) : ℝ)) := by ring

/-- **The summably weighted all-prime frame obstruction.**  For every nonnegative weight with
`∑ ω_p / p` finite the whole weighted diagonal sum of squares drops below any tolerance at
arbitrarily large times.  The `Xi` normal line therefore has no summably weighted diagonal Hilbert
frame rank. -/
theorem exists_gt_tsum_weighted_frameSymbol_lt {ω : Nat.Primes → ℝ} (hω : ∀ p, 0 ≤ ω p)
    (hsum : Summable fun p : Nat.Primes => ω p / ((p : ℕ) : ℝ)) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ t : ℝ, T < t
      ∧ (∑' p : Nat.Primes, ω p * frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2) < δ := by
  classical
  have hsum4 : Summable fun p : Nat.Primes => 4 * (ω p / ((p : ℕ) : ℝ)) := hsum.mul_left 4
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have htail : Filter.Tendsto (fun s : Finset Nat.Primes =>
      ∑' p : {q : Nat.Primes // q ∉ s},
        4 * (ω (p : Nat.Primes) / ((((p : Nat.Primes) : ℕ)) : ℝ))) Filter.atTop (nhds 0) :=
    tendsto_tsum_compl_atTop_zero (fun q : Nat.Primes => 4 * (ω q / ((q : ℕ) : ℝ)))
  obtain ⟨P, hPtail⟩ := (htail.eventually_lt_const hhalf).exists
  set W : ℝ := ∑ p ∈ P, ω p with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun p _ => hω p
  have hdenom : (0 : ℝ) < W + 1 := by linarith
  obtain ⟨t, ht, hhead⟩ := exists_gt_sum_sq_frameSymbol_lt P
    (show (0 : ℝ) < (δ / 2) / (W + 1) from div_pos hhalf hdenom) T
  refine ⟨t, ht, ?_⟩
  have hsummable := summable_weighted_frameSymbol hω hsum t
  have hsplit := hsummable.sum_add_tsum_compl (s := P)
  have hheadbound : (∑ p ∈ P, ω p * frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2) < δ / 2 := by
    have hle : (∑ p ∈ P, ω p * frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2)
        ≤ W * ∑ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Finset.single_le_sum (fun q _ => hω q) hp
    have hpos : W * ∑ p ∈ P, frameSymbol ((p : Nat.Primes) : ℕ) t ^ 2
        ≤ W * ((δ / 2) / (W + 1)) :=
      mul_le_mul_of_nonneg_left hhead.le hW0
    have hfin : W * ((δ / 2) / (W + 1)) < δ / 2 := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ hdenom]
      nlinarith
    linarith
  have htailbound : (∑' p : {q : Nat.Primes // q ∉ P},
      ω (p : Nat.Primes) * frameSymbol (((p : Nat.Primes) : ℕ)) t ^ 2) < δ / 2 := by
    refine lt_of_le_of_lt ?_ hPtail
    refine Summable.tsum_le_tsum (fun p => ?_) (hsummable.subtype _) (hsum4.subtype _)
    have hn : 1 ≤ (((p : Nat.Primes) : ℕ)) := (p : Nat.Primes).2.one_lt.le
    have hle := sq_frameSymbol_le_four_div hn t
    calc ω (p : Nat.Primes) * frameSymbol (((p : Nat.Primes) : ℕ)) t ^ 2
        ≤ ω (p : Nat.Primes) * (4 / ((((p : Nat.Primes) : ℕ)) : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (hω _)
      _ = 4 * (ω (p : Nat.Primes) / ((((p : Nat.Primes) : ℕ)) : ℝ)) := by ring
  rw [← hsplit]
  have htailbound' : (∑' x : ((↑P : Set Nat.Primes)ᶜ : Set Nat.Primes),
      ω (x : Nat.Primes) * frameSymbol (((x : Nat.Primes) : ℕ)) t ^ 2) < δ / 2 := htailbound
  linarith


end HedenmalmThetaSource

end

end RHTower
