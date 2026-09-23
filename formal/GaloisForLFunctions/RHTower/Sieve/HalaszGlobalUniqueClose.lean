import GaloisForLFunctions.RHTower.Sieve.CharacterDistanceGrowth
import GaloisForLFunctions.RHTower.Sieve.HalaszUniqueClose

/-!
# Uniqueness of a close frequency, without a spacing hypothesis

`HalaszUniqueClose.lean` proves that at most one frequency of a set is close to a bounded
multiplicative `f`, but its separation input is supplied twice over: once as the abstract inequality

`2π²δ² < (t − u)²∑_{p ≤ z}(log p)²/p`,

and once as the spacing condition `|(t − u)log p| ≤ π`, which confines the frequency set to a window
of width `π/log z`.  Both are premises there.

The distance growth law discharges both.  For `|t − u| ≤ 2` the pole of `ζ` at `s = 1` bounds the
prime series at frequency `t − u`, and Mertens' second theorem bounds it below, so

`charSepLower z (t − u) ≤ 𝔻(n^{it}, n^{iu}; z)²`

with no restriction relating `t − u` to `log z`.  Consequently a frequency set need only lie in a
fixed interval — no shrinking window — and the admissible mesh is compared against
`log(5 + 1/Δ)` rather than against `π/log z`.  For `Δ` fixed and `z → ∞` the number of frequencies
covered by one dichotomy is therefore larger by a factor `log z`.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The separation lower bound increases with the separation: the frequency enters only through
`log(5 + 1/|v|)`. -/
theorem charSepLower_mono_abs {z : ℕ} {v w : ℝ} (hv : 0 < |v|) (hvw : |v| ≤ |w|) :
    charSepLower z v ≤ charSepLower z w := by
  have hw : (0 : ℝ) < |w| := lt_of_lt_of_le hv hvw
  have hinv : 1 / |w| ≤ 1 / |v| := one_div_le_one_div_of_le hv hvw
  have hlog : Real.log (5 + 1 / |w|) ≤ Real.log (5 + 1 / |v|) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [charSepLower, charSepLower]
  linarith

/-- **At most one close frequency, with no spacing hypothesis.**  A frequency set inside `[-1, 1]`
whose points are `Δ`-separated contains at most one point within `δ` of `f`, provided
`4δ² < charSepLower z Δ`.  Both premises of `card_filter_close_le_one` are discharged: the abstract
separation by the distance growth law, and the spacing by the bound `|t − u| ≤ 2`. -/
theorem card_filter_close_le_one_of_separation {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z : ℕ}
    (hz : 3 ≤ z) {δ Δ : ℝ} (hΔ0 : 0 < Δ) (S : Finset ℝ)
    (hS : ∀ t ∈ S, |t| ≤ 1)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → Δ ≤ |t - u|)
    (hgap : 4 * δ ^ (2 : ℕ) < charSepLower z Δ) :
    ((S.filter (fun t =>
      Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ)).card) ≤ 1 := by
  classical
  have hP : ∀ p ∈ Nat.primesLE z, 0 < p := fun p hp => (Nat.prime_of_mem_primesLE hp).pos
  have hsq : ∀ t : ℝ, Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ →
      mulDistSqPair f (charFn t) (Nat.primesLE z) ≤ δ ^ (2 : ℕ) := by
    intro t h
    have hnn : 0 ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) :=
      mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn t p).le) hP
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt hnn] at this
  refine Finset.card_le_one.2 ?_
  intro t ht u hu
  rw [Finset.mem_filter] at ht hu
  by_contra hne
  have hd : |t - u| ≤ 2 := by
    have h1 := hS t ht.1
    have h2 := hS u hu.1
    calc |t - u| ≤ |t| + |u| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hd0 : t - u ≠ 0 := sub_ne_zero.2 hne
  have hmain := charSepLower_le_four_mul_of_both_close hf hz hd hd0 (hsq t ht.2) (hsq u hu.2)
  have hmono : charSepLower z Δ ≤ charSepLower z (t - u) := by
    refine charSepLower_mono_abs (by rwa [abs_of_pos hΔ0]) ?_
    rw [abs_of_pos hΔ0]
    exact hspace t ht.1 u hu.1 hne
  linarith

/-- **The Halász sum bound over a separated frequency set, with no spacing hypothesis.**  Only the
mesh of the frequency set and the size of the interval containing it enter; the window width
`π/log z` of the spacing form plays no role. -/
theorem sum_norm_smoothMulSum_le_of_separation {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {z : ℕ} (hz : 3 ≤ z) {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ0 : 0 < Δ) (S : Finset ℝ)
    (hS : ∀ t ∈ S, |t| ≤ 1)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → Δ ≤ |t - u|)
    (hgap : 4 * δ ^ (2 : ℕ) < charSepLower z Δ) :
    ∑ t ∈ S, ‖smoothMulSum f (Nat.primesLE z) t‖
      ≤ (S.card : ℝ)
          * Real.exp ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
            + (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ (2 : ℕ)) - δ ^ (2 : ℕ))
        + Real.exp ((∑ p ∈ Nat.primesLE z, 1 / (p : ℝ))
            + (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) ^ (2 : ℕ))) :=
  sum_norm_smoothMulSum_le_of_card hf hmul h1
    (fun _ hp => Nat.prime_of_mem_primesLE hp)
    (fun _ hp => (Nat.prime_of_mem_primesLE hp).pos) hδ S
    (card_filter_close_le_one_of_separation hf hz hΔ0 S hS hspace hgap)

end RHTower.Sieve
end
