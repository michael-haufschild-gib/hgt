import GaloisForLFunctions.BezoutValuationIncidence.BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo

/-!
# Coherent prime blocks: no Type-II dispersion below the quadratic horizon

Let `B` be `k` primes in a short interval `[p₀, p₀ + ℓ]` and give each the jump `a_p p = 1`. On
the observation window `W = [X, 2X)`, `X = J₀ p₀`, the multiples of the block primes cluster:
between the clusters `j(p₀ + ℓ) ≤ n < (j + 1)p₀` every quotient `⌊n/p⌋` equals `j`, and the packet
is exactly affine,

`V(n) = L + k j - n s`,  `s = Σ_{p ∈ B} 1/p ≥ k/(2p₀)`.

Each of the `J₀` clean regions has length at least `p₀/2` when `4 J₀ ℓ ≤ p₀`, so it carries the
ramp variance `s² r³/12` whatever its offset. Summing,

`Σ_{n ∈ W} V(n)²/(n(n+1)) ≥ (k / 2304) · k Σ_{n ∈ W} 1/(n(n+1))`,

and the right factor `k Σ_W 1/(n(n+1)) = Σ_W Σ_p (a_p p)²/(n(n+1))` bounds the window diagonal
`Σ_W Σ_p a_p² F_p(n)²/(n(n+1))` from above. The window energy therefore exceeds the window
diagonal by the factor `k/2304`, the number of primes in an interval of length `ℓ ≈ p₀²/(4X)`.

By pigeonhole every set `S` of primes in `(P, 2P]` has such a block with
`k ≥ |S| / ⌈P/(ℓ+1)⌉ ≈ |S| P/(4X)`. At `X = P^{2/θ}` the loss is `P^{2-2/θ}/log P`, a power of
`P` for every `θ > 1`: the large-sieve loss `P²/X` is attained at every window below the
quadratic horizon, and no Type-II input (arbitrary coefficients, ℓ² norms) reaches any exponent
`θ > 1` on the pronic prime Gram. The obstruction is the jump measure `Σ_{p ∈ I} a_p p` on
intervals `I` of length `P²/X`; the replacement hypothesis is its square-root cancellation at
that scale.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The coherent block packet: unit jumps `a_p p = 1` on `B`. -/
def primeBlockPacket (B : Finset Nat.Primes) (p : Nat.Primes) : ℝ :=
  if p ∈ B then 1 / ((p : ℕ) : ℝ) else 0

/-- Every prime packet is its log moment minus the weighted residues. -/
theorem primePacketValue_eq_logMoment_sub (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) (n : ℕ) :
    primePacketValue S a n =
      primePacketLogMoment S a - ∑ p ∈ S, a p * ((n % (p : ℕ) : ℕ) : ℝ) := by
  unfold primePacketValue primePacketLogMoment
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime p.property,
    vonMangoldt_apply_prime p.property]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

/-- Where all block quotients equal `j`, the block packet is affine: `L + k j - n s`. -/
theorem primeBlockPacket_value_of_div_eq (B : Finset Nat.Primes) {n j : ℕ}
    (h : ∀ p ∈ B, n / (p : ℕ) = j) :
    primePacketValue B (primeBlockPacket B) n =
      primePacketLogMoment B (primeBlockPacket B) + B.card * j -
        n * ∑ p ∈ B, 1 / ((p : ℕ) : ℝ) := by
  rw [primePacketValue_eq_logMoment_sub]
  have hres : ∑ p ∈ B, primeBlockPacket B p * ((n % (p : ℕ) : ℕ) : ℝ) =
      ∑ p ∈ B, ((n : ℝ) * (1 / ((p : ℕ) : ℝ)) - j) := by
    refine sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
    have hmod := Nat.mod_add_div n p
    rw [h p hp] at hmod
    have hcast : ((n % (p : ℕ) : ℕ) : ℝ) = n - (p : ℕ) * j := by
      have := congrArg (Nat.cast (R := ℝ)) hmod
      push_cast at this
      linarith
    rw [primeBlockPacket, if_pos hp, hcast]
    field_simp
  rw [hres, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  ring

/-- A run of `r` consecutive values of an affine function has energy at least the ramp
variance `s² r (r² - 1)/12`. -/
theorem sum_Ico_affine_sq_ge (m r : ℕ) (α s : ℝ) :
    s ^ 2 * ((r : ℝ) * ((r : ℝ) ^ 2 - 1) / 12) ≤ ∑ n ∈ Ico m (m + r), (α - n * s) ^ 2 := by
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have h := sum_range_ramp_sq_ge r (α - m * s + s) (-s)
  rw [neg_sq] at h
  refine h.trans_eq (sum_congr rfl fun v _ => ?_)
  push_cast
  ring

/-- Splitting `[J₀ p₀, J₁ p₀)` into the period blocks `[j p₀, (j+1) p₀)`. -/
theorem sum_Ico_mul_eq_sum_blocks (f : ℕ → ℝ) (p₀ J₀ : ℕ) {J₁ : ℕ} (h : J₀ ≤ J₁) :
    ∑ n ∈ Ico (J₀ * p₀) (J₁ * p₀), f n =
      ∑ j ∈ Ico J₀ J₁, ∑ n ∈ Ico (j * p₀) ((j + 1) * p₀), f n := by
  induction J₁, h using Nat.le_induction with
  | base => simp
  | succ J₁ hJ ih =>
    rw [← sum_Ico_consecutive f (Nat.mul_le_mul_right p₀ hJ)
      (Nat.mul_le_mul_right p₀ (Nat.le_succ J₁)), ih, sum_Ico_succ_top hJ]

/-- **Coherent block energy on a window.** For `k` primes in `[p₀, p₀ + ℓ]` with unit jumps,
`p₀ ≥ 4`, `ℓ ≤ p₀`, `4 J₀ ℓ ≤ p₀`, the pronic energy on `[J₀ p₀, 2 J₀ p₀)` is at least `k/2304`
times the window diagonal bound `k Σ_W 1/(n(n+1))`. -/
theorem primeBlockPacket_window_energy_ge (B : Finset Nat.Primes) {p₀ ℓ J₀ : ℕ}
    (hB : ∀ p ∈ B, p₀ ≤ (p : ℕ) ∧ (p : ℕ) ≤ p₀ + ℓ) (hp₀ : 4 ≤ p₀) (hℓ : ℓ ≤ p₀)
    (hJ : 0 < J₀) (hJℓ : 4 * J₀ * ℓ ≤ p₀) :
    (B.card : ℝ) / 2304 * ((B.card : ℝ) *
        ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀), 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀),
        primePacketValue B (primeBlockPacket B) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  set k : ℝ := (B.card : ℝ) with hkdef
  set s : ℝ := ∑ p ∈ B, 1 / ((p : ℕ) : ℝ) with hsdef
  set L := primePacketLogMoment B (primeBlockPacket B)
  set V := fun n : ℕ => primePacketValue B (primeBlockPacket B) n
  have hp₀R : (4 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hJR : (1 : ℝ) ≤ J₀ := by exact_mod_cast hJ
  set D : ℝ := (2 * (J₀ * p₀ : ℕ) : ℝ) * (2 * (J₀ * p₀ : ℕ) + 1) with hD
  have hDpos : 0 < D := by positivity
  -- the slope is at least `k/(2p₀)`
  have hs : k / (2 * p₀) ≤ s := by
    rw [hsdef, show k / (2 * p₀) = ∑ _p ∈ B, 1 / (2 * (p₀ : ℝ)) by
      rw [sum_const, nsmul_eq_mul]; ring]
    refine sum_le_sum fun p hp => ?_
    have h1 : ((p : ℕ) : ℝ) ≤ 2 * p₀ := by
      have := (hB p hp).2; exact_mod_cast (by omega : (p : ℕ) ≤ 2 * p₀)
    have h0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
    exact one_div_le_one_div_of_le h0 h1
  -- each clean region carries the ramp variance
  have hreg : ∀ j ∈ Ico J₀ (2 * J₀), s ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12) / D ≤
      ∑ n ∈ Ico (j * p₀) ((j + 1) * p₀), V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro j hj
    obtain ⟨hj0, hj1⟩ := mem_Ico.mp hj
    have hjℓ : 2 * (j * ℓ) ≤ p₀ := by nlinarith
    set r := p₀ - j * ℓ
    have hsub : Ico (j * (p₀ + ℓ)) (j * (p₀ + ℓ) + r) ⊆ Ico (j * p₀) ((j + 1) * p₀) := by
      intro n hn
      simp only [mem_Ico] at hn ⊢
      constructor <;> nlinarith [Nat.sub_add_cancel (show j * ℓ ≤ p₀ by omega)]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      div_nonneg (sq_nonneg _) (by positivity))
    have hval : ∀ n ∈ Ico (j * (p₀ + ℓ)) (j * (p₀ + ℓ) + r),
        V n = (L + k * j) - n * s := by
      intro n hn
      have hn' := mem_Ico.mp hn
      have hdiv : ∀ p ∈ B, n / (p : ℕ) = j := fun p hp => by
        obtain ⟨h1, h2⟩ := hB p hp
        refine Nat.div_eq_of_lt_le ?_ ?_
        · nlinarith
        · nlinarith [Nat.sub_add_cancel (show j * ℓ ≤ p₀ by omega)]
      simp only [V]
      rw [primeBlockPacket_value_of_div_eq B hdiv]
    have hwt : ∀ n ∈ Ico (j * (p₀ + ℓ)) (j * (p₀ + ℓ) + r),
        V n ^ 2 / D ≤ V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      intro n hn
      have hn' := mem_Ico.mp hn
      have hnD : n + 1 ≤ 2 * (J₀ * p₀) := by
        nlinarith [Nat.sub_add_cancel (show j * ℓ ≤ p₀ by omega)]
      have hnR : (n : ℝ) + 1 ≤ 2 * (J₀ * p₀ : ℕ) := by exact_mod_cast hnD
      have h0 : 0 < n := by nlinarith
      have : (n : ℝ) * ((n : ℝ) + 1) ≤ D := by
        rw [hD]; apply mul_le_mul <;> [linarith; linarith; positivity; positivity]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) this
    refine le_trans ?_ (sum_le_sum hwt)
    rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    refine le_trans ?_ ((sum_Ico_affine_sq_ge _ r (L + k * j) s).trans_eq
      (sum_congr rfl fun n hn => by rw [hval n hn]))
    -- `r ≥ p₀/2` gives `r (r² - 1) ≥ p₀³/16`
    have hr : (p₀ : ℝ) ≤ 2 * r := by
      have : p₀ ≤ 2 * r := by omega
      exact_mod_cast this
    have hr2 : (p₀ : ℝ) ^ 3 / 16 ≤ (r : ℝ) * ((r : ℝ) ^ 2 - 1) := by
      nlinarith [sq_nonneg ((r : ℝ) - p₀ / 2), mul_pos (by linarith : (0 : ℝ) < p₀)
        (by linarith : (0 : ℝ) < p₀)]
    have := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr2 (by norm_num : (0:ℝ) ≤ 12))
      (sq_nonneg s)
    exact this
  -- assemble the regions
  have hsplit := sum_Ico_mul_eq_sum_blocks
    (fun n => V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) p₀ J₀ (J₁ := 2 * J₀) (by omega)
  rw [show 2 * J₀ * p₀ = (2 * J₀) * p₀ by ring]
  change _ ≤ ∑ n ∈ Ico (J₀ * p₀) ((2 * J₀) * p₀), V n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
  rw [hsplit]
  refine le_trans ?_ (sum_le_sum hreg)
  rw [sum_const, Nat.card_Ico, show 2 * J₀ - J₀ = J₀ by omega, nsmul_eq_mul,
    show (2 * J₀) * p₀ = 2 * (J₀ * p₀) by ring,
    sum_Ico_pronic_mass (by positivity) (by omega)]
  have hX : (0 : ℝ) < (J₀ * p₀ : ℕ) := by positivity
  have hX1 : (1 : ℝ) ≤ (J₀ * p₀ : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hDle : D ≤ 6 * ((J₀ * p₀ : ℕ) : ℝ) ^ 2 := by
    rw [hD]; nlinarith
  have hs2 : (k / (2 * p₀)) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
  have hk : 0 ≤ k := Nat.cast_nonneg _
  push_cast at hX hDle ⊢
  rw [show (1 : ℝ) / (J₀ * p₀) - 1 / (2 * (J₀ * p₀)) = 1 / (2 * (J₀ * p₀)) by field_simp; ring]
  calc k / 2304 * (k * (1 / (2 * ((J₀ : ℝ) * p₀))))
      = (J₀ : ℝ) * ((k / (2 * p₀)) ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12)) /
          (6 * ((J₀ : ℝ) * p₀) ^ 2) := by
        field_simp
        ring
    _ ≤ (J₀ : ℝ) * (s ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12)) / D := by
        apply div_le_div₀ (by positivity) ?_ hDpos hDle
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hs2 (by positivity)) (by positivity)
    _ = (J₀ : ℝ) * (s ^ 2 * ((p₀ : ℝ) ^ 3 / 16 / 12) / D) := by ring

/-- The window energy is part of the energy-centered Gram form of the block packet. -/
theorem sum_Ico_primePacketValue_sq_le_primePacketBilinear (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) (m M : ℕ) :
    ∑ n ∈ Ico m M, primePacketValue S a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      primePacketBilinear S S a a := by
  simp_rw [sq]
  exact sum_le_hasSum _ (fun n _ => div_nonneg (mul_self_nonneg _) (by positivity))
    (hasSum_primePacketBilinear S S a a)

/-- **No Type-II dispersion below the quadratic horizon.** Every set `S` of primes in
`(P, 2P]` contains a block `B` of at least `|S| / ((P-1)/(ℓ+1) + 1)` primes in an interval
`[p₀, p₀ + ℓ]`, `P < p₀ ≤ 2P`, whose unit-jump packet has, on the window `[J₀ p₀, 2 J₀ p₀)`,
pronic energy at least `|B|/2304` times the window diagonal bound, whenever `4 J₀ ℓ ≤ P + 1`. -/
theorem exists_primeBlock_typeII_window_loss (S : Finset Nat.Primes) {P ℓ J₀ : ℕ}
    (hP : 3 ≤ P) (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P) (hJ : 0 < J₀)
    (hJℓ : 4 * J₀ * ℓ ≤ P + 1) (hℓ : ℓ ≤ P + 1) :
    ∃ B ⊆ S, ∃ p₀ : ℕ, P < p₀ ∧ p₀ ≤ 2 * P ∧
      S.card / ((P - 1) / (ℓ + 1) + 1) ≤ B.card ∧
      (∀ p ∈ B, p₀ ≤ (p : ℕ) ∧ (p : ℕ) ≤ p₀ + ℓ) ∧
      (B.card : ℝ) / 2304 * ((B.card : ℝ) *
          ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀), 1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀),
          primePacketValue B (primeBlockPacket B) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ∧
      ∑ n ∈ Ico (J₀ * p₀) (2 * J₀ * p₀),
          primePacketValue B (primeBlockPacket B) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        primePacketBilinear B B (primeBlockPacket B) (primeBlockPacket B) := by
  set m := (P - 1) / (ℓ + 1) + 1 with hm
  set f : Nat.Primes → ℕ := fun p => ((p : ℕ) - (P + 1)) / (ℓ + 1)
  have hmaps : ∀ p ∈ S, f p ∈ range m := by
    intro p hp
    have := hS p hp
    simp only [f, mem_range, hm]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  obtain ⟨y, hy, hcard⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps
    (nonempty_range_iff.mpr (by rw [hm]; exact Nat.succ_ne_zero _))
    (by rw [card_range]; exact Nat.mul_div_le _ _)
  set B := S.filter fun x => f x = y
  set p₀ := P + 1 + y * (ℓ + 1) with hp₀def
  have hyP : y * (ℓ + 1) ≤ P - 1 := by
    have h1 : y ≤ (P - 1) / (ℓ + 1) := Nat.lt_succ_iff.mp (mem_range.mp hy)
    exact (Nat.mul_le_mul_right _ h1).trans (Nat.div_mul_le_self _ _)
  have hBint : ∀ p ∈ B, p₀ ≤ (p : ℕ) ∧ (p : ℕ) ≤ p₀ + ℓ := by
    intro p hp
    obtain ⟨hpS, hfp⟩ := mem_filter.mp hp
    have hpP := hS p hpS
    have hlo := Nat.div_mul_le_self ((p : ℕ) - (P + 1)) (ℓ + 1)
    have hhi := Nat.lt_div_mul_add (a := (p : ℕ) - (P + 1)) (b := ℓ + 1) (by omega)
    simp only [f] at hfp
    rw [hfp] at hlo hhi
    rw [hp₀def]
    constructor <;> omega
  have hyl : 0 ≤ y * (ℓ + 1) := Nat.zero_le _
  refine ⟨B, filter_subset _ _, p₀, by omega, by omega, hcard, hBint,
    primeBlockPacket_window_energy_ge B hBint (by omega) (by omega) hJ
      (le_trans hJℓ (by omega)),
    sum_Ico_primePacketValue_sq_le_primePacketBilinear _ _ _ _⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
