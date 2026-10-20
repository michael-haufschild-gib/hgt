import GaloisForLFunctions.BezoutValuationIncidence.PrimePacketConditionalTailAndCoherentPrefix
import GaloisForLFunctions.BezoutValuationIncidence.ExactVasyuninReciprocityAsResidueDifferenceEnergy

/-!
# The first-jump window of a prime block: Brownian-bridge law and a codimension no-go

For a prime `p` the energy-centered primitive is `F_p(n) = log p - (n mod p)`. While `n < 2p`
the residue has jumped at most once, so a packet `V(n) = Σ_p a_p F_p(n)` equals

`V(n) = L - n A + C(n)`,  `C(n) = Σ_{p ≤ n} a_p p`,

with mass `A = Σ a_p` and log moment `L = Σ a_p log p`. For a block `S ⊆ (P, 2P]` with `A = L = 0`
the pronic energy of the window `n < 2P + 2` is exactly the Brownian-bridge form

`Σ_{n < 2P+2} V(n)² / (n(n+1)) = Σ_{p,q} a_p a_q (min(p,q) - pq/(2P+2))`,

a lower bound for the energy-centered Gram form `Σ a_p a_q 𝒢^{ec}(p,q)`. Its kernel has slowly
decaying spectrum: on `J + 3` consecutive blocks of `k` primes, block-constant jumps make the
cumulative sum `C` grow linearly inside each block. Hence for every family of `J` linear side
conditions there is a nonzero packet satisfying them, with `A = L = 0`, and

`Σ_{p,q} a_p a_q 𝒢^{ec}(p,q) ≥ (k² - 1)/(24 (2P + 1)) · Σ_p p a_p²`.

Cauchy–Schwarz gives the upper bound `|S| · Σ a_p² 𝒢^{ec}(p,p)` with `𝒢^{ec}(p,p) ≍ p`. With
`k ≈ |S|/(J+3)` the lower bound is `≍ |S|² / (P (J+3)²)` times the diagonal: no Type-II
estimate with finitely many side conditions improves Cauchy–Schwarz by more than a factor
`(J+3)² log P` on a prime block, and diagonal quality needs `J ≳ |S| / √P` conditions. The
necessary replacement hypothesis is square-root size of the cumulative jump sum `C` on the
block, which is the summatory function of the coefficients.
-/

open Finset ArithmeticFunction RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The first-jump window -/

/-- Cumulative jump sum `C(n) = Σ_{p ∈ S, p ≤ n} a_p p` of a prime packet. -/
def primePacketJumpSum (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ S.filter (fun p : Nat.Primes => (p : ℕ) ≤ n), a p * (p : ℕ)

/-- Before the second jump of every mode, a prime packet is `L - n A + C(n)`. -/
theorem primePacketValue_eq_of_lt_two_mul (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) {n : ℕ}
    (hn : ∀ p ∈ S, n < 2 * (p : ℕ)) :
    primePacketValue S a n = primePacketLogMoment S a - n * primePacketMass S a +
      primePacketJumpSum S a n := by
  unfold primePacketValue primePacketLogMoment primePacketMass primePacketJumpSum
  rw [sum_filter, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime p.property,
    vonMangoldt_apply_prime p.property]
  simp only [Complex.neg_re, Complex.natCast_re]
  have h2 := hn p hp
  by_cases hpn : (p : ℕ) ≤ n
  · rw [if_pos hpn, Nat.mod_eq_sub_mod hpn, Nat.mod_eq_of_lt (by omega), Nat.cast_sub hpn]
    ring
  · rw [if_neg hpn, Nat.mod_eq_of_lt (by omega)]
    ring

/-! ## §2. The Brownian-bridge law -/

theorem cast_min_eq_mul_div_max (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ((min p q : ℕ) : ℝ) = (p : ℝ) * q / (max p q : ℕ) := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h]
    field_simp
  · rw [min_eq_right h, max_eq_left h]
    field_simp

/-- The pronic energy of the cumulative jump sum below `U` is the Brownian-bridge kernel. -/
theorem sum_range_primePacketJumpSum_sq_div (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {U : ℕ} (hS : ∀ p ∈ S, (p : ℕ) < U) :
    ∑ n ∈ range U, primePacketJumpSum S a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ p ∈ S, ∑ q ∈ S, a p * a q *
        (((min (p : ℕ) (q : ℕ) : ℕ) : ℝ) - ((p : ℕ) : ℝ) * (q : ℕ) / U) := by
  have hterm (n : ℕ) : primePacketJumpSum S a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ p ∈ S, ∑ q ∈ S, if max (p : ℕ) (q : ℕ) ≤ n then
        a p * (p : ℕ) * (a q * (q : ℕ)) / ((n : ℝ) * ((n : ℝ) + 1)) else (0 : ℝ) := by
    rw [primePacketJumpSum, sum_filter, sq, sum_mul_sum, sum_div]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun q _ => ?_
    by_cases hp : (p : ℕ) ≤ n <;> by_cases hq : (q : ℕ) ≤ n <;> simp [hp, hq]
  simp_rw [hterm]
  rw [sum_comm]
  refine sum_congr rfl fun p hpS => ?_
  rw [sum_comm]
  refine sum_congr rfl fun q hqS => ?_
  have hp0 : 0 < (p : ℕ) := p.property.pos
  have hq0 : 0 < (q : ℕ) := q.property.pos
  have hmax : max (p : ℕ) (q : ℕ) < U := max_lt (hS p hpS) (hS q hqS)
  set m := max (p : ℕ) (q : ℕ)
  rw [← sum_filter, show (range U).filter (fun n => m ≤ n) = Ico m U by
      ext n; simp [and_comm],
    show ∑ n ∈ Ico m U, a p * (p : ℕ) * (a q * (q : ℕ)) / ((n : ℝ) * ((n : ℝ) + 1)) =
      a p * (p : ℕ) * (a q * (q : ℕ)) * ∑ n ∈ Ico m U, 1 / ((n : ℝ) * ((n : ℝ) + 1)) by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by ring,
    sum_Ico_pronic_mass (lt_max_of_lt_left hp0) hmax.le, cast_min_eq_mul_div_max _ _ hp0 hq0]
  have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast lt_max_of_lt_left hp0
  have hU : (0 : ℝ) < U := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hmax
  field_simp

/-- Packets with zero mass and log moment on `S ⊆ (P, 2P]`: the pronic energy of the window
`n < 2P + 2` is the Brownian-bridge form. -/
theorem primePacket_window_eq_brownianBridge (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P : ℕ} (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0) :
    ∑ n ∈ range (2 * P + 2), primePacketValue S a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ p ∈ S, ∑ q ∈ S, a p * a q *
        (((min (p : ℕ) (q : ℕ) : ℕ) : ℝ) - ((p : ℕ) : ℝ) * (q : ℕ) / ((2 * P + 2 : ℕ) : ℝ)) := by
  rw [← sum_range_primePacketJumpSum_sq_div S a fun p hp => by have := hS p hp; omega]
  refine sum_congr rfl fun n hn => ?_
  rw [primePacketValue_eq_of_lt_two_mul S a fun p hp => by
    have := hS p hp; have := mem_range.mp hn; omega, hA, hL]
  ring

/-- **Brownian-bridge lower bound for the energy-centered prime Gram.** -/
theorem brownianBridge_le_primePacketBilinear (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P : ℕ} (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0) :
    ∑ p ∈ S, ∑ q ∈ S, a p * a q *
        (((min (p : ℕ) (q : ℕ) : ℕ) : ℝ) - ((p : ℕ) : ℝ) * (q : ℕ) / ((2 * P + 2 : ℕ) : ℝ)) ≤
      primePacketBilinear S S a a := by
  rw [← primePacket_window_eq_brownianBridge S a hS hA hL]
  simp_rw [sq]
  exact sum_le_hasSum _ (fun n _ => div_nonneg (mul_self_nonneg _) (by positivity))
    (hasSum_primePacketBilinear S S a a)

/-! ## §3. Cumulative energy at the prime points -/

/-- At the primes of the block the packet equals its cumulative jump sum, and the pronic weight
is at least `1/(2P(2P+1))`. -/
theorem sum_primePacketJumpSum_sq_le_primePacketBilinear (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) {P : ℕ} (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : primePacketMass S a = 0) (hL : primePacketLogMoment S a = 0) :
    (∑ p ∈ S, primePacketJumpSum S a (p : ℕ) ^ 2) / ((2 * P : ℝ) * (2 * P + 1)) ≤
      primePacketBilinear S S a a := by
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have hle : ∑ n ∈ S.image (fun p : Nat.Primes => (p : ℕ)),
      primePacketValue S a n * primePacketValue S a n / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        primePacketBilinear S S a a :=
    sum_le_hasSum _ (fun n _ => div_nonneg (mul_self_nonneg _) (by positivity))
      (hasSum_primePacketBilinear S S a a)
  rw [sum_image fun x _ y _ h => hinj h] at hle
  refine le_trans ?_ hle
  rw [sum_div]
  refine sum_le_sum fun p hp => ?_
  have hpP := hS p hp
  rw [primePacketValue_eq_of_lt_two_mul S a fun q hq => by have := hS q hq; omega, hA, hL]
  have hP : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
  have hpR : ((p : ℕ) : ℝ) ≤ 2 * P := by exact_mod_cast hpP.2
  have hden : ((p : ℕ) : ℝ) * ((p : ℕ) + 1) ≤ (2 * P : ℝ) * (2 * P + 1) := by
    apply mul_le_mul hpR (by linarith) (by positivity) (by positivity)
  simp only [mul_zero, sub_zero, zero_add]
  rw [← sq]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

/-! ## §4. Block-constant jumps -/

theorem sum_range_cast_add_one (k : ℕ) :
    ∑ v ∈ range k, ((v : ℝ) + 1) = (k : ℝ) * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_cast_add_one_sq (k : ℕ) :
    ∑ v ∈ range k, ((v : ℝ) + 1) ^ 2 = (k : ℝ) * (k + 1) * (2 * k + 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{v<k} (x + (v+1)c)² ≥ c² k (k² - 1)/12`: a linear ramp has variance `k(k²-1)/12`. -/
theorem sum_range_ramp_sq_ge (k : ℕ) (x c : ℝ) :
    c ^ 2 * ((k : ℝ) * ((k : ℝ) ^ 2 - 1) / 12) ≤
      ∑ v ∈ range k, (x + ((v : ℝ) + 1) * c) ^ 2 := by
  have h1 := sum_range_cast_add_one k
  have h2 := sum_range_cast_add_one_sq k
  have hpt : ∀ v : ℕ, (x + ((v : ℝ) + 1) * c) ^ 2 =
      x ^ 2 + 2 * x * c * ((v : ℝ) + 1) + c ^ 2 * ((v : ℝ) + 1) ^ 2 := fun v => by ring
  have hexp : ∑ v ∈ range k, (x + ((v : ℝ) + 1) * c) ^ 2 =
      k * x ^ 2 + 2 * x * c * ∑ v ∈ range k, ((v : ℝ) + 1) +
        c ^ 2 * ∑ v ∈ range k, ((v : ℝ) + 1) ^ 2 := by
    simp_rw [hpt]
    rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
      ← mul_sum]
  rw [hexp, h1, h2]
  nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg (x + c * (k + 1) / 2))]

/-- Partial sums of a block-constant sequence: each block of length `k` contributes the variance
of a ramp. -/
theorem sum_range_blockPartialSum_sq_ge (B k : ℕ) (c : ℕ → ℝ) :
    (k : ℝ) * ((k : ℝ) ^ 2 - 1) / 12 * ∑ i ∈ range B, c i ^ 2 ≤
      ∑ t ∈ range (B * k), (∑ s ∈ range (t + 1), c (s / k)) ^ 2 := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ, mul_add, Nat.succ_mul, Finset.sum_range_add]
    refine add_le_add ih ?_
    have hblock : ∀ v ∈ range k, (∑ s ∈ range (B * k + v + 1), c (s / k)) =
        (∑ s ∈ range (B * k), c (s / k)) + ((v : ℝ) + 1) * c B := by
      intro v hv
      have hvk := mem_range.mp hv
      rw [add_assoc, Finset.sum_range_add]
      congr 1
      rw [sum_congr rfl fun s hs => show c ((B * k + s) / k) = c B by
          have hsk : s < k := by have := mem_range.mp hs; omega
          rw [show B * k + s = s + B * k by ring, Nat.add_mul_div_right _ _ (by omega),
            Nat.div_eq_of_lt hsk, zero_add],
        sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [sum_congr rfl fun v hv => by rw [hblock v hv]]
    linarith [sum_range_ramp_sq_ge k (∑ s ∈ range (B * k), c (s / k)) (c B)]

/-! ## §5. The codimension no-go -/

/-- Primes ordered as natural numbers. -/
local instance primeBlockLinearOrder : LinearOrder Nat.Primes :=
  LinearOrder.lift' (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective

/-- The jump variable of the block construction: constant `c i` on the `i`-th block of `k`
consecutive indices, zero past `B k`. -/
def blockJump (B k : ℕ) (c : Fin B → ℝ) (t : ℕ) : ℝ :=
  if h : t / k < B then c ⟨t / k, h⟩ else 0

/-- The block packet on `S`: jump `blockJump (index p)` at the `index`-th prime of `S`. -/
def blockPacket (S : Finset Nat.Primes) (B k : ℕ) (c : Fin B → ℝ) (p : Nat.Primes) : ℝ :=
  if h : p ∈ S then
    (if ((S.orderIsoOfFin rfl).symm ⟨p, h⟩ : ℕ) < B * k then
      blockJump B k c ((S.orderIsoOfFin rfl).symm ⟨p, h⟩ : ℕ) / (p : ℕ) else 0)
  else 0

/-- `blockPacket` as a linear map of the block amplitudes. -/
def blockPacketLinear (S : Finset Nat.Primes) (B k : ℕ) :
    (Fin B → ℝ) →ₗ[ℝ] (Nat.Primes → ℝ) where
  toFun c := blockPacket S B k c
  map_add' c d := by
    funext p
    simp only [blockPacket, blockJump, Pi.add_apply]
    split_ifs <;> ring
  map_smul' r c := by
    funext p
    simp only [blockPacket, blockJump, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem sum_eq_sum_orderEmbOfFin (S : Finset Nat.Primes) (F : Nat.Primes → ℝ) :
    ∑ p ∈ S, F p = ∑ t : Fin S.card, F (S.orderEmbOfFin rfl t) := by
  conv_lhs => rw [← map_orderEmbOfFin_univ S rfl]
  rw [sum_map]
  rfl

theorem blockPacket_orderEmbOfFin (S : Finset Nat.Primes) (B k : ℕ) (c : Fin B → ℝ)
    (t : Fin S.card) :
    blockPacket S B k c (S.orderEmbOfFin rfl t) =
      if (t : ℕ) < B * k then blockJump B k c t / ((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ)
      else 0 := by
  have hmem := S.orderEmbOfFin_mem rfl t
  have hidx : (S.orderIsoOfFin rfl).symm ⟨S.orderEmbOfFin rfl t, hmem⟩ = t := by
    rw [OrderIso.symm_apply_eq]
    exact Subtype.ext (Finset.coe_orderIsoOfFin_apply S rfl t).symm
  simp only [blockPacket, dif_pos hmem, hidx]

/-- The cumulative jump sum of a block packet at its `t`-th prime is the partial sum of jumps. -/
theorem primePacketJumpSum_blockPacket (S : Finset Nat.Primes) (B k : ℕ) (c : Fin B → ℝ)
    (t : Fin S.card) (ht : (t : ℕ) < B * k) :
    primePacketJumpSum S (blockPacket S B k c) ((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) =
      ∑ s ∈ range ((t : ℕ) + 1), blockJump B k c s := by
  rw [primePacketJumpSum, sum_filter, sum_eq_sum_orderEmbOfFin]
  have hterm : ∀ s : Fin S.card,
      (if ((S.orderEmbOfFin rfl s : Nat.Primes) : ℕ) ≤ (S.orderEmbOfFin rfl t : Nat.Primes) then
        blockPacket S B k c (S.orderEmbOfFin rfl s) *
          ((S.orderEmbOfFin rfl s : Nat.Primes) : ℕ) else 0) =
        if (s : ℕ) ≤ (t : ℕ) then blockJump B k c s else 0 := by
    intro s
    have hle : ((S.orderEmbOfFin rfl s : Nat.Primes) : ℕ) ≤ (S.orderEmbOfFin rfl t : Nat.Primes)
        ↔ (s : ℕ) ≤ t := by
      rw [← Fin.le_def]
      exact (S.orderEmbOfFin rfl).le_iff_le
    have hp : (0 : ℝ) < ((S.orderEmbOfFin rfl s : Nat.Primes) : ℕ) := by
      exact_mod_cast (S.orderEmbOfFin rfl s).property.pos
    rw [blockPacket_orderEmbOfFin]
    by_cases hst : (s : ℕ) ≤ t
    · have hs : (s : ℕ) < B * k := lt_of_le_of_lt hst ht
      rw [if_pos (hle.mpr hst), if_pos hs, if_pos hst]
      field_simp
    · rw [if_neg (fun h => hst (hle.mp h)), if_neg hst]
  rw [sum_congr rfl fun s _ => hterm s,
    Fin.sum_univ_eq_sum_range (fun s => if s ≤ (t : ℕ) then blockJump B k c s else 0),
    ← sum_filter]
  congr 1
  ext s
  simp only [mem_filter, mem_range]
  have := t.isLt
  omega

/-- **Codimension no-go for Type-II bounds on a prime block.** Let `S ⊆ (P, 2P]` contain at
least `(J + 3) k` primes. For any `J` linear side conditions there is a packet on `S`, nonzero,
satisfying them, with zero mass and zero log moment, whose energy-centered Gram form is at least
`(k² - 1)/(24 (2P + 1))` times its diagonal `Σ_p p a_p²`. -/
theorem exists_constrained_primePacket_brownian_energy (S : Finset Nat.Primes) {P J k : ℕ}
    (hP : 0 < P) (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P) (hk : 0 < k)
    (hcard : (J + 3) * k ≤ S.card) (φ : Fin J → (Nat.Primes → ℝ) →ₗ[ℝ] ℝ) :
    ∃ a : Nat.Primes → ℝ, (∀ p, p ∉ S → a p = 0) ∧ (∀ j, φ j a = 0) ∧
      primePacketMass S a = 0 ∧ primePacketLogMoment S a = 0 ∧
      0 < ∑ p ∈ S, ((p : ℕ) : ℝ) * a p ^ 2 ∧
      ((k : ℝ) ^ 2 - 1) / (24 * (2 * P + 1)) * ∑ p ∈ S, ((p : ℕ) : ℝ) * a p ^ 2 ≤
        primePacketBilinear S S a a := by
  set B := J + 3 with hB
  set Ψ : (Fin B → ℝ) →ₗ[ℝ] (Fin (J + 2) → ℝ) := LinearMap.pi
    (Fin.cons ((⟨⟨fun a => primePacketMass S a, fun a b => by
        simp [primePacketMass, sum_add_distrib]⟩, fun r a => by
        simp [primePacketMass, mul_sum]⟩ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ).comp
        (blockPacketLinear S B k))
      (Fin.cons ((⟨⟨fun a => primePacketLogMoment S a, fun a b => by
          simp [primePacketLogMoment, sum_add_distrib, add_mul]⟩, fun r a => by
          simp [primePacketLogMoment, mul_sum, mul_assoc]⟩ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ).comp
          (blockPacketLinear S B k))
        fun j => (φ j).comp (blockPacketLinear S B k))) with hΨ
  have hker : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp [hB])
  obtain ⟨c, hcker, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hΨc : ∀ i, Ψ c i = 0 := fun i => by rw [LinearMap.mem_ker.mp hcker]; rfl
  set a := blockPacket S B k c with ha
  have hA : primePacketMass S a = 0 := by
    have h := hΨc 0
    simp only [hΨ, LinearMap.pi_apply, Fin.cons_zero, LinearMap.comp_apply] at h
    exact h
  have hL : primePacketLogMoment S a = 0 := by
    have h := hΨc 1
    simp only [hΨ, LinearMap.pi_apply] at h
    exact h
  have hφ : ∀ j, φ j a = 0 := fun j => by
    have h := hΨc j.succ.succ
    simp only [hΨ, LinearMap.pi_apply, Fin.cons_succ, LinearMap.comp_apply] at h
    exact h
  have hsupp : ∀ p, p ∉ S → a p = 0 := fun p hp => by simp [ha, blockPacket, dif_neg hp]
  -- the jump sequence and its block amplitudes
  set cn : ℕ → ℝ := fun i => if h : i < B then c ⟨i, h⟩ else 0 with hcn
  have hjump : ∀ s, s < B * k → blockJump B k c s = cn (s / k) := fun s hs => by
    have : s / k < B := (Nat.div_lt_iff_lt_mul hk).mpr hs
    simp [blockJump, hcn, this]
  have hBk : B * k ≤ S.card := by rw [hB]; exact hcard
  have hcnB : ∀ t ∈ range (B * k), cn (t / k) = blockJump B k c t :=
    fun t ht => (hjump t (mem_range.mp ht)).symm
  -- a Fin-indexed sum of a function of the index that vanishes past `B k`
  have hfin : ∀ g : ℕ → ℝ, (∑ t : Fin S.card, if (t : ℕ) < B * k then g t else 0) =
      ∑ t ∈ range (B * k), g t := by
    intro g
    rw [Fin.sum_univ_eq_sum_range (fun t => if t < B * k then g t else 0), ← sum_filter]
    congr 1
    ext t
    simp only [mem_filter, mem_range]
    omega
  -- energy: the cumulative sums at the block primes
  have henergy : (k : ℝ) * ((k : ℝ) ^ 2 - 1) / 12 * ∑ i ∈ range B, cn i ^ 2 ≤
      ∑ p ∈ S, primePacketJumpSum S a (p : ℕ) ^ 2 := by
    refine le_trans (sum_range_blockPartialSum_sq_ge B k cn) ?_
    rw [sum_eq_sum_orderEmbOfFin]
    calc ∑ t ∈ range (B * k), (∑ s ∈ range (t + 1), cn (s / k)) ^ 2
        = ∑ t : Fin S.card, if (t : ℕ) < B * k then
            (∑ s ∈ range ((t : ℕ) + 1), cn (s / k)) ^ 2 else 0 := (hfin _).symm
      _ ≤ ∑ t : Fin S.card,
            primePacketJumpSum S a ((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) ^ 2 := by
          refine sum_le_sum fun t _ => ?_
          split_ifs with ht
          · rw [ha, primePacketJumpSum_blockPacket S B k c t ht]
            refine le_of_eq (congrArg (· ^ 2) (sum_congr rfl fun s hs => ?_))
            exact hcnB s (mem_range.mpr (by have := mem_range.mp hs; omega))
          · exact sq_nonneg _
  -- diagonal: `Σ p a_p² ≤ (k/P) Σ c_i²`
  have hdiag : ∑ p ∈ S, ((p : ℕ) : ℝ) * a p ^ 2 ≤ (k : ℝ) / P * ∑ i ∈ range B, cn i ^ 2 := by
    have hblocks : ∑ t ∈ range (B * k), cn (t / k) ^ 2 = (k : ℝ) * ∑ i ∈ range B, cn i ^ 2 := by
      induction B with
      | zero => simp
      | succ B ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
        congr 1
        rw [sum_congr rfl fun v hv => by
          rw [show B * k + v = v + B * k by ring, Nat.add_mul_div_right _ _ hk,
            Nat.div_eq_of_lt (mem_range.mp hv), zero_add], sum_const, card_range, nsmul_eq_mul]
    rw [sum_eq_sum_orderEmbOfFin, show (k : ℝ) / P * ∑ i ∈ range B, cn i ^ 2 =
        ∑ t ∈ range (B * k), cn (t / k) ^ 2 / P by rw [← sum_div, hblocks]; ring]
    calc ∑ t : Fin S.card, (((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) : ℝ) *
          a (S.orderEmbOfFin rfl t) ^ 2
        ≤ ∑ t : Fin S.card, if (t : ℕ) < B * k then cn ((t : ℕ) / k) ^ 2 / P else 0 := by
          refine sum_le_sum fun t _ => ?_
          rw [ha, blockPacket_orderEmbOfFin]
          have hmem := hS _ (S.orderEmbOfFin_mem rfl t)
          have hp : (P : ℝ) < ((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) := by
            exact_mod_cast hmem.1
          have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
          split_ifs with ht
          · rw [hjump t ht, div_pow, mul_div_assoc', show
                (((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) : ℝ) * cn ((t : ℕ) / k) ^ 2 /
                  (((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) : ℝ) ^ 2 =
                cn ((t : ℕ) / k) ^ 2 / ((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) by
                field_simp]
            exact div_le_div_of_nonneg_left (sq_nonneg _) hP0 hp.le
          · simp
      _ = ∑ t ∈ range (B * k), cn (t / k) ^ 2 / P := hfin fun t => cn (t / k) ^ 2 / P
  -- nondegeneracy
  have hpos : 0 < ∑ p ∈ S, ((p : ℕ) : ℝ) * a p ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      exact hc0 (funext fun i => not_not.mp (not_exists.mp h i))
    have hik : (i : ℕ) * k < S.card := lt_of_lt_of_le
      (by nlinarith [i.isLt] : (i : ℕ) * k < B * k) hBk
    set t : Fin S.card := ⟨(i : ℕ) * k, hik⟩
    have ht : (t : ℕ) < B * k := by simp only [t]; nlinarith [i.isLt]
    have hat : a (S.orderEmbOfFin rfl t) ≠ 0 := by
      rw [ha, blockPacket_orderEmbOfFin, if_pos ht, hjump _ ht]
      have hp : (0 : ℝ) < ((S.orderEmbOfFin rfl t : Nat.Primes) : ℕ) := by
        exact_mod_cast (S.orderEmbOfFin rfl t).property.pos
      refine div_ne_zero ?_ hp.ne'
      simp only [t, hcn, Nat.mul_div_cancel _ hk, dif_pos i.isLt]
      exact hi
    rw [sum_eq_sum_orderEmbOfFin]
    refine sum_pos' (fun s _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      ⟨t, mem_univ _, mul_pos (by exact_mod_cast (S.orderEmbOfFin rfl t).property.pos)
        (pow_pos (abs_pos.mpr hat) 2 |>.trans_eq (sq_abs _))⟩
  refine ⟨a, hsupp, hφ, hA, hL, hpos, ?_⟩
  have hbil := sum_primePacketJumpSum_sq_le_primePacketBilinear S a hS hA hL
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hk1 : (0 : ℝ) ≤ (k : ℝ) ^ 2 - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hden : (0 : ℝ) < (2 * P : ℝ) * (2 * P + 1) := by positivity
  calc ((k : ℝ) ^ 2 - 1) / (24 * (2 * P + 1)) * ∑ p ∈ S, ((p : ℕ) : ℝ) * a p ^ 2
      ≤ ((k : ℝ) ^ 2 - 1) / (24 * (2 * P + 1)) * ((k : ℝ) / P * ∑ i ∈ range B, cn i ^ 2) :=
        mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = (k : ℝ) * ((k : ℝ) ^ 2 - 1) / 12 * (∑ i ∈ range B, cn i ^ 2) /
          ((2 * P : ℝ) * (2 * P + 1)) := by
        field_simp
        ring
    _ ≤ (∑ p ∈ S, primePacketJumpSum S a (p : ℕ) ^ 2) / ((2 * P : ℝ) * (2 * P + 1)) :=
        div_le_div_of_nonneg_right henergy hden.le
    _ ≤ primePacketBilinear S S a a := hbil

end

end GaloisForLFunctions.BezoutValuationIncidence
