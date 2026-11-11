import GaloisForLFunctions.LogarithmicChowla.EntropyDecrement
import GaloisForLFunctions.LogarithmicChowla.ResidueHoeffding

/-!
# Deviations of the prime-shift weights

At scale `k` the primes `𝐏_k ⊂ (2^k, 2^{k+1}]` (`primesAt`), their product `P_k` (`primeProd`), the
product `Q_k = Π_{j<k} P_j` of the earlier scales (`earlierProd`, coprime to `P_k`), the block length
`H_k = 2^{k+1}(h+2)` (`blockLen`, `H_{k+1} = 2H_k`) and the window `N_k = 2^{k+2}` (`winLen`).

For a sign block `x` of length `H_k` and a residue `y mod p`,

`W_p(x, y) = N⁻¹ Σ_{j<N} (p·1[y + j ≡ 0] − 1) x_j x_{j+ph}` (`shiftDev`),

all positions lying inside the block. It has mean zero over `y mod p` (`sum_shiftDev`) and
`|W_p| ≤ 5/2` (`abs_shiftDev_le`): among `N` consecutive integers at most `N/p + 1` lie in one
class, and `p ≤ N/2`. The average `Z = |𝐏_k|⁻¹ Σ_p W_p(x, y_p)` (`devAvg`) is therefore
concentrated: by Hoeffding on `ZMod P_k ≃ Π_p ZMod p`, at most `2 exp(−2ε²|𝐏_k|/25) P_k` residues
`y mod P_k` have `|Z| ≥ ε` (`card_devAvg_ge_le`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Real

noncomputable section

/-- The primes of `(2^k, 2^{k+1}]`. -/
def primesAt (k : ℕ) : Finset ℕ := (Ioc (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime

theorem prime_of_mem_primesAt {k p : ℕ} (hp : p ∈ primesAt k) : p.Prime := (mem_filter.mp hp).2

theorem lt_of_mem_primesAt {k p : ℕ} (hp : p ∈ primesAt k) : 2 ^ k < p :=
  (mem_Ioc.mp (mem_filter.mp hp).1).1

theorem le_of_mem_primesAt {k p : ℕ} (hp : p ∈ primesAt k) : p ≤ 2 ^ (k + 1) :=
  (mem_Ioc.mp (mem_filter.mp hp).1).2

instance (k : ℕ) (p : primesAt k) : NeZero (p : ℕ) := ⟨(prime_of_mem_primesAt p.2).ne_zero⟩

/-- Bertrand: every scale has a prime. -/
theorem card_primesAt_pos (k : ℕ) : 0 < (primesAt k).card := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k) (by positivity)
  refine card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlt, ?_⟩, hp⟩⟩
  rw [pow_succ]
  linarith

/-- `P_k = Π_{p ∈ 𝐏_k} p`. -/
def primeProd (k : ℕ) : ℕ := ∏ p : primesAt k, (p : ℕ)

theorem primeProd_pos (k : ℕ) : 0 < primeProd k :=
  prod_pos fun p _ => (prime_of_mem_primesAt p.2).pos

instance (k : ℕ) : NeZero (primeProd k) := ⟨(primeProd_pos k).ne'⟩

/-- `Q_k = Π_{j<k} P_j`. -/
def earlierProd (k : ℕ) : ℕ := ∏ j ∈ range k, primeProd j

instance (k : ℕ) : NeZero (earlierProd k) :=
  ⟨(prod_pos fun j _ => primeProd_pos j).ne'⟩

theorem earlierProd_succ (k : ℕ) : earlierProd (k + 1) = earlierProd k * primeProd k :=
  prod_range_succ _ _

theorem coprime_earlierProd_primeProd (k : ℕ) : (earlierProd k).Coprime (primeProd k) := by
  refine Nat.Coprime.prod_left fun j hj => Nat.Coprime.prod_left fun p _ =>
    Nat.Coprime.prod_right fun q _ => ?_
  have hjk : j < k := mem_range.mp hj
  refine (Nat.coprime_primes (prime_of_mem_primesAt p.2) (prime_of_mem_primesAt q.2)).mpr ?_
  have h1 := le_of_mem_primesAt p.2
  have h2 := lt_of_mem_primesAt q.2
  have h3 : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
  omega

theorem pairwise_coprime_primesAt (k : ℕ) :
    Pairwise (Function.onFun Nat.Coprime fun p : primesAt k => (p : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (prime_of_mem_primesAt p.2) (prime_of_mem_primesAt q.2)).mpr
    fun h => hpq (Subtype.ext h)

/-- The Chinese remainder theorem at scale `k`. -/
def crtAt (k : ℕ) : ZMod (primeProd k) ≃+* ∀ p : primesAt k, ZMod (p : ℕ) :=
  ZMod.prodEquivPi (fun p : primesAt k => (p : ℕ)) (pairwise_coprime_primesAt k)

theorem crtAt_natCast (k n : ℕ) (p : primesAt k) :
    crtAt k (n : ZMod (primeProd k)) p = (n : ZMod (p : ℕ)) := by
  rw [map_natCast]
  rfl

/-- `H_k = 2^{k+1}(h+2)`. -/
def blockLen (h k : ℕ) : ℕ := 2 ^ (k + 1) * (h + 2)

theorem blockLen_pos (h k : ℕ) : 0 < blockLen h k := by
  unfold blockLen
  positivity

theorem blockLen_succ (h k : ℕ) : blockLen h (k + 1) = blockLen h k + blockLen h k := by
  unfold blockLen
  ring

/-- `N_k = 2^{k+2}`. -/
def winLen (k : ℕ) : ℕ := 2 ^ (k + 2)

theorem winLen_pos (k : ℕ) : 0 < winLen k := by
  unfold winLen
  positivity

/-- Positions `j + ph` with `j < N_k`, `p ∈ 𝐏_k` lie in the block. -/
theorem add_mul_lt_blockLen {h k p j : ℕ} (hp : p ∈ primesAt k) (hj : j < winLen k) :
    j + p * h < blockLen h k := by
  have h1 := le_of_mem_primesAt hp
  have h2 : p * h ≤ 2 ^ (k + 1) * h := Nat.mul_le_mul_right h h1
  unfold winLen at hj
  unfold blockLen
  have : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := by ring
  nlinarith

/-- Signs read off a block, `0` outside it. -/
def sv {H : ℕ} (x : Fin H → Bool) (i : ℕ) : ℝ := if hi : i < H then toSign (x ⟨i, hi⟩) else 0

theorem abs_sv_le {H : ℕ} (x : Fin H → Bool) (i : ℕ) : |sv x i| ≤ 1 := by
  unfold sv
  split_ifs
  · rw [abs_toSign]
  · simp

theorem sv_blk {H n i : ℕ} (hn : n ≠ 0) (hi : i < H) : sv (blk H n) i = lam (n + i) := by
  simp only [sv, hi, dite_true, blk]
  exact toSign_sgn (by omega)

/-- `W_p(x, y) = N⁻¹ Σ_{j<N} (p·1[y + j ≡ 0] − 1) x_j x_{j+ph}`. -/
def shiftDev (h k p : ℕ) (x : Fin (blockLen h k) → Bool) (y : ZMod p) : ℝ :=
  (∑ j ∈ range (winLen k),
      ((if y + (j : ZMod p) = 0 then (p : ℝ) else 0) - 1) * (sv x j * sv x (j + p * h)))
    / winLen k

/-- Among `N` consecutive integers at most `N/p + 1` lie in a residue class. -/
theorem card_filter_range_natCast_eq_le (p N : ℕ) [NeZero p] (c : ZMod p) :
    ((range N).filter fun j : ℕ => (j : ZMod p) = c).card ≤ N / p + 1 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [← card_range (N / p + 1)]
  refine card_le_card_of_injOn (fun j => j / p) ?_ ?_
  · intro j hj
    have hjN := mem_range.mp (mem_filter.mp hj).1
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hjN.le)
  · intro a ha b hb hab
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    have hmod : a % p = b % p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      rw [ha', hb']
    have hdiv : a / p = b / p := hab
    rw [← Nat.div_add_mod a p, ← Nat.div_add_mod b p, hdiv, hmod]

theorem abs_shiftDev_le {h k p : ℕ} (hp : p ∈ primesAt k) (x : Fin (blockLen h k) → Bool)
    (y : ZMod p) : |shiftDev h k p x y| ≤ 5 / 2 := by
  haveI : NeZero p := ⟨(prime_of_mem_primesAt hp).ne_zero⟩
  have hN : (0 : ℝ) < winLen k := by exact_mod_cast winLen_pos k
  have hpN : (p : ℝ) ≤ winLen k / 2 := by
    have h1 := le_of_mem_primesAt hp
    have : (p : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast h1
    unfold winLen
    push_cast
    rw [pow_succ 2 (k + 1)]
    linarith
  set N := winLen k with hNdef
  have hcount : ((range N).filter fun j : ℕ => y + (j : ZMod p) = 0).card ≤ N / p + 1 := by
    have : ((range N).filter fun j : ℕ => y + (j : ZMod p) = 0)
        = (range N).filter fun j : ℕ => (j : ZMod p) = -y := by
      ext j
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2, add_neg_cancel]⟩
    rw [this]
    exact card_filter_range_natCast_eq_le p N (-y)
  have hpcount : (p : ℝ) * (((range N).filter fun j : ℕ => y + (j : ZMod p) = 0).card : ℝ)
      ≤ N + p := by
    have h1 : (((range N).filter fun j : ℕ => y + (j : ZMod p) = 0).card : ℝ) ≤ (N / p : ℕ) + 1 := by
      exact_mod_cast hcount
    have h2 : (p : ℝ) * ((N / p : ℕ) : ℝ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N p
    nlinarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hsum : |∑ j ∈ range N, ((if y + (j : ZMod p) = 0 then (p : ℝ) else 0) - 1)
      * (sv x j * sv x (j + p * h))| ≤ 2 * N + p := by
    calc |∑ j ∈ range N, ((if y + (j : ZMod p) = 0 then (p : ℝ) else 0) - 1)
          * (sv x j * sv x (j + p * h))|
        ≤ ∑ j ∈ range N, ((if y + (j : ZMod p) = 0 then (p : ℝ) else 0) + 1) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          have hb : |sv x j * sv x (j + p * h)| ≤ 1 := by
            rw [abs_mul]
            exact mul_le_one₀ (abs_sv_le x j) (abs_nonneg _) (abs_sv_le x _)
          have ha : |(if y + (j : ZMod p) = 0 then (p : ℝ) else 0) - 1|
              ≤ (if y + (j : ZMod p) = 0 then (p : ℝ) else 0) + 1 := by
            have : (0 : ℝ) ≤ if y + (j : ZMod p) = 0 then (p : ℝ) else 0 := by
              split_ifs <;> positivity
            rw [abs_le]
            constructor <;> linarith
          have hnn : (0 : ℝ) ≤ (if y + (j : ZMod p) = 0 then (p : ℝ) else 0) + 1 := by
            split_ifs <;> positivity
          calc |(if y + (j : ZMod p) = 0 then (p : ℝ) else 0) - 1| * |sv x j * sv x (j + p * h)|
              ≤ ((if y + (j : ZMod p) = 0 then (p : ℝ) else 0) + 1) * 1 :=
                mul_le_mul ha hb (abs_nonneg _) hnn
            _ = _ := mul_one _
      _ = (p : ℝ) * (((range N).filter fun j : ℕ => y + (j : ZMod p) = 0).card : ℝ) + N := by
          rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, sum_const, card_range,
            nsmul_eq_mul, mul_one, mul_comm]
      _ ≤ 2 * N + p := by linarith
  rw [shiftDev, abs_div, abs_of_pos hN, div_le_iff₀ hN]
  linarith

theorem sum_shiftDev {h k p : ℕ} [NeZero p] (x : Fin (blockLen h k) → Bool) :
    ∑ y : ZMod p, shiftDev h k p x y = 0 := by
  have hp : ∀ j : ℕ, ∑ y : ZMod p, (if y + (j : ZMod p) = 0 then (p : ℝ) else 0) = p := by
    intro j
    have : ∀ y : ZMod p, (y + (j : ZMod p) = 0) ↔ y = -(j : ZMod p) := fun y =>
      ⟨fun h => eq_neg_of_add_eq_zero_left h, fun h => by rw [h, neg_add_cancel]⟩
    simp only [this, sum_ite_eq', mem_univ, if_true]
  simp only [shiftDev, ← sum_div]
  rw [sum_comm]
  have : ∀ j ∈ range (winLen k), ∑ y : ZMod p, ((if y + (j : ZMod p) = 0 then (p : ℝ) else 0) - 1)
      * (sv x j * sv x (j + p * h)) = 0 := by
    intro j _
    rw [← sum_mul, sum_sub_distrib, hp j, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
      mul_one, sub_self, zero_mul]
  rw [sum_eq_zero this, zero_div]

/-- `Z(x, z) = |𝐏_k|⁻¹ Σ_p W_p(x, z_p)`. -/
def devAvg (h k : ℕ) (x : Fin (blockLen h k) → Bool) (z : ∀ p : primesAt k, ZMod (p : ℕ)) : ℝ :=
  (∑ p : primesAt k, shiftDev h k p x (z p)) / (primesAt k).card

theorem abs_devAvg_le (h k : ℕ) (x : Fin (blockLen h k) → Bool)
    (z : ∀ p : primesAt k, ZMod (p : ℕ)) : |devAvg h k x z| ≤ 5 / 2 := by
  have hc : (0 : ℝ) < (primesAt k).card := by exact_mod_cast card_primesAt_pos k
  rw [devAvg, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc |∑ p : primesAt k, shiftDev h k p x (z p)| ≤ ∑ p : primesAt k, |shiftDev h k p x (z p)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : primesAt k, (5 / 2 : ℝ) := sum_le_sum fun p _ => abs_shiftDev_le p.2 x _
    _ = 5 / 2 * (primesAt k).card := by
        rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]

/-- **Concentration of the deviation.** At most `2 exp(−2ε²|𝐏_k|/25) P_k` residues mod `P_k` have
`|Z| ≥ ε`. -/
theorem card_devAvg_ge_le (h k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (x : Fin (blockLen h k) → Bool) :
    ((univ.filter fun y : ZMod (primeProd k) => ε ≤ |devAvg h k x (crtAt k y)|).card : ℝ)
      ≤ 2 * exp (-(2 * ε ^ 2 * (primesAt k).card / 25)) * primeProd k := by
  have hc : (0 : ℝ) < (primesAt k).card := by exact_mod_cast card_primesAt_pos k
  have hcard : (univ.filter fun y : ZMod (primeProd k) => ε ≤ |devAvg h k x (crtAt k y)|).card
      = (univ.filter fun z : (∀ p : primesAt k, ZMod (p : ℕ)) =>
          ε * (primesAt k).card ≤ |∑ p : primesAt k, shiftDev h k p x (z p)|).card := by
    refine card_equiv (crtAt k).toEquiv fun y => ?_
    simp only [mem_filter, mem_univ, true_and, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    rw [devAvg, abs_div, abs_of_pos hc, le_div_iff₀ hc]
  rw [hcard]
  have hH := card_abs_sum_ge_le (Y := fun p : primesAt k => ZMod (p : ℕ))
    (fun p y => shiftDev h k p x y) (B := 5 / 2) (by norm_num)
    (fun p y => abs_shiftDev_le p.2 x y) (fun p => sum_shiftDev x)
    (t := ε * (primesAt k).card) (by positivity)
  have hpi : (Fintype.card (∀ p : primesAt k, ZMod (p : ℕ)) : ℝ) = primeProd k := by
    rw [Fintype.card_pi]
    simp [primeProd, ZMod.card]
  rw [hpi, Fintype.card_coe] at hH
  refine hH.trans (le_of_eq ?_)
  congr 3
  field_simp
  ring

end

end GaloisForLFunctions.LogarithmicChowla
