import GaloisForLFunctions.ArithmeticOrientationTheory.PrimePowerSumsRegroupByTowers
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-!
# The ratio part decomposes over cosets

The ratio correlation of a profile at a prime power `p^k`, `R_q(p^k) = Σ_a q(a) q(a p^k)`, pairs
every integer with its `p^k`-fold dilate.  Writing `a = p^i a'` with `a'` prime to `p` (the
`p`-free part `ordCompl[p] a`), the pairs sort into **cosets**: for each `p`-free `a'` the tower
`{p^i a'}` is paired with itself by the shift `i ↦ i + k`
(`ratioCorr_prime_pow_eq_sum_cosets`).  So the ratio part of the tower of `p` is a sum over
cosets of one-sided Toeplitz forms in the tower coordinate (`towerRatioPart_eq_sum_cosets`),
while the product part lives on the unit coset alone and is rank one
(`sum_vonMangoldt_productCorr_prime_pow`).

**The coset law** (`towerOddPrimeSide_eq`): the odd prime side of the tower of `p` is

    log p · ( 2 Σ_{a' p-free} Toeplitz_p(q|_{a'}) − (S_p(q)² − q(1)²) ).

This is the orientation-sensitive decomposition the field asked for: the difference
correlations couple the whole profile coset by coset through a Toeplitz form with kernel
`p^{−k/2}`, the sum correlations are one Hankel square on the unit coset.
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### The `p`-free part -/

/-- The `p`-free part of `a`: `a / p^{v_p(a)}`. -/
def pfreePart (p a : ℕ) : ℕ := a / p ^ a.factorization p

theorem pfreePart_mul_pow (p : ℕ) (a : ℕ) : p ^ a.factorization p * pfreePart p a = a :=
  Nat.ordProj_mul_ordCompl_eq_self a p

theorem not_dvd_pfreePart {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : a ≠ 0) : ¬ p ∣ pfreePart p a :=
  Nat.not_dvd_ordCompl hp ha

theorem pfreePart_pos {p : ℕ} {a : ℕ} (ha : a ≠ 0) : 0 < pfreePart p a :=
  Nat.ordCompl_pos p ha

theorem pfreePart_le (p a : ℕ) : pfreePart p a ≤ a := Nat.ordCompl_le a p

/-- The valuation of `p^i a'` with `p ∤ a'` is `i`. -/
theorem factorization_pow_mul {p : ℕ} (hp : p.Prime) (i : ℕ) {a' : ℕ} (ha' : ¬ p ∣ a')
    (ha0 : a' ≠ 0) : (p ^ i * a').factorization p = i := by
  rw [Nat.factorization_mul (pow_ne_zero i hp.ne_zero) ha0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd ha']
  simp

/-- The `p`-free part of `p^i a'` with `p ∤ a'` is `a'`. -/
theorem pfreePart_pow_mul {p : ℕ} (hp : p.Prime) (i : ℕ) {a' : ℕ} (ha' : ¬ p ∣ a')
    (ha0 : a' ≠ 0) : pfreePart p (p ^ i * a') = a' := by
  unfold pfreePart
  rw [factorization_pow_mul hp i ha' ha0, Nat.mul_div_cancel_left _ (pow_pos hp.pos i)]

/-! ### Cosets of the dilation -/

/-- The `p`-free integers in `[1, X]`: the coset labels. -/
def pfreeLabels (p X : ℕ) : Finset ℕ := (Icc 1 X).filter fun a' => ¬ p ∣ a'

theorem pfreePart_mem_pfreeLabels {p : ℕ} (hp : p.Prime) {X a : ℕ} (ha : a ∈ Icc 1 X) :
    pfreePart p a ∈ pfreeLabels p X := by
  simp only [pfreeLabels, mem_filter, mem_Icc] at ha ⊢
  have ha0 : a ≠ 0 := by omega
  exact ⟨⟨pfreePart_pos ha0, (pfreePart_le p a).trans ha.2⟩, not_dvd_pfreePart hp ha0⟩

/-- The fibre of the `p`-free part over `a'` is the tower `{p^i a' ≤ X}`. -/
theorem fiber_pfreePart_eq_image {p : ℕ} (hp : p.Prime) {X a' : ℕ} (ha' : a' ∈ pfreeLabels p X) :
    (Icc 1 X).filter (fun a => pfreePart p a = a') =
      ((range (Nat.log p X + 1)).filter fun i => p ^ i * a' ≤ X).image (fun i => p ^ i * a') := by
  simp only [pfreeLabels, mem_filter, mem_Icc] at ha'
  obtain ⟨⟨ha1, haX⟩, hpa⟩ := ha'
  have ha0 : a' ≠ 0 := by omega
  ext a
  simp only [mem_filter, mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨⟨h1, hX⟩, hpf⟩
    refine ⟨a.factorization p, ⟨Nat.lt_succ_of_le ?_, ?_⟩, ?_⟩
    · apply Nat.le_log_of_pow_le hp.one_lt
      calc p ^ a.factorization p ≤ p ^ a.factorization p * pfreePart p a :=
            Nat.le_mul_of_pos_right _ (pfreePart_pos (by omega))
        _ = a := pfreePart_mul_pow p a
        _ ≤ X := hX
    · rw [← hpf, pfreePart_mul_pow]; exact hX
    · rw [← hpf, pfreePart_mul_pow]
  · rintro ⟨i, ⟨-, hiX⟩, rfl⟩
    refine ⟨⟨?_, hiX⟩, pfreePart_pow_mul hp i hpa ha0⟩
    exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero i hp.ne_zero) ha0)

/-- **Coset decomposition of the ratio correlation at a prime power.**  For a profile supported
on `[1, X]`, `R_q(p^k) = Σ_{a' p-free} Σ_i q(p^i a') q(p^{i+k} a')`. -/
theorem ratioCorr_prime_pow_eq_sum_cosets (q : ℕ → ℝ) {X : ℕ} (hq : ∀ n, X < n → q n = 0)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ratioCorr q X (p ^ k) =
      ∑ a' ∈ pfreeLabels p X, ∑ i ∈ range (Nat.log p X + 1),
        q (p ^ i * a') * q (p ^ (i + k) * a') := by
  unfold ratioCorr
  rw [← sum_fiberwise_of_maps_to (g := pfreePart p) (t := pfreeLabels p X)
    (fun a ha => pfreePart_mem_pfreeLabels hp ha)]
  refine sum_congr rfl fun a' ha' => ?_
  rw [fiber_pfreePart_eq_image hp ha']
  have ha0 : a' ≠ 0 := by
    simp only [pfreeLabels, mem_filter, mem_Icc] at ha'
    omega
  have hinj : ∀ i ∈ (range (Nat.log p X + 1)).filter (fun i => p ^ i * a' ≤ X),
      ∀ j ∈ (range (Nat.log p X + 1)).filter (fun i => p ^ i * a' ≤ X),
      p ^ i * a' = p ^ j * a' → i = j := fun i _ j _ h =>
    Nat.pow_right_injective hp.two_le (mul_left_injective₀ ha0 h)
  rw [sum_image hinj, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with h
  · ring_nf
  · rw [hq _ (lt_of_not_ge h), zero_mul]

/-! ### The coset law for the tower -/

/-- The one-sided Toeplitz form of the coset `a'` in the tower of `p`, with kernel `p^{−k/2}`:
`Σ_{1 ≤ k ≤ L} p^{−k/2} Σ_i q(p^i a') q(p^{i+k} a')`. -/
def cosetToeplitz (q : ℕ → ℝ) (p X L : ℕ) (a' : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 L, (p : ℝ) ^ (-(k : ℝ) / 2) *
    ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') * q (p ^ (i + k) * a')

/-- The ratio part of the tower of `p`, through `p^L`. -/
def towerRatioPart (q : ℕ → ℝ) (X p L : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 L, Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ratioCorr q X (p ^ k)

theorem rpow_pow_neg_half {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (p : ℝ) ^ (-(k : ℝ) / 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  congr 1
  ring

/-- **The ratio part of a tower is a sum of coset Toeplitz forms.** -/
theorem towerRatioPart_eq_sum_cosets (q : ℕ → ℝ) {X : ℕ} (hq : ∀ n, X < n → q n = 0)
    {p : ℕ} (hp : p.Prime) (L : ℕ) :
    towerRatioPart q X p L = Real.log p * ∑ a' ∈ pfreeLabels p X, cosetToeplitz q p X L a' := by
  unfold towerRatioPart cosetToeplitz
  have hL : ∀ k ∈ Icc 1 L, Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ratioCorr q X (p ^ k)
      = ∑ a' ∈ pfreeLabels p X, Real.log p * ((p : ℝ) ^ (-(k : ℝ) / 2) *
          ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') * q (p ^ (i + k) * a')) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, rpow_pow_neg_half hp,
      ratioCorr_prime_pow_eq_sum_cosets q hq hp k, mul_sum]
    refine sum_congr rfl fun a' _ => ?_
    ring
  rw [sum_congr rfl hL, sum_comm]
  simp only [mul_sum]

/-- The odd prime side of the tower of `p` through `p^{2K}`. -/
def towerOddPrimeSide (q : ℕ → ℝ) (X p K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (2 * K), Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
    (2 * ratioCorr q X (p ^ k) - productCorr q (p ^ k))

/-- The product part over `Icc 1 (2K)` is the tower product part. -/
theorem sum_Icc_productCorr_eq_towerProductPart (q : ℕ → ℝ) {p : ℕ} (K : ℕ) :
    ∑ k ∈ Icc 1 (2 * K), Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k) =
      towerProductPart q p K := by
  unfold towerProductPart
  symm
  rw [sum_range_succ_eq_sum_Icc]
  simp [vonMangoldt_apply_one]

/-- **The coset law**: the odd prime side of a tower is twice the coset Toeplitz forms minus the
rank-one square, up to the pole-like term. -/
theorem towerOddPrimeSide_eq (q : ℕ → ℝ) {X : ℕ} (hq : ∀ n, X < n → q n = 0) {p : ℕ}
    (hp : p.Prime) {K : ℕ} (hK : ∀ i, K < i → q (p ^ i) = 0) :
    towerOddPrimeSide q X p K =
      Real.log p * (2 * ∑ a' ∈ pfreeLabels p X, cosetToeplitz q p X (2 * K) a' -
        (towerMellin q p K ^ 2 - q 1 ^ 2)) := by
  have hsplit : towerOddPrimeSide q X p K = 2 * towerRatioPart q X p (2 * K) -
      ∑ k ∈ Icc 1 (2 * K), Λ (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k) := by
    unfold towerOddPrimeSide towerRatioPart
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hsplit, sum_Icc_productCorr_eq_towerProductPart, sum_vonMangoldt_productCorr_prime_pow q hp hK,
    towerRatioPart_eq_sum_cosets q hq hp]
  ring

end

end GaloisForLFunctions.ArithmeticOrientationTheory
