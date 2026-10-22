import GaloisForLFunctions.RHTower.Sieve.SeparatedCount
import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalPrimeChannelCrossBlockDecay

set_option autoImplicit false

/-!
# Separation of the ratios `n₁/n₂` with a fixed gcd

For `N < n₁, n₂ ≤ 2N` write `x(n₁, n₂) = log(n₁/n₂)`. Two distinct pairs with the same
`gcd = d` have different ratios (the reduced fraction determines the pair once the common factor
is fixed), and `d² | n₁m₂ − m₁n₂`, so

`|n₁/n₂ − m₁/m₂| ≥ d²/(4N²)`,   `|x(n₁,n₂) − x(m₁,m₂)| ≥ d²/(8N²)`.

Counting each gcd class in a window of length `2δ` (`Sieve.card_le_of_separated`) and summing
`Σ_{d ≤ D} (16δN²/d² + 1) ≤ D + 32δN²` (`Σ 1/d² ≤ 2`, corpus `sum_one_div_sq_le_two_div`):

`#{(n₁, n₂) : gcd(n₁, n₂) ≤ D, |u − log(n₁/n₂)| ≤ δ} ≤ D + 32 δ N²`

for every `u`. This is the counting step of Guth–Maynard Lemma 11.8 (the paper's "the fractions
`n₁'/n₂'` are `d²/N²`-separated").
-/

open Finset

namespace RHTower.GuthMaynard

noncomputable section

/-- The log-ratio `x(p) = log(p₁/p₂)`. -/
def logRatio (p : ℕ × ℕ) : ℝ := Real.log ((p.1 : ℝ) / p.2)

/-- Two pairs with the same gcd and the same ratio coincide. -/
theorem eq_of_mul_eq_mul_of_gcd_eq {n₁ n₂ m₁ m₂ : ℕ} (h₁ : 0 < n₁)
    (h : n₁ * m₂ = m₁ * n₂) (hg : Nat.gcd n₁ n₂ = Nat.gcd m₁ m₂) : n₁ = m₁ ∧ n₂ = m₂ := by
  set d := Nat.gcd n₁ n₂ with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ h₁
  have hdn₁ : d ∣ n₁ := Nat.gcd_dvd_left _ _
  have hdn₂ : d ∣ n₂ := Nat.gcd_dvd_right _ _
  have hdm₁ : d ∣ m₁ := hg ▸ Nat.gcd_dvd_left _ _
  have hdm₂ : d ∣ m₂ := hg ▸ Nat.gcd_dvd_right _ _
  obtain ⟨a, ha⟩ := hdn₁
  obtain ⟨b, hb⟩ := hdn₂
  obtain ⟨c, hc⟩ := hdm₁
  obtain ⟨e, he⟩ := hdm₂
  have hab : Nat.Coprime a b := by
    have := Nat.coprime_div_gcd_div_gcd (m := n₁) (n := n₂) hd0
    rw [← hd, ha, hb, Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
    exact this
  have hce : Nat.Coprime c e := by
    have hd0' : 0 < Nat.gcd m₁ m₂ := hg ▸ hd0
    have := Nat.coprime_div_gcd_div_gcd (m := m₁) (n := m₂) hd0'
    rw [← hg, hc, he, Nat.mul_div_cancel_left _ hd0, Nat.mul_div_cancel_left _ hd0] at this
    exact this
  have hae : a * e = c * b := by
    have : d * d * (a * e) = d * d * (c * b) := by
      have := h; rw [ha, hb, hc, he] at this; linarith [this]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hac : a ∣ c := hab.dvd_of_dvd_mul_right ⟨e, by rw [hae]⟩
  have hca : c ∣ a := hce.dvd_of_dvd_mul_right ⟨b, by rw [← hae]⟩
  have hac' : a = c := Nat.dvd_antisymm hac hca
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, mul_zero] at ha; omega
    · exact h0
  have hbe : b = e := by
    rw [hac'] at hae
    exact (Nat.eq_of_mul_eq_mul_left (hac' ▸ ha0) hae).symm
  exact ⟨by rw [ha, hc, hac'], by rw [hb, he, hbe]⟩

/-- `|log x − log y| ≥ |x − y|/2` for `0 < x, y ≤ 2` (from corpus `Sieve.div_le_log_sub`). -/
theorem abs_sub_div_two_le_abs_log_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx2 : x ≤ 2)
    (hy2 : y ≤ 2) : |x - y| / 2 ≤ |Real.log x - Real.log y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm (Real.log x)]
    exact this hy hx hy2 hx2 (le_of_not_ge hxy)
  have h := Sieve.div_le_log_sub hx hxy
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [Real.log_le_log hx hxy])]
  have h2 : (y - x) / 2 ≤ (y - x) / y := div_le_div_of_nonneg_left (by linarith) hy hy2
  linarith

/-- **Separation within a gcd class.** For distinct `p, q ∈ (N, 2N]²` with `gcd p = gcd q = d`:
`|log(p₁/p₂) − log(q₁/q₂)| ≥ d²/(8N²)`. -/
theorem le_abs_logRatio_sub {N : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N))
    (hq : q ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)) (hne : p ≠ q)
    (hg : Nat.gcd p.1 p.2 = Nat.gcd q.1 q.2) :
    ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) ≤ |logRatio p - logRatio q| := by
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  obtain ⟨hq1, hq2⟩ := mem_product.mp hq
  obtain ⟨a1, b1⟩ := mem_Ioc.mp hp1
  obtain ⟨a2, b2⟩ := mem_Ioc.mp hp2
  obtain ⟨a3, b3⟩ := mem_Ioc.mp hq1
  obtain ⟨a4, b4⟩ := mem_Ioc.mp hq2
  set d := Nat.gcd p.1 p.2
  have hN : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- the cross term is a nonzero multiple of `d²`
  have hcross : (p.1 : ℤ) * q.2 - q.1 * p.2 ≠ 0 := by
    intro h0
    have h' : p.1 * q.2 = q.1 * p.2 := by
      have : (p.1 : ℤ) * q.2 = q.1 * p.2 := by linarith
      exact_mod_cast this
    obtain ⟨e1, e2⟩ := eq_of_mul_eq_mul_of_gcd_eq (by omega) h' hg
    exact hne (Prod.ext e1 e2)
  have hdvd : ((d : ℤ) ^ 2) ∣ (p.1 : ℤ) * q.2 - q.1 * p.2 := by
    have d1 : (d : ℤ) ∣ p.1 := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    have d2 : (d : ℤ) ∣ p.2 := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    have d3 : (d : ℤ) ∣ q.1 := Int.natCast_dvd_natCast.mpr (hg ▸ Nat.gcd_dvd_left _ _)
    have d4 : (d : ℤ) ∣ q.2 := Int.natCast_dvd_natCast.mpr (hg ▸ Nat.gcd_dvd_right _ _)
    rw [sq]
    exact dvd_sub (mul_dvd_mul d1 d4) (mul_dvd_mul d3 d2)
  have hge : (d : ℝ) ^ 2 ≤ |(p.1 : ℝ) * q.2 - q.1 * p.2| := by
    have h1 := Int.natAbs_le_of_dvd_ne_zero hdvd hcross
    have h2 : ((d : ℤ) ^ 2).natAbs = d ^ 2 := by simp [Int.natAbs_pow]
    rw [h2] at h1
    have h3 : ((d ^ 2 : ℕ) : ℝ) ≤ (((p.1 : ℤ) * q.2 - q.1 * p.2).natAbs : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_natAbs, Int.cast_abs] at h3
    push_cast at h3
    exact h3
  -- ratios in `(1/2, 2)`
  have hp1r : (0 : ℝ) < p.1 := by exact_mod_cast (show 0 < p.1 by omega)
  have hp2r : (0 : ℝ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
  have hq1r : (0 : ℝ) < q.1 := by exact_mod_cast (show 0 < q.1 by omega)
  have hq2r : (0 : ℝ) < q.2 := by exact_mod_cast (show 0 < q.2 by omega)
  have hp2N : (p.2 : ℝ) ≤ 2 * N := by exact_mod_cast b2
  have hq2N : (q.2 : ℝ) ≤ 2 * N := by exact_mod_cast b4
  have hp1N : (p.1 : ℝ) ≤ 2 * N := by exact_mod_cast b1
  have hq1N : (q.1 : ℝ) ≤ 2 * N := by exact_mod_cast b3
  have hNp2 : (N : ℝ) ≤ p.2 := by exact_mod_cast a2.le
  have hNq2 : (N : ℝ) ≤ q.2 := by exact_mod_cast a4.le
  have hrp : (p.1 : ℝ) / p.2 ≤ 2 := by rw [div_le_iff₀ hp2r]; linarith
  have hrq : (q.1 : ℝ) / q.2 ≤ 2 := by rw [div_le_iff₀ hq2r]; linarith
  have hdiff : (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) ≤ |(p.1 : ℝ) / p.2 - q.1 / q.2| := by
    have e : (p.1 : ℝ) / p.2 - q.1 / q.2 = ((p.1 : ℝ) * q.2 - q.1 * p.2) / (p.2 * q.2) := by
      field_simp
    rw [e, abs_div, abs_of_pos (show (0 : ℝ) < p.2 * q.2 by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hpq : (p.2 : ℝ) * q.2 ≤ 4 * (N : ℝ) ^ 2 := by nlinarith
    calc (d : ℝ) ^ 2 * (p.2 * q.2) ≤ (d : ℝ) ^ 2 * (4 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hpq (by positivity)
      _ ≤ |(p.1 : ℝ) * q.2 - q.1 * p.2| * (4 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hge (by positivity)
  have hlog := abs_sub_div_two_le_abs_log_sub (div_pos hp1r hp2r) (div_pos hq1r hq2r) hrp hrq
  unfold logRatio
  calc (d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) = (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) / 2 := by
        field_simp; ring
    _ ≤ |(p.1 : ℝ) / p.2 - q.1 / q.2| / 2 := by gcongr
    _ ≤ _ := hlog

/-- **Counting the small-gcd pairs near a point.** For `N ≥ 1`, `D, δ ≥ 0` and every `u`:
`#{(n₁, n₂) ∈ (N, 2N]² : gcd ≤ D, |u − log(n₁/n₂)| ≤ δ} ≤ D + 32 δ N²`. -/
theorem card_smallGcd_near_le {N : ℕ} (hN : 1 ≤ N) {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ) (u : ℝ) :
    ((((Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        fun p => ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D).filter
          fun p => |u - logRatio p| ≤ δ).card : ℝ) ≤ D + 32 * δ * (N : ℝ) ^ 2 := by
  classical
  set P := Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)
  set F := (P.filter fun p => ((Nat.gcd p.1 p.2 : ℕ) : ℝ) ≤ D).filter
    fun p => |u - logRatio p| ≤ δ
  set Fd : ℕ → Finset (ℕ × ℕ) := fun d => F.filter fun p => Nat.gcd p.1 p.2 = d
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcover : F ⊆ (Finset.Icc 1 ⌊D⌋₊).biUnion Fd := by
    intro p hp
    have hpF := hp
    obtain ⟨hp', -⟩ := mem_filter.mp hp
    obtain ⟨hpP, hpD⟩ := mem_filter.mp hp'
    obtain ⟨hp1, -⟩ := mem_product.mp hpP
    have hp0 : 0 < p.1 := by have := (mem_Ioc.mp hp1).1; omega
    refine mem_biUnion.mpr ⟨Nat.gcd p.1 p.2, mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ hp0,
      Nat.le_floor hpD⟩, mem_filter.mpr ⟨hpF, rfl⟩⟩
  have hclass : ∀ d ∈ Finset.Icc 1 ⌊D⌋₊,
      ((Fd d).card : ℝ) ≤ 16 * δ * (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) + 1 := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Icc.mp hd).1
    have hg : (0 : ℝ) < (d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) := by positivity
    have h := Sieve.card_le_of_separated (s := Fd d) (u := logRatio) (L := 2 * δ) (c := u - δ) hg
      (by positivity)
      (fun p hp q hq hne => by
        obtain ⟨hpF, hpd⟩ := mem_filter.mp hp
        obtain ⟨hqF, hqd⟩ := mem_filter.mp hq
        have hpP := (mem_filter.mp (mem_filter.mp hpF).1).1
        have hqP := (mem_filter.mp (mem_filter.mp hqF).1).1
        have := le_abs_logRatio_sub hpP hqP hne (hpd.trans hqd.symm)
        rwa [hpd] at this)
      (fun p hp => by
        have := abs_le.mp ((mem_filter.mp (mem_filter.mp hp).1).2)
        constructor <;> linarith [this.1, this.2])
    calc ((Fd d).card : ℝ) ≤ 2 * δ / ((d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2)) + 1 := h
      _ = 16 * δ * (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) + 1 := by field_simp; ring
  have hsum2 := GaloisForLFunctions.ArithmeticPositivityTheory.sum_one_div_sq_le_two_div
    (Finset.Icc 1 ⌊D⌋₊) (X := 1) one_pos (fun r hr => by exact_mod_cast (mem_Icc.mp hr).1)
  have hfloor : ((Finset.Icc 1 ⌊D⌋₊).card : ℝ) ≤ D := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    exact Nat.floor_le hD
  calc (F.card : ℝ) ≤ ((Finset.Icc 1 ⌊D⌋₊).biUnion Fd).card := by
        exact_mod_cast card_le_card hcover
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, ((Fd d).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (16 * δ * (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) + 1) :=
        sum_le_sum hclass
    _ = 16 * δ * (N : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 ⌊D⌋₊, 1 / (d : ℝ) ^ 2) +
          ((Finset.Icc 1 ⌊D⌋₊).card : ℝ) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 16 * δ * (N : ℝ) ^ 2 * (2 / 1) + D := by gcongr
    _ = D + 32 * δ * (N : ℝ) ^ 2 := by ring

end

end RHTower.GuthMaynard
