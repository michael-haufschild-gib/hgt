import GaloisForLFunctions.RHTower.ExteriorSatake
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Heat time spreads the configuration

The de Bruijn–Newman flow moves zeros by the backward heat equation `∂_t H = −∂_z² H`. For a
polynomial configuration the flow is the operator `e^{−tD²} = Σ_k (−t)^k D^{2k}/k!`
(`heatFlow`). This module proves the exact averaged repulsion law of the field in that model.

* **Coefficients** (`coeff_heatFlow_top`, `coeff_heatFlow_sub_one`, `coeff_heatFlow_sub_two`). For
  a polynomial of degree `n` the flow keeps the coefficients of `xⁿ` and `x^{n−1}` and lowers that
  of `x^{n−2}` by `t n(n−1)` times the leading coefficient.
* **The second moment grows linearly** (`sum_sq_roots_heatFlow`). For monic `p` of degree `n` over
  `ℂ`, `Σ x_j(t) = Σ x_j` and `Σ x_j(t)² = Σ x_j² + 2n(n−1)t`.
* **The total squared gap grows linearly** (`spread_roots_heatFlow`). With
  `spread = n Σ x_j² − (Σ x_j)² = Σ_{j<k} (x_j − x_k)²`: `spread(t) = spread(0) + 2n²(n−1)t`.

For an FE-symmetric configuration each pair contributes its squared gap: real pairs a positive
amount, tilted pairs `−(2δ)²`. Heat time raises the total by a fixed rate whatever the configuration.
For one pair (`n = 2`) the squared half-gap moves as `w²(t) = w² + 2t`, so a tilted pair of depth `δ`
collides at `t = δ²/2` and is real afterwards — the de Bruijn–Newman mechanism in its smallest case.
The law is averaged: it does not by itself prevent one pair from tilting while others spread.

* **Bounded backward exit** (`spread_cons`, `spread_real_nonneg`, `exists_nonreal_root_heatFlow`).
  For a real configuration the total squared gap is a sum of squares, hence `≥ 0`. Backward heat
  time lowers it at the same rate, so a real configuration of total squared gap `S` acquires a
  non-real point before backward time `S/(2n²(n−1))`. This is the averaged form of the Lehmer
  phenomenon: small gaps force early loss of reality backward in heat time, exactly for one pair.
-/

open Polynomial

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- The heat flow `e^{−tD²}` on polynomials. -/
def heatFlow (t : ℂ) (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), C ((-t) ^ k / (k.factorial : ℂ)) * derivative^[2 * k] p

theorem coeff_heatFlow (t : ℂ) (p : ℂ[X]) (m : ℕ) :
    (heatFlow t p).coeff m = ∑ k ∈ Finset.range (p.natDegree + 1),
      (-t) ^ k / (k.factorial : ℂ) * (((m + 2 * k).descFactorial (2 * k) : ℕ) : ℂ) *
        p.coeff (m + 2 * k) := by
  simp only [heatFlow, finsetSum_coeff, coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Only the `k = 0` term reaches the coefficients of degree `≥ n − 1`. -/
theorem coeff_heatFlow_of_le (t : ℂ) (p : ℂ[X]) {m : ℕ} (hm : p.natDegree ≤ m + 1) :
    (heatFlow t p).coeff m = p.coeff m := by
  rw [coeff_heatFlow, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem coeff_heatFlow_top (t : ℂ) (p : ℂ[X]) :
    (heatFlow t p).coeff p.natDegree = p.coeff p.natDegree :=
  coeff_heatFlow_of_le t p (Nat.le_succ _)

theorem coeff_heatFlow_sub_one (t : ℂ) (p : ℂ[X]) :
    (heatFlow t p).coeff (p.natDegree - 1) = p.coeff (p.natDegree - 1) :=
  coeff_heatFlow_of_le t p (by omega)

theorem coeff_heatFlow_sub_two (t : ℂ) (p : ℂ[X]) (hn : 2 ≤ p.natDegree) :
    (heatFlow t p).coeff (p.natDegree - 2) =
      p.coeff (p.natDegree - 2) -
        t * (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) * p.coeff p.natDegree := by
  rw [coeff_heatFlow, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : 0 < p.natDegree + 1)),
    Finset.sum_eq_single_of_mem 1
      (Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_range.mpr (by omega)⟩)]
  · have h2 : p.natDegree - 2 + 2 * 1 = p.natDegree := by omega
    have hd : ((p.natDegree.descFactorial 2 : ℕ) : ℂ) =
        (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p.natDegree)]
      ring
    rw [h2, show 2 * 1 = 2 from rfl, hd]
    simp
    ring
  · intro k hk hk1
    have hk0 := (Finset.mem_erase.mp hk).1
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

theorem natDegree_heatFlow_le (t : ℂ) (p : ℂ[X]) : (heatFlow t p).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hm' : p.natDegree < m := by exact_mod_cast hm
  rw [coeff_heatFlow_of_le t p (by omega), coeff_eq_zero_of_natDegree_lt hm']

theorem heatFlow_monic {t : ℂ} {p : ℂ[X]} (hp : p.Monic) : (heatFlow t p).Monic ∧
    (heatFlow t p).natDegree = p.natDegree := by
  have hc : (heatFlow t p).coeff p.natDegree = 1 := by
    rw [coeff_heatFlow_top]; exact hp
  have hdeg := natDegree_eq_of_le_of_coeff_ne_zero (natDegree_heatFlow_le t p) (by rw [hc]; simp)
  refine ⟨?_, hdeg⟩
  rw [Monic, leadingCoeff, hdeg, hc]

/-- The first elementary symmetric function is the sum. -/
theorem multiset_esymm_one (s : Multiset ℂ) : s.esymm 1 = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | cons a s ih =>
    rw [show (1 : ℕ) = 0 + 1 from rfl, GaloisForLFunctions.multiset_esymm_cons, ← show (1 : ℕ) = 0 + 1 from rfl,
      ih, Multiset.sum_cons]
    simp [Multiset.esymm]; ring

/-- `Σ x² = e₁² − 2e₂`. -/
theorem multiset_sum_sq (s : Multiset ℂ) :
    (s.map fun x => x ^ 2).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons,
      show (2 : ℕ) = 1 + 1 from rfl, GaloisForLFunctions.multiset_esymm_cons,
      multiset_esymm_one]
    ring

/-- Vieta for monic polynomials over `ℂ` in degrees `n − 1` and `n − 2`. -/
theorem vieta_two {q : ℂ[X]} (hq : q.Monic) (hn : 2 ≤ q.natDegree) :
    q.coeff (q.natDegree - 1) = -q.roots.sum ∧ q.coeff (q.natDegree - 2) = q.roots.esymm 2 := by
  have hcard := IsAlgClosed.card_roots_eq_natDegree (p := q)
  have h1 := coeff_eq_esymm_roots_of_card hcard (k := q.natDegree - 1) (by omega)
  have h2 := coeff_eq_esymm_roots_of_card hcard (k := q.natDegree - 2) (by omega)
  rw [hq.leadingCoeff, one_mul, show q.natDegree - (q.natDegree - 1) = 1 by omega,
    multiset_esymm_one] at h1
  rw [hq.leadingCoeff, one_mul, show q.natDegree - (q.natDegree - 2) = 2 by omega] at h2
  refine ⟨by rw [h1]; ring, by rw [h2]; ring⟩

/-- **The heat flow keeps the centre and raises the second moment linearly.** -/
theorem sum_sq_roots_heatFlow {p : ℂ[X]} (hp : p.Monic) (hn : 2 ≤ p.natDegree) (t : ℂ) :
    (heatFlow t p).roots.sum = p.roots.sum ∧
      ((heatFlow t p).roots.map fun x => x ^ 2).sum =
        (p.roots.map fun x => x ^ 2).sum +
          2 * t * (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) := by
  obtain ⟨hmon, hdeg⟩ := heatFlow_monic (t := t) hp
  obtain ⟨a1, a2⟩ := vieta_two hp hn
  obtain ⟨b1, b2⟩ := vieta_two hmon (hdeg ▸ hn)
  rw [hdeg] at b1 b2
  have hs1 : (heatFlow t p).roots.sum = p.roots.sum := by
    have := coeff_heatFlow_sub_one t p
    rw [b1, a1] at this
    linear_combination -this
  have hs2 : (heatFlow t p).roots.esymm 2 =
      p.roots.esymm 2 - t * (p.natDegree : ℂ) * ((p.natDegree : ℂ) - 1) := by
    have := coeff_heatFlow_sub_two t p hn
    rw [b2, a2, hp.coeff_natDegree, mul_one] at this
    exact this
  refine ⟨hs1, ?_⟩
  rw [multiset_sum_sq, multiset_sum_sq, hs1, hs2]
  ring

/-- The total squared gap `n Σ x_j² − (Σ x_j)² = Σ_{j<k} (x_j − x_k)²` of a multiset. -/
def spread (s : Multiset ℂ) : ℂ := (Multiset.card s : ℂ) * (s.map fun x => x ^ 2).sum - s.sum ^ 2

/-- **The total squared gap grows at the rate `2n²(n−1)` in heat time.** -/
theorem spread_roots_heatFlow {p : ℂ[X]} (hp : p.Monic) (hn : 2 ≤ p.natDegree) (t : ℂ) :
    spread (heatFlow t p).roots =
      spread p.roots + 2 * t * (p.natDegree : ℂ) ^ 2 * ((p.natDegree : ℂ) - 1) := by
  obtain ⟨hs1, hs2⟩ := sum_sq_roots_heatFlow hp hn t
  have hc : Multiset.card (heatFlow t p).roots = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, (heatFlow_monic (t := t) hp).2]
  have hc' : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  rw [spread, spread, hc, hc', hs1, hs2]
  ring

/-- Adding a point `a` raises the total squared gap by `Σ_x (a − x)²`. -/
theorem spread_cons (a : ℂ) (s : Multiset ℂ) :
    spread (a ::ₘ s) = spread s + (s.map fun x => (a - x) ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [spread]
  | cons b s ih =>
    simp only [spread, Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add,
      Nat.cast_one] at ih ⊢
    have hP : (s.map fun x => (a - x) ^ 2).sum = (Multiset.card s : ℂ) * a ^ 2 - 2 * a * s.sum +
        (s.map fun x => x ^ 2).sum := by
      clear ih
      induction s using Multiset.induction_on with
      | empty => simp
      | cons c s ih' =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
          Nat.cast_one, ih']
        ring
    rw [hP]
    ring

/-- A real configuration has a real, nonnegative total squared gap. -/
theorem spread_real_nonneg {s : Multiset ℂ} (hs : ∀ x ∈ s, x.im = 0) :
    (spread s).im = 0 ∧ 0 ≤ (spread s).re := by
  induction s using Multiset.induction_on with
  | empty => simp [spread]
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have ha := hs a (Multiset.mem_cons_self a s)
    have hterm : ∀ x ∈ s, ((a - x) ^ 2).im = 0 ∧ 0 ≤ ((a - x) ^ 2).re := fun x hx => by
      have hx' := hs x (Multiset.mem_cons_of_mem hx)
      simp only [sq, Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re, ha, hx']
      constructor
      · ring
      · nlinarith [sq_nonneg (a.re - x.re)]
    have hsum : ∀ u : Multiset ℂ, u.sum.re = (u.map Complex.re).sum ∧
        u.sum.im = (u.map Complex.im).sum := fun u => by
      induction u using Multiset.induction_on <;> simp_all
    rw [spread_cons, Complex.add_im, Complex.add_re, (hsum _).1, (hsum _).2]
    refine ⟨?_, ?_⟩
    · rw [h1, zero_add, Multiset.map_map]
      exact Multiset.sum_eq_zero fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
        exact (hterm x hx).1
    · rw [Multiset.map_map]
      exact add_nonneg h2 (Multiset.sum_nonneg fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
        exact (hterm x hx).2)

/-- **Backward heat time exits reality in bounded time.** Let `p` be monic of degree `n ≥ 2` with
total squared gap `S`. For real `t` with `Re S + 2n²(n−1)t < 0`, the polynomial `e^{−tD²}p` has a
non-real root. A real configuration (`S ≥ 0`) therefore stays real for backward heat time at most
`S/(2n²(n−1))`; for one pair of gap `Δ` this is the exact collision time `Δ²/8`. -/
theorem exists_nonreal_root_heatFlow {p : ℂ[X]} (hp : p.Monic) (hn : 2 ≤ p.natDegree) {t : ℝ}
    (ht : (spread p.roots).re + 2 * t * (p.natDegree : ℝ) ^ 2 * ((p.natDegree : ℝ) - 1) < 0) :
    ∃ x ∈ (heatFlow t p).roots, x.im ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := (spread_real_nonneg h).2
  rw [spread_roots_heatFlow hp hn t] at h1
  have e : (spread p.roots + 2 * (t : ℂ) * (p.natDegree : ℂ) ^ 2 * ((p.natDegree : ℂ) - 1)).re =
      (spread p.roots).re + 2 * t * (p.natDegree : ℝ) ^ 2 * ((p.natDegree : ℝ) - 1) := by
    simp [Complex.add_re, Complex.mul_re, pow_two]
  rw [e] at h1
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
