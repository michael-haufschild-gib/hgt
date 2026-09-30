import GaloisForLFunctions.RHTower.WeilFullConeLacunaryRigidity

/-!
# Dyadic rigidity: a Weil-positive system cannot deviate from `Λ` only at the powers of `2`

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_powers_two`, unconditional). Let `lam` be
Weil-positive with the pole term (`WeilPositiveFull`). Suppose `lam m = Λ(m)` for every `m ≥ 2`
that is not a power `2^k` (`k ≥ 1`). Then `lam = Λ`. The deviations at the powers of `2` are
arbitrary a priori: they may change sign and need not be summable.

This closes the ratio-`2` case left open by `eq_vonMangoldt_of_weilPositiveFull_of_powers`, whose
`3`-lacunary decay budget does not survive log-spacing `log 2`.

**The sharp kernel input.** At one dyadic step the Riemann autocorrelation is small:
`K(log 2) ≤ (101/100)² · (7/50) · K(0) ≈ 0.143 K(0)` (`riemannAutocorr_log_two_le`). This comes
from the pointwise product bound `φ₁(|s + ½log 2|) φ₁(|s − ½log 2|) ≤ (7/50) φ₁(|s|)²` for the
leading theta term (`riemannLeadTerm_shift_mul_le_two`). That bound is the elementary inequality
`e^{7d} e^{−πV}(8π − 3V)(2πV − 3) ≤ (7/50)(4π − 3V)²` for `V = e^{2d} ∈ [1, 2]`
(`dyadic_core_le`). At larger dyadic steps the L156 shift law gives geometric decay
(`riemannAutocorr_nat_mul_log_two_le`).

**The weight.** Deviations are measured against `3 + log n`, not `1 + log n`. The weight ratio
across a log-distance `D` is then at most `1 + D/3` (`three_add_le_mul`). The weighted kernel obeys
`(1 + k log 2 / 3) K(k log 2) ≤ 0.177 · 18^{−(k−1)} K(0)` (`dyadic_weighted_autocorr_le`), whose sum
is at most `0.1875` (`tsum_dyadicDecay_le`).

**The argument.** It uses the pair test `Φχ_L ± Φχ_L(· − log 2^{j+1})` of
`WeilFullConeLacunaryRigidity`. Let `M = sup_i |v(2^{i+1})|/(3 + log 2^{i+1})`, with
`v = (Λ − lam)/√n`.
- Positivity at each atom gives `|v(2^{j+1})| ≤ 0.7605 M (3 + log 2^{j+1})` (`dyadic_atom_le`).
- Taking the supremum gives `M = 0`.

**Consequence.** Every single prime-power line `{p^k}` is rigid, for `p = 2` here and `p ≥ 3` in
L158. The rigid classes are now separated sets with gap ratio at least `2`. The open classes are
those whose logarithms accumulate: two-sided deviations on `{p^a q^b}` or on sets of positive
density.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Exponential lower bounds -/

private theorem exp_ge_of_taylor {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (n : ℕ) :
    ∑ i ∈ Finset.range n, y ^ i / (i.factorial : ℝ) ≤ Real.exp x :=
  (Real.sum_le_exp_of_nonneg hy n).trans (Real.exp_le_exp.mpr hxy)

theorem exp_pi_quarter_ge : (2.0937 : ℝ) ≤ Real.exp (π / 4) := by
  have h := exp_ge_of_taylor (x := π / 4) (y := 0.785375) (by norm_num)
    (by linarith [Real.pi_gt_d4]) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

theorem exp_pi_half_ge : (4.45 : ℝ) ≤ Real.exp (π / 2) := by
  have h := exp_ge_of_taylor (x := π / 2) (y := 1.57075) (by norm_num)
    (by linarith [Real.pi_gt_d4]) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

theorem exp_three_pi_quarter_ge : (10.43 : ℝ) ≤ Real.exp (3 * π / 4) := by
  have h := exp_ge_of_taylor (x := 3 * π / 4) (y := 2.356125) (by norm_num)
    (by linarith [Real.pi_gt_d4]) 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

private theorem exp_neg_mul_pi_le_inv {a c : ℝ} (hc : 0 < c) (h : c ≤ Real.exp (a * π)) :
    Real.exp (-(a * π)) ≤ 1 / c := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hc h

/-- The exponent `7d − π e^{2d}` decreases once `2π e^{2d} ≥ 7`. -/
private theorem exp_seven_mul_sub_le {d₀ d : ℝ} (hd : d₀ ≤ d) (h7 : 7 ≤ 2 * π * Real.exp (2 * d₀)) :
    Real.exp (7 * d) * Real.exp (-(π * Real.exp (2 * d))) ≤
      Real.exp (7 * d₀) * Real.exp (-(π * Real.exp (2 * d₀))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : Real.exp (2 * d₀) * (2 * (d - d₀)) ≤ Real.exp (2 * d) - Real.exp (2 * d₀) := by
    have := Real.add_one_le_exp (2 * (d - d₀))
    have e : Real.exp (2 * d) = Real.exp (2 * d₀) * Real.exp (2 * (d - d₀)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]; nlinarith [Real.exp_pos (2 * d₀)]
  have hp := Real.pi_pos
  nlinarith

/-- `exp(7d) = V³ exp(d)` with `V = exp(2d)`. -/
private theorem exp_seven_mul_eq (d : ℝ) : Real.exp (7 * d) = Real.exp (2 * d) ^ 3 * Real.exp d := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- A square-root bound: `exp(2d) ≤ c²` implies `exp d ≤ c`. -/
private theorem exp_le_of_exp_two_mul_le {d c : ℝ} (hc : 0 ≤ c) (h : Real.exp (2 * d) ≤ c ^ 2) :
    Real.exp d ≤ c := by
  have e : Real.exp (2 * d) = Real.exp d ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  rw [e] at h
  exact (pow_le_pow_iff_left₀ (Real.exp_pos d).le hc (by norm_num)).mp h

/-! ## The sharp shift inequality at `x = 2` -/

/-- **The reduced dyadic inequality.** For `0 ≤ d ≤ ½ log 2` and `V = e^{2d}`,
`e^{7d} e^{−πV} (8π − 3V)(2πV − 3) ≤ (7/50)(4π − 3V)²`. -/
theorem dyadic_core_le {d : ℝ} (hd0 : 0 ≤ d) (hdh : Real.exp (2 * d) ≤ 2) :
    Real.exp (7 * d) * Real.exp (-(π * Real.exp (2 * d))) *
        ((8 * π - 3 * Real.exp (2 * d)) * (2 * π * Real.exp (2 * d) - 3)) ≤
      7 / 50 * (4 * π - 3 * Real.exp (2 * d)) ^ 2 := by
  have hπ1 := Real.pi_gt_d4
  have hπ2 := Real.pi_lt_d4
  have hpi := exp_pi_ge
  set V := Real.exp (2 * d) with hV
  have hV1 : 1 ≤ V := Real.one_le_exp (by linarith)
  have hP1 : 0 < 8 * π - 3 * V := by linarith
  have hP2 : 0 < 2 * π * V - 3 := by nlinarith
  have hQ : 0 < 4 * π - 3 * V := by linarith
  have hE0 : 0 ≤ Real.exp (7 * d) * Real.exp (-(π * V)) := by positivity
  -- the four pieces
  rcases le_or_gt V 1.25 with h1 | h1
  · -- `V ≤ 5/4`: crude exponential factor
    have hed : Real.exp d ≤ 1.1181 := exp_le_of_exp_two_mul_le (by norm_num) (by rw [← hV]; linarith)
    have h7 : Real.exp (7 * d) ≤ 2.1843 := by
      rw [exp_seven_mul_eq, ← hV]
      have hV3 : V ^ 3 ≤ 1.25 ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
      calc V ^ 3 * Real.exp d ≤ 1.25 ^ 3 * 1.1181 :=
            mul_le_mul hV3 hed (Real.exp_pos _).le (by norm_num)
        _ ≤ 2.1843 := by norm_num
    have hex : Real.exp (-(π * V)) ≤ 2 / 45 := by
      calc Real.exp (-(π * V)) ≤ Real.exp (-(1 * π)) := Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ 1 / (45 / 2) := exp_neg_mul_pi_le_inv (by norm_num) (by rw [one_mul]; exact hpi)
        _ = 2 / 45 := by norm_num
    have hE : Real.exp (7 * d) * Real.exp (-(π * V)) ≤ 2.1843 * (2 / 45) :=
      mul_le_mul h7 hex (Real.exp_pos _).le (by norm_num)
    have ha : 8 * π - 3 * V ≤ 22.1328 := by linarith
    have hb : 2 * π * V - 3 ≤ 4.854 := by nlinarith
    have hc : 8.816 ≤ 4 * π - 3 * V := by linarith
    have hprod : (8 * π - 3 * V) * (2 * π * V - 3) ≤ 22.1328 * 4.854 :=
      mul_le_mul ha hb hP2.le (by norm_num)
    have hsq : 8.816 ^ 2 ≤ (4 * π - 3 * V) ^ 2 := pow_le_pow_left₀ (by norm_num) hc 2
    calc Real.exp (7 * d) * Real.exp (-(π * V)) * ((8 * π - 3 * V) * (2 * π * V - 3))
        ≤ (2.1843 * (2 / 45)) * (22.1328 * 4.854) :=
          mul_le_mul hE hprod (mul_pos hP1 hP2).le (by norm_num)
      _ ≤ 7 / 50 * 8.816 ^ 2 := by norm_num
      _ ≤ 7 / 50 * (4 * π - 3 * V) ^ 2 := by gcongr
  -- the monotone pieces share the anchor `d_a` with `exp(2 d_a) = V_a`
  have piece : ∀ (Va ca ea a b c : ℝ), 1.25 ≤ Va → Va ≤ V → 0 ≤ ca → Va ≤ ca ^ 2 →
      0 < ea → ea ≤ Real.exp (Va * π) →
      8 * π - 3 * V ≤ a → 2 * π * V - 3 ≤ b → 0 < c → c ≤ 4 * π - 3 * V →
      Va ^ 3 * ca * (1 / ea) * (a * b) ≤ 7 / 50 * c ^ 2 →
      Real.exp (7 * d) * Real.exp (-(π * V)) * ((8 * π - 3 * V) * (2 * π * V - 3)) ≤
        7 / 50 * (4 * π - 3 * V) ^ 2 := by
    intro Va ca ea a b c hVa hVaV hca hca2 hea heaπ ha hb hc hcQ hnum
    set da := Real.log Va / 2 with hda
    have hVa0 : 0 < Va := by linarith
    have hexpda : Real.exp (2 * da) = Va := by rw [hda, show 2 * (Real.log Va / 2) = Real.log Va by ring,
      Real.exp_log hVa0]
    have hdad : da ≤ d := by
      have : Real.exp (2 * da) ≤ Real.exp (2 * d) := by rw [hexpda, ← hV]; exact hVaV
      have := Real.exp_le_exp.mp this; linarith
    have h7 : (7 : ℝ) ≤ 2 * π * Real.exp (2 * da) := by rw [hexpda]; nlinarith
    have hmono := exp_seven_mul_sub_le hdad h7
    rw [hexpda, ← hV] at hmono
    have hed : Real.exp da ≤ ca := exp_le_of_exp_two_mul_le hca (by rw [hexpda]; exact hca2)
    have h7a : Real.exp (7 * da) ≤ Va ^ 3 * ca := by
      rw [exp_seven_mul_eq, hexpda]; exact mul_le_mul_of_nonneg_left hed (by positivity)
    have hexa : Real.exp (-(π * Va)) ≤ 1 / ea := by
      rw [show π * Va = Va * π by ring]; exact exp_neg_mul_pi_le_inv hea heaπ
    have hEa : Real.exp (7 * da) * Real.exp (-(π * Va)) ≤ Va ^ 3 * ca * (1 / ea) :=
      mul_le_mul h7a hexa (Real.exp_pos _).le (by positivity)
    have hprod : (8 * π - 3 * V) * (2 * π * V - 3) ≤ a * b :=
      mul_le_mul ha hb hP2.le (by linarith)
    have hsq : c ^ 2 ≤ (4 * π - 3 * V) ^ 2 := pow_le_pow_left₀ hc.le hcQ 2
    calc Real.exp (7 * d) * Real.exp (-(π * V)) * ((8 * π - 3 * V) * (2 * π * V - 3))
        ≤ (Va ^ 3 * ca * (1 / ea)) * (a * b) :=
          mul_le_mul (hmono.trans hEa) hprod (mul_pos hP1 hP2).le (by positivity)
      _ ≤ 7 / 50 * c ^ 2 := hnum
      _ ≤ 7 / 50 * (4 * π - 3 * V) ^ 2 := by gcongr
  have he125 : (47.108 : ℝ) ≤ Real.exp (1.25 * π) := by
    rw [show (1.25 : ℝ) * π = π + π / 4 by ring, Real.exp_add]
    have := exp_pi_quarter_ge; nlinarith
  have he15 : (100.125 : ℝ) ≤ Real.exp (1.5 * π) := by
    rw [show (1.5 : ℝ) * π = π + π / 2 by ring, Real.exp_add]
    have := exp_pi_half_ge; nlinarith
  have he175 : (234.675 : ℝ) ≤ Real.exp (1.75 * π) := by
    rw [show (1.75 : ℝ) * π = π + 3 * π / 4 by ring, Real.exp_add]
    have := exp_three_pi_quarter_ge; nlinarith
  rcases le_or_gt V 1.5 with h2 | h2
  · exact piece 1.25 1.1181 47.108 21.3828 6.4248 8.066 le_rfl h1.le (by norm_num) (by norm_num)
      (by norm_num) he125 (by linarith) (by nlinarith) (by norm_num) (by linarith) (by norm_num)
  rcases le_or_gt V 1.75 with h3 | h3
  · exact piece 1.5 1.22475 100.125 20.6328 7.9956 7.316 (by norm_num) h2.le (by norm_num)
      (by norm_num) (by norm_num) he15 (by linarith) (by nlinarith) (by norm_num) (by linarith)
      (by norm_num)
  · exact piece 1.75 1.3229 234.675 19.8828 9.5664 6.566 (by norm_num) h3.le (by norm_num)
      (by norm_num) (by norm_num) he175 (by linarith) (by nlinarith) (by norm_num) (by linarith)
      (by norm_num)

/-- **The sharp shift inequality at `x = 2`** for `s ≥ 0`:
`φ₁(s + h) φ₁(|s − h|) ≤ (7/50) φ₁(s)²` with `h = ½ log 2`. -/
theorem riemannLeadTerm_shift_mul_le_two_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    riemannLeadTerm |s + Real.log 2 / 2| * riemannLeadTerm |s - Real.log 2 / 2| ≤
      7 / 50 * riemannLeadTerm |s| ^ 2 := by
  have hπ := Real.pi_gt_three
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 4 * π ^ 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 6 * π := ⟨_, rfl⟩
  have hpq : 0 < p - q := by rw [hp, hq]; nlinarith
  have hq0 : 0 < q := by rw [hq]; positivity
  have hp0 : 0 < p := by linarith
  have hlead : ∀ t : ℝ, riemannLeadTerm t =
      Real.exp (5 * t / 2) * (p * Real.exp (2 * t) - q) * Real.exp (-π * Real.exp (2 * t)) := by
    intro t; rw [hp, hq]; rfl
  set h := Real.log 2 / 2 with hh
  have hh0 : 0 ≤ h := by rw [hh]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); linarith
  have hx : Real.exp (2 * h) = 2 := by
    rw [hh, show 2 * (Real.log 2 / 2) = Real.log 2 by ring, Real.exp_log (by norm_num)]
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = Real.exp (2 * s) := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZdef]; exact Real.one_le_exp (by linarith)
  have habs_s : |s| = s := abs_of_nonneg hs
  have habs_p : |s + h| = s + h := abs_of_nonneg (by linarith)
  set E := Real.exp (5 * s) * Real.exp (-(2 * π * Z)) with hEdef
  have hE0 : 0 < E := by positivity
  have hRHS : 7 / 50 * riemannLeadTerm |s| ^ 2 = 7 / 50 * (p * Z - q) ^ 2 * E := by
    rw [habs_s, hlead s, ← hZdef]
    have e1 : Real.exp (5 * s / 2) ^ 2 = Real.exp (5 * s) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have e2 : Real.exp (-π * Z) ^ 2 = Real.exp (-(2 * π * Z)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    calc 7 / 50 * (Real.exp (5 * s / 2) * (p * Z - q) * Real.exp (-π * Z)) ^ 2
        = 7 / 50 * (p * Z - q) ^ 2 * (Real.exp (5 * s / 2) ^ 2 * Real.exp (-π * Z) ^ 2) := by ring
      _ = _ := by rw [e1, e2]
  have hZq : 0 < p * Z - q := by
    have : p * 1 ≤ p * Z := mul_le_mul_of_nonneg_left hZ1 hp0.le
    linarith
  rw [hRHS]
  rcases le_or_gt h s with hhs | hsh
  · -- both points on the right half-line: the ratio is at most `e^{−π}`
    have habs_m : |s - h| = s - h := abs_of_nonneg (by linarith)
    have hxZ : 2 ≤ Z := by
      calc (2 : ℝ) = Real.exp (2 * h) := hx.symm
        _ ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr (by linarith)
        _ = Z := hZdef.symm
    have e1 : Real.exp (2 * (s + h)) = Z * 2 := by
      rw [show 2 * (s + h) = 2 * s + 2 * h by ring, Real.exp_add, hx, hZdef]
    have e2 : Real.exp (2 * (s - h)) = Z * (1 / 2) := by
      rw [show 2 * (s - h) = 2 * s + -(2 * h) by ring, Real.exp_add, Real.exp_neg, hx, hZdef]
      ring
    have e3 : Real.exp (5 * (s + h) / 2) * Real.exp (5 * (s - h) / 2) = Real.exp (5 * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [habs_p, habs_m, hlead, hlead, e1, e2]
    have hQ0 : 0 ≤ (p * (Z * 2) - q) * (p * (Z * (1 / 2)) - q) := by
      have h1 : p * 1 ≤ p * (Z * 2) := mul_le_mul_of_nonneg_left (by linarith) hp0.le
      have h2 : p * 1 ≤ p * (Z * (1 / 2)) := mul_le_mul_of_nonneg_left (by linarith) hp0.le
      exact mul_nonneg (by linarith) (by linarith)
    have hQ : (p * (Z * 2) - q) * (p * (Z * (1 / 2)) - q) ≤ (p * Z - q) ^ 2 := by
      have e : (p * Z - q) ^ 2 - (p * (Z * 2) - q) * (p * (Z * (1 / 2)) - q) = p * q * Z * (1 / 2) := by
        ring
      have : 0 ≤ p * q * Z * (1 / 2) := by positivity
      linarith
    have hE : Real.exp (-π * (Z * 2)) * Real.exp (-π * (Z * (1 / 2))) ≤
        Real.exp (-π) * Real.exp (-(2 * π * Z)) := by
      rw [← Real.exp_add (-π * (Z * 2)), ← Real.exp_add (-π)]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hpi : Real.exp (-π) ≤ 7 / 50 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := exp_pi_ge; linarith
    have hEE0 : 0 ≤ Real.exp (-π * (Z * 2)) * Real.exp (-π * (Z * (1 / 2))) := by positivity
    calc Real.exp (5 * (s + h) / 2) * (p * (Z * 2) - q) * Real.exp (-π * (Z * 2)) *
          (Real.exp (5 * (s - h) / 2) * (p * (Z * (1 / 2)) - q) * Real.exp (-π * (Z * (1 / 2))))
        = (Real.exp (5 * (s + h) / 2) * Real.exp (5 * (s - h) / 2)) *
            ((p * (Z * 2) - q) * (p * (Z * (1 / 2)) - q)) *
            (Real.exp (-π * (Z * 2)) * Real.exp (-π * (Z * (1 / 2)))) := by ring
      _ = Real.exp (5 * s) * ((p * (Z * 2) - q) * (p * (Z * (1 / 2)) - q)) *
            (Real.exp (-π * (Z * 2)) * Real.exp (-π * (Z * (1 / 2)))) := by rw [e3]
      _ ≤ Real.exp (5 * s) * (p * Z - q) ^ 2 * (Real.exp (-π) * Real.exp (-(2 * π * Z))) := by
          gcongr
      _ = Real.exp (-π) * (p * Z - q) ^ 2 * E := by rw [hEdef]; ring
      _ ≤ 7 / 50 * (p * Z - q) ^ 2 * E := by gcongr
  · -- the reflected case reduces to the core inequality
    have habs_m : |s - h| = h - s := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = h - s := ⟨_, rfl⟩
    obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = Real.exp (2 * d) := ⟨_, rfl⟩
    have hd0 : 0 ≤ d := by rw [hd]; linarith
    have hV2 : V ≤ 2 := by
      rw [hVdef]
      calc Real.exp (2 * d) ≤ Real.exp (2 * h) := Real.exp_le_exp.mpr (by rw [hd]; linarith)
        _ = 2 := hx
    have hV1 : 1 ≤ V := by rw [hVdef]; exact Real.one_le_exp (by linarith)
    have hV0 : 0 < V := by linarith
    have hZV : Z * V = 2 := by
      rw [hZdef, hVdef, ← Real.exp_add, show 2 * s + 2 * d = 2 * h by rw [hd]; ring, hx]
    have hL1 : riemannLeadTerm |s + h| =
        Real.exp (5 * (s + h) / 2) * (p * (Z * 2) - q) * Real.exp (-(2 * π * Z)) := by
      rw [habs_p, hlead, show 2 * (s + h) = 2 * s + 2 * h by ring, Real.exp_add, hx, ← hZdef]
      ring_nf
    have hL2 : riemannLeadTerm |s - h| =
        Real.exp (5 * d / 2) * (p * V - q) * Real.exp (-(π * V)) := by
      rw [habs_m, ← hd, hlead, ← hVdef]; ring_nf
    rw [hL1, hL2]
    have hcore := dyadic_core_le hd0 (by rw [← hVdef]; exact hV2)
    rw [← hVdef] at hcore
    have h7 : Real.exp (7 * d) = Real.exp (5 * d) * V := by rw [hVdef, ← Real.exp_add]; ring_nf
    have hA : (p * (Z * 2) - q) * V = 2 * π * (8 * π - 3 * V) := by
      have e : (p * (Z * 2) - q) * V = 2 * p * (Z * V) - q * V := by ring
      rw [e, hZV, hp, hq]; ring
    have hB : p * V - q = 2 * π * (2 * π * V - 3) := by rw [hp, hq]; ring
    have hC : (p * Z - q) * V = 2 * π * (4 * π - 3 * V) := by
      have e : (p * Z - q) * V = p * (Z * V) - q * V := by ring
      rw [e, hZV, hp, hq]; ring
    have hexp5 : Real.exp (5 * (s + h) / 2) * Real.exp (5 * d / 2) = Real.exp (5 * s) * Real.exp (5 * d) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hd]; ring
    -- the key inequality multiplied by `V²`
    set X := Real.exp (5 * d) * ((p * (Z * 2) - q) * (p * V - q)) * Real.exp (-(π * V)) with hX
    have key : X * V ^ 2 ≤ 7 / 50 * (p * Z - q) ^ 2 * V ^ 2 := by
      have lhs : X * V ^ 2 = 4 * π ^ 2 *
          (Real.exp (7 * d) * Real.exp (-(π * V)) * ((8 * π - 3 * V) * (2 * π * V - 3))) := by
        rw [hX, h7]
        have e : Real.exp (5 * d) * ((p * (Z * 2) - q) * (p * V - q)) * Real.exp (-(π * V)) * V ^ 2 =
            Real.exp (5 * d) * V * (((p * (Z * 2) - q) * V) * (p * V - q)) * Real.exp (-(π * V)) := by
          ring
        rw [e, hA, hB]; ring
      have rhs : 7 / 50 * (p * Z - q) ^ 2 * V ^ 2 = 4 * π ^ 2 * (7 / 50 * (4 * π - 3 * V) ^ 2) := by
        have e : 7 / 50 * (p * Z - q) ^ 2 * V ^ 2 = 7 / 50 * ((p * Z - q) * V) ^ 2 := by ring
        rw [e, hC]; ring
      rw [lhs, rhs]
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    have hXle : X ≤ 7 / 50 * (p * Z - q) ^ 2 := le_of_mul_le_mul_right key (by positivity)
    calc Real.exp (5 * (s + h) / 2) * (p * (Z * 2) - q) * Real.exp (-(2 * π * Z)) *
          (Real.exp (5 * d / 2) * (p * V - q) * Real.exp (-(π * V)))
        = (Real.exp (5 * (s + h) / 2) * Real.exp (5 * d / 2)) *
            ((p * (Z * 2) - q) * (p * V - q)) * Real.exp (-(π * V)) * Real.exp (-(2 * π * Z)) := by
          ring
      _ = Real.exp (5 * s) * X * Real.exp (-(2 * π * Z)) := by rw [hexp5, hX]; ring
      _ ≤ Real.exp (5 * s) * (7 / 50 * (p * Z - q) ^ 2) * Real.exp (-(2 * π * Z)) := by gcongr
      _ = 7 / 50 * (p * Z - q) ^ 2 * E := by rw [hEdef]; ring

theorem riemannLeadTerm_shift_mul_le_two (s : ℝ) :
    riemannLeadTerm |s + Real.log 2 / 2| * riemannLeadTerm |s - Real.log 2 / 2| ≤
      7 / 50 * riemannLeadTerm |s| ^ 2 := by
  rcases le_or_gt 0 s with hs | hs
  · exact riemannLeadTerm_shift_mul_le_two_of_nonneg hs
  · have hk := riemannLeadTerm_shift_mul_le_two_of_nonneg (s := -s) (by linarith)
    have e1 : |-s + Real.log 2 / 2| = |s - Real.log 2 / 2| := by
      rw [show -s + Real.log 2 / 2 = -(s - Real.log 2 / 2) by ring, abs_neg]
    have e2 : |-s - Real.log 2 / 2| = |s + Real.log 2 / 2| := by
      rw [show -s - Real.log 2 / 2 = -(s + Real.log 2 / 2) by ring, abs_neg]
    rw [e1, e2, abs_neg, mul_comm] at hk
    exact hk

/-- **The sharp dyadic autocorrelation bound.** `K(log 2) ≤ (101/100)² (7/50) K(0)`. -/
theorem riemannAutocorr_log_two_le :
    riemannAutocorr (Real.log 2) ≤ (101 / 100) ^ 2 * (7 / 50) * riemannAutocorr 0 := by
  set h := Real.log 2 / 2 with hh
  have hpt : ∀ s : ℝ, riemannKernelReal (s + h) * riemannKernelReal (s - h) ≤
      (101 / 100) ^ 2 * (7 / 50) * riemannKernelReal s ^ 2 := by
    intro s
    obtain ⟨-, h1⟩ := riemannKernelReal_sandwich (s + h)
    obtain ⟨-, h2⟩ := riemannKernelReal_sandwich (s - h)
    obtain ⟨h3, -⟩ := riemannKernelReal_sandwich s
    have hk := riemannLeadTerm_shift_mul_le_two s
    have p3 := riemannLeadTerm_pos (abs_nonneg s)
    have hΦ2 := riemannKernelReal_pos (s - h)
    calc riemannKernelReal (s + h) * riemannKernelReal (s - h)
        ≤ ((101 / 100) * riemannLeadTerm |s + h|) * ((101 / 100) * riemannLeadTerm |s - h|) :=
          mul_le_mul h1 h2 hΦ2.le (by have := riemannLeadTerm_pos (abs_nonneg (s + h)); positivity)
      _ = (101 / 100) ^ 2 * (riemannLeadTerm |s + h| * riemannLeadTerm |s - h|) := by ring
      _ ≤ (101 / 100) ^ 2 * (7 / 50 * riemannLeadTerm |s| ^ 2) :=
          mul_le_mul_of_nonneg_left hk (by norm_num)
      _ ≤ (101 / 100) ^ 2 * (7 / 50 * riemannKernelReal s ^ 2) := by gcongr
      _ = _ := by ring
  have hshift : riemannAutocorr (Real.log 2) =
      ∫ s, riemannKernelReal (s + h) * riemannKernelReal (s - h) := by
    unfold riemannAutocorr
    rw [← integral_add_right_eq_self (fun t => riemannKernelReal t *
      riemannKernelReal (t - Real.log 2)) h]
    congr 1; funext s
    rw [show s + h - Real.log 2 = s - h by rw [hh]; ring]
  rw [hshift, riemannAutocorr_zero, ← integral_const_mul]
  have hi1 : Integrable fun s => riemannKernelReal (s + h) * riemannKernelReal (s - h) := by
    have := (integrable_riemannKernelReal_mul (Real.log 2)).comp_add_right h
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only
    rw [show s + h - Real.log 2 = s - h by rw [hh]; ring]
  have hi2 : Integrable fun s => (101 / 100) ^ 2 * (7 / 50 : ℝ) * riemannKernelReal s ^ 2 := by
    have := (integrable_riemannKernelReal_mul 0).const_mul ((101 / 100) ^ 2 * (7 / 50 : ℝ))
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only
    rw [sub_zero]; ring
  exact integral_mono hi1 hi2 hpt

private theorem two_mul_le_two_pow {k : ℕ} (hk : 2 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega

/-- `K(k log 2) ≤ (101/100)² (19/50) 64^{−(k−1)} K(0)` for `k ≥ 2`. -/
theorem riemannAutocorr_nat_mul_log_two_le {k : ℕ} (hk : 2 ≤ k) :
    riemannAutocorr (k * Real.log 2) ≤
      (101 / 100) ^ 2 * (19 / 50 * (1 / 64 : ℝ) ^ (k - 1)) * riemannAutocorr 0 := by
  have hK0 := riemannAutocorr_zero_pos
  set h := (k : ℝ) * Real.log 2 / 2 with hh
  have hexp : Real.exp (2 * h) = ((2 ^ k - 2 + 2 : ℕ) : ℝ) := by
    rw [hh, show 2 * ((k : ℝ) * Real.log 2 / 2) = (k : ℝ) * Real.log 2 by ring, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.sub_add_cancel h2k]; push_cast; ring
  have hh0 : 0 ≤ h := by rw [hh]; have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  have hx2 : 2 ≤ Real.exp (2 * h) := by rw [hexp]; push_cast; linarith
  have h1 := riemannAutocorr_two_mul_le hh0 hx2
  rw [hexp, show 2 * h = (k : ℝ) * Real.log 2 by rw [hh]; ring] at h1
  have h2 := riemannShiftRatio_le (2 ^ k - 2)
  have hge : 2 * (k - 1) ≤ 2 ^ k - 2 := by
    have := two_mul_le_two_pow hk
    omega
  have h3 : (1 / 8 : ℝ) ^ (2 ^ k - 2) ≤ (1 / 64 : ℝ) ^ (k - 1) := by
    calc (1 / 8 : ℝ) ^ (2 ^ k - 2) ≤ (1 / 8 : ℝ) ^ (2 * (k - 1)) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hge
      _ = (1 / 64 : ℝ) ^ (k - 1) := by rw [pow_mul]; norm_num
  calc riemannAutocorr ((k : ℝ) * Real.log 2)
      ≤ (101 / 100) ^ 2 * riemannShiftRatio ((2 ^ k - 2 + 2 : ℕ) : ℝ) * riemannAutocorr 0 := h1
    _ ≤ (101 / 100) ^ 2 * (19 / 50 * (1 / 8 : ℝ) ^ (2 ^ k - 2)) * riemannAutocorr 0 := by gcongr
    _ ≤ (101 / 100) ^ 2 * (19 / 50 * (1 / 64 : ℝ) ^ (k - 1)) * riemannAutocorr 0 := by gcongr

/-! ## Dyadic rigidity -/

/-- The dyadic decay constants `β_k = 0.177 · 18^{1−k}`. -/
def dyadicDecay (k : ℕ) : ℝ := 0.177 * (1 / 18 : ℝ) ^ (k - 1)

theorem dyadicDecay_nonneg (k : ℕ) : 0 ≤ dyadicDecay k := by unfold dyadicDecay; positivity

/-- `(1 + k log 2 / 3) K(k log 2) ≤ β_k K(0)` for `k ≥ 1`. -/
theorem dyadic_weighted_autocorr_le {k : ℕ} (hk : 1 ≤ k) :
    (1 + k * Real.log 2 / 3) * riemannAutocorr (k * Real.log 2) ≤ dyadicDecay k * riemannAutocorr 0 := by
  have hK0 := riemannAutocorr_zero_pos
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKk := riemannAutocorr_nonneg (k * Real.log 2)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    have h := riemannAutocorr_log_two_le
    simp only [Nat.cast_one, one_mul, dyadicDecay, Nat.sub_self, pow_zero, mul_one]
    have hw : 1 + Real.log 2 / 3 ≤ 1.2311 := by norm_num at hl2 ⊢; linarith
    calc (1 + Real.log 2 / 3) * riemannAutocorr (Real.log 2)
        ≤ 1.2311 * ((101 / 100) ^ 2 * (7 / 50) * riemannAutocorr 0) :=
          mul_le_mul hw h (riemannAutocorr_nonneg _) (by norm_num)
      _ ≤ 0.177 * riemannAutocorr 0 := by nlinarith
  · have h := riemannAutocorr_nat_mul_log_two_le hk2
    have hbern : 1 + k * Real.log 2 / 3 ≤ (1.2311 : ℝ) ^ k := by
      have hb := one_add_mul_le_pow (a := (0.2311 : ℝ)) (by norm_num) k
      have : (k : ℝ) * Real.log 2 / 3 ≤ k * 0.2311 := by
        have : Real.log 2 / 3 ≤ 0.2311 := by norm_num at hl2 ⊢; linarith
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      norm_num at hb ⊢; linarith
    have hk1 : k - 1 + 1 = k := by omega
    have hpow : (1.2311 : ℝ) ^ k * (1 / 64 : ℝ) ^ (k - 1) = 1.2311 * (1.2311 / 64 : ℝ) ^ (k - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      subst hm
      rw [Nat.add_sub_cancel, pow_succ, div_pow, div_pow, one_pow]; ring
    have hratio : (1.2311 / 64 : ℝ) ^ (k - 1) ≤ 0.36885 * (1 / 18 : ℝ) ^ (k - 1) := by
      have e : (1.2311 / 64 : ℝ) ^ (k - 1) = (1.2311 * 18 / 64 : ℝ) ^ (k - 1) * (1 / 18 : ℝ) ^ (k - 1) := by
        rw [← mul_pow]; norm_num
      rw [e]
      have : (1.2311 * 18 / 64 : ℝ) ^ (k - 1) ≤ (1.2311 * 18 / 64 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h18 : (0 : ℝ) ≤ (1 / 18 : ℝ) ^ (k - 1) := by positivity
      nlinarith
    unfold dyadicDecay
    calc (1 + k * Real.log 2 / 3) * riemannAutocorr (k * Real.log 2)
        ≤ (1.2311 : ℝ) ^ k * ((101 / 100) ^ 2 * (19 / 50 * (1 / 64 : ℝ) ^ (k - 1)) * riemannAutocorr 0) :=
          mul_le_mul hbern h hKk (by positivity)
      _ = (101 / 100) ^ 2 * (19 / 50) * ((1.2311 : ℝ) ^ k * (1 / 64 : ℝ) ^ (k - 1)) *
            riemannAutocorr 0 := by ring
      _ = (101 / 100) ^ 2 * (19 / 50) * (1.2311 * (1.2311 / 64 : ℝ) ^ (k - 1)) * riemannAutocorr 0 := by
          rw [hpow]
      _ ≤ (101 / 100) ^ 2 * (19 / 50) * (1.2311 * (0.36885 * (1 / 18 : ℝ) ^ (k - 1))) *
            riemannAutocorr 0 := by gcongr
      _ ≤ 0.177 * (1 / 18 : ℝ) ^ (k - 1) * riemannAutocorr 0 := by
          have h18 : (0 : ℝ) ≤ (1 / 18 : ℝ) ^ (k - 1) := by positivity
          have : (101 / 100 : ℝ) ^ 2 * (19 / 50) * (1.2311 * 0.36885) ≤ 0.177 := by norm_num
          have e : (101 / 100 : ℝ) ^ 2 * (19 / 50) * (1.2311 * (0.36885 * (1 / 18 : ℝ) ^ (k - 1))) *
              riemannAutocorr 0 = ((101 / 100 : ℝ) ^ 2 * (19 / 50) * (1.2311 * 0.36885)) *
              ((1 / 18 : ℝ) ^ (k - 1) * riemannAutocorr 0) := by ring
          rw [e, show (0.177 : ℝ) * (1 / 18 : ℝ) ^ (k - 1) * riemannAutocorr 0 =
            0.177 * ((1 / 18 : ℝ) ^ (k - 1) * riemannAutocorr 0) by ring]
          exact mul_le_mul_of_nonneg_right this (by positivity)

theorem dyadicDecay_summable : Summable fun k : ℕ => dyadicDecay (k + 1) := by
  unfold dyadicDecay
  simp only [Nat.add_sub_cancel]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

theorem tsum_dyadicDecay_le : ∑' k : ℕ, dyadicDecay (k + 1) ≤ 0.1875 := by
  unfold dyadicDecay
  simp only [Nat.add_sub_cancel]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem tsum_dyadicDecay_shift_le (j : ℕ) :
    Summable (fun i : ℕ => dyadicDecay (i + j + 2)) ∧ ∑' i : ℕ, dyadicDecay (i + j + 2) ≤ 0.0105 := by
  have hle : ∀ i : ℕ, dyadicDecay (i + j + 2) ≤ 0.177 * (1 / 18 : ℝ) * (1 / 18 : ℝ) ^ i := by
    intro i
    unfold dyadicDecay
    have e : i + j + 2 - 1 = (i + 1) + j := by omega
    rw [e, pow_add, pow_succ]
    have h1 : (1 / 18 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ (1 / 18 : ℝ) ^ i := by positivity
    nlinarith
  have hg : Summable fun i : ℕ => (0.177 : ℝ) * (1 / 18) * (1 / 18 : ℝ) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs := Summable.of_nonneg_of_le (fun i => dyadicDecay_nonneg _) hle hg
  refine ⟨hs, (hs.tsum_le_tsum hle hg).trans ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- The dyadic weight transfer: `3 + x ≤ (3 + y)(1 + |x − y|/3)` for `y ≥ 0`. -/
private theorem three_add_le_mul {x y : ℝ} (hy : 0 ≤ y) : 3 + x ≤ (3 + y) * (1 + |x - y| / 3) := by
  rcases le_or_gt x y with h | h
  · have : 0 ≤ (3 + y) * (|x - y| / 3) := by positivity
    nlinarith
  · rw [abs_of_pos (by linarith)]; nlinarith

private theorem log_two_pow_succ (i : ℕ) : Real.log ((2 ^ (i + 1) : ℕ) : ℝ) = (i + 1 : ℕ) * Real.log 2 := by
  push_cast; rw [Real.log_pow]; push_cast; ring

/-- The off-diagonal dyadic bookkeeping. -/
theorem dyadic_offdiag {i j : ℕ} (hij : i ≠ j) :
    1 ≤ Nat.dist i j ∧
      |((i + 1 : ℕ) : ℝ) * Real.log 2 - ((j + 1 : ℕ) : ℝ) * Real.log 2| = (Nat.dist i j : ℝ) * Real.log 2 ∧
      (if j < i then dyadicDecay (i - j - 1 + 1) else 0) + (if i < j then dyadicDecay (j - i - 1 + 1) else 0) =
        dyadicDecay (Nat.dist i j) := by
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases lt_or_gt_of_ne hij with h | h
  · have hd : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le h.le
    refine ⟨by rw [hd]; omega, ?_, ?_⟩
    · rw [hd, abs_sub_comm, abs_of_nonneg]
      · rw [Nat.cast_sub h.le]; push_cast; ring
      · have : ((i + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ j + 1)
        nlinarith
    · rw [if_neg (by omega), if_pos h, zero_add, hd, show j - i - 1 + 1 = j - i by omega]
  · have hd : Nat.dist i j = i - j := Nat.dist_eq_sub_of_le_right h.le
    refine ⟨by rw [hd]; omega, ?_, ?_⟩
    · rw [hd, abs_of_nonneg]
      · rw [Nat.cast_sub h.le]; push_cast; ring
      · have : ((j + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ i + 1)
        nlinarith
    · rw [if_pos h, if_neg (by omega), add_zero, hd, show i - j - 1 + 1 = i - j by omega]

/-- **The key inequality at one dyadic atom.** -/
theorem dyadic_atom_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hsupp : ∀ m, 2 ≤ m → (∀ k, 1 ≤ k → m ≠ 2 ^ k) → lam m = ArithmeticFunction.vonMangoldt m)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, |normDeficit lam (2 ^ (i + 1))| ≤ M * (3 + Real.log ((2 ^ (i + 1) : ℕ) : ℝ))) (j : ℕ) :
    2 * |normDeficit lam (2 ^ (j + 1))| * riemannAutocorr 0 ≤
      M * (3 + Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) * (1.521 * riemannAutocorr 0) := by
  have hK0 := riemannAutocorr_zero_pos
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, n = fun i => 2 ^ (i + 1) := ⟨_, rfl⟩
  have hni : ∀ i, n i = 2 ^ (i + 1) := fun i => by rw [hn]
  have hlogn : ∀ i, Real.log (n i) = (i + 1 : ℕ) * Real.log 2 := fun i => by
    rw [hni]; exact log_two_pow_succ i
  have hM' : ∀ i, |normDeficit lam (n i)| ≤ M * (3 + Real.log (n i)) := fun i => by
    rw [hni]; exact hM i
  rw [show (2 : ℕ) ^ (j + 1) = n j from (hni j).symm]
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = normDeficit lam := ⟨_, rfl⟩
  rw [← hvdef] at hM' ⊢
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = Real.log (n j) := ⟨_, rfl⟩
  rw [← hc₀]
  have hc₀e : c₀ = (j + 1 : ℕ) * Real.log 2 := by rw [hc₀, hlogn]
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀e]; positivity
  obtain ⟨wj, hwj⟩ : ∃ wj : ℝ, wj = 3 + c₀ := ⟨_, rfl⟩
  rw [← hwj]
  have hwj3 : 3 ≤ wj := by rw [hwj]; linarith
  have hinj : Function.Injective n := by
    intro a b hab
    rw [hni, hni] at hab
    have := Nat.pow_right_injective (le_refl 2) hab
    omega
  -- the majorant
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun k => dyadicDecay (k + 1) := ⟨_, rfl⟩
  have hg0 : ∀ k, 0 ≤ g k := fun k => by rw [hg]; exact dyadicDecay_nonneg _
  have hgs : Summable g := by rw [hg]; exact dyadicDecay_summable
  have hgt : ∑' k, g k ≤ 0.1875 := by rw [hg]; exact tsum_dyadicDecay_le
  obtain ⟨hS3, hS3t⟩ := tsum_dyadicDecay_shift_le j
  obtain ⟨hS2, hS2t⟩ := sum_shift_reflect_le hg0 hgs j
  set P : ℝ := M * wj * riemannAutocorr 0 with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℝ, β = fun i => P * (4 * g i + 2 * dyadicDecay (i + j + 2) +
      2 * ((if j < i then g (i - j - 1) else 0) + (if i < j then g (j - i - 1) else 0))) := ⟨_, rfl⟩
  have hβs : Summable β := by
    rw [hβ]; exact (((hgs.mul_left 4).add (hS3.mul_left 2)).add (hS2.mul_left 2)).mul_left _
  have hβt : ∑' i, β i ≤ P * 1.521 := by
    rw [hβ, tsum_mul_left, Summable.tsum_add ((hgs.mul_left 4).add (hS3.mul_left 2)) (hS2.mul_left 2),
      Summable.tsum_add (hgs.mul_left 4) (hS3.mul_left 2), tsum_mul_left, tsum_mul_left, tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ hP0
    linarith
  -- weighted decay at a lattice distance `k ≥ 1`
  have hwK : ∀ i (k : ℕ), 1 ≤ k → 3 + Real.log (n i) ≤ wj * (1 + k * Real.log 2 / 3) →
      M * (3 + Real.log (n i)) * riemannAutocorr (k * Real.log 2) ≤ P * dyadicDecay k := by
    intro i k hk hw
    have h := dyadic_weighted_autocorr_le hk
    have hKD := riemannAutocorr_nonneg (k * Real.log 2)
    have hw0 : 0 ≤ 3 + Real.log (n i) := by rw [hlogn]; positivity
    calc M * (3 + Real.log (n i)) * riemannAutocorr (k * Real.log 2)
        ≤ M * (wj * (1 + k * Real.log 2 / 3)) * riemannAutocorr (k * Real.log 2) := by gcongr
      _ = M * wj * ((1 + k * Real.log 2 / 3) * riemannAutocorr (k * Real.log 2)) := by ring
      _ ≤ M * wj * (dyadicDecay k * riemannAutocorr 0) := by gcongr
      _ = P * dyadicDecay k := by rw [hP]; ring
  have hwbase : ∀ i, 3 + Real.log (n i) ≤ wj * (1 + ((i + 1 : ℕ) : ℝ) * Real.log 2 / 3) := by
    intro i
    rw [hlogn]
    have h : 3 + ((i + 1 : ℕ) : ℝ) * Real.log 2 = 3 * (1 + ((i + 1 : ℕ) : ℝ) * Real.log 2 / 3) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_right hwj3 (by positivity)
  -- the limit over truncations
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨L₁, hL₁⟩ := exists_truncatedRiemannAutocorr_zero_ge
    (η := δ / (4 * (|v (n j)| + 1))) (by positivity)
  obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (1 + 1 * Real.exp (c₀ / 2)) ^ 2 := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨L₂, hL₂⟩ := exists_nearRadicalEnergy_le (ε := δ / (2 * (Q + 1))) (by positivity)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = max L₁ L₂ := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = if 0 ≤ v (n j) then -1 else 1 := ⟨_, rfl⟩
  have hεabs : |ε| = 1 := by rw [hε]; split_ifs <;> norm_num
  have hε2 : ε ^ 2 = 1 := by rw [hε]; split_ifs <;> norm_num
  have hεv : ε * v (n j) = -|v (n j)| := by
    rw [hε]; split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hfd : ContDiff ℝ 2 (pairRiemannKernel L c₀ ε) := contDiff_pairRiemannKernel L c₀ ε
  have hfc : HasCompactSupport (pairRiemannKernel L c₀ ε) := hasCompactSupport_pairRiemannKernel L c₀ ε
  have hWL : ‖zetaZeroConfig.W (pairRiemannKernel L c₀ ε) (pairRiemannKernel L c₀ ε)‖ ≤ δ / 2 := by
    have h1 := norm_W_pairRiemannKernel_le L hc₀0 ε hΛ'
    rw [hεabs, ← hQ] at h1
    have h2 := hL₂ L (by rw [hL]; exact le_max_right _ _)
    calc _ ≤ Q * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := h1
      _ ≤ Q * (δ / (2 * (Q + 1))) := mul_le_mul_of_nonneg_left h2 hQ0
      _ ≤ δ / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hKL0 := hL₁ L (by rw [hL]; exact le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℂ, k = EF.weilTest (pairRiemannKernel L c₀ ε) (pairRiemannKernel L c₀ ε) :=
    ⟨_, rfl⟩
  have hkc : HasCompactSupport k := hk ▸ EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨KL, hKL⟩ : ∃ KL : ℝ → ℝ, KL = truncatedRiemannAutocorr L := ⟨_, rfl⟩
  have hKLle : ∀ y, KL y ≤ riemannAutocorr y := fun y => hKL ▸ truncatedRiemannAutocorr_le_riemannAutocorr L y
  have hKLnn : ∀ y, 0 ≤ KL y := fun y => hKL ▸ truncatedRiemannAutocorr_nonneg L y
  have hKLneg : ∀ y, KL (-y) = KL y := fun y => hKL ▸ truncatedRiemannAutocorr_neg L y
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun m : ℕ =>
      4 * KL (Real.log (m : ℝ)) + 2 * ε * (KL (Real.log (m : ℝ) + c₀) + KL (Real.log (m : ℝ) - c₀)) :=
    ⟨_, rfl⟩
  have hkT : ∀ m : ℕ, k (Real.log m) + k (-Real.log m) = ((T m : ℝ) : ℂ) := by
    intro m
    rw [hk, weilTest_pairRiemannKernel, weilTest_pairRiemannKernel, hε2, ← hKL, hT]
    have e1 := hKLneg (Real.log m)
    have e2 : KL (-Real.log m + c₀) = KL (Real.log m - c₀) := by
      rw [show -Real.log m + c₀ = -(Real.log m - c₀) by ring]; exact hKLneg _
    have e3 : KL (-Real.log m - c₀) = KL (Real.log m + c₀) := by
      rw [show -Real.log m - c₀ = -(Real.log m + c₀) by ring]; exact hKLneg _
    simp only
    rw [e1, e2, e3]; push_cast; ring
  have hpos := hW _ hfd hfc
  rw [← hk, weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt, hk,
    ← zeta_W_eq_weilFullFunctional hfd hfc, ← hk] at hpos
  set a : ℕ → ℝ := fun m => if 2 ≤ m then
      (lam m - ArithmeticFunction.vonMangoldt m) / Real.sqrt m else 0 with ha
  have hav : ∀ m, a m = -v m := by
    intro m; rw [hvdef]; simp only [ha, normDeficit]; split_ifs <;> ring
  have hsum := summable_primeAtoms a hkc
  rw [Complex.sub_re, Complex.re_tsum hsum] at hpos
  have hre : ∀ m : ℕ, (((a m : ℝ) : ℂ) * (k (Real.log m) + k (-Real.log m))).re = -(v m * T m) := by
    intro m; rw [hkT, ← Complex.ofReal_mul, Complex.ofReal_re, hav]; ring
  obtain ⟨N₁, hN₁⟩ := exists_forall_log_eq_zero hkc
  have hTz : ∀ m, N₁ ≤ m → T m = 0 := by
    intro m hm
    obtain ⟨h1, h2⟩ := hN₁ m hm
    have := hkT m
    rw [h1, h2, add_zero] at this
    exact_mod_cast this.symm
  have hvz : ∀ m, m ∉ Set.range n → v m = 0 := by
    intro m hm
    rw [hvdef]; simp only [normDeficit]
    split_ifs with h2
    · rw [hsupp m h2 (fun k hk hmk => hm ⟨k - 1, by rw [hni, Nat.sub_add_cancel hk, hmk]⟩),
        sub_self, zero_div]
    · rfl
  have hsupport : Function.support (fun m => v m * T m) ⊆ Set.range n := by
    intro m hm
    by_contra hc
    exact hm (by simp only; rw [hvz m hc, zero_mul])
  have hreindex : ∑' i, v (n i) * T (n i) = ∑' m, v m * T m :=
    hinj.tsum_eq (f := fun m => v m * T m) hsupport
  have hnii : ∀ i, i ≤ n i := fun i => by
    rw [hni]; exact le_of_lt (lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hsumT : Summable fun i => v (n i) * T (n i) :=
    summable_of_ne_finset_zero (s := Finset.range N₁) fun i hi => by
      rw [Finset.mem_range, not_lt] at hi
      rw [hTz (n i) (le_trans hi (hnii i)), mul_zero]
  have hmain : -(δ / 2) ≤ ∑' i, v (n i) * T (n i) := by
    rw [hreindex]
    have e : (∑' m : ℕ, (((a m : ℝ) : ℂ) * (k (Real.log m) + k (-Real.log m))).re) =
        -∑' m, v m * T m := by rw [← tsum_neg]; exact tsum_congr hre
    rw [e] at hpos
    have := Complex.re_le_norm (zetaZeroConfig.W (pairRiemannKernel L c₀ ε) (pairRiemannKernel L c₀ ε))
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, A = fun i => if i = j then 2 * |v (n j)| * KL 0 else (0 : ℝ) :=
    ⟨_, rfl⟩
  have hAs : Summable A := by
    rw [hA]; exact summable_of_ne_finset_zero (s := {j}) fun i hi => by
      rw [Finset.mem_singleton] at hi; rw [if_neg hi]
  have hAt : ∑' i, A i = 2 * |v (n j)| * KL 0 := by rw [hA, tsum_ite_eq]
  have hle : ∀ i, v (n i) * T (n i) + A i ≤ β i := by
    intro i
    have hMi := hM' i
    have hvi := abs_nonneg (v (n i))
    have hw0 : 0 ≤ 3 + Real.log (n i) := by rw [hlogn]; positivity
    -- term 1
    have hb1 : |v (n i)| * (4 * KL (Real.log (n i))) ≤ P * (4 * g i) := by
      have h := hwK i (i + 1) (by omega) (hwbase i)
      rw [← hlogn] at h
      have h2 := mul_le_mul hMi (hKLle (Real.log (n i))) (hKLnn _) (by positivity)
      have hgi : g i = dyadicDecay (i + 1) := by rw [hg]
      rw [hgi]
      calc |v (n i)| * (4 * KL (Real.log (n i))) = 4 * (|v (n i)| * KL (Real.log (n i))) := by ring
        _ ≤ 4 * (M * (3 + Real.log (n i)) * riemannAutocorr (Real.log (n i))) := by linarith
        _ ≤ 4 * (P * dyadicDecay (i + 1)) := by linarith
        _ = P * (4 * dyadicDecay (i + 1)) := by ring
    -- term 2
    have hb2 : |v (n i)| * (2 * KL (Real.log (n i) + c₀)) ≤ P * (2 * dyadicDecay (i + j + 2)) := by
      have hsumlog : Real.log (n i) + c₀ = ((i + j + 2 : ℕ) : ℝ) * Real.log 2 := by
        rw [hlogn, hc₀e]; push_cast; ring
      have hw : 3 + Real.log (n i) ≤ wj * (1 + ((i + j + 2 : ℕ) : ℝ) * Real.log 2 / 3) := by
        have h := hwbase i
        have hc : ((i + 1 : ℕ) : ℝ) ≤ ((i + j + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ i + j + 2)
        have hl : ((i + 1 : ℕ) : ℝ) * Real.log 2 / 3 ≤ ((i + j + 2 : ℕ) : ℝ) * Real.log 2 / 3 := by
          have := mul_le_mul_of_nonneg_right hc hl0.le; linarith
        have : wj * (1 + ((i + 1 : ℕ) : ℝ) * Real.log 2 / 3) ≤
            wj * (1 + ((i + j + 2 : ℕ) : ℝ) * Real.log 2 / 3) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      have h := hwK i (i + j + 2) (by omega) hw
      rw [← hsumlog] at h
      have h2 := mul_le_mul hMi (hKLle (Real.log (n i) + c₀)) (hKLnn _) (by positivity)
      calc |v (n i)| * (2 * KL (Real.log (n i) + c₀)) = 2 * (|v (n i)| * KL (Real.log (n i) + c₀)) := by
            ring
        _ ≤ 2 * (M * (3 + Real.log (n i)) * riemannAutocorr (Real.log (n i) + c₀)) := by linarith
        _ ≤ 2 * (P * dyadicDecay (i + j + 2)) := by linarith
        _ = P * (2 * dyadicDecay (i + j + 2)) := by ring
    have hTi : T (n i) = 4 * KL (Real.log (n i)) +
        2 * ε * (KL (Real.log (n i) + c₀) + KL (Real.log (n i) - c₀)) := by rw [hT]
    have hβi : β i = P * (4 * g i + 2 * dyadicDecay (i + j + 2) +
        2 * ((if j < i then g (i - j - 1) else 0) + (if i < j then g (j - i - 1) else 0))) := by rw [hβ]
    have hAi : A i = if i = j then 2 * |v (n j)| * KL 0 else 0 := by rw [hA]
    rw [hTi, hβi, hAi]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, ← hc₀, sub_self, if_neg (lt_irrefl _)]
      have hat := pair_atom_le (c := v (n i)) (ε := ε) (K1 := KL c₀)
        (K2 := KL (c₀ + c₀)) (K0 := KL 0) hεv (hKLnn _) (hKLnn _)
      rw [← hc₀] at hb1 hb2
      have e : |v (n i)| * (4 * KL c₀ + 2 * KL (c₀ + c₀)) =
          |v (n i)| * (4 * KL c₀) + |v (n i)| * (2 * KL (c₀ + c₀)) := by ring
      have e2 : P * (4 * g i + 2 * dyadicDecay (i + i + 2) + 2 * (0 + 0)) =
          P * (4 * g i) + P * (2 * dyadicDecay (i + i + 2)) := by ring
      rw [e2]
      calc v (n i) * (4 * KL c₀ + 2 * ε * (KL (c₀ + c₀) + KL 0)) + 2 * |v (n i)| * KL 0
          ≤ |v (n i)| * (4 * KL c₀ + 2 * KL (c₀ + c₀)) := hat
        _ = |v (n i)| * (4 * KL c₀) + |v (n i)| * (2 * KL (c₀ + c₀)) := e
        _ ≤ P * (4 * g i) + P * (2 * dyadicDecay (i + i + 2)) := add_le_add hb1 hb2
    · rw [if_neg hij, add_zero]
      -- the off-atom lattice distance
      obtain ⟨hdk1, hdkeq0, hgd0⟩ := dyadic_offdiag hij
      set dk := Nat.dist i j with hdk
      have hdkeq : |Real.log (n i) - c₀| = dk * Real.log 2 := by rw [hlogn, hc₀e]; exact hdkeq0
      have hgd : (if j < i then g (i - j - 1) else 0) + (if i < j then g (j - i - 1) else 0) =
          dyadicDecay dk := by
        have e1 : ∀ m, g m = dyadicDecay (m + 1) := fun m => by rw [hg]
        rw [e1, e1]; exact hgd0
      rw [hgd]
      have hKabs : KL (Real.log (n i) - c₀) = KL |Real.log (n i) - c₀| := by
        rcases le_or_gt 0 (Real.log (n i) - c₀) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h, hKLneg]
      rw [hKabs]
      have ht := pair_term_le (c := v (n i)) (K1 := KL (Real.log (n i))) (K2 := KL (Real.log (n i) + c₀))
        (K3 := KL |Real.log (n i) - c₀|) hεabs (hKLnn _) (hKLnn _) (hKLnn _)
      have hb3 : |v (n i)| * (2 * KL |Real.log (n i) - c₀|) ≤ P * (2 * dyadicDecay dk) := by
        have hw : 3 + Real.log (n i) ≤ wj * (1 + dk * Real.log 2 / 3) := by
          rw [← hdkeq, hwj]
          exact three_add_le_mul hc₀0
        have h := hwK i dk hdk1 hw
        rw [← hdkeq] at h
        have h2 := mul_le_mul hMi (hKLle |Real.log (n i) - c₀|) (hKLnn _) (by positivity)
        calc |v (n i)| * (2 * KL |Real.log (n i) - c₀|) = 2 * (|v (n i)| * KL |Real.log (n i) - c₀|) := by
              ring
          _ ≤ 2 * (M * (3 + Real.log (n i)) * riemannAutocorr |Real.log (n i) - c₀|) := by linarith
          _ ≤ 2 * (P * dyadicDecay dk) := by linarith
          _ = P * (2 * dyadicDecay dk) := by ring
      have e : |v (n i)| * (4 * KL (Real.log (n i)) + 2 * KL (Real.log (n i) + c₀) +
          2 * KL |Real.log (n i) - c₀|) = |v (n i)| * (4 * KL (Real.log (n i))) +
          |v (n i)| * (2 * KL (Real.log (n i) + c₀)) + |v (n i)| * (2 * KL |Real.log (n i) - c₀|) := by
        ring
      have e2 : P * (4 * g i + 2 * dyadicDecay (i + j + 2) + 2 * dyadicDecay dk) =
          P * (4 * g i) + P * (2 * dyadicDecay (i + j + 2)) + P * (2 * dyadicDecay dk) := by ring
      linarith
  have hsum2 : ∑' i, (v (n i) * T (n i) + A i) ≤ ∑' i, β i :=
    (hsumT.add hAs).tsum_le_tsum hle hβs
  rw [hsumT.tsum_add hAs, hAt] at hsum2
  have hcorr : 2 * |v (n j)| * (δ / (4 * (|v (n j)| + 1))) ≤ δ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have := abs_nonneg (v (n j)); nlinarith
  have hKL0' : riemannAutocorr 0 - δ / (4 * (|v (n j)| + 1)) ≤ KL 0 := by rw [hKL]; exact hKL0
  have hv0 := abs_nonneg (v (n j))
  have hmul : 2 * |v (n j)| * (riemannAutocorr 0 - δ / (4 * (|v (n j)| + 1))) ≤ 2 * |v (n j)| * KL 0 :=
    mul_le_mul_of_nonneg_left hKL0' (by positivity)
  have hPe : P * 1.521 = M * wj * (1.521 * riemannAutocorr 0) := by rw [hP]; ring
  linarith

/-- **The dyadic line is rigid.** A Weil-positive system that agrees with `Λ` except at the powers
`2^k` (`k ≥ 1`) is `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_powers_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hsupp : ∀ m, 2 ≤ m → (∀ k, 1 ≤ k → m ≠ 2 ^ k) → lam m = ArithmeticFunction.vonMangoldt m) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  obtain ⟨C₀, hC₀⟩ := abs_le_of_weilPositive (weilPositive_of_weilPositiveFull hW)
  obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ, n = fun i => 2 ^ (i + 1) := ⟨_, rfl⟩
  have hni : ∀ i, n i = 2 ^ (i + 1) := fun i => by rw [hn]
  have hn2 : ∀ i, 2 ≤ n i := fun i => by
    rw [hni, pow_succ]; have := Nat.one_le_two_pow (n := i); omega
  set B : ℝ := 2 + |C₀| with hB
  have hw : ∀ i, 0 < 3 + Real.log (n i) := fun i => by
    have := Real.log_natCast_nonneg (n i); linarith
  have hbox : ∀ i, |normDeficit lam (n i)| ≤ B * (3 + Real.log (n i)) := by
    intro i
    have hsq1 : 1 ≤ Real.sqrt (n i) := by
      rw [Real.one_le_sqrt]; exact_mod_cast (by have := hn2 i; omega : 1 ≤ n i)
    have hsq0 : 0 < Real.sqrt (n i) := by linarith
    have hlog0 := Real.log_natCast_nonneg (n i)
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n i)
    have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt (n i) := ArithmeticFunction.vonMangoldt_nonneg
    have hl := hC₀ (n i) (hn2 i)
    simp only [normDeficit, if_pos (hn2 i)]
    rw [abs_div, abs_of_pos hsq0, div_le_iff₀ hsq0]
    have h1 : |(ArithmeticFunction.vonMangoldt (n i) : ℝ) - lam (n i)| ≤
        Real.log (n i) + Real.sqrt (n i) * (Real.log (n i) + C₀) := by
      calc _ ≤ |(ArithmeticFunction.vonMangoldt (n i) : ℝ)| + |lam (n i)| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hΛ0]; linarith
    have h2 : Real.log (n i) ≤ Real.log (n i) * Real.sqrt (n i) := le_mul_of_one_le_right hlog0 hsq1
    have h3 : C₀ ≤ |C₀| := le_abs_self C₀
    have h4 : Real.sqrt (n i) * C₀ ≤ Real.sqrt (n i) * |C₀| := mul_le_mul_of_nonneg_left h3 hsq0.le
    have h5 : 0 ≤ Real.sqrt (n i) * |C₀| * Real.log (n i) := by positivity
    have h6 : 0 ≤ Real.sqrt (n i) * |C₀| := by positivity
    nlinarith
  set r : ℕ → ℝ := fun i => |normDeficit lam (n i)| / (3 + Real.log (n i)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => div_nonneg (abs_nonneg _) (hw i).le
  have hrB : ∀ i, r i ≤ B := fun i => by
    simp only [hr]; rw [div_le_iff₀ (hw i)]; exact hbox i
  have hbdd : BddAbove (Set.range r) := ⟨B, by rintro _ ⟨i, rfl⟩; exact hrB i⟩
  set M := ⨆ i, r i with hMdef
  have hM0 : 0 ≤ M := le_trans (hr0 0) (le_ciSup hbdd 0)
  have hM : ∀ i, |normDeficit lam (n i)| ≤ M * (3 + Real.log (n i)) := fun i => by
    have := le_ciSup hbdd i
    simp only [hr] at this
    rwa [div_le_iff₀ (hw i)] at this
  have hM2 : ∀ i, |normDeficit lam (2 ^ (i + 1))| ≤ M * (3 + Real.log ((2 ^ (i + 1) : ℕ) : ℝ)) :=
    fun i => by rw [← hni]; exact hM i
  have hK0 := riemannAutocorr_zero_pos
  have hrle : ∀ j, r j ≤ 0.7605 * M := by
    intro j
    have h := dyadic_atom_le hW hsupp hM0 hM2 j
    rw [← hni] at h
    simp only [hr]
    rw [div_le_iff₀ (hw j)]
    have e : M * (3 + Real.log (n j)) * (1.521 * riemannAutocorr 0) =
        (2 * (0.7605 * M * (3 + Real.log (n j)))) * riemannAutocorr 0 := by ring
    rw [e, mul_assoc 2] at h
    have := le_of_mul_le_mul_right (by linarith : 2 * |normDeficit lam (n j)| * riemannAutocorr 0 ≤
      2 * (0.7605 * M * (3 + Real.log (n j))) * riemannAutocorr 0) hK0
    linarith
  have hMle : M ≤ 0.7605 * M := ciSup_le hrle
  have hMz : M = 0 := by linarith
  intro m hm
  by_cases hmr : ∃ k, 1 ≤ k ∧ m = 2 ^ k
  · obtain ⟨k, hk, rfl⟩ := hmr
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := hM j
    rw [hMz, zero_mul, hni] at h
    have hv : normDeficit lam (2 ^ (j + 1)) = 0 := abs_nonpos_iff.mp h
    simp only [normDeficit, if_pos hm] at hv
    have hsq : Real.sqrt ((2 ^ (j + 1) : ℕ) : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast (by positivity : 0 < 2 ^ (j + 1)))).ne'
    rw [div_eq_zero_iff, sub_eq_zero] at hv
    rcases hv with hv | hv
    · exact hv.symm
    · exact absurd hv hsq
  · exact hsupp m hm fun k hk hmk => hmr ⟨k, hk, hmk⟩

end

end RHTower
