import GaloisForLFunctions.RHTower.Sieve.SieveBoundSharp
import GaloisForLFunctions.RHTower.MultiplicativeLargeSieve
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanCosecantInequality

/-!
# The large sieve with the Montgomery–Vaughan constant `N + Q² − 1`

The window sandwich gives the log-free large sieve with constant `N + 2Q² − 1`. The
Montgomery–Vaughan cosecant inequality removes the factor two:

* for frequencies `δ`-separated modulo one and any window of `K` integers,
  `Σ_{A<n≤A+K} |Σ_r b_r e(nα_r)|² ≤ (K + δ⁻¹) Σ |b_r|²` — the window sum of `e(nθ)` is
  `(e((A+K+½)θ) − e((A+½)θ))/(2i sin πθ)`, and each of the two cosecant forms is at most
  `δ⁻¹ Σ |b_r|²`;
* distinct Farey fractions of order `Q ≥ 2`, and distinct roots of unity of order at most `Q`, are
  `1/(Q(Q−1))`-separated (`1/(qq')` for distinct denominators, `1/q` for equal ones), and
  `Q(Q − 1) ≤ Q² − 1`.

Consequences, each with constant `N + Q² − 1` in place of `N + 2Q² − 1`: the Farey large sieve
`Σ_{q ≤ Q} Σ_{(a,q)=1} |Σ_{n<N} c_n e(na/q)|² ≤ (N + Q² − 1) Σ |c_n|²`, the large sieve over roots
of unity, the multiplicative large sieve over primitive characters, Montgomery's sieve inequality
and the resulting sieve bound for sets of integers.
-/

open Finset RHTower.Sieve
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

open GaloisForLFunctions.HilbertInequality

/-! ## §1. The window sum of a circle frequency and the dual large sieve -/

/-- `2i sin(πθ) Σ_{A<n≤A+K} e(nθ) = e((A+K+½)θ) − e((A+½)θ)`: the sum telescopes against
`e(θ/2) − e(−θ/2) = 2i sin(πθ)`. -/
theorem two_I_sin_mul_window_sum (θ : ℝ) (A K : ℕ) :
    2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ) *
        ∑ n ∈ Icc (A + 1) (A + K), circleFreq ((n : ℝ) * θ) =
      circleFreq (((A + K : ℕ) + 1 / 2 : ℝ) * θ) - circleFreq (((A : ℕ) + 1 / 2 : ℝ) * θ) := by
  have hstep (x : ℝ) : 2 * Complex.I * (Real.sin (Real.pi * θ) : ℂ) * circleFreq (x * θ) =
      circleFreq ((x + 1 / 2) * θ) - circleFreq ((x - 1 / 2) * θ) := by
    simp only [circleFreq]
    rw [Complex.ofReal_sin, Complex.sin, show ((x + 1 / 2) * θ) = x * θ + θ / 2 by ring,
      show ((x - 1 / 2) * θ) = x * θ - θ / 2 by ring]
    push_cast
    rw [show (2 * (Real.pi : ℂ) * (x * θ + θ / 2)) * Complex.I =
        2 * Real.pi * (x * θ) * Complex.I + Real.pi * θ * Complex.I by ring,
      show (2 * (Real.pi : ℂ) * (x * θ - θ / 2)) * Complex.I =
        2 * Real.pi * (x * θ) * Complex.I + -(Real.pi * θ * Complex.I) by ring,
      Complex.exp_add, Complex.exp_add]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [show -((Real.pi : ℂ) * θ * Complex.I) = -((Real.pi : ℂ) * θ) * Complex.I by ring]
    linear_combination (Complex.exp (2 * Real.pi * (x * θ) * Complex.I)) *
      (Complex.exp (-(↑Real.pi * ↑θ) * Complex.I) - Complex.exp (↑Real.pi * ↑θ * Complex.I)) * hI
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show A + (K + 1) = A + K + 1 by ring, sum_Icc_succ_top (by omega), mul_add, ih,
      hstep]
    push_cast
    ring_nf


/-- The window sum of one frequency: `K` on the diagonal, the cosecant kernel off it. -/
theorem window_sum_eq (θ : ℝ) (hθ : θ = 0 ∨ ∀ m : ℤ, θ ≠ m) (A K : ℕ) :
    ∑ n ∈ Icc (A + 1) (A + K), circleFreq ((n : ℝ) * θ) =
      (if θ = 0 then (K : ℂ) else 0) +
        (circleFreq (((A + K : ℕ) + 1 / 2 : ℝ) * θ) - circleFreq (((A : ℕ) + 1 / 2 : ℝ) * θ)) *
          (1 / (2 * Complex.I)) * ((1 / Real.sin (Real.pi * θ) : ℝ) : ℂ) := by
  rcases hθ with rfl | hθ
  · simp only [mul_zero, sub_self, zero_mul, Real.sin_zero, div_zero, Complex.ofReal_zero,
      mul_zero, add_zero, if_true]
    rw [show circleFreq 0 = 1 by simp [circleFreq], sum_const, Nat.card_Icc, nsmul_one,
      show A + K + 1 - (A + 1) = K by omega]
  · have hsin : Real.sin (Real.pi * θ) ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
      exact hθ n (by nlinarith [Real.pi_pos])
    have hθ0 : θ ≠ 0 := by exact_mod_cast hθ 0
    rw [if_neg hθ0, zero_add, ← two_I_sin_mul_window_sum θ A K, Complex.ofReal_div,
      Complex.ofReal_one]
    have hs : (Real.sin (Real.pi * θ) : ℂ) ≠ 0 := by exact_mod_cast hsin
    generalize ∑ n ∈ Icc (A + 1) (A + K), circleFreq ((n : ℝ) * θ) = S
    generalize (Real.sin (Real.pi * θ) : ℂ) = s at hs ⊢
    field_simp

/-- **Large sieve with the Montgomery–Vaughan constant, dual form.** For frequencies
`δ`-separated modulo one and any window of `K` consecutive integers,
`Σ_{A<n≤A+K} |Σ_r b_r e(nα_r)|² ≤ (K + δ⁻¹) Σ |b_r|²`. -/
theorem sum_window_norm_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ toIntDist (α r - α s)) (b : ι → ℂ) (A K : ℕ) :
    ∑ n ∈ Icc (A + 1) (A + K), ‖∑ r, b r * circleFreq ((n : ℝ) * α r)‖ ^ 2 ≤
      ((K : ℝ) + δ⁻¹) * ∑ r, ‖b r‖ ^ 2 := by
  set P : ℝ := ((A + K : ℕ) + 1 / 2 : ℝ)
  set B : ℝ := ((A : ℕ) + 1 / 2 : ℝ)
  set c : ι → ι → ℝ := fun r s => 1 / Real.sin (Real.pi * (α r - α s))
  set u : ι → ℂ := fun r => b r * circleFreq (P * α r) with hu
  set v : ι → ℂ := fun r => b r * circleFreq (B * α r) with hv
  have hsep' : ∀ r s, r ≠ s → ∀ m : ℤ, δ ≤ |α r - α s - m| := fun r s hrs m =>
    (hsep r s hrs).trans (round_le _ m)
  have hdiff : ∀ r s, α r - α s = 0 ∨ ∀ m : ℤ, α r - α s ≠ m := by
    intro r s
    by_cases hrs : r = s
    · exact Or.inl (by rw [hrs, sub_self])
    · refine Or.inr fun m hm => ?_
      have := hsep' r s hrs m
      rw [hm, sub_self, abs_zero] at this
      linarith
  have hzero : ∀ r s, α r - α s = 0 ↔ r = s := by
    intro r s
    refine ⟨fun h => ?_, fun h => by rw [h, sub_self]⟩
    by_contra hrs
    have := hsep' r s hrs 0
    rw [h, Int.cast_zero, sub_zero, abs_zero] at this
    linarith
  -- the expansion of the window energy
  have hcf (x y : ℝ) : circleFreq x * conj (circleFreq y) = circleFreq (x - y) := by
    rw [mul_comm, conj_circleFreq_mul]
  have hexp : ((∑ n ∈ Icc (A + 1) (A + K), ‖∑ r, b r * circleFreq ((n : ℝ) * α r)‖ ^ 2 : ℝ) : ℂ) =
      (K : ℂ) * ((∑ r, ‖b r‖ ^ 2 : ℝ) : ℂ) + 1 / (2 * Complex.I) *
        (∑ r, ∑ s, u r * conj (u s) * (c r s : ℂ) - ∑ r, ∑ s, v r * conj (v s) * (c r s : ℂ)) := by
    have h1 : ∀ n : ℕ, ((‖∑ r, b r * circleFreq ((n : ℝ) * α r)‖ ^ 2 : ℝ) : ℂ) =
        ∑ r, ∑ s, b r * conj (b s) * circleFreq ((n : ℝ) * (α r - α s)) := by
      intro n
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
      refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
      rw [map_mul, mul_sub, ← hcf]
      ring
    rw [Complex.ofReal_sum, sum_congr rfl fun n _ => h1 n]
    have h2 : ∀ r s, ∑ n ∈ Icc (A + 1) (A + K), b r * conj (b s) *
        circleFreq ((n : ℝ) * (α r - α s)) =
        b r * conj (b s) * ((if r = s then (K : ℂ) else 0) +
          (circleFreq (P * α r) * conj (circleFreq (P * α s)) -
            circleFreq (B * α r) * conj (circleFreq (B * α s))) *
              (1 / (2 * Complex.I)) * (c r s : ℂ)) := by
      intro r s
      rw [← mul_sum, window_sum_eq _ (hdiff r s), hcf, hcf, ← mul_sub, ← mul_sub]
      simp only [hzero r s]
      rfl
    rw [sum_comm]
    refine (sum_congr rfl fun r _ => sum_comm).trans ?_
    simp_rw [h2]
    have hdiag : ∑ r, ∑ s, b r * conj (b s) * (if r = s then (K : ℂ) else 0) =
        (K : ℂ) * ((∑ r, ‖b r‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, mul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [sum_eq_single r (fun s _ hs => by rw [if_neg (Ne.symm hs), mul_zero])
        (fun h => absurd (mem_univ r) h), if_pos rfl, Complex.ofReal_pow, ← Complex.mul_conj']
      ring
    simp only [mul_add, sum_add_distrib]
    rw [hdiag]
    congr 1
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    simp only [hu, hv, map_mul]
    ring
  -- both cosecant forms are bounded by the Montgomery–Vaughan inequality
  have hnu : ∑ r, ‖u r‖ ^ 2 = ∑ r, ‖b r‖ ^ 2 :=
    sum_congr rfl fun r _ => by rw [hu, norm_mul, norm_circleFreq, mul_one]
  have hnv : ∑ r, ‖v r‖ ^ 2 = ∑ r, ‖b r‖ ^ 2 :=
    sum_congr rfl fun r _ => by rw [hv, norm_mul, norm_circleFreq, mul_one]
  have hU := norm_sum_mul_conj_div_sin_le α hδ hsep' u
  have hV := norm_sum_mul_conj_div_sin_le α hδ hsep' v
  rw [hnu] at hU
  rw [hnv] at hV
  have hnn : 0 ≤ ∑ n ∈ Icc (A + 1) (A + K), ‖∑ r, b r * circleFreq ((n : ℝ) * α r)‖ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hX : 0 ≤ ∑ r, ‖b r‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h2I : ‖(1 : ℂ) / (2 * Complex.I)‖ = 1 / 2 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_I, Complex.norm_two, mul_one]
  have key := congrArg (‖·‖) hexp
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn] at key
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, h2I, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hX]
  have hsub := norm_sub_le (∑ r, ∑ s, u r * conj (u s) * (c r s : ℂ))
    (∑ r, ∑ s, v r * conj (v s) * (c r s : ℂ))
  nlinarith


/-! ## §2. Duality and the primal form -/

/-- **Duality.** A bound on the dual sums over a window transfers, with the same constant, to the
values of a trigonometric polynomial at the frequencies. -/
theorem sum_norm_sq_primal_le_of_dual' {ι : Type*} [Fintype ι] (α : ι → ℝ) (W : Finset ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hdual : ∀ b : ι → ℂ, ∑ n ∈ W, ‖∑ r, b r * circleFreq ((n : ℝ) * α r)‖ ^ 2 ≤
      C * ∑ r, ‖b r‖ ^ 2) (x : ℕ → ℂ) :
    ∑ r, ‖∑ n ∈ W, x n * circleFreq ((n : ℝ) * α r)‖ ^ 2 ≤ C * ∑ n ∈ W, ‖x n‖ ^ 2 := by
  set y : ι → ℂ := fun r => ∑ n ∈ W, x n * circleFreq ((n : ℝ) * α r) with hy
  set S := ∑ r, ‖y r‖ ^ 2 with hS
  set z : ℕ → ℂ := fun n => ∑ r, conj (y r) * circleFreq ((n : ℝ) * α r) with hz
  set X := ∑ n ∈ W, ‖x n‖ ^ 2 with hX
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hX0 : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hZ : ∑ n ∈ W, ‖z n‖ ^ 2 ≤ C * S := by
    have h := hdual fun r => conj (y r)
    simp only [Complex.norm_conj] at h
    exact h
  have hSz : (S : ℂ) = ∑ n ∈ W, x n * z n := by
    rw [hS, Complex.ofReal_sum]
    have h1 : ∀ r, ((‖y r‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ W, conj (y r) * (x n * circleFreq ((n : ℝ) * α r)) :=
      fun r => by rw [← mul_sum, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
    rw [sum_congr rfl fun r _ => h1 r, sum_comm]
    refine sum_congr rfl fun n _ => ?_
    rw [hz, mul_sum]
    exact sum_congr rfl fun r _ => by ring
  have hle : S ≤ ∑ n ∈ W, ‖x n‖ * ‖z n‖ := by
    have h := norm_sum_le W fun n => x n * z n
    rw [← hSz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at h
    exact h.trans_eq (sum_congr rfl fun n _ => norm_mul _ _)
  have hcs := sum_mul_sq_le_sq_mul_sq W (fun n => ‖x n‖) (fun n => ‖z n‖)
  have hsq : S ^ 2 ≤ X * (C * S) :=
    (pow_le_pow_left₀ hS0 hle 2).trans (hcs.trans (mul_le_mul_of_nonneg_left hZ hX0))
  rcases hS0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    exact mul_nonneg hC hX0

/-- **Large sieve with the Montgomery–Vaughan constant.** For frequencies `δ`-separated modulo
one, `Σ_r |Σ_{A<n≤A+K} x_n e(nα_r)|² ≤ (K + δ⁻¹) Σ |x_n|²`. -/
theorem largeSieve_separated_sharp {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ toIntDist (α r - α s)) (A K : ℕ) (x : ℕ → ℂ) :
    ∑ r, ‖∑ n ∈ Icc (A + 1) (A + K), x n * circleFreq ((n : ℝ) * α r)‖ ^ 2 ≤
      ((K : ℝ) + δ⁻¹) * ∑ n ∈ Icc (A + 1) (A + K), ‖x n‖ ^ 2 :=
  sum_norm_sq_primal_le_of_dual' α _ (by positivity)
    (fun b => sum_window_norm_sq_le α hδ hsep b A K) x

/-! ## §3. Farey points are `1/(Q(Q−1))`-separated -/

/-- Distinct Farey fractions of order `Q ≥ 2` are at circle distance at least `1/(Q(Q−1))`:
`1/(qq')` for distinct denominators and `1/q` for equal ones. -/
theorem fareySet_sep_sharp {Q : ℕ} (hQ : 2 ≤ Q) :
    ∀ p ∈ fareySet Q, ∀ r ∈ fareySet Q, p ≠ r →
      1 / ((Q : ℝ) * ((Q : ℝ) - 1)) ≤ toIntDist ((r.1 : ℝ) / (r.2 : ℝ) - (p.1 : ℝ) / (p.2 : ℝ)) := by
  intro p hp r hr hpr
  obtain ⟨⟨hp1, _⟩, ⟨hp2, hpQ⟩, hple, hpc⟩ := mem_fareySet.mp hp
  obtain ⟨⟨hr1, _⟩, ⟨hr2, hrQ⟩, hrle, hrc⟩ := mem_fareySet.mp hr
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQQ : (0 : ℝ) < (Q : ℝ) * ((Q : ℝ) - 1) := by nlinarith
  by_cases hq : r.2 = p.2
  · -- equal denominators: the difference is `(a − a')/q` with `0 < |a − a'| < q`
    have hne : r.1 ≠ p.1 := fun h => hpr (Prod.ext h.symm hq.symm)
    have hcross : ¬ (((r.2 * 1 : ℕ) : ℤ) ∣ ((r.1 : ℤ) - (p.1 : ℤ)) * ((1 : ℕ) : ℤ) - 0 * (r.2 : ℤ)) := by
      rintro ⟨k, hk⟩
      simp only [mul_one, Nat.cast_one, zero_mul, sub_zero] at hk
      have hr1' : r.1 ≤ r.2 := hrle
      have hp1' : p.1 ≤ r.2 := hq ▸ hple
      have hlt : |(r.1 : ℤ) - p.1| < r.2 := by
        rw [abs_lt]; constructor <;> omega
      rcases eq_or_ne k 0 with rfl | hk0
      · exact hne (by omega)
      · have : (r.2 : ℤ) ≤ |(r.1 : ℤ) - p.1| := by
          rw [hk, abs_mul, abs_of_pos (by exact_mod_cast hr2)]
          exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hk0)
        omega
    have h := RHTower.Sieve.one_div_le_toIntDist_farey (q := r.2) (q' := 1) hr2 one_pos
      (a := (r.1 : ℤ) - p.1) (a' := 0) hcross
    rw [show ((((r.1 : ℤ) - p.1 : ℤ) : ℝ) / (r.2 : ℝ) - ((0 : ℤ) : ℝ) / ((1 : ℕ) : ℝ)) =
      (r.1 : ℝ) / (r.2 : ℝ) - (p.1 : ℝ) / (p.2 : ℝ) by
        rw [← hq]; push_cast; ring] at h
    refine le_trans ?_ h
    have hr2R : (1 : ℝ) ≤ r.2 := by exact_mod_cast hr2
    have hrQR : (r.2 : ℝ) ≤ Q := by exact_mod_cast hrQ
    rw [Nat.cast_one, mul_one]
    exact one_div_le_one_div_of_le (by linarith) (by nlinarith)
  · -- distinct denominators: `qq' ≤ Q(Q − 1)`
    have hne : (r.1, r.2) ≠ (p.1, p.2) := by simpa using (Ne.symm hpr)
    have hcross := RHTower.Sieve.not_dvd_farey_cross hr2 hp2 hr1 hrle hp1 hple hrc hpc hne
    have h := RHTower.Sieve.one_div_le_toIntDist_farey (q := r.2) (q' := p.2) hr2 hp2
      (a := (r.1 : ℤ)) (a' := (p.1 : ℤ)) hcross
    push_cast at h
    refine le_trans ?_ h
    have hprod : (r.2 : ℝ) * (p.2 : ℝ) ≤ (Q : ℝ) * ((Q : ℝ) - 1) := by
      have : r.2 * p.2 ≤ Q * (Q - 1) := by
        rcases lt_or_gt_of_ne hq with h | h
        · calc r.2 * p.2 ≤ (Q - 1) * Q := Nat.mul_le_mul (by omega) hpQ
            _ = Q * (Q - 1) := mul_comm _ _
        · exact Nat.mul_le_mul hrQ (by omega)
      have h1 : ((Q * (Q - 1) : ℕ) : ℝ) = (Q : ℝ) * ((Q : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [← h1]
      exact_mod_cast this
    have hpos : (0 : ℝ) < (r.2 : ℝ) * (p.2 : ℝ) := by
      have : (0 : ℝ) < r.2 := by exact_mod_cast hr2
      have : (0 : ℝ) < p.2 := by exact_mod_cast hp2
      positivity
    exact one_div_le_one_div_of_le hpos hprod


/-! ## §4. The large sieve at Farey points with constant `N + Q² − 1` -/

theorem inv_farey_delta_le {Q : ℕ} (hQ : 2 ≤ Q) :
    (1 / ((Q : ℝ) * ((Q : ℝ) - 1)))⁻¹ ≤ (Q : ℝ) ^ 2 - 1 := by
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  rw [one_div, inv_inv]
  nlinarith

/-- **Large sieve at the Farey points of order `Q`, Montgomery–Vaughan constant.**
`Σ_{a/q ∈ F_Q} |Σ_{A<n≤A+K} x_n e(na/q)|² ≤ (K + Q² − 1) Σ |x_n|²`. -/
theorem largeSieve_fareySet_sharp (A K : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (x : ℕ → ℂ) :
    ∑ p ∈ fareySet Q, ‖∑ n ∈ Icc (A + 1) (A + K),
        x n * circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ 2 ≤
      ((K : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ n ∈ Icc (A + 1) (A + K), ‖x n‖ ^ 2 := by
  classical
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hδ : (0 : ℝ) < 1 / ((Q : ℝ) * ((Q : ℝ) - 1)) := by
    have : (0 : ℝ) < (Q : ℝ) * ((Q : ℝ) - 1) := by nlinarith
    positivity
  have h := largeSieve_separated_sharp (ι := fareySet Q)
    (fun p => ((p : ℕ × ℕ).1 : ℝ) / ((p : ℕ × ℕ).2 : ℝ)) hδ
    (fun p r hpr => fareySet_sep_sharp hQ r r.2 p p.2
      (fun h => hpr (Subtype.ext h.symm))) A K x
  rw [Finset.sum_coe_sort (fareySet Q) (fun p : ℕ × ℕ => ‖∑ n ∈ Icc (A + 1) (A + K),
    x n * circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ 2)] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
  linarith [inv_farey_delta_le hQ]

/-- Moving the window `[0, N)` to `[1, N]` does not change the modulus. -/
theorem norm_sum_range_circleFreq_eq (N : ℕ) (y : ℕ → ℂ) (θ : ℝ) :
    ‖∑ n ∈ range N, y n * circleFreq ((n : ℝ) * θ)‖ =
      ‖∑ k ∈ Icc (0 + 1) (0 + N), y (k - 1) * circleFreq ((k : ℝ) * θ)‖ := by
  have h : ∑ k ∈ Icc (0 + 1) (0 + N), y (k - 1) * circleFreq ((k : ℝ) * θ) =
      circleFreq θ * ∑ n ∈ range N, y n * circleFreq ((n : ℝ) * θ) := by
    rw [show Icc (0 + 1) (0 + N) = Ico (0 + 1) (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      ← sum_Ico_add' (fun k => y (k - 1) * circleFreq ((k : ℝ) * θ)) 0 N 1, range_eq_Ico, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [Nat.add_sub_cancel, ← circleFreq_pow, ← circleFreq_pow, pow_succ]
    ring
  rw [h, norm_mul, norm_circleFreq, one_mul]


/-- **Large sieve at Farey points on the window `[0, N)`.** -/
theorem largeSieve_fareySet_range_sharp (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (y : ℕ → ℂ) :
    ∑ p ∈ fareySet Q, ‖∑ n ∈ range N, y n * circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ n ∈ range N, ‖y n‖ ^ 2 := by
  have h := largeSieve_fareySet_sharp 0 N hQ (fun k => y (k - 1))
  have hre : ∑ k ∈ Icc (0 + 1) (0 + N), ‖y (k - 1)‖ ^ 2 = ∑ n ∈ range N, ‖y n‖ ^ 2 := by
    rw [show Icc (0 + 1) (0 + N) = Ico (0 + 1) (N + 1) by ext; simp only [mem_Icc, mem_Ico]; omega,
      ← sum_Ico_add' (fun k => ‖y (k - 1)‖ ^ 2) 0 N 1, range_eq_Ico]
    simp only [Nat.add_sub_cancel]
  rw [hre] at h
  refine le_of_eq_of_le (sum_congr rfl fun p _ => ?_) h
  rw [norm_sum_range_circleFreq_eq]

/-- **The Farey large sieve in textbook form, constant `N + Q² − 1`.** -/
theorem largeSieve_expSum_fareySet_sharp (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ p ∈ fareySet Q, ‖RHTower.Sieve.expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ n : Fin N, ‖c n‖ ^ 2 := by
  set y : ℕ → ℂ := fun n => if h : n < N then c ⟨n, h⟩ else 0 with hy
  have hexp : ∀ θ : ℝ, RHTower.Sieve.expSum N c θ =
      ∑ n ∈ range N, y n * circleFreq ((n : ℝ) * θ) := by
    intro θ
    rw [RHTower.Sieve.expSum, ← Fin.sum_univ_eq_sum_range (fun n => y n * circleFreq ((n : ℝ) * θ))]
    refine sum_congr rfl fun n _ => ?_
    simp only [hy, dif_pos n.isLt, circleFreq_pow]
  have hc : ∑ n ∈ range N, ‖y n‖ ^ 2 = ∑ n : Fin N, ‖c n‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => ‖y n‖ ^ 2)]
    exact sum_congr rfl fun n _ => by simp only [hy, dif_pos n.isLt]
  have h := largeSieve_fareySet_range_sharp N hQ y
  rw [hc] at h
  simp_rw [hexp]
  exact h

/-- **The Farey large sieve over moduli and residues, constant `N + Q² − 1`.**
`Σ_{q ≤ Q} Σ_{(a,q)=1} |Σ_{n<N} c_n e(na/q)|² ≤ (N + Q² − 1) Σ |c_n|²`. -/
theorem largeSieve_expSum_double_sharp (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (c : Fin N → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖RHTower.Sieve.expSum N c ((a : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ n : Fin N, ‖c n‖ ^ 2 := by
  classical
  have hdisj : (↑(Icc 1 Q) : Set ℕ).PairwiseDisjoint
      (fun q => ((Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (a, q))) := by
    intro q _ q' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    rintro p hp hp'
    rw [mem_image] at hp hp'
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨a', _, heq⟩ := hp'
    exact hne (congrArg Prod.snd heq).symm
  have hbase := largeSieve_expSum_fareySet_sharp N hQ c
  rw [fareySet_eq_biUnion, sum_biUnion hdisj] at hbase
  have hinner : ∀ q ∈ Icc 1 Q,
      ∑ p ∈ ((Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (a, q)),
          ‖RHTower.Sieve.expSum N c ((p.1 : ℝ) / (p.2 : ℝ))‖ ^ 2 =
        ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
          ‖RHTower.Sieve.expSum N c ((a : ℝ) / (q : ℝ))‖ ^ 2 :=
    fun q _ => sum_image fun a _ a' _ heq => congrArg Prod.fst heq
  rwa [sum_congr rfl hinner] at hbase

open Classical in
/-- **The multiplicative large sieve with constant `N + R² − 1`.** For `R ≥ 2`,
`Σ_{q ≤ R} (q/φ(q)) Σ_{ψ primitive mod q} |Σ_{n<N} c_n ψ̄(n)|² ≤ (N + R² − 1) Σ |c_n|²`. -/
theorem multiplicative_largeSieve_sharp (N R : ℕ) (hR : 2 ≤ R) (c : ℕ → ℂ) :
    ∑ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ range N, c n * conj (ψ n)‖ ^ 2 ≤
      ((N : ℝ) + (R : ℝ) ^ 2 - 1) * ∑ n ∈ range N, ‖c n‖ ^ 2 := by
  classical
  set c' : Fin N → ℂ := fun n => c n with hc'
  have hterm : ∀ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
      ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ range N, c n * conj (ψ n)‖ ^ 2 ≤
      ∑ a ∈ (Icc 1 (r + 1)).filter (fun a => Nat.Coprime a (r + 1)),
          ‖RHTower.Sieve.expSum N c' ((a : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 := by
    intro r _
    have hφ : (0 : ℝ) < (r + 1).totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos r)
    have hq : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
    have h := RHTower.sum_primitive_normSq_le (r := r + 1) N c
    have h2 := mul_le_mul_of_nonneg_left h
      (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / (r + 1).totient)
    refine h2.trans (le_of_eq ?_)
    rw [← mul_assoc, show ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ((r + 1).totient / ((r + 1 : ℕ) : ℝ)) = 1 by field_simp, one_mul,
      RHTower.sum_units_eq_sum_coprime]
    refine sum_congr rfl fun a _ => ?_
    congr 2
    rw [RHTower.Sieve.expSum, Finset.sum_range]
    refine sum_congr rfl fun n _ => ?_
    rw [RHTower.stdChar_natCast_mul]
  refine (sum_le_sum hterm).trans ?_
  have hreindex : ∑ r ∈ range R, ∑ a ∈ (Icc 1 (r + 1)).filter (fun a => Nat.Coprime a (r + 1)),
        ‖RHTower.Sieve.expSum N c' ((a : ℝ) / ((r + 1 : ℕ) : ℝ))‖ ^ 2 =
      ∑ q ∈ Icc 1 R, ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖RHTower.Sieve.expSum N c' ((a : ℝ) / (q : ℝ))‖ ^ 2 := by
    rw [range_eq_Ico, sum_Ico_add' (f := fun q =>
      ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖RHTower.Sieve.expSum N c' ((a : ℝ) / (q : ℝ))‖ ^ 2) 0 R 1]
    have hI : Ico (0 + 1) (R + 1) = Icc 1 R := by
      ext x
      simp only [mem_Ico, mem_Icc]
      omega
    rw [hI]
  rw [hreindex]
  have hls := largeSieve_expSum_double_sharp N hR c'
  have hcoef : ∑ n : Fin N, ‖c' n‖ ^ 2 = ∑ n ∈ range N, ‖c n‖ ^ 2 := by
    rw [Finset.sum_range]
  rwa [hcoef] at hls


/-! ## §5. Montgomery's sieve with constant `N + Q² − 1` -/

/-- The Farey large sieve for a set of integers in `[0, N)`, over the proper Farey points. -/
theorem largeSieve_set_properFarey_sharp (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) :
    ∑ p ∈ properFareySet Q, ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((p.1 : ℝ) / (p.2 : ℝ)))‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * (A.card : ℝ) := by
  classical
  set y : ℕ → ℂ := fun n => if n ∈ A then 1 else 0 with hy
  have hval : ∀ θ : ℝ, ∑ n ∈ A, circleFreq ((n : ℝ) * θ) =
      ∑ n ∈ range N, y n * circleFreq ((n : ℝ) * θ) := by
    intro θ
    simp only [hy, ite_mul, one_mul, zero_mul]
    rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hA]
  have hY : ∑ n ∈ range N, ‖y n‖ ^ 2 = (A.card : ℝ) := by
    simp only [hy, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_one, one_pow, norm_zero,
      zero_pow two_ne_zero]
    rw [sum_ite_mem, inter_eq_right.mpr hA, sum_const, nsmul_eq_mul, mul_one]
  have h := largeSieve_fareySet_range_sharp N hQ y
  rw [hY] at h
  refine le_trans ?_ h
  simp_rw [hval]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

/-- **Montgomery's sieve inequality with constant `N + Q² − 1`.** For `A ⊆ [0, N)` occupying
`ω_p` classes modulo each prime `p ≤ Q`, `|A| Σ_{p ∈ P} (p − ω_p)/ω_p ≤ N + Q² − 1`. -/
theorem montgomery_sieve_montgomeryVaughanConstant (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) (hAne : A.Nonempty) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ) ≤
      (N : ℝ) + (Q : ℝ) ^ 2 - 1 := by
  classical
  have hlow : ∀ p ∈ P,
      (A.card : ℝ) ^ (2 : ℕ) *
          (((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)) ≤
        ∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
          ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) := by
    intro p hp
    obtain ⟨hprime, hpQ⟩ := hP p hp
    have hc : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    have hmont := occupied_mul_sum_nonzero_ge hprime.pos A
    rw [← sum_fareySet_fibre_eq hprime hpQ A, ← properFareySet_fibre_prime hprime (Q := Q)] at hmont
    rw [mul_div_assoc', div_le_iff₀ hc]
    linarith [hmont, mul_comm ((occupiedClasses p A).card : ℝ)
      (∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ))]
  have hdisj : (↑P : Set ℕ).PairwiseDisjoint
      (fun p => (properFareySet Q).filter (fun x => x.2 = p)) := by
    intro p _ p' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_filter] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have hsub : P.biUnion (fun p => (properFareySet Q).filter (fun x => x.2 = p)) ⊆
      properFareySet Q := by
    intro x hx
    obtain ⟨p, _, hxp⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hxp).1
  have hfibres : ∑ p ∈ P, ∑ x ∈ (properFareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) ≤
      ∑ x ∈ properFareySet Q,
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ (2 : ℕ) := by
    rw [← sum_biUnion hdisj]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hbig := largeSieve_set_properFarey_sharp N hQ A hA
  have hcardpos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast card_pos.mpr hAne
  have hchain : (A.card : ℝ) ^ (2 : ℕ) * ∑ p ∈ P,
      ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * (A.card : ℝ) := by
    rw [mul_sum]
    exact (sum_le_sum hlow).trans (hfibres.trans hbig)
  refine le_of_mul_le_mul_right ?_ hcardpos
  calc ((A.card : ℝ) * ∑ p ∈ P,
        ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ)) *
        (A.card : ℝ)
      = (A.card : ℝ) ^ (2 : ℕ) * ∑ p ∈ P,
          ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) / ((occupiedClasses p A).card : ℝ) := by
        ring
    _ ≤ _ := hchain

/-- **The sieve bound with constant `N + Q² − 1`.** A set in `[0, N)` omitting at least `w_p`
classes modulo each prime `p ∈ P` has at most `(N + Q² − 1)/L` elements, `L ≤ Σ_p w_p/(p − w_p)`. -/
theorem card_le_of_sieve_montgomeryVaughanConstant (N : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) (A : Finset ℕ)
    (hA : A ⊆ range N) (hAne : A.Nonempty) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q)
    (w : ℕ → ℝ) (hwp : ∀ p ∈ P, w p < (p : ℝ))
    (hocc : ∀ p ∈ P, ((occupiedClasses p A).card : ℝ) + w p ≤ (p : ℝ))
    {L : ℝ} (hL : 0 < L) (hLle : L ≤ ∑ p ∈ P, w p / ((p : ℝ) - w p)) :
    (A.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ) ^ 2 - 1) / L := by
  have hbase := montgomery_sieve_montgomeryVaughanConstant N hQ A hA hAne P hP
  have hcard : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
  have hmono : ∑ p ∈ P, w p / ((p : ℝ) - w p) ≤
      ∑ p ∈ P, ((p : ℝ) - ((occupiedClasses p A).card : ℝ)) /
        ((occupiedClasses p A).card : ℝ) := by
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hprime, _⟩ := hP p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hcpos : (0 : ℝ) < ((occupiedClasses p A).card : ℝ) := by
      exact_mod_cast occupiedClasses_card_pos hprime.pos hAne
    exact deficiency_ge hppos hcpos (hwp p hp) (hocc p hp)
  rw [le_div_iff₀ hL]
  exact (mul_le_mul_of_nonneg_left hLle hcard).trans
    ((mul_le_mul_of_nonneg_left hmono hcard).trans hbase)


/-! ## §6. Roots of unity of order at most `Q` -/

/-- A real `x ∉ ℤ` with `m x ∈ ℤ` is at distance at least `1/m` from the integers. -/
theorem one_div_le_toIntDist_of_mul_mem_int {x : ℝ} {m : ℕ} (hm : 0 < m)
    (hint : ∃ n : ℤ, (m : ℝ) * x = n) (hx : ∀ n : ℤ, x ≠ n) : 1 / (m : ℝ) ≤ toIntDist x := by
  obtain ⟨n, hn⟩ := hint
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set j : ℤ := n - m * round x with hj
  have hjx : x - round x = (j : ℝ) / m := by
    rw [hj]; push_cast; field_simp; linarith
  have hj0 : j ≠ 0 := by
    intro h
    rw [h, Int.cast_zero, zero_div, sub_eq_zero] at hjx
    exact hx _ hjx
  rw [toIntDist, hjx, abs_div, abs_of_pos hmR]
  have : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
  exact div_le_div_of_nonneg_right this hmR.le

theorem exists_int_of_circleFreq_eq_one {y : ℝ} (h : circleFreq y = 1) : ∃ n : ℤ, y = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : ((2 * Real.pi * y : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have := hn
    rw [show (n : ℂ) * (2 * Real.pi * Complex.I) = ((n : ℂ) * (2 * Real.pi)) * Complex.I by ring]
      at this
    exact mul_right_cancel₀ hI this
  have h3 : (2 * Real.pi * y : ℝ) = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  nlinarith

/-- **Large sieve over roots of unity of order at most `Q`, constant `K + Q² − 1`.** -/
theorem largeSieve_rootsOfUnity_sharp {Q : ℕ} (hQ : 2 ≤ Q) {T : Finset ℂ}
    (hT : ∀ ζ ∈ T, ∃ d, 1 ≤ d ∧ d ≤ Q ∧ ζ ^ d = 1) (A K : ℕ) (x : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ k ∈ Icc (A + 1) (A + K), x k * ζ ^ k‖ ^ 2 ≤
      ((K : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ k ∈ Icc (A + 1) (A + K), ‖x k‖ ^ 2 := by
  classical
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  set α : ℂ → ℝ := fun ζ => Complex.arg ζ / (2 * Real.pi) with hα
  have hnorm : ∀ ζ ∈ T, ‖ζ‖ = 1 := fun ζ hζ => by
    obtain ⟨d, hd1, _, hd⟩ := hT ζ hζ
    exact Complex.norm_eq_one_of_pow_eq_one hd (by omega)
  have hfreq : ∀ ζ ∈ T, circleFreq (α ζ) = ζ := by
    intro ζ hζ
    rw [circleFreq, hα]
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [show (2 * Real.pi * (Complex.arg ζ / (2 * Real.pi)) : ℝ) = Complex.arg ζ by field_simp]
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rwa [hnorm ζ hζ, Complex.ofReal_one, one_mul] at this
  have hpow : ∀ ζ ∈ T, ∀ k : ℕ, ζ ^ k = circleFreq ((k : ℝ) * α ζ) := fun ζ hζ k => by
    rw [← circleFreq_pow, hfreq ζ hζ]
  have hδ : (0 : ℝ) < 1 / ((Q : ℝ) * ((Q : ℝ) - 1)) := by
    have : (0 : ℝ) < (Q : ℝ) * ((Q : ℝ) - 1) := by nlinarith
    positivity
  have hsep : ∀ r s : T, r ≠ s →
      1 / ((Q : ℝ) * ((Q : ℝ) - 1)) ≤ toIntDist (α r - α s) := by
    rintro ⟨ζ, hζ⟩ ⟨η, hη⟩ hne
    have hne' : ζ ≠ η := fun h => hne (Subtype.ext h)
    obtain ⟨d, hd1, hdQ, hd⟩ := hT ζ hζ
    obtain ⟨e, he1, heQ, he⟩ := hT η hη
    set m : ℕ := if d = e then d else d * e with hm
    have hm0 : 0 < m := by rw [hm]; split_ifs <;> positivity
    have hmQ : (m : ℝ) ≤ (Q : ℝ) * ((Q : ℝ) - 1) := by
      have : m ≤ Q * (Q - 1) := by
        rw [hm]
        split_ifs with hde
        · calc d ≤ Q := hdQ
            _ ≤ Q * (Q - 1) := Nat.le_mul_of_pos_right Q (by omega)
        · rcases lt_or_gt_of_ne hde with h | h
          · calc d * e ≤ (Q - 1) * Q := Nat.mul_le_mul (by omega) heQ
              _ = Q * (Q - 1) := mul_comm _ _
          · exact Nat.mul_le_mul hdQ (by omega)
      have h1 : ((Q * (Q - 1) : ℕ) : ℝ) = (Q : ℝ) * ((Q : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      rw [← h1]
      exact_mod_cast this
    have hmζ : ζ ^ m = 1 := by
      rw [hm]; split_ifs
      · exact hd
      · rw [pow_mul, hd, one_pow]
    have hmη : η ^ m = 1 := by
      rw [hm]; split_ifs with hde
      · rw [hde]; exact he
      · rw [mul_comm, pow_mul, he, one_pow]
    have hdiff : circleFreq (α ζ - α η) = conj η * ζ := by
      rw [← conj_circleFreq_mul, hfreq ζ hζ, hfreq η hη]
    have hint : ∃ n : ℤ, (m : ℝ) * (α ζ - α η) = n := by
      refine exists_int_of_circleFreq_eq_one ?_
      rw [← circleFreq_pow, hdiff, mul_pow, ← map_pow, hmζ, hmη, map_one, one_mul]
    have hnot : ∀ n : ℤ, α ζ - α η ≠ n := by
      intro n hn
      have h1 : circleFreq (α ζ - α η) = 1 := by
        rw [hn, circleFreq]
        rw [Complex.exp_eq_one_iff]
        exact ⟨n, by push_cast; ring⟩
      rw [hdiff] at h1
      have h2 : η * (conj η * ζ) = η := by rw [h1, mul_one]
      rw [← mul_assoc, Complex.mul_conj', hnorm η hη] at h2
      simp only [Complex.ofReal_one, one_pow, one_mul] at h2
      exact hne' h2
    refine le_trans ?_ (one_div_le_toIntDist_of_mul_mem_int hm0 hint hnot)
    exact one_div_le_one_div_of_le (by exact_mod_cast hm0) hmQ
  have h := largeSieve_separated_sharp (ι := T) (fun ζ => α ζ) hδ hsep A K x
  rw [Finset.sum_coe_sort T (fun ζ : ℂ => ‖∑ n ∈ Icc (A + 1) (A + K),
    x n * circleFreq ((n : ℝ) * α ζ)‖ ^ 2)] at h
  refine le_trans (le_of_eq (sum_congr rfl fun ζ hζ => ?_))
    (h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _)))
  · congr 2
    exact sum_congr rfl fun k _ => by rw [hpow ζ hζ k]
  · linarith [inv_farey_delta_le hQ]

/-- **Large sieve over roots of unity on the window `[0, N)`.** -/
theorem largeSieve_rootsOfUnity_range_sharp {Q : ℕ} (hQ : 2 ≤ Q) {T : Finset ℂ}
    (hT : ∀ ζ ∈ T, ∃ d, 1 ≤ d ∧ d ≤ Q ∧ ζ ^ d = 1) (N : ℕ) (y : ℕ → ℂ) :
    ∑ ζ ∈ T, ‖∑ n ∈ range N, y n * ζ ^ n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2 - 1) * ∑ n ∈ range N, ‖y n‖ ^ 2 := by
  have h := largeSieve_rootsOfUnity_sharp hQ hT 0 N (fun k => y (k - 1))
  have hI : Icc (0 + 1) (0 + N) = Ico (0 + 1) (N + 1) := by
    ext; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, ← sum_Ico_add' (fun k => ‖y (k - 1)‖ ^ 2) 0 N 1] at h
  simp only [Nat.add_sub_cancel, ← range_eq_Ico] at h
  refine le_of_eq_of_le (sum_congr rfl fun ζ hζ => ?_) h
  obtain ⟨d, hd1, _, hd⟩ := hT ζ hζ
  have hζ1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hd (by omega)
  have hsh : ∑ k ∈ Ico (0 + 1) (N + 1), y (k - 1) * ζ ^ k = ζ * ∑ n ∈ range N, y n * ζ ^ n := by
    rw [← sum_Ico_add' (fun k => y (k - 1) * ζ ^ k) 0 N 1, range_eq_Ico, mul_sum]
    exact sum_congr rfl fun n _ => by rw [Nat.add_sub_cancel, pow_succ]; ring
  rw [hsh, norm_mul, hζ1, one_mul]

end
end GaloisForLFunctions.BezoutValuationIncidence
