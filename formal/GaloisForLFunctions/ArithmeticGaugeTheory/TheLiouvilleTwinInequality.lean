import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialLocusReadsGRH
import GaloisForLFunctions.RHTower.SquarefreeCounting

/-!
# The Liouville twin inequality

Translating a gauge point `x` by the Liouville point `ℓ` (`χ_ℓ(p) = −1`) turns its twisted Möbius
function into `μ(n)² χ_x(n)` (`moebiusGaugeSum_liouvilleTwin`). Expanding `μ² = Σ_{d² ∣ n} μ(d)` writes
the twin's Möbius sums through two sums at other points: the constant-source sums at `x` and the Möbius
sums at the double `2x` (`sum_moebius_sq_mul_twist`). A hyperbola split at `d ≈ N^κ` then gives

* **The twin inequality** (`gaugeExponent_moebius_liouvilleTwin_le`).
  `exp_μ(x + ℓ) ≤ (1 + 2 exp_1(x) + exp_μ(2x)/2) / 3`.

At a nonprincipal Dirichlet point the constant source has exponent `0`, so:

* **Twins of the special locus are at most typical**
  (`gaugeExponent_moebius_liouvilleTwin_dirichletGauge_le_half`): the Liouville twin of every
  nonprincipal Dirichlet point has Möbius exponent at most `1/2`, unconditionally. The Dirichlet point
  itself has exponent at least `1/2` (`twin_duality`).
* **Real characters read `Θ`** (`gaugeExponent_moebius_liouvilleTwin_quadratic_le`). If `χ² = 1` the
  double `2x_χ` is a finite modification of `0`, and the twin has exponent at most `(2 + Θ)/6`.
* **The floor is not a theorem** (`zetaZeroAbscissa_eq_one_of_floor`). Applied to the quadratic
  character mod `4`: if every gauge point had Möbius exponent at least `1/2`, then `Θ = 1`. Any zero-free
  strip, and in particular RH (bound `5/12`), produces points strictly better than typical
  (`exists_gaugeExponent_moebius_le`).

The almost-sure value `1/2` is a floor for the special locus and an average, not a lower bound on `G`:
the Liouville translation exchanges the sides of `1/2`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

variable {x y z : GaugeTorus}

/-! ### The twin and the double -/

/-- At the Liouville twin of `x` the twist gains the sign `(−1)^{Ω(n)}`. -/
theorem twist_liouvilleTwin (hy : ∀ p, p.Prime → twist y p = -twist x p) {n : ℕ} (hn : n ≠ 0) :
    twist y n = (-1 : ℂ) ^ ArithmeticFunction.cardFactors n * twist x n := by
  obtain ⟨ℓ, hℓ⟩ := exists_liouville_gaugePoint
  have h : twist y n = twist (ℓ + x) n := twist_eq_of_primes hn fun q hq _ => by
    rw [twist_add, hℓ q hq.ne_zero, ArithmeticFunction.cardFactors_apply_prime hq, pow_one, hy q hq]
    ring
  rw [h, twist_add, hℓ n hn]

/-- At the double of `x` the twist is squared. -/
theorem twist_double (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2) {n : ℕ} (hn : n ≠ 0) :
    twist z n = twist x n ^ 2 := by
  have h : twist z n = twist (x + x) n :=
    twist_eq_of_primes hn fun q hq _ => by rw [twist_add, hz q hq, sq]
  rw [h, twist_add, sq]

/-- **At the Liouville twin the Möbius source becomes `μ²`.** -/
theorem moebiusGaugeSum_liouvilleTwin (hy : ∀ p, p.Prime → twist y p = -twist x p) (N : ℕ) :
    moebiusGaugeSum N y = ∑ n ∈ Icc 1 N, (((μ n : ℤ) ^ 2 : ℤ) : ℂ) * twist x n := by
  refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  rw [twist_liouvilleTwin hy hn0, ← mul_assoc, moebius_mul_neg_one_pow_cardFactors]

/-- **The squarefree expansion.**
`Σ_{n ≤ N} μ(n)² χ_x(n) = Σ_{d ≤ N} μ(d) χ_{2x}(d) Σ_{m ≤ N/d²} χ_x(m)`. -/
theorem sum_moebius_sq_mul_twist (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (((μ n : ℤ) ^ 2 : ℤ) : ℂ) * twist x n =
      ∑ d ∈ Icc 1 N, ((μ d : ℤ) : ℂ) * twist z d * ∑ m ∈ Icc 1 (N / (d * d)), twist x m := by
  classical
  -- `μ(n)² = Σ_{d ≤ N, d² ∣ n} μ(d)` for `1 ≤ n ≤ N`.
  have hstep : ∀ n ∈ Icc 1 N, (μ n : ℤ) ^ 2 =
      ∑ d ∈ Icc 1 N, if d * d ∣ n then (μ d : ℤ) else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    rw [← RHTower.sum_moebius_sq_dvd_Icc hn.1, sum_filter]
    refine sum_subset (fun d hd => ?_) fun d hd hdn => ?_
    · rw [mem_Icc] at hd ⊢
      exact ⟨hd.1, hd.2.trans hn.2⟩
    · rw [mem_Icc] at hd hdn
      refine if_neg fun hdvd => ?_
      have hle : d * d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have : n < d := by omega
      nlinarith [hd.1]
  calc ∑ n ∈ Icc 1 N, (((μ n : ℤ) ^ 2 : ℤ) : ℂ) * twist x n
      = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N,
          if d * d ∣ n then ((μ d : ℤ) : ℂ) * twist x n else 0 := by
        refine sum_congr rfl fun n hn => ?_
        rw [hstep n hn, Int.cast_sum, sum_mul]
        refine sum_congr rfl fun d _ => ?_
        split_ifs <;> simp
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (fun n => d * d ∣ n),
          ((μ d : ℤ) : ℂ) * twist x n := by
        rw [sum_comm]
        exact sum_congr rfl fun d _ => (sum_filter _ _).symm
    _ = _ := by
        refine sum_congr rfl fun d hd => ?_
        have hd0 : d ≠ 0 := by have := (mem_Icc.mp hd).1; omega
        have hdd : 0 < d * d := Nat.pos_of_ne_zero (mul_ne_zero hd0 hd0)
        rw [← image_mul_Icc hdd N, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hdd h,
          mul_sum]
        refine sum_congr rfl fun m hm => ?_
        have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
        rw [twist_mul x hdd.ne' hm0, twist_mul x hd0 hd0, twist_double hz hd0, sq]
        ring

/-! ### The hyperbola bound -/

/-- `⌊√N⌋ + 1 ≤ 2 (N + 1)^{1/2}`. -/
theorem natSqrt_add_one_le (N : ℕ) :
    ((Nat.sqrt N : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := by
  have hX : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  have h1 : ((Nat.sqrt N : ℕ) : ℝ) ≤ ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (by linarith))
  have h2 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := Real.one_le_rpow hX (by norm_num)
  linarith

/-- The interval `[1, k]` as `(0, k]`. -/
theorem Icc_one_eq_Ioc (k : ℕ) : Icc 1 k = Ioc 0 k := by
  ext n
  simp only [mem_Icc, mem_Ioc]
  omega

/-- **The hyperbola bound.** If `f` and `g` are bounded by one, with partial sums `O((s + 1)^b)` and
`O((M + 1)^a)`, then `Σ_{d ≤ N} f(d) Σ_{m ≤ N/d²} g(m) = O((N + 1)^{(1 + 2a + b/2)/3})`. Split at
`D = ⌊(N + 1)^κ⌋`, `κ = (1 + b/2 − a)/3`: for `d ≤ D` bound the inner sums; for `d > D` exchange the
order and bound the sums of `f` over `(D, √(N/m)]`. -/
theorem norm_sum_mul_partialSum_div_sq_le {f g : ℕ → ℂ} {a b CA CB : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hf : ∀ d, ‖f d‖ ≤ 1) (hg : ∀ m, ‖g m‖ ≤ 1)
    (hA : ∀ M : ℕ, ‖∑ m ∈ Icc 1 M, g m‖ ≤ CA * ((M : ℝ) + 1) ^ a)
    (hB : ∀ s : ℕ, ‖∑ d ∈ Icc 1 s, f d‖ ≤ CB * ((s : ℝ) + 1) ^ b) (N : ℕ) :
    ‖∑ d ∈ Icc 1 N, f d * ∑ m ∈ Icc 1 (N / (d * d)), g m‖ ≤
      (CA + 2 ^ (b + 1) * CB) * ((N : ℝ) + 1) ^ ((1 + 2 * a + b / 2) / 3) := by
  classical
  set X : ℝ := (N : ℝ) + 1 with hXdef
  have hX1 : (1 : ℝ) ≤ X := by linarith [N.cast_nonneg (α := ℝ)]
  have hX0 : (0 : ℝ) < X := by linarith
  set κ : ℝ := (1 + b / 2 - a) / 3 with hκ
  set E : ℝ := (1 + 2 * a + b / 2) / 3 with hE
  set D : ℕ := ⌊X ^ κ⌋₊ with hD
  have hD1 : (D : ℝ) ≤ X ^ κ := Nat.floor_le (Real.rpow_nonneg hX0.le _)
  have hD2 : X ^ κ < (D : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun d => d ≤ D)]
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  · -- Small `d`: at most `D` terms, each `O((N + 1)^a)`.
    have hterm : ∀ d ∈ (Icc 1 N).filter (fun d => d ≤ D),
        ‖f d * ∑ m ∈ Icc 1 (N / (d * d)), g m‖ ≤ CA * X ^ a := by
      intro d _
      rw [norm_mul]
      calc ‖f d‖ * ‖∑ m ∈ Icc 1 (N / (d * d)), g m‖ ≤ 1 * (CA * X ^ a) := by
            refine mul_le_mul (hf d) ((hA _).trans (mul_le_mul_of_nonneg_left ?_ hCA))
              (norm_nonneg _) zero_le_one
            refine Real.rpow_le_rpow (by positivity) ?_ ha
            have : ((N / (d * d) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N (d * d)
            linarith
        _ = CA * X ^ a := one_mul _
    have hcard : #((Icc 1 N).filter (fun d => d ≤ D)) ≤ D := by
      calc #((Icc 1 N).filter (fun d => d ≤ D)) ≤ #(Icc 1 D) := card_le_card fun d hd => by
            simp only [mem_filter, mem_Icc] at hd ⊢
            exact ⟨hd.1.1, hd.2⟩
        _ = D := by simp
    calc ‖∑ d ∈ (Icc 1 N).filter (fun d => d ≤ D), f d * ∑ m ∈ Icc 1 (N / (d * d)), g m‖
        ≤ ∑ d ∈ (Icc 1 N).filter (fun d => d ≤ D), CA * X ^ a := norm_sum_le_of_le _ hterm
      _ = #((Icc 1 N).filter (fun d => d ≤ D)) * (CA * X ^ a) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ X ^ κ * (CA * X ^ a) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (by exact_mod_cast hcard : (#((Icc 1 N).filter (fun d => d ≤ D)) : ℝ) ≤ D).trans
            hD1
      _ = CA * X ^ E := by
          rw [show E = κ + a by rw [hE, hκ]; ring, Real.rpow_add hX0]
          ring
  · -- Large `d`: exchange the order of summation.
    have hfilt : (Icc 1 N).filter (fun d => ¬ d ≤ D) = Ioc D N := by
      ext d
      simp only [mem_filter, mem_Icc, mem_Ioc]
      omega
    have hswap : ∑ d ∈ Ioc D N, f d * ∑ m ∈ Icc 1 (N / (d * d)), g m =
        ∑ m ∈ Icc 1 (N / ((D + 1) * (D + 1))), (∑ d ∈ Ioc D (Nat.sqrt (N / m)), f d) * g m := by
      simp_rw [mul_sum, sum_mul]
      refine sum_comm' fun d m => ?_
      simp only [mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨⟨hDd, hdN⟩, hm1, hmN⟩
        have hdd : 0 < d * d := Nat.mul_pos (by omega) (by omega)
        have h1 : m * (d * d) ≤ N := (Nat.le_div_iff_mul_le hdd).mp hmN
        refine ⟨⟨hDd, Nat.le_sqrt.mpr ((Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith))⟩,
          hm1, (Nat.le_div_iff_mul_le (by positivity)).mpr ?_⟩
        have : (D + 1) * (D + 1) ≤ d * d := Nat.mul_le_mul hDd hDd
        nlinarith
      · rintro ⟨⟨hDd, hds⟩, hm1, hmN⟩
        have h1 : d * d * m ≤ N :=
          (Nat.le_div_iff_mul_le (by omega)).mp (Nat.le_sqrt.mp hds)
        have hd1 : 1 ≤ d := by omega
        refine ⟨⟨hDd, by nlinarith⟩, hm1,
          (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) (by omega))).mpr (by nlinarith)⟩
    -- Each inner sum is a difference of two partial sums of `f` of length at most `√N`.
    have hinner : ∀ m ∈ Icc 1 (N / ((D + 1) * (D + 1))),
        ‖(∑ d ∈ Ioc D (Nat.sqrt (N / m)), f d) * g m‖ ≤ 2 * CB * (2 ^ b * X ^ (b / 2)) := by
      intro m hm
      rw [mem_Icc] at hm
      have hm0 : 0 < m := by omega
      have hDs : D ≤ Nat.sqrt (N / m) := by
        have h1 : m * ((D + 1) * (D + 1)) ≤ N :=
          (Nat.le_div_iff_mul_le (by positivity)).mp hm.2
        have h2 : (D + 1) * (D + 1) ≤ N / m :=
          (Nat.le_div_iff_mul_le hm0).mpr (by nlinarith)
        have := Nat.le_sqrt.mpr h2
        omega
      have hsN : Nat.sqrt (N / m) ≤ Nat.sqrt N := Nat.sqrt_le_sqrt (Nat.div_le_self N m)
      have hpow : ∀ s : ℕ, s ≤ Nat.sqrt N → ((s : ℝ) + 1) ^ b ≤ 2 ^ b * X ^ (b / 2) := by
        intro s hs
        have hs' : (s : ℝ) + 1 ≤ 2 * X ^ (1 / 2 : ℝ) := by
          have : (s : ℝ) ≤ (Nat.sqrt N : ℕ) := by exact_mod_cast hs
          linarith [natSqrt_add_one_le N]
        calc ((s : ℝ) + 1) ^ b ≤ (2 * X ^ (1 / 2 : ℝ)) ^ b := Real.rpow_le_rpow (by positivity) hs' hb
          _ = 2 ^ b * X ^ (b / 2) := by
              rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hX0.le]
              ring_nf
      have hsplit : ∑ d ∈ Ioc D (Nat.sqrt (N / m)), f d =
          ∑ d ∈ Icc 1 (Nat.sqrt (N / m)), f d - ∑ d ∈ Icc 1 D, f d := by
        rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, ← sum_Ioc_consecutive f (Nat.zero_le D) hDs]
        ring
      rw [norm_mul, hsplit]
      calc ‖∑ d ∈ Icc 1 (Nat.sqrt (N / m)), f d - ∑ d ∈ Icc 1 D, f d‖ * ‖g m‖
          ≤ (CB * (2 ^ b * X ^ (b / 2)) + CB * (2 ^ b * X ^ (b / 2))) * 1 := by
            refine mul_le_mul ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (hg m) (norm_nonneg _)
              (by positivity)
            · exact (hB _).trans (mul_le_mul_of_nonneg_left (hpow _ hsN) hCB)
            · exact (hB _).trans (mul_le_mul_of_nonneg_left (hpow _ (hDs.trans hsN)) hCB)
        _ = 2 * CB * (2 ^ b * X ^ (b / 2)) := by ring
    -- The number of `m` is at most `(N + 1)/(D + 1)² ≤ (N + 1)^{1 − 2κ}`.
    have hcount : ((N / ((D + 1) * (D + 1)) : ℕ) : ℝ) ≤ X ^ (1 - 2 * κ) := by
      have hDpos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
      have hsq : (X ^ κ) ^ 2 ≤ ((D : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hX0.le _) hD2.le 2
      have hpow2 : (X ^ κ) ^ 2 = X ^ (2 * κ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        ring_nf
      calc ((N / ((D + 1) * (D + 1)) : ℕ) : ℝ) ≤ (N : ℝ) / (((D + 1) * (D + 1) : ℕ) : ℝ) :=
            Nat.cast_div_le
        _ ≤ X / X ^ (2 * κ) := by
            push_cast
            refine div_le_div₀ hX0.le (by linarith) (by positivity) ?_
            nlinarith
        _ = X ^ (1 - 2 * κ) := by
            rw [Real.rpow_sub hX0, Real.rpow_one]
    rw [hfilt, hswap]
    calc ‖∑ m ∈ Icc 1 (N / ((D + 1) * (D + 1))), (∑ d ∈ Ioc D (Nat.sqrt (N / m)), f d) * g m‖
        ≤ ∑ m ∈ Icc 1 (N / ((D + 1) * (D + 1))), 2 * CB * (2 ^ b * X ^ (b / 2)) :=
          norm_sum_le_of_le _ hinner
      _ = ((N / ((D + 1) * (D + 1)) : ℕ) : ℝ) * (2 * CB * (2 ^ b * X ^ (b / 2))) := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      _ ≤ X ^ (1 - 2 * κ) * (2 * CB * (2 ^ b * X ^ (b / 2))) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = 2 ^ (b + 1) * CB * X ^ E := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
            show E = (1 - 2 * κ) + b / 2 by rw [hE, hκ]; ring, Real.rpow_add hX0]
          ring

/-! ### The twin inequality -/

/-- **Power bounds pass to the Liouville twin.** Exponents `a` for the constant source at `x` and `b`
for the Möbius source at `2x` give the exponent `(1 + 2a + b/2)/3` for the Möbius source at `x + ℓ`. -/
theorem gaugePowerBound_moebius_liouvilleTwin (hy : ∀ p, p.Prime → twist y p = -twist x p)
    (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : GaugePowerBound oneSource x a) (hB : GaugePowerBound moebiusSource z b) :
    GaugePowerBound moebiusSource y ((1 + 2 * a + b / 2) / 3) := by
  obtain ⟨CA, hCA, hA⟩ := hA
  obtain ⟨CB, hCB, hB⟩ := hB
  -- The constant-source sums without the index `0`.
  have hA' : ∀ M : ℕ, ‖∑ m ∈ Icc 1 M, twist x m‖ ≤ (CA + 1) * ((M : ℝ) + 1) ^ a := by
    intro M
    have h := hA M
    simp only [oneSource, one_mul] at h
    rw [sum_range_succ_eq_add_Icc, twist_at_zero] at h
    have h1 : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ a :=
      Real.one_le_rpow (by linarith [M.cast_nonneg (α := ℝ)]) ha
    calc ‖∑ m ∈ Icc 1 M, twist x m‖ = ‖(1 + ∑ m ∈ Icc 1 M, twist x m) - 1‖ := by ring_nf
      _ ≤ ‖1 + ∑ m ∈ Icc 1 M, twist x m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ CA * ((M : ℝ) + 1) ^ a + 1 := by rw [norm_one]; linarith
      _ ≤ (CA + 1) * ((M : ℝ) + 1) ^ a := by nlinarith
  have hB' : ∀ s : ℕ, ‖∑ d ∈ Icc 1 s, ((μ d : ℤ) : ℂ) * twist z d‖ ≤ CB * ((s : ℝ) + 1) ^ b := by
    intro s
    have h := hB s
    rwa [sum_range_moebiusSource] at h
  have hf : ∀ d, ‖((μ d : ℤ) : ℂ) * twist z d‖ ≤ 1 := fun d => by
    rw [norm_mul, norm_twist, mul_one]
    exact norm_moebiusSource_le d
  refine ⟨(CA + 1) + 2 ^ (b + 1) * CB, by positivity, fun N => ?_⟩
  rw [sum_range_moebiusSource, moebiusGaugeSum_liouvilleTwin hy, sum_moebius_sq_mul_twist hz]
  exact norm_sum_mul_partialSum_div_sq_le ha hb (by linarith) hCB hf (fun m => (norm_twist x m).le)
    hA' hB' N

/-- **The Liouville twin inequality.** `exp_μ(x + ℓ) ≤ (1 + 2 exp_1(x) + exp_μ(2x)/2)/3`. -/
theorem gaugeExponent_moebius_liouvilleTwin_le (hy : ∀ p, p.Prime → twist y p = -twist x p)
    (hz : ∀ p, p.Prime → twist z p = twist x p ^ 2) :
    gaugeExponent moebiusSource y ≤
      (1 + 2 * gaugeExponent oneSource x + gaugeExponent moebiusSource z / 2) / 3 := by
  have hα := gaugeExponent_nonneg norm_oneSource_le (x := x)
  have hβ := gaugeExponent_nonneg norm_moebiusSource_le (x := z)
  refine gaugeExponent_le_of_forall (by positivity) fun δ hδ => ?_
  have hA := gaugePowerBound_of_gaugeExponent_lt norm_oneSource_le
    (lt_add_of_pos_right (gaugeExponent oneSource x) hδ)
  have hB := gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le
    (lt_add_of_pos_right (gaugeExponent moebiusSource z) hδ)
  refine (gaugePowerBound_moebius_liouvilleTwin hy hz (by linarith) (by linarith) hA hB).mono ?_
  linarith

/-! ### The special locus and its twins -/

variable {q : ℕ} [NeZero q]

/-- **Twins of Dirichlet points are at most typical.** The Liouville twin of a nonprincipal
Dirichlet point has Möbius exponent at most `1/2`. -/
theorem gaugeExponent_moebius_liouvilleTwin_dirichletGauge_le_half {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hy : ∀ p, p.Prime → twist y p = -twist (dirichletGauge χ) p) :
    gaugeExponent moebiusSource y ≤ 1 / 2 := by
  have h := gaugeExponent_moebius_liouvilleTwin_le hy
    (z := dirichletGauge χ + dirichletGauge χ) fun p _ => by rw [twist_add, sq]
  rw [gaugeExponent_one_dirichletGauge χ hχ] at h
  linarith [gaugeExponent_le_one norm_moebiusSource_le (x := dirichletGauge χ + dirichletGauge χ)]

/-- The double of a quadratic Dirichlet point is trivial at every prime not dividing `q`. -/
theorem twist_double_dirichletGauge_of_sq {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hpq : p ∉ q.primeFactors) :
    twist (dirichletGauge χ + dirichletGauge χ) p = 1 := by
  have hcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd =>
    hpq (Nat.mem_primeFactors.mpr ⟨hp, hdvd, NeZero.ne q⟩)
  rw [twist_add, twist_dirichletGauge χ hp.ne_zero hcop, ← Pi.mul_apply, ← MulChar.coeToFun_mul,
    ← sq, hχ2, MulChar.one_apply ((ZMod.isUnit_iff_coprime p q).mpr hcop)]

/-- **Twins of real Dirichlet points read `Θ`.** For `χ² = 1`, `χ ≠ 1`, the Liouville twin has
Möbius exponent at most `(2 + Θ)/6`. -/
theorem gaugeExponent_moebius_liouvilleTwin_quadratic_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hχ2 : χ ^ 2 = 1) (hy : ∀ p, p.Prime → twist y p = -twist (dirichletGauge χ) p) :
    gaugeExponent moebiusSource y ≤ (2 + RHTower.zetaZeroAbscissa) / 6 := by
  have h := gaugeExponent_moebius_liouvilleTwin_le hy
    (z := dirichletGauge χ + dirichletGauge χ) fun p _ => by rw [twist_add, sq]
  rw [gaugeExponent_one_dirichletGauge χ hχ,
    gaugeExponent_moebius_finiteFlip q.primeFactors fun p hp hpq =>
      twist_double_dirichletGauge_of_sq hχ2 hp hpq] at h
  linarith

/-- **Twin duality.** At a primitive nonprincipal Dirichlet point the Möbius exponent is at least
typical; at its Liouville twin it is at most typical. -/
theorem twin_duality {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (hy : ∀ p, p.Prime → twist y p = -twist (dirichletGauge χ) p) :
    gaugeExponent moebiusSource y ≤ typicalExponent moebiusSource ∧
      typicalExponent moebiusSource ≤ gaugeExponent moebiusSource (dirichletGauge χ) := by
  rw [typicalExponent_moebius_eq_half]
  refine ⟨gaugeExponent_moebius_liouvilleTwin_dirichletGauge_le_half hχ hy, ?_⟩
  rw [← typicalExponent_moebius_eq_half]
  exact typicalExponent_le_gaugeExponent_moebius_dirichletGauge hχ hprim

/-! ### The floor -/

/-- The quadratic character modulo `4`, with complex values. -/
def chiFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chiFour_sq : chiFour ^ 2 = 1 := (ZMod.isQuadratic_χ₄.comp _).sq_eq_one

theorem chiFour_ne_one : chiFour ≠ 1 := by
  intro h
  have h3 : chiFour ((3 : ℕ) : ZMod 4) = 1 := by
    rw [h, MulChar.one_apply ((ZMod.isUnit_iff_coprime 3 4).mpr (by norm_num))]
  rw [chiFour, MulChar.ringHomComp_apply, ZMod.χ₄_nat_three_mod_four (by norm_num)] at h3
  norm_num at h3

/-- **Some gauge point has Möbius exponent at most `(2 + Θ)/6`**: the Liouville twin of the
quadratic character mod `4`. Under RH this is `5/12 < 1/2`. -/
theorem exists_gaugeExponent_moebius_le :
    ∃ y : GaugeTorus, gaugeExponent moebiusSource y ≤ (2 + RHTower.zetaZeroAbscissa) / 6 := by
  obtain ⟨ℓ, hℓ⟩ := exists_liouville_gaugePoint
  refine ⟨dirichletGauge chiFour + ℓ, gaugeExponent_moebius_liouvilleTwin_quadratic_le
    chiFour_ne_one chiFour_sq fun p hp => ?_⟩
  rw [twist_add, hℓ p hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
  ring

/-- **The floor is not a theorem.** If every gauge point had Möbius exponent at least the typical
value `1/2`, the zeros of `ζ` would approach the line `Re s = 1`. -/
theorem zetaZeroAbscissa_eq_one_of_floor
    (h : ∀ x : GaugeTorus, typicalExponent moebiusSource ≤ gaugeExponent moebiusSource x) :
    RHTower.zetaZeroAbscissa = 1 := by
  obtain ⟨y, hy⟩ := exists_gaugeExponent_moebius_le
  have hfloor := h y
  rw [typicalExponent_moebius_eq_half] at hfloor
  have hle : RHTower.zetaZeroAbscissa ≤ 1 := by
    rw [← gaugeExponent_moebius_trivial]
    exact gaugeExponent_le_one norm_moebiusSource_le
  linarith

end GaloisForLFunctions.ArithmeticGaugeTheory
