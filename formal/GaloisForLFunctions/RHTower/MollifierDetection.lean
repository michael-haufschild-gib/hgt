/-
The mollified convolution collapses: `ζ·M` has vanishing coefficients below the cutoff.

For the unit-coefficient Dirichlet polynomial `D_N = ∑_{n≤N} n^{-it}` (the ζ approximation) and the
Möbius mollifier `M_y = ∑_{m≤y} μ(m) m^{-it}`, the product `D_N·M_y = dpoly(convCoeff)` has convolution
coefficient at `k`:

  cₖ = ∑_{ab=k, a≤N, b≤y} 1·μ(b).

For `1 ≤ k ≤ min(N, y)` every factorisation `ab=k` has `a,b ≤ k ≤ min(N,y)`, so the constraints
`a≤N, b≤y` are automatic, the fibre is exactly `k`'s divisor-antidiagonal, and

  cₖ = ∑_{b∣k} μ(b) = [k = 1]

by the Möbius cancellation (`Mollifier.sum_moebius_divisors`).  Thus `D_N·M_y − 1` has *zero*
coefficients for all `k ≤ min(N,y)`: the mollified product is `1` up to terms of index `> min(N,y)`,
whose second moment (`SecondMoment`) is small — the input to Carlson's density bound.
-/
import GaloisForLFunctions.RHTower.DpolyConvolution
import GaloisForLFunctions.RHTower.Mollifier
import GaloisForLFunctions.RHTower.FourthMomentDiagonal

open Nat Finset

namespace RHTower

/-- **The mollified convolution coefficient below the cutoff.**  For `1 ≤ k ≤ min(N, y)`, the
Dirichlet-convolution coefficient of `1` against `μ` is the Möbius divisor sum, hence `[k = 1]`. -/
theorem convCoeff_ones_moebius_eq {N y k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hky : k ≤ y) :
    convCoeff (fun _ => (1 : ℝ)) moebiusCoeff (Finset.Icc 1 N) (Finset.Icc 1 y) k
      = if k = 1 then 1 else 0 := by
  have hk0 : k ≠ 0 := by omega
  -- the fibre {(a,b) : ab=k, a≤N, b≤y} is exactly `k.divisorsAntidiagonal`
  have hfiber : (Finset.Icc 1 N ×ˢ Finset.Icc 1 y).filter (fun p => p.1 * p.2 = k)
      = k.divisorsAntidiagonal := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, hprod⟩
      exact ⟨hprod, hk0⟩
    · rintro ⟨hprod, _⟩
      have hp1pos : 1 ≤ p.1 := by
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · rw [h, zero_mul] at hprod; omega
        · omega
      have hp2pos : 1 ≤ p.2 := by
        rcases Nat.eq_zero_or_pos p.2 with h | h
        · rw [h, mul_zero] at hprod; omega
        · omega
      have hp1k : p.1 ≤ k := by rw [← hprod]; exact Nat.le_mul_of_pos_right _ hp2pos
      have hp2k : p.2 ≤ k := by rw [← hprod]; exact Nat.le_mul_of_pos_left _ hp1pos
      exact ⟨⟨⟨hp1pos, le_trans hp1k hkN⟩, ⟨hp2pos, le_trans hp2k hky⟩⟩, hprod⟩
  rw [convCoeff, hfiber]
  simp only [one_mul, moebiusCoeff]
  rw [← Int.cast_sum,
    Nat.sum_divisorsAntidiagonal' (fun _ b => (ArithmeticFunction.moebius b : ℤ)),
    sum_moebius_divisors]
  split <;> simp

/-- The fibre of the product map at `k ≤ min(N, y)` is exactly `k.divisorsAntidiagonal`. -/
theorem fiber_eq_divisorsAntidiagonal {N y k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hky : k ≤ y) :
    (Finset.Icc 1 N ×ˢ Finset.Icc 1 y).filter (fun p => p.1 * p.2 = k)
      = k.divisorsAntidiagonal := by
  have hk0 : k ≠ 0 := by omega
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, hprod⟩; exact ⟨hprod, hk0⟩
  · rintro ⟨hprod, _⟩
    have hp1pos : 1 ≤ p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · rw [h, zero_mul] at hprod; omega
      · omega
    have hp2pos : 1 ≤ p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with h | h
      · rw [h, mul_zero] at hprod; omega
      · omega
    have hp1k : p.1 ≤ k := by rw [← hprod]; exact Nat.le_mul_of_pos_right _ hp2pos
    have hp2k : p.2 ≤ k := by rw [← hprod]; exact Nat.le_mul_of_pos_left _ hp1pos
    exact ⟨⟨⟨hp1pos, le_trans hp1k hkN⟩, ⟨hp2pos, le_trans hp2k hky⟩⟩, hprod⟩

/-- **The σ-weighted mollified convolution coefficient below the cutoff.**  With the density weighting
`aₙ = n^{-σ}`, `bₘ = μ(m) m^{-σ}`, the convolution coefficient at `1 ≤ k ≤ min(N, y)` is
`k^{-σ}·[k = 1]`: the characters `n^{-σ}m^{-σ} = k^{-σ}` factor out of the fibre and the Möbius sum
collapses.  This is the coefficient of `D_N(σ+·)·M_y(σ+·)`, whose high-index tail
`∑_{k>min} k^{-2σ} d(k)²` is summable for `σ > 1/2` (via `DivisorBound`). -/
theorem convCoeff_weighted_moebius_eq {N y k : ℕ} (σ : ℝ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (hky : k ≤ y) :
    convCoeff (fun n => (n : ℝ) ^ (-σ))
        (fun m => (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) ^ (-σ))
        (Finset.Icc 1 N) (Finset.Icc 1 y) k
      = (k : ℝ) ^ (-σ) * (if k = 1 then 1 else 0) := by
  rw [convCoeff, fiber_eq_divisorsAntidiagonal hk1 hkN hky]
  have hterm : ∀ p ∈ k.divisorsAntidiagonal,
      (p.1 : ℝ) ^ (-σ) * ((ArithmeticFunction.moebius p.2 : ℝ) * (p.2 : ℝ) ^ (-σ))
        = (k : ℝ) ^ (-σ) * (ArithmeticFunction.moebius p.2 : ℝ) := by
    intro p hp
    have hab : p.1 * p.2 = k := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hpow : (p.1 : ℝ) ^ (-σ) * (p.2 : ℝ) ^ (-σ) = (k : ℝ) ^ (-σ) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1; exact_mod_cast hab
    calc (p.1 : ℝ) ^ (-σ) * ((ArithmeticFunction.moebius p.2 : ℝ) * (p.2 : ℝ) ^ (-σ))
        = ((p.1 : ℝ) ^ (-σ) * (p.2 : ℝ) ^ (-σ)) * (ArithmeticFunction.moebius p.2 : ℝ) := by ring
      _ = (k : ℝ) ^ (-σ) * (ArithmeticFunction.moebius p.2 : ℝ) := by rw [hpow]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [← Int.cast_sum,
    Nat.sum_divisorsAntidiagonal' (fun _ b => (ArithmeticFunction.moebius b : ℤ)),
    sum_moebius_divisors]
  split <;> simp

/-- **The convolution coefficient is bounded by the divisor count.**  `|cₖ| ≤ k^{-σ}·d(k)`: each of
the `≤ d(k)` factorisations `ab=k` contributes `|a^{-σ}μ(b)b^{-σ}| ≤ (ab)^{-σ} = k^{-σ}` (as
`|μ| ≤ 1`).  This feeds the tail bound `∑_{k>min}|cₖ|² ≤ ∑_{k>min} k^{-2σ}d(k)²`, summable for `σ > 1/2`
via `DivisorBound`. -/
theorem abs_convCoeff_weighted_le {N y : ℕ} (σ : ℝ) {k : ℕ} (hk1 : 1 ≤ k) :
    |convCoeff (fun n => (n : ℝ) ^ (-σ))
        (fun m => (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) ^ (-σ))
        (Finset.Icc 1 N) (Finset.Icc 1 y) k|
      ≤ (k : ℝ) ^ (-σ) * (k.divisors.card : ℝ) := by
  have hk0 : k ≠ 0 := by omega
  set fib := (Finset.Icc 1 N ×ˢ Finset.Icc 1 y).filter (fun p => p.1 * p.2 = k) with hfib
  have hsub : fib ⊆ k.divisorsAntidiagonal := by
    intro p hp
    rw [hfib, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨hp.2, hk0⟩
  have hcard : k.divisorsAntidiagonal.card = k.divisors.card := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
      ← Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℕ))]
  rw [convCoeff]
  calc |∑ p ∈ fib, (p.1 : ℝ) ^ (-σ)
          * ((ArithmeticFunction.moebius p.2 : ℝ) * (p.2 : ℝ) ^ (-σ))|
      ≤ ∑ p ∈ fib, |(p.1 : ℝ) ^ (-σ)
          * ((ArithmeticFunction.moebius p.2 : ℝ) * (p.2 : ℝ) ^ (-σ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ fib, (k : ℝ) ^ (-σ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpk : p.1 * p.2 = k := by rw [hfib, Finset.mem_filter] at hp; exact hp.2
        have hmu : |(ArithmeticFunction.moebius p.2 : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hpow : (p.1 : ℝ) ^ (-σ) * (p.2 : ℝ) ^ (-σ) = (k : ℝ) ^ (-σ) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]; congr 1; exact_mod_cast hpk
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
          abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        calc (p.1 : ℝ) ^ (-σ) * (|(ArithmeticFunction.moebius p.2 : ℝ)| * (p.2 : ℝ) ^ (-σ))
            ≤ (p.1 : ℝ) ^ (-σ) * (1 * (p.2 : ℝ) ^ (-σ)) := by
              gcongr
          _ = (k : ℝ) ^ (-σ) := by rw [one_mul, hpow]
    _ = (fib.card : ℝ) * (k : ℝ) ^ (-σ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k.divisors.card : ℝ) * (k : ℝ) ^ (-σ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [← hcard]; exact_mod_cast Finset.card_le_card hsub
    _ = (k : ℝ) ^ (-σ) * (k.divisors.card : ℝ) := by ring

/-- The **σ-weighted detection coefficient** `eₖ(σ) = cₖ(σ) − [k = 1]` of `D_N(σ+·)·M_y(σ+·) − 1`. -/
noncomputable def detCoeffW (N y : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  convCoeff (fun n => (n : ℝ) ^ (-σ))
      (fun m => (ArithmeticFunction.moebius m : ℝ) * (m : ℝ) ^ (-σ))
      (Finset.Icc 1 N) (Finset.Icc 1 y) k
    - (if k = 1 then 1 else 0)

/-- **The σ-weighted detection coefficient vanishes below the cutoff.**  For `1 ≤ k ≤ min(N, y)`,
`eₖ(σ) = 0`: since `cₖ(σ) = k^{-σ}·[k=1] = [k=1]` there (the weight is `1` exactly when the indicator
fires), the detection polynomial `D_N(σ+·)·M_y(σ+·) − 1` is supported on `k > min(N, y)`. -/
theorem detCoeffW_eq_zero_of_le {N y k : ℕ} (σ : ℝ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (hky : k ≤ y) : detCoeffW N y σ k = 0 := by
  rw [detCoeffW, convCoeff_weighted_moebius_eq σ hk1 hkN hky]
  rcases eq_or_ne k 1 with hk | hk
  · subst hk; simp
  · simp [hk]

/-- **The σ-weighted detection coefficient is bounded by `k^{-σ}·d(k)`** above the cutoff (`k > 1`). -/
theorem abs_detCoeffW_le {N y k : ℕ} (σ : ℝ) (hk1 : 1 ≤ k) (hk : k ≠ 1) :
    |detCoeffW N y σ k| ≤ (k : ℝ) ^ (-σ) * (k.divisors.card : ℝ) := by
  rw [detCoeffW, if_neg hk, sub_zero]
  exact abs_convCoeff_weighted_le σ hk1

/-- `(detCoeffW k)² ≤ d(k)² k^{-2σ}` above the cutoff. -/
theorem sq_detCoeffW_le {N y k : ℕ} (σ : ℝ) (hk1 : 1 ≤ k) (hk : k ≠ 1) :
    (detCoeffW N y σ k) ^ 2 ≤ (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ) := by
  have hbd := abs_detCoeffW_le (N := N) (y := y) σ hk1 hk
  have hrpow : ((k : ℝ) ^ (-σ)) ^ 2 = (k : ℝ) ^ (-2 * σ) := by
    rw [← Real.rpow_natCast ((k : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  calc (detCoeffW N y σ k) ^ 2 = |detCoeffW N y σ k| ^ 2 := (sq_abs _).symm
    _ ≤ ((k : ℝ) ^ (-σ) * (k.divisors.card : ℝ)) ^ 2 := by
        apply pow_le_pow_left₀ (abs_nonneg _) hbd
    _ = (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ) := by rw [mul_pow, hrpow]; ring

/-- **The detection diagonal is bounded by the summable tail.**  For `σ > 1/2` and cutoff `min ≥ 1`,
the detection diagonal `∑_{k∈convSupp, k>min} eₖ(σ)²` is at most the tail
`∑'_{k} 𝟙_{k>min} d(k)² k^{-2σ}` of the convergent divisor-square series.  With
`tendsto_divisor_sq_rpow_tail_zero`, this diagonal `→ 0` as `min → ∞`. -/
theorem detection_diagonal_le_tsum {N y : ℕ} (σ : ℝ) (hσ : 1 / 2 < σ) (hmin : 1 ≤ min N y) :
    ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
        (detCoeffW N y σ k) ^ 2
      ≤ ∑' k : ℕ, Set.indicator {j | min N y < j}
          (fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) k := by
  set g : ℕ → ℝ := fun k => (k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ) with hg_def
  have hgnn : ∀ k, 0 ≤ g k := fun k => by rw [hg_def]; positivity
  have hind_summable : Summable (Set.indicator {j | min N y < j} g) :=
    (summable_divisor_sq_rpow hσ).indicator _
  calc ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
          (detCoeffW N y σ k) ^ 2
      ≤ ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
          Set.indicator {j | min N y < j} g k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkmem : k ∈ {j | min N y < j} := hk.2
        rw [Set.indicator_of_mem hkmem]
        have hk1 : 1 ≤ k := le_of_lt (lt_of_le_of_lt hmin hk.2)
        have hkne : k ≠ 1 := by omega
        exact sq_detCoeffW_le σ hk1 hkne
    _ ≤ ∑' k : ℕ, Set.indicator {j | min N y < j} g k :=
        hind_summable.sum_le_tsum _ (fun k _ => Set.indicator_nonneg (fun j _ => hgnn j) k)

/-- The **detection coefficient** `eₖ = cₖ − [k = 1]` of `D_N·M_y − 1`. -/
noncomputable def detCoeff (N y : ℕ) (k : ℕ) : ℝ :=
  convCoeff (fun _ => (1 : ℝ)) moebiusCoeff (Finset.Icc 1 N) (Finset.Icc 1 y) k
    - (if k = 1 then 1 else 0)

/-- **The detection polynomial vanishes below the cutoff.**  For `1 ≤ k ≤ min(N, y)`, the coefficient
of `D_N·M_y − 1` at `k` is zero: the mollified product agrees with `1` on all indices up to the cutoff,
so `D_N·M_y − 1` is supported on `k > min(N, y)` — the regime where its second moment is small. -/
theorem detCoeff_eq_zero_of_le {N y k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) (hky : k ≤ y) :
    detCoeff N y k = 0 := by
  rw [detCoeff, convCoeff_ones_moebius_eq hk1 hkN hky, sub_self]

/-- Every index in the convolution support is `≥ 1` (it is a product of numbers `≥ 1`). -/
theorem one_le_of_mem_convSupp {N y k : ℕ}
    (hk : k ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)) : 1 ≤ k := by
  rw [convSupp, Finset.mem_image] at hk
  obtain ⟨p, hp, hpk⟩ := hk
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  rw [← hpk]
  calc 1 ≤ p.1 := hp.1.1
    _ ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ (by omega)

/-- **The detection second-moment diagonal is a tail sum.**  Because `detCoeff` vanishes for
`k ≤ min(N, y)`, the diagonal `∑_k eₖ²` of the detection polynomial `D_N·M_y − 1` runs only over
indices `k > min(N, y)`: its `L²` mass lives entirely above the cutoff. -/
theorem detection_diagonal_tail (N y : ℕ) :
    ∑ k ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y), (detCoeff N y k) ^ 2
      = ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
          (detCoeff N y k) ^ 2 := by
  refine (Finset.sum_filter_of_ne ?_).symm
  intro k hk hne
  by_contra hle
  rw [not_lt] at hle
  have hk1 : 1 ≤ k := one_le_of_mem_convSupp hk
  have hz : detCoeff N y k = 0 :=
    detCoeff_eq_zero_of_le hk1 (le_trans hle (min_le_left _ _)) (le_trans hle (min_le_right _ _))
  rw [hz] at hne
  simp at hne

/-- **The detection polynomial is `D_N·M_y − 1`.**  The Dirichlet polynomial with the detection
coefficients equals the mollified unit polynomial minus one: `dpoly(detCoeff) = D_N·M_y − 1`, where
`D_N = ∑_{n≤N} n^{-it}`.  Combined with `detection_diagonal_tail`, its `L²` mass lives above the cutoff;
combined with the AFE (`ζ ≈ D_N`), it is `≈ −1` at each ζ-zero. -/
theorem detection_poly_eq {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) (t : ℝ) :
    dpoly (detCoeff N y) (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)) t
      = dpoly (fun _ => (1 : ℝ)) (Finset.Icc 1 N) t * mollifier y t - 1 := by
  have h1mem : (1 : ℕ) ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y) := by
    rw [convSupp, Finset.mem_image]
    exact ⟨(1, 1), by rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; omega, by norm_num⟩
  have hdc : detCoeff N y = fun k => convCoeff (fun _ => (1 : ℝ)) moebiusCoeff
      (Finset.Icc 1 N) (Finset.Icc 1 y) k - (if k = 1 then (1 : ℝ) else 0) := rfl
  rw [hdc, dpoly_sub, dpoly_onehot _ _ h1mem]
  congr 1
  rw [mollifier, ← dpoly_mul_eq_dpoly (fun _ => (1 : ℝ)) moebiusCoeff (Finset.Icc 1 N)
    (Finset.Icc 1 y) t (fun m hm => (Finset.mem_Icc.mp hm).1) (fun n hn => (Finset.mem_Icc.mp hn).1)]

/-- **The detection second moment lives above the cutoff.**  The window `L²` mass of the detection
polynomial `D_N·M_y − 1` is its Montgomery–Vaughan mean value whose diagonal main term
`U·∑ₖ eₖ²` runs only over `k > min(N, y)` (by `detection_diagonal_tail`), plus the off-diagonal
remainder.  So the detection `L²` mass is carried entirely by the high-index tail. -/
theorem detection_secondMoment (N y : ℕ) (T U : ℝ) :
    (∫ t in T..T + U, ‖dpoly (detCoeff N y) (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)) t‖ ^ 2)
      = U * (∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
              (detCoeff N y k) ^ 2)
        + ∑ m ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y),
            ∑ n ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).erase m,
              detCoeff N y m * detCoeff N y n * cosInt (Real.log n - Real.log m) T U := by
  rw [secondMoment_meanValue, detection_diagonal_tail]

/-- `(eₖ·log k)² ≤ d(k)² k^{-2σ}(log k)²` above the cutoff. -/
theorem sq_detCoeffW_log_le {N y k : ℕ} (σ : ℝ) (hk1 : 1 ≤ k) (hk : k ≠ 1) :
    (detCoeffW N y σ k * Real.log k) ^ 2
      ≤ (k.divisors.card : ℝ) ^ 2 * ((k : ℝ) ^ (-2 * σ) * (Real.log k) ^ 2) := by
  have h := sq_detCoeffW_le (N := N) (y := y) σ hk1 hk
  calc (detCoeffW N y σ k * Real.log k) ^ 2
      = (detCoeffW N y σ k) ^ 2 * (Real.log k) ^ 2 := by ring
    _ ≤ ((k.divisors.card : ℝ) ^ 2 * (k : ℝ) ^ (-2 * σ)) * (Real.log k) ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = (k.divisors.card : ℝ) ^ 2 * ((k : ℝ) ^ (-2 * σ) * (Real.log k) ^ 2) := by ring

/-- **The `E'` diagonal is bounded by the summable log-weighted tail.**  The diagonal of the
derivative detection polynomial `E' = −i·dpoly(eₖ·log k)` is
`∑_{k>min}(eₖ log k)² ≤ ∑'𝟙_{k>min} d(k)²k^{-2σ}(log k)² → 0`, via `sq_detCoeffW_log_le` and
`summable_divisor_sq_log_rpow`.  This bounds `∫‖E'‖²`, the second term in the large-values inequality. -/
theorem detection_deriv_diagonal_le_tsum {N y : ℕ} (σ : ℝ) (hσ : 1 / 2 < σ) (hmin : 1 ≤ min N y) :
    ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
        (detCoeffW N y σ k * Real.log k) ^ 2
      ≤ ∑' k : ℕ, Set.indicator {j | min N y < j}
          (fun k => (k.divisors.card : ℝ) ^ 2 * ((k : ℝ) ^ (-2 * σ) * (Real.log k) ^ 2)) k := by
  set g : ℕ → ℝ := fun k => (k.divisors.card : ℝ) ^ 2 * ((k : ℝ) ^ (-2 * σ) * (Real.log k) ^ 2)
    with hg_def
  have hgnn : ∀ k, 0 ≤ g k := fun k => by rw [hg_def]; positivity
  have hind_summable : Summable (Set.indicator {j | min N y < j} g) :=
    (summable_divisor_sq_log_rpow hσ).indicator _
  calc ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
          (detCoeffW N y σ k * Real.log k) ^ 2
      ≤ ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
          Set.indicator {j | min N y < j} g k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkmem : k ∈ {j | min N y < j} := hk.2
        rw [Set.indicator_of_mem hkmem]
        have hk1 : 1 ≤ k := le_of_lt (lt_of_le_of_lt hmin hk.2)
        have hkne : k ≠ 1 := by omega
        exact sq_detCoeffW_log_le σ hk1 hkne
    _ ≤ ∑' k : ℕ, Set.indicator {j | min N y < j} g k :=
        hind_summable.sum_le_tsum _ (fun k _ => Set.indicator_nonneg (fun j _ => hgnn j) k)

/-- The convolution support lies in `[1, N·y]` (products of factors `≤ N`, `≤ y`). -/
theorem convSupp_subset_Icc (N y : ℕ) :
    convSupp (Finset.Icc 1 N) (Finset.Icc 1 y) ⊆ Finset.Icc 1 (N * y) := by
  intro k hk
  rw [convSupp, Finset.mem_image] at hk
  obtain ⟨p, hp, hpk⟩ := hk
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  rw [Finset.mem_Icc, ← hpk]
  refine ⟨?_, Nat.mul_le_mul hp.1.2 hp.2.2⟩
  calc 1 ≤ p.1 := hp.1.1
    _ ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ (by omega)

/-- The σ-weighted detection diagonal `∑_{k∈convSupp} eₖ(σ)²` runs only over `k > min(N,y)`. -/
theorem detectionW_diagonal_tail (N y : ℕ) (σ : ℝ) :
    ∑ k ∈ convSupp (Finset.Icc 1 N) (Finset.Icc 1 y), (detCoeffW N y σ k) ^ 2
      = ∑ k ∈ (convSupp (Finset.Icc 1 N) (Finset.Icc 1 y)).filter (fun k => min N y < k),
          (detCoeffW N y σ k) ^ 2 := by
  refine (Finset.sum_filter_of_ne ?_).symm
  intro k hk hne
  by_contra hle
  rw [not_lt] at hle
  have hk1 : 1 ≤ k := one_le_of_mem_convSupp hk
  have hz : detCoeffW N y σ k = 0 :=
    detCoeffW_eq_zero_of_le σ hk1 (le_trans hle (min_le_left _ _)) (le_trans hle (min_le_right _ _))
  rw [hz] at hne; simp at hne

end RHTower
