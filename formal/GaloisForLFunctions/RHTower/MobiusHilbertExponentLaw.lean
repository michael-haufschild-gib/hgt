import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicOmega
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood

/-!
# Exponent law for the Möbius Hilbert form

Let `E_N = Σ_{m,n≤N} μ(m)μ(n)/(m+n)` and `Θ = sup {Re ρ : ζ(ρ) = 0}` (`zetaZeroAbscissa`).  For
every `a ≥ 0`,

`E_N = O(N^{a+ε}) for every ε > 0`  ⟺  `Θ ≤ (1+a)/2`

(`forall_exists_hilbert_le_rpow_iff`).  The Hilbert form is a quantitative detector of the zero
abscissa: its growth exponent is `2Θ - 1`.  At `a = 0` this is the Hilbert criterion for RH.  Any
unconditional power saving `E_N ≪ N^{1-δ}` is equivalent to a zero-free strip `Re s > 1 - δ/2`.

* `⇐`: Littlewood's bound `M(N) ≪ N^{Θ+ε}` (`mobiusMertens_subpower_zetaZeroAbscissa`) and the
  split of `∫_0^∞ F_N²` at `x = 1/(N+1)`.
* `⇒`: a sharp tail comparison (`F_N` against `F_M` with `M = ⌈y^{-(1+1/m)}⌉`), a layer-cake
  integration by parts, Fatou and the closed-half-plane energy criterion.

Across the Gamma--Hankel family `E_N(r) = Σ_{m,n≤N} μ(m)μ(n)Γ(r)/(m+n)^r` the threshold is `2Θ`:
for `r ≠ 2Θ` the energies are bounded exactly when `r > 2Θ` and tend to infinity otherwise
(`bddAbove_range_finiteMobiusGammaHankelEnergy_iff`).  There is no oscillating regime.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The complex Mertens sum and the shifted real Mertens sum have the same size. -/
theorem norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal (N : ℕ) :
    ‖mobiusMertensPartialSum N‖ = |shiftedMertensReal N| := by
  have h : mobiusMertensPartialSum N = ((shiftedMertensReal N : ℝ) : ℂ) := by
    unfold mobiusMertensPartialSum shiftedMertensReal shiftedMobiusRealCoefficient
    rw [Finset.sum_range_succ']
    simp [mobiusComplexCoefficient]
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- Near `0` (`Nx ≤ 1`) the pencil is at most twice the largest Mertens value up to `N`. -/
theorem abs_finiteMobiusLaplacePencil_le_of_near_zero {N : ℕ} {A x : ℝ}
    (hA : ∀ k ≤ N, |shiftedMertensReal k| ≤ A) (hx : 0 ≤ x) (hNx : (N : ℝ) * x ≤ 1) :
    |finiteMobiusLaplacePencil N x| ≤ 2 * A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  set q := Real.exp (-x) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1q : 1 - q ≤ x := by
    have := Real.add_one_le_exp (-x)
    rw [hq]; linarith
  have h1q0 : 0 ≤ 1 - q := by linarith
  rw [finiteMobiusLaplacePencil_eq_abel]
  have hS : |∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| ≤ N * A := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range N, |shiftedMertensReal k * q ^ k|
        ≤ ∑ _k ∈ Finset.range N, A := Finset.sum_le_sum fun k hk => by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 k)]
          exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq0 hq1)).trans
            (hA k (Finset.mem_range.mp hk).le)
      _ = N * A := by simp
  have hfirst : |shiftedMertensReal N * q ^ N| ≤ A := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 N)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq0 hq1)).trans (hA N le_rfl)
  have hsecond : |(1 - q) * ∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| ≤ A := by
    rw [abs_mul, abs_of_nonneg h1q0]
    calc (1 - q) * |∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| ≤ x * (N * A) :=
          mul_le_mul h1q hS (abs_nonneg _) hx
      _ = (N * x) * A := by ring
      _ ≤ 1 * A := mul_le_mul_of_nonneg_right hNx hA0
      _ = A := one_mul A
  calc _ ≤ |shiftedMertensReal N * q ^ N| +
        |(1 - q) * ∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| := abs_add_le _ _
    _ ≤ 2 * A := by linarith

/-- **Mertens bounds control the Hilbert form.**  If `|M(n)| ≤ C₁(n+1)^b` with `b > 1/2`, then
`E_N ≤ C(N+1)^{2b-1}`.  Split at `x = 1/(N+1)`: below it the pencil is `O(N^b)`, above it
`|F_N(x)| ≪ x^{-b}`. -/
theorem exists_hilbert_le_rpow_of_mertens {b C₁ : ℝ} (hb : 1 / 2 < b) (hC₁ : 0 ≤ C₁)
    (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤ C₁ * ((n : ℝ) + 1) ^ b) :
    ∃ C : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ (2 * b - 1) := by
  have hb0 : 0 ≤ b := by linarith
  set K : ℝ := C₁ * (Real.exp (b ^ 2) + 2 ^ b * mixedSubpowerAbelConstant b) with hKdef
  have h2b : 0 < 2 * b - 1 := by linarith
  refine ⟨4 * C₁ ^ 2 + K ^ 2 / (2 * b - 1) + 2, fun N => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  set u : ℝ := 1 / ((N : ℝ) + 1) with hudef
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hudef, div_le_one hNpos]; exact hN1
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ (2 * b - 1) := Real.one_le_rpow hN1 h2b.le
  have hcont : Continuous fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2 :=
    (continuous_finiteMobiusLaplacePencil N).pow 2
  have hInt := integrableOn_sq_finiteMobiusLaplacePencil N
  rw [← integral_sq_finiteMobiusLaplacePencil, ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  -- far part
  have hfar : ∫ x in Ioi (1 : ℝ), finiteMobiusLaplacePencil N x ^ 2 ≤ 2 := by
    have h := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N (r := 1) one_pos
    simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one, Real.rpow_one] at h
    linarith
  -- near and middle parts
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 u) (hcont.intervalIntegrable (μ := volume) u 1)
  rw [← intervalIntegral.integral_of_le zero_le_one, ← hsplit]
  have hA : ∀ k ≤ N, |shiftedMertensReal k| ≤ C₁ * ((N : ℝ) + 1) ^ b := by
    intro k hk
    rw [← norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal]
    refine (hM k).trans (mul_le_mul_of_nonneg_left ?_ hC₁)
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1) hb0
  have hnear : ∫ x in (0 : ℝ)..u, finiteMobiusLaplacePencil N x ^ 2 ≤
      4 * C₁ ^ 2 * ((N : ℝ) + 1) ^ (2 * b - 1) := by
    have hbd : ∀ x ∈ Icc (0 : ℝ) u, finiteMobiusLaplacePencil N x ^ 2 ≤
        (2 * (C₁ * ((N : ℝ) + 1) ^ b)) ^ 2 := by
      intro x hx
      have hNx : (N : ℝ) * x ≤ 1 := by
        calc (N : ℝ) * x ≤ N * u := mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg N)
          _ ≤ 1 := by rw [hudef]; rw [mul_one_div, div_le_one hNpos]; linarith
      have h := abs_finiteMobiusLaplacePencil_le_of_near_zero hA hx.1 hNx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have := intervalIntegral.integral_mono_on hu0.le (hcont.intervalIntegrable (μ := volume) 0 u)
      intervalIntegrable_const hbd
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    refine this.trans (le_of_eq ?_)
    have hsplit : ((N : ℝ) + 1) ^ (2 * b) = ((N : ℝ) + 1) ^ (2 * b - 1) * ((N : ℝ) + 1) := by
      rw [← Real.rpow_add_one hNpos.ne']; ring_nf
    have hsq : (((N : ℝ) + 1) ^ b) ^ 2 = ((N : ℝ) + 1) ^ (2 * b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; ring_nf
    rw [hudef, mul_pow, mul_pow, hsq, hsplit]
    field_simp
    ring
  have hmid : ∫ x in u..1, finiteMobiusLaplacePencil N x ^ 2 ≤
      K ^ 2 / (2 * b - 1) * ((N : ℝ) + 1) ^ (2 * b - 1) := by
    have hbd : ∀ x ∈ Icc u 1, finiteMobiusLaplacePencil N x ^ 2 ≤ K ^ 2 * x ^ (-(2 * b)) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hu0 hx.1
      have h := abs_finiteMobiusLaplacePencil_le_of_mertensBound hb0 hC₁ hx0 hx.2 hM N
      rw [← hKdef] at h
      have hK0 : 0 ≤ K * (1 / x) ^ b := le_trans (abs_nonneg _) h
      have h2 : finiteMobiusLaplacePencil N x ^ 2 ≤ (K * (1 / x) ^ b) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      refine h2.trans (le_of_eq ?_)
      have hx2 : ((1 / x) ^ b) ^ 2 = x ^ (-(2 * b)) := by
        rw [one_div, Real.inv_rpow hx0.le, inv_pow, ← Real.rpow_natCast (x ^ b),
          ← Real.rpow_mul hx0.le, Real.rpow_neg hx0.le]
        norm_num
        ring_nf
      rw [mul_pow, hx2]
    have hcont2 : ContinuousOn (fun x : ℝ => K ^ 2 * x ^ (-(2 * b))) (uIcc u 1) := by
      intro x hx
      rw [uIcc_of_le hu1] at hx
      exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
        (Or.inl (lt_of_lt_of_le hu0 hx.1).ne'))).continuousWithinAt
    have := intervalIntegral.integral_mono_on hu1 (hcont.intervalIntegrable (μ := volume) u 1)
      hcont2.intervalIntegrable hbd
    refine this.trans ?_
    have hup : u ^ (-(2 * b - 1)) = ((N : ℝ) + 1) ^ (2 * b - 1) := by
      rw [hudef, one_div, Real.inv_rpow hNpos.le, ← Real.rpow_neg hNpos.le, neg_neg]
    have hval : ∫ x in u..1, K ^ 2 * x ^ (-(2 * b)) =
        K ^ 2 * ((((N : ℝ) + 1) ^ (2 * b - 1) - 1) / (2 * b - 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le hu1]; exact fun h => absurd h.1 (not_le.mpr hu0)⟩)]
      rw [show -(2 * b) + 1 = -(2 * b - 1) by ring, Real.one_rpow, hup]
      have hne : -(2 * b - 1) ≠ 0 := by linarith
      field_simp
      ring
    rw [hval]
    have hK2 : 0 ≤ K ^ 2 / (2 * b - 1) := by positivity
    calc K ^ 2 * ((((N : ℝ) + 1) ^ (2 * b - 1) - 1) / (2 * b - 1))
        = K ^ 2 / (2 * b - 1) * ((N : ℝ) + 1) ^ (2 * b - 1) - K ^ 2 / (2 * b - 1) := by ring
      _ ≤ K ^ 2 / (2 * b - 1) * ((N : ℝ) + 1) ^ (2 * b - 1) := by linarith
  have hK2 : 0 ≤ K ^ 2 / (2 * b - 1) := by positivity
  have hX : 2 ≤ 2 * ((N : ℝ) + 1) ^ (2 * b - 1) := by linarith
  calc (∫ x in (0 : ℝ)..u, finiteMobiusLaplacePencil N x ^ 2) +
        (∫ x in u..1, finiteMobiusLaplacePencil N x ^ 2) +
        ∫ x in Ioi (1 : ℝ), finiteMobiusLaplacePencil N x ^ 2
      ≤ 4 * C₁ ^ 2 * ((N : ℝ) + 1) ^ (2 * b - 1) +
          K ^ 2 / (2 * b - 1) * ((N : ℝ) + 1) ^ (2 * b - 1) + 2 := by linarith
    _ ≤ (4 * C₁ ^ 2 + K ^ 2 / (2 * b - 1) + 2) * ((N : ℝ) + 1) ^ (2 * b - 1) := by nlinarith

/-- Layer cake by parts for a power tail: if `∫_y^1 g ≤ K y^{-p}` on `[ε, 1]` and `0 ≤ p < s`, then
`∫_ε^1 x^s g ≤ K + sK/(s-p)`. -/
theorem intervalIntegral_rpow_mul_le_of_tail_rpow {g : ℝ → ℝ} (hg : Continuous g)
    {K p s ε : ℝ} (hK : 0 ≤ K) (hp : 0 ≤ p) (hps : p < s) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (htail : ∀ y ∈ Icc ε 1, ∫ x in y..1, g x ≤ K * y ^ (-p)) :
    ∫ x in ε..1, x ^ s * g x ≤ K + s * K / (s - p) := by
  have hs : 0 < s := lt_of_le_of_lt hp hps
  set T : ℝ → ℝ := fun y => ∫ x in y..1, g x with hT
  have hTderiv : ∀ x, HasDerivAt T (-g x) x := by
    intro x
    have h := intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable x 1)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
    simpa [T] using h
  have hpos : ∀ x ∈ uIcc ε 1, 0 < x := by
    intro x hx
    rw [uIcc_of_le hε1] at hx
    exact lt_of_lt_of_le hε0 hx.1
  have hu : ∀ x ∈ uIcc ε 1, HasDerivAt (fun x : ℝ => x ^ s) (s * x ^ (s - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')
  have hv : ∀ x ∈ uIcc ε 1, HasDerivAt (fun x => -T x) (g x) x := by
    intro x _
    have := (hTderiv x).neg
    rwa [neg_neg] at this
  have hcoefCont : ContinuousOn (fun x : ℝ => s * x ^ (s - 1)) (uIcc ε 1) := fun x hx =>
    (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl (hpos x hx).ne'))).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hcoefCont.intervalIntegrable (hg.intervalIntegrable _ _)
  have hT1 : T 1 = 0 := by simp [T]
  have hTcont : Continuous T := continuous_iff_continuousAt.mpr fun x => (hTderiv x).continuousAt
  have hcoef : ∀ x ∈ uIcc ε 1, 0 ≤ s * x ^ (s - 1) := fun x hx =>
    mul_nonneg hs.le (Real.rpow_nonneg (hpos x hx).le _)
  have hpowCont : ContinuousOn (fun x : ℝ => s * K * x ^ (s - 1 - p)) (uIcc ε 1) := fun x hx =>
    (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
      (Or.inl (hpos x hx).ne'))).continuousWithinAt
  have hmono : ∫ x in ε..1, s * x ^ (s - 1) * T x ≤ ∫ x in ε..1, s * K * x ^ (s - 1 - p) := by
    apply intervalIntegral.integral_mono_on hε1
    · exact (hcoefCont.mul hTcont.continuousOn).intervalIntegrable
    · exact hpowCont.intervalIntegrable
    · intro x hx
      have hx' : x ∈ uIcc ε 1 := by rw [uIcc_of_le hε1]; exact hx
      have hx0 := hpos x hx'
      calc s * x ^ (s - 1) * T x ≤ s * x ^ (s - 1) * (K * x ^ (-p)) :=
            mul_le_mul_of_nonneg_left (htail x hx) (hcoef x hx')
        _ = s * K * (x ^ (s - 1) * x ^ (-p)) := by ring
        _ = s * K * x ^ (s - 1 - p) := by rw [← Real.rpow_add hx0]; ring_nf
  have hcalc : ∫ x in ε..1, s * K * x ^ (s - 1 - p) = s * K * ((1 - ε ^ (s - p)) / (s - p)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    rw [show s - 1 - p + 1 = s - p by ring, Real.one_rpow]
  have hmain : ∫ x in ε..1, x ^ s * g x =
      ε ^ s * T ε + ∫ x in ε..1, s * x ^ (s - 1) * T x := by
    rw [hibp, hT1]
    simp only [Real.one_rpow, mul_zero, zero_sub, neg_zero]
    rw [show (fun x => s * x ^ (s - 1) * -T x) = fun x => -(s * x ^ (s - 1) * T x) by
      funext x; ring, intervalIntegral.integral_neg]
    ring
  have hTε := htail ε ⟨le_rfl, hε1⟩
  have hεs : 0 ≤ ε ^ s := Real.rpow_nonneg hε0.le _
  have hfirst : ε ^ s * T ε ≤ K := by
    calc ε ^ s * T ε ≤ ε ^ s * (K * ε ^ (-p)) := mul_le_mul_of_nonneg_left hTε hεs
      _ = K * ε ^ (s - p) := by rw [← mul_assoc, mul_comm (ε ^ s) K, mul_assoc,
          ← Real.rpow_add hε0]; ring_nf
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hε0.le hε1 (by linarith)) hK
      _ = K := mul_one K
  have hsp : 0 < s - p := by linarith
  have hsecond : s * K * ((1 - ε ^ (s - p)) / (s - p)) ≤ s * K / (s - p) := by
    have h0 : 0 ≤ ε ^ (s - p) := Real.rpow_nonneg hε0.le _
    have he : s * K * ((1 - ε ^ (s - p)) / (s - p)) =
        s * K / (s - p) - s * K * ε ^ (s - p) / (s - p) := by ring
    have hnn : 0 ≤ s * K * ε ^ (s - p) / (s - p) := by positivity
    linarith
  rw [hmain]
  linarith

/-- **Sharp tail.**  From `E_N ≤ C(N+1)^a`, compare `F_N` with `F_M`, `M = ⌈y^{-(1+1/m)}⌉`: on
`[y, 1]` the difference is at most `2e^{-y^{-1/m}}/y ≤ 2·m!`.  Hence
`∫_y^1 F_N² ≪ y^{-(1+1/m)a}` uniformly in `N`. -/
theorem intervalIntegral_sq_pencil_le_of_hilbert_power {C a : ℝ} (hC0 : 0 ≤ C) (ha : 0 ≤ a)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ a)
    (m : ℕ) (hm : 1 ≤ m) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (N : ℕ) :
    ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤
      (2 * C * 3 ^ a + 8 * (m.factorial : ℝ) ^ 2) * y ^ (-((1 + 1 / (m : ℝ)) * a)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Y : ℝ := y ^ (-(1 + 1 / (m : ℝ))) with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by
    have : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith)
  set M : ℕ := ⌈Y⌉₊ with hMdef
  have hYM : Y ≤ (M : ℝ) := Nat.le_ceil Y
  have hM1 : (M : ℝ) + 1 ≤ 3 * Y := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Y)
    linarith
  have hYa : Y ^ a = y ^ (-((1 + 1 / (m : ℝ)) * a)) := by
    rw [hYdef, ← Real.rpow_mul hy0.le]; ring_nf
  have hpowM : ((M : ℝ) + 1) ^ a ≤ 3 ^ a * y ^ (-((1 + 1 / (m : ℝ)) * a)) := by
    calc ((M : ℝ) + 1) ^ a ≤ (3 * Y) ^ a := Real.rpow_le_rpow (by positivity) hM1 ha
      _ = 3 ^ a * Y ^ a := Real.mul_rpow (by norm_num) (by linarith)
      _ = _ := by rw [hYa]
  have hyp1 : 1 ≤ y ^ (-((1 + 1 / (m : ℝ)) * a)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by
      have : 0 ≤ (1 + 1 / (m : ℝ)) * a := by positivity
      linarith)
  have hfact : (0 : ℝ) ≤ 8 * (m.factorial : ℝ) ^ 2 := by positivity
  rcases le_or_gt N M with hNM | hMN
  · have h1 := intervalIntegral_sq_pencil_le_energy N hy0 hy1
    have h2 := hH N
    have h3 : ((N : ℝ) + 1) ^ a ≤ ((M : ℝ) + 1) ^ a :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hNM 1) ha
    have h4 : C * ((N : ℝ) + 1) ^ a ≤ C * (3 ^ a * y ^ (-((1 + 1 / (m : ℝ)) * a))) :=
      mul_le_mul_of_nonneg_left (h3.trans hpowM) hC0
    have h3a : (0 : ℝ) ≤ 3 ^ a := by positivity
    have hYp : 0 ≤ y ^ (-((1 + 1 / (m : ℝ)) * a)) := by linarith
    calc ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤ C * ((N : ℝ) + 1) ^ a := h1.trans h2
      _ ≤ C * (3 ^ a * y ^ (-((1 + 1 / (m : ℝ)) * a))) := h4
      _ = (C * 3 ^ a) * y ^ (-((1 + 1 / (m : ℝ)) * a)) := by ring
      _ ≤ (2 * C * 3 ^ a + 8 * (m.factorial : ℝ) ^ 2) * y ^ (-((1 + 1 / (m : ℝ)) * a)) :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC0 h3a]) hYp
  · have hpt : ∀ x ∈ Icc y 1, finiteMobiusLaplacePencil N x ^ 2 ≤
        2 * finiteMobiusLaplacePencil M x ^ 2 + 8 * (m.factorial : ℝ) ^ 2 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hy0 hx.1
      have hdiff := abs_finiteMobiusLaplacePencil_sub_le hMN.le hx0
      have hden : x / 2 ≤ 1 - Real.exp (-x) := by
        have := exp_neg_le_one_sub_half hx0.le hx.2
        linarith
      have hyYt : y * Y = y ^ (-(1 / (m : ℝ))) := by
        rw [hYdef, show -(1 + 1 / (m : ℝ)) = -1 + -(1 / (m : ℝ)) by ring,
          Real.rpow_add hy0, Real.rpow_neg_one]
        rw [← mul_assoc, mul_inv_cancel₀ hy0.ne', one_mul]
      set t : ℝ := y ^ (-(1 / (m : ℝ))) with htdef
      have ht0 : 0 ≤ t := Real.rpow_nonneg hy0.le _
      have htm : t ^ m = y⁻¹ := by
        rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le,
          show (-(1 / (m : ℝ))) * (m : ℝ) = -1 by field_simp, Real.rpow_neg_one]
      have hnum : Real.exp (-x) ^ (M + 1) ≤ Real.exp (-t) := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have : t ≤ x * ((M + 1 : ℕ) : ℝ) := by
          push_cast
          calc t = y * Y := hyYt.symm
            _ ≤ x * ((M : ℝ) + 1) := mul_le_mul hx.1 (by linarith) (by linarith) hx0.le
        linarith
      have hexpt : Real.exp (-t) ≤ (m.factorial : ℝ) * y := by
        have h := Real.pow_div_factorial_le_exp t ht0 m
        rw [htm] at h
        have hfp : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos t) (by positivity)]
        calc (↑m.factorial * y)⁻¹ = y⁻¹ / m.factorial := by field_simp
          _ ≤ Real.exp t := h
      have hbound : |finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x| ≤
          2 * m.factorial := by
        refine hdiff.trans ?_
        have hyx : y ≤ x := hx.1
        rw [div_le_iff₀ (by linarith)]
        have hfp : (0 : ℝ) ≤ m.factorial := by positivity
        nlinarith
      have hsq : (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x) ^ 2 ≤
          4 * (m.factorial : ℝ) ^ 2 := by
        rw [← sq_abs]
        have := pow_le_pow_left₀ (abs_nonneg _) hbound 2
        linarith
      nlinarith [sq_nonneg (finiteMobiusLaplacePencil N x - 2 * finiteMobiusLaplacePencil M x)]
    have hcontN := continuous_finiteMobiusLaplacePencil N
    have hcontM := continuous_finiteMobiusLaplacePencil M
    have hc2 : Continuous fun x : ℝ => 2 * finiteMobiusLaplacePencil M x ^ 2 :=
      continuous_const.mul (hcontM.pow 2)
    have hmono : ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤
        ∫ x in y..1, (2 * finiteMobiusLaplacePencil M x ^ 2 + 8 * (m.factorial : ℝ) ^ 2) :=
      intervalIntegral.integral_mono_on hy1 ((hcontN.pow 2).intervalIntegrable _ _)
        ((hc2.add continuous_const).intervalIntegrable _ _) hpt
    have h1 : ∫ x in y..1, (2 * finiteMobiusLaplacePencil M x ^ 2 + 8 * (m.factorial : ℝ) ^ 2) =
        (∫ x in y..1, 2 * finiteMobiusLaplacePencil M x ^ 2) +
          ∫ _x in y..1, 8 * (m.factorial : ℝ) ^ 2 :=
      intervalIntegral.integral_add (hc2.intervalIntegrable _ _) intervalIntegrable_const
    have h2 : ∫ x in y..1, 2 * finiteMobiusLaplacePencil M x ^ 2 =
        2 * ∫ x in y..1, finiteMobiusLaplacePencil M x ^ 2 :=
      intervalIntegral.integral_const_mul _ _
    have h3 : ∫ _x in y..1, 8 * (m.factorial : ℝ) ^ 2 = (1 - y) * (8 * (m.factorial : ℝ) ^ 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    have hM := intervalIntegral_sq_pencil_le_energy M hy0 hy1
    have hHM := hH M
    have h4 : C * ((M : ℝ) + 1) ^ a ≤ C * (3 ^ a * y ^ (-((1 + 1 / (m : ℝ)) * a))) :=
      mul_le_mul_of_nonneg_left hpowM hC0
    rw [h1, h2, h3] at hmono
    have h3a : (0 : ℝ) ≤ 3 ^ a := by positivity
    nlinarith

/-- A power bound `E_N(1) ≤ C(N+1)^a` bounds `E_N(r)` uniformly in `N` once `r - 1 > (1+1/m)a`. -/
theorem exists_forall_energy_le_of_hilbert_power {C a r : ℝ} (hC0 : 0 ≤ C) (ha : 0 ≤ a)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ a)
    (m : ℕ) (hm : 1 ≤ m) (hr : (1 + 1 / (m : ℝ)) * a < r - 1) :
    ∃ B : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N r ≤ B := by
  set p : ℝ := (1 + 1 / (m : ℝ)) * a with hpdef
  have hp : 0 ≤ p := by positivity
  have hr1 : 0 < r - 1 := lt_of_le_of_lt hp hr
  have hpos : 0 < r := by linarith
  set K : ℝ := 2 * C * 3 ^ a + 8 * (m.factorial : ℝ) ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨K + (r - 1) * K / (r - 1 - p) + 4 * ((1 / 2) ^ r * Real.Gamma r), fun N => ?_⟩
  have hInt := integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hpos
  rw [← integral_finiteMobiusLaplacePencil_sq N hpos,
    ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hfar := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N hpos
  have hcont : Continuous fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2 :=
    (continuous_finiteMobiusLaplacePencil N).pow 2
  have hnear : ∫ x in Ioc (0 : ℝ) 1, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      K + (r - 1) * K / (r - 1 - p) := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε : ℝ := min 1 (δ / ((N : ℝ) ^ 2 + 1)) with hεdef
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεδ : ε * ((N : ℝ) ^ 2 + 1) ≤ δ := by
      have := min_le_right 1 (δ / ((N : ℝ) ^ 2 + 1))
      rw [← hεdef] at this
      calc ε * ((N : ℝ) ^ 2 + 1) ≤ δ / ((N : ℝ) ^ 2 + 1) * ((N : ℝ) ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = δ := by field_simp
    have hfcont : ContinuousOn (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
        (uIcc 0 1) := fun x _ =>
      ((Real.continuousAt_rpow_const _ _ (Or.inr hr1.le)).mul hcont.continuousAt).continuousWithinAt
    have hi1 : IntervalIntegrable (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
        volume 0 ε :=
      (hfcont.mono (uIcc_subset_uIcc (by simp) (by simp [hε0.le, hε1]))).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2)
        volume ε 1 :=
      (hfcont.mono (uIcc_subset_uIcc (by simp [hε0.le, hε1]) (by simp))).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hsmall : ∫ x in (0 : ℝ)..ε, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
        ε * ((N : ℝ) ^ 2 + 1) := by
      have hb : ∀ x ∈ Icc (0 : ℝ) ε, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
          (N : ℝ) ^ 2 + 1 := by
        intro x hx
        have hx1 : x ≤ 1 := hx.2.trans hε1
        have hpw : x ^ (r - 1) ≤ 1 := Real.rpow_le_one hx.1 hx1 hr1.le
        have hp0 : 0 ≤ x ^ (r - 1) := Real.rpow_nonneg hx.1 _
        have hF := abs_finiteMobiusLaplacePencil_le_card N hx.1
        have hF2 : finiteMobiusLaplacePencil N x ^ 2 ≤ (N : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hF 2
        nlinarith [sq_nonneg (finiteMobiusLaplacePencil N x)]
      have := intervalIntegral.integral_mono_on hε0.le hi1 intervalIntegrable_const hb
      rw [intervalIntegral.integral_const] at this
      simpa using this
    have hlayer := intervalIntegral_rpow_mul_le_of_tail_rpow hcont hK hp hr hε0 hε1
      (fun y hy => intervalIntegral_sq_pencil_le_of_hilbert_power hC0 ha hH m hm
        (lt_of_lt_of_le hε0 hy.1) hy.2 N)
    linarith
  linarith

/-- **Hilbert growth bounds the zero abscissa.**  `E_N(1) ≤ C(N+1)^a` for all `N` forces every zeta
zero to satisfy `Re ρ ≤ (1+a)/2`. -/
theorem zetaZeroAbscissa_le_of_hilbert_power {C a : ℝ} (ha : 0 ≤ a)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ a) :
    zetaZeroAbscissa ≤ (1 + a) / 2 := by
  have hC0 : 0 ≤ C := by
    have h0 := hH 0
    rw [finiteMobiusGammaHankelEnergy_zero] at h0
    simpa using h0
  apply le_of_forall_gt_imp_ge_of_dense
  intro σ hσ
  rcases le_or_gt 1 σ with h1 | h1
  · exact zetaZeroAbscissa_le_one.trans h1
  set d : ℝ := 2 * σ - 1 - a with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  set m : ℕ := ⌈a / d⌉₊ + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmad : a / d < m := by
    have := Nat.le_ceil (a / d)
    have h' : ((⌈a / d⌉₊ + 1 : ℕ) : ℝ) = (⌈a / d⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [hmdef, h']
    linarith
  have hr : (1 + 1 / (m : ℝ)) * a < 2 * σ - 1 := by
    have : a / (m : ℝ) < d := by
      rw [div_lt_iff₀ hm0]
      rw [div_lt_iff₀ hd] at hmad
      linarith
    have e : (1 + 1 / (m : ℝ)) * a = a + a / m := by ring
    rw [e]; linarith
  obtain ⟨B, hB⟩ := exists_forall_energy_le_of_hilbert_power hC0 ha hH m hm hr
  have hσ0 : 0 < σ := by linarith
  have hmem := (memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    hσ0 hB).1
  apply csSup_le zetaZeroReSet_nonempty
  rintro x ⟨ρ, hρ, rfl⟩
  by_contra hcon
  rw [not_le] at hcon
  have hρ1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hρ)
  exact riemannZeta_ne_zero_of_memLp_mobiusLaplaceLogMellinLineSource_closed hσ0 h1 hmem
    hcon.le hρ1 hρ

/-- **The zero abscissa bounds Hilbert growth.**  With `Θ` the supremum of real parts of zeta
zeros, `E_N(1) ≤ C(N+1)^{2Θ-1+ε}` for every `ε > 0` (Littlewood at `Θ`). -/
theorem exists_hilbert_le_rpow_zetaZeroAbscissa {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤
      C * ((N : ℝ) + 1) ^ (2 * zetaZeroAbscissa - 1 + ε) := by
  obtain ⟨C₁, hC₁, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa (ε / 2) (by linarith)
  obtain ⟨C, hC⟩ := exists_hilbert_le_rpow_of_mertens
    (by linarith [half_le_zetaZeroAbscissa] : (1 : ℝ) / 2 < zetaZeroAbscissa + ε / 2) hC₁ hM
  refine ⟨C, fun N => ?_⟩
  have := hC N
  rwa [show 2 * (zetaZeroAbscissa + ε / 2) - 1 = 2 * zetaZeroAbscissa - 1 + ε by ring] at this

/-- **Exponent law.**  For `a ≥ 0`, the Möbius Hilbert form is `O(N^{a+ε})` for every `ε > 0`
exactly when every zeta zero has real part at most `(1+a)/2`.  So
`Σ_{m,n≤N} μ(m)μ(n)/(m+n) = N^{2Θ-1+o(1)}` in the upper-bound sense, `Θ = sup Re ρ`; at `a = 0`
this is RH. -/
theorem forall_exists_hilbert_le_rpow_iff {a : ℝ} (ha : 0 ≤ a) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
        finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ (a + ε)) ↔
      zetaZeroAbscissa ≤ (1 + a) / 2 := by
  constructor
  · intro h
    apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    obtain ⟨C, hC⟩ := h (2 * t - 1 - a) (by linarith)
    have := zetaZeroAbscissa_le_of_hilbert_power (by linarith : (0 : ℝ) ≤ a + (2 * t - 1 - a)) hC
    linarith
  · intro hΘ ε hε
    obtain ⟨C, hC⟩ := exists_hilbert_le_rpow_zetaZeroAbscissa hε
    have hC0 : 0 ≤ C := by
      have h0 := hC 0
      rw [finiteMobiusGammaHankelEnergy_zero] at h0
      have hp : (0 : ℝ) < ((0 : ℕ) + 1 : ℝ) ^ (2 * zetaZeroAbscissa - 1 + ε) := by positivity
      simp at h0 hp
      exact h0
    refine ⟨C, fun N => (hC N).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC0
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      (by linarith)

/-- **Mertens bounds bound the energies above twice the exponent.**  If `|M(n)| ≤ C₁(n+1)^b` and
`2b < r`, then `E_N(r) = ∫_0^∞ x^{r-1}F_N(x)² dx` is bounded uniformly in `N`: on `(0, 1]` the
pencil is `≪ x^{-b}` uniformly in `N`, and `x^{r-1-2b}` is integrable at `0`. -/
theorem exists_forall_energy_le_of_mertens {b C₁ r : ℝ} (hb0 : 0 ≤ b) (hC₁ : 0 ≤ C₁)
    (hM : ∀ n : ℕ, ‖mobiusMertensPartialSum n‖ ≤ C₁ * ((n : ℝ) + 1) ^ b) (hr : 2 * b < r) :
    ∃ B : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N r ≤ B := by
  set K : ℝ := C₁ * (Real.exp (b ^ 2) + 2 ^ b * mixedSubpowerAbelConstant b) with hKdef
  have hr0 : 0 < r := by linarith
  have hrb : 0 < r - 2 * b := by linarith
  refine ⟨K ^ 2 / (r - 2 * b) + 4 * ((1 / 2) ^ r * Real.Gamma r), fun N => ?_⟩
  have hInt := integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hr0
  rw [← integral_finiteMobiusLaplacePencil_sq N hr0, ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hfar := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N hr0
  have hmaj : IntegrableOn (fun x : ℝ => K ^ 2 * x ^ (r - 2 * b - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  have hnear : ∫ x in Ioc 0 1, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      K ^ 2 / (r - 2 * b) := by
    calc ∫ x in Ioc 0 1, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2
        ≤ ∫ x in Ioc 0 1, K ^ 2 * x ^ (r - 2 * b - 1) := by
          refine setIntegral_mono_on (hInt.mono_set Ioc_subset_Ioi_self) hmaj measurableSet_Ioc
            fun x hx => ?_
          have hx0 : 0 < x := hx.1
          have h := abs_finiteMobiusLaplacePencil_le_of_mertensBound hb0 hC₁ hx0 hx.2 hM N
          rw [← hKdef] at h
          have h2 : finiteMobiusLaplacePencil N x ^ 2 ≤ (K * (1 / x) ^ b) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
          have hx2 : ((1 / x) ^ b) ^ 2 = x ^ (-(2 * b)) := by
            rw [one_div, Real.inv_rpow hx0.le, inv_pow, ← Real.rpow_natCast (x ^ b),
              ← Real.rpow_mul hx0.le, Real.rpow_neg hx0.le]
            norm_num
            ring_nf
          have hxr : x ^ (r - 1) * x ^ (-(2 * b)) = x ^ (r - 2 * b - 1) := by
            rw [← Real.rpow_add hx0]; ring_nf
          calc x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2
              ≤ x ^ (r - 1) * (K * (1 / x) ^ b) ^ 2 :=
                mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0.le _)
            _ = K ^ 2 * x ^ (r - 2 * b - 1) := by rw [mul_pow, hx2, ← hxr]; ring
      _ = K ^ 2 / (r - 2 * b) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
            integral_rpow (Or.inl (by linarith))]
          rw [show r - 2 * b - 1 + 1 = r - 2 * b by ring, Real.one_rpow,
            Real.zero_rpow hrb.ne', sub_zero, mul_one_div]
  linarith

/-- Above twice the zero abscissa the Möbius Gamma--Hankel energies are bounded. -/
theorem exists_forall_energy_le_of_two_mul_zetaZeroAbscissa_lt {r : ℝ}
    (hr : 2 * zetaZeroAbscissa < r) :
    ∃ B : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N r ≤ B := by
  set ε : ℝ := (r - 2 * zetaZeroAbscissa) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C₁, hC₁, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε0
  have hΘ := half_le_zetaZeroAbscissa
  exact exists_forall_energy_le_of_mertens (by linarith) hC₁ hM (by rw [hε]; linarith)

/-- Below twice the zero abscissa the Möbius Gamma--Hankel energies tend to infinity. -/
theorem tendsto_finiteMobiusGammaHankelEnergy_atTop_of_lt_two_mul_zetaZeroAbscissa {r : ℝ}
    (hr0 : 0 < r) (hr : r < 2 * zetaZeroAbscissa) :
    Filter.Tendsto (fun N : ℕ => finiteMobiusGammaHankelEnergy N r) Filter.atTop
      Filter.atTop := by
  obtain ⟨ρ, hζ, hρ⟩ := exists_zetaZero_lt_re (b := r / 2) (by linarith)
  have hΘ := zetaZeroAbscissa_le_one
  exact tendsto_finiteMobiusGammaHankelEnergy_atTop_of_riemannZeta_eq_zero hζ hr0
    (by linarith) (by linarith)

/-- **Divergence threshold.**  Off `r = 2Θ`, the Möbius Gamma--Hankel energies
`Σ_{m,n≤N} μ(m)μ(n)Γ(r)/(m+n)^r` are bounded exactly when `r > 2Θ`, and otherwise tend to
infinity; `Θ = sup Re ρ`.  In particular RH holds exactly when they are bounded for every
`r > 1`. -/
theorem bddAbove_range_finiteMobiusGammaHankelEnergy_iff {r : ℝ} (hr0 : 0 < r)
    (hrΘ : r ≠ 2 * zetaZeroAbscissa) :
    BddAbove (Set.range fun N : ℕ => finiteMobiusGammaHankelEnergy N r) ↔
      2 * zetaZeroAbscissa < r := by
  constructor
  · intro ⟨B, hB⟩
    by_contra hle
    have hlt : r < 2 * zetaZeroAbscissa := lt_of_le_of_ne (not_lt.mp hle) hrΘ
    obtain ⟨N, hN⟩ := ((tendsto_finiteMobiusGammaHankelEnergy_atTop_of_lt_two_mul_zetaZeroAbscissa
      hr0 hlt).eventually_gt_atTop B).exists
    exact absurd (hB ⟨N, rfl⟩) (not_le.mpr hN)
  · intro h
    obtain ⟨B, hB⟩ := exists_forall_energy_le_of_two_mul_zetaZeroAbscissa_lt h
    exact ⟨B, by rintro _ ⟨N, rfl⟩; exact hB N⟩

end RHTower
