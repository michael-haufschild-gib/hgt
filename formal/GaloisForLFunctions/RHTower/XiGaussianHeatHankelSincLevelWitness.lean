import GaloisForLFunctions.RHTower.XiGaussianHeatHankelExponentialTypeTransfer

/-!
# A sinc-damped exponential-type zero-side witness, and the window at scale `1/N`

Let `u = w_{q₀}` be an upper off-line heat frequency and `z₀ = z_{q₀}`.  Take the level pair test
`P = K_Λ · ((X − ū) + t(X − u))` of `XiGaussianHeatHankelWindowCeiling`.  It vanishes at every heat
frequency of real part `≤ Λ` other than `u, ū`.  Damp it by an entire function of exponential type:

`Φ(z) = P(z²) · sinc(z)^{2M}`, `sinc z = sin z / z`.

**Theorem** (`exists_sincLevelWitness_zeroSide_re_neg`).  For suitable `Λ`, `t` and `M`,
`Re Σ_q Φ(z_q) \overline{Φ(\bar z_q)} < 0`.

Proof.  The summand is `P(w) \overline{P(\bar w)} · sinc(z)^{4M}`.
* It vanishes below the level, except at `u, ū`.
* At `u` and `ū` it equals `−4 (Im u)² |sinc z₀|^{4M} |K_Λ(u)|²`, for the right phase `t`.
* Above the level, `|sinc z| ≤ 2/|z|` on the strip, so `|sinc z|^{4M} ≤ (4/|w|)^{2M}` beats the
  polynomial growth of `P`.
* The tail relative to the pair is `O((16/(σ₀⁴Λ²))^m)`, with `σ₀ = |sinc z₀| > 0` (since `sin z₀ ≠ 0`
  off the real axis) and `M = deg K_Λ + 2 + m`.  For `Λ σ₀² ≥ 8` and `m` large, the pair wins.

`Φ` is even, entire, of exponential type `2M + 1`, and decays like `1/(1 + |z|)` on the strip.  So
`eventually_re_heatHankel_evenTaylorPoly_neg` applies.

**Theorem** (`exists_pos_eventually_exists_heatMomentDet_nonpos_of_not_riemannHypothesis`).  If RH
fails, there is `K > 0` such that for all large `n` some leading heat determinant `Δ_k(K/n)` with
`k ≤ n + 1` is `≤ 0`.

**Corollary** (`riemannHypothesis_iff_forall_eventually_heatMomentDet_pos_scaled`).  RH holds iff
for every `K > 0`, eventually in `n`, all `Δ_k(K/n)` with `k ≤ n + 1` are positive.  The
unconditional window `Δ_N(a) > 0` for `aN ≤ κ` therefore has the optimal order `1/N`.  Unless RH
holds, the largest admissible `aN` is bounded, and the RH content of the ladder is exactly the
unboundedness of the window constant.
-/

open Complex Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry (leadingMatrix)

namespace RHTower

noncomputable section

/-! ## The entire sinc function -/

/-- `sinc ζ = sin ζ / ζ`, extended by `1` at `0`. -/
def entireSinc : ℂ → ℂ := dslope Complex.sin 0

theorem differentiable_entireSinc : Differentiable ℂ entireSinc := by
  have h := (Complex.differentiableOn_dslope (f := Complex.sin) (s := Set.univ) (c := 0)
    Filter.univ_mem).2 Complex.differentiable_sin.differentiableOn
  exact differentiableOn_univ.1 h

theorem entireSinc_of_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) : entireSinc ζ = Complex.sin ζ / ζ := by
  rw [entireSinc, dslope_of_ne _ hζ, slope_def_field, Complex.sin_zero, sub_zero, sub_zero]

theorem entireSinc_zero : entireSinc 0 = 1 := by
  rw [entireSinc, dslope_same, Complex.deriv_sin, Complex.cos_zero]

theorem entireSinc_neg (ζ : ℂ) : entireSinc (-ζ) = entireSinc ζ := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · rw [neg_zero]
  · rw [entireSinc_of_ne_zero (neg_ne_zero.2 hζ), entireSinc_of_ne_zero hζ, Complex.sin_neg,
      neg_div_neg_eq]

theorem entireSinc_conj (ζ : ℂ) :
    entireSinc ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (entireSinc ζ) := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · rw [map_zero, entireSinc_zero, map_one]
  · rw [entireSinc_of_ne_zero ((_root_.map_ne_zero _).2 hζ), entireSinc_of_ne_zero hζ, map_div₀,
      Complex.sin_conj]

theorem norm_sin_le_exp_abs_im (ζ : ℂ) : ‖Complex.sin ζ‖ ≤ Real.exp |ζ.im| := by
  have h1 : ‖Complex.exp (-ζ * I)‖ ≤ Real.exp |ζ.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simp [le_abs_self])
  have h2 : ‖Complex.exp (ζ * I)‖ ≤ Real.exp |ζ.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simp [neg_le_abs])
  have hs : Complex.sin ζ = (Complex.exp (-ζ * I) - Complex.exp (ζ * I)) * I / 2 := rfl
  have h2n : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hs, norm_div, norm_mul, Complex.norm_I, mul_one, h2n]
  have := norm_sub_le (Complex.exp (-ζ * I)) (Complex.exp (ζ * I))
  linarith

theorem norm_entireSinc_le_of_ne {ζ : ℂ} (hζ : ζ ≠ 0) :
    ‖entireSinc ζ‖ ≤ Real.exp |ζ.im| / ‖ζ‖ := by
  rw [entireSinc_of_ne_zero hζ, norm_div]
  gcongr
  exact norm_sin_le_exp_abs_im ζ

/-- `|sinc ζ| ≤ 2 e^{|ζ|}`. -/
theorem norm_entireSinc_le (ζ : ℂ) : ‖entireSinc ζ‖ ≤ 2 * Real.exp ‖ζ‖ := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · rw [entireSinc_zero, norm_one, norm_zero, Real.exp_zero]
    norm_num
  have hpos : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have hex := Real.exp_pos ‖ζ‖
  by_cases h1 : 1 ≤ ‖ζ‖
  · have him : |ζ.im| ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
    calc ‖entireSinc ζ‖ ≤ Real.exp |ζ.im| / ‖ζ‖ := norm_entireSinc_le_of_ne hζ
      _ ≤ Real.exp ‖ζ‖ / 1 := by gcongr
      _ ≤ 2 * Real.exp ‖ζ‖ := by rw [div_one]; linarith
  · push Not at h1
    have hb := Complex.sin_bound h1.le
    have h3 : ‖ζ‖ ^ 3 ≤ ‖ζ‖ := pow_le_of_le_one (norm_nonneg _) h1.le (by norm_num)
    have h5 : ‖ζ‖ ^ 5 ≤ ‖ζ‖ := pow_le_of_le_one (norm_nonneg _) h1.le (by norm_num)
    have e1 : ‖ζ - ζ ^ 3 / 6‖ ≤ ‖ζ‖ + ‖ζ‖ ^ 3 / 6 := by
      calc ‖ζ - ζ ^ 3 / 6‖ ≤ ‖ζ‖ + ‖ζ ^ 3 / 6‖ := norm_sub_le _ _
        _ = ‖ζ‖ + ‖ζ‖ ^ 3 / 6 := by rw [norm_div, norm_pow]; norm_num
    have e2 := norm_sub_norm_le (Complex.sin ζ) (ζ - ζ ^ 3 / 6)
    have hsin : ‖Complex.sin ζ‖ ≤ 2 * ‖ζ‖ := by linarith
    rw [entireSinc_of_ne_zero hζ, norm_div, div_le_iff₀ hpos]
    nlinarith [Real.add_one_le_exp ‖ζ‖]

theorem entireSinc_ne_zero_of_im_ne_zero {ζ : ℂ} (h : ζ.im ≠ 0) : entireSinc ζ ≠ 0 := by
  have hζ : ζ ≠ 0 := fun h0 => h (by rw [h0, Complex.zero_im])
  rw [entireSinc_of_ne_zero hζ]
  refine div_ne_zero (fun hs => h ?_) hζ
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hs
  rw [hk]
  simp

/-! ## The damped witness -/

/-- The damped witness `Φ(z) = P(z²) · sinc(z)^{2M}`. -/
def sincLevelWitness (P : ℂ[X]) (M : ℕ) (z : ℂ) : ℂ := P.eval (z ^ 2) * entireSinc z ^ (2 * M)

theorem differentiable_sincLevelWitness (P : ℂ[X]) (M : ℕ) :
    Differentiable ℂ (sincLevelWitness P M) :=
  (P.differentiable.comp (differentiable_pow 2)).mul (differentiable_entireSinc.pow _)

theorem sincLevelWitness_neg (P : ℂ[X]) (M : ℕ) (z : ℂ) :
    sincLevelWitness P M (-z) = sincLevelWitness P M z := by
  rw [sincLevelWitness, sincLevelWitness, neg_sq, entireSinc_neg]

/-- Exponential type: `|Φ(z)| ≤ C e^{(2M + 1)|z|}`. -/
theorem norm_sincLevelWitness_le_exp (P : ℂ[X]) (M : ℕ) (z : ℂ) :
    ‖sincLevelWitness P M z‖ ≤
      polyMass P * (2 * P.natDegree).factorial * Real.exp 1 * 4 ^ M *
        Real.exp ((2 * M + 1) * ‖z‖) := by
  set d := P.natDegree
  have hz := norm_nonneg z
  have hP := norm_eval_le_polyMass P (z ^ 2)
  rw [norm_pow] at hP
  have hsq : (1 + ‖z‖ ^ 2) ^ d ≤ (1 + ‖z‖) ^ (2 * d) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hfac := Real.pow_div_factorial_le_exp (1 + ‖z‖) (by positivity) (2 * d)
  have hf : (0 : ℝ) < (2 * d).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf] at hfac
  have hs := norm_entireSinc_le z
  have hs2 : ‖entireSinc z‖ ^ (2 * M) ≤ (2 * Real.exp ‖z‖) ^ (2 * M) :=
    pow_le_pow_left₀ (norm_nonneg _) hs _
  have hmass := polyMass_nonneg P
  have hexp : Real.exp (1 + ‖z‖) * (2 * Real.exp ‖z‖) ^ (2 * M) =
      Real.exp 1 * 4 ^ M * Real.exp ((2 * M + 1) * ‖z‖) := by
    rw [mul_pow, pow_mul, ← Real.exp_nat_mul, Real.exp_add]
    have : Real.exp ((2 * M + 1) * ‖z‖) = Real.exp ‖z‖ * Real.exp (↑(2 * M) * ‖z‖) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [this]
    norm_num
    ring
  rw [sincLevelWitness, norm_mul, norm_pow]
  calc ‖P.eval (z ^ 2)‖ * ‖entireSinc z‖ ^ (2 * M)
      ≤ (polyMass P * (1 + ‖z‖) ^ (2 * d)) * (2 * Real.exp ‖z‖) ^ (2 * M) := by
        gcongr
        exact hP.trans (mul_le_mul_of_nonneg_left hsq hmass)
    _ ≤ (polyMass P * ((2 * d).factorial * Real.exp (1 + ‖z‖))) * (2 * Real.exp ‖z‖) ^ (2 * M) := by
        gcongr
        linarith
    _ = polyMass P * (2 * d).factorial *
          (Real.exp (1 + ‖z‖) * (2 * Real.exp ‖z‖) ^ (2 * M)) := by ring
    _ = polyMass P * (2 * d).factorial * Real.exp 1 * 4 ^ M *
          Real.exp ((2 * M + 1) * ‖z‖) := by rw [hexp]; ring

/-- Decay on the strip: for `M ≥ deg P + 1`, `|Φ(z)| ≤ D/(1 + |z|)` when `|Im z| ≤ 1/2`. -/
theorem norm_sincLevelWitness_le_strip (P : ℂ[X]) {M : ℕ} (hM : P.natDegree + 1 ≤ M) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖sincLevelWitness P M z‖ ≤ 2 * polyMass P * 2 ^ P.natDegree * 36 ^ M / (1 + ‖z‖) := by
  set d := P.natDegree
  have hz0 := norm_nonneg z
  have hmass := polyMass_nonneg P
  have hP := norm_eval_le_polyMass P (z ^ 2)
  rw [norm_pow] at hP
  have hz1 : 0 < 1 + ‖z‖ := by positivity
  rw [le_div_iff₀ hz1, sincLevelWitness, norm_mul, norm_pow]
  by_cases h1 : 1 ≤ ‖z‖
  · have hzne : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have hs : ‖entireSinc z‖ ≤ 2 / ‖z‖ := by
      refine (norm_entireSinc_le_of_ne hzne).trans ?_
      gcongr
      have : Real.exp |z.im| ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hz
      have h2 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h3 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      linarith
    have hPz : ‖P.eval (z ^ 2)‖ ≤ polyMass P * 2 ^ d * ‖z‖ ^ (2 * d) := by
      have h2 : (1 + ‖z‖ ^ 2) ^ d ≤ (2 * ‖z‖ ^ 2) ^ d :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) _
      calc ‖P.eval (z ^ 2)‖ ≤ polyMass P * (1 + ‖z‖ ^ 2) ^ d := hP
        _ ≤ polyMass P * (2 * ‖z‖ ^ 2) ^ d := mul_le_mul_of_nonneg_left h2 hmass
        _ = polyMass P * 2 ^ d * ‖z‖ ^ (2 * d) := by rw [mul_pow, pow_mul]; ring
    have hs2 : ‖entireSinc z‖ ^ (2 * M) ≤ (2 / ‖z‖) ^ (2 * M) :=
      pow_le_pow_left₀ (norm_nonneg _) hs _
    obtain ⟨m, rfl⟩ : ∃ m, M = d + 1 + m := ⟨M - (d + 1), by omega⟩
    have hzpos : 0 < ‖z‖ := by linarith
    have hkey : ‖z‖ ^ (2 * d) * (2 / ‖z‖) ^ (2 * (d + 1 + m)) * (1 + ‖z‖) ≤
        2 * 4 ^ (d + 1 + m) := by
      have hzd : 0 < ‖z‖ ^ (2 * d) := by positivity
      have hzr : ‖z‖ ≤ ‖z‖ ^ (2 + 2 * m) := by
        calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
          _ ≤ ‖z‖ ^ (2 + 2 * m) := pow_le_pow_right₀ h1 (by omega)
      have h4 : (0 : ℝ) < 4 ^ (d + 1 + m) := by positivity
      have e : ‖z‖ ^ (2 * d) * (2 / ‖z‖) ^ (2 * (d + 1 + m)) =
          4 ^ (d + 1 + m) / ‖z‖ ^ (2 + 2 * m) := by
        rw [div_pow, show 2 * (d + 1 + m) = 2 * d + (2 + 2 * m) by ring, pow_add ‖z‖,
          show (2 : ℝ) ^ (2 * d + (2 + 2 * m)) = 4 ^ (d + 1 + m) by
            rw [show 2 * d + (2 + 2 * m) = 2 * (d + 1 + m) by ring, pow_mul]; norm_num]
        field_simp
      rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hzr h4.le]
    calc ‖P.eval (z ^ 2)‖ * ‖entireSinc z‖ ^ (2 * (d + 1 + m)) * (1 + ‖z‖)
        ≤ (polyMass P * 2 ^ d * ‖z‖ ^ (2 * d)) * (2 / ‖z‖) ^ (2 * (d + 1 + m)) * (1 + ‖z‖) := by
          gcongr
      _ = polyMass P * 2 ^ d *
            (‖z‖ ^ (2 * d) * (2 / ‖z‖) ^ (2 * (d + 1 + m)) * (1 + ‖z‖)) := by ring
      _ ≤ polyMass P * 2 ^ d * (2 * 4 ^ (d + 1 + m)) := by gcongr
      _ ≤ 2 * polyMass P * 2 ^ d * 36 ^ (d + 1 + m) := by
          have : (4 : ℝ) ^ (d + 1 + m) ≤ 36 ^ (d + 1 + m) :=
            pow_le_pow_left₀ (by norm_num) (by norm_num) _
          nlinarith [mul_nonneg hmass (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)]
  · push Not at h1
    have hs : ‖entireSinc z‖ ≤ 6 := by
      have := norm_entireSinc_le z
      have he : Real.exp ‖z‖ ≤ Real.exp 1 := Real.exp_le_exp.2 h1.le
      have := Real.exp_one_lt_d9
      linarith
    have hPz : ‖P.eval (z ^ 2)‖ ≤ polyMass P * 2 ^ d := by
      refine hP.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hmass)
      nlinarith
    have hs2 : ‖entireSinc z‖ ^ (2 * M) ≤ 36 ^ M := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg (entireSinc z)]) _
    calc ‖P.eval (z ^ 2)‖ * ‖entireSinc z‖ ^ (2 * M) * (1 + ‖z‖)
        ≤ (polyMass P * 2 ^ d) * 36 ^ M * 2 := by
          gcongr
          linarith
      _ = 2 * polyMass P * 2 ^ d * 36 ^ M := by ring

/-! ## The zero-side summand -/

/-- The zero-side summand `Φ(z) \overline{Φ(\bar z)}`. -/
def zeroSideTerm (Φ : ℂ → ℂ) (z : ℂ) : ℂ := Φ z * (starRingEnd ℂ) (Φ ((starRingEnd ℂ) z))

theorem zeroSideTerm_neg {Φ : ℂ → ℂ} (heven : ∀ z, Φ (-z) = Φ z) (z : ℂ) :
    zeroSideTerm Φ (-z) = zeroSideTerm Φ z := by
  rw [zeroSideTerm, zeroSideTerm, map_neg, heven, heven]

theorem zeroSideTerm_conj (Φ : ℂ → ℂ) (z : ℂ) :
    zeroSideTerm Φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (zeroSideTerm Φ z) := by
  rw [zeroSideTerm, zeroSideTerm, Complex.conj_conj, map_mul, Complex.conj_conj, mul_comm]

/-- Strip decay makes the zero side absolutely summable. -/
theorem summable_zeroSideTerm {Φ : ℂ → ℂ} {D : ℝ}
    (hdecay : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖)) :
    Summable fun q : XiZeroCopy => zeroSideTerm Φ (xiSpectralPoint q) := by
  refine (summable_inv_one_add_norm_xiHeatFrequency.mul_left (D ^ 2)).of_norm_bounded fun q => ?_
  set z := xiSpectralPoint q
  have hz := abs_im_xiSpectralPoint_le_half q
  have hzc : |((starRingEnd ℂ) z).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hz
  have h1 := hdecay z hz
  have h2 := hdecay _ hzc
  rw [Complex.norm_conj] at h2
  have hz1 : 0 < 1 + ‖z‖ := by positivity
  have hD : 0 ≤ D := by
    have := (norm_nonneg _).trans h1
    rwa [le_div_iff₀ hz1, zero_mul] at this
  have hw : ‖xiHeatFrequency q‖ = ‖z‖ ^ 2 := by rw [xiHeatFrequency, norm_pow]
  rw [zeroSideTerm, norm_mul, Complex.norm_conj, hw]
  calc ‖Φ z‖ * ‖Φ ((starRingEnd ℂ) z)‖ ≤ D / (1 + ‖z‖) * (D / (1 + ‖z‖)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = D ^ 2 / ((1 + ‖z‖) * (1 + ‖z‖)) := by rw [div_mul_div_comm, ← sq]
    _ ≤ D ^ 2 * (1 / (1 + ‖z‖ ^ 2)) := by
        rw [mul_one_div]
        gcongr
        nlinarith [norm_nonneg z]

theorem zeroSideTerm_sincLevelWitness (P : ℂ[X]) (M : ℕ) (z : ℂ) :
    zeroSideTerm (sincLevelWitness P M) z =
      heatHankelTermAt 0 P P (z ^ 2) * entireSinc z ^ (4 * M) := by
  simp only [zeroSideTerm, sincLevelWitness, heatHankelTermAt, map_mul, map_pow, entireSinc_conj,
    Complex.conj_conj, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  ring

/-- With `c = sinc(z₀)^{4M} K_Λ(u)²` and phase `t = c/|c|`, the summand at `z₀` is
`−4 (Im u)² |c|`. -/
theorem zeroSideTerm_sincLevelWitness_phase (Λ : ℝ) (M : ℕ) {u z₀ : ℂ} (hz₀ : z₀ ^ 2 = u)
    (hs : entireSinc z₀ ≠ 0) :
    let c := entireSinc z₀ ^ (4 * M) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2
    zeroSideTerm (sincLevelWitness (heatLevelPairTest Λ u (c / (‖c‖ : ℂ))) M) z₀ =
      -(((4 * u.im ^ 2 * ‖c‖ : ℝ)) : ℂ) := by
  intro c
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hs)
    (pow_ne_zero _ (eval_heatLevelRoots_ne_zero Λ u))
  have hnc : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc
  rw [zeroSideTerm_sincLevelWitness, hz₀, heatHankelTermAt_heatLevelPairTest, map_div₀,
    Complex.conj_ofReal, Complex.sub_conj]
  have hcc : c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc Complex.exp (-((0 : ℝ) : ℂ) * u) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2 *
          (((2 * u.im : ℝ) : ℂ) * I) ^ 2 * ((starRingEnd ℂ) c / (‖c‖ : ℂ)) *
          entireSinc z₀ ^ (4 * M)
      = (c * (starRingEnd ℂ) c) / (‖c‖ : ℂ) * (((2 * u.im : ℝ) : ℂ) * I) ^ 2 := by
        rw [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero]
        ring
    _ = -(((4 * u.im ^ 2 * ‖c‖ : ℝ)) : ℂ) := by
        rw [hcc]
        field_simp
        push_cast
        ring_nf
        rw [I_sq]
        ring

/-- Below the level, away from `u, ū`, the summand vanishes. -/
theorem zeroSideTerm_sincLevelWitness_eq_zero {Λ : ℝ} {u t z : ℂ} (M : ℕ)
    (hmem : z ^ 2 ∈ heatLevelRoots Λ u) :
    zeroSideTerm (sincLevelWitness (heatLevelPairTest Λ u t) M) z = 0 := by
  rw [zeroSideTerm_sincLevelWitness, heatHankelTermAt, heatLevelPairTest, eval_mul,
    eval_heatRootPoly_eq_zero hmem]
  simp

theorem norm_entireSinc_le_two_div {z : ℂ} (hz : |z.im| ≤ 1 / 2) (hz0 : z ≠ 0) :
    ‖entireSinc z‖ ≤ 2 / ‖z‖ := by
  refine (norm_entireSinc_le_of_ne hz0).trans ?_
  gcongr
  have : Real.exp |z.im| ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 hz
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have := Real.exp_one_lt_d9
    have h3 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

/-- The polynomial bound behind the tail: for `1 ≤ Λ ≤ W`,
`(C₀(1 + W))^{2k} (1 + W)² (4/W)^{2(k+2+m)} ≤ 8 (2C₀)^{2k} 16^{k+2+m} / (Λ^{2m} (1 + W))`. -/
theorem sinc_tail_numeric {W Λ C₀ : ℝ} {k m : ℕ} (hΛ : 1 ≤ Λ) (hW : Λ ≤ W) (hC₀ : 0 ≤ C₀) :
    (C₀ * (1 + W)) ^ (2 * k) * (1 + W) ^ 2 * (4 / W) ^ (2 * (k + 2 + m)) ≤
      8 * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) / (Λ ^ (2 * m) * (1 + W)) := by
  have hW1 : 1 ≤ W := hΛ.trans hW
  have hW0 : 0 < W := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have h1 : (C₀ * (1 + W)) ^ (2 * k) ≤ (2 * C₀) ^ (2 * k) * W ^ (2 * k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have h2 : (1 + W) ^ 3 ≤ 8 * W ^ 4 := by
    have : (1 + W) ^ 3 ≤ (2 * W) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    nlinarith [pow_le_pow_right₀ hW1 (show 3 ≤ 4 by norm_num)]
  have h3 : Λ ^ (2 * m) ≤ W ^ (2 * m) := pow_le_pow_left₀ hΛ0.le hW _
  have hkey : (C₀ * (1 + W)) ^ (2 * k) * (1 + W) ^ 3 * Λ ^ (2 * m) ≤
      8 * (2 * C₀) ^ (2 * k) * W ^ (2 * (k + 2 + m)) := by
    calc (C₀ * (1 + W)) ^ (2 * k) * (1 + W) ^ 3 * Λ ^ (2 * m)
        ≤ ((2 * C₀) ^ (2 * k) * W ^ (2 * k)) * (8 * W ^ 4) * W ^ (2 * m) := by
          gcongr
      _ = 8 * (2 * C₀) ^ (2 * k) * W ^ (2 * (k + 2 + m)) := by ring
  have h16 : (4 : ℝ) ^ (2 * (k + 2 + m)) = 16 ^ (k + 2 + m) := by
    rw [pow_mul]; norm_num
  have hWM : 0 < W ^ (2 * (k + 2 + m)) := by positivity
  rw [div_pow, h16, le_div_iff₀ (by positivity)]
  calc (C₀ * (1 + W)) ^ (2 * k) * (1 + W) ^ 2 * (16 ^ (k + 2 + m) / W ^ (2 * (k + 2 + m))) *
        (Λ ^ (2 * m) * (1 + W))
      = (C₀ * (1 + W)) ^ (2 * k) * (1 + W) ^ 3 * Λ ^ (2 * m) * 16 ^ (k + 2 + m) /
          W ^ (2 * (k + 2 + m)) := by ring
    _ ≤ 8 * (2 * C₀) ^ (2 * k) * W ^ (2 * (k + 2 + m)) * 16 ^ (k + 2 + m) /
          W ^ (2 * (k + 2 + m)) := by gcongr
    _ = 8 * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) := by field_simp

/-! ## Negativity of the sinc-damped witness -/

/-- **Tail bound.**  Above the level, the summand of the witness with `M = k + 2 + m`,
`k = #(roots of K_Λ)`, is at most `B₀/(1 + |w|)`,
`B₀ = 32 (1 + R)² |K_Λ(u)|² (2C₀)^{2k} 16^M / Λ^{2m}`. -/
theorem norm_zeroSideTerm_sincLevel_tail_le {Λ R d : ℝ} {u t : ℂ} (ht : ‖t‖ = 1) (hd : 0 < d)
    (hR : ‖u‖ ≤ R) (hsep : ∀ v ∈ heatLevelRoots Λ u, ‖v‖ < 2 * R + 2 → d ≤ ‖u - v‖)
    (hΛ1 : 1 ≤ Λ) (m : ℕ) {q : XiZeroCopy} (hlt : Λ < (xiHeatFrequency q).re) :
    ‖zeroSideTerm (sincLevelWitness (heatLevelPairTest Λ u t)
        ((heatLevelRoots Λ u).card + 2 + m)) (xiSpectralPoint q)‖ ≤
      32 * (1 + R) ^ 2 * ‖(heatRootPoly (heatLevelRoots Λ u)).eval u‖ ^ 2 *
        (2 * (2 + (2 * R + 3) / d)) ^ (2 * (heatLevelRoots Λ u).card) *
        16 ^ ((heatLevelRoots Λ u).card + 2 + m) / Λ ^ (2 * m) *
        (1 / (1 + ‖xiHeatFrequency q‖)) := by
  have htail := heatHankelTail_heatLevelPairTest_le (a := 0) ht hd hR hsep q
  obtain ⟨k, hk⟩ : ∃ k, k = (heatLevelRoots Λ u).card := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = heatLevelPairTest Λ u t := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (heatRootPoly (heatLevelRoots Λ u)).eval u := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = 2 + (2 * R + 3) / d := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = xiHeatFrequency q := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = xiSpectralPoint q := ⟨_, rfl⟩
  have hwz : w = z ^ 2 := by rw [hw, hz]; rfl
  rw [← hP, ← hK, ← hk, ← hC₀, ← hw, if_pos (hw ▸ hlt)] at htail
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at htail
  rw [← hk, ← hP, ← hK, ← hC₀, ← hz, ← hw]
  rw [← hw] at hlt
  have hR0 : 0 ≤ R := (norm_nonneg u).trans hR
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have hWΛ : Λ ≤ ‖w‖ := hlt.le.trans (Complex.re_le_norm _)
  have hnw : ‖w‖ = ‖z‖ ^ 2 := by rw [hwz, norm_pow]
  have hz1 : 1 ≤ ‖z‖ := by nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hstrip : |z.im| ≤ 1 / 2 := by rw [hz]; exact abs_im_xiSpectralPoint_le_half q
  have hsz := norm_entireSinc_le_two_div hstrip hz0
  have hsz4 : ‖entireSinc z‖ ^ (4 * (k + 2 + m)) ≤ (4 / ‖w‖) ^ (2 * (k + 2 + m)) := by
    calc ‖entireSinc z‖ ^ (4 * (k + 2 + m)) ≤ (2 / ‖z‖) ^ (4 * (k + 2 + m)) :=
          pow_le_pow_left₀ (norm_nonneg _) hsz _
      _ = (4 / ‖w‖) ^ (2 * (k + 2 + m)) := by
          rw [hnw, show 4 * (k + 2 + m) = 2 * (2 * (k + 2 + m)) by ring, pow_mul, div_pow]
          norm_num
  have hterm : ‖heatHankelTermAt 0 P P w‖ ≤ heatHankelTail 0 Λ P q / 2 := by
    rw [heatHankelTail, ← hw, if_pos hlt, heatHankelTermAt, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_exp]
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.zero_re, Real.exp_zero, one_mul]
    nlinarith [sq_nonneg (‖P.eval w‖ - ‖P.eval ((starRingEnd ℂ) w)‖)]
  have hnum := sinc_tail_numeric (k := k) (m := m) hΛ1 hWΛ hC₀0
  have hFq : zeroSideTerm (sincLevelWitness P (k + 2 + m)) z =
      heatHankelTermAt 0 P P w * entireSinc z ^ (4 * (k + 2 + m)) := by
    rw [hwz]; exact zeroSideTerm_sincLevelWitness P _ z
  rw [hFq, norm_mul, norm_pow]
  calc ‖heatHankelTermAt 0 P P w‖ * ‖entireSinc z‖ ^ (4 * (k + 2 + m))
      ≤ (8 * (1 + R) ^ 2 * ‖K‖ ^ 2 * ((C₀ * (1 + ‖w‖)) ^ (2 * k) * (1 + ‖w‖) ^ 2) / 2) *
          (4 / ‖w‖) ^ (2 * (k + 2 + m)) :=
        mul_le_mul (hterm.trans (div_le_div_of_nonneg_right htail (by norm_num))) hsz4
          (by positivity) (by positivity)
    _ = 4 * (1 + R) ^ 2 * ‖K‖ ^ 2 *
          ((C₀ * (1 + ‖w‖)) ^ (2 * k) * (1 + ‖w‖) ^ 2 * (4 / ‖w‖) ^ (2 * (k + 2 + m))) := by
        ring
    _ ≤ 4 * (1 + R) ^ 2 * ‖K‖ ^ 2 *
          (8 * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) / (Λ ^ (2 * m) * (1 + ‖w‖))) := by
        gcongr
    _ = 32 * (1 + R) ^ 2 * ‖K‖ ^ 2 * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) / Λ ^ (2 * m) *
          (1 / (1 + ‖w‖)) := by
        field_simp
        ring

/-- **Below the level.**  Each summand of real part `≤ Λ` is either the pair value `−4 (Im u)² |c|`
or `0` at a frequency other than `u`. -/
theorem zeroSideTerm_sincLevel_low (Λ : ℝ) (M : ℕ) {u z₀ : ℂ} (hz₀ : z₀ ^ 2 = u)
    (hs : entireSinc z₀ ≠ 0) {q : XiZeroCopy} (hle : (xiHeatFrequency q).re ≤ Λ) :
    let c := entireSinc z₀ ^ (4 * M) * ((heatRootPoly (heatLevelRoots Λ u)).eval u) ^ 2
    zeroSideTerm (sincLevelWitness (heatLevelPairTest Λ u (c / (‖c‖ : ℂ))) M)
        (xiSpectralPoint q) = -(((4 * u.im ^ 2 * ‖c‖ : ℝ)) : ℂ) ∨
      (zeroSideTerm (sincLevelWitness (heatLevelPairTest Λ u (c / (‖c‖ : ℂ))) M)
        (xiSpectralPoint q) = 0 ∧ xiHeatFrequency q ≠ u) := by
  intro c
  have hval := zeroSideTerm_sincLevelWitness_phase Λ M hz₀ hs
  have heven := sincLevelWitness_neg (heatLevelPairTest Λ u (c / (‖c‖ : ℂ))) M
  have hwz : xiHeatFrequency q = xiSpectralPoint q ^ 2 := rfl
  by_cases hwu : xiHeatFrequency q = u
  · left
    have hsq : xiSpectralPoint q ^ 2 = z₀ ^ 2 := by rw [← hwz, hz₀]; exact hwu
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · rw [h]; exact hval
    · rw [h, zeroSideTerm_neg heven]; exact hval
  by_cases hwū : xiHeatFrequency q = (starRingEnd ℂ) u
  · left
    have hsq : xiSpectralPoint q ^ 2 = ((starRingEnd ℂ) z₀) ^ 2 := by
      rw [← hwz, hwū, ← hz₀, map_pow]
    have hc : zeroSideTerm (sincLevelWitness (heatLevelPairTest Λ u (c / (‖c‖ : ℂ))) M)
        ((starRingEnd ℂ) z₀) = -(((4 * u.im ^ 2 * ‖c‖ : ℝ)) : ℂ) := by
      rw [zeroSideTerm_conj, hval, map_neg, Complex.conj_ofReal]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · rw [h]; exact hc
    · rw [h, zeroSideTerm_neg heven]; exact hc
  · right
    have hmem : xiSpectralPoint q ^ 2 ∈ heatLevelRoots Λ u :=
      mem_heatLevelRoots.2 ⟨mem_heatFrequenciesBelow.2 ⟨q, rfl, hle⟩, hwu, hwū⟩
    exact ⟨zeroSideTerm_sincLevelWitness_eq_zero M hmem, hwu⟩

/-- **The pair dominates the tail.**  With `σ > 0`, `Λσ² ≥ 8` and `(1/4)^m < ι/(A₀ + 1)`,
`A₀ = 8 (1 + R)² (2C₀)^{2k} S (16/σ⁴)^{k+2}`, the tail mass is below the pair mass. -/
theorem sinc_pair_dominates {R C₀ S σ Λ κ ι : ℝ} {k m : ℕ} (hσ : 0 < σ) (hΛσ : 8 / σ ^ 2 ≤ Λ)
    (hκ : 0 < κ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hS : 0 ≤ S)
    (hm : (1 / 4 : ℝ) ^ m <
      ι / (8 * (1 + R) ^ 2 * (2 * C₀) ^ (2 * k) * S * (16 / σ ^ 4) ^ (k + 2) + 1)) :
    32 * (1 + R) ^ 2 * κ * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) / Λ ^ (2 * m) * S <
      4 * ι * (σ ^ (4 * (k + 2 + m)) * κ) := by
  obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ = 8 * (1 + R) ^ 2 * (2 * C₀) ^ (2 * k) * S * (16 / σ ^ 4) ^ (k + 2) :=
    ⟨_, rfl⟩
  rw [← hA₀] at hm
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hΛ0 : 0 < Λ := lt_of_lt_of_le (by positivity) hΛσ
  have hρ : 16 / (σ ^ 4 * Λ ^ 2) ≤ 1 / 4 := by
    have h8 : 8 ≤ Λ * σ ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hΛσ
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hid : 32 * (1 + R) ^ 2 * κ * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) / Λ ^ (2 * m) * S =
      4 * κ * σ ^ (4 * (k + 2 + m)) * (A₀ * (16 / (σ ^ 4 * Λ ^ 2)) ^ m) := by
    have hσne : σ ≠ 0 := hσ.ne'
    have hΛne : Λ ≠ 0 := hΛ0.ne'
    have e1 : σ ^ (4 * (k + 2 + m)) = (σ ^ 4) ^ (k + 2) * (σ ^ 4) ^ m := by
      rw [← pow_add, ← pow_mul]
    have e2 : (16 / σ ^ 4) ^ (k + 2) * (σ ^ 4) ^ (k + 2) = 16 ^ (k + 2) := by
      rw [← mul_pow, div_mul_cancel₀ _ (pow_ne_zero 4 hσne)]
    have e3 : (16 / (σ ^ 4 * Λ ^ 2)) ^ m * (σ ^ 4) ^ m = (16 / Λ ^ 2) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc 32 * (1 + R) ^ 2 * κ * (2 * C₀) ^ (2 * k) * 16 ^ (k + 2 + m) / Λ ^ (2 * m) * S
        = 32 * (1 + R) ^ 2 * κ * (2 * C₀) ^ (2 * k) * S * 16 ^ (k + 2) * (16 / Λ ^ 2) ^ m := by
          rw [div_pow, pow_add (16 : ℝ) (k + 2) m, pow_mul Λ 2 m]
          ring
      _ = 32 * (1 + R) ^ 2 * κ * (2 * C₀) ^ (2 * k) * S *
            ((16 / σ ^ 4) ^ (k + 2) * (σ ^ 4) ^ (k + 2)) *
            ((16 / (σ ^ 4 * Λ ^ 2)) ^ m * (σ ^ 4) ^ m) := by rw [e2, e3]
      _ = 4 * κ * σ ^ (4 * (k + 2 + m)) * (A₀ * (16 / (σ ^ 4 * Λ ^ 2)) ^ m) := by
          rw [e1, hA₀]
          ring
  have hρm : (16 / (σ ^ 4 * Λ ^ 2)) ^ m ≤ (1 / 4) ^ m := pow_le_pow_left₀ (by positivity) hρ _
  have hA₀m : A₀ * (16 / (σ ^ 4 * Λ ^ 2)) ^ m < ι := by
    have h1 : A₀ * (16 / (σ ^ 4 * Λ ^ 2)) ^ m ≤ (A₀ + 1) * (1 / 4) ^ m := by
      have := mul_le_mul_of_nonneg_left hρm hA₀0
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) m]
    have h2 : (A₀ + 1) * (1 / 4) ^ m < ι := by
      rw [lt_div_iff₀ (by positivity)] at hm
      linarith
    linarith
  have hpos : 0 < 4 * κ * σ ^ (4 * (k + 2 + m)) := by positivity
  rw [hid]
  have := mul_lt_mul_of_pos_left hA₀m hpos
  nlinarith

/-- **The sinc-damped witness.**  For an upper off-line frequency `u` there are a polynomial `P` and
`M ≥ deg P + 1` such that `Φ(z) = P(z²) sinc(z)^{2M}` has
`Re Σ_q Φ(z_q) \overline{Φ(\bar z_q)} < 0`. -/
theorem exists_sincLevelWitness_zeroSide_re_neg {u : ℂ} (hu : u ∈ xiUpperFrequencies) :
    ∃ (P : ℂ[X]) (M : ℕ), P.natDegree + 1 ≤ M ∧
      (∑' q : XiZeroCopy, zeroSideTerm (sincLevelWitness P M) (xiSpectralPoint q)).re < 0 := by
  obtain ⟨q₀, hq₀, hupos⟩ := hu
  have hz₀ : xiSpectralPoint q₀ ^ 2 = u := hq₀
  have hz₀im : (xiSpectralPoint q₀).im ≠ 0 := by
    intro h
    have := xiHeatFrequency_im q₀
    rw [hq₀, h, mul_zero] at this
    linarith
  have hs := entireSinc_ne_zero_of_im_ne_zero hz₀im
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ‖entireSinc (xiSpectralPoint q₀)‖ := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; exact norm_pos_iff.2 hs
  obtain ⟨d, hd, hdsep⟩ := exists_pos_le_norm_sub {u} (heatFrequenciesBelow (2 * ‖u‖ + 2))
  obtain ⟨S₁, hS₁⟩ : ∃ S₁, S₁ = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) := ⟨_, rfl⟩
  have hS₁0 : 0 ≤ S₁ := by rw [hS₁]; exact tsum_nonneg fun _ => by positivity
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = max (max u.re 1) (8 / σ ^ 2) := ⟨_, rfl⟩
  have hΛu : u.re ≤ Λ := hΛdef ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hΛ1 : 1 ≤ Λ := hΛdef ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hΛσ : 8 / σ ^ 2 ≤ Λ := hΛdef ▸ le_max_right _ _
  obtain ⟨k, hk⟩ : ∃ k, k = (heatLevelRoots Λ u).card := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = 2 + (2 * ‖u‖ + 3) / d := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have hum : 0 < u.im ^ 2 := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (show 0 < u.im ^ 2 / (8 * (1 + ‖u‖) ^ 2 * (2 * C₀) ^ (2 * k) * S₁ * (16 / σ ^ 4) ^ (k + 2) + 1)
      by positivity)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  obtain ⟨M, hMdef⟩ : ∃ M, M = k + 2 + m := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = (heatRootPoly (heatLevelRoots Λ u)).eval u := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hKdef ▸ eval_heatLevelRoots_ne_zero Λ u
  obtain ⟨c, hcdef⟩ : ∃ c, c = entireSinc (xiSpectralPoint q₀) ^ (4 * M) * K ^ 2 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = heatLevelPairTest Λ u (c / (‖c‖ : ℂ)) := ⟨_, rfl⟩
  have hdeg : P.natDegree + 1 ≤ M := by
    have : P.natDegree ≤ (heatLevelRoots Λ u).card + 1 := hPdef ▸ natDegree_heatLevelPairTest_le Λ u _
    omega
  refine ⟨P, M, hdeg, ?_⟩
  have hc0 : c ≠ 0 := hcdef ▸ mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hK0)
  have ht : ‖c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 hc0)]
  have hcn : ‖c‖ = σ ^ (4 * M) * ‖K‖ ^ 2 := by rw [hcdef, hσ, norm_mul, norm_pow, norm_pow]
  obtain ⟨Ω, hΩ⟩ : ∃ Ω, Ω = 4 * u.im ^ 2 * ‖c‖ := ⟨_, rfl⟩
  have hΩ0 : 0 ≤ Ω := by rw [hΩ]; positivity
  have hsep : ∀ v ∈ heatLevelRoots Λ u, ‖v‖ < 2 * ‖u‖ + 2 → d ≤ ‖u - v‖ := by
    intro v hv hvR
    obtain ⟨hvB, hvu, hvu'⟩ := mem_heatLevelRoots.1 hv
    obtain ⟨q, rfl, -⟩ := mem_heatFrequenciesBelow.1 hvB
    exact hdsep u (Finset.mem_singleton_self u) _
      (mem_heatFrequenciesBelow.2 ⟨q, rfl, (Complex.re_le_norm _).trans hvR.le⟩) hvu hvu'
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 32 * (1 + ‖u‖) ^ 2 * ‖K‖ ^ 2 * (2 * C₀) ^ (2 * k) * 16 ^ M /
      Λ ^ (2 * m) := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity
  obtain ⟨F, hF⟩ : ∃ F : XiZeroCopy → ℂ,
      F = fun q => zeroSideTerm (sincLevelWitness P M) (xiSpectralPoint q) := ⟨_, rfl⟩
  have hsumF : Summable F :=
    hF ▸ summable_zeroSideTerm fun z hz => norm_sincLevelWitness_le_strip P hdeg hz
  obtain ⟨g, hg⟩ : ∃ g : XiZeroCopy → ℝ, g = fun q => (if q = q₀ then -Ω else 0) +
      (if Λ < (xiHeatFrequency q).re then B₀ * (1 / (1 + ‖xiHeatFrequency q‖)) else 0) :=
    ⟨_, rfl⟩
  have hle : ∀ q, (F q).re ≤ g q := by
    intro q
    rw [hF, hg]
    dsimp only
    by_cases hlt : Λ < (xiHeatFrequency q).re
    · have hne : q ≠ q₀ := fun h => by rw [h, hq₀] at hlt; linarith
      rw [if_neg hne, if_pos hlt, zero_add]
      refine (Complex.re_le_norm _).trans ?_
      have h := norm_zeroSideTerm_sincLevel_tail_le ht hd le_rfl hsep hΛ1 m hlt
      rw [← hk, ← hKdef, ← hC₀, ← hPdef] at h
      rw [hMdef, hB₀, hMdef]
      exact h
    · rw [if_neg hlt, add_zero]
      have hlow := zeroSideTerm_sincLevel_low Λ M hz₀ hs (not_lt.1 hlt)
      dsimp only at hlow
      rw [← hKdef, ← hcdef, ← hPdef] at hlow
      rcases hlow with h | ⟨h, hwu⟩
      · rw [h, ← hΩ]
        simp only [Complex.neg_re, Complex.ofReal_re]
        split_ifs <;> linarith
      · have hne : q ≠ q₀ := fun h' => hwu (by rw [h', hq₀])
        rw [h, if_neg hne, Complex.zero_re]
  have hsum1 : Summable fun q : XiZeroCopy => if q = q₀ then -Ω else 0 :=
    (hasSum_ite_eq q₀ (-Ω)).summable
  have hsum2 : Summable fun q : XiZeroCopy =>
      if Λ < (xiHeatFrequency q).re then B₀ * (1 / (1 + ‖xiHeatFrequency q‖)) else 0 :=
    (summable_inv_one_add_norm_xiHeatFrequency.mul_left B₀).of_nonneg_of_le
      (fun q => by split_ifs <;> positivity)
      fun q => by split_ifs; exacts [le_rfl, by positivity]
  have hsumg : Summable g := hg ▸ hsum1.add hsum2
  have hsumRe : Summable fun q => (F q).re := Complex.reCLM.summable hsumF
  have htail2 : ∑' q : XiZeroCopy,
      (if Λ < (xiHeatFrequency q).re then B₀ * (1 / (1 + ‖xiHeatFrequency q‖)) else 0) ≤
        B₀ * S₁ := by
    rw [hS₁, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => by split_ifs; exacts [le_rfl, by positivity]) hsum2
      (summable_inv_one_add_norm_xiHeatFrequency.mul_left B₀)
  have htsum_g : ∑' q, g q ≤ -Ω + B₀ * S₁ := by
    rw [hg, Summable.tsum_add hsum1 hsum2, tsum_ite_eq]
    linarith
  have hB₀S : B₀ * S₁ < Ω := by
    have hκ : 0 < ‖K‖ ^ 2 := by have := norm_pos_iff.2 hK0; positivity
    have := sinc_pair_dominates (κ := ‖K‖ ^ 2) hσ0 hΛσ hκ (norm_nonneg u) hC₀0 hS₁0 hm
    rw [hB₀, hΩ, hcn, hMdef]
    linarith
  have hre : (∑' q, F q).re < 0 := by
    rw [Complex.re_tsum hsumF]
    calc ∑' q, (F q).re ≤ ∑' q, g q := Summable.tsum_le_tsum hle hsumRe hsumg
      _ ≤ -Ω + B₀ * S₁ := htsum_g
      _ < 0 := by linarith
  rw [hF] at hre
  exact hre

/-! ## The window has the optimal order `1/N` -/

/-- **An even exponential-type zero-side witness exists unless RH holds.** -/
theorem exists_exponentialType_zeroSide_witness_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ (Φ : ℂ → ℂ) (C B D : ℝ), Differentiable ℂ Φ ∧ (∀ z, Φ (-z) = Φ z) ∧ 0 ≤ B ∧
      (∀ z, ‖Φ z‖ ≤ C * Real.exp (B * ‖z‖)) ∧
      (∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Φ z‖ ≤ D / (1 + ‖z‖)) ∧
      (∑' q : XiZeroCopy, Φ (xiSpectralPoint q) *
        (starRingEnd ℂ) (Φ ((starRingEnd ℂ) (xiSpectralPoint q)))).re < 0 := by
  obtain ⟨u, hu⟩ := exists_mem_xiUpperFrequencies_of_not_riemannHypothesis hRH
  obtain ⟨P, M, hM, hneg⟩ := exists_sincLevelWitness_zeroSide_re_neg hu
  exact ⟨sincLevelWitness P M, _, 2 * M + 1, _, differentiable_sincLevelWitness P M,
    sincLevelWitness_neg P M, by positivity, norm_sincLevelWitness_le_exp P M,
    fun z hz => norm_sincLevelWitness_le_strip P hM hz, hneg⟩

/-- **The window ceiling at the scale `1/N`.**  If RH fails, there is `K > 0` such that for all
large `n` some leading heat determinant `Δ_k(K/n)` with `k ≤ n + 1` is `≤ 0`. -/
theorem exists_pos_eventually_exists_heatMomentDet_nonpos_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∃ k ≤ n + 1, (leadingMatrix (heatMomentArray (K / n)) k).det ≤ 0 := by
  obtain ⟨Φ, C, B, D, hΦ, heven, hB, hgrowth, hdecay, hneg⟩ :=
    exists_exponentialType_zeroSide_witness_of_not_riemannHypothesis hRH
  refine ⟨(B * Real.exp 1 + 1) ^ 2 / 4 + 1, by positivity, ?_⟩
  exact eventually_exists_heatMomentDet_nonpos_of_exponentialType hΦ heven hB hgrowth hdecay hneg
    (by linarith)

/-- **RH as the unboundedness of the window constant.**  RH holds iff for every `K > 0`, for all
large `n`, every leading heat determinant `Δ_k(K/n)` with `k ≤ n + 1` is positive. -/
theorem riemannHypothesis_iff_forall_eventually_heatMomentDet_pos_scaled :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop,
      ∀ k ≤ n + 1, 0 < (leadingMatrix (heatMomentArray (K / n)) k).det := by
  constructor
  · intro hRH K hK
    filter_upwards [eventually_gt_atTop 0] with n hn k _
    exact (riemannHypothesis_iff_heatMomentDet_pos
      (div_pos hK (by exact_mod_cast hn))).1 hRH k
  · intro h
    by_contra hRH
    obtain ⟨K, hK, hev⟩ := exists_pos_eventually_exists_heatMomentDet_nonpos_of_not_riemannHypothesis hRH
    obtain ⟨n, hn1, k, hk, hdet⟩ := ((h K hK).and hev).exists
    exact (hn1 k hk).not_ge hdet

/-- **The window growth gap.**  For every `f : ℕ → ℝ` with `f(n) → ∞`, RH holds iff for all large
`n` every leading heat determinant `Δ_k(a)` with `k ≤ n + 1` and `0 < a ≤ f(n)/n` is positive.  An
unconditional growing window is RH itself: below RH the window is `O(1/N)`, with no intermediate
growth. -/
theorem riemannHypothesis_iff_eventually_growing_window {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, ∀ a : ℝ, 0 < a → a ≤ f n / n →
      ∀ k ≤ n + 1, 0 < (leadingMatrix (heatMomentArray a) k).det := by
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun n a ha _ k _ =>
      (riemannHypothesis_iff_heatMomentDet_pos ha).1 hRH k
  · intro h
    by_contra hRH
    obtain ⟨K, hK, hev⟩ :=
      exists_pos_eventually_exists_heatMomentDet_nonpos_of_not_riemannHypothesis hRH
    obtain ⟨n, ⟨hn1, hn2⟩, hn0, hfn⟩ :=
      ((h.and hev).and ((eventually_gt_atTop 0).and (hf.eventually_ge_atTop K))).exists
    obtain ⟨k, hk, hdet⟩ := hn2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hle : K / n ≤ f n / n := div_le_div_of_nonneg_right hfn hn'.le
    exact (hn1 (K / n) (div_pos hK hn') hle k hk).not_ge hdet

end

end RHTower
