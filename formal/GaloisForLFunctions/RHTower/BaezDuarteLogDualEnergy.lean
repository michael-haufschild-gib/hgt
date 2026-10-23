import GaloisForLFunctions.RHTower.BaezDuarteLogDualDefect

/-!
# The energy of polynomially log-weighted zero duals

Let `Re ρ = ½`, `Im ρ ≠ 0`, `p` a real polynomial, `L = log Y` and
`A_k = p(log k / L)·Re(k^{−ρ}) ψ(k/Y)`.  Then (`exists_bdDualEnergy_polyLogDual_le`)

  `Σ_k k(k+1)(A_k − A_{k+1})² ≤ (|ρ|²/2) Σ_{k ≤ 3Y} p(log k/L)²/k + K₀`   for all `Y ≥ e`.

**Proof.**  With `h_k = p(log k/L)` the increment is `h_k(Re a_k − Re a_{k+1}) + δ_k`, where
`δ_k = (h_k − h_{k+1})Re a_{k+1}` and `|h_k − h_{k+1}| ≤ Λ/(Lk)` on `k ≤ 3Y` (`p` is Lipschitz on
`[0, 4]`).  The first part is handled as for `p = 1` (`mul_add_mul_add_le_of_abs_le`), with main
term `h_k² w_k²(1 + 1/k)(|ρ|²/k + Re(ρ²k^{−2ρ}))/2`.  The `δ_k` terms cost `O(Σ_{k ≤ 3Y} 1/(Lk)) =
O(1)`.  The oscillatory part `Re(ρ²k^{−2ρ})` has bounded partial sums, and the weights
`h_k²w_k²(1 + 1/k)/2` have bounded variation, so Abel summation bounds it
(`abs_sum_mul_le_of_partialSum_le`).
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Abel summation with weights of bounded variation -/

private theorem sum_mul_eq_abel (a v : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, a k * v k =
      (∑ k ∈ Finset.Icc 1 K, a k) * v (K + 1) +
        ∑ k ∈ Finset.Icc 1 K, (∑ i ∈ Finset.Icc 1 k, a i) * (v k - v (k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega) (fun k => a k * v k), ih,
      Finset.sum_Icc_succ_top (by omega)
        (fun k => (∑ i ∈ Finset.Icc 1 k, a i) * (v k - v (k + 1))),
      Finset.sum_Icc_succ_top (by omega) a]
    ring

theorem abs_sum_mul_le_of_partialSum_le {a v : ℕ → ℝ} {B : ℝ} (K : ℕ)
    (hB : ∀ j, |∑ k ∈ Finset.Icc 1 j, a k| ≤ B) :
    |∑ k ∈ Finset.Icc 1 K, a k * v k| ≤
      B * (|v (K + 1)| + ∑ k ∈ Finset.Icc 1 K, |v k - v (k + 1)|) := by
  rw [sum_mul_eq_abel]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine (abs_add_le _ _).trans ?_
  rw [mul_add, abs_mul]
  refine add_le_add (mul_le_mul_of_nonneg_right (hB K) (abs_nonneg _)) ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hB k) (abs_nonneg _)

/-! ## The per-term inequality -/

/-- `k(k+1)(x + e + δ)²` with `|x| ≤ Ps/k`, `|e| ≤ Qs/k² + sHd`, `|δ| ≤ μs/k`, `ks² = 1`. -/
theorem mul_sq_add_add_le {kk s P Q μ H d x e δ : ℝ} (hk : 1 ≤ kk) (hs0 : 0 ≤ s)
    (hs : kk * s ^ 2 = 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hμ : 0 ≤ μ) (hH : 0 ≤ H) (hd : 0 ≤ d)
    (hx : |x| ≤ P * s / kk) (he : |e| ≤ Q * s / kk ^ 2 + s * (H * d))
    (hδ : |δ| ≤ μ * s / kk) :
    kk * (kk + 1) * (x + e + δ) ^ 2 ≤ kk * (kk + 1) * (x * x) +
      2 * (P * Q + P * Q + Q * Q) / kk ^ 2 + 2 * (P + P + Q + Q) * (H * d) +
        (kk + 1) * (H * d) ^ 2 + (4 * μ * (P + Q) + 2 * μ ^ 2) / kk + 4 * μ * (H * d) := by
  have hk0 : 0 < kk := by linarith
  have hHd : 0 ≤ H * d := mul_nonneg hH hd
  have h1 := mul_add_mul_add_le_of_abs_le hk hs0 hs hP hQ hP hQ hHd hx he hx he
  have hX : |x + e| ≤ (P + Q) * s / kk + s * (H * d) := by
    have hkk : Q * s / kk ^ 2 ≤ Q * s / kk := by
      exact div_le_div_of_nonneg_left (by positivity) hk0 (by nlinarith)
    calc |x + e| ≤ |x| + |e| := abs_add_le _ _
      _ ≤ P * s / kk + (Q * s / kk ^ 2 + s * (H * d)) := add_le_add hx he
      _ ≤ P * s / kk + (Q * s / kk + s * (H * d)) := by linarith
      _ = (P + Q) * s / kk + s * (H * d) := by ring
  have hs2 : s ^ 2 = 1 / kk := by field_simp; linarith
  have hk2 : (kk + 1) / kk ≤ 2 := by rw [div_le_iff₀ hk0]; linarith
  have hcross : kk * (kk + 1) * (2 * (x + e) * δ) ≤
      4 * μ * (P + Q) / kk + 4 * μ * (H * d) := by
    have hprod : |2 * (x + e) * δ| ≤ 2 * ((P + Q) * s / kk + s * (H * d)) * (μ * s / kk) := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hX (by norm_num)) hδ (abs_nonneg _)
        (by positivity)
    have hw : 0 ≤ kk * (kk + 1) := by positivity
    have := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hprod) hw
    have e1 : kk * (kk + 1) * (2 * ((P + Q) * s / kk + s * (H * d)) * (μ * s / kk)) =
        2 * μ * (P + Q) * ((kk + 1) / kk) / kk + 2 * μ * (H * d) * ((kk + 1) / kk) := by
      have : kk * (kk + 1) * (2 * ((P + Q) * s / kk + s * (H * d)) * (μ * s / kk)) =
          2 * μ * (P + Q) * (kk + 1) * s ^ 2 / kk + 2 * μ * (H * d) * (kk + 1) * s ^ 2 := by
        field_simp
      rw [this, hs2]
      field_simp
    have e2 : 2 * μ * (P + Q) * ((kk + 1) / kk) / kk ≤ 4 * μ * (P + Q) / kk := by
      rw [div_le_div_iff_of_pos_right hk0]
      nlinarith [mul_nonneg hμ (add_nonneg hP hQ)]
    have e3 : 2 * μ * (H * d) * ((kk + 1) / kk) ≤ 4 * μ * (H * d) := by
      nlinarith [mul_nonneg hμ hHd]
    linarith
  have hδ2 : kk * (kk + 1) * δ ^ 2 ≤ 2 * μ ^ 2 / kk := by
    have hsq : δ ^ 2 ≤ (μ * s / kk) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
    have hw : 0 ≤ kk * (kk + 1) := by positivity
    calc kk * (kk + 1) * δ ^ 2 ≤ kk * (kk + 1) * (μ * s / kk) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hw
      _ = μ ^ 2 * ((kk + 1) / kk) / kk := by
          rw [div_pow, mul_pow, hs2]; field_simp
      _ ≤ 2 * μ ^ 2 / kk := by
          rw [div_le_div_iff_of_pos_right hk0]
          nlinarith [sq_nonneg μ]
  have hsplit : kk * (kk + 1) * (x + e + δ) ^ 2 = kk * (kk + 1) * ((x + e) * (x + e)) +
      kk * (kk + 1) * (2 * (x + e) * δ) + kk * (kk + 1) * δ ^ 2 := by ring
  have e4 : (4 * μ * (P + Q) + 2 * μ ^ 2) / kk = 4 * μ * (P + Q) / kk + 2 * μ ^ 2 / kk := by ring
  linarith

theorem sum_Icc_inv_le_one_add_log (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ 1 + Real.log M := by
  have hH : ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) = (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [hH]
  exact harmonic_le_one_add_log M

theorem log_natSucc_sub_log_le_inv {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / k by positivity)
  have e : ((k + 1 : ℕ) : ℝ) / k - 1 = 1 / k := by push_cast; field_simp; ring
  linarith

/-! ## The per-term bound -/

theorem re_conj_mul_cpow_eq {ρ : ℂ} (hre : ρ.re = 1 / 2) (k : ℕ) :
    (ρ * conj ρ * (k : ℂ) ^ (-(ρ + conj ρ))).re = ‖ρ‖ ^ 2 * (1 / (k : ℝ)) := by
  have h1 : ρ + conj ρ = 1 := by
    rw [Complex.add_conj, hre]; push_cast; ring
  rw [h1, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.cpow_neg_one]
  rw [show ((‖ρ‖ ^ 2 : ℝ) : ℂ) * (k : ℂ)⁻¹ = ((‖ρ‖ ^ 2 * (1 / (k : ℝ)) : ℝ) : ℂ) by
    push_cast; ring, Complex.ofReal_re]

/-- `k(k+1)(Re v)²` for `v = ρk^{−ρ}/k`. -/
theorem mul_re_sq_eq {ρ : ℂ} (hre : ρ.re = 1 / 2) {k : ℕ} (hk1 : 1 ≤ k) (c : ℝ) :
    (k : ℝ) * ((k : ℝ) + 1) * (c * (ρ * (k : ℂ) ^ (-ρ) / k).re *
      (c * (ρ * (k : ℂ) ^ (-ρ) / k).re)) =
      c ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re +
        ‖ρ‖ ^ 2 / 2 * (c ^ 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ))) := by
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  set z : ℂ := (k : ℂ) ^ (-ρ) with hzdef
  set v : ℂ := ρ * z / k with hvdef
  have hzz : z * z = (k : ℂ) ^ (-(ρ + ρ)) := by
    rw [hzdef, ← Complex.cpow_add _ _ hkne, neg_add]
  have hzc : z * conj z = (k : ℂ) ^ (-(ρ + conj ρ)) := by
    rw [hzdef, ← natCast_cpow_conj, ← Complex.cpow_add _ _ hkne, map_neg, neg_add]
  have hk2 : ((k : ℂ) ^ 2) = (((k : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have hvv : (v * v).re = (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re / (k : ℝ) ^ 2 := by
    rw [show v * v = ρ * ρ * (z * z) / (k : ℂ) ^ 2 by rw [hvdef]; ring, hzz, hk2,
      Complex.div_ofReal_re]
  have hvc : (v * conj v).re = (ρ * conj ρ * (k : ℂ) ^ (-(ρ + conj ρ))).re / (k : ℝ) ^ 2 := by
    have : conj v = conj ρ * conj z / k := by
      rw [hvdef, map_div₀, map_mul, Complex.conj_natCast]
    rw [show v * conj v = ρ * conj ρ * (z * conj z) / (k : ℂ) ^ 2 by rw [this, hvdef]; ring,
      hzc, hk2, Complex.div_ofReal_re]
  rw [show c * v.re * (c * v.re) = c ^ 2 * (v.re * v.re) by ring, re_mul_re_eq, hvv, hvc,
    re_conj_mul_cpow_eq hre]
  field_simp

/-- **The per-term bound** for `A_k = h_k Re(a_k)`, `a_k = k^{−ρ}ψ(k/Y)`. -/
theorem polyLogDual_term_le {ν : ℝ → ℝ} (νpos : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε) {ρ : ℂ} (hre : ρ.re = 1 / 2)
    {Y : ℝ} (hY1 : 1 ≤ Y) {Lψ : ℝ} {h : ℕ → ℝ} {H μ : ℝ} (hH0 : 0 ≤ H) (hμ0 : 0 ≤ μ) {k : ℕ}
    (hk1 : 1 ≤ k) (hk3 : (k : ℝ) ≤ 3 * Y)
    (hanti : Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) ≤ Smooth1 ν ε ((k : ℝ) / Y))
    (hwlip : Smooth1 ν ε ((k : ℝ) / Y) - Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) ≤ Lψ / Y)
    (hhk : |h k| ≤ H) (hhLip : |h k - h (k + 1)| ≤ μ / k) :
    (k : ℝ) * ((k : ℝ) + 1) *
        ((h k * (zeroSmoothDual ν ε ρ Y k).re - h (k + 1) * (zeroSmoothDual ν ε ρ Y (k + 1)).re) *
        (h k * (zeroSmoothDual ν ε ρ Y k).re - h (k + 1) * (zeroSmoothDual ν ε ρ Y (k + 1)).re)) ≤
      h k ^ 2 * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) *
          (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re) +
        ‖ρ‖ ^ 2 / 2 * (h k ^ 2 * Smooth1 ν ε ((k : ℝ) / Y) ^ 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ))) +
        2 * (H * ‖ρ‖ * (H * (‖ρ‖ * ‖ρ + 1‖)) + H * ‖ρ‖ * (H * (‖ρ‖ * ‖ρ + 1‖)) +
          H * (‖ρ‖ * ‖ρ + 1‖) * (H * (‖ρ‖ * ‖ρ + 1‖))) / (k : ℝ) ^ 2 +
        (2 * (H * ‖ρ‖ + H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖) + H * (‖ρ‖ * ‖ρ + 1‖)) * H +
          4 * H ^ 2 * Lψ + 4 * μ * H) *
          (Smooth1 ν ε ((k : ℝ) / Y) - Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y)) +
        (4 * μ * (H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖)) + 2 * μ ^ 2) / k := by
  have hY0 : 0 < Y := by linarith
  have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkk0 : (0 : ℝ) < k := by linarith
  set w : ℝ := Smooth1 ν ε ((k : ℝ) / Y) with hw
  set w' : ℝ := Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) with hw'
  have hw0 : 0 ≤ w := Smooth1Nonneg νpos (div_pos hkk0 hY0) hε0
  have hw1 : w ≤ 1 := Smooth1LeOne νpos mass_one hε0 (div_pos hkk0 hY0)
  have hw'0 : 0 ≤ w' := Smooth1Nonneg νpos (div_pos (by positivity) hY0) hε0
  have hw'1 : w' ≤ 1 := Smooth1LeOne νpos mass_one hε0 (div_pos (by positivity) hY0)
  obtain ⟨e, he1, he2⟩ := exists_re_zeroSmoothDual_sub_succ_eq ν ε hre Y hk1 hw0 hw1 hanti
  set s : ℝ := (Real.sqrt k)⁻¹ with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs : (k : ℝ) * s ^ 2 = 1 := by
    rw [hsdef, inv_pow, Real.sq_sqrt hkk0.le]; field_simp
  set v : ℂ := ρ * (k : ℂ) ^ (-ρ) / k with hvdef
  have hzn : ‖(k : ℂ) ^ (-ρ)‖ = s := norm_natCast_cpow_neg_of_re hre hk1
  set d : ℝ := w - w' with hddef
  have hd0 : 0 ≤ d := sub_nonneg.mpr hanti
  set P : ℝ := H * ‖ρ‖ with hPdef
  set Q : ℝ := H * (‖ρ‖ * ‖ρ + 1‖) with hQdef
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hx : |h k * (w * v.re)| ≤ P * s / k := by
    rw [abs_mul]
    have hwv : |w * v.re| ≤ ‖ρ‖ * s / k := by
      rw [abs_mul, abs_of_nonneg hw0]
      calc w * |v.re| ≤ 1 * ‖v‖ :=
            mul_le_mul hw1 (Complex.abs_re_le_norm v) (abs_nonneg _) zero_le_one
        _ = ‖ρ‖ * s / k := by
            rw [one_mul, hvdef, norm_div, norm_mul, hzn, Complex.norm_natCast]
    calc |h k| * |w * v.re| ≤ H * (‖ρ‖ * s / k) := mul_le_mul hhk hwv (abs_nonneg _) hH0
      _ = P * s / k := by rw [hPdef]; ring
  have he : |h k * e| ≤ Q * s / (k : ℝ) ^ 2 + s * (H * d) := by
    rw [abs_mul]
    calc |h k| * |e| ≤ H * (‖ρ‖ * ‖ρ + 1‖ * s / (k : ℝ) ^ 2 + s * d) :=
          mul_le_mul hhk he2 (abs_nonneg _) hH0
      _ = Q * s / (k : ℝ) ^ 2 + s * (H * d) := by rw [hQdef]; ring
  have hre1 : |(zeroSmoothDual ν ε ρ Y (k + 1)).re| ≤ s := by
    rw [re_zeroSmoothDual ν ε ρ Y (by omega), abs_mul, ← hw', abs_of_nonneg hw'0]
    have hn1 : ‖((k + 1 : ℕ) : ℂ) ^ (-ρ)‖ ≤ s := by
      rw [norm_natCast_cpow_neg_of_re hre (by omega), hsdef]
      exact inv_anti₀ (Real.sqrt_pos.mpr hkk0) (Real.sqrt_le_sqrt (by push_cast; linarith))
    calc |(((k + 1 : ℕ) : ℂ) ^ (-ρ)).re| * w' ≤ s * 1 :=
          mul_le_mul ((Complex.abs_re_le_norm _).trans hn1) hw'1 hw'0 hs0
      _ = s := mul_one _
  have hδ : |(h k - h (k + 1)) * (zeroSmoothDual ν ε ρ Y (k + 1)).re| ≤ μ * s / k := by
    rw [abs_mul]
    calc |h k - h (k + 1)| * |(zeroSmoothDual ν ε ρ Y (k + 1)).re| ≤ (μ / k) * s :=
          mul_le_mul hhLip hre1 (abs_nonneg _) (by positivity)
      _ = μ * s / k := by ring
  have hkey := mul_sq_add_add_le hkk hs0 hs hP0 hQ0 hμ0 hH0 hd0 hx he hδ
  have hinc : h k * (zeroSmoothDual ν ε ρ Y k).re - h (k + 1) * (zeroSmoothDual ν ε ρ Y (k + 1)).re =
      h k * (w * v.re) + h k * e + (h k - h (k + 1)) * (zeroSmoothDual ν ε ρ Y (k + 1)).re := by
    have : (zeroSmoothDual ν ε ρ Y k).re = w * v.re + e + (zeroSmoothDual ν ε ρ Y (k + 1)).re := by
      linarith only [he1]
    rw [this]; ring
  have hxx := mul_re_sq_eq hre hk1 (h k * w)
  rw [show h k * w * (ρ * (k : ℂ) ^ (-ρ) / k).re * (h k * w * (ρ * (k : ℂ) ^ (-ρ) / k).re) =
    h k * (w * v.re) * (h k * (w * v.re)) by rw [hvdef]; ring] at hxx
  have hd2 : ((k : ℝ) + 1) * (H * d) ^ 2 ≤ 4 * H ^ 2 * Lψ * d := by
    have hkd : ((k : ℝ) + 1) * d ≤ 4 * Lψ := by
      have hLψ0 : 0 ≤ Lψ := by
        have : 0 ≤ Lψ / Y := hd0.trans hwlip
        exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
      calc ((k : ℝ) + 1) * d ≤ (4 * Y) * (Lψ / Y) :=
            mul_le_mul (by linarith only [hk3, hY1]) hwlip hd0 (by positivity)
        _ = 4 * Lψ := by field_simp
    calc ((k : ℝ) + 1) * (H * d) ^ 2 = H ^ 2 * ((((k : ℝ) + 1) * d) * d) := by ring
      _ ≤ H ^ 2 * ((4 * Lψ) * d) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkd hd0) (sq_nonneg H)
      _ = 4 * H ^ 2 * Lψ * d := by ring
  rw [hinc, ← sq]
  have e1 : (h k * w) ^ 2 = h k ^ 2 * w ^ 2 := by ring
  rw [e1] at hxx
  have e2 : (2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H) * d =
      2 * (P + P + Q + Q) * (H * d) + 4 * H ^ 2 * Lψ * d + 4 * μ * (H * d) := by ring
  have e3 : h k ^ 2 * (w ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re) =
      h k ^ 2 * w ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re := by ring
  linarith only [hkey, hxx, hd2, e2, e3]

/-! ## The oscillatory sum -/

theorem abs_sum_sq_mul_osc_le {ρ : ℂ} {B₀ : ℝ}
    (hB₀ : ∀ j : ℕ, ‖∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-(ρ + ρ))‖ ≤ B₀)
    {h u : ℕ → ℝ} {H μ : ℝ} {M : ℕ} (hH0 : 0 ≤ H) (hμ0 : 0 ≤ μ) (hu0 : ∀ k, 1 ≤ k → 0 ≤ u k)
    (hu1 : ∀ k, 1 ≤ k → u k ≤ 1) (huanti : ∀ k, 1 ≤ k → u (k + 1) ≤ u k) (huzero : ∀ k, M < k → u k = 0)
    (hhH : ∀ k, 1 ≤ k → k ≤ M + 1 → |h k| ≤ H)
    (hhLip : ∀ k, 1 ≤ k → k ≤ M → |h k - h (k + 1)| ≤ μ / k) (K : ℕ) :
    |∑ k ∈ Finset.Icc 1 K, h k ^ 2 * u k * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re| ≤
      ‖ρ‖ ^ 2 * B₀ * (2 * H ^ 2 + 2 * H * μ * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)) := by
  set v : ℕ → ℝ := fun k => h k ^ 2 * u k with hv
  set a : ℕ → ℝ := fun k => (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re with ha
  have hpart : ∀ j, |∑ k ∈ Finset.Icc 1 j, a k| ≤ ‖ρ‖ ^ 2 * B₀ := by
    intro j
    have : ∑ k ∈ Finset.Icc 1 j, a k = (ρ * ρ * ∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-(ρ + ρ))).re := by
      rw [Finset.mul_sum, Complex.re_sum]
    rw [this]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, ← sq]
    exact mul_le_mul_of_nonneg_left (hB₀ j) (sq_nonneg _)
  have habel := abs_sum_mul_le_of_partialSum_le (a := a) (v := v) K hpart
  have hsum_eq : ∑ k ∈ Finset.Icc 1 K, h k ^ 2 * u k * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re =
      ∑ k ∈ Finset.Icc 1 K, a k * v k := Finset.sum_congr rfl fun k _ => by simp only [hv, ha]; ring
  rw [hsum_eq]
  have hB0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  refine habel.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hB0))
  have hvK : |v (K + 1)| ≤ H ^ 2 := by
    simp only [hv]
    rw [abs_mul, abs_of_nonneg (hu0 _ (by omega)), abs_pow]
    by_cases hK : K + 1 ≤ M + 1
    · have h1 := hhH (K + 1) (by omega) hK
      calc |h (K + 1)| ^ 2 * u (K + 1) ≤ H ^ 2 * 1 :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2) (hu1 _ (by omega)) (hu0 _ (by omega))
              (sq_nonneg H)
        _ = H ^ 2 := mul_one _
    · rw [huzero (K + 1) (by omega), mul_zero]; positivity
  have hTV : ∀ k ∈ Finset.Icc 1 K, |v k - v (k + 1)| ≤
      H ^ 2 * (u k - u (k + 1)) + (if k ≤ M then 2 * H * μ * (1 / (k : ℝ)) else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    by_cases hkM : k ≤ M
    · rw [if_pos hkM]
      have hhk := hhH k hk1 (by omega)
      have hhk1 := hhH (k + 1) (by omega) (by omega)
      have hdiff : v k - v (k + 1) = h k ^ 2 * (u k - u (k + 1)) +
          u (k + 1) * ((h k - h (k + 1)) * (h k + h (k + 1))) := by simp only [hv]; ring
      rw [hdiff]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (huanti k hk1)), abs_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hhk 2)
          (sub_nonneg.mpr (huanti k hk1))
      · rw [abs_mul, abs_mul, abs_of_nonneg (hu0 _ (by omega))]
        have hsum : |h k + h (k + 1)| ≤ 2 * H := by
          have := abs_add_le (h k) (h (k + 1)); linarith
        calc u (k + 1) * (|h k - h (k + 1)| * |h k + h (k + 1)|) ≤ 1 * ((μ / k) * (2 * H)) :=
              mul_le_mul (hu1 _ (by omega)) (mul_le_mul (hhLip k hk1 hkM) hsum (abs_nonneg _) (by positivity))
                (by positivity) zero_le_one
          _ = 2 * H * μ * (1 / (k : ℝ)) := by ring
    · rw [if_neg hkM]
      simp only [hv]
      rw [huzero k (by omega), huzero (k + 1) (by omega)]
      simp
  have htel : ∀ K' : ℕ, ∑ k ∈ Finset.Icc 1 K', (u k - u (k + 1)) = u 1 - u (K' + 1) := by
    intro K'
    induction K' with
    | zero => simp
    | succ K'' ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
  have hsumTV : ∑ k ∈ Finset.Icc 1 K, |v k - v (k + 1)| ≤
      H ^ 2 + 2 * H * μ * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
    refine (Finset.sum_le_sum hTV).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htel]
    have h1 : H ^ 2 * (u 1 - u (K + 1)) ≤ H ^ 2 := by
      have := hu1 1 le_rfl; have := hu0 (K + 1) (by omega); nlinarith [sq_nonneg H]
    have h2 : ∑ k ∈ Finset.Icc 1 K, (if k ≤ M then 2 * H * μ * (1 / (k : ℝ)) else 0) ≤
        2 * H * μ * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
    linarith
  linarith [hvK, hsumTV]

/-! ## The energy bound -/

/-- The summed per-term bound, with the oscillatory part isolated. -/
theorem bdDualEnergy_polyLogDual_le_sum {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ : ℂ} (hre : ρ.re = 1 / 2) {Y : ℝ} (hY1 : 1 ≤ Y) {Lψ : ℝ}
    (hLψ : ∀ x x' : ℝ, 0 < x → x ≤ x' → Smooth1 ν ε x - Smooth1 ν ε x' ≤ Lψ * (x' - x))
    {h : ℕ → ℝ} {H μ : ℝ} (hH0 : 0 ≤ H) (hμ0 : 0 ≤ μ)
    (hhH : ∀ k, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ + 1 → |h k| ≤ H)
    (hhLip : ∀ k, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ → |h k - h (k + 1)| ≤ μ / k) (K : ℕ) :
    bdDualEnergy (fun k => h k * (zeroSmoothDual ν ε ρ Y k).re) K ≤
      ∑ k ∈ Finset.Icc 1 K, h k ^ 2 * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ))) *
          (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re +
        ‖ρ‖ ^ 2 / 2 * (∑ k ∈ Finset.Icc 1 ⌊3 * Y⌋₊, h k ^ 2 / k + 2 * H ^ 2) +
        2 * (2 * (H * ‖ρ‖ * (H * (‖ρ‖ * ‖ρ + 1‖)) + H * ‖ρ‖ * (H * (‖ρ‖ * ‖ρ + 1‖)) +
          H * (‖ρ‖ * ‖ρ + 1‖) * (H * (‖ρ‖ * ‖ρ + 1‖)))) +
        (2 * (H * ‖ρ‖ + H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖) + H * (‖ρ‖ * ‖ρ + 1‖)) * H +
          4 * H ^ 2 * Lψ + 4 * μ * H) +
        (4 * μ * (H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖)) + 2 * μ ^ 2) *
          ∑ k ∈ Finset.Icc 1 ⌊3 * Y⌋₊, 1 / (k : ℝ) := by
  have hY0 : 0 < Y := by linarith
  set M : ℕ := ⌊3 * Y⌋₊ with hM
  set w : ℕ → ℝ := fun k => Smooth1 ν ε ((k : ℝ) / Y) with hw
  set C₁ : ℝ := 2 * (H * ‖ρ‖ * (H * (‖ρ‖ * ‖ρ + 1‖)) + H * ‖ρ‖ * (H * (‖ρ‖ * ‖ρ + 1‖)) +
    H * (‖ρ‖ * ‖ρ + 1‖) * (H * (‖ρ‖ * ‖ρ + 1‖))) with hC₁
  set C₂ : ℝ := 2 * (H * ‖ρ‖ + H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖) + H * (‖ρ‖ * ‖ρ + 1‖)) * H +
    4 * H ^ 2 * Lψ + 4 * μ * H with hC₂
  set C₃ : ℝ := 4 * μ * (H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖)) + 2 * μ ^ 2 with hC₃
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hwnn : ∀ k, 1 ≤ k → 0 ≤ w k := fun k hk =>
    Smooth1Nonneg νpos (div_pos (by exact_mod_cast hk) hY0) hε0
  have hwle : ∀ k, 1 ≤ k → w k ≤ 1 := fun k hk =>
    Smooth1LeOne νpos mass_one hε0 (div_pos (by exact_mod_cast hk) hY0)
  have hwanti : ∀ k, 1 ≤ k → w (k + 1) ≤ w k := fun k hk =>
    smooth1_antitoneOn hν νpos hε0 (div_pos (by exact_mod_cast hk) hY0)
      (div_le_div_of_nonneg_right (by push_cast; linarith) hY0.le)
  have hwzero : ∀ k, M < k → w k = 0 := by
    intro k hk
    have h3 : 3 * Y < k := (Nat.floor_lt (by positivity)).mp hk
    exact smooth1_eq_zero_of_three_le hν hε0 hε1 (by rw [le_div_iff₀ hY0]; linarith)
  have hwlip : ∀ k, 1 ≤ k → w k - w (k + 1) ≤ Lψ / Y := by
    intro k hk
    have := hLψ ((k : ℝ) / Y) (((k + 1 : ℕ) : ℝ) / Y) (div_pos (by exact_mod_cast hk) hY0)
      (div_le_div_of_nonneg_right (by push_cast; linarith) hY0.le)
    refine this.trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  have hterm : ∀ k ∈ Finset.Icc 1 K, (k : ℝ) * ((k : ℝ) + 1) *
      ((h k * (zeroSmoothDual ν ε ρ Y k).re - h (k + 1) * (zeroSmoothDual ν ε ρ Y (k + 1)).re) *
        (h k * (zeroSmoothDual ν ε ρ Y k).re - h (k + 1) * (zeroSmoothDual ν ε ρ Y (k + 1)).re)) ≤
      h k ^ 2 * (w k ^ 2 / 2 * (1 + 1 / (k : ℝ))) * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re +
        ‖ρ‖ ^ 2 / 2 * (h k ^ 2 * w k ^ 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ))) +
        C₁ / (k : ℝ) ^ 2 + C₂ * (w k - w (k + 1)) +
        (if k ≤ M then C₃ * (1 / (k : ℝ)) else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    by_cases hkM : M < k
    · have hz0 : (zeroSmoothDual ν ε ρ Y k).re = 0 := by
        rw [re_zeroSmoothDual ν ε ρ Y hk1]
        have := hwzero k hkM; simp only [hw] at this; rw [this, mul_zero]
      have hz1 : (zeroSmoothDual ν ε ρ Y (k + 1)).re = 0 := by
        rw [re_zeroSmoothDual ν ε ρ Y (by omega)]
        have := hwzero (k + 1) (by omega); simp only [hw] at this; rw [this, mul_zero]
      rw [hz0, hz1, hwzero k hkM, hwzero (k + 1) (by omega), if_neg (by omega)]
      simp only [mul_zero, sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div, mul_zero, zero_add]
      positivity
    push Not at hkM
    have hk3 : (k : ℝ) ≤ 3 * Y := (Nat.le_floor_iff (by positivity)).mp hkM
    have := polyLogDual_term_le (h := h) (H := H) (μ := μ) (Lψ := Lψ) νpos mass_one hε0 hre hY1
      hH0 hμ0 hk1 hk3 (hwanti k hk1) (hwlip k hk1) (hhH k hk1 (by omega)) (hhLip k hk1 hkM)
    rw [if_pos hkM]
    simp only [hw, hC₁, hC₂, hC₃] at this ⊢
    have e1 : (4 * μ * (H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖)) + 2 * μ ^ 2) / (k : ℝ) =
        (4 * μ * (H * ‖ρ‖ + H * (‖ρ‖ * ‖ρ + 1‖)) + 2 * μ ^ 2) * (1 / (k : ℝ)) := by ring
    have e2 : h k ^ 2 * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) *
        (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re) = h k ^ 2 * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 *
        (1 + 1 / (k : ℝ))) * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re := by ring
    linarith only [this, e1, e2]
  rw [bdDualEnergy_eq_bdDualBilin, bdDualBilin_eq_sum_Icc]
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_add_distrib]
  -- the main sum
  have hmain : ∑ k ∈ Finset.Icc 1 K, ‖ρ‖ ^ 2 / 2 *
      (h k ^ 2 * w k ^ 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ))) ≤
      ‖ρ‖ ^ 2 / 2 * (∑ k ∈ Finset.Icc 1 M, h k ^ 2 / k + 2 * H ^ 2) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hle : ∀ k ∈ Finset.Icc 1 K, h k ^ 2 * w k ^ 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ)) ≤
        (if k ≤ M then h k ^ 2 / k else 0) + H ^ 2 * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      by_cases hkM : k ≤ M
      · rw [if_pos hkM]
        have hw2 : w k ^ 2 ≤ 1 := pow_le_one₀ (hwnn k hk1) (hwle k hk1)
        have hh2 : h k ^ 2 ≤ H ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hhH k hk1 (by omega)) 2
        have e : h k ^ 2 * w k ^ 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ)) =
            h k ^ 2 * w k ^ 2 / k + h k ^ 2 * w k ^ 2 * (1 / (k : ℝ) ^ 2) := by field_simp
        rw [e]
        have a1 : h k ^ 2 * w k ^ 2 / k ≤ h k ^ 2 / k :=
          div_le_div_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg _) hw2) hkk0.le
        have a2 : h k ^ 2 * w k ^ 2 * (1 / (k : ℝ) ^ 2) ≤ H ^ 2 * (1 / (k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right ((mul_le_of_le_one_right (sq_nonneg _) hw2).trans hh2)
            (by positivity)
        linarith
      · rw [if_neg hkM, hwzero k (by omega)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
          zero_add]
        positivity
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
    have h1 : ∑ k ∈ Finset.Icc 1 K with k ≤ M, h k ^ 2 / k ≤ ∑ k ∈ Finset.Icc 1 M, h k ^ 2 / k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
    have h2 : H ^ 2 * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 ≤ H ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left (by simpa only [one_div] using sum_Icc_inv_sq_le_two K)
        (sq_nonneg _)
    linarith
  have hC₁s : ∑ k ∈ Finset.Icc 1 K, C₁ / (k : ℝ) ^ 2 ≤ 2 * C₁ := by
    calc ∑ k ∈ Finset.Icc 1 K, C₁ / (k : ℝ) ^ 2 =
          C₁ * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ C₁ * 2 := mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using sum_Icc_inv_sq_le_two K) hC₁0
      _ = 2 * C₁ := by ring
  have hC₂s : ∑ k ∈ Finset.Icc 1 K, C₂ * (w k - w (k + 1)) ≤ C₂ := by
    have htel : ∀ K' : ℕ, ∑ k ∈ Finset.Icc 1 K', (w k - w (k + 1)) = w 1 - w (K' + 1) := by
      intro K'
      induction K' with
      | zero => simp
      | succ K'' ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
    have hC₂0 : 0 ≤ C₂ := by
      have : 0 ≤ Lψ := by
        have h := hLψ 1 2 one_pos (by norm_num)
        have h1 : Smooth1 ν ε 2 ≤ Smooth1 ν ε 1 :=
          smooth1_antitoneOn hν νpos hε0 one_pos (by norm_num)
        nlinarith
      positivity
    rw [← Finset.mul_sum, htel]
    have h1 := hwle 1 le_rfl
    have h2 := hwnn (K + 1) (by omega)
    calc C₂ * (w 1 - w (K + 1)) ≤ C₂ * 1 := mul_le_mul_of_nonneg_left (by linarith) hC₂0
      _ = C₂ := mul_one _
  have hC₃s : ∑ k ∈ Finset.Icc 1 K, (if k ≤ M then C₃ * (1 / (k : ℝ)) else 0) ≤
      C₃ * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) := by
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    omega
  linarith only [hmain, hC₁s, hC₂s, hC₃s]

/-- **Energy of the polynomially log-weighted dual.**  For `Re ρ = ½`, `Im ρ ≠ 0` and a real
polynomial `p`, the real dual `A_k = p(log k/log Y)·Re(k^{−ρ})ψ(k/Y)` has
`Σ k(k+1)(A_k − A_{k+1})² ≤ (|ρ|²/2) Σ_{k ≤ 3Y} p(log k/log Y)²/k + K₀` for all `Y ≥ e`. -/
theorem exists_bdDualEnergy_polyLogDual_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) (p : Polynomial ℝ) :
    ∃ K₀ : ℝ, ∀ Y : ℝ, Real.exp 1 ≤ Y → ∀ K : ℕ,
      bdDualEnergy (fun k => p.eval (Real.log k / Real.log Y) *
          (zeroSmoothDual ν ε ρ Y k).re) K ≤
        ‖ρ‖ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 ⌊3 * Y⌋₊,
          p.eval (Real.log k / Real.log Y) ^ 2 / k + K₀ := by
  obtain ⟨H₀, hH₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  obtain ⟨Λ₀, hΛ₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    p.derivative.continuous.continuousOn
  set H : ℝ := max H₀ 0 with hHdef
  set Λ : ℝ := max Λ₀ 0 with hΛdef
  have hH0 : 0 ≤ H := le_max_right _ _
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hpH : ∀ x ∈ Icc (0 : ℝ) 4, |p.eval x| ≤ H := fun x hx =>
    (hH₀ x hx).trans (le_max_left _ _)
  have hpLip : ∀ x ∈ Icc (0 : ℝ) 4, ∀ y ∈ Icc (0 : ℝ) 4,
      |p.eval x - p.eval y| ≤ Λ * |x - y| := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x => p.eval x) (C := Λ)
      (fun z _ => p.differentiableAt) (fun z hz => by
        rw [p.deriv]; exact (hΛ₀ z hz).trans (le_max_left _ _)) (convex_Icc 0 4) hy hx
    simpa [Real.norm_eq_abs] using h
  obtain ⟨Lψ, hLψ0, hLψ⟩ := exists_abs_smooth1_sub_le hν νpos hε0
  have hs1 : (ρ + ρ).re = 1 := by simp [hre]; norm_num
  have hs1' : ρ + ρ ≠ 1 := fun h => him (by
    have := congrArg Complex.im h
    simp at this
    linarith)
  obtain ⟨B₀, hB₀0, hB₀⟩ := exists_norm_sum_natCast_cpow_neg_le hs1 hs1'
  set P : ℝ := H * ‖ρ‖ with hPdef
  set Q : ℝ := H * (‖ρ‖ * ‖ρ + 1‖) with hQdef
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨‖ρ‖ ^ 2 * B₀ * (2 * H ^ 2 + 8 * H * Λ) + ‖ρ‖ ^ 2 * H ^ 2 +
    2 * (2 * (P * Q + P * Q + Q * Q)) + (2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * Λ * H) +
    (16 * Λ * (P + Q) + 8 * Λ ^ 2), fun Y hY K => ?_⟩
  have hY1 : 1 ≤ Y := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hY
  have hY0 : 0 < Y := by linarith
  set L : ℝ := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hY
  have hL0 : 0 < L := by linarith
  set μ : ℝ := Λ / L with hμdef
  have hμ0 : 0 ≤ μ := by positivity
  have hμΛ : μ ≤ Λ := div_le_self hΛ0 hL1
  set M : ℕ := ⌊3 * Y⌋₊ with hM
  set h : ℕ → ℝ := fun k => p.eval (Real.log k / L) with hh
  have hrange : ∀ k, 1 ≤ k → k ≤ M + 1 → Real.log k / L ∈ Icc (0 : ℝ) 4 := by
    intro k hk1 hkM
    have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    refine ⟨div_nonneg (Real.log_nonneg hkk) hL0.le, ?_⟩
    rw [div_le_iff₀ hL0]
    have hk4 : (k : ℝ) ≤ 4 * Y := by
      have h1 : (M : ℝ) ≤ 3 * Y := Nat.floor_le (by positivity)
      have h2 : (k : ℝ) ≤ M + 1 := by exact_mod_cast hkM
      linarith
    have hlog : Real.log k ≤ Real.log (4 * Y) := Real.log_le_log (by linarith) hk4
    rw [Real.log_mul (by norm_num) hY0.ne'] at hlog
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    linarith
  have hhH : ∀ k, 1 ≤ k → k ≤ M + 1 → |h k| ≤ H := fun k hk1 hkM =>
    hpH _ (hrange k hk1 hkM)
  have hhLip : ∀ k, 1 ≤ k → k ≤ M → |h k - h (k + 1)| ≤ μ / k := by
    intro k hk1 hkM
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have h1 := hpLip _ (hrange k hk1 (by omega)) _ (hrange (k + 1) (by omega) (by omega))
    have hdiff : |Real.log k / L - Real.log ((k + 1 : ℕ) : ℝ) / L| ≤ 1 / (L * k) := by
      rw [← sub_div, abs_div, abs_of_pos hL0, abs_sub_comm, div_le_div_iff₀ hL0 (by positivity)]
      have hmono : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
        Real.log_le_log hk0 (by push_cast; linarith)
      rw [abs_of_nonneg (by linarith)]
      have := log_natSucc_sub_log_le_inv hk1
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ L * k)
      field_simp at this ⊢
      nlinarith
    calc |h k - h (k + 1)| ≤ Λ * |Real.log k / L - Real.log ((k + 1 : ℕ) : ℝ) / L| := h1
      _ ≤ Λ * (1 / (L * k)) := mul_le_mul_of_nonneg_left hdiff hΛ0
      _ = μ / k := by rw [hμdef]; field_simp
  -- harmonic bounds
  have hMpos : (1 : ℝ) ≤ M := by
    have : (1 : ℕ) ≤ M := (Nat.le_floor_iff (by positivity)).mpr (by push_cast; linarith)
    exact_mod_cast this
  have hlogM : 1 + Real.log M ≤ 4 * L := by
    have h1 : Real.log M ≤ Real.log (3 * Y) :=
      Real.log_le_log (by linarith) (Nat.floor_le (by positivity))
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    linarith
  set S : ℝ := ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have hμS : μ * S ≤ 4 * Λ := by
    calc μ * S ≤ μ * (4 * L) :=
          mul_le_mul_of_nonneg_left ((sum_Icc_inv_le_one_add_log M).trans hlogM) hμ0
      _ = 4 * Λ := by rw [hμdef]; field_simp
  have hμ2S : μ ^ 2 * S ≤ 4 * Λ ^ 2 := by
    calc μ ^ 2 * S = μ * (μ * S) := by ring
      _ ≤ Λ * (4 * Λ) := mul_le_mul hμΛ hμS (by positivity) hΛ0
      _ = 4 * Λ ^ 2 := by ring
  -- the two lemmas
  have hsum := bdDualEnergy_polyLogDual_le_sum hν νpos mass_one hε0 hε1 hre hY1 hLψ hH0 hμ0
    hhH hhLip K
  set u : ℕ → ℝ := fun k => Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) with hu
  have hu0 : ∀ k, 1 ≤ k → 0 ≤ u k := fun k hk => by
    have := Smooth1Nonneg νpos (div_pos (by exact_mod_cast hk : (0:ℝ) < k) hY0) hε0
    positivity
  have hu1 : ∀ k, 1 ≤ k → u k ≤ 1 := by
    intro k hk
    have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hw0 := Smooth1Nonneg νpos (div_pos (by linarith : (0:ℝ) < k) hY0) hε0
    have hw1 := Smooth1LeOne νpos mass_one hε0 (div_pos (by linarith : (0:ℝ) < k) hY0)
    have hw2 : Smooth1 ν ε ((k : ℝ) / Y) ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
    have hk2 : 1 + 1 / (k : ℝ) ≤ 2 := by
      have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hkk
      linarith
    simp only [hu]
    have := mul_le_mul hw2 hk2 (by positivity) zero_le_one
    linarith
  have huanti : ∀ k, 1 ≤ k → u (k + 1) ≤ u k := by
    intro k hk
    have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hw0 := Smooth1Nonneg νpos (div_pos (by positivity : (0:ℝ) < ((k + 1 : ℕ) : ℝ)) hY0) hε0
    have hanti := smooth1_antitoneOn hν νpos hε0 (div_pos (by linarith : (0:ℝ) < k) hY0)
      (div_le_div_of_nonneg_right (by push_cast; linarith : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) hY0.le)
    have hsq : Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) ^ 2 ≤ Smooth1 ν ε ((k : ℝ) / Y) ^ 2 :=
      pow_le_pow_left₀ hw0 hanti 2
    have hfr : 1 + 1 / (((k + 1 : ℕ) : ℝ)) ≤ 1 + 1 / (k : ℝ) := by
      have := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < k)
        (by push_cast; linarith : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ))
      linarith
    simp only [hu]
    have := mul_le_mul hsq hfr (by positivity) (by positivity)
    linarith
  have huzero : ∀ k, M < k → u k = 0 := by
    intro k hk
    have h3 : 3 * Y < k := (Nat.floor_lt (by positivity)).mp hk
    simp only [hu]
    rw [smooth1_eq_zero_of_three_le hν hε0 hε1 (by rw [le_div_iff₀ hY0]; linarith)]
    simp
  have hosc := abs_sum_sq_mul_osc_le hB₀ (h := h) (u := u) hH0 hμ0 hu0 hu1 huanti huzero hhH
    hhLip K
  have hoscle : ∑ k ∈ Finset.Icc 1 K, h k ^ 2 * u k * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re ≤
      ‖ρ‖ ^ 2 * B₀ * (2 * H ^ 2 + 8 * H * Λ) := by
    refine (le_abs_self _).trans (hosc.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 2 * H * μ * S ≤ 8 * H * Λ := by
      calc 2 * H * μ * S = 2 * H * (μ * S) := by ring
        _ ≤ 2 * H * (4 * Λ) := mul_le_mul_of_nonneg_left hμS (by positivity)
        _ = 8 * H * Λ := by ring
    linarith
  have hC₂le : 2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H ≤
      2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * Λ * H := by
    have := mul_le_mul_of_nonneg_right hμΛ hH0
    linarith
  have hC₃le : (4 * μ * (P + Q) + 2 * μ ^ 2) * S ≤ 16 * Λ * (P + Q) + 8 * Λ ^ 2 := by
    have e : (4 * μ * (P + Q) + 2 * μ ^ 2) * S = 4 * (P + Q) * (μ * S) + 2 * (μ ^ 2 * S) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hμS (by positivity : (0 : ℝ) ≤ 4 * (P + Q))
    linarith
  show bdDualEnergy (fun k => h k * (zeroSmoothDual ν ε ρ Y k).re) K ≤
    ‖ρ‖ ^ 2 / 2 * ∑ k ∈ Finset.Icc 1 M, h k ^ 2 / k + _
  simp only [hu] at hoscle
  simp only [hPdef, hQdef] at hC₂le hC₃le
  simp only [hSdef] at hC₃le
  linarith only [hsum, hoscle, hC₂le, hC₃le]

end

end RHTower
