import GaloisForLFunctions.RHTower.BaezDuarteLogDualEnergy

/-!
# Asymptotic orthogonality of polynomially log-weighted zero duals

Let `ρ ≠ ρ'` be zeros on the critical line in the upper half-plane, `p, p'` real polynomials,
`L = log Y` and `A_k = p(log k/L)Re(k^{−ρ})ψ(k/Y)`, `A'_k = p'(log k/L)Re(k^{−ρ'})ψ(k/Y)`.  Then
(`exists_bdDualBilin_polyLogDual_le_of_ne`)

  `Σ_k k(k+1)(A_k − A_{k+1})(A'_k − A'_{k+1}) ≤ K₃`   for all `Y ≥ e`.

**Proof.**  As for the energy (`exists_bdDualEnergy_polyLogDual_le`), the increments are
`h_k w_k Re(ρk^{−ρ}/k)` plus errors of total cost `O(1)`.  The main product is
`h_k h'_k w_k²(1 + 1/k)(Re(ρρ'k^{−(ρ+ρ')}) + Re(ρρ̄'k^{−(ρ+ρ̄')}))/2`.  Both phases `ρ + ρ'` and
`ρ + ρ̄'` have real part `1` and are `≠ 1`, so their partial sums are bounded, and the weights
`h_k h'_k w_k²(1 + 1/k)/2` have bounded variation (`abs_sum_mul_mul_osc_le`).
-/

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The per-term inequality -/

theorem mul_mul_le_of_abs_le_of_abs_le {kk s P Q μ H d y η : ℝ} (hk : 1 ≤ kk) (hs0 : 0 ≤ s)
    (hs : kk * s ^ 2 = 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hμ : 0 ≤ μ) (hHd : 0 ≤ H * d)
    (hy : |y| ≤ (P + Q) * s / kk + s * (H * d)) (hη : |η| ≤ μ * s / kk) :
    kk * (kk + 1) * (y * η) ≤ 2 * μ * (P + Q) / kk + 2 * μ * (H * d) := by
  have hk0 : 0 < kk := by linarith
  have hprod : y * η ≤ ((P + Q) * s / kk + s * (H * d)) * (μ * s / kk) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul hy hη (abs_nonneg _) (by positivity)
  have hw : 0 ≤ kk * (kk + 1) := by positivity
  have e1 : kk * (kk + 1) * (((P + Q) * s / kk + s * (H * d)) * (μ * s / kk)) =
      (kk * s ^ 2) * ((kk + 1) / kk * (μ * ((P + Q) / kk + H * d))) := by
    field_simp
  have hk2 : (kk + 1) / kk ≤ 2 := by rw [div_le_iff₀ hk0]; linarith
  have hnn : 0 ≤ μ * ((P + Q) / kk + H * d) := by positivity
  have h2 : (kk + 1) / kk * (μ * ((P + Q) / kk + H * d)) ≤ 2 * (μ * ((P + Q) / kk + H * d)) :=
    mul_le_mul_of_nonneg_right hk2 hnn
  have e2 : 2 * (μ * ((P + Q) / kk + H * d)) = 2 * μ * (P + Q) / kk + 2 * μ * (H * d) := by ring
  rw [hs, one_mul] at e1
  have := mul_le_mul_of_nonneg_left hprod hw
  linarith

/-- `k(k+1)(x + e + δ)(x' + e' + δ')` with `|x|, |x'| ≤ Ps/k`, `|e|, |e'| ≤ Qs/k² + sHd`,
`|δ|, |δ'| ≤ μs/k`, `ks² = 1`. -/
theorem mul_add_add_mul_add_add_le {kk s P Q μ H d x e δ x' e' δ' : ℝ} (hk : 1 ≤ kk)
    (hs0 : 0 ≤ s) (hs : kk * s ^ 2 = 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hμ : 0 ≤ μ) (hH : 0 ≤ H)
    (hd : 0 ≤ d) (hx : |x| ≤ P * s / kk) (he : |e| ≤ Q * s / kk ^ 2 + s * (H * d))
    (hδ : |δ| ≤ μ * s / kk) (hx' : |x'| ≤ P * s / kk) (he' : |e'| ≤ Q * s / kk ^ 2 + s * (H * d))
    (hδ' : |δ'| ≤ μ * s / kk) :
    kk * (kk + 1) * ((x + e + δ) * (x' + e' + δ')) ≤ kk * (kk + 1) * (x * x') +
      2 * (P * Q + P * Q + Q * Q) / kk ^ 2 + 2 * (P + P + Q + Q) * (H * d) +
        (kk + 1) * (H * d) ^ 2 + (4 * μ * (P + Q) + 2 * μ ^ 2) / kk + 4 * μ * (H * d) := by
  have hk0 : 0 < kk := by linarith
  have hHd : 0 ≤ H * d := mul_nonneg hH hd
  have h1 := mul_add_mul_add_le_of_abs_le hk hs0 hs hP hQ hP hQ hHd hx he hx' he'
  have hX : ∀ y f : ℝ, |y| ≤ P * s / kk → |f| ≤ Q * s / kk ^ 2 + s * (H * d) →
      |y + f| ≤ (P + Q) * s / kk + s * (H * d) := by
    intro y f hy hf
    have hkk : Q * s / kk ^ 2 ≤ Q * s / kk :=
      div_le_div_of_nonneg_left (by positivity) hk0 (by nlinarith)
    have e : (P + Q) * s / kk = P * s / kk + Q * s / kk := by ring
    have := abs_add_le y f
    linarith
  have hc1 := mul_mul_le_of_abs_le_of_abs_le hk hs0 hs hP hQ hμ hHd (hX x e hx he) hδ'
  have hc2 := mul_mul_le_of_abs_le_of_abs_le hk hs0 hs hP hQ hμ hHd (hX x' e' hx' he') hδ
  have hδ2 : kk * (kk + 1) * (δ * δ') ≤ 2 * μ ^ 2 / kk := by
    have hprod : δ * δ' ≤ (μ * s / kk) * (μ * s / kk) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul hδ hδ' (abs_nonneg _) (by positivity)
    have hw : 0 ≤ kk * (kk + 1) := by positivity
    have e1 : kk * (kk + 1) * ((μ * s / kk) * (μ * s / kk)) =
        (kk * s ^ 2) * ((kk + 1) / kk * (μ ^ 2 / kk)) := by
      field_simp
    rw [hs, one_mul] at e1
    have hk2 : (kk + 1) / kk ≤ 2 := by rw [div_le_iff₀ hk0]; linarith
    have h2 : (kk + 1) / kk * (μ ^ 2 / kk) ≤ 2 * (μ ^ 2 / kk) :=
      mul_le_mul_of_nonneg_right hk2 (by positivity)
    have := mul_le_mul_of_nonneg_left hprod hw
    have e2 : 2 * (μ ^ 2 / kk) = 2 * μ ^ 2 / kk := by ring
    linarith
  have hsplit : kk * (kk + 1) * ((x + e + δ) * (x' + e' + δ')) =
      kk * (kk + 1) * ((x + e) * (x' + e')) + kk * (kk + 1) * ((x + e) * δ') +
        kk * (kk + 1) * ((x' + e') * δ) + kk * (kk + 1) * (δ * δ') := by ring
  have e4 : (4 * μ * (P + Q) + 2 * μ ^ 2) / kk =
      2 * μ * (P + Q) / kk + 2 * μ * (P + Q) / kk + 2 * μ ^ 2 / kk := by ring
  have e5 : 4 * μ * (H * d) = 2 * μ * (H * d) + 2 * μ * (H * d) := by ring
  linarith

/-- **The bilinear per-term bound** for `A_k = h_k Re(a_k)`, `A'_k = h'_k Re(a'_k)`. -/
theorem polyLogDual_bilin_term_le {ν : ℝ → ℝ} (νpos : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε) {ρ ρ' : ℂ}
    (hre : ρ.re = 1 / 2) (hre' : ρ'.re = 1 / 2) {Y : ℝ} (hY1 : 1 ≤ Y) {Lψ : ℝ} {h h' : ℕ → ℝ}
    {H μ P Q : ℝ} (hH0 : 0 ≤ H) (hμ0 : 0 ≤ μ) (hPρ : H * ‖ρ‖ ≤ P) (hPρ' : H * ‖ρ'‖ ≤ P)
    (hQρ : H * (‖ρ‖ * ‖ρ + 1‖) ≤ Q) (hQρ' : H * (‖ρ'‖ * ‖ρ' + 1‖) ≤ Q) {k : ℕ}
    (hk1 : 1 ≤ k) (hk3 : (k : ℝ) ≤ 3 * Y)
    (hanti : Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) ≤ Smooth1 ν ε ((k : ℝ) / Y))
    (hwlip : Smooth1 ν ε ((k : ℝ) / Y) - Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) ≤ Lψ / Y)
    (hhk : |h k| ≤ H) (hhLip : |h k - h (k + 1)| ≤ μ / k)
    (hhk' : |h' k| ≤ H) (hhLip' : |h' k - h' (k + 1)| ≤ μ / k) :
    (k : ℝ) * ((k : ℝ) + 1) *
        ((h k * (zeroSmoothDual ν ε ρ Y k).re - h (k + 1) * (zeroSmoothDual ν ε ρ Y (k + 1)).re) *
        (h' k * (zeroSmoothDual ν ε ρ' Y k).re -
          h' (k + 1) * (zeroSmoothDual ν ε ρ' Y (k + 1)).re)) ≤
      h k * h' k * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ))) *
          ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
            (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) +
        2 * (P * Q + P * Q + Q * Q) / (k : ℝ) ^ 2 +
        (2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H) *
          (Smooth1 ν ε ((k : ℝ) / Y) - Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y)) +
        (4 * μ * (P + Q) + 2 * μ ^ 2) / k := by
  have hY0 : 0 < Y := by linarith
  have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkk0 : (0 : ℝ) < k := by linarith
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hP0 : 0 ≤ P := (by positivity : (0 : ℝ) ≤ H * ‖ρ‖).trans hPρ
  have hQ0 : 0 ≤ Q := (by positivity : (0 : ℝ) ≤ H * (‖ρ‖ * ‖ρ + 1‖)).trans hQρ
  set w : ℝ := Smooth1 ν ε ((k : ℝ) / Y) with hw
  set w' : ℝ := Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) with hw'
  have hw0 : 0 ≤ w := Smooth1Nonneg νpos (div_pos hkk0 hY0) hε0
  have hw1 : w ≤ 1 := Smooth1LeOne νpos mass_one hε0 (div_pos hkk0 hY0)
  have hw'0 : 0 ≤ w' := Smooth1Nonneg νpos (div_pos (by positivity) hY0) hε0
  have hw'1 : w' ≤ 1 := Smooth1LeOne νpos mass_one hε0 (div_pos (by positivity) hY0)
  set s : ℝ := (Real.sqrt k)⁻¹ with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs : (k : ℝ) * s ^ 2 = 1 := by
    rw [hsdef, inv_pow, Real.sq_sqrt hkk0.le]; field_simp
  set d : ℝ := w - w' with hddef
  have hd0 : 0 ≤ d := sub_nonneg.mpr hanti
  -- the bounds for one zero
  have hone : ∀ (σ : ℂ) (g : ℕ → ℝ), σ.re = 1 / 2 → H * ‖σ‖ ≤ P →
      H * (‖σ‖ * ‖σ + 1‖) ≤ Q → |g k| ≤ H → |g k - g (k + 1)| ≤ μ / k →
      ∃ x e δ : ℝ,
        g k * (zeroSmoothDual ν ε σ Y k).re - g (k + 1) * (zeroSmoothDual ν ε σ Y (k + 1)).re =
          x + e + δ ∧ x = g k * (w * (σ * (k : ℂ) ^ (-σ) / k).re) ∧
        |x| ≤ P * s / k ∧ |e| ≤ Q * s / (k : ℝ) ^ 2 + s * (H * d) ∧ |δ| ≤ μ * s / k := by
    intro σ g hσ hPσ hQσ hgk hgLip
    obtain ⟨e, he1, he2⟩ := exists_re_zeroSmoothDual_sub_succ_eq ν ε hσ Y hk1 hw0 hw1 hanti
    have hzn : ‖(k : ℂ) ^ (-σ)‖ = s := norm_natCast_cpow_neg_of_re hσ hk1
    refine ⟨g k * (w * (σ * (k : ℂ) ^ (-σ) / k).re), g k * e,
      (g k - g (k + 1)) * (zeroSmoothDual ν ε σ Y (k + 1)).re, ?_, rfl, ?_, ?_, ?_⟩
    · have : (zeroSmoothDual ν ε σ Y k).re =
          w * (σ * (k : ℂ) ^ (-σ) / k).re + e + (zeroSmoothDual ν ε σ Y (k + 1)).re := by
        linarith only [he1]
      rw [this]; ring
    · rw [abs_mul]
      have hwv : |w * (σ * (k : ℂ) ^ (-σ) / k).re| ≤ ‖σ‖ * s / k := by
        rw [abs_mul, abs_of_nonneg hw0]
        calc w * |(σ * (k : ℂ) ^ (-σ) / k).re| ≤ 1 * ‖σ * (k : ℂ) ^ (-σ) / k‖ :=
              mul_le_mul hw1 (Complex.abs_re_le_norm _) (abs_nonneg _) zero_le_one
          _ = ‖σ‖ * s / k := by
              rw [one_mul, norm_div, norm_mul, hzn, Complex.norm_natCast]
      calc |g k| * |w * (σ * (k : ℂ) ^ (-σ) / k).re| ≤ H * (‖σ‖ * s / k) :=
            mul_le_mul hgk hwv (abs_nonneg _) hH0
        _ = (H * ‖σ‖) * s / k := by ring
        _ ≤ P * s / k := by gcongr
    · rw [abs_mul]
      calc |g k| * |e| ≤ H * (‖σ‖ * ‖σ + 1‖ * s / (k : ℝ) ^ 2 + s * d) :=
            mul_le_mul hgk he2 (abs_nonneg _) hH0
        _ = (H * (‖σ‖ * ‖σ + 1‖)) * s / (k : ℝ) ^ 2 + s * (H * d) := by ring
        _ ≤ Q * s / (k : ℝ) ^ 2 + s * (H * d) := by gcongr
    · have hre1 : |(zeroSmoothDual ν ε σ Y (k + 1)).re| ≤ s := by
        rw [re_zeroSmoothDual ν ε σ Y (by omega), abs_mul, ← hw', abs_of_nonneg hw'0]
        have hn1 : ‖((k + 1 : ℕ) : ℂ) ^ (-σ)‖ ≤ s := by
          rw [norm_natCast_cpow_neg_of_re hσ (by omega), hsdef]
          exact inv_anti₀ (Real.sqrt_pos.mpr hkk0) (Real.sqrt_le_sqrt (by push_cast; linarith))
        calc |(((k + 1 : ℕ) : ℂ) ^ (-σ)).re| * w' ≤ s * 1 :=
              mul_le_mul ((Complex.abs_re_le_norm _).trans hn1) hw'1 hw'0 hs0
          _ = s := mul_one _
      rw [abs_mul]
      calc |g k - g (k + 1)| * |(zeroSmoothDual ν ε σ Y (k + 1)).re| ≤ (μ / k) * s :=
            mul_le_mul hgLip hre1 (abs_nonneg _) (by positivity)
        _ = μ * s / k := by ring
  obtain ⟨x, e, δ, hinc, hxdef, hx, he, hδ⟩ := hone ρ h hre hPρ hQρ hhk hhLip
  obtain ⟨x', e', δ', hinc', hxdef', hx', he', hδ'⟩ := hone ρ' h' hre' hPρ' hQρ' hhk' hhLip'
  have hkey := mul_add_add_mul_add_add_le hkk hs0 hs hP0 hQ0 hμ0 hH0 hd0 hx he hδ hx' he' hδ'
  rw [hinc, hinc']
  -- the main product
  set z : ℂ := (k : ℂ) ^ (-ρ) with hzdef
  set z' : ℂ := (k : ℂ) ^ (-ρ') with hz'def
  set v : ℂ := ρ * z / k with hvdef
  set v' : ℂ := ρ' * z' / k with hv'def
  have hzz : z * z' = (k : ℂ) ^ (-(ρ + ρ')) := by
    rw [hzdef, hz'def, ← Complex.cpow_add _ _ hkne, neg_add]
  have hzc : z * conj z' = (k : ℂ) ^ (-(ρ + conj ρ')) := by
    rw [hz'def, ← natCast_cpow_conj, hzdef, ← Complex.cpow_add _ _ hkne, map_neg, neg_add]
  have hk2 : ((k : ℂ) ^ 2) = (((k : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have hvv : (v * v').re = (ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re / (k : ℝ) ^ 2 := by
    rw [show v * v' = ρ * ρ' * (z * z') / (k : ℂ) ^ 2 by rw [hvdef, hv'def]; ring, hzz, hk2,
      Complex.div_ofReal_re]
  have hvc : (v * conj v').re = (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re / (k : ℝ) ^ 2 := by
    have : conj v' = conj ρ' * conj z' / k := by
      rw [hv'def, map_div₀, map_mul, Complex.conj_natCast]
    rw [show v * conj v' = ρ * conj ρ' * (z * conj z') / (k : ℂ) ^ 2 by rw [this, hvdef]; ring,
      hzc, hk2, Complex.div_ofReal_re]
  have hxx : (k : ℝ) * ((k : ℝ) + 1) * (x * x') =
      h k * h' k * (w ^ 2 / 2 * (1 + 1 / (k : ℝ))) *
        ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re + (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) := by
    rw [hxdef, hxdef', show h k * (w * v.re) * (h' k * (w * v'.re)) =
      h k * h' k * w ^ 2 * (v.re * v'.re) by ring, re_mul_re_eq, hvv, hvc]
    field_simp
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
  have e2 : (2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H) * d =
      2 * (P + P + Q + Q) * (H * d) + 4 * H ^ 2 * Lψ * d + 4 * μ * (H * d) := by ring
  linarith only [hkey, hxx, hd2, e2]

/-! ## The oscillatory sum -/

/-- Abel summation for `Σ h_k h'_k u_k Re(c k^{−s})` with bounded partial sums of `k^{−s}`. -/
theorem abs_sum_mul_mul_osc_le {c s : ℂ} {B₀ : ℝ}
    (hB₀ : ∀ j : ℕ, ‖∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-s)‖ ≤ B₀)
    {h h' u : ℕ → ℝ} {H μ : ℝ} {M : ℕ} (hH0 : 0 ≤ H) (hμ0 : 0 ≤ μ)
    (hu0 : ∀ k, 1 ≤ k → 0 ≤ u k) (hu1 : ∀ k, 1 ≤ k → u k ≤ 1)
    (huanti : ∀ k, 1 ≤ k → u (k + 1) ≤ u k) (huzero : ∀ k, M < k → u k = 0)
    (hhH : ∀ k, 1 ≤ k → k ≤ M + 1 → |h k| ≤ H) (hhH' : ∀ k, 1 ≤ k → k ≤ M + 1 → |h' k| ≤ H)
    (hhLip : ∀ k, 1 ≤ k → k ≤ M → |h k - h (k + 1)| ≤ μ / k)
    (hhLip' : ∀ k, 1 ≤ k → k ≤ M → |h' k - h' (k + 1)| ≤ μ / k) (K : ℕ) :
    |∑ k ∈ Finset.Icc 1 K, h k * h' k * u k * (c * (k : ℂ) ^ (-s)).re| ≤
      ‖c‖ * B₀ * (2 * H ^ 2 + 2 * H * μ * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)) := by
  set v : ℕ → ℝ := fun k => h k * h' k * u k with hv
  set a : ℕ → ℝ := fun k => (c * (k : ℂ) ^ (-s)).re with ha
  have hpart : ∀ j, |∑ k ∈ Finset.Icc 1 j, a k| ≤ ‖c‖ * B₀ := by
    intro j
    have : ∑ k ∈ Finset.Icc 1 j, a k = (c * ∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-s)).re := by
      rw [Finset.mul_sum, Complex.re_sum]
    rw [this]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB₀ j) (norm_nonneg _)
  have habel := abs_sum_mul_le_of_partialSum_le (a := a) (v := v) K hpart
  have hsum_eq : ∑ k ∈ Finset.Icc 1 K, h k * h' k * u k * (c * (k : ℂ) ^ (-s)).re =
      ∑ k ∈ Finset.Icc 1 K, a k * v k :=
    Finset.sum_congr rfl fun k _ => by simp only [hv, ha]; ring
  rw [hsum_eq]
  have hB0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  refine habel.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) hB0))
  have hhh : ∀ k, 1 ≤ k → k ≤ M + 1 → |h k * h' k| ≤ H ^ 2 := by
    intro k hk1 hkM
    rw [abs_mul, sq]
    exact mul_le_mul (hhH k hk1 hkM) (hhH' k hk1 hkM) (abs_nonneg _) hH0
  have hvK : |v (K + 1)| ≤ H ^ 2 := by
    simp only [hv]
    rw [abs_mul, abs_of_nonneg (hu0 _ (by omega))]
    by_cases hK : K + 1 ≤ M + 1
    · calc |h (K + 1) * h' (K + 1)| * u (K + 1) ≤ H ^ 2 * 1 :=
            mul_le_mul (hhh (K + 1) (by omega) hK) (hu1 _ (by omega)) (hu0 _ (by omega))
              (sq_nonneg H)
        _ = H ^ 2 := mul_one _
    · rw [huzero (K + 1) (by omega), mul_zero]; positivity
  have hTV : ∀ k ∈ Finset.Icc 1 K, |v k - v (k + 1)| ≤
      H ^ 2 * (u k - u (k + 1)) + (if k ≤ M then 2 * H * μ * (1 / (k : ℝ)) else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    by_cases hkM : k ≤ M
    · rw [if_pos hkM]
      have hdiff : v k - v (k + 1) = h k * h' k * (u k - u (k + 1)) +
          u (k + 1) * ((h k - h (k + 1)) * h' k + h (k + 1) * (h' k - h' (k + 1))) := by
        simp only [hv]; ring
      rw [hdiff]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (huanti k hk1))]
        exact mul_le_mul_of_nonneg_right (hhh k hk1 (by omega)) (sub_nonneg.mpr (huanti k hk1))
      · rw [abs_mul, abs_of_nonneg (hu0 _ (by omega))]
        have hinner : |(h k - h (k + 1)) * h' k + h (k + 1) * (h' k - h' (k + 1))| ≤
            2 * H * μ * (1 / (k : ℝ)) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          have a1 : |h k - h (k + 1)| * |h' k| ≤ (μ / k) * H :=
            mul_le_mul (hhLip k hk1 hkM) (hhH' k hk1 (by omega)) (abs_nonneg _) (by positivity)
          have a2 : |h (k + 1)| * |h' k - h' (k + 1)| ≤ H * (μ / k) :=
            mul_le_mul (hhH (k + 1) (by omega) (by omega)) (hhLip' k hk1 hkM) (abs_nonneg _) hH0
          have e : 2 * H * μ * (1 / (k : ℝ)) = (μ / k) * H + H * (μ / k) := by ring
          linarith
        calc u (k + 1) * |(h k - h (k + 1)) * h' k + h (k + 1) * (h' k - h' (k + 1))| ≤
            1 * (2 * H * μ * (1 / (k : ℝ))) :=
              mul_le_mul (hu1 _ (by omega)) hinner (abs_nonneg _) zero_le_one
          _ = 2 * H * μ * (1 / (k : ℝ)) := one_mul _
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

/-! ## The bilinear energy bound -/

/-- The summed bilinear per-term bound, with the oscillatory part isolated. -/
theorem bdDualBilin_polyLogDual_le_sum {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ ρ' : ℂ} (hre : ρ.re = 1 / 2) (hre' : ρ'.re = 1 / 2) {Y : ℝ} (hY1 : 1 ≤ Y)
    {Lψ : ℝ}
    (hLψ : ∀ x x' : ℝ, 0 < x → x ≤ x' → Smooth1 ν ε x - Smooth1 ν ε x' ≤ Lψ * (x' - x))
    {h h' : ℕ → ℝ} {H μ P Q : ℝ} (hH0 : 0 ≤ H) (hμ0 : 0 ≤ μ) (hPρ : H * ‖ρ‖ ≤ P)
    (hPρ' : H * ‖ρ'‖ ≤ P) (hQρ : H * (‖ρ‖ * ‖ρ + 1‖) ≤ Q) (hQρ' : H * (‖ρ'‖ * ‖ρ' + 1‖) ≤ Q)
    (hhH : ∀ k, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ + 1 → |h k| ≤ H)
    (hhH' : ∀ k, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ + 1 → |h' k| ≤ H)
    (hhLip : ∀ k, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ → |h k - h (k + 1)| ≤ μ / k)
    (hhLip' : ∀ k, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ → |h' k - h' (k + 1)| ≤ μ / k) (K : ℕ) :
    bdDualBilin (fun k => h k * (zeroSmoothDual ν ε ρ Y k).re)
        (fun k => h' k * (zeroSmoothDual ν ε ρ' Y k).re) K ≤
      ∑ k ∈ Finset.Icc 1 K, h k * h' k * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ))) *
          ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
            (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) +
        2 * (2 * (P * Q + P * Q + Q * Q)) +
        (2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H) +
        (4 * μ * (P + Q) + 2 * μ ^ 2) * ∑ k ∈ Finset.Icc 1 ⌊3 * Y⌋₊, 1 / (k : ℝ) := by
  have hY0 : 0 < Y := by linarith
  have hP0 : 0 ≤ P := (by positivity : (0 : ℝ) ≤ H * ‖ρ‖).trans hPρ
  have hQ0 : 0 ≤ Q := (by positivity : (0 : ℝ) ≤ H * (‖ρ‖ * ‖ρ + 1‖)).trans hQρ
  set M : ℕ := ⌊3 * Y⌋₊ with hM
  set w : ℕ → ℝ := fun k => Smooth1 ν ε ((k : ℝ) / Y) with hw
  set C₁ : ℝ := 2 * (P * Q + P * Q + Q * Q) with hC₁
  set C₂ : ℝ := 2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H with hC₂
  set C₃ : ℝ := 4 * μ * (P + Q) + 2 * μ ^ 2 with hC₃
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
        (h' k * (zeroSmoothDual ν ε ρ' Y k).re -
          h' (k + 1) * (zeroSmoothDual ν ε ρ' Y (k + 1)).re)) ≤
      h k * h' k * (w k ^ 2 / 2 * (1 + 1 / (k : ℝ))) *
          ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
            (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) +
        C₁ / (k : ℝ) ^ 2 + C₂ * (w k - w (k + 1)) +
        (if k ≤ M then C₃ * (1 / (k : ℝ)) else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    by_cases hkM : M < k
    · have hz : ∀ (σ : ℂ) (j : ℕ), k ≤ j → (zeroSmoothDual ν ε σ Y j).re = 0 := by
        intro σ j hj
        rw [re_zeroSmoothDual ν ε σ Y (by omega)]
        have := hwzero j (by omega); simp only [hw] at this; rw [this, mul_zero]
      rw [hz ρ k le_rfl, hz ρ (k + 1) (by omega), hz ρ' k le_rfl, hz ρ' (k + 1) (by omega),
        hwzero k hkM, hwzero (k + 1) (by omega), if_neg (by omega)]
      simp only [mul_zero, sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div, mul_zero, zero_add]
      positivity
    push Not at hkM
    have hk3 : (k : ℝ) ≤ 3 * Y := (Nat.le_floor_iff (by positivity)).mp hkM
    have := polyLogDual_bilin_term_le (h := h) (h' := h') (Lψ := Lψ) νpos mass_one hε0 hre hre'
      hY1 hH0 hμ0 hPρ hPρ' hQρ hQρ' hk1 hk3 (hwanti k hk1) (hwlip k hk1)
      (hhH k hk1 (by omega)) (hhLip k hk1 hkM) (hhH' k hk1 (by omega)) (hhLip' k hk1 hkM)
    rw [if_pos hkM]
    simp only [hw, hC₁, hC₂, hC₃] at this ⊢
    have e1 : (4 * μ * (P + Q) + 2 * μ ^ 2) / (k : ℝ) =
        (4 * μ * (P + Q) + 2 * μ ^ 2) * (1 / (k : ℝ)) := by ring
    linarith only [this, e1]
  rw [bdDualBilin_eq_sum_Icc]
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_add_distrib]
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
  linarith only [hC₁s, hC₂s, hC₃s]

/-- Uniform bounds for a polynomial weight `p(log k/log Y)` on `1 ≤ k ≤ 3Y + 1`, `Y ≥ e`: size
`≤ H` and increments `≤ (Λ/log Y)/k`; moreover `(Λ/log Y) Σ_{k ≤ 3Y} 1/k ≤ 4Λ`. -/
theorem exists_polyLog_weight_bounds (p : Polynomial ℝ) :
    ∃ H Λ : ℝ, 0 ≤ H ∧ 0 ≤ Λ ∧ ∀ Y : ℝ, Real.exp 1 ≤ Y →
      (∀ k : ℕ, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ + 1 → |p.eval (Real.log k / Real.log Y)| ≤ H) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ ⌊3 * Y⌋₊ →
        |p.eval (Real.log k / Real.log Y) - p.eval (Real.log ((k + 1 : ℕ) : ℝ) / Real.log Y)| ≤
          Λ / Real.log Y / k) ∧
      Λ / Real.log Y * ∑ k ∈ Finset.Icc 1 ⌊3 * Y⌋₊, 1 / (k : ℝ) ≤ 4 * Λ := by
  obtain ⟨H₀, hH₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  obtain ⟨Λ₀, hΛ₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    p.derivative.continuous.continuousOn
  refine ⟨max H₀ 0, max Λ₀ 0, le_max_right _ _, le_max_right _ _, fun Y hY => ?_⟩
  set H : ℝ := max H₀ 0 with hHdef
  set Λ : ℝ := max Λ₀ 0 with hΛdef
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
  have hY1 : 1 ≤ Y := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hY
  have hY0 : 0 < Y := by linarith
  set L : ℝ := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hY
  have hL0 : 0 < L := by linarith
  set M : ℕ := ⌊3 * Y⌋₊ with hM
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
  refine ⟨fun k hk1 hkM => hpH _ (hrange k hk1 hkM), fun k hk1 hkM => ?_, ?_⟩
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
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
    calc |p.eval (Real.log k / L) - p.eval (Real.log ((k + 1 : ℕ) : ℝ) / L)|
        ≤ Λ * |Real.log k / L - Real.log ((k + 1 : ℕ) : ℝ) / L| := h1
      _ ≤ Λ * (1 / (L * k)) := mul_le_mul_of_nonneg_left hdiff hΛ0
      _ = Λ / L / k := by field_simp
  · have hlogM : ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ 4 * L := by
      refine (sum_Icc_inv_le_one_add_log M).trans ?_
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · rw [hM0]; simp; linarith
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
      have h1 : Real.log M ≤ Real.log (3 * Y) :=
        Real.log_le_log (by linarith) (Nat.floor_le (by positivity))
      rw [Real.log_mul (by norm_num) hY0.ne'] at h1
      have hl3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
      linarith
    calc Λ / L * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ Λ / L * (4 * L) :=
          mul_le_mul_of_nonneg_left hlogM (by positivity)
      _ = 4 * Λ := by field_simp

/-- **Asymptotic orthogonality of polynomially log-weighted zero duals.**  For distinct zeros
`Re ρ = Re ρ' = ½`, `Im ρ, Im ρ' > 0` and real polynomials `p, p'`, the bilinear energy of
`p(log k/log Y)Re(k^{−ρ})ψ(k/Y)` and `p'(log k/log Y)Re(k^{−ρ'})ψ(k/Y)` is bounded above
uniformly in `Y ≥ e`. -/
theorem exists_bdDualBilin_polyLogDual_le_of_ne {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ ρ' : ℂ} (hre : ρ.re = 1 / 2) (hre' : ρ'.re = 1 / 2) (him : 0 < ρ.im)
    (him' : 0 < ρ'.im) (hne : ρ ≠ ρ') (p p' : Polynomial ℝ) :
    ∃ K₃ : ℝ, ∀ Y : ℝ, Real.exp 1 ≤ Y → ∀ K : ℕ,
      bdDualBilin (fun k => p.eval (Real.log k / Real.log Y) * (zeroSmoothDual ν ε ρ Y k).re)
        (fun k => p'.eval (Real.log k / Real.log Y) * (zeroSmoothDual ν ε ρ' Y k).re) K ≤ K₃ := by
  obtain ⟨H₁, Λ₁, hH₁, hΛ₁, hb₁⟩ := exists_polyLog_weight_bounds p
  obtain ⟨H₂, Λ₂, hH₂, hΛ₂, hb₂⟩ := exists_polyLog_weight_bounds p'
  set H : ℝ := H₁ + H₂ with hHdef
  set Λ : ℝ := Λ₁ + Λ₂ with hΛdef
  have hH0 : 0 ≤ H := by positivity
  have hΛ0 : 0 ≤ Λ := by positivity
  set R : ℝ := ‖ρ‖ + ‖ρ'‖ with hR
  set P : ℝ := H * R with hPdef
  set Q : ℝ := H * (R * (R + 1)) with hQdef
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have hPρ : H * ‖ρ‖ ≤ P := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg ρ']) hH0
  have hPρ' : H * ‖ρ'‖ ≤ P := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg ρ]) hH0
  have hQσ : ∀ σ : ℂ, ‖σ‖ ≤ R → H * (‖σ‖ * ‖σ + 1‖) ≤ Q := by
    intro σ hσ
    refine mul_le_mul_of_nonneg_left (mul_le_mul hσ ?_ (norm_nonneg _) (by positivity)) hH0
    have := norm_add_le σ 1
    rw [norm_one] at this
    linarith
  have hQρ := hQσ ρ (by linarith [norm_nonneg ρ'])
  have hQρ' := hQσ ρ' (by linarith [norm_nonneg ρ])
  obtain ⟨Lψ, hLψ0, hLψ⟩ := exists_abs_smooth1_sub_le hν νpos hε0
  have hs1 : (ρ + ρ').re = 1 := by simp [hre, hre']; norm_num
  have hs1' : ρ + ρ' ≠ 1 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hs2 : (ρ + conj ρ').re = 1 := by simp [hre, hre']; norm_num
  have hs2' : ρ + conj ρ' ≠ 1 := fun h => hne (by
    have := congrArg Complex.im h
    simp at this
    exact Complex.ext (by rw [hre, hre']) (by linarith))
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_sum_natCast_cpow_neg_le hs1 hs1'
  obtain ⟨B₂, hB₂0, hB₂⟩ := exists_norm_sum_natCast_cpow_neg_le hs2 hs2'
  set C : ℝ := (‖ρ * ρ'‖ * B₁ + ‖ρ * conj ρ'‖ * B₂) * (2 * H ^ 2 + 8 * H * Λ) with hC
  refine ⟨C + 2 * (2 * (P * Q + P * Q + Q * Q)) +
    (2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * Λ * H) +
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
  obtain ⟨hH₁Y, hL₁Y, hS₁Y⟩ := hb₁ Y hY
  obtain ⟨hH₂Y, hL₂Y, hS₂Y⟩ := hb₂ Y hY
  set h : ℕ → ℝ := fun k => p.eval (Real.log k / L) with hh
  set h' : ℕ → ℝ := fun k => p'.eval (Real.log k / L) with hh'
  have hhH : ∀ k, 1 ≤ k → k ≤ M + 1 → |h k| ≤ H := fun k hk1 hkM =>
    (hH₁Y k hk1 hkM).trans (by linarith)
  have hhH' : ∀ k, 1 ≤ k → k ≤ M + 1 → |h' k| ≤ H := fun k hk1 hkM =>
    (hH₂Y k hk1 hkM).trans (by linarith)
  have hdivk : ∀ (k : ℕ) (a : ℝ), 0 ≤ a → a ≤ Λ → a / L / k ≤ μ / k := by
    intro k a ha haΛ
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right haΛ hL0.le) (Nat.cast_nonneg k)
  have hhLip : ∀ k, 1 ≤ k → k ≤ M → |h k - h (k + 1)| ≤ μ / k := fun k hk1 hkM =>
    (hL₁Y k hk1 hkM).trans (hdivk k Λ₁ hΛ₁ (by linarith))
  have hhLip' : ∀ k, 1 ≤ k → k ≤ M → |h' k - h' (k + 1)| ≤ μ / k := fun k hk1 hkM =>
    (hL₂Y k hk1 hkM).trans (hdivk k Λ₂ hΛ₂ (by linarith))
  set S : ℝ := ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) with hSdef
  have hμS : μ * S ≤ 4 * Λ := by
    have := add_le_add hS₁Y hS₂Y
    rw [← add_mul, ← add_div] at this
    calc μ * S = (Λ₁ + Λ₂) / L * S := rfl
      _ ≤ 4 * Λ₁ + 4 * Λ₂ := this
      _ = 4 * Λ := by ring
  have hμ2S : μ ^ 2 * S ≤ 4 * Λ ^ 2 := by
    calc μ ^ 2 * S = μ * (μ * S) := by ring
      _ ≤ Λ * (4 * Λ) := mul_le_mul hμΛ hμS (by positivity) hΛ0
      _ = 4 * Λ ^ 2 := by ring
  have hsum := bdDualBilin_polyLogDual_le_sum hν νpos mass_one hε0 hε1 hre hre' hY1 hLψ hH0 hμ0
    hPρ hPρ' hQρ hQρ' hhH hhH' hhLip hhLip' K
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
  have hosc₁ := abs_sum_mul_mul_osc_le (c := ρ * ρ') hB₁ hH0 hμ0 hu0 hu1 huanti huzero hhH hhH'
    hhLip hhLip' K
  have hosc₂ := abs_sum_mul_mul_osc_le (c := ρ * conj ρ') hB₂ hH0 hμ0 hu0 hu1 huanti huzero hhH
    hhH' hhLip hhLip' K
  have hTV : 2 * H ^ 2 + 2 * H * μ * S ≤ 2 * H ^ 2 + 8 * H * Λ := by
    have : 2 * H * μ * S ≤ 8 * H * Λ := by
      calc 2 * H * μ * S = 2 * H * (μ * S) := by ring
        _ ≤ 2 * H * (4 * Λ) := mul_le_mul_of_nonneg_left hμS (by positivity)
        _ = 8 * H * Λ := by ring
    linarith
  have hoscle : ∑ k ∈ Finset.Icc 1 K, h k * h' k * u k *
      ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re + (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) ≤ C := by
    have hsplit : ∑ k ∈ Finset.Icc 1 K, h k * h' k * u k *
        ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re + (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) =
        ∑ k ∈ Finset.Icc 1 K, h k * h' k * u k * (ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
          ∑ k ∈ Finset.Icc 1 K, h k * h' k * u k *
            (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit]
    have a1 := (le_abs_self _).trans (hosc₁.trans (mul_le_mul_of_nonneg_left hTV
      (by positivity)))
    have a2 := (le_abs_self _).trans (hosc₂.trans (mul_le_mul_of_nonneg_left hTV
      (by positivity)))
    rw [hC, add_mul]
    linarith
  have hC₂le : 2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * μ * H ≤
      2 * (P + P + Q + Q) * H + 4 * H ^ 2 * Lψ + 4 * Λ * H := by
    have := mul_le_mul_of_nonneg_right hμΛ hH0
    linarith
  have hC₃le : (4 * μ * (P + Q) + 2 * μ ^ 2) * S ≤ 16 * Λ * (P + Q) + 8 * Λ ^ 2 := by
    have e : (4 * μ * (P + Q) + 2 * μ ^ 2) * S = 4 * (P + Q) * (μ * S) + 2 * (μ ^ 2 * S) := by
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hμS (by positivity : (0 : ℝ) ≤ 4 * (P + Q))
    linarith
  have hsum' : ∑ k ∈ Finset.Icc 1 K, h k * h' k * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 *
      (1 + 1 / (k : ℝ))) * ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
        (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) =
      ∑ k ∈ Finset.Icc 1 K, h k * h' k * u k *
        ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re + (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) :=
    rfl
  show bdDualBilin (fun k => h k * (zeroSmoothDual ν ε ρ Y k).re)
    (fun k => h' k * (zeroSmoothDual ν ε ρ' Y k).re) K ≤ _
  rw [hsum'] at hsum
  linarith only [hsum, hoscle, hC₂le, hC₃le]

end

end RHTower
