import GaloisForLFunctions.ZeroConfigurationGeometry.SymmetricHalvesArePhaseLattices

/-!
# Finite carriers are real above their horizon

Archimedean domination is blind to arithmetic. For any real coefficients `a(n)` and cutoff `X`,
the **finite carrier** `Λ_a(z) = A_a(z) + A_a(1 − z)`, with
`A_a(z) = Γ_ℝ(z) exp(Σ_{1 ≤ n ≤ X} a(n) n^{−z})` (`carrierHalf`), is a symmetric half. Its phase
speed is `Re L_a = Re ψ_ℝ − Re Σ a(n) log n · n^{−z}`. The archimedean part is
`½ log(|t|/2π) + O(1/|t|)`, and the arithmetic part is at most the weight
`W_a(X, u₀) = Σ |a(n)| log n (n^{−½} + n^{u₀−½})` (`re_carrierLogDeriv_ge`, `carrierWeight`).

* **Real above the horizon** (`carrier_ne_zero_near_line`). At heights `|t| ≥ 4` with
  `log(|t|/2π) > 6/|t| + W_a(X, u₀)`, `Λ_a` has no zero with `0 < |Re z − ½| ≤ u₀`.
* **Simple, lattice-like, counted** (`carrier_deriv_ne_zero`, `carrier_eq_zero_iff_phase`,
  `ncard_carrier_zeros`). Above `log(t₀/2π) > 6/t₀ + W_a(X, 0)`, the zeros on the line are simple,
  they form the phase lattice, and they number `⌊Re Θ(T)/π⌋ + 1` in `[t₀, T]` after a zero `t₀`.
* **Repulsion and density** (`carrier_ne_zero_of_lt_gap`, `exists_carrier_zero_within`). Above
  the horizon the gaps between consecutive zeros on the line lie between `π/M` and `π/m`, with
  `m, M = ½ log(t/2π) ∓ W_a/2` up to `O(1/t)`.
* **Euler depth** (`eulerDepth_ne_zero_near_line`, `eulerDepth_deriv_ne_zero`). For the prime
  weight `s ∈ [0, 1]`, i.e. `a = s Λ(n)/log n`, the weight is `s W_Λ`. At height `t` the
  deformation from the archimedean carrier `Γ_ℝ(z) + Γ_ℝ(1 − z)` (`s = 0`) to the finite Euler stage
  (`s = 1`) keeps the configuration near the line on the line and simple for every
  `s < (log(t/2π) − 6/t)/W_Λ`. Along the Euler depth this is the analogue of chain steps 1–3 of
  the heat descent: above the horizon the deformation has no collision.

The theorem holds for every real coefficient sequence: Euler data, flips, the finite truncations of
twins, Davenport–Heilbronn-type data. Domination therefore cannot be the ζ-specific step of an RH
route on its own. The horizon `2π e^{W_a}` is set by the size of the coefficients. It recedes to
infinity exactly when the weights `W_a(X)` are unbounded in `X`, as they are for the Euler data,
where `W_Λ(X, 0) = 2 Σ_{n ≤ X} Λ(n)/√n ≥ 2ψ(X)/√X`.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open _root_.RHTower

/-- The finite Dirichlet logarithm `Σ_{1 ≤ n ≤ X} a(n) n^{−z}`. -/
def carrierLog (a : ℕ → ℝ) (X : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, (a n : ℂ) * (n : ℂ) ^ (-z)

/-- The phase speed `ψ_ℝ(z) − Σ_{1 ≤ n ≤ X} a(n) log n · n^{−z}` of the carrier. -/
def carrierLogDeriv (a : ℕ → ℝ) (X : ℕ) (z : ℂ) : ℂ :=
  (Complex.digamma (z / 2) / 2 - (Real.log Real.pi : ℂ) / 2) -
    ∑ n ∈ Finset.Icc 1 X, ((a n * Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-z)

/-- The weight `W_a(X, u₀) = Σ_{1 ≤ n ≤ X} |a(n)| log n (n^{−½} + n^{u₀−½})`. -/
def carrierWeight (a : ℕ → ℝ) (X : ℕ) (u₀ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, |a n| * Real.log n * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + (n : ℝ) ^ (u₀ - 1 / 2))

theorem hasDerivAt_carrierLog (a : ℕ → ℝ) (X : ℕ) (z : ℂ) :
    HasDerivAt (carrierLog a X)
      (-∑ n ∈ Finset.Icc 1 X, ((a n * Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-z)) z := by
  unfold carrierLog
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show n ≠ 0 by omega)
  have h := ((hasDerivAt_neg z).const_cpow (c := (n : ℂ)) (Or.inl hn0)).const_mul (a n : ℂ)
  refine h.congr_deriv ?_
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  push_cast
  ring

theorem carrierLog_conj (a : ℕ → ℝ) (X : ℕ) (z : ℂ) :
    carrierLog a X (conj z) = conj (carrierLog a X z) := by
  unfold carrierLog
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Ne.symm Real.pi_ne_zero
  rw [← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- The finite carrier with coefficients `a` and cutoff `X`, as a symmetric half. -/
def carrierHalf (a : ℕ → ℝ) (X : ℕ) : SymmetricHalf where
  A z := Complex.Gammaℝ z * cexp (carrierLog a X z)
  L := carrierLogDeriv a X
  hasDerivAt z hz := by
    have h := (hasDerivAt_Gammaℝ_of_re_pos hz).mul (hasDerivAt_carrierLog a X z).cexp
    refine h.congr_deriv ?_
    unfold carrierLogDeriv
    ring
  ne_zero z hz := mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz) (Complex.exp_ne_zero _)
  conj_eq z := by
    show Complex.Gammaℝ (conj z) * cexp (carrierLog a X (conj z)) =
      conj (Complex.Gammaℝ z * cexp (carrierLog a X z))
    rw [Gammaℝ_conj, carrierLog_conj, Complex.exp_conj, map_mul]

/-! ### The phase speed -/

theorem re_carrier_term_le (a : ℕ → ℝ) {X n : ℕ} (hn : n ∈ Finset.Icc 1 X) (σ τ : ℝ) :
    |(((a n * Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + τ * I))).re| ≤
      |a n| * Real.log n * (n : ℝ) ^ (-σ) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hpos : 0 < n := by omega
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog,
    Complex.norm_natCast_cpow_of_pos hpos]
  simp

/-- Lower bound for the phase speed. -/
theorem re_carrierLogDeriv_ge (a : ℕ → ℝ) (X : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 4 ≤ |τ|) :
    (Real.log (|τ| / (2 * Real.pi)) - 6 / |τ|) / 2 -
        ∑ n ∈ Finset.Icc 1 X, |a n| * Real.log n * (n : ℝ) ^ (-σ) ≤
      (carrierLogDeriv a X ((σ : ℂ) + τ * I)).re := by
  unfold carrierLogDeriv
  have hdig := re_digamma_half_ge hσ hτ
  rw [Complex.sub_re, Complex.re_sum]
  have harch : (Complex.digamma (((σ : ℂ) + τ * I) / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re =
      (Complex.digamma (((σ : ℂ) + τ * I) / 2) - (Real.log Real.pi : ℂ)).re / 2 := by
    simp [Complex.sub_re]
    ring
  rw [harch]
  have hsum := Finset.sum_le_sum fun n (hn : n ∈ Finset.Icc 1 X) =>
    (le_abs_self _).trans (re_carrier_term_le a hn σ τ)
  linarith

theorem carrierWeight_ge (a : ℕ → ℝ) (X : ℕ) {u₀ w : ℝ} (hw0 : 0 ≤ w) (hwu : w ≤ u₀) :
    ∑ n ∈ Finset.Icc 1 X, |a n| * Real.log n * (n : ℝ) ^ (-(1 / 2 + w)) +
        ∑ n ∈ Finset.Icc 1 X, |a n| * Real.log n * (n : ℝ) ^ (-(1 / 2 - w)) ≤
      carrierWeight a X u₀ := by
  unfold carrierWeight
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) hlog)
  exact add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))

theorem carrierWeight_zero (a : ℕ → ℝ) (X : ℕ) : carrierWeight a X 0 =
    2 * ∑ n ∈ Finset.Icc 1 X, |a n| * Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [carrierWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [zero_sub]
  ring

/-! ### Real above the horizon -/

/-- **A finite carrier has no zero near the line above its horizon.** -/
theorem carrier_ne_zero_near_line (a : ℕ → ℝ) (X : ℕ) {u₀ t : ℝ} (hu₀ : u₀ < 1 / 2)
    (ht : 4 ≤ |t|) (hcrit : 6 / |t| + carrierWeight a X u₀ < Real.log (|t| / (2 * Real.pi)))
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀) :
    (carrierHalf a X).sym ((σ : ℂ) + t * I) ≠ 0 := by
  refine (carrierHalf a X).sym_ne_zero_near_line hu₀ (fun τ hτ w hw => ?_) hσ hσu
  have h1 := re_carrierLogDeriv_ge a X (σ := 1 / 2 + w) (τ := τ) (by linarith [hw.1])
    (by rw [hτ]; exact ht)
  have h2 := re_carrierLogDeriv_ge a X (σ := 1 / 2 - w) (τ := -τ) (by linarith [hw.2])
    (by rw [abs_neg, hτ]; exact ht)
  rw [abs_neg] at h2
  rw [hτ] at h1 h2
  have hW := carrierWeight_ge a X hw.1 hw.2
  show 0 < (carrierLogDeriv a X (((1 / 2 + w : ℝ) : ℂ) + τ * I)).re +
    (carrierLogDeriv a X (((1 / 2 - w : ℝ) : ℂ) + (-τ : ℝ) * I)).re
  linarith

/-- The phase speed on the line above the horizon. -/
theorem re_carrier_speed_ge (a : ℕ → ℝ) (X : ℕ) {τ : ℝ} (hτ : 4 ≤ |τ|) :
    (Real.log (|τ| / (2 * Real.pi)) - 6 / |τ| - carrierWeight a X 0) / 2 ≤
      ((carrierHalf a X).speed τ).re := by
  have h := re_carrierLogDeriv_ge a X (σ := 1 / 2) (τ := τ) (by norm_num) hτ
  show _ ≤ (carrierLogDeriv a X (linePt τ)).re
  rw [linePt, carrierWeight_zero]
  linarith

theorem carrier_speed_pos (a : ℕ → ℝ) (X : ℕ) {t₀ : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + carrierWeight a X 0 < Real.log (t₀ / (2 * Real.pi))) :
    ∀ τ, t₀ ≤ τ → 0 < ((carrierHalf a X).speed τ).re := fun τ hτ => by
  have hτa : 4 ≤ |τ| := by rw [abs_of_pos (by linarith)]; linarith
  have := re_carrier_speed_ge a X hτa
  have := horizon_mono ht₀ hτ
  linarith

/-- **Zeros on the line above the horizon are simple.** -/
theorem carrier_deriv_ne_zero (a : ℕ → ℝ) (X : ℕ) {t₀ t : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + carrierWeight a X 0 < Real.log (t₀ / (2 * Real.pi))) (ht : t₀ ≤ t)
    (h0 : (carrierHalf a X).sym (linePt t) = 0) :
    deriv (carrierHalf a X).sym (linePt t) ≠ 0 :=
  (carrierHalf a X).sym_deriv_ne_zero h0 (carrier_speed_pos a X ht₀ hhor t ht)

/-- **The phase lattice of a finite carrier.** -/
theorem carrier_eq_zero_iff_phase (a : ℕ → ℝ) (X : ℕ) {t₀ : ℝ}
    (h0 : (carrierHalf a X).sym (linePt t₀) = 0) (t : ℝ) :
    (carrierHalf a X).sym (linePt t) = 0 ↔
      ∃ k : ℤ, ((carrierHalf a X).phase t₀ t).re = k * Real.pi :=
  (carrierHalf a X).sym_eq_zero_iff_phase h0 t

/-- **The count of a finite carrier above its horizon.** -/
theorem ncard_carrier_zeros (a : ℕ → ℝ) (X : ℕ) {t₀ T : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + carrierWeight a X 0 < Real.log (t₀ / (2 * Real.pi)))
    (h0 : (carrierHalf a X).sym (linePt t₀) = 0) (hT : t₀ ≤ T) :
    {t ∈ Icc t₀ T | (carrierHalf a X).sym (linePt t) = 0}.ncard =
      ⌊((carrierHalf a X).phase t₀ T).re / Real.pi⌋₊ + 1 :=
  (carrierHalf a X).ncard_sym_zeros (carrier_speed_pos a X ht₀ hhor) h0 hT

/-- The archimedean part of the speed on the line is at most `(log((|τ|+1)/2π) + 6/|τ|)/2`. -/
theorem re_arch_line_le {τ : ℝ} (hτ : 4 ≤ |τ|) :
    (Complex.digamma (linePt τ / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re ≤
      (Real.log ((|τ| + 1) / (2 * Real.pi)) + 6 / |τ|) / 2 := by
  set z : ℂ := linePt τ / 2 with hz
  have hzre : 0 < z.re := by rw [hz, Complex.div_ofNat_re, linePt_re]; norm_num
  have hnorm_ge : |τ| / 2 ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rwa [hz, Complex.div_ofNat_im, linePt_im, abs_div, abs_two] at h
  have hnorm_le : ‖z‖ ≤ (|τ| + 1) / 2 := by
    have hl : ‖linePt τ‖ ≤ 1 / 2 + |τ| := by
      calc ‖linePt τ‖ ≤ ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
        _ = 1 / 2 + |τ| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [hz, norm_div, Complex.norm_two]
    linarith
  have hz2 : 2 ≤ ‖z‖ := by linarith
  have hst := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hz2
  have hdig : (Complex.digamma z).re ≤ Real.log ‖z‖ + 3 / ‖z‖ := by
    have := (Complex.re_le_norm (Complex.digamma z - Complex.log z)).trans hst
    rw [Complex.sub_re, Complex.log_re] at this
    linarith
  have hlog : Real.log ‖z‖ ≤ Real.log ((|τ| + 1) / 2) := Real.log_le_log (by linarith) hnorm_le
  have hinv : 3 / ‖z‖ ≤ 6 / |τ| := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hsplit : Real.log ((|τ| + 1) / (2 * Real.pi)) =
      Real.log ((|τ| + 1) / 2) - Real.log Real.pi := by
    rw [show (|τ| + 1) / (2 * Real.pi) = ((|τ| + 1) / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  have harch : (Complex.digamma (linePt τ / 2) / 2 - (Real.log Real.pi : ℂ) / 2).re =
      ((Complex.digamma z).re - Real.log Real.pi) / 2 := by
    rw [hz]; simp [Complex.sub_re]; ring
  rw [harch]
  linarith

/-- Upper bound for the phase speed on the line. -/
theorem re_carrier_speed_le (a : ℕ → ℝ) (X : ℕ) {τ : ℝ} (hτ : 4 ≤ |τ|) :
    ((carrierHalf a X).speed τ).re ≤
      (Real.log ((|τ| + 1) / (2 * Real.pi)) + 6 / |τ| + carrierWeight a X 0) / 2 := by
  show (carrierLogDeriv a X (linePt τ)).re ≤ _
  have harch := re_arch_line_le hτ
  have hprime : -(∑ n ∈ Finset.Icc 1 X,
      ((a n * Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-linePt τ)).re ≤
      ∑ n ∈ Finset.Icc 1 X, |a n| * Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have h := re_carrier_term_le a hn (1 / 2) τ
    rw [show ((((1 / 2 : ℝ) : ℂ) + τ * I)) = linePt τ from rfl] at h
    linarith [neg_abs_le (((a n * Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-linePt τ)).re]
  rw [carrierLogDeriv, Complex.sub_re, carrierWeight_zero]
  linarith

/-- **Repulsion: the gap after a zero is at least `π/M`.** Above the horizon of a finite carrier,
after a zero `t₀` on the line there is no zero at heights in `(t₀, t₀ + π/M)`, with
`M = (log((t₀ + 5)/2π) + 6/t₀ + W_a(X, 0))/2 + 1`. -/
theorem carrier_ne_zero_of_lt_gap (a : ℕ → ℝ) (X : ℕ) {t₀ t : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + carrierWeight a X 0 < Real.log (t₀ / (2 * Real.pi)))
    (h0 : (carrierHalf a X).sym (linePt t₀) = 0) (ht : t₀ < t)
    (hgap : t < t₀ + Real.pi /
      ((Real.log ((t₀ + 5) / (2 * Real.pi)) + 6 / t₀ + carrierWeight a X 0) / 2 + 1)) :
    (carrierHalf a X).sym (linePt t) ≠ 0 := by
  set M := (Real.log ((t₀ + 5) / (2 * Real.pi)) + 6 / t₀ + carrierWeight a X 0) / 2 + 1
    with hM
  have hW0 : 0 ≤ carrierWeight a X 0 := by
    rw [carrierWeight_zero]
    exact mul_nonneg two_pos.le (Finset.sum_nonneg fun n hn => mul_nonneg (mul_nonneg
      (abs_nonneg _) (Real.log_natCast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hlog5 : 0 < Real.log ((t₀ + 5) / (2 * Real.pi)) :=
    Real.log_pos ((one_lt_div (by positivity)).mpr (by nlinarith [Real.pi_lt_four]))
  have hM1 : 1 ≤ M := by
    have : 0 < 6 / t₀ := by positivity
    rw [hM]; linarith
  have hπM : Real.pi / M ≤ Real.pi := div_le_self Real.pi_pos.le hM1
  have hpos : ∀ τ ∈ Ioo t₀ t, 0 < ((carrierHalf a X).speed τ).re := fun τ hτ =>
    carrier_speed_pos a X ht₀ hhor τ hτ.1.le
  have hle : ∀ τ ∈ Icc t₀ t, ((carrierHalf a X).speed τ).re ≤ M := fun τ hτ => by
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos hτ0]; linarith [hτ.1]
    have h := re_carrier_speed_le a X hτa
    rw [abs_of_pos hτ0] at h
    have h1 : Real.log ((τ + 1) / (2 * Real.pi)) ≤ Real.log ((t₀ + 5) / (2 * Real.pi)) :=
      Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right (by linarith [hτ.2, Real.pi_lt_four]) (by positivity))
    have h2 : 6 / τ ≤ 6 / t₀ := div_le_div_of_nonneg_left (by norm_num) (by linarith) hτ.1
    rw [hM]; linarith
  refine (carrierHalf a X).sym_ne_zero_of_phase_lt h0 ht hpos ?_
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht.le
    ((carrierHalf a X).continuous_re_speed.intervalIntegrable _ _) intervalIntegrable_const hle
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hM0 : 0 < M := by linarith
  have : (t - t₀) * M < Real.pi := by
    have := (lt_div_iff₀ hM0).mp (show t - t₀ < Real.pi / M by linarith)
    linarith
  linarith

/-- **Density: every window of length `π/m` above the horizon contains a zero**, with
`m = (log(t₀/2π) − 6/t₀ − W_a(X, 0))/2 > 0`. -/
theorem exists_carrier_zero_within (a : ℕ → ℝ) (X : ℕ) {t₀ : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + carrierWeight a X 0 < Real.log (t₀ / (2 * Real.pi))) :
    ∃ τ ∈ Icc t₀ (t₀ + Real.pi /
      ((Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ - carrierWeight a X 0) / 2)),
      (carrierHalf a X).sym (linePt τ) = 0 := by
  set m := (Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ - carrierWeight a X 0) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hlen : 0 ≤ Real.pi / m := (div_pos Real.pi_pos hm0).le
  refine (carrierHalf a X).exists_sym_zero_of_phase_ge (by linarith) ?_
  have hge : ∀ τ ∈ Icc t₀ (t₀ + Real.pi / m), m ≤ ((carrierHalf a X).speed τ).re := fun τ hτ => by
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.1]
    have := re_carrier_speed_ge a X hτa
    have := horizon_mono ht₀ hτ.1
    rw [hm]; linarith
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by linarith)
    intervalIntegrable_const ((carrierHalf a X).continuous_re_speed.intervalIntegrable _ _) hge
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left,
    div_mul_cancel₀ _ hm0.ne'] at hint
  exact hint

/-! ### Euler depth -/

/-- The Euler data at depth `s`: `s Λ(n)/log n`. -/
def eulerDepthCoeff (s : ℝ) (n : ℕ) : ℝ := s * eulerStageCoeff n

theorem carrierWeight_eulerDepth (s : ℝ) (X : ℕ) (u₀ : ℝ) :
    carrierWeight (eulerDepthCoeff s) X u₀ = |s| * eulerStageWeight X u₀ := by
  rw [carrierWeight, eulerStageWeight, Finset.mul_sum]
  have hsplit : Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) := by
    ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, zero_mul, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hlog := eulerStageCoeff_mul_log n
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hcoef : 0 ≤ eulerStageCoeff n := by
    unfold eulerStageCoeff
    exact div_nonneg hΛ (Real.log_natCast_nonneg n)
  rw [eulerDepthCoeff, abs_mul, abs_of_nonneg hcoef, ← hlog]
  ring

/-- **Euler depth stays real near the line above its horizon.** For prime weight `s`, at heights
`|t| ≥ 4` with `log(|t|/2π) > 6/|t| + |s| W_Λ(X, u₀)`, the carrier `Γ_ℝ exp(s Σ Λ(n) n^{−z}/log n)`
symmetrized has no zero at height `t` with `0 < |Re z − ½| ≤ u₀`. -/
theorem eulerDepth_ne_zero_near_line (s : ℝ) (X : ℕ) {u₀ t : ℝ} (hu₀ : u₀ < 1 / 2)
    (ht : 4 ≤ |t|) (hcrit : 6 / |t| + |s| * eulerStageWeight X u₀ < Real.log (|t| / (2 * Real.pi)))
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀) :
    (carrierHalf (eulerDepthCoeff s) X).sym ((σ : ℂ) + t * I) ≠ 0 :=
  carrier_ne_zero_near_line _ X hu₀ ht (by rwa [carrierWeight_eulerDepth]) hσ hσu

/-- **Euler depth stays simple on the line above its horizon.** -/
theorem eulerDepth_deriv_ne_zero (s : ℝ) (X : ℕ) {t₀ t : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + |s| * eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi))) (ht : t₀ ≤ t)
    (h0 : (carrierHalf (eulerDepthCoeff s) X).sym (linePt t) = 0) :
    deriv (carrierHalf (eulerDepthCoeff s) X).sym (linePt t) ≠ 0 :=
  carrier_deriv_ne_zero _ X ht₀ (by rwa [carrierWeight_eulerDepth]) ht h0

end GaloisForLFunctions.ZeroConfigurationGeometry
