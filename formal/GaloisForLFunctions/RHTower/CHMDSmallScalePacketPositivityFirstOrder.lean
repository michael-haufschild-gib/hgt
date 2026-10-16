import GaloisForLFunctions.RHTower.CHMDKleinGordonEnergyPositivityAndOriginMaximum

/-!
# CHMD: Small-Scale Positivity of All First-Order Toeplitz Packets

The origin maximum of the causal wave `φ_Λ = cosineShiftFn Λ sechHalf` handled the two-point
difference packets. The same mechanism, Klein–Gordon energy positivity at every zero plus the finite
quartic mass, controls **every** finite Toeplitz packet at small scale.

For a packet `(t, c)` on `Fin N` and a scale `λ ≥ 0`, the scaled Toeplitz form is
$$T(\lambda) = \sum_{i,j} c_i c_j\,\varphi_\Lambda(\lambda (t_j - t_i)).$$

1. **Uniform second-order expansion of one mode** (`re_mul_one_sub_cos_expansion`): for every weight
   `w` and every `x` with `|Im x| ≤ 1/4`,
   `|Re(w(1 − cos x)) − Re(w x²)/2| ≤ 4 ‖w‖ ‖x‖⁴`, in both the Taylor regime `‖x‖ ≤ 1` and the crude
   regime `‖x‖ > 1`.
2. **First-order expansion of mean-zero packets** (`scaledForm_ge_of_sum_eq_zero`): if `Σ cᵢ = 0`
   and `λ` is at most `1/(4T + 4)` with `T = Σ |tᵢ|`, then
   $$T(\lambda) \ge \lambda^2 \Bigl(\sum_i c_i t_i\Bigr)^2 M_1 - 4\lambda^4 D\, Q,$$
   with `M₁ = Σ_ρ m_ρ Re(ρ_ρ² w_ρ)` the energy moment, `Q` the quartic mass and
   `D = Σ_{i,j} |cᵢ||cⱼ| (tⱼ − tᵢ)⁴`. The mechanism is the exact identity
   `Σ_{i,j} cᵢcⱼ (tⱼ − tᵢ)² = 2(Σ cᵢ)(Σ cᵢ tᵢ²) − 2(Σ cᵢ tᵢ)²`.
3. **Small-scale positivity** (`exists_scaledForm_nonneg`): for every packet with
   `Σ cᵢ ≠ 0` or `Σ cᵢ tᵢ ≠ 0` there is `λ₀ > 0` such that `T(λ) ≥ 0` for all `0 ≤ λ ≤ λ₀`,
   unconditionally. Packets with `Σ cᵢ ≠ 0` are handled by continuity at the origin (the form tends to
   `(Σ cᵢ)² φ_Λ(0)`), mean-zero packets with nonzero first moment by the expansion.

Thus the whole Toeplitz hierarchy of the causal wave is unconditionally positive at small scale on
every packet that is not degenerate to second order. The second-order degenerate packets
(`Σ cᵢ = Σ cᵢ tᵢ = 0`) are governed by the next moment `M₂` of the zero measure.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDSmallScale

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage15 RHTower.CHMDGrowthCollapse RHTower.CHMDEnergyPositivity

/-! ## Section 1: Uniform second-order expansion of one cosine mode -/

/-- `|Re(w(1 − cos x)) − Re(w x²)/2| ≤ 4 ‖w‖ ‖x‖⁴` whenever `|Im x| ≤ 1/4`. -/
theorem re_mul_one_sub_cos_expansion (w x : ℂ) (hx : |x.im| ≤ 1 / 4) :
    |(w * (1 - Complex.cos x)).re - (w * x ^ 2).re / 2| ≤ 4 * ‖w‖ * ‖x‖ ^ 4 := by
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  have hx4 : 0 ≤ ‖x‖ ^ 4 := by positivity
  rcases le_or_gt ‖x‖ 1 with h1 | h1
  · have hcb := Complex.cos_bound h1
    have e : (w * (1 - Complex.cos x)).re - (w * x ^ 2).re / 2 =
        -(w * (Complex.cos x - (1 - x ^ 2 / 2))).re := by
      have h : w * (Complex.cos x - (1 - x ^ 2 / 2)) =
          -(w * (1 - Complex.cos x)) + ((1 / 2 : ℝ) : ℂ) * (w * x ^ 2) := by push_cast; ring
      rw [h, Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul]; ring
    rw [e, abs_neg]
    calc |(w * (Complex.cos x - (1 - x ^ 2 / 2))).re|
        ≤ ‖w * (Complex.cos x - (1 - x ^ 2 / 2))‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * ‖Complex.cos x - (1 - x ^ 2 / 2)‖ := norm_mul _ _
      _ ≤ ‖w‖ * (‖x‖ ^ 4 * (5 / 96)) := mul_le_mul_of_nonneg_left hcb hw
      _ ≤ 4 * ‖w‖ * ‖x‖ ^ 4 := by nlinarith [mul_nonneg hw hx4]
  · have hcos : ‖Complex.cos x‖ ≤ 2 := by
      refine (norm_ccos_le_exp_abs_im _).trans ?_
      calc Real.exp |x.im| ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr hx
        _ ≤ 2 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos (1 / 4), sq_nonneg (Real.exp (1 / 4)),
            sq_nonneg (Real.exp (1 / 4) ^ 2 - 2)]
    have hA : |(w * (1 - Complex.cos x)).re| ≤ 3 * ‖w‖ := by
      calc |(w * (1 - Complex.cos x)).re| ≤ ‖w * (1 - Complex.cos x)‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖1 - Complex.cos x‖ := norm_mul _ _
        _ ≤ ‖w‖ * 3 := by
            apply mul_le_mul_of_nonneg_left _ hw
            calc ‖1 - Complex.cos x‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.cos x‖ := norm_sub_le _ _
              _ ≤ 1 + 2 := by rw [norm_one]; linarith
              _ = 3 := by norm_num
        _ = 3 * ‖w‖ := by ring
    have hB : |(w * x ^ 2).re / 2| ≤ ‖w‖ * ‖x‖ ^ 2 / 2 := by
      rw [abs_div, abs_two]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc |(w * x ^ 2).re| ≤ ‖w * x ^ 2‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖x‖ ^ 2 := by rw [norm_mul, norm_pow]
    have hx2 : ‖x‖ ^ 2 ≤ ‖x‖ ^ 4 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg (‖x‖ ^ 2 - 1)]
    have hx1 : 1 ≤ ‖x‖ ^ 4 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg (‖x‖ ^ 2 - 1)]
    calc |(w * (1 - Complex.cos x)).re - (w * x ^ 2).re / 2|
        ≤ |(w * (1 - Complex.cos x)).re| + |(w * x ^ 2).re / 2| := abs_sub _ _
      _ ≤ 3 * ‖w‖ + ‖w‖ * ‖x‖ ^ 2 / 2 := add_le_add hA hB
      _ ≤ 4 * ‖w‖ * ‖x‖ ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left hx1 hw, mul_le_mul_of_nonneg_left hx2 hw,
            mul_nonneg hw hx4]

/-! ## Section 2: Packet algebra -/

/-- The scaled Toeplitz form `Σ_{i,j} cᵢ cⱼ φ_Λ(λ(tⱼ − tᵢ))`. -/
def scaledForm {N : ℕ} (t c : Fin N → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * chmdWave (lam * (t j - t i))

/-- The quartic packet mass `Σ_{i,j} |cᵢ||cⱼ| (tⱼ − tᵢ)⁴`. -/
def packetQuartic {N : ℕ} (t c : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, |c i| * |c j| * (t j - t i) ^ 4

theorem packetQuartic_nonneg {N : ℕ} (t c : Fin N → ℝ) : 0 ≤ packetQuartic t c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- **The second-difference identity**: `Σ cᵢcⱼ(tⱼ − tᵢ)² = 2(Σ cᵢ)(Σ cᵢtᵢ²) − 2(Σ cᵢtᵢ)²`. -/
theorem sum_sum_mul_sq_sub {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j * (t j - t i) ^ 2) =
      2 * (∑ i, c i) * (∑ i, c i * t i ^ 2) - 2 * (∑ i, c i * t i) ^ 2 := by
  have e : ∀ i j, c i * c j * (t j - t i) ^ 2 =
      c i * (c j * t j ^ 2) - 2 * ((c i * t i) * (c j * t j)) + (c i * t i ^ 2) * c j := by
    intro i j; ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem sum_sum_mul_sq_sub_of_sum_eq_zero {N : ℕ} (t c : Fin N → ℝ) (h : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * (t j - t i) ^ 2) = -2 * (∑ i, c i * t i) ^ 2 := by
  rw [sum_sum_mul_sq_sub, h]; ring

theorem sum_sum_mul_const_of_sum_eq_zero {N : ℕ} (c : Fin N → ℝ) (h : ∑ i, c i = 0) (a : ℝ) :
    (∑ i, ∑ j, c i * c j * a) = 0 := by
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, h]
  simp

/-- `|tⱼ − tᵢ| ≤ 2 Σ |tₖ|`. -/
theorem abs_sub_le_two_mul_sum_abs {N : ℕ} (t : Fin N → ℝ) (i j : Fin N) :
    |t j - t i| ≤ 2 * ∑ k, |t k| := by
  have hi : |t i| ≤ ∑ k, |t k| := Finset.single_le_sum (fun k _ => abs_nonneg (t k)) (Finset.mem_univ i)
  have hj : |t j| ≤ ∑ k, |t k| := Finset.single_le_sum (fun k _ => abs_nonneg (t k)) (Finset.mem_univ j)
  calc |t j - t i| ≤ |t j| + |t i| := abs_sub _ _
    _ ≤ 2 * ∑ k, |t k| := by linarith

/-! ## Section 3: One-zero lower bound and the first-order expansion -/

/-- The per-zero packet sum. -/
def packetMode {N : ℕ} (t c : Fin N → ℝ) (lam : ℝ) (ρ : zetaZeroConfig.carrier) : ℝ :=
  ∑ i, ∑ j, c i * c j * (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re

theorem scaledForm_eq_tsum {N : ℕ} (t c : Fin N → ℝ) (lam : ℝ) :
    scaledForm t c lam =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * packetMode t c lam ρ := by
  unfold scaledForm packetMode
  have hs : ∀ i j : Fin N, Summable fun ρ : zetaZeroConfig.carrier =>
      c i * c j * ((zetaZeroConfig.mult ρ : ℝ) *
        (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re) :=
    fun i j => (summable_re_cosTerm (lam * (t j - t i))).mul_left _
  simp_rw [chmdWave_eq_tsum_re, ← tsum_mul_left]
  have h1 : ∀ i : Fin N, (∑ j, ∑' ρ : zetaZeroConfig.carrier, c i * c j * ((zetaZeroConfig.mult ρ : ℝ) *
        (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re)) =
      ∑' ρ : zetaZeroConfig.carrier, ∑ j, c i * c j * ((zetaZeroConfig.mult ρ : ℝ) *
        (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re) :=
    fun i => (Summable.tsum_finsetSum fun j _ => hs i j).symm
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
  refine tsum_congr fun ρ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **One-zero lower bound for a mean-zero packet** at scale `λ` with `λ · 2T ≤ 1/2`. -/
theorem packetMode_ge {N : ℕ} (t c : Fin N → ℝ) (h0 : ∑ i, c i = 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hT : lam * (2 * ∑ k, |t k|) ≤ 1 / 2) (ρ : zetaZeroConfig.carrier) :
    lam ^ 2 * (∑ i, c i * t i) ^ 2 * (kgFreq ρ ^ 2 * kgWeight ρ).re -
        4 * lam ^ 4 * packetQuartic t c * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4) ≤
      packetMode t c lam ρ := by
  set w := kgWeight ρ with hw
  set k := kgFreq ρ with hk
  -- rewrite each mode as `Re w − Re(w(1 − cos x))`
  have hmode : packetMode t c lam ρ =
      ∑ i, ∑ j, c i * c j * w.re -
        ∑ i, ∑ j, c i * c j * (w * (1 - Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * k))).re := by
    unfold packetMode
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub w, mul_one, Complex.sub_re, mul_comm (Complex.cos _) w]
    ring
  rw [hmode, sum_sum_mul_const_of_sum_eq_zero c h0, zero_sub]
  -- expansion of each mode
  have hexp : ∀ i j : Fin N,
      (w * (1 - Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * k))).re ≤
        lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2 +
          4 * ‖w‖ * (lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4) := by
    intro i j
    set x : ℂ := ((lam * (t j - t i) : ℝ) : ℂ) * k with hx
    have hxim : |x.im| ≤ 1 / 4 := by
      rw [hx, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
        abs_mul, abs_of_nonneg hlam]
      have h1 := abs_sub_le_two_mul_sum_abs t i j
      have h2 : |k.im| ≤ 1 / 2 := by rw [hk]; exact (abs_im_kgFreq_lt ρ).le
      have h3 : lam * |t j - t i| ≤ 1 / 2 := by
        calc lam * |t j - t i| ≤ lam * (2 * ∑ k, |t k|) :=
              mul_le_mul_of_nonneg_left h1 hlam
          _ ≤ 1 / 2 := hT
      have h4 : 0 ≤ lam * |t j - t i| := by positivity
      calc lam * |t j - t i| * |k.im| ≤ 1 / 2 * (1 / 2) :=
            mul_le_mul h3 h2 (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    have hb := re_mul_one_sub_cos_expansion w x hxim
    have hx2 : (w * x ^ 2).re = lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re := by
      rw [hx, show (((lam * (t j - t i) : ℝ) : ℂ) * k) ^ 2 =
        (((lam ^ 2 * (t j - t i) ^ 2 : ℝ) : ℂ)) * k ^ 2 by push_cast; ring,
        mul_comm w, mul_assoc, Complex.re_ofReal_mul]
    have hxn : ‖x‖ ^ 4 = lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4 := by
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (lam * (t j - t i)) ^ 4)]
      ring
    rw [hx2, hxn] at hb
    have := (abs_le.mp hb).2
    linarith
  -- sum the expansions with the signed coefficients
  have hsum : ∑ i, ∑ j, c i * c j * (w * (1 - Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * k))).re ≤
      ∑ i, ∑ j, (c i * c j * (lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2) +
        |c i| * |c j| * (4 * ‖w‖ * (lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4))) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    set x : ℂ := ((lam * (t j - t i) : ℝ) : ℂ) * k with hx
    have hxim : |x.im| ≤ 1 / 4 := by
      rw [hx, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
        abs_mul, abs_of_nonneg hlam]
      have h1 := abs_sub_le_two_mul_sum_abs t i j
      have h2 : |k.im| ≤ 1 / 2 := by rw [hk]; exact (abs_im_kgFreq_lt ρ).le
      have h3 : lam * |t j - t i| ≤ 1 / 2 := by
        calc lam * |t j - t i| ≤ lam * (2 * ∑ k, |t k|) :=
              mul_le_mul_of_nonneg_left h1 hlam
          _ ≤ 1 / 2 := hT
      have h4 : 0 ≤ lam * |t j - t i| := by positivity
      calc lam * |t j - t i| * |k.im| ≤ 1 / 2 * (1 / 2) :=
            mul_le_mul h3 h2 (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    have hb := re_mul_one_sub_cos_expansion w x hxim
    have hx2 : (w * x ^ 2).re = lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re := by
      rw [hx, show (((lam * (t j - t i) : ℝ) : ℂ) * k) ^ 2 =
        (((lam ^ 2 * (t j - t i) ^ 2 : ℝ) : ℂ)) * k ^ 2 by push_cast; ring,
        mul_comm w, mul_assoc, Complex.re_ofReal_mul]
    have hxn : ‖x‖ ^ 4 = lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4 := by
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (lam * (t j - t i)) ^ 4)]
      ring
    rw [hx2, hxn] at hb
    -- `c i * c j * r ≤ c i * c j * q + |c i||c j| * e` from `|r − q| ≤ e`
    have hab := abs_le.mp hb
    have hcc : |c i * c j| = |c i| * |c j| := abs_mul _ _
    have h5 : c i * c j * ((w * (1 - Complex.cos x)).re - lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2) ≤
        |c i * c j| * (4 * ‖w‖ * (lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4)) := by
      calc c i * c j * ((w * (1 - Complex.cos x)).re - lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2)
          ≤ |c i * c j * ((w * (1 - Complex.cos x)).re -
              lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2)| := le_abs_self _
        _ = |c i * c j| * |(w * (1 - Complex.cos x)).re -
              lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2| := abs_mul _ _
        _ ≤ |c i * c j| * (4 * ‖w‖ * (lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4)) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    rw [hcc] at h5
    linarith
  -- evaluate the right-hand side
  have hrhs : ∑ i, ∑ j, (c i * c j * (lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re / 2) +
        |c i| * |c j| * (4 * ‖w‖ * (lam ^ 4 * (t j - t i) ^ 4 * ‖k‖ ^ 4))) =
      lam ^ 2 * (k ^ 2 * w).re / 2 * (∑ i, ∑ j, c i * c j * (t j - t i) ^ 2) +
        4 * lam ^ 4 * packetQuartic t c * (‖w‖ * ‖k‖ ^ 4) := by
    unfold packetQuartic
    simp_rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
  rw [hrhs, sum_sum_mul_sq_sub_of_sum_eq_zero t c h0] at hsum
  linarith

/-- **First-order expansion of a mean-zero packet**: for `Σ cᵢ = 0` and `λ · 2T ≤ 1/2`,
`T(λ) ≥ λ² (Σ cᵢtᵢ)² M₁ − 4 λ⁴ D Q`. -/
theorem scaledForm_ge_of_sum_eq_zero {N : ℕ} (t c : Fin N → ℝ) (h0 : ∑ i, c i = 0) {lam : ℝ}
    (hlam : 0 ≤ lam) (hT : lam * (2 * ∑ k, |t k|) ≤ 1 / 2) :
    lam ^ 2 * (∑ i, c i * t i) ^ 2 * kgEnergyMoment -
        4 * lam ^ 4 * packetQuartic t c * kgQuarticMass ≤ scaledForm t c lam := by
  rw [scaledForm_eq_tsum]
  have hA : Summable fun ρ : zetaZeroConfig.carrier =>
      lam ^ 2 * (∑ i, c i * t i) ^ 2 * kgEnergyTerm ρ := summable_kgEnergyTerm.mul_left _
  have hB : Summable fun ρ : zetaZeroConfig.carrier =>
      4 * lam ^ 4 * packetQuartic t c *
        ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4)) :=
    summable_quartic.mul_left _
  have hsum : lam ^ 2 * (∑ i, c i * t i) ^ 2 * kgEnergyMoment -
      4 * lam ^ 4 * packetQuartic t c * kgQuarticMass =
      ∑' ρ : zetaZeroConfig.carrier,
        (lam ^ 2 * (∑ i, c i * t i) ^ 2 * kgEnergyTerm ρ -
          4 * lam ^ 4 * packetQuartic t c *
            ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4))) := by
    unfold kgEnergyMoment kgQuarticMass
    rw [← tsum_mul_left, ← tsum_mul_left, hA.tsum_sub hB]
  rw [hsum]
  -- the summable majorant of the packet modes
  have hmode_summable : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * packetMode t c lam ρ := by
    have : ∀ i j : Fin N, Summable fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * (c i * c j *
          (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re) :=
      fun i j => ((summable_re_cosTerm (lam * (t j - t i))).mul_left (c i * c j)).congr
        fun ρ => by ring
    have h2 : Summable fun ρ : zetaZeroConfig.carrier => ∑ i, ∑ j,
        (zetaZeroConfig.mult ρ : ℝ) * (c i * c j *
          (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re) :=
      summable_sum fun i _ => summable_sum fun j _ => this i j
    refine h2.congr fun ρ => ?_
    unfold packetMode
    simp_rw [Finset.mul_sum]
  refine Summable.tsum_le_tsum (fun ρ => ?_) (hA.sub hB) hmode_summable
  have h := packetMode_ge t c h0 hlam hT ρ
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h hm
  unfold kgEnergyTerm
  linarith

/-! ## Section 4: Small-scale positivity of all first-order packets -/

theorem scaledForm_zero {N : ℕ} (t c : Fin N → ℝ) :
    scaledForm t c 0 = (∑ i, c i) ^ 2 * chmdWave 0 := by
  unfold scaledForm
  simp only [zero_mul]
  rw [sq, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]

theorem continuous_scaledForm {N : ℕ} (t c : Fin N → ℝ) : Continuous (scaledForm t c) := by
  unfold scaledForm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (continuous_chmdWave.comp (continuous_id.mul continuous_const))

theorem chmdWave_zero_pos [Nonempty zetaZeroConfig.carrier] : 0 < chmdWave 0 := by
  rw [chmdWave_eq_tsum_re]
  let ρ₀ : zetaZeroConfig.carrier := Classical.arbitrary _
  have hs := summable_re_cosTerm 0
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      0 ≤ (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re := by
    intro ρ
    have : Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) = 1 := by simp
    rw [this, one_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (re_kgWeight_pos ρ).le
  have h := hs.le_tsum ρ₀ (fun ρ _ => hterm ρ)
  have hpos : 0 < (zetaZeroConfig.mult ρ₀ : ℝ) *
      (Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ₀) * kgWeight ρ₀).re := by
    have : Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ₀) = 1 := by simp
    rw [this, one_mul]
    have h1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ ρ₀.2
    exact mul_pos (by linarith) (re_kgWeight_pos ρ₀)
  linarith

/-- **Small-scale positivity of every first-order packet**: if `Σ cᵢ ≠ 0` or `Σ cᵢ tᵢ ≠ 0`, the
scaled Toeplitz form of the causal wave is nonnegative for all sufficiently small scales. -/
theorem exists_scaledForm_nonneg {N : ℕ} (t c : Fin N → ℝ)
    (h : (∑ i, c i) ≠ 0 ∨ (∑ i, c i * t i) ≠ 0) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lam₀ → 0 ≤ scaledForm t c lam := by
  rcases isEmpty_or_nonempty zetaZeroConfig.carrier with hempty | hne
  · -- no zeros at all: the wave vanishes identically
    refine ⟨1, one_pos, fun lam _ _ => ?_⟩
    unfold scaledForm
    simp [chmdWave_eq_zero_of_isEmpty]
  · haveI := hne
    by_cases hS : (∑ i, c i) = 0
    · -- mean-zero packet with nonzero first moment: the first-order expansion
      have hM : (∑ i, c i * t i) ≠ 0 := by
        rcases h with h | h
        · exact absurd hS h
        · exact h
      have hMpos : 0 < kgEnergyMoment := kgEnergyMoment_pos
      have hD0 : 0 ≤ packetQuartic t c := packetQuartic_nonneg t c
      have hQ0 : 0 ≤ kgQuarticMass := kgQuarticMass_nonneg
      have hSpos : 0 < (∑ i, c i * t i) ^ 2 := by positivity
      have hT0 : 0 ≤ ∑ k, |t k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      set M : ℝ := kgEnergyMoment with hMdef
      set D : ℝ := packetQuartic t c with hDdef
      set Q : ℝ := kgQuarticMass with hQdef
      set S : ℝ := (∑ i, c i * t i) ^ 2 with hSdef
      set T : ℝ := ∑ k, |t k| with hTdef
      refine ⟨min (1 / (4 * T + 4)) (Real.sqrt (S * M / (4 * (D + 1) * (Q + 1)))),
        lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity)), fun lam hl0 hl => ?_⟩
      have hl1 : lam ≤ 1 / (4 * T + 4) := hl.trans (min_le_left _ _)
      have hl2 : lam ≤ Real.sqrt (S * M / (4 * (D + 1) * (Q + 1))) := hl.trans (min_le_right _ _)
      have hT : lam * (2 * T) ≤ 1 / 2 := by
        calc lam * (2 * T) ≤ 1 / (4 * T + 4) * (2 * T) := by gcongr
          _ ≤ 1 / 2 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
      have hmain := scaledForm_ge_of_sum_eq_zero t c hS hl0 hT
      have hl2' : lam ^ 2 ≤ S * M / (4 * (D + 1) * (Q + 1)) := by
        have := pow_le_pow_left₀ hl0 hl2 2
        rwa [Real.sq_sqrt (by positivity)] at this
      have hkey : 0 ≤ lam ^ 2 * S * M - 4 * lam ^ 4 * D * Q := by
        have h2 : 4 * lam ^ 2 * (D * Q) ≤ S * M * (D * Q / ((D + 1) * (Q + 1))) := by
          calc 4 * lam ^ 2 * (D * Q) ≤ 4 * (S * M / (4 * (D + 1) * (Q + 1))) * (D * Q) := by
                gcongr
            _ = S * M * (D * Q / ((D + 1) * (Q + 1))) := by field_simp
        have h3 : D * Q / ((D + 1) * (Q + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith
        have h4 : S * M * (D * Q / ((D + 1) * (Q + 1))) ≤ S * M :=
          mul_le_of_le_one_right (by positivity) h3
        have h5 : 4 * lam ^ 4 * D * Q = lam ^ 2 * (4 * lam ^ 2 * (D * Q)) := by ring
        rw [h5]
        nlinarith [mul_le_mul_of_nonneg_left (h2.trans h4) (sq_nonneg lam)]
      linarith
    · -- `Σ cᵢ ≠ 0`: continuity at the origin
      have hpos : 0 < scaledForm t c 0 := by
        rw [scaledForm_zero]
        exact mul_pos (by positivity) chmdWave_zero_pos
      have hcont := (continuous_scaledForm t c).continuousAt (x := 0)
      obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hcont (scaledForm t c 0) hpos
      refine ⟨δ / 2, by positivity, fun lam hl0 hl => ?_⟩
      have hd : dist lam 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hl0]; linarith
      have := hδf hd
      rw [Real.dist_eq] at this
      have := (abs_lt.mp this).1
      linarith

end RHTower.CHMDSmallScale

end
