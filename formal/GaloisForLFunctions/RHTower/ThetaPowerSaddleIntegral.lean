import GaloisForLFunctions.RHTower.ThetaPowerSaddleFarField
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Finitely many critical zeros above the cusp-order wall

For `a > 1/2` the transform `Λ_a(u) = ∫ e^{-iux} T_a(x) dx` of `F_a = θ₃h^{a/4}` equals
`e^{-uβ} ∫ e^{-ius} T_a(s - iβ) ds` on every line `Im z = -β`, and at the saddle frequency
`u = mπ/(8t⁴)`, `m = 2a - 1`, the line integral has real part at least `g₀t³/(32K)`, `K = a + 1`:

* the inner window `|s| ≤ t³/(4K)` contributes at least `g₀t³/(8K)`;
* on the core `|s| ≤ Λt³`, `Λ = 1008K/m + 1`, the integrand has positive real part;
* between the core and `2t²` the Gaussian law `R₀ - Re ψ ≥ ms²/(28t⁶)` costs at most `g₀t³/(16K)`;
* beyond `2t²` the Farey far field is `≤ 36^a κ⁻³ e^{R₀/3}`, negligible against `e^{R₀}`.

Every large `u` is a saddle frequency, so `Λ_a(u) ≠ 0` for `u ≥ U`; the transform is even and
extends holomorphically to `|Im w| < 1`, hence its real zeros are finite.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower

noncomputable section

section LineA

variable {a t : ℝ}

theorem continuous_chLineA (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) :
    Continuous (chLineA a t) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  have hc := continuousOn_chargeTailC (differentiableOn_thetaPowerForm a) hβ
  have h1 : Continuous (fun s : ℝ => (s : ℂ) - (chBeta t : ℂ) * Complex.I) := by fun_prop
  have h2 := hc.comp_continuous h1 (fun s => by simp [abs_of_nonneg hβ0])
  unfold chLineA
  exact (by fun_prop : Continuous fun s : ℝ =>
    Complex.exp (-Complex.I * chUm (chMa a) t * s)).mul h2

theorem norm_chLineA (a t s : ℝ) :
    ‖chLineA a t s‖ =
      ‖chargeTailC (thetaPowerForm a) ((s : ℂ) - (chBeta t : ℂ) * Complex.I)‖ := by
  unfold chLineA; rw [norm_mul, Complex.norm_exp]
  have : (-Complex.I * (chUm (chMa a) t : ℂ) * (s : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero, one_mul]

theorem integrable_chLineA (ha : 0 < a) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) :
    Integrable (chLineA a t) := by
  have hβ := chBeta_lt ht (by linarith)
  have hβ0 := chBeta_nonneg ht2
  obtain ⟨C, _, hbd⟩ := thetaPowerTail_decay ha (chBeta t) hβ0 hβ
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' one_pos).const_mul C)
    (continuous_chLineA ht ht2).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have hz : |((s : ℂ) - (chBeta t : ℂ) * Complex.I).im| ≤ chBeta t := by
    simp [abs_of_nonneg hβ0]
  have h := hbd _ hz
  have hre : ((s : ℂ) - (chBeta t : ℂ) * Complex.I).re = s := by simp
  rw [hre] at h
  rw [norm_chLineA]
  simpa using h

/-- The saddle-line integral of `F_a`. -/
def chLineAInt (a t : ℝ) : ℂ := ∫ s : ℝ, chLineA a t s

/-- The core radius `Λ = 1008K/m + 1`. -/
def chLamA (a : ℝ) : ℝ := 1008 * (a + 1) / chMa a + 1

theorem chMa_pos (ha : 1 / 2 < a) : 0 < chMa a := by unfold chMa; linarith

theorem one_le_chLamA (ha : 1 / 2 < a) : 1 ≤ chLamA a := by
  unfold chLamA; have := chMa_pos ha; have : 0 ≤ 1008 * (a + 1) / chMa a := by
    have : 0 ≤ a + 1 := by linarith
    positivity
  linarith

theorem chMa_le (ha : 0 ≤ a) : chMa a ≤ 8 * (a + 1) := by unfold chMa; linarith

theorem chLineA_re_ge_inner (ha : 1 / 2 < a) (h : chSmallA a t)
    (hcore : t * (176 * (a + 1) * chLamA a ^ 3) ≤ 1) {s : ℝ} (hs : |s| ≤ t ^ 3 / (4 * (a + 1))) :
    chG0a a t / 4 ≤ (chLineA a t s).re := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have ht1 : t ≤ 1 := by linarith [h.le ha0]
  have hK : 1 ≤ a + 1 := by linarith
  have hΛ := one_le_chLamA ha
  have hsΛ : |s| ≤ chLamA a * t ^ 3 := by
    have ht3 : 0 < t ^ 3 := by positivity
    have h1 : t ^ 3 / (4 * (a + 1)) ≤ t ^ 3 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have h2 : t ^ 3 ≤ chLamA a * t ^ 3 := le_mul_of_one_le_left ht3.le hΛ
    linarith
  have h1 := half_le_re_chLineA_core ha h hK (chMa_le ha0) hΛ hcore hsΛ
  have hd := chR0m_sub_psim_re_le_inner_real ht0 ht1 hK (chMa_pos ha).le (chMa_le ha0) hs
  have he : 1 / 2 ≤ Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) := by
    have := Real.add_one_le_exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t); linarith
  have hG := chG0a_pos a t
  have h2 := mul_le_mul_of_nonneg_left he hG.le
  linarith

theorem chLineA_re_ge_mid (ha : 1 / 2 < a) (h : chSmallA a t) {s : ℝ}
    (hΛs : chLamA a * t ^ 3 ≤ |s|) (h2 : |s| ≤ 2 * t ^ 2) :
    -(9 / 8 * chG0a a t * Real.exp (-(chMa a * chLamA a / (28 * t ^ 3) * |s|))) ≤
      (chLineA a t s).re := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have hm := chMa_pos ha
  have hw := norm_chLineA_le_window ha0 h h2
  have hmid := chR0m_sub_psim_re_ge_mid_real hm ht0 (by nlinarith [h.t2 ha0]) h2
  have hk : chMa a * chLamA a / (28 * t ^ 3) * |s| ≤ chMa a * s ^ 2 / (28 * t ^ 6) := by
    have e : chMa a * chLamA a / (28 * t ^ 3) * |s| =
        chMa a * (chLamA a * t ^ 3 * |s|) / (28 * t ^ 6) := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hm.le
    rw [← sq_abs s, sq]
    exact mul_le_mul_of_nonneg_right hΛs (abs_nonneg s)
  have hexp : Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) ≤
      Real.exp (-(chMa a * chLamA a / (28 * t ^ 3) * |s|)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hG := chG0a_pos a t
  have hn : ‖chLineA a t s‖ ≤ 9 / 8 * chG0a a t *
      Real.exp (-(chMa a * chLamA a / (28 * t ^ 3) * |s|)) := by
    refine le_trans hw ?_
    have := mul_le_mul_of_nonneg_left hexp (by positivity : (0:ℝ) ≤ 9 / 8 * chG0a a t)
    linarith
  have := Complex.abs_re_le_norm (chLineA a t s)
  have := neg_abs_le (chLineA a t s).re
  linarith

theorem chLineA_re_ge_far (ha : 1 / 2 < a) (h : chSmallA a t) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaPowerForm a τ‖ ≤ M * Real.exp (-(π * a / 4) * τ.im))
    {s : ℝ} (h2 : 2 * t ^ 2 ≤ |s|) :
    -(chBfarA a t M * Real.exp (-|s|)) ≤ (chLineA a t s).re := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have ht4 : t ^ 4 ≤ 1 / 6 := by nlinarith [h.t2 ha0, pow_pos ht0 2]
  have hf := norm_chargeTailA_far ha ht0 ht4 hM h2
  rw [← norm_chLineA] at hf
  have := Complex.abs_re_le_norm (chLineA a t s)
  have := neg_abs_le (chLineA a t s).re
  linarith

/-- **Lower bound for the saddle-line integral.** -/
theorem re_chLineAInt_ge (ha : 1 / 2 < a) (h : chSmallA a t)
    (hcore : t * (176 * (a + 1) * chLamA a ^ 3) ≤ 1) {M : ℝ}
    (hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaPowerForm a τ‖ ≤ M * Real.exp (-(π * a / 4) * τ.im)) :
    chG0a a t * t ^ 3 / (16 * (a + 1)) - 2 * chBfarA a t M ≤ (chLineAInt a t).re := by
  have ha0 : 0 ≤ a := by linarith
  have ht0 := h.1
  have ht2' : t ^ 2 ≤ 1 / 2 := by linarith [h.t2 ha0]
  have hm := chMa_pos ha
  have hK : 0 < a + 1 := by linarith
  have hΛ := one_le_chLamA ha
  have hG := chG0a_pos a t
  have hint := integrable_chLineA (a := a) (by linarith) ht0 ht2'
  have hre_int : Integrable (fun s => (chLineA a t s).re) := hint.re
  set ι : ℝ := t ^ 3 / (4 * (a + 1)) with hι
  have hι0 : 0 ≤ ι := by positivity
  set k : ℝ := chMa a * chLamA a / (28 * t ^ 3) with hk
  have hk0 : 0 < k := by positivity
  set B : ℝ := chBfarA a t M with hBdef
  have hBf : 0 ≤ B := chBfarA_nonneg ht0 (by nlinarith [pow_pos ht0 2]) M
  set lam : ℝ → ℝ := fun s =>
    9 / 8 * chG0a a t * Real.exp (-(k * |s|)) + B * Real.exp (-(1 * |s|)) with hlam
  have hlam_int : Integrable lam :=
    ((integrable_exp_neg_mul_abs' hk0).const_mul _).add
      ((integrable_exp_neg_mul_abs' one_pos).const_mul _)
  have hlam_val : ∫ s, lam s = 63 * chG0a a t * t ^ 3 / (chMa a * chLamA a) + 2 * B := by
    rw [hlam, integral_add ((integrable_exp_neg_mul_abs' hk0).const_mul _)
      ((integrable_exp_neg_mul_abs' one_pos).const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_abs_eq hk0, integral_exp_neg_mul_abs_eq one_pos, hk]
    field_simp; ring
  have hlamsmall : 63 * chG0a a t * t ^ 3 / (chMa a * chLamA a) ≤
      chG0a a t * t ^ 3 / (16 * (a + 1)) := by
    have e : chMa a * chLamA a = 1008 * (a + 1) + chMa a := by
      unfold chLamA; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hGt : 0 ≤ chG0a a t * t ^ 3 := by positivity
    nlinarith
  have hout : ∀ s, -lam s ≤ (chLineA a t s).re := by
    intro s
    have hl1 : 0 ≤ 9 / 8 * chG0a a t * Real.exp (-(k * |s|)) := by positivity
    have hl2 : 0 ≤ B * Real.exp (-(1 * |s|)) := by positivity
    simp only [hlam, one_mul]
    rcases le_or_gt |s| (chLamA a * t ^ 3) with h1 | h1
    · have h3 := half_le_re_chLineA_core ha h (by linarith) (chMa_le ha0) hΛ hcore h1
      have : 0 ≤ chG0a a t * Real.exp ((chPsim (chMa a) t s).re - chR0m (chMa a) t) / 2 := by
        positivity
      rw [one_mul] at hl2
      linarith
    rcases le_or_gt |s| (2 * t ^ 2) with h2 | h2
    · have h3 := chLineA_re_ge_mid ha h h1.le h2
      rw [one_mul] at hl2
      linarith
    · have h3 := chLineA_re_ge_far ha h hM h2.le
      linarith
  have hsplit := integral_add_compl (μ := volume) measurableSet_Icc hre_int (s := Icc (-ι) ι)
  unfold chLineAInt
  have hre_eq : (∫ s, chLineA a t s).re = ∫ s, (chLineA a t s).re := (integral_re hint).symm
  rw [hre_eq, ← hsplit]
  have hA : chG0a a t / 4 * (2 * ι) ≤ ∫ s in Icc (-ι) ι, (chLineA a t s).re := by
    have hc : ∫ s in Icc (-ι) ι, (chG0a a t / 4 : ℝ) = chG0a a t / 4 * (2 * ι) := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
      ring
    rw [← hc]
    exact setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
      hre_int.integrableOn measurableSet_Icc
      (fun s hs => chLineA_re_ge_inner ha h hcore (abs_le.mpr ⟨hs.1, hs.2⟩))
  have hB : -(∫ s, lam s) ≤ ∫ s in (Icc (-ι) ι)ᶜ, (chLineA a t s).re := by
    have h1 : ∫ s in (Icc (-ι) ι)ᶜ, -lam s ≤ ∫ s in (Icc (-ι) ι)ᶜ, (chLineA a t s).re :=
      setIntegral_mono_on hlam_int.neg.integrableOn hre_int.integrableOn
        measurableSet_Icc.compl (fun s _ => hout s)
    have h2 : ∫ s in (Icc (-ι) ι)ᶜ, lam s ≤ ∫ s, lam s :=
      setIntegral_le_integral hlam_int (Filter.Eventually.of_forall fun s => by
        simp only [hlam]; positivity)
    rw [integral_neg] at h1
    linarith
  rw [hlam_val] at hB
  have e : chG0a a t / 4 * (2 * ι) = 2 * (chG0a a t * t ^ 3 / (16 * (a + 1))) := by
    rw [hι]; field_simp; ring
  linarith

/-! ## The far field is negligible -/

theorem far_one_real {A c μ t κ R : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hκ : t ^ 2 ≤ κ) (hμ : 0 < μ)
    (hRt : μ ≤ R * t ^ 2) (hA : 0 ≤ A) (hc : 0 < c)
    (htQ : t * (720 * A / (c * (2 * μ / 3) ^ 6)) ≤ 1) :
    A * κ⁻¹ ^ 3 * Real.exp (R / 3) ≤ c * Real.exp R * t ^ 3 := by
  have ht2p : 0 < t ^ 2 := by positivity
  have hκ0 : 0 < κ := lt_of_lt_of_le ht2p hκ
  have hR0 : 0 ≤ R := by
    by_contra hn; push Not at hn; nlinarith
  have hinv : κ⁻¹ ≤ 1 / t ^ 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le ht2p hκ
  have hinv3 : κ⁻¹ ^ 3 ≤ (1 / t ^ 2) ^ 3 := pow_le_pow_left₀ (inv_nonneg.mpr hκ0.le) hinv 3
  have hsplit : Real.exp R = Real.exp (R / 3) * Real.exp (2 * R / 3) := by
    rw [← Real.exp_add]; ring_nf
  set ν : ℝ := (2 * μ / 3) ^ 6 with hν
  have hνpos : 0 < ν := by positivity
  have hE : ν / 720 ≤ t ^ 12 * Real.exp (2 * R / 3) := by
    have hA6 := pow_six_div_le_exp (x := 2 * R / 3) (by positivity)
    have h6 : ν ≤ (2 * R / 3) ^ 6 * t ^ 12 := by
      have e : (2 * R / 3) ^ 6 * t ^ 12 = (2 / 3 * (R * t ^ 2)) ^ 6 := by ring
      rw [e, hν]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have h7 := mul_le_mul_of_nonneg_right hA6 (by positivity : (0:ℝ) ≤ t ^ 12)
    calc ν / 720 ≤ (2 * R / 3) ^ 6 * t ^ 12 / 720 := by gcongr
      _ = (2 * R / 3) ^ 6 / 720 * t ^ 12 := by ring
      _ ≤ Real.exp (2 * R / 3) * t ^ 12 := h7
      _ = t ^ 12 * Real.exp (2 * R / 3) := by ring
  have hkey : A / c ≤ t ^ 9 * Real.exp (2 * R / 3) := by
    have ht3 : t ^ 3 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
    have h2 : t ^ 3 * (720 * A / (c * ν)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ht3 (by positivity : (0:ℝ) ≤ 720 * A / (c * ν))
      linarith
    have e : t ^ 12 * Real.exp (2 * R / 3) = t ^ 3 * (t ^ 9 * Real.exp (2 * R / 3)) := by ring
    rw [e] at hE
    have ht3p : 0 < t ^ 3 := by positivity
    rw [div_le_iff₀ hc]
    have h3 : t ^ 3 * (720 * A) ≤ c * ν := by
      rw [mul_div_assoc'] at h2
      rw [div_le_one (by positivity)] at h2
      linarith
    by_contra hc'
    push Not at hc'
    have h4 := mul_lt_mul_of_pos_left hc' (by positivity : (0:ℝ) < 720 * t ^ 3)
    have h5 : c * ν ≤ c * (720 * (t ^ 3 * (t ^ 9 * Real.exp (2 * R / 3)))) := by
      apply mul_le_mul_of_nonneg_left _ hc.le; linarith
    nlinarith
  have ht9 : t ^ 9 * (1 / t ^ 2) ^ 3 = t ^ 3 := by field_simp
  calc A * κ⁻¹ ^ 3 * Real.exp (R / 3) ≤ A * (1 / t ^ 2) ^ 3 * Real.exp (R / 3) := by gcongr
    _ = c * (A / c * (1 / t ^ 2) ^ 3) * Real.exp (R / 3) := by field_simp
    _ ≤ c * (t ^ 9 * Real.exp (2 * R / 3) * (1 / t ^ 2) ^ 3) * Real.exp (R / 3) := by gcongr
    _ = c * (t ^ 9 * (1 / t ^ 2) ^ 3) * (Real.exp (R / 3) * Real.exp (2 * R / 3)) := by ring
    _ = c * Real.exp R * t ^ 3 := by rw [ht9, ← hsplit]; ring

theorem far_two_real {M r c μ t κ R : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hκ : t ^ 2 ≤ κ)
    (hμ : 0 < μ) (hRt : μ ≤ R * t ^ 2) (hM0 : 0 ≤ M) (hr : 0 < r) (hc : 0 < c)
    (htQ : t * (720 * M / (r * c * μ ^ 6)) ≤ 1) :
    M / 2 * (1 / (r * κ)) * 2 ≤ c * Real.exp R * t ^ 3 := by
  have ht2p : 0 < t ^ 2 := by positivity
  have hκ0 : 0 < κ := lt_of_lt_of_le ht2p hκ
  have hR0 : 0 ≤ R := by
    by_contra hn; push Not at hn; nlinarith
  have h1 : M / 2 * (1 / (r * κ)) * 2 ≤ M / (r * t ^ 2) := by
    rw [show M / 2 * (1 / (r * κ)) * 2 = M / (r * κ) by field_simp]
    apply div_le_div_of_nonneg_left hM0 (by positivity)
    exact mul_le_mul_of_nonneg_left hκ hr.le
  have hE := pow_six_div_le_exp hR0
  have hR6 : μ ^ 6 ≤ (R * t ^ 2) ^ 6 := pow_le_pow_left₀ hμ.le hRt 6
  have ht7 : t ^ 7 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
  have hMt : 720 * M * t ^ 7 ≤ r * c * μ ^ 6 := by
    have h2 : t * (720 * M) ≤ r * c * μ ^ 6 := by
      rw [mul_div_assoc', div_le_one (by positivity)] at htQ; linarith
    have := mul_le_mul_of_nonneg_left ht7 (by positivity : (0:ℝ) ≤ 720 * M)
    linarith
  have hkey : M ≤ r * c * t ^ 5 * Real.exp R := by
    have h720 : μ ^ 6 ≤ 720 * (t ^ 12 * Real.exp R) := by
      have h3 := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ t ^ 12)
      have e : t ^ 12 * (R ^ 6 / 720) = (R * t ^ 2) ^ 6 / 720 := by ring
      rw [e] at h3
      linarith
    have ht7p : 0 < 720 * t ^ 7 := by positivity
    have h2 : 720 * t ^ 7 * M ≤ 720 * t ^ 7 * (r * c * t ^ 5 * Real.exp R) := by
      have e1 : 720 * t ^ 7 * (r * c * t ^ 5 * Real.exp R) = r * c * (720 * (t ^ 12 * Real.exp R)) := by
        ring
      rw [e1]
      have := mul_le_mul_of_nonneg_left h720 (by positivity : (0:ℝ) ≤ r * c)
      linarith
    exact le_of_mul_le_mul_left h2 ht7p
  calc M / 2 * (1 / (r * κ)) * 2 ≤ M / (r * t ^ 2) := h1
    _ ≤ c * Real.exp R * t ^ 3 := by
        rw [div_le_iff₀ (by positivity)]
        have e : c * Real.exp R * t ^ 3 * (r * t ^ 2) = r * c * t ^ 5 * Real.exp R := by ring
        rw [e]; exact hkey

theorem chR0m_mul_sq_ge {m : ℝ} (hm : 0 ≤ m) (ht : 0 < t) (ht4 : t ^ 4 ≤ 3 / 4) :
    3 * m / 16 ≤ chR0m m t * t ^ 2 := by
  unfold chR0m
  have hb := half_le_chB (t := t) ht4
  have hπ := Real.pi_gt_three
  have e : m * π * chB t / (8 * t ^ 2) * t ^ 2 = m * π * chB t / 8 := by field_simp
  rw [e]
  have : 3 * (1 / 2) ≤ π * chB t := by nlinarith
  nlinarith

/-- The far-field thresholds. -/
def chFarQ1 (a : ℝ) : ℝ :=
  720 * 36 ^ a / ((2 : ℝ) ^ (-(2 * a)) / (32 * (a + 1)) * (2 * (3 * chMa a / 16) / 3) ^ 6)

def chFarQ2 (a M : ℝ) : ℝ :=
  720 * M / (π * a / 4 * ((2 : ℝ) ^ (-(2 * a)) / (32 * (a + 1))) * (3 * chMa a / 16) ^ 6)

theorem two_chBfarA_le (ha : 1 / 2 < a) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) {M : ℝ} (hM0 : 0 ≤ M)
    (h1 : t * chFarQ1 a ≤ 1) (h2 : t * chFarQ2 a M ≤ 1) :
    2 * chBfarA a t M ≤ chG0a a t * t ^ 3 / (32 * (a + 1)) := by
  have ht1' : t ≤ 1 := by linarith
  have ht4 : t ^ 4 ≤ 3 / 4 := by
    have := pow_le_of_le_one ht0.le ht1' (by norm_num : (4:ℕ) ≠ 0); nlinarith
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_of_le_one ht0.le ht1' (by norm_num : (2:ℕ) ≠ 0); nlinarith
  have hκ := chKap_ge ht4
  have hm := chMa_pos ha
  have hμ : 0 < 3 * chMa a / 16 := by positivity
  have hRt := chR0m_mul_sq_ge hm.le ht0 ht4
  have hp := one_le_chP0 ht0 ht2
  set c : ℝ := (2 : ℝ) ^ (-(2 * a)) / (32 * (a + 1)) with hc
  have hc0 : 0 < c := by
    have : 0 < a + 1 := by linarith
    positivity
  have hGt : c * Real.exp (chR0m (chMa a) t) * t ^ 3 ≤ chG0a a t * t ^ 3 / (32 * (a + 1)) := by
    unfold chG0a
    rw [hc]
    have : 0 < a + 1 := by linarith
    have e : (2 : ℝ) ^ (-(2 * a)) / (32 * (a + 1)) * Real.exp (chR0m (chMa a) t) * t ^ 3 =
        (2 : ℝ) ^ (-(2 * a)) * 1 * Real.exp (chR0m (chMa a) t) * t ^ 3 / (32 * (a + 1)) := by
      ring
    rw [e]
    gcongr
  have hA : (0 : ℝ) ≤ 36 ^ a := by positivity
  have hb1 := far_one_real (A := 36 ^ a) (c := c) (μ := 3 * chMa a / 16) ht0 ht1' hκ hμ hRt hA hc0
    (by unfold chFarQ1 at h1; rw [hc]; exact h1)
  have hr : 0 < π * a / 4 := by have := Real.pi_pos; nlinarith
  have hb2 := far_two_real (M := M) (r := π * a / 4) (c := c) (μ := 3 * chMa a / 16) ht0 ht1' hκ hμ
    hRt hM0 hr hc0 (by unfold chFarQ2 at h2; rw [hc]; exact h2)
  unfold chBfarA
  rw [mul_comm, max_mul_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  refine le_trans (max_le ?_ hb2) hGt
  linarith

/-- **Positivity of the saddle-line integral of `F_a`.** -/
theorem exists_re_chLineAInt_pos (ha : 1 / 2 < a) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t : ℝ, 0 < t → t ≤ t₁ → 0 < (chLineAInt a t).re := by
  have ha0 : 0 ≤ a := by linarith
  set M : ℝ := thetaPowerCuspConstant a with hMdef
  have hM : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaPowerForm a τ‖ ≤ M * Real.exp (-(π * a / 4) * τ.im) :=
    thetaPowerForm_cuspDecay ha0
  have hM0 : 0 ≤ M := by unfold thetaPowerCuspConstant at hMdef; rw [hMdef]; positivity
  set A : ℝ := 20000 * (1 + a) with hA
  set B : ℝ := 176 * (a + 1) * chLamA a ^ 3 with hB
  set C₁ : ℝ := chFarQ1 a with hC1
  set C₂ : ℝ := chFarQ2 a M with hC2
  have hm := chMa_pos ha
  have hApos : 0 < A := by rw [hA]; linarith
  have hBpos : 0 < B := by
    have := one_le_chLamA ha
    rw [hB]; have : 0 < a + 1 := by linarith
    positivity
  have hC1pos : 0 ≤ C₁ := by
    rw [hC1]; unfold chFarQ1
    have : 0 < a + 1 := by linarith
    positivity
  have hC2pos : 0 ≤ C₂ := by
    rw [hC2]; unfold chFarQ2
    have : 0 < a + 1 := by linarith
    have : 0 < π * a / 4 := by have := Real.pi_pos; nlinarith
    positivity
  refine ⟨min (1 / 100) (min (1 / A) (min (1 / B) (min (1 / (C₁ + 1)) (1 / (C₂ + 1))))),
    by positivity, fun t ht htt => ?_⟩
  have h0 : t ≤ 1 / 100 := le_trans htt (min_le_left _ _)
  have h1 : t * A ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [le_div_iff₀ hApos] at this; linarith
  have h2 : t * B ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    rw [le_div_iff₀ hBpos] at this; linarith
  have h3 : t * C₁ ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
    rw [le_div_iff₀ (by linarith)] at this; nlinarith
  have h4 : t * C₂ ≤ 1 := by
    have := le_trans htt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
    rw [le_div_iff₀ (by linarith)] at this; nlinarith
  have hsmall : chSmallA a t := by
    refine ⟨ht, ?_⟩
    have ht1 : t ≤ 1 := by linarith
    have : t ^ 2 ≤ t := by nlinarith
    have := mul_le_mul_of_nonneg_right this hApos.le
    rw [hA] at h1 this; linarith
  have hlo := re_chLineAInt_ge ha hsmall (by rw [hB] at h2; linarith) hM
  have hfar := two_chBfarA_le ha ht h0 hM0 h3 h4
  have hG := chG0a_pos a t
  have : 0 < chG0a a t * t ^ 3 / (32 * (a + 1)) := by
    have : 0 < a + 1 := by linarith
    positivity
  have e : chG0a a t * t ^ 3 / (16 * (a + 1)) = 2 * (chG0a a t * t ^ 3 / (32 * (a + 1))) := by
    field_simp; ring
  linarith

end LineA

/-! ## From the line integral to the transform -/

section Transform

variable {a : ℝ}

/-- **Contour shift of the axis transform of `F_a`.** -/
theorem thetaPowerXi_eq_shift (ha : 0 < a) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 4) (u : ℝ) :
    thetaPowerXi a u = Complex.exp (-(u * β : ℝ)) *
      ∫ s : ℝ, Complex.exp (-Complex.I * u * s) *
        chargeTailC (thetaPowerForm a) ((s : ℂ) - (β : ℂ) * Complex.I) := by
  obtain ⟨C, hC, hbd⟩ := thetaPowerTail_decay ha β hβ0 hβ
  set F := thetaPowerForm a
  have hF := differentiableOn_thetaPowerForm a
  set G : ℂ → ℂ := fun z => Complex.exp (-Complex.I * u * z) * chargeTailC F z with hG
  set G' : ℂ → ℂ := fun z => G (-z) with hG'
  have hdiff : ∀ z : ℂ, |z.im| ≤ β → DifferentiableAt ℂ G' z := by
    intro z hz
    have hz' : |(-z).im| < π / 4 := by rw [Complex.neg_im, abs_neg]; linarith
    have h1 : DifferentiableAt ℂ G (-z) :=
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-Complex.I * u * z)) (-z)).mul
        (differentiableAt_chargeTailC hF hz')
    exact h1.comp z differentiableAt_id.neg
  have hbound : ∀ z : ℂ, |z.im| ≤ β →
      ‖G' z‖ ≤ (Real.exp (|u| * β) * C) * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    have hz' : |(-z).im| ≤ β := by rw [Complex.neg_im, abs_neg]; exact hz
    have h1 := hbd (-z) hz'
    rw [Complex.neg_re, abs_neg] at h1
    have hexp : ‖Complex.exp (-Complex.I * u * -z)‖ ≤ Real.exp (|u| * β) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have : (-Complex.I * (u : ℂ) * -z).re = -(u * z.im) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this]
      have := abs_mul u z.im
      have h3 : |u| * |z.im| ≤ |u| * β := mul_le_mul_of_nonneg_left hz (abs_nonneg u)
      have h4 := neg_abs_le (u * z.im)
      linarith
    simp only [hG', hG, norm_mul]
    rw [one_mul]
    calc ‖Complex.exp (-Complex.I * u * -z)‖ * ‖chargeTailC F (-z)‖
        ≤ Real.exp (|u| * β) * (C * Real.exp (-|z.re|)) :=
          mul_le_mul hexp h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|u| * β) * C * Real.exp (-|z.re|) := by ring
  have hshift := integral_horizontal_shift_of_decay hβ0 one_pos hdiff hbound
  simp only [hG', hG] at hshift
  have hL : (∫ x : ℝ, Complex.exp (-Complex.I * u * -((x : ℂ) + (β : ℂ) * Complex.I)) *
      chargeTailC F (-((x : ℂ) + (β : ℂ) * Complex.I))) =
      ∫ s : ℝ, Complex.exp (-Complex.I * u * ((s : ℂ) - (β : ℂ) * Complex.I)) *
        chargeTailC F ((s : ℂ) - (β : ℂ) * Complex.I) := by
    rw [← integral_neg_eq_self]
    congr 1; funext s; push_cast; ring_nf
  have hR : (∫ x : ℝ, Complex.exp (-Complex.I * u * -(x : ℂ)) * chargeTailC F (-(x : ℂ))) =
      ∫ x : ℝ, Complex.exp (-Complex.I * u * x) * modTail F 0 x := by
    rw [← integral_neg_eq_self]
    congr 1; funext x; push_cast; rw [neg_neg, chargeTailC_ofReal]
  unfold thetaPowerXi
  rw [← hR, ← hshift, hL, ← integral_const_mul]
  congr 1; funext s
  have : Complex.exp (-Complex.I * u * ((s : ℂ) - (β : ℂ) * Complex.I)) =
      Complex.exp (-(u * β : ℝ)) * Complex.exp (-Complex.I * u * s) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [this]; ring

theorem thetaPowerXi_chUm (ha : 1 / 2 < a) {t : ℝ} (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2) :
    thetaPowerXi a (chUm (chMa a) t) =
      Complex.exp (-(chUm (chMa a) t * chBeta t : ℝ)) * chLineAInt a t := by
  rw [thetaPowerXi_eq_shift (by linarith) (chBeta_nonneg ht2) (chBeta_lt ht (by linarith))]
  rfl

/-- **Nonvanishing above a height.** -/
theorem thetaPowerXi_eventually_ne_zero (ha : 1 / 2 < a) :
    ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ u → thetaPowerXi a u ≠ 0 := by
  obtain ⟨t₁, ht₁, hpos⟩ := exists_re_chLineAInt_pos ha
  set t₂ : ℝ := min t₁ (1 / 2) with ht₂
  have ht₂pos : 0 < t₂ := by positivity
  have hm := chMa_pos ha
  refine ⟨chUm (chMa a) t₂, by unfold chUm; positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le (by unfold chUm; positivity) hu
  set t : ℝ := (chMa a * π / (8 * u)) ^ (1 / 4 : ℝ) with htdef
  have hbase : 0 < chMa a * π / (8 * u) := by positivity
  have ht0 : 0 < t := Real.rpow_pos_of_pos hbase _
  have ht4 : t ^ 4 = chMa a * π / (8 * u) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul hbase.le]; norm_num
  have hu_eq : chUm (chMa a) t = u := by
    unfold chUm; rw [ht4]; field_simp
  have htt : t ≤ t₂ := by
    have h4 : t ^ 4 ≤ t₂ ^ 4 := by
      rw [ht4]
      have : chUm (chMa a) t₂ = chMa a * π / (8 * t₂ ^ 4) := rfl
      rw [this] at hu
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hu
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) ht₂pos.le h4
  have ht2 : t ^ 2 ≤ 1 / 2 := by
    have : t ≤ 1 / 2 := le_trans htt (min_le_right _ _)
    nlinarith
  have hre := hpos t ht0 (le_trans htt (min_le_left _ _))
  rw [← hu_eq, thetaPowerXi_chUm ha ht0 ht2]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  intro h0; rw [h0] at hre; simp at hre

/-- The axis transform is even. -/
theorem thetaPowerXi_neg (a u : ℝ) : thetaPowerXi a (-u) = thetaPowerXi a u := by
  unfold thetaPowerXi
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  have he : modTail (thetaPowerForm a) 0 (-x) = modTail (thetaPowerForm a) 0 x := by
    have h := modTail_neg (F := thetaPowerForm a) 0 (thetaPowerForm_axis a) x
    simpa using h
  rw [he]
  push_cast
  ring_nf

end Transform

/-! ## The holomorphic extension and finiteness of the real zeros -/

section Complex

variable {a : ℝ}

/-- The axis transform of `F_a` at a complex frequency. -/
def thetaPowerXiC (a : ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * w * x) * modTail (thetaPowerForm a) 0 x

theorem thetaPowerXiC_ofReal (a u : ℝ) : thetaPowerXiC a (u : ℂ) = thetaPowerXi a u := rfl

/-- The strip `|Im w| < 1`. -/
def unitStripSet : Set ℂ := {w : ℂ | |w.im| < 1}

theorem isOpen_unitStripSet : IsOpen unitStripSet :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem differentiableOn_thetaPowerXiC (ha : 0 < a) :
    DifferentiableOn ℂ (thetaPowerXiC a) unitStripSet := by
  obtain ⟨C, hC0, hC⟩ := thetaPowerTail_decay ha 0 le_rfl (by positivity)
  have hT : ∀ x : ℝ, ‖modTail (thetaPowerForm a) 0 x‖ ≤ C * Real.exp (-|x|) := by
    intro x
    have h := hC (x : ℂ) (by simp)
    rw [chargeTailC_ofReal] at h
    simpa using h
  have hTc : Continuous (modTail (thetaPowerForm a) 0) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_modTail 0 (differentiableOn_thetaPowerForm a) x).continuousAt
  intro w₀ hw₀
  have hw₀' : |w₀.im| < 1 := hw₀
  set ρ : ℝ := (|w₀.im| + 1) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρ0 : |w₀.im| < ρ := by rw [hρ]; linarith
  set δ : ℝ := ρ - |w₀.im| with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set g : ℂ → ℝ → ℂ := fun w x => Complex.exp (-Complex.I * w * x) *
    modTail (thetaPowerForm a) 0 x with hg
  set g' : ℂ → ℝ → ℂ := fun w x => (-Complex.I * x) * g w x with hg'
  have hnorm : ∀ w : ℂ, ∀ x : ℝ, ‖Complex.exp (-Complex.I * w * x)‖ = Real.exp (w.im * x) := by
    intro w x; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (g w) volume := fun w =>
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-Complex.I * w * x)).mul hTc).aestronglyMeasurable
  have hdomC : ∀ w : ℂ, |w.im| ≤ ρ → ∀ x : ℝ, ‖g w x‖ ≤ C * Real.exp (-((1 - ρ) * |x|)) := by
    intro w hw x
    simp only [hg]
    rw [norm_mul, hnorm]
    have hwx : w.im * x ≤ ρ * |x| := by
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ ρ * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg x)
    calc Real.exp (w.im * x) * ‖modTail (thetaPowerForm a) 0 x‖
        ≤ Real.exp (ρ * |x|) * (C * Real.exp (-|x|)) :=
          mul_le_mul (Real.exp_le_exp.mpr hwx) (hT x) (norm_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp (-((1 - ρ) * |x|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hr : 0 < 1 - ρ := by linarith
  have hint : Integrable (g w₀) := by
    refine Integrable.mono' ((integrable_exp_neg_mul_abs' hr).const_mul C) (hmeas w₀)
      (Filter.Eventually.of_forall fun x => hdomC w₀ hρ0.le x)
  set bound : ℝ → ℝ := fun x => C * (2 / (1 - ρ)) * Real.exp (-((1 - ρ) / 2 * |x|)) with hbound
  have hboundInt : Integrable bound :=
    (integrable_exp_neg_mul_abs' (by positivity : 0 < (1 - ρ) / 2)).const_mul _
  have hdom : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ δ, ‖g' w x‖ ≤ bound x := by
    filter_upwards with x
    intro w hw
    have hdist : ‖w - w₀‖ < δ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have him : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
    have hwρ : |w.im| ≤ ρ := by
      calc |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ ρ := by rw [hδ] at hdist; linarith
    have h1 := hdomC w hwρ x
    simp only [hg']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hxexp : |x| ≤ 2 / (1 - ρ) * Real.exp ((1 - ρ) / 2 * |x|) := by
      have := Real.add_one_le_exp ((1 - ρ) / 2 * |x|)
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      nlinarith [Real.exp_pos ((1 - ρ) / 2 * |x|), abs_nonneg x]
    calc |x| * ‖g w x‖ ≤ (2 / (1 - ρ) * Real.exp ((1 - ρ) / 2 * |x|)) *
          (C * Real.exp (-((1 - ρ) * |x|))) :=
          mul_le_mul hxexp h1 (norm_nonneg _) (by positivity)
      _ = bound x := by
          rw [hbound]
          have e : Real.exp ((1 - ρ) / 2 * |x|) * Real.exp (-((1 - ρ) * |x|)) =
              Real.exp (-((1 - ρ) / 2 * |x|)) := by rw [← Real.exp_add]; congr 1; ring
          calc 2 / (1 - ρ) * Real.exp ((1 - ρ) / 2 * |x|) * (C * Real.exp (-((1 - ρ) * |x|)))
              = C * (2 / (1 - ρ)) *
                  (Real.exp ((1 - ρ) / 2 * |x|) * Real.exp (-((1 - ρ) * |x|))) := by ring
            _ = _ := by rw [e]
  have hderiv : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ δ, HasDerivAt (fun w => g w x) (g' w x) w := by
    filter_upwards with x
    intro w _
    simp only [hg, hg']
    have h := ((hasDerivAt_id w).const_mul (-Complex.I)).mul_const (x : ℂ)
    have h2 := (h.cexp).mul_const (modTail (thetaPowerForm a) 0 x)
    refine h2.congr_deriv ?_
    simp only [id]
    ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := g) (F' := g') (x₀ := w₀) (bound := bound)
    (Metric.ball_mem_nhds w₀ hδ0) (Filter.Eventually.of_forall hmeas) hint
    ((((by fun_prop : Continuous fun x : ℝ => -Complex.I * (x : ℂ)).mul
      ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-Complex.I * w₀ * x)).mul hTc))).aestronglyMeasurable)
    hdom hboundInt hderiv
  exact hres.2.differentiableAt.differentiableWithinAt

/-- **Finitely many critical zeros above the wall.**  For `a > 1/2` the axis transform of
`F_a = θ₃ h^{a/4}` has only finitely many real zeros. -/
theorem thetaPowerXi_real_zeros_finite (ha : 1 / 2 < a) :
    {u : ℝ | thetaPowerXi a u = 0}.Finite := by
  have ha' : 0 < a := by linarith
  obtain ⟨U, hU, hne⟩ := thetaPowerXi_eventually_ne_zero ha
  have hf := differentiableOn_thetaPowerXiC ha'
  have hUmem : (U : ℂ) ∈ unitStripSet := by show |((U : ℂ)).im| < 1; simp
  have hiso : ∀ z ∈ unitStripSet, ¬ (∀ᶠ w in 𝓝 z, thetaPowerXiC a w = 0) := by
    intro z hz hev
    have han := hf.analyticOnNhd isOpen_unitStripSet
    have hconv : Convex ℝ unitStripSet := by
      intro x hx y hy s' t' hs ht hst
      show |(s' • x + t' • y).im| < 1
      have hx' : |x.im| < 1 := hx
      have hy' : |y.im| < 1 := hy
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      calc |s' * x.im + t' * y.im| ≤ s' * |x.im| + t' * |y.im| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
        _ < 1 := by
            rcases eq_or_lt_of_le hs with h0 | h0
            · subst h0; simp at hst; subst hst; simpa using hy'
            · nlinarith [mul_lt_mul_of_pos_left hx' h0, mul_le_mul_of_nonneg_left hy'.le ht]
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconv.isPreconnected hz hev
    exact hne U le_rfl (by rw [← thetaPowerXiC_ofReal]; exact hzero hUmem)
  have hK : IsCompact ((fun u : ℝ => (u : ℂ)) '' Set.Icc (-U) U) :=
    (isCompact_Icc).image Complex.continuous_ofReal
  have hKsub : (fun u : ℝ => (u : ℂ)) '' Set.Icc (-U) U ⊆ unitStripSet := by
    rintro _ ⟨u, _, rfl⟩; show |((u : ℂ)).im| < 1; simp
  have hfin := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact isOpen_unitStripSet hf hiso
    hK hKsub
  have hinj : Set.InjOn (fun u : ℝ => (u : ℂ)) {u : ℝ | thetaPowerXi a u = 0} :=
    fun x _ y _ h => Complex.ofReal_injective h
  refine Set.Finite.of_finite_image ?_ hinj
  apply hfin.subset
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨⟨u, ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · by_contra h; push Not at h
    have := hne (-u) (by linarith)
    rw [thetaPowerXi_neg] at this
    exact this hu
  · by_contra h; push Not at h
    exact hne u h.le hu
  · show thetaPowerXiC a (u : ℂ) = 0
    rw [thetaPowerXiC_ofReal]; exact hu

end Complex

end

end RHTower
