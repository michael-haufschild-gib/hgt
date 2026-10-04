import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Positivity from nonnegative Laplace moments

If `f` has absolutely convergent weighted Laplace moments `∫_0^∞ s^n e^{-ps} f(s) ds` for every
`n` and every `p > γ`, and all of them are nonnegative, then `f ≥ 0` at every positive point of
continuity.

The proof is a Laplace-method localisation at the peak `t₀` of `s^n e^{-ns/t₀}`.  With
`ψ(s) = (s/t₀) e^{1 - s/t₀}` one has `s^n e^{-ns/t₀} = (t₀/e)^n ψ(s)^n`, `ψ ≤ 1`, `ψ(t₀) = 1`,
and `ψ ≤ ρ < 1` off any neighbourhood of `t₀`.  If `f(t₀) < 0`, a fixed moment `m` absorbs the
growth of `f` away from `t₀`, and the pointwise bound
`ψ^n f ≤ -η ρ'^n 1_{[t₀-δ', t₀+δ']} + ρ^{n-m} ψ^m |f|` with `ρ < ρ'` makes the `n`-th moment
negative for large `n`.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The normalized peak profile `ψ(s) = (s/t₀) e^{1 - s/t₀}`. -/
def laplacePeak (t₀ s : ℝ) : ℝ := s / t₀ * Real.exp (1 - s / t₀)

theorem continuous_laplacePeak (t₀ : ℝ) : Continuous (laplacePeak t₀) := by
  unfold laplacePeak; fun_prop

theorem laplacePeak_self {t₀ : ℝ} (ht₀ : 0 < t₀) : laplacePeak t₀ t₀ = 1 := by
  simp [laplacePeak, div_self ht₀.ne']

theorem laplacePeak_le_one (t₀ s : ℝ) : laplacePeak t₀ s ≤ 1 := by
  unfold laplacePeak
  have h := Real.add_one_le_exp (s / t₀ - 1)
  have he := Real.exp_pos (1 - s / t₀)
  calc s / t₀ * Real.exp (1 - s / t₀) ≤ Real.exp (s / t₀ - 1) * Real.exp (1 - s / t₀) :=
        mul_le_mul_of_nonneg_right (by linarith) he.le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem laplacePeak_lt_one {t₀ s : ℝ} (ht₀ : 0 < t₀) (hs : s ≠ t₀) : laplacePeak t₀ s < 1 := by
  unfold laplacePeak
  have hne : s / t₀ - 1 ≠ 0 := by
    intro h
    apply hs
    have : s / t₀ = 1 := by linarith
    rwa [div_eq_one_iff_eq ht₀.ne'] at this
  have h := Real.add_one_lt_exp hne
  have he := Real.exp_pos (1 - s / t₀)
  calc s / t₀ * Real.exp (1 - s / t₀) < Real.exp (s / t₀ - 1) * Real.exp (1 - s / t₀) :=
        mul_lt_mul_of_pos_right (by linarith) he
    _ = 1 := by rw [← Real.exp_add]; simp

theorem laplacePeak_pos {t₀ s : ℝ} (ht₀ : 0 < t₀) (hs : 0 < s) : 0 < laplacePeak t₀ s := by
  unfold laplacePeak; positivity

theorem laplacePeak_nonneg {t₀ s : ℝ} (ht₀ : 0 < t₀) (hs : 0 ≤ s) : 0 ≤ laplacePeak t₀ s := by
  unfold laplacePeak; positivity

/-- `ψ` decreases to the right of the peak. -/
theorem laplacePeak_antitone {t₀ s s' : ℝ} (ht₀ : 0 < t₀) (hs : t₀ ≤ s) (hss' : s ≤ s') :
    laplacePeak t₀ s' ≤ laplacePeak t₀ s := by
  unfold laplacePeak
  set u := s / t₀
  set v := s' / t₀
  have hu : 1 ≤ u := by rw [le_div_iff₀ ht₀]; linarith
  have huv : u ≤ v := div_le_div_of_nonneg_right hss' ht₀.le
  have h1 : v / u ≤ Real.exp (v - u) := by
    have h := Real.add_one_le_exp (v - u)
    have : v / u ≤ v - u + 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have h2 : v ≤ u * Real.exp (v - u) := by
    rwa [div_le_iff₀ (by linarith), mul_comm] at h1
  calc v * Real.exp (1 - v) ≤ u * Real.exp (v - u) * Real.exp (1 - v) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = u * Real.exp (1 - u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `ψ` increases to the left of the peak. -/
theorem laplacePeak_monotone {t₀ s s' : ℝ} (ht₀ : 0 < t₀) (hs : 0 < s) (hss' : s ≤ s')
    (hs' : s' ≤ t₀) : laplacePeak t₀ s ≤ laplacePeak t₀ s' := by
  unfold laplacePeak
  set u := s / t₀
  set v := s' / t₀
  have hu : 0 < u := div_pos hs ht₀
  have huv : u ≤ v := div_le_div_of_nonneg_right hss' ht₀.le
  have hv1 : v ≤ 1 := by rw [div_le_one ht₀]; exact hs'
  have hv : 0 < v := hu.trans_le huv
  have h1 : u / v ≤ Real.exp (u - v) := by
    have h := Real.add_one_le_exp (u / v - 1)
    have : u / v - 1 ≤ u - v := by
      rw [div_sub_one hv.ne', div_le_iff₀ hv]
      nlinarith
    exact h.trans' (by linarith) |>.trans (Real.exp_le_exp.2 this)
  have h2 : u ≤ v * Real.exp (u - v) := by
    rwa [div_le_iff₀ hv, mul_comm] at h1
  calc u * Real.exp (1 - u) ≤ v * Real.exp (u - v) * Real.exp (1 - u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = v * Real.exp (1 - v) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `s^n e^{-(n/t₀) s} = (t₀ e^{-1})^n ψ(s)^n`. -/
theorem pow_mul_exp_eq_laplacePeak_pow {t₀ : ℝ} (ht₀ : 0 < t₀) (n : ℕ) (s : ℝ) :
    s ^ n * Real.exp (-(n / t₀ * s)) = (t₀ * Real.exp (-1)) ^ n * laplacePeak t₀ s ^ n := by
  rw [← mul_pow]
  have h : t₀ * Real.exp (-1) * laplacePeak t₀ s = s * Real.exp (-(s / t₀)) := by
    unfold laplacePeak
    rw [show t₀ * Real.exp (-1) * (s / t₀ * Real.exp (1 - s / t₀)) =
      s * (Real.exp (-1) * Real.exp (1 - s / t₀)) by field_simp, ← Real.exp_add]
    ring_nf
  rw [h, mul_pow, ← Real.exp_nat_mul]
  ring_nf

/-- **Laplace-moment positivity.**  Nonnegative absolutely convergent weighted Laplace moments
`∫_0^∞ s^n e^{-ps} f(s) ds` for all `n` and all `p > γ` force `f(t₀) ≥ 0` at every positive point
of continuity `t₀`. -/
theorem nonneg_of_laplaceMoments_nonneg {f : ℝ → ℝ} {γ t₀ : ℝ} (ht₀ : 0 < t₀)
    (hf : ContinuousAt f t₀)
    (hint : ∀ n : ℕ, ∀ p, γ < p →
      IntegrableOn (fun s => s ^ n * Real.exp (-(p * s)) * f s) (Ioi 0))
    (hpos : ∀ n : ℕ, ∀ p, γ < p → 0 ≤ ∫ s in Ioi (0 : ℝ), s ^ n * Real.exp (-(p * s)) * f s) :
    0 ≤ f t₀ := by
  by_contra hneg
  push Not at hneg
  set ψ := laplacePeak t₀
  set η := -f t₀ / 2
  have hη : 0 < η := by simp only [η]; linarith
  -- the negative neighbourhood of `t₀`
  obtain ⟨ε₁, hε₁, hfε⟩ := Metric.eventually_nhds_iff.1
    (hf.eventually (gt_mem_nhds (show f t₀ < -η by simp only [η]; linarith)))
  set δ := min (ε₁ / 2) (t₀ / 2)
  have hδ : 0 < δ := lt_min (half_pos hε₁) (half_pos ht₀)
  have hδε : δ < ε₁ := (min_le_left _ _).trans_lt (half_lt_self hε₁)
  have hδt : δ < t₀ := (min_le_right _ _).trans_lt (half_lt_self ht₀)
  -- the far ratio `ρ`
  set ρ := max (ψ (t₀ + δ)) (ψ (t₀ - δ))
  have hρ1 : ρ < 1 := max_lt (laplacePeak_lt_one ht₀ (by linarith))
    (laplacePeak_lt_one ht₀ (by linarith))
  have hρ0 : 0 < ρ := (laplacePeak_pos ht₀ (by linarith : (0 : ℝ) < t₀ + δ)).trans_le
    (le_max_left _ _)
  have hfar : ∀ s, 0 < s → δ ≤ |s - t₀| → ψ s ≤ ρ := by
    intro s hs hsd
    rcases le_abs'.1 hsd with h | h
    · exact (laplacePeak_monotone ht₀ hs (by linarith) (by linarith)).trans (le_max_right _ _)
    · exact (laplacePeak_antitone ht₀ (by linarith) (by linarith)).trans (le_max_left _ _)
  -- the near ratio `ρ'`
  set ρ' := (1 + ρ) / 2
  have hρρ' : ρ < ρ' := by simp only [ρ']; linarith
  have hρ'0 : 0 < ρ' := hρ0.trans hρρ'
  obtain ⟨ε₂, hε₂, hψε⟩ := Metric.eventually_nhds_iff.1
    ((continuous_laplacePeak t₀).continuousAt.eventually
      (lt_mem_nhds (show ρ' < laplacePeak t₀ t₀ by rw [laplacePeak_self ht₀]; simp only [ρ']; linarith)))
  set δ' := min (ε₂ / 2) δ
  have hδ' : 0 < δ' := lt_min (half_pos hε₂) hδ
  have hδ'δ : δ' ≤ δ := min_le_right _ _
  have hδ'ε : δ' < ε₂ := (min_le_left _ _).trans_lt (half_lt_self hε₂)
  set I := Icc (t₀ - δ') (t₀ + δ')
  have hIsub : I ⊆ Ioi 0 := fun s hs => by simp only [I, mem_Icc] at hs; simp only [mem_Ioi]; linarith
  -- a fixed absorbing moment
  set m : ℕ := ⌈γ * t₀⌉₊ + 1
  have hm : γ < m / t₀ := by
    rw [lt_div_iff₀ ht₀]
    have := Nat.le_ceil (γ * t₀)
    simp only [m]; push_cast; linarith
  have hmpos : ∀ n : ℕ, m ≤ n → γ < n / t₀ := fun n hn =>
    hm.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hn) ht₀.le)
  set c := t₀ * Real.exp (-1)
  have hc : 0 < c := by positivity
  have hψm : IntegrableOn (fun s => ψ s ^ m * |f s|) (Ioi 0) := by
    have h : IntegrableOn (fun s => (c ^ m)⁻¹ * |s ^ m * Real.exp (-(m / t₀ * s)) * f s|) (Ioi 0) := ((hint m (m / t₀) hm).abs).const_mul ((c ^ m)⁻¹)
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : 0 ≤ s := le_of_lt hs
    dsimp only
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ m * Real.exp (-(m / t₀ * s))),
      pow_mul_exp_eq_laplacePeak_pow ht₀]
    field_simp
    ring
  set C := ∫ s in Ioi (0 : ℝ), ψ s ^ m * |f s|
  -- the pointwise majorant
  have hmaj : ∀ n : ℕ, m ≤ n → ∀ s ∈ Ioi (0 : ℝ), ψ s ^ n * f s ≤
      I.indicator (fun _ => -η * ρ' ^ n) s + ρ ^ (n - m) * (ψ s ^ m * |f s|) := by
    intro n hn s hs
    have hs0 : 0 < s := hs
    have hψ0 : 0 ≤ ψ s := laplacePeak_nonneg ht₀ hs0.le
    have hsecond : 0 ≤ ρ ^ (n - m) * (ψ s ^ m * |f s|) := by positivity
    by_cases hI : s ∈ I
    · rw [indicator_of_mem hI]
      have hsI : |s - t₀| ≤ δ' := by simp only [I, mem_Icc] at hI; rw [abs_le]; constructor <;> linarith
      have hfs : f s < -η := hfε (by rw [Real.dist_eq]; linarith)
      have hψs : ρ' < ψ s := hψε (by rw [Real.dist_eq]; linarith)
      have hpow : ρ' ^ n ≤ ψ s ^ n := pow_le_pow_left₀ hρ'0.le hψs.le n
      have h1 : ψ s ^ n * f s ≤ ψ s ^ n * (-η) :=
        mul_le_mul_of_nonneg_left hfs.le (pow_nonneg hψ0 n)
      have h2 : ψ s ^ n * (-η) ≤ ρ' ^ n * (-η) := mul_le_mul_of_nonpos_right hpow (by linarith)
      linarith
    · rw [indicator_of_notMem hI, zero_add]
      by_cases hnear : |s - t₀| < δ
      · have hfs : f s < -η := hfε (by rw [Real.dist_eq]; linarith)
        have : ψ s ^ n * f s ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hψ0 n) (by linarith)
        linarith
      · push Not at hnear
        have hψρ := hfar s hs0 hnear
        calc ψ s ^ n * f s ≤ ψ s ^ n * |f s| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hψ0 n)
          _ = ψ s ^ (n - m) * (ψ s ^ m * |f s|) := by
              rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
          _ ≤ ρ ^ (n - m) * (ψ s ^ m * |f s|) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hψ0 hψρ _) (by positivity)
  -- the integral bound
  have hbound : ∀ n : ℕ, m ≤ n → 0 ≤ -η * ρ' ^ n * (2 * δ') + ρ ^ (n - m) * C := by
    intro n hn
    have hp := hmpos n hn
    have hψn : IntegrableOn (fun s => ψ s ^ n * f s) (Ioi 0) := by
      have h : IntegrableOn (fun s => (c ^ n)⁻¹ * (s ^ n * Real.exp (-(n / t₀ * s)) * f s)) (Ioi 0) :=
        (hint n (n / t₀) hp).const_mul ((c ^ n)⁻¹)
      refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
      dsimp only
      rw [pow_mul_exp_eq_laplacePeak_pow ht₀]
      field_simp
      ring
    have hnonneg : 0 ≤ ∫ s in Ioi (0 : ℝ), ψ s ^ n * f s := by
      have h := hpos n (n / t₀) hp
      have he : ∫ s in Ioi (0 : ℝ), s ^ n * Real.exp (-(n / t₀ * s)) * f s =
          c ^ n * ∫ s in Ioi (0 : ℝ), ψ s ^ n * f s := by
        rw [← integral_const_mul]
        exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by
          rw [pow_mul_exp_eq_laplacePeak_pow ht₀]; ring
      rw [he] at h
      exact (mul_nonneg_iff_of_pos_left (pow_pos hc n)).1 h
    have hind : IntegrableOn (I.indicator fun _ => -η * ρ' ^ n) (Ioi 0) :=
      ((continuous_const.integrableOn_Icc (μ := volume)).integrable_indicator
        measurableSet_Icc).integrableOn
    have hsum : IntegrableOn (fun s => I.indicator (fun _ => -η * ρ' ^ n) s +
        ρ ^ (n - m) * (ψ s ^ m * |f s|)) (Ioi 0) := hind.add (hψm.const_mul _)
    have hle := setIntegral_mono_on hψn hsum measurableSet_Ioi (hmaj n hn)
    have hvol : volume.real I = 2 * δ' := by
      simp only [I, measureReal_def, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring
    have hval : ∫ s in Ioi (0 : ℝ), (I.indicator (fun _ => -η * ρ' ^ n) s +
        ρ ^ (n - m) * (ψ s ^ m * |f s|)) = -η * ρ' ^ n * (2 * δ') + ρ ^ (n - m) * C := by
      rw [integral_add hind (hψm.const_mul _), integral_const_mul,
        setIntegral_indicator measurableSet_Icc, inter_eq_right.2 hIsub, setIntegral_const, hvol,
        smul_eq_mul, mul_comm (2 * δ')]
    linarith
  -- the contradiction
  have hlim : Tendsto (fun n : ℕ => (ρ / ρ') ^ n * (C / ρ ^ m)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ0.le hρ'0.le)
      ((div_lt_one hρ'0).2 hρρ')).mul_const (C / ρ ^ m)
    rwa [zero_mul] at this
  obtain ⟨n, hn1, hn2⟩ := ((hlim.eventually (gt_mem_nhds (show (0 : ℝ) < η * (2 * δ') by
    positivity))).and (eventually_ge_atTop m)).exists
  have hb := hbound n hn2
  have hρn : ρ ^ (n - m) = ρ ^ n / ρ ^ m := by
    rw [eq_div_iff (pow_pos hρ0 m).ne', ← pow_add, Nat.sub_add_cancel hn2]
  rw [hρn] at hb
  have hx : (ρ / ρ') ^ n * (C / ρ ^ m) * ρ' ^ n = ρ ^ n / ρ ^ m * C := by
    rw [div_pow]
    field_simp
  have := mul_lt_mul_of_pos_right hn1 (pow_pos hρ'0 n)
  rw [hx] at this
  nlinarith [pow_pos hρ'0 n]

end GaloisForLFunctions.HTGeometry
