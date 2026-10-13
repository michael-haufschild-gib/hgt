import GaloisForLFunctions.RHTower.WeilLagAlmostEverySpacingBlind
import GaloisForLFunctions.RHTower.WeilLagExponentialExceptionRigidity

/-!
# Subexponentially rare excursions are blind

**Theorem** (`exists_configuration_excursion_le`). Let `Θ > 0`, and let `f` be decreasing on
`[0, ∞)` with `Σ_b f(2^b) < ∞` (equivalently `∫^∞ f(t) dt/t < ∞`; e.g. `f(t) = (log t)^{−1−ε}`).
There is a configuration with positive summable weights and locally finite exponents `w_i`,
`0 < Re w_i < Θ`, whose lag function `Φ(t) = Re Σ_i c_i e^{t w_i}` satisfies
`|{t ∈ [k, k+1) : Φ(t) > 0}| ≤ e^{−f(k) k}` for all large `k`.

So exponential rarity of the excursions (`re_nonpos_of_integrableOn_exp_excursion`) cannot be
weakened to `e^{−f(t)t}` with `∫ f(t) dt/t < ∞`; the window `∫ f/t = ∞` is open.

**Construction (Fejér blocks with general parameters).** Block `b` carries the points
`δ_b + i(j − k)ω_b`, `j ≠ k < K_b`, with weights `c_b/(2K_b)`; its lag sum is
`(c_b e^{δ_b t}/2)(F_b(t) − 1)`. If `Φ(t) > 0`, then `t` lies in the thin window
`{|sin(ω_b t/2)| < ε_b}` of some block `b` before its horizon `τ_b`, provided
`(1/ε_b)² ≤ 2^{−b−1}K_b` and block `b + 1` dominates `2^{b+1}K_b` times block `b` after `τ_b`
(`exists_block_of_pos`). The parameters are `K_b = 2^{2^{b+m}}`, `c_{b+1} = c_b 2^{−b}/K_b`,
`ω_b = b + 1`, `ε_b = (2^{b+1}/K_b)^{1/2}`, `δ_b = Θ/2 + Σ_{j<b} g_j` with
`g_b = 16 f'(log K_b)`, `f' = max(f, (1+t)^{−1/2})`, and `τ_b = log(2^{2b+1}K_b²)/g_b`.
On `[τ_{b−1}, τ_b)` the windows of the blocks `≥ b` have measure `≲ ε_b τ_b ≤ e^{−f(t)t}`, and
`Σ g_b < ∞` is the condensation of `Σ f(2^b)`.
-/

open MeasureTheory Set Complex Filter Topology
open RHTower.AlmostEverySpacing

noncomputable section

namespace RHTower.SubexpExcursion

/-! ## Fejér blocks with general parameters -/

/-- The block parameters. -/
structure FejerData where
  K : ℕ → ℕ
  c : ℕ → ℝ
  δ : ℕ → ℝ
  ω : ℕ → ℝ
  ε : ℕ → ℝ
  τ : ℕ → ℝ

/-- The conditions confining positivity to thin windows. -/
structure FejerData.Good (D : FejerData) (Θ : ℝ) : Prop where
  K_two : ∀ b, 2 ≤ D.K b
  c_pos : ∀ b, 0 < D.c b
  δ_pos : ∀ b, 0 < D.δ b
  δ_lt : ∀ b, D.δ b < Θ
  ω_ge : ∀ b : ℕ, (b : ℝ) + 1 ≤ D.ω b
  ε_pos : ∀ b, 0 < D.ε b
  ε_K : ∀ b, (1 / D.ε b) ^ 2 ≤ (1 / 2 : ℝ) ^ (b + 1) * D.K b
  dom : ∀ b t, D.τ b ≤ t → 2 ^ (b + 1) * (D.K b : ℝ) * (D.c b * Real.exp (D.δ b * t)) ≤
    D.c (b + 1) * Real.exp (D.δ (b + 1) * t)
  sum_cK : Summable fun b => D.c b * D.K b
  τ_nonneg : ∀ b, 0 ≤ D.τ b

variable {D : FejerData} {Θ : ℝ}

theorem FejerData.Good.K_pos (hD : D.Good Θ) (b : ℕ) : (0 : ℝ) < D.K b := by
  have := hD.K_two b; exact_mod_cast (by omega : 0 < D.K b)

theorem FejerData.Good.ω_pos (hD : D.Good Θ) (b : ℕ) : 0 < D.ω b := by
  have := hD.ω_ge b; have := Nat.cast_nonneg (α := ℝ) b; linarith

/-- `a_b(t) = c_b e^{δ_b t}`. -/
def amp (D : FejerData) (b : ℕ) (t : ℝ) : ℝ := D.c b * Real.exp (D.δ b * t)

/-- `F_b(t) = |S_{K_b}(ω_b t)|² / K_b`. -/
def fej (D : FejerData) (b : ℕ) (t : ℝ) : ℝ := ‖dirSum (D.K b) (D.ω b * t)‖ ^ 2 / D.K b

/-- The lag value of block `b`: `(a_b/2)(F_b − 1)`. -/
def blockVal (D : FejerData) (b : ℕ) (t : ℝ) : ℝ := amp D b t / 2 * (fej D b t - 1)

/-- The lag function `Φ(t) = Σ_b (a_b(t)/2)(F_b(t) − 1)`. -/
def lag (D : FejerData) (t : ℝ) : ℝ := ∑' b, blockVal D b t

theorem amp_pos (hD : D.Good Θ) (b : ℕ) (t : ℝ) : 0 < amp D b t :=
  mul_pos (hD.c_pos b) (Real.exp_pos _)

theorem fej_nonneg (hD : D.Good Θ) (b : ℕ) (t : ℝ) : 0 ≤ fej D b t :=
  div_nonneg (sq_nonneg _) (hD.K_pos b).le

theorem fej_le (hD : D.Good Θ) (b : ℕ) (t : ℝ) : fej D b t ≤ D.K b := by
  unfold fej
  rw [div_le_iff₀ (hD.K_pos b)]
  have h := norm_dirSum_le (D.K b) (D.ω b * t)
  nlinarith [norm_nonneg (dirSum (D.K b) (D.ω b * t))]

theorem amp_le (hD : D.Good Θ) (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    amp D b t ≤ D.c b * Real.exp (Θ * t) :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (hD.δ_lt b).le ht)) (hD.c_pos b).le

theorem summable_amp (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) : Summable fun b => amp D b t := by
  refine Summable.of_nonneg_of_le (fun b => (amp_pos hD b t).le)
    (fun b => (amp_le hD b ht).trans ?_) (hD.sum_cK.mul_right (Real.exp (Θ * t)))
  have h1 : (1 : ℝ) ≤ D.K b := by have := hD.K_two b; exact_mod_cast (by omega : 1 ≤ D.K b)
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (hD.c_pos b).le h1) (Real.exp_pos _).le

theorem summable_amp_mul_fej (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => amp D b t * fej D b t := by
  refine Summable.of_nonneg_of_le (fun b => mul_nonneg (amp_pos hD b t).le (fej_nonneg hD b t))
    (fun b => ?_) (hD.sum_cK.mul_right (Real.exp (Θ * t)))
  calc amp D b t * fej D b t ≤ (D.c b * Real.exp (Θ * t)) * D.K b :=
        mul_le_mul (amp_le hD b ht) (fej_le hD b t) (fej_nonneg hD b t)
          (mul_pos (hD.c_pos b) (Real.exp_pos _)).le
    _ = D.c b * D.K b * Real.exp (Θ * t) := by ring

theorem lag_eq (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) :
    lag D t = ((∑' b, amp D b t * fej D b t) - ∑' b, amp D b t) / 2 := by
  unfold lag blockVal
  have h1 := summable_amp_mul_fej hD ht
  have h2 := summable_amp hD ht
  have : (fun b => amp D b t / 2 * (fej D b t - 1)) =
      fun b => (amp D b t * fej D b t - amp D b t) / 2 := by
    funext b; ring
  rw [this, tsum_div_const, h1.tsum_sub h2]

/-- Off its thin window a block is small: `F_b ≤ 2^{−b−1}` when `|sin(ω_b t/2)| ≥ ε_b`. -/
theorem fej_le_of_abs_sin_ge (hD : D.Good Θ) (b : ℕ) {t : ℝ}
    (h : D.ε b ≤ |Real.sin (D.ω b * t / 2)|) : fej D b t ≤ (1 / 2 : ℝ) ^ (b + 1) := by
  have hg := norm_dirSum_mul_abs_sin_le (D.K b) (D.ω b * t)
  have hε := hD.ε_pos b
  have hS0 := norm_nonneg (dirSum (D.K b) (D.ω b * t))
  have hS : ‖dirSum (D.K b) (D.ω b * t)‖ ≤ 1 / D.ε b := by
    rw [le_div_iff₀ hε]
    calc ‖dirSum (D.K b) (D.ω b * t)‖ * D.ε b
        ≤ ‖dirSum (D.K b) (D.ω b * t)‖ * |Real.sin (D.ω b * t / 2)| :=
          mul_le_mul_of_nonneg_left h hS0
      _ ≤ 1 := hg
  unfold fej
  rw [div_le_iff₀ (hD.K_pos b)]
  calc ‖dirSum (D.K b) (D.ω b * t)‖ ^ 2 ≤ (1 / D.ε b) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    _ ≤ (1 / 2 : ℝ) ^ (b + 1) * D.K b := hD.ε_K b

/-- **Where the lag function is positive.** If `Φ(t) > 0` for `t ≥ 0`, then `t` lies in the thin
window of a block before its horizon. -/
theorem exists_block_of_pos (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) (hpos : 0 < lag D t) :
    ∃ b, t < D.τ b ∧ |Real.sin (D.ω b * t / 2)| < D.ε b := by
  by_contra hno
  push Not at hno
  have hA := summable_amp hD ht
  set A := ∑' b, amp D b t with hAdef
  have hle : ∀ b, amp D b t ≤ A := fun b =>
    hA.le_tsum b fun j _ => (amp_pos hD j t).le
  have hbound : ∀ b, amp D b t * fej D b t ≤ (1 / 2 : ℝ) ^ (b + 1) * A := by
    intro b
    have hab := (amp_pos hD b t).le
    by_cases hτ : t < D.τ b
    · have hf := fej_le_of_abs_sin_ge hD b (hno b hτ)
      calc amp D b t * fej D b t ≤ amp D b t * (1 / 2 : ℝ) ^ (b + 1) :=
            mul_le_mul_of_nonneg_left hf hab
        _ ≤ A * (1 / 2 : ℝ) ^ (b + 1) := mul_le_mul_of_nonneg_right (hle b) (by positivity)
        _ = (1 / 2 : ℝ) ^ (b + 1) * A := by ring
    · push Not at hτ
      have hd := hD.dom b t hτ
      have h2 : (2 : ℝ) ^ (b + 1) * (1 / 2) ^ (b + 1) = 1 := by rw [← mul_pow]; norm_num
      calc amp D b t * fej D b t ≤ amp D b t * D.K b :=
            mul_le_mul_of_nonneg_left (fej_le hD b t) hab
        _ = (1 / 2 : ℝ) ^ (b + 1) * (2 ^ (b + 1) * D.K b * amp D b t) := by
            rw [← mul_assoc, ← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ (b + 1)), h2]; ring
        _ ≤ (1 / 2 : ℝ) ^ (b + 1) * amp D (b + 1) t :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ ≤ (1 / 2 : ℝ) ^ (b + 1) * A := mul_le_mul_of_nonneg_left (hle (b + 1)) (by positivity)
  have hgeom : Summable fun b : ℕ => (1 / 2 : ℝ) ^ (b + 1) * A :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)).mul_right A
  have hsum : ∑' b, amp D b t * fej D b t ≤ A := by
    calc ∑' b, amp D b t * fej D b t ≤ ∑' b : ℕ, (1 / 2 : ℝ) ^ (b + 1) * A :=
          (summable_amp_mul_fej hD ht).tsum_le_tsum hbound hgeom
      _ = A := by
          rw [tsum_mul_right]
          have : ∑' b : ℕ, (1 / 2 : ℝ) ^ (b + 1) = 1 := by
            simp_rw [pow_succ]
            rw [tsum_mul_right, tsum_geometric_two]
            norm_num
          rw [this, one_mul]
  rw [lag_eq hD ht] at hpos
  linarith

/-! ## Measure of the excursions in a unit interval -/

/-- The excursion set `{t ≥ 0 : Φ(t) > 0}`. -/
def posSet (D : FejerData) : Set ℝ := {t | 0 ≤ t ∧ 0 < lag D t}

/-- **Excursions in `[k, k+1)`.** Only the blocks with `k < τ_b` contribute, each by at most
`ε_b(k+1) + 4πε_b/ω_b`. -/
theorem volume_posSet_inter_le (hD : D.Good Θ) (k : ℝ) :
    volume (posSet D ∩ Ico k (k + 1)) ≤
      ∑' b, Set.indicator {b | k < D.τ b}
        (fun b => ENNReal.ofReal (D.ε b * (max k 0 + 1) + 4 * Real.pi * D.ε b / D.ω b)) b := by
  classical
  have hsub : posSet D ∩ Ico k (k + 1) ⊆
      ⋃ b, ({t : ℝ | 0 ≤ t ∧ t < D.τ b ∧ |Real.sin (D.ω b * t / 2)| < D.ε b} ∩ Ico k (k + 1)) := by
    rintro t ⟨⟨ht0, htp⟩, htk⟩
    obtain ⟨b, hb1, hb2⟩ := exists_block_of_pos hD ht0 htp
    exact mem_iUnion.mpr ⟨b, ⟨ht0, hb1, hb2⟩, htk⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun b => ?_))
  by_cases hb : k < D.τ b
  · rw [Set.indicator_of_mem (show b ∈ {b | k < D.τ b} from hb)]
    refine (measure_mono ?_).trans (volume_thinWindow_le (hD.ω_pos b) (hD.ε_pos b).le
      (by positivity : (0 : ℝ) ≤ max k 0 + 1))
    rintro t ⟨⟨ht0, _, hts⟩, htk⟩
    exact ⟨ht0, by linarith [htk.2, le_max_left k 0], hts⟩
  · rw [Set.indicator_of_notMem (show b ∉ {b | k < D.τ b} from hb)]
    have : {t : ℝ | 0 ≤ t ∧ t < D.τ b ∧ |Real.sin (D.ω b * t / 2)| < D.ε b} ∩ Ico k (k + 1) = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ico, mem_empty_iff_false, iff_false, not_and]
      intro hcon hkt _
      exact hb (lt_of_le_of_lt hkt hcon.2.1)
    rw [this, measure_empty]

/-! ## The configuration of a Fejér datum -/

/-- Index type: blocks `b` and ordered pairs `j ≠ k < K_b`. -/
abbrev Cfg (D : FejerData) := Σ b : ℕ, (offDiag (D.K b) : Set (ℕ × ℕ))

/-- The exponents `δ_b + i(j − k)ω_b`. -/
def cfgPoint (D : FejerData) (i : Cfg D) : ℂ :=
  (D.δ i.1 : ℂ) + I * ((((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * D.ω i.1 : ℝ)

/-- The weights `c_b/(2K_b)`. -/
def cfgWeight (D : FejerData) (i : Cfg D) : ℝ := D.c i.1 / (2 * D.K i.1)

theorem cfgWeight_pos (hD : D.Good Θ) (i : Cfg D) : 0 < cfgWeight D i := by
  unfold cfgWeight; have := hD.c_pos i.1; have := hD.K_pos i.1; positivity

theorem summable_cfgWeight_mul (hD : D.Good Θ) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun i : Cfg D => cfgWeight D i * C := by
  rw [summable_sigma_of_nonneg (fun i => mul_nonneg (cfgWeight_pos hD i).le hC)]
  refine ⟨fun b => Summable.of_finite, ?_⟩
  have hfib : ∀ b, ∑' p : (offDiag (D.K b) : Set (ℕ × ℕ)), cfgWeight D ⟨b, p⟩ * C =
      (offDiag (D.K b)).card * (D.c b / (2 * D.K b) * C) := by
    intro b
    simp [cfgWeight, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  simp_rw [hfib]
  refine Summable.of_nonneg_of_le (fun b => by
    have := hD.c_pos b; have := hD.K_pos b; positivity) (fun b => ?_)
    ((hD.sum_cK.mul_right C).div_const 2)
  have hK := hD.K_pos b
  have hc := hD.c_pos b
  calc ((offDiag (D.K b)).card : ℝ) * (D.c b / (2 * D.K b) * C)
      ≤ (D.K b * D.K b) * (D.c b / (2 * D.K b) * C) :=
        mul_le_mul_of_nonneg_right (card_offDiag_le _) (by positivity)
    _ = D.c b * D.K b * C / 2 := by field_simp

theorem summable_cfgWeight (hD : D.Good Θ) : Summable (cfgWeight D) := by
  simpa using summable_cfgWeight_mul hD 1 zero_le_one

theorem cexp_cfgPoint (D : FejerData) (i : Cfg D) (t : ℝ) :
    cexp (t * cfgPoint D i) = (Real.exp (D.δ i.1 * t) : ℂ) *
      cexp (I * ((((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * (D.ω i.1 * t) : ℝ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold cfgPoint
  push_cast
  ring

theorem norm_cfg_term_le (hD : D.Good Θ) (i : Cfg D) {t : ℝ} (ht : 0 ≤ t) :
    ‖(cfgWeight D i : ℂ) * cexp (t * cfgPoint D i)‖ ≤ cfgWeight D i * Real.exp (Θ * t) := by
  rw [cexp_cfgPoint, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cfgWeight_pos hD i), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp]
  have hre : (I * ((((i.2 : ℕ × ℕ).1 : ℝ) - (i.2 : ℕ × ℕ).2) * (D.ω i.1 * t) : ℝ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (hD.δ_lt i.1).le ht)) (cfgWeight_pos hD i).le

theorem blockVal_eq (hD : D.Good Θ) (b : ℕ) (t : ℝ) :
    blockVal D b t = D.c b / (2 * D.K b) * Real.exp (D.δ b * t) *
      (‖dirSum (D.K b) (D.ω b * t)‖ ^ 2 - D.K b) := by
  have hK := (hD.K_pos b).ne'
  unfold blockVal amp fej
  field_simp

theorem blockSum_eq (hD : D.Good Θ) (b : ℕ) (t : ℝ) :
    ∑ p : (offDiag (D.K b) : Set (ℕ × ℕ)),
        (cfgWeight D ⟨b, p⟩ : ℂ) * cexp (t * cfgPoint D ⟨b, p⟩) = (blockVal D b t : ℂ) := by
  have h := sum_offDiag_cexp (D.K b) (D.ω b * t)
  rw [← Finset.sum_coe_sort] at h
  have hw : ∀ p : (offDiag (D.K b) : Set (ℕ × ℕ)),
      (cfgWeight D ⟨b, p⟩ : ℂ) * cexp (t * cfgPoint D ⟨b, p⟩) =
        ((D.c b / (2 * D.K b) * Real.exp (D.δ b * t) : ℝ) : ℂ) *
          cexp (I * ((((p : ℕ × ℕ).1 : ℝ) - (p : ℕ × ℕ).2) * (D.ω b * t) : ℝ)) := by
    intro p
    rw [cexp_cfgPoint]
    simp only [cfgWeight]
    push_cast
    ring
  have h2 : ∑ p : (offDiag (D.K b) : Set (ℕ × ℕ)),
      cexp (I * ((((p : ℕ × ℕ).1 : ℝ) - (p : ℕ × ℕ).2) * (D.ω b * t) : ℝ)) =
        ((‖dirSum (D.K b) (D.ω b * t)‖ ^ 2 - D.K b : ℝ) : ℂ) := h
  rw [Finset.sum_congr rfl fun p _ => hw p, ← Finset.mul_sum, h2, blockVal_eq hD]
  push_cast
  ring

theorem summable_blockVal (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun b => blockVal D b t := by
  unfold blockVal
  have h1 := summable_amp_mul_fej hD ht
  have h2 := summable_amp hD ht
  exact ((h1.sub h2).div_const 2).congr fun b => by ring

/-- **The configuration sums to the block lag function.** -/
theorem hasSum_cfg (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun i : Cfg D => (cfgWeight D i : ℂ) * cexp (t * cfgPoint D i)) (lag D t : ℂ) := by
  have hs : Summable fun i : Cfg D => (cfgWeight D i : ℂ) * cexp (t * cfgPoint D i) :=
    Summable.of_norm_bounded (summable_cfgWeight_mul hD _ (Real.exp_pos _).le)
      fun i => norm_cfg_term_le hD i ht
  have hσ := hs.hasSum.sigma fun b => hasSum_fintype _
  simp_rw [blockSum_eq hD] at hσ
  have hb : HasSum (fun b => (blockVal D b t : ℂ)) (lag D t : ℂ) := by
    unfold lag
    exact Complex.hasSum_ofReal.mpr (summable_blockVal hD ht).hasSum
  have heq := hσ.unique hb
  rw [← heq]
  exact hs.hasSum

theorem lagRe_cfg (hD : D.Good Θ) {t : ℝ} (ht : 0 ≤ t) :
    OneSidedConfiguration.lagRe (fun i => (cfgWeight D i : ℂ)) (cfgPoint D) t = lag D t := by
  unfold OneSidedConfiguration.lagRe
  rw [(hasSum_cfg hD ht).tsum_eq, Complex.ofReal_re]

theorem cfgPoint_re (D : FejerData) (i : Cfg D) : (cfgPoint D i).re = D.δ i.1 := by
  unfold cfgPoint; simp

theorem one_le_abs_sub_of_mem_offDiag {K : ℕ} {p : ℕ × ℕ} (hp : p ∈ offDiag K) :
    1 ≤ |(p.1 : ℝ) - p.2| := by
  unfold AlmostEverySpacing.offDiag at hp
  rw [Finset.mem_filter] at hp
  rcases lt_or_gt_of_ne hp.2 with h | h
  · have : (p.1 : ℝ) + 1 ≤ p.2 := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : (p.2 : ℝ) + 1 ≤ p.1 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith

/-- **Local finiteness.** Block `b` lies at heights `≥ ω_b ≥ b + 1`. -/
theorem finite_cfgPoint (hD : D.Good Θ) (R : ℝ) : {i : Cfg D | ‖cfgPoint D i‖ ≤ R}.Finite := by
  refine ((Finset.range (⌊R⌋₊ + 1)).finite_toSet.biUnion fun b _ =>
    Set.finite_range (fun p : (offDiag (D.K b) : Set (ℕ × ℕ)) => (⟨b, p⟩ : Cfg D))).subset ?_
  rintro ⟨b, p⟩ hi
  simp only [mem_setOf_eq] at hi
  refine mem_iUnion₂.mpr ⟨b, ?_, ⟨p, rfl⟩⟩
  have him : |(cfgPoint D ⟨b, p⟩).im| ≤ R := (Complex.abs_im_le_norm _).trans hi
  have hval : (cfgPoint D ⟨b, p⟩).im = (((p : ℕ × ℕ).1 : ℝ) - (p : ℕ × ℕ).2) * D.ω b := by
    unfold cfgPoint; simp
  rw [hval, abs_mul, abs_of_pos (hD.ω_pos b)] at him
  have h1 := one_le_abs_sub_of_mem_offDiag p.2
  have h2 := hD.ω_ge b
  have hb : (b : ℝ) + 1 ≤ R := by nlinarith [abs_nonneg (((p : ℕ × ℕ).1 : ℝ) - (p : ℕ × ℕ).2)]
  rw [Finset.coe_range, mem_Iio]
  have : (b : ℝ) ≤ ⌊R⌋₊ := by
    have := Nat.lt_floor_add_one R
    exact_mod_cast Nat.le_floor (by linarith : (b : ℝ) ≤ R)
  exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast this)

/-! ## Parameters for a summable rate -/

/-- `f' = max(f, 1/(1 + t))`. -/
def fMod (f : ℝ → ℝ) (t : ℝ) : ℝ := max (f t) (1 / (1 + t))

theorem fMod_pos (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 < fMod f t :=
  lt_of_lt_of_le (by positivity) (le_max_right _ _)

theorem fMod_anti {f : ℝ → ℝ} (hf : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : fMod f t ≤ fMod f s :=
  max_le_max (hf s t hs hst) (one_div_le_one_div_of_le (by linarith) (by linarith))

theorem f_nonneg {f : ℝ → ℝ} (hf : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s)
    (hsum : Summable fun b : ℕ => f (2 ^ b)) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  by_contra hneg
  push Not at hneg
  have hev : ∀ᶠ b : ℕ in atTop, f t / 2 < f (2 ^ b) :=
    hsum.tendsto_atTop_zero.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ b : ℕ in atTop, t ≤ (2 : ℝ) ^ b :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop t
  obtain ⟨b, h1, h2⟩ := (hev.and hev2).exists
  have := hf t (2 ^ b) ht h2
  linarith

theorem summable_fMod {f : ℝ → ℝ} (hf : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s)
    (hsum : Summable fun b : ℕ => f (2 ^ b)) : Summable fun b : ℕ => fMod f (2 ^ b) := by
  refine Summable.of_nonneg_of_le (fun b => (fMod_pos f (by positivity)).le) (fun b => ?_)
    (hsum.add (summable_geometric_two))
  have h1 := f_nonneg hf hsum (t := 2 ^ b) (by positivity)
  have h2 : 1 / (1 + (2 : ℝ) ^ b) ≤ (1 / 2) ^ b := by
    rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]; linarith
  exact max_le (by linarith [h2, (show (0 : ℝ) ≤ (1 / 2) ^ b by positivity)]) (by linarith)

theorem exists_tail (f : ℝ → ℝ) {Θ : ℝ} (hΘ : 0 < Θ) :
    ∃ m : ℕ, 17 ≤ m ∧ ∑' b : ℕ, fMod f (2 ^ (b + m)) ≤ min (Θ / 64) (1 / 64) := by
  have ht := tendsto_sum_nat_add (fun b : ℕ => fMod f (2 ^ b))
  have hev := ht.eventually (Iic_mem_nhds (show (0 : ℝ) < min (Θ / 64) (1 / 64) by positivity))
  obtain ⟨m, hm⟩ := (hev.and (eventually_ge_atTop 17)).exists
  exact ⟨m, hm.2, hm.1⟩

/-- `K_b = 2^{2^{b+m}}`. -/
def Kp (m b : ℕ) : ℕ := 2 ^ (2 ^ (b + m))

/-- `g_b = 16 f'(2^{b+m})`. -/
def gp (f : ℝ → ℝ) (m b : ℕ) : ℝ := 16 * fMod f (2 ^ (b + m))

/-- The block parameters for the rate `f` and the shift `m`. -/
def params (Θ : ℝ) (f : ℝ → ℝ) (m : ℕ) : FejerData where
  K := Kp m
  c := fun b => ∏ j ∈ Finset.range b, ((1 / 2 : ℝ) ^ j / Kp m j)
  δ := fun b => Θ / 2 + ∑ j ∈ Finset.range b, gp f m j
  ω := fun b => b + 1
  ε := fun b => Real.sqrt (2 ^ (b + 1) / Kp m b)
  τ := fun b => Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) / gp f m b

theorem Kp_succ (m b : ℕ) : (Kp m (b + 1) : ℝ) = (Kp m b : ℝ) ^ 2 := by
  unfold Kp
  push_cast
  rw [← pow_mul, show b + 1 + m = (b + m) + 1 by ring, pow_succ]

theorem log_Kp (m b : ℕ) : Real.log (Kp m b) = 2 ^ (b + m) * Real.log 2 := by
  unfold Kp; push_cast; rw [Real.log_pow]; push_cast; ring

theorem Kp_eq_exp (m b : ℕ) : (Kp m b : ℝ) = Real.exp (2 ^ (b + m) * Real.log 2) := by
  rw [← log_Kp, Real.exp_log (by unfold Kp; positivity)]

theorem two_pow_ge (m b : ℕ) (hm : 1 ≤ m) : 2 * ((b : ℝ) + 1) ≤ 2 ^ (b + m) := by
  have h1 : (b : ℝ) + 1 ≤ 2 ^ b := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ≤ 2 ^ m := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  rw [pow_add]
  nlinarith

theorem Kp_ge (m b : ℕ) (hm : 2 ≤ m) : (8 : ℝ) ≤ Kp m b := by
  unfold Kp
  push_cast
  have h3 : (3 : ℕ) ≤ 2 ^ (b + m) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ b + m))
  calc (8 : ℝ) = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (2 ^ (b + m)) := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast h3)

section Params

variable {f : ℝ → ℝ} (hf : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s)
  (hsum : Summable fun b : ℕ => f (2 ^ b)) {Θ : ℝ} (hΘ : 0 < Θ) {m : ℕ} (hm : 17 ≤ m)
  (htail : ∑' b : ℕ, fMod f (2 ^ (b + m)) ≤ min (Θ / 64) (1 / 64))

include hf hsum in
theorem summable_gp : Summable fun b => gp f m b := by
  unfold gp
  exact ((summable_nat_add_iff m).mpr (summable_fMod hf hsum)).mul_left 16

theorem gp_pos (b : ℕ) : 0 < gp f m b := by
  unfold gp; exact mul_pos (by norm_num) (fMod_pos f (by positivity))

include hf hsum htail in
theorem gp_le (b : ℕ) : gp f m b ≤ 1 / 4 := by
  have hs : Summable fun b : ℕ => fMod f (2 ^ (b + m)) :=
    (summable_nat_add_iff m).mpr (summable_fMod hf hsum)
  have h1 : fMod f (2 ^ (b + m)) ≤ ∑' b : ℕ, fMod f (2 ^ (b + m)) :=
    hs.le_tsum b fun j _ => (fMod_pos f (by positivity)).le
  have h2 := min_le_right (Θ / 64) (1 / 64)
  unfold gp; linarith

include hf hsum htail in
theorem sum_gp_le (b : ℕ) : ∑ j ∈ Finset.range b, gp f m j ≤ Θ / 4 := by
  have h1 := (summable_gp hf hsum (m := m)).sum_le_tsum (Finset.range b)
    fun j _ => (gp_pos (f := f) (m := m) j).le
  have h2 : ∑' j, gp f m j = 16 * ∑' b : ℕ, fMod f (2 ^ (b + m)) := by
    unfold gp; rw [tsum_mul_left]
  have h3 := min_le_left (Θ / 64) (1 / 64)
  linarith

include hf in
theorem gp_anti (b : ℕ) : gp f m (b + 1) ≤ gp f m b := by
  unfold gp
  have : (2 : ℝ) ^ (b + m) ≤ 2 ^ (b + 1 + m) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith [fMod_anti hf (s := 2 ^ (b + m)) (t := 2 ^ (b + 1 + m)) (by positivity) this]

theorem params_c_succ (b : ℕ) : (params Θ f m).c (b + 1) =
    (params Θ f m).c b * ((1 / 2 : ℝ) ^ b / Kp m b) := by
  simp only [params, Finset.prod_range_succ]

theorem params_δ_succ (b : ℕ) : (params Θ f m).δ (b + 1) = (params Θ f m).δ b + gp f m b := by
  simp only [params, Finset.sum_range_succ]; ring

theorem params_c_pos (b : ℕ) : 0 < (params Θ f m).c b := by
  simp only [params]
  exact Finset.prod_pos fun j _ => by unfold Kp; positivity

include hm in
theorem params_cK_le (b : ℕ) :
    (params Θ f m).c b * Kp m b ≤ 2 * Kp m 0 * (1 / 2 : ℝ) ^ b := by
  induction b with
  | zero => simp only [params, Finset.range_zero, Finset.prod_empty, one_mul, pow_zero, mul_one]
            have := Kp_ge m 0 (by omega); linarith
  | succ b ih =>
    rw [params_c_succ, Kp_succ]
    have hK := Kp_ge m b (by omega)
    have hc := params_c_pos (Θ := Θ) (f := f) (m := m) b
    have e : (params Θ f m).c b * ((1 / 2 : ℝ) ^ b / Kp m b) * (Kp m b : ℝ) ^ 2 =
        ((params Θ f m).c b * Kp m b) * (1 / 2 : ℝ) ^ b := by field_simp
    rw [e]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [pow_zero, mul_one, zero_add, pow_one]
      have h0 : (params Θ f m).c 0 * Kp m 0 = Kp m 0 := by simp [params]
      rw [h0]; linarith
    · have hpow : (1 / 2 : ℝ) ^ b * (1 / 2) ^ b ≤ (1 / 2) ^ (b + 1) := by
        rw [← pow_add]; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc ((params Θ f m).c b * Kp m b) * (1 / 2 : ℝ) ^ b
          ≤ (2 * Kp m 0 * (1 / 2 : ℝ) ^ b) * (1 / 2) ^ b :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = 2 * Kp m 0 * ((1 / 2 : ℝ) ^ b * (1 / 2) ^ b) := by ring
        _ ≤ 2 * Kp m 0 * (1 / 2) ^ (b + 1) :=
            mul_le_mul_of_nonneg_left hpow (by have := Kp_ge m 0 (by omega); positivity)

include hf hsum hΘ hm htail in
theorem params_good : (params Θ f m).Good Θ where
  K_two b := by have := Kp_ge m b (by omega); exact_mod_cast (show (2 : ℝ) ≤ Kp m b by linarith)
  c_pos b := params_c_pos b
  δ_pos b := by
    simp only [params]
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range b) => (gp_pos (f := f) (m := m) j).le
    linarith
  δ_lt b := by simp only [params]; linarith [sum_gp_le hf hsum htail b]
  ω_ge b := le_rfl
  ε_pos b := Real.sqrt_pos.mpr (by unfold Kp; positivity)
  ε_K b := by
    simp only [params]
    have hK : (0 : ℝ) < Kp m b := by unfold Kp; positivity
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    field_simp
    rw [one_div_pow]
    field_simp
    ring_nf
    exact le_rfl
  dom b t ht := by
    simp only [params] at ht ⊢
    have hg := gp_pos (f := f) (m := m) b
    have hK : (0 : ℝ) < Kp m b := by unfold Kp; positivity
    have hX : (0 : ℝ) < 2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2 := by positivity
    have hlog : Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) ≤ gp f m b * t := by
      rw [div_le_iff₀ hg] at ht; linarith
    have hexp : 2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2 ≤ Real.exp (gp f m b * t) := by
      rw [← Real.exp_log hX]; exact Real.exp_le_exp.mpr hlog
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    set C := ∏ j ∈ Finset.range b, ((1 / 2 : ℝ) ^ j / Kp m j) with hC
    set δ := Θ / 2 + ∑ j ∈ Finset.range b, gp f m j with hδ
    have hC0 : 0 < C := Finset.prod_pos fun j _ => by unfold Kp; positivity
    have hsplit : Real.exp ((Θ / 2 + (∑ j ∈ Finset.range b, gp f m j + gp f m b)) * t) =
        Real.exp (δ * t) * Real.exp (gp f m b * t) := by
      rw [← Real.exp_add]; congr 1; rw [hδ]; ring
    rw [hsplit]
    have hpow : (2 : ℝ) ^ (b + 1) * (Kp m b : ℝ) =
        (1 / 2 : ℝ) ^ b / Kp m b * (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) := by
      field_simp
      rw [one_div_pow]
      field_simp
      ring
    calc 2 ^ (b + 1) * (Kp m b : ℝ) * (C * Real.exp (δ * t))
        = C * Real.exp (δ * t) * ((1 / 2 : ℝ) ^ b / Kp m b) *
            (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) := by rw [hpow]; ring
      _ ≤ C * Real.exp (δ * t) * ((1 / 2 : ℝ) ^ b / Kp m b) * Real.exp (gp f m b * t) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * ((1 / 2 : ℝ) ^ b / Kp m b) * (Real.exp (δ * t) * Real.exp (gp f m b * t)) := by
          ring
  sum_cK := by
    refine Summable.of_nonneg_of_le (fun b => mul_nonneg (params_c_pos b).le
      (by positivity)) (fun b => params_cK_le hm b)
      (summable_geometric_two.mul_left ((2 : ℝ) * Kp m 0))
  τ_nonneg b := by
    simp only [params]
    have hK : (1 : ℝ) ≤ Kp m b := by have := Kp_ge m b (by omega); linarith
    have : (1 : ℝ) ≤ 2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hK)
    exact div_nonneg (Real.log_nonneg this) (gp_pos b).le

theorem params_ε_sq (b : ℕ) : ((params Θ f m).ε b) ^ 2 = 2 ^ (b + 1) / Kp m b := by
  simp only [params]; exact Real.sq_sqrt (by unfold Kp; positivity)

include hm in
theorem params_ε_succ_le (b : ℕ) : (params Θ f m).ε (b + 1) ≤ (params Θ f m).ε b / 2 := by
  have hK := Kp_ge m b (by omega)
  have h0 : 0 ≤ (params Θ f m).ε b := by simp only [params]; exact Real.sqrt_nonneg _
  have hsq : ((params Θ f m).ε (b + 1)) ^ 2 ≤ ((params Θ f m).ε b / 2) ^ 2 := by
    rw [div_pow, params_ε_sq, params_ε_sq, Kp_succ]
    have hKpos : (0 : ℝ) < Kp m b := by linarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have e : (2 : ℝ) ^ (b + 1 + 1) = 2 ^ (b + 1) * 2 := pow_succ _ _
    rw [e]
    have h2 : (0 : ℝ) < 2 ^ (b + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hK (le_of_lt (mul_pos h2 hKpos))]
  have h1 : 0 ≤ (params Θ f m).ε (b + 1) := by simp only [params]; exact Real.sqrt_nonneg _
  nlinarith

include hm in
theorem params_ε_le_geom (b j : ℕ) :
    (params Θ f m).ε (b + j) ≤ (params Θ f m).ε b * (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc (params Θ f m).ε (b + (j + 1)) = (params Θ f m).ε (b + j + 1) := by rw [add_assoc]
      _ ≤ (params Θ f m).ε (b + j) / 2 := params_ε_succ_le hm _
      _ ≤ (params Θ f m).ε b * (1 / 2 : ℝ) ^ j / 2 := by linarith
      _ = (params Θ f m).ε b * (1 / 2 : ℝ) ^ (j + 1) := by ring

theorem log_params_X (b : ℕ) :
    Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) =
      (2 * b + 1) * Real.log 2 + 2 * (2 ^ (b + m) * Real.log 2) := by
  rw [Real.log_mul (by positivity) (by unfold Kp; positivity), Real.log_pow, Real.log_pow, log_Kp]
  push_cast; ring

include hf hsum htail in
theorem params_τ_ge (b : ℕ) : (2 : ℝ) ^ (b + 1 + m) ≤ (params Θ f m).τ b := by
  simp only [params]
  have hg := gp_pos (f := f) (m := m) b
  have hg4 := gp_le hf hsum htail b
  have hl := Real.log_two_gt_d9
  rw [le_div_iff₀ hg, log_params_X]
  have h1 : (2 : ℝ) ^ (b + 1 + m) = 2 * 2 ^ (b + m) := by
    rw [show b + 1 + m = (b + m) + 1 by ring, pow_succ]; ring
  have h2 : (0 : ℝ) ≤ 2 ^ (b + m) := by positivity
  have h3 : (0 : ℝ) ≤ (2 * b + 1) * Real.log 2 := by positivity
  rw [h1]
  nlinarith

include hf hm in
theorem params_τ_mono : Monotone (params Θ f m).τ := by
  refine monotone_nat_of_le_succ fun b => ?_
  simp only [params]
  have hg := gp_pos (f := f) (m := m) b
  have hg1 := gp_pos (f := f) (m := m) (b + 1)
  have hanti := gp_anti hf (m := m) b
  have hK := Kp_ge m b (by omega)
  have hnum : Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) ≤
      Real.log (2 ^ (2 * (b + 1) + 1) * (Kp m (b + 1) : ℝ) ^ 2) := by
    rw [log_params_X, log_params_X]
    have : (2 : ℝ) ^ (b + m) ≤ 2 ^ (b + 1 + m) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hl := Real.log_two_gt_d9
    push_cast
    nlinarith
  have hn0 : 0 ≤ Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) := by
    rw [log_params_X]; have := Real.log_two_gt_d9; positivity
  exact div_le_div₀ (hn0.trans hnum) hnum hg1 hanti

include hm in
/-- **The window budget at one scale.** `2ε_b(τ_b + 1 + 4π) ≤ (2^{2b+1}K_b²)^{−1/16}`. -/
theorem params_key (b : ℕ) :
    2 * (params Θ f m).ε b * ((params Θ f m).τ b + 1 + 4 * Real.pi) ≤
      Real.exp (-(Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) / 16)) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 2 ^ (b + m) * Real.log 2 := ⟨_, rfl⟩
  have hl := Real.log_two_gt_d9
  have hl1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hpow : (2 : ℝ) ^ 17 ≤ 2 ^ (b + m) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hL : 90000 ≤ L := by rw [hLdef]; nlinarith
  have hb2 := two_pow_ge m b (by omega)
  have hX : Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) = (2 * b + 1) * Real.log 2 + 2 * L := by
    rw [log_params_X, hLdef]
  have hX0 : 0 ≤ Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) := by rw [hX]; positivity
  have hX3 : Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) ≤ 3 * L := by
    rw [hX, hLdef]
    have : (2 * (b : ℝ) + 1) ≤ 2 ^ (b + m) := by linarith
    nlinarith
  have h2L : (2 : ℝ) ^ (b + m) ≤ 2 * L := by rw [hLdef]; nlinarith
  -- `τ_b ≤ L²`
  have hτ : (params Θ f m).τ b ≤ L ^ 2 := by
    simp only [params]
    have hg := gp_pos (f := f) (m := m) b
    have hgl : 16 / (1 + 2 ^ (b + m)) ≤ gp f m b := by
      unfold gp
      have := le_max_right (f (2 ^ (b + m))) (1 / (1 + (2 : ℝ) ^ (b + m)))
      unfold fMod
      rw [div_eq_mul_one_div 16]
      linarith
    have h1 : Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) / gp f m b ≤
        Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) * (1 + 2 ^ (b + m)) / 16 := by
      rw [div_le_iff₀ hg]
      have h16 : (16 : ℝ) / (1 + 2 ^ (b + m)) * (1 + 2 ^ (b + m)) = 16 := by
        field_simp
      have := mul_le_mul_of_nonneg_left hgl
        (show 0 ≤ Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) * (1 + 2 ^ (b + m)) / 16 by
          positivity)
      calc Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2)
          = Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) * (1 + 2 ^ (b + m)) / 16 *
              (16 / (1 + 2 ^ (b + m))) := by field_simp
        _ ≤ _ := this
    calc Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) / gp f m b
        ≤ Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) * (1 + 2 ^ (b + m)) / 16 := h1
      _ ≤ 3 * L * (1 + 2 * L) / 16 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul hX3 (by linarith) (by positivity) (by linarith)
      _ ≤ L ^ 2 := by nlinarith
  -- `ε_b ≤ e^{−L/4}`
  have hε : (params Θ f m).ε b ≤ Real.exp (-(L / 4)) := by
    have hK : (Kp m b : ℝ) = Real.exp L := by rw [Kp_eq_exp, hLdef]
    have h2b : (2 : ℝ) ^ (b + 1) ≤ Real.exp (L / 2) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (b + 1)), Real.log_pow]
      apply Real.exp_le_exp.mpr
      rw [hLdef]; push_cast; nlinarith
    have hsq : 2 ^ (b + 1) / (Kp m b : ℝ) ≤ Real.exp (-(L / 4)) ^ 2 := by
      rw [hK, div_le_iff₀ (Real.exp_pos _), ← Real.exp_nat_mul, ← Real.exp_add]
      calc (2 : ℝ) ^ (b + 1) ≤ Real.exp (L / 2) := h2b
        _ = Real.exp (((2 : ℕ) : ℝ) * -(L / 4) + L) := by congr 1; push_cast; ring
    simp only [params]
    calc Real.sqrt (2 ^ (b + 1) / (Kp m b : ℝ)) ≤ Real.sqrt (Real.exp (-(L / 4)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.exp (-(L / 4)) := Real.sqrt_sq (Real.exp_pos _).le
  -- `2(L² + 14) ≤ e^{L/16}`
  have hexp : 2 * (L ^ 2 + 14) ≤ Real.exp (L / 16) := by
    have h := Real.pow_div_factorial_le_exp (x := L / 16) (by positivity) 3
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6] at h
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    nlinarith
  have hπ := Real.pi_lt_d2
  have hε0 : 0 ≤ (params Θ f m).ε b := by simp only [params]; exact Real.sqrt_nonneg _
  have hτ0 : 0 ≤ (params Θ f m).τ b := by
    simp only [params]; exact div_nonneg hX0 (gp_pos b).le
  calc 2 * (params Θ f m).ε b * ((params Θ f m).τ b + 1 + 4 * Real.pi)
      ≤ 2 * Real.exp (-(L / 4)) * (L ^ 2 + 14) := by
        have : (params Θ f m).τ b + 1 + 4 * Real.pi ≤ L ^ 2 + 14 := by linarith
        have h1 : 0 ≤ (params Θ f m).τ b + 1 + 4 * Real.pi := by positivity
        calc 2 * (params Θ f m).ε b * ((params Θ f m).τ b + 1 + 4 * Real.pi)
            ≤ 2 * Real.exp (-(L / 4)) * ((params Θ f m).τ b + 1 + 4 * Real.pi) :=
              mul_le_mul_of_nonneg_right (by linarith) h1
          _ ≤ 2 * Real.exp (-(L / 4)) * (L ^ 2 + 14) :=
              mul_le_mul_of_nonneg_left this (by positivity)
    _ = Real.exp (-(L / 4)) * (2 * (L ^ 2 + 14)) := by ring
    _ ≤ Real.exp (-(L / 4)) * Real.exp (L / 16) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ = Real.exp (-(3 * L / 16)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(Real.log (2 ^ (2 * b + 1) * (Kp m b : ℝ) ^ 2) / 16)) :=
        Real.exp_le_exp.mpr (by linarith)

end Params

/-! ## The theorem -/

theorem zero_one_mem_offDiag_of_two_le {K : ℕ} (hK : 2 ≤ K) : ((0, 1) : ℕ × ℕ) ∈ offDiag K := by
  unfold AlmostEverySpacing.offDiag
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, ne_eq, zero_ne_one,
    not_false_eq_true, and_true]
  omega

theorem hasSum_shifted_geom (C : ℝ) (n : ℕ) :
    HasSum (fun j : ℕ => if n ≤ j then C * (1 / 2 : ℝ) ^ (j - n) else 0) (2 * C) := by
  rw [← hasSum_nat_add_iff' n]
  have h0 : ∑ i ∈ Finset.range n, (if n ≤ i then C * (1 / 2 : ℝ) ^ (i - n) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [if_neg]; rw [Finset.mem_range] at hi; omega
  rw [h0, sub_zero]
  have h1 : (fun i : ℕ => if n ≤ i + n then C * (1 / 2 : ℝ) ^ (i + n - n) else 0) =
      fun i => C * (1 / 2 : ℝ) ^ i := by
    funext i; rw [if_pos (by omega), Nat.add_sub_cancel]
  rw [h1]
  have h2 := hasSum_geometric_two.mul_left C
  rw [mul_comm]
  exact h2

/-- **Subexponentially rare excursions are blind.** For `f` decreasing on `[0, ∞)` with
`Σ_b f(2^b) < ∞` and `Θ > 0`, there is a positive locally finite configuration with
`0 < Re w_i < Θ` whose excursion set `{Φ > 0}` meets `[k, k+1)` in measure `≤ e^{−f(k)k}` for all
large `k`. -/
theorem exists_configuration_excursion_le {Θ : ℝ} (hΘ : 0 < Θ) {f : ℝ → ℝ}
    (hf : ∀ s t, 0 ≤ s → s ≤ t → f t ≤ f s) (hsum : Summable fun b : ℕ => f (2 ^ b)) :
    ∃ (ι : Type) (c : ι → ℝ) (w : ι → ℂ), Nonempty ι ∧ (∀ i, 0 < c i) ∧ Summable c ∧
      (∀ R : ℝ, {i | ‖w i‖ ≤ R}.Finite) ∧ (∀ i, 0 < (w i).re ∧ (w i).re < Θ) ∧
      ∀ᶠ k : ℕ in atTop, volume {t ∈ Ico (k : ℝ) (k + 1) |
          0 < OneSidedConfiguration.lagRe (fun i => (c i : ℂ)) w t} ≤
        ENNReal.ofReal (Real.exp (-(f k * k))) := by
  classical
  obtain ⟨m, hm, htail⟩ := exists_tail f hΘ
  have hD : (params Θ f m).Good Θ := params_good hf hsum hΘ hm htail
  refine ⟨Cfg (params Θ f m), cfgWeight (params Θ f m), cfgPoint (params Θ f m),
    ⟨⟨0, ⟨(0, 1), zero_one_mem_offDiag_of_two_le (hD.K_two 0)⟩⟩⟩, cfgWeight_pos hD,
    summable_cfgWeight hD, finite_cfgPoint hD,
    fun i => ⟨by rw [cfgPoint_re]; exact hD.δ_pos _, by rw [cfgPoint_re]; exact hD.δ_lt _⟩, ?_⟩
  filter_upwards [eventually_ge_atTop ⌈(params Θ f m).τ 0⌉₊] with k hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hτk : (params Θ f m).τ 0 ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hsub : {t ∈ Ico (k : ℝ) (k + 1) | 0 < OneSidedConfiguration.lagRe
      (fun i => (cfgWeight (params Θ f m) i : ℂ)) (cfgPoint (params Θ f m)) t} ⊆
        posSet (params Θ f m) ∩ Ico (k : ℝ) (k + 1) := by
    rintro t ⟨ht, hpos⟩
    have ht0 : 0 ≤ t := hk0.trans ht.1
    exact ⟨⟨ht0, by rwa [lagRe_cfg hD ht0] at hpos⟩, ht⟩
  -- the first block alive at `k`
  have hex : ∃ b, (k : ℝ) < (params Θ f m).τ b := ⟨k, by
    have h1 := params_τ_ge hf hsum htail (Θ := Θ) k
    have h2 : (k : ℝ) < 2 ^ (k + 1 + m) :=
      calc (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
        _ ≤ 2 ^ (k + 1 + m) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = Nat.find hex := ⟨_, rfl⟩
  have hbk : (k : ℝ) < (params Θ f m).τ b := hbdef ▸ Nat.find_spec hex
  have hb1 : b ≠ 0 := by
    rintro rfl; linarith
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hprev : (params Θ f m).τ b' ≤ k := by
    have := Nat.find_min hex (show b' < Nat.find hex by omega)
    push Not at this; exact this
  -- the real bound `2C ≤ e^{−f(k)k}`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ((k : ℝ) + 1 + 4 * Real.pi) * (params Θ f m).ε (b' + 1) :=
    ⟨_, rfl⟩
  have hε1 := (hD.ε_pos (b' + 1)).le
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have h2C : 2 * C ≤ Real.exp (-(f k * k)) := by
    have hkey := params_key (Θ := Θ) (f := f) hm (b' + 1)
    have h1 : 2 * C ≤
        Real.exp (-(Real.log (2 ^ (2 * (b' + 1) + 1) * (Kp m (b' + 1) : ℝ) ^ 2) / 16)) := by
      calc 2 * C = 2 * (params Θ f m).ε (b' + 1) * ((k : ℝ) + 1 + 4 * Real.pi) := by
            rw [hC]; ring
        _ ≤ 2 * (params Θ f m).ε (b' + 1) * ((params Θ f m).τ (b' + 1) + 1 + 4 * Real.pi) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ _ := hkey
    have hfk : f k * k ≤ Real.log (2 ^ (2 * (b' + 1) + 1) * (Kp m (b' + 1) : ℝ) ^ 2) / 16 := by
      have hτge := params_τ_ge hf hsum htail (Θ := Θ) b'
      have hmod1 : f k ≤ fMod f k := le_max_left _ _
      have hmod2 : fMod f k ≤ fMod f (2 ^ (b' + 1 + m)) :=
        fMod_anti hf (by positivity) (hτge.trans hprev)
      have hg := gp_pos (f := f) (m := m) (b' + 1)
      have hτdef : (params Θ f m).τ (b' + 1) =
          Real.log (2 ^ (2 * (b' + 1) + 1) * (Kp m (b' + 1) : ℝ) ^ 2) / gp f m (b' + 1) := rfl
      have hgp : gp f m (b' + 1) = 16 * fMod f (2 ^ (b' + 1 + m)) := rfl
      calc f k * k ≤ fMod f k * k := mul_le_mul_of_nonneg_right hmod1 hk0
        _ ≤ fMod f (2 ^ (b' + 1 + m)) * (params Θ f m).τ (b' + 1) :=
            mul_le_mul hmod2 hbk.le hk0 (fMod_pos f (by positivity)).le
        _ = Real.log (2 ^ (2 * (b' + 1) + 1) * (Kp m (b' + 1) : ℝ) ^ 2) / 16 := by
            rw [hτdef, hgp]
            have := fMod_pos f (t := 2 ^ (b' + 1 + m)) (by positivity)
            field_simp
    exact h1.trans (Real.exp_le_exp.mpr (by linarith))
  -- termwise bound by the shifted geometric series
  have hterm : ∀ j : ℕ, Set.indicator {j | (k : ℝ) < (params Θ f m).τ j}
      (fun j => ENNReal.ofReal ((params Θ f m).ε j * (max (k : ℝ) 0 + 1) +
        4 * Real.pi * (params Θ f m).ε j / (params Θ f m).ω j)) j ≤
      ENNReal.ofReal (if b' + 1 ≤ j then C * (1 / 2 : ℝ) ^ (j - (b' + 1)) else 0) := by
    intro j
    by_cases hj : (k : ℝ) < (params Θ f m).τ j
    · rw [Set.indicator_of_mem (show j ∈ {j | (k : ℝ) < (params Θ f m).τ j} from hj)]
      have hjb : Nat.find hex ≤ j := Nat.find_min' hex hj
      rw [if_pos (by omega)]
      apply ENNReal.ofReal_le_ofReal
      have hε0 := (hD.ε_pos j).le
      have hgeo := params_ε_le_geom (Θ := Θ) (f := f) hm (b' + 1) (j - (b' + 1))
      rw [show b' + 1 + (j - (b' + 1)) = j by omega] at hgeo
      rw [max_eq_left hk0]
      have hω1 : (1 : ℝ) ≤ (params Θ f m).ω j := by
        have := hD.ω_ge j; have := Nat.cast_nonneg (α := ℝ) j; linarith
      have h4 : 4 * Real.pi * (params Θ f m).ε j / (params Θ f m).ω j ≤
          4 * Real.pi * (params Θ f m).ε j := div_le_self (by positivity) hω1
      calc (params Θ f m).ε j * ((k : ℝ) + 1) +
            4 * Real.pi * (params Θ f m).ε j / (params Θ f m).ω j
          ≤ ((k : ℝ) + 1 + 4 * Real.pi) * (params Θ f m).ε j := by nlinarith
        _ ≤ ((k : ℝ) + 1 + 4 * Real.pi) *
              ((params Θ f m).ε (b' + 1) * (1 / 2 : ℝ) ^ (j - (b' + 1))) :=
            mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = C * (1 / 2 : ℝ) ^ (j - (b' + 1)) := by rw [hC]; ring
    · rw [Set.indicator_of_notMem (show j ∉ {j | (k : ℝ) < (params Θ f m).τ j} from hj)]
      exact zero_le
  have hgeom := hasSum_shifted_geom C (b' + 1)
  have ha0 : ∀ j : ℕ, 0 ≤ (if b' + 1 ≤ j then C * (1 / 2 : ℝ) ^ (j - (b' + 1)) else 0) :=
    fun j => by split_ifs <;> positivity
  calc volume {t ∈ Ico (k : ℝ) (k + 1) | 0 < OneSidedConfiguration.lagRe
        (fun i => (cfgWeight (params Θ f m) i : ℂ)) (cfgPoint (params Θ f m)) t}
      ≤ volume (posSet (params Θ f m) ∩ Ico (k : ℝ) (k + 1)) := measure_mono hsub
    _ ≤ _ := volume_posSet_inter_le hD k
    _ ≤ ∑' j, ENNReal.ofReal (if b' + 1 ≤ j then C * (1 / 2 : ℝ) ^ (j - (b' + 1)) else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (2 * C) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hgeom.summable, hgeom.tsum_eq]
    _ ≤ ENNReal.ofReal (Real.exp (-(f k * k))) := ENNReal.ofReal_le_ofReal h2C

end RHTower.SubexpExcursion
