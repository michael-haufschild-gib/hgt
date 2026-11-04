import GaloisForLFunctions.ZeroConfigurationGeometry.EulerStagesRepelAboveTheHorizon

/-!
# Symmetric halves are phase lattices

The mechanism of `EulerStagesRepelAboveTheHorizon` and `EulerStagesAreCountedByTheirPhase`
needs only four properties of the half `A`. A **symmetric half** (`SymmetricHalf`) is a function
`A` that is holomorphic and zero-free on `Re z > 0`, with logarithmic derivative `L = A'/A`, and
real on the real axis: `A(z̄) = conj A(z)`. Its symmetrization `Λ_A(z) = A(z) + A(1 − z)` satisfies
the functional equation `Λ_A(1 − z) = Λ_A(z)` and is real on the critical line, where it equals
`2 Re A(½ + it)` (`sym_linePt`).

* **The phase lattice** (`line_eq_mul_exp`, `sym_eq_zero_iff_phase`). `A(½+it) = A(½+it₀)
  exp(i Θ(t))` with `Θ(t) = ∫_{t₀}^t L(½+iτ) dτ`. From a zero `t₀` on the line, `t` is a zero of
  `Λ_A` iff `Re Θ(t) ∈ πℤ`.
* **Simplicity** (`sym_deriv_ne_zero`). A zero on the line where `Re L > 0` is simple.
* **Gaps** (`sym_ne_zero_of_phase_lt`, `exists_sym_zero_of_phase_ge`). After a zero, the next one
  comes exactly when the phase has turned by `π`.
* **The count** (`ncard_sym_zeros`). Where `Re L > 0`, the zeros in `[t₀, T]` after a zero `t₀`
  number `⌊Re Θ(T)/π⌋ + 1`.
* **Dominance near the line** (`norm_lt_of_speed_pos`, `sym_ne_zero_near_line`). If
  `Re L(½+w+it) + Re L(½−w−it) > 0` for `0 ≤ w ≤ u₀`, then `|A(½+u+it)| > |A(½−u−it)|` for
  `0 < u ≤ u₀`, so `Λ_A` has no zero at height `t` with `0 < |Re z − ½| ≤ u₀`.

Everything is sign-free on the configuration: positions follow from the phase speed of `A`
alone. The instances are the finite Euler stages and every finite Dirichlet carrier with real
coefficients (`FiniteCarriersAreRealAboveTheirHorizon`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- A **symmetric half**: holomorphic and zero-free on `Re z > 0` with logarithmic derivative
`L`, and real on the real axis. -/
structure SymmetricHalf where
  /-- the half -/
  A : ℂ → ℂ
  /-- its logarithmic derivative on `Re z > 0` -/
  L : ℂ → ℂ
  hasDerivAt : ∀ z : ℂ, 0 < z.re → HasDerivAt A (A z * L z) z
  ne_zero : ∀ z : ℂ, 0 < z.re → A z ≠ 0
  conj_eq : ∀ z : ℂ, A (conj z) = conj (A z)

namespace SymmetricHalf

variable (H : SymmetricHalf)

/-- The symmetrization `Λ_A(z) = A(z) + A(1 − z)`. -/
def sym (z : ℂ) : ℂ := H.A z + H.A (1 - z)

/-- The half along the critical line. -/
def line (t : ℝ) : ℂ := H.A (linePt t)

/-- The phase speed `L(½ + it)`. -/
def speed (t : ℝ) : ℂ := H.L (linePt t)

theorem sym_one_sub (z : ℂ) : H.sym (1 - z) = H.sym z := by
  unfold sym; rw [sub_sub_cancel]; ring

theorem line_ne_zero (t : ℝ) : H.line t ≠ 0 := H.ne_zero _ (linePt_re_pos t)

/-- On the critical line `Λ_A = 2 Re A`. -/
theorem sym_linePt (t : ℝ) : H.sym (linePt t) = ((2 * (H.line t).re : ℝ) : ℂ) := by
  rw [sym, one_sub_linePt, H.conj_eq, add_conj, line]

theorem hasDerivAt_line (t : ℝ) : HasDerivAt H.line (I * H.line t * H.speed t) t := by
  have h := (H.hasDerivAt _ (linePt_re_pos t)).comp t (hasDerivAt_linePt t)
  refine h.congr_deriv ?_
  simp only [line, speed]
  ring

theorem continuous_line : Continuous H.line :=
  continuous_iff_continuousAt.mpr fun t => (H.hasDerivAt_line t).continuousAt

/-- The phase speed is continuous: `L = A'/A` with `A` holomorphic and zero-free. -/
theorem continuous_speed : Continuous H.speed := by
  set U : Set ℂ := {s | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ H.A U := fun s hs =>
    (H.hasDerivAt s hs).differentiableAt.differentiableWithinAt
  have hq : ContinuousOn (fun s => deriv H.A s / H.A s) U :=
    ((hd.deriv hUo).continuousOn).div hd.continuousOn fun s hs => H.ne_zero s hs
  have hcont := hq.comp_continuous continuous_linePt linePt_re_pos
  refine hcont.congr fun t => ?_
  show deriv H.A (linePt t) / H.A (linePt t) = H.L (linePt t)
  rw [(H.hasDerivAt _ (linePt_re_pos t)).deriv,
    mul_div_cancel_left₀ _ (H.ne_zero _ (linePt_re_pos t))]

theorem continuous_re_speed : Continuous fun τ => (H.speed τ).re :=
  Complex.continuous_re.comp H.continuous_speed

/-! ### The phase law -/

/-- The phase integral `Θ(t) = ∫_{t₀}^t L(½ + iτ) dτ`. -/
def phase (t₀ t : ℝ) : ℂ := ∫ τ in t₀..t, H.speed τ

theorem hasDerivAt_phase (t₀ τ : ℝ) : HasDerivAt (H.phase t₀) (H.speed τ) τ :=
  (H.continuous_speed.integral_hasStrictDerivAt t₀ τ).hasDerivAt

theorem phase_self (t₀ : ℝ) : H.phase t₀ t₀ = 0 := intervalIntegral.integral_same

/-- **The phase law.** `A(½+it) = A(½+it₀) exp(i Θ(t))`. -/
theorem line_eq_mul_exp (t₀ t : ℝ) : H.line t = H.line t₀ * cexp (I * H.phase t₀ t) := by
  set k : ℝ → ℂ := fun τ => H.line τ * cexp (-(I * H.phase t₀ τ)) with hk
  have hkd : ∀ τ, HasDerivAt k 0 τ := by
    intro τ
    have := (H.hasDerivAt_line τ).mul (((H.hasDerivAt_phase t₀ τ).const_mul I).neg.cexp)
    refine this.congr_deriv ?_
    ring
  have hconst := is_const_of_deriv_eq_zero (fun τ => (hkd τ).differentiableAt)
    (fun τ => (hkd τ).deriv) t t₀
  simp only [hk, H.phase_self, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  calc H.line t = H.line t * cexp (-(I * H.phase t₀ t)) * cexp (I * H.phase t₀ t) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [hconst]

theorem re_phase (t₀ t : ℝ) : (H.phase t₀ t).re = ∫ τ in t₀..t, (H.speed τ).re := by
  rw [phase, ← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    (H.continuous_speed.intervalIntegrable _ _)]
  simp only [Complex.reCLM_apply]

theorem continuous_phase_re (t₀ : ℝ) : Continuous fun t => (H.phase t₀ t).re :=
  Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun τ =>
    (H.hasDerivAt_phase t₀ τ).continuousAt)

/-- After a zero `t₀` on the line, `Re A(½+it) = −b e^{−Im Θ(t)} sin(Re Θ(t))`. -/
theorem re_line_of_zero {t₀ : ℝ} (h0 : (H.line t₀).re = 0) (t : ℝ) :
    (H.line t).re = -(H.line t₀).im * Real.exp (-(H.phase t₀ t).im) *
      Real.sin (H.phase t₀ t).re := by
  have hc : H.line t₀ = (((H.line t₀).im : ℝ) : ℂ) * I :=
    Complex.ext (by simp [h0]) (by simp)
  set b := (H.line t₀).im with hb
  rw [H.line_eq_mul_exp t₀ t, hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul, one_mul, mul_one, sub_zero,
    zero_sub, add_zero, zero_add]
  ring

theorem line_re_eq_zero_of_sym {t : ℝ} (h : H.sym (linePt t) = 0) : (H.line t).re = 0 := by
  rw [H.sym_linePt] at h
  have := Complex.ofReal_eq_zero.mp h
  linarith

/-- **The phase lattice.** From a zero `t₀` on the line, `t` is a zero of `Λ_A` iff
`Re Θ(t) ∈ πℤ`. -/
theorem sym_eq_zero_iff_phase {t₀ : ℝ} (h0 : H.sym (linePt t₀) = 0) (t : ℝ) :
    H.sym (linePt t) = 0 ↔ ∃ k : ℤ, (H.phase t₀ t).re = k * Real.pi := by
  have hre0 := H.line_re_eq_zero_of_sym h0
  have hb : (H.line t₀).im ≠ 0 := fun h => H.line_ne_zero t₀ (Complex.ext hre0 h)
  have hE := (Real.exp_pos (-(H.phase t₀ t).im)).ne'
  rw [H.sym_linePt, Complex.ofReal_eq_zero, H.re_line_of_zero hre0]
  simp only [mul_eq_zero, neg_eq_zero, two_ne_zero, hb, hE, false_or, Real.sin_eq_zero_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- **No zero before a half turn.** -/
theorem sym_ne_zero_of_phase_lt {t₀ t : ℝ} (h0 : H.sym (linePt t₀) = 0) (ht : t₀ < t)
    (hpos : ∀ τ ∈ Ioo t₀ t, 0 < (H.speed τ).re)
    (hlt : ∫ τ in t₀..t, (H.speed τ).re < Real.pi) : H.sym (linePt t) ≠ 0 := by
  intro hz
  obtain ⟨k, hk⟩ := (H.sym_eq_zero_iff_phase h0 t).mp hz
  have hint : 0 < ∫ τ in t₀..t, (H.speed τ).re :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (H.continuous_re_speed.intervalIntegrable _ _) hpos ht
  rw [H.re_phase] at hk
  rw [hk] at hint hlt
  have h1 : (0 : ℝ) < k := by
    by_contra hneg
    have : (k : ℝ) * Real.pi ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) Real.pi_pos.le
    linarith
  have h2 : (k : ℝ) < 1 := by
    by_contra hge
    have : Real.pi ≤ (k : ℝ) * Real.pi := le_mul_of_one_le_left Real.pi_pos.le (not_lt.mp hge)
    linarith
  have h1' : (0 : ℤ) < k := by exact_mod_cast h1
  have h2' : k < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- **A zero in every half turn.** -/
theorem exists_sym_zero_of_phase_ge {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hge : Real.pi ≤ ∫ τ in t₀..t, (H.speed τ).re) :
    ∃ τ ∈ Icc t₀ t, H.sym (linePt τ) = 0 := by
  obtain ⟨τ₁, hτ₁, hθ⟩ : ∃ τ₁ ∈ Icc t₀ t, (H.phase t₀ τ₁).re = Real.pi :=
    intermediate_value_Icc ht (H.continuous_phase_re t₀).continuousOn
      ⟨by simp only [H.phase_self, Complex.zero_re]; exact Real.pi_pos.le,
        by rw [H.re_phase]; exact hge⟩
  have hflip : (H.line τ₁).re = -Real.exp (-(H.phase t₀ τ₁).im) * (H.line t₀).re := by
    rw [H.line_eq_mul_exp t₀ τ₁]
    have he : cexp (I * H.phase t₀ τ₁) = -((Real.exp (-(H.phase t₀ τ₁).im) : ℝ) : ℂ) :=
      Complex.ext (by simp [Complex.exp_re, hθ]) (by simp [Complex.exp_im, hθ])
    rw [he]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hcre : ContinuousOn (fun τ => (H.line τ).re) (Icc t₀ τ₁) :=
    (Complex.continuous_re.comp H.continuous_line).continuousOn
  have hexp := Real.exp_pos (-(H.phase t₀ τ₁).im)
  have hsub : Icc t₀ τ₁ ⊆ Icc t₀ t := Icc_subset_Icc le_rfl hτ₁.2
  rcases le_total 0 (H.line t₀).re with hnn | hnp
  · obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc' hτ₁.1 hcre
      (show (0 : ℝ) ∈ Icc (H.line τ₁).re (H.line t₀).re from ⟨by rw [hflip]; nlinarith, hnn⟩)
    refine ⟨τ, hsub hτ, ?_⟩
    simp only at hτ0
    rw [H.sym_linePt, hτ0, mul_zero, Complex.ofReal_zero]
  · obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc hτ₁.1 hcre
      (show (0 : ℝ) ∈ Icc (H.line t₀).re (H.line τ₁).re from ⟨hnp, by rw [hflip]; nlinarith⟩)
    refine ⟨τ, hsub hτ, ?_⟩
    simp only at hτ0
    rw [H.sym_linePt, hτ0, mul_zero, Complex.ofReal_zero]

/-- **Zeros with positive phase speed are simple.** -/
theorem sym_deriv_ne_zero {t₀ : ℝ} (h0 : H.sym (linePt t₀) = 0) (hpos : 0 < (H.speed t₀).re) :
    deriv H.sym (linePt t₀) ≠ 0 := by
  have hre0 := H.line_re_eq_zero_of_sym h0
  have hb : (H.line t₀).im ≠ 0 := fun h => H.line_ne_zero t₀ (Complex.ext hre0 h)
  set s₀ := linePt t₀ with hs₀
  have h1s : 0 < (1 - s₀).re := by rw [hs₀, one_sub_linePt, conj_re, linePt_re]; norm_num
  have hA := H.hasDerivAt _ (linePt_re_pos t₀)
  have hB := (H.hasDerivAt _ h1s).comp s₀ ((hasDerivAt_id s₀).const_sub 1)
  have hΛ : HasDerivAt H.sym _ s₀ := hA.add hB
  have hline := hΛ.comp t₀ (hasDerivAt_linePt t₀)
  have hre : HasDerivAt (fun t => ((2 * (H.line t).re : ℝ) : ℂ))
      (((2 * (I * H.line t₀ * H.speed t₀).re : ℝ)) : ℂ) t₀ :=
    ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt t₀ (H.hasDerivAt_line t₀)).const_mul
      2).ofReal_comp
  have hfun : (H.sym ∘ linePt) = fun t => ((2 * (H.line t).re : ℝ) : ℂ) :=
    funext fun t => H.sym_linePt t
  rw [hfun] at hline
  have huniq := hline.unique hre
  rw [hΛ.deriv]
  intro hD
  rw [hD, zero_mul] at huniq
  have hval : (I * H.line t₀ * H.speed t₀).re = -(H.line t₀).im * (H.speed t₀).re := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hre0]
    ring
  rw [hval] at huniq
  have h2 : 2 * (-(H.line t₀).im * (H.speed t₀).re) = 0 := by exact_mod_cast huniq.symm
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hb (neg_eq_zero.mp h')
    · exact hpos.ne' h'

/-- **The phase is strictly increasing where the speed is positive.** -/
theorem phase_re_strictMonoOn {t₀ : ℝ} (hpos : ∀ τ, t₀ ≤ τ → 0 < (H.speed τ).re) :
    StrictMonoOn (fun t => (H.phase t₀ t).re) (Ici t₀) := by
  intro s hs t _ hst
  have hi := fun a b => H.continuous_re_speed.intervalIntegrable (μ := volume) a b
  simp only
  rw [H.re_phase, H.re_phase,
    ← intervalIntegral.integral_add_adjacent_intervals (hi t₀ s) (hi s t)]
  have := intervalIntegral.intervalIntegral_pos_of_pos_on (hi s t)
    (fun τ hτ => hpos τ ((mem_Ici.mp hs).trans hτ.1.le)) hst
  linarith

/-- **The exact count.** Where the phase speed is positive, the zeros of `Λ_A` on the line at
heights in `[t₀, T]` after a zero `t₀` number exactly `⌊Re Θ(T)/π⌋ + 1`. -/
theorem ncard_sym_zeros {t₀ T : ℝ} (hpos : ∀ τ, t₀ ≤ τ → 0 < (H.speed τ).re)
    (h0 : H.sym (linePt t₀) = 0) (hT : t₀ ≤ T) :
    {t ∈ Icc t₀ T | H.sym (linePt t) = 0}.ncard = ⌊(H.phase t₀ T).re / Real.pi⌋₊ + 1 := by
  set Φ : ℝ → ℝ := fun t => (H.phase t₀ t).re with hΦdef
  have hmono : StrictMonoOn Φ (Icc t₀ T) :=
    (H.phase_re_strictMonoOn hpos).mono Icc_subset_Ici_self
  have hcont : ContinuousOn Φ (Icc t₀ T) := (H.continuous_phase_re t₀).continuousOn
  have hΦ0 : Φ t₀ = 0 := by simp [hΦdef, H.phase_self]
  have hT0 : 0 ≤ Φ T := hΦ0 ▸ hmono.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  set N := ⌊Φ T / Real.pi⌋₊ with hN
  have himage : Φ '' {t ∈ Icc t₀ T | H.sym (linePt t) = 0} =
      (fun k : ℕ => (k : ℝ) * Real.pi) '' ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨t, ⟨htI, hz⟩, rfl⟩
      obtain ⟨k, hk⟩ := (H.sym_eq_zero_iff_phase h0 t).mp hz
      have h1 : 0 ≤ Φ t := hΦ0 ▸ hmono.monotoneOn ⟨le_rfl, hT⟩ htI htI.1
      have h2 : Φ t ≤ Φ T := hmono.monotoneOn htI ⟨hT, le_rfl⟩ htI.2
      have hk' : Φ t = k * Real.pi := hk
      have hk0 : 0 ≤ k := by
        by_contra hneg
        have : (k : ℝ) * Real.pi < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast not_le.mp hneg) Real.pi_pos
        linarith
      have hkcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
      refine ⟨k.toNat, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.le_floor ?_))), ?_⟩
      · rw [hkcast, le_div_iff₀ Real.pi_pos]; linarith
      · simp only; rw [hkcast, hk']
    · rintro ⟨k, hk, rfl⟩
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_coe.mp hk))
      have hle : (k : ℝ) * Real.pi ≤ Φ T := by
        have h1 : (k : ℝ) ≤ Φ T / Real.pi :=
          (Nat.cast_le.mpr hkN).trans (Nat.floor_le (div_nonneg hT0 Real.pi_pos.le))
        rwa [le_div_iff₀ Real.pi_pos] at h1
      obtain ⟨t, htI, ht⟩ := intermediate_value_Icc hT hcont ⟨by rw [hΦ0]; positivity, hle⟩
      exact ⟨t, ⟨htI, (H.sym_eq_zero_iff_phase h0 t).mpr ⟨k, by
        have : Φ t = (k : ℝ) * Real.pi := ht
        rw [show (H.phase t₀ t).re = Φ t from rfl, this]; push_cast; ring⟩⟩, ht⟩
  have hinj : Function.Injective fun k : ℕ => (k : ℝ) * Real.pi := fun a b h => by
    have := mul_right_cancel₀ Real.pi_ne_zero h
    exact_mod_cast this
  rw [← (hmono.injOn.mono fun t ht => ht.1).ncard_image, himage,
    Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]

/-! ### Dominance near the line -/

theorem hasDerivAt_log_norm_path {c v : ℂ} {u : ℝ} (hre : 0 < (c + u * v).re) :
    HasDerivAt (fun w : ℝ => Real.log ‖H.A (c + w * v)‖) ((v * H.L (c + u * v)).re) u := by
  have hpath : HasDerivAt (fun w : ℝ => c + (w : ℂ) * v) v u := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const v).const_add c
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using h
  have hA := (H.hasDerivAt _ hre).comp u hpath
  have hlog := _root_.RHTower.hasDerivAt_log_norm_comp hA (H.ne_zero _ hre)
  refine hlog.congr_deriv ?_
  simp only [Function.comp_apply]
  congr 1
  field_simp [H.ne_zero _ hre]

/-- **Dominance.** If `Re L(½+w+it) + Re L(½−w−it) > 0` for `0 ≤ w ≤ u₀ < ½`, then
`|A(½+u+it)| > |A(½−u−it)|` for `0 < u ≤ u₀`. -/
theorem norm_lt_of_speed_pos {u₀ t : ℝ} (hu₀ : u₀ < 1 / 2)
    (hspeed : ∀ w ∈ Icc (0 : ℝ) u₀, 0 < (H.L (((1 / 2 + w : ℝ) : ℂ) + t * I)).re +
      (H.L (((1 / 2 - w : ℝ) : ℂ) + (-t : ℝ) * I)).re)
    {u : ℝ} (hu : 0 < u) (huu : u ≤ u₀) :
    ‖H.A (((1 / 2 - u : ℝ) : ℂ) + (-t : ℝ) * I)‖ < ‖H.A (((1 / 2 + u : ℝ) : ℂ) + t * I)‖ := by
  set cp : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I with hcp
  set cm : ℂ := ((1 / 2 : ℝ) : ℂ) + (-t : ℝ) * I with hcm
  have hpt : ∀ w : ℝ, cp + w * 1 = ((1 / 2 + w : ℝ) : ℂ) + t * I := fun w => by
    rw [hcp]; push_cast; ring
  have hmt : ∀ w : ℝ, cm + w * (-1) = ((1 / 2 - w : ℝ) : ℂ) + (-t : ℝ) * I := fun w => by
    rw [hcm]; push_cast; ring
  set g : ℝ → ℝ := fun w => Real.log ‖H.A (cp + w * 1)‖ - Real.log ‖H.A (cm + w * (-1))‖
    with hg
  have hre_p : ∀ w : ℝ, 0 ≤ w → 0 < (cp + w * 1).re := fun w hw => by
    rw [hpt]; simp; linarith
  have hre_m : ∀ w : ℝ, w < 1 / 2 → 0 < (cm + w * (-1)).re := fun w hw => by
    rw [hmt]; simp; linarith
  have hderiv : ∀ w ∈ Icc (0 : ℝ) u₀, HasDerivAt g
      ((1 * H.L (cp + w * 1)).re - ((-1) * H.L (cm + w * (-1))).re) w := fun w hw =>
    (H.hasDerivAt_log_norm_path (hre_p w hw.1)).sub
      (H.hasDerivAt_log_norm_path (hre_m w (by linarith [hw.2])))
  have hpos : ∀ w ∈ Icc (0 : ℝ) u₀,
      0 < (1 * H.L (cp + w * 1)).re - ((-1) * H.L (cm + w * (-1))).re := by
    intro w hw
    rw [one_mul, neg_one_mul, Complex.neg_re, sub_neg_eq_add, hpt, hmt]
    exact hspeed w hw
  have hcont : ContinuousOn g (Icc 0 u) := fun w hw =>
    (hderiv w ⟨hw.1, hw.2.trans huu⟩).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ hu hcont
    (fun w hw => hderiv w ⟨hw.1.le, hw.2.le.trans huu⟩)
  have hg0 : g 0 = 0 := by
    simp only [hg, Complex.ofReal_zero, zero_mul, add_zero]
    have hconj : cm = conj cp := by
      rw [hcm, hcp]; apply Complex.ext <;> simp
    rw [hconj, H.conj_eq, Complex.norm_conj, sub_self]
  have hgu : 0 < g u := by
    have hp := hpos c ⟨hc.1.le, hc.2.le.trans huu⟩
    rw [hslope, hg0, sub_zero, sub_zero] at hp
    exact (div_pos_iff_of_pos_right hu).mp hp
  have hm := hre_m u (by linarith)
  have hp := hre_p u hu.le
  simp only [hg] at hgu
  rw [hmt] at hm hgu
  rw [hpt] at hp hgu
  exact (Real.log_lt_log_iff (norm_pos_iff.mpr (H.ne_zero _ hm))
    (norm_pos_iff.mpr (H.ne_zero _ hp))).mp (by linarith)

/-- **No zero near the line at a dominated height.** If the speed condition of
`norm_lt_of_speed_pos` holds at heights `t` and `−t`, then `Λ_A` has no zero at height `t` with
`0 < |Re z − ½| ≤ u₀`. -/
theorem sym_ne_zero_near_line {u₀ t : ℝ} (hu₀ : u₀ < 1 / 2)
    (hspeed : ∀ τ : ℝ, |τ| = |t| → ∀ w ∈ Icc (0 : ℝ) u₀,
      0 < (H.L (((1 / 2 + w : ℝ) : ℂ) + τ * I)).re + (H.L (((1 / 2 - w : ℝ) : ℂ) + (-τ : ℝ) * I)).re)
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσu : |σ - 1 / 2| ≤ u₀) :
    H.sym ((σ : ℂ) + t * I) ≠ 0 := by
  have key : ∀ τ : ℝ, |τ| = |t| → ∀ u : ℝ, 0 < u → u ≤ u₀ →
      H.sym (((1 / 2 + u : ℝ) : ℂ) + τ * I) ≠ 0 := by
    intro τ hτ u hu huu h
    have hlt := H.norm_lt_of_speed_pos hu₀ (hspeed τ hτ) hu huu
    have hrefl : 1 - (((1 / 2 + u : ℝ) : ℂ) + τ * I) = ((1 / 2 - u : ℝ) : ℂ) + (-τ : ℝ) * I := by
      push_cast; ring
    unfold sym at h
    rw [hrefl, add_eq_zero_iff_eq_neg] at h
    rw [h, norm_neg] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne (abs_pos.mp hσ) with hlt | hgt
  · rw [← H.sym_one_sub]
    have hrefl : 1 - ((σ : ℂ) + t * I) = ((1 / 2 + (1 / 2 - σ) : ℝ) : ℂ) + (-t : ℝ) * I := by
      push_cast; ring
    rw [hrefl]
    rw [abs_of_neg (by linarith)] at hσu
    exact key (-t) (abs_neg t) (1 / 2 - σ) (by linarith) (by linarith)
  · rw [abs_of_pos (by linarith)] at hσu
    have h := key t rfl (σ - 1 / 2) (by linarith) hσu
    rwa [show ((1 / 2 + (σ - 1 / 2) : ℝ) : ℂ) = (σ : ℂ) by push_cast; ring] at h

end SymmetricHalf

end GaloisForLFunctions.ZeroConfigurationGeometry
