import GaloisForLFunctions.RHTower.HerglotzProducerAtomDomination
import GaloisForLFunctions.RHTower.WeilAtomicExplicitFormula
import GaloisForLFunctions.RHTower.WeilBoundaryIntegerCountingRigidity

/-!
# A Herglotz Weil function makes the weights full-cone Weil-positive

Let `lam` be real with `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, and let `Φ` be holomorphic on `Re s > ½`
with `Re Φ ≥ 0` there and `Φ = Φ_lam` (the Weil function) on `Re s > 1`.

**Theorem** (`weilPositiveFull_of_herglotz`).  `lam` is full-cone Weil-positive.

This is the converse of `herglotzWeilPositive_of_weilPositiveFull`: Herglotz
positivity of the Weil function and full-cone Weil positivity are equivalent.

**Proof.**
* In the disc chart `w = (2s − 3)/(2s + 1)`, `Re Φ` is the Poisson integral of a finite measure `ν`
  (`exists_poissonRepresentation_halfPlane`).  Since `Φ(s̄) = conj Φ(s)`, the symmetrised
  Herglotz–Riesz kernel `K_sym(s, ζ) = ½(K(s, ζ) + K(s, ζ̄))`, `K(s, ζ) = (ζ + w)/(ζ − w)`, also
  represents `Re Φ`.  Its integral `Ψ` is holomorphic, so `Φ − Ψ` is a holomorphic function with
  zero real part, hence an imaginary constant.
* For `ζ ≠ 1` on the circle, put `iγ = (1 + ζ)/(1 − ζ)`.  Then
  `K_sym(s, ζ) = ½(1 + γ²) g_{½+iγ}(s)` with `g_{z₀}(s) = 1/(s − z₀) + 1/(s − 1 + z₀)`, and
  `K_sym(s, 1) = s − ½`.
* By the line-integral form of the Weil functional and Fubini, `W_lam(f ⋆ f̃)` is the
  `ν`-integral of the line integrals of `(H(s) + H(1 − s)) K_sym(s, ζ)` on `Re s = 5/4`, plus the
  imaginary constant times a real number.  The two-line residue identity evaluates the atoms with
  `ζ ≠ 1` to `½(1 + γ²)(|f̂(γ)|² + |f̂(−γ)|²) ≥ 0`.  The point `ζ = 1` contributes a line integral
  of `(s − ½)(H(s) + H(1 − s))`, which moves to the critical line and is purely imaginary there.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal ComplexConjugate

noncomputable section

namespace RHTower.AtomDomination

open GaloisForLFunctions.HTGeometry Zeta23 Zeta23.WeilEF RHTower.WeilLineIntegral RHTower.WeilAtomic

/-! ## The Herglotz–Riesz kernel in the half-plane chart -/

/-- The Herglotz–Riesz kernel `(ζ + w)/(ζ − w)` at `w = (2s − 3)/(2s + 1)`. -/
def hrKernel (s ζ : ℂ) : ℂ := (ζ + discPt s) / (ζ - discPt s)

/-- The kernel symmetrised under `ζ ↦ ζ̄`. -/
def symKernel (s ζ : ℂ) : ℂ := (hrKernel s ζ + hrKernel s (conj ζ)) / 2

theorem discPt_ne_of_norm_eq_one {s ζ : ℂ} (hs : 1 / 2 < s.re) (hζ : ‖ζ‖ = 1) :
    ζ - discPt s ≠ 0 := by
  intro h
  have : ζ = discPt s := by linear_combination h
  have h1 := norm_discPt_lt_one hs
  rw [← this, hζ] at h1
  exact lt_irrefl _ h1

theorem re_hrKernel (s ζ : ℂ) :
    (hrKernel s ζ).re = poissonKernel 0 (discPt s) ζ := by
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := discPt s)) ζ
  rw [h, Function.comp_apply, herglotzRieszKernel_def]
  simp [hrKernel]

theorem discPt_conj (s : ℂ) : discPt (conj s) = conj (discPt s) := by
  simp [discPt, map_div₀, map_ofNat]

theorem poissonKernel_conj_right (w ζ : ℂ) :
    poissonKernel 0 w (conj ζ) = poissonKernel 0 (conj w) ζ := by
  rw [poissonKernel_def, poissonKernel_def]
  simp only [sub_zero, Complex.norm_conj]
  congr 2
  rw [show conj ζ - w = conj (ζ - conj w) by simp, Complex.norm_conj]

/-- `K(s, 1) = s − ½`. -/
theorem hrKernel_one {s : ℂ} (hs : 2 * s + 1 ≠ 0) : hrKernel s 1 = s - 1 / 2 := by
  unfold hrKernel discPt
  have e1 : (1 : ℂ) + (2 * s - 3) / (2 * s + 1) = (4 * s - 2) / (2 * s + 1) := by
    rw [eq_div_iff hs, add_mul, div_mul_cancel₀ _ hs]
    ring
  have e2 : (1 : ℂ) - (2 * s - 3) / (2 * s + 1) = 4 / (2 * s + 1) := by
    rw [eq_div_iff hs, sub_mul, div_mul_cancel₀ _ hs]
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hs]
  ring

theorem symKernel_one {s : ℂ} (hs : 2 * s + 1 ≠ 0) : symKernel s 1 = s - 1 / 2 := by
  unfold symKernel
  rw [map_one, hrKernel_one hs]
  ring

/-- The circle parameter `u = (1 + ζ)/(1 − ζ)` is purely imaginary for `|ζ| = 1`, `ζ ≠ 1`. -/
theorem re_cayleyParam {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) : ((1 + ζ) / (1 - ζ)).re = 0 := by
  have hw1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hn : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have := Complex.sq_norm ζ
    rw [hζ, normSq_apply] at this
    nlinarith
  rw [div_re]
  simp only [add_re, one_re, sub_re, add_im, one_im, sub_im]
  have : (1 + ζ.re) * (1 - ζ.re) / normSq (1 - ζ) + (0 + ζ.im) * (0 - ζ.im) / normSq (1 - ζ) =
      (1 - (ζ.re ^ 2 + ζ.im ^ 2)) / normSq (1 - ζ) := by
    field_simp
    ring
  rw [this, hn, sub_self, zero_div]

/-- The ordinate attached to a circle point `ζ ≠ 1`: `iγ = (1 + ζ)/(1 − ζ)`. -/
def circleOrd (ζ : ℂ) : ℝ := ((1 + ζ) / (1 - ζ)).im

theorem cayleyParam_eq {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) :
    (1 + ζ) / (1 - ζ) = (circleOrd ζ : ℂ) * I := by
  apply Complex.ext
  · rw [re_cayleyParam hζ h1]
    simp
  · simp [circleOrd]

/-- `K(s, ζ) = (1 + γ²)/(s − ½ − iγ) − iγ` for `|ζ| = 1`, `ζ ≠ 1`. -/
theorem hrKernel_eq {s ζ : ℂ} (hs : 1 / 2 < s.re) (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) :
    hrKernel s ζ = (1 + (circleOrd ζ : ℂ) ^ 2) / (s - 1 / 2 - circleOrd ζ * I) -
      circleOrd ζ * I := by
  have hs0 := two_mul_add_one_ne_zero (s := s) (by linarith)
  have hζ1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hu := cayleyParam_eq hζ h1
  set γ : ℝ := circleOrd ζ
  have hden : s - 1 / 2 - γ * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd : (γ : ℂ) * I + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hζeq : ζ = ((γ : ℂ) * I - 1) / ((γ : ℂ) * I + 1) := by
    rw [eq_div_iff hd, ← hu]
    field_simp
    ring
  have hN : ((γ : ℂ) * I - 1) * (2 * s + 1) - ((γ : ℂ) * I + 1) * (2 * s - 3) ≠ 0 := by
    have e : ((γ : ℂ) * I - 1) * (2 * s + 1) - ((γ : ℂ) * I + 1) * (2 * s - 3) =
        -4 * (s - 1 / 2 - γ * I) := by ring
    rw [e]
    exact mul_ne_zero (by norm_num) hden
  have hstep : hrKernel s ζ = (1 - γ * I * (s - 1 / 2)) / (s - 1 / 2 - γ * I) := by
    unfold hrKernel discPt
    rw [hζeq, div_add_div _ _ hd hs0, div_sub_div _ _ hd hs0,
      div_div_div_cancel_right₀ (mul_ne_zero hd hs0), div_eq_div_iff hN hden]
    ring_nf
  rw [hstep, eq_sub_iff_add_eq, div_add' _ _ _ hden]
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-- `K_sym(s, ζ) = ½(1 + γ²) g_{½+iγ}(s)` for `|ζ| = 1`, `ζ ≠ 1`. -/
theorem symKernel_eq {s ζ : ℂ} (hs : 1 / 2 < s.re) (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) :
    symKernel s ζ = (1 + (circleOrd ζ : ℂ) ^ 2) / 2 * gPair (1 / 2 + circleOrd ζ * I) s := by
  have hζc : ‖conj ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  have h1c : conj ζ ≠ 1 := fun h => h1 (by rw [← conj_conj ζ, h, map_one])
  have hord : circleOrd (conj ζ) = -circleOrd ζ := by
    unfold circleOrd
    have : (1 + conj ζ) / (1 - conj ζ) = conj ((1 + ζ) / (1 - ζ)) := by
      rw [map_div₀, map_add, map_sub, map_one]
    rw [this, Complex.conj_im]
  have hden1 : s - 1 / 2 - circleOrd ζ * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hden2 : s - 1 / 2 + circleOrd ζ * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  unfold symKernel gPair
  rw [hrKernel_eq hs hζ h1, hrKernel_eq hs hζc h1c, hord]
  have e1 : s - (1 / 2 + (circleOrd ζ : ℂ) * I) = s - 1 / 2 - circleOrd ζ * I := by ring
  have e2 : s - (1 - (1 / 2 + (circleOrd ζ : ℂ) * I)) = s - 1 / 2 + circleOrd ζ * I := by ring
  rw [e1, e2]
  push_cast
  field_simp
  ring

/-- `Re K_sym(s, ζ) = ½(P(w, ζ) + P(w, ζ̄))`. -/
theorem re_symKernel {s ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (symKernel s ζ).re =
      (poissonKernel 0 (discPt s) ζ + poissonKernel 0 (discPt s) (conj ζ)) / 2 := by
  have hζc : ‖conj ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  unfold symKernel
  rw [Complex.div_ofNat_re, Complex.add_re, re_hrKernel, re_hrKernel]

/-- `|K_sym(s, ζ)| ≤ (|s − ½|/(Re s − ½)) Re K_sym(s, ζ)`. -/
theorem norm_symKernel_le {s ζ : ℂ} (hs : 1 / 2 < s.re) (hζ : ‖ζ‖ = 1) :
    ‖symKernel s ζ‖ ≤ ‖s - 1 / 2‖ / (s.re - 1 / 2) * (symKernel s ζ).re := by
  have hx : 0 < s.re - 1 / 2 := by linarith
  by_cases h1 : ζ = 1
  · subst h1
    rw [symKernel_one (two_mul_add_one_ne_zero (by linarith))]
    have : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [this, div_mul_cancel₀ _ hx.ne']
  · rw [symKernel_eq hs hζ h1]
    set γ := circleOrd ζ
    have hc : (1 + (γ : ℂ) ^ 2) / 2 = (((1 + γ ^ 2) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_mul, Complex.re_ofReal_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have := norm_gPair_le_re (τ := γ) hs
    calc (1 + γ ^ 2) / 2 * ‖gPair (1 / 2 + γ * I) s‖
        ≤ (1 + γ ^ 2) / 2 * (‖s - 1 / 2‖ / (s.re - 1 / 2) * (gPair (1 / 2 + γ * I) s).re) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

theorem re_symKernel_nonneg {s ζ : ℂ} (hs : 1 / 2 < s.re) (hζ : ‖ζ‖ = 1) :
    0 ≤ (symKernel s ζ).re := by
  rw [re_symKernel hζ]
  have hw := norm_discPt_lt_one hs
  have hζc : ‖conj ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  have p1 : 0 ≤ poissonKernel 0 (discPt s) ζ := by
    rw [poissonKernel_def]
    simp only [sub_zero, hζ, one_pow]
    exact div_nonneg (by nlinarith [norm_nonneg (discPt s)]) (by positivity)
  have p2 : 0 ≤ poissonKernel 0 (discPt s) (conj ζ) := by
    rw [poissonKernel_def]
    simp only [sub_zero, hζc, one_pow]
    exact div_nonneg (by nlinarith [norm_nonneg (discPt s)]) (by positivity)
  positivity

/-! ## The Herglotz–Riesz integral -/

/-- The symmetrised Herglotz–Riesz kernel in the disc variable. -/
def diskSym (w ζ : ℂ) : ℂ := ((ζ + w) / (ζ - w) + (conj ζ + w) / (conj ζ - w)) / 2

/-- Its derivative in the disc variable. -/
def diskSymDeriv (w ζ : ℂ) : ℂ := (2 * ζ / (ζ - w) ^ 2 + 2 * conj ζ / (conj ζ - w) ^ 2) / 2

theorem symKernel_eq_diskSym (s ζ : ℂ) : symKernel s ζ = diskSym (discPt s) ζ := rfl

theorem one_sub_norm_le_norm_sub {w ζ : ℂ} (hζ : ‖ζ‖ = 1) : 1 - ‖w‖ ≤ ‖ζ - w‖ := by
  have := norm_sub_norm_le ζ w
  rw [hζ] at this
  exact this

theorem sub_ne_zero_of_norm {w ζ : ℂ} (hζ : ‖ζ‖ = 1) (hw : ‖w‖ < 1) : ζ - w ≠ 0 := by
  intro h
  have := one_sub_norm_le_norm_sub (w := w) hζ
  rw [h, norm_zero] at this
  linarith

theorem norm_hr_le {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ = 1) :
    ‖(ζ + w) / (ζ - w)‖ ≤ 2 / (1 - ‖w‖) := by
  have h1 : 0 < 1 - ‖w‖ := by linarith
  rw [norm_div]
  have hn : ‖ζ + w‖ ≤ 2 := by
    calc ‖ζ + w‖ ≤ ‖ζ‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 2 := by rw [hζ]; linarith
  exact div_le_div₀ (by norm_num) hn h1 (one_sub_norm_le_norm_sub hζ)

theorem norm_diskSym_le {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ = 1) :
    ‖diskSym w ζ‖ ≤ 2 / (1 - ‖w‖) := by
  have hζc : ‖conj ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  unfold diskSym
  rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have := norm_add_le ((ζ + w) / (ζ - w)) ((conj ζ + w) / (conj ζ - w))
  linarith [norm_hr_le hw hζ, norm_hr_le hw hζc]

theorem hasDerivAt_hr {w ζ : ℂ} (h : ζ - w ≠ 0) :
    HasDerivAt (fun x : ℂ => (ζ + x) / (ζ - x)) (2 * ζ / (ζ - w) ^ 2) w := by
  have hN : HasDerivAt (fun x : ℂ => ζ + x) 1 w := (hasDerivAt_id w).const_add ζ
  have hD : HasDerivAt (fun x : ℂ => ζ - x) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub ζ
  rw [show 2 * ζ / (ζ - w) ^ 2 = (1 * (ζ - w) - (ζ + w) * -1) / (ζ - w) ^ 2 by ring]
  exact hN.div hD h

theorem hasDerivAt_diskSym {w ζ : ℂ} (h1 : ζ - w ≠ 0) (h2 : conj ζ - w ≠ 0) :
    HasDerivAt (fun x => diskSym x ζ) (diskSymDeriv w ζ) w := by
  unfold diskSym diskSymDeriv
  exact ((hasDerivAt_hr h1).add (hasDerivAt_hr h2)).div_const 2

theorem norm_diskSymDeriv_le {w ζ : ℂ} {ε : ℝ} (hε : 0 < ε) (hζ : ‖ζ‖ = 1)
    (h1 : ε ≤ ‖ζ - w‖) (h2 : ε ≤ ‖conj ζ - w‖) : ‖diskSymDeriv w ζ‖ ≤ 2 / ε ^ 2 := by
  have hζc : ‖conj ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  have b : ∀ z : ℂ, ‖z‖ = 1 → ε ≤ ‖z - w‖ → ‖2 * z / (z - w) ^ 2‖ ≤ 2 / ε ^ 2 := by
    intro z hz hzw
    rw [norm_div, norm_mul, norm_pow, hz, Complex.norm_two, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hε.le hzw 2)
  unfold diskSymDeriv
  rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have := norm_add_le (2 * ζ / (ζ - w) ^ 2) (2 * conj ζ / (conj ζ - w) ^ 2)
  linarith [b ζ hζ h1, b (conj ζ) hζc h2]

theorem continuous_diskSym_comp {X : Type*} [TopologicalSpace X] {w ζ : X → ℂ}
    (hw : Continuous w) (hζ : Continuous ζ) (hw1 : ∀ x, ‖w x‖ < 1) (hζ1 : ∀ x, ‖ζ x‖ = 1) :
    Continuous fun x => diskSym (w x) (ζ x) := by
  have hne : ∀ x, ζ x - w x ≠ 0 := fun x => sub_ne_zero_of_norm (hζ1 x) (hw1 x)
  have hne' : ∀ x, conj (ζ x) - w x ≠ 0 := fun x =>
    sub_ne_zero_of_norm (by rw [Complex.norm_conj, hζ1 x]) (hw1 x)
  have hζc : Continuous fun x => conj (ζ x) := Complex.continuous_conj.comp hζ
  unfold diskSym
  exact (((hζ.add hw).div (hζ.sub hw) hne).add ((hζc.add hw).div (hζc.sub hw) hne')).div_const 2

theorem continuous_diskSymDeriv_comp {X : Type*} [TopologicalSpace X] {w ζ : X → ℂ}
    (hw : Continuous w) (hζ : Continuous ζ) (hw1 : ∀ x, ‖w x‖ < 1) (hζ1 : ∀ x, ‖ζ x‖ = 1) :
    Continuous fun x => diskSymDeriv (w x) (ζ x) := by
  have hne : ∀ x, ζ x - w x ≠ 0 := fun x => sub_ne_zero_of_norm (hζ1 x) (hw1 x)
  have hne' : ∀ x, conj (ζ x) - w x ≠ 0 := fun x =>
    sub_ne_zero_of_norm (by rw [Complex.norm_conj, hζ1 x]) (hw1 x)
  have hζc : Continuous fun x => conj (ζ x) := Complex.continuous_conj.comp hζ
  unfold diskSymDeriv
  exact (((continuous_const.mul hζ).div ((hζ.sub hw).pow 2) fun x => pow_ne_zero 2 (hne x)).add
    ((continuous_const.mul hζc).div ((hζc.sub hw).pow 2) fun x =>
      pow_ne_zero 2 (hne' x))).div_const 2

theorem norm_circleMap_one (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  rw [norm_circleMap_zero, abs_one]

theorem integrable_diskSym {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun θ => diskSym w (circleMap 0 1 θ)) ν :=
  (integrable_const (2 / (1 - ‖w‖))).mono'
    (continuous_diskSym_comp continuous_const (continuous_circleMap 0 1) (fun _ => hw)
      norm_circleMap_one).aestronglyMeasurable
    (ae_of_all _ fun θ => norm_diskSym_le hw (norm_circleMap_one θ))

/-- The Herglotz–Riesz integral `∫ K_sym(w, e^{iθ}) dν(θ)` in the disc variable. -/
def diskHerglotz (ν : Measure ℝ) (w : ℂ) : ℂ := ∫ θ, diskSym w (circleMap 0 1 θ) ∂ν

theorem differentiableAt_diskHerglotz {ν : Measure ℝ} [IsFiniteMeasure ν] {w₀ : ℂ}
    (hw₀ : ‖w₀‖ < 1) : DifferentiableAt ℂ (diskHerglotz ν) w₀ := by
  set ε : ℝ := (1 - ‖w₀‖) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ w ∈ Metric.ball w₀ ε, ‖w‖ < 1 ∧ ∀ θ : ℝ,
      ε ≤ ‖circleMap 0 1 θ - w‖ ∧ ε ≤ ‖conj (circleMap 0 1 θ) - w‖ := by
    intro w hw
    have hd : ‖w - w₀‖ < ε := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have hnw : ‖w‖ < ‖w₀‖ + ε := by linarith [norm_sub_norm_le w w₀]
    refine ⟨by rw [hε] at hnw; linarith, fun θ => ⟨?_, ?_⟩⟩
    · have := one_sub_norm_le_norm_sub (w := w) (norm_circleMap_one θ)
      rw [hε] at hnw ⊢
      linarith
    · have := one_sub_norm_le_norm_sub (w := w)
        (show ‖conj (circleMap 0 1 θ)‖ = 1 by rw [Complex.norm_conj, norm_circleMap_one])
      rw [hε] at hnw ⊢
      linarith
  have hmem : Metric.ball w₀ ε ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ hε0
  have hw₀b : w₀ ∈ Metric.ball w₀ ε := Metric.mem_ball_self hε0
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun w θ => diskSym w (circleMap 0 1 θ))
    (F' := fun w θ => diskSymDeriv w (circleMap 0 1 θ)) (bound := fun _ => 2 / ε ^ 2) hmem
    (Filter.eventually_of_mem hmem fun w hw => (integrable_diskSym (hball w hw).1).1)
    (integrable_diskSym hw₀)
    (continuous_diskSymDeriv_comp continuous_const (continuous_circleMap 0 1) (fun _ => hw₀)
      norm_circleMap_one).aestronglyMeasurable
    (ae_of_all _ fun θ w hw => norm_diskSymDeriv_le hε0 (norm_circleMap_one θ)
      ((hball w hw).2 θ).1 ((hball w hw).2 θ).2)
    (integrable_const _)
    (ae_of_all _ fun θ w hw => hasDerivAt_diskSym
      (norm_pos_iff.mp (lt_of_lt_of_le hε0 ((hball w hw).2 θ).1))
      (norm_pos_iff.mp (lt_of_lt_of_le hε0 ((hball w hw).2 θ).2)))
  exact hderiv.differentiableAt

theorem differentiableAt_discPt {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ discPt s := by
  have hne := two_mul_add_one_ne_zero (s := s) (by linarith)
  have heq : discPt = fun z : ℂ => (2 * z - 3) / (2 * z + 1) := rfl
  rw [heq]
  exact ((differentiableAt_id.const_mul 2).sub_const 3).div
    ((differentiableAt_id.const_mul 2).add_const 1) hne

/-! ## The Herglotz–Riesz representation -/

/-- A holomorphic `Φ` on `Re s > ½` agreeing on `Re s > 1` with a function `G` that has real
coefficients (`G(s̄) = conj G(s)`) has real coefficients: `Φ(s̄) = conj Φ(s)`. -/
theorem herglotz_conj_of {G Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = G s)
    (hG : ∀ s : ℂ, 1 < s.re → G (conj s) = conj (G s)) {s : ℂ}
    (hs : 1 / 2 < s.re) : Φ (conj s) = conj (Φ s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ Φ ∘ (starRingEnd ℂ) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hcz : conj z ∈ U := by simpa [hU] using hz
    have h := ((hΦd (conj z) hcz).differentiableAt (hUo.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num
  have heq : Φ =ᶠ[𝓝 2] g := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)
    filter_upwards [hV] with z hz
    have hz' : 1 < (conj z).re := by simpa using hz
    simp only [hg, Function.comp_apply]
    rw [hΦ z hz, hΦ _ hz', hG z hz, Complex.conj_conj]
  have hEq := (hΦd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  have hcs : conj s ∈ U := by simpa [hU] using hs
  have := hEq hcs
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  exact this

/-- A holomorphic `Φ` on `Re s > ½` agreeing with a Weil function on `Re s > 1` has real
coefficients: `Φ(s̄) = conj Φ(s)`. -/
theorem herglotz_conj {lam : ℕ → ℝ} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = WeilHerglotz.weilFunction lam s) {s : ℂ}
    (hs : 1 / 2 < s.re) : Φ (conj s) = conj (Φ s) :=
  herglotz_conj_of hΦd hΦ (fun z _ => WeilSpectral.weilFunction_conj lam z) hs

theorem integrable_poissonKernel_circleMap {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℂ}
    (hw : ‖w‖ < 1) : Integrable (fun θ => poissonKernel 0 w (circleMap 0 1 θ)) ν :=
  (integrable_const ((1 - ‖w‖ ^ 2) / (1 - ‖w‖) ^ 2)).mono'
    (continuous_poissonKernel_circleMap hw).aestronglyMeasurable
    (ae_of_all _ fun θ => by
      rw [Real.norm_of_nonneg (poissonKernel_circleMap_one_nonneg hw θ)]
      exact poissonKernel_circleMap_one_le hw θ)

/-- **The Herglotz–Riesz representation with real coefficients.**  If `Φ` is holomorphic with
`Re Φ ≥ 0` on `Re s > ½` and `Φ(s̄) = conj Φ(s)`, then for a finite measure `ν` on angles and a
real `c`, `Φ(s) = ∫ K_sym(s, e^{iθ}) dν(θ) + ic` on `Re s > ½`. -/
theorem exists_herglotzRiesz_representation {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hconj : ∀ s : ℂ, 1 / 2 < s.re → Φ (conj s) = conj (Φ s)) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∃ c : ℝ, ∀ s : ℂ, 1 / 2 < s.re →
      Φ s = (∫ θ, symKernel s (circleMap 0 1 θ) ∂ν) + c * I := by
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation_halfPlane hΦd hΦre
  refine ⟨ν, hfin, ?_⟩
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsConnected U := (convex_halfSpace_re_gt (1 / 2)).isConnected
    ⟨1, show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num⟩
  set Ψ : ℂ → ℂ := fun s => diskHerglotz ν (discPt s) with hΨ
  have hΨd : DifferentiableOn ℂ Ψ U := fun s hs =>
    ((differentiableAt_diskHerglotz (norm_discPt_lt_one hs)).comp s
      (differentiableAt_discPt hs)).differentiableWithinAt
  have hreΨ : ∀ s ∈ U, (Ψ s).re = (Φ s).re := by
    intro s hs
    have hs' : 1 / 2 < s.re := hs
    have hw := norm_discPt_lt_one hs'
    have hwc : ‖discPt (conj s)‖ < 1 := norm_discPt_lt_one (by simpa using hs')
    have hcs : 1 / 2 < (conj s).re := by simpa using hs'
    simp only [hΨ, diskHerglotz]
    have hre : (∫ θ, diskSym (discPt s) (circleMap 0 1 θ) ∂ν).re =
        ∫ θ, (diskSym (discPt s) (circleMap 0 1 θ)).re ∂ν :=
      (integral_re (integrable_diskSym hw)).symm
    rw [hre]
    have hpt : ∀ θ : ℝ, (diskSym (discPt s) (circleMap 0 1 θ)).re =
        (poissonKernel 0 (discPt s) (circleMap 0 1 θ) +
          poissonKernel 0 (discPt (conj s)) (circleMap 0 1 θ)) / 2 := by
      intro θ
      rw [← symKernel_eq_diskSym, re_symKernel (norm_circleMap_one θ), poissonKernel_conj_right,
        discPt_conj]
    simp_rw [hpt]
    rw [integral_div, integral_add (integrable_poissonKernel_circleMap hw)
      (integrable_poissonKernel_circleMap hwc), hrep s hs', hrep _ hcs, hconj s hs',
      Complex.conj_re]
    ring
  have hre0 : ∀ s ∈ U, ((Φ - Ψ) s).re = 0 := fun s hs => by
    rw [Pi.sub_apply, Complex.sub_re, hreΨ s hs, sub_self]
  obtain ⟨c, hc⟩ := ((hΦd.sub hΨd).analyticOnNhd hUo).eq_re_add_const_mul_I_of_re_eq_const
    hre0 hUo hUc
  refine ⟨c, fun s hs => ?_⟩
  have h := hc s hs
  rw [Pi.sub_apply, Complex.ofReal_zero, zero_add, sub_eq_iff_eq_add] at h
  rw [h, add_comm]
  rfl

/-! ## Moving a line integral to the critical line -/

/-- **Moving a line integral to the critical line.**  Let `|H_k(σ + it)| ≤ D(1 + t²)^{−2}` on
`−1 ≤ σ ≤ 2`, let `q` be entire with `|q(σ + it)| ≤ 1 + |t|` on `½ ≤ σ ≤ b`, `¾ < b ≤ 3/2`.  Then
the line integral of `(H(s) + H(1 − s)) q(s)` on `Re s = b` equals the one on `Re s = ½`.  Apply the
two-line residue identity to `(H(s) + H(1 − s)) q(s) (s − ¾)` with its pole at `¾`, where the
residue vanishes. -/
theorem integral_line_shift_critical {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {D : ℝ}
    (hD : ∀ σ t : ℝ, -1 ≤ σ → σ ≤ 2 → ‖Hfn k (σ + t * I)‖ ≤ D / (1 + t ^ 2) ^ 2)
    {q : ℂ → ℂ} (hq : Differentiable ℂ q) {b : ℝ} (hb1 : 3 / 4 < b) (hb2 : b ≤ 3 / 2)
    (hqb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ b → ‖q (σ + t * I)‖ ≤ 1 + |t|) :
    (∫ t : ℝ, (Hfn k (b + t * I) + Hfn k (1 - b - t * I)) * q (b + t * I)) =
      ∫ t : ℝ, (Hfn k ((1 / 2 : ℝ) + t * I) + Hfn k ((1 / 2 : ℝ) - t * I)) *
        q ((1 / 2 : ℝ) + t * I) := by
  set E : ℂ → ℂ := fun s => (Hfn k s + Hfn k (1 - s)) * q s * (s - 3 / 4) with hE
  have hHd := differentiable_Hfn hk hkc
  have hEd : Differentiable ℂ E :=
    ((hHd.add (hHd.comp ((differentiable_const 1).sub differentiable_id))).mul hq).mul
      (differentiable_id.sub_const _)
  have hD0 : 0 ≤ D := by
    have := hD 0 0 (by norm_num) (by norm_num)
    simp at this
    exact (norm_nonneg _).trans this
  have hEb : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ b → ‖E (σ + t * I)‖ ≤ 4 * D / (1 + t ^ 2) := by
    intro σ t h1 h2
    have e : (1 : ℂ) - (σ + t * I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    have hA := hD σ t (by linarith) (by linarith)
    have hB := hD (1 - σ) (-t) (by linarith) (by linarith)
    rw [neg_sq] at hB
    have hlin : ‖(σ : ℂ) + t * I - 3 / 4‖ ≤ 1 + |t| := by
      have e2 : (σ : ℂ) + t * I - 3 / 4 = ((σ - 3 / 4 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have : |σ - 3 / 4| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hq' := hqb σ t h1 h2
    have hsq : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    simp only [hE]
    rw [norm_mul, norm_mul, e]
    calc ‖Hfn k (σ + t * I) + Hfn k (((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ *
          ‖q (σ + t * I)‖ * ‖(σ : ℂ) + t * I - 3 / 4‖
        ≤ (D / (1 + t ^ 2) ^ 2 + D / (1 + t ^ 2) ^ 2) * (1 + |t|) * (1 + |t|) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hA hB)
      _ = 2 * D * (1 + |t|) ^ 2 / (1 + t ^ 2) ^ 2 := by ring
      _ ≤ 2 * D * (2 * (1 + t ^ 2)) / (1 + t ^ 2) ^ 2 := by gcongr
      _ = 4 * D / (1 + t ^ 2) := by field_simp; ring
  have h := two_line_simple_pole hEd hEb (p := 3 / 4) (by norm_num) (by norm_num; linarith)
  have hE0 : E (3 / 4) = 0 := by simp [hE]
  rw [hE0, mul_zero, sub_eq_zero] at h
  have hR : ∀ t : ℝ, E (b + t * I) / (b + t * I - 3 / 4) =
      (Hfn k (b + t * I) + Hfn k (1 - b - t * I)) * q (b + t * I) := by
    intro t
    have hne : (b : ℂ) + t * I - 3 / 4 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    simp only [hE]
    rw [mul_div_cancel_right₀ _ hne, sub_add_eq_sub_sub]
  have hL : ∀ t : ℝ, E (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I - 3 / 4) =
      (Hfn k ((1 / 2 : ℝ) + t * I) + Hfn k ((1 / 2 : ℝ) - t * I)) * q ((1 / 2 : ℝ) + t * I) := by
    intro t
    have hne : ((1 / 2 : ℝ) : ℂ) + t * I - 3 / 4 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    simp only [hE]
    rw [mul_div_cancel_right₀ _ hne]
    congr 3
    push_cast
    ring
  simp_rw [hR, hL] at h
  exact h

/-- On the critical line the transform of an autocorrelation is `|f̂|²`. -/
theorem Hfn_weilTest_critical {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (t : ℝ) : Hfn (EF.weilTest f f) ((1 / 2 : ℝ) + t * I) = ((‖paperFT f t‖ ^ 2 : ℝ) : ℂ) := by
  rw [← paperFT_weilTest_self_ofReal hf hfc t]
  unfold Hfn
  congr 1
  push_cast
  rw [add_sub_cancel_left, mul_div_cancel_right₀ _ I_ne_zero]

theorem Hfn_weilTest_critical_neg {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (t : ℝ) : Hfn (EF.weilTest f f) ((1 / 2 : ℝ) - t * I) =
      ((‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) := by
  have h := Hfn_weilTest_critical hf hfc (-t)
  rw [Complex.ofReal_neg] at h
  rw [← h]
  congr 1
  push_cast
  ring

/-- `∫ (H(5/4 + it) + H(−1/4 − it)) dt` is real for an autocorrelation. -/
theorem im_integral_line_weilTest {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) ((5 / 4 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (1 - (5 / 4 : ℝ) - t * I))).im = 0 := by
  obtain ⟨D, -, hD⟩ := norm_Hfn_weilTest_le hf hfc
  have h := integral_line_shift_critical (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc) hD (q := fun _ => 1) (differentiable_const 1)
    (b := 5 / 4) (by norm_num) (by norm_num) (fun σ t _ _ => by
      rw [norm_one]; linarith [abs_nonneg t])
  simp only [mul_one] at h
  have hpt : ∀ t : ℝ, Hfn (EF.weilTest f f) ((1 / 2 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) ((1 / 2 : ℝ) - t * I) =
      ((‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Hfn_weilTest_critical hf.continuous hfc, Hfn_weilTest_critical_neg hf.continuous hfc]
    push_cast
    ring
  rw [h, integral_congr_ae (Eventually.of_forall hpt)]
  rw [integral_complex_ofReal, Complex.ofReal_im]

/-- `∫ (H(5/4 + it) + H(−1/4 − it))(¾ + it) dt` is purely imaginary for an autocorrelation. -/
theorem re_integral_line_weilTest_linear {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (∫ t : ℝ, (Hfn (EF.weilTest f f) ((5 / 4 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) (1 - (5 / 4 : ℝ) - t * I)) *
        (((5 / 4 : ℝ) : ℂ) + t * I - 1 / 2)).re = 0 := by
  obtain ⟨D, -, hD⟩ := norm_Hfn_weilTest_le hf hfc
  have h := integral_line_shift_critical (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc) hD (q := fun s => s - 1 / 2)
    (differentiable_id.sub_const _) (b := 5 / 4) (by norm_num) (by norm_num)
    (fun σ t h1 h2 => by
      have e : (σ : ℂ) + t * I - 1 / 2 = ((σ - 1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have : |σ - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith)
  rw [h]
  have hpt : ∀ t : ℝ, (Hfn (EF.weilTest f f) ((1 / 2 : ℝ) + t * I) +
      Hfn (EF.weilTest f f) ((1 / 2 : ℝ) - t * I)) * (((1 / 2 : ℝ) : ℂ) + t * I - 1 / 2) =
      I * ((t * (‖paperFT f t‖ ^ 2 + ‖paperFT f (-t)‖ ^ 2) : ℝ) : ℂ) := by
    intro t
    rw [Hfn_weilTest_critical hf.continuous hfc, Hfn_weilTest_critical_neg hf.continuous hfc]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_complex_ofReal, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## The theorem -/

/-- **The line-integral core of the bridge.**  Let `Φ` be holomorphic with `Re Φ ≥ 0` on
`Re s > ½`, real on the real axis (`Φ(s̄) = conj Φ(s)`), and equal on `Re s > 1` to a function `G`
of at most linear growth on the line `Re s = 5/4`.  Then for every autocorrelation `k = f ⋆ f̃` of a
`C²` compactly supported `f`, the line integral
`(1/2π) ∫ (H_k(5/4 + it) + H_k(−1/4 − it)) G(5/4 + it) dt` has nonnegative real part. -/
theorem re_lineIntegral_nonneg_of_herglotz {G Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hconj : ∀ s : ℂ, 1 / 2 < s.re → Φ (conj s) = conj (Φ s))
    (hΦG : ∀ s : ℂ, 1 < s.re → Φ s = G s) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ t : ℝ, ‖G (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ A * (1 + |t|))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (Hfn (EF.weilTest f f) (((5 / 4 : ℝ) : ℂ) + t * I) +
        Hfn (EF.weilTest f f) (1 - ((5 / 4 : ℝ) : ℂ) - t * I)) *
        G (((5 / 4 : ℝ) : ℂ) + t * I)).re := by
  obtain ⟨ν, hfin, c, hrep⟩ := exists_herglotzRiesz_representation hΦd hΦre hconj
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le hf hfc
  obtain ⟨Ck, hCk0, hCk⟩ := norm_Hfn_le hkd hkc
  set c₀ : ℝ := 5 / 4 with hc₀
  set F : ℝ → ℂ := fun t => Hfn k (c₀ + t * I) + Hfn k (1 - c₀ - t * I) with hF
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c₀ - t * I = ((1 - c₀ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c₀ t (by norm_num [hc₀]) (by norm_num [hc₀])
    have h2 := hD (1 - c₀) (-t) (by norm_num [hc₀]) (by norm_num [hc₀])
    rw [neg_sq] at h2
    rw [two_mul, add_div]
    exact add_le_add h1 h2
  have hFc : Continuous F := by
    have hm : ∀ t : ℝ, Hfn k (1 - c₀ - t * I) = Hfn (fun u => k (-u)) (c₀ + t * I) :=
      fun t => Hfn_mirror k c₀ t
    simp only [hF, hm]
    exact (continuous_Hfn_line hkd hkc c₀).add
      (continuous_Hfn_line (hkd.comp contDiff_neg) (hkc.comp_homeomorph (Homeomorph.neg ℝ)) c₀)
  have hFi : Integrable F := by
    refine (integrable_inv_one_add_sq.const_mul (2 * D)).mono' hFc.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    calc ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := hFb t
      _ ≤ 2 * D / (1 + t ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg t])
      _ = 2 * D * (1 + t ^ 2)⁻¹ := by ring
  have hre : ∀ t : ℝ, ((c₀ : ℂ) + t * I).re = c₀ := fun t => by simp
  have hs : ∀ t : ℝ, 1 / 2 < ((c₀ : ℂ) + t * I).re := fun t => by rw [hre]; norm_num [hc₀]
  have hs1 : ∀ t : ℝ, 1 < ((c₀ : ℂ) + t * I).re := fun t => by rw [hre]; norm_num [hc₀]
  set K : ℝ → ℝ → ℂ := fun t θ => symKernel (c₀ + t * I) (circleMap 0 1 θ) with hK
  have hKi : ∀ t, Integrable (K t) ν := fun t => integrable_diskSym (norm_discPt_lt_one (hs t))
  have hΦK : ∀ t : ℝ, G (c₀ + t * I) = (∫ θ, K t θ ∂ν) + c * I := fun t => by
    rw [← hΦG _ (hs1 t)]
    exact hrep _ (hs t)
  -- the majorant
  set w : ℝ → ℝ := fun t => ‖((c₀ : ℂ) + t * I) - 1 / 2‖ / (c₀ - 1 / 2) with hw
  have hw0 : ∀ t, 0 ≤ w t := fun t => div_nonneg (norm_nonneg _) (by norm_num [hc₀])
  have hwb : ∀ t : ℝ, w t ≤ 2 * (1 + |t|) := by
    intro t
    simp only [hw]
    rw [div_le_iff₀ (show (0 : ℝ) < c₀ - 1 / 2 by norm_num [hc₀])]
    have e : ((c₀ : ℂ) + t * I) - 1 / 2 = ((3 / 4 : ℝ) : ℂ) + t * I := by
      rw [hc₀]; push_cast; ring
    rw [e]
    calc ‖((3 / 4 : ℝ) : ℂ) + t * I‖ ≤ ‖((3 / 4 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 3 / 4 + |t| := by simp
      _ ≤ 2 * (1 + |t|) * (c₀ - 1 / 2) := by rw [hc₀]; linarith [abs_nonneg t]
  have hKn : ∀ t : ℝ, ∫ θ, ‖K t θ‖ ∂ν ≤
      w t * ‖G (c₀ + t * I)‖ := by
    intro t
    have hpt : ∀ θ, ‖K t θ‖ ≤ w t * (K t θ).re := fun θ => by
      have := norm_symKernel_le (hs t) (norm_circleMap_one θ)
      rw [hre] at this
      exact this
    have hreI : ∫ θ, (K t θ).re ∂ν = (∫ θ, K t θ ∂ν).re := integral_re (hKi t)
    calc ∫ θ, ‖K t θ‖ ∂ν ≤ ∫ θ, w t * (K t θ).re ∂ν :=
          integral_mono (hKi t).norm ((hKi t).re.const_mul _) hpt
      _ = w t * (G (c₀ + t * I)).re := by
          rw [integral_const_mul, hreI, hΦK t, Complex.add_re]
          simp
      _ ≤ w t * ‖G (c₀ + t * I)‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (hw0 t)
  -- integrability on the product
  have hdc : Continuous fun t : ℝ => discPt ((c₀ : ℂ) + t * I) := by
    have heq : (fun t : ℝ => discPt ((c₀ : ℂ) + t * I)) =
        fun t : ℝ => (2 * ((c₀ : ℂ) + t * I) - 3) / (2 * ((c₀ : ℂ) + t * I) + 1) := rfl
    rw [heq]
    exact Continuous.div (by fun_prop) (by fun_prop) fun t =>
      two_mul_add_one_ne_zero (by rw [hre]; norm_num [hc₀])
  set g : ℝ × ℝ → ℂ := fun p => F p.1 * K p.1 p.2 with hg
  have hgc : Continuous g :=
    (hFc.comp continuous_fst).mul (continuous_diskSym_comp (hdc.comp continuous_fst)
      ((continuous_circleMap 0 1).comp continuous_snd) (fun p => norm_discPt_lt_one (hs p.1))
      fun p => norm_circleMap_one p.2)
  have hgi : Integrable g (volume.prod ν) := by
    rw [integrable_prod_iff hgc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun t => (hKi t).const_mul (F t), ?_⟩
    refine (integrable_inv_one_add_sq.const_mul (8 * D * A)).mono'
      hgc.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
    simp only [hg, norm_mul]
    rw [integral_const_mul]
    have hK1 : ∫ θ, ‖K t θ‖ ∂ν ≤ 2 * (1 + |t|) * (A * (1 + |t|)) :=
      (hKn t).trans (mul_le_mul (hwb t) (hA t) (norm_nonneg _) (by positivity))
    calc ‖F t‖ * ∫ θ, ‖K t θ‖ ∂ν
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (2 * (1 + |t|) * (A * (1 + |t|))) :=
          mul_le_mul (hFb t) hK1 (integral_nonneg fun θ => norm_nonneg _) (by positivity)
      _ = 4 * D * A * ((1 + |t|) ^ 2 / (1 + t ^ 2)) * (1 + t ^ 2)⁻¹ := by
          field_simp
          ring
      _ ≤ 4 * D * A * 2 * (1 + t ^ 2)⁻¹ := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
      _ = 8 * D * A * (1 + t ^ 2)⁻¹ := by ring
  -- the line integral as a `ν`-integral
  have hsplit : (∫ t : ℝ, F t * G (c₀ + t * I)) =
      (∫ θ, ∫ t, F t * K t θ ∂volume ∂ν) + (c * I) * ∫ t, F t := by
    have h1 : ∀ t, F t * G (c₀ + t * I) =
        (∫ θ, F t * K t θ ∂ν) + c * I * F t := by
      intro t
      rw [hΦK t, integral_const_mul]
      ring
    rw [integral_congr_ae (Eventually.of_forall h1),
      integral_add hgi.integral_prod_left (hFi.const_mul _), integral_const_mul]
    congr 1
    exact integral_integral_swap (f := fun t θ => F t * K t θ) hgi
  -- each angle contributes a nonnegative real part
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hJre : ∀ θ, 0 ≤ (∫ t, F t * K t θ).re := by
    intro θ
    set ζ := circleMap 0 1 θ with hζdef
    have hζ : ‖ζ‖ = 1 := norm_circleMap_one θ
    by_cases h1 : ζ = 1
    · have hKt : ∀ t, K t θ = (c₀ : ℂ) + t * I - 1 / 2 := fun t => by
        show symKernel _ ζ = _
        rw [h1]
        exact symKernel_one (two_mul_add_one_ne_zero (by rw [hre]; norm_num [hc₀]))
      have e : (∫ t, F t * K t θ) = ∫ t, F t * ((c₀ : ℂ) + t * I - 1 / 2) :=
        integral_congr_ae (Eventually.of_forall fun t => congrArg (fun x => F t * x) (hKt t))
      rw [e]
      exact (re_integral_line_weilTest_linear hf hfc).symm.le
    · set γ : ℝ := circleOrd ζ with hγ
      have hKt : ∀ t, K t θ =
          (1 + (γ : ℂ) ^ 2) / 2 * gPair (1 / 2 + γ * I) (c₀ + t * I) := fun t =>
        symKernel_eq (hs t) hζ h1
      have h2 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * gPair (1 / 2 + γ * I) (c₀ + t * I) =
          Hfn k (1 / 2 + γ * I) + Hfn k (1 - (1 / 2 + γ * I)) :=
        two_line_pair (differentiable_Hfn hkd hkc) (c := c₀) (C := Ck)
          (fun σ t h1 h2 => hCk σ t (by norm_num [hc₀] at h1 ⊢; linarith)
            (by norm_num [hc₀] at h2 ⊢; linarith)) (z₀ := 1 / 2 + γ * I)
          (by simp; norm_num [hc₀]) (by simp; norm_num [hc₀])
      have hHz : Hfn k (1 / 2 + γ * I) + Hfn k (1 - (1 / 2 + γ * I)) =
          ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2 : ℝ) : ℂ) := by
        have a := Hfn_weilTest_critical hf.continuous hfc γ
        have b := Hfn_weilTest_critical_neg hf.continuous hfc γ
        rw [show (1 / 2 : ℂ) + γ * I = ((1 / 2 : ℝ) : ℂ) + γ * I by push_cast; ring,
          show (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + γ * I) = ((1 / 2 : ℝ) : ℂ) - γ * I by
            push_cast; ring, a, b]
        push_cast
        ring
      have e : (∫ t, F t * K t θ) =
          (1 + (γ : ℂ) ^ 2) / 2 * ∫ t, F t * gPair (1 / 2 + γ * I) (c₀ + t * I) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show F t * K t θ = (1 + (γ : ℂ) ^ 2) / 2 * (F t * gPair (1 / 2 + γ * I) (c₀ + t * I))
        rw [hKt t]
        ring
      have hX : (∫ t, F t * gPair (1 / 2 + γ * I) (c₀ + t * I)) =
          (2 * Real.pi : ℂ) * ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hHz, ← h2, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
      rw [e, hX]
      have hval : (1 + (γ : ℂ) ^ 2) / 2 * ((2 * Real.pi : ℂ) *
          ((‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2 : ℝ) : ℂ)) =
          (((1 + γ ^ 2) / 2 * (2 * Real.pi) * (‖paperFT f γ‖ ^ 2 + ‖paperFT f (-γ)‖ ^ 2) : ℝ) :
            ℂ) := by
        push_cast
        ring
      rw [hval, Complex.ofReal_re]
      positivity
  -- assemble
  have hFim : (∫ t, F t).im = 0 := im_integral_line_weilTest hf hfc
  have hJi : Integrable (fun θ => ∫ t, F t * K t θ) ν := hgi.integral_prod_right
  have hJre' : ∫ θ, (∫ t, F t * K t θ).re ∂ν = (∫ θ, ∫ t, F t * K t θ ∂volume ∂ν).re :=
    integral_re hJi
  have hcI : ((c : ℂ) * I * ∫ t, F t).re = 0 := by
    simp [Complex.mul_re, hFim]
  rw [hsplit,
    show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.add_re, hcI, add_zero, ← hJre']
  exact mul_nonneg (by positivity) (integral_nonneg hJre)

/-- **A Herglotz Weil function makes the weights full-cone Weil-positive.**  If `Φ` is holomorphic
with `Re Φ ≥ 0` on `Re s > ½` and equals the Weil function of `lam` on `Re s > 1`, then
`W_lam(f ⋆ f̃) ≥ 0` for every `C²` compactly supported `f`. -/
theorem weilPositiveFull_of_herglotz {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = WeilHerglotz.weilFunction lam s) :
    WeilPositiveFull lam := by
  intro f hf hfc
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨A, hA0, hA⟩ := norm_weilFunction_le hsl (c := 5 / 4) (by norm_num) (by norm_num)
  rw [weilFullFunctional_eq_line_integral hsl hkd hkc (c := 5 / 4) (by norm_num) (by norm_num)]
  exact re_lineIntegral_nonneg_of_herglotz hΦd hΦre (fun s hs => herglotz_conj hΦd hΦ hs) hΦ hA0
    hA hf hfc

/-- **Herglotz positivity of the Weil function is equivalent to full-cone Weil positivity.** -/
theorem weilPositiveFull_iff_exists_herglotz {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    WeilPositiveFull lam ↔ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
      ∀ s : ℂ, 1 < s.re → Φ s = WeilHerglotz.weilFunction lam s :=
  ⟨fun hW => ⟨WeilSpectral.weilContinuation hW, WeilSpectral.differentiableOn_weilContinuation hW,
      fun _ hs => WeilSpectral.re_weilContinuation_nonneg hW hs,
      fun _ hs => WeilSpectral.weilContinuation_eq hW hs⟩,
    fun ⟨_, hΦd, hΦre, hΦ⟩ => weilPositiveFull_of_herglotz hsl hΦd hΦre hΦ⟩

/-- A Herglotz function equal to `ψ_ℝ(s) + 1/s + 1/(s − 1) − Σ_{n≥2} lam(n) n^{−s}` on `Re s > 1`
makes `lam` full-cone Weil-positive. -/
theorem weilPositiveFull_of_herglotz_lamTwo {lam : ℕ → ℝ} {Φ : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (IntegerMassRigidity.lamTwo lam) s) :
    WeilPositiveFull lam := by
  refine weilPositiveFull_of_herglotz hsl hΦd hΦre fun s hs => ?_
  have hfun : IntegerMassRigidity.lamTwo lam = WeilHerglotz.lamC lam := by
    funext n
    unfold IntegerMassRigidity.lamTwo WeilHerglotz.lamC
    split_ifs <;> simp
  rw [hid s hs, WeilHerglotz.weilFunction, zetaArchimedeanDatum, hfun]

end RHTower.AtomDomination
