import GaloisForLFunctions.ArithmeticProduction.TheMollifiedZetaFunctionIsBandLimited
import GaloisForLFunctions.ArithmeticProduction.EveryOffLineZeroPinsAFloor
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailFromGate
import GaloisForLFunctions.RHTower.MollifiedDetectorFarRightDecay
import GaloisForLFunctions.HTGeometry.ZetaTailBound

/-!
# The two floors of the mollified second moment

The second moment of a mollified zeta function has a floor on each side of the critical line, and the two floors have a kink at `½`.

* **Right of the line** (`right_floor`).  Since the leading coefficient of `M` is `1`, the first moment of `ζM` against the Gaussian equals the
  mass of the Gaussian up to a small error: shift the contour to `Re s = K`, where `ζM = 1 + O(2^{−K})`.  Cauchy–Schwarz turns this
  into a floor `∫|F(½+a+it)|² ≥ (1 − e)² w√π e^{−a²/w²}`, uniform in the mollifier and its length.
* **Left of the line** (`left_floor`).  Littlewood's lemma charges every zero of `ζ` to the right of `½ − a`; pairing each zero with its
  reflection contributes `a` per zero.  With the count of zeros this gives
  `∫_{T₁}^{T₂} |ζM(½ − a + it)|² dt ≥ (T₂ − T₁) exp((2/(T₂−T₁))(2πa ΔN − C − K log(T₂ Mb)))`.
  This is the floor that knows about `N(T)`; it holds for every real mollifier with bounded coefficients.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-! ### Decay of products with the squared window -/

/-- A polynomially bounded factor times the squared window decays like `1/(1+t²)`. -/
theorem exists_decay_mul_gaussWindow_sq (t₀ : ℝ) {w : ℝ} (hw : 0 < w) {G : ℂ → ℂ} {C₀ K : ℝ} {k : ℕ}
    (hC₀ : 0 ≤ C₀) {S : Set ℂ} (hS : ∀ s ∈ S, |s.re - 1 / 2| ≤ K)
    (hG : ∀ s ∈ S, ‖G s‖ ≤ C₀ * (1 + |s.im|) ^ k) :
    ∃ C : ℝ, ∀ s ∈ S, ‖G s * gaussWindow t₀ w s * gaussWindow t₀ w s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_one_add_abs_pow_mul_gauss_le (k + 2) t₀ hw
  refine ⟨C₀ * Real.exp (K ^ 2 / w ^ 2) * C₂, fun s hs => ?_⟩
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rw [le_div_iff₀ hpos, norm_mul, norm_mul, mul_assoc (‖G s‖), norm_gaussWindow, ← Real.exp_add]
  have hexp : Real.exp (((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2) +
      ((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2)) ≤
      Real.exp (K ^ 2 / w ^ 2) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (s.re - 1 / 2) ^ 2 ≤ K ^ 2 := by
      have := hS s hs
      have h2 : 0 ≤ K := (abs_nonneg _).trans this
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hw2 : 0 < w ^ 2 := by positivity
    have h3 : (s.re - 1 / 2) ^ 2 / w ^ 2 ≤ K ^ 2 / w ^ 2 :=
      div_le_div_of_nonneg_right h1 hw2.le
    have h4 : 0 ≤ (s.im - t₀) ^ 2 / (2 * w ^ 2) := by positivity
    have h5 : ((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2) +
        ((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2) =
        (s.re - 1 / 2) ^ 2 / w ^ 2 - (s.im - t₀) ^ 2 / (2 * w ^ 2) -
          (s.im - t₀) ^ 2 / (2 * w ^ 2) := by
      field_simp
      ring
    rw [h5]
    linarith
  have hpow : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
    have := sq_abs s.im
    nlinarith [abs_nonneg s.im]
  have hE := Real.exp_pos (-((s.im - t₀) ^ 2 / (2 * w ^ 2)))
  have hE2 := Real.exp_pos (K ^ 2 / w ^ 2)
  calc ‖G s‖ * Real.exp (((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2) +
        ((s.re - 1 / 2) ^ 2 - (s.im - t₀) ^ 2) / (2 * w ^ 2)) * (1 + s.im ^ 2)
      ≤ (C₀ * (1 + |s.im|) ^ k) *
          (Real.exp (K ^ 2 / w ^ 2) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2)))) *
            (1 + |s.im|) ^ 2 :=
        mul_le_mul (mul_le_mul (hG s hs) hexp (Real.exp_pos _).le (by positivity)) hpow hpos.le
          (by positivity)
    _ = C₀ * Real.exp (K ^ 2 / w ^ 2) *
          ((1 + |s.im|) ^ (k + 2) * Real.exp (-((s.im - t₀) ^ 2 / (2 * w ^ 2)))) := by ring
    _ ≤ C₀ * Real.exp (K ^ 2 / w ^ 2) * C₂ :=
        mul_le_mul_of_nonneg_left (hC₂ s.im) (by positivity)

private theorem re_line' (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).re = c := by simp

private theorem im_line' (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).im = t := by simp

/-- A function with `C/(1+t²)` decay and continuous on a line is integrable on that line. -/
theorem integrable_of_decay_on_line {Φ : ℂ → ℂ} {c C : ℝ}
    (hd : ∀ t : ℝ, DifferentiableAt ℂ Φ ((c : ℂ) + (t : ℂ) * I))
    (hb : ∀ t : ℝ, ‖Φ ((c : ℂ) + (t : ℂ) * I)‖ ≤ C / (1 + t ^ 2)) :
    Integrable fun t : ℝ => Φ ((c : ℂ) + (t : ℂ) * I) := by
  have hcont : Continuous fun t : ℝ => Φ ((c : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I) (g := Φ)
      (hd t).continuousAt (by fun_prop)
  have hg : Integrable fun t : ℝ => C * (1 + t ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hg hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [← div_eq_mul_inv]
  exact hb t

/-! ### The right floor -/

/-- On a far line `Re s = K`, the mollified body is `1` up to `19·2^{−K} + 4/|s + 1|`. -/
theorem norm_windowBody_sub_one_le {K : ℝ} (hK : 5 ≤ K) {b : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hb1 : b 1 = 1) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {s : ℂ} (hre : s.re = K) :
    ‖windowBody b N s - 1‖ ≤ 19 * Real.exp (-(Real.log 2 * K)) + 4 / ‖s + 1‖ := by
  have hK2 : 2 ≤ s.re := by rw [hre]; linarith
  have hne : s ≠ 1 := by
    intro h
    rw [h] at hK2
    norm_num at hK2
  have hne' : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hre] at this
    linarith
  set x₂ := Real.exp (-(Real.log 2 * K)) with hx₂
  have hx₂0 : 0 < x₂ := Real.exp_pos _
  have hlog2 := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  have hx₂le : x₂ ≤ 1 / 32 := by
    have h1 : x₂ ≤ Real.exp (-(Real.log 2 * 5)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-(Real.log 2 * 5)) = 1 / 32 := by
      rw [Real.exp_neg, Real.exp_mul, Real.exp_log two_pos,
        show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hζ : ‖riemannZeta s - 1‖ ≤ 4 * x₂ := by
    have h := GaloisForLFunctions.HTGeometry.norm_riemannZeta_sub_one_le_rpow hK2
    rw [hre, Real.rpow_def_of_pos two_pos] at h
    refine h.trans (le_of_eq ?_)
    rw [hx₂]
    congr 2
    ring
  have hM := norm_edPoly_sub_one_le_exp b (s := Finset.Icc 1 N) (fun n hn => (Finset.mem_Icc.mp hn).1)
    (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) hb1 hb (z := s) hK2
  have hMx : ‖edPoly b (Finset.Icc 1 N) s - 1‖ ≤ 11 * x₂ := by
    refine hM.trans (le_of_eq ?_)
    rw [hre, hx₂]
    congr 2
    ring
  have hMn : ‖edPoly b (Finset.Icc 1 N) s‖ ≤ 2 := by
    have h1 : edPoly b (Finset.Icc 1 N) s = (edPoly b (Finset.Icc 1 N) s - 1) + 1 := by ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_one]
    linarith
  set X := riemannZeta s * edPoly b (Finset.Icc 1 N) s with hX
  have hX1 : ‖X - 1‖ ≤ 19 * x₂ := by
    have h1 : X - 1 = (riemannZeta s - 1) * edPoly b (Finset.Icc 1 N) s +
        (edPoly b (Finset.Icc 1 N) s - 1) := by
      rw [hX]
      ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h2 := mul_le_mul hζ hMn (norm_nonneg _) (by positivity)
    linarith
  have hXn : ‖X‖ ≤ 2 := by
    have h1 : X = (X - 1) + 1 := by ring
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_one]
    linarith
  have hbody : windowBody b N s - 1 = (X - 1) - 2 / (s + 1) * X := by
    unfold windowBody
    rw [zetaEntire_eq hne, hX]
    field_simp
    ring
  rw [hbody]
  refine (norm_sub_le _ _).trans (add_le_add hX1 ?_)
  rw [norm_mul, norm_div]
  have hn : 0 < ‖s + 1‖ := norm_pos_iff.mpr hne'
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  calc 2 / ‖s + 1‖ * ‖X‖ ≤ 2 / ‖s + 1‖ * 2 := mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = 4 / ‖s + 1‖ := by ring

/-- The Gaussian mass of the squared window on any line. -/
theorem integral_gaussWindow_sq_eq (t₀ : ℝ) {w : ℝ} (hw : 0 < w) {K : ℝ} (hK : 1 / 2 ≤ K) :
    ∫ t : ℝ, gaussWindow t₀ w ((K : ℂ) + (t : ℂ) * I) * gaussWindow t₀ w ((K : ℂ) + (t : ℂ) * I) =
      ((w * √Real.pi : ℝ) : ℂ) := by
  have hw' : 0 < w / √2 := by positivity
  have hS : ∀ s ∈ {s : ℂ | s.re ∈ uIcc (1 / 2 : ℝ) K}, |s.re - 1 / 2| ≤ K := by
    intro s hs
    have hs' : s.re ∈ uIcc (1 / 2 : ℝ) K := hs
    rw [uIcc_of_le hK] at hs'
    rw [abs_of_nonneg (by linarith [hs'.1])]
    linarith [hs'.2]
  obtain ⟨C, hC⟩ := exists_decay_mul_gaussWindow_sq t₀ hw (G := fun _ => 1) (C₀ := 1) (K := K) (k := 0)
    (by norm_num) hS (fun s _ => by simp)
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay
    (Φ := fun s => gaussWindow t₀ w s * gaussWindow t₀ w s) (c₁ := K) (c₂ := 1 / 2) (C := C)
    (fun s _ => (differentiable_gaussWindow t₀ w s).mul (differentiable_gaussWindow t₀ w s))
    (fun s hs => by
      have h := hC s (by
        show s.re ∈ uIcc (1 / 2 : ℝ) K
        rwa [uIcc_comm])
      simpa using h)
  rw [hshift]
  have hpt : ∀ t : ℝ, gaussWindow t₀ w (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        gaussWindow t₀ w (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      ((Real.exp (-((t - t₀) ^ 2 / (2 * (w / √2) ^ 2))) : ℝ) : ℂ) := by
    intro t
    unfold gaussWindow
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    have hval : (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - 1 / 2 - (t₀ : ℂ) * I) ^ 2) =
        -(((t - t₀ : ℝ) : ℂ) ^ 2) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [hval]
    have hre : (2 * (w / √2) ^ 2 : ℝ) = w ^ 2 := by
      rw [div_pow, hsq]
      ring
    rw [hre]
    push_cast
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_gauss t₀ hw']
  have hsqrt : (w / √2) * √(2 * Real.pi) = w * √Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : √(2 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hsqrt]

/-- **The right floor.**  For `0 ≤ a ≤ 1` and `K ≥ 5`,
`(1 − e)² w√π e^{−a²/w²} ≤ ∫ |F(½ + a + it)|² dt`, with
`e = e^{(K−½)²/w²}(19·2^{−K} + 8/t₀ + 6 e^{−t₀²/(8w²)})`. -/
theorem right_floor {t₀ w a K : ℝ} (ht₀ : 0 < t₀) (hw : 0 < w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hK : 5 ≤ K) {b : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    (he : Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
      (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) ≤ 1) :
    (1 - Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
        (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))))) ^ 2 *
        (w * √Real.pi) * Real.exp (-(a ^ 2 / w ^ 2)) ≤
      ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) a t‖ ^ 2 := by
  set e := Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
    (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) with he'
  set D : ℝ := w * √Real.pi with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  set G : ℝ := Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) with hG
  have hG0 : 0 < G := Real.exp_pos _
  set E := gaussWindow t₀ w with hE
  set c : ℝ := 1 / 2 + a with hc
  have hcK : c ≤ K := by rw [hc]; linarith
  have hcpos : 1 / 2 ≤ c := by rw [hc]; linarith
  -- decay of the product on `½ ≤ Re s ≤ K`
  obtain ⟨C₁, k, hC₁, hZ⟩ := exists_norm_zetaEntire_le (M := K) (by linarith)
  set S : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ K} with hSdef
  have hSK : ∀ s ∈ S, |s.re - 1 / 2| ≤ K := by
    rintro s ⟨h1, h2⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hbody : ∀ s ∈ S, ‖windowBody b N s‖ ≤
      (C₁ * (N : ℝ) ^ ((3 : ℝ) / 2) * 2) * (1 + |s.im|) ^ k := by
    rintro s ⟨h1, h2⟩
    have hs1 : (1 / 2 : ℝ) ≤ ‖s + 1‖ := by
      have h3 := Complex.abs_re_le_norm (s + 1)
      have h4 : (s + 1).re = s.re + 1 := by simp
      rw [h4] at h3
      have h5 := le_abs_self (s.re + 1)
      linarith
    unfold windowBody
    rw [norm_div, norm_mul, div_eq_mul_inv]
    have hinv : ‖s + 1‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖zetaEntire s‖ * ‖edPoly b (Finset.Icc 1 N) s‖ * ‖s + 1‖⁻¹
        ≤ (C₁ * (1 + |s.im|) ^ k) * (N : ℝ) ^ ((3 : ℝ) / 2) * 2 :=
          mul_le_mul (mul_le_mul (hZ s (by linarith) h2)
            (norm_edPoly_le_three_halves hb (by linarith)) (norm_nonneg _) (by positivity)) hinv
            (by positivity) (by positivity)
      _ = _ := by ring
  obtain ⟨C, hC⟩ := exists_decay_mul_gaussWindow_sq t₀ hw (by positivity) hSK hbody
  -- first moment on the far line
  have hsubS : ∀ s : ℂ, s.re ∈ uIcc c K → s ∈ S := by
    intro s hs
    rw [uIcc_of_le hcK] at hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay
    (Φ := fun s => windowBody b N s * E s * E s) (c₁ := c) (c₂ := K) (C := C)
    (fun s hs => by
      have h := hsubS s hs
      exact ((differentiableAt_windowBody b N (by linarith [h.1])).mul
        (differentiable_gaussWindow t₀ w s)).mul (differentiable_gaussWindow t₀ w s))
    (fun s hs => hC s (hsubS s hs))
  set J : ℂ := ∫ t : ℝ, windowBody b N ((c : ℂ) + (t : ℂ) * I) * E ((c : ℂ) + (t : ℂ) * I) *
    E ((c : ℂ) + (t : ℂ) * I) with hJ
  -- the Gaussian mass
  have hmass := integral_gaussWindow_sq_eq t₀ hw (K := K) (by linarith)
  -- the difference on the far line
  have hKS : ∀ t : ℝ, ((K : ℂ) + (t : ℂ) * I) ∈ S := fun t => by
    show 1 / 2 ≤ ((K : ℂ) + (t : ℂ) * I).re ∧ ((K : ℂ) + (t : ℂ) * I).re ≤ K
    rw [re_line']
    exact ⟨by linarith, le_rfl⟩
  have hint1 : Integrable fun t : ℝ => windowBody b N ((K : ℂ) + (t : ℂ) * I) *
      E ((K : ℂ) + (t : ℂ) * I) * E ((K : ℂ) + (t : ℂ) * I) := by
    refine integrable_of_decay_on_line (Φ := fun s => windowBody b N s * E s * E s) (c := K) (C := C)
      (fun t => ?_) (fun t => ?_)
    · have h := hKS t
      exact ((differentiableAt_windowBody b N (by linarith [h.1])).mul
        (differentiable_gaussWindow t₀ w _)).mul (differentiable_gaussWindow t₀ w _)
    · have h := hC _ (hKS t)
      rwa [im_line'] at h
  obtain ⟨C', hC'⟩ := exists_decay_mul_gaussWindow_sq t₀ hw (G := fun _ => 1) (C₀ := 1) (K := K)
    (k := 0) (by norm_num) hSK (fun s _ => by simp)
  have hint2 : Integrable fun t : ℝ => E ((K : ℂ) + (t : ℂ) * I) * E ((K : ℂ) + (t : ℂ) * I) := by
    refine integrable_of_decay_on_line (Φ := fun s => E s * E s) (c := K) (C := C')
      (fun t => ?_) (fun t => ?_)
    · exact (differentiable_gaussWindow t₀ w _).mul (differentiable_gaussWindow t₀ w _)
    · have h := hC' _ (hKS t)
      rw [im_line'] at h
      simpa using h
  have hdiff : J - (D : ℂ) = ∫ t : ℝ, (windowBody b N ((K : ℂ) + (t : ℂ) * I) - 1) *
      (E ((K : ℂ) + (t : ℂ) * I) * E ((K : ℂ) + (t : ℂ) * I)) := by
    rw [hshift, hD, ← hmass, ← integral_sub hint1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    ring
  -- pointwise bound on the far line
  set η : ℝ := 19 * Real.exp (-(Real.log 2 * K)) with hη
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  set κ : ℝ := Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))) with hκ
  have hκ0 : 0 < κ := Real.exp_pos _
  have hw2 : 0 < w / √2 := by positivity
  set g₁ : ℝ → ℝ := fun t => Real.exp (-((t - t₀) ^ 2 / (2 * (w / √2) ^ 2))) with hg₁
  set g₂ : ℝ → ℝ := fun t => Real.exp (-((t - t₀) ^ 2 / (2 * w ^ 2))) with hg₂
  have hsq2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hdenom : 2 * (w / √2) ^ 2 = w ^ 2 := by
    rw [div_pow, hsq2]
    ring
  have hEnorm : ∀ t : ℝ, ‖E ((K : ℂ) + (t : ℂ) * I) * E ((K : ℂ) + (t : ℂ) * I)‖ = G * g₁ t := by
    intro t
    rw [norm_mul, hE, norm_gaussWindow, re_line', im_line', ← Real.exp_add, hG]
    show _ = Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) * Real.exp (-((t - t₀) ^ 2 / (2 * (w / √2) ^ 2)))
    rw [hdenom, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hpoint : ∀ t : ℝ, ‖(windowBody b N ((K : ℂ) + (t : ℂ) * I) - 1) *
      (E ((K : ℂ) + (t : ℂ) * I) * E ((K : ℂ) + (t : ℂ) * I))‖ ≤
      G * ((η + 8 / t₀) * g₁ t + 4 * κ * g₂ t) := by
    intro t
    set s : ℂ := (K : ℂ) + (t : ℂ) * I with hs
    have hre : s.re = K := re_line' K t
    have him : s.im = t := im_line' K t
    have hbound := norm_windowBody_sub_one_le hK hN hb1 hb hre
    rw [norm_mul, hEnorm t]
    have hsplit : 4 / ‖s + 1‖ * g₁ t ≤ (8 / t₀) * g₁ t + 4 * κ * g₂ t := by
      have hg₁0 : 0 < g₁ t := Real.exp_pos _
      have hg₂0 : 0 < g₂ t := Real.exp_pos _
      by_cases ht : t₀ / 2 ≤ t
      · have h1 : t₀ / 2 ≤ ‖s + 1‖ := by
          have h2 := Complex.abs_im_le_norm (s + 1)
          have h3 : (s + 1).im = t := by simp [him]
          rw [h3] at h2
          linarith [le_abs_self t]
        have h4 : 4 / ‖s + 1‖ ≤ 8 / t₀ := by
          rw [div_le_div_iff₀ (by linarith) ht₀]
          linarith
        have := mul_le_mul_of_nonneg_right h4 hg₁0.le
        have h5 : 0 ≤ 4 * κ * g₂ t := by positivity
        linarith
      · have ht' : t < t₀ / 2 := not_le.mp ht
        have h1 : (1 : ℝ) ≤ ‖s + 1‖ := by
          have h2 := Complex.abs_re_le_norm (s + 1)
          have h3 : (s + 1).re = K + 1 := by simp [hre]
          rw [h3] at h2
          have h4 := le_abs_self (K + 1)
          linarith
        have h4 : 4 / ‖s + 1‖ ≤ 4 := by
          rw [div_le_iff₀ (by linarith)]
          linarith
        have hτ : t₀ ^ 2 / 4 ≤ (t - t₀) ^ 2 := by
          have h5 : (t₀ / 2) ^ 2 ≤ (t₀ - t) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
          have h6 : (t - t₀) ^ 2 = (t₀ - t) ^ 2 := by ring
          rw [h6]
          calc t₀ ^ 2 / 4 = (t₀ / 2) ^ 2 := by ring
            _ ≤ _ := h5
        have hg : g₁ t ≤ κ * g₂ t := by
          simp only [hg₁, hg₂, hκ]
          rw [← Real.exp_add, hdenom]
          refine Real.exp_le_exp.mpr ?_
          have hw3 : 0 < w ^ 2 := by positivity
          have h6 : t₀ ^ 2 / (8 * w ^ 2) ≤ (t - t₀) ^ 2 / (2 * w ^ 2) := by
            have h61 : t₀ ^ 2 / (8 * w ^ 2) = (t₀ ^ 2 / 4) / (2 * w ^ 2) := by
              field_simp
              ring
            rw [h61]
            exact div_le_div_of_nonneg_right hτ (by positivity)
          have h7 : (t - t₀) ^ 2 / w ^ 2 = (t - t₀) ^ 2 / (2 * w ^ 2) + (t - t₀) ^ 2 / (2 * w ^ 2) := by
            field_simp
            ring
          rw [h7]
          linarith
        have h8 : 4 / ‖s + 1‖ * g₁ t ≤ 4 * (κ * g₂ t) :=
          mul_le_mul h4 hg hg₁0.le (by norm_num)
        have h9 : 0 ≤ (8 / t₀) * g₁ t := by positivity
        linarith
    have hg₁0 : 0 < g₁ t := Real.exp_pos _
    calc ‖windowBody b N s - 1‖ * (G * g₁ t)
        ≤ (η + 4 / ‖s + 1‖) * (G * g₁ t) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = G * (η * g₁ t + 4 / ‖s + 1‖ * g₁ t) := by ring
      _ ≤ G * (η * g₁ t + ((8 / t₀) * g₁ t + 4 * κ * g₂ t)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hsplit) hG0.le
      _ = _ := by ring
  have hg₁int : Integrable g₁ := integrable_gauss t₀ hw2
  have hg₂int : Integrable g₂ := integrable_gauss t₀ hw
  have hRint : Integrable fun t => G * ((η + 8 / t₀) * g₁ t + 4 * κ * g₂ t) :=
    (((hg₁int.const_mul _).add (hg₂int.const_mul _))).const_mul G
  have hdiffle : ‖J - (D : ℂ)‖ ≤ e * D := by
    rw [hdiff]
    refine (norm_integral_le_of_norm_le hRint (Filter.Eventually.of_forall hpoint)).trans ?_
    have h1 : ∫ t, G * ((η + 8 / t₀) * g₁ t + 4 * κ * g₂ t) =
        G * ((η + 8 / t₀) * (∫ t, g₁ t) + 4 * κ * ∫ t, g₂ t) := by
      rw [integral_const_mul, integral_add (hg₁int.const_mul _) (hg₂int.const_mul _),
        integral_const_mul, integral_const_mul]
    rw [h1, he']
    have hI1 : ∫ t, g₁ t = D := by
      simp only [hg₁]
      rw [integral_gauss t₀ hw2, hD]
      have h2 : √(2 : ℝ) ≠ 0 := by positivity
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have hI2 : ∫ t, g₂ t ≤ (3 / 2) * D := by
      simp only [hg₂]
      rw [integral_gauss t₀ hw, hD, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hs2 : √(2 : ℝ) ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      have hs0 : 0 ≤ w * √Real.pi := by positivity
      have h5 : w * (√2 * √Real.pi) = √2 * (w * √Real.pi) := by ring
      rw [h5]
      exact mul_le_mul_of_nonneg_right hs2 hs0
    rw [hI1]
    have h3 : 4 * κ * ∫ t, g₂ t ≤ 4 * κ * ((3 / 2) * D) :=
      mul_le_mul_of_nonneg_left hI2 (by positivity)
    calc G * ((η + 8 / t₀) * D + 4 * κ * ∫ t, g₂ t)
        ≤ G * ((η + 8 / t₀) * D + 4 * κ * ((3 / 2) * D)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) hG0.le
      _ = G * (η + 8 / t₀ + 6 * κ) * D := by ring
  -- the first moment is large
  have hJlow : (1 - e) * D ≤ ‖J‖ := by
    have h1 : ‖(D : ℂ)‖ ≤ ‖J‖ + ‖J - (D : ℂ)‖ := by
      have h2 : (D : ℂ) = J - (J - (D : ℂ)) := by ring
      calc ‖(D : ℂ)‖ = ‖J - (J - (D : ℂ))‖ := by rw [← h2]
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hD0.le] at h1
    have h3 : (1 - e) * D = D - e * D := by ring
    rw [h3]
    linarith
  -- Cauchy-Schwarz on the line
  obtain ⟨Cs, hCs⟩ := exists_stripDecay_mollifiedWindow t₀ hw hb
  have hamem : a ∈ Icc (-1 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
  set f := lineFun (mollifiedWindow t₀ w b N) a with hf
  set g : ℝ → ℂ := fun t => E ((c : ℂ) + (t : ℂ) * I) with hgdef
  have hgnorm : ∀ t, ‖g t‖ ^ 2 = Real.exp (a ^ 2 / w ^ 2) * g₁ t := by
    intro t
    simp only [hgdef, hg₁]
    rw [hE, norm_gaussWindow, re_line', im_line', ← Real.exp_nat_mul, ← Real.exp_add, hdenom]
    congr 1
    rw [hc]
    push_cast
    field_simp
    ring
  have hgcont : Continuous g := by
    simp only [hgdef]
    exact (differentiable_gaussWindow t₀ w).continuous.comp (by fun_prop)
  have hgint : Integrable fun t => ‖g t‖ ^ 2 := by
    simp_rw [hgnorm]
    exact hg₁int.const_mul _
  have hfint : Integrable fun t => ‖f t‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (hCs.continuous_lineFun hamem).aestronglyMeasurable).mp
      (hCs.memLp_two_lineFun hamem)
  have hCS := norm_sq_integral_mul_le (μ := volume) (hCs.continuous_lineFun hamem).aestronglyMeasurable
    hgcont.aestronglyMeasurable hfint hgint
  have hJeq : ∫ t, f t * g t = J := by
    rw [hJ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf, hgdef, lineFun, mollifiedWindow, hc]
    rw [← hE]
  rw [hJeq] at hCS
  have hgval : ∫ t, ‖g t‖ ^ 2 = Real.exp (a ^ 2 / w ^ 2) * D := by
    simp_rw [hgnorm]
    rw [integral_const_mul]
    simp only [hg₁]
    rw [integral_gauss t₀ hw2, hD, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    have h2 : √(2 : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hgval] at hCS
  have h1e : 0 ≤ 1 - e := by linarith
  have hJsq : ((1 - e) * D) ^ 2 ≤ ‖J‖ ^ 2 := pow_le_pow_left₀ (by positivity) hJlow 2
  have hEpos := Real.exp_pos (a ^ 2 / w ^ 2)
  have hEinv : Real.exp (-(a ^ 2 / w ^ 2)) * Real.exp (a ^ 2 / w ^ 2) = 1 := by
    rw [← Real.exp_add]
    simp
  set I₀ := ∫ t, ‖f t‖ ^ 2 with hI₀
  have hgoal : (1 - e) ^ 2 * D * Real.exp (-(a ^ 2 / w ^ 2)) * D ≤ I₀ * D := by
    have h3 : (1 - e) ^ 2 * D * D ≤ I₀ * (Real.exp (a ^ 2 / w ^ 2) * D) := by
      calc (1 - e) ^ 2 * D * D = ((1 - e) * D) ^ 2 := by ring
        _ ≤ ‖J‖ ^ 2 := hJsq
        _ ≤ _ := hCS
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(a ^ 2 / w ^ 2))).le
    calc (1 - e) ^ 2 * D * Real.exp (-(a ^ 2 / w ^ 2)) * D
        = Real.exp (-(a ^ 2 / w ^ 2)) * ((1 - e) ^ 2 * D * D) := by ring
      _ ≤ Real.exp (-(a ^ 2 / w ^ 2)) * (I₀ * (Real.exp (a ^ 2 / w ^ 2) * D)) := h4
      _ = (Real.exp (-(a ^ 2 / w ^ 2)) * Real.exp (a ^ 2 / w ^ 2)) * (I₀ * D) := by ring
      _ = I₀ * D := by rw [hEinv, one_mul]
  exact le_of_mul_le_mul_right hgoal hD0

/-! ### The left floor -/

/-- **The left floor.**  With the Littlewood constants `C`, `K₁` of the mollified budget: for every real mollifier with bounded coefficients,
if the exponent `E = (2/(T₂−T₁))(2πa ΔN − C − K₁ log(T₂ Mb))` is positive then
`(T₂ − T₁) e^E ≤ ∫_{T₁}^{T₂} |ζM(½ − a + it)|² dt`. -/
theorem exists_left_floor :
    ∃ C K₁ : ℝ, 0 < C ∧ 0 < K₁ ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb → (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ a T₁ T₂ : ℝ, 0 < a → a ≤ 1 / 4 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      0 < 2 * Real.pi * (a * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)) - C -
          K₁ * (Real.log T₂ + Real.log Mb) →
      (T₂ - T₁) * Real.exp (2 / (T₂ - T₁) * (2 * Real.pi * (a * ((xiPosZeroCount T₂ : ℝ) -
          xiPosZeroCount T₁)) - C - K₁ * (Real.log T₂ + Real.log Mb))) ≤
        ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨C, K₁, hC, hK₁, hwide⟩ := exists_zetaWideMoment_le_of_mollified_meanSquare
  refine ⟨C, K₁, hC, hK₁, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb hmass a T₁ T₂ ha0 ha1 h20 hT hG1 hG2 hP1 hP2 hpos
  have hlen : 0 < T₂ - T₁ := by linarith
  set σ₀ : ℝ := 1 / 2 - a with hσ₀
  have hσ₀a : 1 / 4 ≤ σ₀ := by rw [hσ₀]; linarith
  have hσ₀b : σ₀ < 1 / 2 := by rw [hσ₀]; linarith
  have hsub : Set.Icc σ₀ (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc_left hσ₀a
  set I₀ : ℝ := ∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
    edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hI₀
  obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT
  have hc := hwide b N hN hb1 hbn hbreal Mb hMb hmass σ₀ T₁ T₂ I₀ hσ₀a hσ₀b h20 hT
    (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx))
    (fun x hx => hP1 x (hsub hx)) (fun x hx => hP2 x (hsub hx)) le_rfl Z hZ
  have hbridge := window_count_add_tail_le_zetaWideSum (d := a) ha0.le hT.le Z (by
    rw [← hσ₀]
    exact hZ)
  rw [← hσ₀] at hbridge
  have htail : 0 ≤ offLineTail a T₂ - offLineTail a T₁ := sub_nonneg.mpr (offLineTail_mono hT.le)
  have hπ := Real.pi_pos
  set Δ := (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁ with hΔ
  have hchain : 2 * Real.pi * (a * Δ) ≤
      (T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁)) + C + K₁ * (Real.log T₂ + Real.log Mb) := by
    have h1 := mul_le_mul_of_nonneg_left hbridge (by positivity : 0 ≤ 2 * Real.pi)
    have h2 : 0 ≤ 2 * Real.pi * (offLineTail a T₂ - offLineTail a T₁) :=
      mul_nonneg (by positivity) htail
    have h3 : 2 * Real.pi * (a * Δ + (offLineTail a T₂ - offLineTail a T₁)) =
        2 * Real.pi * (a * Δ) + 2 * Real.pi * (offLineTail a T₂ - offLineTail a T₁) := by ring
    linarith
  set E₀ := 2 * Real.pi * (a * Δ) - C - K₁ * (Real.log T₂ + Real.log Mb) with hE₀
  have hlog : E₀ ≤ (T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁)) := by
    rw [hE₀]
    linarith
  have hI₀nn : 0 ≤ I₀ := by
    rw [hI₀]
    exact intervalIntegral.integral_nonneg hT.le fun t _ => by positivity
  have hI₀pos : 0 < I₀ := by
    rcases hI₀nn.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_div, Real.log_zero, mul_zero] at hlog
      linarith
  have hexp : 2 / (T₂ - T₁) * E₀ ≤ Real.log (I₀ / (T₂ - T₁)) := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / (T₂ - T₁))
    have h2 : 2 / (T₂ - T₁) * ((T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁))) =
        Real.log (I₀ / (T₂ - T₁)) := by
      field_simp
    linarith
  have h3 := Real.exp_le_exp.mpr hexp
  rw [Real.exp_log (by positivity), le_div_iff₀ hlen] at h3
  linarith

end GaloisForLFunctions.ArithmeticProduction
