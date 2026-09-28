import GaloisForLFunctions.RHTower.WeilPositivityHalfPoleRigidity

/-!
# Weil positivity pins the residue: regular rigidity with both poles

Fix the archimedean term and the pole of `ζ` and perturb the von Mangoldt weights to `Λ + w`.

* **Polar pairing** (`polarPairing`).  `Re(ĥ(i/2) conj ĥ(−i/2)) = ∫ cosh(u/2) k(u) du` for the Weil
  test `k = f ⋆ f̃`; it vanishes on polar-constrained tests.
* **Constant weights** (`pairing_one`).  With `n^{-1/2} = ∫_{log(n−1)}^{log n} e^u n^{-1/2} du`,
  `2π ∑_{n ≥ 2} n^{-1/2} φ_f(log n) = 4π Re(ĥ(i/2) conj ĥ(−i/2)) + ∫ |ĥ_f|² P_1`, where
  `∫_0^L e^{u/2} φ_f = 2 Re(ĥ(i/2) conj ĥ(−i/2)) − ∫_0^∞ e^{-u/2} φ_f`
  (`integral_exp_half_mul_weilTestEvenPart_eq`) and `P_1` is continuous of linear growth.
* **Rigidity with a polar atom** (`vonMangoldt_add_eq_zero_of_symbol_polar`).  A polar atom is
  invisible to the polar-constrained concentration tests; probes with polar pairing of either sign
  (`polarPairing_weilScaledBump_pos`, `polarPairing_oddProbe_neg`) force it to vanish.
* **Residue rigidity** (`vonMangoldt_add_residue_eq_zero`).  Partial sums `κ(n − 1) + E(n)` with
  `∑ |E(n)|/(n √n) < ∞` ⇒ `w = 0`.  Example: `Λ + c·1_{2 | n}` only for `c = 0`.
* **Both poles** (`vonMangoldt_add_twoPole_eq_zero`).  Partial sums
  `κ₁(n − 1) + κ₂(√n − 1) + E(n)` with `∑ |E(n)|/(n √n) < ∞` ⇒ `w = 0`.  The two atoms (at the
  origin and at the poles `±i/2`) are separated by zero-mean probes of both polar signs
  (`polarPairing_evenZeroMeanProbe_pos`).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

/-- The polar pairing `Re(ĥ(i/2) · conj ĥ(−i/2)) = ∫ cosh(u/2) k(u) du` of a test. -/
def polarPairing (f : ℝ → ℂ) : ℝ := (paperFT f (I / 2) * conj (paperFT f (-(I / 2)))).re

/-- `∫ κ(x) e^{cx} dx > 0`. -/
def bumpExpMoment (c : ℝ) : ℝ := ∫ x : ℝ, weilBump x * Real.exp (c * x)

theorem bumpExpMoment_pos (c : ℝ) : 0 < bumpExpMoment c := by
  unfold bumpExpMoment
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (weilBump.continuous.mul (by fun_prop)) hasCompactSupport_weilBump.mul_right
    (fun x => mul_nonneg weilBump.nonneg (Real.exp_pos _).le) ?_
  have : weilBump (0 : ℝ) = 1 := weilBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self weilBump.rIn_pos.le)
  rw [this]; simp

theorem paperFT_weilBumpC_I_mul (c : ℝ) :
    paperFT weilBumpC ((c : ℂ) * I) = (bumpExpMoment (-c) : ℂ) := by
  unfold paperFT bumpExpMoment weilBumpC
  rw [← integral_complex_ofReal]
  congr 1; funext x
  have e : I * ((c : ℂ) * I) * (x : ℂ) = ((-c * x : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- The scaled bump `x ↦ κ(x/ε)`. -/
def weilScaledBump (ε : ℝ) (x : ℝ) : ℂ := weilBumpC (x / ε)

theorem paperFT_weilScaledBump_I_mul {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    paperFT (weilScaledBump ε) ((c : ℂ) * I) = ((ε * bumpExpMoment (-(ε * c))) : ℝ) := by
  unfold weilScaledBump
  rw [paperFT_comp_div hε, show (ε : ℂ) * ((c : ℂ) * I) = ((ε * c : ℝ) : ℂ) * I by push_cast; ring,
    paperFT_weilBumpC_I_mul]
  push_cast; ring

theorem contDiff_weilScaledBump (ε : ℝ) : ContDiff ℝ 2 (weilScaledBump ε) :=
  (contDiff_weilBumpC.of_le (by norm_num)).comp (contDiff_id.div_const ε)

theorem weilScaledBump_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : ε / 4 ≤ |x|) : weilScaledBump ε x = 0 := by
  unfold weilScaledBump
  apply weilBumpC_eq_zero
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]; linarith

/-- The odd probe `κ((x − s)/ε) − κ((x + s)/ε)`. -/
def oddProbe (ε s : ℝ) (x : ℝ) : ℂ := weilScaledBump ε (x - s) - weilScaledBump ε (x + s)

theorem contDiff_oddProbe (ε s : ℝ) : ContDiff ℝ 2 (oddProbe ε s) :=
  ((contDiff_weilScaledBump ε).comp (contDiff_id.sub contDiff_const)).sub
    ((contDiff_weilScaledBump ε).comp (contDiff_id.add contDiff_const))

theorem integrable_shift_mul_cexp {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (s : ℝ) (z : ℂ) : Integrable (fun y : ℝ => g (y - s) * cexp (I * z * y)) := by
  have hcs : HasCompactSupport (fun y : ℝ => g (y - s)) :=
    hgc.comp_homeomorph (Homeomorph.subRight s)
  exact ((hg.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
    hcs.mul_right

theorem hasCompactSupport_weilScaledBump {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (weilScaledBump ε) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(ε / 4)) (b := ε / 4))
  intro x hx
  apply weilScaledBump_eq_zero hε
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem paperFT_oddProbe {ε : ℝ} (hε : 0 < ε) (s : ℝ) (z : ℂ) :
    paperFT (oddProbe ε s) z = (cexp (I * z * s) - cexp (I * z * -(s : ℂ))) * paperFT (weilScaledBump ε) z := by
  have hc := (contDiff_weilScaledBump ε).continuous
  have hk := hasCompactSupport_weilScaledBump hε
  have i1 := integrable_shift_mul_cexp hc hk s z
  have i2 : Integrable (fun y : ℝ => weilScaledBump ε (y + s) * cexp (I * z * y)) := by
    simpa [sub_neg_eq_add] using integrable_shift_mul_cexp hc hk (-s) z
  have h1 := paperFT_translate' (weilScaledBump ε) s z
  have h2 := paperFT_translate' (weilScaledBump ε) (-s) z
  simp only [sub_neg_eq_add, ofReal_neg] at h2
  have e : (fun y : ℝ => oddProbe ε s y * cexp (I * z * y)) =
      fun y => weilScaledBump ε (y - s) * cexp (I * z * y) - weilScaledBump ε (y + s) * cexp (I * z * y) := by
    funext y; simp only [oddProbe]; ring
  have h1' : (∫ y : ℝ, weilScaledBump ε (y - s) * cexp (I * z * y)) =
      cexp (I * z * s) * paperFT (weilScaledBump ε) z := h1
  have h2' : (∫ y : ℝ, weilScaledBump ε (y + s) * cexp (I * z * y)) =
      cexp (I * z * -(s : ℂ)) * paperFT (weilScaledBump ε) z := h2
  rw [paperFT, e, integral_sub i1 i2, h1', h2']
  ring

theorem polarPairing_weilScaledBump_pos {ε : ℝ} (hε : 0 < ε) : 0 < polarPairing (weilScaledBump ε) := by
  unfold polarPairing
  have h1 := paperFT_weilScaledBump_I_mul hε (1 / 2)
  have h2 := paperFT_weilScaledBump_I_mul hε (-(1 / 2))
  rw [show ((1 / 2 : ℝ) : ℂ) * I = I / 2 by push_cast; ring] at h1
  rw [show ((-(1 / 2) : ℝ) : ℂ) * I = -(I / 2) by push_cast; ring] at h2
  rw [h1, h2, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos (mul_pos hε (bumpExpMoment_pos _)) (mul_pos hε (bumpExpMoment_pos _))

theorem polarPairing_oddProbe_neg {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : s ≠ 0) :
    polarPairing (oddProbe ε s) < 0 := by
  unfold polarPairing
  rw [paperFT_oddProbe hε, paperFT_oddProbe hε]
  have h1 := paperFT_weilScaledBump_I_mul hε (1 / 2)
  have h2 := paperFT_weilScaledBump_I_mul hε (-(1 / 2))
  rw [show ((1 / 2 : ℝ) : ℂ) * I = I / 2 by push_cast; ring] at h1
  rw [show ((-(1 / 2) : ℝ) : ℂ) * I = -(I / 2) by push_cast; ring] at h2
  rw [h1, h2]
  have e1 : cexp (I * (I / 2) * s) - cexp (I * (I / 2) * -(s : ℂ)) =
      ((Real.exp (-(s / 2)) - Real.exp (s / 2) : ℝ) : ℂ) := by
    push_cast
    rw [show I * (I / 2) * (s : ℂ) = ((-(s / 2) : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring,
      show I * (I / 2) * -(s : ℂ) = ((s / 2 : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring]
    push_cast; ring
  have e2 : cexp (I * -(I / 2) * s) - cexp (I * -(I / 2) * -(s : ℂ)) =
      ((Real.exp (s / 2) - Real.exp (-(s / 2)) : ℝ) : ℂ) := by
    push_cast
    rw [show I * -(I / 2) * (s : ℂ) = ((s / 2 : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring,
      show I * -(I / 2) * -(s : ℂ) = ((-(s / 2)) : ℝ) by push_cast; ring_nf; rw [I_sq]; ring]
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have hd : Real.exp (-(s / 2)) - Real.exp (s / 2) ≠ 0 := by
    intro h
    have := Real.exp_injective (sub_eq_zero.mp h)
    exact hs (by linarith)
  have hB1 := mul_pos hε (bumpExpMoment_pos (-(ε * (1 / 2))))
  have hB2 := mul_pos hε (bumpExpMoment_pos (-(ε * -(1 / 2))))
  have hsq : 0 < (Real.exp (-(s / 2)) - Real.exp (s / 2)) ^ 2 := by positivity
  have e3 : Real.exp (s / 2) - Real.exp (-(s / 2)) = -(Real.exp (-(s / 2)) - Real.exp (s / 2)) := by
    ring
  rw [e3]
  nlinarith [mul_pos hB1 hB2]

theorem tsupport_weilScaledBump_sub_subset {ε s : ℝ} (hε : 0 < ε) :
    tsupport (oddProbe ε s) ⊆ Icc (-(|s| + ε / 4)) (|s| + ε / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  have hxa : |s| + ε / 4 < |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    have hs0 := abs_nonneg s
    rcases h with h | h
    · rw [abs_of_neg (show x < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < x by linarith)]; linarith
  have h1 : weilScaledBump ε (x - s) = 0 := weilScaledBump_eq_zero hε (by
    have := abs_sub_abs_le_abs_sub x s; linarith)
  have h2 : weilScaledBump ε (x + s) = 0 := weilScaledBump_eq_zero hε (by
    have := abs_sub_abs_le_abs_sub x (-s); rw [sub_neg_eq_add, abs_neg] at this; linarith)
  simp [oddProbe, h1, h2]

theorem tsupport_weilScaledBump {ε : ℝ} (hε : 0 < ε) :
    tsupport (weilScaledBump ε) ⊆ Icc (-(ε / 4)) (ε / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  apply weilScaledBump_eq_zero hε
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **Rigidity with a polar atom.**  Suppose the atoms of `w` pair with every test through a
continuous symbol `P` of linear growth plus `m` times the polar pairing
`Re(ĥ(i/2) conj ĥ(−i/2)) = ∫ cosh(u/2) k(u) du`.  If `Λ + w` is Weil-positive, then `w = 0`.
Polar tests do not see the atom, so concentration forces `P ≤ 0`; probes supported in
`[-log 2/4, log 2/4]` with polar pairing of either sign force `m = 0`; then `P ≡ 0` and the
resonators finish. -/
theorem vonMangoldt_add_eq_zero_of_symbol_polar {w : ℕ → ℝ} {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) {m : ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + m * polarPairing f)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  -- on polar tests the atom vanishes
  have hpairP : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ := by
    intro a ha f hf hfs hp
    rw [hpair a ha f hf hfs]
    unfold polarPairing; rw [hp, zero_mul, Complex.zero_re, mul_zero, add_zero]
  -- step 1: `P ≤ 0` (as in the continuous-symbol case, on polar tests)
  have hle : ∀ τ, P τ ≤ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨τ₁, hτ₁⟩ := hall
    set d₁ := P τ₁ with hd₁
    obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
      (hPc.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
    have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ P τ := by
      intro τ hτ
      have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
      rw [Real.dist_eq] at this
      have := (abs_lt.mp this).1
      linarith
    have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
      (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0))))
    obtain ⟨τ₀, h0, hball⟩ := hev.exists
    have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
    have hlim0 : twistLimit 0 τ₀ ≠ 0 := by
      unfold twistLimit
      simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
      exact mul_ne_zero (mul_ne_zero h0 h0) h0
    set m' := ‖twistLimit 0 τ₀‖ with hm'
    have hm0 : 0 < m' := norm_pos_iff.mpr hlim0
    obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
      ((continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m' / 2) (by linarith)
    set η := min (η₁ / 2) (η₂ / 2) with hη
    have hη0 : 0 < η := lt_min (by linarith) (by linarith)
    have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m' / 2 ≤ ‖twistLimit 0 τ‖ := by
      intro τ hτ
      constructor
      · refine hnear₁ τ ?_
        have : |τ - τ₁| ≤ |τ - τ₀| + |τ₀ - τ₁| := by
          calc |τ - τ₁| = |(τ - τ₀) + (τ₀ - τ₁)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        have := min_le_left (η₁ / 2) (η₂ / 2)
        linarith
      · have hd : dist τ τ₀ < η₂ := by
          rw [Real.dist_eq]; have := min_le_right (η₁ / 2) (η₂ / 2); linarith
        have := hη₂ hd
        rw [dist_eq_norm] at this
        have := norm_sub_norm_le (twistLimit 0 τ₀) (twistLimit 0 τ)
        rw [norm_sub_rev] at this
        linarith
    obtain ⟨a, ha, f, hfd, hfs, hp, hm'', hneg⟩ :=
      vonMangoldt_sub_symbol_violation_of_concentration_linear hPc hPb hη0 hm0 hτ₁ hnear
    have := hpos a ha f hfd hfs hp hm''
    rw [integral_weilAtomSymbol_eq_sub hfd hfs] at this
    have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ((Λ n : ℝ) + w n - Λ n) / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
      Finset.sum_congr rfl fun n _ => by ring_nf
    rw [hsum, hpairP a ha f hfd hfs hp] at this
    have hsub : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ)) =
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
          weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ := by
      rw [← integral_sub
        (integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs (fun n => (Λ n : ℝ)))
        (integrable_normSq_paperFT_mul_of_linear hfd hfs hPc hPb)]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only; ring
    linarith
  -- the probe identity
  have hε : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hprobe : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) →
      (∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * P τ) + m * polarPairing g = 0 := by
    intro g hg hgs
    have hint0 := hpair (Real.log 2 / 4) (by positivity) g hg hgs
    rw [floor_exp_half_log_two] at hint0
    simp only [Finset.Icc_eq_empty (by norm_num : ¬ (2 ≤ 1)), Finset.sum_empty, mul_zero] at hint0
    exact hint0.symm
  have hnonpos : ∀ g : ℝ → ℂ, ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * P τ ≤ 0 := fun g =>
    integral_nonpos fun τ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hle τ)
  -- step 2: `m = 0` from probes of both polar signs
  have hε2 : (0 : ℝ) < Real.log 2 / 2 := by positivity
  have hs : Real.log 2 / 8 ≠ 0 := by positivity
  have hsupp1 : tsupport (weilScaledBump (Real.log 2 / 2)) ⊆
      Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) :=
    (tsupport_weilScaledBump hε2).trans (Icc_subset_Icc (by linarith) (by linarith))
  have hsupp2 : tsupport (oddProbe (Real.log 2 / 2) (Real.log 2 / 8)) ⊆
      Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) := by
    refine (tsupport_weilScaledBump_sub_subset hε2).trans (Icc_subset_Icc ?_ ?_) <;>
      rw [abs_of_pos (by positivity)] <;> linarith
  have hm1 := hprobe _ (contDiff_weilScaledBump _) hsupp1
  have hm2 := hprobe _ (contDiff_oddProbe _ _) hsupp2
  have hpp1 := polarPairing_weilScaledBump_pos hε2
  have hpp2 := polarPairing_oddProbe_neg hε2 hs
  have hn1 := hnonpos (weilScaledBump (Real.log 2 / 2))
  have hn2 := hnonpos (oddProbe (Real.log 2 / 2) (Real.log 2 / 8))
  have hmzero : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · have : m * polarPairing (weilScaledBump (Real.log 2 / 2)) < 0 := mul_neg_of_neg_of_pos h hpp1
      linarith
    · exact h
    · have : m * polarPairing (oddProbe (Real.log 2 / 2) (Real.log 2 / 8)) < 0 :=
        mul_neg_of_pos_of_neg h hpp2
      linarith
  -- step 3: the continuous-symbol rigidity
  refine vonMangoldt_add_eq_zero_of_symbol hPc hPb (fun a ha f hf hfs => ?_) hpos hn₀
  rw [hpair a ha f hf hfs, hmzero, zero_mul, add_zero]

/-! ### The pairing of constant weights -/

/-- The residue kernel `K_n(τ) = n^{-1/2} cos(τ log n) − ∫_{log(n−1)}^{log n} e^{u/2} cos(τu) du`. -/
def residueKernel (τ : ℝ) (n : ℕ) : ℝ :=
  1 / Real.sqrt n * Real.cos (τ * Real.log n) -
    ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.exp (u / 2) * Real.cos (τ * u)

/-- The exponential tail `∫_0^∞ e^{-u/2} cos(τu) du`. -/
def expTailSymbol (τ : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) * Real.cos (τ * u)

theorem integrableOn_exp_neg_half : IntegrableOn (fun u : ℝ => Real.exp (-(u / 2))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -(1 / 2)) (by norm_num) 0
  refine this.congr_fun (fun u _ => by simp only; congr 1; ring) measurableSet_Ioi

theorem abs_expTailSymbol_le (τ : ℝ) : |expTailSymbol τ| ≤ 2 := by
  unfold expTailSymbol
  have hi := integrableOn_exp_neg_half
  have h1 : |∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) * Real.cos (τ * u)| ≤
      ∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hi (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have h2 : ∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) = 2 := by
    have := integral_exp_mul_Ioi (a := -(1 / 2)) (by norm_num) 0
    rw [show (fun u : ℝ => Real.exp (-(u / 2))) = fun u => Real.exp (-(1 / 2) * u) by
      funext u; congr 1; ring, this]
    norm_num
  linarith

theorem continuous_expTailSymbol : Continuous expTailSymbol := by
  unfold expTailSymbol
  refine continuous_of_dominated (bound := fun u => Real.exp (-(u / 2)))
    (fun τ => (by fun_prop : Continuous fun u : ℝ => Real.exp (-(u / 2)) *
      Real.cos (τ * u)).aestronglyMeasurable)
    (fun τ => Eventually.of_forall fun u => ?_) integrableOn_exp_neg_half
    (Eventually.of_forall fun u => by fun_prop)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- `n^{-1/2} = ∫_{log(n−1)}^{log n} e^u n^{-1/2} du`. -/
theorem inv_sqrt_eq_integral {n : ℕ} (hn : 2 ≤ n) :
    1 / Real.sqrt n = ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.exp u / Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [intervalIntegral.integral_div, integral_exp, Real.exp_log (by linarith),
    Real.exp_log (by linarith)]
  ring

/-- `|K_n(τ)| ≤ √n (1 + |τ|)/(n − 1)²`. -/
theorem abs_residueKernel_le (τ : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    |residueKernel τ n| ≤ Real.sqrt n * (1 + |τ|) / ((n : ℝ) - 1) ^ 2 := by
  set a := Real.log ((n : ℝ) - 1) with ha
  set b := Real.log (n : ℝ) with hb
  have hab : a ≤ b := log_pred_le_log hn
  have hba : b - a ≤ 1 / ((n : ℝ) - 1) := log_sub_log_pred_le hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have heb : Real.exp (b / 2) = Real.sqrt n := by
    rw [hb, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]; congr 1; ring
  have hi1 : IntervalIntegrable (fun u => Real.exp u / Real.sqrt n * Real.cos (τ * b)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi2 : IntervalIntegrable (fun u => Real.exp (u / 2) * Real.cos (τ * u)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hK : residueKernel τ n = ∫ u in a..b,
      (Real.exp u / Real.sqrt n * Real.cos (τ * b) - Real.exp (u / 2) * Real.cos (τ * u)) := by
    unfold residueKernel
    rw [inv_sqrt_eq_integral hn, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_mul_const]
  rw [hK]
  have hbound : ∀ u ∈ Set.uIoc a b,
      ‖Real.exp u / Real.sqrt n * Real.cos (τ * b) - Real.exp (u / 2) * Real.cos (τ * u)‖ ≤
        Real.sqrt n * (1 + |τ|) * (b - a) := by
    intro u hu
    rw [Set.uIoc_of_le hab] at hu
    obtain ⟨hu1, hu2⟩ := hu
    rw [Real.norm_eq_abs]
    have hsplit : Real.exp u / Real.sqrt n = Real.exp (u / 2) * Real.exp ((u - b) / 2) := by
      rw [← heb, ← Real.exp_add, ← Real.exp_sub]; congr 1; ring
    have e1 : Real.exp u / Real.sqrt n * Real.cos (τ * b) - Real.exp (u / 2) * Real.cos (τ * u) =
        Real.exp (u / 2) * ((Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b) +
          (Real.cos (τ * b) - Real.cos (τ * u))) := by
      rw [hsplit]; ring
    rw [e1, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (u / 2) ≤ Real.sqrt n := by
      rw [← heb]; exact Real.exp_le_exp.mpr (by linarith)
    have h1 : |Real.exp ((u - b) / 2) - 1| ≤ (b - u) / 2 := by
      have hle : Real.exp ((u - b) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have := Real.add_one_le_exp ((u - b) / 2)
      rw [abs_of_nonpos (by linarith)]; linarith
    have h2 : |Real.cos (τ * b) - Real.cos (τ * u)| ≤ |τ| * (b - u) := by
      have := Real.abs_cos_sub_cos_le (τ * b) (τ * u)
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : 0 ≤ b - u)] at this
      exact this
    have h3 : |(Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b)| ≤ (b - u) / 2 := by
      rw [abs_mul]
      exact (mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) (by linarith)).trans
        (by linarith)
    have h4 := abs_add_le ((Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b))
      (Real.cos (τ * b) - Real.cos (τ * u))
    have hin : |(Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b) +
        (Real.cos (τ * b) - Real.cos (τ * u))| ≤ (1 + |τ|) * (b - a) := by
      nlinarith [abs_nonneg τ]
    calc Real.exp (u / 2) * |(Real.exp ((u - b) / 2) - 1) * Real.cos (τ * b) +
          (Real.cos (τ * b) - Real.cos (τ * u))|
        ≤ Real.sqrt n * ((1 + |τ|) * (b - a)) :=
          mul_le_mul hexp hin (abs_nonneg _) hsq.le
      _ = Real.sqrt n * (1 + |τ|) * (b - a) := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at hnorm
  calc _ ≤ Real.sqrt n * (1 + |τ|) * (b - a) * (b - a) := hnorm
    _ ≤ Real.sqrt n * (1 + |τ|) * (1 / ((n : ℝ) - 1)) * (1 / ((n : ℝ) - 1)) := by
        have h0 : 0 ≤ b - a := by linarith
        have h1 : 0 ≤ Real.sqrt n * (1 + |τ|) := by positivity
        gcongr
    _ = Real.sqrt n * (1 + |τ|) / ((n : ℝ) - 1) ^ 2 := by field_simp

/-- The comparison weight `√n/(n−1)²` for `n ≥ 2`. -/
def residueWeight (n : ℕ) : ℝ := if 2 ≤ n then Real.sqrt n / ((n : ℝ) - 1) ^ 2 else 0

theorem residueWeight_nonneg (n : ℕ) : 0 ≤ residueWeight n := by
  unfold residueWeight; split_ifs <;> positivity

theorem summable_residueWeight : Summable residueWeight := by
  refine Summable.of_nonneg_of_le residueWeight_nonneg (fun n => ?_)
    ((summable_growthWeight (θ := 0) (by norm_num)).mul_left 4)
  unfold residueWeight growthWeight
  split_ifs with hn
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hh : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    rw [Real.rpow_zero]
    have hsq2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    calc Real.sqrt n / ((n : ℝ) - 1) ^ 2 ≤ Real.sqrt n / ((n : ℝ) / 2) ^ 2 :=
          div_le_div_of_nonneg_left hsq.le (by positivity) (pow_le_pow_left₀ (by positivity) hh 2)
      _ = 4 * (1 / ((n : ℝ) * Real.sqrt n)) := by
          field_simp
          nlinarith [hsq2]
  · positivity

def residueKernelTerm (τ : ℝ) (n : ℕ) : ℝ := if 2 ≤ n then residueKernel τ n else 0

theorem abs_residueTerm_le (τ : ℝ) (n : ℕ) :
    |residueKernelTerm τ n| ≤ (1 + |τ|) * residueWeight n := by
  unfold residueKernelTerm residueWeight
  split_ifs with hn
  · have := abs_residueKernel_le τ hn
    calc |residueKernel τ n| ≤ Real.sqrt n * (1 + |τ|) / ((n : ℝ) - 1) ^ 2 := this
      _ = (1 + |τ|) * (Real.sqrt n / ((n : ℝ) - 1) ^ 2) := by ring
  · simp

theorem continuous_residueKernel (n : ℕ) : Continuous fun τ => residueKernel τ n := by
  unfold residueKernel
  have h : Continuous fun τ : ℝ => ∫ u in Real.log ((n : ℝ) - 1)..Real.log n,
      Real.exp (u / 2) * Real.cos (τ * u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ u : ℝ => Real.exp (u / 2) * Real.cos (τ * u)) (by fun_prop) _ _
  exact (continuous_const.mul (by fun_prop)).sub h

theorem continuous_residueTerm (n : ℕ) : Continuous fun τ => residueKernelTerm τ n := by
  unfold residueKernelTerm; split_ifs
  · exact continuous_residueKernel n
  · exact continuous_const

theorem summable_residueTerm (τ : ℝ) : Summable fun n => residueKernelTerm τ n :=
  Summable.of_norm_bounded (summable_residueWeight.mul_left (1 + |τ|))
    fun n => by rw [Real.norm_eq_abs]; exact abs_residueTerm_le τ n

/-- The residue symbol `P_1(τ) = 2 ∑_{n ≥ 2} K_n(τ) − 2 ∫_0^∞ e^{-u/2} cos(τu) du`. -/
def residueSymbol (τ : ℝ) : ℝ := 2 * ∑' n : ℕ, residueKernelTerm τ n - 2 * expTailSymbol τ

theorem abs_residueSymbol_le (τ : ℝ) :
    |residueSymbol τ| ≤ (2 * (∑' n : ℕ, residueWeight n) + 4) * (1 + |τ|) := by
  have hs := summable_residueTerm τ
  have h1 : |∑' n : ℕ, residueKernelTerm τ n| ≤ ∑' n : ℕ, |residueKernelTerm τ n| := by
    have := norm_tsum_le_tsum_norm hs.norm
    simp only [Real.norm_eq_abs] at this
    exact this
  have h2 : ∑' n : ℕ, |residueKernelTerm τ n| ≤ ∑' n : ℕ, (1 + |τ|) * residueWeight n :=
    Summable.tsum_le_tsum (fun n => abs_residueTerm_le τ n) hs.abs
      (summable_residueWeight.mul_left _)
  rw [tsum_mul_left] at h2
  have h3 := abs_expTailSymbol_le τ
  have hZ : 0 ≤ ∑' n : ℕ, residueWeight n := tsum_nonneg residueWeight_nonneg
  unfold residueSymbol
  have h4 : |2 * ∑' n : ℕ, residueKernelTerm τ n - 2 * expTailSymbol τ| ≤
      2 * |∑' n : ℕ, residueKernelTerm τ n| + 2 * |expTailSymbol τ| := by
    have := abs_sub (2 * ∑' n : ℕ, residueKernelTerm τ n) (2 * expTailSymbol τ)
    rw [abs_mul, abs_mul, abs_two] at this
    exact this
  nlinarith [abs_nonneg τ]

theorem continuous_residueSymbol : Continuous residueSymbol := by
  have hsum : Continuous fun τ => ∑' n : ℕ, residueKernelTerm τ n := by
    rw [continuous_iff_continuousAt]
    intro τ₁
    have hOn : ContinuousOn (fun τ => ∑' n : ℕ, residueKernelTerm τ n) (Ioo (τ₁ - 1) (τ₁ + 1)) := by
      refine continuousOn_tsum (f := fun (n : ℕ) (τ : ℝ) => residueKernelTerm τ n)
        (u := fun n : ℕ => (1 + (|τ₁| + 1)) * residueWeight n)
        (fun n => (continuous_residueTerm n).continuousOn)
        (summable_residueWeight.mul_left _) fun n τ hτ => ?_
      rw [Real.norm_eq_abs]
      refine (abs_residueTerm_le τ n).trans ?_
      have hτ : |τ| ≤ |τ₁| + 1 := by
        have := abs_sub_abs_le_abs_sub τ τ₁
        have : |τ - τ₁| < 1 := abs_lt.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        linarith
      exact mul_le_mul_of_nonneg_right (by linarith) (residueWeight_nonneg n)
    exact hOn.continuousAt (Ioo_mem_nhds (show τ₁ - 1 < τ₁ by linarith)
      (show τ₁ < τ₁ + 1 by linarith))
  unfold residueSymbol
  exact (continuous_const.mul hsum).sub (continuous_const.mul continuous_expTailSymbol)

theorem integral_normSq_mul_residueKernel {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) {n : ℕ} (hn : 2 ≤ n) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueKernel τ n =
      π * (1 / Real.sqrt n * weilTestEvenPart f (Real.log n) -
        ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.exp (u / 2) * weilTestEvenPart f u) := by
  set A := Real.log ((n : ℝ) - 1) with hA
  set B := Real.log (n : ℝ) with hB
  have hAB : A ≤ B := log_pred_le_log hn
  have hF := integrable_normSq_paperFT hf hfs
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  have hIc : Continuous fun τ : ℝ => ∫ u in A..B, Real.exp (u / 2) * Real.cos (τ * u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ u : ℝ => Real.exp (u / 2) * Real.cos (τ * u)) (by fun_prop) _ _
  have hIb : ∀ τ : ℝ, |∫ u in A..B, Real.exp (u / 2) * Real.cos (τ * u)| ≤
      Real.exp (B / 2) * (B - A) := by
    intro τ
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := A) (b := B)
      (C := Real.exp (B / 2)) (f := fun u => Real.exp (u / 2) * Real.cos (τ * u)) fun u hu => by
        rw [Set.uIoc_of_le hAB] at hu
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans
          (Real.exp_le_exp.mpr (by linarith [hu.2]))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ B - A)] at this
    linarith
  have hI : Integrable fun τ : ℝ =>
      ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.exp (u / 2) * Real.cos (τ * u) := by
    refine (hF.mul_const (Real.exp (B / 2) * (B - A))).mono' (hHc.mul hIc).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hIb τ) (sq_nonneg _)
  have hC := integrable_normSq_paperFT_mul_cos hf hfs B
  have hswap : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.exp (u / 2) * Real.cos (τ * u) =
      ∫ u in A..B, Real.exp (u / 2) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc A B)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
    have hE : Integrable (fun u : ℝ => Real.exp (u / 2)) (volume.restrict (Ioc A B)) :=
      (Real.continuous_exp.comp (continuous_id.div_const 2)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hprod : Integrable (Function.uncurry fun (τ u : ℝ) =>
        ‖paperFT f τ‖ ^ 2 * (Real.exp (u / 2) * Real.cos (τ * u)))
        (volume.prod (volume.restrict (Ioc A B))) := by
      refine (hF.mul_prod hE).mono'
        ((hHc.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      show ‖‖paperFT f p.1‖ ^ 2 * (Real.exp (p.2 / 2) * Real.cos (p.1 * p.2))‖ ≤
        ‖paperFT f p.1‖ ^ 2 * Real.exp (p.2 / 2)
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), norm_mul, Real.norm_of_nonneg
        (Real.exp_pos _).le, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.abs_cos_le_one _)) (sq_nonneg _)
    have e1 : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.exp (u / 2) * Real.cos (τ * u)) =
        fun τ : ℝ => ∫ u in Ioc A B, ‖paperFT f τ‖ ^ 2 * (Real.exp (u / 2) * Real.cos (τ * u)) := by
      funext τ
      rw [intervalIntegral.integral_of_le hAB, ← integral_const_mul]
    rw [e1, integral_integral_swap hprod, intervalIntegral.integral_of_le hAB]
    congr 1; funext u
    rw [← integral_const_mul]; congr 1; funext τ; ring
  have hinner : ∀ u : ℝ, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u) =
      π * weilTestEvenPart f u := fun u => by
    rw [integral_normSq_paperFT_mul_cos_eq hf hfs u]; rfl
  have e2 : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * residueKernel τ n) = fun τ : ℝ =>
      1 / Real.sqrt n * (‖paperFT f τ‖ ^ 2 * Real.cos (τ * B)) -
        ‖paperFT f τ‖ ^ 2 * ∫ u in A..B, Real.exp (u / 2) * Real.cos (τ * u) := by
    funext τ; unfold residueKernel; ring
  rw [e2, integral_sub (hC.const_mul _) hI, integral_const_mul, hswap, hinner B]
  simp_rw [hinner]
  have : ∫ u in A..B, Real.exp (u / 2) * (π * weilTestEvenPart f u) =
      π * ∫ u in A..B, Real.exp (u / 2) * weilTestEvenPart f u := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring
  rw [this]
  ring

/-- `∫_0^∞ e^{-u/2} φ_f(u) du = (1/π) ∫ |ĥ_f|² ∫_0^∞ e^{-u/2} cos(τu) du`. -/
theorem integral_exp_neg_half_mul_weilTestEvenPart {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) * weilTestEvenPart f u =
      (1 / π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * expTailSymbol τ := by
  have hF := integrable_normSq_paperFT hf hfs
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hf hfs
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hf.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  have hE : Integrable (fun u : ℝ => Real.exp (-(u / 2))) (volume.restrict (Ioi 0)) :=
    integrableOn_exp_neg_half
  have hprod : Integrable (Function.uncurry fun (τ u : ℝ) =>
      ‖paperFT f τ‖ ^ 2 * (Real.exp (-(u / 2)) * Real.cos (τ * u)))
      (volume.prod (volume.restrict (Ioi 0))) := by
    refine (hF.mul_prod hE).mono'
      ((hHc.comp continuous_fst).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    show ‖‖paperFT f p.1‖ ^ 2 * (Real.exp (-(p.2 / 2)) * Real.cos (p.1 * p.2))‖ ≤
      ‖paperFT f p.1‖ ^ 2 * Real.exp (-(p.2 / 2))
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), norm_mul, Real.norm_of_nonneg
      (Real.exp_pos _).le, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (Real.exp_pos _).le
      (Real.abs_cos_le_one _)) (sq_nonneg _)
  have hinner : ∀ u : ℝ, weilTestEvenPart f u =
      (1 / π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * Real.cos (τ * u) := fun u => by
    rw [integral_normSq_paperFT_mul_cos_eq hf hfs u]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp; rfl
  have e1 : (fun u : ℝ => Real.exp (-(u / 2)) * weilTestEvenPart f u) = fun u : ℝ =>
      (1 / π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (Real.exp (-(u / 2)) * Real.cos (τ * u)) := by
    funext u
    rw [hinner u, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext τ; ring
  rw [e1, integral_const_mul, ← integral_integral_swap hprod]
  congr 1; congr 1; funext τ
  unfold expTailSymbol
  rw [← integral_const_mul]

/-- **The polar evaluation.**  For `L > 2a`,
`∫_0^L e^{u/2} φ_f(u) du = 2 Re(ĥ(i/2) conj ĥ(−i/2)) − ∫_0^∞ e^{-u/2} φ_f(u) du`. -/
theorem integral_exp_half_mul_weilTestEvenPart_eq {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) {L : ℝ} (hL : 2 * a < L) :
    ∫ u in (0 : ℝ)..L, Real.exp (u / 2) * weilTestEvenPart f u =
      2 * polarPairing f - ∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) * weilTestEvenPart f u := by
  obtain ⟨hfc, hkd, hks, hki, -⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  have hkc : Continuous k := hkd.continuous
  have hL0 : 0 < L := by linarith
  have hzero : ∀ x : ℝ, 2 * a < |x| → k x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hks hmem
      have : |x| ≤ 2 * a := abs_le.mpr ⟨this.1, this.2⟩
      linarith
  have hφ0 : ∀ u : ℝ, 2 * a < |u| → weilTestEvenPart f u = 0 := fun u hu =>
    weilTestEvenPart_eq_zero hf hfs hu
  -- the tail is an interval integral
  have htail : ∫ u in Ioi (0 : ℝ), Real.exp (-(u / 2)) * weilTestEvenPart f u =
      ∫ u in (0 : ℝ)..L, Real.exp (-(u / 2)) * weilTestEvenPart f u := by
    rw [intervalIntegral.integral_of_le hL0.le]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := hx
    have hx3 : L < x := by
      by_contra h; push Not at h; exact hx2 ⟨hx1, h⟩
    rw [hφ0 x (by rw [abs_of_pos (by linarith : (0 : ℝ) < x)]; linarith), mul_zero]
  rw [htail]
  -- the cosh integral of `k`
  set c : ℝ → ℝ := fun u => Real.exp (u / 2) + Real.exp (-(u / 2)) with hc
  have hcc : Continuous c := by rw [hc]; fun_prop
  have hceven : ∀ u, c (-u) = c u := fun u => by
    simp only [hc, neg_div, neg_neg]; ring
  have hsum : (∫ u in (0 : ℝ)..L, Real.exp (u / 2) * weilTestEvenPart f u) +
      (∫ u in (0 : ℝ)..L, Real.exp (-(u / 2)) * weilTestEvenPart f u) =
      (∫ u in (-L)..L, ((c u : ℝ) : ℂ) * k u).re := by
    have hφc : Continuous (weilTestEvenPart f) := (contDiff_weilTestEvenPart hf hfs).continuous
    rw [← intervalIntegral.integral_add ((by fun_prop : Continuous fun u : ℝ =>
      Real.exp (u / 2) * weilTestEvenPart f u).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(u / 2)) * weilTestEvenPart f u).intervalIntegrable _ _)]
    have e1 : (fun u : ℝ => Real.exp (u / 2) * weilTestEvenPart f u +
        Real.exp (-(u / 2)) * weilTestEvenPart f u) =
        fun u : ℝ => (((c u : ℝ) : ℂ) * (k u + k (-u))).re := by
      funext u
      unfold weilTestEvenPart
      rw [← hk, Complex.re_ofReal_mul]; simp only [hc]; ring
    rw [e1]
    have hii : IntervalIntegrable (fun u : ℝ => ((c u : ℝ) : ℂ) * (k u + k (-u))) volume 0 L :=
      ((Complex.continuous_ofReal.comp hcc).mul (hkc.add (hkc.comp continuous_neg))).intervalIntegrable
        _ _
    have hre := Complex.reCLM.intervalIntegral_comp_comm hii
    simp only [Complex.reCLM_apply] at hre
    rw [hre]
    congr 1
    have hi1 : IntervalIntegrable (fun u : ℝ => ((c u : ℝ) : ℂ) * k u) volume 0 L :=
      ((Complex.continuous_ofReal.comp hcc).mul hkc).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun u : ℝ => ((c u : ℝ) : ℂ) * k (-u)) volume 0 L :=
      ((Complex.continuous_ofReal.comp hcc).mul (hkc.comp continuous_neg)).intervalIntegrable _ _
    have e2 : (fun u : ℝ => ((c u : ℝ) : ℂ) * (k u + k (-u))) =
        fun u => ((c u : ℝ) : ℂ) * k u + ((c u : ℝ) : ℂ) * k (-u) := by funext u; ring
    rw [e2, intervalIntegral.integral_add hi1 hi2]
    have hneg : ∫ u in (0 : ℝ)..L, ((c u : ℝ) : ℂ) * k (-u) =
        ∫ u in (-L)..0, ((c u : ℝ) : ℂ) * k u := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := L)
        (fun u : ℝ => ((c u : ℝ) : ℂ) * k u)
      simp only [neg_zero, hceven] at this
      exact this
    have hA1 : IntervalIntegrable (fun u : ℝ => ((c u : ℝ) : ℂ) * k u) volume (-L) 0 :=
      ((Complex.continuous_ofReal.comp hcc).mul hkc).intervalIntegrable _ _
    have hA2 : IntervalIntegrable (fun u : ℝ => ((c u : ℝ) : ℂ) * k u) volume 0 L :=
      ((Complex.continuous_ofReal.comp hcc).mul hkc).intervalIntegrable _ _
    rw [hneg, add_comm, intervalIntegral.integral_add_adjacent_intervals hA1 hA2]
  have hfull : ∫ u in (-L)..L, ((c u : ℝ) : ℂ) * k u = ∫ u, ((c u : ℝ) : ℂ) * k u := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [hzero x (by rw [abs_of_neg (by linarith)]; linarith), mul_zero]
    · rw [hzero x (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  have hint1 : Integrable (fun u : ℝ => k u * cexp (I * (-(I / 2)) * u)) :=
    (hkc.mul (by fun_prop)).integrable_of_hasCompactSupport
      (EF.weilTest_hasCompactSupport hfc hfc).mul_right
  have hint2 : Integrable (fun u : ℝ => k u * cexp (I * (I / 2) * u)) :=
    (hkc.mul (by fun_prop)).integrable_of_hasCompactSupport
      (EF.weilTest_hasCompactSupport hfc hfc).mul_right
  have hsplit : ∫ u, ((c u : ℝ) : ℂ) * k u = paperFT k (-(I / 2)) + paperFT k (I / 2) := by
    unfold paperFT
    rw [← integral_add hint1 hint2]
    congr 1; funext u
    simp only [hc]
    have e1 : cexp (I * (-(I / 2)) * (u : ℂ)) = ((Real.exp (u / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
    have e2 : cexp (I * (I / 2) * (u : ℂ)) = ((Real.exp (-(u / 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
    rw [e1, e2]; push_cast; ring
  have hpw1 := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc (I / 2)
  have hpw2 := EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc (-(I / 2))
  rw [← hk] at hpw1 hpw2
  have hcI : conj (I / 2) = -(I / 2) := by
    rw [map_div₀, Complex.conj_I, map_ofNat]; ring
  have hcI' : conj (-(I / 2)) = I / 2 := by rw [map_neg, hcI, neg_neg]
  rw [hcI] at hpw1
  rw [hcI'] at hpw2
  have hpp : (∫ u in (-L)..L, ((c u : ℝ) : ℂ) * k u).re = 2 * polarPairing f := by
    rw [hfull, hsplit, hpw1, hpw2, Complex.add_re]
    unfold polarPairing
    have : (paperFT f (-(I / 2)) * conj (paperFT f (I / 2))).re =
        (paperFT f (I / 2) * conj (paperFT f (-(I / 2)))).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    rw [this]; ring
  linarith

/-- **The pairing of constant weights.**  `2π ∑_{n ≥ 2} n^{-1/2} φ_f(log n)
= 4π Re(ĥ(i/2) conj ĥ(−i/2)) + ∫ |ĥ_f|² P_1`: a polar atom (the pole of `ζ` at `s = 1`) plus the
continuous residue symbol. -/
theorem pairing_one {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      4 * π * polarPairing f + ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueSymbol τ := by
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  set M := N + 1 with hM
  set φ := weilTestEvenPart f with hφ
  have hφc : Continuous φ := (contDiff_weilTestEvenPart hf hfs).continuous
  have hφ0 : ∀ u : ℝ, 2 * a < |u| → φ u = 0 := fun u hu => weilTestEvenPart_eq_zero hf hfs hu
  have hN1 : 1 ≤ N := by
    rw [hN]; apply Nat.le_floor; push_cast
    exact Real.one_le_exp (by linarith)
  have hlogM : 2 * a < Real.log M := by
    have h1 : Real.exp (2 * a) < (M : ℝ) := by
      rw [hM]; push_cast; exact Nat.lt_floor_add_one _
    rw [← Real.log_exp (2 * a)]
    exact Real.log_lt_log (Real.exp_pos _) h1
  have hM1r : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hlogpos : ∀ n : ℕ, M ≤ n → 2 * a < |Real.log n| := by
    intro n hn
    have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
    have := Real.log_le_log (by linarith) hMn
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    linarith
  have hi : ∑ n ∈ Finset.Icc 2 N, 1 / Real.sqrt n *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 M, 1 / Real.sqrt n * φ (Real.log n) := by
    rw [hM, Finset.sum_Icc_succ_top (by omega), hφ0 _ (hlogpos _ le_rfl), mul_zero, add_zero]
    rfl
  have hii : ∀ n ∈ Finset.Icc 2 M, 1 / Real.sqrt n * φ (Real.log n) =
      (1 / π) * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueKernel τ n) +
        ∫ u in Real.log ((n : ℝ) - 1)..Real.log n, Real.exp (u / 2) * φ u := by
    intro n hn
    rw [integral_normSq_mul_residueKernel hf hfs (Finset.mem_Icc.mp hn).1]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hexpc : Continuous fun u : ℝ => Real.exp (u / 2) * φ u := by fun_prop
  rw [hi, Finset.sum_congr rfl hii, Finset.sum_add_distrib,
    sum_integral_log_steps hexpc M (by omega),
    integral_exp_half_mul_weilTestEvenPart_eq ha hf hfs hlogM,
    integral_exp_neg_half_mul_weilTestEvenPart hf hfs, ← Finset.mul_sum]
  -- the symbol side
  have hlin := integrable_normSq_paperFT_mul_of_linear hf hfs (P := fun τ => 1 + |τ|)
    (by fun_prop) (Mp := 1) fun τ => by rw [abs_of_nonneg (by positivity)]; linarith
  have hterm : ∀ n : ℕ, Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * residueKernelTerm τ n := fun n =>
    integrable_normSq_paperFT_mul_of_linear hf hfs (continuous_residueTerm n)
      (Mp := residueWeight n) fun τ => by
        have := abs_residueTerm_le τ n; linarith [residueWeight_nonneg n]
  have hnorm : Summable fun n : ℕ => ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * residueKernelTerm τ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (summable_residueWeight.mul_right
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 + |τ|)))
    calc ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * residueKernelTerm τ n‖
        ≤ ∫ τ : ℝ, residueWeight n * (‖paperFT f τ‖ ^ 2 * (1 + |τ|)) :=
          integral_mono (hterm n).norm (hlin.const_mul _) fun τ => by
            rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
            have := abs_residueTerm_le τ n
            calc ‖paperFT f τ‖ ^ 2 * |residueKernelTerm τ n|
                ≤ ‖paperFT f τ‖ ^ 2 * ((1 + |τ|) * residueWeight n) :=
                  mul_le_mul_of_nonneg_left this (sq_nonneg _)
              _ = residueWeight n * (‖paperFT f τ‖ ^ 2 * (1 + |τ|)) := by ring
      _ = residueWeight n * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 + |τ|) := integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hterm hnorm
  have hsumK : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (∑' n : ℕ, residueKernelTerm τ n) =
      ∑ n ∈ Finset.Icc 2 M, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueKernel τ n := by
    have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (∑' n : ℕ, residueKernelTerm τ n)) =
        fun τ : ℝ => ∑' n : ℕ, ‖paperFT f τ‖ ^ 2 * residueKernelTerm τ n := by
      funext τ; rw [tsum_mul_left]
    rw [e, ← hswap]
    rw [tsum_eq_sum (s := Finset.Icc 2 M) fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      unfold residueKernelTerm; simp only [if_pos h2]
    · rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with hn | hn
      · have h2 : ¬ 2 ≤ n := by omega
        unfold residueKernelTerm; simp only [if_neg h2, mul_zero, integral_zero]
      · have h2 : 2 ≤ n := by omega
        unfold residueKernelTerm
        simp only [if_pos h2]
        rw [integral_normSq_mul_residueKernel hf hfs h2]
        have hzero : ∫ u in Real.log ((n : ℝ) - 1)..Real.log n,
            Real.exp (u / 2) * weilTestEvenPart f u = 0 := by
          have hM' : M ≤ n - 1 := by omega
          have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          have hlog : 2 * a < Real.log ((n : ℝ) - 1) := by
            have := hlogpos (n - 1) hM'
            rw [hcast] at this
            have h1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
              have : (M : ℝ) ≤ (n : ℝ) - 1 := by rw [← hcast]; exact_mod_cast hM'
              linarith
            rwa [abs_of_nonneg (Real.log_nonneg h1)] at this
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
          · simp
          · rw [Set.uIcc_of_le (log_pred_le_log (by omega))] at hu
            simp only
            rw [show weilTestEvenPart f u = 0 from
              hφ0 u (by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.1]), mul_zero]
        have hz2 : weilTestEvenPart f (Real.log n) = 0 := hφ0 _ (hlogpos n (by omega))
        rw [hzero, hz2]
        simp
  have hsym : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueSymbol τ =
      2 * (∑ n ∈ Finset.Icc 2 M, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueKernel τ n) -
        2 * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * expTailSymbol τ := by
    have hcsum : Continuous fun τ => ∑' n : ℕ, residueKernelTerm τ n := by
      have h2 : (fun τ => ∑' n : ℕ, residueKernelTerm τ n) =
          fun τ => (residueSymbol τ + 2 * expTailSymbol τ) / 2 := by
        funext τ; unfold residueSymbol; ring
      rw [h2]
      exact (continuous_residueSymbol.add (continuous_const.mul continuous_expTailSymbol)).div_const 2
    have hi1 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (∑' n : ℕ, residueKernelTerm τ n) :=
      integrable_normSq_paperFT_mul_of_linear hf hfs hcsum (Mp := ∑' n : ℕ, residueWeight n)
        fun τ => by
          have hs := summable_residueTerm τ
          have h1 : |∑' n : ℕ, residueKernelTerm τ n| ≤ ∑' n : ℕ, |residueKernelTerm τ n| := by
            have := norm_tsum_le_tsum_norm hs.norm
            simp only [Real.norm_eq_abs] at this
            exact this
          have h2 : ∑' n : ℕ, |residueKernelTerm τ n| ≤ ∑' n : ℕ, (1 + |τ|) * residueWeight n :=
            Summable.tsum_le_tsum (fun n => abs_residueTerm_le τ n) hs.abs
              (summable_residueWeight.mul_left _)
          rw [tsum_mul_left] at h2
          have hZ : 0 ≤ ∑' n : ℕ, residueWeight n := tsum_nonneg residueWeight_nonneg
          nlinarith
    have hi2 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * expTailSymbol τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs continuous_expTailSymbol (Mp := 2)
        fun τ => by have := abs_expTailSymbol_le τ; nlinarith [abs_nonneg τ]
    have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * residueSymbol τ) = fun τ : ℝ =>
        2 * (‖paperFT f τ‖ ^ 2 * (∑' n : ℕ, residueKernelTerm τ n)) -
          2 * (‖paperFT f τ‖ ^ 2 * expTailSymbol τ) := by
      funext τ; unfold residueSymbol; ring
    rw [e, integral_sub (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
      integral_const_mul, hsumK]
  rw [hsym]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ### Residue rigidity -/

/-- **Weil positivity pins the residue.**  Let the partial sums of a perturbation `w` be
`κ(n − 1)` plus a remainder `E(n)` with `∑ |E(n)|/(n √n) < ∞` (`κ` arbitrary).  If `Λ + w` is
Weil-positive, then `w = 0`.  The main term `κ(n − 1)` is a shift of the residue of the pole at
`s = 1`; it pairs with the tests through the polar atom `4πκ Re(ĥ(i/2) conj ĥ(−i/2))` plus the
continuous residue symbol. -/
theorem vonMangoldt_add_residue_eq_zero {w : ℕ → ℝ} {κ : ℝ}
    (hE : Summable (partialSumWeight fun n => w n - κ))
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  set e : ℕ → ℝ := fun n => w n - κ with he
  set Z₁ := ∑' n : ℕ, residueWeight n with hZ₁
  set Ze := ∑' n : ℕ, partialSumWeight e n with hZe
  have hZe0 : 0 ≤ Ze := tsum_nonneg (partialSumWeight_nonneg e)
  refine vonMangoldt_add_eq_zero_of_symbol_polar (w := w)
    (P := fun τ => κ * residueSymbol τ + oscSymbol e τ)
    ((continuous_const.mul continuous_residueSymbol).add (continuous_oscSymbol_of_weight hE))
    (Mp := |κ| * (2 * Z₁ + 4) + 2 * Ze) (fun τ => ?_) (m := 4 * π * κ)
    (fun a ha f hf hfs => ?_) hpos hn₀
  · have h1 := abs_residueSymbol_le τ
    have h2 := abs_oscSymbol_le_of_weight hE τ
    calc |κ * residueSymbol τ + oscSymbol e τ| ≤ |κ| * |residueSymbol τ| + |oscSymbol e τ| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |κ| * ((2 * Z₁ + 4) * (1 + |τ|)) + 2 * Ze * (1 + |τ|) := by gcongr
      _ = (|κ| * (2 * Z₁ + 4) + 2 * Ze) * (1 + |τ|) := by ring
  · have h1 := pairing_one ha hf hfs
    have he' := pairing_eq_integral_oscSymbol hE hf hfs
    have hsplit : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        κ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, e n / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [he]; ring
    have hi1 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * residueSymbol τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs continuous_residueSymbol
        (Mp := 2 * Z₁ + 4) fun τ => abs_residueSymbol_le τ
    have hi2 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * oscSymbol e τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs (continuous_oscSymbol_of_weight hE)
        (Mp := 2 * Ze) fun τ => abs_oscSymbol_le_of_weight hE τ
    have hint : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (κ * residueSymbol τ + oscSymbol e τ) =
        κ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueSymbol τ) +
          ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol e τ := by
      rw [← integral_const_mul, ← integral_add (hi1.const_mul κ) hi2]
      congr 1; funext τ; ring
    rw [hsplit, mul_add, hint, ← he']
    have : 2 * π * (κ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) =
        κ * (2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) := by ring
    rw [this, h1]
    ring

/-- The indicator of the even numbers. -/
def evenWeight (n : ℕ) : ℝ := if n % 2 = 0 then 1 else 0

theorem partialFrom2_evenWeight (n : ℕ) : partialFrom2 evenWeight n = (n / 2 : ℕ) := by
  induction n with
  | zero => simp [partialFrom2]
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : n = 0 := by omega
      subst this; simp [partialFrom2, evenWeight]
    · unfold partialFrom2 at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      unfold evenWeight
      split_ifs with h
      · have : (n + 1) / 2 = n / 2 + 1 := by omega
        rw [this]; push_cast; ring
      · have : (n + 1) / 2 = n / 2 := by omega
        rw [this]; simp

/-- **Periodic perturbations with nonzero mean are excluded.**  `Λ + c·1_{2 | n}` is Weil-positive
only for `c = 0`: the perturbation shifts the residue by `c/2`. -/
theorem vonMangoldt_add_even_weilPositive_eq_zero {c : ℝ}
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + c * evenWeight n) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π))) : c = 0 := by
  have hE : Summable (partialSumWeight fun n => c * evenWeight n - c / 2) := by
    refine Summable.of_nonneg_of_le (partialSumWeight_nonneg _) (fun n => ?_)
      ((summable_growthWeight (θ := 0) (by norm_num)).mul_left |c|)
    unfold partialSumWeight growthWeight
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [partialFrom2]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hsum : partialFrom2 (fun k => c * evenWeight k - c / 2) n =
          c * (((n / 2 : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) := by
        unfold partialFrom2
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have := partialFrom2_evenWeight n
        unfold partialFrom2 at this
        rw [this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        rcases Nat.lt_or_ge n 2 with h | h
        · have : n = 1 := by omega
          subst this; norm_num
        · rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hsum, Real.rpow_zero, abs_mul]
      have hb : |((n / 2 : ℕ) : ℝ) - ((n : ℝ) - 1) / 2| ≤ 1 := by
        have h1 : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
        have h2 : (n : ℝ) < ((n / 2 : ℕ) : ℝ) * 2 + 2 := by
          have : n < n / 2 * 2 + 2 := by omega
          exact_mod_cast this
        rw [abs_le]; constructor <;> linarith
      have hd : 0 < (n : ℝ) * Real.sqrt n := by positivity
      rw [mul_one_div]
      calc |c| * |((n / 2 : ℕ) : ℝ) - ((n : ℝ) - 1) / 2| / ((n : ℝ) * Real.sqrt n)
          ≤ |c| * 1 / ((n : ℝ) * Real.sqrt n) := by gcongr
        _ = |c| / ((n : ℝ) * Real.sqrt n) := by ring
  have h := vonMangoldt_add_residue_eq_zero (w := fun n => c * evenWeight n) (κ := c / 2) hE hpos
    (n₀ := 2) le_rfl
  have h2 : evenWeight 2 = 1 := by unfold evenWeight; norm_num
  rw [h2, mul_one] at h
  exact h

/-! ### Both poles at once -/

theorem bumpExpMoment_neg (c : ℝ) : bumpExpMoment (-c) = bumpExpMoment c := by
  unfold bumpExpMoment
  have h := integral_neg_eq_self (fun x : ℝ => weilBump x * Real.exp (c * x)) volume
  simp only [weilBump.neg, mul_neg] at h
  rw [← h]
  congr 1; funext x; ring_nf

/-- `∫ κ e^{cx}` increases strictly with `|c|`. -/
theorem bumpExpMoment_lt {c₁ c₂ : ℝ} (h0 : 0 ≤ c₁) (h : c₁ < c₂) :
    bumpExpMoment c₁ < bumpExpMoment c₂ := by
  have hsym : ∀ c, bumpExpMoment c = ∫ x : ℝ, weilBump x * Real.cosh (c * x) := by
    intro c
    have h2 : 2 * bumpExpMoment c = bumpExpMoment c + bumpExpMoment (-c) := by
      rw [bumpExpMoment_neg]; ring
    have hint : ∀ d : ℝ, Integrable (fun x : ℝ => weilBump x * Real.exp (d * x)) := fun d =>
      (weilBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        hasCompactSupport_weilBump.mul_right
    have : bumpExpMoment c + bumpExpMoment (-c) = ∫ x : ℝ, weilBump x * (2 * Real.cosh (c * x)) := by
      unfold bumpExpMoment
      rw [← integral_add (hint c) (hint (-c))]
      congr 1; funext x; rw [Real.cosh_eq]; ring_nf
    rw [this] at h2
    have h3 : ∫ x : ℝ, weilBump x * (2 * Real.cosh (c * x)) =
        2 * ∫ x : ℝ, weilBump x * Real.cosh (c * x) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    linarith
  have hi : ∀ c : ℝ, Integrable (fun x : ℝ => weilBump x * Real.cosh (c * x)) := fun c =>
    (weilBump.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hasCompactSupport_weilBump.mul_right
  rw [hsym, hsym, ← sub_pos, ← integral_sub (hi c₂) (hi c₁)]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1 / 8)
    ((weilBump.continuous.mul (by fun_prop)).sub (weilBump.continuous.mul (by fun_prop)))
    ((hasCompactSupport_weilBump.mul_right).sub (hasCompactSupport_weilBump.mul_right))
    (fun x => ?_) ?_
  · have hle : Real.cosh (c₁ * x) ≤ Real.cosh (c₂ * x) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by linarith : 0 ≤ c₂)]
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg x)
    have hb := weilBump.nonneg (x := x)
    simp only [Pi.zero_apply]
    nlinarith
  · have hb : weilBump (1 / 8 : ℝ) = 1 := weilBump.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_pos (by norm_num)]; exact le_rfl)
    simp only [hb, one_mul]
    have hlt : Real.cosh (c₁ * (1 / 8)) < Real.cosh (c₂ * (1 / 8)) := by
      rw [Real.cosh_lt_cosh, abs_mul, abs_mul, abs_of_nonneg h0,
        abs_of_nonneg (by linarith : 0 ≤ c₂)]
      exact mul_lt_mul_of_pos_right h (by norm_num)
    exact (sub_pos.mpr hlt).ne'

/-- The even zero-mean probe `κ(x/ε₁) − (ε₁/ε₂) κ(x/ε₂)`. -/
def evenZeroMeanProbe (ε₁ ε₂ : ℝ) (x : ℝ) : ℂ :=
  weilScaledBump ε₁ x - ((ε₁ / ε₂ : ℝ) : ℂ) * weilScaledBump ε₂ x

theorem contDiff_evenZeroMeanProbe (ε₁ ε₂ : ℝ) : ContDiff ℝ 2 (evenZeroMeanProbe ε₁ ε₂) :=
  (contDiff_weilScaledBump ε₁).sub (contDiff_const.mul (contDiff_weilScaledBump ε₂))

theorem paperFT_evenZeroMeanProbe {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h2 : 0 < ε₂) (z : ℂ) :
    paperFT (evenZeroMeanProbe ε₁ ε₂) z =
      paperFT (weilScaledBump ε₁) z - ((ε₁ / ε₂ : ℝ) : ℂ) * paperFT (weilScaledBump ε₂) z := by
  have i1 : Integrable (fun y : ℝ => weilScaledBump ε₁ y * cexp (I * z * y)) := by
    simpa using integrable_shift_mul_cexp (contDiff_weilScaledBump ε₁).continuous
      (hasCompactSupport_weilScaledBump h1) 0 z
  have i2 : Integrable (fun y : ℝ => ((ε₁ / ε₂ : ℝ) : ℂ) * (weilScaledBump ε₂ y * cexp (I * z * y))) := by
    have := integrable_shift_mul_cexp (contDiff_weilScaledBump ε₂).continuous
      (hasCompactSupport_weilScaledBump h2) 0 z
    simp only [sub_zero] at this
    exact this.const_mul _
  have e : (fun y : ℝ => evenZeroMeanProbe ε₁ ε₂ y * cexp (I * z * y)) = fun y =>
      weilScaledBump ε₁ y * cexp (I * z * y) -
        ((ε₁ / ε₂ : ℝ) : ℂ) * (weilScaledBump ε₂ y * cexp (I * z * y)) := by
    funext y; simp only [evenZeroMeanProbe]; ring
  rw [paperFT, e, integral_sub i1 i2, integral_const_mul]
  rfl

theorem paperFT_evenZeroMeanProbe_zero {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h2 : 0 < ε₂) :
    paperFT (evenZeroMeanProbe ε₁ ε₂) 0 = 0 := by
  rw [paperFT_evenZeroMeanProbe h1 h2]
  have e1 := paperFT_weilScaledBump_I_mul h1 0
  have e2 := paperFT_weilScaledBump_I_mul h2 0
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, neg_zero] at e1 e2
  rw [e1, e2]
  have h2' : (ε₂ : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  push_cast
  field_simp
  ring

theorem polarPairing_evenZeroMeanProbe_pos {ε₁ ε₂ : ℝ} (h2 : 0 < ε₂) (h12 : ε₂ < ε₁) :
    0 < polarPairing (evenZeroMeanProbe ε₁ ε₂) := by
  have h1 : 0 < ε₁ := by linarith
  unfold polarPairing
  rw [paperFT_evenZeroMeanProbe h1 h2, paperFT_evenZeroMeanProbe h1 h2]
  have a1 := paperFT_weilScaledBump_I_mul h1 (1 / 2)
  have a2 := paperFT_weilScaledBump_I_mul h2 (1 / 2)
  have b1 := paperFT_weilScaledBump_I_mul h1 (-(1 / 2))
  have b2 := paperFT_weilScaledBump_I_mul h2 (-(1 / 2))
  rw [show ((1 / 2 : ℝ) : ℂ) * I = I / 2 by push_cast; ring] at a1 a2
  rw [show ((-(1 / 2) : ℝ) : ℂ) * I = -(I / 2) by push_cast; ring] at b1 b2
  rw [a1, a2, b1, b2]
  have hm : bumpExpMoment (ε₂ * (1 / 2)) < bumpExpMoment (ε₁ * (1 / 2)) :=
    bumpExpMoment_lt (by positivity) (by linarith)
  have e1 : bumpExpMoment (-(ε₁ * (1 / 2))) = bumpExpMoment (ε₁ * (1 / 2)) := bumpExpMoment_neg _
  have e2 : bumpExpMoment (-(ε₂ * (1 / 2))) = bumpExpMoment (ε₂ * (1 / 2)) := bumpExpMoment_neg _
  have e3 : bumpExpMoment (-(ε₁ * -(1 / 2))) = bumpExpMoment (ε₁ * (1 / 2)) := by
    congr 1; ring
  have e4 : bumpExpMoment (-(ε₂ * -(1 / 2))) = bumpExpMoment (ε₂ * (1 / 2)) := by
    congr 1; ring
  rw [e1, e2, e3, e4]
  set D := ε₁ * bumpExpMoment (ε₁ * (1 / 2)) - ε₁ / ε₂ * (ε₂ * bumpExpMoment (ε₂ * (1 / 2)))
    with hD
  have hDpos : 0 < D := by
    rw [hD, show ε₁ / ε₂ * (ε₂ * bumpExpMoment (ε₂ * (1 / 2))) = ε₁ * bumpExpMoment (ε₂ * (1 / 2)) by
      field_simp]
    nlinarith
  have : (((ε₁ * bumpExpMoment (ε₁ * (1 / 2)) : ℝ) : ℂ) - ((ε₁ / ε₂ : ℝ) : ℂ) *
      ((ε₂ * bumpExpMoment (ε₂ * (1 / 2)) : ℝ) : ℂ)) = ((D : ℝ) : ℂ) := by
    rw [hD]; push_cast; ring
  rw [this, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

theorem tsupport_evenZeroMeanProbe {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h2 : 0 < ε₂) (h12 : ε₂ ≤ ε₁) :
    tsupport (evenZeroMeanProbe ε₁ ε₂) ⊆ Icc (-(ε₁ / 4)) (ε₁ / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  apply hx
  have hxa : ε₁ / 4 < |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (show x < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < x by linarith)]; linarith
  have e1 : weilScaledBump ε₁ x = 0 := weilScaledBump_eq_zero h1 hxa.le
  have e2 : weilScaledBump ε₂ x = 0 := weilScaledBump_eq_zero h2 (by linarith)
  simp [evenZeroMeanProbe, e1, e2]

theorem paperFT_oddProbe_zero {ε : ℝ} (hε : 0 < ε) (s : ℝ) : paperFT (oddProbe ε s) 0 = 0 := by
  rw [paperFT_oddProbe hε]; simp

/-- On polar tests: an atom at the origin does not prevent the concentration argument, so a
Weil-positive `Λ + w` has `P ≤ 0`. -/
theorem symbol_nonpos_of_polar_atom {w : ℕ → ℝ} {P : ℝ → ℝ} (hPc : Continuous P)
    {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) {m : ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + m * ‖paperFT f 0‖ ^ 2)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    ∀ τ, P τ ≤ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨τ₁, hτ₁⟩ := hall
  set d₁ := P τ₁ with hd₁
  obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
    (hPc.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
  have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ P τ := by
    intro τ hτ
    have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  have hne0 : ∀ᶠ t : ℝ in 𝓝[≠] τ₁, t ≠ 0 := by
    rcases eq_or_ne τ₁ 0 with h | h
    · rw [h]; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)
  have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0)))).and hne0
  obtain ⟨τ₀, ⟨h0, hball⟩, hτ₀ne⟩ := hev.exists
  have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
  have hlim0 : twistLimit 0 τ₀ ≠ 0 := by
    unfold twistLimit
    simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  set m' := ‖twistLimit 0 τ₀‖ with hm'
  have hm0 : 0 < m' := norm_pos_iff.mpr hlim0
  obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
    ((continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m' / 2) (by linarith)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η → d₁ / 2 ≤ P τ ∧ m' / 2 ≤ ‖twistLimit 0 τ‖ := by
    intro τ hτ
    constructor
    · refine hnear₁ τ ?_
      have : |τ - τ₁| ≤ |τ - τ₀| + |τ₀ - τ₁| := by
        calc |τ - τ₁| = |(τ - τ₀) + (τ₀ - τ₁)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have := min_le_left (η₁ / 2) (η₂ / 2)
      linarith
    · have hd : dist τ τ₀ < η₂ := by
        rw [Real.dist_eq]; have := min_le_right (η₁ / 2) (η₂ / 2); linarith
      have := hη₂ hd
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le (twistLimit 0 τ₀) (twistLimit 0 τ)
      rw [norm_sub_rev] at this
      linarith
  obtain ⟨a, ha, f, hfd, hfs, hp, hm'', hneg⟩ :=
    vonMangoldt_sub_symbol_atom_violation hPc hPb hη0 hm0 hτ₁ hnear hτ₀ne (abs_nonneg m)
  have := hpos a ha f hfd hfs hp hm''
  rw [integral_weilAtomSymbol_eq_sub hfd hfs] at this
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, ((Λ n : ℝ) + w n - Λ n) / Real.sqrt n *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
    Finset.sum_congr rfl fun n _ => by ring_nf
  rw [hsum, hpair a ha f hfd hfs hp hm''] at this
  have hsub : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) - P τ)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) -
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ := by
    rw [← integral_sub
      (integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs (fun n => (Λ n : ℝ)))
      (integrable_normSq_paperFT_mul_of_linear hfd hfs hPc hPb)]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only; ring
  have hmm : -m * ‖paperFT f 0‖ ^ 2 ≤ |m| * ‖paperFT f 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (neg_le_abs m) (sq_nonneg _)
  linarith

/-- **Rigidity with both poles.**  If the atoms of `w` pair with every test through a continuous
symbol `P` of linear growth plus an atom `m₀ |ĥ(0)|²` at the origin and a polar atom
`m₁ Re(ĥ(i/2) conj ĥ(−i/2))`, then Weil positivity of `Λ + w` forces `w = 0`. -/
theorem vonMangoldt_add_eq_zero_of_symbol_two_atoms {w : ℕ → ℝ} {P : ℝ → ℝ}
    (hPc : Continuous P) {Mp : ℝ} (hPb : ∀ τ, |P τ| ≤ Mp * (1 + |τ|)) {m₀ m₁ : ℝ}
    (hpair : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * P τ) + m₀ * ‖paperFT f 0‖ ^ 2 + m₁ * polarPairing f)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  have hle : ∀ τ, P τ ≤ 0 := symbol_nonpos_of_polar_atom hPc hPb (m := m₀)
    (fun a ha f hf hfs hp _ => by
      rw [hpair a ha f hf hfs]; unfold polarPairing; rw [hp, zero_mul, Complex.zero_re, mul_zero,
        add_zero]) hpos
  have hε : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hprobe : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
      tsupport g ⊆ Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) →
      (∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * P τ) + m₀ * ‖paperFT g 0‖ ^ 2 + m₁ * polarPairing g = 0 := by
    intro g hg hgs
    have hint0 := hpair (Real.log 2 / 4) (by positivity) g hg hgs
    rw [floor_exp_half_log_two] at hint0
    simp only [Finset.Icc_eq_empty (by norm_num : ¬ (2 ≤ 1)), Finset.sum_empty, mul_zero] at hint0
    exact hint0.symm
  have hnonpos : ∀ g : ℝ → ℂ, ∫ τ : ℝ, ‖paperFT g τ‖ ^ 2 * P τ ≤ 0 := fun g =>
    integral_nonpos fun τ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hle τ)
  -- `m₁ = 0` from zero-mean probes of both polar signs
  have hε2 : (0 : ℝ) < Real.log 2 / 2 := by positivity
  have hε4 : (0 : ℝ) < Real.log 2 / 4 := by positivity
  have hs : Real.log 2 / 8 ≠ 0 := by positivity
  have hsupp2 : tsupport (oddProbe (Real.log 2 / 2) (Real.log 2 / 8)) ⊆
      Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) := by
    refine (tsupport_weilScaledBump_sub_subset hε2).trans (Icc_subset_Icc ?_ ?_) <;>
      rw [abs_of_pos (by positivity)] <;> linarith
  have hsupp3 : tsupport (evenZeroMeanProbe (Real.log 2) (Real.log 2 / 2)) ⊆
      Icc (-(Real.log 2 / 4)) (Real.log 2 / 4) :=
    tsupport_evenZeroMeanProbe hε hε2 (by linarith)
  have ho := hprobe _ (contDiff_oddProbe _ _) hsupp2
  have hev := hprobe _ (contDiff_evenZeroMeanProbe _ _) hsupp3
  rw [paperFT_oddProbe_zero hε2, norm_zero] at ho
  rw [paperFT_evenZeroMeanProbe_zero hε hε2, norm_zero] at hev
  have hpo := polarPairing_oddProbe_neg hε2 hs
  have hpe := polarPairing_evenZeroMeanProbe_pos hε2 (by linarith : Real.log 2 / 2 < Real.log 2)
  have hn1 := hnonpos (oddProbe (Real.log 2 / 2) (Real.log 2 / 8))
  have hn2 := hnonpos (evenZeroMeanProbe (Real.log 2) (Real.log 2 / 2))
  have hm1 : m₁ = 0 := by
    rcases lt_trichotomy m₁ 0 with h | h | h
    · have : m₁ * polarPairing (evenZeroMeanProbe (Real.log 2) (Real.log 2 / 2)) < 0 :=
        mul_neg_of_neg_of_pos h hpe
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero] at hev
      linarith
    · exact h
    · have : m₁ * polarPairing (oddProbe (Real.log 2 / 2) (Real.log 2 / 8)) < 0 :=
        mul_neg_of_pos_of_neg h hpo
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero] at ho
      linarith
  -- now only the atom at the origin remains
  refine vonMangoldt_add_eq_zero_of_symbol_atom hPc hPb (m := m₀) (fun a ha f hf hfs => ?_) hpos hn₀
  rw [hpair a ha f hf hfs, hm1, zero_mul, add_zero]

/-- **Regular rigidity with both poles.**  If the partial sums of a perturbation `w` are
`κ₁(n − 1) + κ₂(√n − 1) + E(n)` with `∑ |E(n)|/(n √n) < ∞` (`κ₁, κ₂` arbitrary), then Weil
positivity of `Λ + w` forces `w = 0`.  The two main terms are the pole of `ζ` at `s = 1` (a shift
of the residue) and the pole of `ζ(2s)` at `s = 1/2`. -/
theorem vonMangoldt_add_twoPole_eq_zero {w : ℕ → ℝ} {κ₁ κ₂ : ℝ}
    (hE : Summable (partialSumWeight fun n => w n - κ₁ - κ₂ * sqrtStep n))
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  set e : ℕ → ℝ := fun n => w n - κ₁ - κ₂ * sqrtStep n with he
  set Z₁ := ∑' n : ℕ, residueWeight n
  set Zβ := ∑' n : ℕ, halfPoleWeight n
  set Ze := ∑' n : ℕ, partialSumWeight e n
  refine vonMangoldt_add_eq_zero_of_symbol_two_atoms (w := w)
    (P := fun τ => κ₁ * residueSymbol τ + κ₂ * halfPoleSymbol τ + oscSymbol e τ)
    (((continuous_const.mul continuous_residueSymbol).add
      (continuous_const.mul continuous_halfPoleSymbol)).add (continuous_oscSymbol_of_weight hE))
    (Mp := |κ₁| * (2 * Z₁ + 4) + |κ₂| * (2 * Zβ) + 2 * Ze) (fun τ => ?_)
    (m₀ := π * κ₂) (m₁ := 4 * π * κ₁) (fun a ha f hf hfs => ?_) hpos hn₀
  · have h1 := abs_residueSymbol_le τ
    have h2 := abs_halfPoleSymbol_le τ
    have h3 := abs_oscSymbol_le_of_weight hE τ
    calc |κ₁ * residueSymbol τ + κ₂ * halfPoleSymbol τ + oscSymbol e τ|
        ≤ |κ₁| * |residueSymbol τ| + |κ₂| * |halfPoleSymbol τ| + |oscSymbol e τ| := by
          rw [← abs_mul, ← abs_mul]
          have := abs_add_le (κ₁ * residueSymbol τ + κ₂ * halfPoleSymbol τ) (oscSymbol e τ)
          have := abs_add_le (κ₁ * residueSymbol τ) (κ₂ * halfPoleSymbol τ)
          linarith
      _ ≤ |κ₁| * ((2 * Z₁ + 4) * (1 + |τ|)) + |κ₂| * (2 * Zβ * (1 + |τ|)) + 2 * Ze * (1 + |τ|) := by
          gcongr
      _ = (|κ₁| * (2 * Z₁ + 4) + |κ₂| * (2 * Zβ) + 2 * Ze) * (1 + |τ|) := by ring
  · have h1 := pairing_one ha hf hfs
    have h2 := pairing_sqrtStep ha hf hfs
    have he' := pairing_eq_integral_oscSymbol hE hf hfs
    have hsplit : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, w n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
        κ₁ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re +
        κ₂ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, e n / Real.sqrt n *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [he]; ring
    have hi1 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * residueSymbol τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs continuous_residueSymbol
        (Mp := 2 * Z₁ + 4) fun τ => abs_residueSymbol_le τ
    have hi2 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs continuous_halfPoleSymbol
        (Mp := 2 * Zβ) fun τ => abs_halfPoleSymbol_le τ
    have hi3 : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * oscSymbol e τ :=
      integrable_normSq_paperFT_mul_of_linear hf hfs (continuous_oscSymbol_of_weight hE)
        (Mp := 2 * Ze) fun τ => abs_oscSymbol_le_of_weight hE τ
    have hint : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        (κ₁ * residueSymbol τ + κ₂ * halfPoleSymbol τ + oscSymbol e τ) =
        κ₁ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * residueSymbol τ) +
          κ₂ * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ) +
          ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * oscSymbol e τ := by
      have hi12 : Integrable fun τ : ℝ => κ₁ * (‖paperFT f τ‖ ^ 2 * residueSymbol τ) +
          κ₂ * (‖paperFT f τ‖ ^ 2 * halfPoleSymbol τ) := (hi1.const_mul κ₁).add (hi2.const_mul κ₂)
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hi1.const_mul κ₁) (hi2.const_mul κ₂), ← integral_add hi12 hi3]
      congr 1; funext τ; ring
    rw [hsplit, mul_add, mul_add, hint, ← he']
    have e1 : 2 * π * (κ₁ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) =
        κ₁ * (2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 1 / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) := by ring
    have e2 : 2 * π * (κ₂ * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) =
        κ₂ * (2 * π * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, sqrtStep n / Real.sqrt n *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re) := by ring
    rw [e1, e2, h1, h2]
    ring

end RHTower
