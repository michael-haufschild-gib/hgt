import GaloisForLFunctions.RHTower.WeilEvaporationLockRigidity

/-!
# Locks with a decaying analytic twist are impossible

Let `G` be a Herglotz producer and let `L` be holomorphic on `Re s > ½` and continuous on
`Re s ≥ ½`, with `Re L ≤ A` on the lower strip `½ ≤ Re s ≤ 3/2`, `Im s ≤ −1`, and on the lower
critical line, and with

`Re L(3/2 + iy) → −∞`  as  `y → −∞`.

**Theorem** (`decaying_twist_lock_impossible`).  No Herglotz producer satisfies the lower-line lock
`G(1 − s) = κ₀ e^{L(s)} G(s)`, `s = ½ + 2iτ`, `τ < 0`.

No rate is needed for the decay.  For a lock phase `θ(x)` (`x = −τ`) with holomorphic extension
`L = iΘ`, one has `Re L(3/2 + iy) ≈ −θ'(|y|/2)/2`, so the hypothesis says that the spectral
density of the lock tends to infinity.  Bounded densities (linear phases) are quantized instead
(`linear_twist_quantization`).

**Corollary** (`perturbed_evaporation_lock_impossible`).  The constant-rate evaporation lock
`κ₀ W_B(s) e^{M(s)}` (`B > 0`) is impossible for every holomorphic perturbation `M` whose real
part is bounded above on the lower strip and the lower line.  This contains the linear twists
`M = −(η/2)(s − ½)` (`evaporation_lock_impossible`), so the lock phase may be
`2Bx log(2x) + ηx + ψ(x)` with `ψ` any boundary phase of such an `M`.

**Windows** (`windowed_decaying_twist_lock_impossible`).  The lock may hold only on windows
`−Y_j ≤ τ ≤ −X_j` with `X_j → ∞` and `Y_j` super-polynomial in `X_j`.

**Proof.**  `H = e^{L} G` satisfies `H' = (L' + Φ) H`.  The lower contour shift
(`setIntegral_Iic_radial_eq_of_lower`) writes `∫_{t ≤ −1} φ_H k` as half the right edge on
`Re s = 3/2` plus a bounded top edge.  The right edge is at most
`C ∫_{y ≤ −2} e^{Re L(3/2+iy)} e^{−δ|y|} dy`.  Split at `−Y`, where `Re L ≤ log η'` below `−Y`:
`ε` times the right edge is at most `C(e^A Y ε + η')`.  So the twisted radial integral tends to `0`,
while Hamburger's reflected radial limit is `2β ≠ 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- The twisted producer `e^{L} G`. -/
def expTwistG (L G : ℂ → ℂ) (s : ℂ) : ℂ := cexp (L s) * G s

theorem continuousAt_expTwistG {L G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (expTwistG L G) s :=
  (Complex.continuous_exp.continuousAt.comp (hLc s hs)).mul (hGc s hs)

theorem hasDerivAt_expTwistG {Φ G L : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (expTwistG L G) ((deriv L s + Φ s) * expTwistG L G s) s := by
  have h := ((hLd s hs).hasDerivAt.cexp).mul (hGd s hs)
  refine h.congr_deriv ?_
  unfold expTwistG
  ring

theorem prodF_expTwistG (L G : ℂ → ℂ) (s : ℂ) :
    prodF (expTwistG L G) s = cexp (L s) * prodF G s := by
  unfold prodF expTwistG; ring

theorem phiG_expTwistG (L G : ℂ → ℂ) (t : ℝ) :
    phiG (expTwistG L G) t = cexp (L (lineS t)) * phiG G t := by
  unfold phiG expTwistG; ring

theorem edgeIntegrand_expTwistG (L G : ℂ → ℂ) (τ s : ℂ) :
    edgeIntegrand (expTwistG L G) τ s = cexp (L s) * edgeIntegrand G τ s := by
  unfold edgeIntegrand; rw [prodF_expTwistG]; ring

theorem integrableOn_exp_neg_abs_mul_Iic {δ b : ℝ} (hδ : 0 < δ) (hb : b ≤ 0) :
    IntegrableOn (fun y : ℝ => Real.exp (-(|y| * δ))) (Iic b) := by
  have h : IntegrableOn (fun y : ℝ => ‖cexp ((δ : ℂ) * (y : ℂ))‖) (Iic b) :=
    (integrableOn_exp_mul_complex_Iic (a := (δ : ℂ)) (by simpa using hδ) b).norm
  refine h.congr_fun (fun y hy => ?_) measurableSet_Iic
  have hy0 : y ≤ 0 := le_trans hy hb
  simp only
  rw [Complex.norm_exp, abs_of_nonpos hy0]
  congr 1
  simp
  ring

/-- `∫_{y ≤ b} e^{−δ|y|} dy ≤ 1/δ` for `b ≤ −2`. -/
theorem setIntegral_exp_neg_abs_mul_Iic_le {δ b : ℝ} (hδ : 0 < δ) (hb : b ≤ -2) :
    ∫ y in Iic b, Real.exp (-(|y| * δ)) ≤ 1 / δ := by
  have h := integral_rpow_exp_Iic_le (B := 0) (by norm_num) hδ
  simp only [neg_zero, Real.rpow_zero, one_mul, sub_zero, Real.rpow_one, Real.Gamma_one,
    mul_one] at h
  refine le_trans (setIntegral_mono_set (integrableOn_exp_neg_abs_mul_Iic hδ (by norm_num))
    (ae_of_all _ fun y => (Real.exp_pos _).le) (Iic_subset_Iic.mpr hb).eventuallyLE) h

/-! ### The twisted radial integral vanishes -/

/-- **The decaying-twist radial integral tends to `0`.** -/
theorem tendsto_decaying_twist_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    (hLdec : Tendsto (fun y : ℝ => (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re) atBot atBot) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  obtain ⟨CF₀, hCF₀, hF₀⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  set CF : ℝ := eA * CF₀ with hCF
  have hCF0 : 0 ≤ CF := by positivity
  set H : ℂ → ℂ := expTwistG L G with hH
  have hHc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt H s := fun s hs =>
    continuousAt_expTwistG hGc hLc hs
  have hHd := fun (s : ℂ) (hs : 1 / 2 < s.re) => hasDerivAt_expTwistG hGd hLd hs
  have hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF H ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ) := by
    intro x y hx1 hx2 hy
    have hre : (1 / 2 : ℝ) ≤ ((x : ℂ) + (y : ℂ) * I).re := by simpa using hx1
    have hre2 : ((x : ℂ) + (y : ℂ) * I).re ≤ 3 / 2 := by simpa using hx2
    have him : ((x : ℂ) + (y : ℂ) * I).im ≤ -1 := by simp; linarith
    rw [hH, prodF_expTwistG, norm_mul, Complex.norm_exp, hCF]
    have h1 : Real.exp (L ((x : ℂ) + (y : ℂ) * I)).re ≤ eA :=
      Real.exp_le_exp.mpr (hLs _ hre hre2 him)
    have h3 := hF₀ x y hx1 hx2 (by rw [abs_of_neg (by linarith)]; linarith)
    calc Real.exp (L ((x : ℂ) + (y : ℂ) * I)).re * ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖
        ≤ eA * (CF₀ * (1 + |y|) ^ (1 / 2 : ℝ)) :=
          mul_le_mul h1 h3 (norm_nonneg _) heA0.le
      _ = eA * CF₀ * (1 + |y|) ^ (1 / 2 : ℝ) := by ring
  -- the near part
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_eps_mul_setIntegral_Ioo (h := fun t => cexp (L (lineS t)) * phiG G t)
      (B := eA * (CB * 2 ^ N)) (fun t ht => ?_) le_rfl).congr fun ε => ?_
    · rw [norm_mul, Complex.norm_exp]
      have h1 : Real.exp (L (lineS t)).re ≤ eA := Real.exp_le_exp.mpr (hLl t ht.2)
      have h2 : ‖phiG G t‖ ≤ CB * 2 ^ N := by
        refine (hpoly t).1.trans ?_
        have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        gcongr; linarith
      exact mul_le_mul h1 h2 (norm_nonneg _) heA0.le
    · simp only [mul_assoc]
  -- the far part, for a given tail level `η'` reached below `−Y`
  have hfar_bound : ∀ η' : ℝ, 0 < η' → ∀ Y : ℝ, 2 ≤ Y →
      (∀ y : ℝ, y ≤ -Y → (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ Real.log η') →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
        (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))‖ ≤
      Real.exp S * K * (2 * η') + Real.exp S * K * eA * Y * ε +
        CF * (1 + 2) ^ (1 / 2 : ℝ) * K * ε := by
    intro η' hη' Y hY2 htail ε hε hε1
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = 1 := by simp [hτ]
      rw [him, abs_one] at h; exact h
    have hτ2 : ‖τ‖ ≤ 2 := by
      have h := norm_add_le (ε : ℂ) (((1 : ℕ) : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Nat.cast_one, norm_one,
        Real.norm_eq_abs, abs_of_pos hε] at h
      have e : τ = (ε : ℂ) + 1 * I := by rw [hτ, Nat.cast_one]
      rw [e]; linarith
    have hτpos : 0 < ‖τ‖ := by linarith
    set δ : ℝ := τ.re / ‖τ‖ with hδ
    have hδ0 : 0 < δ := div_pos hτre0 hτpos
    have hδε : ε / 2 ≤ δ := by
      rw [hδ, hτre]; exact div_le_div_of_nonneg_left hε.le hτpos hτ2
    -- the edge bound on `Re s = 3/2`
    have hedge0 : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        Real.exp (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re *
          (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) := by
      intro y hy
      rw [hH, edgeIntegrand_expTwistG, norm_mul, Complex.norm_exp]
      have hE := norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1
        (show 1 ≤ |y| by rw [abs_of_neg (by linarith)]; linarith)
      have hE' : ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := hE
      exact mul_le_mul_of_nonneg_left hE' (Real.exp_pos _).le
    have hLe : ∀ y : ℝ, y ≤ -1 → Real.exp (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ eA := by
      intro y hy
      refine Real.exp_le_exp.mpr (hLs _ (by norm_num) (by norm_num) (by simpa using hy))
    have hedge : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        (eA * Real.exp S) *
          (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
      intro y hy
      refine (hedge0 y hy).trans ?_
      have h0 : 0 ≤ Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
      calc _ ≤ eA * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
            mul_le_mul_of_nonneg_right (hLe y hy) h0
        _ = _ := by rw [hδ, hK]; ring
    -- integrability
    have hfint : IntegrableOn (fun t => phiG H t * pairKernel (2 * t) τ) (Iic (-1)) := by
      have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
        hτre0).norm.const_mul eA).integrableOn (s := Iic (-1))
      refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iic).mpr
        (Filter.Eventually.of_forall fun t ht => ?_))
      · exact ((continuous_phiG hHc).mul (continuous_pairKernel_two_mul hτ0)).aestronglyMeasurable
      · have ht0 : t < 0 := lt_of_le_of_lt ht (by norm_num)
        rw [hH, phiG_expTwistG, mul_assoc, norm_mul, Complex.norm_exp]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
    have hec : Continuous fun y : ℝ => edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hre : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re = 3 / 2 := by simp
      have h0 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this
      have h1 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; norm_num at this
      refine ContinuousAt.comp (g := edgeIntegrand H τ) ?_ (by fun_prop)
      exact (continuousAt_prodF hHc (by rw [hre]; norm_num) h0 h1).mul
        (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num) (by rw [hre]; norm_num)).continuousAt
    have heint : IntegrableOn (fun y : ℝ => edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
        (Iic (-2)) := by
      refine ((integrableOn_exp_neg_abs_mul_Iic hδ0 (by norm_num : (-2 : ℝ) ≤ 0)).const_mul
        (eA * (Real.exp S * (K * ‖τ‖)))).mono' hec.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => ?_))
      have hy' : y ≤ -2 := hy
      refine (hedge0 y (by linarith)).trans ?_
      have h0 : 0 ≤ Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
      calc _ ≤ eA * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
            mul_le_mul_of_nonneg_right (hLe y (by linarith)) h0
        _ = _ := by ring
    have hcont := setIntegral_Iic_radial_eq_of_lower hHc hHd hCF0 hF hτre0 hτ1 hedge le_rfl hfint
    have hrewrite : ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
        (phiG G t * pairKernel (2 * t) τ) =
        ∫ t in Iic (-1 : ℝ), phiG H t * pairKernel (2 * t) τ := by
      refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
      rw [hH, phiG_expTwistG]; ring
    rw [hrewrite, hcont]
    -- the right edge, split at `−Y`
    have hdisj : Disjoint (Iic (-Y)) (Ioc (-Y) (-2 : ℝ)) :=
      Set.disjoint_left.mpr fun y h1 h2 => absurd (show y ≤ -Y from h1) (not_le.mpr h2.1)
    have hright : ‖∫ y in Iic (2 * (-1 : ℝ)),
        edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        (η' * Real.exp S * K * ‖τ‖) * (1 / δ) + Real.exp S * K * ‖τ‖ * eA * (Y - 2) := by
      rw [show (2 * (-1 : ℝ)) = -2 by norm_num,
        ← Iic_union_Ioc_eq_Iic (show -Y ≤ -2 by linarith),
        setIntegral_union hdisj measurableSet_Ioc
          (heint.mono_set (Iic_subset_Iic.mpr (by linarith))) (heint.mono_set Ioc_subset_Iic_self)]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · have hg : IntegrableOn (fun y : ℝ => (η' * Real.exp S * K * ‖τ‖) *
            Real.exp (-(|y| * δ))) (Iic (-Y)) :=
          (integrableOn_exp_neg_abs_mul_Iic hδ0 (by linarith)).const_mul _
        have h : ‖∫ y in Iic (-Y), edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
            ∫ y in Iic (-Y), (η' * Real.exp S * K * ‖τ‖) * Real.exp (-(|y| * δ)) :=
          norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Iic).mpr
            (Eventually.of_forall fun y hy => ?_))
        · refine h.trans ?_
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (setIntegral_exp_neg_abs_mul_Iic_le hδ0 (by linarith))
            (by positivity)
        · have hy' : y ≤ -Y := hy
          refine (hedge0 y (by linarith)).trans ?_
          have h1 : Real.exp (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ η' :=
            calc _ ≤ Real.exp (Real.log η') := Real.exp_le_exp.mpr (htail y hy')
              _ = η' := Real.exp_log hη'
          calc _ ≤ η' * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = _ := by ring
      · have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-Y) (-2 : ℝ))
          (f := fun y : ℝ => edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
          (C := Real.exp S * K * ‖τ‖ * eA) measure_Ioc_lt_top (fun y hy => ?_)
        · rw [Real.volume_real_Ioc_of_le (by linarith)] at h
          refine h.trans (le_of_eq ?_)
          ring
        · have hy2 : y ≤ -2 := hy.2
          refine (hedge0 y (by linarith)).trans ?_
          have he : Real.exp (-(|y| * δ)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; have := abs_nonneg y; nlinarith
          have h0 : 0 ≤ Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ))) := by positivity
          calc _ ≤ eA * (Real.exp S * (K * ‖τ‖ * Real.exp (-(|y| * δ)))) :=
                mul_le_mul_of_nonneg_right (hLe y (by linarith)) h0
            _ ≤ eA * (Real.exp S * (K * ‖τ‖ * 1)) := by gcongr
            _ = _ := by ring
    -- the top edge
    have htop : ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
        edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤
        CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) := by
      have h := norm_horizontalEdge_le_lower hF hτre0 hτ1 (y := 2 * (-1 : ℝ)) (by norm_num)
      refine h.trans ?_
      have habs : |2 * (-1 : ℝ)| = 2 := by norm_num
      rw [habs]
      have he : Real.exp (-(2 * (τ.re / ‖τ‖))) ≤ 1 := by
        rw [Real.exp_le_one_iff]; have := div_pos hτre0 hτpos; linarith
      have h0 : 0 ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) := by positivity
      calc CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
            Real.exp (-(2 * (τ.re / ‖τ‖))))
          ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * 2 * 1) := by gcongr
        _ = CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2) := by rw [hK]; ring
    -- assemble
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, norm_mul,
      show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
    have htri := norm_add_le (∫ y in Iic (2 * (-1 : ℝ)),
      edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I))
    rw [norm_mul (I : ℂ), Complex.norm_I, one_mul] at htri
    have hτh : ‖τ‖ / 2 ≤ 1 := by linarith
    have hεδ : ε * (1 / δ) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hδ0]; linarith
    have ta : ε * (1 / 2) * ((η' * Real.exp S * K * ‖τ‖) * (1 / δ)) ≤
        Real.exp S * K * (2 * η') := by
      have e1 : ε * (1 / 2) * ((η' * Real.exp S * K * ‖τ‖) * (1 / δ)) =
          (η' * Real.exp S * K) * ((‖τ‖ / 2) * (ε * (1 / δ))) := by ring
      have h' : (‖τ‖ / 2) * (ε * (1 / δ)) ≤ 1 * 2 :=
        mul_le_mul hτh hεδ (by positivity) (by norm_num)
      have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ η' * Real.exp S * K by positivity)
      calc _ = _ := e1
        _ ≤ (η' * Real.exp S * K) * (1 * 2) := h''
        _ = Real.exp S * K * (2 * η') := by ring
    have tb : ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) ≤
        Real.exp S * K * eA * Y * ε := by
      have e1 : ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) =
          (Real.exp S * K * eA * ε) * ((‖τ‖ / 2) * (Y - 2)) := by ring
      have h' : (‖τ‖ / 2) * (Y - 2) ≤ 1 * Y :=
        mul_le_mul hτh (by linarith) (by linarith) (by norm_num)
      have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ Real.exp S * K * eA * ε by positivity)
      calc _ = _ := e1
        _ ≤ (Real.exp S * K * eA * ε) * (1 * Y) := h''
        _ = Real.exp S * K * eA * Y * ε := by ring
    have tc : ε * (1 / 2) * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2)) =
        CF * (1 + 2) ^ (1 / 2 : ℝ) * K * ε := by ring
    calc ε * (1 / 2 * ‖(∫ y in Iic (2 * (-1 : ℝ)),
            edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
          I * ∫ x in (1 / 2 : ℝ)..(3 / 2),
            edgeIntegrand H τ ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖)
        ≤ ε * (1 / 2 * (((η' * Real.exp S * K * ‖τ‖) * (1 / δ) +
            Real.exp S * K * ‖τ‖ * eA * (Y - 2)) + CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2))) := by
          gcongr
          exact htri.trans (add_le_add hright htop)
      _ = ε * (1 / 2) * ((η' * Real.exp S * K * ‖τ‖) * (1 / δ)) +
            ε * (1 / 2) * (Real.exp S * K * ‖τ‖ * eA * (Y - 2)) +
            ε * (1 / 2) * (CF * (1 + 2) ^ (1 / 2 : ℝ) * (K * 2)) := by ring
      _ ≤ Real.exp S * K * (2 * η') + Real.exp S * K * eA * Y * ε +
            CF * (1 + 2) ^ (1 / 2 : ℝ) * K * ε := by
          rw [tc]; linarith [ta, tb]
  have hfar : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro e he
    set C₁ : ℝ := Real.exp S * K with hC₁
    have hC₁0 : 0 ≤ C₁ := by positivity
    set η' : ℝ := e / (4 * (C₁ + 1)) with hη'
    have hη'0 : 0 < η' := by positivity
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp
      (hLdec.eventually (eventually_le_atBot (Real.log η')))
    set Y : ℝ := max 2 (-a) with hY
    have hY2 : 2 ≤ Y := le_max_left _ _
    have htail : ∀ y : ℝ, y ≤ -Y →
        (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ Real.log η' := fun y hy =>
      ha y (by have := le_max_right 2 (-a); linarith)
    set C₂ : ℝ := C₁ * eA * Y + CF * (1 + 2) ^ (1 / 2 : ℝ) * K with hC₂
    have hC₂0 : 0 ≤ C₂ := by positivity
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (e / (2 * (C₂ + 1))) by positivity)]
      with ε hε
    rw [dist_zero_right]
    have hb := hfar_bound η' hη'0 Y hY2 htail ε hε.1 (hε.2.le.trans (min_le_left _ _))
    have hε2 : ε * (2 * (C₂ + 1)) < e :=
      (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hε.2 (min_le_right _ _))
    have hη'e : η' * (4 * (C₁ + 1)) = e := by rw [hη']; field_simp
    have h1 : C₂ * ε < e / 2 := by nlinarith [hε.1]
    have h2 : C₁ * (2 * η') < e / 2 := by nlinarith
    calc _ ≤ _ := hb
      _ = C₁ * (2 * η') + C₂ * ε := by rw [hC₂, hC₁]; ring
      _ < e / 2 + e / 2 := add_lt_add h2 h1
      _ = e := by ring
  -- combine
  have hsum := hfar.add hnear
  rw [add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hε' : (0 : ℝ) < ε := hε
  set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
  have hτre : 0 < τ.re := by simp [hτ]; exact hε'
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hint : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iio 0) := by
    have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre).norm.const_mul eA).integrableOn (s := Iio (0 : ℝ))
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iio).mpr
      (Eventually.of_forall fun t ht => ?_))
    · have hc : Continuous fun t : ℝ => phiG H t * pairKernel (2 * t) τ :=
        (continuous_phiG hHc).mul (continuous_pairKernel_two_mul hτ0)
      refine (hc.congr fun t => ?_).aestronglyMeasurable
      rw [hH, phiG_expTwistG]; ring
    · have ht0 : t < 0 := ht
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext t
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro h
      by_cases h1 : t ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
    Set.disjoint_left.mpr fun t h1 h2 => by
      simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
  have h1 : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iic (-1)) := hint.mono_set (by rw [hsplit]; exact subset_union_left)
  have h2 : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Ioo (-1) 0) := hint.mono_set (by rw [hsplit]; exact subset_union_right)
  simp only
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioo h1 h2]
  ring

/-! ### The theorems -/

/-- **Locks with a decaying analytic twist are impossible.**  If `L` is holomorphic on
`Re s > ½`, continuous on `Re s ≥ ½`, `Re L ≤ A` on the lower strip and the lower line, and
`Re L(3/2 + iy) → −∞` as `y → −∞`, then no Herglotz producer satisfies
`G(1 − s) = κ₀ e^{L(s)} G(s)` at `s = ½ + 2iτ`, `τ < 0`. -/
theorem decaying_twist_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    (hLdec : Tendsto (fun y : ℝ => (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re) atBot atBot)
    {κ₀ : ℂ} (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * cexp (L (lineS τ)) * G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  set R : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) with hR
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    have h := (tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 (le_refl 1)).const_mul
      ((2 * Real.pi : ℝ) : ℂ)
    have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) = 2 * betaG G := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast; field_simp
    rw [hval] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    simp only [hR]
    linear_combination ((ε : ℂ) * ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) * h2pi
  have hR0 : Tendsto R (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_decaying_twist_radial hsl hΦre hidT hGc hGd hG2 hLc hLd hLs hLl
      hLdec).const_mul κ₀
    rw [mul_zero] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    simp only [hR]
    rw [← mul_assoc, mul_comm κ₀, mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    have ht0 : t < 0 := ht
    simp only [phiStar, phiG]
    rw [hlock t ht0]
    ring
  have h0 : (2 : ℂ) * betaG G = 0 := tendsto_nhds_unique hRlim hR0
  exact hβ ((mul_eq_zero.mp h0).resolve_left two_ne_zero)

theorem twistG_zero_eq_self (G : ℂ → ℂ) : twistG 0 G = G := by
  funext s
  simp [twistG, linTwist]

/-- **Windowed decaying-twist locks are impossible.**  The lock of
`decaying_twist_lock_impossible` holding only on windows `−Y_j ≤ τ ≤ −X_j` (`X_j → ∞`,
`Y_j ≥ (1 + X_j)^p` eventually for every `p`, `‖κ_j‖ ≤ K₀`) is already impossible. -/
theorem windowed_decaying_twist_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    (hLdec : Tendsto (fun y : ℝ => (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re) atBot atBot)
    {K₀ : ℝ} {X Y : ℕ → ℝ} {κ : ℕ → ℂ}
    (hX : Tendsto X atTop atTop) (hY : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X j) ^ p ≤ Y j)
    (hκ : ∀ j, ‖κ j‖ ≤ K₀)
    (hlock : ∀ j, ∀ τ : ℝ, -Y j ≤ τ → τ ≤ -X j →
      G (1 - lineS τ) = κ j * cexp (L (lineS τ)) * G (lineS τ)) :
    False := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set w : ℝ → ℂ := (Iio (0 : ℝ)).indicator fun τ => cexp (L (lineS τ)) with hw
  have hwc : Continuous fun τ : ℝ => cexp (L (lineS τ)) := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    have hl : Continuous lineS := by unfold lineS; fun_prop
    exact Complex.continuous_exp.continuousAt.comp
      ((hLc _ (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt)
  have hwm : AEStronglyMeasurable w volume :=
    (hwc.measurable.indicator measurableSet_Iio).aestronglyMeasurable
  have hwb : ∀ t, ‖w t‖ ≤ Real.exp A := by
    intro t
    by_cases ht : t < 0
    · rw [hw, Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht), Complex.norm_exp]
      exact Real.exp_le_exp.mpr (hLl t ht)
    · rw [hw, Set.indicator_of_notMem (show t ∉ Iio (0 : ℝ) from ht), norm_zero]
      exact (Real.exp_pos _).le
  have hXpos : ∀ᶠ j in atTop, 0 < X j := hX.eventually_gt_atTop 0
  obtain ⟨j₀, hj₀⟩ := hXpos.exists_forall_of_atTop
  have hX' : Tendsto (fun j => X (j + j₀)) atTop atTop := hX.comp (tendsto_add_atTop_nat j₀)
  have hY' : ∀ p : ℕ, ∀ᶠ j in atTop, (1 + X (j + j₀)) ^ p ≤ Y (j + j₀) := fun p =>
    (tendsto_add_atTop_nat j₀).eventually (hY p)
  refine windowed_lock_impossible_of_tendsto hsl hΦd hΦre hidT hGc hGd hG2 (η := 0) (K₀ := K₀)
    hwm hwb hX' hY' (fun j => hκ (j + j₀)) (fun j τ h1 h2 => ?_) ?_
  · have hτ0 : τ < 0 := by have := hj₀ (j + j₀) (by omega); linarith
    rw [hlock (j + j₀) τ h1 h2, hw, Set.indicator_of_mem (show τ ∈ Iio (0 : ℝ) from hτ0)]
    simp
  · rw [twistG_zero_eq_self]
    refine (tendsto_decaying_twist_radial hsl hΦre hidT hGc hGd hG2 hLc hLd hLs hLl
      hLdec).congr fun ε => ?_
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    rw [hw, Set.indicator_of_mem ht]

/-! ### Perturbed constant-rate evaporation -/

/-- The exponent of the evaporation twist, `W_B = e^{E_B}`. -/
def evapExponent (B : ℝ) (s : ℂ) : ℂ :=
  -((B : ℂ) * ((s - 1 / 2) * (Complex.log (s - 1 / 2) + (Real.pi / 2 : ℝ) * I)))

theorem evapTwist_eq_cexp (B : ℝ) (s : ℂ) : evapTwist B s = cexp (evapExponent B s) := rfl

theorem differentiableAt_evapExponent (B : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (evapExponent B) s := by
  have hslit : s - 1 / 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp; linarith
  have h1 : HasDerivAt (fun z : ℂ => z - 1 / 2) 1 s := (hasDerivAt_id s).sub_const _
  exact ((h1.mul ((h1.clog hslit).add_const ((Real.pi / 2 : ℝ) * I))).const_mul
    (B : ℂ)).neg.differentiableAt

theorem continuousAt_evapExponent' (B : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (evapExponent B) s :=
  (continuousAt_const.mul (continuousAt_evapExponent hs)).neg

theorem re_evapExponent_le_zero {B : ℝ} (hB : 0 ≤ B) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (him : s.im ≤ -1) : (evapExponent B s).re ≤ 0 := by
  have h := norm_evapTwist_le_one hB hs him
  rw [evapTwist_eq_cexp, Complex.norm_exp] at h
  exact Real.exp_le_one_iff.mp h

theorem re_evapExponent_lineS {B t : ℝ} (ht : t < 0) : (evapExponent B (lineS t)).re = 0 := by
  have h := norm_evapTwist_lineS (B := B) ht
  rw [evapTwist_eq_cexp, Complex.norm_exp] at h
  exact Real.exp_eq_one_iff _ |>.mp h

theorem re_evapExponent_three_halves_le {B : ℝ} (hB : 0 ≤ B) {y : ℝ} (hy : y ≤ -1) :
    (evapExponent B (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ -(B * Real.log |y|) := by
  have h := norm_evapTwist_three_halves_le hB hy
  rw [evapTwist_eq_cexp, Complex.norm_exp] at h
  have hy0 : 0 < |y| := by rw [abs_pos]; linarith
  have h' := (Real.le_log_iff_exp_le (Real.rpow_pos_of_pos hy0 _)).mpr h
  rw [Real.log_rpow hy0] at h'
  linarith

/-- **Perturbed constant-rate evaporation locks are impossible.**  Let `B > 0` and let `M` be
holomorphic on `Re s > ½` and continuous on `Re s ≥ ½`, with `Re M ≤ A` on the lower strip and
the lower line.  No Herglotz producer satisfies `G(1 − s) = κ₀ W_B(s) e^{M(s)} G(s)` at
`s = ½ + 2iτ`, `τ < 0`. -/
theorem perturbed_evaporation_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {B : ℝ} (hB : 0 < B) {M : ℂ → ℂ} (hMc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt M s)
    (hMd : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ M s) {A : ℝ}
    (hMs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (M s).re ≤ A)
    (hMl : ∀ t : ℝ, t < 0 → (M (lineS t)).re ≤ A) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * evapTwist B (lineS τ) * cexp (M (lineS τ)) * G (lineS τ)) :
    False := by
  refine decaying_twist_lock_impossible (L := fun s => evapExponent B s + M s) hsl hΦd hΦre hid
    hGc hGd hG2 (fun s hs => (continuousAt_evapExponent' B hs).add (hMc s hs))
    (fun s hs => (differentiableAt_evapExponent B hs).add (hMd s hs)) (A := A)
    (fun s hs1 _ him => ?_) (fun t ht => ?_) ?_ (κ₀ := κ₀) (fun τ hτ => ?_)
  · have h1 := re_evapExponent_le_zero hB.le hs1 him
    have h2 := hMs s hs1 ‹_› him
    simp only [Complex.add_re]
    linarith
  · have h1 := re_evapExponent_lineS (B := B) ht
    have h2 := hMl t ht
    simp only [Complex.add_re]
    linarith
  · have hlog : Tendsto (fun y : ℝ => -(B * Real.log |y|) + A) atBot atBot :=
      tendsto_atBot_add_const_right _ A (tendsto_neg_atTop_atBot.comp
        ((Real.tendsto_log_atTop.comp tendsto_abs_atBot_atTop).const_mul_atTop hB))
    refine tendsto_atBot_mono' _ ?_ hlog
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
    have h1 := re_evapExponent_three_halves_le hB.le hy
    have h2 := hMs (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) (by norm_num) (by norm_num)
      (by simpa using hy)
    simp only [Complex.add_re]
    linarith
  · rw [hlock τ hτ, evapTwist_eq_cexp, mul_assoc κ₀, ← Complex.exp_add]

end

end AbelianTwist

end RHTower
