import GaloisForLFunctions.RHTower.CHMDWindowLocalization

/-!
# No Weyl sequences of the arithmetic resolvent above the threshold

Let `R` be the bounded arithmetic resolvent on `L²(Θcosh(x/2)dx)` and `μ > 1/2`. A sequence of
unit vectors `e_n` with `⟪e_n, k⟫ → 0` for every `k` and `‖R e_n − μ e_n‖ → 0` cannot exist.

Proof. By confinement, the window part `1_{|x|≤R} R e_n` carries mass `≥ θ > 0`. Approximate
`Riesz(e_n)` in graph norm by compact `C²` tests `p_n = compactLift v_n` and cut off with the smooth
window `χ_R`: the functions `g_n = χ_R v_n` have uniformly bounded archimedean Lévy forms
(localization), hence uniform high-frequency Fourier tails (logarithmic symbol growth), and they are
weakly null in `L²(dx)` because `e_n` is weakly null and `R` is selfadjoint. Dominated convergence
on the low frequencies and Plancherel then give `∫ g_n² → 0`, contradicting the window mass
`∫ g_n² ≥ nearMass(p_n)/M ≥ θ/(4M)` for large `n`.

Hence every Weyl value of the resolvent lies in `[0, 1/2]`: all spectrum of `R` above `1/2` is
discrete in the Weyl sense, and eigenspaces for eigenvalues above `1/2` admit no infinite
orthonormal family.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Weak nullness -/

/-- A sequence of mass-space vectors is weakly null if it pairs to zero with every vector. -/
def WeaklyNull (e : ℕ → MassSpace) : Prop :=
  ∀ k : MassSpace, Tendsto (fun n => ⟪e n, k⟫_ℝ) atTop (𝓝 0)

theorem weaklyNull_of_orthonormal {e : ℕ → MassSpace} (he : Orthonormal ℝ e) : WeaklyNull e := by
  intro k
  have h := (he.inner_products_summable k).tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h' : Tendsto (fun n => Real.sqrt (‖⟪e n, k⟫_ℝ‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) := h.sqrt
  rw [Real.sqrt_zero] at h'
  exact Filter.Tendsto.congr (fun n => Real.sqrt_sq (norm_nonneg _)) h'

theorem norm_sub_fst_le (p q : SourceGraph) : ‖p.val.fst - q.val.fst‖ ≤ ‖p - q‖ := by
  have h : (p - q).val.fst = p.val.fst - q.val.fst := rfl
  rw [← h]
  exact norm_source_le_graph _

/-- Sources of graph vectors approximating `Riesz(e_n)` are weakly null when `e_n` is. -/
theorem tendsto_inner_source_zero {e : ℕ → MassSpace} (hweak : WeaklyNull e) {p : ℕ → SourceGraph}
    (hp : Tendsto (fun n => ‖p n - rieszLift (e n)‖) atTop (𝓝 0)) (k : MassSpace) :
    Tendsto (fun n => ⟪(p n).val.fst, k⟫_ℝ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ⟪(rieszLift (e n)).val.fst, k⟫_ℝ) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun n => ?_) (hweak (resolvent k))
    show ⟪e n, resolvent k⟫_ℝ = ⟪resolvent (e n), k⟫_ℝ
    rw [resolvent_symm]
  have h2 : Tendsto (fun n => ⟪(p n).val.fst - (rieszLift (e n)).val.fst, k⟫_ℝ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun n => ‖p n - rieszLift (e n)‖ * ‖k‖) atTop (𝓝 0) := by
      simpa using hp.mul_const ‖k‖
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    calc ‖⟪(p n).val.fst - (rieszLift (e n)).val.fst, k⟫_ℝ‖
        ≤ ‖(p n).val.fst - (rieszLift (e n)).val.fst‖ * ‖k‖ := norm_inner_le_norm _ _
      _ ≤ ‖p n - rieszLift (e n)‖ * ‖k‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_fst_le _ _) (norm_nonneg _)
  have h3 := h2.add h1
  rw [add_zero] at h3
  refine Filter.Tendsto.congr (fun n => ?_) h3
  rw [inner_sub_left]
  ring

/-! ## Weights as mass-space vectors -/

/-- The weight `φ / massDensity`, so that pairing with it in `L²(μ)` is the flat pairing with `φ`. -/
def massVecFun (φ : ℝ → ℝ) (x : ℝ) : ℝ := φ x / massDensity x

theorem continuous_massVecFun {φ : ℝ → ℝ} (hφ : Continuous φ) : Continuous (massVecFun φ) :=
  hφ.div continuous_massDensity fun x => (massDensity_pos x).ne'

theorem hasCompactSupport_massVecFun {φ : ℝ → ℝ} (hφc : HasCompactSupport φ) :
    HasCompactSupport (massVecFun φ) := by
  have h := hφc.mul_right (f' := fun x => (massDensity x)⁻¹)
  have he : massVecFun φ = φ * fun x => (massDensity x)⁻¹ := by
    funext x
    simp [massVecFun, div_eq_mul_inv]
  rw [he]
  exact h

/-- The mass-space vector of a continuous compactly supported weight. -/
def massVec (φ : ℝ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) : MassSpace :=
  (compact_memLp_mass (continuous_massVecFun hφ) (hasCompactSupport_massVecFun hφc)).toLp _

theorem inner_compactLift_massVec {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ⟪(compactLift w hw hwc).val.fst, massVec φ hφ hφc⟫_ℝ = ∫ x, w x * φ x := by
  rw [L2.inner_def]
  have hae : (fun x => inner ℝ ((compactLift w hw hwc).val.fst x) ((massVec φ hφ hφc) x)) =ᵐ[massMeasure]
      fun x => w x * massVecFun φ x := by
    filter_upwards [compactLift_source_ae w hw hwc,
      (compact_memLp_mass (continuous_massVecFun hφ) (hasCompactSupport_massVecFun hφc)).coeFn_toLp]
      with x h1 h2
    have h2' : (massVec φ hφ hφc) x = massVecFun φ x := h2
    rw [h1, h2']
    simp [mul_comm]
  rw [integral_congr_ae hae, integral_mass]
  congr 1
  funext x
  have hne := (massDensity_pos x).ne'
  simp only [massVecFun]
  calc massDensity x * (w x * (φ x / massDensity x)) = w x * φ x * (massDensity x / massDensity x) := by
        ring
    _ = w x * φ x := by rw [div_self hne, mul_one]

/-! ## Real and imaginary parts of the Fourier transform -/

theorem paperFT_ofReal_re_im {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) (r : ℂ)).re = ∫ u, g u * Real.cos (r * u) ∧
      (paperFT (fun u => (g u : ℂ)) (r : ℂ)).im = ∫ u, g u * Real.sin (r * u) := by
  have hint : Integrable fun u => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) := by
    have hc : Continuous fun u => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) :=
      (Complex.continuous_ofReal.comp hg).mul (Complex.continuous_exp.comp (by fun_prop))
    exact hc.integrable_of_hasCompactSupport ((hgc.comp_left Complex.ofReal_zero).mul_right)
  have hexp : ∀ u : ℝ, Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by
    intro u
    push_cast
    ring
  unfold paperFT
  constructor
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    show (∫ u, (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re = _
    rw [← h]
    congr 1
    funext u
    rw [hexp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · have h := integral_im hint
    simp only [RCLike.im_to_complex] at h
    show (∫ u, (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).im = _
    rw [← h]
    congr 1
    funext u
    rw [hexp, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem norm_paperFT_ofReal_le {g : ℝ → ℝ} (r : ℝ) :
    ‖paperFT (fun u => (g u : ℂ)) (r : ℂ)‖ ≤ ∫ u, |g u| := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext u
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, show Complex.I * (r : ℂ) * (u : ℂ) =
    ((r * u : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]

/-! ## Uniform bounds for windowed tests -/

theorem abs_le_half_add_sq (a : ℝ) : |a| ≤ (1 + a ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - 1), sq_abs a]

/-- The flat `L¹` norm of a windowed test is controlled by the window and the mass. -/
theorem integral_abs_windowTest_le {R : ℝ} (hR : 0 ≤ R) {m' : ℝ} (hm'0 : 0 < m')
    (hm' : ∀ y, |y| ≤ R + 3 → m' ≤ massDensity y) {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) :
    ∫ u, |windowTest R hR v u| ≤ (R + 2) + (∫ x, v x ^ 2 ∂massMeasure) / (2 * m') := by
  have hW0 := integrable_windowSq (R + 3) hv hvc
  have hind : Integrable ((Icc (-(R + 2)) (R + 2)).indicator fun _ : ℝ => (1 : ℝ) / 2) :=
    (continuous_const.integrableOn_Icc (a := -(R + 2)) (b := R + 2)).integrable_indicator
      measurableSet_Icc
  have hpt : ∀ u, |windowTest R hR v u| ≤
      (Icc (-(R + 2)) (R + 2)).indicator (fun _ => (1 : ℝ) / 2) u + windowSq (R + 3) v u / 2 := by
    intro u
    by_cases hu : |u| ≤ R + 2
    · rw [Set.indicator_of_mem (mem_Icc.mpr (abs_le.mp hu))]
      have h1 := windowTest_sq_le_windowSq hR v u
      have h2 := abs_le_half_add_sq (windowTest R hR v u)
      linarith
    · have h0 : windowTest R hR v u = 0 := by
        unfold windowTest
        rw [windowBump_eq_zero hR (le_of_lt (lt_of_not_ge hu)), zero_mul]
      rw [h0, abs_zero]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => by norm_num) u)
        (by linarith [windowSq_nonneg (R + 3) v u])
  have hvol : (volume (Icc (-(R + 2)) (R + 2))).toReal = 2 * (R + 2) := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  calc ∫ u, |windowTest R hR v u|
      ≤ ∫ u, (Icc (-(R + 2)) (R + 2)).indicator (fun _ => (1 : ℝ) / 2) u + windowSq (R + 3) v u / 2 :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => abs_nonneg _)
          (hind.add (hW0.div_const 2)) (Eventually.of_forall hpt)
    _ = (R + 2) + flatWindowMass (R + 3) v / 2 := by
        rw [integral_add hind (hW0.div_const 2), integral_div, integral_windowSq,
          integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, measureReal_def, hvol]
        ring
    _ ≤ (R + 2) + (∫ x, v x ^ 2 ∂massMeasure) / (2 * m') := by
        have h1 := flatWindowMass_le hm'0 hm' hv hvc
        have h2 : (∫ x, v x ^ 2 ∂massMeasure) / m' / 2 = (∫ x, v x ^ 2 ∂massMeasure) / (2 * m') := by
          ring
        linarith [div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2)]

theorem fourierSq_windowTest_le {R : ℝ} (hR : 0 ≤ R) {m' : ℝ} (hm'0 : 0 < m')
    (hm' : ∀ y, |y| ≤ R + 3 → m' ≤ massDensity y) {v : ℝ → ℝ} (hv : Continuous v)
    (hvc : HasCompactSupport v) (r : ℝ) :
    fourierSq (windowTest R hR v) r ≤ ((R + 2) + (∫ x, v x ^ 2 ∂massMeasure) / (2 * m')) ^ 2 := by
  unfold fourierSq
  have h := norm_paperFT_ofReal_le (g := windowTest R hR v) r
  have h2 := integral_abs_windowTest_le hR hm'0 hm' hv hvc
  exact pow_le_pow_left₀ (norm_nonneg _) (h.trans h2) 2

/-! ## Pointwise decay of the Fourier transforms along a weakly null family -/

theorem tendsto_fourierSq_windowTest {e : ℕ → MassSpace} (hweak : WeaklyNull e) {v : ℕ → ℝ → ℝ}
    (hv : ∀ n, ContDiff ℝ 2 (v n)) (hvc : ∀ n, HasCompactSupport (v n))
    (hp : Tendsto (fun n => ‖compactLift (v n) (hv n) (hvc n) - rieszLift (e n)‖) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (r : ℝ) :
    Tendsto (fun n => fourierSq (windowTest R hR (v n)) r) atTop (𝓝 0) := by
  set φc : ℝ → ℝ := fun u => windowBump R hR u * Real.cos (r * u) with hφc_def
  set φs : ℝ → ℝ := fun u => windowBump R hR u * Real.sin (r * u) with hφs_def
  have hφc : Continuous φc :=
    (contDiff_windowBump R hR).continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hφcc : HasCompactSupport φc := (hasCompactSupport_windowBump R hR).mul_right
  have hφs : Continuous φs :=
    (contDiff_windowBump R hR).continuous.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hφsc : HasCompactSupport φs := (hasCompactSupport_windowBump R hR).mul_right
  have hre : ∀ n, (paperFT (fun u => (windowTest R hR (v n) u : ℂ)) (r : ℂ)).re =
      ⟪(compactLift (v n) (hv n) (hvc n)).val.fst, massVec φc hφc hφcc⟫_ℝ := by
    intro n
    rw [(paperFT_ofReal_re_im (contDiff_windowTest R hR (hv n)).continuous
      (hasCompactSupport_windowTest R hR (hvc n)) r).1, inner_compactLift_massVec]
    congr 1
    funext u
    simp only [windowTest, hφc_def]
    ring
  have him : ∀ n, (paperFT (fun u => (windowTest R hR (v n) u : ℂ)) (r : ℂ)).im =
      ⟪(compactLift (v n) (hv n) (hvc n)).val.fst, massVec φs hφs hφsc⟫_ℝ := by
    intro n
    rw [(paperFT_ofReal_re_im (contDiff_windowTest R hR (hv n)).continuous
      (hasCompactSupport_windowTest R hR (hvc n)) r).2, inner_compactLift_massVec]
    congr 1
    funext u
    simp only [windowTest, hφs_def]
    ring
  have h1 := tendsto_inner_source_zero hweak (p := fun n => compactLift (v n) (hv n) (hvc n)) hp
    (massVec φc hφc hφcc)
  have h2 := tendsto_inner_source_zero hweak (p := fun n => compactLift (v n) (hv n) (hvc n)) hp
    (massVec φs hφs hφsc)
  have h3 : Tendsto (fun n => |⟪(compactLift (v n) (hv n) (hvc n)).val.fst, massVec φc hφc hφcc⟫_ℝ| +
      |⟪(compactLift (v n) (hv n) (hvc n)).val.fst, massVec φs hφs hφsc⟫_ℝ|) atTop (𝓝 0) := by
    have := h1.abs.add h2.abs
    simpa using this
  have hnorm : Tendsto (fun n => ‖paperFT (fun u => (windowTest R hR (v n) u : ℂ)) (r : ℂ)‖)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h3
    rw [← hre n, ← him n]
    exact Complex.norm_le_abs_re_add_abs_im _
  unfold fourierSq
  simpa using hnorm.pow 2

/-! ## The main theorem -/

/-- **No Weyl sequences above the threshold.** For `μ > 1/2` there is no weakly null sequence of
unit vectors `e_n` with `‖R e_n − μ e_n‖ → 0`. -/
theorem no_weakly_null_weyl_above_half {μ : ℝ} (hμ : 1 / 2 < μ) (e : ℕ → MassSpace)
    (he : ∀ n, ‖e n‖ = 1) (hweak : WeaklyNull e)
    (hw : Tendsto (fun n => ‖resolvent (e n) - μ • e n‖) atTop (𝓝 0)) : False := by
  obtain ⟨R, θ, η, hR0, hθ, hη, hconf⟩ := exists_window_mass_resolvent hμ
  -- compact approximants of the Riesz lifts
  have happrox : ∀ n : ℕ, ∃ (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v),
      ‖compactLift v hv hvc - rieszLift (e n)‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨q, hq, hd⟩ := dense_compactTests.exists_dist_lt (rieszLift (e n))
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    obtain ⟨v, hv, hvc, rfl⟩ := hq
    exact ⟨v, hv, hvc, by rwa [dist_comm, dist_eq_norm] at hd⟩
  choose v hv hvc hdist using happrox
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : Tendsto (fun n => ‖compactLift (v n) (hv n) (hvc n) - rieszLift (e n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hdist n).le) hinv
  -- uniform graph bounds
  have hriesz : ∀ n, ‖rieszLift (e n)‖ ≤ 1 := by
    intro n
    have h := graph_norm_sq_rieszLift (e n)
    have h2 : ⟪e n, resolvent (e n)⟫_ℝ ≤ 1 := by
      calc ⟪e n, resolvent (e n)⟫_ℝ ≤ ‖e n‖ * ‖resolvent (e n)‖ := real_inner_le_norm _ _
        _ ≤ 1 * 1 := by
            rw [he n]
            refine mul_le_mul_of_nonneg_left ?_ zero_le_one
            calc ‖resolvent (e n)‖ ≤ ‖resolvent‖ * ‖e n‖ := resolvent.le_opNorm _
              _ ≤ 1 * 1 := mul_le_mul norm_resolvent_le (he n).le (norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1
        _ = 1 := one_mul 1
    have h3 : ‖rieszLift (e n)‖ ^ 2 ≤ 1 := by rw [h]; exact h2
    nlinarith [norm_nonneg (rieszLift (e n))]
  have hpn : ∀ n, ‖compactLift (v n) (hv n) (hvc n)‖ ≤ 2 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc ‖compactLift (v n) (hv n) (hvc n)‖
        = ‖(compactLift (v n) (hv n) (hvc n) - rieszLift (e n)) + rieszLift (e n)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖compactLift (v n) (hv n) (hvc n) - rieszLift (e n)‖ + ‖rieszLift (e n)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add ((hdist n).le.trans h1) (hriesz n)
      _ = 2 := by norm_num
  have hJV : ∀ n, phiDoobArchJumpEnergy (v n) + ∫ x, v n x ^ 2 ∂massMeasure ≤ 4 := by
    intro n
    have hsq := graph_norm_sq (compactLift (v n) (hv n) (hvc n))
    have hfst := norm_compactLift_source_sq (v n) (hv n) (hvc n)
    have hsnd : ‖(compactLift (v n) (hv n) (hvc n)).val.snd‖ ^ 2 =
        phiDoobArchJumpEnergy (v n) + ∑' k, ∫ x, phiDoobPrimeJump (v n) k x := by
      show ‖(compact_memLp_difference (hv n) (hvc n)).toLp _‖ ^ 2 = _
      rw [norm_toLp_sq]
      exact integral_complete_difference_sq (hv n) (hvc n)
    have hprime := tsum_integral_phiDoobPrimeJump_nonneg (v n)
    have hp2 : ‖compactLift (v n) (hv n) (hvc n)‖ ^ 2 ≤ 4 := by
      nlinarith [hpn n, norm_nonneg (compactLift (v n) (hv n) (hvc n))]
    linarith
  have hVn : ∀ n, ∫ x, v n x ^ 2 ∂massMeasure ≤ 4 := fun n => by
    linarith [hJV n, phiDoobArchJumpEnergy_nonneg (v n)]
  -- localization: uniformly bounded Lévy forms
  obtain ⟨C, hC0, hCb⟩ := exists_window_levyForm_bound hR0
  have hlevy : ∀ n, levyForm (windowTest R hR0 (v n)) ≤ 4 * C := fun n => by
    have h1 := hCb (v n) (hv n) (hvc n)
    have h2 := hJV n
    have h3 : 0 ≤ phiDoobArchJumpEnergy (v n) + ∫ x, v n x ^ 2 ∂massMeasure :=
      add_nonneg (phiDoobArchJumpEnergy_nonneg _) (integral_nonneg fun x => sq_nonneg _)
    nlinarith
  -- window constants
  obtain ⟨m', hm'0, hm'⟩ := exists_mass_window_lower (a := R + 3) (by linarith)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-R) R)
    continuous_massDensity.continuousOn
  have hM' : ∀ y, |y| ≤ R → massDensity y ≤ M := fun y hy => by
    have h := hM y (mem_Icc.mpr (abs_le.mp hy))
    rwa [Real.norm_eq_abs, abs_of_pos (massDensity_pos y)] at h
  have hM0 : 0 < M := lt_of_lt_of_le (massDensity_pos 0) (hM' 0 (by rw [abs_zero]; exact hR0))
  -- the window mass of the approximants is controlled by the flat square mass of the windowed test
  have hlow : ∀ n, nearMass R (compactLift (v n) (hv n) (hvc n)) ≤
      M * ∫ x, windowTest R hR0 (v n) x ^ 2 := by
    intro n
    rw [nearMass_compactLift, integral_mass, ← integral_const_mul]
    have hg2 : Integrable fun x => windowTest R hR0 (v n) x ^ 2 :=
      integrable_sq_of_compact (contDiff_windowTest R hR0 (hv n)).continuous
        (hasCompactSupport_windowTest R hR0 (hvc n))
    have hlhs : Integrable fun x => massDensity x * (nearInd R x * v n x ^ 2) := by
      have hbase : Integrable fun x => massDensity x * v n x ^ 2 :=
        (continuous_massDensity.mul ((hv n).continuous.pow 2)).integrable_of_hasCompactSupport
          (hasCompactSupport_sq (hvc n)).mul_left
      exact (integrable_mul_bounded hbase (measurable_nearInd R) (abs_nearInd_le_one R)).congr
        (Eventually.of_forall fun x => by ring)
    refine integral_mono hlhs (hg2.const_mul M) fun x => ?_
    rcases nearInd_zero_or_one R x with h0 | h1
    · rw [h0, zero_mul, mul_zero]
      exact mul_nonneg hM0.le (sq_nonneg _)
    · have hxR : |x| ≤ R := by
        by_contra hc
        simp [nearInd, hc] at h1
      rw [h1, one_mul, windowTest_eq_of_le hR0 (v n) (by linarith)]
      exact mul_le_mul_of_nonneg_right (hM' x hxR) (sq_nonneg _)
  -- window mass is bounded below eventually
  have hmass : ∀ᶠ n in atTop, θ / 4 ≤ nearMass R (compactLift (v n) (hv n) (hvc n)) := by
    have h2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.sqrt θ / 2 :=
      (hinv.eventually_lt_const (by positivity)).mono fun n h => h.le
    filter_upwards [hw.eventually_lt_const hη, h2] with n hn hn2
    have hc := hconf (e n) (he n) hn.le
    have hsq : Real.sqrt θ ≤ ‖nearMul R (resolvent (e n))‖ := by
      calc Real.sqrt θ ≤ Real.sqrt (‖nearMul R (resolvent (e n))‖ ^ 2) := Real.sqrt_le_sqrt hc
        _ = ‖nearMul R (resolvent (e n))‖ := Real.sqrt_sq (norm_nonneg _)
    have hres : resolvent (e n) = (rieszLift (e n)).val.fst := rfl
    have htri : ‖nearMul R (resolvent (e n))‖ ≤
        ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst)‖ + 1 / ((n : ℝ) + 1) := by
      calc ‖nearMul R (resolvent (e n))‖
          = ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst) -
              nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst - resolvent (e n))‖ := by
            rw [map_sub, sub_sub_cancel]
        _ ≤ ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst)‖ +
              ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst - resolvent (e n))‖ :=
            norm_sub_le _ _
        _ ≤ ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst)‖ + 1 / ((n : ℝ) + 1) := by
            refine add_le_add le_rfl ?_
            calc ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst - resolvent (e n))‖
                ≤ ‖(compactLift (v n) (hv n) (hvc n)).val.fst - resolvent (e n)‖ := norm_nearMul_le R _
              _ ≤ ‖compactLift (v n) (hv n) (hvc n) - rieszLift (e n)‖ := by
                  rw [hres]
                  exact norm_sub_fst_le _ _
              _ ≤ 1 / ((n : ℝ) + 1) := (hdist n).le
    have hhalf : Real.sqrt θ / 2 ≤ ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst)‖ := by
      linarith
    rw [nearMass_eq_norm_sq]
    have hsm : sourceMap (compactLift (v n) (hv n) (hvc n)) =
        (compactLift (v n) (hv n) (hvc n)).val.fst := rfl
    rw [hsm]
    calc θ / 4 = (Real.sqrt θ / 2) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hθ.le]
          ring
      _ ≤ ‖nearMul R ((compactLift (v n) (hv n) (hvc n)).val.fst)‖ ^ 2 :=
          pow_le_pow_left₀ (by positivity) hhalf 2
  -- the flat square masses of the windowed tests tend to zero
  have hfour : Tendsto (fun n => ∫ x, windowTest R hR0 (v n) x ^ 2) atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha
      (integral_nonneg fun x => sq_nonneg _), fun ε hε => ?_⟩
    -- choose the frequency cutoff
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
      (tendsto_log_half_sub_atTop.eventually_gt_atTop (max (8 * C / ε) 0))
    set T : ℝ := max T₀ 4 with hT_def
    have hT4 : 4 ≤ T := le_max_right _ _
    have hLT : max (8 * C / ε) 0 < Real.log (T / 2) - levyConst := hT₀ T (le_max_left _ _)
    have hL0 : 0 < Real.log (T / 2) - levyConst := lt_of_le_of_lt (le_max_right _ _) hLT
    have hL8 : 8 * C / ε < Real.log (T / 2) - levyConst := lt_of_le_of_lt (le_max_left _ _) hLT
    set L : ℝ := Real.log (T / 2) - levyConst with hL_def
    -- the tail part
    have htail : ∀ n, (1 / (2 * Real.pi)) * ∫ r in highFreq T, fourierSq (windowTest R hR0 (v n)) r ≤
        4 * C / L := by
      intro n
      have h := fourier_tail_le (contDiff_windowTest R hR0 (hv n))
        (hasCompactSupport_windowTest R hR0 (hvc n)) hT4
      have h2 := hlevy n
      have hpi := Real.pi_pos
      have h3 : L * ∫ r in highFreq T, fourierSq (windowTest R hR0 (v n)) r ≤ 2 * Real.pi * (4 * C) := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        linarith
      rw [le_div_iff₀ hL0]
      have h4 : (1 / (2 * Real.pi)) * (∫ r in highFreq T, fourierSq (windowTest R hR0 (v n)) r) * L =
          (L * ∫ r in highFreq T, fourierSq (windowTest R hR0 (v n)) r) / (2 * Real.pi) := by
        ring
      rw [h4, div_le_iff₀ (by positivity)]
      linarith
    have htail' : 4 * C / L < ε / 2 := by
      rw [div_lt_iff₀ hL0]
      rw [div_lt_iff₀ hε] at hL8
      linarith
    -- the low-frequency part by dominated convergence
    have hlowset : IntegrableOn (fun _ : ℝ => ((R + 2) + 4 / (2 * m')) ^ 2) (highFreq T)ᶜ := by
      refine (continuous_const.integrableOn_Icc (a := -T) (b := T)).mono_set ?_
      intro r hr
      have hr' : ¬ T ≤ |r| := hr
      rw [not_le] at hr'
      exact mem_Icc.mpr (abs_le.mp hr'.le)
    have hlow : Tendsto (fun n => ∫ r in (highFreq T)ᶜ, fourierSq (windowTest R hR0 (v n)) r)
        atTop (𝓝 (∫ _ in (highFreq T)ᶜ, (0 : ℝ))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ((R + 2) + 4 / (2 * m')) ^ 2)
        (fun n => (continuous_fourierSq (contDiff_windowTest R hR0 (hv n)).continuous
          (hasCompactSupport_windowTest R hR0 (hvc n))).aestronglyMeasurable) hlowset
        (fun n => Eventually.of_forall fun r => ?_) (Eventually.of_forall fun r => ?_)
      · rw [Real.norm_eq_abs, abs_of_nonneg (fourierSq_nonneg _ _)]
        refine (fourierSq_windowTest_le hR0 hm'0 hm' (hv n).continuous (hvc n) r).trans ?_
        have h1 := hVn n
        have h2 : (∫ x, v n x ^ 2 ∂massMeasure) / (2 * m') ≤ 4 / (2 * m') :=
          div_le_div_of_nonneg_right h1 (by positivity)
        have h3 : 0 ≤ (R + 2) + (∫ x, v n x ^ 2 ∂massMeasure) / (2 * m') := by
          have hV0 : 0 ≤ ∫ x, v n x ^ 2 ∂massMeasure := integral_nonneg fun x => sq_nonneg _
          positivity
        exact pow_le_pow_left₀ h3 (by linarith) 2
      · exact tendsto_fourierSq_windowTest hweak hv hvc hp hR0 r
    rw [integral_zero] at hlow
    have hlow' : ∀ᶠ n in atTop,
        (1 / (2 * Real.pi)) * ∫ r in (highFreq T)ᶜ, fourierSq (windowTest R hR0 (v n)) r < ε / 2 := by
      have hpi := Real.pi_pos
      have hc : (0 : ℝ) < ε / 2 / (1 / (2 * Real.pi)) := by positivity
      filter_upwards [hlow.eventually_lt_const hc] with n hn
      rw [lt_div_iff₀ (by positivity)] at hn
      linarith
    filter_upwards [hlow'] with n hn
    -- Plancherel and the splitting
    have hpl := integral_fourierSq_eq (contDiff_windowTest R hR0 (hv n))
      (hasCompactSupport_windowTest R hR0 (hvc n))
    have hsplit := integral_add_compl (measurableSet_highFreq T)
      (integrable_fourierSq (contDiff_windowTest R hR0 (hv n)) (hasCompactSupport_windowTest R hR0 (hvc n)))
    have hpi := Real.pi_pos
    have hmain : (∫ x, windowTest R hR0 (v n) x ^ 2) =
        (1 / (2 * Real.pi)) * (∫ r in highFreq T, fourierSq (windowTest R hR0 (v n)) r) +
          (1 / (2 * Real.pi)) * (∫ r in (highFreq T)ᶜ, fourierSq (windowTest R hR0 (v n)) r) := by
      rw [← mul_add, hsplit, hpl]
      field_simp
    rw [hmain]
    linarith [htail n]
  -- contradiction
  have hev : ∀ᶠ n in atTop, (∫ x, windowTest R hR0 (v n) x ^ 2) < θ / (4 * M) :=
    hfour.eventually_lt_const (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (hmass.and hev).exists
  have h5 : M * ∫ x, windowTest R hR0 (v n) x ^ 2 < M * (θ / (4 * M)) :=
    mul_lt_mul_of_pos_left hn2 hM0
  have h6 : M * (θ / (4 * M)) = θ / 4 := by
    field_simp
  linarith [hlow n]

/-- **Weyl values of the arithmetic resolvent lie in `[0, 1/2]`.** No weakly null unit sequence
is an approximate eigenvector family of `R` at a level above the threshold `1/2`. -/
theorem weyl_value_le_half {μ : ℝ} (e : ℕ → MassSpace) (he : ∀ n, ‖e n‖ = 1) (hweak : WeaklyNull e)
    (hw : Tendsto (fun n => ‖resolvent (e n) - μ • e n‖) atTop (𝓝 0)) : μ ≤ 1 / 2 := by
  by_contra h
  rw [not_le] at h
  exact no_weakly_null_weyl_above_half h e he hweak hw

/-- **Eigenspaces above the threshold carry no infinite orthonormal family.** -/
theorem no_orthonormal_eigenfamily_above_half {μ : ℝ} (hμ : 1 / 2 < μ) (e : ℕ → MassSpace)
    (he : Orthonormal ℝ e) (heig : ∀ n, resolvent (e n) = μ • e n) : False := by
  refine no_weakly_null_weyl_above_half hμ e (fun n => he.1 n) (weaklyNull_of_orthonormal he) ?_
  simp [heig]

end RHTower.CHMDPolar
