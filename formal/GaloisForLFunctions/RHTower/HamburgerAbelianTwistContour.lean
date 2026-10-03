import GaloisForLFunctions.RHTower.HamburgerRightEdgeKernel
import GaloisForLFunctions.RHTower.WeilFractionalMassSummableRigidity

/-!
# The radial integral of a producer: main term at `n = m` and a decaying error

Let `G` be a Herglotz producer with boundary value `F(½ + 2it) = phiG G t` and Dirichlet
coefficients `a(n)` of `F = exp(Σ lam(n) n^{−s}/log n)`.  Put `τ = ε + i m`, `m ≥ 1`, `0 < ε ≤ 1`,
`f(t) = F(½ + 2it) k(2t, τ)`, and write the `n = m` right-edge density as
`ρ_m(t) = m^{−(3/2 + 2it)} k_τ(3/2 + 2it)`.

**Theorem** (`exists_norm_radialError_le`).  There is `K` with
`‖ε (∫_{t ≤ b} f − a(m) ∫_{t ≤ b} ρ_m)‖ ≤ K ε^{1/2} e^{b·Re τ/‖τ‖}` for all `b ≤ −1` and
`0 < ε ≤ 1`.

**Proof.**
* Cauchy's theorem on `[½, 3/2] × [2a, 2b]` and `a → −∞` give
  `∫_{t ≤ b} f = ½(∫_{y ≤ 2b} F(3/2+iy) k_τ(3/2+iy) dy + i ∫_{½}^{3/2} F(x+2bi) k_τ(x+2bi) dx)`
  (`setIntegral_Iic_radial_eq`).  The bottom edge vanishes in the limit because `k_τ` decays like
  `e^{−δ|y|}` and `F` grows at most like `|y|^{1/2}`.
* On the right edge `F = Σ a(n) n^{−s}` converges absolutely.  The terms with `n ≠ m` are
  off-resonant, since `|log‖τ‖ − log n| ≥ 1/(4m)` (`abs_log_norm_sub_log_ge`), so each is
  `≪ n^{−3/2} m ‖τ‖^{1/2} e^{2bδ}` (`RightEdgeKernel.norm_integral_edge_term_le`).
* The top edge is `≪ ε^{−1/2} e^{bδ}` by the strip bound for `F`.

**Scaling** (`natCast_cpow_mul_offKernel_scale`).  `m^{−s} k_{mτ}(s) = m^{−1} k_τ(s)`.  So the main
term at `(m, ε)` is `a(m)` times the main term at `(1, ε/m)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel

noncomputable section

/-! ### Scaling of the kernel -/

/-- **Scaling.**  For `m ≥ 1`, `m^{−s} k_{mτ}(s) = m^{−1} k_τ(s)`. -/
theorem natCast_cpow_mul_offKernel_scale {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ : τ ≠ 0) (s : ℂ) :
    (m : ℂ) ^ (-s) * offKernel ((m : ℂ) * τ) s = (m : ℂ)⁻¹ * offKernel τ s := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmτ : (m : ℂ) * τ ≠ 0 := mul_ne_zero (by exact_mod_cast hm0) hτ
  have hnorm : ‖(m : ℂ) * τ‖ = m * ‖τ‖ := by
    rw [norm_mul, Complex.norm_natCast]
  have harg : ((Real.pi : ℂ) * ((m : ℂ) * τ) ^ 2).arg = ((Real.pi : ℂ) * τ ^ 2).arg := by
    rw [show (Real.pi : ℂ) * ((m : ℂ) * τ) ^ 2 = (((m : ℝ) ^ 2 : ℝ) : ℂ) * ((Real.pi : ℂ) * τ ^ 2) by
      push_cast; ring]
    exact Complex.arg_real_mul _ (by positivity)
  have hlog : Real.log ‖(m : ℂ) * τ‖ = Real.log m + Real.log ‖τ‖ := by
    rw [hnorm, Real.log_mul hm0 (norm_ne_zero_iff.mpr hτ)]
  have hk : ∀ σ : ℂ, offKernel σ s = σ * ((Real.pi : ℂ) ^ (1 - s / 2) *
      ((Real.pi : ℂ) * σ ^ 2) ^ (s / 2 - 1)) / Complex.sin (Real.pi * s / 2) := by
    intro σ; unfold offKernel; ring
  rw [hk, hk, pi_cpow_mul_cpow_eq hmτ, pi_cpow_mul_cpow_eq hτ, harg, hlog,
    natCast_cpow_eq_exp hm]
  set lm : ℂ := ((Real.log m : ℝ) : ℂ) with hlm
  set E₂ : ℂ := (2 * ((Real.log ‖τ‖ : ℝ) : ℂ) + ((((Real.pi : ℂ) * τ ^ 2).arg : ℝ) : ℂ) * I) *
    (s / 2 - 1) with hE₂
  have hE₁ : (2 * (((Real.log m + Real.log ‖τ‖ : ℝ)) : ℂ) +
      ((((Real.pi : ℂ) * τ ^ 2).arg : ℝ) : ℂ) * I) * (s / 2 - 1) = lm * (s - 2) + E₂ := by
    rw [hE₂, hlm]; push_cast; ring
  rw [hE₁]
  have hminv : (m : ℂ)⁻¹ = cexp (-lm) := by
    rw [hlm, Complex.exp_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hmpos]
  have hmexp : (m : ℂ) = cexp lm := by
    rw [hlm, ← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hmpos]
  have hexp : cexp (lm * -s) * cexp lm * cexp (lm * (s - 2) + E₂) = cexp (-lm) * cexp E₂ := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [hminv]
  conv_lhs => rw [hmexp]
  calc cexp (lm * -s) * (cexp lm * τ * cexp (lm * (s - 2) + E₂) / Complex.sin (Real.pi * s / 2))
      = τ * (cexp (lm * -s) * cexp lm * cexp (lm * (s - 2) + E₂)) /
          Complex.sin (Real.pi * s / 2) := by ring
    _ = τ * (cexp (-lm) * cexp E₂) / Complex.sin (Real.pi * s / 2) := by rw [hexp]
    _ = cexp (-lm) * (τ * cexp E₂ / Complex.sin (Real.pi * s / 2)) := by ring

/-! ### Separation of the resonance -/

/-- For `τ = ε + im` with `0 < ε ≤ 1` and `n ≠ m`, `|log‖τ‖ − log n| ≥ 1/(4m)`. -/
theorem abs_log_norm_sub_log_ge {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≠ m) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 / (4 * m) ≤ |Real.log ‖(ε : ℂ) + (m : ℂ) * I‖ - Real.log n| := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnorm2 : ‖(ε : ℂ) + (m : ℂ) * I‖ ^ 2 = ε ^ 2 + (m : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  set r : ℝ := ‖(ε : ℂ) + (m : ℂ) * I‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrm : (m : ℝ) ≤ r := by
    have h := Complex.abs_im_le_norm ((ε : ℂ) + (m : ℂ) * I)
    have him : ((ε : ℂ) + (m : ℂ) * I).im = m := by simp
    rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; exact h
  have hrpos : 0 < r := by linarith
  have hr2 : r ^ 2 ≤ (m : ℝ) ^ 2 + 1 := by rw [hnorm2]; nlinarith
  -- `log x ≥ 1 − 1/x`
  have hlog_ge : ∀ x : ℝ, 0 < x → 1 - 1 / x ≤ Real.log x := by
    intro x hx
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at h
    rw [one_div]; linarith
  have hm4 : (0 : ℝ) < 4 * m := by positivity
  have hfac : (0 : ℝ) ≤ 1 - 1 / (4 * m) := by
    rw [sub_nonneg, div_le_one hm4]; linarith
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · -- `n < m`
    have hnle : (n : ℝ) ≤ m - 1 := by
      have h : n + 1 ≤ m := hlt
      have h' : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast h
      push_cast at h'; linarith
    have hnpos : (0 : ℝ) < n := by linarith
    have h1 := hlog_ge (r / n) (div_pos hrpos hnpos)
    rw [Real.log_div hrpos.ne' hnpos.ne', one_div_div] at h1
    have h2 : (n : ℝ) / r ≤ 1 - 1 / (4 * m) := by
      rw [div_le_iff₀ hrpos]
      calc (n : ℝ) ≤ m - 1 := hnle
        _ ≤ m * (1 - 1 / (4 * m)) := by
            have e : (m : ℝ) * (1 - 1 / (4 * m)) = m - 1 / 4 := by field_simp
            rw [e]; linarith
        _ ≤ (1 - 1 / (4 * m)) * r := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hrm hfac
    exact le_abs.mpr (Or.inl (by linarith))
  · -- `n > m`
    have hnge : (m : ℝ) + 1 ≤ n := by
      have h : m + 1 ≤ n := hgt
      exact_mod_cast h
    have hnpos : (0 : ℝ) < n := by linarith
    have hsq : (4 * m * r) ^ 2 ≤ (n * (4 * m - 1)) ^ 2 := by
      have h4 : (0 : ℝ) ≤ 4 * m - 1 := by linarith
      have hA : (4 * m * r) ^ 2 ≤ 16 * (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 + 1) := by
        rw [mul_pow, mul_pow]; nlinarith
      have hB : 16 * (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 + 1) ≤ (((m : ℝ) + 1) * (4 * m - 1)) ^ 2 := by
        nlinarith [sq_nonneg ((m : ℝ) - 1), mul_pos (by linarith : (0 : ℝ) < m) (by linarith : (0 : ℝ) < m)]
      have hC : (((m : ℝ) + 1) * (4 * m - 1)) ^ 2 ≤ (n * (4 * m - 1)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_right hnge h4
      linarith
    have hlin : 4 * m * r ≤ n * (4 * m - 1) := by
      have h4 : (0 : ℝ) ≤ 4 * m - 1 := by linarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have h1 := hlog_ge (n / r) (div_pos hnpos hrpos)
    rw [Real.log_div hnpos.ne' hrpos.ne', one_div_div] at h1
    have h2 : r / n ≤ 1 - 1 / (4 * m) := by
      rw [div_le_iff₀ hnpos, sub_mul, one_mul, one_div, inv_mul_eq_div, le_sub_iff_add_le,
        ← le_sub_iff_add_le', div_le_iff₀ hm4]
      nlinarith
    exact le_abs.mpr (Or.inr (by linarith))

/-! ### The contour shift on a finite rectangle -/

/-- The integrand `F(s) k_τ(s)` of the contour shift. -/
def edgeIntegrand (G : ℂ → ℂ) (τ s : ℂ) : ℂ := prodF G s * offKernel τ s

theorem phiG_mul_pairKernel_eq (G : ℂ → ℂ) (τ : ℂ) (t : ℝ) :
    phiG G t * pairKernel (2 * t) τ =
      edgeIntegrand G τ (((1 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) := by
  unfold edgeIntegrand
  rw [phiG_eq_prodF, pairKernel_eq_offKernel, lineS_eq]
  have e : HamburgerStability.linePt (2 * t) = ((1 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    unfold HamburgerStability.linePt; push_cast; ring
  rw [e]; push_cast; ring_nf

theorem continuousOn_edgeIntegrand {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    {τ : ℂ} (hτ0 : τ ≠ 0) {c d : ℝ} (hcd : c ≤ d) (hd : d ≤ -1) :
    ContinuousOn (edgeIntegrand G τ) (Set.uIcc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.uIcc c d) := by
  intro s hs
  rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hcd] at hs
  obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
  have h0 : s ≠ 0 := fun h => by rw [h] at hi2; simp at hi2; linarith
  have h1 : s ≠ 1 := fun h => by rw [h] at hi2; simp at hi2; linarith
  exact ((continuousAt_prodF hGc hr1 h0 h1).mul
    (differentiableAt_offKernel hτ0 (by linarith) (by linarith)).continuousAt).continuousWithinAt

theorem differentiableOn_edgeIntegrand {Φ G : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) {τ : ℂ} (hτ0 : τ ≠ 0) {c d : ℝ}
    (hcd : c ≤ d) (hd : d ≤ -1) :
    DifferentiableOn ℂ (edgeIntegrand G τ) (Set.Ioo (min (1 / 2 : ℝ) (3 / 2)) (max (1 / 2 : ℝ) (3 / 2)) ×ℂ
      Set.Ioo (min c d) (max c d)) := by
  intro s hs
  rw [Complex.mem_reProdIm, min_eq_left (by norm_num), max_eq_right (by norm_num),
    min_eq_left hcd, max_eq_right hcd] at hs
  obtain ⟨⟨hr1, hr2⟩, ⟨_, hi2⟩⟩ := hs
  have h0 : s ≠ 0 := fun h => by rw [h] at hi2; simp at hi2; linarith
  have h1 : s ≠ 1 := fun h => by rw [h] at hi2; simp at hi2; linarith
  exact ((differentiableAt_prodF hGd hr1 h0 h1).mul
    (differentiableAt_offKernel hτ0 (by linarith) (by linarith))).differentiableWithinAt

/-- **Contour shift on a finite rectangle.**  For `a ≤ b ≤ −1`,
`∫_a^b F(½+2it) k(2t,τ) dt = ½(∫_{2a}^{2b} (F k_τ)(3/2+iy) dy − i Bot(2a) + i Top(2b))`, where
`Bot`, `Top` are the horizontal edges at heights `2a`, `2b`. -/
theorem intervalIntegral_radial_eq {Φ G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) {τ : ℂ} (hτ0 : τ ≠ 0) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ -1) :
    ∫ t in a..b, phiG G t * pairKernel (2 * t) τ = (1 / 2 : ℂ) *
      ((∫ y in (2 * a)..(2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I * (∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  set g : ℝ → ℂ := fun y => edgeIntegrand G τ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) with hg
  have hchange : ∫ t in a..b, phiG G t * pairKernel (2 * t) τ =
      (2 : ℝ)⁻¹ • ∫ y in (2 * a)..(2 * b), g y := by
    rw [← intervalIntegral.integral_comp_mul_left g (two_ne_zero' ℝ)]
    exact intervalIntegral.integral_congr fun t _ => phiG_mul_pairKernel_eq G τ t
  have h2ab : 2 * a ≤ 2 * b := by linarith
  have h2b : 2 * b ≤ -1 := by linarith
  set z : ℂ := ((1 / 2 : ℝ) : ℂ) + ((2 * a : ℝ) : ℂ) * I with hz
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + ((2 * b : ℝ) : ℂ) * I with hw
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = 2 * a := by simp [hz]
  have hwre : w.re = 3 / 2 := by simp [hw]
  have hwim : w.im = 2 * b := by simp [hw]
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    (edgeIntegrand G τ) z w
    (by rw [hzre, hwre, hzim, hwim]; exact continuousOn_edgeIntegrand hGc hτ0 h2ab h2b)
    (by rw [hzre, hwre, hzim, hwim]; exact differentiableOn_edgeIntegrand hGd hτ0 h2ab h2b)
  rw [hzre, hwre, hzim, hwim] at hrect
  simp only [smul_eq_mul] at hrect
  rw [hchange, Complex.real_smul]
  have hL : ∫ y in (2 * a)..(2 * b), g y =
      (∫ y in (2 * a)..(2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I * (∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I) := by
    have hI2 : I * I = -1 := Complex.I_mul_I
    linear_combination I * hrect + ((∫ y in (2 * a)..(2 * b), g y) -
      ∫ y in (2 * a)..(2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) * hI2
  rw [hL]
  push_cast
  ring

/-! ### Bounds for the integrand off the critical line -/

/-- On `Re s = 3/2`, `‖F k_τ‖ ≤ e^{S} · 4π^{3/4}‖τ‖ e^{−|y|δ}` for `|y| ≥ 1`. -/
theorem norm_edgeIntegrand_three_halves_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {y : ℝ} (hy : 1 ≤ |y|) :
    ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      Real.exp (∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖) *
        (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
  have hre : 1 < (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re := by simp; norm_num
  unfold edgeIntegrand
  rw [norm_mul, prodF_eq_zetaOf hsl hid hGd hG2 hre]
  have hz := norm_zetaOf_le hsl hre
  have hre' : ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re : ℂ) = ((3 / 2 : ℝ) : ℂ) := by simp
  rw [hre'] at hz
  exact mul_le_mul hz (norm_offKernel_le hτre hτ1 (by norm_num) (by norm_num) hy) (norm_nonneg _)
    (by positivity)

/-- The horizontal edges: `‖∫_{½}^{3/2} (F k_τ)(x + iy) dx‖ ≤ C_F(1+|y|)^{1/2}·4π^{3/4}‖τ‖e^{−|y|δ}`
for `|y| ≥ 2`. -/
theorem norm_horizontalEdge_le {G : ℂ → ℂ} {CF ν : ℝ}
    (hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ ν)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {y : ℝ} (hy : 2 ≤ |y|) :
    ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      CF * (1 + |y|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
        Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
  have hbd : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) (3 / 2), ‖edgeIntegrand G τ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      CF * (1 + |y|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
        Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    unfold edgeIntegrand
    rw [norm_mul]
    have hCF : 0 ≤ CF * (1 + |y|) ^ ν :=
      (norm_nonneg _).trans (hF x y (by linarith [hx.1]) hx.2 hy)
    exact mul_le_mul (hF x y (by linarith [hx.1]) hx.2 hy)
      (norm_offKernel_le hτre hτ1 (by linarith [hx.1]) hx.2 (by linarith)) (norm_nonneg _) hCF
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rwa [show |(3 / 2 : ℝ) - 1 / 2| = 1 by norm_num, mul_one] at h

/-- **The contour shift on a half-line, abstract form.**  Let `G` be continuous on `Re s ≥ ½` with
`G' = ΦG` on `Re s > ½`.  Suppose `|F(x+iy)| ≤ C_F(1+|y|)^{1/2}` on the strip (`F = prodF G`),
`|F k_τ| ≤ M·4π^{3/4}‖τ‖e^{−|y|δ}` on `Re s = 3/2`, and `F(½+2it)k(2t,τ)` is integrable on `t ≤ b`.
Then for `b ≤ −1`,
`∫_{t ≤ b} F(½+2it) k(2t, τ) dt = ½(∫_{y ≤ 2b} (F k_τ)(3/2+iy) dy + i Top(2b))`. -/
theorem setIntegral_Iic_radial_eq_of {Φ G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) {CF M : ℝ} (hCF : 0 ≤ CF)
    (hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ))
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖)
    (hedge : ∀ y : ℝ, 1 ≤ |y| → ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      M * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))))
    {b : ℝ} (hb : b ≤ -1)
    (hfint : IntegrableOn (fun t => phiG G t * pairKernel (2 * t) τ) (Iic b)) :
    ∫ t in Iic b, phiG G t * pairKernel (2 * t) τ = (1 / 2 : ℂ) *
      ((∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  have hpi := Real.pi_pos
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre hτpos
  set K : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ with hK
  have hec : Continuous fun y : ℝ => edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I).re = 3 / 2 := by simp
    have h0 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have h1 : ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; norm_num at this
    refine ContinuousAt.comp (g := edgeIntegrand G τ) ?_ (by fun_prop)
    exact (continuousAt_prodF hGc (by rw [hre]; norm_num) h0 h1).mul
      (differentiableAt_offKernel hτ0 (by rw [hre]; norm_num) (by rw [hre]; norm_num)).continuousAt
  have heint : IntegrableOn (fun y : ℝ => edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      (Iic (2 * b)) := by
    have hdom : IntegrableOn (fun y : ℝ => M * K * ‖cexp ((δ : ℂ) * (y : ℂ))‖)
        (Iic (2 * b)) :=
      ((integrableOn_exp_mul_complex_Iic (a := (δ : ℂ)) (by simpa using hδ0) (2 * b)).norm).const_mul _
    refine hdom.mono' hec.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => ?_))
    have hy0 : y < 0 := by have : y ≤ 2 * b := hy; linarith
    have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; have : y ≤ 2 * b := hy; linarith
    have h := hedge y hy1
    rw [Complex.norm_exp]
    have he : ((δ : ℂ) * (y : ℂ)).re = -(|y| * δ) := by
      rw [abs_of_neg hy0]; simp; ring
    rw [he]
    calc ‖edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
          M * (K * Real.exp (-(|y| * δ))) := h
      _ = M * K * Real.exp (-(|y| * δ)) := by ring
  -- the bottom edge vanishes
  have hbotb : ∀ a : ℝ, a ≤ -1 → ‖∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)‖ ≤ CF * K * (2 / δ ^ 2) / |a| := by
    intro a ha
    have ha0 : 0 < |a| := by rw [abs_of_neg (by linarith)]; linarith
    have hu : 2 ≤ |2 * a| := by rw [abs_mul, abs_two]; rw [abs_of_neg (by linarith : a < 0)]; linarith
    have h := norm_horizontalEdge_le hF hτre hτ1 hu
    set u : ℝ := |2 * a| with hu_def
    have hu1 : (1 + u) ^ (1 / 2 : ℝ) ≤ 1 + u := by
      calc (1 + u) ^ (1 / 2 : ℝ) ≤ (1 + u) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = 1 + u := Real.rpow_one _
    have hexp : Real.exp (-(u * δ)) ≤ 2 / (u * δ) ^ 2 := by
      have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ u * δ by positivity)
      have hpos : 0 < u * δ := by positivity
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div,
        div_le_iff₀ (by norm_num)]
      nlinarith [sq_nonneg (u * δ)]
    have hua : u = 2 * |a| := by rw [hu_def, abs_mul, abs_two]
    calc _ ≤ CF * (1 + u) ^ (1 / 2 : ℝ) * (K * Real.exp (-(u * δ))) := h
      _ ≤ CF * (1 + u) * (K * (2 / (u * δ) ^ 2)) := by
          gcongr
      _ ≤ CF * K * (2 / δ ^ 2) / |a| := by
          rw [hua]
          have hK0 : 0 ≤ K := by positivity
          have e : CF * (1 + 2 * |a|) * (K * (2 / (2 * |a| * δ) ^ 2)) =
              CF * K * (2 / δ ^ 2) * ((1 + 2 * |a|) / (4 * |a| ^ 2)) := by
            field_simp; ring
          rw [e, div_eq_mul_one_div (CF * K * (2 / δ ^ 2))]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) ha0]
          nlinarith
  have hbot : Tendsto (fun a : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand G τ ((x : ℂ) + ((2 * a : ℝ) : ℂ) * I)) atBot (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun a : ℝ => CF * K * (2 / δ ^ 2) / |a|) ?_ ?_
    · filter_upwards [eventually_le_atBot (-1 : ℝ)] with a ha using hbotb a ha
    · have := (tendsto_inv_atTop_zero.comp tendsto_abs_atBot_atTop).const_mul (CF * K * (2 / δ ^ 2))
      rw [mul_zero] at this
      exact this.congr fun a => by simp [div_eq_mul_inv]
  -- pass to the limit
  have h1 : Tendsto (fun a : ℝ => ∫ t in a..b, phiG G t * pairKernel (2 * t) τ) atBot
      (𝓝 (∫ t in Iic b, phiG G t * pairKernel (2 * t) τ)) :=
    intervalIntegral_tendsto_integral_Iic b hfint tendsto_id
  have h2 : Tendsto (fun a : ℝ => ∫ y in (2 * a)..(2 * b),
      edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) atBot
      (𝓝 (∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) :=
    intervalIntegral_tendsto_integral_Iic (2 * b) heint (tendsto_id.const_mul_atBot two_pos)
  set T : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)
    with hT
  have h3 := ((h2.sub (hbot.const_mul I)).add (tendsto_const_nhds (x := I * T))).const_mul
    (1 / 2 : ℂ)
  rw [mul_zero, sub_zero] at h3
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [eventually_le_atBot b] with a ha
  rw [intervalIntegral_radial_eq hGc hGd hτ0 ha hb]

/-- **The contour shift on a half-line.**  For `b ≤ −1`,
`∫_{t ≤ b} F(½+2it) k(2t, τ) dt = ½(∫_{y ≤ 2b} (F k_τ)(3/2+iy) dy + i Top(2b))`. -/
theorem setIntegral_Iic_radial_eq {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {b : ℝ} (hb : b ≤ -1) :
    ∫ t in Iic b, phiG G t * pairKernel (2 * t) τ = (1 / 2 : ℂ) *
      ((∫ y in Iic (2 * b), edgeIntegrand G τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  obtain ⟨CF, hCF, hF⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  exact setIntegral_Iic_radial_eq_of hGc hGd hCF hF hτre hτ1
    (fun y hy => norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre hτ1 hy) hb
    (MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτre).integrableOn

/-! ### The main term and the radial error -/

/-- The `n = m` right-edge density `ρ_m(t) = m^{−(3/2+2it)} k_τ(3/2 + 2it)`. -/
def rhoMain (m : ℕ) (τ : ℂ) (t : ℝ) : ℂ :=
  (m : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)) *
    offKernel τ (((3 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)

/-- Change of variables `y = 2t` on a half-line. -/
theorem setIntegral_Iic_comp_two_mul (g : ℝ → ℂ) (b : ℝ) :
    ∫ t in Iic b, g (2 * t) = (1 / 2 : ℂ) * ∫ y in Iic (2 * b), g y := by
  have h := MeasureTheory.Measure.integral_comp_mul_left ((Iic (2 * b)).indicator g) 2
  have hind : (fun t : ℝ => (Iic (2 * b)).indicator g (2 * t)) = (Iic b).indicator fun t => g (2 * t) := by
    funext t
    by_cases ht : t ≤ b
    · rw [Set.indicator_of_mem (show 2 * t ∈ Iic (2 * b) by simp; linarith),
        Set.indicator_of_mem (show t ∈ Iic b from ht)]
    · rw [Set.indicator_of_notMem (show 2 * t ∉ Iic (2 * b) by simp; push Not at ht; linarith),
        Set.indicator_of_notMem (show t ∉ Iic b from ht)]
  rw [hind, integral_indicator measurableSet_Iic, integral_indicator measurableSet_Iic] at h
  rw [h, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Complex.real_smul]
  push_cast; ring

/-- `ε (1 + 2|b|)^ν e^{2bδ} ≤ ε^{1−ν}(1 + 2M) e^{bδ}` when `0 ≤ ν ≤ 1`, `ε ≤ 1` and `ε ≤ δ M`. -/
theorem mul_rpow_exp_le_rpow {ε δ M b ν : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hεδ : ε ≤ δ * M) (hb : b ≤ 0) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ)) ≤
      ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ) := by
  have hab : |b| = -b := abs_of_nonpos hb
  set x : ℝ := δ * |b| with hx
  have hx0 : 0 ≤ x := by positivity
  have hbase : 1 + 2 * |b| ≤ (1 + 2 * M * x) / ε := by
    rw [le_div_iff₀ hε, hx]
    have : ε * |b| ≤ δ * M * |b| := mul_le_mul_of_nonneg_right hεδ (abs_nonneg b)
    nlinarith [abs_nonneg b]
  have hpow1 : (1 + 2 * |b|) ^ ν ≤ (1 + 2 * M * x) ^ ν / ε ^ ν := by
    rw [← Real.div_rpow (by positivity) hε.le]
    exact Real.rpow_le_rpow (by positivity) hbase hν0
  have hpow2 : (1 + 2 * M * x) ^ ν ≤ 1 + 2 * M * x := by
    calc (1 + 2 * M * x) ^ ν ≤ (1 + 2 * M * x) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) hν1
      _ = 1 + 2 * M * x := Real.rpow_one _
  have hlin : 1 + 2 * M * x ≤ (1 + 2 * M) * Real.exp x := by
    have := Real.add_one_le_exp x
    nlinarith [Real.exp_pos x]
  have hexp2 : Real.exp (2 * b * δ) = Real.exp (b * δ) * Real.exp (-x) := by
    rw [← Real.exp_add, hx, hab]; congr 1; ring
  have hεν : ε * (1 / ε ^ ν) = ε ^ (1 - ν) := by
    rw [Real.rpow_sub hε, Real.rpow_one]; ring
  have hεν0 : 0 < ε ^ ν := Real.rpow_pos_of_pos hε ν
  calc ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ))
      ≤ ε * ((1 + 2 * M * x) ^ ν / ε ^ ν * Real.exp (2 * b * δ)) := by gcongr
    _ ≤ ε * ((1 + 2 * M) * Real.exp x / ε ^ ν * Real.exp (2 * b * δ)) := by
        gcongr; exact hpow2.trans hlin
    _ = ε * (1 / ε ^ ν) * (1 + 2 * M) * (Real.exp x * Real.exp (-x)) * Real.exp (b * δ) := by
        rw [hexp2]; ring
    _ = ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ) := by
        rw [hεν, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring

/-- The point `3/2 + iy` of the right edge. -/
def edgePt (y : ℝ) : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I

theorem edgePt_re (y : ℝ) : (edgePt y).re = 3 / 2 := by simp [edgePt]

/-- The `n`-th right-edge term `∫_{y ≤ B} (a(n) n^{−s}) k_τ(s) dy`, `s = 3/2 + iy`. -/
def edgeTerm (a : ℕ → ℂ) (τ : ℂ) (B : ℝ) (n : ℕ) : ℂ :=
  ∫ y in Iic B, LSeries.term a (edgePt y) n * offKernel τ (edgePt y)

theorem continuous_offKernel_edgePt {τ : ℂ} (hτ0 : τ ≠ 0) :
    Continuous fun y : ℝ => offKernel τ (edgePt y) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (differentiableAt_offKernel hτ0 (by rw [edgePt_re]; norm_num)
    (by rw [edgePt_re]; norm_num)).continuousAt.comp (by unfold edgePt; fun_prop)

theorem continuous_term_edgePt (a : ℕ → ℂ) (n : ℕ) :
    Continuous fun y : ℝ => LSeries.term a (edgePt y) n := by
  by_cases hn : n = 0
  · subst hn; simp only [LSeries.term_zero]; exact continuous_const
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have e : (fun y => LSeries.term a (edgePt y) n) = fun y => a n / (n : ℂ) ^ (edgePt y) := by
      funext y; rw [LSeries.term_of_ne_zero hn]
    rw [e]
    exact continuous_const.div (Continuous.const_cpow (by unfold edgePt; fun_prop) (Or.inl hn'))
      fun y => by simp [hn']

theorem norm_term_edgePt (a : ℕ → ℂ) (n : ℕ) (y : ℝ) :
    ‖LSeries.term a (edgePt y) n‖ = ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, edgePt_re]; simp

/-- The kernel on the right edge is integrable on a half-line `y ≤ B ≤ −1`. -/
theorem integrableOn_offKernel_edgePt {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ}
    (hB : B ≤ -1) : IntegrableOn (fun y : ℝ => offKernel τ (edgePt y)) (Iic B) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  have hδ0 : 0 < δ := div_pos hτre (by linarith)
  have hdom : IntegrableOn (fun y : ℝ => 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * ‖cexp ((δ : ℂ) * (y : ℂ))‖)
      (Iic B) :=
    ((integrableOn_exp_mul_complex_Iic (a := (δ : ℂ)) (by simpa using hδ0) B).norm).const_mul _
  refine hdom.mono' (continuous_offKernel_edgePt hτ0).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun y hy => ?_))
  have hy' : y ≤ B := hy
  have hy0 : y < 0 := by linarith
  have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; linarith
  have h := norm_offKernel_le hτre hτ1 (x := 3 / 2) (y := y) (by norm_num) (by norm_num) hy1
  rw [Complex.norm_exp]
  have he : ((δ : ℂ) * (y : ℂ)).re = -(|y| * δ) := by rw [abs_of_neg hy0]; simp; ring
  rw [he]; exact h

/-- **Dirichlet expansion of the right edge**: `∫_{y≤B} F k_τ = Σ_n edgeTerm n`. -/
theorem hasSum_edgeTerm {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -1) :
    HasSum (edgeTerm (dirichletExp (lamLog lam)) τ B)
      (∫ y in Iic B, edgeIntegrand G τ (edgePt y)) := by
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have h32 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by simp; norm_num
  have hSa : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := (hLa _ h32).1.norm
  have hkint := integrableOn_offKernel_edgePt hτre hτ1 hB
  have hFint : ∀ n, Integrable (fun y => LSeries.term a (edgePt y) n * offKernel τ (edgePt y))
      (volume.restrict (Iic B)) := by
    intro n
    refine (hkint.norm.const_mul ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖).mono'
      ((continuous_term_edgePt a n).mul (continuous_offKernel_edgePt hτ0)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_term_edgePt]
  have hFnorm : ∀ n, ∫ y in Iic B, ‖LSeries.term a (edgePt y) n * offKernel τ (edgePt y)‖ =
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * ∫ y in Iic B, ‖offKernel τ (edgePt y)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1; funext y; rw [norm_mul, norm_term_edgePt]
  have hsum : Summable fun n =>
      ∫ y in Iic B, ‖LSeries.term a (edgePt y) n * offKernel τ (edgePt y)‖ := by
    simp only [hFnorm]; exact hSa.mul_right _
  have hsumm : Summable (edgeTerm a τ B) :=
    Summable.of_norm_bounded hsum fun n => norm_integral_le_integral_norm _
  have hedge : ∀ y, edgeIntegrand G τ (edgePt y) =
      ∑' n, LSeries.term a (edgePt y) n * offKernel τ (edgePt y) := by
    intro y
    have h1 : 1 < (edgePt y).re := by rw [edgePt_re]; norm_num
    unfold edgeIntegrand
    rw [prodF_eq_zetaOf hsl hid hGd hG2 h1, ← (hLa _ h1).2, LSeries, tsum_mul_right]
  have hint : ∫ y in Iic B, edgeIntegrand G τ (edgePt y) = ∑' n, edgeTerm a τ B n := by
    simp only [hedge, edgeTerm]
    exact (integral_tsum_of_summable_integral_norm hFint hsum).symm
  rw [hint]
  exact hsumm.hasSum

/-- **The resonant term**: `edgeTerm m = a(m) · 2 ∫_{t ≤ B/2} ρ_m`. -/
theorem edgeTerm_resonant (a : ℕ → ℂ) {m : ℕ} (hm : 1 ≤ m) (τ : ℂ) (b : ℝ) :
    edgeTerm a τ (2 * b) m = a m * (2 * ∫ t in Iic b, rhoMain m τ t) := by
  have hm0 : m ≠ 0 := by omega
  have e1 : ∀ y, LSeries.term a (edgePt y) m * offKernel τ (edgePt y) =
      a m * ((m : ℂ) ^ (-(edgePt y)) * offKernel τ (edgePt y)) := by
    intro y
    rw [LSeries.term_of_ne_zero hm0, Complex.cpow_neg]
    ring
  simp only [edgeTerm, e1, integral_const_mul]
  congr 1
  have h := setIntegral_Iic_comp_two_mul (fun y => (m : ℂ) ^ (-(edgePt y)) * offKernel τ (edgePt y)) b
  have e2 : (fun t : ℝ => (fun y => (m : ℂ) ^ (-(edgePt y)) * offKernel τ (edgePt y)) (2 * t)) =
      rhoMain m τ := by
    funext t; simp only [edgePt, rhoMain]
  rw [e2] at h
  rw [h]; ring

/-- **The off-resonant terms.**  For `τ = ε + im`, `0 < ε ≤ 1`, `n ≠ m`, `B ≤ −1`:
`‖edgeTerm n‖ ≤ ‖a_n n^{−3/2}‖ · ‖τ‖^{1/2}(8m + 4/π) e^{Bδ}`, `δ = ε/‖τ‖`. -/
theorem norm_edgeTerm_le (a : ℕ → ℂ) {m n : ℕ} (hm : 1 ≤ m) (hnm : n ≠ m) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {B : ℝ} (hB : B ≤ -1) :
    ‖edgeTerm a ((ε : ℂ) + (m : ℂ) * I) B n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
      (‖(ε : ℂ) + (m : ℂ) * I‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) *
        Real.exp (B * (ε / ‖(ε : ℂ) + (m : ℂ) * I‖))) := by
  have hpi := Real.pi_pos
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [hτ]
    rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := ε / ‖τ‖ with hδ
  have hδ' : τ.re / ‖τ‖ = δ := by rw [hτre]
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hτpos]; linarith
  set A : ℝ := ((Real.pi : ℂ) * τ ^ 2).arg with hA
  have hAδ : 2 * δ ≤ Real.pi - A := by
    have h := abs_arg_pi_mul_sq_le hτre0
    rw [hδ'] at h
    have := le_abs_self A
    linarith
  by_cases hn0 : n = 0
  · subst hn0
    have : edgeTerm a τ B 0 = 0 := by simp [edgeTerm, LSeries.term]
    rw [this, norm_zero]; positivity
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have e1 : ∀ y, LSeries.term a (edgePt y) n * offKernel τ (edgePt y) =
      a n * ((n : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) *
        offKernel τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) := by
    intro y
    rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg]
    simp only [edgePt]; ring
  have hsep := abs_log_norm_sub_log_ge hm hn1 hnm hε hε1
  have hne : Real.log ‖τ‖ ≠ Real.log n := by
    intro h; rw [h, sub_self, abs_zero] at hsep
    have : (0 : ℝ) < 1 / (4 * m) := by positivity
    linarith
  have hedgeb := norm_integral_edge_term_le hτre0 hn1 hne hB
  have hterm : ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ = ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [LSeries.norm_term_eq, if_neg hn0, Real.rpow_neg (by positivity), div_eq_mul_inv]
    simp
  simp only [edgeTerm, e1, integral_const_mul]
  rw [norm_mul, hterm, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine hedgeb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hlog : 1 / |Real.log ‖τ‖ - Real.log n| ≤ 4 * m := by
    have hpos : 0 < |Real.log ‖τ‖ - Real.log n| := lt_of_lt_of_le (by positivity) hsep
    rw [div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hsep (show (0 : ℝ) ≤ 4 * m by positivity)
    rw [mul_one_div_cancel (by positivity)] at this
    linarith
  have he1 : Real.exp (B * ((Real.pi - A) / 2)) ≤ Real.exp (B * δ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (Real.pi * B) ≤ Real.exp (B * δ) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  have hτs : 0 ≤ ‖τ‖ ^ (1 / 2 : ℝ) := by positivity
  calc 2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * ((Real.pi - A) / 2)) / |Real.log ‖τ‖ - Real.log n| +
        4 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) / Real.pi
      = 2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * ((Real.pi - A) / 2)) *
          (1 / |Real.log ‖τ‖ - Real.log n|) +
          4 / Real.pi * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (Real.pi * B) := by ring
    _ ≤ 2 * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * δ) * (4 * m) +
          4 / Real.pi * ‖τ‖ ^ (1 / 2 : ℝ) * Real.exp (B * δ) := by gcongr
    _ = ‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (B * δ) := by ring

/-- The radial error `∫_{t ≤ b} f − a(m) ∫_{t ≤ b} ρ_m` as half the off-resonant sum plus the top
edge. -/
theorem radialError_eq {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {b : ℝ} (hb : b ≤ -1) :
    (∫ t in Iic b, phiG G t * pairKernel (2 * t) τ) -
        dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m τ t =
      (1 / 2 : ℂ) * ((∑' n, if n = m then 0 else edgeTerm (dirichletExp (lamLog lam)) τ (2 * b) n) +
        I * ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)) := by
  have hc := setIntegral_Iic_radial_eq hsl hΦre hid hGc hGd hG2 hτre hτ1 hb
  have hs := hasSum_edgeTerm hsl hid hGd hG2 hτre hτ1 (B := 2 * b) (by linarith)
  have hsplit := hs.summable.tsum_eq_add_tsum_ite m
  change _ = (1 / 2 : ℂ) * ((∫ y in Iic (2 * b), edgeIntegrand G τ (edgePt y)) + _) at hc
  rw [← hs.tsum_eq] at hc
  rw [hc, hsplit, edgeTerm_resonant _ hm]
  ring

/-- **The radial error bound from a strip bound.**  If `|F(x+iy)| ≤ C_F(1+|y|)^ν` on
`½ ≤ x ≤ 3/2`, `|y| ≥ 2`, with `0 ≤ ν ≤ 1`, then for `m ≥ 1` there is `K` with
`‖ε(∫_{t≤b} F(½+2it)k(2t,τ) dt − a(m)∫_{t≤b} ρ_m)‖ ≤ K ε^{1−ν} e^{bε/‖τ‖}`, `τ = ε + im`, for all
`0 < ε ≤ 1` and `b ≤ −1`. -/
theorem exists_norm_radialError_le_of_strip {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {ν CF : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hCF : 0 ≤ CF)
    (hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ ν)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ b : ℝ, b ≤ -1 →
      ‖(ε : ℂ) * ((∫ t in Iic b, phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) -
        dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m ((ε : ℂ) + (m : ℂ) * I) t)‖ ≤
      K * ε ^ (1 - ν) * Real.exp (b * (ε / ‖(ε : ℂ) + (m : ℂ) * I‖)) := by
  have hpi := Real.pi_pos
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have h32 : 1 < (((3 / 2 : ℝ) : ℂ)).re := by simp; norm_num
  have hSa_summ : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ := (hLa _ h32).1.norm
  set Sa : ℝ := ∑' n, ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ with hSa
  have hSa0 : 0 ≤ Sa := tsum_nonneg fun n => norm_nonneg _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  set K : ℝ := (1 / 2) * (Sa * M ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) +
    CF * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (1 + 2 * M)) with hK
  refine ⟨K, fun ε hε hε1 b hb => ?_⟩
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [hτ]
    rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hM]; linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  set δ : ℝ := ε / ‖τ‖ with hδ
  have hδ' : τ.re / ‖τ‖ = δ := by rw [hτre]
  have hδ0 : 0 < δ := div_pos hε hτpos
  have hεδ : ε ≤ δ * M := by
    rw [hδ, div_mul_eq_mul_div, le_div_iff₀ hτpos]; nlinarith
  -- off-resonant terms
  have hite : ∀ n, ‖(if n = m then 0 else edgeTerm a τ (2 * b) n)‖ ≤
      ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ *
        (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) := by
    intro n
    split_ifs with hnm
    · rw [norm_zero]; positivity
    · exact norm_edgeTerm_le a hm hnm hε hε1 (B := 2 * b) (by linarith)
  have hite_summ : Summable fun n => ‖(if n = m then 0 else edgeTerm a τ (2 * b) n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hite (hSa_summ.mul_right _)
  have hoff : ‖∑' n, (if n = m then 0 else edgeTerm a τ (2 * b) n)‖ ≤
      Sa * (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) := by
    refine (norm_tsum_le_tsum_norm hite_summ).trans ?_
    rw [hSa, ← tsum_mul_right]
    exact hite_summ.tsum_le_tsum hite (hSa_summ.mul_right _)
  -- the top edge
  have h2b : 2 ≤ |2 * b| := by rw [abs_mul, abs_two, abs_of_neg (by linarith : b < 0)]; linarith
  have htop := norm_horizontalEdge_le hF hτre0 hτ1 h2b
  rw [hδ'] at htop
  have h2babs : |2 * b| = 2 * |b| := by rw [abs_mul, abs_two]
  have hexpb : Real.exp (-(|2 * b| * δ)) = Real.exp (2 * b * δ) := by
    rw [h2babs, abs_of_neg (by linarith : b < 0)]; congr 1; ring
  rw [hexpb, h2babs] at htop
  -- assemble
  rw [radialError_eq hsl hΦre hid hGc hGd hG2 hm hτre0 hτ1 hb]
  set T : ℂ := ∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand G τ ((x : ℂ) + ((2 * b : ℝ) : ℂ) * I)
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  rw [norm_mul, hεn, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  have hsum_le : ‖(∑' n, if n = m then 0 else edgeTerm a τ (2 * b) n) + I * T‖ ≤
      Sa * (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) +
        CF * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
          Real.exp (2 * b * δ)) := by
    refine (norm_add_le _ _).trans (add_le_add hoff ?_)
    rw [norm_mul, Complex.norm_I, one_mul]; exact htop
  have hτs : ‖τ‖ ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hτM (by norm_num)
  have hεs : ε ≤ ε ^ (1 - ν) := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε ^ (1 - ν) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have he2 : Real.exp (2 * b * δ) ≤ Real.exp (b * δ) := Real.exp_le_exp.mpr (by nlinarith)
  have hpart2 := mul_rpow_exp_le_rpow hε hε1 hδ0 hM0 hεδ (by linarith : b ≤ 0) hν0 hν1
  have h1 : ε * Sa * ‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ) ≤
      ε ^ (1 - ν) * Sa * M ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (b * δ) := by
    gcongr
  have h2 : CF * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) *
      (ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ))) ≤
      CF * (4 * Real.pi ^ (3 / 4 : ℝ) * M) * (ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ)) := by
    gcongr
  calc ε * (1 / 2 * ‖(∑' n, if n = m then 0 else edgeTerm a τ (2 * b) n) + I * T‖)
      ≤ ε * (1 / 2 * (Sa * (‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ)) +
          CF * (1 + 2 * |b|) ^ ν * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
            Real.exp (2 * b * δ)))) := by gcongr
    _ = 1 / 2 * (ε * Sa * ‖τ‖ ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) * Real.exp (2 * b * δ) +
          CF * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) *
            (ε * ((1 + 2 * |b|) ^ ν * Real.exp (2 * b * δ)))) := by ring
    _ ≤ 1 / 2 * (ε ^ (1 - ν) * Sa * M ^ (1 / 2 : ℝ) * (8 * m + 4 / Real.pi) *
          Real.exp (b * δ) + CF * (4 * Real.pi ^ (3 / 4 : ℝ) * M) *
            (ε ^ (1 - ν) * (1 + 2 * M) * Real.exp (b * δ))) := by linarith
    _ = K * ε ^ (1 - ν) * Real.exp (b * δ) := by rw [hK]; ring

/-- **The radial error bound.**  For `m ≥ 1` there is `K` with
`‖ε(∫_{t≤b} F(½+2it)k(2t,τ) dt − a(m)∫_{t≤b} ρ_m)‖ ≤ K ε^{1/2} e^{bε/‖τ‖}`, `τ = ε + im`, for all
`0 < ε ≤ 1` and `b ≤ −1`. -/
theorem exists_norm_radialError_le {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ b : ℝ, b ≤ -1 →
      ‖(ε : ℂ) * ((∫ t in Iic b, phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) -
        dirichletExp (lamLog lam) m * ∫ t in Iic b, rhoMain m ((ε : ℂ) + (m : ℂ) * I) t)‖ ≤
      K * ε ^ (1 / 2 : ℝ) * Real.exp (b * (ε / ‖(ε : ℂ) + (m : ℂ) * I‖)) := by
  obtain ⟨CF, hCF, hF⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  obtain ⟨K, hK⟩ := exists_norm_radialError_le_of_strip hsl hΦre hid hGc hGd hG2
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hCF hF hm
  refine ⟨K, fun ε hε hε1 b hb => ?_⟩
  have h := hK ε hε hε1 b hb
  rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h

end

end AbelianTwist

end RHTower
