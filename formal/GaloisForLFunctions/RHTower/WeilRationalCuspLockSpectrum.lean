import GaloisForLFunctions.RHTower.WeilMixedResonanceLockRigidity
import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicResidues

/-!
# The twisted radial limit at every positive real height

Let `G` be a Herglotz producer with lower-line lock `G(1 − s) = V(s) G(s)`, where
`V = Σ_k P(k) k^{−(s−½)} + Σ_j c_j u_j^{−(s−½)}`.  At an integer height `m` Hamburger's reflected radial
limit sees the resonances `n · (frequency) = m`.  This file computes the limit at every real height
`x > 0`, and shows that it is period-one in `x`.

**Theorem** (`tendsto_far_real_height`).  For `x > 0`,

`ε ∫_{t ≤ −1} φ*(t) k(2t, ε + ix) dt → √x Σ_n a(n) n^{−3/2} A_x(n)`,

with `A_x(n) = Σ_{n(k+1) = x} n P(k+1) + Σ_{n u_j = x} n c_j`.

**Theorem** (`tendsto_far_translation`).  The far integrals at heights `x` and `x + 1` have the same
radial behaviour: their difference times `ε` tends to `0`.

**Proof.**  The kernel dilation `k(2t, xτ) = x^{−1/2} x^{2it} k(2t, τ)`
(`quantization_setIntegral_real_scale`) turns height `x` into height `1` with the lock factor
`x^{s−½} V(s)`, whose frequencies are divided by `x`.  The twisted spectral system at height one
(`tendsto_twisted_spectral_v`) and the resonant edge Abel limits (`tendsto_apLock_abel_res`) give
the value.  For the translation, the reflected Laplace transform equals the theta series minus the
polar term (`reflected_laplace_identity`).  The theta series is `i`-periodic, and the upper and
compact pieces vanish at every positive height (`tendsto_quantization_laplace_sub_far_real`).
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral

noncomputable section

/-! ### Dilated exponential sums -/

theorem linTwist_mul_cpow {x ρ : ℝ} (hx : 0 < x) (hρ : 0 < ρ) (s : ℂ) :
    linTwist (-2 * Real.log x) s * (ρ : ℂ) ^ (-(s - 1 / 2)) =
      ((ρ / x : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hq : 0 < ρ / x := div_pos hρ hx
  have hq0 : ((ρ / x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [Complex.cpow_def_of_ne_zero hρ0, Complex.cpow_def_of_ne_zero hq0,
    ← Complex.ofReal_log hρ.le, ← Complex.ofReal_log hq.le, Real.log_div hρ.ne' hx.ne', linTwist,
    ← Complex.exp_add]
  congr 1; push_cast; ring

theorem dirLock_eq_apLock_succ {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {s : ℂ}
    (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    dirLock P s = apLock (fun k => P (k + 1)) (fun k => (k : ℝ) + 1) s := by
  rw [dirLock_of_le P h1, apLock_of_mem _ _ h1 h2, LSeries]
  have hz : 0 ≤ (s - 1 / 2).re := by rw [Complex.sub_re]; norm_num; linarith
  rw [(lseriesSummable_of_nonneg hP hz).tsum_eq_zero_add, LSeries.term_zero, zero_add]
  congr 1; funext k
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), Complex.cpow_neg, div_eq_mul_inv]
  push_cast; ring

theorem linTwist_mul_apLock {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    linTwist (-2 * Real.log x) s * apLock q ρ s = apLock q (fun j => ρ j / x) s := by
  rw [apLock_of_mem q ρ h1 h2, apLock_of_mem _ _ h1 h2, ← tsum_mul_left]
  congr 1; funext j
  rw [← linTwist_mul_cpow hx (hρ j)]; ring

theorem summable_weight_div {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) (x : ℝ) :
    Summable fun j => ‖q j‖ * max 1 (ρ j / x)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hq.mul_left (max 1 x))
  rw [inv_div]
  have hρ' : 0 ≤ (ρ j)⁻¹ := (inv_pos.mpr (hρ j)).le
  have h : max 1 (x / ρ j) ≤ max 1 x * max 1 (ρ j)⁻¹ := by
    have hm1 : 1 ≤ max 1 x := le_max_left _ _
    have hm2 : 1 ≤ max 1 (ρ j)⁻¹ := le_max_left _ _
    apply max_le
    · nlinarith
    · rw [div_eq_mul_inv]
      exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hρ' (by linarith)
  calc ‖q j‖ * max 1 (x / ρ j) ≤ ‖q j‖ * (max 1 x * max 1 (ρ j)⁻¹) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = max 1 x * (‖q j‖ * max 1 (ρ j)⁻¹) := by ring

theorem summable_succ_weight {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) :
    Summable fun k : ℕ => ‖P (k + 1)‖ * max 1 ((k : ℝ) + 1)⁻¹ := by
  have h1 : ∀ k : ℕ, max 1 ((k : ℝ) + 1)⁻¹ = 1 := fun k => by
    apply max_eq_left
    rw [inv_le_one₀ (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  simp only [h1, mul_one]
  exact (summable_nat_add_iff 1).mpr hP

/-- The resonance sum of a dilated lock at height one. -/
def ratSpec (P c : ℕ → ℂ) (u : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  (∑' k : ℕ, if (n : ℝ) * (((k : ℝ) + 1) / x) = ((1 : ℕ) : ℝ) then (n : ℂ) * P (k + 1) else 0) +
    ∑' j, if (n : ℝ) * (u j / x) = ((1 : ℕ) : ℝ) then (n : ℂ) * c j else 0

/-- **The edge Abel spectrum of the dilated lock at height one.** -/
theorem tendsto_dilated_lock_abel {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {c : ℕ → ℂ}
    {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {x : ℝ}
    (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      (linTwist (-2 * Real.log x) (edgePt y) * (dirLock P (edgePt y) + apLock c u (edgePt y))) *
        cexp ((y : ℂ) * (edgeExp ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I)))
      (𝓝[>] 0) (𝓝 (ratSpec P c u x n)) := by
  have hρ1 : ∀ k : ℕ, 0 < ((k : ℝ) + 1) / x := fun k => div_pos (by positivity) hx
  have hρ2 : ∀ j, 0 < u j / x := fun j => div_pos (hu j) hx
  have hw1 := summable_weight_div (fun k => by positivity : ∀ k : ℕ, 0 < (k : ℝ) + 1)
    (summable_succ_weight hP) x
  have hw2 := summable_weight_div hu hc x
  have hedge : ∀ y : ℝ, linTwist (-2 * Real.log x) (edgePt y) *
      (dirLock P (edgePt y) + apLock c u (edgePt y)) =
      apLock (fun k => P (k + 1)) (fun k => ((k : ℝ) + 1) / x) (edgePt y) +
        apLock c (fun j => u j / x) (edgePt y) := by
    intro y
    have h1 : 1 / 2 ≤ (edgePt y).re := by rw [edgePt_re]; norm_num
    have h2 : (edgePt y).re ≤ 3 / 2 := by rw [edgePt_re]
    rw [mul_add, dirLock_eq_apLock_succ hP h1 h2,
      linTwist_mul_apLock (fun k => by positivity : ∀ k : ℕ, 0 < (k : ℝ) + 1) hx h1 h2,
      linTwist_mul_apLock hu hx h1 h2]
  have h1 := tendsto_apLock_abel_res (q := fun k => P (k + 1)) hρ1 hw1 (m := 1) le_rfl hn
  have h2 := tendsto_apLock_abel_res (q := c) hρ2 hw2 (m := 1) le_rfl hn
  unfold ratSpec
  refine (h1.add h2).congr' ?_
  have h1m : (0 : ℝ) < 1 / ((1 : ℕ) : ℝ) := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_re_edgeExp_div (m := 1) le_rfl).eventually (lt_mem_nhds h1m)] with ε hε hr
  have hpos : 0 < (edgeExp ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)).re :=
    (div_pos_iff_of_pos_right (show (0 : ℝ) < ε from hε)).mp hr
  have hw : 0 < (edgeExp ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith
  have hi1 := integrableOn_edge_mul_exp (continuous_apLock hρ1 hw1) (norm_apLock_le hρ1 hw1) hw
  have hi2 := integrableOn_edge_mul_exp (continuous_apLock hρ2 hw2) (norm_apLock_le hρ2 hw2) hw
  simp only [hedge, add_mul]
  rw [integral_add hi1 hi2, mul_add]

/-! ### The reflected transform of a producer -/

/-- The reflected boundary function of a producer is polynomially bounded. -/
theorem exists_poly_bound_phiStar {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ t, ‖phiStar G t‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨CB, N, _, hB⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  refine ⟨2 * CB, N, fun t => ?_⟩
  rw [← phiG_sub_gG]
  calc ‖phiG G t - gG G t‖ ≤ ‖phiG G t‖ + ‖gG G t‖ := norm_sub_le _ _
    _ ≤ CB * (1 + |t|) ^ N + CB * (1 + |t|) ^ N := add_le_add (hB t).1 (hB t).2
    _ = 2 * CB * (1 + |t|) ^ N := by ring

theorem continuous_phiStar {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) :
    Continuous (phiStar G) := by
  have : phiStar G = fun τ => phiG G τ - gG G τ := by funext τ; rw [phiG_sub_gG]
  rw [this]; exact (continuous_phiG hGc).sub (continuous_gG hGc)

/-- **The reflected Laplace transform of a producer** is its theta series minus the polar term. -/
theorem producer_reflected_laplace {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {τ : ℂ} (hτ : 0 < τ.re) :
    defectLaplace (phiStar G) τ =
      thetaLaplace (dirichletExp (lamLog lam)) τ - betaG G / (Real.pi * τ) := by
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable (hLa σ (by simpa using hσ)).1
  obtain ⟨C, hC⟩ := exists_decay_bigEG hsl hΦre hid hGc hGd hG2
  obtain ⟨CB, N, hCB, hB⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hdE := differentiableOn_bigEG hGd
  have hrefl := reflected_laplace_identity (a := a) ha (E := bigEG G) (β := betaG G) (C := C)
    (g := gG G) (Φ := phiG G) (CB := CB) (N := N)
    (fun z hz => by
      rw [mem_verticalStrip] at hz
      exact (continuousAt_bigEG hGc hGd hz.1).continuousWithinAt)
    (hdE.mono fun z hz => by show (1 / 2 : ℝ) < z.re; exact hz.1)
    hC
    (fun s hs => by
      have h1 : 1 < s.re := by rw [hs]; norm_num
      have h0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
      have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [coeffDirichlet_eq_LSeries, (hLa s h1).2, bigEG_eq h0 hs1,
        G_eq_bigG hsl hid hGd hG2 h1]
      unfold bigG
      field_simp
      ring)
    (fun s hs => bigEG_sub_eq_gG hs)
    (fun τ => bigEG_add_eq_phiG τ)
    (continuous_gG hGc).measurable (fun t => (hB t).2)
    (continuous_phiG hGc).measurable (fun t => (hB t).1) hτ
  have i1 := integrable_defectLaplace_integrand (continuous_phiG hGc).aestronglyMeasurable
    (fun t => (hB t).1) hτ
  have i2 := integrable_defectLaplace_integrand (continuous_gG hGc).aestronglyMeasurable
    (fun t => (hB t).2) hτ
  rw [hrefl]
  unfold defectLaplace
  rw [← mul_sub, ← integral_sub i1 i2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [← phiG_sub_gG]
  ring

/-- **Unit translation.**  The lower far integrals of a producer at heights `x` and `x + 1` have the
same radial behaviour. -/
theorem tendsto_far_translation {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      ((∫ t in Iic (-1 : ℝ), phiStar G t * pairKernel (2 * t) ((ε : ℂ) + ((x + 1 : ℝ) : ℂ) * I)) -
        ∫ t in Iic (-1 : ℝ), phiStar G t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, N, hCB⟩ := exists_poly_bound_phiStar hsl hΦre hid hGc hGd hG2
  have hm : AEStronglyMeasurable (phiStar G) volume := (continuous_phiStar hGc).aestronglyMeasurable
  have hA1 := tendsto_quantization_laplace_sub_far_real hm hCB (x := x + 1) (by linarith)
  have hA0 := tendsto_quantization_laplace_sub_far_real hm hCB hx
  set β := betaG G with hβ
  have hcorr : ∀ y : ℝ, 0 < y → Tendsto (fun ε : ℝ => (ε : ℂ) *
      (β / (Real.pi * ((ε : ℂ) + (y : ℂ) * I)))) (𝓝[>] 0) (𝓝 0) := by
    intro y hy
    have hden : (Real.pi : ℂ) * ((0 : ℂ) + (y : ℂ) * I) ≠ 0 := by
      simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr hy.ne']
    have ht := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mul
      ((tendsto_const_nhds (x := β)).div ((tendsto_const_nhds (x := (Real.pi : ℂ))).mul
        ((Complex.continuous_ofReal.tendsto (0 : ℝ)).add_const ((y : ℂ) * I))) hden)
    simpa using ht.mono_left nhdsWithin_le_nhds
  have hP := ((hcorr x hx).sub (hcorr (x + 1) (by linarith))).const_mul (2 * Real.pi : ℂ)
  have h := (hP.sub hA1).add hA0
  simp only [sub_self, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hre0 : 0 < ((ε : ℂ) + (x : ℂ) * I).re := by simpa using hε
  have hre1 : 0 < ((ε : ℂ) + ((x + 1 : ℝ) : ℂ) * I).re := by simpa using hε
  have e0 := producer_reflected_laplace hsl hΦre hid hGc hGd hG2 hre0
  have e1 := producer_reflected_laplace hsl hΦre hid hGc hGd hG2 hre1
  have hp := thetaLaplace_add_nat_mul_I (dirichletExp (lamLog lam)) ((ε : ℂ) + (x : ℂ) * I) 1
  simp only [Nat.cast_one, one_mul] at hp
  have he : (ε : ℂ) + ((x + 1 : ℝ) : ℂ) * I = ((ε : ℂ) + (x : ℂ) * I) + I := by push_cast; ring
  rw [he] at e1 ⊢
  rw [hp] at e1
  rw [e0, e1]
  ring

/-! ### The twisted radial limit at real height -/

theorem phiStar_eq_lock {G V : ℂ → ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ)) {t : ℝ} (ht : t < 0) :
    phiStar G t = V (lineS t) * phiG G t := by
  unfold phiStar phiG
  rw [hlock t ht, mul_div_assoc]

theorem differentiable_linTwist (η : ℝ) : Differentiable ℂ (linTwist η) := by
  unfold linTwist; fun_prop

theorem real_mul_exp_neg_half_log {x : ℝ} (hx : 0 < x) :
    x * Real.exp (-(Real.log x / 2)) = Real.sqrt x := by
  have h1 : x = Real.exp (Real.log x) := (Real.exp_log hx).symm
  calc x * Real.exp (-(Real.log x / 2)) =
        Real.exp (Real.log x) * Real.exp (-(Real.log x / 2)) := by rw [← h1]
    _ = Real.exp (Real.log x * (1 / 2)) := by rw [← Real.exp_add]; congr 1; ring
    _ = Real.sqrt x := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]

/-- **The twisted radial limit at real height `x`.** -/
theorem tendsto_far_real_height {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖) {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = (dirLock P (lineS τ) + apLock c u (lineS τ)) * G (lineS τ))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      ∫ t in Iic (-1 : ℝ), phiStar G t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I)) (𝓝[>] 0)
      (𝓝 (((Real.sqrt x : ℝ) : ℂ) *
        ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n *
          ratSpec P c u x n)) := by
  set V : ℂ → ℂ := fun s => dirLock P s + apLock c u s with hV
  set Vx : ℂ → ℂ := fun s => linTwist (-2 * Real.log x) s * V s with hVx
  have hVcont : Continuous V := (continuous_dirLock hP).add (continuous_apLock hu hc)
  set S : ℝ := (∑' k, ‖P k‖) + ∑' j, ‖c j‖ * max 1 (u j)⁻¹ with hS
  have hVb : ∀ s, ‖V s‖ ≤ S := fun s =>
    (norm_add_le _ _).trans (add_le_add (norm_dirLock_le hP s) (norm_apLock_le hu hc s))
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hVb 0)
  set B : ℝ := Real.exp (|-2 * Real.log x| / 2) * S with hB
  have hB0 : 0 ≤ B := by positivity
  have hVxs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖Vx s‖ ≤ Real.exp (Real.log (B + 1)) := by
    intro s h1 h2
    rw [Real.exp_log (by linarith)]
    calc ‖Vx s‖ = ‖linTwist (-2 * Real.log x) s‖ * ‖V s‖ := norm_mul _ _
      _ ≤ Real.exp (|-2 * Real.log x| / 2) * S :=
          mul_le_mul (norm_linTwist_strip_le _ h1 h2) (hVb s) (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ B + 1 := by rw [hB]; linarith
  have hlineRe : ∀ t : ℝ, (lineS t).re = 1 / 2 := lineS_re
  have hVxc : Continuous Vx := (continuous_linTwist _).mul hVcont
  have hT := tendsto_twisted_spectral_v hsl hΦre hid hGc hGd hG2 (m := 1) le_rfl (V := Vx)
    (fun s _ _ _ => hVxc.continuousAt)
    (fun s h1 h2 _ => ((differentiable_linTwist _) s).mul
      ((differentiableAt_dirLock hP h1).add (differentiableAt_apLock hu hc h1 h2)))
    (fun s h1 h2 _ => hVxs s h1 h2)
    (fun t _ => hVxs _ (le_of_eq (hlineRe t).symm) (by rw [hlineRe]; norm_num))
    (Aspec := ratSpec P c u x) (fun n hn => tendsto_dilated_lock_abel hP hu hc hx hn)
  have hT' := hT.comp (quantization_tendsto_div_nhdsGT hx)
  obtain ⟨CB, N, hCB, hBd⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  set hxf : ℝ → ℂ := fun t => Vx (lineS t) * phiG G t with hxf_def
  have hnearB : ∀ t ∈ Ioo (-1 : ℝ) 0, ‖hxf t‖ ≤ (B + 1) * (CB * 2 ^ N) := by
    intro t ht
    have hVt := hVxs (lineS t) (le_of_eq (hlineRe t).symm) (by rw [hlineRe]; norm_num)
    rw [Real.exp_log (by linarith)] at hVt
    have hpt : ‖phiG G t‖ ≤ CB * 2 ^ N := by
      refine (hBd t).1.trans ?_
      have : (1 + |t|) ≤ 2 := by
        rw [abs_of_neg ht.2]; linarith [ht.1]
      gcongr
    rw [hxf_def, norm_mul]
    exact mul_le_mul hVt hpt (norm_nonneg _) (by linarith)
  have hN := (tendsto_eps_mul_setIntegral_Ioo hnearB (m := 1) le_rfl).comp
    (quantization_tendsto_div_nhdsGT hx)
  have hlim := (hT'.sub hN).const_mul ((x : ℂ) * (Real.exp (-(Real.log x / 2)) : ℂ))
  rw [sub_zero] at hlim
  have hval : (x : ℂ) * (Real.exp (-(Real.log x / 2)) : ℂ) *
      (((Real.sqrt ((1 : ℕ) : ℝ) : ℝ) : ℂ) * ∑' n, LSeries.term (dirichletExp (lamLog lam))
        (((3 / 2 : ℝ) : ℂ)) n * ratSpec P c u x n) =
      ((Real.sqrt x : ℝ) : ℂ) * ∑' n, LSeries.term (dirichletExp (lamLog lam))
        (((3 / 2 : ℝ) : ℂ)) n * ratSpec P c u x n := by
    rw [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_mul]
    congr 1
    rw [← Complex.ofReal_mul, real_mul_exp_neg_half_log hx]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  -- the identity at fixed `ε`
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  set τ' : ℂ := ((ε / x : ℝ) : ℂ) + I with hτ'
  have hτ'0 : τ' ≠ 0 := by
    intro hz; have := congrArg Complex.im hz; simp [hτ'] at this
  have hxτ : (x : ℂ) * τ' = (ε : ℂ) + (x : ℂ) * I := by
    rw [hτ']; push_cast; field_simp
  set g : ℝ → ℂ := fun t => V (lineS t) * phiG G t with hg
  have hgm : AEStronglyMeasurable g volume :=
    ((hVcont.comp (by unfold lineS; fun_prop)).mul (continuous_phiG hGc)).aestronglyMeasurable
  have hgb : ∀ t, ‖g t‖ ≤ (S * CB) * (1 + |t|) ^ N := by
    intro t
    rw [hg, norm_mul, mul_assoc]
    exact mul_le_mul (hVb _) (hBd t).1 (norm_nonneg _) hS0
  have hint := integrable_defectLaplace_integrand hgm hgb
    (τ := (ε : ℂ) + (x : ℂ) * I) (by simpa using hε)
  -- far = whole lower half minus the near part
  have hfar : ∫ t in Iic (-1 : ℝ), phiStar G t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I) =
      (∫ t in Iio (0 : ℝ), g t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I)) -
        ∫ t in Ioo (-1 : ℝ) 0, g t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I) := by
    have hunion : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
      ext t; simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h; by_cases h1 : t ≤ -1
        · exact Or.inl h1
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) := by
      rw [Set.disjoint_left]; intro t h1 h2; exact absurd h2.1 (not_lt.mpr h1)
    rw [hunion, setIntegral_union hdisj measurableSet_Ioo hint.integrableOn hint.integrableOn]
    rw [add_sub_cancel_right]
    refine setIntegral_congr_fun measurableSet_Iic fun t ht => ?_
    have ht0 : t < 0 := by have : t ≤ -1 := ht; linarith
    simp only [hg]
    rw [phiStar_eq_lock (V := fun s => dirLock P s + apLock c u s) hlock ht0]
  -- dilation of both pieces
  have hdil : ∀ s : Set ℝ, ∫ t in s, g t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I) =
      (Real.exp (-(Real.log x / 2)) : ℂ) * ∫ t in s, Vx (lineS t) * phiG G t *
        pairKernel (2 * t) (((ε / x : ℝ) : ℂ) + ((1 : ℕ) : ℂ) * I) := by
    intro s
    rw [← hxτ, quantization_setIntegral_real_scale g s hx hτ'0]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hg, hVx, hτ', Nat.cast_one, one_mul]
    rw [show (((1 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I) = lineS t by rw [lineS_eq]; push_cast; ring]
    ring
  simp only [Function.comp_def, hxf_def]
  rw [hfar, hdil, hdil]
  have hεx : (ε : ℂ) = (x : ℂ) * ((ε / x : ℝ) : ℂ) := by push_cast; field_simp
  rw [hεx]
  have e1 : ∀ t : ℝ, Vx (lineS t) * phiG G t * pairKernel (2 * t)
      (((ε / x : ℝ) : ℂ) + ((1 : ℕ) : ℂ) * I) = Vx (lineS t) * (phiG G t * pairKernel (2 * t)
        (((ε / x : ℝ) : ℂ) + ((1 : ℕ) : ℂ) * I)) := fun t => by ring
  simp only [e1]
  ring

end

end AbelianTwist

end RHTower
