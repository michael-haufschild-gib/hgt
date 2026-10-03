import GaloisForLFunctions.RHTower.WeilFractionalMassTailRigidity
import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof

/-!
# Fractional spectral masses with a polynomially decaying tail force `Λ` and RH

This sharpens `FractionalMassTailRigidity.fractional_mass_tail_rigidity`, whose tail hypothesis is
`Σ_k c_k u_k^K < ∞` for **every** `K`, to a single power `η > 0`.

**Theorem** (`fractional_mass_polynomial_tail_rigidity`).  Let `Σ |lam(n)| n^{−σ} < ∞` for
`σ > 1`, and on `Re s > 1`

`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{−s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)
  + Σ_k c_k · 2(s−½)/((s−½)² + u_k²)`,

with integer masses `m_j` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`), and real masses `c_k ≥ 0` at
ordinates `u_k ≥ 1`, `u_k → ∞`, with `Σ_k c_k u_k^η < ∞` for one `η > 0`.  Then
`lam(n) = Λ(n)` for `n ≥ 2` and RH holds.

**Proof.**  The boundary value `F(½ + iv) = G/(s(s−1)Γ_ℝ(s))` is `O(|v|^ν)` for every `ν > 0`
(`exists_norm_phiG_le_rpow_small`): `|G|` increases from the critical line to `Re s = ½ + δ`.  There
the producer Lindelöf bound `|F| ≤ (|v| + 3)^ε` applies (corpus `exists_producerZeta_subpolynomial`,
identified with `G/(s(s−1)Γ_ℝ)` by the identity theorem), and `|Γ_ℝ(½ + δ + iv)/Γ_ℝ(½ + iv)| ≪
|v|^{δ/2}` (the vertical Gamma-ratio asymptotic).  With `ν = η/2` the phase defect
`(e^{2πiC(y)} − e^{2πiC_∞})F` is `≪ y^{−η}·y^{η/2} → 0`.  A bounded defect tending to zero is
Abel-sublinear, and the lock-defect rigidity theorem applies.  (`exists_norm_phiG_le_rpow` is the
elementary convexity version, exponent `(σ₁ − ½)/2` for `σ₁ > 1`.)

The atomic door that remains open is that of tails decaying slower than every power, such as the
slowly evaporating profile `r_γ ≍ κ/log γ`.
-/

open Complex Filter Topology Set MeasureTheory Metric

namespace RHTower

namespace FractionalMassPolynomialTailRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity FractionalMassTailRigidity

noncomputable section

/-! ### Abel means of decaying defects -/

/-- **A bounded defect tending to zero at `±∞` is Abel-sublinear.** -/
theorem tendsto_mul_abelMass_of_tendsto_zero {g : ℝ → ℂ} {M : ℝ} (hM : ∀ t, ‖g t‖ ≤ M)
    (hgm : AEStronglyMeasurable g volume)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R ≤ |t| → ‖g t‖ ≤ ε) :
    Tendsto (fun δ => δ * HamburgerStability.abelMass g δ) (𝓝[>] 0) (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨R, hR0, hR⟩ := hlim (ε / 4) (by positivity)
  refine ⟨ε / (4 * (2 * R * M + 1)), by positivity, fun δ hδ hδd => ?_⟩
  have hδ0 : 0 < δ := hδ
  rw [dist_zero_right] at hδd ⊢
  rw [Real.norm_eq_abs, abs_of_pos hδ0] at hδd
  have hpt : ∀ t, ‖g t‖ * Real.exp (-(δ * |t|)) ≤
      M * (Icc (-R) R).indicator (fun _ => (1 : ℝ)) t + ε / 4 * Real.exp (-(δ * |t|)) := by
    intro t
    have he0 : 0 ≤ Real.exp (-(δ * |t|)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(δ * |t|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := abs_nonneg t; nlinarith
    by_cases ht : |t| ≤ R
    · rw [indicator_of_mem (show t ∈ Icc (-R) R from abs_le.mp ht)]
      have : ‖g t‖ * Real.exp (-(δ * |t|)) ≤ M :=
        (mul_le_of_le_one_right (norm_nonneg _) he1).trans (hM t)
      have : 0 ≤ ε / 4 * Real.exp (-(δ * |t|)) := by positivity
      linarith
    · push Not at ht
      rw [indicator_of_notMem (show t ∉ Icc (-R) R from fun h => absurd (abs_le.mpr h)
        (not_le.mpr ht)), mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (hR t ht.le) he0
  have hint1 : Integrable fun t : ℝ => M * (Icc (-R) R).indicator (fun _ => (1 : ℝ)) t :=
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).const_mul M
  have hexp : Integrable fun t : ℝ => Real.exp (-(δ * |t|)) := by
    have := HamburgerStability.integrable_abelMass (g := fun _ : ℝ => (1 : ℂ)) (Cg := 1)
      (N := 0) aestronglyMeasurable_const (fun t => by simp) hδ0
    simpa using this
  have hint : Integrable fun t : ℝ => ‖g t‖ * Real.exp (-(δ * |t|)) :=
    HamburgerStability.integrable_abelMass (Cg := M) (N := 0) hgm (fun t => by simpa using hM t) hδ0
  have hval : ∫ t : ℝ, Real.exp (-(δ * |t|)) = 2 / δ := integral_exp_neg_mul_abs_tail hδ0
  have h1 : HamburgerStability.abelMass g δ ≤ M * (2 * R) + ε / 4 * (2 / δ) := by
    unfold HamburgerStability.abelMass
    calc ∫ t : ℝ, ‖g t‖ * Real.exp (-(δ * |t|))
        ≤ ∫ t : ℝ, (M * (Icc (-R) R).indicator (fun _ => (1 : ℝ)) t +
            ε / 4 * Real.exp (-(δ * |t|))) := integral_mono hint (hint1.add (hexp.const_mul _)) hpt
      _ = M * (2 * R) + ε / 4 * (2 / δ) := by
          rw [integral_add hint1 (hexp.const_mul _), integral_const_mul, integral_const_mul,
            integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
            Real.volume_real_Icc_of_le (by linarith), hval]
          ring
  have h0 : 0 ≤ HamburgerStability.abelMass g δ :=
    integral_nonneg fun t => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ0.le h0)]
  have h2 : δ * HamburgerStability.abelMass g δ ≤ δ * (2 * R * M) + ε / 2 := by
    have := mul_le_mul_of_nonneg_left h1 hδ0.le
    have e : δ * (M * (2 * R) + ε / 4 * (2 / δ)) = δ * (2 * R * M) + ε / 2 := by
      field_simp; ring
    linarith
  have h3 : δ * (2 * R * M) ≤ ε / 4 := by
    have hpos : 0 < 4 * (2 * R * M + 1) := by positivity
    have := (lt_div_iff₀ hpos).mp hδd
    nlinarith [mul_nonneg hR0 hM0]
  linarith

/-! ### Vertical Gamma ratios -/

theorem norm_Gamma_conj_line (a τ : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ = ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
  have h : (a : ℂ) + ((-τ : ℝ) : ℂ) * I = starRingEnd ℂ ((a : ℂ) + (τ : ℂ) * I) := by
    simp
  rw [h, Complex.Gamma_conj, Complex.norm_conj]

/-- **Shifting the abscissa of `Γ` costs at most a power of the height.**  For `a > 0`, `δ ≥ 0`
there is `C` with `|Γ(a + δ + iτ)| ≤ C (1 + |τ|)^δ |Γ(a + iτ)|` for all `τ`. -/
theorem exists_norm_Gamma_shift_le {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      C * (1 + |τ|) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
  have hpos : ∀ b : ℝ, 0 < b → ∀ τ : ℝ, 0 < ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * I)‖ := by
    intro b hb τ
    exact norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb))
  have hlim := gamma_vertical_ratio_norm_rpow_tendsto ha.le hδ
  obtain ⟨τ₀, hτ₀⟩ := (hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists_forall_of_atTop
  set T : ℝ := max τ₀ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  -- the far range
  have hfar : ∀ τ : ℝ, T ≤ τ → ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      2 * τ ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
    intro τ hτ
    have hτ0 : 0 < τ := by linarith
    have h := hτ₀ τ ((le_max_left _ _).trans hτ)
    have p1 := hpos a ha τ
    have p2 := hpos (a + δ) (by linarith) τ
    rw [Real.exp_sub, Real.exp_log p1, Real.exp_log p2] at h
    have hτδ : 0 < τ ^ δ := Real.rpow_pos_of_pos hτ0 δ
    rw [div_mul_eq_mul_div, lt_div_iff₀ p2] at h
    nlinarith
  -- the compact range
  have hcont : ContinuousOn (fun τ : ℝ => ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
      ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖) (Icc (-T) T) := by
    have hG : ∀ b : ℝ, 0 < b → Continuous fun τ : ℝ => Complex.Gamma ((b : ℂ) + (τ : ℂ) * I) := by
      intro b hb
      refine continuous_iff_continuousAt.mpr fun τ => ?_
      have hd : DifferentiableAt ℂ Complex.Gamma ((b : ℂ) + (τ : ℂ) * I) :=
        Complex.differentiableAt_Gamma _ fun m h => by
          have := congrArg Complex.re h
          simp at this
          have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
      have hl : Continuous fun τ : ℝ => (b : ℂ) + (τ : ℂ) * I := by fun_prop
      exact ContinuousAt.comp (g := Complex.Gamma) (f := fun τ : ℝ => (b : ℂ) + (τ : ℂ) * I)
        hd.continuousAt hl.continuousAt
    exact ((hG (a + δ) (by linarith)).norm.div (hG a ha).norm
      fun τ => (hpos a ha τ).ne').continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨by linarith, by linarith⟩)
  refine ⟨max K 2, le_max_of_le_right (by norm_num), fun τ => ?_⟩
  have hone : 1 ≤ (1 + |τ|) ^ δ := Real.one_le_rpow (by linarith [abs_nonneg τ]) hδ
  have hGa := hpos a ha τ
  by_cases hτ : |τ| ≤ T
  · have h := hK τ (abs_le.mp hτ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    rw [div_le_iff₀ hGa] at h
    calc ‖Complex.Gamma (((a + δ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ K * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := h
      _ ≤ max K 2 * (1 + |τ|) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
        have : K ≤ max K 2 * (1 + |τ|) ^ δ :=
          (le_max_left K 2).trans (le_mul_of_one_le_right (by positivity) hone)
        exact mul_le_mul_of_nonneg_right this hGa.le
  · push Not at hτ
    have hmono : |τ| ^ δ ≤ (1 + |τ|) ^ δ :=
      Real.rpow_le_rpow (abs_nonneg τ) (by linarith) hδ
    rcases le_or_gt 0 τ with h0 | h0
    · rw [abs_of_nonneg h0] at hτ hmono
      have h := hfar τ hτ.le
      have hr : 0 ≤ τ ^ δ := Real.rpow_nonneg h0 δ
      calc _ ≤ 2 * τ ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := h
        _ ≤ max K 2 * (1 + |τ|) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
          rw [abs_of_nonneg h0]
          refine mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) hmono hr
            (by positivity)) hGa.le
    · rw [abs_of_neg h0] at hτ hmono
      have h := hfar (-τ) hτ.le
      rw [norm_Gamma_conj_line (a + δ) τ, norm_Gamma_conj_line a τ] at h
      have hGa' := hpos a ha τ
      have hr : 0 ≤ (-τ) ^ δ := Real.rpow_nonneg (by linarith) δ
      calc _ ≤ 2 * (-τ) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := h
        _ ≤ max K 2 * (1 + |τ|) ^ δ * ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * I)‖ := by
          rw [abs_of_neg h0]
          refine mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) hmono hr
            (by positivity)) hGa'.le

/-- **The `Γ_ℝ` ratio between `Re s = σ₁` and the critical line.**  For `σ₁ ≥ ½`,
`|Γ_ℝ(σ₁ + iv)| ≤ C (1 + |v|)^{(σ₁−½)/2} |Γ_ℝ(½ + iv)|`. -/
theorem exists_norm_Gammaℝ_shift_le {σ₁ : ℝ} (hσ₁ : 1 / 2 ≤ σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖Complex.Gammaℝ ((σ₁ : ℂ) + (v : ℂ) * I)‖ ≤
      C * (1 + |v|) ^ ((σ₁ - 1 / 2) / 2) * ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (v : ℂ) * I)‖ := by
  set δ : ℝ := (σ₁ - 1 / 2) / 2 with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  obtain ⟨C, hC, hshift⟩ := exists_norm_Gamma_shift_le (a := 1 / 4) (by norm_num) hδ0
  refine ⟨C, hC, fun v => ?_⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnorm : ∀ σ : ℝ, ‖Complex.Gammaℝ ((σ : ℂ) + (v : ℂ) * I)‖ =
      Real.pi ^ (-(σ / 2)) * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ := by
    intro σ
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 2
    · simp; ring
    · congr 1; push_cast; ring
  have h1 := hnorm σ₁
  have h2 := hnorm (1 / 2)
  push_cast at h2
  rw [h1, show ((1 / 2 : ℂ) + (v : ℂ) * I) = (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I) by push_cast; ring,
    hnorm (1 / 2)]
  have hs := hshift (v / 2)
  have ea : ((1 / 4 + δ : ℝ) : ℂ) = ((σ₁ / 2 : ℝ) : ℂ) := by rw [hδ]; push_cast; ring
  have eb : ((1 / 4 : ℝ) : ℂ) = (((1 / 2 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [ea, eb] at hs
  have habs : (1 + |v / 2|) ^ δ ≤ (1 + |v|) ^ δ := by
    refine Real.rpow_le_rpow (by positivity) ?_ hδ0
    rw [abs_div, abs_two]; linarith [abs_nonneg v]
  have hpow : Real.pi ^ (-(σ₁ / 2)) ≤ Real.pi ^ (-((1 / 2 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have hG0 : 0 ≤ ‖Complex.Gamma ((((1 / 2 : ℝ) / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ :=
    norm_nonneg _
  calc Real.pi ^ (-(σ₁ / 2)) * ‖Complex.Gamma (((σ₁ / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖
      ≤ Real.pi ^ (-((1 / 2 : ℝ) / 2)) *
          (C * (1 + |v|) ^ δ * ‖Complex.Gamma ((((1 / 2 : ℝ) / 2 : ℝ) : ℂ) +
            ((v / 2 : ℝ) : ℂ) * I)‖) := by
        refine mul_le_mul hpow (hs.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hC) hG0
    _ = C * (1 + |v|) ^ δ * (Real.pi ^ (-((1 / 2 : ℝ) / 2)) *
          ‖Complex.Gamma ((((1 / 2 : ℝ) / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖) := by ring

/-- **Horizontal monotonicity** up to an arbitrary abscissa: `|G(σ + iv)| ≤ |G(σ₁ + iv)|` for
`½ ≤ σ ≤ σ₁`. -/
theorem norm_G_le_of_le {Φ G : ℂ → ℂ} (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s)
    {σ σ₁ : ℝ} (v : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ σ₁) : ‖G (σ + v * I)‖ ≤ ‖G (σ₁ + v * I)‖ := by
  set φ : ℝ → ℝ := fun x => ‖G (x + v * I)‖ ^ 2 with hφ
  have hcont : ContinuousOn φ (Set.Icc σ σ₁) := by
    intro x hx
    have hre : 1 / 2 ≤ ((x : ℂ) + v * I).re := by simpa using h1.trans hx.1
    have h := (hGc _ hre).comp (f := fun y : ℝ => (y : ℂ) + v * I) (by fun_prop)
    exact (h.norm.pow 2).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo σ σ₁, HasDerivAt φ
      (2 * inner ℝ (G (x + v * I)) (Φ (x + v * I) * G (x + v * I))) x := by
    intro x hx
    have hre : 1 / 2 < ((x : ℂ) + v * I).re := by simpa using lt_of_le_of_lt h1 hx.1
    have hd2 : HasDerivAt (fun y : ℂ => G (y + v * I)) (Φ (x + v * I) * G (x + v * I)) (x : ℂ) :=
      (hGd _ hre).comp_add_const _ _
    exact hd2.comp_ofReal.norm_sq
  have hnonneg : ∀ x ∈ Set.Ioo σ σ₁,
      0 ≤ 2 * inner ℝ (G (x + v * I)) (Φ (x + v * I) * G (x + v * I)) := by
    intro x hx
    rw [Complex.inner]
    set g := G (x + v * I)
    set φ' := Φ (x + v * I)
    have e : φ' * g * (starRingEnd ℂ) g = ((Complex.normSq g : ℝ) : ℂ) * φ' := by
      rw [mul_assoc, Complex.mul_conj]; ring
    rw [e, Complex.re_ofReal_mul]
    have hre : 1 / 2 < ((x : ℂ) + v * I).re := by simpa using lt_of_le_of_lt h1 hx.1
    exact mul_nonneg (by norm_num) (mul_nonneg (Complex.normSq_nonneg _) (hΦre _ hre))
  have hmono : MonotoneOn φ (Set.Icc σ σ₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      exact hnonneg x hx
  have h := hmono ⟨le_rfl, h2⟩ ⟨h2, le_rfl⟩ h2
  simp only [hφ] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **The tail of the fractional masses**, with a real power. -/
theorem tsum_sub_phaseSum_le_rpow {c u : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hcs : Summable c) {η : ℝ} (hη : 0 ≤ η) (hcη : Summable fun k => c k * u k ^ η) {y : ℝ}
    (hy : 0 < y) :
    0 ≤ (∑' k, c k) - phaseSum c u y ∧
      (∑' k, c k) - phaseSum c u y ≤ (∑' k, c k * u k ^ η) / y ^ η := by
  have hsp : Summable fun k => if u k < y then c k else 0 :=
    hcs.of_nonneg_of_le (fun k => by split_ifs; exacts [hc k, le_rfl])
      fun k => by split_ifs; exacts [le_rfl, hc k]
  have hdiff : (∑' k, c k) - phaseSum c u y = ∑' k, if u k < y then 0 else c k := by
    unfold phaseSum
    rw [← hcs.tsum_sub hsp]
    exact tsum_congr fun k => by split_ifs <;> ring
  have hst : Summable fun k => if u k < y then (0 : ℝ) else c k :=
    hcs.of_nonneg_of_le (fun k => by split_ifs; exacts [le_rfl, hc k])
      fun k => by split_ifs; exacts [hc k, le_rfl]
  rw [hdiff]
  refine ⟨tsum_nonneg fun k => by split_ifs; exacts [le_rfl, hc k], ?_⟩
  rw [← tsum_div_const]
  refine hst.tsum_le_tsum (fun k => ?_) (hcη.div_const _)
  split_ifs with h
  · exact div_nonneg (mul_nonneg (hc k) (Real.rpow_nonneg (by linarith [hu1 k]) _))
      (Real.rpow_nonneg hy.le _)
  · rw [le_div_iff₀ (Real.rpow_pos_of_pos hy _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le (not_lt.mp h) hη) (hc k)

/-- **Convexity bound for the boundary value.**  For `σ₁ > 1`,
`|F(½ + 2iτ)| = |G/(s(s−1)Γ_ℝ(s))| ≤ C (1 + |τ|)^{(σ₁−½)/2}`. -/
theorem exists_norm_phiG_le_rpow {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {σ₁ : ℝ} (hσ₁ : 1 < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖phiG G τ‖ ≤ C * (1 + |τ|) ^ ((σ₁ - 1 / 2) / 2) := by
  set δ : ℝ := (σ₁ - 1 / 2) / 2 with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_Gammaℝ_shift_le (σ₁ := σ₁) (by linarith)
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (σ₁ : ℂ) n‖ with hS
  refine ⟨8 * σ₁ ^ 2 * Real.exp S * CΓ * 2 ^ δ, by positivity, fun τ => ?_⟩
  set v : ℝ := 2 * τ with hv
  set s₀ : ℂ := lineS τ with hs₀
  set s₁ : ℂ := (σ₁ : ℂ) + (v : ℂ) * I with hs₁
  have hs₀e : s₀ = ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I := by rw [hs₀, lineS_eq, hv]; push_cast; ring
  have hs₁re : 1 < s₁.re := by simp [hs₁]; exact hσ₁
  -- monotonicity and the value at `σ₁`
  have hmono : ‖G s₀‖ ≤ ‖G s₁‖ := by
    rw [hs₀e]; exact norm_G_le_of_le hΦre hGc hGd v le_rfl (by linarith)
  have hG1 : G s₁ = bigG lam s₁ := G_eq_bigG hsl hid hGd hG2 hs₁re
  have hsumm : LSeriesSummable (lamLog lam) s₁ := lseriesSummable_of_le (norm_lamLog_le lam) hsl hs₁re
  have hL : ‖LSeries (lamLog lam) s₁‖ ≤ S := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsumm.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp [hs₁]
  have hz : ‖Complex.exp (LSeries (lamLog lam) s₁)‖ ≤ Real.exp S := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)
  -- the polynomial factors
  have hs₀n : 1 / 4 + v ^ 2 ≤ ‖s₀‖ * ‖s₀ - 1‖ := by
    have e1 : ‖s₀‖ ^ 2 = 1 / 4 + v ^ 2 := by
      rw [hs₀e, Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have e2 : ‖s₀ - 1‖ = ‖s₀‖ := by
      rw [hs₀e]
      have : ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I - 1 = -(starRingEnd ℂ (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) := by
        simp [Complex.ext_iff]; norm_num
      rw [this, norm_neg, Complex.norm_conj]
    rw [e2, ← sq, e1]
  have hs₁n : ‖s₁‖ * ‖s₁ - 1‖ ≤ 8 * σ₁ ^ 2 * (1 / 4 + v ^ 2) := by
    have h1 : ‖s₁‖ ≤ σ₁ + |v| := by
      have := norm_add_le (σ₁ : ℂ) ((v : ℂ) * I)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have h2 : ‖s₁ - 1‖ ≤ σ₁ + |v| := by
      have := norm_add_le ((σ₁ - 1 : ℝ) : ℂ) ((v : ℂ) * I)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs] at this
      have e : s₁ - 1 = ((σ₁ - 1 : ℝ) : ℂ) + (v : ℂ) * I := by rw [hs₁]; push_cast; ring
      rw [e]; linarith
    have hv2 : |v| ^ 2 = v ^ 2 := sq_abs v
    calc ‖s₁‖ * ‖s₁ - 1‖ ≤ (σ₁ + |v|) * (σ₁ + |v|) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ 8 * σ₁ ^ 2 * (1 / 4 + v ^ 2) := by
          have hsq : 1 ≤ σ₁ ^ 2 := by nlinarith
          have h3 : 2 * v ^ 2 ≤ 8 * σ₁ ^ 2 * v ^ 2 := by nlinarith [sq_nonneg v]
          nlinarith [sq_nonneg (σ₁ - |v|), abs_nonneg v]
  have hΓ1 := hΓ v
  rw [← hs₁] at hΓ1
  rw [show ((1 / 2 : ℂ) + (v : ℂ) * I) = s₀ by rw [hs₀e]; push_cast; ring] at hΓ1
  have hτv : (1 + |v|) ^ δ ≤ 2 ^ δ * (1 + |τ|) ^ δ := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hδ0
    rw [hv, abs_mul, abs_two]; linarith [abs_nonneg τ]
  -- assemble
  have hΓ0 : 0 < ‖Complex.Gammaℝ s₀‖ := norm_pos_iff.mpr (Gammaℝ_lineS_ne_zero τ)
  have hpoly0 : 0 < ‖s₀‖ * ‖s₀ - 1‖ := by
    have : 0 < 1 / 4 + v ^ 2 := by positivity
    linarith
  unfold phiG
  rw [← hs₀, norm_div, norm_mul, norm_mul, div_le_iff₀ (by positivity)]
  calc ‖G s₀‖ ≤ ‖G s₁‖ := hmono
    _ = ‖s₁‖ * ‖s₁ - 1‖ * ‖Complex.Gammaℝ s₁‖ * ‖Complex.exp (LSeries (lamLog lam) s₁)‖ := by
        rw [hG1]; unfold bigG zetaOf; rw [norm_mul, norm_mul, norm_mul]
    _ ≤ (8 * σ₁ ^ 2 * (‖s₀‖ * ‖s₀ - 1‖)) *
          (CΓ * (2 ^ δ * (1 + |τ|) ^ δ) * ‖Complex.Gammaℝ s₀‖) * Real.exp S := by
        have hA : ‖s₁‖ * ‖s₁ - 1‖ ≤ 8 * σ₁ ^ 2 * (‖s₀‖ * ‖s₀ - 1‖) :=
          hs₁n.trans (mul_le_mul_of_nonneg_left hs₀n (by positivity))
        have hB : ‖Complex.Gammaℝ s₁‖ ≤ CΓ * (2 ^ δ * (1 + |τ|) ^ δ) * ‖Complex.Gammaℝ s₀‖ :=
          hΓ1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτv hCΓ)
            (norm_nonneg _))
        exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity)) hz (norm_nonneg _)
          (by positivity)
    _ = 8 * σ₁ ^ 2 * Real.exp S * CΓ * 2 ^ δ * (1 + |τ|) ^ δ *
          (‖s₀‖ * ‖s₀ - 1‖ * ‖Complex.Gammaℝ s₀‖) := by ring

/-! ### Lindelöf up to the critical line -/

/-- **Lindelöf bound for the boundary value.**  Under the Herglotz hypotheses, for every `ν > 0`
there is `C` with `|F(½ + 2iτ)| ≤ C (1 + |τ|)^ν`.  The proof combines horizontal monotonicity of `|G|`,
the producer Lindelöf bound on `Re s = ½ + δ` (`exists_producerZeta_subpolynomial`, identified with
`G/(s(s−1)Γ_ℝ)` by the identity theorem), and the `Γ_ℝ` ratio `|v|^{δ/2}`. -/
theorem exists_norm_phiG_le_rpow_small {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖phiG G τ‖ ≤ C * (1 + |τ|) ^ ν := by
  set lam₂ : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam₂
  have hTwo : lamTwo lam = fun n => ((lam₂ n : ℝ) : ℂ) := by
    funext n; simp only [lamTwo, hlam₂]; split_ifs <;> simp
  have hsum₂ : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam₂ n| / (n : ℝ) ^ σ := fun σ hσ =>
    (hsl σ hσ).of_nonneg_of_le (fun _ => by positivity) fun n => by
      simp only [hlam₂]
      split_ifs
      · exact le_rfl
      · simp; positivity
  have hHW : HerglotzWeilPositive lam₂ zetaArchimedeanDatum :=
    ⟨hsum₂, ⟨Φ, hΦd, hΦre, fun s hs => by rw [hid s hs, hTwo]⟩⟩
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  set δ : ℝ := min ν (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min hν (by norm_num)
  have hδ1 : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hδν : δ ≤ ν := min_le_left _ _
  have hε : 0 < ν / 2 := by linarith
  obtain ⟨T₀, hT₀⟩ := exists_producerZeta_subpolynomial hHW (by simp [hlam₂]) hK
    (differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith) hAK hδ0 hδ1 hε
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_Gammaℝ_shift_le (σ₁ := 1 / 2 + δ) (by linarith)
  set T₁ : ℝ := max T₀ 2 with hT₁
  -- the far range
  have hfar : ∀ τ : ℝ, T₁ ≤ |2 * τ| →
      ‖phiG G τ‖ ≤ 4 * CΓ * 3 ^ (ν / 2) * (1 + |2 * τ|) ^ (ν / 2 + δ / 2) := by
    intro τ hτ
    set v : ℝ := 2 * τ with hv
    have hv2 : 2 ≤ |v| := (le_max_right _ _).trans hτ
    obtain ⟨g, hgd, hgL, hgb⟩ := hT₀ v ((le_max_left _ _).trans hτ)
    set B : Set ℂ := ball ((3 : ℂ) + v * I) (5 / 2 - δ / 4) with hB
    set s₁ : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + v * I with hs₁
    set s₀ : ℂ := lineS τ with hs₀
    have hs₀e : s₀ = ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I := by rw [hs₀, lineS_eq, hv]; push_cast; ring
    -- `B` lies in `Re s > ½` and avoids `0` and `1`
    have hBre : ∀ s ∈ B, 1 / 2 < s.re := fun s hs => by
      have h := Complex.abs_re_le_norm (s - ((3 : ℂ) + v * I))
      rw [hB, mem_ball, dist_eq_norm] at hs
      simp at h
      have := neg_abs_le (s.re - 3)
      linarith
    have hB1 : ∀ s ∈ B, s ≠ 1 := fun s hs h1 => by
      rw [h1, hB, mem_ball, dist_eq_norm] at hs
      have h := Complex.abs_im_le_norm ((1 : ℂ) - ((3 : ℂ) + v * I))
      have h2 := Complex.abs_re_le_norm ((1 : ℂ) - ((3 : ℂ) + v * I))
      simp at h h2
      have hsq : ‖(1 : ℂ) - (3 + v * I)‖ ^ 2 = 4 + v ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have : (5 / 2 - δ / 4) ^ 2 < 4 + v ^ 2 := by
        have : 4 ≤ v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
        nlinarith
      nlinarith [norm_nonneg ((1 : ℂ) - (3 + v * I))]
    set F₂ : ℂ → ℂ := fun s => G s / (s * (s - 1) * Complex.Gammaℝ s) with hF₂
    have hden : ∀ s ∈ B, s * (s - 1) * Complex.Gammaℝ s ≠ 0 := fun s hs => by
      have hr := hBre s hs
      refine mul_ne_zero (mul_ne_zero (fun h0 => by rw [h0] at hr; simp at hr; linarith)
        (sub_ne_zero.mpr (hB1 s hs))) (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    have hF₂d : DifferentiableOn ℂ F₂ B := fun s hs => by
      have hr := hBre s hs
      have hGa : DifferentiableAt ℂ G s := (hGd s hr).differentiableAt
      have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s := differentiableAt_Gammaℝ (by linarith)
      exact (hGa.div ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hΓd)
        (hden s hs)).differentiableWithinAt
    have hF₁d : DifferentiableOn ℂ (fun s => cexp (g s)) B := fun s hs =>
      ((hgd s hs).differentiableAt (isOpen_ball.mem_nhds hs)).cexp.differentiableWithinAt
    -- identification on `B`
    have hcoef : logZetaCoeff lam₂ = lamLog lam := by
      funext n; simp only [logZetaCoeff, lamLog, hlam₂]; split_ifs <;> simp
    have hc₀ : (3 : ℂ) + v * I ∈ B := mem_ball_self (by linarith)
    have hev : (fun s => cexp (g s)) =ᶠ[𝓝 ((3 : ℂ) + v * I)] F₂ := by
      have hO : IsOpen (B ∩ {s : ℂ | 1 < s.re}) :=
        isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
      have hmem : (3 : ℂ) + v * I ∈ B ∩ {s : ℂ | 1 < s.re} := ⟨hc₀, by simp⟩
      refine Filter.eventuallyEq_of_mem (hO.mem_nhds hmem) fun s hs => ?_
      have hs1 : 1 < s.re := hs.2
      simp only [hF₂]
      rw [hgL s hs.1 hs1, hcoef, G_eq_bigG hsl hid hGd hG2 hs1]
      unfold bigG zetaOf
      exact (mul_div_cancel_left₀ _ (hden s hs.1)).symm
    have hEq := (hF₁d.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      (hF₂d.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected hc₀ hev
    have hs₁B : s₁ ∈ B := by
      rw [hB, mem_ball, dist_eq_norm]
      have e : s₁ - ((3 : ℂ) + v * I) = ((-(5 / 2 - δ) : ℝ) : ℂ) := by
        rw [hs₁]; push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
      linarith
    have hbound : ‖F₂ s₁‖ ≤ (|v| + 3) ^ (ν / 2) := by
      rw [← hEq hs₁B]
      exact (hgb (1 / 2 + δ) le_rfl (by linarith)).2
    -- monotonicity to the line
    have hmono : ‖G s₀‖ ≤ ‖G s₁‖ := by
      rw [hs₀e]; exact norm_G_le_of_le hΦre hGc hGd v le_rfl (by linarith)
    have hΓ1 := hΓ v
    rw [show ((1 / 2 : ℂ) + (v : ℂ) * I) = s₀ by rw [hs₀e]; push_cast; ring] at hΓ1
    have hs₁e : ((1 / 2 + δ : ℝ) : ℂ) + (v : ℂ) * I = s₁ := rfl
    rw [hs₁e] at hΓ1
    -- polynomial factors
    have hs₀n : 1 / 4 + v ^ 2 ≤ ‖s₀‖ * ‖s₀ - 1‖ := by
      have e1 : ‖s₀‖ ^ 2 = 1 / 4 + v ^ 2 := by
        rw [hs₀e, Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have e2 : ‖s₀ - 1‖ = ‖s₀‖ := by
        rw [hs₀e]
        have : ((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I - 1 =
            -(starRingEnd ℂ (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) := by
          simp [Complex.ext_iff]; norm_num
        rw [this, norm_neg, Complex.norm_conj]
      rw [e2, ← sq, e1]
    have hs₁n : ‖s₁‖ * ‖s₁ - 1‖ ≤ 4 * (1 / 4 + v ^ 2) := by
      have h1 : ‖s₁‖ ≤ 1 + |v| := by
        have := norm_add_le ((1 / 2 + δ : ℝ) : ℂ) ((v : ℂ) * I)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
        rw [← hs₁e]; linarith
      have h2 : ‖s₁ - 1‖ ≤ 1 + |v| := by
        have e : s₁ - 1 = ((δ - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I := by rw [hs₁]; push_cast; ring
        have := norm_add_le ((δ - 1 / 2 : ℝ) : ℂ) ((v : ℂ) * I)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
        rw [e]; linarith
      have hv2' : |v| ^ 2 = v ^ 2 := sq_abs v
      calc ‖s₁‖ * ‖s₁ - 1‖ ≤ (1 + |v|) * (1 + |v|) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ 4 * (1 / 4 + v ^ 2) := by nlinarith [abs_nonneg v]
    have hΓ0 : 0 < ‖Complex.Gammaℝ s₀‖ := norm_pos_iff.mpr (Gammaℝ_lineS_ne_zero τ)
    have hp0 : 0 < ‖s₀‖ * ‖s₀ - 1‖ := lt_of_lt_of_le (by positivity) hs₀n
    have hG1 : ‖G s₁‖ = ‖F₂ s₁‖ * (‖s₁‖ * ‖s₁ - 1‖ * ‖Complex.Gammaℝ s₁‖) := by
      have hd := hden s₁ hs₁B
      simp only [hF₂]
      rw [norm_div, norm_mul, norm_mul, div_mul_cancel₀]
      rw [← norm_mul, ← norm_mul]; exact norm_ne_zero_iff.mpr hd
    have h3 : (|v| + 3) ^ (ν / 2) ≤ 3 ^ (ν / 2) * (1 + |v|) ^ (ν / 2) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg v]) (by linarith)
    have h4 : (1 + |v|) ^ (ν / 2) * (1 + |v|) ^ ((1 / 2 + δ - 1 / 2) / 2) =
        (1 + |v|) ^ (ν / 2 + δ / 2) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    unfold phiG
    rw [← hs₀, norm_div, norm_mul, norm_mul, div_le_iff₀ (by positivity)]
    calc ‖G s₀‖ ≤ ‖G s₁‖ := hmono
      _ = ‖F₂ s₁‖ * (‖s₁‖ * ‖s₁ - 1‖ * ‖Complex.Gammaℝ s₁‖) := hG1
      _ ≤ (3 ^ (ν / 2) * (1 + |v|) ^ (ν / 2)) * ((4 * (‖s₀‖ * ‖s₀ - 1‖)) *
            (CΓ * (1 + |v|) ^ ((1 / 2 + δ - 1 / 2) / 2) * ‖Complex.Gammaℝ s₀‖)) := by
          refine mul_le_mul (hbound.trans h3) (mul_le_mul ?_ hΓ1 (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
          exact hs₁n.trans (mul_le_mul_of_nonneg_left hs₀n (by norm_num))
      _ = 4 * CΓ * 3 ^ (ν / 2) * ((1 + |v|) ^ (ν / 2) * (1 + |v|) ^ ((1 / 2 + δ - 1 / 2) / 2)) *
            (‖s₀‖ * ‖s₀ - 1‖ * ‖Complex.Gammaℝ s₀‖) := by ring
      _ = _ := by rw [h4]
  -- the compact range
  have hcont := continuous_phiG hGc
  obtain ⟨Kc, hKc⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-T₁) T₁)
    hcont.continuousOn
  have hKc0 : 0 ≤ Kc := (norm_nonneg _).trans (hKc 0 ⟨by
    have : (2 : ℝ) ≤ T₁ := le_max_right _ _
    linarith, by
    have : (2 : ℝ) ≤ T₁ := le_max_right _ _
    linarith⟩)
  set Cf : ℝ := 4 * CΓ * 3 ^ (ν / 2) * 2 ^ ν with hCf
  refine ⟨max Kc Cf, le_max_of_le_left hKc0, fun τ => ?_⟩
  have hone : 1 ≤ (1 + |τ|) ^ ν := Real.one_le_rpow (by linarith [abs_nonneg τ]) hν.le
  by_cases hτ : T₁ ≤ |2 * τ|
  · refine (hfar τ hτ).trans ?_
    have hexp : ν / 2 + δ / 2 ≤ ν := by linarith
    have h1 : (1 + |2 * τ|) ^ (ν / 2 + δ / 2) ≤ (1 + |2 * τ|) ^ ν :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (2 * τ)]) hexp
    have h2 : (1 + |2 * τ|) ^ ν ≤ 2 ^ ν * (1 + |τ|) ^ ν := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ hν.le
      rw [abs_mul, abs_two]; linarith [abs_nonneg τ]
    calc 4 * CΓ * 3 ^ (ν / 2) * (1 + |2 * τ|) ^ (ν / 2 + δ / 2)
        ≤ 4 * CΓ * 3 ^ (ν / 2) * (2 ^ ν * (1 + |τ|) ^ ν) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = Cf * (1 + |τ|) ^ ν := by rw [hCf]; ring
      _ ≤ max Kc Cf * (1 + |τ|) ^ ν :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · push Not at hτ
    have hτ' : τ ∈ Icc (-T₁) T₁ := by
      rw [abs_mul, abs_two] at hτ
      constructor <;> linarith [abs_le.mp (show |τ| ≤ T₁ by linarith [abs_nonneg τ])]
    calc ‖phiG G τ‖ ≤ Kc := hKc τ hτ'
      _ ≤ max Kc Cf * (1 + |τ|) ^ ν :=
          (le_max_left Kc Cf).trans (le_mul_of_one_le_right (le_max_of_le_left hKc0) hone)

/-! ### The rigidity theorem -/

/-- **Fractional masses with a polynomially decaying tail force `Λ` and RH.**  As
`fractional_mass_tail_rigidity`, with the tail hypothesis weakened from `Σ c_k u_k^K < ∞` for every
`K` to `Σ c_k u_k^η < ∞` for one `η > 0`. -/
theorem fractional_mass_polynomial_tail_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ}
    {c u : ℕ → ℝ} {η : ℝ}
    (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hη : 0 < η) (hcη : Summable fun k => c k * u k ^ η)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hη0 : 0 ≤ η := by linarith
  have hcs : Summable c := hcη.of_nonneg_of_le (fun k => hc k)
    (fun k => le_mul_of_one_le_right (hc k) (Real.one_le_rpow (hu1 k) hη0))
  have hcs2 := summable_div_sq_of_summable hc hu1 hcs
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid'
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  obtain ⟨CB, N, hCB, hB⟩ := exists_poly_bound_lineG hsl hΦre hidT hGc hGd hG2
  set Cinf : ℝ := ∑' k, c k with hCinf
  set κ : ℂ := Complex.exp (-((2 * Real.pi * Cinf : ℝ) : ℂ) * I) with hκ
  have hκ0 : κ ≠ 0 := Complex.exp_ne_zero _
  have hκinv : κ⁻¹ = Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I) := by
    rw [hκ, ← Complex.exp_neg]; congr 1; ring
  set ω : ℝ → ℂ := fun τ => Complex.exp (((2 * Real.pi * phaseSum c u (-(2 * τ)) : ℝ) : ℂ) * I)
    with hω
  set e : ℝ → ℂ := fun τ => if τ < 0 then (ω τ - κ⁻¹) * phiG G τ else 0 with he
  -- the exact lock on the lower half-line
  have hlock : ∀ τ : ℝ, τ < -0 → G (1 - lineS τ) =
      κ⁻¹ * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ := by
    intro τ hτ
    have hτ0 : τ < 0 := by linarith
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hrefl : G (1 - lineS τ) = ω τ * G (lineS τ) := by
      simp only [hGdef, gInf, hω]
      rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
        hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
      ring
    have hD : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ)
    simp only [he, if_pos hτ0]
    unfold phiG
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) with hDdef
    have hcancel : D * ((ω τ - κ⁻¹) * (G (lineS τ) / D)) = (ω τ - κ⁻¹) * G (lineS τ) := by
      field_simp
    rw [hrefl, hcancel]
    ring
  have hgap : ∀ τ, ‖ω τ - κ⁻¹‖ ≤ 2 := by
    intro τ
    rw [hκinv]
    calc ‖ω τ - Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I)‖
        ≤ ‖ω τ‖ + ‖Complex.exp (((2 * Real.pi * Cinf : ℝ) : ℂ) * I)‖ := norm_sub_le _ _
      _ = 2 := by rw [hω]; simp only [Complex.norm_exp_ofReal_mul_I]; norm_num
  have heb : ∀ τ, ‖e τ‖ ≤ (2 * CB) * (1 + |τ|) ^ N := by
    intro τ
    simp only [he]
    split_ifs
    · rw [norm_mul]
      calc ‖ω τ - κ⁻¹‖ * ‖phiG G τ‖ ≤ 2 * (CB * (1 + |τ|) ^ N) :=
            mul_le_mul (hgap τ) (hB τ).1 (norm_nonneg _) (by norm_num)
        _ = 2 * CB * (1 + |τ|) ^ N := by ring
    · rw [norm_zero]; positivity
  have hph : Measurable fun τ : ℝ => phaseSum c u (-(2 * τ)) :=
    ((phaseSum_mono hc hut).comp_antitone (show Antitone fun τ : ℝ => -(2 * τ) from
      fun a b hab => by linarith)).measurable
  have hωm : Measurable ω :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hph)).mul_const I)
  have hem : Measurable e :=
    Measurable.ite measurableSet_Iio ((hωm.sub_const _).mul (continuous_phiG hGc).measurable)
      measurable_const
  -- the Lindelöf bound on the boundary value, with exponent `ν = η/2 < η`
  set ν : ℝ := η / 2 with hν
  have hνη : ν < η := by rw [hν]; linarith
  have hν0 : 0 ≤ ν := by rw [hν]; linarith
  obtain ⟨Cφ, hCφ, hφ⟩ := exists_norm_phiG_le_rpow_small hsl hΦd hΦre hidT hGc hGd hG2
    (by rw [hν]; linarith : 0 < ν)
  set Sη : ℝ := ∑' k, c k * u k ^ η with hSη
  have hSη0 : 0 ≤ Sη := tsum_nonneg fun k =>
    mul_nonneg (hc k) (Real.rpow_nonneg (by linarith [hu1 k]) _)
  set A : ℝ := 4 * Real.pi * Sη * Cφ with hA
  have hA0 : 0 ≤ A := by positivity
  -- decay of the defect
  have hdecay : ∀ τ, 1 ≤ |τ| → ‖e τ‖ ≤ A * (2 * |τ|) ^ (ν - η) := by
    intro τ hτ
    simp only [he]
    split_ifs with hτ0
    · have habs : |τ| = -τ := abs_of_neg hτ0
      set y : ℝ := -(2 * τ) with hy
      have hy0 : 0 < y := by rw [hy]; linarith
      have hy2 : y = 2 * |τ| := by rw [hy, habs]; ring
      obtain ⟨_, hhi⟩ := tsum_sub_phaseSum_le_rpow hc hu1 hcs hη0 hcη hy0
      have hω1 : ‖ω τ - κ⁻¹‖ ≤ 4 * Real.pi * (Sη / y ^ η) := by
        rw [hκinv, hω]
        refine (norm_cexp_mul_I_sub_le _ _).trans ?_
        rw [show 2 * Real.pi * phaseSum c u y - 2 * Real.pi * Cinf =
          -(2 * Real.pi * (Cinf - phaseSum c u y)) by ring, abs_neg,
          abs_of_nonneg (by
            have := (tsum_sub_phaseSum_le_rpow hc hu1 hcs hη0 hcη hy0).1
            positivity)]
        have := mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
        linarith
      have hpoly : ‖phiG G τ‖ ≤ Cφ * y ^ ν := by
        refine (hφ τ).trans (mul_le_mul_of_nonneg_left ?_ hCφ)
        exact Real.rpow_le_rpow (by positivity) (by rw [hy2]; linarith) hν0
      rw [norm_mul]
      have hyη : 0 < y ^ η := Real.rpow_pos_of_pos hy0 η
      calc ‖ω τ - κ⁻¹‖ * ‖phiG G τ‖ ≤ 4 * Real.pi * (Sη / y ^ η) * (Cφ * y ^ ν) :=
            mul_le_mul hω1 hpoly (norm_nonneg _) (by positivity)
        _ = A * y ^ (ν - η) := by
            rw [hA, Real.rpow_sub hy0]
            field_simp
        _ = A * (2 * |τ|) ^ (ν - η) := by rw [hy2]
    · rw [norm_zero]
      exact mul_nonneg hA0 (Real.rpow_nonneg (by positivity) _)
  have hM : ∀ τ, ‖e τ‖ ≤ 2 * CB * 2 ^ N + A := by
    intro τ
    by_cases hτ : 1 ≤ |τ|
    · have h1 := hdecay τ hτ
      have h2 : (2 * |τ|) ^ (ν - η) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      have h3 : 0 ≤ 2 * CB * 2 ^ N := by positivity
      nlinarith
    · push Not at hτ
      have h1 := heb τ
      have h2 : (1 + |τ|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have h3 : 2 * CB * (1 + |τ|) ^ N ≤ 2 * CB * 2 ^ N :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
  have hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ τ, R ≤ |τ| → ‖e τ‖ ≤ ε := by
    intro ε hε
    set β : ℝ := η - ν with hβ
    have hβ0 : 0 < β := by rw [hβ]; linarith
    set R : ℝ := max 1 ((A / ε + 1) ^ (1 / β)) with hR
    refine ⟨R, by positivity, fun τ hτ => ?_⟩
    have hτ1 : 1 ≤ |τ| := (le_max_left _ _).trans hτ
    refine (hdecay τ hτ1).trans ?_
    have hx : (A / ε + 1) ^ (1 / β) ≤ 2 * |τ| :=
      ((le_max_right _ _).trans hτ).trans (by linarith)
    have hxβ : A / ε + 1 ≤ (2 * |τ|) ^ β := by
      have := Real.rpow_le_rpow (by positivity) hx hβ0.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ0.ne', Real.rpow_one] at this
    have hpos : 0 < (2 * |τ|) ^ β := Real.rpow_pos_of_pos (by linarith) _
    have heq : (2 * |τ|) ^ (ν - η) = ((2 * |τ|) ^ β)⁻¹ := by
      rw [hβ, ← Real.rpow_neg (by linarith)]; ring_nf
    rw [heq, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have : A ≤ ε * (A / ε + 1) - ε := by field_simp; linarith
    nlinarith
  have heA := tendsto_mul_abelMass_of_tendsto_zero hM hem.aestronglyMeasurable hlim
  exact phase_lock_rigidity_of_defect hsl hΦd hΦre hid' hGc hGd hG2 hem heb heA le_rfl hκ0 hlock

end

end FractionalMassPolynomialTailRigidity

end RHTower
