import GaloisForLFunctions.RHTower.WeilConeSoundararajanMoments
import GaloisForLFunctions.RHTower.WeilLinearTwistPositivity
import GaloisForLFunctions.RHTower.WeilFractionalMassPolynomialTailRigidity
import GaloisForLFunctions.RHTower.ArchEnvelope

/-!
# Settled locks on the Weil cone

Let `lam` be full-cone Weil-positive with `|lam(n)| ≤ κ log n` and summable rest weight, and let
`G` be a Herglotz producer for `lam`: `G' = Φ_lam G` on `Re s > ½`, continuous to the line, with
`G(2) = 2Γ_ℝ(2) exp(Σ lam(n) n^{−2}/log n)`.  Suppose its critical-line reflection is locked,
`G(1 − s) = w(τ) G(s)` at `s = ½ + 2iτ`, `τ < −Y`, by a bounded measurable factor `w`.

**Theorem** (`settled_lock_rigidity`).  If for some `η > 0`

`∫_T^{2T} |w(−τ) − c₀⁻¹|² dτ = O(T (log T)^{−κ² − η})`,

then `lam = Λ` and the Riemann hypothesis holds.  The uniform version
(`uniformly_settled_lock_rigidity`) needs only `|w(−τ) − c₀⁻¹| = O((log T)^{−κ²/4 − η})`.  It uses
the first moment (`k = ½`) of `G/(s(s−1)Γ_ℝ)` on the line instead of the second.  Both reduce to
`lock_rigidity_of_block_means`.

**Proof.**
* On `Re s > ½`, `G(σ + it) = s(s−1)Γ_ℝ(s) exp(log F_lam(σ + it))`, where `log F_lam` is the
  horizontal logarithm (`G_eq_lineFactor_mul_cexp`).  The modulus `|G|` is nondecreasing in `σ`
  and `|s(s−1)Γ_ℝ(s)|` changes by a bounded factor over `½ ≤ σ ≤ ½ + 1/log T`.  The mean square
  of `exp(2k log F_lam)` at `σ = ½ + 1/log T` (`exists_setIntegral_exp_mul_le`) therefore bounds
  the `2k`-th moment of `G(s)/(s(s−1)Γ_ℝ(s))` on the line by `T (log T)^{k²κ² + o(1)}`
  (`exists_setIntegral_norm_phiG_rpow_le`).
* The lock defect `e = (w − c₀⁻¹) G/(s(s−1)Γ_ℝ)` then has `∫_T^{2T} |e| = o(T)` (weighted
  Cauchy–Schwarz).  Block means of size `o(T)` make `e` Abel-sublinear
  (`setIntegral_Ioi_mul_exp_le_of_blocks`), and `phase_lock_rigidity_of_defect` applies.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz WeilConeMoments IntegerMassRigidity FractionalMassRigidity

/-! ### The archimedean factor -/

/-- The archimedean factor `s(s−1)Γ_ℝ(s)` of a producer. -/
def lineFactor (s : ℂ) : ℂ := s * (s - 1) * Complex.Gammaℝ s

theorem lineFactor_ne_zero {s : ℂ} (hs : 0 < s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    lineFactor s ≠ 0 :=
  mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (Complex.Gammaℝ_ne_zero_of_re_pos hs)

/-- `(s(s−1)Γ_ℝ(s))′ = s(s−1)Γ_ℝ(s) · (Γ̃(s) + 1/(s−1))`. -/
theorem hasDerivAt_lineFactor {s : ℂ} (hs : 0 < s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    HasDerivAt lineFactor (lineFactor s * archU s) s := by
  have hpoly : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have h := hpoly.mul (hasDerivAt_Gammaℝ_of_re_pos hs)
  refine h.congr_deriv ?_
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold lineFactor archU zetaArchimedeanDatum
  field_simp
  ring

theorem lamLog_eq_lamLogC (lam : ℕ → ℝ) : lamLog lam = lamLogC lam := by
  funext n
  unfold lamLog lamLogC lamC
  split_ifs <;> simp

/-! ### Producers are `s(s−1)Γ_ℝ(s) · exp(log F)` -/

theorem weilContinuation_eq_lamTwo {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) : weilContinuation hW s =
      zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := by
  have hfun : lamTwo lam = lamC lam := by
    funext n
    unfold lamTwo lamC
    split_ifs <;> simp
  rw [weilContinuation_eq hW hs, weilFunction, zetaArchimedeanDatum, hfun]

/-- **A producer is the archimedean factor times `exp(log F_lam)`.**  For `σ > ½`, `t ≠ 0`,
`G(σ + it) = (σ + it)(σ + it − 1)Γ_ℝ(σ + it) · exp(log F_lam(σ + it))`. -/
theorem G_eq_lineFactor_mul_cexp {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {σ t : ℝ} (hσ : 1 / 2 < σ) (ht : t ≠ 0) :
    G ((σ : ℂ) + t * I) = lineFactor ((σ : ℂ) + t * I) * cexp (producerLogZeta hW σ t) := by
  have hsl := fun (σ : ℝ) (hσ : 1 < σ) =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have hid := fun (s : ℂ) (hs : 1 < s.re) => weilContinuation_eq_lamTwo hW hs
  set P : ℝ → ℂ := fun u => producerLogZeta hW u t with hP
  set f : ℝ → ℂ := fun v => producerA hW ((v : ℂ) + t * I) with hf
  have hdom : ∀ v : ℝ, 1 / 2 < v → (v : ℂ) + t * I ∈ producerDomain := fun v hv =>
    horizontal_mem_producerDomain hv ht
  have hre : ∀ v : ℝ, ((v : ℂ) + t * I).re = v := fun v => by simp
  have hfc : ContinuousOn f (Ioi (1 / 2)) :=
    (continuousOn_producerA hW).comp (by fun_prop) fun v hv => hdom v hv
  have hPd : ∀ x : ℝ, 1 / 2 < x → HasDerivAt P (-f x) x := by
    intro x hx
    have hII : IntervalIntegrable f volume x 2 := by
      refine (hfc.mono fun v hv => ?_).intervalIntegrable
      rcases Set.mem_uIcc.mp hv with h | h
      · exact lt_of_lt_of_le hx h.1
      · show 1 / 2 < v; linarith [h.1]
    have hsm : StronglyMeasurableAtFilter f (𝓝 x) volume :=
      hfc.stronglyMeasurableAtFilter isOpen_Ioi x hx
    have hca : ContinuousAt f x := hfc.continuousAt (isOpen_Ioi.mem_nhds hx)
    exact (intervalIntegral.integral_hasDerivAt_left hII hsm hca).const_add
      (LSeries (lamLogC lam) ((2 : ℂ) + t * I))
  set q : ℝ → ℂ := fun u => G ((u : ℂ) + t * I) * cexp (-P u) with hq
  set r : ℝ → ℂ := fun u => lineFactor ((u : ℂ) + t * I) with hr
  have hr0 : ∀ x : ℝ, 1 / 2 < x → r x ≠ 0 := fun x hx =>
    lineFactor_ne_zero (by rw [hre]; linarith) (fun h => by
      have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith) (hdom x hx).2
  have hqd : ∀ x : ℝ, 1 / 2 < x → HasDerivAt q (archU ((x : ℂ) + t * I) * q x) x := by
    intro x hx
    have hG : HasDerivAt (fun u : ℝ => G ((u : ℂ) + t * I))
        (weilContinuation hW ((x : ℂ) + t * I) * G ((x : ℂ) + t * I)) x :=
      ((hGd _ (by rw [hre]; exact hx)).comp_add_const (x : ℂ) (t * I)).comp_ofReal
    have hE : HasDerivAt (fun u : ℝ => cexp (-P u)) (cexp (-P x) * (-(-f x))) x :=
      ((hPd x hx).neg).cexp
    refine (hG.mul hE).congr_deriv ?_
    simp only [hq, hf, neg_neg]
    rw [archU_eq hW]
    ring
  have hrd : ∀ x : ℝ, 1 / 2 < x → HasDerivAt r (archU ((x : ℂ) + t * I) * r x) x := by
    intro x hx
    have hm := hdom x hx
    have h := (hasDerivAt_lineFactor (s := (x : ℂ) + t * I) (by rw [hre]; linarith)
      (fun h => by have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith)
      hm.2).comp_add_const (x : ℂ) (t * I) |>.comp_ofReal
    refine h.congr_deriv ?_
    simp only [hr]
    ring
  set g : ℝ → ℂ := fun u => q u / r u with hg
  have hgd : ∀ x : ℝ, 1 / 2 < x → HasDerivAt g 0 x := by
    intro x hx
    refine ((hqd x hx).div (hrd x hx) (hr0 x hx)).congr_deriv ?_
    ring
  have hg2 : g 2 = 1 := by
    have h2 : P 2 = LSeries (lamLog lam) ((2 : ℂ) + t * I) := by
      simp only [hP]
      rw [producerLogZeta_eq_LSeries hW (by norm_num) t, lamLog_eq_lamLogC]
      push_cast
      rfl
    have hG := PhaseLockRigidity.G_eq_bigG hsl hid hGd hG2 (s := (2 : ℂ) + t * I) (by simp)
    simp only [hg, hq, hr]
    push_cast
    rw [hG, h2, bigG, zetaOf, mul_assoc _ (cexp _), ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, mul_one]
    have h0 := hr0 2 (by norm_num)
    simp only [hr] at h0
    push_cast at h0
    exact div_self h0
  have hconst : g σ = g 2 := by
    have hcont : ∀ a b : ℝ, 1 / 2 < a → ContinuousOn g (Icc a b) := fun a b ha =>
      fun x hx => (hgd x (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hder : ∀ a b : ℝ, 1 / 2 < a → ∀ x ∈ Ico a b, HasDerivWithinAt g 0 (Ici x) x :=
      fun a b ha x hx => (hgd x (by linarith [hx.1])).hasDerivWithinAt
    rcases le_or_gt σ 2 with h | h
    · exact (constant_of_has_deriv_right_zero (hcont σ 2 hσ) (hder σ 2 hσ) 2
        ⟨h, le_rfl⟩).symm
    · exact constant_of_has_deriv_right_zero (hcont 2 σ (by norm_num)) (hder 2 σ (by norm_num))
        σ ⟨h.le, le_rfl⟩
  have h1 : q σ = r σ := by
    have h := hconst.trans hg2
    simp only [hg] at h
    exact (div_eq_one_iff_eq (hr0 σ hσ)).mp h
  simp only [hq, hr] at h1
  calc G ((σ : ℂ) + t * I) = G ((σ : ℂ) + t * I) * cexp (-P σ) * cexp (P σ) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = lineFactor ((σ : ℂ) + t * I) * cexp (producerLogZeta hW σ t) := by rw [h1]


/-! ### The archimedean factor across a thin strip -/

/-- **The archimedean factor across a thin strip.**
`|s(s−1)Γ_ℝ(s)| ≤ e^{(σ−½)(log|t|/2 + 3)} |s₀(s₀−1)Γ_ℝ(s₀)|`, `s = σ + it`, `s₀ = ½ + it`, for
`½ ≤ σ ≤ 2`, `|t| ≥ 4`. -/
theorem norm_lineFactor_le {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|) :
    ‖lineFactor ((σ : ℂ) + t * I)‖ ≤ Real.exp ((σ - 1 / 2) * (Real.log |t| / 2 + 3)) *
      ‖lineFactor (((1 / 2 : ℝ) : ℂ) + t * I)‖ := by
  set M : ℝ := Real.log |t| / 2 + 3 with hM
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hre : ∀ u : ℝ, ((u : ℂ) + t * I).re = u := fun u => by simp
  have him : ∀ u : ℝ, ((u : ℂ) + t * I).im = t := fun u => by simp
  have hne0 : ∀ u : ℝ, (u : ℂ) + t * I ≠ 0 := fun u h => by
    have := congrArg Complex.im h; rw [him] at this; exact ht0 (by simpa using this)
  have hne1 : ∀ u : ℝ, (u : ℂ) + t * I ≠ 1 := fun u h => by
    have := congrArg Complex.im h; rw [him] at this; exact ht0 (by simpa using this)
  set D : ℝ → ℂ := fun u => lineFactor ((u : ℂ) + t * I) with hD
  have hDd : ∀ u : ℝ, 0 < u → HasDerivAt D (lineFactor ((u : ℂ) + t * I) *
      archU ((u : ℂ) + t * I)) u := fun u hu =>
    ((hasDerivAt_lineFactor (by rw [hre]; exact hu) (hne0 u) (hne1 u)).comp_add_const (u : ℂ)
      (t * I)).comp_ofReal
  set φ : ℝ → ℝ := fun u => ‖D u‖ ^ 2 * Real.exp (-(2 * M) * u) with hφ
  have hφd : ∀ u : ℝ, 0 < u → HasDerivAt φ
      (2 * inner ℝ (D u) (lineFactor ((u : ℂ) + t * I) * archU ((u : ℂ) + t * I)) *
        Real.exp (-(2 * M) * u) + ‖D u‖ ^ 2 * (Real.exp (-(2 * M) * u) * (-(2 * M) * 1))) u :=
    fun u hu => ((hDd u hu).norm_sq).mul (((hasDerivAt_id u).const_mul (-(2 * M))).exp)
  have hcont : ContinuousOn φ (Icc (1 / 2) σ) := fun u hu =>
    (hφd u (by linarith [hu.1])).continuousAt.continuousWithinAt
  have hanti : AntitoneOn φ (Icc (1 / 2) σ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hφd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hφd x (by linarith [hx.1])).deriv]
      have hin : inner ℝ (D x) (lineFactor ((x : ℂ) + t * I) * archU ((x : ℂ) + t * I)) =
          ‖D x‖ ^ 2 * (archU ((x : ℂ) + t * I)).re := by
        rw [Complex.inner]
        have e : D x * archU ((x : ℂ) + t * I) * (starRingEnd ℂ) (D x) =
            ((Complex.normSq (D x) : ℝ) : ℂ) * archU ((x : ℂ) + t * I) := by
          rw [mul_comm (D x), mul_assoc, Complex.mul_conj, mul_comm]
        simp only [hD] at e ⊢
        rw [e, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
      rw [hin]
      have hL := re_archU_le (u := x) (t := t) (by linarith [hx.1]) (by linarith [hx.2]) ht
      have hE := Real.exp_pos (-(2 * M) * x)
      have hN := sq_nonneg ‖D x‖
      have : ‖D x‖ ^ 2 * (archU ((x : ℂ) + t * I)).re ≤ ‖D x‖ ^ 2 * M :=
        mul_le_mul_of_nonneg_left hL hN
      nlinarith
  have h := hanti ⟨le_rfl, hσ⟩ ⟨hσ, le_rfl⟩ hσ
  simp only [hφ] at h
  have hexp : Real.exp (-(2 * M) * (1 / 2)) = Real.exp (-(2 * M) * σ) *
      Real.exp ((σ - 1 / 2) * M) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [hexp] at h
  have h2 : ‖D σ‖ ^ 2 ≤ (Real.exp ((σ - 1 / 2) * M) * ‖D (1 / 2)‖) ^ 2 := by
    have hpos := Real.exp_pos (-(2 * M) * σ)
    rw [mul_pow]
    nlinarith
  have h3 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  simpa [hD] using h3


/-! ### Block means control Abel means -/

/-- `e^{−δτ} log 2 ≤ ∫_{τ/2}^{τ} e^{−δT} dT/T`. -/
theorem log_two_mul_exp_le_lintegral {δ τ : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ) :
    ENNReal.ofReal (Real.exp (-(δ * τ))) * ENNReal.ofReal (Real.log 2) ≤
      ∫⁻ T in Ico (τ / 2) τ, ENNReal.ofReal (Real.exp (-(δ * T)) / T) := by
  have hτ2 : 0 < τ / 2 := by positivity
  have hcI : IntegrableOn (fun T : ℝ => Real.exp (-(δ * τ)) * T⁻¹) (Ico (τ / 2) τ) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ico_subset_Icc_self
    exact continuousOn_const.mul (continuousOn_inv₀.mono fun T hT =>
      ne_of_gt (lt_of_lt_of_le hτ2 hT.1))
  have hint : ∫ T in Ico (τ / 2) τ, Real.exp (-(δ * τ)) * T⁻¹ =
      Real.exp (-(δ * τ)) * Real.log 2 := by
    rw [integral_const_mul, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), integral_inv_of_pos hτ2 hτ]
    congr 2
    field_simp
  have hnn : 0 ≤ᵐ[volume.restrict (Ico (τ / 2) τ)] fun T : ℝ => Real.exp (-(δ * τ)) * T⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with T hT
    exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (hτ2.trans_le hT.1).le)
  calc ENNReal.ofReal (Real.exp (-(δ * τ))) * ENNReal.ofReal (Real.log 2)
      = ENNReal.ofReal (∫ T in Ico (τ / 2) τ, Real.exp (-(δ * τ)) * T⁻¹) := by
        rw [hint, ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ∫⁻ T in Ico (τ / 2) τ, ENNReal.ofReal (Real.exp (-(δ * τ)) * T⁻¹) :=
        ofReal_integral_eq_lintegral_ofReal hcI hnn
    _ ≤ ∫⁻ T in Ico (τ / 2) τ, ENNReal.ofReal (Real.exp (-(δ * T)) / T) := by
        refine setLIntegral_mono' measurableSet_Ico fun T hT => ENNReal.ofReal_le_ofReal ?_
        have hT0 : 0 < T := hτ2.trans_le hT.1
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (inv_nonneg.mpr hT0.le)
        have := mul_le_mul_of_nonneg_left hT.2.le hδ
        linarith

/-- **Block means control Abel means.**  If `h ≥ 0` is bounded by `M` on `(0, 2T₀]` and
`∫_T^{2T} h ≤ η T` for `T ≥ T₀`, then `∫_0^∞ h(τ) e^{−δτ} dτ ≤ (M T₀ + η/δ)/log 2`. -/
theorem lintegral_Ioi_mul_exp_le_of_blocks {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ τ, 0 ≤ h τ)
    {δ M η T₀ : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hη : 0 ≤ η) (hT₀ : 0 ≤ T₀)
    (hsmall : ∀ τ ∈ Ioc 0 (2 * T₀), h τ ≤ M)
    (hblock : ∀ T, T₀ ≤ T →
      ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ) ≤ ENNReal.ofReal (η * T)) :
    ∫⁻ τ in Ioi 0, ENNReal.ofReal (h τ * Real.exp (-(δ * τ))) ≤
      ENNReal.ofReal ((M * T₀ + η / δ) / Real.log 2) := by
  set g : ℝ → ENNReal := fun T => ENNReal.ofReal (Real.exp (-(δ * T)) / T) with hg
  have hgm : Measurable g :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul measurable_id).neg).div measurable_id)
  have hhm : Measurable fun τ => ENNReal.ofReal (h τ) := ENNReal.measurable_ofReal.comp hm
  set S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 / 2 ≤ p.2 ∧ p.2 < p.1} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le (measurable_fst.div_const 2) measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst))
  set F : ℝ → ℝ → ENNReal := fun τ T =>
    S.indicator (fun p => ENNReal.ofReal (h p.1) * g p.2) (τ, T) with hF
  have hFm : Measurable (Function.uncurry F) :=
    ((hhm.comp measurable_fst).mul (hgm.comp measurable_snd)).indicator hSm
  have hτslice : ∀ τ, ∫⁻ T, F τ T =
      (Ioi 0).indicator (fun τ => ENNReal.ofReal (h τ) * ∫⁻ T in Ico (τ / 2) τ, g T) τ := by
    intro τ
    by_cases hτ : 0 < τ
    · rw [indicator_of_mem (show τ ∈ Ioi 0 from hτ)]
      have e : ∀ T, F τ T = ENNReal.ofReal (h τ) * (Ico (τ / 2) τ).indicator g T := by
        intro T
        simp only [hF, Set.indicator_apply, hS, mem_setOf_eq, mem_Ico]
        by_cases h1 : τ / 2 ≤ T ∧ T < τ
        · rw [if_pos ⟨hτ, h1⟩, if_pos h1]
        · rw [if_neg (fun h2 => h1 h2.2), if_neg h1, mul_zero]
      simp_rw [e]
      rw [lintegral_const_mul _ (hgm.indicator measurableSet_Ico),
        lintegral_indicator measurableSet_Ico]
    · rw [indicator_of_notMem (show τ ∉ Ioi 0 from hτ)]
      have e : ∀ T, F τ T = 0 := fun T => by
        simp only [hF, Set.indicator_apply, hS, mem_setOf_eq]
        rw [if_neg (fun h2 => hτ h2.1)]
      simp [e]
  have hTslice : ∀ T, ∫⁻ τ, F τ T = g T * ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ) := by
    intro T
    by_cases hT : 0 < T
    · have e : ∀ τ, F τ T = g T * (Ioc T (2 * T)).indicator (fun τ => ENNReal.ofReal (h τ)) τ := by
        intro τ
        simp only [hF, Set.indicator_apply, hS, mem_setOf_eq, mem_Ioc]
        by_cases h1 : 0 < τ ∧ τ / 2 ≤ T ∧ T < τ
        · rw [if_pos h1, if_pos ⟨h1.2.2, by linarith [h1.2.1]⟩, mul_comm]
        · rw [if_neg h1, if_neg, mul_zero]
          rintro ⟨a, b⟩
          exact h1 ⟨by linarith, by linarith, a⟩
      simp_rw [e]
      rw [lintegral_const_mul _ (hhm.indicator measurableSet_Ioc),
        lintegral_indicator measurableSet_Ioc]
    · have hg0 : g T = 0 := by
        simp only [hg]
        rw [ENNReal.ofReal_eq_zero]
        exact div_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (not_lt.mp hT)
      have e : ∀ τ, F τ T = 0 := fun τ => by
        simp only [hF, Set.indicator_apply, hS, mem_setOf_eq]
        rw [if_neg]
        rintro ⟨a, b, c⟩
        exact hT (by linarith)
      simp [e, hg0]
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    hFm.aemeasurable
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the left side
  have hL : (∫⁻ τ in Ioi 0, ENNReal.ofReal (h τ * Real.exp (-(δ * τ)))) *
      ENNReal.ofReal (Real.log 2) ≤ ∫⁻ τ, ∫⁻ T, F τ T := by
    simp_rw [hτslice]
    rw [lintegral_indicator measurableSet_Ioi, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun τ hτ => ?_
    rw [ENNReal.ofReal_mul (h0 τ), mul_assoc]
    exact mul_le_mul_right (log_two_mul_exp_le_lintegral hδ.le hτ) _
  -- the right side
  have hpt : ∀ T, g T * ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ) ≤
      (Ioc 0 T₀).indicator (fun _ => ENNReal.ofReal M) T +
        (Ioi 0).indicator (fun T => ENNReal.ofReal (η * Real.exp (-(δ * T)))) T := by
    intro T
    by_cases hT : 0 < T
    · rw [indicator_of_mem (show T ∈ Ioi 0 from hT)]
      by_cases hT₀ : T₀ ≤ T
      · refine le_add_left ?_
        calc g T * ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ)
            ≤ g T * ENNReal.ofReal (η * T) := mul_le_mul_right (hblock T hT₀) _
          _ = ENNReal.ofReal (η * Real.exp (-(δ * T))) := by
              simp only [hg]
              rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hT.le)]
              congr 1
              field_simp
      · push Not at hT₀
        rw [indicator_of_mem (show T ∈ Ioc 0 T₀ from ⟨hT, hT₀.le⟩)]
        refine le_add_right ?_
        have hb : ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ) ≤ ENNReal.ofReal M * ENNReal.ofReal T := by
          calc ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ)
              ≤ ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal M :=
                setLIntegral_mono' measurableSet_Ioc fun τ hτ => ENNReal.ofReal_le_ofReal
                  (hsmall τ ⟨hT.trans hτ.1, by linarith [hτ.2]⟩)
            _ = ENNReal.ofReal M * ENNReal.ofReal T := by
                rw [setLIntegral_const, Real.volume_Ioc]
                congr 2
                ring
        calc g T * ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ)
            ≤ g T * (ENNReal.ofReal M * ENNReal.ofReal T) := mul_le_mul_right hb _
          _ = ENNReal.ofReal (M * Real.exp (-(δ * T))) := by
              simp only [hg]
              rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le
                hT.le)]
              congr 1
              field_simp
          _ ≤ ENNReal.ofReal M := by
              refine ENNReal.ofReal_le_ofReal ?_
              have : Real.exp (-(δ * T)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
              nlinarith
    · have hg0 : g T = 0 := by
        simp only [hg]
        rw [ENNReal.ofReal_eq_zero]
        exact div_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (not_lt.mp hT)
      rw [hg0, zero_mul]
      exact bot_le
  have hexpI : ∫⁻ T in Ioi 0, ENNReal.ofReal (η * Real.exp (-(δ * T))) = ENNReal.ofReal (η / δ) := by
    have hI : IntegrableOn (fun T : ℝ => η * Real.exp (-(δ * T))) (Ioi 0) := by
      have h1 : IntegrableOn (fun T : ℝ => η * Real.exp (-δ * T)) (Ioi 0) :=
        (exp_neg_integrableOn_Ioi 0 hδ).const_mul η
      exact h1.congr_fun (fun T _ => by simp only [neg_mul]) measurableSet_Ioi
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun T => by
      positivity), integral_const_mul]
    have h1 : ∫ T in Ioi (0 : ℝ), Real.exp (-(δ * T)) = 1 / δ := by
      have := integral_exp_mul_Ioi (a := -δ) (by linarith) 0
      simp only [neg_mul, mul_zero, Real.exp_zero] at this
      rw [this]
      field_simp
    rw [h1, mul_one_div]
  have hR : ∫⁻ T, g T * ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ) ≤
      ENNReal.ofReal (M * T₀ + η / δ) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioc),
      lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioi, hexpI,
      setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_add (mul_nonneg hM hT₀) (div_nonneg hη hδ.le)]
  have hmain : (∫⁻ τ in Ioi 0, ENNReal.ofReal (h τ * Real.exp (-(δ * τ)))) *
      ENNReal.ofReal (Real.log 2) ≤ ENNReal.ofReal (M * T₀ + η / δ) := by
    refine hL.trans ?_
    rw [hswap]
    simp_rw [hTslice]
    exact hR
  rw [ENNReal.ofReal_div_of_pos hlog2]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hlog2))
    (Or.inl ENNReal.ofReal_ne_top)).mpr hmain


/-- **Abel-sublinearity from block means.**  A polynomially bounded measurable `g`, vanishing on
`t ≥ 0`, with `∫_T^{2T} |g(−τ)| dτ ≤ ηT` eventually for every `η > 0`, has
`δ ∫ |g(t)| e^{−δ|t|} dt → 0` as `δ → 0⁺`. -/
theorem tendsto_mul_abelMass_of_blocks {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg0 : ∀ t, 0 ≤ t → g t = 0)
    (hblock : ∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖g (-τ)‖ ≤ η * T) :
    Tendsto (fun δ => δ * HamburgerStability.abelMass g δ) (𝓝[>] 0) (𝓝 0) := by
  have hCg : 0 ≤ Cg := by
    have := (norm_nonneg _).trans (hgb 0)
    simpa using this
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀, hb⟩ := hblock (ε * Real.log 2 / 2) (by positivity)
  set M : ℝ := Cg * (1 + 2 * T₀) ^ N with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨ε * Real.log 2 / (2 * (M * T₀ + 1)), by positivity, fun δ hδ hδd => ?_⟩
  have hδ0 : (0 : ℝ) < δ := hδ
  rw [Real.dist_eq, sub_zero] at hδd
  rw [abs_of_pos hδ0] at hδd
  set h : ℝ → ℝ := fun τ => ‖g (-τ)‖ with hh
  have hhm : Measurable h := (hgm.comp measurable_neg).norm
  have hbound : ∀ τ, h τ ≤ Cg * (1 + |τ|) ^ N := fun τ => by
    simpa [hh, abs_neg] using hgb (-τ)
  have hsmall : ∀ τ ∈ Ioc 0 (2 * T₀), h τ ≤ M := fun τ hτ => by
    refine (hbound τ).trans (mul_le_mul_of_nonneg_left ?_ hCg)
    rw [abs_of_pos hτ.1]
    exact pow_le_pow_left₀ (by linarith [hτ.1]) (by linarith [hτ.2]) N
  have hIb : ∀ T, IntegrableOn h (Ioc T (2 * T)) := by
    intro T
    refine Integrable.mono' ((by fun_prop : Continuous fun τ : ℝ =>
      Cg * (1 + |τ|) ^ N).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      hhm.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hbound τ
  have hblock' : ∀ T, T₀ ≤ T → ∫⁻ τ in Ioc T (2 * T), ENNReal.ofReal (h τ) ≤
      ENNReal.ofReal (ε * Real.log 2 / 2 * T) := by
    intro T hT
    rw [← ofReal_integral_eq_lintegral_ofReal (hIb T) (Eventually.of_forall fun τ =>
      norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hb T hT)
  have hL := lintegral_Ioi_mul_exp_le_of_blocks hhm (fun τ => norm_nonneg _) hδ0 hM0
    (by positivity) hT₀ hsmall hblock'
  -- the Abel mass as a lintegral over `τ > 0`
  have hAeq : HamburgerStability.abelMass g δ =
      (∫⁻ τ in Ioi 0, ENNReal.ofReal (h τ * Real.exp (-(δ * τ)))).toReal := by
    unfold HamburgerStability.abelMass
    have hmeas : Measurable fun t : ℝ => ‖g t‖ * Real.exp (-(δ * |t|)) :=
      hgm.norm.mul (by fun_prop : Continuous fun t : ℝ => Real.exp (-(δ * |t|))).measurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t =>
      mul_nonneg (norm_nonneg (g t)) (Real.exp_pos _).le) hmeas.aestronglyMeasurable]
    congr 1
    rw [← lintegral_neg_eq_self, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun τ => ?_
    by_cases hτ : 0 < τ
    · rw [indicator_of_mem (show τ ∈ Ioi 0 from hτ), abs_neg, abs_of_pos hτ]
    · rw [indicator_of_notMem (show τ ∉ Ioi 0 from hτ), hg0 (-τ) (by linarith [not_lt.mp hτ]),
        norm_zero, zero_mul, ENNReal.ofReal_zero]
  have hA : HamburgerStability.abelMass g δ ≤
      (M * T₀ + ε * Real.log 2 / 2 / δ) / Real.log 2 := by
    rw [hAeq]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL
  have hA0 : 0 ≤ HamburgerStability.abelMass g δ :=
    integral_nonneg fun t => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hδ0.le hA0)]
  have hMδ : δ * (M * T₀) < ε * Real.log 2 / 2 := by
    have h1 : δ * (M * T₀ + 1) < ε * Real.log 2 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hδd
      linarith
    nlinarith
  calc δ * HamburgerStability.abelMass g δ
      ≤ δ * ((M * T₀ + ε * Real.log 2 / 2 / δ) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hA hδ0.le
    _ = (δ * (M * T₀) + ε * Real.log 2 / 2) / Real.log 2 := by field_simp
    _ < ε := by
        rw [div_lt_iff₀ hlog2]
        linarith


/-! ### The mean square on the line -/

theorem lineFactor_conj (s : ℂ) : lineFactor (conj s) = conj (lineFactor s) := by
  unfold lineFactor
  rw [RHTower.Gammaℝ_conj]
  simp only [map_mul, map_sub, map_one]

/-- `|φ_G(−τ)| = |φ_G(τ)|` for a producer with real coefficients. -/
theorem norm_phiG_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) (τ : ℝ) :
    ‖PhaseLockRigidity.phiG G (-τ)‖ = ‖PhaseLockRigidity.phiG G τ‖ := by
  have hsl := fun (σ : ℝ) (hσ : 1 < σ) =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have hid := fun (s : ℂ) (hs : 1 < s.re) => weilContinuation_eq_lamTwo hW hs
  have hc : lineS (-τ) = conj (lineS τ) := by rw [← one_sub_lineS, one_sub_lineS_eq_conj]
  have hG := AbelianTwist.G_conj hsl hid hGc hGd hG2 (s := lineS τ) (by rw [lineS_re])
  have hD := lineFactor_conj (lineS τ)
  unfold lineFactor at hD
  unfold PhaseLockRigidity.phiG
  rw [hc, hG, hD, norm_div, norm_div, Complex.norm_conj, Complex.norm_conj]

/-- **Pointwise transfer to the line.**  For `T ≥ 2` and `T < τ ≤ 2T`,
`|G(½ + 2iτ)/(s(s−1)Γ_ℝ(s))| ≤ e⁴ |exp(log F_lam(½ + 1/log 2T + 2iτ))|`. -/
theorem norm_phiG_le_exp_producerLogZeta {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {T τ : ℝ} (hT2 : 2 ≤ T) (hτ : τ ∈ Ioc T (2 * T)) :
    ‖PhaseLockRigidity.phiG G τ‖ ≤ Real.exp 4 *
      Real.exp (producerLogZeta hW (1 / 2 + 1 / Real.log (2 * T)) (2 * τ)).re := by
  have hT0 : 0 < T := by linarith
  set σ' : ℝ := 1 / 2 + 1 / Real.log (2 * T) with hσ'
  have hlog2T : 1 ≤ Real.log (2 * T) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hσ'1 : 1 / 2 < σ' := by
    have : 0 < 1 / Real.log (2 * T) := by positivity
    linarith
  have hσ'2 : σ' ≤ 2 := by
    have : 1 / Real.log (2 * T) ≤ 1 := by rw [div_le_one (by linarith)]; exact hlog2T
    linarith
  have hτ0 : 0 < τ := hT0.trans hτ.1
  have h2τ : 4 ≤ |2 * τ| := by rw [abs_of_pos (by linarith)]; linarith [hτ.1]
  have hline : lineS τ = ((1 / 2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I := by
    rw [lineS_eq]; push_cast; ring
  have hmono := FractionalMassPolynomialTailRigidity.norm_G_le_of_le
    (fun s hs => re_weilContinuation_nonneg hW hs) hGc hGd (2 * τ) le_rfl hσ'1.le
  have hGeq := G_eq_lineFactor_mul_cexp hW hGd hG2 hσ'1 (t := 2 * τ) (by positivity)
  have hD := norm_lineFactor_le hσ'1.le hσ'2 h2τ
  have hDpos : 0 < ‖lineFactor (((1 / 2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I)‖ :=
    norm_pos_iff.mpr (by
      rw [← hline]
      exact mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ))
  have hexp4 : Real.exp ((σ' - 1 / 2) * (Real.log |2 * τ| / 2 + 3)) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_pos (by linarith)]
    have hl : Real.log (2 * τ) ≤ Real.log (4 * T) :=
      Real.log_le_log (by linarith) (by linarith [hτ.2])
    have hl4 : Real.log (4 * T) ≤ 2 * Real.log (2 * T) := by
      have hp := Real.log_pow (2 * T) 2
      push_cast at hp
      rw [← hp]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have e : σ' - 1 / 2 = 1 / Real.log (2 * T) := by rw [hσ']; ring
    rw [e, one_div_mul_eq_div, div_le_iff₀ (by linarith)]
    linarith
  set s₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * I with hs₀
  have e : PhaseLockRigidity.phiG G τ = G s₀ / lineFactor s₀ := by
    unfold PhaseLockRigidity.phiG lineFactor; rw [hline]
  rw [e, norm_div, div_le_iff₀ hDpos]
  calc ‖G s₀‖ ≤ ‖G ((σ' : ℂ) + ((2 * τ : ℝ) : ℂ) * I)‖ := hmono
    _ = ‖lineFactor ((σ' : ℂ) + ((2 * τ : ℝ) : ℂ) * I)‖ *
          Real.exp (producerLogZeta hW σ' (2 * τ)).re := by
        rw [hGeq, norm_mul, Complex.norm_exp]
    _ ≤ Real.exp 4 * ‖lineFactor s₀‖ * Real.exp (producerLogZeta hW σ' (2 * τ)).re :=
        mul_le_mul_of_nonneg_right
          (hD.trans (mul_le_mul_of_nonneg_right hexp4 (norm_nonneg _))) (Real.exp_pos _).le
    _ = Real.exp 4 * Real.exp (producerLogZeta hW σ' (2 * τ)).re * ‖lineFactor s₀‖ := by
        ring

/-- **Moments of the producer on the line.**  For `k > 0` and `0 < ε ≤ 1/8` there are `C`, `T₀`
with `∫_T^{2T} |G(½ + 2iτ)/(s(s−1)Γ_ℝ(s))|^{2k} dτ ≤ C T (log T)^{k² e^ε κ²/(1−4ε)² + ε}`. -/
theorem exists_setIntegral_norm_phiG_rpow_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {k : ℝ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ (2 * k) ≤
        C * T * Real.log T ^ (k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) := by
  set β : ℝ := k ^ 2 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hk2 : 0 ≤ 2 * k := by positivity
  obtain ⟨C₀, T₁, hC₀⟩ := exists_setIntegral_exp_mul_le hW hA hκ hlam hk hε hε8
  refine ⟨Real.exp (8 * k) * max C₀ 0 * 2 ^ β, max T₁ 2, by positivity, fun T hT => ?_⟩
  have hT2 : 2 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  set σ' : ℝ := 1 / 2 + 1 / Real.log (2 * T) with hσ'
  have hlog2T : 1 ≤ Real.log (2 * T) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hσ'1 : 1 / 2 < σ' := by
    have : 0 < 1 / Real.log (2 * T) := by positivity
    linarith
  have hσ'2 : σ' ≤ 2 := by
    have : 1 / Real.log (2 * T) ≤ 1 := by rw [div_le_one (by linarith)]; exact hlog2T
    linarith
  -- the pointwise bound
  have hpt : ∀ τ ∈ Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ (2 * k) ≤
      Real.exp (8 * k) * Real.exp (2 * k * (producerLogZeta hW σ' (2 * τ)).re) := by
    intro τ hτ
    have hphi := norm_phiG_le_exp_producerLogZeta hW hGc hGd hG2 hT2 hτ
    calc ‖PhaseLockRigidity.phiG G τ‖ ^ (2 * k)
        ≤ (Real.exp 4 * Real.exp (producerLogZeta hW σ' (2 * τ)).re) ^ (2 * k) :=
          Real.rpow_le_rpow (norm_nonneg _) hphi hk2
      _ = Real.exp (8 * k) * Real.exp (2 * k * (producerLogZeta hW σ' (2 * τ)).re) := by
          rw [← Real.exp_add, ← Real.exp_mul, ← Real.exp_add]
          congr 1; ring
  -- integrate
  set f : ℝ → ℝ := fun t => Real.exp (2 * k * (producerLogZeta hW σ' t).re) with hf
  have hfc : ∀ a : ℝ, 0 < a → ∀ b, ContinuousOn f (Icc a b) := fun a ha b =>
    (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((continuousOn_producerLogZeta hW hσ'1 hσ'2).mono fun t ht =>
        show (0 : ℝ) < t from ha.trans_le ht.1))).rexp
  have hI1 : IntegrableOn (fun τ => ‖PhaseLockRigidity.phiG G τ‖ ^ (2 * k)) (Ioc T (2 * T)) :=
    ((((PhaseLockRigidity.continuous_phiG hGc).norm.rpow_const fun _ =>
      Or.inr hk2)).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hI2 : IntegrableOn (fun τ : ℝ => Real.exp (8 * k) * f (2 * τ)) (Ioc T (2 * T)) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    refine continuousOn_const.mul ((hfc (2 * T) (by positivity) (2 * (2 * T))).comp
      (continuousOn_const.mul continuousOn_id) fun τ hτ => ?_)
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hchange : ∫ τ in Ioc T (2 * T), f (2 * τ) =
      2⁻¹ * ∫ t in Ioc (2 * T) (2 * (2 * T)), f t := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  have hmom := hC₀ (2 * T) ((le_max_left _ _).trans (by linarith [hT]))
  rw [← hβ] at hmom
  have hlogle : Real.log (2 * T) ≤ 2 * Real.log T := by
    have hp := Real.log_pow T 2
    push_cast at hp
    rw [← hp]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hpow : Real.log (2 * T) ^ β ≤ 2 ^ β * Real.log T ^ β := by
    rw [← Real.mul_rpow (by norm_num) hlogT]
    exact Real.rpow_le_rpow (by linarith) hlogle hβ0
  have hX : 0 ≤ 2 * T * Real.log (2 * T) ^ β := by positivity
  calc ∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ (2 * k)
      ≤ ∫ τ in Ioc T (2 * T), Real.exp (8 * k) * f (2 * τ) :=
        setIntegral_mono_on hI1 hI2 measurableSet_Ioc hpt
    _ = Real.exp (8 * k) * (2⁻¹ * ∫ t in Ioc (2 * T) (2 * (2 * T)), f t) := by
        rw [integral_const_mul, hchange]
    _ ≤ Real.exp (8 * k) * (2⁻¹ * (max C₀ 0 * (2 * T) * Real.log (2 * T) ^ β)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmom.trans ?_)
          (by norm_num)) (Real.exp_pos _).le
        have h := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) hX
        calc C₀ * (2 * T) * Real.log (2 * T) ^ β = C₀ * (2 * T * Real.log (2 * T) ^ β) := by
              ring
          _ ≤ max C₀ 0 * (2 * T * Real.log (2 * T) ^ β) := h
          _ = max C₀ 0 * (2 * T) * Real.log (2 * T) ^ β := by ring
    _ = Real.exp (8 * k) * max C₀ 0 * T * Real.log (2 * T) ^ β := by ring
    _ ≤ Real.exp (8 * k) * max C₀ 0 * T * (2 ^ β * Real.log T ^ β) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp (8 * k) * max C₀ 0 * 2 ^ β * T * Real.log T ^ β := by ring

/-- **The mean square of the producer on the line** (`k = 1`). -/
theorem exists_setIntegral_norm_phiG_sq_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 8) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ 2 ≤
        C * T * Real.log T ^ (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2 + ε) := by
  obtain ⟨C, T₀, hC, h⟩ := exists_setIntegral_norm_phiG_rpow_le hW hA hκ hlam hGc hGd hG2
    one_pos hε hε8
  refine ⟨C, T₀, hC, fun T hT => ?_⟩
  have := h T hT
  simp only [mul_one, one_pow, one_mul] at this
  simpa only [Real.rpow_two] using this

/-! ### Settled locks -/

theorem exists_eps_exponent_lt (r κ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 8 ∧
      r * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε < r * κ ^ 2 + η := by
  have hc : ContinuousAt (fun ε : ℝ => r * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) 0 :=
    (continuousAt_const.mul ((Real.continuous_exp.continuousAt.mul continuousAt_const).div
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2)
      (by norm_num))).add continuousAt_id
  have h0 : (fun ε : ℝ => r * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε) 0 <
      r * κ ^ 2 + η := by
    simp only [Real.exp_zero, one_mul, mul_zero, sub_zero, one_pow, div_one, add_zero]
    linarith
  have hev := (hc.eventually (gt_mem_nhds h0)).and
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  exact ⟨ε, h3, h2.le, h1⟩

theorem tendsto_log_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℝ => Real.log T ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp Real.tendsto_log_atTop

theorem integrableOn_mul_norm_phiG {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) {u : ℝ → ℂ} (hum : Measurable u) {Cu : ℝ}
    (hub : ∀ τ, ‖u τ‖ ≤ Cu) (T : ℝ) :
    IntegrableOn (fun τ => ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖) (Ioc T (2 * T)) := by
  have hp : IntegrableOn (fun τ => Cu * ‖PhaseLockRigidity.phiG G τ‖) (Ioc T (2 * T)) :=
    ((continuous_const.mul (PhaseLockRigidity.continuous_phiG hGc).norm).continuousOn
      |>.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine Integrable.mono' hp ((hum.norm.mul
    (PhaseLockRigidity.continuous_phiG hGc).measurable.norm)).aestronglyMeasurable
    (Eventually.of_forall fun τ => ?_)
  have hCu : 0 ≤ Cu := (norm_nonneg _).trans (hub τ)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (hub τ) (norm_nonneg _)

/-- **Lock rigidity from block means.**  Let `G` be a producer for a full-cone Weil-positive
`lam`, with `G(1 − s) = w(τ) G(s)` at `s = ½ + 2iτ`, `τ < −Y`, `w` bounded and measurable.  If
`∫_T^{2T} |w(−τ) − c₀⁻¹| |G(½+2iτ)/(s(s−1)Γ_ℝ(s))| dτ = o(T)`, then `lam = Λ` and RH holds. -/
theorem lock_rigidity_of_block_means {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {w : ℝ → ℂ} (hwm : Measurable w) {Cw : ℝ}
    (hwb : ∀ τ, ‖w τ‖ ≤ Cw) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) = w τ * G (lineS τ))
    (hblock : ∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖w (-τ) - c₀⁻¹‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤ η * T) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hsl := fun (σ : ℝ) (hσ : 1 < σ) =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have hid := fun (s : ℂ) (hs : 1 < s.re) => weilContinuation_eq_lamTwo hW hs
  have hΦre := fun (s : ℂ) (hs : 1 / 2 < s.re) => re_weilContinuation_nonneg hW hs
  obtain ⟨CB, N, hCB, hpoly⟩ := PhaseLockRigidity.exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  set e : ℝ → ℂ := fun τ => if τ < -Y then (w τ - c₀⁻¹) * PhaseLockRigidity.phiG G τ else 0
    with he
  have hD : ∀ τ, lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 := fun τ =>
    mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
      (Gammaℝ_lineS_ne_zero τ)
  have hlock' : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) =
      c₀⁻¹ * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ := by
    intro τ hτ
    simp only [he, if_pos hτ]
    unfold PhaseLockRigidity.phiG
    rw [hlock τ hτ]
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)
    have hDG : D * (G (lineS τ) / D) = G (lineS τ) := mul_div_cancel₀ _ (hD τ)
    calc w τ * G (lineS τ) = c₀⁻¹ * G (lineS τ) + (w τ - c₀⁻¹) * (D * (G (lineS τ) / D)) := by
          rw [hDG]; ring
      _ = c₀⁻¹ * G (lineS τ) + D * ((w τ - c₀⁻¹) * (G (lineS τ) / D)) := by ring
  have hem : Measurable e :=
    Measurable.ite measurableSet_Iio ((hwm.sub_const _).mul
      (PhaseLockRigidity.continuous_phiG hGc).measurable) measurable_const
  have hCw : 0 ≤ Cw := (norm_nonneg _).trans (hwb 0)
  have heb : ∀ τ, ‖e τ‖ ≤ ((Cw + ‖c₀⁻¹‖) * CB) * (1 + |τ|) ^ N := by
    intro τ
    simp only [he]
    split_ifs
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add_left (hwb τ) _ |>.trans_eq
        (by ring))) (hpoly τ).1 (norm_nonneg _) (by positivity)
    · rw [norm_zero]; positivity
  have hg0 : ∀ t : ℝ, 0 ≤ t → e t = 0 := fun t ht => by
    simp only [he]; rw [if_neg (by linarith)]
  have hblock' : ∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖e (-τ)‖ ≤ η * T := by
    intro η hη
    obtain ⟨T₀, hT₀⟩ := hblock η hη
    refine ⟨max T₀ Y, le_max_of_le_right hY, fun T hT => ?_⟩
    have hTY : Y ≤ T := (le_max_right _ _).trans hT
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_)
      (hT₀ T ((le_max_left _ _).trans hT))
    have hneg : -τ < -Y := by linarith [hτ.1]
    simp only [he, if_pos hneg]
    rw [norm_mul, norm_phiG_neg hW hGc hGd hG2]
  have heA := tendsto_mul_abelMass_of_blocks hem heb hg0 hblock'
  exact PhaseLockRigidity.phase_lock_rigidity_of_defect hsl
    (differentiableOn_weilContinuation hW) hΦre hid hGc hGd hG2 hem heb heA hY hc₀ hlock'

/-- **Block means from a mean-square gap.**  In the class of `exists_setIntegral_exp_mul_le`, a
bounded measurable `u` with `∫_T^{2T} |u|² ≤ C T (log T)^{−κ² − η}` has
`∫_T^{2T} |u(τ)| |G(½+2iτ)/(s(s−1)Γ_ℝ(s))| dτ = o(T)`. -/
theorem blockMeans_of_meanSquare {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {u : ℝ → ℂ} (hum : Measurable u) {Cu : ℝ}
    (hub : ∀ τ, ‖u τ‖ ≤ Cu) {η Cm T₁ : ℝ} (hη : 0 < η)
    (hmean : ∀ T : ℝ, T₁ ≤ T → ∫ τ in Ioc T (2 * T), ‖u τ‖ ^ 2 ≤
      Cm * T * Real.log T ^ (-(κ ^ 2 + η))) :
    ∀ η' : ℝ, 0 < η' → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤ η' * T := by
  obtain ⟨ε, hε, hε8, hβlt⟩ := exists_eps_exponent_lt 1 κ (half_pos hη)
  simp only [one_mul] at hβlt
  set β : ℝ := Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2 + ε with hβ
  obtain ⟨C₂, T₂, hC₂, hB⟩ := exists_setIntegral_norm_phiG_sq_le hW hA hκ hlam hGc hGd hG2 hε hε8
  intro η' hη'
  set d : ℝ := κ ^ 2 + η / 2 - β with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hlim : Tendsto (fun T : ℝ => (max Cm 0 * Real.log T ^ (-(η / 2)) +
      C₂ * Real.log T ^ (-d)) / 2) atTop (𝓝 0) := by
    have h := ((tendsto_log_rpow_neg (half_pos hη)).const_mul (max Cm 0)).add
      ((tendsto_log_rpow_neg hd0).const_mul C₂)
    simpa using h.div_const 2
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη'))
  refine ⟨max (max T₁ T₂) (max T₃ 2), fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT3 : T₃ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTtwo : 2 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  set L : ℝ := Real.log T with hL
  set lam' : ℝ := L ^ (κ ^ 2 + η / 2) with hlam'
  have hlam'0 : 0 < lam' := Real.rpow_pos_of_pos hlogT _
  have hpt : ∀ τ ∈ Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤
      (lam' * ‖u τ‖ ^ 2 + lam'⁻¹ * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) / 2 := by
    intro τ _
    set a := ‖u τ‖
    set b := ‖PhaseLockRigidity.phiG G τ‖
    have e1 : (lam' * a ^ 2 + lam'⁻¹ * b ^ 2) / 2 - a * b = lam'⁻¹ * (lam' * a - b) ^ 2 / 2 := by
      field_simp; ring
    have : 0 ≤ lam'⁻¹ * (lam' * a - b) ^ 2 / 2 := by positivity
    linarith
  have hwI : IntegrableOn (fun τ => ‖u τ‖ ^ 2) (Ioc T (2 * T)) := by
    refine Measure.integrableOn_of_bounded (M := Cu ^ 2)
      (by simp [Real.volume_Ioc]) (hum.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hub τ) 2
  have hpI : IntegrableOn (fun τ => ‖PhaseLockRigidity.phiG G τ‖ ^ 2) (Ioc T (2 * T)) :=
    (((PhaseLockRigidity.continuous_phiG hGc).norm.pow 2).continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hI1 : IntegrableOn (fun τ => lam' * ‖u τ‖ ^ 2) (Ioc T (2 * T)) := hwI.const_mul lam'
  have hI2 : IntegrableOn (fun τ => lam'⁻¹ * ‖PhaseLockRigidity.phiG G τ‖ ^ 2)
      (Ioc T (2 * T)) := hpI.const_mul lam'⁻¹
  have hI3 : IntegrableOn (fun τ => (lam' * ‖u τ‖ ^ 2 +
      lam'⁻¹ * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) / 2) (Ioc T (2 * T)) :=
    (hI1.add hI2).div_const 2
  have hmono := setIntegral_mono_on (integrableOn_mul_norm_phiG hGc hum hub T) hI3
    measurableSet_Ioc hpt
  rw [integral_div, integral_add hI1 hI2, integral_const_mul, integral_const_mul] at hmono
  have hA' := hmean T hT1
  have hB' := hB T hT2
  rw [← hβ] at hB'
  have hA'' : lam' * ∫ τ in Ioc T (2 * T), ‖u τ‖ ^ 2 ≤ T * (max Cm 0 * L ^ (-(η / 2))) := by
    calc lam' * ∫ τ in Ioc T (2 * T), ‖u τ‖ ^ 2
        ≤ lam' * (max Cm 0 * T * L ^ (-(κ ^ 2 + η))) := by
          refine mul_le_mul_of_nonneg_left (hA'.trans ?_) hlam'0.le
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            hT0.le) (by positivity)
      _ = T * (max Cm 0 * L ^ (-(η / 2))) := by
          rw [hlam']
          have e1 : L ^ (κ ^ 2 + η / 2) * L ^ (-(κ ^ 2 + η)) = L ^ (-(η / 2)) := by
            rw [← Real.rpow_add hlogT]; congr 1; ring
          calc L ^ (κ ^ 2 + η / 2) * (max Cm 0 * T * L ^ (-(κ ^ 2 + η)))
              = T * (max Cm 0 * (L ^ (κ ^ 2 + η / 2) * L ^ (-(κ ^ 2 + η)))) := by ring
            _ = T * (max Cm 0 * L ^ (-(η / 2))) := by rw [e1]
  have hB'' : lam'⁻¹ * ∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ 2 ≤
      T * (C₂ * L ^ (-d)) := by
    calc lam'⁻¹ * ∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ 2
        ≤ lam'⁻¹ * (C₂ * T * L ^ β) := mul_le_mul_of_nonneg_left hB' (inv_nonneg.mpr hlam'0.le)
      _ = T * (C₂ * L ^ (-d)) := by
          rw [hlam', ← Real.rpow_neg hlogT.le]
          have e1 : L ^ (-(κ ^ 2 + η / 2)) * L ^ β = L ^ (-d) := by
            rw [← Real.rpow_add hlogT]; congr 1; rw [hd]; ring
          calc L ^ (-(κ ^ 2 + η / 2)) * (C₂ * T * L ^ β)
              = T * (C₂ * (L ^ (-(κ ^ 2 + η / 2)) * L ^ β)) := by ring
            _ = T * (C₂ * L ^ (-d)) := by rw [e1]
  have hlt := hT₃ T hT3
  calc ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖
      ≤ (lam' * (∫ τ in Ioc T (2 * T), ‖u τ‖ ^ 2) +
        lam'⁻¹ * (∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ^ 2)) / 2 := hmono
    _ ≤ (T * (max Cm 0 * L ^ (-(η / 2))) + T * (C₂ * L ^ (-d))) / 2 := by
        linarith
    _ = T * ((max Cm 0 * L ^ (-(η / 2)) + C₂ * L ^ (-d)) / 2) := by ring
    _ ≤ T * η' := mul_le_mul_of_nonneg_left hlt.le hT0.le
    _ = η' * T := mul_comm _ _

/-- **Block means from a uniform gap.**  In the class of `exists_setIntegral_exp_mul_le`, a
bounded measurable `u` with `|u(τ)| ≤ C (log T)^{−κ²/4 − η}` on `(T, 2T]` has
`∫_T^{2T} |u(τ)| |G(½+2iτ)/(s(s−1)Γ_ℝ(s))| dτ = o(T)`. -/
theorem blockMeans_of_uniform {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {u : ℝ → ℂ} (hum : Measurable u) {Cu : ℝ}
    (hub : ∀ τ, ‖u τ‖ ≤ Cu) {η Cm T₁ : ℝ} (hη : 0 < η)
    (hunif : ∀ T : ℝ, T₁ ≤ T → ∀ τ ∈ Ioc T (2 * T),
      ‖u τ‖ ≤ Cm * Real.log T ^ (-(κ ^ 2 / 4 + η))) :
    ∀ η' : ℝ, 0 < η' → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤ η' * T := by
  obtain ⟨ε, hε, hε8, hβlt⟩ := exists_eps_exponent_lt (1 / 4) κ (half_pos hη)
  set β : ℝ := 1 / 4 * (Real.exp ε * κ ^ 2 / (1 - 4 * ε) ^ 2) + ε with hβ
  obtain ⟨C₂, T₂, hC₂, hB⟩ := exists_setIntegral_norm_phiG_rpow_le hW hA hκ hlam hGc hGd hG2
    (k := 1 / 2) (by norm_num) hε hε8
  have hk : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
  have h21 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [hk, h21, Real.rpow_one] at hB
  rw [← hβ] at hB
  intro η' hη'
  set d : ℝ := κ ^ 2 / 4 + η - β with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hlim : Tendsto (fun T : ℝ => max Cm 0 * C₂ * Real.log T ^ (-d)) atTop (𝓝 0) := by
    simpa using (tendsto_log_rpow_neg hd0).const_mul (max Cm 0 * C₂)
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη'))
  refine ⟨max (max T₁ T₂) (max T₃ 2), fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hT3 : T₃ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTtwo : 2 ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  set L : ℝ := Real.log T with hL
  have hLpos : 0 ≤ L ^ (-(κ ^ 2 / 4 + η)) := (Real.rpow_pos_of_pos hlogT _).le
  have hpI : IntegrableOn (fun τ => ‖PhaseLockRigidity.phiG G τ‖) (Ioc T (2 * T)) :=
    ((PhaseLockRigidity.continuous_phiG hGc).norm.continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hpt : ∀ τ ∈ Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤
      max Cm 0 * L ^ (-(κ ^ 2 / 4 + η)) * ‖PhaseLockRigidity.phiG G τ‖ := fun τ hτ =>
    mul_le_mul_of_nonneg_right ((hunif T hT1 τ hτ).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) hLpos)) (norm_nonneg _)
  have hmono := setIntegral_mono_on (integrableOn_mul_norm_phiG hGc hum hub T)
    (hpI.const_mul (max Cm 0 * L ^ (-(κ ^ 2 / 4 + η)))) measurableSet_Ioc hpt
  rw [integral_const_mul] at hmono
  have hB' := hB T hT2
  have hlt := hT₃ T hT3
  have e1 : L ^ (-(κ ^ 2 / 4 + η)) * L ^ β = L ^ (-d) := by
    rw [← Real.rpow_add hlogT]; congr 1; rw [hd]; ring
  calc ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖
      ≤ max Cm 0 * L ^ (-(κ ^ 2 / 4 + η)) *
          ∫ τ in Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ := hmono
    _ ≤ max Cm 0 * L ^ (-(κ ^ 2 / 4 + η)) * (C₂ * T * L ^ β) :=
        mul_le_mul_of_nonneg_left hB' (mul_nonneg (le_max_right _ _) hLpos)
    _ = T * (max Cm 0 * C₂ * (L ^ (-(κ ^ 2 / 4 + η)) * L ^ β)) := by ring
    _ = T * (max Cm 0 * C₂ * L ^ (-d)) := by rw [e1]
    _ ≤ T * η' := mul_le_mul_of_nonneg_left hlt.le hT0.le
    _ = η' * T := mul_comm _ _

/-- **Settled locks are rigid.**  Let `lam` be full-cone Weil-positive with `|lam(n)| ≤ κ log n`
and summable rest weight, and `G` a producer for `lam`.  Suppose
`G(1 − s) = w(τ) G(s)` at `s = ½ + 2iτ`, `τ < −Y`, with `w` bounded and measurable, and for some
`η > 0`

`∫_T^{2T} |w(−τ) − c₀⁻¹|² dτ ≤ C T (log T)^{−κ² − η}`  for `T ≥ T₁`.

Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {w : ℝ → ℂ} (hwm : Measurable w) {Cw : ℝ}
    (hwb : ∀ τ, ‖w τ‖ ≤ Cw) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) = w τ * G (lineS τ))
    {η Cm T₁ : ℝ} (hη : 0 < η)
    (hmean : ∀ T : ℝ, T₁ ≤ T → ∫ τ in Ioc T (2 * T), ‖w (-τ) - c₀⁻¹‖ ^ 2 ≤
      Cm * T * Real.log T ^ (-(κ ^ 2 + η))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  lock_rigidity_of_block_means hW hGc hGd hG2 hwm hwb hc₀ hY hlock
    (blockMeans_of_meanSquare hW hA hκ hlam hGc hGd hG2 (u := fun τ => w (-τ) - c₀⁻¹)
      ((hwm.comp measurable_neg).sub_const _) (Cu := Cw + ‖c₀⁻¹‖)
      (fun τ => (norm_sub_le _ _).trans (by linarith [hwb (-τ)])) hη hmean)

/-- **Uniformly settled locks are rigid.**  In the setting of `settled_lock_rigidity`, suppose
instead that for some `η > 0`

`|w(−τ) − c₀⁻¹| ≤ C (log T)^{−κ²/4 − η}`  for `T < τ ≤ 2T`, `T ≥ T₁`.

Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.  The exponent `κ²/4`
comes from the first moment `∫_T^{2T} |G/(s(s−1)Γ_ℝ)| ≪ T (log T)^{κ²/4 + o(1)}` (`k = ½`). -/
theorem uniformly_settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {w : ℝ → ℂ} (hwm : Measurable w) {Cw : ℝ}
    (hwb : ∀ τ, ‖w τ‖ ≤ Cw) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) = w τ * G (lineS τ))
    {η Cm T₁ : ℝ} (hη : 0 < η)
    (hunif : ∀ T : ℝ, T₁ ≤ T → ∀ τ ∈ Ioc T (2 * T),
      ‖w (-τ) - c₀⁻¹‖ ≤ Cm * Real.log T ^ (-(κ ^ 2 / 4 + η))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  lock_rigidity_of_block_means hW hGc hGd hG2 hwm hwb hc₀ hY hlock
    (blockMeans_of_uniform hW hA hκ hlam hGc hGd hG2 (u := fun τ => w (-τ) - c₀⁻¹)
      ((hwm.comp measurable_neg).sub_const _) (Cu := Cw + ‖c₀⁻¹‖)
      (fun τ => (norm_sub_le _ _).trans (by linarith [hwb (-τ)])) hη hunif)


/-! ### Every producer: power-rate settling -/

/-- **Block means from a power-saving gap, for every producer.**  Producer Lindelöf on the line
(`|φ_G(τ)| ≪_ν (1+|τ|)^ν`) turns `∫_T^{2T} |u| = O(T^{1−δ})` into
`∫_T^{2T} |u(τ)| |G(½+2iτ)/(s(s−1)Γ_ℝ(s))| dτ = o(T)`.  No class condition on `lam` is used. -/
theorem blockMeans_of_powerL1 {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {u : ℝ → ℂ} (hum : Measurable u) {Cu : ℝ}
    (hub : ∀ τ, ‖u τ‖ ≤ Cu) {δ Cm T₁ : ℝ} (hδ : 0 < δ)
    (hpow : ∀ T : ℝ, T₁ ≤ T → ∫ τ in Ioc T (2 * T), ‖u τ‖ ≤ Cm * T ^ (1 - δ)) :
    ∀ η' : ℝ, 0 < η' → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤ η' * T := by
  have hsl := fun (σ : ℝ) (hσ : 1 < σ) =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have hid := fun (s : ℂ) (hs : 1 < s.re) => weilContinuation_eq_lamTwo hW hs
  have hΦre := fun (s : ℂ) (hs : 1 / 2 < s.re) => re_weilContinuation_nonneg hW hs
  obtain ⟨C, hC0, hC⟩ := FractionalMassPolynomialTailRigidity.exists_norm_phiG_le_rpow_small hsl
    (differentiableOn_weilContinuation hW) hΦre hid hGc hGd hG2 (half_pos hδ)
  intro η' hη'
  set K : ℝ := C * (4 : ℝ) ^ (δ / 2) * max Cm 0 with hK
  have hlim : Tendsto (fun T : ℝ => K * T ^ (-(δ / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (half_pos hδ)).const_mul K
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη'))
  refine ⟨max (max T₁ T₃) 1, fun T hT => ?_⟩
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT3 : T₃ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTone : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hpI : IntegrableOn (fun τ => ‖u τ‖) (Ioc T (2 * T)) := by
    refine Measure.integrableOn_of_bounded (M := Cu) (by simp [Real.volume_Ioc])
      hum.norm.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hub τ
  have hbound : ∀ τ ∈ Ioc T (2 * T), ‖PhaseLockRigidity.phiG G τ‖ ≤
      C * ((4 : ℝ) ^ (δ / 2) * T ^ (δ / 2)) := by
    intro τ hτ
    rw [← Real.mul_rpow (by norm_num) hT0.le]
    refine (hC τ).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_
      (by positivity)) hC0)
    rw [abs_of_pos (hT0.trans hτ.1)]
    linarith [hτ.2]
  have hpt : ∀ τ ∈ Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤
      C * ((4 : ℝ) ^ (δ / 2) * T ^ (δ / 2)) * ‖u τ‖ := fun τ hτ => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hbound τ hτ) (norm_nonneg _)
  have hmono := setIntegral_mono_on (integrableOn_mul_norm_phiG hGc hum hub T)
    (hpI.const_mul (C * ((4 : ℝ) ^ (δ / 2) * T ^ (δ / 2)))) measurableSet_Ioc hpt
  rw [integral_const_mul] at hmono
  have hA := hpow T hT1
  have hlt := hT₃ T hT3
  have e1 : T ^ (δ / 2) * T ^ (1 - δ) = T * T ^ (-(δ / 2)) := by
    rw [← Real.rpow_add hT0, show δ / 2 + (1 - δ) = 1 + -(δ / 2) by ring, Real.rpow_add hT0,
      Real.rpow_one]
  calc ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖
      ≤ C * ((4 : ℝ) ^ (δ / 2) * T ^ (δ / 2)) * ∫ τ in Ioc T (2 * T), ‖u τ‖ := hmono
    _ ≤ C * ((4 : ℝ) ^ (δ / 2) * T ^ (δ / 2)) * (max Cm 0 * T ^ (1 - δ)) := by
        refine mul_le_mul_of_nonneg_left (hA.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = T * (K * T ^ (-(δ / 2))) := by
        rw [hK]
        calc C * ((4 : ℝ) ^ (δ / 2) * T ^ (δ / 2)) * (max Cm 0 * T ^ (1 - δ))
            = C * (4 : ℝ) ^ (δ / 2) * max Cm 0 * (T ^ (δ / 2) * T ^ (1 - δ)) := by ring
          _ = _ := by rw [e1]; ring
    _ ≤ T * η' := mul_le_mul_of_nonneg_left hlt.le hT0.le
    _ = η' * T := mul_comm _ _

/-- **Power-rate settled locks are rigid, for every producer.**  Let `G` be a producer for a
full-cone Weil-positive `lam` (no growth or support condition), with
`G(1 − s) = w(τ) G(s)` at `s = ½ + 2iτ`, `τ < −Y`, `w` bounded and measurable.  If
`∫_T^{2T} |w(−τ) − c₀⁻¹| dτ = O(T^{1−δ})` for some `δ > 0`, then `lam = Λ` and RH holds. -/
theorem power_settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {w : ℝ → ℂ} (hwm : Measurable w) {Cw : ℝ}
    (hwb : ∀ τ, ‖w τ‖ ≤ Cw) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) = w τ * G (lineS τ))
    {δ Cm T₁ : ℝ} (hδ : 0 < δ)
    (hpow : ∀ T : ℝ, T₁ ≤ T → ∫ τ in Ioc T (2 * T), ‖w (-τ) - c₀⁻¹‖ ≤ Cm * T ^ (1 - δ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  lock_rigidity_of_block_means hW hGc hGd hG2 hwm hwb hc₀ hY hlock
    (blockMeans_of_powerL1 hW hGc hGd hG2 (u := fun τ => w (-τ) - c₀⁻¹)
      ((hwm.comp measurable_neg).sub_const _) (Cu := Cw + ‖c₀⁻¹‖)
      (fun τ => (norm_sub_le _ _).trans (by linarith [hwb (-τ)])) hδ hpow)


/-! ### The weighted mean-square criterion -/

/-- **Block means from a weighted mean square.**  If `∫_T^{2T} |u|² |φ_G|² = o(T)`, then
`∫_T^{2T} |u| |φ_G| = o(T)` (weighted Cauchy–Schwarz against `1`). -/
theorem blockMeans_of_weightedMeanSquare {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) {u : ℝ → ℂ} (hum : Measurable u) {Cu : ℝ}
    (hub : ∀ τ, ‖u τ‖ ≤ Cu)
    (hE : ∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖u τ‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2 ≤ η * T) :
    ∀ η' : ℝ, 0 < η' → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤ η' * T := by
  intro η' hη'
  obtain ⟨T₀, hT₀⟩ := hE (η' ^ 2) (by positivity)
  refine ⟨max T₀ 0, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
  have hE' := hT₀ T ((le_max_left _ _).trans hT)
  have hpt : ∀ τ ∈ Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖ ≤
      (η'⁻¹ * (‖u τ‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) + η') / 2 := by
    intro τ _
    set a := ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖
    have e1 : (η'⁻¹ * (‖u τ‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) + η') / 2 - a =
        η'⁻¹ * (a - η') ^ 2 / 2 := by
      simp only [a]; field_simp; ring
    have : 0 ≤ η'⁻¹ * (a - η') ^ 2 / 2 := by positivity
    linarith
  have hI1 : IntegrableOn (fun τ => ‖u τ‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2)
      (Ioc T (2 * T)) := by
    have hp : IntegrableOn (fun τ => Cu ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) (Ioc T (2 * T)) :=
      ((continuous_const.mul ((PhaseLockRigidity.continuous_phiG hGc).norm.pow 2)).continuousOn
        |>.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    refine Integrable.mono' hp ((hum.norm.pow_const 2).mul
      ((PhaseLockRigidity.continuous_phiG hGc).measurable.norm.pow_const 2)).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hub τ) 2) (by positivity)
  have hI2 : IntegrableOn (fun τ => (η'⁻¹ * (‖u τ‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) + η') / 2)
      (Ioc T (2 * T)) :=
    ((hI1.const_mul η'⁻¹).add (integrableOn_const (by simp [Real.volume_Ioc]))).div_const 2
  have hmono := setIntegral_mono_on (integrableOn_mul_norm_phiG hGc hum hub T) hI2
    measurableSet_Ioc hpt
  rw [integral_div, integral_add (hI1.const_mul η'⁻¹) (integrableOn_const
    (by simp [Real.volume_Ioc])), integral_const_mul, setIntegral_const, smul_eq_mul,
    Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at hmono
  calc ∫ τ in Ioc T (2 * T), ‖u τ‖ * ‖PhaseLockRigidity.phiG G τ‖
      ≤ (η'⁻¹ * (∫ τ in Ioc T (2 * T), ‖u τ‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2) +
          (2 * T - T) * η') / 2 := hmono
    _ ≤ (η'⁻¹ * (η' ^ 2 * T) + T * η') / 2 := by
        gcongr
        linarith
    _ = η' * T := by field_simp; ring

/-- **The weighted mean-square criterion (every producer).**  A producer whose lock gap has
`∫_T^{2T} |w(−τ) − c₀⁻¹|² |G(½+2iτ)/(s(s−1)Γ_ℝ(s))|² dτ = o(T)` is `Λ`, and RH holds.  For
`w = e^{−2πiN_ν}` and `c₀ = 1` the integral is twice the mean-square excess
`ℰ(T) = ∫ |F|² (1 − cos 2πN_ν)`. -/
theorem weighted_meanSquare_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {w : ℝ → ℂ} (hwm : Measurable w) {Cw : ℝ}
    (hwb : ∀ τ, ‖w τ‖ ≤ Cw) {c₀ : ℂ} (hc₀ : c₀ ≠ 0) {Y : ℝ} (hY : 0 ≤ Y)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) = w τ * G (lineS τ))
    (hE : ∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ τ in Ioc T (2 * T), ‖w (-τ) - c₀⁻¹‖ ^ 2 * ‖PhaseLockRigidity.phiG G τ‖ ^ 2 ≤ η * T) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  lock_rigidity_of_block_means hW hGc hGd hG2 hwm hwb hc₀ hY hlock
    (blockMeans_of_weightedMeanSquare hGc (u := fun τ => w (-τ) - c₀⁻¹)
      ((hwm.comp measurable_neg).sub_const _) (Cu := Cw + ‖c₀⁻¹‖)
      (fun τ => (norm_sub_le _ _).trans (by linarith [hwb (-τ)])) hE)

end RHTower.WeilSpectral
