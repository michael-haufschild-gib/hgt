import GaloisForLFunctions.RHTower.NonvacuousTestField

/-!
# The Dirichlet energy of the test field

For the test field `F = F_{N,L}` and a point pair `(z, w)`, the difference splits into a phase part and a
cutoff part (`norm_sq_testField_sub_le`):

  `‖F(z) − F(w)‖² ≤ (2 c_L(z)²/N²) Σ_q |ℓ(g_q⁻¹z) − ℓ(g_q⁻¹w)|² + 2 [SL(2,ℤ):Γ_N] (log ρ(u)/log L)²`,

because `|e^{ia} − e^{ib}| ≤ |a − b|`, the ramp is `1/log L`-Lipschitz in `log Y`, and
`|log Y(z) − log Y(w)| ≤ log ρ(u(z, w))` (`abs_log_invHeight_sub_le`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped MatrixGroups InnerProductSpace ENNReal

namespace GaloisForLFunctions.RHTower.NonvacuousWitness

open GaloisForLFunctions.HTGeometry RepPointPair RepCoset ModularLambdaWinding

noncomputable section

/-- `|e^{ia/N} − e^{ib/N}| ≤ |a − b|/N`. -/
theorem norm_phase_sub_le (N : ℕ) [NeZero N] (a b : ℝ) :
    ‖Complex.exp (((a / N : ℝ) : ℂ) * Complex.I) - Complex.exp (((b / N : ℝ) : ℂ) * Complex.I)‖ ≤
      |a - b| / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have e : Complex.exp (((a / N : ℝ) : ℂ) * Complex.I) - Complex.exp (((b / N : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((b / N : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * (((a - b) / N : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hN]

/-- The comparison factor is at least `1` and monotone. -/
theorem one_le_heightRatio {u : ℝ} (hu : 0 ≤ u) : 1 ≤ heightRatio u := by
  unfold heightRatio
  have := Real.sqrt_nonneg (u ^ 2 + u)
  linarith

theorem heightRatio_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : heightRatio u ≤ heightRatio v := by
  unfold heightRatio
  have : Real.sqrt (u ^ 2 + u) ≤ Real.sqrt (v ^ 2 + v) :=
    Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- **Log-heights of near points**: `|log Y(z) − log Y(w)| ≤ log ρ(u(z, w))`. -/
theorem abs_log_invHeight_sub_le (z w : ℍ) :
    |Real.log (invHeight z) - Real.log (invHeight w)| ≤ Real.log (heightRatio (pairU z w)) := by
  have hρ := one_le_heightRatio (pairU_nonneg z w)
  have hρpos : 0 < heightRatio (pairU z w) := by linarith
  have h1 := invHeight_le_rho_mul z w
  have h2 := invHeight_le_rho_mul w z
  rw [pairU_comm] at h2
  have hz := invHeight_pos z
  have hw := invHeight_pos w
  rw [abs_le]
  constructor
  · have := Real.log_le_log hw h2
    rw [Real.log_mul hρpos.ne' hz.ne'] at this
    linarith
  · have := Real.log_le_log hz h1
    rw [Real.log_mul hρpos.ne' hw.ne'] at this
    linarith

/-- **The cutoff is Lipschitz in the log-height**: `|c_L(z) − c_L(w)| ≤ log ρ(u(z, w))/log L`. -/
theorem abs_cuspRamp_sub_le {L : ℝ} (hL : 1 < L) (z w : ℍ) :
    |cuspRamp L z - cuspRamp L w| ≤ Real.log (heightRatio (pairU z w)) / Real.log L := by
  have hlogL : 0 < Real.log L := Real.log_pos hL
  unfold cuspRamp logRamp
  refine (abs_min_sub_min_le_max (1 : ℝ) _ 1 _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (div_nonneg (Real.log_nonneg (one_le_heightRatio (pairU_nonneg z w))) hlogL.le) ?_
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs (α := ℝ) _ _ _).trans ?_
  rw [show (2 - Real.log (invHeight z) / Real.log L) - (2 - Real.log (invHeight w) / Real.log L) =
      -((Real.log (invHeight z) - Real.log (invHeight w)) / Real.log L) by ring, abs_neg, abs_div,
    abs_of_pos hlogL]
  exact div_le_div_of_nonneg_right (abs_log_invHeight_sub_le z w) hlogL.le

/-- **Pointwise splitting of the test function**:
`|f(a) − f(b)|² ≤ 2 c(a)² |ℓ(a) − ℓ(b)|²/N² + 2 (c(a) − c(b))²`. -/
theorem normSq_testFun_sub_le (N : ℕ) [NeZero N] (L : ℝ) (a b : ℍ) :
    ‖testFun N L a - testFun N L b‖ ^ 2 ≤
      2 * cuspRamp L a ^ 2 * ‖lambdaLog a - lambdaLog b‖ ^ 2 / (N : ℝ) ^ 2 +
        2 * (cuspRamp L a - cuspRamp L b) ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set ea := Complex.exp ((((lambdaLog a).im / N : ℝ) : ℂ) * Complex.I)
  set eb := Complex.exp ((((lambdaLog b).im / N : ℝ) : ℂ) * Complex.I)
  have heb : ‖eb‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hca := cuspRamp_nonneg L a
  have e : testFun N L a - testFun N L b =
      (cuspRamp L a : ℂ) * (ea - eb) + eb * ((cuspRamp L a - cuspRamp L b : ℝ) : ℂ) := by
    simp only [testFun, ea, eb]
    push_cast
    ring
  have hphase : ‖ea - eb‖ ≤ ‖lambdaLog a - lambdaLog b‖ / N := by
    refine (norm_phase_sub_le N _ _).trans (div_le_div_of_nonneg_right ?_ hN.le)
    rw [← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  have hnorm : ‖testFun N L a - testFun N L b‖ ≤
      cuspRamp L a * (‖lambdaLog a - lambdaLog b‖ / N) + |cuspRamp L a - cuspRamp L b| := by
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hca]
      exact mul_le_mul_of_nonneg_left hphase hca
    · rw [norm_mul, heb, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  refine hsq.trans ?_
  have hx : 0 ≤ cuspRamp L a * (‖lambdaLog a - lambdaLog b‖ / N) := by positivity
  have key : (cuspRamp L a * (‖lambdaLog a - lambdaLog b‖ / N) + |cuspRamp L a - cuspRamp L b|) ^ 2 ≤
      2 * (cuspRamp L a * (‖lambdaLog a - lambdaLog b‖ / N)) ^ 2 +
        2 * |cuspRamp L a - cuspRamp L b| ^ 2 := by
    nlinarith [sq_nonneg (cuspRamp L a * (‖lambdaLog a - lambdaLog b‖ / N) -
      |cuspRamp L a - cuspRamp L b|)]
  refine key.trans (le_of_eq ?_)
  rw [sq_abs]
  field_simp


/-- **The pair bound for the test field**: the phase part is a coset sum of `|Δℓ|²`, the cutoff part is
`2 [SL(2,ℤ):Γ_N] (log ρ(u)/log L)²`. -/
theorem norm_sq_testField_sub_le (N : ℕ) [NeZero N] {L : ℝ} (hL : 1 < L) (z w : ℍ) :
    ‖testField N L z - testField N L w‖ ^ 2 ≤
      2 * cuspRamp L z ^ 2 / (N : ℝ) ^ 2 * ∑ q : SL(2, ℤ) ⧸ windingSubgroup N,
        ‖lambdaLog ((Quotient.out q)⁻¹ • z : ℍ) - lambdaLog ((Quotient.out q)⁻¹ • w : ℍ)‖ ^ 2 +
      2 * Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) *
        (Real.log (heightRatio (pairU z w)) / Real.log L) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  calc ∑ q, ‖(testField N L z - testField N L w).ofLp q‖ ^ 2
      ≤ ∑ q : SL(2, ℤ) ⧸ windingSubgroup N,
          (2 * cuspRamp L z ^ 2 / (N : ℝ) ^ 2 * ‖lambdaLog ((Quotient.out q)⁻¹ • z : ℍ) -
            lambdaLog ((Quotient.out q)⁻¹ • w : ℍ)‖ ^ 2 +
          2 * (Real.log (heightRatio (pairU z w)) / Real.log L) ^ 2) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [WithLp.ofLp_sub, Pi.sub_apply]
        change ‖testField N L z q - testField N L w q‖ ^ 2 ≤ _
        rw [testField_apply, testField_apply]
        refine (normSq_testFun_sub_le N L _ _).trans ?_
        rw [cuspRamp_smul, cuspRamp_smul]
        have hc : (cuspRamp L z - cuspRamp L w) ^ 2 ≤
            (Real.log (heightRatio (pairU z w)) / Real.log L) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_cuspRamp_sub_le hL z w) 2
        have e : 2 * cuspRamp L z ^ 2 * ‖lambdaLog ((Quotient.out q)⁻¹ • z : ℍ) -
            lambdaLog ((Quotient.out q)⁻¹ • w : ℍ)‖ ^ 2 / (N : ℝ) ^ 2 =
            2 * cuspRamp L z ^ 2 / (N : ℝ) ^ 2 * ‖lambdaLog ((Quotient.out q)⁻¹ • z : ℍ) -
            lambdaLog ((Quotient.out q)⁻¹ • w : ℍ)‖ ^ 2 := by ring
        rw [e]
        linarith
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring


/-! ## Coset sums of invariant functions -/

/-- For a `Γ`-invariant `φ`, `φ(g_q⁻¹ z)` does not depend on the representative of `q`. -/
theorem apply_out_inv_smul_eq {Γ : Subgroup SL(2, ℤ)} {φ : ℍ → ℝ}
    (hφ : ∀ γ ∈ Γ, ∀ z, φ (γ • z) = φ z) (g : SL(2, ℤ)) (z : ℍ) :
    φ ((Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ))⁻¹ • z) = φ (g⁻¹ • z) := by
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ g
  have e : Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) = g * γ := hγ
  rw [e, mul_inv_rev, mul_smul]
  exact hφ _ (Γ.inv_mem γ.2) _

/-- **The coset sum of a `Γ`-invariant function is `SL(2,ℤ)`-invariant.** -/
theorem sum_out_inv_smul_smul {Γ : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ Γ)] {φ : ℍ → ℝ}
    (hφ : ∀ γ ∈ Γ, ∀ z, φ (γ • z) = φ z) (B : SL(2, ℤ)) (z : ℍ) :
    ∑ q : SL(2, ℤ) ⧸ Γ, φ ((Quotient.out q)⁻¹ • (B • z)) =
      ∑ q : SL(2, ℤ) ⧸ Γ, φ ((Quotient.out q)⁻¹ • z) := by
  rw [← Equiv.sum_comp (MulAction.toPerm B⁻¹ : Equiv.Perm (SL(2, ℤ) ⧸ Γ))
    (fun q => φ ((Quotient.out q)⁻¹ • z))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [MulAction.toPerm_apply]
  induction q using QuotientGroup.induction_on with
  | H g =>
    have h1 := apply_out_inv_smul_eq hφ g (B • z)
    have h2 := apply_out_inv_smul_eq hφ (B⁻¹ * g) z
    have e : (B⁻¹ • (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ)) = QuotientGroup.mk (B⁻¹ * g) := rfl
    rw [e, h1, h2, mul_inv_rev, inv_inv, mul_smul]

/-! ## The energy bound -/

theorem cuspRamp_eq_zero {L : ℝ} (hL : 1 < L) {z : ℍ} (hz : L ^ 2 ≤ invHeight z) :
    cuspRamp L z = 0 := by
  have hlogL : 0 < Real.log L := Real.log_pos hL
  rw [cuspRamp, logRamp]
  have h1 : 2 * Real.log L ≤ Real.log (invHeight z) := by
    rw [← Real.log_rpow (by linarith), show (L : ℝ) ^ (2 : ℝ) = L ^ 2 by norm_cast]
    exact Real.log_le_log (by positivity) hz
  have : 2 - Real.log (invHeight z) / Real.log L ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hlogL]
    linarith
  rw [max_eq_left this, min_eq_right zero_le_one]

/-- `c_L(z)² ≤ 1_{Y(z) < L²}`. -/
theorem cuspRamp_sq_le_indicator {L : ℝ} (hL : 1 < L) (z : ℍ) :
    cuspRamp L z ^ 2 ≤ {z : ℍ | invHeight z ≤ L ^ 2}.indicator (fun _ => (1 : ℝ)) z := by
  by_cases h : invHeight z ≤ L ^ 2
  · rw [Set.indicator_of_mem (show z ∈ {z : ℍ | invHeight z ≤ L ^ 2} from h)]
    have h0 := cuspRamp_nonneg L z
    have h1 := cuspRamp_le_one L z
    nlinarith
  · rw [Set.indicator_of_notMem (show z ∉ {z : ℍ | invHeight z ≤ L ^ 2} from h),
      cuspRamp_eq_zero hL (le_of_lt (not_le.1 h))]
    norm_num


variable (N : ℕ) [NeZero N]

/-- The coset sum `H(η) = Σ_q G(g_q⁻¹ η)` of an energy density along `Γ_N`. -/
def cosetEnergy (G : ℍ → ℝ) (η : ℍ) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ windingSubgroup N, G ((Quotient.out q)⁻¹ • η)

theorem cosetEnergy_nonneg {G : ℍ → ℝ} (hG0 : ∀ η, 0 ≤ G η) (η : ℍ) : 0 ≤ cosetEnergy N G η :=
  Finset.sum_nonneg fun _ _ => hG0 _

theorem continuous_cosetEnergy {G : ℍ → ℝ} (hGc : Continuous G) : Continuous (cosetEnergy N G) :=
  continuous_finsetSum _ fun _ _ => hGc.comp (continuous_smul_int _)

omit [NeZero N] in
/-- Change of variables: `∫ k(u(g⁻¹z, η)) H(η) dμ(η) = ∫ k(u(z, η)) H(g⁻¹η) dμ(η)`. -/
theorem integral_kernel_mul_smul_inv (g : SL(2, ℤ)) (z : ℍ) {k : ℝ → ℝ}
    {H : ℍ → ℝ} :
    ∫ η, k (pairU (g⁻¹ • z) η) * H η = ∫ η, k (pairU z η) * H (g⁻¹ • η) := by
  have hmp : MeasurePreserving (fun η : ℍ => g⁻¹ • η) volume volume := measurePreserving_smul _ _
  rw [← hmp.integral_comp (measurableEmbedding_const_smul _)
    (fun η => k (pairU (g⁻¹ • z) η) * H η)]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only
  rw [pairU_smul_int]


/-- **The Dirichlet energy of the test field.**  Given a local energy estimate for `ℓ = log λ` with a
`Γ_N`-invariant density `G` and bump `β = β_{R₂}`, the Dirichlet form of `F_{N,L}` is bounded by
`(2 C m_φ m_β / N²) ∫_𝒟 1_{Y ≤ ρ L²} Σ_q G(g_q⁻¹ ·) + 2 [SL(2,ℤ):Γ_N] (log ρ(R)/log L)² m_φ μ(𝒟)`. -/
theorem lintegral_dirichlet_testField_le (P : SmoothProfile) (hφ0 : ∀ u, 0 ≤ P.toFun u) {L : ℝ}
    (hL : 1 < L) {G : ℍ → ℝ} (hG0 : ∀ η, 0 ≤ G η) (hGc : Continuous G)
    (hGinv : ∀ γ ∈ windingSubgroup N, ∀ η, G (γ • η) = G η) {C R₂ : ℝ} (hC : 0 ≤ C)
    (hE : ∀ z w : ℍ, pairU z w ≤ P.radius →
      ‖lambdaLog w - lambdaLog z‖ ^ 2 ≤ C * ∫ η, bumpProfile R₂ (pairU z η) * G η) :
    ∫⁻ z in fd, ∫⁻ w, ENNReal.ofReal (P.toFun (pairU z w) * ‖testField N L z - testField N L w‖ ^ 2) ≤
      ENNReal.ofReal (2 * C * kernelMassR P.toFun * kernelMassR (bumpProfile R₂) / (N : ℝ) ^ 2) *
        (∫⁻ z in fd, ENNReal.ofReal ({η : ℍ | invHeight η ≤ heightRatio (R₂ + 1) * L ^ 2}.indicator
          (cosetEnergy N G) z)) +
      ENNReal.ofReal (2 * Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) *
        (Real.log (heightRatio P.radius) / Real.log L) ^ 2 * kernelMassR P.toFun) * volume fd := by
  set φ := P.toFun
  set R := P.radius
  set β := bumpProfile R₂
  set Q : ℝ := (Fintype.card (SL(2, ℤ) ⧸ windingSubgroup N) : ℝ)
  set K : ℝ := 2 * Q * (Real.log (heightRatio R) / Real.log L) ^ 2
  set T := heightRatio (R₂ + 1) * L ^ 2
  set g : ℍ → ℝ := {η : ℍ | invHeight η ≤ T}.indicator (cosetEnergy N G)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hK0 : 0 ≤ K := by positivity
  have hβ0 := bumpProfile_nonneg R₂
  have hβc := continuous_bumpProfile R₂
  have hβR := kernelSupport_bumpProfile R₂
  have hH0 := cosetEnergy_nonneg N hG0
  have hHc := continuous_cosetEnergy N hGc
  -- the energy integral at a point
  set I : ℍ → ℝ := fun z => ∫ η, β (pairU z η) * cosetEnergy N G η
  have hI0 : ∀ z, 0 ≤ I z := fun z => integral_nonneg fun η => mul_nonneg (hβ0 _) (hH0 _)
  have hIq : ∀ z, ∑ q : SL(2, ℤ) ⧸ windingSubgroup N,
      ∫ η, β (pairU ((Quotient.out q)⁻¹ • z) η) * G η = I z := by
    intro z
    simp_rw [integral_kernel_mul_smul_inv]
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Eventually.of_forall fun η => ?_)
      simp only [cosetEnergy, Finset.mul_sum]
    · intro q _
      simpa [smul_eq_mul] using integrable_kernel_mul hβc hβR z
        (hGc.comp (continuous_smul_int (Quotient.out q)⁻¹))
  -- Step 1: the pointwise bound
  have hpt : ∀ z w : ℍ, φ (pairU z w) * ‖testField N L z - testField N L w‖ ^ 2 ≤
      φ (pairU z w) * (2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K) := by
    intro z w
    by_cases h0 : φ (pairU z w) = 0
    · rw [h0, zero_mul, zero_mul]
    have huR : pairU z w ≤ R := by
      by_contra hlt
      push Not at hlt
      exact h0 (P.support _ (by rwa [abs_of_nonneg (pairU_nonneg _ _)]))
    refine mul_le_mul_of_nonneg_left ?_ (hφ0 _)
    refine (norm_sq_testField_sub_le N hL z w).trans ?_
    have hlog : (Real.log (heightRatio (pairU z w)) / Real.log L) ^ 2 ≤
        (Real.log (heightRatio R) / Real.log L) ^ 2 := by
      have hlogL : 0 < Real.log L := Real.log_pos hL
      have h1 : 0 ≤ Real.log (heightRatio (pairU z w)) :=
        Real.log_nonneg (one_le_heightRatio (pairU_nonneg _ _))
      have h2 : Real.log (heightRatio (pairU z w)) ≤ Real.log (heightRatio R) :=
        Real.log_le_log (by linarith [one_le_heightRatio (pairU_nonneg z w)])
          (heightRatio_mono (pairU_nonneg _ _) huR)
      exact pow_le_pow_left₀ (div_nonneg h1 hlogL.le) (div_le_div_of_nonneg_right h2 hlogL.le) 2
    have hsum : ∑ q : SL(2, ℤ) ⧸ windingSubgroup N,
        ‖lambdaLog ((Quotient.out q)⁻¹ • z : ℍ) - lambdaLog ((Quotient.out q)⁻¹ • w : ℍ)‖ ^ 2 ≤
          C * I z := by
      rw [← hIq, Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [norm_sub_rev]
      exact hE _ _ (by rw [pairU_smul_int]; exact huR)
    have hc : 0 ≤ 2 * cuspRamp L z ^ 2 / (N : ℝ) ^ 2 := by positivity
    calc 2 * cuspRamp L z ^ 2 / (N : ℝ) ^ 2 * ∑ q : SL(2, ℤ) ⧸ windingSubgroup N,
          ‖lambdaLog ((Quotient.out q)⁻¹ • z : ℍ) - lambdaLog ((Quotient.out q)⁻¹ • w : ℍ)‖ ^ 2 +
          2 * Q * (Real.log (heightRatio (pairU z w)) / Real.log L) ^ 2
        ≤ 2 * cuspRamp L z ^ 2 / (N : ℝ) ^ 2 * (C * I z) + K := by
          gcongr
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  -- Step 2: integrate in `w`
  have hmφ0 : 0 ≤ kernelMassR φ := integral_nonneg fun w => hφ0 _
  have hmφ : ∀ z : ℍ, ∫⁻ w, ENNReal.ofReal (φ (pairU z w)) = ENNReal.ofReal (kernelMassR φ) := by
    intro z
    have h := kernelMass_centre φ z
    simp_rw [abs_of_nonneg (hφ0 _)] at h
    rw [h, ← ENNReal.ofReal_toReal (kernelMass_lt_top P.radius_nonneg P.abs_le
      P.kernelSupport').ne, ppKernelMass_toReal P.contDiff.continuous hφ0 P.kernelSupport']
  have hw : ∀ z : ℍ, ∫⁻ w, ENNReal.ofReal (φ (pairU z w) *
      ‖testField N L z - testField N L w‖ ^ 2) ≤
      ENNReal.ofReal (kernelMassR φ * (2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K)) := by
    intro z
    have hX : 0 ≤ 2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K := by
      have := hI0 z
      positivity
    calc ∫⁻ w, ENNReal.ofReal (φ (pairU z w) * ‖testField N L z - testField N L w‖ ^ 2)
        ≤ ∫⁻ w, ENNReal.ofReal (φ (pairU z w)) *
            ENNReal.ofReal (2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K) := by
          refine lintegral_mono fun w => ?_
          rw [← ENNReal.ofReal_mul (hφ0 _)]
          exact ENNReal.ofReal_le_ofReal (hpt z w)
      _ = _ := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hmφ, ← ENNReal.ofReal_mul hmφ0]
  -- Step 3–4: the cutoff and the height window
  have hgm : Measurable g := by
    refine Measurable.indicator hHc.measurable ?_
    exact (isClosed_le continuous_invHeight continuous_const).measurableSet
  have hginv : ∀ (B : SL(2, ℤ)) η, g (B • η) = g η := by
    intro B η
    simp only [g, Set.indicator, Set.mem_setOf_eq, invHeight_smul]
    split_ifs
    · exact sum_out_inv_smul_smul hGinv B η
    · rfl
  have hg0 : ∀ η, 0 ≤ g η := fun η => Set.indicator_nonneg (fun η _ => hH0 η) η
  have hloc : ∀ z : ℍ, ENNReal.ofReal (kernelMassR φ * (2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K)) ≤
      ENNReal.ofReal (2 * C * kernelMassR φ / (N : ℝ) ^ 2) *
        (∫⁻ η, ENNReal.ofReal (β (pairU z η) * g η)) + ENNReal.ofReal (K * kernelMassR φ) := by
    intro z
    have hcI : cuspRamp L z ^ 2 * I z ≤
        {z : ℍ | invHeight z ≤ L ^ 2}.indicator (fun _ => (1 : ℝ)) z * I z :=
      mul_le_mul_of_nonneg_right (cuspRamp_sq_le_indicator hL z) (hI0 z)
    have hind : ENNReal.ofReal ({z : ℍ | invHeight z ≤ L ^ 2}.indicator (fun _ => (1 : ℝ)) z * I z) ≤
        ∫⁻ η, ENNReal.ofReal (β (pairU z η) * g η) := by
      by_cases hz : invHeight z ≤ L ^ 2
      · rw [Set.indicator_of_mem (show z ∈ {z : ℍ | invHeight z ≤ L ^ 2} from hz), one_mul]
        have hint : Integrable (fun η => β (pairU z η) * cosetEnergy N G η) := by
          simpa [smul_eq_mul] using integrable_kernel_mul hβc hβR z hHc
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun η => mul_nonneg (hβ0 _) (hH0 _))]
        refine lintegral_mono fun η => ENNReal.ofReal_le_ofReal ?_
        by_cases hβz : β (pairU z η) = 0
        · rw [hβz, zero_mul, zero_mul]
        have hu : pairU z η ≤ R₂ + 1 := by
          by_contra hlt
          push Not at hlt
          exact hβz (hβR _ hlt)
        have hYη : invHeight η ≤ T := by
          have h1 := invHeight_le_rho_mul η z
          rw [pairU_comm] at h1
          have h2 : heightRatio (pairU z η) ≤ heightRatio (R₂ + 1) :=
            heightRatio_mono (pairU_nonneg _ _) hu
          have h3 : 0 ≤ heightRatio (pairU z η) := by
            linarith [one_le_heightRatio (pairU_nonneg z η)]
          calc invHeight η ≤ heightRatio (pairU z η) * invHeight z := h1
            _ ≤ heightRatio (R₂ + 1) * L ^ 2 :=
                mul_le_mul h2 hz (invHeight_pos z).le (by linarith)
        rw [show g η = cosetEnergy N G η from
          Set.indicator_of_mem (show η ∈ {η : ℍ | invHeight η ≤ T} from hYη) _]
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℍ | invHeight z ≤ L ^ 2} from hz), zero_mul,
          ENNReal.ofReal_zero]
        exact bot_le
    have hsplit : kernelMassR φ * (2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K) ≤
        2 * C * kernelMassR φ / (N : ℝ) ^ 2 *
          ({z : ℍ | invHeight z ≤ L ^ 2}.indicator (fun _ => (1 : ℝ)) z * I z) +
        K * kernelMassR φ := by
      have h2 : 0 ≤ 2 * C * kernelMassR φ / (N : ℝ) ^ 2 := by positivity
      calc kernelMassR φ * (2 * cuspRamp L z ^ 2 * C / (N : ℝ) ^ 2 * I z + K)
          = 2 * C * kernelMassR φ / (N : ℝ) ^ 2 * (cuspRamp L z ^ 2 * I z) + K * kernelMassR φ := by
            ring
        _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hcI h2) _
    have hind0 : 0 ≤ {z : ℍ | invHeight z ≤ L ^ 2}.indicator (fun _ => (1 : ℝ)) z * I z :=
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hI0 z)
    refine (ENNReal.ofReal_le_ofReal hsplit).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hind0) (mul_nonneg hK0 hmφ0),
      ENNReal.ofReal_mul (by positivity)]
    exact add_le_add_left (by gcongr) _
  -- Step 5: integrate over the cell
  calc ∫⁻ z in fd, ∫⁻ w, ENNReal.ofReal (φ (pairU z w) * ‖testField N L z - testField N L w‖ ^ 2)
      ≤ ∫⁻ z in fd, (ENNReal.ofReal (2 * C * kernelMassR φ / (N : ℝ) ^ 2) *
          (∫⁻ η, ENNReal.ofReal (β (pairU z η) * g η)) + ENNReal.ofReal (K * kernelMassR φ)) :=
        lintegral_mono fun z => (hw z).trans (hloc z)
    _ = ENNReal.ofReal (2 * C * kernelMassR φ / (N : ℝ) ^ 2) *
          (∫⁻ z in fd, ∫⁻ η, ENNReal.ofReal (β (pairU z η) * g η)) +
        ENNReal.ofReal (K * kernelMassR φ) * volume fd := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const]
    _ = _ := by
        rw [lintegral_fd_kernel_mul_invariant hβc hβR hβ0 hgm hginv, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 3
        ring


/-! ## Coset towers -/

omit [NeZero N] in
/-- **Coset sums along a tower `H ≤ K`**: for a `K`-invariant `φ`,
`Σ_{q ∈ G/H} φ(g_q⁻¹ z) = [K : H] Σ_{p ∈ G/K} φ(g_p⁻¹ z)`. -/
theorem sum_out_inv_smul_tower {H K : Subgroup SL(2, ℤ)} (hHK : H ≤ K) [Fintype (SL(2, ℤ) ⧸ H)]
    [Fintype (SL(2, ℤ) ⧸ K)] [Fintype (K ⧸ H.subgroupOf K)] {φ : ℍ → ℝ}
    (hφ : ∀ γ ∈ K, ∀ z, φ (γ • z) = φ z) (z : ℍ) :
    ∑ q : SL(2, ℤ) ⧸ H, φ ((Quotient.out q)⁻¹ • z) =
      Fintype.card (K ⧸ H.subgroupOf K) * ∑ p : SL(2, ℤ) ⧸ K, φ ((Quotient.out p)⁻¹ • z) := by
  set e := Subgroup.quotientEquivProdOfLE hHK
  have hproj : ∀ q : SL(2, ℤ) ⧸ H, φ ((Quotient.out q)⁻¹ • z) =
      φ ((Quotient.out (e q).1)⁻¹ • z) := by
    intro q
    have h1 : (e q).1 = (QuotientGroup.mk (Quotient.out q) : SL(2, ℤ) ⧸ K) := by
      rw [Subgroup.quotientEquivProdOfLE_apply]
      conv_lhs => rw [← Quotient.out_eq' q]
      rfl
    rw [h1, apply_out_inv_smul_eq hφ]
  simp_rw [hproj]
  rw [← Equiv.sum_comp e.symm (fun x => φ ((Quotient.out (e x).1)⁻¹ • z))]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

end

end GaloisForLFunctions.RHTower.NonvacuousWitness
