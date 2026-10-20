import GaloisForLFunctions.ArithmeticCriticalityTheory.ArchimedeanZTypeLaw

/-!
# The full zero form: the Markov form modulo the whole theta span

For a real test `F` put

    Ẑ(F) = markovEnergy(F) − 2 (∫ F sinh(x/2))² + 2 (∫ F cosh(x/2))²       (`fullZeroForm`).

On the translates of `Φ` the Markov form is the Lorentzian form `(B² − A²)/2` in the pole
coordinates `A = 2∫M cosh(x/2)`, `B = 2∫M sinh(x/2)`; `Ẑ` subtracts exactly this form. Then:

* **Radical** (`tendsto_fullZeroForm_add_translatePlateau`). For every finite combination of
  translates `ω = Σ α_j τ_{b_j}` and every test `v ∈ C²_c`, `Ẑ(Φ(ω u_L + v)) → Ẑ(Φ v)`: the whole
  theta span, both parities and every pole coefficient, is invisible to `Ẑ`.
* **RH** (`riemannHypothesis_iff_forall_fullZeroForm_nonneg`). RH holds iff `Ẑ ≥ 0` on every real
  `C²_c` test. On odd tests `Ẑ` is the odd zero form; on even tests the cosh moment is cancelled by
  a multiple `λ_L Φ u_L` of the truncated kernel, which `Ẑ` does not see, and the cancelled test is
  nonnegative by the primitive-hyperplane criterion.

So the explicit formula's pole part is, inside the theory, the Lorentz form of the theta span, and
RH is positivity of the Markov form on the quotient of all tests by the theta span.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The even pole moment `∫ F(x) cosh(x/2) dx`. -/
def evenPoleMoment (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.cosh (x / 2)

/-- The full zero form `markovEnergy(F) − 2 (∫F sinh(x/2))² + 2 (∫F cosh(x/2))²`. -/
def fullZeroForm (F : ℝ → ℝ) : ℝ :=
  markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2 + 2 * evenPoleMoment F ^ 2

/-! ### Homogeneity of the generator calculus -/

theorem twoSidedGenerator_const_mul (c : ℝ) (z : ℝ → ℝ) (x : ℝ) :
    twoSidedGenerator (fun y => c * z y) x = c * twoSidedGenerator z x := by
  have hpt : ∀ t, twoSidedShiftGenerator (fun y => c * z y) t x =
      c * twoSidedShiftGenerator z t x := fun t => by
    unfold twoSidedShiftGenerator
    ring
  unfold twoSidedGenerator
  simp_rw [hpt]
  rw [mul_add, ← integral_const_mul, ← tsum_mul_left]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  · exact tsum_congr fun n => by ring

theorem markovEnergy_phiDoob_const_mul {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) (c : ℝ) :
    markovEnergy (fun x => (phiDoobTest (fun y => c * z y) x : ℂ)) =
      c ^ 2 * markovEnergy (fun x => (phiDoobTest z x : ℂ)) := by
  rw [markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential
      (contDiff_const.mul hz) (hzc.mul_left),
    markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential hz hzc,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [twoSidedGenerator_const_mul]
  ring

/-! ### Moments -/

theorem integrable_mul_of_compactSupport {F h : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hh : Continuous h) : Integrable fun x => F x * h x :=
  (hF.mul hh).integrable_of_hasCompactSupport hFc.mul_right

theorem oddPoleMoment_add {F G : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    oddPoleMoment (fun x => F x + G x) = oddPoleMoment F + oddPoleMoment G := by
  have hs : Continuous fun x : ℝ => Real.sinh (x / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  unfold oddPoleMoment
  rw [← integral_add (integrable_mul_of_compactSupport hF hFc hs)
    (integrable_mul_of_compactSupport hG hGc hs)]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

theorem evenPoleMoment_add {F G : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    evenPoleMoment (fun x => F x + G x) = evenPoleMoment F + evenPoleMoment G := by
  have hc : Continuous fun x : ℝ => Real.cosh (x / 2) :=
    Real.continuous_cosh.comp (continuous_id.div_const 2)
  unfold evenPoleMoment
  rw [← integral_add (integrable_mul_of_compactSupport hF hFc hc)
    (integrable_mul_of_compactSupport hG hGc hc)]
  exact integral_congr_ae (Eventually.of_forall fun x => by ring)

theorem phiDoobTest_add' (f g : ℝ → ℝ) :
    phiDoobTest (fun y => f y + g y) = fun x => phiDoobTest f x + phiDoobTest g x :=
  funext (phiDoobTest_add f g)

/-- The pole moments of the plateau truncation `M u_L` converge at rate `e^{−8L}` to the full
moments, for every `M` with `|M| ≤ C e^{−24|·|}` and every `h` with `|h| ≤ e^{8|·|}`. -/
theorem abs_integral_mul_smoothPlateau_sub_le {M h : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hMc : Continuous M) (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) (hhc : Continuous h)
    (hh : ∀ y, |h y| ≤ Real.exp (8 * |y|)) (hint : Integrable fun x => M x * h x) (L : ℝ) :
    |(∫ x, M x * smoothPlateau L x * h x) - ∫ x, M x * h x| ≤
      C * (∫ x : ℝ, Real.exp (-(8 * |x|))) * Real.exp (-(8 * L)) := by
  have hA : Integrable fun x => M x * smoothPlateau L x * h x :=
    Continuous.integrable_of_hasCompactSupport ((hMc.mul (contDiff_smoothPlateau L).continuous).mul hhc)
      ((hasCompactSupport_smoothPlateau L).mul_left.mul_right)
  rw [← integral_sub hA hint, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_exp_neg_eight_mul_abs.const_mul
    (C * 1 * Real.exp (-(8 * L)))) (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, show M x * smoothPlateau L x * h x - M x * h x =
      (smoothPlateau L x - 1) * (M x * h x) by ring]
    have h1 := abs_smoothPlateau_sq_sub_one_mul_le_of_growth hC0 zero_le_one hM
      (fun y => by rw [one_mul]; exact hh y) L x
    rw [abs_mul] at h1 ⊢
    exact (mul_le_mul_of_nonneg_right (abs_smoothPlateau_sub_one_le_abs_sq_sub_one L x)
      (abs_nonneg _)).trans h1
  · rw [integral_const_mul]
    ring

theorem abs_sinh_half_le_exp_eight (y : ℝ) : |Real.sinh (y / 2)| ≤ Real.exp (8 * |y|) :=
  (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight y)

theorem abs_cosh_half_le_exp_eight (y : ℝ) : |Real.cosh (y / 2)| ≤ Real.exp (8 * |y|) := by
  rw [abs_of_pos (Real.cosh_pos _)]
  exact (cosh_le_exp_abs _).trans (exp_abs_half_le_exp_eight y)

theorem tendsto_const_mul_exp_neg_eight (K : ℝ) :
    Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
  have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
  simpa [Function.comp_def, neg_mul] using this

theorem tendsto_of_abs_sub_le {f : ℝ → ℝ} {l K : ℝ} (h : ∀ᶠ L in atTop, |f L - l| ≤
    K * Real.exp (-(8 * L))) : Tendsto f atTop (𝓝 l) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (h.mono fun L hL => by rwa [Real.norm_eq_abs]) (tendsto_const_mul_exp_neg_eight K))

/-! ### The radical of the full zero form -/

variable {ι : Type*}

theorem translateSpan_mul_smoothPlateau_moments (s : Finset ι) (α b : ι → ℝ) :
    Tendsto (fun L => oddPoleMoment (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y)))
        atTop (𝓝 (translateSinhCoefficient s α b / 2)) ∧
      Tendsto (fun L => evenPoleMoment (phiDoobTest
        (fun y => translateSpan s α b y * smoothPlateau L y))) atTop
        (𝓝 (translateCoshCoefficient s α b / 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le s α b
  set M : ℝ → ℝ := fun x => riemannKernelReal x * translateSpan s α b x with hM_def
  have hMc : Continuous M := continuous_riemannKernelReal.mul (contDiff_translateSpan s α b).continuous
  have hrw : ∀ L, phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y) =
      fun x => M x * smoothPlateau L x := fun L => funext fun x => by
    unfold phiDoobTest
    simp only [hM_def]
    ring
  have hsinh : (∫ x, M x * Real.sinh (x / 2)) = translateSinhCoefficient s α b / 2 := by
    have e : (fun x => M x * Real.sinh (x / 2)) = fun x => ∑ j ∈ s, α j *
        (riemannKernelReal (x - b j) * Real.sinh (x / 2)) := by
      funext x
      simp only [hM_def]
      rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j _ =>
      (integrable_riemannKernelReal_sub_mul_sinh_half (b j)).const_mul _]
    unfold translateSinhCoefficient
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by
      rw [integral_const_mul, integral_riemannKernelReal_sub_mul_sinh_half]; ring
  have hcosh : (∫ x, M x * Real.cosh (x / 2)) = translateCoshCoefficient s α b / 2 := by
    have e : (fun x => M x * Real.cosh (x / 2)) = fun x => ∑ j ∈ s, α j *
        (riemannKernelReal (x - b j) * Real.cosh (x / 2)) := by
      funext x
      simp only [hM_def]
      rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j _ =>
      (integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul _]
    unfold translateCoshCoefficient
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by
      rw [integral_const_mul, integral_riemannKernelReal_sub_mul_cosh_half]; ring
  have hintS : Integrable fun x => M x * Real.sinh (x / 2) := by
    have e : (fun x => M x * Real.sinh (x / 2)) = fun x => ∑ j ∈ s, α j *
        (riemannKernelReal (x - b j) * Real.sinh (x / 2)) := by
      funext x
      simp only [hM_def]
      rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum s fun j _ =>
      (integrable_riemannKernelReal_sub_mul_sinh_half (b j)).const_mul _
  have hintC : Integrable fun x => M x * Real.cosh (x / 2) := by
    have e : (fun x => M x * Real.cosh (x / 2)) = fun x => ∑ j ∈ s, α j *
        (riemannKernelReal (x - b j) * Real.cosh (x / 2)) := by
      funext x
      simp only [hM_def]
      rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum s fun j _ =>
      (integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul _
  constructor
  · refine tendsto_of_abs_sub_le (K := C * ∫ x : ℝ, Real.exp (-(8 * |x|)))
      (Eventually.of_forall fun L => ?_)
    rw [hrw, oddPoleMoment, ← hsinh]
    exact abs_integral_mul_smoothPlateau_sub_le hC0 hMc hC
      (Real.continuous_sinh.comp (continuous_id.div_const 2)) abs_sinh_half_le_exp_eight hintS L
  · refine tendsto_of_abs_sub_le (K := C * ∫ x : ℝ, Real.exp (-(8 * |x|)))
      (Eventually.of_forall fun L => ?_)
    rw [hrw, evenPoleMoment, ← hcosh]
    exact abs_integral_mul_smoothPlateau_sub_le hC0 hMc hC
      (Real.continuous_cosh.comp (continuous_id.div_const 2)) abs_cosh_half_le_exp_eight hintC L

/-- **The theta span is the radical of the full zero form.** For every finite combination of
translates `ω` and every `v ∈ C²_c(ℝ)`, `Ẑ(Φ(ω u_L + v)) → Ẑ(Φ v)`. -/
theorem tendsto_fullZeroForm_add_translatePlateau (s : Finset ι) (α b : ι → ℝ) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    Tendsto (fun L => fullZeroForm (phiDoobTest
        (fun y => translateSpan s α b y * smoothPlateau L y + v y))) atTop
      (𝓝 (fullZeroForm (phiDoobTest v))) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le s α b
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hvc
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_translatePlateau_sub_le s α b
  obtain ⟨hsN, hcN⟩ := translateSpan_mul_smoothPlateau_moments s α b
  set A := translateCoshCoefficient s α b
  set B := translateSinhCoefficient s α b
  obtain ⟨sv, hsv⟩ : ∃ sv, sv = oddPoleMoment (phiDoobTest v) := ⟨_, rfl⟩
  obtain ⟨cv, hcv⟩ : ∃ cv, cv = evenPoleMoment (phiDoobTest v) := ⟨_, rfl⟩
  have hω := contDiff_translateSpan s α b
  -- the pairing
  have hpair : Tendsto (fun L => ∫ x, v x * (twoSidedGenerator
      (fun y => translateSpan s α b y * smoothPlateau L y) x -
        riemannKernelReal x * Real.cosh (x / 2) * (translateSpan s α b x * smoothPlateau L x)))
      atTop (𝓝 (-A * cv + B * sv)) := by
    have hval : (∫ x, v x * (riemannKernelReal x * translateSource s α b x)) = -A * cv + B * sv := by
      have hi1 : Integrable fun x => phiDoobTest v x * Real.cosh (x / 2) :=
        integrable_mul_of_compactSupport (continuous_riemannKernelReal.mul hv.continuous)
          hvc.mul_left (Real.continuous_cosh.comp (continuous_id.div_const 2))
      have hi2 : Integrable fun x => phiDoobTest v x * Real.sinh (x / 2) :=
        integrable_mul_of_compactSupport (continuous_riemannKernelReal.mul hv.continuous)
          hvc.mul_left (Real.continuous_sinh.comp (continuous_id.div_const 2))
      have e : (fun x => v x * (riemannKernelReal x * translateSource s α b x)) =
          fun x => -A * (phiDoobTest v x * Real.cosh (x / 2)) +
            B * (phiDoobTest v x * Real.sinh (x / 2)) := by
        funext x
        unfold translateSource phiDoobTest
        ring
      rw [e, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
        integral_const_mul, hsv, hcv]
      rfl
    rw [← hval]
    refine tendsto_of_abs_sub_le (K := riemannKernelReal 0 * C * (2 * Λ * archFirstMoment +
      2 * Real.exp (8 * R) * primeEighthMoment) * (∫ x, |v x|)) ?_
    filter_upwards [eventually_ge_atTop R] with L hRL
    exact abs_integral_mul_generator_plateau_sub_le hω hC0 hC hΛ0 hΛ
      (integrableOn_archLevy_twoSidedShiftGenerator_translateSpan s α b)
      (summable_atom_twoSidedShiftGenerator_translateSpan s α b)
      (twoSidedGenerator_translateSpan_sub_potential s α b) (continuous_translateSource s α b)
      hv hvc hsupp hRL
  have hQN : Tendsto (fun L => markovEnergy (fun x =>
      (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y) x : ℂ))) atTop
      (𝓝 ((B ^ 2 - A ^ 2) / 2)) :=
    tendsto_of_abs_sub_le (Eventually.of_forall fun L => hK L)
  -- the identity for each `L`
  have hid : ∀ L, fullZeroForm (phiDoobTest
      (fun y => translateSpan s α b y * smoothPlateau L y + v y)) =
      markovEnergy (fun x => (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y) x
        : ℂ)) + markovEnergy (fun x => (phiDoobTest v x : ℂ)) +
        2 * (∫ x, v x * (twoSidedGenerator (fun y => translateSpan s α b y * smoothPlateau L y) x -
          riemannKernelReal x * Real.cosh (x / 2) * (translateSpan s α b x * smoothPlateau L x))) -
        2 * (oddPoleMoment (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y)) +
          sv) ^ 2 +
        2 * (evenPoleMoment (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y)) +
          cv) ^ 2 := fun L => by
    have hz : ContDiff ℝ 2 fun y => translateSpan s α b y * smoothPlateau L y :=
      hω.mul (contDiff_smoothPlateau L)
    have hzc : HasCompactSupport fun y => translateSpan s α b y * smoothPlateau L y :=
      (hasCompactSupport_smoothPlateau L).mul_left
    have hΦz : Continuous (phiDoobTest fun y => translateSpan s α b y * smoothPlateau L y) :=
      continuous_riemannKernelReal.mul hz.continuous
    have hΦv : Continuous (phiDoobTest v) := continuous_riemannKernelReal.mul hv.continuous
    unfold fullZeroForm
    rw [markovEnergy_phiDoob_add hz hzc hv hvc, phiDoobTest_add',
      oddPoleMoment_add hΦz hzc.mul_left hΦv hvc.mul_left,
      evenPoleMoment_add hΦz hzc.mul_left hΦv hvc.mul_left, hsv, hcv]
  simp_rw [hid]
  have hc1 : Tendsto (fun _ : ℝ => markovEnergy (fun x => (phiDoobTest v x : ℂ))) atTop
      (𝓝 (markovEnergy (fun x => (phiDoobTest v x : ℂ)))) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℝ => sv) atTop (𝓝 sv) := tendsto_const_nhds
  have hc3 : Tendsto (fun _ : ℝ => cv) atTop (𝓝 cv) := tendsto_const_nhds
  have hlim := ((((hQN.add hc1).add (hpair.const_mul 2)).sub
    (((hsN.add hc2).pow 2).const_mul 2)).add (((hcN.add hc3).pow 2).const_mul 2))
  convert hlim using 2
  unfold fullZeroForm
  rw [← hsv, ← hcv]
  ring

/-! ### RH as positivity of the full zero form -/

theorem evenPoleMoment_eq_zero_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) :
    evenPoleMoment F = 0 :=
  integral_mul_cosh_half_of_odd hodd

theorem oddPoleMoment_eq_zero_of_even {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) :
    oddPoleMoment F = 0 := by
  unfold oddPoleMoment
  have h : (∫ x, F x * Real.sinh (x / 2)) = -∫ x, F x * Real.sinh (x / 2) := by
    rw [← integral_neg, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [heven, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]
    ring
  linarith

/-- The cosh moment of the truncated kernel converges to `1/2`. -/
theorem tendsto_evenPoleMoment_phiDoob_smoothPlateau :
    Tendsto (fun L => evenPoleMoment (phiDoobTest (smoothPlateau L))) atTop (𝓝 (1 / 2)) := by
  have h := (translateSpan_mul_smoothPlateau_moments (Finset.univ : Finset (Fin 1))
    (fun _ => 1) (fun _ => 0)).2
  have hval : translateCoshCoefficient (Finset.univ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) / 2 =
      1 / 2 := by simp [translateCoshCoefficient]
  have hfun : ∀ L, (fun y => translateSpan (Finset.univ : Finset (Fin 1)) (fun _ => 1)
      (fun _ => 0) y * smoothPlateau L y) = smoothPlateau L := fun L => by
    funext y
    simp [translateSpan, translateGroundState_zero]
  simp_rw [hfun, hval] at h
  exact h

/-- The truncated kernel pairs with a test through its cosh moment:
`∫ v (𝓛_D u_L − ρ u_L) → −∫ Φv cosh(x/2)`. -/
theorem tendsto_pairing_smoothPlateau {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    Tendsto (fun L => ∫ x, v x * (twoSidedGenerator (smoothPlateau L) x -
        riemannKernelReal x * Real.cosh (x / 2) * smoothPlateau L x)) atTop
      (𝓝 (-evenPoleMoment (phiDoobTest v))) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  obtain ⟨R, -, hsupp⟩ := exists_support_radius hvc
  have hτ : ∀ L, (fun y => translateGroundState 0 y * smoothPlateau L y) = smoothPlateau L :=
    fun L => funext fun y => by rw [translateGroundState_zero, one_mul]
  have hM : ∀ y, |riemannKernelReal y * translateGroundState 0 y| ≤ C * Real.exp (-(24 * |y|)) :=
    fun y => by
      rw [riemannKernelReal_mul_translateGroundState, sub_zero,
        abs_of_pos (riemannKernelReal_pos y)]
      exact hC y
  have hval : (∫ x, v x * (riemannKernelReal x * -Real.cosh ((x - 0) / 2))) =
      -evenPoleMoment (phiDoobTest v) := by
    unfold evenPoleMoment phiDoobTest
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_zero]
    ring
  rw [← hval]
  refine tendsto_of_abs_sub_le (K := riemannKernelReal 0 * C * (2 * Λ * archFirstMoment +
    2 * Real.exp (8 * R) * primeEighthMoment) * (∫ x, |v x|)) ?_
  filter_upwards [eventually_ge_atTop R] with L hRL
  have h := abs_integral_mul_generator_plateau_sub_le (g := fun x => -Real.cosh ((x - 0) / 2))
    (contDiff_translateGroundState 0) hC0 hM hΛ0 hΛ
    (integrableOn_archLevy_twoSidedShiftGenerator_translateGroundState 0)
    (summable_atom_twoSidedShiftGenerator_translateGroundState 0)
    (twoSidedGenerator_translateGroundState_sub_potential 0)
    ((Real.continuous_cosh.comp ((continuous_id.sub continuous_const).div_const 2)).neg)
    hv hvc hsupp hRL
  rw [hτ L] at h
  simpa only [translateGroundState_zero, one_mul] using h

/-- **RH is positivity of the full zero form.** RH holds iff `Ẑ(Φ v) ≥ 0` for every
`v ∈ C²_c(ℝ)`. -/
theorem riemannHypothesis_iff_forall_fullZeroForm_nonneg :
    RiemannHypothesis ↔ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v →
      0 ≤ fullZeroForm (phiDoobTest v) := by
  constructor
  · intro hRH v hv hvc
    set F := phiDoobTest v with hF_def
    have hFd : ContDiff ℝ 2 F := contDiff_phiDoobTest hv
    have hFc : HasCompactSupport F := hasCompactSupport_phiDoobTest hvc
    -- the odd part
    have hodd : 0 ≤ zeroForm (oddPartReal F) := by
      have h := (riemannHypothesis_iff_forall_odd_zeroForm_nonneg.mp hRH)
        (phiDoobInv (oddPartReal F)) (contDiff_phiDoobInv (contDiff_oddPartReal hFd))
        (hasCompactSupport_phiDoobInv (hasCompactSupport_oddPartReal hFc))
        (phiDoobInv_odd (oddPartReal_neg F))
      rwa [show phiDoobTest (phiDoobInv (oddPartReal F)) = oddPartReal F from
        funext (phiDoobTest_phiDoobInv _)] at h
    -- the even part
    set w := phiDoobInv (evenPartReal F) with hw_def
    have hwd : ContDiff ℝ 2 w := contDiff_phiDoobInv (contDiff_evenPartReal hFd)
    have hwc : HasCompactSupport w := hasCompactSupport_phiDoobInv (hasCompactSupport_evenPartReal hFc)
    have hΦw : phiDoobTest w = evenPartReal F := funext (phiDoobTest_phiDoobInv _)
    set ce := evenPoleMoment (evenPartReal F) with hce
    have hcL := tendsto_evenPoleMoment_phiDoob_smoothPlateau
    have hQL := tendsto_markovEnergy_phiDoob_smoothPlateau
    have hPL := tendsto_pairing_smoothPlateau hwd hwc
    rw [hΦw] at hPL
    set lamL : ℝ → ℝ := fun L => -ce / evenPoleMoment (phiDoobTest (smoothPlateau L)) with hlam
    have hlamlim : Tendsto lamL atTop (𝓝 (-ce / (1 / 2))) :=
      tendsto_const_nhds.div hcL (by norm_num)
    have hGL : ∀ᶠ L in atTop, 0 ≤ markovEnergy (fun x =>
        (phiDoobTest (fun y => lamL L * smoothPlateau L y + w y) x : ℂ)) := by
      filter_upwards [hcL.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
        with L hcpos
      have hz : ContDiff ℝ 2 fun y => lamL L * smoothPlateau L y + w y :=
        (contDiff_const.mul (contDiff_smoothPlateau L)).add hwd
      have hzc : HasCompactSupport fun y => lamL L * smoothPlateau L y + w y :=
        ((hasCompactSupport_smoothPlateau L).mul_left).add hwc
      refine (riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg.mp hRH) _
        (contDiff_phiDoobTest hz) (hasCompactSupport_phiDoobTest hzc) ?_
      have hm := evenPoleMoment_add (F := phiDoobTest fun y => lamL L * smoothPlateau L y)
        (G := phiDoobTest w)
        (continuous_riemannKernelReal.mul (continuous_const.mul (contDiff_smoothPlateau L).continuous))
        (hasCompactSupport_phiDoobTest (hasCompactSupport_smoothPlateau L).mul_left)
        (continuous_riemannKernelReal.mul hwd.continuous) (hasCompactSupport_phiDoobTest hwc)
      have hlin : evenPoleMoment (phiDoobTest fun y => lamL L * smoothPlateau L y) =
          lamL L * evenPoleMoment (phiDoobTest (smoothPlateau L)) := by
        unfold evenPoleMoment phiDoobTest
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      have hsum : evenPoleMoment (phiDoobTest fun y => lamL L * smoothPlateau L y + w y) = 0 := by
        rw [phiDoobTest_add', hm, hlin, hΦw, hlam]
        simp only
        field_simp
        ring
      exact hsum
    have hexp : ∀ L, markovEnergy (fun x =>
        (phiDoobTest (fun y => lamL L * smoothPlateau L y + w y) x : ℂ)) =
        lamL L ^ 2 * markovEnergy (fun x => (phiDoobTest (smoothPlateau L) x : ℂ)) +
          markovEnergy (fun x => (evenPartReal F x : ℂ)) +
          2 * (lamL L * ∫ x, w x * (twoSidedGenerator (smoothPlateau L) x -
            riemannKernelReal x * Real.cosh (x / 2) * smoothPlateau L x)) := fun L => by
      have hz : ContDiff ℝ 2 fun y => lamL L * smoothPlateau L y :=
        contDiff_const.mul (contDiff_smoothPlateau L)
      have hzc : HasCompactSupport fun y => lamL L * smoothPlateau L y :=
        (hasCompactSupport_smoothPlateau L).mul_left
      rw [markovEnergy_phiDoob_add hz hzc hwd hwc,
        markovEnergy_phiDoob_const_mul (contDiff_smoothPlateau L) (hasCompactSupport_smoothPlateau L),
        hΦw]
      congr 2
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [twoSidedGenerator_const_mul]
      ring
    have hlim : Tendsto (fun L => markovEnergy (fun x =>
        (phiDoobTest (fun y => lamL L * smoothPlateau L y + w y) x : ℂ))) atTop
        (𝓝 ((-ce / (1 / 2)) ^ 2 * -(1 / 2) + markovEnergy (fun x => (evenPartReal F x : ℂ)) +
          2 * ((-ce / (1 / 2)) * -ce))) := by
      simp_rw [hexp]
      exact ((hlamlim.pow 2).mul hQL |>.add tendsto_const_nhds).add
        ((hlamlim.mul hPL).const_mul 2)
    have heven : 0 ≤ markovEnergy (fun x => (evenPartReal F x : ℂ)) + 2 * ce ^ 2 := by
      have := ge_of_tendsto hlim hGL
      nlinarith
    -- assembly
    have hsplit : fullZeroForm F = zeroForm (oddPartReal F) +
        (markovEnergy (fun x => (evenPartReal F x : ℂ)) + 2 * ce ^ 2) := by
      have hFe : Continuous (evenPartReal F) := (contDiff_evenPartReal hFd).continuous
      have hFo : Continuous (oddPartReal F) := (contDiff_oddPartReal hFd).continuous
      have hFeq : F = fun x => evenPartReal F x + oddPartReal F x :=
        funext fun x => (evenPartReal_add_oddPartReal F x).symm
      have hs : oddPoleMoment F = oddPoleMoment (oddPartReal F) := by
        conv_lhs => rw [hFeq]
        rw [oddPoleMoment_add hFe (hasCompactSupport_evenPartReal hFc) hFo
          (hasCompactSupport_oddPartReal hFc), oddPoleMoment_eq_zero_of_even (evenPartReal_neg F),
          zero_add]
      have hc : evenPoleMoment F = ce := by
        conv_lhs => rw [hFeq]
        rw [evenPoleMoment_add hFe (hasCompactSupport_evenPartReal hFc) hFo
          (hasCompactSupport_oddPartReal hFc), evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F),
          add_zero]
      unfold fullZeroForm zeroForm
      rw [markovEnergy_ofReal_eq_even_add_odd hFd hFc, hs, hc]
      ring
    rw [hsplit]
    linarith
  · intro h
    rw [riemannHypothesis_iff_forall_odd_zeroForm_nonneg]
    intro v hv hvc hodd
    have h1 := h v hv hvc
    have hpo : ∀ x, phiDoobTest v (-x) = -phiDoobTest v x := fun x => by
      unfold phiDoobTest
      rw [riemannKernelReal_neg', hodd]
      ring
    unfold fullZeroForm at h1
    unfold zeroForm
    rw [evenPoleMoment_eq_zero_of_odd hpo] at h1
    linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
