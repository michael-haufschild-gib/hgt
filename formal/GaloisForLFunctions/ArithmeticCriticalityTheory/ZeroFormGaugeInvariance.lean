import GaloisForLFunctions.ArithmeticCriticalityTheory.HarmonicThetaSpanRadical
import GaloisForLFunctions.ArithmeticCriticalityTheory.SingleShiftCompleteness

/-!
# The zero form: the pole-free variation form is gauge invariant

For a real test `F` put

    Z(F) = markovEnergy(F) − 2 (∫ F(x) sinh(x/2) dx)²,

the Markov energy with the odd pole term removed (`zeroForm`). Three facts make it the canonical
object behind the frontier inequalities of the theory.

* **Gauge invariance** (`poleFreeForm_eq_zeroForm`). For every shift `a > 0` and every even profile
  `u ∈ C²_c`, the pole-free variation form is the zero form of the test:
  `2 S_a(u) − D_a(u) + V_a(u) = Z(m_a u)`. The left side depends on the gauge `ω_a`, the right side
  only on the test; for one test `F` and two shifts, `PF_a(F/m_a) = PF_b(F/m_b)`.
* **Theta-span invariance** (`abs_zeroForm_add_spanPlateau_sub_le`). Adding the plateau truncation of
  any finite odd superposition of shifted ground states, of any pole coefficient, changes `Z` by
  `O(e^{−8L})`: the zero form annihilates the whole odd theta span, not only its pole-free part.
* **RH** (`riemannHypothesis_iff_forall_odd_zeroForm_nonneg`): RH holds iff `Z ≥ 0` on every odd
  `C²_c` test. The direction `⇐` is `Q = Z + 2(∫F sinh)² ≥ Z`; for `⇒` the pole moment of `F` is
  cancelled by a multiple of `m_1 u_L`, which `Z` does not see.

So the content of RH in the theory is the sign of one quadratic form on the quotient of the odd test
space by the odd theta span; the gauge, the shift and the pole are bookkeeping.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The odd pole moment `∫ F(x) sinh(x/2) dx` of a test. -/
def oddPoleMoment (F : ℝ → ℝ) : ℝ := ∫ x, F x * Real.sinh (x / 2)

/-- The zero form `Z(F) = markovEnergy(F) − 2 (∫ F sinh(x/2))²`. -/
def zeroForm (F : ℝ → ℝ) : ℝ :=
  markovEnergy (fun x => (F x : ℂ)) - 2 * oddPoleMoment F ^ 2

/-! ### Gauge invariance -/

/-- The odd pole moment of `m_a u` is twice the profile moment. -/
theorem oddPoleMoment_phiDoob_shiftedGroundState {a : ℝ} {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    oddPoleMoment (phiDoobTest (fun y => shiftedGroundState a y * u y)) = 2 * profileMoment a u := by
  have hfun : (fun x => phiDoobTest (fun y => shiftedGroundState a y * u y) x * Real.sinh (x / 2)) =
      fun x => u x * shiftDifference a x * Real.sinh (x / 2) := by
    funext x
    unfold phiDoobTest
    rw [← mul_assoc, riemannKernelReal_mul_shiftedGroundState]
    ring
  have hint : Integrable fun x => u x * shiftDifference a x * Real.sinh (x / 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (huc.mul_right.mul_right)
    exact (hu.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))
  unfold oddPoleMoment profileMoment
  rw [hfun, integral_Ioi_eq_half_of_even hint (fun x => by
    rw [heven, shiftDifference_neg, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]
    ring)]
  ring

/-- **Gauge invariance of the pole-free form.** `2 S_a(u) − D_a(u) + V_a(u) = Z(m_a u)` for every
`a > 0` and every even `u ∈ C²_c(ℝ)`. -/
theorem poleFreeForm_eq_zeroForm {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    2 * sameSideEnergy (shiftedGroundState a) u - reflectedDifferenceEnergy (shiftedGroundState a) u +
        profileVariance a u =
      zeroForm (phiDoobTest (fun y => shiftedGroundState a y * u y)) := by
  unfold zeroForm
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_poleFree_add_eight_profileMoment_sq ha hu huc heven,
    oddPoleMoment_phiDoob_shiftedGroundState hu.continuous huc heven]
  ring

/-- For one test `F` vanishing near the origin, the pole-free forms of all gauges agree:
`PF_a(F/m_a) = PF_b(F/m_b)`. -/
theorem poleFreeForm_shiftQuotient_eq {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hvan : ∀ x, |x| < ε → F x = 0) :
    2 * sameSideEnergy (shiftedGroundState a) (shiftQuotient a F) -
        reflectedDifferenceEnergy (shiftedGroundState a) (shiftQuotient a F) +
        profileVariance a (shiftQuotient a F) =
      2 * sameSideEnergy (shiftedGroundState b) (shiftQuotient b F) -
        reflectedDifferenceEnergy (shiftedGroundState b) (shiftQuotient b F) +
        profileVariance b (shiftQuotient b F) := by
  have h0 : F 0 = 0 := hvan 0 (by rwa [abs_zero])
  rw [poleFreeForm_eq_zeroForm ha (contDiff_shiftQuotient ha hε hF hvan)
      (hasCompactSupport_shiftQuotient a hFc) (shiftQuotient_neg a hodd),
    poleFreeForm_eq_zeroForm hb (contDiff_shiftQuotient hb hε hF hvan)
      (hasCompactSupport_shiftQuotient b hFc) (shiftQuotient_neg b hodd)]
  have ea : phiDoobTest (fun y => shiftedGroundState a y * shiftQuotient a F y) = F :=
    funext (phiDoobTest_shiftedGroundState_mul_shiftQuotient ha h0)
  have eb : phiDoobTest (fun y => shiftedGroundState b y * shiftQuotient b F y) = F :=
    funext (phiDoobTest_shiftedGroundState_mul_shiftQuotient hb h0)
  rw [ea, eb]

/-! ### Invariance under the odd theta span -/

theorem abs_smoothPlateau_sub_one_le_abs_sq_sub_one (L x : ℝ) :
    |smoothPlateau L x - 1| ≤ |smoothPlateau L x ^ 2 - 1| := by
  have h0 := smoothPlateau_nonneg L x
  have h1 := smoothPlateau_le_one L x
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by nlinarith)]
  nlinarith

/-- The odd pole moment of `M u_L` converges to `σ` at rate `e^{−8L}`. -/
theorem abs_oddPoleMoment_spanPlateau_sub_le {ι : Type*} (s : Finset ι) (c a : ι → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |oddPoleMoment (fun x => spanShiftDifference s c a x * smoothPlateau L x) -
        spanSourceCoefficient s c a| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_spanShiftDifference_le s c a
  refine ⟨C * ∫ x : ℝ, Real.exp (-(8 * |x|)),
    mul_nonneg hC0 (integral_nonneg fun x => (Real.exp_pos _).le), fun L => ?_⟩
  have hu := (contDiff_smoothPlateau L).continuous
  have hA : Integrable fun x => spanShiftDifference s c a x * smoothPlateau L x * Real.sinh (x / 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((continuous_spanShiftDifference s c a).mul hu).mul
        (Real.continuous_sinh.comp (continuous_id.div_const 2))
    · exact ((hasCompactSupport_smoothPlateau L).mul_left).mul_right
  unfold oddPoleMoment
  rw [← integral_spanShiftDifference_mul_sinh_half s c a,
    ← integral_sub hA (integrable_spanShiftDifference_mul_sinh_half s c a), ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (integrable_exp_neg_eight_mul_abs.const_mul
    (C * Real.exp (-(8 * L)))) (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [Real.norm_eq_abs, show spanShiftDifference s c a x * smoothPlateau L x * Real.sinh (x / 2) -
      spanShiftDifference s c a x * Real.sinh (x / 2) =
        (smoothPlateau L x - 1) * (spanShiftDifference s c a x * Real.sinh (x / 2)) by ring]
    have h := abs_smoothPlateau_sq_sub_one_mul_le hC0 hC L x
    rw [abs_mul] at h ⊢
    exact (mul_le_mul_of_nonneg_right (abs_smoothPlateau_sub_one_le_abs_sq_sub_one L x)
      (abs_nonneg _)).trans h
  · rw [integral_const_mul]
    ring

theorem phiDoobTest_add (f g : ℝ → ℝ) (x : ℝ) :
    phiDoobTest (fun y => f y + g y) x = phiDoobTest f x + phiDoobTest g x := by
  unfold phiDoobTest
  ring

/-- **The zero form annihilates the odd theta span.** For every finite superposition `ω` of shifted
ground states (any pole coefficient) and every test `v ∈ C²_c(ℝ)` there are `K, R` with
`|Z(Φ(ω u_L + v)) − Z(Φ v)| ≤ K e^{−8L}` for `L ≥ R`. -/
theorem abs_zeroForm_add_spanPlateau_sub_le {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 ≤ R ∧ ∀ L, R ≤ L →
      |zeroForm (phiDoobTest (fun y => spanGroundState s c a y * smoothPlateau L y + v y)) -
        zeroForm (phiDoobTest v)| ≤ K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_spanShiftDifference_le s c a
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius hvc
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_abs_markovEnergy_spanPlateauProfile_sub_le s c a
  obtain ⟨K₃, hK₃0, hK₃⟩ := abs_oddPoleMoment_spanPlateau_sub_le s c a
  set σ := spanSourceCoefficient s c a with hσ
  set sv := oddPoleMoment (phiDoobTest v) with hsv
  have hM : ∀ y, |riemannKernelReal y * spanGroundState s c a y| ≤ C * Real.exp (-(24 * |y|)) :=
    fun y => by rw [riemannKernelReal_mul_spanGroundState]; exact hC y
  have hsrc : ∀ x, twoSidedGenerator (spanGroundState s c a) x -
      riemannKernelReal x * Real.cosh (x / 2) * spanGroundState s c a x =
      riemannKernelReal x * (2 * σ * Real.sinh (x / 2)) := fun x => by
    rw [twoSidedGenerator_spanGroundState_sub_potential]
    ring
  set K₂ := riemannKernelReal 0 * C * (2 * Λ * archFirstMoment +
    2 * Real.exp (8 * R) * primeEighthMoment) * (∫ x, |v x|)
  have hK₂0 : 0 ≤ K₂ := by
    have := archFirstMoment_nonneg
    have := primeEighthMoment_nonneg
    have := riemannKernelReal_pos 0
    have : 0 ≤ ∫ x, |v x| := integral_nonneg fun x => abs_nonneg _
    positivity
  refine ⟨K₁ + 2 * K₂ + 2 * K₃ * (2 * |σ + sv| + K₃), R, by positivity, by linarith, fun L hRL => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  have hexp1 : Real.exp (-(8 * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  set N : ℝ → ℝ := fun y => spanGroundState s c a y * smoothPlateau L y with hN_def
  have hN : ContDiff ℝ 2 N := (contDiff_spanGroundState s c a).mul (contDiff_smoothPlateau L)
  have hNc : HasCompactSupport N := (hasCompactSupport_smoothPlateau L).mul_left
  -- the three errors
  have e1 := hK₁ L
  have hN_eq : spanPlateauProfile s c a L = N := rfl
  rw [hN_eq] at e1
  have e2 := abs_integral_mul_generator_plateau_sub_le (contDiff_spanGroundState s c a) hC0 hM hΛ0 hΛ
    (integrableOn_archLevy_twoSidedShiftGenerator_spanGroundState s c a)
    (summable_atom_twoSidedShiftGenerator_spanGroundState s c a) hsrc
    (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))) hv hvc hsupp hRL
  have hpair : (∫ x, v x * (riemannKernelReal x * (2 * σ * Real.sinh (x / 2)))) = 2 * σ * sv := by
    rw [hsv, oddPoleMoment, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    unfold phiDoobTest
    ring
  rw [hpair] at e2
  have e3 := hK₃ L
  have hpm : oddPoleMoment (phiDoobTest fun y => N y + v y) =
      oddPoleMoment (fun x => spanShiftDifference s c a x * smoothPlateau L x) + sv := by
    have hi1 : Integrable fun x => spanShiftDifference s c a x * smoothPlateau L x *
        Real.sinh (x / 2) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact ((continuous_spanShiftDifference s c a).mul (contDiff_smoothPlateau L).continuous).mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2))
      · exact ((hasCompactSupport_smoothPlateau L).mul_left).mul_right
    have hi2 : Integrable fun x => phiDoobTest v x * Real.sinh (x / 2) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (continuous_riemannKernelReal.mul hv.continuous).mul
          (Real.continuous_sinh.comp (continuous_id.div_const 2))
      · exact (hvc.mul_left).mul_right
    rw [hsv]
    unfold oddPoleMoment
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [phiDoobTest_add, hN_def]
    rw [show phiDoobTest (fun y => spanGroundState s c a y * smoothPlateau L y) x =
      spanShiftDifference s c a x * smoothPlateau L x by
        unfold phiDoobTest; rw [← mul_assoc, riemannKernelReal_mul_spanGroundState]]
    ring
  have hpol := markovEnergy_phiDoob_add hN hNc hv hvc
  unfold zeroForm
  rw [hpm, hpol]
  set P := ∫ x, v x * (twoSidedGenerator N x - riemannKernelReal x * Real.cosh (x / 2) * N x)
  set m := oddPoleMoment (fun x => spanShiftDifference s c a x * smoothPlateau L x)
  set QN := markovEnergy (fun x => (phiDoobTest N x : ℂ))
  have hdiff : QN + markovEnergy (fun x => (phiDoobTest v x : ℂ)) + 2 * P - 2 * (m + sv) ^ 2 -
      (markovEnergy (fun x => (phiDoobTest v x : ℂ)) - 2 * sv ^ 2) =
      (QN - 2 * σ ^ 2) + 2 * (P - 2 * σ * sv) - 2 * (m - σ) * (2 * (σ + sv) + (m - σ)) := by ring
  rw [hdiff]
  have he3' : |m - σ| ≤ K₃ := (hK₃ L).trans (by nlinarith)
  calc |(QN - 2 * σ ^ 2) + 2 * (P - 2 * σ * sv) - 2 * (m - σ) * (2 * (σ + sv) + (m - σ))|
      ≤ |QN - 2 * σ ^ 2| + 2 * |P - 2 * σ * sv| +
          2 * |m - σ| * (2 * |σ + sv| + |m - σ|) := by
        refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
        · rw [abs_mul, abs_two]
        · rw [abs_mul, abs_mul, abs_two]
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (by positivity)
          rw [abs_mul, abs_two]
    _ ≤ K₁ * Real.exp (-(8 * L)) + 2 * (K₂ * Real.exp (-(8 * L))) +
          2 * (K₃ * Real.exp (-(8 * L))) * (2 * |σ + sv| + K₃) := by
        have hm := hK₃ L
        gcongr
    _ = _ := by ring

/-! ### RH as positivity of the zero form -/

/-- **RH is the positivity of the zero form on odd tests.** -/
theorem riemannHypothesis_iff_forall_odd_zeroForm_nonneg :
    RiemannHypothesis ↔ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v →
      (∀ x, v (-x) = -v x) → 0 ≤ zeroForm (phiDoobTest v) := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg]
  constructor
  · intro hRH v hv hvc hodd
    -- cancel the pole moment by a multiple of `ω_1 u_L`
    set lam := -(oddPoleMoment (phiDoobTest v) / Real.sinh (1 / 2)) with hlam
    have hs1 : 0 < Real.sinh (1 / 2) := Real.sinh_pos_iff.mpr (by norm_num)
    obtain ⟨K, R, hK0, hR0, hK⟩ := abs_zeroForm_add_spanPlateau_sub_le
      (Finset.univ : Finset (Fin 1)) (fun _ => lam) (fun _ => 1) hv hvc
    obtain ⟨K₃, hK₃0, hK₃⟩ := abs_oddPoleMoment_spanPlateau_sub_le
      (Finset.univ : Finset (Fin 1)) (fun _ => lam) (fun _ => 1)
    have hσ : spanSourceCoefficient (Finset.univ : Finset (Fin 1)) (fun _ => lam) (fun _ => 1) =
        -oddPoleMoment (phiDoobTest v) := by
      simp only [spanSourceCoefficient, Finset.univ_unique, Finset.sum_singleton, hlam]
      field_simp
    -- the energies along the cancelled sequence are nonnegative
    by_contra hneg
    simp only [not_le] at hneg
    set z := zeroForm (phiDoobTest v)
    have h0 : Tendsto (fun L : ℝ => Real.exp (-(8 * L))) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))
      simpa [Function.comp_def, neg_mul] using this
    have hev : ∀ᶠ L : ℝ in atTop, (K + 2 * K₃ ^ 2) * Real.exp (-(8 * L)) < -z := by
      have := h0.const_mul (K + 2 * K₃ ^ 2)
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    obtain ⟨L, hL⟩ := (hev.and (eventually_ge_atTop (max R 0))).exists
    have hRL : R ≤ L := le_trans (le_max_left _ _) hL.2
    have hL0 : 0 ≤ L := le_trans (le_max_right _ _) hL.2
    have hexp1 : Real.exp (-(8 * L)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    set w : ℝ → ℝ := fun y => spanGroundState (Finset.univ : Finset (Fin 1)) (fun _ => lam)
      (fun _ => 1) y * smoothPlateau L y + v y with hw
    have hwC : ContDiff ℝ 2 w :=
      ((contDiff_spanGroundState _ _ _).mul (contDiff_smoothPlateau L)).add hv
    have hwc : HasCompactSupport w :=
      ((hasCompactSupport_smoothPlateau L).mul_left).add hvc
    have hwodd : ∀ x, w (-x) = -w x := fun x => by
      simp only [hw, spanGroundState, Finset.univ_unique, Finset.sum_singleton,
        shiftedGroundState_neg, smoothPlateau_neg, hodd]
      ring
    have hQ := hRH w hwC hwc hwodd
    have hZ : |zeroForm (phiDoobTest w) - z| ≤ K * Real.exp (-(8 * L)) := hK L hRL
    -- the pole moment of `w` is small
    have hpm : |oddPoleMoment (phiDoobTest w)| ≤ K₃ * Real.exp (-(8 * L)) := by
      have hi1 : Integrable fun x => spanShiftDifference (Finset.univ : Finset (Fin 1))
          (fun _ => lam) (fun _ => 1) x * smoothPlateau L x * Real.sinh (x / 2) := by
        refine Continuous.integrable_of_hasCompactSupport ?_ ?_
        · exact ((continuous_spanShiftDifference _ _ _).mul (contDiff_smoothPlateau L).continuous).mul
            (Real.continuous_sinh.comp (continuous_id.div_const 2))
        · exact ((hasCompactSupport_smoothPlateau L).mul_left).mul_right
      have hi2 : Integrable fun x => phiDoobTest v x * Real.sinh (x / 2) := by
        refine Continuous.integrable_of_hasCompactSupport ?_ ?_
        · exact (continuous_riemannKernelReal.mul hv.continuous).mul
            (Real.continuous_sinh.comp (continuous_id.div_const 2))
        · exact (hvc.mul_left).mul_right
      have hsplit : oddPoleMoment (phiDoobTest w) =
          oddPoleMoment (fun x => spanShiftDifference (Finset.univ : Finset (Fin 1)) (fun _ => lam)
            (fun _ => 1) x * smoothPlateau L x) + oddPoleMoment (phiDoobTest v) := by
        unfold oddPoleMoment
        rw [← integral_add hi1 hi2]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hw, phiDoobTest_add]
        rw [show phiDoobTest (fun y => spanGroundState (Finset.univ : Finset (Fin 1)) (fun _ => lam)
          (fun _ => 1) y * smoothPlateau L y) x = spanShiftDifference (Finset.univ : Finset (Fin 1))
            (fun _ => lam) (fun _ => 1) x * smoothPlateau L x by
          unfold phiDoobTest; rw [← mul_assoc, riemannKernelReal_mul_spanGroundState]]
        ring
      have h3 := hK₃ L
      rw [hσ] at h3
      rw [hsplit]
      calc |oddPoleMoment (fun x => spanShiftDifference Finset.univ (fun _ => lam) (fun _ => 1) x *
            smoothPlateau L x) + oddPoleMoment (phiDoobTest v)|
          = |oddPoleMoment (fun x => spanShiftDifference Finset.univ (fun _ => lam) (fun _ => 1) x *
              smoothPlateau L x) - -oddPoleMoment (phiDoobTest v)| := by ring_nf
        _ ≤ _ := h3
    have hZw : zeroForm (phiDoobTest w) ≥ -(2 * (K₃ * Real.exp (-(8 * L))) ^ 2) := by
      unfold zeroForm
      have hsq : oddPoleMoment (phiDoobTest w) ^ 2 ≤ (K₃ * Real.exp (-(8 * L))) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hpm 2
      linarith
    have hsmall : (K₃ * Real.exp (-(8 * L))) ^ 2 ≤ K₃ ^ 2 * Real.exp (-(8 * L)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith [Real.exp_pos (-(8 * L))]) (sq_nonneg _)
    have habs := (abs_le.mp hZ).2
    have hfin := hL.1
    rw [add_mul] at hfin
    nlinarith
  · intro h v hv hvc hodd
    have := h v hv hvc hodd
    unfold zeroForm at this
    nlinarith [sq_nonneg (oddPoleMoment (phiDoobTest v))]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
