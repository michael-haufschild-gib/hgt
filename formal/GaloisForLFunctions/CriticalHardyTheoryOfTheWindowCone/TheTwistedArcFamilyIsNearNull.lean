import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheShiftedGammaTestsAreTaylorCoefficients
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistenceDecidesRH

/-!
# The twisted-arc family is near-null for every point of the window cone

The twisted arc minimum principle gives weights `w_j ≥ 0`, `w₀ > 0`, for which the shifted-Gamma tests
`F_j`, `F̂_j = Ξ Q_j`, are jointly blind: `Σ_j w_j (F_j ⋆ F_j)(log n) = 0` for every `n ≥ 2`. Their
transforms vanish at every zero of `ζ`. So on the full family the weights drop out and the zero side
vanishes: `Σ_j w_j W_λ(F_j) = 0` for *every* weight `λ`.

On a window both statements fail only by the tail of the family, and the tail is doubly exponentially
small (`abs_xiShiftedGammaTest_le`). Truncating at radius `L`:

  `Σ_j w_j W_λ(F_{j,L}) ≤ K (1 + V)(e^{2L} + 1) exp(−(π/16) e^{2(L−1)})`,

where `V` bounds `|λ(n) − Λ(n)|/√n` on the integers the window sees (`exists_tsum_nullEnergy_le`).
Positivity on a window supplies such a `V` through the box of two-point resonators
(`abs_sub_vonMangoldt_div_sqrt_le`). Hence:

* **Near-nullity** (`exists_nullWeights_tsum_nullEnergy_le`): every point of the cone `𝒜(c)` has
  doubly exponentially small energy on the whole family, with one constant for all weights.
* **The margin law** (`exists_margin_ceiling`): no weight has a margin above
  `K exp(3c − (π/16) e^{2(c−2)})` on `[−c, c]`. Slack from other weights is excluded at a doubly
  exponential rate; the Gaussian ceiling known for `Λ` holds for the best margin over all weights,
  with a smaller rate.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

local notation "𝔽" => xiShiftedGammaTest
local notation "Λₙ" => fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### The weights of the null family -/

/-- The growth scale of the shifted-Gamma family. -/
def gammaScale (j : ℕ) : ℝ := (j ! : ℝ) * (3 / 2 : ℝ) ^ j

theorem gammaScale_nonneg (j : ℕ) : 0 ≤ gammaScale j := by
  unfold gammaScale
  positivity

/-- Weights making the shifted-Gamma family jointly blind at every `log n`, `n ≥ 2`. -/
structure NullWeights (w : ℕ → ℝ) : Prop where
  nonneg : ∀ j, 0 ≤ w j
  pos_zero : 0 < w 0
  summable : Summable fun j => w j * gammaScale j ^ 2
  blind : ∀ n : ℕ, 2 ≤ n → ∑' j, w j * crossCorr (𝔽 j) (𝔽 j) (Real.log n) = 0

/-- The twisted arc minimum principle supplies null weights. -/
theorem exists_nullWeights : ∃ w : ℕ → ℝ, NullWeights w := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds
  set ν : Measure ArcParam := (μ : Measure ArcParam)
  have hmom : ∀ j, 0 ≤ twArcEvenMoment ν (fun _ => 1) j := twArcEvenMoment_one_nonneg μ
  have hblind0 : ∀ n : ℕ, ∫ u, (fun _ : ArcParam => (1 : ℝ)) u * twArcMoment n u ∂ν = 0 :=
    fun n => by simpa using hμ n
  set w : ℕ → ℝ := fun j => arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j with hw_def
  have hw : ∀ j, 0 ≤ w j := fun j => arcGammaWeight_nonneg (hmom j) j
  have hw0 : 0 < w 0 := by
    simp only [hw_def, arcGammaWeight]
    exact div_pos (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
      (by exact_mod_cast Nat.factorial_pos _)
  have hsumw : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 :=
    summable_arcGammaWeight hmom
      (twArcEvenMoment_le (ν := ν) (g := fun _ => 1) (B := 1) fun _ => by norm_num)
  have hblindInt := shiftedGamma_blind_of_twistedArc (B := 1) measurable_const
    (fun _ => by norm_num) hblind0 hmom
  refine ⟨w, hw, hw0, hsumw, fun n hn => ?_⟩
  simp_rw [crossCorr_xiShiftedGammaTest]
  have e : ∀ j, w j * (1 / (2 * Real.pi) *
      ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
      1 / (2 * Real.pi) * (w j *
        ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
  simp_rw [e]
  rw [tsum_mul_left, hblindInt n hn, mul_zero]

/-! ### Pointwise bounds -/

/-- The doubly exponential tail `exp(−(π/16) e^{2X})`. -/
def doubleExpTail (X : ℝ) : ℝ := Real.exp (-(Real.pi / 16) * Real.exp (2 * X))

theorem doubleExpTail_pos (X : ℝ) : 0 < doubleExpTail X := Real.exp_pos _

theorem doubleExpTail_le_one (X : ℝ) : doubleExpTail X ≤ 1 := by
  unfold doubleExpTail
  refine Real.exp_le_one_iff.mpr ?_
  have := Real.exp_pos (2 * X)
  have := Real.pi_pos
  nlinarith [mul_pos (by positivity : (0 : ℝ) < Real.pi / 16) (Real.exp_pos (2 * X))]

theorem doubleExpTail_anti {X Y : ℝ} (h : X ≤ Y) : doubleExpTail Y ≤ doubleExpTail X := by
  unfold doubleExpTail
  refine Real.exp_le_exp.mpr ?_
  have hm : Real.exp (2 * X) ≤ Real.exp (2 * Y) := Real.exp_le_exp.mpr (by linarith)
  have hπ : (0 : ℝ) ≤ Real.pi / 16 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hm hπ]

/-- `y³ ≤ 6 (16/π)³ e^{(π/16) y}` for `y ≥ 0`. -/
def envelopeConst : ℝ := 6 * (16 / Real.pi) ^ 3

theorem envelopeConst_pos : 0 < envelopeConst := by
  unfold envelopeConst
  positivity

theorem pow_three_le_envelopeConst {y : ℝ} (hy : 0 ≤ y) :
    y ^ 3 ≤ envelopeConst * Real.exp (Real.pi / 16 * y) := by
  have hπ := Real.pi_pos
  have hz : 0 ≤ Real.pi / 16 * y := by positivity
  have h1 := Real.pow_div_factorial_le_exp (Real.pi / 16 * y) hz 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf, div_le_iff₀ (by norm_num)] at h1
  have e : y ^ 3 = (16 / Real.pi) ^ 3 * (Real.pi / 16 * y) ^ 3 := by
    field_simp
  rw [e]
  unfold envelopeConst
  have hq : 0 ≤ (16 / Real.pi) ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hq]

/-- For `|x| ≥ X` the profile with the Weil weight `e^{|x|/2}` is below `K e^{−|x|} exp(−(π/16) e^{2X})`. -/
theorem shiftedGammaEnvelope_mul_exp_le {x X : ℝ} (h : X ≤ |x|) :
    shiftedGammaEnvelope x * Real.exp (1 / 2 * |x|) ≤
      envelopeConst * (Real.exp (-|x|) * doubleExpTail X) := by
  have hπ := Real.pi_pos
  have hy3 := pow_three_le_envelopeConst (Real.exp_pos (2 * |x|)).le
  have e6 : Real.exp (2 * |x|) ^ 3 = Real.exp (6 * |x|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e6] at hy3
  have hmono : Real.exp (2 * X) ≤ Real.exp (2 * |x|) := Real.exp_le_exp.mpr (by linarith)
  have hτ : Real.exp (-(Real.pi / 16 * Real.exp (2 * |x|))) ≤ doubleExpTail X := by
    unfold doubleExpTail
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ Real.pi / 16)]
  obtain ⟨z, hz⟩ : ∃ z, z = Real.pi / 16 * Real.exp (2 * |x|) := ⟨_, rfl⟩
  rw [← hz] at hy3 hτ
  have hsplit : shiftedGammaEnvelope x * Real.exp (1 / 2 * |x|) =
      Real.exp (-|x|) * (Real.exp (6 * |x|) * Real.exp (-z)) * Real.exp (-z) := by
    unfold shiftedGammaEnvelope
    simp only [← Real.exp_add]
    congr 1
    rw [hz]
    ring
  have hone : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  have hle : Real.exp (6 * |x|) * Real.exp (-z) ≤ envelopeConst := by
    have := mul_le_mul_of_nonneg_right hy3 (Real.exp_pos (-z)).le
    rw [mul_assoc, hone, mul_one] at this
    exact this
  rw [hsplit]
  calc Real.exp (-|x|) * (Real.exp (6 * |x|) * Real.exp (-z)) * Real.exp (-z)
      ≤ Real.exp (-|x|) * envelopeConst * doubleExpTail X := by
        have hp := Real.exp_pos (-|x|)
        have hq := Real.exp_pos (-z)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hle hp.le) hτ hq.le
          (mul_nonneg hp.le envelopeConst_pos.le)
    _ = _ := by ring

/-- The constant of the uniform pointwise bound on `F_j` and `F_j′`. -/
def nullConst : ℝ := 40 * shiftedGammaConstant

theorem nullConst_nonneg : 0 ≤ nullConst := by
  have := shiftedGammaConstant_nonneg
  unfold nullConst
  positivity

theorem succ_factorial_mul_le (j : ℕ) :
    (((j + 1)! : ℝ)) * (4 / 3 : ℝ) ^ j ≤ 8 * gammaScale j := by
  have hb := one_add_mul_le_pow (a := (1 / 8 : ℝ)) (by norm_num) j
  have hfac : (((j + 1)! : ℝ)) = ((j : ℝ) + 1) * (j ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hj : (j : ℝ) + 1 ≤ 8 * (9 / 8 : ℝ) ^ j := by
    have e : (1 + 1 / 8 : ℝ) = 9 / 8 := by norm_num
    rw [e] at hb
    nlinarith
  have hp : (9 / 8 : ℝ) ^ j * (4 / 3 : ℝ) ^ j = (3 / 2 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  unfold gammaScale
  rw [hfac]
  have hf : (0 : ℝ) ≤ (j ! : ℝ) * (4 / 3 : ℝ) ^ j := by positivity
  calc ((j : ℝ) + 1) * (j ! : ℝ) * (4 / 3 : ℝ) ^ j
      = ((j : ℝ) + 1) * ((j ! : ℝ) * (4 / 3 : ℝ) ^ j) := by ring
    _ ≤ (8 * (9 / 8 : ℝ) ^ j) * ((j ! : ℝ) * (4 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_right hj hf
    _ = 8 * ((j ! : ℝ) * ((9 / 8 : ℝ) ^ j * (4 / 3 : ℝ) ^ j)) := by ring
    _ = _ := by rw [hp]

theorem abs_xiShiftedGammaTest_le_scale (j : ℕ) (x : ℝ) :
    |𝔽 j x| ≤ nullConst * gammaScale j * shiftedGammaEnvelope x := by
  have hK := shiftedGammaConstant_nonneg
  have hG := (shiftedGammaEnvelope_pos x).le
  refine (abs_xiShiftedGammaTest_le j x).trans (mul_le_mul_of_nonneg_right ?_ hG)
  have hp : (4 / 3 : ℝ) ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hs : (j ! : ℝ) * (4 / 3 : ℝ) ^ j ≤ gammaScale j :=
    mul_le_mul_of_nonneg_left hp (by positivity)
  have hg := gammaScale_nonneg j
  unfold nullConst
  nlinarith [mul_le_mul_of_nonneg_left hs hK, mul_nonneg hK hg]

theorem abs_deriv_xiShiftedGammaTest_le_scale (j : ℕ) (x : ℝ) :
    |deriv (𝔽 j) x| ≤ nullConst * gammaScale j * shiftedGammaEnvelope x := by
  have hK := shiftedGammaConstant_nonneg
  have hG := (shiftedGammaEnvelope_pos x).le
  refine (abs_deriv_xiShiftedGammaTest_le j x).trans (mul_le_mul_of_nonneg_right ?_ hG)
  have hs := succ_factorial_mul_le j
  unfold nullConst
  nlinarith [mul_le_mul_of_nonneg_left hs hK]

/-- The product of the two constants. -/
def decayConst : ℝ := nullConst * envelopeConst

theorem decayConst_nonneg : 0 ≤ decayConst :=
  mul_nonneg nullConst_nonneg envelopeConst_pos.le

theorem abs_mul_exp_le_of_tail (j : ℕ) {x X : ℝ} (h : X ≤ |x|) :
    |𝔽 j x| * Real.exp (1 / 2 * |x|) ≤
      decayConst * gammaScale j * (Real.exp (-|x|) * doubleExpTail X) := by
  have hg := gammaScale_nonneg j
  have hN := nullConst_nonneg
  have hE := Real.exp_pos (1 / 2 * |x|)
  calc |𝔽 j x| * Real.exp (1 / 2 * |x|)
      ≤ (nullConst * gammaScale j * shiftedGammaEnvelope x) * Real.exp (1 / 2 * |x|) :=
        mul_le_mul_of_nonneg_right (abs_xiShiftedGammaTest_le_scale j x) hE.le
    _ = nullConst * gammaScale j * (shiftedGammaEnvelope x * Real.exp (1 / 2 * |x|)) := by ring
    _ ≤ nullConst * gammaScale j * (envelopeConst * (Real.exp (-|x|) * doubleExpTail X)) :=
        mul_le_mul_of_nonneg_left (shiftedGammaEnvelope_mul_exp_le h) (by positivity)
    _ = _ := by unfold decayConst; ring

theorem abs_deriv_mul_exp_le_of_tail (j : ℕ) {x X : ℝ} (h : X ≤ |x|) :
    |deriv (𝔽 j) x| * Real.exp (1 / 2 * |x|) ≤
      decayConst * gammaScale j * (Real.exp (-|x|) * doubleExpTail X) := by
  have hg := gammaScale_nonneg j
  have hN := nullConst_nonneg
  have hE := Real.exp_pos (1 / 2 * |x|)
  calc |deriv (𝔽 j) x| * Real.exp (1 / 2 * |x|)
      ≤ (nullConst * gammaScale j * shiftedGammaEnvelope x) * Real.exp (1 / 2 * |x|) :=
        mul_le_mul_of_nonneg_right (abs_deriv_xiShiftedGammaTest_le_scale j x) hE.le
    _ = nullConst * gammaScale j * (shiftedGammaEnvelope x * Real.exp (1 / 2 * |x|)) := by ring
    _ ≤ nullConst * gammaScale j * (envelopeConst * (Real.exp (-|x|) * doubleExpTail X)) :=
        mul_le_mul_of_nonneg_left (shiftedGammaEnvelope_mul_exp_le h) (by positivity)
    _ = _ := by unfold decayConst; ring

/-- `|F_j(x)| ≤ A_j e^{−|x|}`. -/
theorem abs_xiShiftedGammaTest_le_exp (j : ℕ) (x : ℝ) :
    |𝔽 j x| ≤ decayConst * gammaScale j * Real.exp (-|x|) := by
  have h := abs_mul_exp_le_of_tail j (le_refl |x|)
  have hA : 0 ≤ decayConst * gammaScale j := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  have h1 : (1 : ℝ) ≤ Real.exp (1 / 2 * |x|) := Real.one_le_exp (by positivity)
  have h2 : |𝔽 j x| ≤ |𝔽 j x| * Real.exp (1 / 2 * |x|) :=
    le_mul_of_one_le_right (abs_nonneg _) h1
  have hE := (Real.exp_pos (-|x|)).le
  refine h2.trans (h.trans (mul_le_mul_of_nonneg_left ?_ hA))
  exact mul_le_of_le_one_right hE (doubleExpTail_le_one _)

theorem abs_xiShiftedGammaTest_le_const (j : ℕ) (x : ℝ) :
    |𝔽 j x| ≤ decayConst * gammaScale j := by
  have hA : 0 ≤ decayConst * gammaScale j := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  refine (abs_xiShiftedGammaTest_le_exp j x).trans ?_
  have : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (by simp)
  exact mul_le_of_le_one_right hA this

/-- The truncation error is below `A_j e^{−|t|} exp(−(π/16) e^{2(L−1)})`. -/
theorem abs_truncTest_sub_le (j : ℕ) (L t : ℝ) :
    |truncTest (𝔽 j) L t - 𝔽 j t| ≤
      decayConst * gammaScale j * (Real.exp (-|t|) * doubleExpTail (L - 1)) := by
  have hA : 0 ≤ decayConst * gammaScale j := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  rcases le_or_gt |t| (L - 1) with ht | ht
  · rw [truncTest_eq_self ht, sub_self, abs_zero]
    exact mul_nonneg hA (mul_nonneg (Real.exp_pos _).le (doubleExpTail_pos _).le)
  · have e : truncTest (𝔽 j) L t - 𝔽 j t = 𝔽 j t * (bulkCutoff L t - 1) := by
      unfold truncTest
      ring
    have hb : |bulkCutoff L t - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [bulkCutoff_nonneg L t, bulkCutoff_le_one L t]
    rw [e, abs_mul]
    have h1 : (1 : ℝ) ≤ Real.exp (1 / 2 * |t|) := Real.one_le_exp (by positivity)
    calc |𝔽 j t| * |bulkCutoff L t - 1| ≤ |𝔽 j t| * 1 :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |𝔽 j t| * Real.exp (1 / 2 * |t|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ _ := abs_mul_exp_le_of_tail j ht.le

/-! ### The zero side -/

/-- `∫ e^{−|u|} du`. -/
def absMass : ℝ := ∫ u : ℝ, Real.exp (-|u|)

theorem absMass_nonneg : 0 ≤ absMass := integral_nonneg fun _ => (Real.exp_pos _).le

theorem tailBound_xiShiftedGammaTest_le {Λc : ℝ} (hΛ0 : 0 ≤ Λc) (j : ℕ) (L : ℝ) :
    tailBound (𝔽 j) Λc L ≤
      (3 + 4 * Λc) * (decayConst * gammaScale j) * absMass * doubleExpTail (L - 1) := by
  have hA : 0 ≤ decayConst * gammaScale j := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  have hτ := (doubleExpTail_pos (L - 1)).le
  set Q : ℝ := (3 + 4 * Λc) * (decayConst * gammaScale j) * doubleExpTail (L - 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hint : Integrable fun u : ℝ => Q * Real.exp (-|u|) := integrable_exp_neg_abs.const_mul Q
  have hle : tailBound (𝔽 j) Λc L ≤ ∫ u : ℝ, Q * Real.exp (-|u|) := by
    unfold tailBound
    refine integral_mono_of_nonneg (Eventually.of_forall fun u =>
      Set.indicator_nonneg (fun v _ => tailMajorant_nonneg _ hΛ0 v) u) hint
      (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ {u : ℝ | L - 1 ≤ |u|}
    · simp only [Set.indicator_of_mem hu]
      have h1 := abs_mul_exp_le_of_tail j (x := u) hu
      have h2 := abs_deriv_mul_exp_le_of_tail j (x := u) hu
      set R : ℝ := decayConst * gammaScale j * (Real.exp (-|u|) * doubleExpTail (L - 1)) with hR
      have hR' : Q * Real.exp (-|u|) = (3 + 4 * Λc) * R := by rw [hQ, hR]; ring
      rw [hR']
      unfold tailMajorant
      have h3 := mul_le_mul_of_nonneg_left h1 hΛ0
      nlinarith
    · simp only [Set.indicator_of_notMem hu]
      exact mul_nonneg hQ0 (Real.exp_pos _).le
  refine hle.trans (le_of_eq ?_)
  rw [integral_const_mul, hQ]
  unfold absMass
  ring

/-- **The zero side of a truncation.** -/
theorem abs_re_W_truncTest_null_le {Λc : ℝ} (hΛ0 : 0 ≤ Λc)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λc) (j : ℕ) (L : ℝ) :
    |(zetaZeroConfig.W (fun u => (truncTest (𝔽 j) L u : ℂ))
        (fun u => (truncTest (𝔽 j) L u : ℂ))).re| ≤
      ((5 / 4) * zetaInvSqSum * ((3 + 4 * Λc) * decayConst * absMass) ^ 2) *
        gammaScale j ^ 2 * doubleExpTail (L - 1) ^ 2 := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  have hexp := (hF j).expDecayTest (by norm_num : (0 : ℝ) < 1 / 4)
  have h := (Complex.abs_re_le_norm _).trans (norm_W_truncTest_le hexp hΛ hΛ0
    (fun ρ => paperFT_xiShiftedGammaTest_gammaOf j ρ) L)
  refine h.trans ?_
  have ht0 := tailBound_nonneg (𝔽 j) hΛ0 L
  have ht := tailBound_xiShiftedGammaTest_le hΛ0 j L
  have hZ : 0 ≤ zetaInvSqSum := zetaInvSqSum_nonneg
  calc (5 / 4) * zetaInvSqSum * tailBound (𝔽 j) Λc L ^ 2
      ≤ (5 / 4) * zetaInvSqSum * ((3 + 4 * Λc) * (decayConst * gammaScale j) * absMass *
          doubleExpTail (L - 1)) ^ 2 := by
        gcongr
    _ = _ := by ring

/-! ### The correlations -/

theorem abs_integral_mul_shift_le {H₁ H₂ : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h₁ : ∀ t, |H₁ t| ≤ A * Real.exp (-|t|)) (h₂ : ∀ t, |H₂ t| ≤ A) (y : ℝ) :
    |∫ t, H₁ t * H₂ (t - y)| ≤ A ^ 2 * absMass := by
  have hg : Integrable fun t : ℝ => A ^ 2 * Real.exp (-|t|) := integrable_exp_neg_abs.const_mul _
  have h := norm_integral_le_of_norm_le (f := fun t => H₁ t * H₂ (t - y)) hg
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |H₁ t| * |H₂ (t - y)| ≤ (A * Real.exp (-|t|)) * A :=
            mul_le_mul (h₁ t) (h₂ _) (abs_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
        _ = _ := by ring)
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

theorem abs_truncTest_le_exp (j : ℕ) (L t : ℝ) :
    |truncTest (𝔽 j) L t| ≤ decayConst * gammaScale j * Real.exp (-|t|) :=
  (abs_truncTest_le _ L t).trans (abs_xiShiftedGammaTest_le_exp j t)

theorem abs_truncTest_le_const (j : ℕ) (L t : ℝ) :
    |truncTest (𝔽 j) L t| ≤ decayConst * gammaScale j :=
  (abs_truncTest_le _ L t).trans (abs_xiShiftedGammaTest_le_const j t)

theorem abs_crossCorr_truncTest_null_le (j : ℕ) (L y : ℝ) :
    |crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) y| ≤
      (decayConst * gammaScale j) ^ 2 * absMass :=
  abs_integral_mul_shift_le (mul_nonneg decayConst_nonneg (gammaScale_nonneg j))
    (abs_truncTest_le_exp j L) (abs_truncTest_le_const j L) y

theorem abs_crossCorr_xiShiftedGammaTest_le (j : ℕ) (y : ℝ) :
    |crossCorr (𝔽 j) (𝔽 j) y| ≤ (decayConst * gammaScale j) ^ 2 * absMass :=
  abs_integral_mul_shift_le (mul_nonneg decayConst_nonneg (gammaScale_nonneg j))
    (abs_xiShiftedGammaTest_le_exp j) (abs_xiShiftedGammaTest_le_const j) y

theorem continuous_xiShiftedGammaTest (j : ℕ) : Continuous (𝔽 j) := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  exact (hF j).1.continuous

theorem integrable_xiShiftedGammaTest_mul_shift (j : ℕ) (y : ℝ) :
    Integrable fun t => 𝔽 j t * 𝔽 j (t - y) := by
  have hA := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  have hc := continuous_xiShiftedGammaTest j
  refine (integrable_exp_neg_abs.const_mul ((decayConst * gammaScale j) ^ 2)).mono'
    (hc.mul (hc.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |𝔽 j t| * |𝔽 j (t - y)|
      ≤ (decayConst * gammaScale j * Real.exp (-|t|)) * (decayConst * gammaScale j) :=
        mul_le_mul (abs_xiShiftedGammaTest_le_exp j t) (abs_xiShiftedGammaTest_le_const j _)
          (abs_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
    _ = _ := by ring

theorem integrable_truncTest_mul_shift (j : ℕ) (L y : ℝ) :
    Integrable fun t => truncTest (𝔽 j) L t * truncTest (𝔽 j) L (t - y) := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  have hc := (contDiff_truncTest (hF j).1 L).continuous
  exact integrable_translate_prod hc (hasCompactSupport_truncTest _ L) hc y

/-- **The correlations of a truncation deviate by the doubly exponential tail.** -/
theorem abs_crossCorr_truncTest_sub_le (j : ℕ) (L y : ℝ) :
    |crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) y - crossCorr (𝔽 j) (𝔽 j) y| ≤
      2 * absMass * (decayConst * gammaScale j) ^ 2 * doubleExpTail (L - 1) := by
  set A := decayConst * gammaScale j with hA
  have hA0 : 0 ≤ A := mul_nonneg decayConst_nonneg (gammaScale_nonneg j)
  set τ := doubleExpTail (L - 1) with hτ
  have hτ0 : 0 ≤ τ := (doubleExpTail_pos _).le
  unfold crossCorr
  rw [← integral_sub (integrable_truncTest_mul_shift j L y)
    (integrable_xiShiftedGammaTest_mul_shift j y)]
  have hg1 : Integrable fun t : ℝ => A ^ 2 * τ * Real.exp (-|t|) :=
    integrable_exp_neg_abs.const_mul _
  have hg2 : Integrable fun t : ℝ => A ^ 2 * τ * Real.exp (-|t - y|) :=
    (integrable_exp_neg_abs.comp_sub_right y).const_mul _
  have hg := hg1.add hg2
  have h := norm_integral_le_of_norm_le
    (f := fun t => truncTest (𝔽 j) L t * truncTest (𝔽 j) L (t - y) - 𝔽 j t * 𝔽 j (t - y)) hg
    (Eventually.of_forall fun t => by
      have e : truncTest (𝔽 j) L t * truncTest (𝔽 j) L (t - y) - 𝔽 j t * 𝔽 j (t - y) =
          (truncTest (𝔽 j) L t - 𝔽 j t) * truncTest (𝔽 j) L (t - y) +
            𝔽 j t * (truncTest (𝔽 j) L (t - y) - 𝔽 j (t - y)) := by ring
      have e1 := abs_truncTest_sub_le j L t
      have e2 := abs_truncTest_sub_le j L (t - y)
      have e3 := abs_truncTest_le_const j L (t - y)
      have e4 := abs_xiShiftedGammaTest_le_const j t
      rw [← hA, ← hτ] at e1 e2
      rw [← hA] at e3 e4
      rw [Real.norm_eq_abs, e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have p1 := mul_le_mul e1 e3 (abs_nonneg _) (by positivity)
      have p2 := mul_le_mul e4 e2 (abs_nonneg _) hA0
      simp only [Pi.add_apply]
      nlinarith)
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [integral_add' hg1 hg2, integral_const_mul, integral_const_mul,
    integral_sub_right_eq_self (fun t : ℝ => Real.exp (-|t|)) y]
  unfold absMass
  ring

/-! ### The sum over the family -/

theorem summable_mul_crossCorr_null {w : ℕ → ℝ} (hw : NullWeights w) (L y : ℝ) :
    Summable fun j => w j *
      crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) y := by
  refine Summable.of_norm_bounded
    (g := fun j => (decayConst ^ 2 * absMass) * (w j * gammaScale j ^ 2))
    (hw.summable.mul_left _) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg j)]
  calc w j * |crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) y|
      ≤ w j * ((decayConst * gammaScale j) ^ 2 * absMass) :=
        mul_le_mul_of_nonneg_left (abs_crossCorr_truncTest_null_le j L y) (hw.nonneg j)
    _ = _ := by ring

theorem summable_mul_crossCorr_test {w : ℕ → ℝ} (hw : NullWeights w) (y : ℝ) :
    Summable fun j => w j * crossCorr (𝔽 j) (𝔽 j) y := by
  refine Summable.of_norm_bounded
    (g := fun j => (decayConst ^ 2 * absMass) * (w j * gammaScale j ^ 2))
    (hw.summable.mul_left _) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg j)]
  calc w j * |crossCorr (𝔽 j) (𝔽 j) y|
      ≤ w j * ((decayConst * gammaScale j) ^ 2 * absMass) :=
        mul_le_mul_of_nonneg_left (abs_crossCorr_xiShiftedGammaTest_le j y) (hw.nonneg j)
    _ = _ := by ring

/-- **Joint blindness survives truncation up to the tail.** -/
theorem abs_tsum_crossCorr_null_le {w : ℕ → ℝ} (hw : NullWeights w) (L : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    |∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)| ≤
      (2 * absMass * decayConst ^ 2 * ∑' j, w j * gammaScale j ^ 2) * doubleExpTail (L - 1) := by
  have h1 := summable_mul_crossCorr_null hw L (Real.log n)
  have h2 := summable_mul_crossCorr_test hw (Real.log n)
  have hsub : (∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) =
      ∑' j, w j * (crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n) -
        crossCorr (𝔽 j) (𝔽 j) (Real.log n)) := by
    have := h1.tsum_sub h2
    rw [hw.blind n hn, sub_zero] at this
    rw [← this]
    exact tsum_congr fun j => by ring
  rw [hsub, ← Real.norm_eq_abs]
  set c := 2 * absMass * decayConst ^ 2 * doubleExpTail (L - 1) with hc
  have hsum : HasSum (fun j => c * (w j * gammaScale j ^ 2)) (c * ∑' j, w j * gammaScale j ^ 2) :=
    hw.summable.hasSum.mul_left c
  refine (tsum_of_norm_bounded hsum (f := fun j => w j *
    (crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n) -
      crossCorr (𝔽 j) (𝔽 j) (Real.log n))) fun j => ?_).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg j)]
    calc w j * |crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n) -
          crossCorr (𝔽 j) (𝔽 j) (Real.log n)|
        ≤ w j * (2 * absMass * (decayConst * gammaScale j) ^ 2 * doubleExpTail (L - 1)) :=
          mul_le_mul_of_nonneg_left (abs_crossCorr_truncTest_sub_le j L _) (hw.nonneg j)
      _ = _ := by rw [hc]; ring
  · rw [hc]
    ring

/-! ### Weil's functional on the family -/

/-- The truncated family as complex tests. -/
def nullTest (j : ℕ) (L u : ℝ) : ℂ := (truncTest (𝔽 j) L u : ℂ)

/-- The energy of the weights `lam` on the truncated family member `F_{j,L}`. -/
def nullEnergy (lam : ℕ → ℝ) (j : ℕ) (L : ℝ) : ℝ :=
  (weilFullFunctional lam (EF.weilTest (nullTest j L) (nullTest j L))).re

theorem contDiff_nullTest (j : ℕ) (L : ℝ) : ContDiff ℝ 2 (nullTest j L) := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  exact contDiff_ofReal_truncTest (hF j).1 L

theorem tsupport_nullTest_subset (j : ℕ) {L c : ℝ} (hLc : L ≤ c) :
    tsupport (nullTest j L) ⊆ Icc (-c) c := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have hlt : |u| < L := by
    by_contra hcon
    apply hu
    simp [nullTest, truncTest_eq_zero (not_lt.mp hcon)]
  exact abs_le.mp (hlt.le.trans hLc)

/-- The energy splits into the zero side and the prime pairing of `λ − Λ`. -/
theorem nullEnergy_eq (lam : ℕ → ℝ) (j : ℕ) (L : ℝ) :
    nullEnergy lam j L =
      (zetaZeroConfig.W (fun u => (truncTest (𝔽 j) L u : ℂ))
        (fun u => (truncTest (𝔽 j) L u : ℂ))).re -
        atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L)) := by
  have h := re_weilFullFunctional_add_eq (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ))
    (F := truncTest (𝔽 j) L) (contDiff_nullTest j L) (hasCompactSupport_truncTest _ L)
  have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) +
      (lam n - (ArithmeticFunction.vonMangoldt n : ℝ))) = lam := funext fun n => by ring
  rw [hfun] at h
  exact h

/-- The number of integers the window of radius `L` can see, plus one. -/
def seenCount (L : ℝ) : ℕ := ⌊Real.exp (2 * L)⌋₊ + 1

theorem atomPairing_null_eq (v : ℕ → ℝ) (j : ℕ) (L : ℝ) :
    atomPairing v (crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L)) =
      ∑ n ∈ Finset.range (seenCount L), (if 2 ≤ n then v n / Real.sqrt n else 0) *
        (2 * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) := by
  unfold atomPairing
  rw [tsum_eq_sum (s := Finset.range (seenCount L)) fun n hn => ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [crossCorr_self_neg]
    ring
  · rw [Finset.mem_range, not_lt] at hn
    have hlt : Real.exp (2 * L) < n := by
      have h1 := Nat.lt_floor_add_one (Real.exp (2 * L))
      have h2 : ((seenCount L : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      unfold seenCount at h2
      push_cast at h2
      linarith
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hlt
    have hlog : 2 * L < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hlt
    have hab : 2 * L ≤ |Real.log n| := hlog.le.trans (le_abs_self _)
    rw [crossCorr_truncTest_eq_zero _ hab,
      crossCorr_truncTest_eq_zero _ (by rwa [abs_neg] : 2 * L ≤ |-Real.log n|)]
    simp

/-- **The family bound.** On the truncated family, Weil's functional of *any* weights is at most
`K (1 + V)(e^{2L} + 1) exp(−(π/16) e^{2(L−1)})`, where `V` bounds `|λ(n) − Λ(n)|/√n` on the integers
the window sees. -/
theorem exists_tsum_nullEnergy_le {w : ℕ → ℝ} (hw : NullWeights w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L V : ℝ) (lam : ℕ → ℝ), 0 ≤ V →
      (∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (2 * L) →
        |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / Real.sqrt n ≤ V) →
      Summable (fun j => w j * nullEnergy lam j L) ∧
        ∑' j, w j * nullEnergy lam j L ≤
          K * ((1 + V) * (Real.exp (2 * L) + 1)) * doubleExpTail (L - 1) := by
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set B := ∑' j, w j * gammaScale j ^ 2 with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun j => mul_nonneg (hw.nonneg j) (sq_nonneg _)
  have hI := absMass_nonneg
  have hZs : 0 ≤ zetaInvSqSum := zetaInvSqSum_nonneg
  set Z₀ := (5 / 4) * zetaInvSqSum * ((3 + 4 * Λc) * decayConst * absMass) ^ 2 with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := by positivity
  set P₀ := 2 * absMass * decayConst ^ 2 * B with hP₀
  have hP₀0 : 0 ≤ P₀ := by positivity
  refine ⟨Z₀ * B + 2 * P₀, by positivity, fun L V lam hV hbound => ?_⟩
  set τ := doubleExpTail (L - 1) with hτ
  have hτ0 : 0 ≤ τ := (doubleExpTail_pos _).le
  have hτ1 : τ ≤ 1 := doubleExpTail_le_one _
  set v : ℕ → ℝ := fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ) with hv
  set c : ℕ → ℝ := fun n => if 2 ≤ n then v n / Real.sqrt n else 0 with hc
  set Z : ℕ → ℝ := fun j => (zetaZeroConfig.W (fun u => (truncTest (𝔽 j) L u : ℂ))
    (fun u => (truncTest (𝔽 j) L u : ℂ))).re with hZ
  have hZb : ∀ j, |Z j| ≤ Z₀ * gammaScale j ^ 2 * τ ^ 2 :=
    fun j => abs_re_W_truncTest_null_le hΛ0 hΛ j L
  have hsumZ : Summable fun j => w j * Z j := by
    refine Summable.of_norm_bounded (g := fun j => (Z₀ * τ ^ 2) * (w j * gammaScale j ^ 2))
      (hw.summable.mul_left _) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg j)]
    calc w j * |Z j| ≤ w j * (Z₀ * gammaScale j ^ 2 * τ ^ 2) :=
          mul_le_mul_of_nonneg_left (hZb j) (hw.nonneg j)
      _ = _ := by ring
  have hsumC : ∀ n, Summable fun j => w j *
      crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n) :=
    fun n => summable_mul_crossCorr_null hw L _
  have hsplit : ∀ j, w j * nullEnergy lam j L = w j * Z j -
      ∑ n ∈ Finset.range (seenCount L), c n * 2 *
        (w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) := by
    intro j
    rw [nullEnergy_eq, atomPairing_null_eq, mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hsumS : ∀ n ∈ Finset.range (seenCount L), Summable fun j => c n * 2 *
      (w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) :=
    fun n _ => (hsumC n).mul_left _
  have hsumF : Summable fun j => ∑ n ∈ Finset.range (seenCount L), c n * 2 *
      (w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) :=
    summable_sum hsumS
  have hfun : (fun j => w j * nullEnergy lam j L) = fun j => w j * Z j -
      ∑ n ∈ Finset.range (seenCount L), c n * 2 *
        (w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) := funext hsplit
  rw [hfun]
  refine ⟨hsumZ.sub hsumF, ?_⟩
  have hrw : (∑' j, ∑ n ∈ Finset.range (seenCount L), c n * 2 *
      (w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n))) =
      ∑ n ∈ Finset.range (seenCount L), c n * 2 *
        ∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n) := by
    rw [Summable.tsum_finsetSum hsumS]
    exact Finset.sum_congr rfl fun n _ => tsum_mul_left
  rw [hsumZ.tsum_sub hsumF, hrw]
  -- the zero side
  have hzero : ∑' j, w j * Z j ≤ Z₀ * B * τ := by
    have hsum : HasSum (fun j => (Z₀ * τ ^ 2) * (w j * gammaScale j ^ 2)) ((Z₀ * τ ^ 2) * B) :=
      hw.summable.hasSum.mul_left _
    have hb := tsum_of_norm_bounded hsum (f := fun j => w j * Z j) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.nonneg j)]
      calc w j * |Z j| ≤ w j * (Z₀ * gammaScale j ^ 2 * τ ^ 2) :=
            mul_le_mul_of_nonneg_left (hZb j) (hw.nonneg j)
        _ = _ := by ring
    rw [Real.norm_eq_abs] at hb
    have h1 := (le_abs_self _).trans hb
    have h2 : τ ^ 2 ≤ τ := by nlinarith
    have h3 : Z₀ * τ ^ 2 * B ≤ Z₀ * τ * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hZ₀0) hB0
    calc ∑' j, w j * Z j ≤ Z₀ * τ ^ 2 * B := h1
      _ ≤ Z₀ * τ * B := h3
      _ = _ := by ring
  -- the prime side
  have hterm : ∀ n ∈ Finset.range (seenCount L),
      -(c n * 2 * ∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) ≤
        2 * V * (P₀ * τ) := by
    intro n hn
    have hnon : 0 ≤ 2 * V * (P₀ * τ) := by positivity
    by_cases h2 : 2 ≤ n
    · have hcn : |c n| ≤ V := by
        simp only [hc, if_pos h2]
        have hle : (n : ℝ) ≤ Real.exp (2 * L) := by
          have hn' : n ≤ ⌊Real.exp (2 * L)⌋₊ := by
            have := Finset.mem_range.mp hn
            unfold seenCount at this
            omega
          exact (Nat.le_floor_iff (Real.exp_pos _).le).mp hn'
        have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
        rw [abs_div, abs_of_nonneg hs]
        exact hbound n h2 hle
      have hS : |∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)| ≤
          P₀ * τ := abs_tsum_crossCorr_null_le hw L h2
      obtain ⟨S, hSdef⟩ : ∃ S, S = ∑' j, w j *
        crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n) := ⟨_, rfl⟩
      rw [← hSdef] at hS ⊢
      have habs : |c n * 2 * S| = 2 * (|c n| * |S|) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
      have hmul : |c n| * |S| ≤ V * (P₀ * τ) := mul_le_mul hcn hS (abs_nonneg _) hV
      have := neg_abs_le (c n * 2 * S)
      nlinarith
    · simp only [hc, if_neg h2, zero_mul, neg_zero]
      exact hnon
  have hsumNeg : -(∑ n ∈ Finset.range (seenCount L), c n * 2 *
      ∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)) ≤
      (seenCount L : ℝ) * (2 * V * (P₀ * τ)) := by
    rw [← Finset.sum_neg_distrib]
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Finset.card_range, nsmul_eq_mul] at this
    exact this
  -- assembly
  have hE : 0 < Real.exp (2 * L) := Real.exp_pos _
  have hN : (seenCount L : ℝ) ≤ Real.exp (2 * L) + 1 := by
    unfold seenCount
    push_cast
    linarith [Nat.floor_le hE.le]
  set R := (1 + V) * (Real.exp (2 * L) + 1) with hR
  have hR1 : 1 ≤ R := by
    rw [hR]
    nlinarith
  have hN2 : (seenCount L : ℝ) * (2 * V * (P₀ * τ)) ≤ 2 * P₀ * R * τ := by
    have h0 : 0 ≤ 2 * V * (P₀ * τ) := by positivity
    calc (seenCount L : ℝ) * (2 * V * (P₀ * τ))
        ≤ (Real.exp (2 * L) + 1) * (2 * V * (P₀ * τ)) := mul_le_mul_of_nonneg_right hN h0
      _ ≤ 2 * P₀ * R * τ := by
          rw [hR]
          have h1 : 0 ≤ P₀ * τ * (Real.exp (2 * L) + 1) := by positivity
          nlinarith
  have hZ2 : Z₀ * B * τ ≤ Z₀ * B * R * τ := by
    have h0 : 0 ≤ Z₀ * B * τ := by positivity
    nlinarith
  calc ∑' j, w j * Z j - ∑ n ∈ Finset.range (seenCount L), c n * 2 *
        ∑' j, w j * crossCorr (truncTest (𝔽 j) L) (truncTest (𝔽 j) L) (Real.log n)
      ≤ Z₀ * B * τ + (seenCount L : ℝ) * (2 * V * (P₀ * τ)) := by linarith
    _ ≤ Z₀ * B * R * τ + 2 * P₀ * R * τ := add_le_add hZ2 hN2
    _ = (Z₀ * B + 2 * P₀) * R * τ := by ring

/-! ### Points of the window cone -/

theorem boxConst_nonneg : 0 ≤ boxConst := by
  unfold boxConst
  have h1 := _root_.RHTower.ResonatorProfile.profileRatio_nonneg
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- Positivity on a window bounds the deviation from `Λ` on the integers a smaller radius sees. -/
theorem abs_sub_vonMangoldt_div_sqrt_le {lam : ℕ → ℝ} {c L : ℝ}
    (h : WeilPositiveFullUpTo lam c) (hLc : L + 1 / 12 ≤ c) {n : ℕ} (hn : 2 ≤ n)
    (hnL : (n : ℝ) ≤ Real.exp (2 * L)) :
    |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| / Real.sqrt n ≤ 4 * L + boxConst := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : Real.log n ≤ 2 * L := (Real.log_le_iff_le_exp hn0).mpr hnL
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlev : atomLevel n ≤ c := by
    unfold atomLevel
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hbox := abs_le_boxWidth_of_weilPositiveUpTo
    (weilPositiveUpTo_of_weilPositiveFullUpTo h) hn hlev
  have hs : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hC := boxConst_nonneg
  have hw : boxWidth n = Real.sqrt n * (Real.log n + boxConst) := by
    unfold boxWidth
    exact abs_of_nonneg (by positivity)
  rw [hw] at hbox
  have hΛ0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ1 : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
    ArithmeticFunction.vonMangoldt_le_log
  have h1 : |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| ≤
      |lam n| + (ArithmeticFunction.vonMangoldt n : ℝ) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hΛ0]
  rw [div_le_iff₀ (by linarith)]
  have h2 : Real.log n ≤ Real.sqrt n * Real.log n := le_mul_of_one_le_left hlog0 hs
  have h3 : Real.sqrt n * (2 * Real.log n) ≤ Real.sqrt n * (4 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/-- The ceiling `exp(3c − (π/16) e^{2(c−2)})`. -/
def marginCeiling (c : ℝ) : ℝ := Real.exp (3 * c - Real.pi / 16 * Real.exp (2 * (c - 2)))

theorem marginCeiling_pos (c : ℝ) : 0 < marginCeiling c := Real.exp_pos _

theorem exp_mul_doubleExpTail (c : ℝ) :
    Real.exp (3 * c) * doubleExpTail (c - 2) = marginCeiling c := by
  unfold doubleExpTail marginCeiling
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Near-nullity.** One family and one constant serve the whole cone: every `λ ∈ 𝒜(c)` has family
energy at most `K exp(3c − (π/16) e^{2(c−2)})`. -/
theorem exists_nullWeights_tsum_nullEnergy_le :
    ∃ w : ℕ → ℝ, NullWeights w ∧ ∃ K : ℝ, 0 < K ∧ ∀ (c : ℝ) (lam : ℕ → ℝ), 1 ≤ c →
      WeilPositiveFullUpTo lam c →
        Summable (fun j => w j * nullEnergy lam j (c - 1 / 12)) ∧
          ∑' j, w j * nullEnergy lam j (c - 1 / 12) ≤ K * marginCeiling c := by
  obtain ⟨w, hw⟩ := exists_nullWeights
  obtain ⟨K, hK, hmain⟩ := exists_tsum_nullEnergy_le hw
  have hC := boxConst_nonneg
  refine ⟨w, hw, K * (2 * (5 + boxConst)) + 1, by positivity, fun c lam hc h => ?_⟩
  have hL0 : 0 ≤ c - 1 / 12 := by linarith
  have hV : 0 ≤ 4 * (c - 1 / 12) + boxConst := by linarith
  obtain ⟨hs, hle⟩ := hmain (c - 1 / 12) (4 * (c - 1 / 12) + boxConst) lam hV
    (fun n hn hnL => abs_sub_vonMangoldt_div_sqrt_le h (by linarith) hn hnL)
  refine ⟨hs, hle.trans ?_⟩
  have hec : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
  have hfac1 : 1 + (4 * (c - 1 / 12) + boxConst) ≤ (5 + boxConst) * Real.exp c := by
    have h1 : (5 + boxConst) * (1 + c) ≤ (5 + boxConst) * Real.exp c :=
      mul_le_mul_of_nonneg_left hec (by linarith)
    nlinarith
  have hfac2 : Real.exp (2 * (c - 1 / 12)) + 1 ≤ 2 * Real.exp (2 * c) := by
    have h1 : Real.exp (2 * (c - 1 / 12)) ≤ Real.exp (2 * c) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (1 : ℝ) ≤ Real.exp (2 * c) := Real.one_le_exp (by linarith)
    linarith
  have hprod : (1 + (4 * (c - 1 / 12) + boxConst)) * (Real.exp (2 * (c - 1 / 12)) + 1) ≤
      2 * (5 + boxConst) * Real.exp (3 * c) := by
    have h3 : Real.exp (3 * c) = Real.exp c * Real.exp (2 * c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h3]
    calc _ ≤ ((5 + boxConst) * Real.exp c) * (2 * Real.exp (2 * c)) :=
          mul_le_mul hfac1 hfac2 (by positivity) (by positivity)
      _ = _ := by ring
  have hτ : doubleExpTail (c - 1 / 12 - 1) ≤ doubleExpTail (c - 2) :=
    doubleExpTail_anti (by linarith)
  have hτ0 := (doubleExpTail_pos (c - 1 / 12 - 1)).le
  have hM := marginCeiling_pos c
  calc K * ((1 + (4 * (c - 1 / 12) + boxConst)) * (Real.exp (2 * (c - 1 / 12)) + 1)) *
        doubleExpTail (c - 1 / 12 - 1)
      ≤ K * (2 * (5 + boxConst) * Real.exp (3 * c)) * doubleExpTail (c - 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hprod hK) hτ hτ0 (by positivity)
    _ = K * (2 * (5 + boxConst)) * (Real.exp (3 * c) * doubleExpTail (c - 2)) := by ring
    _ = K * (2 * (5 + boxConst)) * marginCeiling c := by rw [exp_mul_doubleExpTail]
    _ ≤ _ := by nlinarith

/-- `F₀ = Φ` as a real function. -/
theorem xiShiftedGammaTest_zero_eq_real (x : ℝ) : 𝔽 0 x = riemannKernelReal x := by
  have h := xiShiftedGammaTest_zero_eq x
  rw [riemannPhiKernel_eq_ofReal] at h
  exact_mod_cast h

/-- The mass of `Φ` on `[−1, 1]`. -/
def kernelCoreMass : ℝ := ∫ u in (-1 : ℝ)..1, riemannKernelReal u ^ 2

theorem kernelCoreMass_pos : 0 < kernelCoreMass := by
  have hc : Continuous fun u => riemannKernelReal u ^ 2 := continuous_riemannKernelReal.pow 2
  exact intervalIntegral.intervalIntegral_pos_of_pos (hc.intervalIntegrable _ _)
    (fun x => pow_pos (riemannKernelReal_pos x) 2) (by norm_num)

theorem kernelCoreMass_le_mass {L : ℝ} (hL : 2 ≤ L) :
    kernelCoreMass ≤ ∫ u, ‖nullTest 0 L u‖ ^ 2 := by
  have hc : Continuous fun u => ‖nullTest 0 L u‖ ^ 2 := (contDiff_nullTest 0 L).continuous.norm.pow 2
  have hcs : HasCompactSupport fun u => ‖nullTest 0 L u‖ ^ 2 :=
    (hasCompactSupport_truncTest (𝔽 0) L).comp_left
      (g := fun t : ℝ => ‖(t : ℂ)‖ ^ 2) (by simp)
  have hi : Integrable fun u => ‖nullTest 0 L u‖ ^ 2 := hc.integrable_of_hasCompactSupport hcs
  unfold kernelCoreMass
  rw [intervalIntegral.integral_of_le (by norm_num)]
  have heq : ∫ u in Ioc (-1 : ℝ) 1, riemannKernelReal u ^ 2 =
      ∫ u in Ioc (-1 : ℝ) 1, ‖nullTest 0 L u‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu1 : |u| ≤ L - 1 := by
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
    simp only [nullTest, truncTest_eq_self hu1, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      xiShiftedGammaTest_zero_eq_real]
  rw [heq]
  exact setIntegral_le_integral hi (Eventually.of_forall fun u => by positivity)

/-- **The margin law.** No weight has a positive margin above `K exp(3c − (π/16) e^{2(c−2)})` on
`[−c, c]`, whatever the weights: slack from other weights is excluded at a doubly exponential rate. -/
theorem exists_margin_ceiling :
    ∃ K : ℝ, 0 < K ∧ ∀ (c m : ℝ) (lam : ℕ → ℝ), 3 ≤ c → 0 ≤ m →
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-c) c →
        m * ∫ u, ‖f u‖ ^ 2 ≤ (weilFullFunctional lam (EF.weilTest f f)).re) →
      m ≤ K * marginCeiling c := by
  obtain ⟨w, hw, K, hK, hmain⟩ := exists_nullWeights_tsum_nullEnergy_le
  have hw0 := hw.pos_zero
  have hμ := kernelCoreMass_pos
  refine ⟨K / (w 0 * kernelCoreMass), by positivity, fun c m lam hc hm hmargin => ?_⟩
  have hLc : c - 1 / 12 ≤ c := by linarith
  have hE : ∀ j, m * ∫ u, ‖nullTest j (c - 1 / 12) u‖ ^ 2 ≤ nullEnergy lam j (c - 1 / 12) :=
    fun j => hmargin _ (contDiff_nullTest j _) (tsupport_nullTest_subset j hLc)
  have hE0 : ∀ j, 0 ≤ nullEnergy lam j (c - 1 / 12) := fun j =>
    (mul_nonneg hm (integral_nonneg fun _ => by positivity)).trans (hE j)
  have hpos : WeilPositiveFullUpTo lam c := fun f hf hfs =>
    (mul_nonneg hm (integral_nonneg fun _ => by positivity)).trans (hmargin f hf hfs)
  obtain ⟨hs, hle⟩ := hmain c lam (by linarith) hpos
  have h0 : w 0 * nullEnergy lam 0 (c - 1 / 12) ≤ ∑' j, w j * nullEnergy lam j (c - 1 / 12) :=
    hs.le_tsum 0 fun j _ => mul_nonneg (hw.nonneg j) (hE0 j)
  have hmass := kernelCoreMass_le_mass (L := c - 1 / 12) (by linarith)
  have h1 : m * kernelCoreMass ≤ nullEnergy lam 0 (c - 1 / 12) :=
    (mul_le_mul_of_nonneg_left hmass hm).trans (hE 0)
  have h2 : w 0 * (m * kernelCoreMass) ≤ K * marginCeiling c :=
    (mul_le_mul_of_nonneg_left h1 hw0.le).trans (h0.trans hle)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
