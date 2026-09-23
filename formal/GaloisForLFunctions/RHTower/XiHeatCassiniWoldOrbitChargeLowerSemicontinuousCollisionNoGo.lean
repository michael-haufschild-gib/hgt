import GaloisForLFunctions.RHTower.XiHeatCassiniWoldOrbitChargeQuantization
import GaloisForLFunctions.RHTower.SymmetricShiftMultiplicity
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization

/-!
# Lower-semicontinuous collision no-go for reflected Wold orbit charge

The reflected physical Wold charge has exact multiplicity energy `2 * m^(2 : ℕ)`. This module tests
that quadratic law on a source-faithful local divisor collision. Two simple off-wall zeros of an
explicit entire quadratic merge into one double off-wall zero under compact-open convergence. The
Wold energy jumps from `4` to `8`, so no scalar reporter exact on this collision can be sequentially
lower semicontinuous.

Combined with the upper-semicontinuous escape no-go, this eliminates both one-sided
semicontinuous scalar directions for a coefficient-faithful T2 descent. The positive survivor is
an exact classification: additive scalar collision weights are precisely linear in multiplicity.
Thus any collision-stable scalar replacement must linearize multiplicity before attempting a
noncompact completion. No RH assumption, Xi zero, numerical certificate, or new axiom occurs.
-/

open Complex Filter Set Topology

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Fixed strict-right center used by the source-faithful divisor collision. -/
def woldCollisionCenter : ℂ := (3 / 4 : ℝ)

/-- Positive collision scale, bounded by `1/8` and tending to zero. -/
def woldCollisionScale (n : ℕ) : ℝ :=
  1 / (8 * ((n + 1 : ℕ) : ℝ))

/-- Simple entire source whose root is the collision center. -/
def woldCollisionBaseSource (z : ℂ) : ℂ :=
  z - woldCollisionCenter

/-- Symmetric shift with two separated simple roots. -/
def woldSimplePairCollisionSource (n : ℕ) : ℂ → ℂ :=
  symmetricShiftProduct woldCollisionBaseSource (woldCollisionScale n)

/-- Zero-shift source with one double root. -/
def woldDoubleCollisionSource : ℂ → ℂ :=
  symmetricShiftProduct woldCollisionBaseSource 0

theorem woldCollisionScale_pos (n : ℕ) :
    0 < woldCollisionScale n := by
  unfold woldCollisionScale
  positivity

theorem woldCollisionScale_le_eighth (n : ℕ) :
    woldCollisionScale n ≤ 1 / 8 := by
  rw [woldCollisionScale, div_le_iff₀ (by positivity :
    (0 : ℝ) < 8 * ((n + 1 : ℕ) : ℝ))]
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  norm_num at ⊢
  nlinarith

private theorem tendsto_nat_succ_atTop :
    Tendsto (fun n : ℕ => n + 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

theorem woldCollisionScale_tendsto_zero :
    Tendsto woldCollisionScale atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_succ_atTop
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hcast
  have hconst : Tendsto (fun _ : ℕ => (1 / 8 : ℝ)) atTop (𝓝 (1 / 8 : ℝ)) :=
    tendsto_const_nhds
  have hmul := hconst.mul hinv
  have hmul0 : Tendsto
      (fun n : ℕ => (1 / 8 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 0) := by simpa using hmul
  convert hmul0 using 1
  funext n
  simp only [woldCollisionScale, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The separated simple-root sources converge compact-open to the double-root source. -/
theorem woldSimplePairCollisionSource_tendstoLocallyUniformly :
    TendstoLocallyUniformly woldSimplePairCollisionSource
      woldDoubleCollisionSource atTop := by
  have hscaleC : Tendsto (fun n => (woldCollisionScale n : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp woldCollisionScale_tendsto_zero
  have hsq : Tendsto (fun n => (woldCollisionScale n : ℂ) ^ (2 : ℕ)) atTop (𝓝 0) := by
    simpa using hscaleC.pow 2
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  refine ⟨Set.univ, univ_mem, ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hsq ε hε] with n hn y hy
  have hdiff :
      woldSimplePairCollisionSource n y - woldDoubleCollisionSource y =
        -(woldCollisionScale n : ℂ) ^ (2 : ℕ) := by
    simp [woldSimplePairCollisionSource, woldDoubleCollisionSource,
      symmetricShiftProduct, woldCollisionBaseSource]
    ring
  calc
    dist (woldDoubleCollisionSource y) (woldSimplePairCollisionSource n y) =
        ‖woldSimplePairCollisionSource n y - woldDoubleCollisionSource y‖ := by
      rw [dist_comm, dist_eq_norm]
    _ = ‖(woldCollisionScale n : ℂ) ^ (2 : ℕ)‖ := by rw [hdiff, norm_neg]
    _ = dist ((woldCollisionScale n : ℂ) ^ (2 : ℕ)) 0 := by simp [dist_eq_norm]
    _ < ε := hn

theorem woldCollisionBaseSource_analyticOnNhd :
    AnalyticOnNhd ℂ woldCollisionBaseSource Set.univ := by
  intro z hz
  unfold woldCollisionBaseSource
  fun_prop

theorem analyticOrderAt_woldCollisionBaseSource_center :
    analyticOrderAt woldCollisionBaseSource woldCollisionCenter = 1 := by
  change analyticOrderAt (fun z : ℂ => z - woldCollisionCenter)
    woldCollisionCenter = 1
  simpa only [pow_one, Nat.cast_one] using
    (GaloisForLFunctions.HTGeometry.analyticOrderAt_sub_pow_self
      woldCollisionCenter 1)

/-- The compact-open limit source has exact analytic multiplicity two at the center. -/
theorem analyticOrderAt_woldDoubleCollisionSource_center :
    analyticOrderAt woldDoubleCollisionSource woldCollisionCenter = 2 := by
  rw [woldDoubleCollisionSource,
    analyticOrderAt_symmetricShiftProduct_zero_shift
      woldCollisionBaseSource_analyticOnNhd]
  rw [analyticOrderAt_woldCollisionBaseSource_center]
  norm_num

/-- Every approximating source has two distinct roots of exact analytic multiplicity one. -/
theorem analyticOrderAt_woldSimplePairCollisionSource_pair (n : ℕ) :
    analyticOrderAt (woldSimplePairCollisionSource n)
        (woldCollisionCenter + (woldCollisionScale n : ℂ)) = 1 ∧
      analyticOrderAt (woldSimplePairCollisionSource n)
        (woldCollisionCenter - (woldCollisionScale n : ℂ)) = 1 := by
  have hs0 : woldCollisionScale n ≠ 0 := ne_of_gt (woldCollisionScale_pos n)
  have hpair := analyticOrderAt_symmetricShiftProduct_pair_eq_of_no_overlap
    woldCollisionBaseSource_analyticOnNhd (woldCollisionScale n) woldCollisionCenter
    (by simp [woldCollisionBaseSource, hs0])
    (by simp [woldCollisionBaseSource, hs0])
  simpa [woldSimplePairCollisionSource,
    analyticOrderAt_woldCollisionBaseSource_center] using hpair

/-- The double off-wall root has exact reflected Wold orbit-charge energy eight. -/
theorem woldDoubleCollisionOrbitChargeEnergy_eq_eight :
    principalPartOrbitChargeEnergy
        (xiHeatCassiniReflectedWoldPhysicalOrbitCharge woldCollisionCenter 2) = 8 := by
  rw [xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq]
  · norm_num
  · norm_num [woldCollisionCenter]
  · norm_num [woldCollisionCenter]
  · norm_num

/-- The two separated simple off-wall roots have total Wold orbit-charge energy four. -/
theorem woldSimplePairCollisionOrbitChargeEnergy_eq_four (n : ℕ) :
    principalPartOrbitChargeEnergy
          (xiHeatCassiniReflectedWoldPhysicalOrbitCharge
            (woldCollisionCenter + (woldCollisionScale n : ℂ)) 1) +
        principalPartOrbitChargeEnergy
          (xiHeatCassiniReflectedWoldPhysicalOrbitCharge
            (woldCollisionCenter - (woldCollisionScale n : ℂ)) 1) = 4 := by
  have hspos := woldCollisionScale_pos n
  have hsle := woldCollisionScale_le_eighth n
  rw [xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq,
    xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq]
  · norm_num
  · constructor <;> simp [woldCollisionCenter] <;> linarith
  · simp [woldCollisionCenter]
    linarith
  · norm_num
  · constructor <;> simp [woldCollisionCenter] <;> linarith
  · simp [woldCollisionCenter]
    linarith
  · norm_num

/-- A scalar reporter that is sequentially lower semicontinuous for locally uniform convergence. -/
def CompactOpenSequentialLowerReporter (Q : (ℂ → ℂ) → ℝ) : Prop :=
  ∀ (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    TendstoLocallyUniformly F f atTop →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, Q f ≤ Q (F n) + ε

/-- Exact Wold-energy reporting on the source-faithful simple-to-double collision family. -/
def WoldOrbitChargeCollisionExact (Q : (ℂ → ℂ) → ℝ) : Prop :=
  Q woldDoubleCollisionSource =
      principalPartOrbitChargeEnergy
        (xiHeatCassiniReflectedWoldPhysicalOrbitCharge woldCollisionCenter 2) ∧
    ∀ n : ℕ,
      Q (woldSimplePairCollisionSource n) =
        principalPartOrbitChargeEnergy
            (xiHeatCassiniReflectedWoldPhysicalOrbitCharge
              (woldCollisionCenter + (woldCollisionScale n : ℂ)) 1) +
          principalPartOrbitChargeEnergy
            (xiHeatCassiniReflectedWoldPhysicalOrbitCharge
              (woldCollisionCenter - (woldCollisionScale n : ℂ)) 1)

/-- Exact positive survivor: quadratic Wold energy has a four-unit upward collision defect. -/
theorem woldOrbitChargeCollision_exact_defect_eq_four
    (Q : (ℂ → ℂ) → ℝ) (hQ : WoldOrbitChargeCollisionExact Q) (n : ℕ) :
    Q woldDoubleCollisionSource = Q (woldSimplePairCollisionSource n) + 4 := by
  rw [hQ.1, hQ.2 n, woldDoubleCollisionOrbitChargeEnergy_eq_eight,
    woldSimplePairCollisionOrbitChargeEnergy_eq_four]
  norm_num

/-- **T2 lower-semicontinuous route kill.** No compact-open sequentially lower-semicontinuous
scalar reporter can be exact on the reflected Wold energy of even this explicit, source-faithful
two-simple-to-double divisor collision. -/
theorem no_compactOpenSequentialLowerReporter_exactOn_woldOrbitChargeCollision :
    ¬ ∃ Q : (ℂ → ℂ) → ℝ,
      CompactOpenSequentialLowerReporter Q ∧ WoldOrbitChargeCollisionExact Q := by
  rintro ⟨Q, hlower, hexact⟩
  have heventual := hlower woldSimplePairCollisionSource woldDoubleCollisionSource
    woldSimplePairCollisionSource_tendstoLocallyUniformly 1 (by norm_num)
  obtain ⟨n, hn⟩ := heventual.exists
  have hdefect := woldOrbitChargeCollision_exact_defect_eq_four Q hexact n
  linarith

/-- A scalar multiplicity law preserving zero mass under every binary collision. -/
def CollisionAdditiveMultiplicityWeight (w : ℕ → ℝ) : Prop :=
  w 0 = 0 ∧ ∀ m n : ℕ, w (m + n) = w m + w n

/-- **Positive survivor classification.** Collision-additive scalar multiplicity weights are
exactly the linear weights. -/
theorem collisionAdditiveMultiplicityWeight_iff_linear (w : ℕ → ℝ) :
    CollisionAdditiveMultiplicityWeight w ↔
      ∀ m : ℕ, w m = (m : ℝ) * w 1 := by
  constructor
  · rintro ⟨hzero, hadd⟩ m
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
        calc
          w m.succ = w (m + 1) := by rw [Nat.succ_eq_add_one]
          _ = w m + w 1 := hadd m 1
          _ = (m.succ : ℝ) * w 1 := by rw [ih]; push_cast; ring
  · intro hlinear
    constructor
    · simpa using hlinear 0
    · intro m n
      rw [hlinear (m + n), hlinear m, hlinear n]
      push_cast
      ring

end

end RHTower
