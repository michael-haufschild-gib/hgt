import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineVariationalCompactness
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation

/-!
# The confined form has finite index at every ratio

At a fixed ratio `R > 0` the confined Weil form `Q_R = B + a(R) W₈` has only finitely many mutually
orthogonal unit directions on which it is nonpositive. The mechanism is confinement: on such a
direction, `Q_R = Q_{2R} + (a(R)/2) W₈` and the ground energy `λ(2R)` bound the confinement mass
`W₈`, and bounded confinement with bounded energy is `L²`-compact. An orthogonal unit family is
`√2`-separated in `L²`, so a compact set holds only finitely many of its members.

Consequently the critical ratios (where `Q_R` acquires a null direction) cannot accumulate at any
finite ratio: infinitely many zeros off the line can only produce critical ratios tending to `∞`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations

/-- A smooth compactly supported half-line test of unit mass on which `Q_R` is nonpositive. -/
def NonpositiveUnitTest (R : ℝ) (U : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 U ∧ HasCompactSupport U ∧ (∀ u, 0 ≤ u → U u = 0) ∧ (∫ u, U u ^ 2) = 1 ∧
    criticalHalfLineFullEnergy R U ≤ 0

theorem NonpositiveUnitTest.domain {R : ℝ} {U : ℝ → ℝ} (h : NonpositiveUnitTest R U) :
    CriticalHalfLineEnergyDomain U :=
  criticalHalfLineEnergyDomain_of_compact_negative h.1 h.2.1 h.2.2.1

/-- The confinement bound of the nonpositive cone at ratio `R`. -/
def confinementBound (R : ℝ) : ℝ :=
  max 0 (-(2 * criticalHalfLineGroundEnergy (2 * R)) / criticalAliasCoefficient R)

/-- **Nonpositive directions have bounded confinement.** -/
theorem exponentialMass_le_of_nonpositive {R : ℝ} (hR : 0 < R) {U : ℝ → ℝ}
    (h : NonpositiveUnitTest R U) :
    (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ confinementBound R := by
  have hd := h.domain
  have ha : 0 < criticalAliasCoefficient R := criticalAliasCoefficient_positive hR
  have hchange := criticalHalfLineFullEnergy_change_ratio R (2 * R) hd
  have hfloor := criticalHalfLineGroundEnergy_le (by linarith : 0 < 2 * R) hd h.2.2.2.1
  have h2 : criticalAliasCoefficient (2 * R) = criticalAliasCoefficient R / 2 := by
    rw [criticalAliasCoefficient_eq_div (2 * R), criticalAliasCoefficient_eq_div R]
    field_simp
  rw [h2] at hchange
  have hle : criticalAliasCoefficient R / 2 * (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤
      -criticalHalfLineGroundEnergy (2 * R) := by
    have := h.2.2.2.2
    nlinarith only [hchange, hfloor, this]
  unfold confinementBound
  refine le_max_of_le_right ?_
  rw [le_div_iff₀ ha]
  linarith only [hle]

/-- Pointwise parallelogram bound, integrated: `‖U - V‖² ≤ 2‖U - P‖² + 2‖V - P‖²`. -/
theorem integral_sq_sub_le {U V P : ℝ → ℝ}
    (hUP : Integrable fun u => (U u - P u) ^ 2) (hVP : Integrable fun u => (V u - P u) ^ 2)
    (hUV : Integrable fun u => (U u - V u) ^ 2) :
    (∫ u, (U u - V u) ^ 2) ≤ 2 * (∫ u, (U u - P u) ^ 2) + 2 * ∫ u, (V u - P u) ^ 2 := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hUP.const_mul 2) (hVP.const_mul 2)]
  exact integral_mono hUV ((hUP.const_mul 2).add (hVP.const_mul 2)) fun u => by
    dsimp only
    nlinarith [sq_nonneg (U u + V u - 2 * P u)]

theorem integrable_sq_sub {U V : ℝ → ℝ} (hU : Integrable fun u => U u ^ 2)
    (hV : Integrable fun u => V u ^ 2) (hUm : Measurable U) (hVm : Measurable V) :
    Integrable fun u => (U u - V u) ^ 2 := by
  refine ((hU.add hV).const_mul 2).mono' ((hUm.sub hVm).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  dsimp only [Pi.add_apply]
  nlinarith [sq_nonneg (U u + V u)]

/-- Two orthogonal unit tests are at squared distance `2`. -/
theorem integral_sq_sub_of_orthonormal {U V : ℝ → ℝ} (hU : Integrable fun u => U u ^ 2)
    (hV : Integrable fun u => V u ^ 2) (hUm : Measurable U) (hVm : Measurable V)
    (hU1 : (∫ u, U u ^ 2) = 1) (hV1 : (∫ u, V u ^ 2) = 1) (hUV : (∫ u, U u * V u) = 0) :
    (∫ u, (U u - V u) ^ 2) = 2 := by
  have hm : Integrable fun u => U u * V u := by
    refine ((hU.add hV).div_const 2).mono' (hUm.mul hVm).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]
    dsimp only [Pi.add_apply]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (U u + V u), sq_nonneg (U u - V u)]
  have he : (fun u => (U u - V u) ^ 2) = fun u => U u ^ 2 + V u ^ 2 - 2 * (U u * V u) := by
    funext u; ring
  have hsum : Integrable fun u => U u ^ 2 + V u ^ 2 := hU.add hV
  rw [he, integral_sub hsum (hm.const_mul 2), integral_add hU hV, integral_const_mul,
    hU1, hV1, hUV]
  ring

/-- **Finite index at every ratio.** At each ratio `R > 0` there is a bound `N` on the size of
every `L²`-orthonormal family of smooth half-line tests on which the confined form is nonpositive. -/
theorem exists_bound_orthonormal_nonpositive {R : ℝ} (hR : 0 < R) :
    ∃ N : ℕ, ∀ (n : ℕ) (U : Fin n → ℝ → ℝ), (∀ i, NonpositiveUnitTest R (U i)) →
      (∀ i j, i ≠ j → (∫ u, U i u * U j u) = 0) → n ≤ N := by
  by_contra hcon
  push Not at hcon
  -- greedy separated sequence in the nonpositive cone
  have hstep : ∀ s : Finset (ℝ → ℝ), (∀ x ∈ s, NonpositiveUnitTest R x) →
      ∃ y, NonpositiveUnitTest R y ∧ ∀ x ∈ s, (1 : ℝ) / 4 ≤ ∫ u, (x u - y u) ^ 2 := by
    intro s hs
    obtain ⟨n, U, hU, horth, hn⟩ := hcon s.card
    by_contra hall
    push Not at hall
    have hcap : ∀ i, ∃ x ∈ s, (∫ u, (x u - U i u) ^ 2) < 1 / 4 := fun i => hall (U i) (hU i)
    choose f hfs hfd using hcap
    have hinj : Function.Injective fun i => (⟨f i, hfs i⟩ : s) := by
      intro i j hij
      by_contra hne
      have hfij : f i = f j := congrArg Subtype.val hij
      have hdi := (hU i).domain
      have hdj := (hU j).domain
      have hdx := (hs _ (hfs i)).domain
      have h2 := integral_sq_sub_of_orthonormal hdi.sq hdj.sq hdi.meas hdj.meas (hU i).2.2.2.1
        (hU j).2.2.2.1 (horth i j hne)
      have hle := integral_sq_sub_le (P := f i)
        (integrable_sq_sub hdi.sq hdx.sq hdi.meas hdx.meas)
        (integrable_sq_sub hdj.sq hdx.sq hdj.meas hdx.meas)
        (integrable_sq_sub hdi.sq hdj.sq hdi.meas hdj.meas)
      have e1 : (∫ u, (U i u - f i u) ^ 2) = ∫ u, (f i u - U i u) ^ 2 := by
        congr 1; funext u; ring
      have e2 : (∫ u, (U j u - f i u) ^ 2) = ∫ u, (f j u - U j u) ^ 2 := by
        rw [hfij]; congr 1; funext u; ring
      have := hfd i
      have := hfd j
      linarith
    have := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  obtain ⟨f, hfP, hfsep⟩ := exists_seq_of_forall_finset_exists (NonpositiveUnitTest R)
    (fun x y => (1 : ℝ) / 4 ≤ ∫ u, (x u - y u) ^ 2) hstep
  -- bounded energies have a convergent subsequence
  have henergy : ∀ k, criticalHalfLineFullEnergy R (f k) ∈
      Icc (criticalHalfLineGroundEnergy R) 0 := fun k =>
    ⟨criticalHalfLineGroundEnergy_le hR (hfP k).domain (hfP k).2.2.2.1, (hfP k).2.2.2.2⟩
  obtain ⟨L, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc _ _) henergy
  -- compactness of bounded confinement
  obtain ⟨F, s, hs, hFd, -, -, -, hL2, -⟩ := exists_domain_limit_of_smooth_energy_limit hR
    (U := fun k => f (φ k)) (fun k => (hfP (φ k)).domain) (fun k => (hfP (φ k)).1)
    (fun k => (hfP (φ k)).2.1) (fun k => (hfP (φ k)).2.2.2.1.le)
    (by simp only [(hfP _).2.2.2.1]; exact tendsto_const_nhds)
    (le_max_left 0 _) (fun k => exponentialMass_le_of_nonpositive hR (hfP (φ k)))
    (fun k => (hfP (φ k)).2.2.2.2) hlim
  have hev : ∀ᶠ k in atTop, (∫ u, (f (φ (s k)) u - F u) ^ 2) < 1 / 20 :=
    (tendsto_order.mp hL2).2 _ (by norm_num)
  obtain ⟨k, hk⟩ := hev.exists_forall_of_atTop
  have hk1 := hk k le_rfl
  have hk2 := hk (k + 1) (Nat.le_succ k)
  have hlt : φ (s k) < φ (s (k + 1)) := hφ (hs (Nat.lt_succ_self k))
  have hsep := hfsep _ _ hlt
  have hdk := (hfP (φ (s k))).domain
  have hdk1 := (hfP (φ (s (k + 1)))).domain
  have hle := integral_sq_sub_le (P := F)
    (integrable_sq_sub hdk.sq hFd.sq hdk.meas hFd.meas)
    (integrable_sq_sub hdk1.sq hFd.sq hdk1.meas hFd.meas)
    (integrable_sq_sub hdk.sq hdk1.sq hdk.meas hdk1.meas)
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
