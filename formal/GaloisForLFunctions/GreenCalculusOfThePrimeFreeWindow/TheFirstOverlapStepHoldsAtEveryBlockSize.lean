import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt
import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenWeilFormHasAFloorAtAperture1881Over5000

/-!
# The first overlap step holds at every block size

The excess of an overlap step is controlled by the ground energy of one aperture, and at the
aperture of the first step the ground energy is positive.

* **Levels** (`overlapSchurLevel_nonneg_of_floor`, `windowExcess_eq_zero_of_floor`): if the
  neutral part of `(R, 2(R + a) + b]` is at least `c`, `0 ≤ c < 1/5000`, on its charge-free
  packets, the Schur complement of the dyadic middle is nonnegative at every level in
  `[−c, μ_{R+a})`. The window keeps one bound state down to the level `−c`.
* **The excess inside an aperture** (`schurStepExcess_eq_zero_of_le_groundEnergy`): let
  `log(ρ²/2) < 2A` and `ρ²/2 < Q + 1`. The windows of the steps of ratio `ρ` lie inside the
  aperture `A`, so the excess of these steps vanishes at every level `C ≥ −c`, for every
  `0 ≤ c < 1/5000` that is at most the ground energy of `A`. As a function of the ratio the
  excess is zero as long as `ρ²/2` stays inside an aperture of nonnegative ground energy.
* **The first step.** Weil's form has the floor `1/50000` on the even tests of the aperture
  `1881/5000` (`evenWeilFloor_firstStep`), so the ground energy of this aperture is at least
  `1/50000` (`one_div_50000_le_groundEnergy_firstStep`). Every window of ratio at most
  `10609/5000` has the gap `1/50000` (`hasGap_neutralWindow_firstStep`) and, for `R ≤ J`,
  exactly one bound state (`hermNegIndex_neutralWindow_firstStep`), at every block size and
  for every cutoff `Q ≥ 2`. On the two ends of a window of the first step
  `B G₊ Bᵀ + 1/50000 ⪯ N_e + (Bφ)(Bφ)ᵀ/μ` (`greenForm_firstStep`); the middle dressed by the
  attraction of both ends holds one bound state (`hermNegIndex_dressedMiddle_firstStep`,
  `dressedMiddle_wells_bound_firstStep`); the excess of the first step vanishes at every level
  `C ≥ −1/50000` (`schurStepExcess_firstStep`), and the ladder starts without loss
  (`levelAt_one`).

The step is the floor of Weil's form at its aperture, carried to the matrices. No bound for the
Green matrix of the middle enters.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### A floor of a window in the levels of its step -/

/-- **A floor of a window is a level of its step.** If the neutral part of `(R, 2(R + a) + b]`
is at least `c`, `0 ≤ c < 1/5000`, on the packets of charge zero, the Schur complement of the
dyadic middle is nonnegative at every level `C ≥ −c` below the binding energy of the middle:
the window shifted by `−c` has at most one negative square, and so has its middle. -/
theorem overlapSchurLevel_nonneg_of_floor {Q R a b : ℕ} (hR : 1 ≤ R) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c < 1 / 5000)
    (hfloor : ∀ z : Fin (a + (R + a) + b) → ℝ, ∑ i, z i = 0 →
      c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R (a + (R + a) + b) *ᵥ z))
    {C : ℝ} (hC : -c ≤ C) (hCμ : C < bindingEnergy (R + a)) (e : Fin a ⊕ Fin b → ℝ) :
    0 ≤ e ⬝ᵥ (overlapSchurLevel Q R a b C *ᵥ e) := by
  have hD : 1 ≤ R + a := by omega
  have hμ : -c < bindingEnergy (R + a) :=
    (neg_nonpos.mpr hc0).trans_lt (zero_lt_one.trans (one_lt_bindingEnergy hD))
  have hA := (oneBoundState_primeFreeMiddle hD).add_diagonal hμ
    (by linarith : (0 : ℝ) < 1 / 5000 + -c)
  have hidx : hermNegIndex ((neutralWindow Q R (a + (R + a) + b) +
      Matrix.diagonal fun _ => -c).map (↑) :
      Matrix (Fin (a + (R + a) + b)) (Fin (a + (R + a) + b)) ℂ) ≤ 1 := by
    refine hermNegIndex_le_one_of_nonneg_on_hyperplane _ (fun _ => 1) fun y hy => ?_
    have h := hfloor y (by simpa only [dotProduct, one_mul] using hy)
    rw [dotProduct_add_diagonal_mulVec, neg_mul]
    linarith
  rw [← hermNegIndex_map_submatrix _ (overlapEquiv a (R + a) b), submatrix_add_diagonal_equiv,
    neutralWindow_submatrix_overlapEquiv, neutralWindow_dyadic_eq, overlapWhole,
    fromBlocks_add_diagonal_const (primeFreeMiddle (R + a)) _ _ _ (-c)] at hidx
  have h0 : 0 ≤ e ⬝ᵥ (overlapSchurLevel Q R a b (-c) *ᵥ e) :=
    schur_nonneg_of_hermNegIndex_le_one hA (endCoupling Q R a b)
      (symm_add_diagonal (endForm_symm Q R a b) (-c)) hidx e
  have hmono := overlapSchurLevel_mono Q a b hR (by linarith : -(1 / 5000 : ℝ) < -c) hC hCμ e
  have hee : 0 ≤ (C - -c) * (e ⬝ᵥ e) :=
    mul_nonneg (by linarith) (dotProduct_self_star_nonneg (v := e))
  linarith

/-- The excess of a window with a floor `c` on its charge-free packets vanishes at every level
`C ≥ −c` below the binding energy of its middle. -/
theorem windowExcess_eq_zero_of_floor {Q R a b : ℕ} (hR : 1 ≤ R) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c < 1 / 5000)
    (hfloor : ∀ z : Fin (a + (R + a) + b) → ℝ, ∑ i, z i = 0 →
      c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R (a + (R + a) + b) *ᵥ z))
    {C : ℝ} (hC : -c ≤ C) (hCμ : C < bindingEnergy (R + a)) : windowExcess Q R a b C = 0 :=
  (windowExcess_eq_zero_iff Q R a b C).mpr
    (overlapSchurLevel_nonneg_of_floor hR hc0 hc hfloor hC hCμ)

/-! ### The excess of the steps inside an aperture -/

/-- **The excess of a step vanishes inside an aperture of nonnegative ground energy.** If
`log(ρ²/2) < 2A` and `ρ²/2 < Q + 1`, every window of a step of ratio `ρ` lies inside the
aperture `A`; for `0 ≤ c < 1/5000` at most the ground energy of `A`, the excess of the steps of
ratio `ρ` vanishes at every level `C ≥ −c` below the binding energy. -/
theorem schurStepExcess_eq_zero_of_le_groundEnergy
    {A : _root_.RHTower.SuzukiPositiveAperture} {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 5000)
    (hcA : c ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A) {ρ : ℝ}
    (hρ : Real.log (ρ ^ 2 / 2) < 2 * A.1) {Q : ℕ} (hQ : ρ ^ 2 / 2 < Q + 1) {C : ℝ}
    (hC : -c ≤ C) (hC2 : C < -neutralBlock 1 1 1) : schurStepExcess Q ρ C = 0 := by
  refine le_antisymm (csSup_le ⟨0, Or.inl rfl⟩ ?_) (schurStepExcess_nonneg Q ρ C)
  rintro y (rfl | ⟨R, a, b, hstep, rfl⟩)
  · exact le_rfl
  · have hR := hstep.1
    have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
    have hρ0 : 0 < ρ := by linarith [ratioStep_two_le hstep]
    have hρ2 : 0 < ρ ^ 2 / 2 := by positivity
    have hnat : R + (a + (R + a) + b) = 2 * (R + a) + b := by omega
    have hwhole := ratioStep_whole_le hstep
    have hlog : Real.log ((R + (a + (R + a) + b) : ℕ) : ℝ) - Real.log R < 2 * A.1 := by
      rw [hnat]
      have hpos : (0 : ℝ) < ((2 * (R + a) + b : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < 2 * (R + a) + b)
      have h1 := Real.log_le_log hpos hwhole
      rw [Real.log_mul hρ2.ne' hR0.ne'] at h1
      linarith
    have hlt : R + (a + (R + a) + b) < (Q + 1) * R := by
      rw [hnat]
      have h2 : ((2 * (R + a) + b : ℕ) : ℝ) < (((Q + 1) * R : ℕ) : ℝ) := by
        have h3 := mul_lt_mul_of_pos_right hQ hR0
        have hw := hwhole
        push_cast at hw ⊢
        linarith
      exact_mod_cast h2
    exact (windowExcess_eq_zero_of_floor hR hc0 hc
      (neutralWindow_floor_of_le_groundEnergy hR hlog hlt hcA) hC
      (lt_of_lt_of_le hC2 (groundPair_spec (by omega)).2.2)).le

/-! ### The first step -/

/-- **On the even tests of the aperture `1881/5000` Weil's form has the floor `1/50000`.** -/
theorem evenWeilFloor_firstStep : EvenWeilFloor (1881 / 5000) (1 / 50000) :=
  fun _ hF hs he => WindowTowerOfSpecZ.weilQuad_ge_even_at_aperture_1881_over_5000 hF hs he

/-- **The ground energy of the aperture `1881/5000` is at least `1/50000`.** -/
theorem one_div_50000_le_groundEnergy_firstStep :
    (1 / 50000 : ℝ) ≤
      _root_.RHTower.ccmRestrictedWeilGroundEnergy ⟨1881 / 5000, by norm_num⟩ :=
  WeilFloor.le_groundEnergy (A := ⟨1881 / 5000, by norm_num⟩)
    (WeilFloor.of_even_of_odd evenWeilFloor_firstStep
      (oddWeilFloor_firstStep.mono (by norm_num)))

/-- **Every window of ratio at most `10609/5000` is at least `1/50000` on its charge-free
packets**, at every block size and for every cutoff `Q ≥ 2`. -/
theorem neutralWindow_floor_firstStep {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : 5000 * (R + J) ≤ 10609 * R) (z : Fin J → ℝ) (hz : ∑ i, z i = 0) :
    1 / 50000 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (neutralWindow Q R J *ᵥ z) :=
  neutralWindow_floor_of_even_floor (by norm_num) evenWeilFloor_firstStep hQ hR hJ z hz

/-- Every window of ratio at most `10609/5000` has the gap `1/50000`. -/
theorem hasGap_neutralWindow_firstStep {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hJ : 5000 * (R + J) ≤ 10609 * R) : HasGap (neutralWindow Q R J) (1 / 50000) :=
  hasGap_neutralWindow_of_even_floor (by norm_num) evenWeilFloor_firstStep hQ hR hJ

/-- **The first overlap step.** Every window `(R, R + J]` with `R ≤ J` of ratio at most
`10609/5000` has exactly one bound state, at every block size and for every cutoff `Q ≥ 2`. -/
theorem hermNegIndex_neutralWindow_firstStep {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hRJ : R ≤ J) (hJ : 5000 * (R + J) ≤ 10609 * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  hermNegIndex_neutralWindow_eq_one_of_hasGap hR hRJ (by norm_num)
    (hasGap_neutralWindow_firstStep hQ hR hJ)

/-- **The first overlap step in Green form, with its excess.** On the two ends of every window
`(R, 2(R + a) + b]` with `a ≤ 3R/100`, `b ≤ 3(R + a)/50` the attraction through the positive
part of the Green matrix of the dyadic middle, plus `1/50000` times the mass of the ends, is
at most the neutral form of the ends plus the repulsion through the bound state of the
middle. -/
theorem greenForm_firstStep {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R) (ha : 100 * a ≤ 3 * R)
    (hb : 50 * b ≤ 3 * (R + a)) (e : Fin a ⊕ Fin b → ℝ) :
    (endCoupling Q R a b *ᵥ e) ⬝ᵥ (greenPositive (R + a) *ᵥ (endCoupling Q R a b *ᵥ e)) +
        1 / 50000 * (e ⬝ᵥ e) ≤
      e ⬝ᵥ (endForm Q R a b *ᵥ e) +
        (groundVector (R + a) ⬝ᵥ (endCoupling Q R a b *ᵥ e)) ^ 2 / bindingEnergy (R + a) :=
  greenForm_firstStep_of_even_floor (by norm_num) (by norm_num) evenWeilFloor_firstStep hQ hR
    ha hb e

/-- **The attractions of the two ends superpose without a second bound state.** On the first
step the dyadic middle dressed by the attraction of both ends holds exactly one bound state. -/
theorem hermNegIndex_dressedMiddle_firstStep {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) :
    hermNegIndex ((dressedMiddle Q R a b).map (↑) :
      Matrix (Fin (R + a)) (Fin (R + a)) ℂ) = 1 := by
  rw [← hermNegIndex_neutralWindow_eq_dressedMiddle hR (by omega) (by omega)]
  exact hermNegIndex_neutralWindow_firstStep hQ hR (by omega) (by omega)

/-- **The Hodge index inequality of the dressed middle on the first step**: two nonnegative
packets of the dyadic middle without a common block, the first of negative dressed energy,
satisfy the reverse Cauchy–Schwarz inequality of the dressed form. -/
theorem dressedMiddle_wells_bound_firstStep {Q R a b : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (ha : 100 * a ≤ 3 * R) (hb : 50 * b ≤ 3 * (R + a)) (x y : Fin (R + a) → ℝ)
    (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k) (hxy : ∀ k, x k * y k = 0)
    (hneg : bilin (dressedMiddle Q R a b) x x < 0) :
    bilin (dressedMiddle Q R a b) x x * bilin (dressedMiddle Q R a b) y y ≤
      bilin (dressedMiddle Q R a b) x y ^ 2 :=
  (hermNegIndex_neutralWindow_eq_one_iff_dressedMiddle_wells_bound hR (by omega) (by omega)).mp
    (hermNegIndex_neutralWindow_firstStep hQ hR (by omega) (by omega)) x y hx hy hxy hneg

/-- The square of the ratio `103/50`, halved, lies inside the aperture `1881/5000`. -/
theorem log_firstStep_ratio_lt : Real.log ((103 / 50 : ℝ) ^ 2 / 2) < 2 * (1881 / 5000) := by
  have h := log_window_lt_of_firstStep (R := 5000) (J := 5609) (by norm_num) (by norm_num)
  have e : ((103 / 50 : ℝ) ^ 2 / 2) = ((5000 + 5609 : ℕ) : ℝ) / ((5000 : ℕ) : ℝ) := by
    norm_num
  rw [e, Real.log_div (by norm_num) (by norm_num)]
  exact h

/-- **The excess of the first step vanishes at every level `C ≥ −1/50000`** below the binding
energy, for every cutoff `Q ≥ 2`. -/
theorem schurStepExcess_firstStep {Q : ℕ} (hQ : 2 ≤ Q) {C : ℝ} (hC : -(1 / 50000) ≤ C)
    (hC2 : C < -neutralBlock 1 1 1) : schurStepExcess Q (103 / 50) C = 0 := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  exact schurStepExcess_eq_zero_of_le_groundEnergy (A := ⟨1881 / 5000, by norm_num⟩)
    (by norm_num) (by norm_num) one_div_50000_le_groundEnergy_firstStep log_firstStep_ratio_lt
    (by norm_num; linarith) hC hC2

/-- **The ladder starts without loss**: the cumulative level after the first step is zero. -/
theorem levelAt_one {Q : ℕ} (hQ : 2 ≤ Q) : levelAt Q 1 = 0 := by
  have h := schurStepExcess_firstStep hQ (C := 0) (by norm_num)
    (by rw [neutralBlock_one_one, neg_neg]; linarith [dyadicDepth_mem.1])
  show levelAt Q 0 + schurStepExcess Q (iteratedRatio 0) (levelAt Q 0) = 0
  rw [show levelAt Q 0 = 0 from rfl, zero_add, iteratedRatio_milestones.1]
  exact h

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
