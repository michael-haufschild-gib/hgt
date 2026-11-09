import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLandingLaw
import GaloisForLFunctions.ZeroConfigurationGeometry.SymmetricShiftsPreserveTheAsymptoticAbscissaLaw
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit
import GaloisForLFunctions.RHTower.XiLogDerivEventualPositivityAbscissa
import GaloisForLFunctions.RHTower.GaussianCentralGapLargeHeightFiniteOffLine
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.ExceptionalLayerTheory.TheGaussianObservationBoundary

/-!
# The landing law for `ζ`

`ZetaLandingLaw : ZerosApproachLine → FiniteOffLine` is the landing law of the zero configuration
of `ζ`: if the zeros approach the critical line, all but finitely many lie on it.

* **Atoms of RH** (`riemannHypothesis_iff_three_atoms`). RH is ZAL, the finite stratum
  `FiniteOffLine → RH`, and landing. Under landing RH is ZAL plus the finite stratum.
* **Equivalent forms** (`zetaLandingLaw_tfae`). Landing is the configuration law
  `LandingLaw zetaZeroConfig`; it says that eventual Hadamard positivity (`Re ξ'/ξ ≥ 0` right of
  `σ` above a height, for every `σ > ½`) holds uniformly up to the line; that the height threshold
  `hadamardThreshold σ` stays bounded as `σ ↓ ½`; that eventual Hadamard positivity forces a finite
  Krein–Langer index of the Weil kernel, on `ℚ_{>0}` or on two prime towers; and, under ZAL, the
  critical line above a height, bounded heat counts, slice positivity, the central-gap budget and
  a finite odd bound-state space.
* **What does not land** (`heat_finiteness_does_not_pass`, `symmetricShift_not_approachesLine`).
  Each heat deformation `H_t`, `t > 0`, has finitely many non-real zeros, yet off-line zeros of `ζ`
  make the collision mass diverge as `t → 0⁺`. Every symmetric shift `ξ(s + a)ξ(s − a)`, `a > 0`,
  has infinitely many zeros on `Re s = ½ + a` (Hardy), so it violates ZAL and lands vacuously.
* **Resolution barriers** (`gaussianObservationRate_neg_of_shallow`, `offLine_modes_split`).
  A zero at depth `δ` is supercritical in the exponential current only at speeds `a > π/(2δ)`;
  under ZAL and infinitely many off-line zeros, every fixed speed sees finitely many off-line
  modes and loses infinitely many.
-/

open Complex Set Filter Topology
open Zeta23 RHTower RHTower.BacklundConverse RHTower.DeBruijn RHTower.LindelofSparse
open _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open GaloisForLFunctions.ZeroConfigurationGeometry.ZetaAbscissa
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticOrientationGeometry

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- **The landing law for `ζ`.** -/
def ZetaLandingLaw : Prop := ZerosApproachLine → FiniteOffLine

/-- The zeros right of the line are finitely many exactly when the off-line zeros are. -/
theorem rightOf_zetaZeroConfig_finite_iff : (rightOf zetaZeroConfig 0).Finite ↔ FiniteOffLine := by
  have h : rightOf zetaZeroConfig 0 = ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig := by
    ext ρ
    simp [rightOf, ArithmeticCastelnuovoSeveri.rightZeros]
  rw [h]
  exact rightZeros_zeta_finite_iff_finiteOffLine

theorem zetaLandingLaw_iff_landingLaw : ZetaLandingLaw ↔ LandingLaw zetaZeroConfig := by
  rw [ZetaLandingLaw, LandingLaw, zetaZeroConfig_approachesLine_iff, rightOf_zetaZeroConfig_finite_iff]

/-- RH puts every zero of `ζ` on the line, so the off-line zeros are finitely many. -/
theorem finiteOffLine_of_riemannHypothesis (hRH : RiemannHypothesis) : FiniteOffLine :=
  finiteOffLine_iff_exists_onLine_above.mpr
    ⟨0, fun ρ hρ _ => CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH ρ hρ⟩

/-- **RH is three atoms**: ZAL, the finite stratum, and landing. -/
theorem riemannHypothesis_iff_three_atoms :
    RiemannHypothesis ↔
      ZerosApproachLine ∧ (FiniteOffLine → RiemannHypothesis) ∧ ZetaLandingLaw :=
  ⟨fun h => ⟨zerosApproachLine_of_riemannHypothesis h, fun _ => h,
      fun _ => finiteOffLine_of_riemannHypothesis h⟩,
    fun ⟨hZ, hB, hL⟩ => hB (hL hZ)⟩

/-- **Under landing, RH is ZAL plus the finite stratum.** -/
theorem riemannHypothesis_iff_of_zetaLandingLaw (hL : ZetaLandingLaw) :
    RiemannHypothesis ↔ ZerosApproachLine ∧ (FiniteOffLine → RiemannHypothesis) :=
  riemannHypothesis_iff_three_atoms.trans ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hL⟩⟩

/-- The finite stratum of the configuration of `ζ` is `FiniteOffLine → RH`. -/
theorem abscissaLawAt_zero_zetaZeroConfig_iff :
    AbscissaLawAt zetaZeroConfig 0 ↔ (FiniteOffLine → RiemannHypothesis) := by
  rw [AbscissaLawAt, rightOf_zetaZeroConfig_finite_iff,
    CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine]
  refine imp_congr_right fun _ => ?_
  simp only [add_zero]
  exact (pure_iff_forall_re_le zetaZeroConfig).symm

/-- **Existential linear AAL for `ζ` is the finite stratum plus landing.** -/
theorem zetaLinearAbscissaLaw_iff_b13_and_landing :
    ZetaLinearAbscissaLaw ↔ (FiniteOffLine → RiemannHypothesis) ∧ ZetaLandingLaw := by
  have h : ZetaLinearAbscissaLaw ↔ LinearAbscissaLaw zetaZeroConfig :=
    exists_congr fun C => zetaLinearAbscissaLawAt_iff_config C
  rw [h, linearAbscissaLaw_iff_abscissaLawAt_zero_and_landingLaw,
    abscissaLawAt_zero_zetaZeroConfig_iff, zetaLandingLaw_iff_landingLaw]

/-! ### The Hadamard threshold -/

/-- Heights above which `Re ξ'/ξ ≥ 0` on `Re s ≥ σ`. -/
def hadamardThresholdSet (σ : ℝ) : Set ℝ :=
  {T : ℝ | 0 ≤ T ∧ ∀ s : ℂ, σ ≤ s.re → T ≤ |s.im| → 0 ≤ (logDeriv xi s).re}

/-- The least height of Hadamard positivity right of `σ`. -/
def hadamardThreshold (σ : ℝ) : ℝ := sInf (hadamardThresholdSet σ)

theorem bddBelow_hadamardThresholdSet (σ : ℝ) : BddBelow (hadamardThresholdSet σ) :=
  ⟨0, fun _ h => h.1⟩

theorem hadamardThresholdSet_nonempty (hE : EventualHadamardPositivity) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (hadamardThresholdSet σ).Nonempty := by
  obtain ⟨T, hT⟩ := hE σ hσ
  exact ⟨max T 0, le_max_right _ _, fun s hs hT' => hT s hs ((le_max_left _ _).trans hT')⟩

theorem hadamardThresholdSet_mono {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) :
    hadamardThresholdSet σ₁ ⊆ hadamardThresholdSet σ₂ :=
  fun _ ⟨h0, hT⟩ => ⟨h0, fun s hs => hT s (h.trans hs)⟩

/-- **The threshold can only grow as `σ` approaches the line.** -/
theorem hadamardThreshold_antitoneOn (hE : EventualHadamardPositivity) {σ₁ σ₂ : ℝ}
    (hσ₁ : 1 / 2 < σ₁) (h : σ₁ ≤ σ₂) : hadamardThreshold σ₂ ≤ hadamardThreshold σ₁ :=
  csInf_le_csInf (bddBelow_hadamardThresholdSet σ₂) (hadamardThresholdSet_nonempty hE hσ₁)
    (hadamardThresholdSet_mono h)

/-- **Bounded threshold ⇔ Hadamard positivity on the whole open half-plane.** -/
theorem bddAbove_hadamardThreshold_iff (hE : EventualHadamardPositivity) :
    BddAbove (hadamardThreshold '' Ioi (1 / 2)) ↔ EventualHadamardPositivityRight (1 / 2) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max M 0 + 1, fun s hs hT => ?_⟩
    set σ := (1 / 2 + s.re) / 2
    have hσ : 1 / 2 < σ := by simp only [σ]; linarith
    have hle : hadamardThreshold σ ≤ M := hM ⟨σ, hσ, rfl⟩
    obtain ⟨T, ⟨_, hTs⟩, hTlt⟩ := exists_lt_of_csInf_lt (hadamardThresholdSet_nonempty hE hσ)
      (show hadamardThreshold σ < hadamardThreshold σ + 1 by linarith)
    exact hTs s (by simp only [σ]; linarith) (by linarith [le_max_left M 0])
  · rintro ⟨T₀, hT₀⟩
    refine ⟨max T₀ 0, ?_⟩
    rintro _ ⟨σ, hσ, rfl⟩
    exact csInf_le (bddBelow_hadamardThresholdSet σ) ⟨le_max_right _ _, fun s hs hT =>
      hT₀ s (lt_of_lt_of_le (mem_Ioi.mp hσ) hs) ((le_max_left _ _).trans hT)⟩

/-! ### Equivalent forms of landing -/

/-- **Equivalent forms of the landing law for `ζ`.** -/
theorem zetaLandingLaw_tfae :
    [ZetaLandingLaw,
      LandingLaw zetaZeroConfig,
      EventualHadamardPositivity → EventualHadamardPositivityRight (1 / 2),
      EventualHadamardPositivity → BddAbove (hadamardThreshold '' Ioi (1 / 2)),
      EventualHadamardPositivity → negIndex zetaKernel < ⊤,
      ZerosApproachLine →
        negIndex (zetaKernel ∘ (twoPrimeLattice Nat.prime_two Nat.prime_three).subtype) < ⊤,
      ZerosApproachLine → ∃ T₀ : ℝ, ∀ ρ ∈ zetaZeroConfig.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2,
      ZerosApproachLine → ∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M,
      ZerosApproachLine → EventualSlicePositivity,
      ZerosApproachLine → EventualFilteredCentralGapBudget,
      ZerosApproachLine → FiniteDimensional ℝ oddBoundStateSpace].TFAE := by
  have hk := zetaKernel_finiteIndex_tfae Nat.prime_two Nat.prime_three (by norm_num)
  have hE := eventualHadamardPositivity_iff_zerosApproachLine
  have hR := eventualHadamardPositivityRight_half_iff_finiteOffLine
  tfae_have 1 ↔ 2 := zetaLandingLaw_iff_landingLaw
  tfae_have 1 ↔ 3 := by rw [ZetaLandingLaw, hE, hR]
  tfae_have 3 ↔ 4 := forall_congr' fun h => (bddAbove_hadamardThreshold_iff h).symm
  have h0 : negIndex zetaKernel < ⊤ ↔ FiniteOffLine := hk.out 0 2
  have h1 : negIndex (zetaKernel ∘ (twoPrimeLattice Nat.prime_two Nat.prime_three).subtype) < ⊤ ↔
      FiniteOffLine := hk.out 1 2
  have h4 : (∃ T₀ : ℝ, ∀ ρ ∈ zetaZeroConfig.carrier, T₀ < |ρ.im| → ρ.re = 1 / 2) ↔
      FiniteOffLine := hk.out 4 2
  have h3 : (∃ M : ℕ, ∀ t, 0 < t → nonrealZeroCount t ≤ M) ↔ FiniteOffLine := hk.out 3 2
  tfae_have 1 ↔ 5 := by rw [ZetaLandingLaw, hE, h0]
  tfae_have 1 ↔ 6 := by rw [ZetaLandingLaw, h1]
  tfae_have 1 ↔ 7 := by rw [ZetaLandingLaw, h4]
  tfae_have 1 ↔ 8 := by rw [ZetaLandingLaw, h3]
  tfae_have 1 ↔ 9 := by rw [ZetaLandingLaw, eventualSlicePositivity_iff_finiteOffLine]
  tfae_have 1 ↔ 10 := by
    rw [ZetaLandingLaw, RHTower.eventualFilteredCentralGapBudget_iff_finiteOffLine]
  tfae_have 1 ↔ 11 := by
    rw [ZetaLandingLaw, CrossRouteReceiverBridges.finiteDimensional_oddBoundStateSpace_iff_finiteOffLine]
  tfae_finish

/-- **The collar.** Under ZAL, Hadamard positivity holds right of `½ + r` above some height for
every `r > 0`; high points of negative `Re ξ'/ξ` right of the line lie in shrinking collars. -/
theorem collar_of_zerosApproachLine (hZ : ZerosApproachLine) {r : ℝ} (hr : 0 < r) :
    ∃ T : ℝ, ∀ s : ℂ, 1 / 2 + r ≤ s.re → T ≤ |s.im| → 0 ≤ (logDeriv xi s).re :=
  eventualHadamardPositivity_iff_zerosApproachLine.mpr hZ _ (by linarith)

/-! ### What does not land -/

/-- **Heat finiteness does not pass to `t = 0`.** Each `H_t`, `t > 0`, has finitely many non-real
zeros, while infinitely many off-line zeros of `ζ` make the collision mass diverge as `t → 0⁺`. -/
theorem heat_finiteness_does_not_pass :
    (∀ t : ℝ, 0 < t → {z : ℂ | riemannHeat t z = 0 ∧ z.im ≠ 0}.Finite) ∧
      (¬ FiniteOffLine → Tendsto collisionMassAfter (𝓝[>] 0) atTop) :=
  ⟨fun _ ht => riemannHeat_nonreal_zeros_finite ht, fun hF =>
    tendsto_collisionMassAfter_atTop fun h => hF (rightZeros_zeta_finite_iff_finiteOffLine.mp h)⟩

/-- Hardy's theorem: `ξ` vanishes on the critical line above every height. -/
theorem exists_xi_zero_on_line_gt (T : ℝ) :
    ∃ t : ℝ, T < t ∧ xi ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
  obtain ⟨t, ht, hzero⟩ := exists_Xi_zero_gt T
  refine ⟨t, ht, ?_⟩
  rw [xi_eq_XiC_comp]
  have he : (((1 / 2 : ℂ) + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
    ring_nf
    simp only [Complex.I_sq, mul_neg, mul_one, neg_neg]
  rw [he, XiC_ofReal, hzero, Complex.ofReal_zero]

/-- **Symmetric shifts violate ZAL.** For `a > 0`, `ξ(s + a)ξ(s − a)` has infinitely many zeros
on `Re s = ½ + a`, so infinitely many right of `½ + a/2`; its landing law holds vacuously. -/
theorem symmetricShift_not_approachesLine {a : ℝ} (ha : 0 < a) :
    {z : ℂ | symmetricShiftProduct xi a z = 0 ∧ 1 / 2 + a / 2 < z.re}.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨t, ht, hzero⟩ := exists_xi_zero_on_line_gt M
  have hmem : (1 / 2 : ℂ) + (t : ℂ) * I + (a : ℂ) ∈
      {z : ℂ | symmetricShiftProduct xi a z = 0 ∧ 1 / 2 + a / 2 < z.re} :=
    ⟨(symmetricShiftProduct_zero_translates xi a hzero).1, by simp; linarith⟩
  have := hM ⟨_, hmem, rfl⟩
  simp at this
  linarith

/-! ### Resolution barriers in the exponential current -/

/-- Observed midway between a zero and the line, the Gaussian rate is `aδ/4 − π/4`. -/
theorem gaussianObservationRate_midpoint (ρ : ℂ) (a : ℝ) :
    gaussianObservationRate ρ (1 / 2 + (ρ.re - 1 / 2) / 2) a =
      a * (ρ.re - 1 / 2) / 4 - Real.pi / 4 := by
  unfold gaussianObservationRate
  ring

/-- **A zero at depth `δ` is lost at every speed `a < π/(2δ)`**, on every line `σ ≥ ½`. -/
theorem gaussianObservationRate_neg_of_shallow {ρ : ℂ} {σ a : ℝ} (hσ : 1 / 2 ≤ σ) (ha : 0 ≤ a)
    (hshallow : a * (ρ.re - 1 / 2) < Real.pi / 2) : gaussianObservationRate ρ σ a < 0 := by
  unfold gaussianObservationRate
  nlinarith

/-- **Every fixed speed sees finitely many off-line modes and loses infinitely many**, under ZAL
with infinitely many off-line zeros. -/
theorem offLine_modes_split (hZ : ZerosApproachLine) (hF : ¬ FiniteOffLine) {σ a : ℝ}
    (hσ : 1 / 2 ≤ σ) (ha : 0 < a) :
    {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2 ∧ 0 ≤ gaussianObservationRate ρ σ a}.Finite ∧
      {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2 ∧
        gaussianObservationRate ρ σ a < 0}.Infinite := by
  have hfin : {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2 ∧
      0 ≤ gaussianObservationRate ρ σ a}.Finite := by
    refine (zetaZeroConfig_approachesLine_iff.mpr hZ (Real.pi / (4 * a)) (by positivity)).subset ?_
    rintro ρ ⟨hρ, _, hr⟩
    refine ⟨hρ, ?_⟩
    unfold gaussianObservationRate at hr
    have h1 : Real.pi / 2 ≤ a * (ρ.re - σ) := by linarith
    have h2 : Real.pi / (4 * a) < ρ.re - σ := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    linarith
  refine ⟨hfin, fun hneg => hF ?_⟩
  refine CrossRouteReceiverBridges.offLineZeros_finite_iff_finiteOffLine.mp ((hfin.union hneg).subset ?_)
  rintro ρ ⟨hρ, hre⟩
  rcases le_or_gt 0 (gaussianObservationRate ρ σ a) with h | h
  · exact Or.inl ⟨hρ, hre, h⟩
  · exact Or.inr ⟨hρ, hre, h⟩

end GaloisForLFunctions.ExceptionalLayerTheory
