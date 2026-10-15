import GaloisForLFunctions.RHTower.PrimeBlindFiniteLevelFarkas
import GaloisForLFunctions.RHTower.LatticeMasksDeepPair
import GaloisForLFunctions.RHTower.BlindDecayClassPoleCertificate
import GaloisForLFunctions.RHTower.WeilBlindPoleSignLaw

/-!
# The level value of prime-blind positivity

At level `L` and pole weight `β`, the floors `m` with `A_β(c) ≥ m·mass(c)` on all nonnegative blind
combinations of tests supported in `[−L, L]` form a closed down-set.  This module shows that it is a
nonempty, bounded-above interval `(−∞, p_L(β)]`:

* **Explicit floor.**  The pole term of a level-`L` test is at most `4 L e^L ‖f‖²` in modulus
  (Cauchy–Schwarz against `e^{±x/2}` on `[−L, L]`), so with the anomaly bound
  `Re P + γ(0)‖f‖² ≤ weilArchRe` the number `γ(0) − 4|β| L e^L` is a floor
  (`levelFloor_mem`).
* **Bounded above.**  The blind two-bump test of level `3/10` has positive mass, so every floor is
  at most its energy-to-mass ratio (`levelFloors_bddAbove`).
* **The level value** `levelValueAt L β = sup levelFloors L β` is attained, the floors are exactly
  `Iic (levelValueAt L β)`, and blind positivity at level `L` is `0 ≤ levelValueAt L β`
  (`primeBlindPositiveAtLevel_iff_nonneg_levelValueAt`).  By the finite-level strong duality the
  same number is the best margin of a level-`L` Weil form.  The level value is antitone in `L`, and
  RH holds iff it is nonnegative at pole weight `1` at every level
  (`riemannHypothesis_iff_forall_nonneg_levelValueAt`).
-/

open Complex MeasureTheory Set Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The pole term of a level-`L` test -/

theorem tsupport_subset_of_levelTest {L : ℝ} {f : WeilTestFn} (hf : LevelTest L f) :
    tsupport f.1 ⊆ Icc (-L) L :=
  closure_minimal (fun u hu => abs_le.mp (hf u hu)) isClosed_Icc

theorem testMass_nonneg (f : WeilTestFn) : 0 ≤ testMass f :=
  integral_nonneg fun _ => by positivity

theorem norm_paperFT_sq_le_of_levelTest {L : ℝ} (hL : 0 ≤ L) {f : WeilTestFn}
    (hf : LevelTest L f) (z : ℂ) :
    ‖paperFT f.1 z‖ ^ 2 ≤ 2 * L * Real.exp (2 * L * |z.im|) * testMass f :=
  norm_paperFT_sq_le hL f.2.1.continuous (tsupport_subset_of_levelTest hf) z

/-- The pole term of a test supported in `[−L, L]` is at most `4 L e^L ‖f‖²` in modulus. -/
theorem abs_re_weilPoleTerm_le_of_levelTest {L : ℝ} (hL : 0 ≤ L) {f : WeilTestFn}
    (hf : LevelTest L f) :
    |(weilPoleTerm (EF.weilTest f.1 f.1)).re| ≤ 4 * L * Real.exp L * testMass f := by
  rw [weilPoleTerm_re_eq_two_re f.2.1.continuous f.2.2]
  have h1 := norm_paperFT_sq_le_of_levelTest hL hf (I / 2)
  have h2 := norm_paperFT_sq_le_of_levelTest hL hf (-I / 2)
  have him1 : |(I / 2 : ℂ).im| = 1 / 2 := by simp
  have him2 : |(-I / 2 : ℂ).im| = 1 / 2 := by simp; norm_num
  have hhalf : 2 * L * (1 / 2) = L := by ring
  rw [him1, hhalf] at h1
  rw [him2, hhalf] at h2
  have hab : ‖paperFT f.1 (I / 2)‖ * ‖paperFT f.1 (-I / 2)‖ ≤ 2 * L * Real.exp L * testMass f := by
    nlinarith [sq_nonneg (‖paperFT f.1 (I / 2)‖ - ‖paperFT f.1 (-I / 2)‖),
      norm_nonneg (paperFT f.1 (I / 2)), norm_nonneg (paperFT f.1 (-I / 2))]
  have hre : |(paperFT f.1 (I / 2) * (starRingEnd ℂ) (paperFT f.1 (-I / 2))).re| ≤
      ‖paperFT f.1 (I / 2)‖ * ‖paperFT f.1 (-I / 2)‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  calc |2 * (paperFT f.1 (I / 2) * (starRingEnd ℂ) (paperFT f.1 (-I / 2))).re|
      = 2 * |(paperFT f.1 (I / 2) * (starRingEnd ℂ) (paperFT f.1 (-I / 2))).re| := by
        rw [abs_mul, abs_two]
    _ ≤ 2 * (2 * L * Real.exp L * testMass f) := by linarith
    _ = 4 * L * Real.exp L * testMass f := by ring

/-- `A_β(f) ≥ (γ(0) − 4|β| L e^L) ‖f‖²` for every test supported in `[−L, L]`. -/
theorem poleWeightFunctional_ge_of_levelTest {L : ℝ} (hL : 0 ≤ L) (β : ℝ) {f : WeilTestFn}
    (hf : LevelTest L f) :
    (EF.gammaBracket 0 - 4 * |β| * L * Real.exp L) * testMass f ≤ poleWeightFunctional β f := by
  have h1 : (weilPoleTerm (EF.weilTest f.1 f.1)).re + EF.gammaBracket 0 * testMass f ≤
      weilArchRe (EF.weilTest f.1 f.1) := pole_add_anomaly_le_weilArchRe' f
  have h2 := abs_re_weilPoleTerm_le_of_levelTest hL hf
  have h3 : -(|β| * |(weilPoleTerm (EF.weilTest f.1 f.1)).re|) ≤
      β * (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
    have := neg_abs_le (β * (weilPoleTerm (EF.weilTest f.1 f.1)).re)
    rwa [abs_mul] at this
  have h4 : |β| * |(weilPoleTerm (EF.weilTest f.1 f.1)).re| ≤
      |β| * (4 * L * Real.exp L * testMass f) := mul_le_mul_of_nonneg_left h2 (abs_nonneg β)
  have e : (EF.gammaBracket 0 - 4 * |β| * L * Real.exp L) * testMass f =
      EF.gammaBracket 0 * testMass f - |β| * (4 * L * Real.exp L * testMass f) := by ring
  unfold poleWeightFunctional
  rw [e]
  linarith

/-! ## Linear combinations: monotonicity and scalars -/

theorem linearCombination_mono {Φ Ψ : WeilTestFn → ℝ} {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (h : ∀ f ∈ c.support, Φ f ≤ Ψ f) : linearCombination ℝ Φ c ≤ linearCombination ℝ Ψ c := by
  simp only [linearCombination_apply]
  unfold Finsupp.sum
  exact Finset.sum_le_sum fun f hf => by
    simp only [smul_eq_mul]; exact mul_le_mul_of_nonneg_left (h f hf) (hc f)

theorem linearCombination_const_mul (m : ℝ) (Ψ : WeilTestFn → ℝ) (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ (fun f => m * Ψ f) c = m * linearCombination ℝ Ψ c := by
  simp only [linearCombination_apply, Finsupp.sum, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => by ring

theorem linearCombination_testMass_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) :
    0 ≤ linearCombination ℝ testMass c := by
  rw [linearCombination_apply]
  exact Finsupp.sum_nonneg fun f _ => by
    rw [smul_eq_mul]; exact mul_nonneg (hc f) (testMass_nonneg f)

/-! ## The floors form a nonempty bounded interval -/

/-- **Explicit floor.**  `γ(0) − 4|β| L e^L` is a floor of the blind level-`L` functional. -/
theorem levelFloor_mem (L β : ℝ) (hL : 0 ≤ L) :
    EF.gammaBracket 0 - 4 * |β| * L * Real.exp L ∈ levelFloors L β := by
  intro c hc hcL _
  rw [← linearCombination_poleWeightFunctional, ← linearCombination_const_mul]
  exact linearCombination_mono hc fun f hf => poleWeightFunctional_ge_of_levelTest hL β (hcL f hf)

theorem levelFloors_nonempty {L : ℝ} (hL : 0 ≤ L) (β : ℝ) : (levelFloors L β).Nonempty :=
  ⟨_, levelFloor_mem L β hL⟩

theorem adjTest_one_apply_fifth : adjTest 1 (1 / 5) = 1 := by
  have h0 : adjBump ((1 : ℝ) / 5 - 1 / 5) = 1 := by
    rw [sub_self]
    exact adjBump.one_of_mem_closedBall (Metric.mem_closedBall_self adjBump.rIn_pos.le)
  have h1 : adjBump ((1 : ℝ) / 5 + 1 / 5) = 0 :=
    adjBump_eq_zero (by rw [abs_of_pos (by norm_num)]; norm_num)
  simp only [adjTest, adjReal, h0, h1]
  push_cast
  ring

theorem testMass_adjTestFn_one_pos : 0 < testMass (adjTestFn 1) := by
  have hc : Continuous fun x => ‖(adjTestFn 1).1 x‖ ^ 2 := ((continuous_adjTest 1).norm.pow 2)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((hasCompactSupport_adjTest 1).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
    (fun x => by positivity) (x := 1 / 5) ?_
  change ‖adjTest 1 (1 / 5)‖ ^ 2 ≠ 0
  rw [adjTest_one_apply_fifth]
  norm_num

/-- Every floor is at most the energy-to-mass ratio of the blind two-bump test. -/
theorem levelFloors_bddAbove {L : ℝ} (hL : 3 / 10 ≤ L) (β : ℝ) : BddAbove (levelFloors L β) := by
  refine ⟨poleWeightFunctional β (adjTestFn 1) / testMass (adjTestFn 1), fun m hm => ?_⟩
  have h := hm (Finsupp.single (adjTestFn 1) 1) (single_adjTestFn_nonneg 1)
    (support_single_adjTestFn_level hL 1) (by rw [nodeVector_single_test, logVector_adjTestFn])
  rw [← linearCombination_poleWeightFunctional, linearCombination_single, linearCombination_single,
    one_smul, one_smul] at h
  rw [le_div_iff₀ testMass_adjTestFn_one_pos]
  exact h

theorem levelFloors_mem_of_le {L β m m' : ℝ} (hm : m ∈ levelFloors L β) (h : m' ≤ m) :
    m' ∈ levelFloors L β := by
  intro c hc hcL hcv
  have := hm c hc hcL hcv
  have hmass := linearCombination_testMass_nonneg hc
  nlinarith

theorem isClosed_levelFloors (L β : ℝ) : IsClosed (levelFloors L β) := by
  have e : levelFloors L β = ⋂ (c : WeilTestFn →₀ ℝ)
      (_ : (∀ f, 0 ≤ c f) ∧ (∀ f ∈ c.support, LevelTest L f) ∧ nodeVector c = 0),
      {m : ℝ | m * linearCombination ℝ testMass c ≤ nodeArchEnergy c + (β - 1) * nodePoleMass c} := by
    ext m
    simp only [levelFloors, mem_setOf_eq, mem_iInter]
    exact ⟨fun h c ⟨h1, h2, h3⟩ => h c h1 h2 h3, fun h c h1 h2 h3 => h c ⟨h1, h2, h3⟩⟩
  rw [e]
  exact isClosed_iInter fun c => isClosed_iInter fun _ =>
    isClosed_le (continuous_mul_const _) continuous_const

/-! ## The level value -/

/-- The level value: the best uniform floor of the blind level-`L` functional at pole weight `β`,
equivalently (strong duality) the best margin of a level-`L` Weil form. -/
def levelValueAt (L β : ℝ) : ℝ := sSup (levelFloors L β)

theorem le_levelValueAt {L : ℝ} (hL : 3 / 10 ≤ L) (β : ℝ) {m : ℝ} (hm : m ∈ levelFloors L β) :
    m ≤ levelValueAt L β :=
  le_csSup (levelFloors_bddAbove hL β) hm

theorem levelValueAt_mem {L : ℝ} (hL : 3 / 10 ≤ L) (β : ℝ) :
    levelValueAt L β ∈ levelFloors L β :=
  (isClosed_levelFloors L β).csSup_mem (levelFloors_nonempty (by linarith) β)
    (levelFloors_bddAbove hL β)

/-- The floors are exactly the numbers below the level value. -/
theorem levelFloors_eq_Iic {L : ℝ} (hL : 3 / 10 ≤ L) (β : ℝ) :
    levelFloors L β = Iic (levelValueAt L β) := by
  ext m
  constructor
  · exact fun hm => le_levelValueAt hL β hm
  · exact fun hm => levelFloors_mem_of_le (levelValueAt_mem hL β) hm

/-- The explicit lower bound for the level value. -/
theorem gammaBracket_sub_le_levelValueAt {L : ℝ} (hL : 3 / 10 ≤ L) (β : ℝ) :
    EF.gammaBracket 0 - 4 * |β| * L * Real.exp L ≤ levelValueAt L β :=
  le_levelValueAt hL β (levelFloor_mem L β (by linarith))

/-- The level value is also the supremum of the margins of level-`L` Weil forms. -/
theorem levelValueAt_eq_sSup_levelMargins (L β : ℝ) :
    levelValueAt L β = sSup (levelMargins L β) := by
  rw [levelValueAt, levelFloors_eq_levelMargins]

/-- **Blind positivity at level `L` is the nonnegativity of the level value.** -/
theorem primeBlindPositiveAtLevel_iff_nonneg_levelValueAt {L : ℝ} (hL : 3 / 10 ≤ L) (β : ℝ) :
    PrimeBlindPositiveAtLevel L β ↔ 0 ≤ levelValueAt L β := by
  rw [← zero_mem_levelMargins_iff, ← levelFloors_eq_levelMargins, levelFloors_eq_Iic hL β, mem_Iic]

/-- The level window is the set of pole weights with nonnegative level value. -/
theorem levelWindow_eq_setOf_nonneg_levelValueAt {L : ℝ} (hL : 3 / 10 ≤ L) :
    levelWindow L = {β | 0 ≤ levelValueAt L β} := by
  ext β
  exact primeBlindPositiveAtLevel_iff_nonneg_levelValueAt hL β

/-- The level value decreases with the level. -/
theorem levelValueAt_antitone {L L' : ℝ} (hL : 3 / 10 ≤ L) (hLL' : L ≤ L') (β : ℝ) :
    levelValueAt L' β ≤ levelValueAt L β := by
  refine csSup_le_csSup (levelFloors_bddAbove hL β) (levelFloors_nonempty (by linarith) β) ?_
  intro m hm c hc hcL hcv
  exact hm c hc (fun f hf => (hcL f hf).mono hLL') hcv

/-- **RH is the nonnegativity of the level value at pole weight `1` at every level.** -/
theorem riemannHypothesis_iff_forall_nonneg_levelValueAt :
    RiemannHypothesis ↔ ∀ L : ℝ, 3 / 10 ≤ L → 0 ≤ levelValueAt L 1 := by
  rw [riemannHypothesis_iff_forall_one_mem_levelWindow]
  constructor
  · intro h L hL
    exact (primeBlindPositiveAtLevel_iff_nonneg_levelValueAt hL 1).mp (h L)
  · intro h L
    have hmax : (1 : ℝ) ∈ levelWindow (max L (3 / 10)) :=
      (primeBlindPositiveAtLevel_iff_nonneg_levelValueAt (le_max_right L (3 / 10)) 1).mpr
        (h _ (le_max_right _ _))
    exact levelWindow_antitone (le_max_left L (3 / 10)) hmax

/-- Under RH the level values at pole weight `1` are nonnegative, lie in
`[γ(0) − 4 L e^L, …]`, and decrease with the level. -/
theorem nonneg_levelValueAt_of_riemannHypothesis (hRH : RiemannHypothesis) {L : ℝ}
    (hL : 3 / 10 ≤ L) : 0 ≤ levelValueAt L 1 :=
  riemannHypothesis_iff_forall_nonneg_levelValueAt.mp hRH L hL

end

end RHTower.WeilOneSided
