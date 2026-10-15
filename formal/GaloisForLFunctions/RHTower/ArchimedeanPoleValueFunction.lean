import GaloisForLFunctions.RHTower.ArchimedeanNodeValueFunction
import GaloisForLFunctions.RHTower.WeilBlindPoleSignLaw
import GaloisForLFunctions.RHTower.WeilPoleWeightForcedOne

/-!
# The archimedean value function with the pole as a coordinate: gradient `(Λ, −1)`

For a nonnegative combination `c` of Weil tests write `A(c)` for its pole and archimedean energy,
`P(c) = Σ c_f Re(k̂_f(i/2) + k̂_f(−i/2))` for its total pole mass (`nodePoleMass`), and
`A(c) − P(c)` for its archimedean part without the pole (`nodeArchOnly`): the archimedean symbol
`Re ψ(¼ + ir/2) − log π` integrated against the spectral measure of `c`.  For a node vector `v` and a
real number `p` let `poleFibre v p` be the set of values `A(c) − P(c)` over the combinations with
node vector `v` and pole mass `p`, and `poleValue v p = inf poleFibre v p`.

**Blind tests of both pole signs** (`blindEvenTest`, `blindOddTest`).  Two narrow bumps at
`±1/5` with equal or opposite signs are blind by support (autocorrelation inside `(−log 2, log 2)`)
and have pole term `> 0` and `< 0`.  Hence every pair `(v, p)` is attained (`poleFibre_nonempty`)
and every real pole mass is realised by a blind combination (`exists_blind_nodePoleMass_eq`).

**Theorems.**
* `poleValue_eq` (under RH): `poleValue v p = Σ_n Λ(n) v_n − p`.  The value function in the
  variables (node vector, pole mass) is linear with gradient `(Λ, −1)`: the von Mangoldt weights at
  the nodes and the exact pole weight `1`.
* `riemannHypothesis_iff_zeroPoleBlindPositive`: RH holds iff the archimedean symbol is nonnegative
  on every nonnegative blind combination of total pole mass zero.  The pole enters only as a
  constraint; the functional is the archimedean symbol alone.
* `riemannHypothesis_iff_forall_le_poleFibre`: RH holds iff `Σ_n Λ(n) v_n − p ≤ E` for every
  `E ∈ poleFibre v p` and every `(v, p)`.
* `riemannHypothesis_iff_bddBelow_poleFibre`: RH holds iff one fibre is bounded below.

Proof.  The linear law follows the node-only case: the fibres form a convex cone, the value
function is finite and sublinear under RH, Hahn–Banach produces a linear minorant
`g(v, p) = g₁(v) + b p` touching at `(v₀, p₀)`, and on single tests `g` is dominated by
`A(f) − P(f)`.  So the weights `w(n) = g₁(e_n)` are Weil-positive at pole weight `−b`; pole-weight
rigidity (`eq_one_of_weilPositiveAt`) gives `b = −1`, and cone uniqueness gives `w = Λ`.
The zero-pole criterion is the two-sided Farkas lemma on the node vector extended by the pole
coordinate, whose generators are pole-corrected pair tests and the blind tests above; the resulting
dual weights are Weil-positive at some pole weight, which must be `1`.
-/

open Complex MeasureTheory Finsupp Zeta23

namespace RHTower.WeilOneSided

noncomputable section

/-! ## Blind tests with pole terms of both signs -/

/-- The bump at `0`, equal to `1` on `[−1/20, 1/20]` and `0` outside `(−1/10, 1/10)`. -/
def adjBump : ContDiffBump (0 : ℝ) := ⟨1 / 20, 1 / 10, by norm_num, by norm_num⟩

/-- The real two-bump profile `b(u − 1/5) + σ b(u + 1/5)`. -/
def adjReal (σ : ℝ) (u : ℝ) : ℝ := adjBump (u - 1 / 5) + σ * adjBump (u + 1 / 5)

/-- The two-bump test, as a complex test. -/
def adjTest (σ : ℝ) : ℝ → ℂ := fun u => ((adjReal σ u : ℝ) : ℂ)

theorem adjBump_eq_zero {t : ℝ} (ht : 1 / 10 ≤ |t|) : adjBump t = 0 :=
  adjBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht)

theorem adjReal_eq_zero (σ : ℝ) {u : ℝ} (hu : 3 / 10 ≤ |u|) : adjReal σ u = 0 := by
  have h1 : 1 / 10 ≤ |u - 1 / 5| := by
    rcases le_abs.mp hu with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  have h2 : 1 / 10 ≤ |u + 1 / 5| := by
    rcases le_abs.mp hu with h | h
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
  rw [adjReal, adjBump_eq_zero h1, adjBump_eq_zero h2, mul_zero, add_zero]

theorem contDiff_adjReal (σ : ℝ) : ContDiff ℝ 2 (adjReal σ) := by
  have hb : ContDiff ℝ 2 (adjBump : ℝ → ℝ) := (adjBump.contDiff (n := ⊤)).of_le (by norm_cast)
  exact (hb.comp (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul (hb.comp (contDiff_id.add contDiff_const)))

theorem contDiff_adjTest (σ : ℝ) : ContDiff ℝ 2 (adjTest σ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_adjReal σ)

theorem continuous_adjReal (σ : ℝ) : Continuous (adjReal σ) := (contDiff_adjReal σ).continuous

theorem continuous_adjTest (σ : ℝ) : Continuous (adjTest σ) := (contDiff_adjTest σ).continuous

theorem hasCompactSupport_adjReal (σ : ℝ) : HasCompactSupport (adjReal σ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(3 / 10 : ℝ)) (b := 3 / 10)) fun u hu => by
    refine adjReal_eq_zero σ ?_
    rw [Set.mem_Icc, not_and_or] at hu
    rcases hu with h | h
    · rw [not_le] at h; rw [abs_of_neg (by linarith)]; linarith
    · rw [not_le] at h; rw [abs_of_pos (by linarith)]; linarith

theorem hasCompactSupport_adjTest (σ : ℝ) : HasCompactSupport (adjTest σ) :=
  (hasCompactSupport_adjReal σ).comp_left Complex.ofReal_zero

/-- The two-bump test as a Weil test. -/
def adjTestFn (σ : ℝ) : WeilTestFn := ⟨adjTest σ, contDiff_adjTest σ, hasCompactSupport_adjTest σ⟩

theorem adjTest_ne_zero_imp {σ u : ℝ} (hu : adjTest σ u ≠ 0) : |u| ≤ 3 / 10 := by
  by_contra h
  rw [not_le] at h
  exact hu (by simp [adjTest, adjReal_eq_zero σ h.le])

/-- **The two-bump tests are blind by support.** -/
theorem logValue_adjTest (σ : ℝ) {n : ℕ} (hn : 2 ≤ n) : logValue (adjTest σ) n = 0 := by
  have hk := weilTest_support_abs_le (f := adjTest σ) (g := adjTest σ) (A := 3 / 10) (B := 3 / 10)
    (fun u hu => adjTest_ne_zero_imp hu) (fun u hu => adjTest_ne_zero_imp hu)
  have hlog : 3 / 5 < Real.log n := by
    have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
    linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two]
  have e1 : EF.weilTest (adjTest σ) (adjTest σ) (Real.log n) = 0 := by
    by_contra h
    have := hk _ h
    rw [abs_of_pos (by linarith)] at this
    linarith
  have e2 : EF.weilTest (adjTest σ) (adjTest σ) (-Real.log n) = 0 := by
    by_contra h
    have := hk _ h
    rw [abs_neg, abs_of_pos (by linarith)] at this
    linarith
  simp [logValue, e1, e2]

theorem logVector_adjTestFn (σ : ℝ) : logVector (adjTestFn σ) = 0 := by
  ext j
  rw [logVector_apply]
  exact logValue_adjTest σ j.2

theorem adjReal_one_even (u : ℝ) : adjReal 1 (-u) = adjReal 1 u := by
  simp only [adjReal, one_mul]
  rw [show -u - 1 / 5 = -(u + 1 / 5) by ring, show -u + 1 / 5 = -(u - 1 / 5) by ring,
    adjBump.neg, adjBump.neg, add_comm]

theorem adjReal_neg_one_odd (u : ℝ) : adjReal (-1) (-u) = -adjReal (-1) u := by
  simp only [adjReal, neg_one_mul]
  rw [show -u - 1 / 5 = -(u + 1 / 5) by ring, show -u + 1 / 5 = -(u - 1 / 5) by ring,
    adjBump.neg, adjBump.neg]
  ring

/-- `∫ b(t) e^{−t/2} dt > 0`. -/
theorem integral_adjBump_exp_pos : 0 < ∫ t, adjBump t * Real.exp (-t / 2) := by
  have hc : Continuous fun t => adjBump t * Real.exp (-t / 2) :=
    adjBump.continuous.mul (by fun_prop)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (adjBump.hasCompactSupport.mul_right) (fun t => mul_nonneg adjBump.nonneg (Real.exp_pos _).le)
    (x := 0) ?_
  rw [adjBump.one_of_mem_closedBall (Metric.mem_closedBall_self adjBump.rIn_pos.le)]
  simp

/-- The exponential moment of a shifted bump. -/
theorem integral_adjBump_shift_exp (a : ℝ) :
    ∫ u, adjBump (u - a) * Real.exp (-u / 2) =
      Real.exp (-a / 2) * ∫ t, adjBump t * Real.exp (-t / 2) := by
  have h := integral_add_right_eq_self (μ := volume) (fun u => adjBump (u - a) * Real.exp (-u / 2)) a
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [add_sub_cancel_right, show -(t + a) / 2 = -t / 2 + -a / 2 by ring, Real.exp_add]
  ring

theorem integral_adjReal_exp (σ : ℝ) :
    ∫ u, adjReal σ u * Real.exp (-u / 2) =
      (Real.exp (-(1 / 5) / 2) + σ * Real.exp (1 / 5 / 2)) * ∫ t, adjBump t * Real.exp (-t / 2) := by
  have h1 : Integrable fun u => adjBump (u - 1 / 5) * Real.exp (-u / 2) :=
    ((adjBump.continuous.comp (continuous_id.sub continuous_const)).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        ((adjBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (1 / 5 : ℝ))).mul_right)
  have h2 : Integrable fun u => adjBump (u + 1 / 5) * Real.exp (-u / 2) :=
    ((adjBump.continuous.comp (continuous_id.add continuous_const)).mul (by fun_prop))
      |>.integrable_of_hasCompactSupport
        ((adjBump.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (1 / 5 : ℝ))).mul_right)
  have e : (fun u => adjReal σ u * Real.exp (-u / 2)) =
      fun u => adjBump (u - 1 / 5) * Real.exp (-u / 2) +
        σ * (adjBump (u + 1 / 5) * Real.exp (-u / 2)) := by
    funext u; simp only [adjReal]; ring
  rw [e, integral_add h1 (h2.const_mul σ), integral_const_mul, integral_adjBump_shift_exp]
  have h3 : ∫ u, adjBump (u + 1 / 5) * Real.exp (-u / 2) =
      Real.exp (1 / 5 / 2) * ∫ t, adjBump t * Real.exp (-t / 2) := by
    have := integral_adjBump_shift_exp (-(1 / 5))
    simp only [sub_neg_eq_add, neg_neg] at this
    exact this
  rw [h3]
  ring

theorem paperFT_adjTest_I_div_two (σ : ℝ) :
    paperFT (adjTest σ) (I / 2) =
      (((Real.exp (-(1 / 5) / 2) + σ * Real.exp (1 / 5 / 2)) *
        ∫ t, adjBump t * Real.exp (-t / 2) : ℝ) : ℂ) := by
  rw [show adjTest σ = fun u => ((adjReal σ u : ℝ) : ℂ) from rfl,
    RHTower.WeilLevyPole.paperFT_ofReal_I_div_two, integral_adjReal_exp]

/-- **The even two-bump test has positive pole term.** -/
theorem pole_adjTestFn_one_pos : 0 < (weilPoleTerm (EF.weilTest (adjTestFn 1).1 (adjTestFn 1).1)).re := by
  change 0 < (weilPoleTerm (EF.weilTest (adjTest 1) (adjTest 1))).re
  rw [RHTower.weilPoleTerm_even (continuous_adjTest 1) (hasCompactSupport_adjTest 1)
    (fun x => by simp [adjTest, adjReal_one_even]), Complex.ofReal_re, paperFT_adjTest_I_div_two,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := integral_adjBump_exp_pos
  have : 0 < Real.exp (-(1 / 5) / 2) + 1 * Real.exp (1 / 5 / 2) := by positivity
  positivity

/-- **The odd two-bump test has negative pole term.** -/
theorem pole_adjTestFn_neg_one_neg :
    (weilPoleTerm (EF.weilTest (adjTestFn (-1)).1 (adjTestFn (-1)).1)).re < 0 := by
  change (weilPoleTerm (EF.weilTest (adjTest (-1)) (adjTest (-1)))).re < 0
  rw [RHTower.weilPoleTerm_odd (continuous_adjTest (-1)) (hasCompactSupport_adjTest (-1))
    (fun x => by simp [adjTest, adjReal_neg_one_odd]), Complex.ofReal_re,
    paperFT_adjTest_I_div_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := integral_adjBump_exp_pos
  have hne : Real.exp (-(1 / 5) / 2) + (-1) * Real.exp (1 / 5 / 2) ≠ 0 := by
    have : Real.exp (-(1 / 5) / 2) < Real.exp (1 / 5 / 2) := Real.exp_lt_exp.mpr (by norm_num)
    intro h0; linarith
  have hsq : 0 < ((Real.exp (-(1 / 5) / 2) + (-1) * Real.exp (1 / 5 / 2)) *
      ∫ t, adjBump t * Real.exp (-t / 2)) ^ 2 := by positivity
  linarith

/-! ## Pole mass of a combination -/

/-- The total pole mass `Σ c_f Re P(k_f)` of a combination. -/
def nodePoleMass (c : WeilTestFn →₀ ℝ) : ℝ :=
  linearCombination ℝ (fun f : WeilTestFn => (weilPoleTerm (EF.weilTest f.1 f.1)).re) c

/-- The archimedean part without the pole: `A(c) − P(c)`. -/
def nodeArchOnly (c : WeilTestFn →₀ ℝ) : ℝ := nodeArchEnergy c - nodePoleMass c

theorem nodePoleMass_add (c d : WeilTestFn →₀ ℝ) :
    nodePoleMass (c + d) = nodePoleMass c + nodePoleMass d := by
  simp only [nodePoleMass, map_add]

theorem nodePoleMass_smul (t : ℝ) (c : WeilTestFn →₀ ℝ) : nodePoleMass (t • c) = t * nodePoleMass c := by
  simp only [nodePoleMass, map_smul, smul_eq_mul]

theorem nodePoleMass_single (f : WeilTestFn) (t : ℝ) :
    nodePoleMass (Finsupp.single f t) = t * (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  rw [nodePoleMass, linearCombination_single, smul_eq_mul]

theorem nodeArchOnly_add (c d : WeilTestFn →₀ ℝ) :
    nodeArchOnly (c + d) = nodeArchOnly c + nodeArchOnly d := by
  simp only [nodeArchOnly, nodeArchEnergy_add, nodePoleMass_add]; ring

theorem nodeArchOnly_smul (t : ℝ) (c : WeilTestFn →₀ ℝ) : nodeArchOnly (t • c) = t * nodeArchOnly c := by
  simp only [nodeArchOnly, nodeArchEnergy_smul, nodePoleMass_smul]; ring

theorem nodeVector_adjTestFn_single (σ t : ℝ) : nodeVector (Finsupp.single (adjTestFn σ) t) = 0 := by
  rw [nodeVector_eq, linearCombination_single, logVector_adjTestFn, smul_zero]

/-- **Every real pole mass is realised by a blind nonnegative combination.** -/
theorem exists_blind_nodePoleMass_eq (p : ℝ) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ nodeVector c = 0 ∧ nodePoleMass c = p := by
  classical
  rcases le_or_gt 0 p with hp | hp
  · set P := (weilPoleTerm (EF.weilTest (adjTestFn 1).1 (adjTestFn 1).1)).re with hP
    have hP0 := pole_adjTestFn_one_pos
    refine ⟨Finsupp.single (adjTestFn 1) (p / P), fun f => ?_, nodeVector_adjTestFn_single 1 _, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs <;> [exact div_nonneg hp hP0.le; exact le_rfl]
    · rw [nodePoleMass_single, ← hP, div_mul_cancel₀ _ hP0.ne']
  · set P := (weilPoleTerm (EF.weilTest (adjTestFn (-1)).1 (adjTestFn (-1)).1)).re with hP
    have hP0 := pole_adjTestFn_neg_one_neg
    refine ⟨Finsupp.single (adjTestFn (-1)) (p / P), fun f => ?_,
      nodeVector_adjTestFn_single (-1) _, ?_⟩
    · rw [Finsupp.single_apply]
      split_ifs
      · exact div_nonneg_of_nonpos hp.le hP0.le
      · exact le_rfl
    · rw [nodePoleMass_single, ← hP, div_mul_cancel₀ _ hP0.ne]

/-! ## The fibres over (node vector, pole mass) -/

/-- The archimedean parts `A(c) − P(c)` of the nonnegative combinations with node vector `v` and
pole mass `p`. -/
def poleFibre (v : LogIndex →₀ ℝ) (p : ℝ) : Set ℝ :=
  {E | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ nodeVector c = v ∧ nodePoleMass c = p ∧
    nodeArchOnly c = E}

/-- The value function `(v, p) ↦ inf poleFibre v p`. -/
def poleValue (v : LogIndex →₀ ℝ) (p : ℝ) : ℝ := sInf (poleFibre v p)

theorem poleFibre_nonempty (v : LogIndex →₀ ℝ) (p : ℝ) : (poleFibre v p).Nonempty := by
  obtain ⟨d, hd, hdv, hdp⟩ := exists_blind_nodePoleMass_eq (p - nodePoleMass (nodeLift v))
  refine ⟨nodeArchOnly (nodeLift v + d), nodeLift v + d, fun f => ?_, ?_, ?_, rfl⟩
  · rw [Finsupp.add_apply]; exact add_nonneg (nodeLift_nonneg v f) (hd f)
  · rw [nodeVector_add, nodeVector_nodeLift, hdv, add_zero]
  · rw [nodePoleMass_add, hdp]; ring

theorem add_mem_poleFibre {v w : LogIndex →₀ ℝ} {p q E F : ℝ} (hE : E ∈ poleFibre v p)
    (hF : F ∈ poleFibre w q) : E + F ∈ poleFibre (v + w) (p + q) := by
  obtain ⟨c, hc, hcv, hcp, rfl⟩ := hE
  obtain ⟨d, hd, hdw, hdq, rfl⟩ := hF
  refine ⟨c + d, fun f => ?_, ?_, ?_, ?_⟩
  · rw [Finsupp.add_apply]; exact add_nonneg (hc f) (hd f)
  · rw [nodeVector_add, hcv, hdw]
  · rw [nodePoleMass_add, hcp, hdq]
  · rw [nodeArchOnly_add]

theorem smul_mem_poleFibre {v : LogIndex →₀ ℝ} {p E t : ℝ} (ht : 0 ≤ t) (hE : E ∈ poleFibre v p) :
    t * E ∈ poleFibre (t • v) (t * p) := by
  obtain ⟨c, hc, hcv, hcp, rfl⟩ := hE
  refine ⟨t • c, fun f => ?_, ?_, ?_, ?_⟩
  · rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg ht (hc f)
  · rw [nodeVector_smul, hcv]
  · rw [nodePoleMass_smul, hcp]
  · rw [nodeArchOnly_smul]

theorem archOnly_single_mem_poleFibre (f : WeilTestFn) :
    weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re ∈
      poleFibre (logVector f) (weilPoleTerm (EF.weilTest f.1 f.1)).re :=
  ⟨Finsupp.single f 1, fun g => by
      classical
      rw [Finsupp.single_apply]; split_ifs <;> norm_num,
    nodeVector_single_test f, by rw [nodePoleMass_single, one_mul],
    by rw [nodeArchOnly, nodeArchEnergy_single_test, nodePoleMass_single, one_mul]⟩

/-! ## The zero-pole blind criterion (Farkas on the extended node vector) -/

/-- **Zero-pole blind positivity**: the archimedean symbol is nonnegative on every nonnegative
blind combination of total pole mass zero. -/
def ZeroPoleBlindPositive : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 → nodePoleMass c = 0 →
    0 ≤ nodeArchEnergy c

/-- The node vector extended by the pole mass, as a linear map into `Option LogIndex →₀ ℝ`
(`none` is the pole coordinate). -/
def extVector : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Option LogIndex →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ Option.some).comp (linearCombination ℝ logVector) +
    (Finsupp.lsingle none).comp
      (linearCombination ℝ fun f : WeilTestFn => (weilPoleTerm (EF.weilTest f.1 f.1)).re)

theorem extVector_apply (c : WeilTestFn →₀ ℝ) :
    extVector c = Finsupp.mapDomain Option.some (nodeVector c) + Finsupp.single none (nodePoleMass c) := by
  simp only [extVector, LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.lsingle_apply]
  rfl

theorem extVector_apply_some (c : WeilTestFn →₀ ℝ) (j : LogIndex) :
    extVector c (some j) = nodeVector c j := by
  rw [extVector_apply, Finsupp.add_apply, Finsupp.mapDomain_apply (Option.some_injective _),
    Finsupp.single_apply, if_neg (by simp), add_zero]

theorem extVector_apply_none (c : WeilTestFn →₀ ℝ) : extVector c none = nodePoleMass c := by
  rw [extVector_apply, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp),
    Finsupp.single_eq_same, zero_add]

theorem linearCombination_extVector (lam : Option LogIndex → ℝ) (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ lam (extVector c) =
      linearCombination ℝ (fun j : LogIndex => lam (some j)) (nodeVector c) +
        lam none * nodePoleMass c := by
  rw [extVector_apply, map_add, linearCombination_mapDomain, linearCombination_single, smul_eq_mul,
    mul_comm]
  rfl

/-- The nonnegative combinations, used as generators. -/
def NonnegCombo : Type := {c : WeilTestFn →₀ ℝ // ∀ f, 0 ≤ c f}

theorem nonnegCombo_sum_nonneg (c' : NonnegCombo →₀ ℝ) (hc' : ∀ i, 0 ≤ c' i) (f : WeilTestFn) :
    0 ≤ (c'.sum fun i t => t • i.1) f := by
  rw [Finsupp.sum_apply]
  exact Finsupp.sum_nonneg fun i _ => by
    rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg (hc' i) (i.2 f)

/-- A pole-corrected pair test at the node `j` with sign `σ`: node vector a multiple of `σ e_j`
and pole mass zero. -/
theorem exists_nonnegCombo_single_some (j : LogIndex) (σ : ℝ) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      extVector c = Finsupp.single (some j) (σ * (2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j)) := by
  classical
  obtain ⟨d, hd, hdv, hdp⟩ :=
    exists_blind_nodePoleMass_eq (-(nodePoleMass (Finsupp.single (pairTestFn j σ) 1)))
  refine ⟨Finsupp.single (pairTestFn j σ) 1 + d, fun f => ?_, ?_⟩
  · rw [Finsupp.add_apply]
    refine add_nonneg ?_ (hd f)
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [extVector_apply, nodeVector_add, nodePoleMass_add, hdv, hdp, add_zero, add_neg_cancel,
      Finsupp.single_zero, add_zero, nodeVector_eq, linearCombination_single, one_smul,
      logVector_pairTestFn, Finsupp.mapDomain_single]
    congr 1
    ring

/-- **RH is zero-pole blind positivity.**  The archimedean symbol `Re ψ(¼ + ir/2) − log π` is
nonnegative on every nonnegative combination of autocorrelations that is blind at all `±log n` and
has total pole mass zero, if and only if RH holds. -/
theorem riemannHypothesis_iff_zeroPoleBlindPositive : RiemannHypothesis ↔ ZeroPoleBlindPositive := by
  constructor
  · intro hRH c hc hv _
    have h := riemannHypothesis_iff_primeBlindPositive_unconditional.mp hRH c hc fun n hn => by
      have := congrArg (fun w : LogIndex →₀ ℝ => w ⟨n, hn⟩) hv
      simpa [nodeVector_eq, linearCombination_logVector_apply] using this
    rwa [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h
  · intro hZ
    classical
    -- Farkas on the extended node vector
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (ι := NonnegCombo) (J := Option LogIndex) (fun i => extVector i.1) (fun i => nodeArchEnergy i.1)
      (fun o => by
        rcases o with _ | j
        · refine ⟨⟨Finsupp.single (adjTestFn (-1)) 1, fun f => ?_⟩,
            -(weilPoleTerm (EF.weilTest (adjTestFn (-1)).1 (adjTestFn (-1)).1)).re,
            by linarith [pole_adjTestFn_neg_one_neg], ?_⟩
          · rw [Finsupp.single_apply]; split_ifs <;> norm_num
          · simp only
            rw [extVector_apply, nodeVector_adjTestFn_single, Finsupp.mapDomain_zero, zero_add,
              nodePoleMass_single, one_mul, neg_neg]
        · obtain ⟨c, hc, hce⟩ := exists_nonnegCombo_single_some j (-1)
          refine ⟨⟨c, hc⟩, 2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j, pairTest_weight_pos j, ?_⟩
          simp only
          rw [hce]; congr 1; ring)
      (fun o => by
        rcases o with _ | j
        · refine ⟨⟨Finsupp.single (adjTestFn 1) 1, fun f => ?_⟩,
            (weilPoleTerm (EF.weilTest (adjTestFn 1).1 (adjTestFn 1).1)).re,
            pole_adjTestFn_one_pos, ?_⟩
          · rw [Finsupp.single_apply]; split_ifs <;> norm_num
          · simp only
            rw [extVector_apply, nodeVector_adjTestFn_single, Finsupp.mapDomain_zero, zero_add,
              nodePoleMass_single, one_mul]
        · obtain ⟨c, hc, hce⟩ := exists_nonnegCombo_single_some j 1
          refine ⟨⟨c, hc⟩, 2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j, pairTest_weight_pos j, ?_⟩
          simp only
          rw [hce]; congr 1; ring)
      (fun c' hc' hnull => by
        -- the combined combination is blind with zero pole mass
        set C : WeilTestFn →₀ ℝ := c'.sum fun i t => t • i.1 with hC
        have hCext : extVector C = linearCombination ℝ (fun i : NonnegCombo => extVector i.1) c' := by
          rw [hC, map_finsuppSum, linearCombination_apply]
          exact Finsupp.sum_congr fun i _ => by rw [map_smul]
        have hCA : nodeArchEnergy C = linearCombination ℝ (fun i : NonnegCombo => nodeArchEnergy i.1) c' := by
          rw [hC, nodeArchEnergy_eq, map_finsuppSum, linearCombination_apply]
          exact Finsupp.sum_congr fun i _ => by rw [map_smul]; rfl
        rw [← hCA]
        refine hZ C (nonnegCombo_sum_nonneg c' hc') ?_ ?_
        · ext j
          have := extVector_apply_some C j
          rw [hCext, hnull] at this
          simpa using this.symm
        · have := extVector_apply_none C
          rw [hCext, hnull] at this
          simpa using this.symm)
    -- the dual weights are Weil-positive at pole weight `1 − lam none`
    set w : LogIndex → ℝ := fun j => lam (some j) with hw
    set lamN : ℕ → ℝ := fun n => if hn : 2 ≤ n then w ⟨n, hn⟩ else 0 with hlamN
    have hsingle : ∀ f : WeilTestFn,
        linearCombination ℝ w (logVector f) + lam none * (weilPoleTerm (EF.weilTest f.1 f.1)).re ≤
          weilArchRe (EF.weilTest f.1 f.1) := by
      intro f
      have h := hlam ⟨Finsupp.single f 1, fun g => by
        rw [Finsupp.single_apply]; split_ifs <;> norm_num⟩
      simp only at h
      rwa [linearCombination_extVector, nodeVector_single_test, nodePoleMass_single, one_mul,
        nodeArchEnergy_single_test] at h
    have hW : RHTower.WeilPositiveAt (1 - lam none) lamN := by
      intro f hf hc
      have h := RHTower.re_weilPoleWeightFunctional_eq (1 - lam none) lamN ⟨f, hf, hc⟩
      change (WeilPoleWeight.weilPoleWeightFunctional (1 - lam none) lamN (EF.weilTest f f)).re = _ at h
      rw [h]
      have e : (fun j : LogIndex => lamN (j : ℕ)) = w := funext fun j => by simp [hlamN, j.2]
      rw [e]
      have := hsingle ⟨f, hf, hc⟩
      simp only [RHTower.poleWeightArchRe] at this ⊢
      linarith
    have hb : 1 - lam none = 1 := RHTower.eq_one_of_weilPositiveAt hW
    have hnone : lam none = 0 := by linarith
    have hle : ∀ f : WeilTestFn,
        linearCombination ℝ w (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := fun f => by
      have := hsingle f
      rwa [hnone, zero_mul, add_zero] at this
    exact riemannHypothesis_iff_primeBlindPositive_unconditional.mpr
      (exists_weilPositiveFull_iff_primeBlindPositive.mp ⟨_, weilPositiveFull_of_le_arch hle⟩)

/-! ## The linear law under RH -/

/-- Under RH every value in the fibre over `(v, p)` is at least `⟨Λ, v⟩ − p`. -/
theorem vonMangoldtPairing_sub_le_of_mem_poleFibre (hRH : RiemannHypothesis) {v : LogIndex →₀ ℝ}
    {p E : ℝ} (hE : E ∈ poleFibre v p) : vonMangoldtPairing v - p ≤ E := by
  obtain ⟨c, hc, hcv, hcp, rfl⟩ := hE
  have h := vonMangoldtPairing_le_of_mem_nodeFibre hRH ⟨c, hc, hcv, rfl⟩
  rw [nodeArchOnly, hcp]
  linarith

theorem bddBelow_poleFibre (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) (p : ℝ) :
    BddBelow (poleFibre v p) :=
  ⟨vonMangoldtPairing v - p, fun _ hE => vonMangoldtPairing_sub_le_of_mem_poleFibre hRH hE⟩

theorem vonMangoldtPairing_sub_le_poleValue (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) (p : ℝ) :
    vonMangoldtPairing v - p ≤ poleValue v p :=
  le_csInf (poleFibre_nonempty v p) fun _ hE => vonMangoldtPairing_sub_le_of_mem_poleFibre hRH hE

theorem poleValue_le_of_mem (hRH : RiemannHypothesis) {v : LogIndex →₀ ℝ} {p E : ℝ}
    (hE : E ∈ poleFibre v p) : poleValue v p ≤ E :=
  csInf_le (bddBelow_poleFibre hRH v p) hE

theorem poleValue_zero (hRH : RiemannHypothesis) : poleValue 0 0 = 0 := by
  refine le_antisymm (poleValue_le_of_mem hRH ⟨0, fun _ => le_rfl, by simp [nodeVector_eq],
    by simp [nodePoleMass], by simp [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass]⟩) ?_
  have := vonMangoldtPairing_sub_le_poleValue hRH 0 0
  rwa [vonMangoldtPairing, map_zero, sub_zero] at this

theorem poleValue_add_le (hRH : RiemannHypothesis) (v w : LogIndex →₀ ℝ) (p q : ℝ) :
    poleValue (v + w) (p + q) ≤ poleValue v p + poleValue w q := by
  have h : ∀ E ∈ poleFibre v p, ∀ F ∈ poleFibre w q, poleValue (v + w) (p + q) ≤ E + F :=
    fun E hE F hF => poleValue_le_of_mem hRH (add_mem_poleFibre hE hF)
  have h1 : ∀ F ∈ poleFibre w q, poleValue (v + w) (p + q) - F ≤ poleValue v p := fun F hF =>
    le_csInf (poleFibre_nonempty v p) fun E hE => by linarith [h E hE F hF]
  have h2 : poleValue (v + w) (p + q) - poleValue v p ≤ poleValue w q :=
    le_csInf (poleFibre_nonempty w q) fun F hF => by linarith [h1 F hF]
  linarith

theorem poleFibre_smul {v : LogIndex →₀ ℝ} {p t : ℝ} (ht : 0 < t) :
    poleFibre (t • v) (t * p) = (fun E => t * E) '' poleFibre v p := by
  ext E
  constructor
  · intro hE
    refine ⟨t⁻¹ * E, ?_, by simp only; rw [mul_inv_cancel_left₀ ht.ne']⟩
    have := smul_mem_poleFibre (inv_nonneg.mpr ht.le) hE
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ ht.ne',
      one_mul] at this
  · rintro ⟨F, hF, rfl⟩
    exact smul_mem_poleFibre ht.le hF

theorem poleValue_smul (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t) (v : LogIndex →₀ ℝ) (p : ℝ) :
    poleValue (t • v) (t * p) = t * poleValue v p := by
  rw [poleValue, poleValue, poleFibre_smul ht]
  have hne := poleFibre_nonempty v p
  have hbdd := bddBelow_poleFibre hRH v p
  have hbdd' : BddBelow ((fun E => t * E) '' poleFibre v p) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨t * b, by rintro _ ⟨E, hE, rfl⟩; exact mul_le_mul_of_nonneg_left (hb hE) ht.le⟩
  refine le_antisymm ?_ ?_
  · have h2 : t⁻¹ * sInf ((fun E => t * E) '' poleFibre v p) ≤ sInf (poleFibre v p) := by
      refine le_csInf hne fun E hE => ?_
      rw [inv_mul_le_iff₀ ht]
      exact csInf_le hbdd' ⟨E, hE, rfl⟩
    have := mul_le_mul_of_nonneg_left h2 ht.le
    rwa [mul_inv_cancel_left₀ ht.ne'] at this
  · refine le_csInf (s := (fun E => t * E) '' poleFibre v p) (hne.image _) ?_
    rintro _ ⟨E, hE, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd hE) ht.le

/-- The value function on the product space `(LogIndex →₀ ℝ) × ℝ`. -/
def poleValueProd (x : (LogIndex →₀ ℝ) × ℝ) : ℝ := poleValue x.1 x.2

theorem poleValueProd_smul (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t) (x : (LogIndex →₀ ℝ) × ℝ) :
    poleValueProd (t • x) = t * poleValueProd x := by
  obtain ⟨v, p⟩ := x
  rw [Prod.smul_mk, poleValueProd, poleValueProd, smul_eq_mul, poleValue_smul hRH ht]

theorem poleValueProd_add_le (hRH : RiemannHypothesis) (x y : (LogIndex →₀ ℝ) × ℝ) :
    poleValueProd (x + y) ≤ poleValueProd x + poleValueProd y := by
  obtain ⟨v, p⟩ := x
  obtain ⟨w, q⟩ := y
  rw [Prod.mk_add_mk]
  exact poleValue_add_le hRH v w p q

theorem poleValueProd_add_neg_nonneg (hRH : RiemannHypothesis) (x : (LogIndex →₀ ℝ) × ℝ) :
    0 ≤ poleValueProd x + poleValueProd (-x) := by
  have := poleValueProd_add_le hRH x (-x)
  rw [add_neg_cancel] at this
  have h0 : poleValueProd 0 = 0 := poleValue_zero hRH
  linarith

theorem mul_poleValueProd_le (hRH : RiemannHypothesis) (t : ℝ) (x : (LogIndex →₀ ℝ) × ℝ) :
    t * poleValueProd x ≤ poleValueProd (t • x) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have e : t • x = (-t) • (-x) := (neg_smul_neg t x).symm
    rw [e, poleValueProd_smul hRH (by linarith) (-x)]
    have := poleValueProd_add_neg_nonneg hRH x
    nlinarith
  · rw [zero_smul]
    have h0 : poleValueProd 0 = 0 := poleValue_zero hRH
    rw [h0, zero_mul]
  · rw [poleValueProd_smul hRH ht]

/-- A linear functional on node vectors dominated by the archimedean energy on single tests is the
von Mangoldt pairing. -/
theorem linearMap_eq_vonMangoldtPairing_of_le_arch (g : (LogIndex →₀ ℝ) →ₗ[ℝ] ℝ)
    (hg : ∀ f : WeilTestFn, g (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1))
    (v : LogIndex →₀ ℝ) : g v = vonMangoldtPairing v := by
  set lam : LogIndex → ℝ := fun j => g (Finsupp.single j 1) with hlam
  have hle : ∀ f : WeilTestFn,
      linearCombination ℝ lam (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := by
    intro f
    rw [hlam, ← linearMap_eq_linearCombination g]
    exact hg f
  have hΛ := RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull (weilPositiveFull_of_le_arch hle)
  have hlamΛ : lam = fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ) := by
    funext j
    have := hΛ j j.2
    simpa [j.2] using this
  rw [linearMap_eq_linearCombination g, ← hlam, hlamΛ]
  rfl

/-- **The value function with the pole coordinate is linear with gradient `(Λ, −1)`.**  Under RH,
`inf {A(c) − P(c) : c ≥ 0, L(c) = v, P(c) = p} = Σ_n Λ(n) v_n − p` for every node vector `v` and
every pole mass `p`. -/
theorem poleValue_eq (hRH : RiemannHypothesis) (v : LogIndex →₀ ℝ) (p : ℝ) :
    poleValue v p = vonMangoldtPairing v - p := by
  set x₀ : (LogIndex →₀ ℝ) × ℝ := (v, p) with hx₀
  by_cases hx : x₀ = 0
  · have hv : v = 0 := congrArg Prod.fst hx
    have hp : p = 0 := congrArg Prod.snd hx
    subst hv; subst hp
    rw [poleValue_zero hRH, vonMangoldtPairing, map_zero, sub_zero]
  have H : ∀ c : ℝ, c • x₀ = 0 → (RingHom.id ℝ) c • poleValueProd x₀ = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · exfalso
      apply hx
      have : x₀ = c⁻¹ • (c • x₀) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, hc, smul_zero]
  set φ : ((LogIndex →₀ ℝ) × ℝ) →ₗ.[ℝ] ℝ :=
    LinearPMap.mkSpanSingleton' (R := ℝ) (S := ℝ) (σ := RingHom.id ℝ) x₀ (poleValueProd x₀) H
    with hφ
  have hdom : ∀ y : φ.domain, φ y ≤ poleValueProd y := by
    intro y
    have hy : (y : (LogIndex →₀ ℝ) × ℝ) ∈ Submodule.span ℝ {x₀} := y.2
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
    have hy' : y = ⟨a • x₀, by rw [ha]; exact y.2⟩ := Subtype.ext ha.symm
    rw [hy']
    have h' : (φ ⟨a • x₀, by rw [ha]; exact y.2⟩ : ℝ) = (RingHom.id ℝ) a • poleValueProd x₀ :=
      LinearPMap.mkSpanSingleton'_apply (R := ℝ) (S := ℝ) (σ := RingHom.id ℝ) x₀
        (poleValueProd x₀) H a (by rw [ha]; exact y.2)
    rw [h']
    simp only [RingHom.id_apply, smul_eq_mul]
    exact mul_poleValueProd_le hRH a x₀
  obtain ⟨g, hgφ, hg⟩ := exists_extension_of_le_sublinear φ poleValueProd
    (fun c hc y => poleValueProd_smul hRH hc y) (poleValueProd_add_le hRH) hdom
  have hgx : g x₀ = poleValueProd x₀ := by
    have hmem : x₀ ∈ φ.domain := Submodule.mem_span_singleton_self x₀
    have := hgφ ⟨x₀, hmem⟩
    have h' : (φ ⟨x₀, hmem⟩ : ℝ) = poleValueProd x₀ :=
      LinearPMap.mkSpanSingleton'_apply_self (R := ℝ) (S := ℝ) (σ := RingHom.id ℝ) x₀
        (poleValueProd x₀) H hmem
    rw [this, h']
  -- decompose `g` into its node part and its pole slope
  set g₁ : (LogIndex →₀ ℝ) →ₗ[ℝ] ℝ := g.comp (LinearMap.inl ℝ (LogIndex →₀ ℝ) ℝ) with hg₁
  set b : ℝ := g (0, 1) with hb
  have hsplit : ∀ w : LogIndex →₀ ℝ, ∀ q : ℝ, g (w, q) = g₁ w + q * b := by
    intro w q
    have e : ((w, q) : (LogIndex →₀ ℝ) × ℝ) = (w, 0) + q • (0, 1) := by
      ext <;> simp
    rw [e, map_add, g.map_smul, smul_eq_mul, hg₁, LinearMap.comp_apply, LinearMap.inl_apply]
  -- on single tests `g` is dominated by the archimedean part without the pole
  have hsingle : ∀ f : WeilTestFn,
      g₁ (logVector f) + (weilPoleTerm (EF.weilTest f.1 f.1)).re * b ≤
        weilArchRe (EF.weilTest f.1 f.1) - (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
    intro f
    have h1 := hg (logVector f, (weilPoleTerm (EF.weilTest f.1 f.1)).re)
    have h2 := poleValue_le_of_mem hRH (archOnly_single_mem_poleFibre f)
    rw [hsplit] at h1
    exact h1.trans h2
  -- pole-weight rigidity: `b = −1`
  set lam : LogIndex → ℝ := fun j => g₁ (Finsupp.single j 1) with hlam
  set lamN : ℕ → ℝ := fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0 with hlamN
  have hW : RHTower.WeilPositiveAt (-b) lamN := by
    intro f hf hc
    have h := RHTower.re_weilPoleWeightFunctional_eq (-b) lamN ⟨f, hf, hc⟩
    change (WeilPoleWeight.weilPoleWeightFunctional (-b) lamN (EF.weilTest f f)).re = _ at h
    rw [h]
    have e : (fun j : LogIndex => lamN (j : ℕ)) = lam := funext fun j => by simp [hlamN, j.2]
    rw [e, hlam, ← linearMap_eq_linearCombination g₁]
    have := hsingle ⟨f, hf, hc⟩
    simp only [RHTower.poleWeightArchRe] at this ⊢
    linarith
  have hb1 : b = -1 := by
    have := RHTower.eq_one_of_weilPositiveAt hW
    linarith
  -- cone uniqueness: `g₁ = ⟨Λ, ·⟩`
  have hg₁Λ : ∀ w, g₁ w = vonMangoldtPairing w := by
    refine linearMap_eq_vonMangoldtPairing_of_le_arch g₁ fun f => ?_
    have := hsingle f
    rw [hb1] at this
    linarith
  have : g x₀ = vonMangoldtPairing v - p := by
    rw [hx₀, hsplit, hg₁Λ, hb1]; ring
  rw [← this, hgx]
  rfl

/-- Under RH, blind combinations of pole mass `p` have archimedean part at least `−p`, sharply:
`inf {A(c) − P(c) : c blind, P(c) = p} = −p`. -/
theorem poleValue_zero_left (hRH : RiemannHypothesis) (p : ℝ) : poleValue 0 p = -p := by
  rw [poleValue_eq hRH, vonMangoldtPairing, map_zero, zero_sub]

/-! ## Criteria -/

/-- **RH is the lower bound `⟨Λ, v⟩ − p` on every fibre.** -/
theorem riemannHypothesis_iff_forall_le_poleFibre :
    RiemannHypothesis ↔
      ∀ (v : LogIndex →₀ ℝ) (p : ℝ), ∀ E ∈ poleFibre v p, vonMangoldtPairing v - p ≤ E := by
  constructor
  · intro hRH v p E hE
    exact vonMangoldtPairing_sub_le_of_mem_poleFibre hRH hE
  · intro h
    refine riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp => ?_
    have := h 0 0 (nodeArchOnly c) ⟨c, hc, hv, hp, rfl⟩
    rw [vonMangoldtPairing, map_zero, sub_zero, nodeArchOnly, hp, sub_zero] at this
    exact this

/-- **If RH fails, every fibre is unbounded below.** -/
theorem not_bddBelow_poleFibre (hRH : ¬ RiemannHypothesis) (v : LogIndex →₀ ℝ) (p : ℝ) :
    ¬ BddBelow (poleFibre v p) := by
  have hZ : ¬ ZeroPoleBlindPositive := fun h => hRH (riemannHypothesis_iff_zeroPoleBlindPositive.mpr h)
  simp only [ZeroPoleBlindPositive, not_forall, not_le, exists_prop] at hZ
  obtain ⟨c₀, hc₀, hv₀, hp₀, hneg⟩ := hZ
  obtain ⟨E₀, c₁, hc₁, hc₁v, hc₁p, rfl⟩ := poleFibre_nonempty v p
  rw [not_bddBelow_iff]
  intro x
  set t : ℝ := (|nodeArchOnly c₁| + |x| + 1) / (-nodeArchEnergy c₀) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  refine ⟨nodeArchOnly (c₁ + t • c₀), ⟨c₁ + t • c₀, fun f => ?_, ?_, ?_, rfl⟩, ?_⟩
  · rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact add_nonneg (hc₁ f) (mul_nonneg ht0 (hc₀ f))
  · rw [nodeVector_add, nodeVector_smul, hc₁v, hv₀, smul_zero, add_zero]
  · rw [nodePoleMass_add, nodePoleMass_smul, hc₁p, hp₀, mul_zero, add_zero]
  · have e0 : nodeArchOnly c₀ = nodeArchEnergy c₀ := by rw [nodeArchOnly, hp₀, sub_zero]
    rw [nodeArchOnly_add, nodeArchOnly_smul, e0]
    have h2 : t * nodeArchEnergy c₀ = -(|nodeArchOnly c₁| + |x| + 1) := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith : -nodeArchEnergy c₀ ≠ 0)]
      ring
    have h3 := le_abs_self (nodeArchOnly c₁)
    have h4 := neg_abs_le x
    linarith

/-- **RH is the boundedness of a single fibre.** -/
theorem riemannHypothesis_iff_bddBelow_poleFibre (v : LogIndex →₀ ℝ) (p : ℝ) :
    RiemannHypothesis ↔ BddBelow (poleFibre v p) :=
  ⟨fun h => bddBelow_poleFibre h v p, fun h => by
    by_contra hRH
    exact not_bddBelow_poleFibre hRH v p h⟩

end

end RHTower.WeilOneSided

namespace RHTower.WeilOneSided

noncomputable section

/-- **RH is the bound of the symbol's deficit by the positive pole mass.**  RH holds iff on every
nonnegative blind combination the archimedean symbol integral is at least `−max(P(c), 0)`: only
the positive part of the pole mass can be charged against the symbol. -/
theorem riemannHypothesis_iff_forall_blind_archOnly_add_posPart_nonneg :
    RiemannHypothesis ↔
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 →
        0 ≤ nodeArchOnly c + max (nodePoleMass c) 0 := by
  constructor
  · intro hRH c hc hv
    have h := riemannHypothesis_iff_primeBlindPositive_unconditional.mp hRH c hc fun n hn => by
      have := congrArg (fun w : LogIndex →₀ ℝ => w ⟨n, hn⟩) hv
      simpa [nodeVector_eq, linearCombination_logVector_apply] using this
    rw [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h
    have := le_max_left (nodePoleMass c) 0
    rw [nodeArchOnly]
    linarith
  · intro h
    refine riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp => ?_
    have := h c hc hv
    rwa [hp, max_self, add_zero, nodeArchOnly, hp, sub_zero] at this

/-- **The pole-positive and pole-nonpositive sectors are each RH-complete.**  RH holds iff the pole
and archimedean energy is nonnegative on the blind combinations of nonpositive pole mass, and iff it
is nonnegative on those of nonnegative pole mass. -/
theorem riemannHypothesis_iff_blind_nonposPole_sector :
    RiemannHypothesis ↔
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 → nodePoleMass c ≤ 0 →
        0 ≤ nodeArchEnergy c := by
  constructor
  · intro hRH c hc hv _
    have h := riemannHypothesis_iff_primeBlindPositive_unconditional.mp hRH c hc fun n hn => by
      have := congrArg (fun w : LogIndex →₀ ℝ => w ⟨n, hn⟩) hv
      simpa [nodeVector_eq, linearCombination_logVector_apply] using this
    rwa [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h
  · intro h
    exact riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp => h c hc hv hp.le

theorem riemannHypothesis_iff_blind_nonnegPole_sector :
    RiemannHypothesis ↔
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) → nodeVector c = 0 → 0 ≤ nodePoleMass c →
        0 ≤ nodeArchEnergy c := by
  constructor
  · intro hRH c hc hv _
    have h := riemannHypothesis_iff_primeBlindPositive_unconditional.mp hRH c hc fun n hn => by
      have := congrArg (fun w : LogIndex →₀ ℝ => w ⟨n, hn⟩) hv
      simpa [nodeVector_eq, linearCombination_logVector_apply] using this
    rwa [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at h
  · intro h
    exact riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp => h c hc hv hp.ge

end

end RHTower.WeilOneSided
