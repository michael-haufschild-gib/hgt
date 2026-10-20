import GaloisForLFunctions.BiScaleUncertainty.PowerNodeRemovalLaw
import GaloisForLFunctions.RHTower.ArchimedeanPoleValueFunction
import GaloisForLFunctions.RHTower.PrimeBlindNodeCriticality

/-!
# Zero-pole positivity is node-critical: incidence, not density

`ZeroPoleBlindPositiveOn 𝒩` says that the archimedean symbol is nonnegative on every nonnegative
combination of Weil tests that is blind at the nodes `log n`, `n ∈ 𝒩`, and has total pole mass zero.
On the full integer grid it is RH (`riemannHypothesis_iff_zeroPoleBlindPositiveOn_all`); on gapped
node sets and on node sets of sub-square-root window density it fails, because the pole can be
carried at vanishing archimedean cost (`PoleInvisibilityOnGappedBlindGrids`,
`SquareRootDensityPoleInvisibility`). This module decides every node set.

**Theorem** (`zeroPoleBlindPositiveOn_iff`). For every `𝒩 ⊆ ℕ`,

`ZeroPoleBlindPositiveOn 𝒩 ↔ RH ∧ (every prime power lies in 𝒩)`.

So the dividing line is not a density threshold but an incidence condition:
* the prime powers (`≍ e^X/X` nodes per unit window) carry the full criterion
  (`riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers`);
* the primes alone, although far above square-root density, never suffice: the prime squares are
  missing, and the first of them is `4` (`not_zeroPoleBlindPositiveOn_primes`);
* deleting one prime power from any node set, however dense, falsifies the statement
  unconditionally (`not_zeroPoleBlindPositiveOn_diff_of_isPrimePow`; `log 4` in
  `not_zeroPoleBlindPositiveOn_diff_four`), while deleting any integer that is not a prime power
  changes nothing (`zeroPoleBlindPositiveOn_diff_iff_of_not_isPrimePow`; `log 6` in
  `zeroPoleBlindPositiveOn_diff_six_iff`).

The pole constraint is invisible to node criticality: zero-pole positivity and pole-retained
prime-blind positivity hold on exactly the same node sets (`zeroPoleBlindPositiveOn_iff_primeBlindPositiveOn`).

**Mechanism** (`exists_weilPositiveFull_of_zeroPoleBlindPositiveOn`). Two-sided Farkas duality on the
node values in `𝒩` extended by the pole coordinate, with pole-corrected pair tests and the blind
two-bump tests of both pole signs as generators, turns zero-pole positivity on `𝒩` into a weight
system supported on `𝒩` that is Weil-positive at some pole weight. Pole-weight rigidity
(`RHTower.eq_one_of_weilPositiveAt`) fixes the pole weight at `1`, and Weil-cone uniqueness
(`RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull`) identifies the weights with `Λ`. A node
is indispensable exactly when the certificate must charge it: `Λ(4) = log 2`, `Λ(6) = 0`.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Node values on `𝒩` extended by the pole coordinate -/

/-- Node values on `𝒩` (coordinates `some a`) together with the pole mass (coordinate `none`). -/
def extVectorOn (𝒩 : Set ℕ) :
    (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Option {j : LogIndex // (j : ℕ) ∈ 𝒩} →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ Option.some).comp (linearCombination ℝ (logVectorOn 𝒩)) +
    (Finsupp.lsingle none).comp
      (linearCombination ℝ fun f : WeilTestFn => (weilPoleTerm (EF.weilTest f.1 f.1)).re)

theorem extVectorOn_apply (𝒩 : Set ℕ) (c : WeilTestFn →₀ ℝ) :
    extVectorOn 𝒩 c = Finsupp.mapDomain Option.some (linearCombination ℝ (logVectorOn 𝒩) c) +
      Finsupp.single none (nodePoleMass c) := by
  simp only [extVectorOn, LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.lsingle_apply]
  rfl

theorem extVectorOn_apply_some (𝒩 : Set ℕ) (c : WeilTestFn →₀ ℝ)
    (a : {j : LogIndex // (j : ℕ) ∈ 𝒩}) : extVectorOn 𝒩 c (some a) = nodeVector c a.1 := by
  rw [extVectorOn_apply, Finsupp.add_apply, Finsupp.mapDomain_apply (Option.some_injective _),
    Finsupp.single_apply, if_neg (by simp), add_zero, linearCombination_logVectorOn_apply,
    nodeVector_eq, linearCombination_logVector_apply]

theorem extVectorOn_apply_none (𝒩 : Set ℕ) (c : WeilTestFn →₀ ℝ) :
    extVectorOn 𝒩 c none = nodePoleMass c := by
  rw [extVectorOn_apply, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ (by simp),
    Finsupp.single_eq_same, zero_add]

theorem linearCombination_extVectorOn (𝒩 : Set ℕ) (lam : Option {j : LogIndex // (j : ℕ) ∈ 𝒩} → ℝ)
    (c : WeilTestFn →₀ ℝ) :
    linearCombination ℝ lam (extVectorOn 𝒩 c) =
      linearCombination ℝ (fun a => lam (some a)) (linearCombination ℝ (logVectorOn 𝒩) c) +
        lam none * nodePoleMass c := by
  rw [extVectorOn_apply, map_add, linearCombination_mapDomain, linearCombination_single,
    smul_eq_mul, mul_comm]
  rfl

/-- The extended vector of a pole-corrected pair test at a node of `𝒩`. -/
theorem exists_nonnegCombo_extVectorOn_single (𝒩 : Set ℕ) (a : {j : LogIndex // (j : ℕ) ∈ 𝒩})
    (σ : ℝ) : ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      extVectorOn 𝒩 c =
        Finsupp.single (some a) (σ * (2 * (∫ t, (narrowBump a.1 t) ^ 2) / Real.sqrt a.1)) := by
  obtain ⟨c, hc, hce⟩ := exists_nonnegCombo_single_some a.1 σ
  refine ⟨c, hc, ?_⟩
  ext o
  rcases o with _ | b
  · rw [extVectorOn_apply_none, ← extVector_apply_none, hce, Finsupp.single_apply,
      Finsupp.single_apply, if_neg (by simp), if_neg (by simp)]
  · rw [extVectorOn_apply_some, ← extVector_apply_some, hce, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (by simpa using fun h' => h (Subtype.ext h')), if_neg (by simpa using h)]

/-! ### 2. The certificate of zero-pole positivity on `𝒩` -/

/-- **Zero-pole positivity on `𝒩` produces a Weil-positive weight supported on `𝒩`.** -/
theorem exists_weilPositiveFull_of_zeroPoleBlindPositiveOn {𝒩 : Set ℕ}
    (hZ : ZeroPoleBlindPositiveOn 𝒩) :
    ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∀ n, 2 ≤ n → n ∉ 𝒩 → lam n = 0 := by
  classical
  obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
    (fun i : NonnegCombo => extVectorOn 𝒩 i.1) (fun i => nodeArchEnergy i.1)
    (fun o => by
      rcases o with _ | a
      · refine ⟨⟨Finsupp.single (adjTestFn (-1)) 1, fun f => ?_⟩,
          -(weilPoleTerm (EF.weilTest (adjTestFn (-1)).1 (adjTestFn (-1)).1)).re,
          by linarith [pole_adjTestFn_neg_one_neg], ?_⟩
        · rw [Finsupp.single_apply]; split_ifs <;> norm_num
        · simp only
          rw [extVectorOn_apply, linearCombination_single, one_smul]
          have h0 : logVectorOn 𝒩 (adjTestFn (-1)) = 0 := by
            rw [logVectorOn, logVector_adjTestFn, Finsupp.subtypeDomain_zero]
          rw [h0, Finsupp.mapDomain_zero, zero_add, nodePoleMass_single, one_mul, neg_neg]
      · obtain ⟨c, hc, hce⟩ := exists_nonnegCombo_extVectorOn_single 𝒩 a (-1)
        exact ⟨⟨c, hc⟩, 2 * (∫ t, (narrowBump a.1 t) ^ 2) / Real.sqrt a.1,
          pairTest_weight_pos a.1, by simp only; rw [hce]; congr 1; ring⟩)
    (fun o => by
      rcases o with _ | a
      · refine ⟨⟨Finsupp.single (adjTestFn 1) 1, fun f => ?_⟩,
          (weilPoleTerm (EF.weilTest (adjTestFn 1).1 (adjTestFn 1).1)).re,
          pole_adjTestFn_one_pos, ?_⟩
        · rw [Finsupp.single_apply]; split_ifs <;> norm_num
        · simp only
          rw [extVectorOn_apply, linearCombination_single, one_smul]
          have h0 : logVectorOn 𝒩 (adjTestFn 1) = 0 := by
            rw [logVectorOn, logVector_adjTestFn, Finsupp.subtypeDomain_zero]
          rw [h0, Finsupp.mapDomain_zero, zero_add, nodePoleMass_single, one_mul]
      · obtain ⟨c, hc, hce⟩ := exists_nonnegCombo_extVectorOn_single 𝒩 a 1
        exact ⟨⟨c, hc⟩, 2 * (∫ t, (narrowBump a.1 t) ^ 2) / Real.sqrt a.1,
          pairTest_weight_pos a.1, by simp only; rw [hce]; congr 1; ring⟩)
    (fun c' hc' hnull => by
      set C : WeilTestFn →₀ ℝ := c'.sum fun i t => t • i.1 with hC
      have hCext : extVectorOn 𝒩 C =
          linearCombination ℝ (fun i : NonnegCombo => extVectorOn 𝒩 i.1) c' := by
        rw [hC, map_finsuppSum, linearCombination_apply]
        exact Finsupp.sum_congr fun i _ => by rw [map_smul]
      have hCA : nodeArchEnergy C =
          linearCombination ℝ (fun i : NonnegCombo => nodeArchEnergy i.1) c' := by
        rw [hC, nodeArchEnergy_eq, map_finsuppSum, linearCombination_apply]
        exact Finsupp.sum_congr fun i _ => by rw [map_smul]; rfl
      rw [← hCA]
      refine hZ C (nonnegCombo_sum_nonneg c' hc') (fun j hj => ?_) ?_
      · have := extVectorOn_apply_some 𝒩 C ⟨j, hj⟩
        rw [hCext, hnull] at this
        simpa using this.symm
      · have := extVectorOn_apply_none 𝒩 C
        rw [hCext, hnull] at this
        simpa using this.symm)
  -- the dual weights, extended by `0` off `𝒩`
  set w : LogIndex → ℝ := fun j => if hj : (j : ℕ) ∈ 𝒩 then lam (some ⟨j, hj⟩) else 0 with hw
  set lamN : ℕ → ℝ := fun n => if hn : 2 ≤ n then w ⟨n, hn⟩ else 0 with hlamN
  have hsingle : ∀ f : WeilTestFn,
      linearCombination ℝ w (logVector f) + lam none * (weilPoleTerm (EF.weilTest f.1 f.1)).re ≤
        weilArchRe (EF.weilTest f.1 f.1) := by
    intro f
    have h := hlam ⟨Finsupp.single f 1, fun g => by
      rw [Finsupp.single_apply]; split_ifs <;> norm_num⟩
    simp only at h
    rw [linearCombination_extVectorOn, linearCombination_single, one_smul, nodePoleMass_single,
      one_mul, nodeArchEnergy_single_test, ← linearCombination_extendOn] at h
    exact h
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
  have hnone : lam none = 0 := by linarith [RHTower.eq_one_of_weilPositiveAt hW]
  have hle : ∀ f : WeilTestFn,
      linearCombination ℝ w (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := fun f => by
    have := hsingle f
    rwa [hnone, zero_mul, add_zero] at this
  refine ⟨_, weilPositiveFull_of_le_arch hle, fun n hn hn𝒩 => ?_⟩
  simp [hw, hn, hn𝒩]

/-! ### 3. The classification -/

/-- **Zero-pole positivity is node-critical.** It holds on `𝒩` exactly when RH holds and `𝒩`
contains every prime power. -/
theorem zeroPoleBlindPositiveOn_iff {𝒩 : Set ℕ} :
    ZeroPoleBlindPositiveOn 𝒩 ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → ArithmeticFunction.vonMangoldt n ≠ 0 → n ∈ 𝒩 := by
  constructor
  · intro hZ
    refine ⟨riemannHypothesis_iff_zeroPoleBlindPositive.mpr fun c hc hv hp =>
      hZ c hc (fun j _ => by rw [hv]; rfl) hp, fun n hn hΛ => ?_⟩
    obtain ⟨lam, hW, h0⟩ := exists_weilPositiveFull_of_zeroPoleBlindPositiveOn hZ
    by_contra hn𝒩
    exact hΛ (by rw [← RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW n hn,
      h0 n hn hn𝒩])
  · intro h c hc hb _
    have hP := primeBlindPositiveOn_iff.mpr h c hc fun n hn hn𝒩 => by
      rw [← linearCombination_logVector_apply c ⟨n, hn⟩]
      exact hb ⟨n, hn⟩ hn𝒩
    rwa [sum_weilArchRe_eq, ← nodeArchEnergy_eq] at hP

/-- The pole constraint is invisible to node criticality: zero-pole positivity and pole-retained
prime-blind positivity hold on the same node sets. -/
theorem zeroPoleBlindPositiveOn_iff_primeBlindPositiveOn {𝒩 : Set ℕ} :
    ZeroPoleBlindPositiveOn 𝒩 ↔ PrimeBlindPositiveOn 𝒩 := by
  rw [zeroPoleBlindPositiveOn_iff, primeBlindPositiveOn_iff]

/-- **The prime powers carry the full criterion.** -/
theorem riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers :
    RiemannHypothesis ↔ ZeroPoleBlindPositiveOn {n | IsPrimePow n} := by
  rw [zeroPoleBlindPositiveOn_iff]
  exact ⟨fun h => ⟨h, fun n _ hn => ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn⟩,
    fun h => h.1⟩

/-- **Deleting one prime power falsifies zero-pole positivity**, on every node set. -/
theorem not_zeroPoleBlindPositiveOn_diff_of_isPrimePow (𝒩 : Set ℕ) {m : ℕ} (hm : IsPrimePow m) :
    ¬ ZeroPoleBlindPositiveOn (𝒩 \ {m}) := fun h =>
  ((zeroPoleBlindPositiveOn_iff.mp h).2 m hm.two_le
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hm)).2 rfl

/-- **Deleting an integer that is not a prime power changes nothing.** -/
theorem zeroPoleBlindPositiveOn_diff_iff_of_not_isPrimePow (𝒩 : Set ℕ) {n : ℕ}
    (hn : ¬ IsPrimePow n) : ZeroPoleBlindPositiveOn (𝒩 \ {n}) ↔ ZeroPoleBlindPositiveOn 𝒩 := by
  rw [zeroPoleBlindPositiveOn_iff, zeroPoleBlindPositiveOn_iff]
  refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk => imp_congr_right
    fun hΛ => ⟨fun h => h.1, fun h => ⟨h, fun hkn => ?_⟩⟩
  rw [Set.mem_singleton_iff] at hkn
  exact hn (hkn ▸ ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)

/-- `log 4` is indispensable. -/
theorem not_zeroPoleBlindPositiveOn_diff_four (𝒩 : Set ℕ) : ¬ ZeroPoleBlindPositiveOn (𝒩 \ {4}) :=
  not_zeroPoleBlindPositiveOn_diff_of_isPrimePow 𝒩 (by decide)

/-- `log 6` is redundant. -/
theorem zeroPoleBlindPositiveOn_diff_six_iff (𝒩 : Set ℕ) :
    ZeroPoleBlindPositiveOn (𝒩 \ {6}) ↔ ZeroPoleBlindPositiveOn 𝒩 :=
  zeroPoleBlindPositiveOn_diff_iff_of_not_isPrimePow 𝒩 (by decide)

/-- **The primes alone never suffice**, although they lie far above square-root density: the
prime squares are missing. -/
theorem not_zeroPoleBlindPositiveOn_primes : ¬ ZeroPoleBlindPositiveOn {n | n.Prime} := by
  intro h
  have h4 := (zeroPoleBlindPositiveOn_iff.mp h).2 4 (by norm_num)
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr (by decide))
  exact (by decide : ¬ (4 : ℕ).Prime) h4

end

end GaloisForLFunctions.BiScaleUncertainty
