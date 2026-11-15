import GaloisForLFunctions.ZeroForcingCalculus.ExpandingForcingLawsRulersAndTheRiemannHypothesis
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheShortMoebiusMonomialsPayExactlyHalf

/-!
# The three lines of frames

A frame `(c, k)` acts on exponents by the lever `b ↦ (c + b)/k` (`pairingStep`). Three lines of
frames organize the tensor-power route:

* the **Deligne line** `c = (k − 1)/2` (`deligneLever`): the frame of the `k`-th tensor or Adams
  power, which moves a zero at `β` to `kβ − (k − 1)/2`;
* the **sign line** `c = k/2` (`signLever`): short Möbius-signed Gauss monomials, priced by
  Stickelberger (`Stickelberger.stickelbergerPrice_eq_half_mul`);
* the **completion line** `c = 2k/3 − 1`: Gauss pairings completed factor by factor
  (`FamilyContinuationTheory.two_thirds_mul_period_sub_one_le_pairingC`).

Price ledger and assembly:

* **The half unit** (`signPrice_sub_delignePrice`): the two prices differ by exactly `½` at every
  period; one step with top bound `1` gives `½ + 1/(2k)` and `½ + 1/k` (`deligneLever_one`,
  `signLever_one`); the completion line gives `2/3` at every period (`completionStep_one`).
* **One Deligne frame excludes everything right of `½`** (`excluded_deligneLever`), so a single
  valid Deligne lever proves RH (`riemannHypothesis_of_deligneLever`).
* **The sign line needs every large period** (`excluded_signLever`): one sign frame excludes only
  `(k/(2(k − 1)), ∞)`; valid sign levers at all large periods prove RH
  (`riemannHypothesis_of_signLevers`): the sign is free in the limit.
* **The completion line closes at `2/3`** (`completionCentre_lt_two_thirds`,
  `completionCentre_strictMono`, `tendsto_completionCentre`): its tower centres
  `2/3 − 1/(3(k − 1))` increase to `2/3`; beyond `k = 6` completion, not the sign, is the
  obstruction, and the Gauss levers stop at `3/5` (`wall_gaussLevers`).
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

open ExponentDynamicsOfTheCriticalStrip FamilyContinuationTheory

/-- The Deligne lever of period `k`: `b ↦ ((k − 1)/2 + b)/k`. -/
def deligneLever (k : ℝ) : ℝ → ℝ := pairingStep ((k - 1) / 2) k

/-- The sign lever of period `k`: `b ↦ (k/2 + b)/k`. -/
def signLever (k : ℝ) : ℝ → ℝ := pairingStep (k / 2) k

/-- The tower centre `(2k/3 − 1)/(k − 1)` of the completion line. -/
def completionCentre (k : ℝ) : ℝ := (2 / 3 * k - 1) / (k - 1)

/-- **The half unit.** The sign line lies half a unit above the Deligne line at every period. -/
theorem signPrice_sub_delignePrice (k : ℝ) : k / 2 - (k - 1) / 2 = 1 / 2 := by ring

theorem deligneLever_one {k : ℝ} (hk : 0 < k) : deligneLever k 1 = 1 / 2 + 1 / (2 * k) := by
  rw [deligneLever, pairingStep]
  field_simp
  ring

theorem signLever_one {k : ℝ} (hk : 0 < k) : signLever k 1 = 1 / 2 + 1 / k := by
  rw [signLever, pairingStep]
  field_simp
  ring

theorem completionStep_one {k : ℝ} (hk : 0 < k) : pairingStep (2 / 3 * k - 1) k 1 = 2 / 3 := by
  rw [pairingStep]
  field_simp
  ring

/-- **One Deligne frame excludes every exponent right of `½`.** -/
theorem excluded_deligneLever {k : ℝ} (hk : 1 < k) : excluded (deligneLever k) = Set.Ioi (1 / 2) := by
  ext b
  simp only [excluded, Set.mem_setOf_eq, Set.mem_Ioi, deligneLever, pairingStep]
  rw [div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- One sign frame excludes only the exponents right of its centre `k/(2(k − 1))`. -/
theorem excluded_signLever {k : ℝ} (hk : 1 < k) :
    excluded (signLever k) = Set.Ioi (k / (2 * (k - 1))) := by
  ext b
  simp only [excluded, Set.mem_setOf_eq, Set.mem_Ioi, signLever, pairingStep]
  rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- **A single valid Deligne lever proves RH.** -/
theorem riemannHypothesis_of_deligneLever {k : ℝ} (hk : 1 < k)
    (h : IsLever RHTower.zetaZeroAbscissa (deligneLever k)) : RiemannHypothesis := by
  refine (ZeroForcingCalculus.riemannHypothesis_of_covering_levers (𝒯 := {deligneLever k})
    (fun T hT => by rw [Set.mem_singleton_iff.mp hT]; exact h) ?_).2.2
  intro b hb
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_left]
  rw [excluded_deligneLever hk]
  exact hb.1

/-- **Valid sign levers at all large periods prove RH.** -/
theorem riemannHypothesis_of_signLevers {K : ℕ}
    (h : ∀ k : ℕ, K ≤ k → 2 ≤ k → IsLever RHTower.zetaZeroAbscissa (signLever k)) :
    RiemannHypothesis := by
  refine (ZeroForcingCalculus.riemannHypothesis_of_covering_levers
    (𝒯 := {T | ∃ k : ℕ, K ≤ k ∧ 2 ≤ k ∧ T = signLever k})
    (fun T ⟨k, hK, h2, hT⟩ => hT ▸ h k hK h2) ?_).2.2
  intro b hb
  have hb1 : 1 / 2 < b := hb.1
  -- a period with centre k/(2(k − 1)) below b
  obtain ⟨k, hk⟩ := exists_nat_gt (max (max K 2) (b / (2 * b - 1)))
  have hkK : (K : ℝ) < k := lt_of_le_of_lt (le_trans (by exact_mod_cast le_max_left K 2)
    (le_max_left _ _)) hk
  have hk2 : (2 : ℝ) < k := lt_of_le_of_lt (le_trans (by exact_mod_cast le_max_right K 2)
    (le_max_left _ _)) hk
  have hkb : b / (2 * b - 1) < k := lt_of_le_of_lt (le_max_right _ _) hk
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨signLever k, ⟨k, by exact_mod_cast hkK.le, by exact_mod_cast hk2.le, rfl⟩, ?_⟩
  rw [excluded_signLever (by linarith)]
  show k / (2 * (k - 1)) < b
  rw [div_lt_iff₀ (by linarith)]
  rw [div_lt_iff₀ (by linarith)] at hkb
  nlinarith

/-- The completion centres lie below `2/3`. -/
theorem completionCentre_lt_two_thirds {k : ℝ} (hk : 1 < k) : completionCentre k < 2 / 3 := by
  rw [completionCentre, div_lt_iff₀ (by linarith)]
  linarith

/-- `(2k/3 − 1)/(k − 1) = 2/3 − 1/(3(k − 1))`. -/
theorem completionCentre_eq {k : ℝ} (hk : 1 < k) :
    completionCentre k = 2 / 3 - 1 / (3 * (k - 1)) := by
  rw [completionCentre]
  have : k - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The completion centres strictly increase with the period. -/
theorem completionCentre_strictMono : StrictMonoOn completionCentre (Set.Ioi 1) := by
  intro a ha b hb hab
  rw [completionCentre_eq ha, completionCentre_eq hb]
  have ha1 : 0 < a - 1 := by simp at ha; linarith
  have hb1 : 0 < b - 1 := by simp at hb; linarith
  have : 1 / (3 * (b - 1)) < 1 / (3 * (a - 1)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- The completion centres tend to `2/3`: factor-by-factor completion gets worse with the period. -/
theorem tendsto_completionCentre : Tendsto completionCentre atTop (𝓝 (2 / 3)) := by
  have h : Tendsto (fun k : ℝ => 2 / 3 - 1 / (3 * (k - 1))) atTop (𝓝 (2 / 3 - 0)) := by
    refine tendsto_const_nhds.sub ?_
    refine tendsto_const_nhds.div_atTop ?_
    exact Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with k hk
  exact (completionCentre_eq hk).symm

end GaloisForLFunctions.TensorPowerProgramme
