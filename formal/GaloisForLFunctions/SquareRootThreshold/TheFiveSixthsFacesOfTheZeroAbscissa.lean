import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.JointOscillationsAtTheLastHalfOfThePrimeRow
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.SuperpolynomialMobiusOrder
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheGreatestMertensMassOnSparseSamples
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfRateUnderTheRiemannHypothesis
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.RHTower.XiWardGlobalCapAndFiniteHeadArithmetic

/-!
# The five-sixths faces of the zero abscissa

Five observables read the zero abscissa `Θ` exactly. For every `c ∈ [½, 1)`:

* **PSM.** `Θ ≤ c` iff one sign of the halving increment
  `E(H) − E(⌊H/2⌋)`, `E = θ − id`, is `≤ C H^b` eventually for every `b > c`.
* **ECS.** `Θ ≤ c` iff the terminal joint height is `≤ K H^e` eventually for every
  `e > 2c − 1`.
* **WD.** `Θ ≤ c` iff, along any schedule `N, T → ∞` with `log T = o(log N)`, the
  logarithmic order of the long Möbius energy is eventually below every `e > 2c − 1`.
* **MC.** `Θ ≤ c` iff the Mertens mass of every finite sample `S` is
  `≤ C (|S| + 1)^(c + ε)`.
* **AAD.** `Θ ≤ c` iff integer floor producers reach every rate `K^{−a}`, `0 < a < 1 − c`.

At `c = 5/6` these are the faces of `Θ ≤ 5/6` (`fiveSixths_faces`). The corpus strip
`Θ ≤ 20999/24000` turns the forward direction of each face into an unconditional theorem
(`unconditional_faces`).
-/

open Filter Finset Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower GaloisForLFunctions.ArithmeticPowerMass
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The supremum of the real parts of the zero copies and the zero abscissa bound the same
half-planes right of the critical line. -/
theorem zeroReSup_le_iff_zetaZeroAbscissa_le {c : ℝ} (hc : 1/2 ≤ c) :
    zeroReSup ≤ c ↔ zetaZeroAbscissa ≤ c := by
  have hw : zetaZeroWidth ≤ c - 1/2 ↔ zetaZeroAbscissa ≤ c := by
    rw [zetaZeroWidth_le_iff_zetaZeroAbscissa_le (by linarith)]
    constructor <;> intro h <;> linarith
  rw [← hw, _root_.RHTower.zetaZeroWidth_le_iff_forall_xiZeroCopy_re_le (by linarith),
    show 1/2 + (c - 1/2) = c by ring]
  exact ⟨fun h q => (re_le_zeroReSup q).trans h, _root_.RHTower.zeroReSup_le_of_forall_re_le⟩

/-- Zero-freeness right of `c` is the abscissa bound `Θ ≤ c`. -/
theorem zeroFree_iff_zetaZeroAbscissa_le {c : ℝ} :
    (∀ s : ℂ, c < s.re → riemannZeta s ≠ 0) ↔ zetaZeroAbscissa ≤ c := by
  refine ⟨fun h => ?_, fun h s hs => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt (h.trans_lt hs)⟩
  by_contra! hc
  obtain ⟨ρ, hρ, hr⟩ := exists_zetaZero_lt_re hc
  exact h ρ hr hρ

/-- **PSM face.** One fixed sign of the halving increment reads the abscissa. -/
theorem zetaZeroAbscissa_le_iff_terminalOddHalf_le {c s : ℝ} (hc : 1/2 ≤ c) (hs : s = 1 ∨ s = -1) :
    zetaZeroAbscissa ≤ c ↔ ∀ b : ℝ, c < b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ H : ℕ in atTop, s * terminalOddHalf H ≤ C * (H:ℝ)^b := by
  rw [← zeroReSup_le_iff_zetaZeroAbscissa_le hc]
  exact terminal_odd_half_width_iff c hs

/-- **ECS face.** The terminal joint height reads `2Θ − 1`. -/
theorem zetaZeroAbscissa_le_iff_terminalJointHeight_le {c s : ℝ} (hc : 1/2 ≤ c)
    (hs : s = 1 ∨ s = -1) :
    zetaZeroAbscissa ≤ c ↔ ∀ e : ℝ, 2*c - 1 < e → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ H : ℕ in atTop, terminalJointHeight s H ≤ K * (H:ℝ)^e := by
  rw [← zeroReSup_le_iff_zetaZeroAbscissa_le hc, terminal_joint_width_iff hc hs]
  constructor
  · intro h e he
    simpa only [show 2*((1+e)/2) - 1 = e by ring] using h ((1+e)/2) (by linarith)
  · exact fun h b hb => h (2*b - 1) (by linarith)

/-- **WD face.** Along every superpolynomial schedule, the logarithmic order of the long Möbius
energy reads `2Θ − 1`. -/
theorem zetaZeroAbscissa_le_iff_sectionEnergy_order_lt {ι : Type*} {l : Filter ι} [l.NeBot]
    {N : ι → ℕ} {T : ι → ℝ} (hN : Tendsto N l atTop) (hT : Tendsto T l atTop)
    (hlog : Tendsto (fun i => Real.log (T i) / Real.log (N i)) l (𝓝 0)) {c : ℝ} :
    zetaZeroAbscissa ≤ c ↔ ∀ e : ℝ, 2*c - 1 < e → ∀ᶠ i in l,
      Real.log (1 + sectionHeightEnergy (N i) 1 (T i)) / Real.log (N i) < e := by
  have h := superpolynomial_section_energy_order hN hT hlog
  have hw := zetaZeroWidth_eq_zetaZeroAbscissa_sub_half
  constructor
  · exact fun hΘ e he => h.eventually (eventually_lt_nhds (by linarith))
  · intro hall
    by_contra! hΘ
    obtain ⟨e, h1, h2⟩ := exists_between (show 2*c - 1 < 2*zetaZeroWidth by linarith)
    obtain ⟨i, hi, hi'⟩ := ((hall e h1).and (h.eventually (eventually_gt_nhds h2))).exists
    exact lt_asymm hi hi'

/-- **MC face.** The cardinality exponent of Mertens masses on arbitrary samples reads `Θ`. -/
theorem zetaZeroAbscissa_le_iff_mertens_sample_bound {c : ℝ} (hc : 1/2 ≤ c) :
    zetaZeroAbscissa ≤ c ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      ∑ k ∈ S, reciprocalMertensWeight k ≤ C * ((S.card:ℝ) + 1)^(c + ε) := by
  constructor
  · exact fun h ε hε => sparse_mertens_mass_bound (by linarith)
  · intro h
    by_contra! hw
    obtain ⟨b, hb, hb'⟩ := exists_between hw
    obtain ⟨C, _, hC⟩ := h (b - c) (by linarith)
    obtain ⟨m, hm⟩ := (eventually_large_mertens_abel_mass (by linarith) hb' C).exists
    have hz := hC (Icc 1 m)
    simp only [show c + (b - c) = b by ring, Nat.card_Icc, Nat.add_sub_cancel] at hz
    rw [mertens_abel_mass_eq] at hm
    exact hm.not_ge hz

/-- **AAD face.** Integer floor producers reach exactly the rates `K^{−a}`, `a < 1 − Θ`. -/
theorem zetaZeroAbscissa_le_iff_forall_hasRate {c : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) :
    zetaZeroAbscissa ≤ c ↔ ∀ a : ℝ, 0 < a → a < 1 - c → HasRate fun K => (K:ℝ)^(-a) := by
  rw [← zeroFree_iff_zetaZeroAbscissa_le]
  exact zeroFree_iff_forall_hasRate hc hc1

/-- **The faces of `Θ ≤ 5/6`.** One sign of the halving increment below `H^(5/6+ε)`, the joint
height below `H^(2/3+ε)`, Mertens sample exponent `5/6`, floor rates `a < 1/6`. -/
theorem fiveSixths_faces {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (zetaZeroAbscissa ≤ 5/6 ↔ ∀ b : ℝ, 5/6 < b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ H : ℕ in atTop, s * terminalOddHalf H ≤ C * (H:ℝ)^b) ∧
    (zetaZeroAbscissa ≤ 5/6 ↔ ∀ e : ℝ, 2/3 < e → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ H : ℕ in atTop, terminalJointHeight s H ≤ K * (H:ℝ)^e) ∧
    (zetaZeroAbscissa ≤ 5/6 ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      ∑ k ∈ S, reciprocalMertensWeight k ≤ C * ((S.card:ℝ) + 1)^(5/6 + ε)) ∧
    (zetaZeroAbscissa ≤ 5/6 ↔ ∀ a : ℝ, 0 < a → a < 1/6 → HasRate fun K => (K:ℝ)^(-a)) := by
  have hc : (1:ℝ)/2 ≤ 5/6 := by norm_num
  refine ⟨zetaZeroAbscissa_le_iff_terminalOddHalf_le hc hs, ?_,
    zetaZeroAbscissa_le_iff_mertens_sample_bound hc, ?_⟩
  · rw [zetaZeroAbscissa_le_iff_terminalJointHeight_le hc hs]; norm_num
  · rw [zetaZeroAbscissa_le_iff_forall_hasRate hc (by norm_num)]; norm_num

/-- **The WD face of `Θ ≤ 5/6`:** log-exponent `2/3` along every superpolynomial schedule. -/
theorem fiveSixths_wd_face {ι : Type*} {l : Filter ι} [l.NeBot]
    {N : ι → ℕ} {T : ι → ℝ} (hN : Tendsto N l atTop) (hT : Tendsto T l atTop)
    (hlog : Tendsto (fun i => Real.log (T i) / Real.log (N i)) l (𝓝 0)) :
    zetaZeroAbscissa ≤ 5/6 ↔ ∀ e : ℝ, 2/3 < e → ∀ᶠ i in l,
      Real.log (1 + sectionHeightEnergy (N i) 1 (T i)) / Real.log (N i) < e := by
  rw [zetaZeroAbscissa_le_iff_sectionEnergy_order_lt hN hT hlog]; norm_num

/-- **Unconditional faces.** The strip `Θ ≤ 20999/24000` gives: both signs of the halving
increment below `H^b` for `b > 20999/24000`; the joint height below `H^e` for
`e > 8999/12000`; Mertens sample exponent `20999/24000`; every floor rate `a < 3001/24000`. -/
theorem unconditional_faces :
    (∀ b : ℝ, 20999/24000 < b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ H : ℕ in atTop, |terminalOddHalf H| ≤ C * (H:ℝ)^b) ∧
    (∀ s : ℝ, s = 1 ∨ s = -1 → ∀ e : ℝ, 8999/12000 < e → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ H : ℕ in atTop, terminalJointHeight s H ≤ K * (H:ℝ)^e) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      ∑ k ∈ S, reciprocalMertensWeight k ≤ C * ((S.card:ℝ) + 1)^(20999/24000 + ε)) ∧
    (∀ a : ℝ, 0 < a → a < 3001/24000 → HasRate fun K => (K:ℝ)^(-a)) := by
  have hΘ := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
  have hc : (1:ℝ)/2 ≤ 20999/24000 := by norm_num
  have hR := (zeroReSup_le_iff_zetaZeroAbscissa_le hc).mpr hΘ
  refine ⟨fun b hb => terminal_odd_half_above_abscissa (hR.trans_lt hb), fun s hs e he => ?_,
    (zetaZeroAbscissa_le_iff_mertens_sample_bound hc).mp hΘ, fun a ha ha' => ?_⟩
  · exact (zetaZeroAbscissa_le_iff_terminalJointHeight_le hc hs).mp hΘ e (by linarith)
  · exact (zetaZeroAbscissa_le_iff_forall_hasRate hc (by norm_num)).mp hΘ a ha (by linarith)

/-- **Unconditional WD face:** the long Möbius energy has log-exponent at most `8999/12000`. -/
theorem unconditional_wd_face {ι : Type*} {l : Filter ι} [l.NeBot]
    {N : ι → ℕ} {T : ι → ℝ} (hN : Tendsto N l atTop) (hT : Tendsto T l atTop)
    (hlog : Tendsto (fun i => Real.log (T i) / Real.log (N i)) l (𝓝 0)) {e : ℝ}
    (he : 8999/12000 < e) : ∀ᶠ i in l,
      Real.log (1 + sectionHeightEnergy (N i) 1 (T i)) / Real.log (N i) < e :=
  (zetaZeroAbscissa_le_iff_sectionEnergy_order_lt hN hT hlog).mp
    ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths e (by linarith)

#print axioms fiveSixths_faces
#print axioms fiveSixths_wd_face
#print axioms unconditional_faces
#print axioms unconditional_wd_face

end GaloisForLFunctions.SquareRootThreshold
