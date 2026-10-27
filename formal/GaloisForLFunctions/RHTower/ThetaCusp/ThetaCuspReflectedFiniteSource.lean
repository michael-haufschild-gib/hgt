import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspIntegerRelativeTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxSourceWeld

/-!
# Reflected finite theta sources and their entire amplitudes

Reflection of a nonempty integer prefix gives a positive continuous even
source. Domination by the completed theta source proves every exponential
moment directly, so its bilateral amplitude is entire with literal first
moment derivative despite the physical cusp at the origin.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

lemma reflectedFiniteThetaSource_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ reflectedFiniteThetaSource N x := by
  unfold reflectedFiniteThetaSource thetaCuspFiniteShellPrefix
  exact Finset.sum_nonneg fun m _ => thetaCuspSourceTerm_nonneg_on_halfLine (abs_nonneg x) m

lemma reflectedFiniteThetaSource_le_full (N : ℕ) (x : ℝ) :
    reflectedFiniteThetaSource N x ≤ thetaCuspFullSource x :=
  sub_nonneg.mp (reflectedFiniteThetaSource_relative_tail N x).1

lemma continuous_reflectedFiniteThetaSource (N : ℕ) :
    Continuous (reflectedFiniteThetaSource N) := by
  unfold reflectedFiniteThetaSource thetaCuspFiniteShellPrefix
  apply continuous_finsetSum
  intro m hm
  unfold thetaCuspSourceTerm thetaCuspSeed
  fun_prop

lemma reflectedFiniteThetaSource_even (N : ℕ) (x : ℝ) :
    reflectedFiniteThetaSource N (-x) = reflectedFiniteThetaSource N x := by
  simp only [reflectedFiniteThetaSource, abs_neg]

lemma reflectedFiniteThetaSource_pos {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    0 < reflectedFiniteThetaSource N x := by
  have hfirst : 0 < thetaCuspSourceTerm |x| 1 := by
    rcases (abs_nonneg x).eq_or_lt with hx | hx
    · rw [← hx]
      exact thetaCuspSourceTerm_zero_pos (by norm_num)
    · exact thetaCuspSourceTerm_one_pos_of_pos hx
  refine hfirst.trans_le ?_
  unfold reflectedFiniteThetaSource thetaCuspFiniteShellPrefix
  exact Finset.single_le_sum
    (fun m _ => thetaCuspSourceTerm_nonneg_on_halfLine (abs_nonneg x) m)
    (Finset.mem_range.mpr (by omega))

/-- A nonempty finite reflected prefix satisfies every bilateral source condition. -/
def finiteThetaTiltSource (N : ℕ) : ThetaSource where
  k := reflectedFiniteThetaSource (N + 1)
  pos := reflectedFiniteThetaSource_pos (by omega)
  even' := reflectedFiniteThetaSource_even (N + 1)
  cont := continuous_reflectedFiniteThetaSource (N + 1)
  decay M := ⟨thetaCuspTiltDecayConstant M, thetaCuspTiltDecayConstant_pos M,
    fun x => (reflectedFiniteThetaSource_le_full (N + 1) x).trans
      (thetaCuspFullSource_le_tiltDecayConstant M x)⟩

/-- Literal entire amplitude of the reflected finite arithmetic source. -/
def finiteThetaAmplitude (N : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (reflectedFiniteThetaSource (N + 1) x : ℂ) *
    Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))

/-- Literal first source moment for the same finite integer prefix. -/
def finiteThetaFirstMoment (N : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * (reflectedFiniteThetaSource (N + 1) x : ℂ) *
    Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))

lemma finiteThetaAmplitude_eq_bilateral (N : ℕ) (z : ℂ) :
    finiteThetaAmplitude N z = bilateralLaplace (finiteThetaTiltSource N) ((1 / 2 : ℂ) - z) := rfl

/-- Finite arithmetic amplitudes are entire; their derivatives retain the exact first moment. -/
theorem hasDerivAt_finiteThetaAmplitude (N : ℕ) (z : ℂ) :
    HasDerivAt (finiteThetaAmplitude N) (-finiteThetaFirstMoment N z) z := by
  have h := (hasDerivAt_bilateralLaplace (finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)).comp z
    ((hasDerivAt_id z).const_sub (1 / 2 : ℂ))
  convert h using 1 <;> first
    | rfl
    | simp only [bilateralLaplaceDeriv, finiteThetaFirstMoment, finiteThetaTiltSource,
        mul_neg, mul_one]

theorem differentiable_finiteThetaAmplitude (N : ℕ) : Differentiable ℂ (finiteThetaAmplitude N) :=
  fun z => (hasDerivAt_finiteThetaAmplitude N z).differentiableAt

theorem deriv_finiteThetaAmplitude (N : ℕ) (z : ℂ) :
    deriv (finiteThetaAmplitude N) z = -finiteThetaFirstMoment N z :=
  (hasDerivAt_finiteThetaAmplitude N z).deriv

end RHTower

#print axioms RHTower.hasDerivAt_finiteThetaAmplitude
