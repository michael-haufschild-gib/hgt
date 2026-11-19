import GaloisForLFunctions.FamilyContinuationTheory.ChordBoundsForMellinReadingsOnTheSecondLine
import GaloisForLFunctions.FamilyContinuationTheory.TheCubicProbeIsACoupledTowerReachingThreeFifths
import GaloisForLFunctions.RHTower.GaussianWindowMomentRescaling

/-!
# Reading the actual cubic Hecke probe on a sparse mesh

Linear interpolation between n^(3/2) and (n+1)^(3/2) costs O(Z^(2/3)).
Consequently every improvement above the two-thirds boundary can be tested
on this mesh. The interval error comes from the finite second moment of
the Gaussian on the inversion line.
-/

noncomputable section
open Complex Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein EisensteinNorm
local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-- The physical receiver in the zero-centered Gaussian cubic probe. -/
def cubicRaySignal (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O)) :=
  signal (fun s : ℂ => Complex.exp (s^2)*probeCorrection 𝔪 η S s/heckeLFunction 𝔪 η s) 2

private theorem cubic_chords (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {a h q : ℝ}, 0 < a → 0 ≤ h → 0 ≤ q → q ≤ 1 →
      ‖cubicRaySignal 𝔪 η S (a+q*h) - (1-q:ℝ) • cubicRaySignal 𝔪 η S a -
        q • cubicRaySignal 𝔪 η S (a+h)‖ ≤ B*q*(1-q)*h^2 := by
  let G := fun s : ℂ => Complex.exp (s^2)*continuedProbeCorrection 𝔪 η S s/heckeLFunction 𝔪 η s
  have eq : cubicRaySignal 𝔪 η S = signal G 2 := by
    simpa only [cubicRaySignal,G,Complex.ofReal_zero,sub_zero] using
      signal_probeCorrection_eq_continuedProbeCorrection 𝔪 η S hS 0
  rw [eq]
  have gcont : Continuous fun y => G (linePoint y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let s := linePoint y
    have hs : 1 < s.re := by change 1 < (linePoint y).re; rw [linePoint_re]; norm_num
    have hhalf : s ∈ {z : ℂ | 1/2 < z.re} := (by norm_num : (1:ℝ)/2 < 1).trans hs
    have d := (differentiableOn_continuedProbeCorrection 𝔪 η S).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hhalf)
    have g : DifferentiableAt ℂ G s := ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (z^2)) s).mul d).div
      (differentiableAt_heckeLFunction 𝔪 η (ne_one_of_one_lt_re hs))
      (heckeLFunction_ne_zero_of_one_lt_re 𝔪 η hs)
    exact g.continuousAt.comp continuous_linePoint.continuousAt
  apply mellin_signal_chord_bound gcont
  let L := Real.exp (-(3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K),
    ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖))
  have lp : 0 < L := Real.exp_pos _
  obtain ⟨M,hM⟩ := exists_norm_continuedProbeCorrection_le 𝔪 η S
  let C := Real.exp 4*|M|/L
  have c0 : 0 ≤ C := div_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) lp.le
  have gauss (y : ℝ) : ‖G (linePoint y)‖ ≤ C*Real.exp (-y^2) := by
    let s := linePoint y
    have re : s.re=2 := linePoint_re y
    have im : s.im= -y := linePoint_im y
    have lower : L ≤ ‖heckeLFunction 𝔪 η s‖ := by
      rw [heckeLFunction_eq_heckeL 𝔪 η (by rw [re]; norm_num)]
      exact exp_neg_le_norm_heckeL 𝔪 η re.ge
    have xe : (s^2).re=4+(-y^2) := by rw [sq,mul_re,re,im]; ring
    change ‖Complex.exp (s^2)*continuedProbeCorrection 𝔪 η S s/heckeLFunction 𝔪 η s‖ ≤ _
    rw [norm_div,norm_mul,norm_exp,xe,Real.exp_add]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ((hM s re.ge).trans (le_abs_self _))
      (by positivity)) (norm_nonneg _)).trans
    apply (div_le_div_of_nonneg_left (by positivity) lp lower).trans_eq
    dsimp only [C]; ring
  have gauss₀ : Integrable (fun y : ℝ => Real.exp (-y^2)) := by
    simpa using _root_.RHTower.integrable_pow_mul_exp_neg_sq 0
  have gi := ((gauss₀.const_mul 4).add (_root_.RHTower.integrable_pow_mul_exp_neg_sq 2)).const_mul C
  apply gi.mono' (by fun_prop)
  intro y
  apply Eventually.of_forall
  -- The second derivative has at most quadratic frequency growth.
  all_goals first | assumption | skip
