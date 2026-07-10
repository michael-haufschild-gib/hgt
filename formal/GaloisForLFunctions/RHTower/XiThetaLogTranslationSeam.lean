import GaloisForLFunctions.RHTower.XiThetaSourceSeam

/-!
# Log-translation coordinates and the moving theta boundary

Every square-rate heat atom becomes a translate of one mother profile after x = exp u. The
translation distance is 2 log m and the scalar weight is m to the power minus one half.

The positive-half truncation needed by the Sonin support interface does not commute with these
translations. The commutator is exact: it is the profile restricted to the interval swept across
zero. For the m-th square atom that interval has length 2 log m. Thus coefficient diagonalization
in the full logarithmic coordinate acquires an index-dependent boundary charge after passing to the
one-sided source.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- The common logarithmic heat profile underlying every positive square-rate theta atom. -/
def thetaLogMother (u : ℝ) : ℝ :=
  2 * Real.exp (u / 4) * Real.exp (-π * Real.exp u)

/-- The logarithmic heat atom with square rate pi times m squared. -/
def thetaSquareLogAtom (m : ℕ) (u : ℝ) : ℝ :=
  2 * Real.exp (u / 4) *
    Real.exp (-π * (m : ℝ) ^ 2 * Real.exp u)

/-- Square-rate atoms are weighted translates of a single logarithmic mother profile. -/
theorem thetaSquareLogAtom_eq_shifted_mother {m : ℕ} (hm : 0 < m) (u : ℝ) :
    thetaSquareLogAtom m u =
      (m : ℝ) ^ (-(1 : ℝ) / 2) * thetaLogMother (u + 2 * Real.log m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [thetaSquareLogAtom, thetaLogMother, Real.rpow_def_of_pos hmR]
  have hlog : Real.exp (Real.log (m : ℝ)) = m := Real.exp_log hmR
  rw [Real.exp_add u (2 * Real.log (m : ℝ))]
  rw [show (u + 2 * Real.log (m : ℝ)) / 4 =
      u / 4 + Real.log (m : ℝ) / 2 by ring]
  rw [Real.exp_add]
  rw [show Real.exp (2 * Real.log (m : ℝ)) = (m : ℝ) ^ 2 by
    rw [show 2 * Real.log (m : ℝ) =
      Real.log (m : ℝ) + Real.log (m : ℝ) by ring, Real.exp_add, hlog]
    ring]
  have hcancel : Real.exp (Real.log (m : ℝ) * (-(1 : ℝ) / 2)) *
      Real.exp (Real.log (m : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  have hX : Real.exp (-π * (Real.exp u * (m : ℝ) ^ 2)) =
      Real.exp (-π * (m : ℝ) ^ 2 * Real.exp u) := by
    congr 1
    ring
  rw [hX]
  symm
  calc
    Real.exp (Real.log (m : ℝ) * (-(1 : ℝ) / 2)) *
          (2 * (Real.exp (u / 4) * Real.exp (Real.log (m : ℝ) / 2)) *
            Real.exp (-π * (m : ℝ) ^ 2 * Real.exp u)) =
        2 * Real.exp (u / 4) *
          (Real.exp (Real.log (m : ℝ) * (-(1 : ℝ) / 2)) *
            Real.exp (Real.log (m : ℝ) / 2)) *
          Real.exp (-π * (m : ℝ) ^ 2 * Real.exp u) := by ring
    _ = 2 * Real.exp (u / 4) * Real.exp (-π * (m : ℝ) ^ 2 * Real.exp u) := by
      rw [hcancel]
      ring

/-- Restriction to the strict positive logarithmic half-line. -/
def positiveLogTruncation {E : Type*} [Zero E] (f : ℝ → E) (u : ℝ) : E :=
  (Ioi (0 : ℝ)).indicator f u

/-- The interval swept across the boundary when a profile is translated forward by a. -/
def forwardTranslationBoundary {E : Type*} [Zero E]
    (a : ℝ) (f : ℝ → E) (u : ℝ) : E :=
  (Ioc (-a) 0).indicator (fun v => f (v + a)) u

/-- Exact half-line/translation seam. Positive truncation does not commute with a forward
translation. The entire commutator is the profile restricted to the swept interval. -/
theorem positiveLogTruncation_translate_add_boundary
    {E : Type*} [AddCommMonoid E] (f : ℝ → E) {a : ℝ} (ha : 0 < a) (u : ℝ) :
    positiveLogTruncation (fun v => f (v + a)) u +
        forwardTranslationBoundary a f u =
      positiveLogTruncation f (u + a) := by
  by_cases hu : 0 < u
  · have hua : 0 < u + a := by linarith
    have hub : u ∉ Ioc (-a) 0 := fun h => (not_lt_of_ge h.2) hu
    simp [positiveLogTruncation, forwardTranslationBoundary, hu, hua, hub]
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    by_cases hshift : -a < u
    · have hua : 0 < u + a := by linarith
      have hub : u ∈ Ioc (-a) 0 := ⟨hshift, hu0⟩
      simp [positiveLogTruncation, forwardTranslationBoundary, hu, hua, hub]
    · have hua : u + a ≤ 0 := by linarith
      have hub : u ∉ Ioc (-a) 0 := fun h => hshift h.1
      have huanot : ¬ 0 < u + a := not_lt_of_ge hua
      simp [positiveLogTruncation, forwardTranslationBoundary, hu, huanot, hub]

/-- For every square index m greater than one, the moving boundary has length 2 log m. -/
theorem squareTranslationBoundary_length {m : ℕ} (hm : 1 < m) :
    |(0 : ℝ) - (-(2 * Real.log m))| = 2 * Real.log m := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos hmR
  rw [sub_neg_eq_add, zero_add, abs_of_pos]
  linarith

/-- Combining the square-atom shift law with the truncation commutator exposes the exact
index-dependent boundary charge. -/
theorem positiveThetaSquareLogAtom_translation_seam {m : ℕ} (hm : 1 < m) (u : ℝ) :
    positiveLogTruncation (thetaSquareLogAtom m) u +
        (m : ℝ) ^ (-(1 : ℝ) / 2) *
          forwardTranslationBoundary (2 * Real.log m) thetaLogMother u =
      (m : ℝ) ^ (-(1 : ℝ) / 2) *
        positiveLogTruncation thetaLogMother (u + 2 * Real.log m) := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < 2 * Real.log (m : ℝ) := by
    have := Real.log_pos hmR
    linarith
  let c : ℝ := (m : ℝ) ^ (-(1 : ℝ) / 2)
  let a : ℝ := 2 * Real.log m
  have hatom : positiveLogTruncation (thetaSquareLogAtom m) u =
      c * positiveLogTruncation (fun v => thetaLogMother (v + a)) u := by
    by_cases hu : 0 < u
    · simp [positiveLogTruncation, hu, c, a,
        thetaSquareLogAtom_eq_shifted_mother hm0]
    · simp [positiveLogTruncation, hu]
  have hcomm :=
    positiveLogTruncation_translate_add_boundary thetaLogMother ha u
  change positiveLogTruncation (thetaSquareLogAtom m) u +
      c * forwardTranslationBoundary a thetaLogMother u =
    c * positiveLogTruncation thetaLogMother (u + a)
  rw [hatom]
  calc
    c * positiveLogTruncation (fun v => thetaLogMother (v + a)) u +
          c * forwardTranslationBoundary a thetaLogMother u =
        c * (positiveLogTruncation (fun v => thetaLogMother (v + a)) u +
          forwardTranslationBoundary a thetaLogMother u) := by ring
    _ = c * positiveLogTruncation thetaLogMother (u + a) := by rw [hcomm]

/-- The swept boundary written in the mother coordinate after translation. -/
def forwardTranslationWindow {E : Type*} [Zero E]
    (a : ℝ) (f : ℝ → E) (v : ℝ) : E :=
  (Ioc 0 a).indicator f v

theorem forwardTranslationBoundary_eq_window_translate
    {E : Type*} [Zero E] (f : ℝ → E) (a u : ℝ) :
    forwardTranslationBoundary a f u =
      forwardTranslationWindow a f (u + a) := by
  by_cases hu : u ∈ Ioc (-a) 0
  · have huv : u + a ∈ Ioc 0 a := by
      constructor <;> linarith [hu.1, hu.2]
    simp [forwardTranslationBoundary, forwardTranslationWindow, hu, huv]
  · have huv : u + a ∉ Ioc 0 a := by
      intro h
      apply hu
      constructor <;> linarith [h.1, h.2]
    simp [forwardTranslationBoundary, forwardTranslationWindow, hu, huv]

/-- The exact Fourier coordinate of the moving boundary: a translation phase times a finite
mother-profile window. -/
theorem fourier_forwardTranslationBoundary (f : ℝ → ℂ) (a w : ℝ) :
    𝓕 (forwardTranslationBoundary a f) w =
      (Real.fourierChar (a * w) : ℂ) * 𝓕 (forwardTranslationWindow a f) w := by
  have hfun : forwardTranslationBoundary a f =
      forwardTranslationWindow a f ∘ fun u : ℝ => u + a := by
    funext u
    exact forwardTranslationBoundary_eq_window_translate f a u
  rw [hfun]
  have h := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (forwardTranslationWindow a f) a) w
  simpa [Real.fourier_eq, Fourier.fourierIntegral_def, Circle.smul_def,
    Function.comp_apply, mul_comm] using h

end RHTower
