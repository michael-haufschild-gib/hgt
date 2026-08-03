import GaloisForLFunctions.RHTower.CCMRationalAdelicOrbitLOne
import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzUniformLattice

/-!
# Trace-norm continuity in the archimedean class-space coordinate

For a fixed finite idele and finite Bruhat factor, the rational orbit coefficient of an
archimedean/finite pure tensor varies continuously in genuine `ℓ1(ℚˣ)` as the nonzero real
base coordinate varies.  Via the exact weighted-shift isometry, the corresponding CCM Morita
operator therefore varies continuously in Schatten-`1` norm.
-/

noncomputable section

open scoped RestrictedProduct algebraMap
open Filter Topology

namespace GaloisForLFunctions
namespace RHTower

/-- Nonzero real base coordinates with their honest subspace topology. -/
abbrev CCMRationalNonzeroReal := {r : ℝ // r ≠ 0}

/-- Pure-tensor orbit coefficient over the nonzero real base coordinate. -/
def ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (r : CCMRationalNonzeroReal) :
    CCMRationalMoritaLOneCoefficient :=
  ccmRationalAdelicBruhatPureTensorOrbitLOne f φ r.property b

@[simp]
theorem ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily_apply
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ)
    (r : CCMRationalNonzeroReal) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily f φ b r q =
      ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ r.1 b q :=
  rfl

/-- **Archimedean `ℓ1` landing law.**  Rational pure-tensor orbit coefficients are continuous
in every nonzero real base coordinate. -/
theorem ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily_continuous
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    Continuous
      (ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily f φ b) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  classical
  obtain ⟨C, hC⟩ := ccmRationalFiniteBruhat_exists_norm_bound φ
  obtain ⟨d, hd, hden⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_integerDenominator φ b
  let S : Set CCMRationalUnit :=
    {q | φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * b) ≠ 0}
  choose n hn using fun q : S => hden (q.1 : ℚ) q.2
  have hnInjective : Function.Injective n := by
    intro q s hqs
    apply Subtype.ext
    apply Units.ext
    have hdQ : algebraMap ℤ ℚ d ≠ 0 := by
      simpa using (Int.cast_ne_zero.mpr hd : (d : ℚ) ≠ 0)
    apply mul_left_cancel₀ hdQ
    calc
      algebraMap ℤ ℚ d * (q.1 : ℚ) = algebraMap ℤ ℚ (n q) := (hn q).symm
      _ = algebraMap ℤ ℚ (n s) := by rw [hqs]
      _ = algebraMap ℤ ℚ d * (s.1 : ℚ) := hn s
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  let a₀ : ℝ := (|r₀.1| / 2) / |(d : ℝ)|
  have hr₀abs : 0 < |r₀.1| := abs_pos.mpr r₀.property
  have hdabs : 0 < |(d : ℝ)| := abs_pos.mpr hdR
  have ha₀ : 0 < a₀ := by
    dsimp [a₀]
    positivity
  obtain ⟨uZ, huZ, huZMajor⟩ :=
    ccmRationalArchimedeanSchwartz_exists_uniformLatticeMajorant f ha₀
  let nFull : CCMRationalUnit → ℤ := fun q =>
    if hq : q ∈ S then n ⟨q, hq⟩ else 0
  let v : CCMRationalUnit → ℝ := fun q => C * uZ (nFull q)
  let u : CCMRationalUnit → ℝ := S.indicator v
  have hsub : Summable (fun q : S => C * uZ (n q)) :=
    (huZ.comp_injective hnInjective).mul_left C
  have hsub' : Summable (fun q : S => v q.1) :=
    hsub.congr fun q => by simp [v, nFull, q.2]
  have hu : Summable u := by
    exact summable_subtype_iff_indicator.mp hsub'
  have hcoord : ∀ q, ContinuousAt
      (fun r => ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily
        f φ b r q) r₀ := by
    intro q
    change ContinuousAt (fun r : CCMRationalNonzeroReal =>
      f (r.1 * ((q : ℚ) : ℝ)) *
        φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * b)) r₀
    fun_prop
  have habs : Tendsto (fun r : CCMRationalNonzeroReal => |r.1|)
      (𝓝 r₀) (𝓝 |r₀.1|) := by
    change ContinuousAt (fun r : CCMRationalNonzeroReal => |r.1|) r₀
    fun_prop
  have hevent : ∀ᶠ r in 𝓝 r₀, |r₀.1| / 2 < |r.1| :=
    habs (Ioi_mem_nhds (by linarith))
  have hbound : ∀ᶠ r in 𝓝 r₀, ∀ q,
      ‖ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily f φ b r q‖ ≤
        u q := by
    filter_upwards [hevent] with r hr
    intro q
    by_cases hq : q ∈ S
    · let qs : S := ⟨q, hq⟩
      have hreal : (n qs : ℝ) = (d : ℝ) * ((q : ℚ) : ℝ) := by
        exact_mod_cast hn qs
      have harg :
          r.1 * ((q : ℚ) : ℝ) =
            (r.1 / (d : ℝ)) * (n qs : ℝ) := by
        rw [hreal]
        field_simp
      have hspacing : a₀ ≤ |r.1 / (d : ℝ)| := by
        rw [abs_div]
        exact div_le_div_of_nonneg_right hr.le hdabs.le
      have harch := huZMajor (r.1 / (d : ℝ)) hspacing (n qs)
      rw [← harg] at harch
      rw [ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily_apply,
        ccmRationalAdelicBruhatPureTensorOrbitCoefficient,
        ccmRationalAdelicBruhatPureTensorOrbit, norm_mul]
      have hprod :
          ‖f (r.1 * ((q : ℚ) : ℝ))‖ *
              ‖φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * b)‖ ≤
            uZ (n qs) * C :=
        mul_le_mul harch (hC _)
          (norm_nonneg _) ((norm_nonneg _).trans harch)
      simpa [u, Set.indicator_of_mem hq, v, nFull, hq, qs, mul_comm] using hprod
    · have hφ :
          φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * b) = 0 := by
        simpa [S] using hq
      simp [ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily,
        ccmRationalAdelicBruhatPureTensorOrbitLOne_apply,
        ccmRationalAdelicBruhatPureTensorOrbitCoefficient,
        ccmRationalAdelicBruhatPureTensorOrbit, hφ, u,
        Set.indicator_of_notMem hq]
  exact continuousAt_ccmRationalMoritaLOneCoefficient_of_dominated
    (ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily f φ b)
    r₀ u hu hcoord hbound

/-- Exact Schatten-`1` continuity of every fixed-label pure-tensor Morita family in the
archimedean class-space coordinate. -/
theorem ccmRationalAdelicBruhatPureTensorWeightedShiftRealFamily_continuous
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) (k : CCMRationalUnit) :
    Continuous (fun r : CCMRationalNonzeroReal =>
      ccmRationalMoritaLOneWeightedShift k
        (ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily f φ b r)) :=
  (ccmRationalMoritaLOneWeightedShiftLinearIsometry k).continuous.comp
    (ccmRationalAdelicBruhatPureTensorOrbitLOneRealFamily_continuous f φ b)

end RHTower
end GaloisForLFunctions
