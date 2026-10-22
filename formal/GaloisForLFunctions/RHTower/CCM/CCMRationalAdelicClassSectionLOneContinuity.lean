import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicArchimedeanLOneContinuity
import GaloisForLFunctions.RHTower.CCM.CCMRationalProfiniteUniformDenominator

/-!
# Joint `ℓ1` continuity on the rational idele-class section

Pure adelic Bruhat tensors define genuine `ℓ1(ℚˣ)` orbit coefficients continuously over the
actual rational class-space section `𝔽̂ˣ × ℝ₊ˣ`.  The proof combines one denominator valid
for every profinite unit with a local uniform Schwartz lattice envelope in the positive-real
coordinate.  Coordinate continuity then upgrades to `ℓ1` continuity by Tannery's theorem.
-/

noncomputable section

open scoped RestrictedProduct algebraMap
open Filter Topology

namespace GaloisForLFunctions
namespace RHTower

/-- Pure-tensor orbit coefficient over the actual rational class-space section. -/
def ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (s : CCMRationalClassSpaceSection) :
    CCMRationalMoritaLOneCoefficient :=
  ccmRationalAdelicBruhatPureTensorOrbitLOne f φ
    (bInf := ((s.2.val : NNReal) : ℝ))
    (by
      have hspos : 0 < ((s.2.val : NNReal) : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr s.2.ne_zero : 0 < s.2.val)
      exact hspos.ne')
    s.1.val

@[simp]
theorem ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection_apply
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (s : CCMRationalClassSpaceSection) (q : CCMRationalUnit) :
    ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection f φ s q =
      ccmRationalAdelicBruhatPureTensorOrbitCoefficient f φ
        ((s.2.val : NNReal) : ℝ) s.1.val q :=
  rfl

/-- **Full-section pure-tensor landing.** -/
theorem ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection_continuous
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz) :
    Continuous
      (ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection f φ) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  classical
  obtain ⟨C, hC⟩ := ccmRationalFiniteBruhat_exists_norm_bound φ
  obtain ⟨d, hd, hden⟩ :=
    ccmRationalFiniteBruhat_exists_uniformProfiniteIntegerDenominator φ
  let S : Set CCMRationalUnit :=
    {q | algebraMap ℤ ℚ d * (q : ℚ) ∈ (algebraMap ℤ ℚ).range}
  choose n hn using fun q : S => q.2
  have hnInjective : Function.Injective n := by
    intro q r hqr
    apply Subtype.ext
    apply Units.ext
    have hdQ : algebraMap ℤ ℚ d ≠ 0 := by
      simpa using (Int.cast_ne_zero.mpr hd : (d : ℚ) ≠ 0)
    apply mul_left_cancel₀ hdQ
    calc
      algebraMap ℤ ℚ d * (q.1 : ℚ) = algebraMap ℤ ℚ (n q) := (hn q).symm
      _ = algebraMap ℤ ℚ (n r) := by rw [hqr]
      _ = algebraMap ℤ ℚ d * (r.1 : ℚ) := hn r
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hdabs : 0 < |(d : ℝ)| := abs_pos.mpr hdR
  let r₀ : ℝ := ((s₀.2.val : NNReal) : ℝ)
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    exact_mod_cast (pos_iff_ne_zero.mpr s₀.2.ne_zero : 0 < s₀.2.val)
  let a₀ : ℝ := (r₀ / 2) / |(d : ℝ)|
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
  have hu : Summable u := summable_subtype_iff_indicator.mp hsub'
  have hcoord : ∀ q, ContinuousAt
      (fun s => ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection
        f φ s q) s₀ := by
    intro q
    change ContinuousAt (fun s : CCMRationalClassSpaceSection =>
      f (((s.2.val : NNReal) : ℝ) * ((q : ℚ) : ℝ)) *
        φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * s.1.val)) s₀
    have hsnd : Continuous
        (fun s : CCMRationalClassSpaceSection => s.2) := continuous_snd
    have hunitNN : Continuous
        (fun x : Units NNReal => x.val) := Units.continuous_val
    have hNNReal : Continuous
        (fun x : NNReal => (x : ℝ)) := NNReal.continuous_coe
    have hrealCoord : Continuous
        (fun s : CCMRationalClassSpaceSection => ((s.2.val : NNReal) : ℝ)) :=
      hNNReal.comp (hunitNN.comp hsnd)
    have hprofinite : Continuous
        (fun s : CCMRationalClassSpaceSection => s.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hidele : Continuous
        (fun x : CCMRationalFiniteAdeleˣ =>
          (x : CCMRationalFiniteAdele)) := Units.continuous_val
    have hfinite : Continuous
        (fun s : CCMRationalClassSpaceSection =>
          (s.1.val : CCMRationalFiniteAdele)) :=
      hidele.comp hprofinite
    exact (f.continuous.comp (hrealCoord.mul continuous_const)).mul
      (φ.1.continuous.comp (continuous_const.mul hfinite)) |>.continuousAt
  have hreal : Tendsto
      (fun s : CCMRationalClassSpaceSection => ((s.2.val : NNReal) : ℝ))
      (𝓝 s₀) (𝓝 r₀) := by
    change ContinuousAt
      (fun s : CCMRationalClassSpaceSection => ((s.2.val : NNReal) : ℝ)) s₀
    fun_prop
  have hevent : ∀ᶠ s in 𝓝 s₀,
      r₀ / 2 < ((s.2.val : NNReal) : ℝ) :=
    hreal (Ioi_mem_nhds (by linarith))
  have hbound : ∀ᶠ s in 𝓝 s₀, ∀ q,
      ‖ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection f φ s q‖ ≤
        u q := by
    filter_upwards [hevent] with s hs
    intro q
    by_cases hq : q ∈ S
    · let qs : S := ⟨q, hq⟩
      have hnReal : (n qs : ℝ) = (d : ℝ) * ((q : ℚ) : ℝ) := by
        exact_mod_cast hn qs
      have harg :
          ((s.2.val : NNReal) : ℝ) * ((q : ℚ) : ℝ) =
            (((s.2.val : NNReal) : ℝ) / (d : ℝ)) * (n qs : ℝ) := by
        rw [hnReal]
        field_simp
      have hspos : 0 < ((s.2.val : NNReal) : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr s.2.ne_zero : 0 < s.2.val)
      have hspacing :
          a₀ ≤ |((s.2.val : NNReal) : ℝ) / (d : ℝ)| := by
        rw [abs_div, abs_of_pos hspos]
        exact div_le_div_of_nonneg_right hs.le hdabs.le
      have harch := huZMajor
        (((s.2.val : NNReal) : ℝ) / (d : ℝ)) hspacing (n qs)
      rw [← harg] at harch
      rw [ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection_apply,
        ccmRationalAdelicBruhatPureTensorOrbitCoefficient,
        ccmRationalAdelicBruhatPureTensorOrbit, norm_mul]
      have hprod :
          ‖f (((s.2.val : NNReal) : ℝ) * ((q : ℚ) : ℝ))‖ *
              ‖φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * s.1.val)‖ ≤
            uZ (n qs) * C :=
        mul_le_mul harch (hC _)
          (norm_nonneg _) ((norm_nonneg _).trans harch)
      simpa [u, Set.indicator_of_mem hq, v, nFull, hq, qs, mul_comm] using hprod
    · have hφ :
          φ.1 (algebraMap ℚ CCMRationalFiniteAdele (q : ℚ) * s.1.val) = 0 := by
        by_contra hne
        exact hq (hden s.1 (q : ℚ) hne)
      simp [ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection,
        ccmRationalAdelicBruhatPureTensorOrbitLOne_apply,
        ccmRationalAdelicBruhatPureTensorOrbitCoefficient,
        ccmRationalAdelicBruhatPureTensorOrbit, hφ, u,
        Set.indicator_of_notMem hq]
  exact continuousAt_ccmRationalMoritaLOneCoefficient_of_dominated
    (ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection f φ)
    s₀ u hu hcoord hbound

/-- Pure-tensor Morita operators vary continuously in the actual trace norm over the full
rational class-space section. -/
theorem ccmRationalAdelicBruhatPureTensorWeightedShiftClassSection_continuous
    (f : CCMRationalArchimedeanSchwartz)
    (φ : CCMRationalFiniteBruhatSchwartz)
    (k : CCMRationalUnit) :
    Continuous (fun s : CCMRationalClassSpaceSection =>
      ccmRationalMoritaLOneWeightedShift k
        (ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection f φ s)) :=
  (ccmRationalMoritaLOneWeightedShiftLinearIsometry k).continuous.comp
    (ccmRationalAdelicBruhatPureTensorOrbitLOneClassSection_continuous f φ)

end RHTower
end GaloisForLFunctions
