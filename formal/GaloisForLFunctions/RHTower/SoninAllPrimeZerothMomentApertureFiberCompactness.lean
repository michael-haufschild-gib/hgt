import GaloisForLFunctions.RHTower.SoninAllPrimeZerothMomentApertureSurjectivity
import GaloisForLFunctions.HTGeometry.SpectralBundleCaptureTube

/-!
# Compactness of the exact Sonin zeroth-moment aperture fiber

The positive apertures which exactly match the normalized prime--archimedean zeroth moment form
a nonempty compact set.  Consequently, every higher-moment mismatch attains a genuine minimum on
that exact normalization fiber.  This removes all aperture-escape and unattained-infimum
ambiguity from the remaining simultaneous-moment problem.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Positive apertures with exact normalized prime--archimedean zeroth moment. -/
def soninNormalizedZerothApertureFiber : Set ℝ :=
  {a | 0 < a ∧
    soninAllPrimeEnergyMoment a 0 = (normalizedPrimeArchMoment 0 : ℂ)}

/-- The exact zeroth-moment aperture fiber is nonempty. -/
theorem soninNormalizedZerothApertureFiber_nonempty :
    soninNormalizedZerothApertureFiber.Nonempty := by
  obtain ⟨a, ha, heq⟩ :=
    exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq_normalizedPrimeArchMoment
  exact ⟨a, ha, heq⟩

/-- Every exact zeroth-moment aperture lies in one fixed compact positive window. -/
theorem soninNormalizedZerothApertureFiber_exists_compactWindow :
    ∃ δ A : ℝ, 0 < δ ∧ δ < A ∧
      soninNormalizedZerothApertureFiber ⊆ Set.Icc δ A := by
  let T : ℝ := normalizedPrimeArchMoment 0
  let M : ℝ := soninAllPrimeColumnWeightSqMass
  let R : ℝ := 128 * M
  let δ : ℝ := Real.sqrt (T / (2 * R))
  have hT : 0 < T := by
    simpa only [T] using normalizedPrimeArchMoment_zero_pos
  have hM : 0 < M := by
    simpa only [M] using soninAllPrimeColumnWeightSqMass_pos
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hratio : 0 < T / (2 * R) := by positivity
  have hδ : 0 < δ := Real.sqrt_pos.2 hratio
  have hδsq : δ ^ (2 : ℕ) = T / (2 * R) := by
    dsimp only [δ]
    exact Real.sq_sqrt hratio.le
  let f : ℝ → ℝ := fun a => (soninAllPrimeEnergyMoment a 0).re
  have hlargeEventually : ∀ᶠ a : ℝ in atTop, T < f a := by
    simpa only [f] using
      tendsto_re_soninAllPrimeEnergyMoment_zero_atTop.eventually_gt_atTop T
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 hlargeEventually
  let A : ℝ := max (δ + 1) A₀
  have hδA : δ < A :=
    (lt_add_one δ).trans_le (le_max_left (δ + 1) A₀)
  refine ⟨δ, A, hδ, hδA, ?_⟩
  intro a ha
  have haPos : 0 < a := ha.1
  have hfa : f a = T := by
    have hre := congrArg Complex.re ha.2
    simpa only [f, T, Complex.ofReal_re] using hre
  have harea := re_soninAllPrimeEnergyMoment_zero_le_area a haPos
  have hbound : T ≤ R * a ^ (2 : ℕ) := by
    rw [← hfa]
    dsimp only [f]
    calc
      (soninAllPrimeEnergyMoment a 0).re ≤
          (128 * a ^ (2 : ℕ)) * soninAllPrimeColumnWeightSqMass := harea
      _ = R * a ^ (2 : ℕ) := by
        dsimp only [R, M]
        ring
  have hδa : δ ≤ a := by
    by_contra hnot
    have haδ : a < δ := lt_of_not_ge hnot
    have hsquares : a ^ (2 : ℕ) < δ ^ (2 : ℕ) := by nlinarith
    have hhalf : R * a ^ (2 : ℕ) < T / 2 := by
      rw [hδsq] at hsquares
      rw [lt_div_iff₀ (by positivity : 0 < (2 : ℝ))]
      rw [div_eq_mul_inv] at hsquares
      field_simp [hR.ne'] at hsquares
      nlinarith
    nlinarith
  have haA : a ≤ A := by
    by_contra hnot
    have hAa : A < a := lt_of_not_ge hnot
    have hA₀a : A₀ ≤ a :=
      (le_max_right (δ + 1) A₀).trans hAa.le
    have hstrict := hA₀ a hA₀a
    rw [hfa] at hstrict
    exact lt_irrefl T hstrict
  exact ⟨hδa, haA⟩

/-- The exact normalized zeroth-moment aperture fiber is compact. -/
theorem soninNormalizedZerothApertureFiber_isCompact :
    IsCompact soninNormalizedZerothApertureFiber := by
  obtain ⟨δ, A, hδ, _hδA, hsub⟩ :=
    soninNormalizedZerothApertureFiber_exists_compactWindow
  let g : ℝ → ℂ := fun a => soninAllPrimeEnergyMoment a 0
  let target : ℂ := normalizedPrimeArchMoment 0
  have hg : ContinuousOn g (Set.Icc δ A) := by
    exact (continuousOn_soninAllPrimeEnergyMoment 0).mono
      (fun a ha => hδ.trans_le ha.1)
  have hcompact : IsCompact
      (Set.Icc δ A ∩ g ⁻¹' ({target} : Set ℂ)) :=
    GaloisForLFunctions.HTGeometry.isCompact_inter_preimage_of_continuousOn
      isCompact_Icc hg isClosed_singleton
  have heq : soninNormalizedZerothApertureFiber =
      Set.Icc δ A ∩ g ⁻¹' ({target} : Set ℂ) := by
    ext a
    constructor
    · intro ha
      exact ⟨hsub ha, by simpa only [Set.mem_preimage, Set.mem_singleton_iff, g, target]
        using ha.2⟩
    · rintro ⟨haIcc, haeq⟩
      refine ⟨hδ.trans_le haIcc.1, ?_⟩
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, g, target] using haeq
  rwa [heq]

/-- Degree-`r` mismatch after imposing exact zeroth-moment normalization. -/
def soninNormalizedHigherMomentDefect (r : ℕ) (a : ℝ) : ℝ :=
  ‖soninAllPrimeEnergyMoment a r - (normalizedPrimeArchMoment r : ℂ)‖

/-- Every higher-moment mismatch attains its minimum on the exact zeroth-moment aperture fiber. -/
theorem exists_soninNormalizedHigherMomentDefect_isMinOn (r : ℕ) :
    ∃ a ∈ soninNormalizedZerothApertureFiber,
      IsMinOn (soninNormalizedHigherMomentDefect r)
        soninNormalizedZerothApertureFiber a := by
  apply soninNormalizedZerothApertureFiber_isCompact.exists_isMinOn
    soninNormalizedZerothApertureFiber_nonempty
  exact (((continuousOn_soninAllPrimeEnergyMoment r).sub continuousOn_const).norm).mono
    (fun a ha => ha.1)

/-- Exact first-coordinate classification on the zeroth-normalized fiber: either moments `0` and
`1` match at one positive aperture, or a single uniform positive gap separates the first moment
at every exactly zeroth-normalized aperture. -/
theorem soninNormalizedFirstMoment_exact_or_uniformGap :
    (∃ a : ℝ, 0 < a ∧
      soninAllPrimeEnergyMoment a 0 = (normalizedPrimeArchMoment 0 : ℂ) ∧
      soninAllPrimeEnergyMoment a 1 = (normalizedPrimeArchMoment 1 : ℂ)) ∨
    (∃ ε : ℝ, 0 < ε ∧ ∀ a : ℝ, 0 < a →
      soninAllPrimeEnergyMoment a 0 = (normalizedPrimeArchMoment 0 : ℂ) →
      ε ≤ ‖soninAllPrimeEnergyMoment a 1 -
        (normalizedPrimeArchMoment 1 : ℂ)‖) := by
  obtain ⟨a, ha, hmin⟩ :=
    exists_soninNormalizedHigherMomentDefect_isMinOn 1
  by_cases hzero : soninNormalizedHigherMomentDefect 1 a = 0
  · left
    refine ⟨a, ha.1, ha.2, ?_⟩
    have hsub : soninAllPrimeEnergyMoment a 1 -
        (normalizedPrimeArchMoment 1 : ℂ) = 0 := by
      apply norm_eq_zero.mp
      simpa only [soninNormalizedHigherMomentDefect] using hzero
    exact sub_eq_zero.mp hsub
  · right
    refine ⟨soninNormalizedHigherMomentDefect 1 a, ?_, ?_⟩
    · exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    · intro b hb hbeq
      exact hmin ⟨hb, hbeq⟩

end

end RHTower
