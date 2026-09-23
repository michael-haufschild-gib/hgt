import GaloisForLFunctions.RHTower.SelbergMaassUniformCurvatureTail

/-!
# Exact total mass of the original compact-orbit curvature functional

Uniform tails of the actual regularized source let normalized compact orbit
weights capture the full cell mass. The limiting functional therefore has
exact total mass equal to half the spectral parameter times original amplitude
mass. The factor one half retains the kernel of the full SL(2,Z) periodization.
A positive compact test also proves that the constructed curvature measure is
nonzero for every original exceptional Maass source.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassQuotientMass
open SelbergMaassMean SelbergModularDomainSlices SelbergMaassFullCurvatureBudget
  SelbergMaassRegularizedArea SelbergMaassUniformCurvatureTail SelbergMaassRegulatorMass
  SelbergMaassCellCurvature SelbergMaassCurvatureCovariance SelbergCompactPeriodization
  SelbergQuotientCurvature SelbergMaassCurvatureMeasure SelbergMaassWeakCurvature
noncomputable section

/-- The literal closed hyperbolic modular cell truncated at height Y. -/
def cellCore (Y : ℝ) : Set ℍ := {z | z ∈ fd ∧ z.im ≤ Y}

/-- Every finite closed cell truncation is compact. -/
theorem cellCore_compact (Y : ℝ) : IsCompact (cellCore Y) :=
  _root_.RHTower.D4BMModularCore.truncated_cell_compact Y

/-- Original planar truncations and hyperbolic cell truncations agree pointwise. -/
theorem domain_iff_cellCore (z : ℍ) (Y : ℝ) : (z.re, z.im) ∈ domain Y ↔ z ∈ cellCore Y := by
  change ((z.re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ z.im ∈ Icc (1 / 2 : ℝ) Y) ∧
    SelbergMaassTraceStokes.arcHeight z.re ≤ z.im) ↔ z ∈ fd ∧ z.im ≤ Y
  constructor
  · rintro ⟨⟨hx, hy⟩, ha⟩
    exact ⟨(fullDomain_iff_fd z).mp ⟨hx, ha⟩, hy.2⟩
  · rintro ⟨hz, hy⟩
    obtain ⟨hx, ha⟩ := (fullDomain_iff_fd z).mpr hz
    exact ⟨⟨hx, (arcHeight_half_le hx).trans ha, hy⟩, ha⟩

/-- The full planar tail is exactly the closed-cell complement of the matching hyperbolic truncation. -/
theorem tailDomain_iff_cellTail (z : ℍ) (Y : ℝ) :
    (z.re, z.im) ∈ tailDomain Y ↔ z ∈ fd \ cellCore Y := by
  simp only [tailDomain, Set.mem_sdiff, fullDomain_iff_fd, domain_iff_cellCore]

section Source
variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Exact chart transport identifies the complete retained-curvature tail on both original domains. -/
theorem cell_tail_curvature_eq (e : Ioi (0 : ℝ)) (Y : ℝ) :
    (∫ z : ℍ in fd \ cellCore Y, hyperbolicCurvature N f e z) =
      ∫ p in tailDomain Y, weightedRemainder N f e p := by
  have hmeas := isClosed_fd.measurableSet.diff (cellCore_compact Y).measurableSet
  have he (z : ℍ) :
      z.im ^ (2 : ℕ) * (tailDomain Y).indicator (weightedRemainder N f e) (z.re, z.im) =
        (fd \ cellCore Y).indicator (hyperbolicCurvature N f e) z := by
    by_cases hz : z ∈ fd \ cellCore Y
    · rw [Set.indicator_of_mem ((tailDomain_iff_cellTail z Y).mpr hz), Set.indicator_of_mem hz]
      have hp : point z.re z.im = (z : ℂ) := by apply Complex.ext <;> simp [point]
      simp only [hyperbolicCurvature, curvatureWeight, weightedRemainder, hp]
    · rw [Set.indicator_of_notMem (fun hp => hz ((tailDomain_iff_cellTail z Y).mp hp)),
        Set.indicator_of_notMem hz, mul_zero]
  have h := integral_height_sq_cell ((tailDomain Y).indicator (weightedRemainder N f e))
  simp only [he, setIntegral_indicator hmeas, setIntegral_indicator (tailDomain_measurable Y),
    inter_eq_right.mpr (sdiff_subset : fd \ cellCore Y ⊆ fd),
    inter_eq_right.mpr (tailDomain_subset Y)] at h
  exact h
end Source

section Exceptional
variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- A normalized orbit test equal to one on the actual core loses at most the original curvature tail. -/
theorem cell_pairing_deficit_le_tail (e : Ioi (0 : ℝ)) (Y : ℝ) (w : C_c(ℍ, ℝ))
    (h0 : ∀ z, 0 ≤ periodize w z) (h1 : ∀ z, periodize w z ≤ 1)
    (hK : ∀ z ∈ cellCore Y, periodize w z = 1) :
    (∫ z : ℍ in fd, hyperbolicCurvature N f e z) -
      (∫ z : ℍ in fd, periodize w z * hyperbolicCurvature N f e z) ≤
        ∫ p in tailDomain Y, weightedRemainder N f e p := by
  have hi := cell_curvature_integrable N lam f e
  have hw : IntegrableOn (fun z : ℍ => periodize w z * hyperbolicCurvature N f e z) fd :=
    hi.mono' ((periodize_continuous w).mul (hyperbolicCurvature_continuous N f e)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 z) (hyperbolicCurvature_nonneg N f e z))]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (h1 z) (hyperbolicCurvature_nonneg N f e z))
  have hmeas := isClosed_fd.measurableSet.diff (cellCore_compact Y).measurableSet
  have htail : (∫ z : ℍ in fd, (fd \ cellCore Y).indicator (hyperbolicCurvature N f e) z) =
      ∫ p in tailDomain Y, weightedRemainder N f e p := by
    rw [setIntegral_indicator hmeas, inter_eq_right.mpr (sdiff_subset : fd \ cellCore Y ⊆ fd),
      cell_tail_curvature_eq]
  rw [← integral_sub hi hw, ← htail]
  apply integral_mono_ae (hi.sub hw) (hi.indicator hmeas)
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
  change hyperbolicCurvature N f e z - periodize w z * hyperbolicCurvature N f e z ≤ _
  by_cases hzk : z ∈ cellCore Y
  · rw [Set.indicator_of_notMem (fun (ht : z ∈ fd \ cellCore Y) => ht.2 hzk), hK z hzk]
    simp
  · rw [Set.indicator_of_mem (show z ∈ fd \ cellCore Y from ⟨hz, hzk⟩)]
    have h := mul_nonneg (h0 z) (hyperbolicCurvature_nonneg N f e z)
    linarith

/-- Actual compact orbit tests capture arbitrarily close to all of the original source mass. -/
theorem exists_weight_capturing_mass {eps : ℝ} (heps : 0 < eps) :
    ∃ w : C_c(ℍ, ℝ), (∀ z, 0 ≤ w z) ∧ (∀ z, periodize w z ≤ 1) ∧
      0 ≤ (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
        2 * positiveFunctional N f (orbitTest w) ∧
      (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
        2 * positiveFunctional N f (orbitTest w) < eps := by
  obtain ⟨Y, hY, ht⟩ := curvature_tail_uniform_decay N lam f (half_pos heps)
  obtain ⟨w, hw, h1, hK⟩ := exists_normalized_weight (cellCore_compact Y)
  have h0 : ∀ z, 0 ≤ periodize w z := fun z => periodize_nonneg hw z
  have hlim : Tendsto (fun e : Ioi (0 : ℝ) => ∫ z : ℍ in fd, hyperbolicCurvature N f e z)
      regulatorAtZero (𝓝 ((lam : ℝ) * ∫ p in fullDomain, amplitudeMassDensity N lam f p)) := by
    simpa only [cell_curvature_eq_planar] using full_curvature_limit N lam f
  have hd := hlim.sub (cell_pairing_limit N f w)
  have hle : (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) -
      2 * positiveFunctional N f (orbitTest w) ≤ eps / 2 := by
    apply le_of_tendsto hd
    exact Eventually.of_forall fun e =>
      (cell_pairing_deficit_le_tail N lam f e Y w h0 h1 hK).trans (ht e Y le_rfl).le
  refine ⟨w, hw, h1, ?_, lt_of_le_of_lt hle (by linarith)⟩
  exact sub_nonneg.mpr (positiveFunctional_le_amplitude N lam f w h0 h1)

/-- Literal values of the positive source functional on full orbit fields between zero and one. -/
def orbitValues : Set ℝ := {r | ∃ g : C_c(ℍ, ℝ), (∀ z, 0 ≤ periodize g z) ∧
  (∀ z, periodize g z ≤ 1) ∧ r = positiveFunctional N f (orbitTest g)}

/-- The actual compact orbit-value family is nonempty. -/
theorem orbitValues_nonempty : (orbitValues N lam f).Nonempty := by
  obtain ⟨w, hw, h1, _hlo, _hhi⟩ := exists_weight_capturing_mass N lam f (eps := 1) zero_lt_one
  exact ⟨positiveFunctional N f (orbitTest w), w, (fun z => periodize_nonneg hw z), h1, rfl⟩

/-- The total curvature of the literal orbit functional, defined by its compact positive tests. -/
def totalOrbitCurvature : ℝ := sSup (orbitValues N lam f)

/-- Uniform source tails identify the exact total limiting orbit curvature, including the SL/PSL normalization. -/
theorem totalOrbitCurvature_eq :
    totalOrbitCurvature N lam f = (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) / 2 := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (orbitValues_nonempty N lam f)
  · rintro r ⟨g, h0, h1, rfl⟩
    have h := positiveFunctional_le_amplitude N lam f g h0 h1
    linarith
  · intro r hr
    have heps : 0 < (lam : ℝ) * (∫ p in fullDomain, amplitudeMassDensity N lam f p) - 2 * r := by linarith
    obtain ⟨w, hw, h1, _hlo, hhi⟩ := exists_weight_capturing_mass N lam f heps
    refine ⟨positiveFunctional N f (orbitTest w), ⟨w, (fun z => periodize_nonneg hw z), h1, rfl⟩, ?_⟩
    linarith

/-- The full limiting orbit curvature has strictly positive mass from original source nonvanishing. -/
theorem totalOrbitCurvature_pos : 0 < totalOrbitCurvature N lam f := by
  rw [totalOrbitCurvature_eq]
  exact div_pos (mul_pos lam.2.1 (full_amplitudeMass_pos N lam f)) (by norm_num)

/-- Some actual nonnegative compact test has strictly positive limiting curvature. -/
theorem exists_positive_compact_curvature :
    ∃ g : C_c(ℍ, ℝ), (∀ z, 0 ≤ g z) ∧ 0 < ∫ z : ℍ, g z ∂curvatureMeasure N f := by
  have hp := mul_pos lam.2.1 (full_amplitudeMass_pos N lam f)
  obtain ⟨g, hg, _h1, _hlo, hhi⟩ := exists_weight_capturing_mass N lam f (half_pos hp)
  refine ⟨g, hg, ?_⟩
  rw [← positiveFunctional_orbitTest]
  linarith

/-- The actual limiting curvature measure is nonzero. -/
theorem curvatureMeasure_ne_zero : curvatureMeasure N f ≠ 0 := by
  obtain ⟨g, _hg, hp⟩ := exists_positive_compact_curvature N lam f
  intro hz
  rw [hz, integral_zero_measure] at hp
  exact lt_irrefl 0 hp

end Exceptional
end
end GaloisForLFunctions.RHTower.SelbergMaassQuotientMass
