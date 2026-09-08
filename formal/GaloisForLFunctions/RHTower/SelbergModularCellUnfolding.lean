import GaloisForLFunctions.RHTower.SelbergCompactPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompactModularPeriodization
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-!
# Exact full modular cell unfolding

The literal SL(2,Z) orbit sum is twice its projective counterpart, by the
actual two-element fibers of the modular action quotient. Compact support
and the modular height bound make all contributing translates finite over
the entire closed cell. This discharges real integral unfolding, including
continuous invariant densities and all kernel/stabilizer repetitions.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergModularCellUnfolding
noncomputable section
open SelbergCompactPeriodization

private theorem ne_neg (A : SL2Z) : A ≠ -A := by
  intro h
  have h1 : (1 : SL2Z) = -1 := by
    have hh := congrArg (fun B : SL2Z => A⁻¹ * B) h
    simpa using hh
  have hh := congrArg (fun B : SL2Z => B 0 0) h1
  norm_num at hh

private def signFiber (A : SL2Z) : Bool → {B : SL2Z // (QuotientGroup.mk B : PSL2Z) = QuotientGroup.mk A}
  | false => ⟨A, rfl⟩
  | true => ⟨-A, PSL2Z_mk_neg A⟩

private def signFiberEquiv (A : SL2Z) :
    Bool ≃ {B : SL2Z // (QuotientGroup.mk B : PSL2Z) = QuotientGroup.mk A} :=
  Equiv.ofBijective (signFiber A) (by
    constructor
    · intro b c h
      cases b <;> cases c <;> simp_all [signFiber, Subtype.ext_iff, ne_neg A, (ne_neg A).symm]
    · rintro ⟨B, hB⟩
      rcases (PSL2Z_mk_eq_iff A B).mp hB.symm with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩)

/-- Literal projective orbit sum, retaining elliptic stabilizer repetitions. -/
def projectivePeriodize (g : ℍ → ℝ) (z : ℍ) : ℝ := ∑' A : PSL2Z, g (A • z)

/-- Regrouping the full integral group sum proves its exact factor-two normalization. -/
theorem periodize_eq_twice_projective (g : C_c(ℍ, ℝ)) (z : ℍ) :
    periodize g z = 2 * projectivePeriodize g z := by
  have h := (orbit_summable g.hasCompactSupport z).hasSum.tsum_fiberwise
    (QuotientGroup.mk : SL2Z → PSL2Z)
  have hf (q : PSL2Z) :
      (∑' B : (QuotientGroup.mk : SL2Z → PSL2Z) ⁻¹' {q}, g ((B : SL2Z) • z)) =
        2 * g (q • z) := by
    induction q using QuotientGroup.induction_on with
    | H A =>
      change (∑' B : {B : SL2Z // (QuotientGroup.mk B : PSL2Z) = QuotientGroup.mk A},
        g ((B : SL2Z) • z)) = _
      rw [← (signFiberEquiv A).tsum_eq]
      rw [tsum_fintype, Fintype.sum_bool]
      simp only [signFiberEquiv, Equiv.ofBijective_apply, signFiber, SL_neg_smul, PSL2Z_mk_smul]
      ring
  simpa only [hf, tsum_mul_left, projectivePeriodize, periodize] using h.tsum_eq.symm

/-- A compact real test has only finitely many contributing translates over the whole closed cell. -/
theorem cell_translates_finite (g : C_c(ℍ, ℝ)) :
    ∃ s : Finset PSL2Z, ∀ A ∉ s, ∀ z ∈ fd, g (A • z) = 0 := by
  classical
  obtain ⟨M, hM⟩ := _root_.RHTower.D4BMModularCore.compact_orbit_cell_bound
    (tsupport g) g.hasCompactSupport
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z)
    (_root_.RHTower.D4BMModularCore.truncated_cell_compact M) g.hasCompactSupport
  refine ⟨hfin.toFinset, ?_⟩
  intro A hA z hz
  by_contra hn
  apply hA
  simp only [Set.Finite.mem_toFinset]
  exact ⟨A • z, ⟨z, ⟨hz, hM z ⟨A, subset_tsupport g hn⟩⟩, rfl⟩, subset_tsupport g hn⟩

/-- The absolute cell integrals of all compact translates form a summable series. -/
theorem cell_integral_norm_summable (g : C_c(ℍ, ℝ)) :
    Summable (fun A : PSL2Z => ∫ z : ℍ in fd, ‖g (A • z)‖) := by
  classical
  obtain ⟨s, hs⟩ := cell_translates_finite g
  apply summable_of_ne_finset_zero (s := s)
  intro A hA
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
  simp only [hs A hA z hz, norm_zero, Pi.zero_apply]

/-- Projective periodization unfolds against actual hyperbolic volume for every compact continuous real test. -/
theorem integral_projectivePeriodize (g : C_c(ℍ, ℝ)) :
    (∫ z : ℍ in fd, projectivePeriodize g z) = ∫ z : ℍ, g z := by
  have hi : Integrable g := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have ht (A : PSL2Z) : IntegrableOn (fun z : ℍ => g (A • z)) fd :=
    ((measurePreserving_smul A volume).integrable_comp_emb
      (measurableEmbedding_const_smul A) |>.mpr hi).integrableOn
  rw [isFundamentalDomain_fd.integral_eq_tsum'' g hi,
    integral_tsum_of_summable_integral_norm ht (cell_integral_norm_summable g)]
  rfl

/-- Full SL(2,Z) periodization unfolds with its exact doubled normalization. -/
theorem integral_periodize (g : C_c(ℍ, ℝ)) :
    (∫ z : ℍ in fd, periodize g z) = 2 * ∫ z : ℍ, g z := by
  simp only [periodize_eq_twice_projective, integral_const_mul, integral_projectivePeriodize]

/-- Unfolding with a continuous invariant density has all compactness and integrability discharged. -/
theorem integral_periodize_mul (g : C_c(ℍ, ℝ)) (u : ℍ → ℝ) (hu : Continuous u)
    (hinv : ∀ A : SL2Z, ∀ z : ℍ, u (A • z) = u z) :
    (∫ z : ℍ in fd, periodize g z * u z) = 2 * ∫ z : ℍ, g z * u z := by
  have h := integral_periodize (mulContinuous g u hu)
  have hp (z : ℍ) : periodize (mulContinuous g u hu) z = periodize g z * u z := by
    simp only [periodize, mulContinuous_apply, hinv, tsum_mul_right]
  simpa only [hp, mulContinuous_apply] using h

end
end GaloisForLFunctions.RHTower.SelbergModularCellUnfolding
