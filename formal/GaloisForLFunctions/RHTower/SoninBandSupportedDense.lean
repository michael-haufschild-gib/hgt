import GaloisForLFunctions.RHTower.SoninBurnolLogBandComparison

/-!
# The band-supported core is dense

The bands `1/(N+1) < |t| ≤ N+1` exhaust the punctured line, so a vector all of whose band
truncations vanish is zero.  Each truncation is an orthogonal projection, so a vector orthogonal
to every band-supported vector is orthogonal to its own truncations, hence has all of them zero,
hence is zero.

The band-supported vectors therefore span a dense subspace.  Together with stationarity of the
truncated logarithms on that core, the logarithm of position is defined on a dense domain.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Set Filter Topology
open scoped InnerProduct InnerProductSpace

/-- The bands exhausting the punctured line. -/
def soninExhaustingBand (N : ℕ) : Set ℝ :=
  (fun t : ℝ => |t|) ⁻¹' Set.Ioc (((N : ℝ) + 1)⁻¹) ((N : ℝ) + 1)

theorem measurableSet_soninExhaustingBand (N : ℕ) :
    MeasurableSet (soninExhaustingBand N) :=
  (continuous_abs.measurable) measurableSet_Ioc

/-- Every nonzero point lies in some band. -/
theorem exists_mem_soninExhaustingBand {x : ℝ} (hx : x ≠ 0) :
    ∃ N : ℕ, x ∈ soninExhaustingBand N := by
  have hxpos : (0 : ℝ) < |x| := abs_pos.mpr hx
  obtain ⟨N, hN⟩ := exists_nat_gt (max |x| |x|⁻¹)
  have hNx : |x| < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNinv : |x|⁻¹ < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hinv : |x| * |x|⁻¹ = 1 := mul_inv_cancel₀ hxpos.ne'
  refine ⟨N, ?_⟩
  simp only [soninExhaustingBand, Set.mem_preimage, Set.mem_Ioc]
  constructor
  · have hlt : (1 : ℝ) / ((N : ℝ) + 1) < |x| := by
      rw [div_lt_iff₀ hNpos]
      nlinarith [hinv, hNinv, hxpos]
    simpa [one_div] using hlt
  · linarith

/-- A vector all of whose band truncations vanish is zero. -/
theorem eq_zero_of_forall_bandTruncation_eq_zero {h : SoninL2}
    (hz : ∀ N : ℕ, indicatorCutoff (soninExhaustingBand N)
      (measurableSet_soninExhaustingBand N) h = 0) : h = 0 := by
  apply Lp.ext
  have hae : ∀ N : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      (soninExhaustingBand N).indicator (fun y => (h : ℝ → ℂ) y) x = 0 := by
    intro N
    have h1 := indicatorCutoff_ae (soninExhaustingBand N)
      (measurableSet_soninExhaustingBand N) h
    have h2 : (indicatorCutoff (soninExhaustingBand N)
        (measurableSet_soninExhaustingBand N) h : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [hz N]
      exact Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← hx1, hx2]
    rfl
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ N : ℕ,
      (soninExhaustingBand N).indicator (fun y => (h : ℝ → ℂ) y) x = 0 :=
    ae_all_iff.mpr hae
  have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    have : (volume : Measure ℝ) {(0 : ℝ)} = 0 := Real.volume_singleton
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr this] with x hx
    simpa using hx
  filter_upwards [hall, hzero, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hx0 hz0
  obtain ⟨N, hN⟩ := exists_mem_soninExhaustingBand hx0
  have := hx N
  rw [Set.indicator_of_mem hN] at this
  rw [this, hz0]
  rfl

/-- **Density of the band-supported core.**  A vector orthogonal to every band-supported vector is
zero: applying the hypothesis to the vector's own band truncations, which are band supported
because the cutoffs are idempotent, makes each truncation have zero norm. -/
theorem eq_zero_of_inner_bandSupported_eq_zero {h : SoninL2}
    (horth : ∀ k : SoninL2, (∃ N : ℕ, indicatorCutoff (soninExhaustingBand N)
        (measurableSet_soninExhaustingBand N) k = k) → inner ℂ k h = 0) :
    h = 0 := by
  refine eq_zero_of_forall_bandTruncation_eq_zero fun N => ?_
  set T := indicatorCutoff (soninExhaustingBand N)
    (measurableSet_soninExhaustingBand N) with hT
  have hidem : T * T = T := by
    simpa only [hT] using
      (indicatorCutoff_idempotent (soninExhaustingBand N)
        (measurableSet_soninExhaustingBand N)).eq
  have hTT : T (T h) = T h := by
    have := congrArg (fun S : SoninL2 →L[ℂ] SoninL2 => S h) hidem
    simpa using this
  have hsym := indicatorCutoff_symmetric (soninExhaustingBand N)
    (measurableSet_soninExhaustingBand N)
  have hinner : inner ℂ (T h) (T h) = inner ℂ (T h) h := by
    calc
      inner ℂ (T h) (T h) = inner ℂ (T (T h)) h := (hsym (T h) h).symm
      _ = inner ℂ (T h) h := by rw [hTT]
  have hzero : inner ℂ (T h) h = 0 := horth (T h) ⟨N, hTT⟩
  have hnorm : inner ℂ (T h) (T h) = 0 := by rw [hinner, hzero]
  exact inner_self_eq_zero.mp hnorm

end RHTower
