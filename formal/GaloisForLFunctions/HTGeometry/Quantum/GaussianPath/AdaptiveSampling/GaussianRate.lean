import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.CircuitVisits
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Exponentially small affordable fraction at every nonzero sampling period -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section
open SharpOccupation

/-- Enlarging a fixed positive arc by any amount absorbs the loss of one
independent phase as the dimension tends to infinity. -/
private theorem deletion_density {y z : ℝ} (hy : 0 ≤ y) (hyz : y < z) :
    ∀ᶠ D : ℕ in atTop, zeroGateArcDensity (D-1) y ≤ zeroGateArcDensity D z := by
  have hz := hy.trans_lt hyz
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hy hz.le) ((div_lt_one hz).mpr hyz)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlim.eventually_lt_const hz)
  filter_upwards [eventually_ge_atTop (M+2)] with D hD
  obtain ⟨d,rfl⟩ : ∃ d, D=d+2 := ⟨D-2,by omega⟩
  have h := (hM d (by omega)).le
  rw [div_pow] at h
  have hp : y^d ≤ z^(d+1) := by
    rw [pow_succ']
    exact (div_le_iff₀ (pow_pos hz _)).mp h
  simp only [zeroGateArcDensity, Nat.add_one_sub_one]
  exact mul_le_mul (by exact_mod_cast (show d+1 ≤ d+2 by omega)) hp (pow_nonneg hy _) (Nat.cast_nonneg _)

/-- For budget D/[q(N+1)], every affine lattice chosen after the draw
obeys the same exponential upper rate as a prescribed clock. -/
theorem gaussian_hilbert_budget :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (q : ℕ), 0 < q → ∀ x ∈ Ioo (0:ℝ) (1/2),
      ∀ b : ℝ, 0 < b → Real.log x+32*Real.log 2/q < Real.log b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a τ : ℝ, τ ≠ 0 → ∀ᶠ M : ℕ in atTop, ∀ j ≤ D/(q*(N+1)),
          (timeLaw a τ M).real (visitSet H j (zeroGateArcTolerance x)) < b^D := by
  filter_upwards [gaussian_adaptive_circuit_bound] with ω hω
  intro q hq x hx b hb hxb
  have hc : ContinuousAt (fun z => Real.log z+32*Real.log 2/q) x :=
    (Real.continuousAt_log hx.1.ne').add continuousAt_const
  have hnear := (hc.eventually_lt_const hxb).and (eventually_lt_nhds hx.2)
  have hright : ∀ᶠ z in 𝓝[>] x, x < z := self_mem_nhdsWithin
  obtain ⟨z,hxz,hzb,hzhalf⟩ := (hright.and (hnear.filter_mono nhdsWithin_le_nhds)).exists
  obtain ⟨y,hxy,hyz⟩ := exists_between hxz
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hyhalf := hyz.trans hzhalf
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance ⟨hx.1.le,hx.2.le⟩
    ⟨(hx.1.trans hxy).le,hyhalf.le⟩ hxy)
  have he := positive_budget_exponent q hq δ z b hδ (hx.1.trans hxz) hb hzb
  have hpow : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hd := hpow.eventually (deletion_density (hx.1.trans hxy).le hyz)
  filter_upwards [(tendsto_add_atTop_nat 3).eventually (he.and hd)] with k hk
  intro N D H a τ hτ
  let s := D/(q*(N+1))
  have hnet : 0 ≤ ((s:ℝ)+1)*((((N:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s := by positivity
  have ht := hω k s x y hx.1.le hxy hyhalf a τ hτ (b^D)
    ((mul_le_mul_of_nonneg_left hk.2 hnet).trans_lt hk.1)
  filter_upwards [ht] with M hm j hj
  apply lt_of_le_of_lt _ hm
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro t ⟨c,hc,C,hC,he⟩
  exact ⟨c,hc,C,hC.trans hj,he⟩

/-- At physical error 1/4 all budgets through D/[32(N+1)] occupy less
than 2⁻ᴰ of sufficiently long samples for every affine clock. -/
theorem gaussian_physical_half_power :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a τ : ℝ, τ ≠ 0 → ∀ᶠ M : ℕ in atTop, ∀ j ≤ D/(32*(N+1)),
        (timeLaw a τ M).real (visitSet H j (1/4)) < (1/2:ℝ)^D := by
  let x : ℝ := 1/12
  have hx : x ∈ Ioo (0:ℝ) (1/2) := by norm_num [x]
  have htol : 1/4 ≤ zeroGateArcTolerance x :=
    (by norm_num [x] : 1/4 ≤ 3*x).trans (three_mul_le_arcTolerance hx.1.le (by norm_num [x]))
  have hlog := Real.log_lt_log (by norm_num [x] : 0 < x*2) (by norm_num [x] : x*2 < 1/2)
  rw [Real.log_mul hx.1.ne' (by norm_num)] at hlog
  have hl : Real.log x+32*Real.log 2/(32:ℕ) < Real.log (1/2) := by
    norm_num only [Nat.cast_ofNat]
    linarith only [hlog]
  filter_upwards [gaussian_hilbert_budget] with ω hw
  filter_upwards [hw 32 (by decide) x hx (1/2) (by norm_num) hl] with k hk
  intro N D H a τ hτ
  filter_upwards [hk a τ hτ] with M hm j hj
  apply lt_of_le_of_lt _ (hm j hj)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro t ⟨c,hc,C,hC,he⟩
  exact ⟨c,hc,C,hC,he.trans htol⟩

#print axioms gaussian_hilbert_budget
#print axioms gaussian_physical_half_power
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
