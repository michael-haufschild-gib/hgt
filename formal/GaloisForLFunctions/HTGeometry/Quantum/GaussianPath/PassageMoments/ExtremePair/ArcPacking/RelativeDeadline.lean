import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.ExtremePair.ArcPacking.SynchronizedPair
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.ExtremePair.Origin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # The volume bound for the first cheap return from the original crossing -/
open Real Finset Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
open PrecisionReturns SpectralFilling.ReplicaOrders
noncomputable section

/-- From a measured origin a whole extreme-gap period suffices as a clock
increment. Pack half-radius arcs on the remaining distinct phases. -/
theorem packed_first_visit {n : ℕ} (H : selfAdjoint (Register n)) {a : ℝ}
    (ha : 0<a) (hw : 0<circuitHamiltonianSpectralWidth H) (s : ℕ)
    {ε : ℝ} (hε : ε∈Ioo 0 (sqrt 2)) :
    let d : ℕ := 2^n-1
    let r := SharpOccupation.physicalArc ε/2
    firstVisit H a s ε*((d:ℝ)*r^(d-1)) ≤ a+2*π/circuitHamiltonianSpectralWidth H := by
  intro d r
  let W := circuitHamiltonianSpectralWidth H
  let E := H.2.isHermitian.eigenvalues
  obtain ⟨b,_,hb⟩ := exists_mem_eq_sup' univ_nonempty E
  obtain ⟨c,_,hc⟩ := exists_mem_eq_inf' univ_nonempty E
  have he : W=E b-E c := congrArg₂ (·-·) hb hc
  have hbc : c≠b := fun h => hw.ne' (by rwa [h,sub_self] at he)
  let P := 2*π/W
  have hP : 0<P := div_pos two_pi_pos hw
  let m := ⌈a/P⌉₊
  let τ := (m:ℝ)*P
  have hlo : a≤τ := (div_le_iff₀ hP).mp (Nat.le_ceil _)
  have hhi : τ≤a+P := by
    have h := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg ha.le hP.le)).le hP.le
    simpa only [τ,m,add_mul,one_mul,div_mul_cancel₀ _ hP.ne'] using h
  have hclock : τ*(E b-E c)/(2*π)=(m:ℤ) := by
    rw [←he,Int.cast_natCast]
    dsimp only [τ,P]
    field_simp [show W≠0 from hw.ne',pi_ne_zero]
  obtain ⟨hr,hfit⟩ := SharpOccupation.physicalArc_spec hε.1 hε.2
  have hr₀ : 0<r := half_pos hr.1
  have hr₁ : r≤1/4 := by dsimp only [r]; linarith only [hr.2]
  obtain ⟨q,hq,hh,hret⟩ := synchronized_tick H c b hbc τ (m:ℤ) hclock r hr₀ hr₁
  have htol : 2*sin (π*r)=ε := by
    simpa only [r,zeroGateArcTolerance,mul_div_assoc] using hfit
  rw [htol] at hret
  have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
  have hτ : 0≤τ := ha.le.trans hlo
  obtain ⟨z,hz,C,hC,hdist⟩ := hret
  have hv := (firstVisit_isLeast H a s hε.1).2
    ⟨hlo.trans (le_mul_of_one_le_left hτ hq₁),z,hz,C,hC.trans (Nat.zero_le _),hdist⟩
  let μ := (d:ℝ)*r^(d-1)
  have hμ : 0≤μ := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr₀.le _)
  have hμ' : 0<μ := lt_of_le_of_ne hμ (by
    intro he
    change (q:ℝ)≤1/μ at hh
    rw [←he,div_zero] at hh
    exact (Nat.cast_pos.mpr hq).not_ge hh)
  have hp := (le_div_iff₀ hμ').mp hh
  calc
    _ ≤ ((q:ℝ)*τ)*μ := mul_le_mul_of_nonneg_right hv hμ
    _ = τ*((q:ℝ)*μ) := by ring
    _ ≤ τ := mul_le_of_le_one_right hτ hp
    _ ≤ _ := hhi

/-- Relative to any origin at distance at least δ from a circuit budget,
the deadline is independent of the bandwidth. This applies to any date
attaining a positive maximum, using its predecessor budget. -/
theorem packed_at_hard_origin {n : ℕ} (H : selfAdjoint (Register n)) {a δ : ℝ}
    (ha : 0≤a) (hδ : 0<δ) (j s : ℕ) (hh : δ≤orbitCircuitDistance H j a)
    {ε : ℝ} (hε : ε∈Ioo 0 (sqrt 2)) :
    let d : ℕ := 2^n-1
    firstVisit H a s ε*((d:ℝ)*(SharpOccupation.physicalArc ε/2)^(d-1))≤(1+π/δ)*a := by
  intro d
  let W := circuitHamiltonianSpectralWidth H
  have hwidth := width_at_origin H j ha
  have hscale : 2*δ≤a*W := by linarith only [hh,hwidth]
  have hprod : 0<a*W := (mul_pos zero_lt_two hδ).trans_le hscale
  have ha' : 0<a := lt_of_le_of_ne ha (fun hz => by rw [←hz,zero_mul] at hprod; exact hprod.false)
  have hw : 0<W := pos_of_mul_pos_right hprod ha
  have hp : 2*π/W≤(π/δ)*a := by
    apply (div_le_iff₀ hw).mpr
    have h := mul_le_mul_of_nonneg_left hscale (div_pos pi_pos hδ).le
    calc
      _ = (π/δ)*(2*δ) := by field_simp [hδ.ne'] <;> ring
      _ ≤ _ := h
      _ = _ := by ring
  exact (packed_first_visit H ha' hw s hε).trans (by linarith only [hp])

/-- For every sufficiently large frozen prefix the first visit at the
physical tolerance ε pays the reciprocal half-radius arc mass on D−1
distinct phases, measured relative to its own first crossing. -/
theorem gaussian_packed_first_visit :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget K
      let σ := ReturnExcursions.Iterated.crossing H P 0
      let d : ℕ := 2^K-1
      ∀ s : ℕ, ∀ ε∈Ioo (0:ℝ) (sqrt 2),
        firstVisit H σ s ε*((d:ℝ)*(SharpOccupation.physicalArc ε/2)^(d-1)) ≤ (1+80*π/9)*σ := by
  obtain ⟨_,_,h⟩ := gaussian_replica_crossing_deadline
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro K H P σ d s ε hε
  have hc := (hk 0).1.1
  change 0≤σ ∧ 9/80≤orbitCircuitDistance H P σ at hc
  have hbound := packed_at_hard_origin H hc.1 (by norm_num : (0:ℝ)<9/80) P s hc.2 hε
  convert hbound using 1 <;> ring

#print axioms gaussian_packed_first_visit
end
end GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
