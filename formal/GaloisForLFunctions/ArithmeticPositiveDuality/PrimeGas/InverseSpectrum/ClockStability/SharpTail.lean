import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.DetectorError

/-! # Exact worst-case spectral error beyond a finite cutoff -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

def tailCeiling (f : SpectralResponse) (r N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, (f.value (occupationWeight (N+j)) - f.value 0)

private theorem hasSum_shifted_edge (f : SpectralResponse) (r N : ℕ) :
    HasSum (fun k => spectralDrop f (coldEdge r) (k+N)) (tailCeiling f r N) := by
  let a (n : ℕ) := f.value (occupationWeight (n+N)) - f.value 0
  have ha : Antitone a := fun i j h => sub_le_sub_right
    (f.inc.monotoneOn (occupation_in_unit _) (occupation_in_unit _)
      (occupationWeight_antitone (Nat.add_le_add_right h N))) _
  have h0 : Tendsto (fun k => f.value (occupationWeight k)) atTop (𝓝 (f.value 0)) := (f.cont 0 (show (0:ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨occupationWeight_tendsto,Eventually.of_forall occupation_in_unit⟩)
  have hz : Tendsto a atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => f.value (occupationWeight (n+N))) atTop (𝓝 (f.value 0)) :=
      h0.comp (tendsto_add_atTop_nat N)
    simpa only [a,sub_self] using ht.sub (tendsto_const_nhds (x := f.value 0))
  have hhead : tailCeiling f r N = ∑ j ∈ Finset.range r, a j := by simp only [tailCeiling,a,Nat.add_comm N]
  rw [hhead]
  apply (hasSum_shift_drop ha hz r).congr_fun
  intro n
  change f.value (occupationWeight (n+N)) - f.value (occupationWeight (n+N+r)) =
    (f.value (occupationWeight (n+N))-f.value 0) - (f.value (occupationWeight (n+r+N))-f.value 0)
  rw [Nat.add_right_comm n N r]
  abel

theorem detectorTail_le (f : SpectralResponse) {r : ℕ} (b c : SpectralBand r) (N : ℕ) :
    detectorTail f b c N ≤ tailCeiling f r N := by
  have h := hasSum_shifted_edge f r N
  rw [← h.tsum_eq]
  exact ((summable_nat_add_iff N).mpr (summable_levelError f b c)).tsum_le_tsum
    (fun k => levelError_le_edge f b c (k+N)) h.summable

theorem detectorTail_edges (f : SpectralResponse) (r N : ℕ) :
    detectorTail f (hotEdge r) (coldEdge r) N = tailCeiling f r N := by
  apply HasSum.tsum_eq
  apply (hasSum_shifted_edge f r N).congr_fun
  intro n
  exact abs_of_nonneg (drop_nonneg f (coldEdge r) (n+N))

theorem power_tailCeiling_le (β : GibbsExponent) (r N : ℕ) :
    tailCeiling (powerResponse β) r N ≤ (r:ℝ) * occupationWeight N ^ β.val := by
  calc
    tailCeiling (powerResponse β) r N ≤ ∑ _j ∈ Finset.range r, occupationWeight N ^ β.val := by
      apply Finset.sum_le_sum
      intro j _
      change occupationWeight (N+j)^β.val - (0:ℝ)^β.val ≤ _
      rw [Real.zero_rpow β.property.ne',sub_zero]
      exact Real.rpow_le_rpow (occupationWeight_pos _).le (occupationWeight_antitone (Nat.le_add_right N j)) β.property.le
    _ = _ := by simp

/-- Pairs of actual positive conserving omissions of a prescribed dimension. -/
def physicalTailErrors (f : SpectralResponse) (r N : ℕ) : Set ℝ :=
  {y | ∃ (P Q : Projection) (hP : MissingDimension P r) (cP : Conserving (projected P))
    (hQ : MissingDimension Q r) (cQ : Conserving (projected Q)),
    detectorTail f (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ) N = y}

private theorem lane_has_projection {r : ℕ} (b : SpectralBand r) (hb : b ∈ laneSpectra r) :
    ∃ (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)), physicalSpectrum P hd hc = b := by
  obtain ⟨v,rfl⟩ := hb
  unfold laneSpectrum
  exact ⟨_,_,_,rfl⟩

/-- Every closed relation holding for all physical pairs holds for the simultaneous hot and cold edges. -/
theorem edgePair_mem_closed_of_physical (r : ℕ) {U : Set (SpectralBand (r+1) × SpectralBand (r+1))}
    (hU : IsClosed U) (h : ∀ (P Q : Projection) (hP : MissingDimension P (r+1)) (cP : Conserving (projected P))
      (hQ : MissingDimension Q (r+1)) (cQ : Conserving (projected Q)),
      (physicalSpectrum P hP cP,physicalSpectrum Q hQ cQ) ∈ U) : (hotEdge (r+1),coldEdge (r+1)) ∈ U := by
  let S := laneSpectra (r+1)
  have hsub : S ×ˢ S ⊆ U := by
    rintro ⟨b,c⟩ ⟨hb,hc⟩
    obtain ⟨P,hP,cP,rfl⟩ := lane_has_projection b hb
    obtain ⟨Q,hQ,cQ,rfl⟩ := lane_has_projection c hc
    exact h P Q hP cP hQ cQ
  obtain ⟨hh,hc⟩ := physical_spectral_edges r
  have hedge : (hotEdge (r+1),coldEdge (r+1)) ∈ closure (S ×ˢ S) := by rw [closure_prod_eq]; exact ⟨hh,hc⟩
  exact closure_minimal hsub hU hedge

/-- The interlacing tail bound is the physical supremum, including for cutoffs beyond the first level. -/
theorem physicalTailErrors_isLUB (f : SpectralResponse) (r N : ℕ) :
    IsLUB (physicalTailErrors f (r+1) N) (tailCeiling f (r+1) N) := by
  constructor
  · rintro _ ⟨P,Q,hP,cP,hQ,cQ,rfl⟩
    exact detectorTail_le f _ _ N
  · intro v hv
    have hu := edgePair_mem_closed_of_physical r (isClosed_le (continuous_detectorTail f _ N) (continuous_const (y := v)))
      (fun P Q hP cP hQ cQ => hv ⟨P,Q,hP,cP,hQ,cQ,rfl⟩)
    change detectorTail f (hotEdge (r+1)) (coldEdge (r+1)) N ≤ v at hu
    simpa only [detectorTail_edges] using hu

#print axioms detectorTail_le
#print axioms power_tailCeiling_le
#print axioms physicalTailErrors_isLUB

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
