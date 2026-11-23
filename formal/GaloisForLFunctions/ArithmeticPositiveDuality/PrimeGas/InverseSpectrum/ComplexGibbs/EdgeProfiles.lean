import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.RelativePartition

/-! # The two extreme complex partitions and separation of nested spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

theorem relativePartition_hot (r : ℕ) (z : ℂ) : relativePartition (hotEdge r) z = 0 := by
  simp [relativePartition,complexDrop,hotEdge]

/-- The full shift leaves a finite Dirichlet polynomial even below absolute convergence. -/
theorem relativePartition_cold (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    relativePartition (coldEdge r) z = ∑ n ∈ Finset.range r, (occupationWeight n : ℂ) ^ z := by
  let a (n : ℕ) := (occupationWeight n : ℂ) ^ z
  have ha : Tendsto a atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun n => occupationWeight n ^ z.re) atTop (𝓝 ((0:ℝ)^z.re)) :=
      ((Real.continuous_rpow_const hz.le).tendsto 0).comp occupationWeight_tendsto
    simpa only [a,Complex.norm_cpow_eq_rpow_re_of_pos (occupationWeight_pos _),Real.zero_rpow hz.ne'] using ht
  have hpart (N : ℕ) : (∑ n ∈ Finset.range N, complexDrop (coldEdge r) n z) =
      (∑ j ∈ Finset.range r, a j) - ∑ j ∈ Finset.range r, a (N+j) := by
    change (∑ n ∈ Finset.range N, (a n-a (n+r))) = _
    have hn := Finset.sum_range_add a N r
    have hr := Finset.sum_range_add a r N
    rw [Nat.add_comm r N] at hr
    simp only [Nat.add_comm r] at hr
    rw [Finset.sum_sub_distrib]
    linear_combination hr - hn
  have htail := tendsto_finsetSum (Finset.range r) (fun j _ => ha.comp (tendsto_add_atTop_nat j))
  simp only [Finset.sum_const_zero] at htail
  apply tendsto_nhds_unique (summable_complexDrop (coldEdge r) hz).hasSum.tendsto_sum_nat
  simpa only [funext hpart,sub_zero,Function.comp_apply] using
    (tendsto_const_nhds (x := ∑ j ∈ Finset.range r, a j)).sub htail

/-- The complex separation of ordered spectra is bounded by their measured real separation. -/
theorem norm_relativePartition_sub_le {r : ℕ} (b c : SpectralBand r)
    (hbc : ∀ n, (b n).val ≤ (c n).val) (δ : GibbsExponent) {z : ℂ} (hz : δ.val ≤ z.re) :
    ‖relativePartition b z - relativePartition c z‖ ≤ (‖z‖ / δ.val) *
      (relativeReading (powerResponse δ) b - relativeReading (powerResponse δ) c) := by
  let f := powerResponse δ
  have hb := summable_complexDrop b (δ.property.trans_le hz)
  have hc := summable_complexDrop c (δ.property.trans_le hz)
  have hs := (summable_spectralDrop f b).sub (summable_spectralDrop f c)
  have he (n : ℕ) : ‖complexDrop b n z - complexDrop c n z‖ ≤
      (‖z‖ / δ.val) * (spectralDrop f b n - spectralDrop f c n) := by
    have e₁ : complexDrop b n z - complexDrop c n z = ((c n).val : ℂ)^z - ((b n).val : ℂ)^z := by
      unfold complexDrop
      abel
    have e₂ : spectralDrop f b n - spectralDrop f c n = (c n).val^δ.val - (b n).val^δ.val := by
      change (_ - (b n).val^δ.val) - (_ - (c n).val^δ.val) = _
      abel
    rw [e₁,e₂]
    exact norm_thermal_chord (band_pos b n) (hbc n) (band_in_unit c n).2 δ.property hz
  calc
    ‖relativePartition b z - relativePartition c z‖ = ‖∑' n, (complexDrop b n z - complexDrop c n z)‖ := by
      simp only [relativePartition,hb.tsum_sub hc]
    _ ≤ ∑' n, (‖z‖ / δ.val) * (spectralDrop f b n - spectralDrop f c n) :=
      tsum_of_norm_bounded (hs.mul_left _).hasSum he
    _ = _ := by
      rw [tsum_mul_left,(summable_spectralDrop f b).tsum_sub (summable_spectralDrop f c)]
      rfl

#print axioms relativePartition_hot
#print axioms relativePartition_cold
#print axioms norm_relativePartition_sub_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
