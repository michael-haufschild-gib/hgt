import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.RHTower.Sieve.GallagherRange
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import GaloisForLFunctions.RHTower.Sieve.SquarefreeIndicator

/-!
# The isolated diagonal of the short Möbius windows

At bandwidth δ≤1/(M+1) the windows belonging to the first M integers
are disjoint from all later ones. Their diagonal therefore survives
even for a polynomial much longer than the inverse bandwidth. The
squarefree harmonic mass on these sites forces logarithmic growth in
the normalized energy, regardless of cancellation farther out.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
open Finset MeasureTheory Filter Topology _root_.RHTower _root_.RHTower.Sieve
noncomputable section

private theorem window_eq_zero_outside (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ)
    (h : ∀ n∈s, u∉logWindow δ n) : logWindowSum a s δ u=0 := by
  unfold logWindowSum
  apply sum_eq_zero
  intro n hn
  rw [Set.indicator_of_notMem (h n hn),zero_smul]

/-- A gap at the boundary of a prefix separates the two continuum
window energies exactly, for arbitrary complex coefficients. -/
theorem window_energy_split_at_gap (a : ℕ → ℂ) {M N : ℕ} (hm : 1≤M) (hmn : M≤N)
    {δ : ℝ} (hgap : δ≤Real.log (M+1:ℕ)-Real.log M) :
    (∫ u : ℝ, ‖logWindowSum a (Icc 1 N) δ u‖^2)=
      (∫ u : ℝ, ‖logWindowSum a (Icc 1 M) δ u‖^2)+
      ∫ u : ℝ, ‖logWindowSum a (Ioc M N) δ u‖^2 := by
  have hu : Icc 1 M∪Ioc M N=Icc 1 N := by ext n; simp only [mem_union,mem_Icc,mem_Ioc]; omega
  have hd : Disjoint (Icc 1 M) (Ioc M N) := disjoint_left.mpr fun _ hn ht =>
    (not_lt_of_ge (mem_Icc.mp hn).2) (mem_Ioc.mp ht).1
  rw [←integral_add (integrable_normSq_logWindowSum a (Icc 1 M) δ)
    (integrable_normSq_logWindowSum a (Ioc M N) δ)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  have he : logWindowSum a (Icc 1 N) δ u=
      logWindowSum a (Icc 1 M) δ u+logWindowSum a (Ioc M N) δ u := by
    rw [←hu,logWindowSum,sum_union hd]
    rfl
  dsimp only
  rw [he]
  by_cases hl : Real.log M≤u
  · have hx := window_eq_zero_outside a (Icc 1 M) δ u (fun n hn h => by
      have hnm := Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hn).1) (Nat.cast_le.mpr (mem_Icc.mp hn).2)
      exact (not_lt_of_ge (hnm.trans hl)) h.2)
    simp [hx]
  · have hx := window_eq_zero_outside a (Ioc M N) δ u (fun n hn h => by
      have hmn' : (M+1:ℕ)≤n := (mem_Ioc.mp hn).1
      have hl' := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos M)) (Nat.cast_le.mpr hmn')
      have hu' : Real.log n-δ≤u := h.1
      exact hl (by linarith only [hl',hu',hgap]))
    simp [hx]

/-- Exact decomposition into the full squarefree diagonal on the prefix
and a nonnegative tail. Later coefficients cannot cancel this prefix. -/
theorem bandEnergy_isolated_prefix {M N : ℕ} (hm : 1≤M) (hmn : M≤N)
    {δ : ℝ} (hδ : 0≤δ) (hcut : δ≤((M+1:ℕ):ℝ)⁻¹) :
    bandEnergy N δ=δ*(∑ n ∈ Icc 1 M, mobiusRealCoefficient n^2/n)+
      ∫ u : ℝ, ‖logWindowSum (fun n => (coeff n:ℂ)) (Ioc M N) δ u‖^2 := by
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr (Nat.le_succ M))
  have hg := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le (Nat.succ_pos M) hm
    (Nat.succ_ne_self M) le_rfl (Nat.le_succ M)
  rw [abs_of_nonneg (sub_nonneg.mpr hlog)] at hg
  have hc := hcut.trans (inv_anti₀ (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr (Nat.le_succ M)))
  exact (window_energy_split_at_gap (fun n => (coeff n:ℂ)) hm hmn (hcut.trans hg)).trans
    (congrArg (· + ∫ u : ℝ, ‖logWindowSum (fun n => (coeff n:ℂ)) (Ioc M N) δ u‖^2)
      (bandEnergy_diagonal hδ hc))

/-- A resolved prefix of length M forces at least half its logarithm
into the normalized energy at every polynomial length beyond M. -/
theorem normalized_energy_log_lower {M N : ℕ} (hm : 1 ≤ M) (hmn : M ≤ N)
    {T : ℝ} (hT : ((M+1 : ℕ) : ℝ) ≤ T) :
    Real.log ((M : ℝ)+1)/2 ≤ T*bandEnergy N T⁻¹ := by
  classical
  have ht := (Nat.cast_pos.mpr (Nat.succ_pos M)).trans_le hT
  have hcut := inv_anti₀ (Nat.cast_pos.mpr (Nat.succ_pos M)) hT
  have hh := bandEnergy_isolated_prefix hm hmn (inv_nonneg.mpr ht.le) hcut
  have htail : 0 ≤ ∫ u : ℝ, ‖logWindowSum (fun n => (coeff n : ℂ)) (Ioc M N) T⁻¹ u‖^2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hlog : Real.log ((M : ℝ)+1) ≤ ∑ n ∈ Icc 1 M, 1/(n : ℝ) := by
    simpa using (log_sub_le_sum_Icc_one_div (m := 1) (n := M) le_rfl (Nat.succ_le_succ (Nat.zero_le M)))
  have hs := sum_inv_le_two_mul_sum_inv_squarefree M
  have hdiag : (∑ n ∈ (Icc 1 M).filter Squarefree, 1/(n : ℝ)) =
      ∑ n ∈ Icc 1 M, mobiusRealCoefficient n^2/n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    rw [mobiusRealCoefficient, moebius_sq_eq_indicator]
    split <;> simp
  rw [hdiag] at hs
  rw [hh,mul_add,←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
  exact le_add_of_le_of_nonneg (by linarith only [hs,hlog]) (mul_nonneg ht.le htail)

/-- At any lengths and inverse bandwidths that both tend to infinity,
the normalized physical energy itself tends to infinity. -/
theorem normalized_energy_tendsto_atTop {ι : Type*} {l : Filter ι} (N : ι → ℕ) (T : ι → ℝ)
    (hN : Tendsto N l atTop) (hT : Tendsto T l atTop) :
    Tendsto (fun i => T i*bandEnergy (N i) (T i)⁻¹) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨M,hM⟩ := exists_nat_ge (max 1 (Real.exp (2*b)))
  have h₁ : (1 : ℝ) ≤ M := (le_max_left _ _).trans hM
  have hm : 1 ≤ M := by exact_mod_cast h₁
  have he : Real.exp (2*b) ≤ (M : ℝ)+1 :=
    ((le_max_right _ _).trans hM).trans (le_add_of_nonneg_right zero_le_one)
  have hlog := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  filter_upwards [(tendsto_atTop.mp hN) M,(tendsto_atTop.mp hT) ((M+1 : ℕ) : ℝ)] with i hn ht
  exact (show b ≤ Real.log ((M : ℝ)+1)/2 by linarith only [hlog]).trans
    (normalized_energy_log_lower hm hn ht)

#print axioms window_energy_split_at_gap
#print axioms bandEnergy_isolated_prefix
#print axioms normalized_energy_log_lower
#print axioms normalized_energy_tendsto_atTop
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
