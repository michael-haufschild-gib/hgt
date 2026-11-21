import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.GaussianLaw

/-! # Separation between the actual first waits after one complexity crossing -/
open Filter MeasureTheory Topology Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section
open PrecisionReturns

private theorem separate_waits {u v : ℝ → ℝ} {d : ℕ} {B K b : ℝ}
    (hB : 0 < B) (hd : (d:ℝ) < 2*b)
    (hu : ∀ ε ∈ Ioc 0 B, 0≤u ε ∧ 0≤v ε ∧ (u ε)^2*ε^d ≤ K)
    (hv : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 b))
    {R : ℝ} (hR : 0 < R) : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), R*u ε < v ε := by
  let q := (2*b+(d:ℝ))/4
  have hqb : q < b := by dsimp only [q]; linarith only [hd]
  have hq : 0 < q := by dsimp only [q]; linarith only [hd,Nat.cast_nonneg (α := ℝ) d]
  have hgap : 0 < 2*q-(d:ℝ) := by dsimp only [q]; linarith only [hd]
  have hc := (tendsto_const_div_log_one_div (log K+2*log R)).eventually_lt_const hgap
  filter_upwards [hv.eventually_const_lt hqb,hc,Ioo_mem_nhdsGT (lt_min hB zero_lt_one)] with ε hvε hcε he
  have hε := he.1
  have hε' := he.2.trans_le (min_le_right B 1)
  obtain ⟨hu0,hv0,hupper⟩ := hu ε ⟨hε,(he.2.trans_le (min_le_left B 1)).le⟩
  have hlog := log_pos ((one_lt_div hε).mpr hε')
  have hl := (lt_div_iff₀ hlog).mp hvε
  have hl' := (div_lt_iff₀ hlog).mp hcε
  have hv' : 0 < v ε := by
    rcases hv0.eq_or_lt with h|h
    · rw [←h,Real.log_zero] at hl
      exact ((mul_pos hq hlog).asymm hl).elim
    · exact h
  rcases hu0.eq_or_lt with h|h
  · simpa only [←h,mul_zero] using hv'
  have hpos := mul_pos (sq_pos_of_pos h) (pow_pos hε d)
  have hh := log_le_log hpos hupper
  rw [log_mul (sq_pos_of_pos h).ne' (pow_pos hε d).ne',log_pow,log_pow,Nat.cast_ofNat] at hh
  apply (log_lt_log_iff (mul_pos hR h) hv').mp
  rw [log_mul hR.ne' h.ne']
  rw [one_div,Real.log_inv] at hl hl'
  linarith only [hh,hl,hl']

/-- For every factor R the first quadratic-budget wait is eventually less
than 1/R of the first wait at any budget leaving a qubit untouched.
Both minima start at the very same first near-Hilbert crossing. -/
theorem gaussian_first_wait_separation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let S := (Fintype.card (PathLabel (k+1))+1)^2*9
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ s : ℕ, 2*s < N → ∀ R > (0:ℝ), ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
          R*(firstVisit H σ S ε-σ) < firstVisit H σ s ε-σ := by
  filter_upwards [gaussian_quadratic_first_crossing] with ω hw
  filter_upwards [hw] with k hk
  intro N H S P
  obtain ⟨σ,hσ,he,hbefore,⟨B,hB,K,_,h⟩,hsmall⟩ := hk
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro s hs R hR
  let D : ℕ := 2^N
  have hdim : 3≤D := (by decide : 3≤2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp only [N]; omega))
  have hgap : ((2*D-5:ℕ):ℝ) < 2*((D-2:ℕ):ℝ) := by exact_mod_cast (show 2*D-5 < 2*(D-2) by omega)
  apply separate_waits (K := K) hB hgap _ (hsmall s hs) hR
  intro ε hε
  exact ⟨sub_nonneg.mpr (firstVisit_isLeast H σ S hε.1).1.1,sub_nonneg.mpr (firstVisit_isLeast H σ s hε.1).1.1,h ε hε⟩

#print axioms gaussian_first_wait_separation
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
