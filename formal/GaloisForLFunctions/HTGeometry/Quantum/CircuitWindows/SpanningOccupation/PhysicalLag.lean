import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PhysicalDensity
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Translating deep returns into visits of nearly one gate per bond -/
open Filter Set Real MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningOccupation
noncomputable section
open SharpOccupation

/-- A gate fits at the upper budget, and every fit pays the lower count. -/
def densityBand {N : ℕ} (H : selfAdjoint (Register N)) (ε low : ℝ) : Set ℝ :=
  {t | t ∈ visitSet H (N-1) ε ∧ ∀ j : ℕ, t ∈ visitSet H j ε → low ≤ j}

/-- At lag A/(N−1), a single sweep costs O(1/N) in error. Translating
any empty visit at the remaining tolerance puts the minimum cost
between (1−8q)(N−1) and N−1. -/
theorem gaussian_scalar_shift_to_density_band :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Register N) :=
          ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
        let m : ℝ := ((n+1:ℕ):ℝ)
        ∀ v : ℝ, v ∈ visitSet H 0 (1/10-K/m) →
          v+A/m ∈ densityBand H (1/10) ((1-8*q)*m) := by
  obtain ⟨b,hb,hdens⟩ := SpanningDensity.gaussian_spanning_gate_density
  obtain ⟨_,B,_,hB,hmass⟩ := gaussian_path_eventual_coefficient_mass
  filter_upwards [hdens,hmass] with ω hd hm k
  intro q
  let A := π/q^2
  let K := 168*B*A^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨J,hJ⟩ := exists_nat_ge (2*A^2/b)
  refine ⟨A,K,hA,hK,?_⟩
  filter_upwards [hd k,hm,eventually_ge_atTop J] with n hn hbound hnJ
  intro N H m
  let t := A/m
  have hmn : 1 ≤ m := by dsimp only [m]; exact_mod_cast (by omega : 1 ≤ n+1)
  have hmp : 0 < m := zero_lt_one.trans_le hmn
  have ht : 0 < t := div_pos hA hmp
  have hN : ((n+2:ℕ):ℝ) ≤ 2*m := by dsimp [m]; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have hlate : π ≤ |t| * q^2*(n+1:ℕ) := by
    change π ≤ |t| * q^2*m
    rw [abs_of_pos ht]; dsimp only [t,A]
    apply le_of_eq; field_simp [hmp.ne',hq.ne']
  have hscale : t^2*m^2=A^2 := by dsimp only [t]; rw [div_pow,div_mul_cancel₀ _ (sq_pos_of_pos hmp).ne']
  have htprod : t^2*((n+2:ℕ):ℝ)*m ≤ 2*A^2 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (sq_nonneg t)) hmp.le
    nlinarith only [hh,hscale]
  have htshort : t^2*(n+2:ℕ) ≤ b := by
    have hmJ : (J:ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : J ≤ n+1)
    have hh := (div_le_iff₀ hb).mp (hJ.trans hmJ)
    exact (le_of_mul_le_mul_right (htprod.trans (by linarith only [hh])) hmp)
  obtain ⟨r,hmin,hlow,_⟩ := hn t hlate htshort (1/4) (by constructor <;> norm_num)
  let u := pathPauliDisorderShell ω n
  obtain ⟨z,hz,C,hC,he⟩ := BondProducts.bond_sweep_error u t ht.le 1 one_pos
  have hfit : t ∈ visitSet H (n+1) (K/m) := by
    refine ⟨z,hz,C,by simpa using hC.le,he.trans ?_⟩
    simp only [Nat.cast_one,div_one]
    apply (le_div_iff₀ hmp).mpr
    have hh := mul_le_mul_of_nonneg_left hbound.2 (show 0 ≤ t^2*84*m by positivity)
    have hb' := mul_le_mul_of_nonneg_left htprod (show 0 ≤ 84*B by positivity)
    dsimp only [K,u]
    linarith only [hh,hb']
  intro v hv
  constructor
  · obtain ⟨w,hw,Q,hQ,herr⟩ := affordable_add_time H hv hfit
    refine ⟨w,hw,Q,by simpa [N] using hQ,herr.trans ?_⟩
    linarith
  · intro j hj
    have hh := affordable_add_time H (HasProjectiveCircuitApproximation.neg_time H hv) hj
    rw [neg_add_cancel_left] at hh
    obtain ⟨w,hw,Q,hQ,herr⟩ := hh
    have hj' := hmin.2 (show j ∈ {i | HasProjectiveCircuitApproximation N (1/4) i
      (unitaryEvolution H.val t)} from ⟨w,hw,Q,by simpa using hQ,herr.trans (by
        have := div_nonneg hK.le hmp.le; linarith only [this])⟩)
    exact hlow.trans (by exact_mod_cast hj')

#print axioms gaussian_scalar_shift_to_density_band
end
end GaloisForLFunctions.HTGeometry.SpanningOccupation
