import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.WeakEdgeSweep

/-! # Uniform gate savings on every initial inverse-size interval -/

open Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section

/-- One fixed weak-edge cutoff saves a positive density of gates
through the entire inverse-size interval, including time zero. -/
theorem gaussian_initial_saving (A : ℝ) (hA : 0<A) :
    ∃ γ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ (t : ℝ), K * |t|≤A → ∀ d : ℕ, (d:ℝ)≤γ*K →
        HasProjectiveCircuitApproximation (n+2) (1/20) ((n+1)-d)
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) := by
  obtain ⟨c,hc,C,hC,hcounts⟩ := gaussian_weak_edge_counts
  obtain ⟨_,B,_,hB,hbulk⟩ := gaussian_path_eventual_coefficient_mass
  let h := min 1 (1/(720*A*C))
  have hh : 0<h := lt_min zero_lt_one (by positivity)
  have h₁ : h≤1 := min_le_left ..
  have hp : 720*A*C*h≤1 := by
    have h' := (le_div_iff₀ (show 0<720*A*C by positivity)).mp (min_le_right (1:ℝ) (1/(720*A*C)))
    linarith only [h']
  have hh₁ : h^9≤1 := pow_le_one₀ hh.le h₁
  refine ⟨c*h^9,mul_pos hc (pow_pos hh _),?_⟩
  have htop : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [hcounts,hbulk] with ω hcω hBω
  filter_upwards [hcω,hBω,htop.eventually (eventually_ge_atTop ((4*2^20)/h^20)),
    htop.eventually (eventually_ge_atTop (10000*B*A^2))] with n hn he hgrid hsize
  intro K t ht d hd
  let u := pathPauliDisorderShell ω n
  let R := removable u h
  have hK : 0<K := by dsimp only [K]; positivity
  obtain ⟨hl,hu⟩ := hn h hh h₁ ((div_le_iff₀ (pow_pos hh 20)).mp hgrid)
  have hsave : d≤R.card := (Nat.cast_le (α:=ℝ)).mp (hd.trans (by
    change c*h^9*K≤(R.card:ℝ)
    change c*K*h^9≤(R.card:ℝ) at hl
    linarith only [hl]))
  have hcount : (R.card:ℝ)≤C*K := by
    have hsub : R.card≤(weakEdges u h).card := Finset.card_le_card (Finset.filter_subset ..)
    exact ((Nat.cast_le.mpr hsub).trans hu).trans
      ((mul_le_mul_of_nonneg_left hh₁ (mul_nonneg hC.le hK.le)).trans_eq (mul_one _))
  have herase : 9 * |t| * h*(R.card:ℝ)≤1/80 := by
    calc
      _ ≤ 9 * |t| * h*(C*K) := mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = (9*h*C)*(K * |t|) := by ring
      _ ≤ (9*h*C)*A := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ _ := by linarith only [hp]
  have henergy : t^2*‖u‖^2≤1/10000 := by
    change 10000*B*A^2≤K at hsize
    have hm := mul_le_mul_of_nonneg_left he.2 (sq_nonneg t)
    change t^2*‖u‖^2≤t^2*(B*K) at hm
    have hsq := pow_le_pow_left₀ (mul_nonneg hK.le (abs_nonneg t)) ht 2
    rw [mul_pow,sq_abs] at hsq
    have hsmall : t^2*(B*K)*K≤(1/10000:ℝ)*K := by
      nlinarith only [mul_le_mul_of_nonneg_left hsq hB.le,hsize]
    exact hm.trans (le_of_mul_le_mul_right hsmall hK)
  obtain ⟨z,hz,D,hD,hfit⟩ := affordable_after_pruning u h t
  exact ⟨z,hz,D,hD.trans (Nat.sub_le_sub_left hsave _),
    hfit.trans (by change 9 * |t| * h*(R.card:ℝ)+t^2*(84*‖u‖^2)≤1/20
                   linarith only [herase,henergy])⟩

#print axioms gaussian_initial_saving
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
