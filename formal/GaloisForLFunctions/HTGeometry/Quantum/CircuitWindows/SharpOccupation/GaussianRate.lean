import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.EntropyScale

/-! # Sharp return-occupation exponent for a fixed Gaussian chain -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- Subexponential covering entropy means one factor of N per allowed gate
is negligible relative to Hilbert-space dimension. -/
def subcriticalBudget (s : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => ((n:ℝ)+1)*((s n:ℝ)+1)/(2:ℝ)^n) atTop (𝓝 0)

theorem polynomial_subcritical (m : ℕ) : subcriticalBudget (fun n => n^m) := by
  have h (j : ℕ) := tendsto_pow_const_div_const_pow_of_one_lt j (by norm_num : (1:ℝ)<2)
  have ht := (((h (m+1)).add (h m)).add (h 1)).add (h 0)
  unfold subcriticalBudget
  push_cast
  convert ht using 1
  · funext n
    rw [pow_succ,pow_one,pow_zero]
    ring
  · simp

theorem budget_le_dimension_eventually {s : ℕ → ℕ} (hs : subcriticalBudget s) :
    ∀ᶠ n : ℕ in atTop, s n ≤ 2^n := by
  filter_upwards [hs.eventually_lt_const (zero_lt_one : (0:ℝ)<1)] with n hn
  have hb := (div_lt_iff₀ (by positivity : (0:ℝ)<2^n)).mp hn
  have hc : (s n:ℝ) ≤ (2:ℝ)^n := by
    nlinarith only [hb,Nat.cast_nonneg (α := ℝ) n,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) (s n))]
  exact_mod_cast hc

/-- For every inexpensive gate budget the long-interval fraction of visits
has the same exponential rate as the empty circuit. The time origin, error
and gate schedule can all be chosen on the common full-measure event. -/
theorem gaussian_cheap_occupation_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (s : ℕ → ℕ), subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ l b : ℝ, 0 ≤ l → l < x → x < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j ≤ s N,
          l^D < visitFraction H j (zeroGateArcTolerance x) a T ∧
          visitFraction H j (zeroGateArcTolerance x) a T < b^D := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro s hs x hx l b hl hlx hxb
  obtain ⟨y,hxy,hy⟩ := exists_between (lt_min hxb hx.2)
  have hyb := hy.trans_le (min_le_left ..)
  have hyhalf := hy.trans_le (min_le_right ..)
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance
    ⟨hx.1.le,hx.2.le⟩ ⟨(hx.1.trans hxy).le,hyhalf.le⟩ hxy)
  have hh := enlarged_arc_eventually_lt hs (36+128/δ) y b (hx.1.trans hxy) hyb
  have hN := (tendsto_add_atTop_nat 3).eventually (hh.and (budget_le_dimension_eventually hs))
  filter_upwards [hN] with k hgood
  intro N D H a
  have hD : 0 < D := by dsimp [D]; positivity
  have hu := finite_budget_eventually_lt H (hω k) (s N) hx.1.le hxy hyhalf a (b^D) (by
    have hp : 0 ≤ zeroGateArcDensity (2^N) y :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx.1.trans hxy).le _)
    apply (mul_le_mul_of_nonneg_right (net_envelope_le_exp N (s N) δ hδ hgood.2) hp).trans_lt
    simpa only [zeroGateArcDensity,Nat.cast_pow,Nat.cast_ofNat] using hgood.1)
  have hlow : l^D < zeroGateArcDensity D x := by
    have hpow := pow_lt_pow_left₀ hlx hl hD.ne'
    apply hpow.trans_le
    dsimp [zeroGateArcDensity]
    have hone : (1:ℝ) ≤ D := by exact_mod_cast hD
    calc
      x^D = x*x^(D-1) := by rw [←pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ D)]
      _ ≤ (D:ℝ)*x^(D-1) := mul_le_mul_of_nonneg_right ((hx.2.le.trans (by norm_num : (1/2:ℝ) ≤ 1)).trans hone) (pow_nonneg hx.1.le _)
  have hp := (zero_visitFraction_tendsto H (hω k) ⟨x,hx.1.le,hx.2.le⟩ a).eventually_const_lt hlow
  filter_upwards [hp,hu,eventually_gt_atTop a] with T hLo hHi hT j hj
  exact ⟨hLo.trans_le (visitFraction_mono H (Nat.zero_le j) _ a T hT.le),
    (visitFraction_mono H hj _ a T hT.le).trans_lt hHi⟩

/-- In particular the sharp logarithmic rate holds for every polynomial
gate budget with no assumption on the Gaussian coefficients. -/
theorem gaussian_polynomial_occupation_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : ℕ, ∀ x ∈ Ioo (0:ℝ) (1/2),
      ∀ l b : ℝ, 0 ≤ l → l < x → x < b → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j ≤ N^m,
          l^D < visitFraction H j (zeroGateArcTolerance x) a T ∧
          visitFraction H j (zeroGateArcTolerance x) a T < b^D := by
  filter_upwards [gaussian_cheap_occupation_rate] with ω hw
  exact fun m => hw _ (polynomial_subcritical m)

#print axioms gaussian_cheap_occupation_rate
#print axioms gaussian_polynomial_occupation_rate
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
