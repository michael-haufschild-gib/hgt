import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.WeakEdgeSweep

/-! # Error of a physical sweep with a prescribed number of missing bonds -/

open Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section

/-- If the missing gate count is at most K h⁹, a single pruned sweep
has error at most A |t| K h¹⁰ + B K t² at every real time. -/
theorem gaussian_sweep_error :
    ∃ γ>0, ∃ Q>0, ∃ A>0, ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let u := pathPauliDisorderShell ω n
      ∀ h : ℝ, 0<h → h≤γ → Q≤K*h^20 → ∀ d : ℕ, (d:ℝ)≤K*h^9 →
        ∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) (A* |t| * (K*h^10)+B*K*t^2)
          (n+1-d) (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨c,hc,C,hC,hw⟩ := gaussian_weak_edge_counts
  obtain ⟨_,B,_,hB,hbulk⟩ := gaussian_path_eventual_coefficient_mass
  let M := max 1 (1/c)
  have hM : 1≤M := le_max_left ..
  have hm := zero_lt_one.trans_le hM
  have hM9 : 1≤c*M^9 := by
    have he : 1/c≤M^9 := (le_max_right ..).trans (by
      calc M = M^1 := (pow_one _).symm
           _ ≤ _ := pow_le_pow_right₀ hM (by decide))
    have hc' := (div_le_iff₀ hc).mp he
    linarith only [hc']
  refine ⟨1/M,one_div_pos.mpr hm,4*2^20,by norm_num,9*C*M^10,by positivity,84*B,by positivity,?_⟩
  filter_upwards [hw,hbulk] with ω hω hb
  filter_upwards [hω,hb] with n hn hb
  intro K u h hh hγ hQ d hd t
  have hK : 0<K := by dsimp only [K]; positivity
  let y := M*h
  have hy : 0<y := mul_pos hm hh
  have hhy : h≤y := le_mul_of_one_le_left hh.le hM
  have hy' : y≤1 := by
    have hh' := (le_div_iff₀ hm).mp hγ
    change M*h≤1
    linarith only [hh']
  obtain ⟨hl,hu⟩ := hn y hy hy' (hQ.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hh.le hhy 20) hK.le))
  let R := removable u y
  have hsave : d≤R.card := by
    apply (Nat.cast_le (α:=ℝ)).mp
    apply hd.trans (le_trans _ hl)
    calc
      K*h^9 ≤ (c*M^9)*(K*h^9) := le_mul_of_one_le_left (by positivity) hM9
      _ = c*K*y^9 := by dsimp only [y]; ring
  obtain ⟨z,hz,D,hD,hfit⟩ := affordable_after_pruning u y t
  refine ⟨z,hz,D,hD.trans (Nat.sub_le_sub_left hsave _),hfit.trans ?_⟩
  have hs : (R.card:ℝ)≤C*K*y^9 :=
    ((Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card (Finset.filter_subset ..))).trans hu
  have he := mul_le_mul_of_nonneg_left hb.2 (show 0≤84*t^2 by positivity)
  change 84*t^2*‖u‖^2≤84*t^2*(B*K) at he
  have hp := mul_le_mul_of_nonneg_left hs (show 0≤9* |t| * y by positivity)
  change 9* |t| * y*R.card+t^2*(84*‖u‖^2)≤_
  dsimp only [y] at hp
  dsimp only [y,R]
  linarith only [hp,he]

#print axioms gaussian_sweep_error
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
