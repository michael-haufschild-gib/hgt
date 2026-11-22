import GaloisForLFunctions.HTGeometry.Quantum.MetricIntegerClock
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing

/-! # Metric Weyl cancellation at separated real observation dates -/
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section

/-- Scalar character average at real laboratory dates. -/
def clockCharacterMean (s : ℕ→ℝ) (u : ℝ) (N : ℕ) : ℂ :=
  (N:ℂ)⁻¹ * ∑ j ∈ range N, Complex.exp (((s j*u:ℝ):ℂ)*Complex.I)

/-- Quantizing dates in units 1/M changes every character average
by at most |u|/M, independently of the number of observations. -/
private theorem round_error (s : ℕ→ℝ) (u : ℝ) {M : ℝ} (hM : 0<M) (N : ℕ) :
    ‖clockCharacterMean s u N-clockCharacterMean (fun j => (⌊M*s j⌋:ℝ)) (u/M) N‖≤|u|/M := by
  have hj (j : ℕ) :
      ‖Complex.exp (((s j*u:ℝ):ℂ)*Complex.I)-Complex.exp ((((⌊M*s j⌋:ℝ)*(u/M):ℝ):ℂ)*Complex.I)‖≤|u|/M := by
    apply (norm_exp_ofReal_mul_I_sub_le _ _).trans
    rw [show s j*u-(⌊M*s j⌋:ℝ)*(u/M)=(M*s j-(⌊M*s j⌋:ℝ))*u/M by field_simp; ring,
      abs_div,abs_mul,abs_of_pos hM,abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    apply div_le_div_of_nonneg_right _ hM.le
    exact mul_le_of_le_one_left (abs_nonneg u) (by linarith only [Int.lt_floor_add_one (M*s j)])
  by_cases hn : N=0
  · simp [hn,clockCharacterMean,div_nonneg (abs_nonneg u) hM.le]
  have hp : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [clockCharacterMean,clockCharacterMean,←mul_sub,←sum_sub_distrib,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (N:ℝ)⁻¹*(∑ _j ∈ range N, |u|/M) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun j _ => hj j)) (inv_nonneg.mpr hp.le)
    _ = _ := by simp [hp.ne']

/-- A schedule with unit-separated successive real dates has character
cancellation at almost every frequency. Finer integer clocks approximate
the exact schedule uniformly in prefix length. -/
theorem ae_separated_clock_exp (s : ℕ→ℝ) (hs : ∀ j, s j+1≤s (j+1)) :
    ∀ᵐ u : ℝ, Tendsto (clockCharacterMean s u) atTop (𝓝 0) := by
  let M (m : ℕ) := (m:ℝ)+1
  let b (m j : ℕ) := ⌊M m*s j⌋
  have hm (m : ℕ) : 0<M m := by dsimp [M]; positivity
  have hb (m : ℕ) : Function.Injective (b m) := by
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro j
    have h₁ := mul_le_mul_of_nonneg_left (hs j) (hm m).le
    have h₂ := Int.floor_le (M m*s j)
    have h₃ : 1≤M m := by dsimp [M]; linarith only [Nat.cast_nonneg (α:=ℝ) m]
    apply Int.add_one_le_iff.mp
    apply Int.le_floor.mpr
    push_cast
    dsimp [b]
    linarith only [h₂,h₃,show M m*s j+M m≤M m*s (j+1) by simpa only [mul_add,mul_one] using h₁]
  have htest (m : ℕ) : ∀ᵐ u : ℝ, Tendsto (clockCharacterMean (fun j => (b m j:ℝ)) (u/M m)) atTop (𝓝 0) := by
    have hq : Measure.QuasiMeasurePreserving (fun u : ℝ => (M m)⁻¹*u) volume volume := by
      refine ⟨measurable_const_mul _,?_⟩
      rw [Real.map_volume_mul_left (inv_ne_zero (hm m).ne')]
      exact Measure.smul_absolutelyContinuous
    simpa only [clockCharacterMean,div_eq_inv_mul] using hq.ae (ae_integerClock_exp (b m) (hb m))
  filter_upwards [ae_all_iff.mpr htest] with u hu
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm'⟩ := exists_nat_gt (2*|u|/ε)
  have hsmall : |u|/M m<ε/2 := by
    apply (div_lt_iff₀ (hm m)).mpr
    have hh := (div_lt_iff₀ hε).mp hm'
    dsimp [M]
    nlinarith only [hh,hε]
  filter_upwards [Metric.tendsto_nhds.mp (hu m) (ε/2) (half_pos hε)] with N hN
  rw [dist_zero_right] at hN ⊢
  exact (norm_le_norm_sub_add _ _).trans_lt (add_lt_add_of_le_of_lt (round_error s u (hm m) N) hN
    |>.trans_le (by linarith only [hsmall]))

#print axioms ae_separated_clock_exp
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
