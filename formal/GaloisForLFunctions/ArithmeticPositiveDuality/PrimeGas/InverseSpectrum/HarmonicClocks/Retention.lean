import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Fejer

/-! # Occupation probability retained under simultaneous harmonic tests -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

def windowFejer (v : MissingWave) (t : ℝ) (F : Finset ℕ+) (d : ℕ) :=
  ∑ n ∈ F, occupationProbability v n*‖clockPolynomial d (splitPhase t n)‖^2

theorem windowFejer_le (v : MissingWave) (t : ℝ) (F : Finset ℕ+) (d : ℕ) :
    windowFejer v t F d ≤ fejerReading v t d := by
  have h := fejer_hasSum v t d
  exact (h.summable.sum_le_tsum F (fun n _ => mul_nonneg (occupationLaw_nonneg v n) (sq_nonneg _))).trans_eq h.tsum_eq

/-- The finite-window energy error tends to zero uniformly in the chosen sequence of states. -/
theorem windowFejer_error (v : ℕ → MissingWave) {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0))
    (F : Finset ℕ+) (d : ℕ) :
    Tendsto (fun j => (d:ℝ)^2*windowMass (v j) F-windowFejer (v j) (t j) F d) atTop (𝓝 0) := by
  have hterm (n : ℕ+) : Tendsto (fun j => occupationProbability (v j) n*
      ((d:ℝ)^2-‖clockPolynomial d (splitPhase (t j) n)‖^2)) atTop (𝓝 0) := by
    have h := ((clockPolynomial_limit ht n d).norm.pow 2)
    rw [Complex.norm_natCast] at h
    apply squeeze_zero_norm (a := fun j => ‖(d:ℝ)^2-‖clockPolynomial d (splitPhase (t j) n)‖^2‖)
    · intro j
      rw [norm_mul,Real.norm_of_nonneg (occupationLaw_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (occupationLaw_le_one _ _)
    · have he : Tendsto (fun j => ‖(d:ℝ)^2-‖clockPolynomial d (splitPhase (t j) n)‖^2‖)
          atTop (𝓝 ‖(d:ℝ)^2-(d:ℝ)^2‖) := (h.const_sub ((d:ℝ)^2)).norm
      rw [sub_self,norm_zero] at he
      exact he
  have h := tendsto_finsetSum F (fun n _ => hterm n)
  simpa only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,windowMass,windowFejer,
    Finset.sum_const_zero,mul_comm ((d:ℝ)^2)] using h

theorem harmonic_window_bound {r : ℕ+} {δ : ℝ} {v : ℕ → MissingWave} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hc : ∀ j, harmonicTest r δ (v j) (t j))
    (F : Finset ℕ+) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, windowMass (v j) F < retentionCeiling r δ+ε := by
  have hr : 0 < (r.val:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr r.pos)
  filter_upwards [(windowFejer_error v ht F r.val).eventually_lt_const (mul_pos hr hε)] with j hj
  have hb := (windowFejer_le (v j) (t j) F r.val).trans (fejer_bound (hc j) _ le_rfl)
  rw [← retentionCeiling_mul_sq] at hb
  refine lt_of_mul_lt_mul_left ?_ hr.le
  rw [mul_add]
  linarith only [hb,hj]

/-- Nonnegative occupation arrays with total mass at most q. -/
def retainedAt (q : ℝ) (m : ℕ+ → ℝ) : Prop := (∀ n, 0 ≤ m n) ∧ Summable m ∧ ∑' n, m n ≤ q

theorem harmonic_limit_retained {r : ℕ+} {δ : ℝ} {v : ℕ → MissingWave} {t : ℕ → ℝ}
    {m : ℕ+ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (hc : ∀ j, harmonicTest r δ (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) :
    retainedAt (retentionCeiling r δ) m := by
  have hp (n : ℕ+) := ge_of_tendsto (hm n) (Eventually.of_forall fun j => occupationLaw_nonneg (v j) n)
  have hF (F : Finset ℕ+) : ∑ n ∈ F, m n ≤ retentionCeiling r δ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto (tendsto_finsetSum F (fun n _ => hm n))
      ((harmonic_window_bound ht hc F hε).mono fun j hj => hj.le)
  exact ⟨hp,summable_of_sum_le hp hF,le_of_tendsto' (summable_of_sum_le hp hF).hasSum hF⟩

#print axioms windowFejer_le
#print axioms windowFejer_error
#print axioms harmonic_window_bound
#print axioms harmonic_limit_retained

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
