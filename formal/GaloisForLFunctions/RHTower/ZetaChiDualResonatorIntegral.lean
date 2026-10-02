import GaloisForLFunctions.RHTower.ZetaChiDualCoherentMomentMatrix

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RHTower


/-- A finite physical Dirichlet resonator with its literal complex coefficients. -/
def zetaChiDualResonator (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ a ∈ S, c a * bourgainOscillation (t * Real.log a)

private theorem bourgainOscillation_mul_conj_log_ratio {a q : ℕ}
    (ha : 0 < a) (hq : 0 < q) (t : ℝ) :
    bourgainOscillation (t * Real.log a) * conj (bourgainOscillation (t * Real.log q)) =
      bourgainOscillation (t * Real.log ((a : ℝ) / q)) := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold bourgainOscillation
  rw [← Complex.exp_conj, ← Complex.exp_add, Real.log_div haR hqR]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_mul,
    Complex.ofReal_sub]
  ring

/-- The full square expands into all rational cross frequencies, including its diagonal. -/
theorem zetaChiDualResonator_norm_sq_eq (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ a ∈ S, 0 < a) (t : ℝ) :
    ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * bourgainOscillation (t * Real.log ((a : ℝ) / q)) := by
  have heq : ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ) =
      zetaChiDualResonator S c t * conj (zetaChiDualResonator S c t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [heq]
  unfold zetaChiDualResonator
  simp only [map_sum, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    _ = c a * conj (c q) * (bourgainOscillation (t * Real.log a) *
        conj (bourgainOscillation (t * Real.log q))) := by ring
    _ = _ := by rw [bourgainOscillation_mul_conj_log_ratio (hS a ha) (hS q hq)]

theorem continuous_zetaChiDualCoherentCarrier {s : ℂ} (hs : s.re < 1) (m : ℕ) :
    Continuous (zetaChiDualCoherentCarrier s m) := by
  have hchi : Continuous (fun t : ℝ => zetaChi (s + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hG : Gammaℝ (1 - (s + (t : ℂ) * I)) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simpa using sub_pos.mpr hs
    have hpath : Continuous (fun u : ℝ => s + (u : ℂ) * I) := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => s + (u : ℂ) * I) (x := t)
      (zetaChi_analyticAt hG).continuousAt hpath.continuousAt
  unfold zetaChiDualCoherentCarrier
  apply continuous_finsetSum
  intro n _
  unfold zetaChiDualInteriorAtom bourgainOscillation
  exact continuous_const.mul ((hchi.mul continuous_const).mul (by fun_prop))

/-- The first-moment quadratic form is exactly the actual weighted physical integral. -/
theorem integral_zetaChiDualCoherentCarrier_mul_resonator_sq
    {s : ℂ} (hs : s.re < 1) (m : ℕ) (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ a ∈ S, 0 < a) :
    (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
      zetaChiDualCoherentCarrier s m t * ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) * zetaChiDualCoherentFirstMomentKernel s m a q := by
  have hc (a q : ℕ) : Continuous (fun t : ℝ => c a * conj (c q) *
      (zetaChiDualCoherentCarrier s m t * bourgainOscillation (t * Real.log ((a : ℝ) / q)))) :=
    continuous_const.mul ((continuous_zetaChiDualCoherentCarrier hs m).mul (by
      unfold bourgainOscillation
      fun_prop))
  calc
    _ = ∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
        ∑ a ∈ S, ∑ q ∈ S, c a * conj (c q) *
          (zetaChiDualCoherentCarrier s m t * bourgainOscillation (t * Real.log ((a : ℝ) / q))) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [zetaChiDualResonator_norm_sq_eq S c hS t, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun a _ =>
        (continuous_finsetSum S (fun q _ => hc a q)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro a _
      rw [intervalIntegral.integral_finsetSum (fun q _ => (hc a q).intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const_mul, zetaChiDualCoherentFirstMomentKernel]

/-- Every complete narrow family obeys the physical first-moment energy bound. -/
theorem exists_zetaChi_dual_coherent_resonator_integral_bound
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ Q : ℕ, 0 < Q → ∀ S : Finset ℕ,
      (∀ a ∈ S, 100 * Q ≤ a ∧ a ≤ 101 * Q) → ∀ c : ℕ → ℂ,
      ‖(∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          zetaChiDualCoherentCarrier s m t * ((‖zetaChiDualResonator S c t‖ ^ 2 : ℝ) : ℂ)) -
        (((∑ a ∈ S, ‖c a‖ ^ 2 : ℝ)) : ℂ) *
          (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10), zetaChiDualCoherentCarrier s m t)‖ ≤
        C * (101 * (Q : ℝ) + (5 * (m : ℝ)) ^ 10 / m) * S.card * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaChi_dual_coherent_moment_matrix_bound z hr hz0 hz1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with m hm
  intro s hs Q hQ S hS c
  have hre : |s.re - z.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - z) :
      |s.re - z.re| ≤ dist s z).trans hs
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  rw [integral_zetaChiDualCoherentCarrier_mul_resonator_sq hs1 m S c (by
    intro a ha
    have := (hS a ha).1
    omega)]
  exact hm s hs Q hQ S hS c

end RHTower
