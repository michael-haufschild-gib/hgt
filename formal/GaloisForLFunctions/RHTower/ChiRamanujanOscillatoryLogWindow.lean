import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual off-pole prime logarithmic windows

The prime-ordered boundary sums converge by the corpus unconditional PNT
argument. An exact finite Abel identity retains the original cutoff and
transports that convergence through every fixed smooth logarithmic window.
For the exponential window the limit is unchanged; its first logarithmic
response has limit zero. These are actual prime-source limits, with no
oscillation or summability premise. They supply the linear prime terms in
BAG mixed-frequency response and Euler-product asymptotics. This module
does not assert the full labelled source limit or physical signed saving.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RHTower.BAGTrace

/-- The original prime boundary character, including its reciprocal weight. -/
def criticalPrimeBoundaryCoeff (tau : ℝ) (p : ℕ) : ℂ := (p : ℂ)^(-1-(tau : ℂ)*Complex.I)

/-- The literal prime-ordered partial sum on the one-line. -/
def criticalPrimeBoundarySum (tau x : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, criticalPrimeBoundaryCoeff tau p

/-- A logarithmic test of the actual off-pole prime source. -/
def criticalOscillatoryLogWindow (tau : ℝ) (H : ℝ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ Nat.primesLE N, H (Real.log p/Real.log N)*criticalPrimeBoundaryCoeff tau p

private def movingHead (tau : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ Nat.primesLE N, (Ici (Real.log p/Real.log N)).indicator
    (fun _ : ℝ => criticalPrimeBoundaryCoeff tau p) t

private theorem boundary_sum_eq (tau x : ℝ) :
    criticalPrimeBoundarySum tau x = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊ with k.Prime,
      (k : ℂ)^(-1-(tau : ℂ)*Complex.I) := by
  unfold criticalPrimeBoundarySum criticalPrimeBoundaryCoeff
  congr 1
  ext k
  simp [Nat.mem_primesLE]

/-- Off-pole convergence of the original prime-ordered boundary sums. -/
theorem criticalPrimeBoundarySum_tendsto (tau : ℝˣ) :
    ∃ A : ℂ, Tendsto (criticalPrimeBoundarySum tau) atTop (𝓝 A) := by
  obtain ⟨A,hA⟩ := exists_tendsto_primeCpowSum tau.ne_zero
  exact ⟨A,hA.congr (fun x => (boundary_sum_eq tau x).symm)⟩

private theorem boundary_sum_bound {tau : ℝ} {A : ℂ}
    (hA : Tendsto (criticalPrimeBoundarySum tau) atTop (𝓝 A)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖criticalPrimeBoundarySum tau x‖ ≤ C := by
  have hn := hA.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ hn).exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun x => ?_⟩
  have he : criticalPrimeBoundarySum tau x = criticalPrimeBoundarySum tau (⌊x⌋₊ : ℝ) := by
    simp [criticalPrimeBoundarySum]
  rw [he]
  exact (hC _ ⟨⌊x⌋₊,rfl⟩).trans (le_max_left _ _)

private theorem head_eq {N : ℕ} (hN : 2 ≤ N) (tau : ℝ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    movingHead tau N t = criticalPrimeBoundarySum tau ((N : ℝ)^t) := by
  have hN1 : (1 : ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 : (0 : ℝ)<N := lt_trans zero_lt_one hN1
  have hlog : 0<Real.log N := Real.log_pos hN1
  have hpow : (N : ℝ)^t ≤ N := by
    calc _ ≤ (N : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1.le ht.2
      _ = _ := Real.rpow_one _
  have hfloor : ⌊(N : ℝ)^t⌋₊ ≤ N := by
    exact_mod_cast (Nat.floor_le (Real.rpow_nonneg hN0.le t)).trans hpow
  have hs : Nat.primesLE ⌊(N : ℝ)^t⌋₊ =
      (Nat.primesLE N).filter (fun p : ℕ => Real.log p/Real.log N ≤ t) := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter]
    constructor
    · rintro ⟨hpN,hp⟩
      refine ⟨⟨hpN.trans hfloor,hp⟩,?_⟩
      rw [div_le_iff₀ hlog,← Real.le_rpow_iff_log_le (by exact_mod_cast hp.pos) hN0]
      exact (Nat.le_floor_iff (Real.rpow_nonneg hN0.le t)).mp hpN
    · rintro ⟨⟨_,hp⟩,htp⟩
      refine ⟨?_,hp⟩
      rw [div_le_iff₀ hlog,← Real.le_rpow_iff_log_le (by exact_mod_cast hp.pos) hN0] at htp
      exact (Nat.le_floor_iff (Real.rpow_nonneg hN0.le t)).mpr htp
  rw [criticalPrimeBoundarySum,hs,Finset.sum_filter]
  simp [movingHead,Set.indicator,Set.mem_Ici]

private theorem indicator_integral {a : ℝ} (ha0 : 0<a) (ha1 : a≤1) (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, (Ici a).indicator f t) = ∫ t in a..1, f t := by
  have he : Ici a ∩ Ioc (0 : ℝ) 1 = Icc a 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · tauto
    · rintro ⟨hat,ht1⟩
      exact ⟨hat,lt_of_lt_of_le ha0 hat,ht1⟩
  rw [intervalIntegral.integral_of_le zero_le_one,MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,he,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ha1]

private theorem atom_integral (H D : ℝ → ℂ) (hD : Continuous D)
    (hH : ∀ t, HasDerivAt H (D t) t) {a : ℝ} (ha0 : 0<a) (ha1 : a≤1) (b : ℂ) :
    H a*b = H 1*b-∫ t in (0 : ℝ)..1,
      D t*(Ici a).indicator (fun _ : ℝ => b) t := by
  have he (t : ℝ) : D t*(Ici a).indicator (fun _ : ℝ => b) t =
      (Ici a).indicator (fun t => D t*b) t := by
    by_cases ht : t ∈ Ici a <;> simp [ht]
  simp_rw [he]
  rw [indicator_integral ha0 ha1,intervalIntegral.integral_mul_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hH t) (hD.intervalIntegrable a 1)]
  ring

private theorem atom_integrable (D : ℝ → ℂ) (hD : Continuous D) (a : ℝ) (b : ℂ) :
    IntervalIntegrable (fun t => D t*(Ici a).indicator (fun _ : ℝ => b) t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hi := ((hD.mul_const b).intervalIntegrable (μ := volume) (0 : ℝ) 1).1
  convert hi.indicator (measurableSet_Ici (a := a)) using 1
  funext t
  by_cases ht : t ∈ Ici a <;> simp [ht]

private theorem window_abel {N : ℕ} (hN : 2 ≤ N) (tau : ℝ) (H D : ℝ → ℂ)
    (hD : Continuous D) (hH : ∀ t, HasDerivAt H (D t) t) :
    criticalOscillatoryLogWindow tau H N = H 1*criticalPrimeBoundarySum tau N-
      ∫ t in (0 : ℝ)..1, D t*movingHead tau N t := by
  classical
  have hN1 : (1 : ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog : 0<Real.log N := Real.log_pos hN1
  have he (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      H (Real.log p/Real.log N)*criticalPrimeBoundaryCoeff tau p = H 1*criticalPrimeBoundaryCoeff tau p-
        ∫ t in (0 : ℝ)..1, D t*(Ici (Real.log p/Real.log N)).indicator
          (fun _ : ℝ => criticalPrimeBoundaryCoeff tau p) t := by
    have hpp := Nat.prime_of_mem_primesLE hp
    have ha0 : 0<Real.log p/Real.log N := div_pos (Real.log_pos (by exact_mod_cast hpp.one_lt)) hlog
    have ha1 : Real.log p/Real.log N ≤ 1 := by
      rw [div_le_one hlog]
      exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast (Nat.mem_primesLE.mp hp).1)
    exact atom_integral H D hD hH ha0 ha1 _
  unfold criticalOscillatoryLogWindow
  rw [Finset.sum_congr rfl he,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [criticalPrimeBoundarySum,Nat.floor_natCast]
  congr 1
  rw [← intervalIntegral.integral_finsetSum (fun p _ => atom_integrable D hD _ _)]
  apply intervalIntegral.integral_congr
  intro t _
  simp [movingHead,Finset.mul_sum]

private theorem head_measurable (tau : ℝ) (N : ℕ) : StronglyMeasurable (movingHead tau N) := by
  unfold movingHead
  convert (Nat.primesLE N).stronglyMeasurable_sum
    (f := fun p : ℕ => (Ici (Real.log p/Real.log N)).indicator (fun _ : ℝ => criticalPrimeBoundaryCoeff tau p))
    (fun p _ => stronglyMeasurable_const.indicator
      (measurableSet_Ici (a := Real.log p/Real.log N))) using 1
  ext t
  simp only [Finset.sum_apply]

private theorem head_bound {tau : ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖criticalPrimeBoundarySum tau x‖ ≤ C) (N : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖movingHead tau N t‖ ≤ C := by
  by_cases hN : 2 ≤ N
  · rw [head_eq hN tau ht]
    exact hC _
  · have hN' : N=0 ∨ N=1 := by omega
    rcases hN' with rfl | rfl <;> simpa [movingHead] using hC0

private theorem head_tendsto {tau : ℝ} {A : ℂ}
    (hA : Tendsto (criticalPrimeBoundarySum tau) atTop (𝓝 A)) {t : ℝ} (ht : t ∈ Ioc 0 1) :
    Tendsto (fun N : ℕ => movingHead tau N t) atTop (𝓝 A) := by
  have h := hA.comp ((tendsto_rpow_atTop ht.1).comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (head_eq hN tau ⟨ht.1.le,ht.2⟩).symm

private theorem window_tendsto {tau : ℝ} {A : ℂ}
    (hA : Tendsto (criticalPrimeBoundarySum tau) atTop (𝓝 A)) (H D : ℝ → ℂ)
    (hD : Continuous D) (hH : ∀ t, HasDerivAt H (D t) t) :
    Tendsto (criticalOscillatoryLogWindow tau H) atTop (𝓝 (H 0*A)) := by
  obtain ⟨C,hC0,hC⟩ := boundary_sum_bound hA
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun N t => D t*movingHead tau N t) (f := fun t => D t*A)
    (fun t => ‖D t‖*C)
    (fun N => hD.aestronglyMeasurable.mul (head_measurable tau N).aestronglyMeasurable)
    (((hD.norm.mul_const C).intervalIntegrable (0 : ℝ) 1).1)
    (fun N => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (head_bound hC0 hC N ⟨ht.1.le,ht.2⟩) (norm_nonneg _))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (head_tendsto hA ht).const_mul (D t))
  have hlim' : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..1,D t*movingHead tau N t) atTop
      (𝓝 ((H 1-H 0)*A)) := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hH t)
      (hD.intervalIntegrable 0 1),← intervalIntegral.integral_mul_const]
    simpa only [intervalIntegral.integral_of_le zero_le_one] using hlim
  have h := ((hA.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (H 1)).sub hlim'
  have he : H 1*A-(H 1-H 0)*A=H 0*A := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (window_abel hN tau H D hD hH).symm

/-- The actual off-pole prime source is stable under every fixed exponential
logarithmic tilt; its normalized first logarithmic response vanishes. -/
theorem criticalOscillatoryLogWindow_tendsto (tau : ℝˣ) :
    ∃ A : ℂ, ∀ w : ℂ,
      Tendsto (criticalOscillatoryLogWindow tau (fun t => Complex.exp (w*(t : ℂ)))) atTop (𝓝 A) ∧
      Tendsto (criticalOscillatoryLogWindow tau (fun t => (t : ℂ)*Complex.exp (w*(t : ℂ))))
        atTop (𝓝 0) := by
  obtain ⟨A,hA⟩ := criticalPrimeBoundarySum_tendsto tau
  refine ⟨A,fun w => ?_⟩
  have he (t : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (w*(r : ℂ)))
      (Complex.exp (w*(t : ℂ))*w) t := by
    simpa only [id_eq,Complex.ofReal_one,mul_one] using
      (((hasDerivAt_id t).ofReal_comp.const_mul w).cexp)
  have ht (t : ℝ) : HasDerivAt (fun r : ℝ => (r : ℂ)*Complex.exp (w*(r : ℂ)))
      (Complex.exp (w*(t : ℂ))+(t : ℂ)*(Complex.exp (w*(t : ℂ))*w)) t := by
    simpa only [id_eq,Complex.ofReal_one,one_mul,Pi.mul_apply] using!
      ((hasDerivAt_id t).ofReal_comp.mul (he t))
  constructor
  · simpa using window_tendsto hA (fun t => Complex.exp (w*(t : ℂ)))
      (fun t => Complex.exp (w*(t : ℂ))*w) (by fun_prop) he
  · simpa using window_tendsto hA (fun t => (t : ℂ)*Complex.exp (w*(t : ℂ)))
      (fun t => Complex.exp (w*(t : ℂ))+(t : ℂ)*(Complex.exp (w*(t : ℂ))*w)) (by fun_prop) ht

/-- The entire linear Euler-log perturbation vanishes at the moving logarithmic scale. -/
theorem criticalOscillatoryLogWindow_difference_tendsto (tau : ℝˣ) (w : ℂ) :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesLE N,
      (Complex.exp (w*((Real.log p/Real.log N : ℝ) : ℂ))-1)*criticalPrimeBoundaryCoeff tau p)
      atTop (𝓝 0) := by
  obtain ⟨A,hA⟩ := criticalOscillatoryLogWindow_tendsto tau
  have h := ((hA w).1).sub ((hA 0).1)
  simp only [sub_self] at h
  apply h.congr
  intro N
  rw [criticalOscillatoryLogWindow,criticalOscillatoryLogWindow,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [zero_mul,Complex.exp_zero,one_mul]
  ring

end RHTower.BAGTrace
