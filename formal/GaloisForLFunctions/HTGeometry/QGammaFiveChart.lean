import GaloisForLFunctions.HTGeometry.ConstitutiveQGammaProcess

/-!
# Reconstruction of the nome from every q-Gamma chart

The atomic support of the q-Gamma law is strictly decreasing, so its largest point is
`x_0 = −log(1−q)` and the nome is recovered by `q = 1 − exp(−x_0)`.  Consequently the probability
law, its characteristic function, and the germ of the exponential response at the origin each
determine the nome: the law by its largest atom, the characteristic function by Fourier
uniqueness, and the germ by analytic continuation inside the strip `−1/2 < Re s < 2`, which
carries the whole imaginary axis and hence the characteristic function.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

noncomputable section

/-! ## The atom order -/

theorem RealEulerNome.ext' {q q' : RealEulerNome} (h : q.val = q'.val) : q = q' := by
  cases q
  cases q'
  simp only [RealEulerNome.mk.injEq]
  exact h

theorem qGammaAtom_zero (q : RealEulerNome) :
    qGammaAtom q 0 = -Real.log (1 - q.val) := by
  rw [qGammaAtom]
  simp

/-- The atoms strictly decrease, because `log q < 0`. -/
theorem qGammaAtom_strictAnti (q : RealEulerNome) : StrictAnti (qGammaAtom q) := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  have hlog : Real.log q.val < 0 := Real.log_neg q.pos q.lt_one
  rw [qGammaAtom, qGammaAtom]
  push_cast
  nlinarith

/-- **Equation (5).**  `x_0` is the largest atom. -/
theorem qGammaAtom_le_zero (q : RealEulerNome) (n : ℕ) :
    qGammaAtom q n ≤ qGammaAtom q 0 :=
  (qGammaAtom_strictAnti q).antitone (Nat.zero_le n)

/-- **Equation (6).**  The nome is recovered from the largest atom. -/
theorem nome_eq_one_sub_exp_neg (q : RealEulerNome) :
    q.val = 1 - Real.exp (-(qGammaAtom q 0)) := by
  have h1 : (0 : ℝ) < 1 - q.val := by
    have := q.lt_one
    linarith
  rw [qGammaAtom_zero, neg_neg, Real.exp_log h1]
  ring

theorem nome_eq_of_atom_zero_eq {q q' : RealEulerNome}
    (h : qGammaAtom q 0 = qGammaAtom q' 0) : q = q' := by
  apply RealEulerNome.ext'
  rw [nome_eq_one_sub_exp_neg q, nome_eq_one_sub_exp_neg q', h]

/-! ## The probability chart -/

/-- **Equation (2), law form.**  The atomic q-Gamma probability law on `ℝ`. -/
def qLaw (q : RealEulerNome) : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (qGammaWeight q n) • Measure.dirac (qGammaAtom q n)

theorem qLaw_apply (q : RealEulerNome) {s : Set ℝ} (hs : MeasurableSet s) :
    qLaw q s = ∑' n : ℕ, ENNReal.ofReal (qGammaWeight q n) * Measure.dirac (qGammaAtom q n) s := by
  rw [qLaw, Measure.sum_apply _ hs]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, smul_eq_mul]

theorem qLaw_univ (q : RealEulerNome) : qLaw q Set.univ = 1 := by
  rw [qLaw_apply q MeasurableSet.univ]
  have hone : ∀ n : ℕ, Measure.dirac (qGammaAtom q n) Set.univ = 1 := fun n => measure_univ
  simp only [hone, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (qGammaWeight_pos q n).le)
      (qGammaWeight_summable q), (qGammaWeight_hasSum_one q).tsum_eq, ENNReal.ofReal_one]

instance isProbabilityMeasure_qLaw (q : RealEulerNome) : IsProbabilityMeasure (qLaw q) :=
  ⟨qLaw_univ q⟩

theorem qLaw_singleton (q : RealEulerNome) (a : ℝ) :
    qLaw q {a} = ∑' n : ℕ,
      if qGammaAtom q n = a then ENNReal.ofReal (qGammaWeight q n) else 0 := by
  rw [qLaw_apply q (measurableSet_singleton a)]
  refine tsum_congr fun n => ?_
  rw [Measure.dirac_apply, Set.indicator_apply]
  by_cases h : qGammaAtom q n = a
  · rw [if_pos (Set.mem_singleton_iff.mpr h), Pi.one_apply, mul_one, if_pos h]
  · rw [if_neg (fun hm => h (Set.mem_singleton_iff.mp hm)), mul_zero, if_neg h]

theorem qLaw_singleton_atom (q : RealEulerNome) (k : ℕ) :
    qLaw q {qGammaAtom q k} = ENNReal.ofReal (qGammaWeight q k) := by
  rw [qLaw_singleton]
  rw [tsum_eq_single k (fun n hn => if_neg (fun h => hn (qGammaAtom_injective q h)))]
  rw [if_pos rfl]

theorem qLaw_singleton_eq_zero (q : RealEulerNome) {a : ℝ}
    (ha : ∀ n : ℕ, qGammaAtom q n ≠ a) : qLaw q {a} = 0 := by
  rw [qLaw_singleton]
  have hzero : ∀ n : ℕ,
      (if qGammaAtom q n = a then ENNReal.ofReal (qGammaWeight q n) else 0) = 0 :=
    fun n => if_neg (ha n)
  simp only [hzero, tsum_zero]

/-- The largest atom of the law is monotone under equality of laws. -/
private theorem atom_zero_le_of_qLaw_eq {q q' : RealEulerNome} (h : qLaw q = qLaw q') :
    qGammaAtom q 0 ≤ qGammaAtom q' 0 := by
  by_contra hcon
  have hlt : qGammaAtom q' 0 < qGammaAtom q 0 := not_le.mp hcon
  have h0 : qLaw q' {qGammaAtom q 0} = 0 := by
    refine qLaw_singleton_eq_zero q' fun n hn => ?_
    have hle := qGammaAtom_le_zero q' n
    rw [hn] at hle
    exact absurd hle (not_le.mpr hlt)
  rw [← h, qLaw_singleton_atom] at h0
  exact (ENNReal.ofReal_pos.mpr (qGammaWeight_pos q 0)).ne' h0

/-- **Chart 2 determines the parameter**: the law reconstructs the nome from its largest atom. -/
theorem nome_eq_of_qLaw_eq {q q' : RealEulerNome} (h : qLaw q = qLaw q') : q = q' :=
  nome_eq_of_atom_zero_eq
    (le_antisymm (atom_zero_le_of_qLaw_eq h) (atom_zero_le_of_qLaw_eq h.symm))

/-! ## The characteristic chart -/

theorem integrable_qCharKernel (q : RealEulerNome) (t : ℝ) :
    Integrable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) (qLaw q) := by
  have hmeas : Measurable fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_const (1 : ℝ)).mono ?_
  filter_upwards with x
  have hre : ((t : ℂ) * (x : ℂ) * Complex.I).re = 0 := by
    simp
  rw [Complex.norm_exp, hre, Real.exp_zero]
  simp

/-- **Equation (2).**  The characteristic function of the law is the q-Gamma characteristic
process. -/
theorem charFun_qLaw (q : RealEulerNome) (t : ℝ) : charFun (qLaw q) t = qChar q t := by
  have hint : Integrable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (Measure.sum fun n : ℕ =>
        ENNReal.ofReal (qGammaWeight q n) • Measure.dirac (qGammaAtom q n)) :=
    integrable_qCharKernel q t
  rw [charFun_apply_real, qLaw, integral_sum_measure hint, ← (qChar_hasSum q t).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (qGammaWeight_pos q n).le,
    Complex.real_smul]
  have hcomm : (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ) * Complex.I
      = Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ) := by ring
  rw [hcomm]

/-- **Chart 3 determines the parameter**: Fourier uniqueness. -/
theorem nome_eq_of_qChar_eq {q q' : RealEulerNome} (h : qChar q = qChar q') : q = q' := by
  refine nome_eq_of_qLaw_eq (Measure.ext_of_charFun ?_)
  funext t
  rw [charFun_qLaw, charFun_qLaw, h]

/-! ## The analytic germ chart -/

theorem differentiableOn_qResponseFun (q : RealEulerNome) :
    DifferentiableOn ℂ (qResponseFun q) qStrip :=
  fun _ hs => ((hasDerivAt_qResponseFun q hs).differentiableAt).differentiableWithinAt

theorem analyticOnNhd_qResponseFun (q : RealEulerNome) :
    AnalyticOnNhd ℂ (qResponseFun q) qStrip :=
  (differentiableOn_qResponseFun q).analyticOnNhd isOpen_qStrip

theorem mem_qStrip_zero : (0 : ℂ) ∈ qStrip := by
  constructor <;> norm_num

theorem mem_qStrip_I_mul (t : ℝ) : Complex.I * (t : ℂ) ∈ qStrip := by
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
  constructor <;> rw [hre] <;> norm_num

theorem qChar_eq_qResponseFun (q : RealEulerNome) (t : ℝ) :
    qChar q t = qResponseFun q (Complex.I * (t : ℂ)) := by
  rw [qChar, qResponseFun_eq q (s := Complex.I * (t : ℂ)) (by simp)]

/-- **Chart 5 determines the parameter**: the germ of the response at the origin continues
analytically across the strip, which carries the whole imaginary axis. -/
theorem nome_eq_of_response_germ_eq {q q' : RealEulerNome}
    (h : qResponseFun q =ᶠ[𝓝 0] qResponseFun q') : q = q' := by
  have hEq : Set.EqOn (qResponseFun q) (qResponseFun q') qStrip :=
    (analyticOnNhd_qResponseFun q).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_qResponseFun q') convex_qStrip.isPreconnected mem_qStrip_zero h
  refine nome_eq_of_qChar_eq ?_
  funext t
  rw [qChar_eq_qResponseFun, qChar_eq_qResponseFun]
  exact hEq (mem_qStrip_I_mul t)

/-! ## Four-chart rigidity -/

/-- **Corollary 4.1, charts 1, 2, 3 and 5.**  Parameter, probability law, characteristic process
and analytic germ determine one another. -/
theorem qGamma_fourChart_tfae (q q' : RealEulerNome) :
    List.TFAE
      [q = q',
       qLaw q = qLaw q',
       qChar q = qChar q',
       qResponseFun q =ᶠ[𝓝 0] qResponseFun q'] := by
  tfae_have 1 → 2 := fun h => by rw [h]
  tfae_have 2 → 3 := fun h => nome_eq_of_qLaw_eq h ▸ rfl
  tfae_have 3 → 4 := fun h => nome_eq_of_qChar_eq h ▸ EventuallyEq.rfl
  tfae_have 4 → 1 := fun h => nome_eq_of_response_germ_eq h
  tfae_finish

end

end GaloisForLFunctions.HTGeometry
