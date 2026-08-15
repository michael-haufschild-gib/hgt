import GaloisForLFunctions.HTGeometry.MovingDivisorProduct

/-!
# The functional-equation-even canonical product of a moving divisor

The symmetric product `E(z) = F(z) F(-z)` of the genus-one canonical product of a moving divisor is
entire, even, Schwarz-real, of exact order one, and has the simple divisor `{±Λ_j(θ)}`.  Its
negative logarithmic derivative is the odd Herglotz carrier `H(z) = L(z) - L(-z)`.
-/

open Complex Filter
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

namespace MovingDivisor

noncomputable section
set_option maxHeartbeats 2000000

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- The functional-equation-even canonical product `F(z) F(-z)`. -/
def evenCanonicalProduct (z : ℂ) : ℂ :=
  D.canonicalProduct θ z * D.canonicalProduct θ (-z)

theorem evenCanonicalProduct_analytic :
    AnalyticOnNhd ℂ (D.evenCanonicalProduct θ) Set.univ := by
  have hF := D.canonicalProduct_analytic θ
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -z) Set.univ := by
    intro z hz
    fun_prop
  exact hF.mul (hF.comp hneg (by simp))

theorem evenCanonicalProduct_even (z : ℂ) :
    D.evenCanonicalProduct θ (-z) = D.evenCanonicalProduct θ z := by
  simp [evenCanonicalProduct, mul_comm]

theorem evenCanonicalProduct_conj (z : ℂ) :
    D.evenCanonicalProduct θ (conj z) = conj (D.evenCanonicalProduct θ z) := by
  change D.canonicalProduct θ (conj z) * D.canonicalProduct θ (-(conj z)) =
    conj (D.canonicalProduct θ z * D.canonicalProduct θ (-z))
  rw [D.canonicalProduct_conj θ]
  have harg : -(conj z) = conj (-z) := by simp
  rw [harg, D.canonicalProduct_conj θ]
  exact map_mul (starRingEnd ℂ) (D.canonicalProduct θ z) (D.canonicalProduct θ (-z)) |>.symm

theorem evenCanonicalProduct_orderOneEnvelope :
    OrderOneEnvelope (D.evenCanonicalProduct θ) := by
  obtain ⟨C, hC, hbound⟩ := D.canonicalProduct_orderOneEnvelope θ
  refine ⟨2 * C, by positivity, fun z => ?_⟩
  rw [evenCanonicalProduct, norm_mul]
  calc
    ‖D.canonicalProduct θ z‖ * ‖D.canonicalProduct θ (-z)‖ ≤
        Real.exp (orderOneWeight C z) * Real.exp (orderOneWeight C (-z)) :=
      mul_le_mul (hbound z) (hbound (-z)) (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (orderOneWeight C z + orderOneWeight C (-z)) := by
      rw [← Real.exp_add]
    _ = Real.exp (orderOneWeight (2 * C) z) := by
      congr 1
      simp only [orderOneWeight, norm_neg]
      ring_nf

theorem evenCanonicalProduct_eq_zero_iff (z : ℂ) :
    D.evenCanonicalProduct θ z = 0 ↔
      ∃ n, z = (D.zero θ n : ℂ) ∨ z = -(D.zero θ n : ℂ) := by
  rw [evenCanonicalProduct, mul_eq_zero, D.canonicalProduct_eq_zero_iff θ,
    D.canonicalProduct_eq_zero_iff θ]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨n, Or.inl hn⟩
    · refine ⟨n, Or.inr ?_⟩
      have h := congrArg Neg.neg hn
      simpa using h
  · rintro ⟨n, hn | hn⟩
    · exact Or.inl ⟨n, hn⟩
    · refine Or.inr ⟨n, ?_⟩
      have h := congrArg Neg.neg hn
      simpa using h

theorem evenCanonicalProduct_pos_zero_analyticOrderAt (n : ℕ) :
    analyticOrderAt (D.evenCanonicalProduct θ) (D.zero θ n : ℂ) = 1 := by
  set A : ℂ := ((D.zero θ n : ℝ) : ℂ) with hA
  have hF : AnalyticAt ℂ (D.canonicalProduct θ) A :=
    D.canonicalProduct_analytic θ A (Set.mem_univ _)
  have hFneg : AnalyticAt ℂ (fun z => D.canonicalProduct θ (-z)) A :=
    (D.canonicalProduct_analytic θ (-A) (Set.mem_univ _)).comp (by fun_prop)
  have hne : D.canonicalProduct θ (-A) ≠ 0 := by
    rw [Ne, D.canonicalProduct_eq_zero_iff θ]
    push Not
    intro j
    have hpos := D.zero_pos θ j
    have hposn := D.zero_pos θ n
    intro h
    have hre := congrArg Complex.re h
    simp [hA] at hre
    linarith
  change analyticOrderAt
      (fun z => D.canonicalProduct θ z * D.canonicalProduct θ (-z)) A = 1
  rw [show (fun z => D.canonicalProduct θ z * D.canonicalProduct θ (-z)) =
      D.canonicalProduct θ * (fun z => D.canonicalProduct θ (-z)) by rfl,
    analyticOrderAt_mul hF hFneg,
    hFneg.analyticOrderAt_eq_zero.mpr hne]
  rw [show analyticOrderAt (D.canonicalProduct θ) A = 1 by
    simpa [hA] using D.canonicalProduct_zero_analyticOrderAt θ n]
  rfl

theorem evenCanonicalProduct_neg_zero_analyticOrderAt (n : ℕ) :
    analyticOrderAt (D.evenCanonicalProduct θ) (-(D.zero θ n : ℂ)) = 1 := by
  set F : ℂ → ℂ := D.canonicalProduct θ with hF0
  set g : ℂ → ℂ := fun z => -z with hg0
  have hg : AnalyticAt ℂ g (-(D.zero θ n : ℂ)) := by fun_prop
  have hg' : deriv g (-(D.zero θ n : ℂ)) ≠ 0 := by simp [hg0]
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := F) hg hg'
  have hF : AnalyticAt ℂ F (-(D.zero θ n : ℂ)) :=
    D.canonicalProduct_analytic θ _ (Set.mem_univ _)
  have hFcomp : AnalyticAt ℂ (F ∘ g) (-(D.zero θ n : ℂ)) := by
    have houter : AnalyticAt ℂ F (g (-(D.zero θ n : ℂ))) := by
      simpa [hF0, hg0] using
        (D.canonicalProduct_analytic θ (D.zero θ n : ℂ) (Set.mem_univ _))
    exact houter.comp hg
  have hne : F (-(D.zero θ n : ℂ)) ≠ 0 := by
    rw [hF0, Ne, D.canonicalProduct_eq_zero_iff θ]
    push Not
    intro j
    have hpos := D.zero_pos θ j
    have hposn := D.zero_pos θ n
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  change analyticOrderAt (fun z => F z * F (-z)) (-(D.zero θ n : ℂ)) = 1
  rw [show (fun z => F z * F (-z)) = F * (F ∘ g) by rfl,
    analyticOrderAt_mul hF hFcomp,
    hF.analyticOrderAt_eq_zero.mpr hne]
  rw [show analyticOrderAt (F ∘ g) (-(D.zero θ n : ℂ)) =
      analyticOrderAt F (D.zero θ n : ℂ) by
    simpa [hF0, hg0] using hcomp]
  rw [hF0, D.canonicalProduct_zero_analyticOrderAt θ n]
  rfl

/-- The odd carrier of the symmetric divisor `±Λ_j(θ)`. -/
def evenCarrier (z : ℂ) : ℂ :=
  D.logDerivative θ z - D.logDerivative θ (-z)

theorem evenCarrier_odd (z : ℂ) :
    D.evenCarrier θ (-z) = -D.evenCarrier θ z := by
  simp [evenCarrier]

theorem logDerivative_conj (z : ℂ) :
    D.logDerivative θ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (D.logDerivative θ z) :=
  realLogDerivative_conj (D.zero θ) z

/-- **The odd carrier is Herglotz on the upper half-plane.** -/
theorem evenCarrier_im_nonneg {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (D.evenCarrier θ z).im := by
  set w : ℂ := -(starRingEnd ℂ) z with hw0
  have hw : 0 < w.im := by
    simp [hw0]
    exact hz
  have hzpos := D.logDerivative_im_nonneg θ hz
  have hwpos := D.logDerivative_im_nonneg θ hw
  have href := D.logDerivative_conj θ w
  have harg : (starRingEnd ℂ) w = -z := by
    simp [hw0]
  rw [harg] at href
  rw [evenCarrier, href]
  simp only [Complex.sub_im, Complex.conj_im]
  linarith

theorem logDeriv_canonicalProduct_comp_neg (z : ℂ) :
    logDeriv (fun w => D.canonicalProduct θ (-w)) z =
      -logDeriv (D.canonicalProduct θ) (-z) := by
  rw [logDeriv_apply, deriv_comp_neg, logDeriv_apply]
  ring_nf

theorem neg_logDeriv_evenCanonicalProduct_eq {z : ℂ}
    (hzpos : ∀ n, z ≠ (D.zero θ n : ℂ))
    (hzneg : ∀ n, z ≠ -(D.zero θ n : ℂ)) :
    -logDeriv (D.evenCanonicalProduct θ) z = D.evenCarrier θ z := by
  have hFz : D.canonicalProduct θ z ≠ 0 := by
    rw [Ne, D.canonicalProduct_eq_zero_iff θ]
    push Not
    exact hzpos
  have hFnz : D.canonicalProduct θ (-z) ≠ 0 := by
    rw [Ne, D.canonicalProduct_eq_zero_iff θ]
    push Not
    intro n h
    apply hzneg n
    have h' := congrArg Neg.neg h
    simpa using h'
  have hFd : DifferentiableAt ℂ (D.canonicalProduct θ) z :=
    (D.canonicalProduct_analytic θ z (Set.mem_univ _)).differentiableAt
  have hFnd : DifferentiableAt ℂ (fun w => D.canonicalProduct θ (-w)) z :=
    (D.canonicalProduct_analytic θ (-z) (Set.mem_univ _)).differentiableAt.comp
      z (by fun_prop)
  change -logDeriv (fun w => D.canonicalProduct θ w * D.canonicalProduct θ (-w)) z =
    D.evenCarrier θ z
  rw [logDeriv_mul z hFz hFnz hFd hFnd, D.logDeriv_canonicalProduct_comp_neg θ]
  have hpos := D.neg_logDeriv_canonicalProduct_eq θ hzpos
  have hneg := D.neg_logDeriv_canonicalProduct_eq (z := -z) θ (fun n h => by
    apply hzneg n
    have h' := congrArg Neg.neg h
    simpa using h')
  rw [evenCarrier]
  linear_combination hpos - hneg

/-- **The symmetric canonical product of a moving divisor has exact order one and the exact simple
divisor `{±Λ_j(θ)}`.** -/
theorem evenCanonicalProduct_exactOrderOneDivisor :
    OrderOneEnvelope (D.evenCanonicalProduct θ) ∧
      HasExponentOfConvergenceOne (fun n => (D.zero θ n : ℂ)) ∧
      (∀ n, analyticOrderAt (D.evenCanonicalProduct θ) (D.zero θ n : ℂ) = 1) ∧
      ∀ n, analyticOrderAt (D.evenCanonicalProduct θ) (-(D.zero θ n : ℂ)) = 1 :=
  ⟨D.evenCanonicalProduct_orderOneEnvelope θ, D.hasExponentOfConvergenceOne θ,
    D.evenCanonicalProduct_pos_zero_analyticOrderAt θ,
    D.evenCanonicalProduct_neg_zero_analyticOrderAt θ⟩

end

end MovingDivisor

end GaloisForLFunctions.HTGeometry
