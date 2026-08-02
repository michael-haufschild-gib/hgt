import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFullTranslationFreeness

/-!
# Functional-equation-even moving canonical product

The symmetric product is defined exactly as `F_θ(z) F_θ(-z)` and identified with

`∏ j, (1 - z² / Λ_j(θ)²)`.

This file proves entirety, evenness, Schwarz reality, an order-one envelope, exact simple divisor
`{±Λ_j(θ)}`, the Herglotz and odd properties of its carrier, and the literal negative
logarithmic-derivative identity.  Together with `MovingEvenCanonicalFullTranslationFreeness`, these
are the unsurgered claims of the functional-equation-even strengthening.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology
open scoped ComplexConjugate

noncomputable section
set_option maxHeartbeats 2000000

def movingEvenCanonicalProduct
    (θ : BoundedRealSequence) (z : ℂ) : ℂ :=
  movingCanonicalProduct θ z * movingCanonicalProduct θ (-z)

theorem movingEvenCanonicalProduct_eq_tprod
    (θ : BoundedRealSequence) (z : ℂ) :
    movingEvenCanonicalProduct θ z =
      ∏' n : ℕ, (1 -
        z ^ 2 / (movingCanonicalZero θ n : ℂ) ^ 2) := by
  have hmulPos : Multipliable (fun n =>
      RHTower.weierstrassE1
        (z / (movingCanonicalZero θ n : ℂ))) :=
    (RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ)
      |>.multipliableLocallyUniformlyOn).multipliable (Set.mem_univ z)
  have hmulNeg : Multipliable (fun n =>
      RHTower.weierstrassE1
        ((-z) / (movingCanonicalZero θ n : ℂ))) :=
    (RHTower.canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ)
      |>.multipliableLocallyUniformlyOn).multipliable (Set.mem_univ (-z))
  change
    (∏' n, RHTower.weierstrassE1
      (z / (movingCanonicalZero θ n : ℂ))) *
    (∏' n, RHTower.weierstrassE1
      ((-z) / (movingCanonicalZero θ n : ℂ))) = _
  rw [← hmulPos.tprod_mul hmulNeg]
  apply tprod_congr
  intro n
  have ha : (movingCanonicalZero θ n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (movingCanonicalZero_pos θ n))
  rw [RHTower.weierstrassE1, RHTower.weierstrassE1]
  let x : ℂ := z / (movingCanonicalZero θ n : ℂ)
  calc
    (1 - z / (movingCanonicalZero θ n : ℂ)) *
          Complex.exp (z / (movingCanonicalZero θ n : ℂ)) *
        ((1 - -z / (movingCanonicalZero θ n : ℂ)) *
          Complex.exp (-z / (movingCanonicalZero θ n : ℂ))) =
        (1 - x) * (1 + x) *
          (Complex.exp x * Complex.exp (-x)) := by
            simp only [x]
            ring_nf
    _ = (1 - x) * (1 + x) := by
      rw [← Complex.exp_add]
      simp
    _ = 1 - z ^ 2 /
        (movingCanonicalZero θ n : ℂ) ^ 2 := by
      simp only [x]
      field_simp [ha]
      ring_nf

theorem movingEvenCanonicalProduct_analytic
    (θ : BoundedRealSequence) :
    AnalyticOnNhd ℂ (movingEvenCanonicalProduct θ) Set.univ := by
  have hF := movingCanonicalProduct_analytic θ
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -z) Set.univ := by
    intro z hz
    fun_prop
  exact hF.mul (hF.comp hneg (by simp))

theorem movingEvenCanonicalProduct_even
    (θ : BoundedRealSequence) (z : ℂ) :
    movingEvenCanonicalProduct θ (-z) =
      movingEvenCanonicalProduct θ z := by
  simp [movingEvenCanonicalProduct, mul_comm]

theorem movingEvenCanonicalProduct_conj
    (θ : BoundedRealSequence) (z : ℂ) :
    movingEvenCanonicalProduct θ (conj z) =
      conj (movingEvenCanonicalProduct θ z) := by
  change movingCanonicalProduct θ (conj z) *
      movingCanonicalProduct θ (-(conj z)) =
    conj (movingCanonicalProduct θ z *
      movingCanonicalProduct θ (-z))
  rw [movingCanonicalProduct_conj]
  have harg : -(conj z) = conj (-z) := by simp
  rw [harg, movingCanonicalProduct_conj]
  exact map_mul (starRingEnd ℂ)
    (movingCanonicalProduct θ z)
    (movingCanonicalProduct θ (-z)) |>.symm

theorem movingEvenCanonicalProduct_orderOneEnvelope
    (θ : BoundedRealSequence) :
    OrderOneEnvelope (movingEvenCanonicalProduct θ) := by
  obtain ⟨C, hC, hbound⟩ :=
    movingCanonicalProduct_orderOneEnvelope θ
  refine ⟨2 * C, by positivity, fun z => ?_⟩
  rw [movingEvenCanonicalProduct, norm_mul]
  calc
    ‖movingCanonicalProduct θ z‖ *
          ‖movingCanonicalProduct θ (-z)‖ ≤
        Real.exp (orderOneWeight C z) *
          Real.exp (orderOneWeight C (-z)) :=
      mul_le_mul (hbound z) (hbound (-z))
        (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp
        (orderOneWeight C z + orderOneWeight C (-z)) := by
      rw [← Real.exp_add]
    _ = Real.exp (orderOneWeight (2 * C) z) := by
      congr 1
      simp only [orderOneWeight, norm_neg]
      ring_nf

theorem movingEvenCanonicalProduct_eq_zero_iff
    (θ : BoundedRealSequence) (z : ℂ) :
    movingEvenCanonicalProduct θ z = 0 ↔
      ∃ n, z = (movingCanonicalZero θ n : ℂ) ∨
        z = -(movingCanonicalZero θ n : ℂ) := by
  rw [movingEvenCanonicalProduct, mul_eq_zero,
    movingCanonicalProduct_eq_zero_iff,
    movingCanonicalProduct_eq_zero_iff]
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

theorem movingEvenCanonicalProduct_pos_zero_analyticOrderAt
    (θ : BoundedRealSequence) (n : ℕ) :
    analyticOrderAt (movingEvenCanonicalProduct θ)
      (movingCanonicalZero θ n : ℂ) = 1 := by
  let a : ℂ := movingCanonicalZero θ n
  have hF : AnalyticAt ℂ (movingCanonicalProduct θ) a :=
    movingCanonicalProduct_analytic θ a (Set.mem_univ _)
  have hFneg : AnalyticAt ℂ
      (fun z => movingCanonicalProduct θ (-z)) a := by
    exact (movingCanonicalProduct_analytic θ (-a) (Set.mem_univ _)).comp
      (by fun_prop)
  have hne : movingCanonicalProduct θ (-a) ≠ 0 := by
    rw [Ne, movingCanonicalProduct_eq_zero_iff]
    push Not
    intro j
    have hpos := movingCanonicalZero_pos θ j
    have hposn := movingCanonicalZero_pos θ n
    intro h
    have hre := congrArg Complex.re h
    simp [a] at hre
    linarith
  change analyticOrderAt
      (fun z => movingCanonicalProduct θ z *
        movingCanonicalProduct θ (-z)) a = 1
  rw [show (fun z => movingCanonicalProduct θ z *
      movingCanonicalProduct θ (-z)) =
      movingCanonicalProduct θ *
        (fun z => movingCanonicalProduct θ (-z)) by rfl,
    analyticOrderAt_mul hF hFneg,
    hFneg.analyticOrderAt_eq_zero.mpr hne]
  rw [show analyticOrderAt (movingCanonicalProduct θ) a = 1 by
    simpa [a] using movingCanonicalProduct_zero_analyticOrderAt θ n]
  rfl

theorem movingEvenCanonicalProduct_neg_zero_analyticOrderAt
    (θ : BoundedRealSequence) (n : ℕ) :
    analyticOrderAt (movingEvenCanonicalProduct θ)
      (-(movingCanonicalZero θ n : ℂ)) = 1 := by
  let F : ℂ → ℂ := movingCanonicalProduct θ
  let g : ℂ → ℂ := fun z => -z
  have hg : AnalyticAt ℂ g (-(movingCanonicalZero θ n : ℂ)) := by
    fun_prop
  have hg' : deriv g (-(movingCanonicalZero θ n : ℂ)) ≠ 0 := by
    simp [g]
  have hcomp :=
    analyticOrderAt_comp_of_deriv_ne_zero
      (f := F) hg hg'
  have hF : AnalyticAt ℂ F (-(movingCanonicalZero θ n : ℂ)) :=
    movingCanonicalProduct_analytic θ _ (Set.mem_univ _)
  have hFcomp : AnalyticAt ℂ (F ∘ g)
      (-(movingCanonicalZero θ n : ℂ)) :=
    by
      have houter : AnalyticAt ℂ F
          (g (-(movingCanonicalZero θ n : ℂ))) := by
        simpa [F, g] using
          (movingCanonicalProduct_analytic θ
            (movingCanonicalZero θ n : ℂ) (Set.mem_univ _))
      exact houter.comp hg
  have hne : F (-(movingCanonicalZero θ n : ℂ)) ≠ 0 := by
    rw [Ne, movingCanonicalProduct_eq_zero_iff]
    push Not
    intro j
    have hpos := movingCanonicalZero_pos θ j
    have hposn := movingCanonicalZero_pos θ n
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  change analyticOrderAt (fun z => F z * F (-z))
      (-(movingCanonicalZero θ n : ℂ)) = 1
  rw [show (fun z => F z * F (-z)) = F * (F ∘ g) by rfl,
    analyticOrderAt_mul hF hFcomp,
    hF.analyticOrderAt_eq_zero.mpr hne]
  rw [show analyticOrderAt (F ∘ g)
      (-(movingCanonicalZero θ n : ℂ)) =
      analyticOrderAt F (movingCanonicalZero θ n : ℂ) by
    simpa [F, g] using hcomp]
  rw [movingCanonicalProduct_zero_analyticOrderAt]
  rfl

theorem movingEvenCanonicalCarrier_odd
    (θ : BoundedRealSequence) (z : ℂ) :
    movingEvenCanonicalCarrier θ (-z) =
      -movingEvenCanonicalCarrier θ z := by
  simp [movingEvenCanonicalCarrier]

theorem movingEvenCanonicalCarrier_im_nonneg
    (θ : BoundedRealSequence) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (movingEvenCanonicalCarrier θ z).im := by
  let w : ℂ := -(starRingEnd ℂ) z
  have hw : 0 < w.im := by
    simp [w]
    exact hz
  have hzpos := movingCanonicalLogDerivative_im_nonneg θ hz
  have hwpos := movingCanonicalLogDerivative_im_nonneg θ hw
  have href := movingCanonicalLogDerivative_conj θ w
  have harg : (starRingEnd ℂ) w = -z := by
    simp [w]
  rw [harg] at href
  rw [movingEvenCanonicalCarrier, href]
  simp only [Complex.sub_im, Complex.conj_im]
  linarith

theorem logDeriv_movingCanonicalProduct_comp_neg
    (θ : BoundedRealSequence) (z : ℂ) :
    logDeriv (fun w => movingCanonicalProduct θ (-w)) z =
      -logDeriv (movingCanonicalProduct θ) (-z) := by
  rw [logDeriv_apply, deriv_comp_neg, logDeriv_apply]
  ring_nf

theorem neg_logDeriv_movingEvenCanonicalProduct_eq
    (θ : BoundedRealSequence) {z : ℂ}
    (hzpos : ∀ n, z ≠ (movingCanonicalZero θ n : ℂ))
    (hzneg : ∀ n, z ≠ -(movingCanonicalZero θ n : ℂ)) :
    -logDeriv (movingEvenCanonicalProduct θ) z =
      movingEvenCanonicalCarrier θ z := by
  have hFz : movingCanonicalProduct θ z ≠ 0 := by
    rw [Ne, movingCanonicalProduct_eq_zero_iff]
    push Not
    exact hzpos
  have hFnz : movingCanonicalProduct θ (-z) ≠ 0 := by
    rw [Ne, movingCanonicalProduct_eq_zero_iff]
    push Not
    intro n h
    apply hzneg n
    have h' := congrArg Neg.neg h
    simpa using h'
  have hFd : DifferentiableAt ℂ (movingCanonicalProduct θ) z :=
    (movingCanonicalProduct_analytic θ z (Set.mem_univ _)).differentiableAt
  have hFnd : DifferentiableAt ℂ
      (fun w => movingCanonicalProduct θ (-w)) z :=
    (movingCanonicalProduct_analytic θ (-z) (Set.mem_univ _)).differentiableAt.comp
      z (by fun_prop)
  change -logDeriv
      (fun w => movingCanonicalProduct θ w *
        movingCanonicalProduct θ (-w)) z =
    movingEvenCanonicalCarrier θ z
  rw [logDeriv_mul z hFz hFnz hFd hFnd,
    logDeriv_movingCanonicalProduct_comp_neg]
  have hpos := neg_logDeriv_movingCanonicalProduct_eq θ hzpos
  have hneg := neg_logDeriv_movingCanonicalProduct_eq
    (z := -z) θ (fun n h => by
      apply hzneg n
      have h' := congrArg Neg.neg h
      simpa using h')
  rw [movingEvenCanonicalCarrier]
  linear_combination hpos - hneg

theorem movingEvenCanonicalProduct_exactOrderOneDivisor
    (θ : BoundedRealSequence) :
    OrderOneEnvelope (movingEvenCanonicalProduct θ) ∧
      HasExponentOfConvergenceOne
        (fun n => (movingCanonicalZero θ n : ℂ)) ∧
      (∀ n, analyticOrderAt (movingEvenCanonicalProduct θ)
        (movingCanonicalZero θ n : ℂ) = 1) ∧
      ∀ n, analyticOrderAt (movingEvenCanonicalProduct θ)
        (-(movingCanonicalZero θ n : ℂ)) = 1 :=
  ⟨movingEvenCanonicalProduct_orderOneEnvelope θ,
    movingCanonicalZero_hasExponentOfConvergenceOne θ,
    movingEvenCanonicalProduct_pos_zero_analyticOrderAt θ,
    movingEvenCanonicalProduct_neg_zero_analyticOrderAt θ⟩

end

end GaloisForLFunctions.HTGeometry
