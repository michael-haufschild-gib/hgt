import GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole
import GaloisForLFunctions.RHTower.PrimeSquareTwoLevelReflectedRigidity


/-!
# Prime and prime-square normal jets give a two-level line classifier

The literal deletions `D_{p^j} = 1 - p^{-j/2} T_{j log p}` (`j = 1, 2`) remove exactly the theta
atoms with labels divisible by `p^j`, satisfy `D_{p²} = (1 + A) D_p`, and multiply the transform
`F(w) = XiC(i w)` by `1 - p^{-j(1/2+w)}`.  At an interior Xi zero `w₀` of multiplicity `m` the
first nonzero deleted jet is the base jet times this nonzero factor; evenness and realness make the
base jets at `w₀` and `-conj w₀` equal in modulus.  Equal reflected moduli of the deleted jets at
both levels force `Re w₀ = 0`, while one level alone can always be balanced by a phase.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace RHTower

/-- Prime-power deletion `D_{p^j} = 1 - p^{-j/2} T_{j log p}`. -/
noncomputable def thetaPrimePowerDeletion (p j : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - (p : ℝ) ^ (-(j : ℝ) / 2) * f (x + j * Real.log p)

/-- `D_{p^j} k` removes exactly the atoms whose labels are divisible by `p^j`. -/
theorem thetaPrimePowerDeletion_eq_tsum {p : ℕ} (hp : 0 < p) (j : ℕ) (x : ℝ) :
    thetaPrimePowerDeletion p j thetaCuspFullSource x =
      ∑' m : ℕ, {m : ℕ | ¬ p ^ j ∣ m}.indicator (thetaCuspSourceTerm x) m := by
  have hd : 0 < p ^ j := pow_pos hp j
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hscale : (p : ℝ) ^ (-(j : ℝ) / 2) * thetaCuspFullSource (x + j * Real.log p) =
      ((p ^ j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (x + Real.log ((p ^ j : ℕ) : ℝ)) := by
    push_cast
    rw [Real.log_pow, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le]
    ring_nf
  have hsum := summable_thetaCuspSourceTerm x
  rw [thetaPrimePowerDeletion, hscale, rpow_neg_half_mul_thetaCuspFullSource_add_log hd,
    thetaCuspFullSource, ← hsum.tsum_sub (hsum.indicator _)]
  apply tsum_congr
  intro m
  by_cases hm : p ^ j ∣ m
  · rw [Set.indicator_of_mem (show m ∈ {m : ℕ | p ^ j ∣ m} from hm),
      Set.indicator_of_notMem (show m ∉ {m : ℕ | ¬ p ^ j ∣ m} from fun h => h hm), sub_self]
  · rw [Set.indicator_of_notMem (show m ∉ {m : ℕ | p ^ j ∣ m} from hm),
      Set.indicator_of_mem (show m ∈ {m : ℕ | ¬ p ^ j ∣ m} from hm), sub_zero]

/-- `D_{p²} = (1 + A) D_p` with `A = p^{-1/2} T_{log p}`: the second level is a polynomial in the
same prime translation. -/
theorem thetaPrimePowerDeletion_two_eq {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ) (x : ℝ) :
    thetaPrimePowerDeletion p 2 f x =
      thetaPrimePowerDeletion p 1 f x +
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * thetaPrimePowerDeletion p 1 f (x + Real.log p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold thetaPrimePowerDeletion
  have hsq : (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-((1 : ℕ) : ℝ) / 2) =
      (p : ℝ) ^ (-((2 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add hpR]
    norm_num
  rw [show x + ((2 : ℕ) : ℝ) * Real.log p = x + Real.log p + ((1 : ℕ) : ℝ) * Real.log p by
    push_cast; ring, ← hsq]
  push_cast
  ring_nf


private theorem natCast_cpow_eq_cexp_log {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp (z * (Real.log n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', mul_comm, Complex.natCast_log]

/-- The prime-power Euler factor `E_j(w) = 1 - p^{-j(1/2+w)}`. -/
noncomputable def primePowerEulerFactor (p j : ℕ) (w : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (-(j : ℂ) * (1 / 2 + w))

/-- **Prime-power deletion transform (1).**  `F_{p^j}(w) = F(w) (1 - p^{-j(1/2+w)})`. -/
theorem integral_cexp_mul_thetaPrimePowerDeletion {p : ℕ} (hp : 0 < p) (j : ℕ) (w : ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaPrimePowerDeletion p j thetaCuspFullSource x : ℂ)) =
      XiC (I * w) * primePowerEulerFactor p j w := by
  have hk := integrable_cexp_mul_thetaCuspFullSource w
  have hshift := integrable_cexp_mul_comp_add (j * Real.log p)
    (G := fun y => (thetaCuspFullSource y : ℂ)) hk
  have hfun : (fun x : ℝ => Complex.exp (w * x) *
      (thetaPrimePowerDeletion p j thetaCuspFullSource x : ℂ)) =
      fun x : ℝ => Complex.exp (w * x) * (thetaCuspFullSource x : ℂ) -
        (((p : ℝ) ^ (-(j : ℝ) / 2) : ℝ) : ℂ) *
          (Complex.exp (w * x) * (thetaCuspFullSource (x + j * Real.log p) : ℂ)) := by
    funext x
    unfold thetaPrimePowerDeletion
    push_cast
    ring
  rw [hfun, integral_sub hk (hshift.const_mul _), integral_const_mul,
    integral_cexp_mul_comp_add w (j * Real.log p) (fun y => (thetaCuspFullSource y : ℂ)),
    integral_cexp_mul_thetaCuspFullSource, primePowerEulerFactor,
    natCast_cpow_eq_cexp_log hp, Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast,
    natCast_cpow_eq_cexp_log hp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem differentiable_primePowerEulerFactor {p : ℕ} (hp : 0 < p) (j : ℕ) :
    Differentiable ℂ (primePowerEulerFactor p j) := fun w =>
  (differentiableAt_const _).sub (DifferentiableAt.const_cpow (by fun_prop)
    (Or.inl (by exact_mod_cast hp.ne')))

/-- Both prime-power Euler factors are zero-free to the right of `Re w = -1/2`. -/
theorem primePowerEulerFactor_ne_zero {p : ℕ} (hp : 2 ≤ p) {j : ℕ} (hj : 0 < j) {w : ℂ}
    (hw : -(1 / 2) < w.re) : primePowerEulerFactor p j w ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-(j : ℂ) * (1 / 2 + w)) = 1 := by
    unfold primePowerEulerFactor at h
    linear_combination -h
  have hnorm := congrArg norm h1
  rw [Complex.norm_natCast_cpow_of_pos (by omega), norm_one] at hnorm
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hre : (-(j : ℂ) * (1 / 2 + w)).re < 0 := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.add_re,
      Complex.neg_im, Complex.natCast_im, Complex.add_im, neg_zero, zero_mul, sub_zero]
    norm_num
    nlinarith
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have := Real.rpow_lt_one_of_one_lt_of_neg hpR hre
  linarith

/-- The Laplace transform `F(w) = XiC(i w)` of the completed source. -/
noncomputable def thetaSourceTransform (w : ℂ) : ℂ := XiC (I * w)

theorem differentiable_thetaSourceTransform : Differentiable ℂ thetaSourceTransform :=
  XiC_differentiable.comp (differentiable_id.const_mul I)

theorem thetaSourceTransform_neg (w : ℂ) : thetaSourceTransform (-w) = thetaSourceTransform w := by
  unfold thetaSourceTransform
  rw [show I * -w = -(I * w) by ring, XiC_even]

theorem thetaSourceTransform_conj (w : ℂ) :
    thetaSourceTransform (conj w) = conj (thetaSourceTransform w) := by
  unfold thetaSourceTransform
  rw [← XiC_conj, show I * conj w = -conj (I * w) by simp [map_mul, Complex.conj_I], XiC_even]

private theorem iteratedDeriv_conj_comp_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]

/-- **Reflected normal jets.**  Evenness and realness give
`F^{(m)}(-conj w) = (-1)^m conj F^{(m)}(w)`. -/
theorem iteratedDeriv_thetaSourceTransform_neg_conj (m : ℕ) (w : ℂ) :
    iteratedDeriv m thetaSourceTransform (-conj w) =
      (-1) ^ m * conj (iteratedDeriv m thetaSourceTransform w) := by
  have hconj : (starRingEnd ℂ) ∘ thetaSourceTransform ∘ (starRingEnd ℂ) = thetaSourceTransform := by
    funext z
    simp [Function.comp_apply, thetaSourceTransform_conj]
  have hC : iteratedDeriv m thetaSourceTransform (conj w) =
      conj (iteratedDeriv m thetaSourceTransform w) := by
    have := congrFun (iteratedDeriv_conj_comp_conj thetaSourceTransform m) (conj w)
    rw [hconj] at this
    simpa using this
  have heven : thetaSourceTransform = fun x => thetaSourceTransform (-x) := by
    funext x
    rw [thetaSourceTransform_neg]
  have hN : iteratedDeriv m thetaSourceTransform (conj w) =
      (-1) ^ m * iteratedDeriv m thetaSourceTransform (-conj w) := by
    conv_lhs => rw [heven]
    rw [iteratedDeriv_comp_neg, smul_eq_mul]
  have hsq : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by
    rw [← mul_pow]; norm_num
  calc iteratedDeriv m thetaSourceTransform (-conj w) =
        ((-1) ^ m * (-1) ^ m) * iteratedDeriv m thetaSourceTransform (-conj w) := by
          rw [hsq, one_mul]
    _ = (-1) ^ m * iteratedDeriv m thetaSourceTransform (conj w) := by rw [hN]; ring
    _ = (-1) ^ m * conj (iteratedDeriv m thetaSourceTransform w) := by rw [hC]

theorem norm_iteratedDeriv_thetaSourceTransform_neg_conj (m : ℕ) (w : ℂ) :
    ‖iteratedDeriv m thetaSourceTransform (-conj w)‖ =
      ‖iteratedDeriv m thetaSourceTransform w‖ := by
  rw [iteratedDeriv_thetaSourceTransform_neg_conj, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_conj]

/-- Leibniz transport of the first nonzero jet through a smooth factor. -/
theorem iteratedDeriv_mul_of_lower_vanish {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {w₀ : ℂ} {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i f w₀ = 0) :
    (∀ i < m, iteratedDeriv i (f * g) w₀ = 0) ∧
      iteratedDeriv m (f * g) w₀ = iteratedDeriv m f w₀ * g w₀ := by
  have hfc : ∀ n : ℕ, ContDiffAt ℂ n f w₀ := fun n => (hf.contDiff (n := n)).contDiffAt
  have hgc : ∀ n : ℕ, ContDiffAt ℂ n g w₀ := fun n => (hg.contDiff (n := n)).contDiffAt
  constructor
  · intro i hi
    rw [iteratedDeriv_mul (hfc i) (hgc i)]
    apply Finset.sum_eq_zero
    intro l hl
    rw [hvan l (by have := Finset.mem_range.mp hl; omega)]
    ring
  · rw [iteratedDeriv_mul (hfc m) (hgc m), Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp
    · intro l hl
      rw [hvan l (Finset.mem_range.mp hl)]
      ring


/-- The deleted transform `F_{p^j} = F · E_j`. -/
noncomputable def thetaPrimePowerDeletedTransform (p j : ℕ) (w : ℂ) : ℂ :=
  thetaSourceTransform w * primePowerEulerFactor p j w

theorem thetaPrimePowerDeletedTransform_eq_integral {p : ℕ} (hp : 0 < p) (j : ℕ) (w : ℂ) :
    thetaPrimePowerDeletedTransform p j w =
      ∫ x : ℝ, Complex.exp (w * x) * (thetaPrimePowerDeletion p j thetaCuspFullSource x : ℂ) :=
  (integral_cexp_mul_thetaPrimePowerDeletion hp j w).symm

/-- **Jet transport (2).**  At an interior Xi zero of multiplicity `m`, the first nonzero jet of
each deleted transform is the base jet times the nonzero Euler factor. -/
theorem thetaPrimePowerDeleted_jet {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : 0 < j) {w₀ : ℂ}
    (hw₀ : -(1 / 2) < w₀.re) {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i thetaSourceTransform w₀ = 0) :
    (∀ i < m, iteratedDeriv i (thetaPrimePowerDeletedTransform p j) w₀ = 0) ∧
      iteratedDeriv m (thetaPrimePowerDeletedTransform p j) w₀ =
        iteratedDeriv m thetaSourceTransform w₀ * primePowerEulerFactor p j w₀ ∧
      primePowerEulerFactor p j w₀ ≠ 0 := by
  have h := iteratedDeriv_mul_of_lower_vanish differentiable_thetaSourceTransform
    (differentiable_primePowerEulerFactor hp.pos j) hvan
  exact ⟨h.1, h.2, primePowerEulerFactor_ne_zero hp.two_le hj hw₀⟩

/-- The reflected point `-conj w₀` is a zero of the same multiplicity. -/
theorem iteratedDeriv_thetaSourceTransform_neg_conj_eq_zero_iff (i : ℕ) (w : ℂ) :
    iteratedDeriv i thetaSourceTransform (-conj w) = 0 ↔
      iteratedDeriv i thetaSourceTransform w = 0 := by
  rw [← norm_eq_zero, norm_iteratedDeriv_thetaSourceTransform_neg_conj, norm_eq_zero]

private theorem natCast_cpow_jet_form {p : ℕ} (hp : 0 < p) (j : ℕ) (w : ℂ) :
    (p : ℂ) ^ (-(j : ℂ) * (1 / 2 + w)) =
      ((((p : ℝ) ^ (-(1 / 2) - w.re)) ^ j : ℝ) : ℂ) *
        Complex.exp ((((j : ℝ) * (-(w.im * Real.log p)) : ℝ) : ℂ) * I) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [natCast_cpow_eq_cexp_log hp, ← Real.rpow_natCast, ← Real.rpow_mul hpR.le,
    Real.rpow_def_of_pos hpR, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im w]
  push_cast
  ring

/-- **Two-level rigidity (3).**  If the deleted normal jets at a Xi zero `w₀` of the open strip
have equal reflected magnitudes at the levels `p` and `p²`, then `Re w₀ = 0`. -/
theorem re_eq_zero_of_prime_and_square_deleted_jets {p : ℕ} (hp : p.Prime) {w₀ : ℂ}
    (hstrip : |w₀.re| < 1 / 2) {m : ℕ}
    (hvan : ∀ i < m, iteratedDeriv i thetaSourceTransform w₀ = 0)
    (hm : iteratedDeriv m thetaSourceTransform w₀ ≠ 0)
    (h1 : ‖iteratedDeriv m (thetaPrimePowerDeletedTransform p 1) w₀‖ =
      ‖iteratedDeriv m (thetaPrimePowerDeletedTransform p 1) (-conj w₀)‖)
    (h2 : ‖iteratedDeriv m (thetaPrimePowerDeletedTransform p 2) w₀‖ =
      ‖iteratedDeriv m (thetaPrimePowerDeletedTransform p 2) (-conj w₀)‖) :
    w₀.re = 0 := by
  have hre := abs_lt.mp hstrip
  have hw₀ : -(1 / 2) < w₀.re := by linarith
  have hw₁ : -(1 / 2) < (-conj w₀).re := by simp; linarith
  have hvan' : ∀ i < m, iteratedDeriv i thetaSourceTransform (-conj w₀) = 0 := fun i hi =>
    (iteratedDeriv_thetaSourceTransform_neg_conj_eq_zero_iff i w₀).mpr (hvan i hi)
  have hnorm := norm_iteratedDeriv_thetaSourceTransform_neg_conj m w₀
  have hmpos : 0 < ‖iteratedDeriv m thetaSourceTransform w₀‖ := norm_pos_iff.mpr hm
  have hfactor : ∀ j, 0 < j →
      ‖iteratedDeriv m (thetaPrimePowerDeletedTransform p j) w₀‖ =
        ‖iteratedDeriv m (thetaPrimePowerDeletedTransform p j) (-conj w₀)‖ →
      ‖primePowerEulerFactor p j w₀‖ = ‖primePowerEulerFactor p j (-conj w₀)‖ := by
    intro j hj heq
    rw [(thetaPrimePowerDeleted_jet hp hj hw₀ hvan).2.1,
      (thetaPrimePowerDeleted_jet hp hj hw₁ hvan').2.1, norm_mul, norm_mul, hnorm] at heq
    exact mul_left_cancel₀ hmpos.ne' heq
  have e1 := hfactor 1 one_pos h1
  have e2 := hfactor 2 two_pos h2
  simp only [primePowerEulerFactor] at e1 e2
  rw [natCast_cpow_jet_form hp.pos, natCast_cpow_jet_form hp.pos] at e1 e2
  simp only [Complex.neg_re, Complex.conj_re, Complex.neg_im, Complex.conj_im, neg_neg,
    pow_one, Nat.cast_one, one_mul] at e1 e2
  set θ := -(w₀.im * Real.log p)
  have hp1 : 1 < p := hp.one_lt
  rcases le_or_gt 0 w₀.re with hσ | hσ
  · apply epsilon_eq_zero_of_prime_and_square_reflected_modulus_neutral hp1 hσ hre.2
      (theta := θ)
    · rw [show (-1 / 2 + w₀.re : ℝ) = -(1 / 2) - -w₀.re by ring,
        show (-1 / 2 - w₀.re : ℝ) = -(1 / 2) - w₀.re by ring]
      exact e1.symm
    · rw [show (-1 / 2 + w₀.re : ℝ) = -(1 / 2) - -w₀.re by ring,
        show (-1 / 2 - w₀.re : ℝ) = -(1 / 2) - w₀.re by ring]
      push_cast at e2 ⊢
      exact e2.symm
  · have h0 := epsilon_eq_zero_of_prime_and_square_reflected_modulus_neutral hp1
      (epsilon := -w₀.re) (by linarith) (by linarith) (theta := θ)
      (by
        rw [show (-1 / 2 + -w₀.re : ℝ) = -(1 / 2) - w₀.re by ring,
          show (-1 / 2 - -w₀.re : ℝ) = -(1 / 2) - -w₀.re by ring]
        exact e1)
      (by
        rw [show (-1 / 2 + -w₀.re : ℝ) = -(1 / 2) - w₀.re by ring,
          show (-1 / 2 - -w₀.re : ℝ) = -(1 / 2) - -w₀.re by ring]
        push_cast at e2 ⊢
        exact e2)
    linarith

/-- **One level is insufficient.**  For any two radii in `(0,1)` some phase makes the first-level
reflected moduli equal. -/
theorem exists_phase_one_level_neutral {rplus rminus : ℝ} (hplus : 0 < rplus) (hplus1 : rplus < 1)
    (hminus : 0 < rminus) (hminus1 : rminus < 1) :
    ∃ θ : ℝ, ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((θ : ℂ) * I)‖ =
      ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((θ : ℂ) * I)‖ := by
  set c := (rplus + rminus) / 2
  have hc : Real.cos (Real.arccos c) = c :=
    Real.cos_arccos (by simp only [c]; linarith) (by simp only [c]; linarith)
  have hs : Real.sin (Real.arccos c) ^ 2 = 1 - c ^ 2 := by
    have := Real.sin_sq_add_cos_sq (Real.arccos c)
    rw [hc] at this
    linarith
  refine ⟨Real.arccos c, ?_⟩
  have hsq : ∀ r : ℝ, ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((Real.arccos c : ℂ) * I)‖ ^ 2 =
      1 - 2 * r * c + r ^ 2 := by
    intro r
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero, add_zero, zero_sub]
    rw [hc]
    linear_combination r ^ 2 * hs
  have h1 := hsq rplus
  have h2 := hsq rminus
  have heq : ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((Real.arccos c : ℂ) * I)‖ ^ 2 =
      ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((Real.arccos c : ℂ) * I)‖ ^ 2 := by
    rw [h1, h2]
    simp only [c]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq

end RHTower
