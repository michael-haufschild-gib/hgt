import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalCoordinate

/-!
# The functional equation admits every finite layer

Is a finite top layer compatible with the functional equation once the bottom layer is reflected?
At the level of entire functions of order one: yes, for every finite layer.

For a finite set `Q` of points, the **cosh model**

`G_Q(s) = cosh(s − ½) · Π_{q∈Q} (s − q)(s − q̄)(s − 1 + q)(s − 1 + q̄)`

is entire (`differentiable_coshModel`), satisfies the functional equation `G_Q(1 − s) = G_Q(s)`
(`coshModel_one_sub`) and reality `G_Q(s̄) = conj G_Q(s)` (`coshModel_conj`), grows at most like
`(1 + |s|)^{4#Q} e^{|s|}` (`norm_coshModel_le`), and vanishes exactly on the critical zeros
`½ + iπ(n + ½)` of the cosh factor and on the quartets of `Q` (`coshModel_eq_zero_iff`,
`re_eq_half_of_cosh_eq_zero`). So every finite reflection-closed off-line layer is the off-line zero
set of an entire function of order one with the functional equation and reality, whose other zeros
(infinitely many) lie on the critical line. The functional equation, order one and reality exclude no
finite top layer; on level sums of a tower the functional equation acts only through
`S(−ν) = conj S(ν)` (`WeilTower.levelSum_neg`). An argument excluding a finite top layer must use the
Dirichlet series.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The quartet polynomial `(s − q)(s − q̄)(s − 1 + q)(s − 1 + q̄)`. -/
def quartet (q s : ℂ) : ℂ :=
  (s - q) * (s - starRingEnd ℂ q) * (s - (1 - q)) * (s - (1 - starRingEnd ℂ q))

/-- The **cosh model** with off-line layer the quartets of `Q`. -/
def coshModel (Q : Finset ℂ) (s : ℂ) : ℂ := Complex.cosh (s - 1 / 2) * ∏ q ∈ Q, quartet q s

theorem quartet_one_sub (q s : ℂ) : quartet q (1 - s) = quartet q s := by
  unfold quartet; ring

theorem quartet_conj (q s : ℂ) :
    quartet q (starRingEnd ℂ s) = starRingEnd ℂ (quartet q s) := by
  unfold quartet
  simp only [map_mul, map_sub, map_one, Complex.conj_conj]
  ring

/-- **Functional equation.** `G_Q(1 − s) = G_Q(s)`. -/
theorem coshModel_one_sub (Q : Finset ℂ) (s : ℂ) : coshModel Q (1 - s) = coshModel Q s := by
  unfold coshModel
  rw [show (1 - s - 1 / 2 : ℂ) = -(s - 1 / 2) by ring, Complex.cosh_neg]
  simp_rw [quartet_one_sub]

/-- **Reality.** `G_Q(s̄) = conj G_Q(s)`. -/
theorem coshModel_conj (Q : Finset ℂ) (s : ℂ) :
    coshModel Q (starRingEnd ℂ s) = starRingEnd ℂ (coshModel Q s) := by
  have h12 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  unfold coshModel
  rw [map_mul, map_prod, ← Complex.cosh_conj, map_sub, h12]
  simp_rw [quartet_conj]

theorem differentiable_quartet (q : ℂ) : Differentiable ℂ (quartet q) := by
  unfold quartet; fun_prop

/-- The cosh model is entire. -/
theorem differentiable_coshModel (Q : Finset ℂ) : Differentiable ℂ (coshModel Q) := by
  unfold coshModel
  refine (Complex.differentiable_cosh.comp (differentiable_id.sub_const _)).mul ?_
  have hfun : (fun s => ∏ q ∈ Q, quartet q s) = ∏ q ∈ Q, quartet q := by
    ext s; rw [Finset.prod_apply]
  rw [hfun]
  exact Differentiable.finsetProd fun q _ => differentiable_quartet q

/-- The zeros of `cosh(s − ½)` lie on the critical line. -/
theorem re_eq_half_of_cosh_eq_zero {s : ℂ} (h : Complex.cosh (s - 1 / 2) = 0) : s.re = 1 / 2 := by
  set w := s - 1 / 2 with hw
  have h2 : Complex.exp (2 * w) = -1 := by
    have hc := Complex.two_cosh w
    rw [h, mul_zero] at hc
    have hsum : Complex.exp w + Complex.exp (-w) = 0 := hc.symm
    have hmul := congrArg (· * Complex.exp w) hsum
    simp only [add_mul, zero_mul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero] at hmul
    rw [show 2 * w = w + w by ring]
    linear_combination hmul
  have hn := congrArg norm h2
  rw [Complex.norm_exp, norm_neg, norm_one, Real.exp_eq_one_iff] at hn
  have : (2 * w).re = 2 * (s.re - 1 / 2) := by simp [hw, Complex.mul_re]
  linarith

/-- The cosh factor has a zero at `½ + iπ(n + ½)` for every integer `n`: infinitely many critical
zeros. -/
theorem cosh_criticalZero (n : ℤ) :
    Complex.cosh ((1 / 2 + (Real.pi * (n + 1 / 2) : ℝ) * I) - 1 / 2) = 0 := by
  rw [show (1 / 2 + (Real.pi * (n + 1 / 2) : ℝ) * I - 1 / 2 : ℂ) =
      ((Real.pi * (n + 1 / 2) : ℝ) : ℂ) * I by ring, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  have : Real.cos (Real.pi * (n + 1 / 2)) = 0 := by
    rw [Real.cos_eq_zero_iff]
    exact ⟨n, by ring⟩
  rw [this, Complex.ofReal_zero]

/-- **The zero set of the model.** `G_Q(s) = 0` iff `s` is a critical zero of the cosh factor or a
point of a quartet of `Q`. -/
theorem coshModel_eq_zero_iff (Q : Finset ℂ) (s : ℂ) :
    coshModel Q s = 0 ↔ Complex.cosh (s - 1 / 2) = 0 ∨
      ∃ q ∈ Q, s = q ∨ s = starRingEnd ℂ q ∨ s = 1 - q ∨ s = 1 - starRingEnd ℂ q := by
  unfold coshModel
  rw [mul_eq_zero, Finset.prod_eq_zero_iff]
  refine or_congr Iff.rfl (exists_congr fun q => and_congr Iff.rfl ?_)
  unfold quartet
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

/-- **Order one.** `|G_Q(s)| ≤ C (1 + |s|)^{4#Q} e^{|s|}`. -/
theorem norm_coshModel_le (Q : Finset ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      ‖coshModel Q s‖ ≤ C * (1 + ‖s‖) ^ (4 * Q.card) * Real.exp ‖s‖ := by
  set K : ℝ := 2 + ∑ q ∈ Q, ‖q‖ with hK
  have hsum0 : 0 ≤ ∑ q ∈ Q, ‖q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK1 : 1 ≤ K := by linarith
  refine ⟨3 * K ^ (4 * Q.card), by positivity, fun s => ?_⟩
  have hs0 := norm_nonneg s
  have hfac : ∀ x : ℂ, ‖x‖ ≤ K → ‖s - x‖ ≤ K * (1 + ‖s‖) := fun x hx => by
    have := norm_sub_le s x
    nlinarith
  have hq : ∀ q ∈ Q, ‖quartet q s‖ ≤ (K * (1 + ‖s‖)) ^ 4 := by
    intro q hqQ
    have hqK : ‖q‖ + 2 ≤ K := by
      have := Finset.single_le_sum (f := fun x : ℂ => ‖x‖) (fun x _ => norm_nonneg x) hqQ
      linarith
    have h1 : ‖q‖ ≤ K := by linarith [norm_nonneg q]
    have h2 : ‖starRingEnd ℂ q‖ ≤ K := by rw [Complex.norm_conj]; exact h1
    have h3 : ‖1 - q‖ ≤ K := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    have h4 : ‖1 - starRingEnd ℂ q‖ ≤ K :=
      (norm_sub_le _ _).trans (by rw [norm_one, Complex.norm_conj]; linarith)
    unfold quartet
    rw [norm_mul, norm_mul, norm_mul,
      show (K * (1 + ‖s‖)) ^ 4 = (K * (1 + ‖s‖)) * (K * (1 + ‖s‖)) * (K * (1 + ‖s‖)) *
        (K * (1 + ‖s‖)) by ring]
    have hp : 0 ≤ K * (1 + ‖s‖) := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul (hfac _ h1) (hfac _ h2) (norm_nonneg _) hp)
      (hfac _ h3) (norm_nonneg _) (by positivity)) (hfac _ h4) (norm_nonneg _) (by positivity)
  have hprod : ‖∏ q ∈ Q, quartet q s‖ ≤ ((K * (1 + ‖s‖)) ^ 4) ^ Q.card := by
    rw [norm_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hq
  have hcosh : ‖Complex.cosh (s - 1 / 2)‖ ≤ 3 * Real.exp ‖s‖ := by
    have hb : ∀ w : ℂ, ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := fun w => by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm w)
    have hw : ‖s - 1 / 2‖ ≤ ‖s‖ + 1 := (norm_sub_le _ _).trans (by norm_num)
    have he : Real.exp ‖s - 1 / 2‖ ≤ Real.exp 1 * Real.exp ‖s‖ := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hcw : Complex.cosh (s - 1 / 2) =
        (Complex.exp (s - 1 / 2) + Complex.exp (-(s - 1 / 2))) / 2 := by
      rw [← Complex.two_cosh]; ring
    rw [hcw, norm_div, h2n]
    have hadd := norm_add_le (Complex.exp (s - 1 / 2)) (Complex.exp (-(s - 1 / 2)))
    have h1 := hb (s - 1 / 2)
    have h2 := hb (-(s - 1 / 2))
    rw [norm_neg] at h2
    have hpos := Real.exp_pos ‖s‖
    have hpos1 := Real.exp_pos 1
    nlinarith
  unfold coshModel
  rw [norm_mul]
  calc ‖Complex.cosh (s - 1 / 2)‖ * ‖∏ q ∈ Q, quartet q s‖
      ≤ (3 * Real.exp ‖s‖) * ((K * (1 + ‖s‖)) ^ 4) ^ Q.card :=
        mul_le_mul hcosh hprod (norm_nonneg _) (by positivity)
    _ = 3 * K ^ (4 * Q.card) * (1 + ‖s‖) ^ (4 * Q.card) * Real.exp ‖s‖ := by
        rw [← pow_mul, mul_pow]; ring

/-! ### The zero configuration of the model -/

/-- The zero configuration of `G_Q`. -/
def coshModelZeros (Q : Finset ℂ) : {s : ℂ // coshModel Q s = 0} → ℂ := fun s => s.1

/-- **ZAL holds**: only the finitely many quartet points of `Q` lie off the critical line. -/
theorem zerosApproachLine_coshModelZeros (Q : Finset ℂ) :
    ZerosApproachLine (coshModelZeros Q) := by
  intro h hh
  set P : Set ℂ := ⋃ q ∈ Q, ({q, starRingEnd ℂ q, 1 - q, 1 - starRingEnd ℂ q} : Set ℂ)
  have hP : P.Finite := Set.Finite.biUnion Q.finite_toSet fun q _ => Set.toFinite _
  refine (hP.preimage Subtype.val_injective.injOn).subset fun s hs => ?_
  have hs : 1 / 2 + h < s.1.re := hs
  rcases (coshModel_eq_zero_iff Q s.1).1 s.2 with hc | ⟨q, hq, hsq⟩
  · have := re_eq_half_of_cosh_eq_zero hc
    linarith
  · simp only [Set.mem_preimage, P, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨q, hq, hsq⟩

/-- **AAL fails** as soon as `Q` contains an off-line point: the functional equation, order one and
reality admit every finite top layer. -/
theorem not_asymptoticAbscissaLaw_coshModelZeros {Q : Finset ℂ} {q : ℂ} (hq : q ∈ Q)
    (hoff : q.re ≠ 1 / 2) : ¬ AsymptoticAbscissaLaw (coshModelZeros Q) := by
  intro hA
  set d := |q.re - 1 / 2| with hd
  have hd0 : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hoff)
  -- the right member of the pair `q, 1 − q`
  obtain ⟨s, hs0, hsre⟩ : ∃ s : ℂ, coshModel Q s = 0 ∧ s.re = 1 / 2 + d := by
    rcases le_or_gt q.re (1 / 2) with hle | hgt
    · refine ⟨1 - q, (coshModel_eq_zero_iff Q _).2 (Or.inr ⟨q, hq, by simp⟩), ?_⟩
      rw [hd, abs_of_nonpos (by linarith)]
      simp only [Complex.sub_re, Complex.one_re]
      ring
    · refine ⟨q, (coshModel_eq_zero_iff Q _).2 (Or.inr ⟨q, hq, by simp⟩), ?_⟩
      rw [hd, abs_of_pos (by linarith)]
      ring
  have hfin := zerosApproachLine_coshModelZeros Q (d / 2) (by linarith)
  have := hA (d / 2) (by linarith) hfin ⟨s, hs0⟩
  simp only [coshModelZeros, hsre] at this
  linarith

end GaloisForLFunctions.InfiniteRankWeilTheory
