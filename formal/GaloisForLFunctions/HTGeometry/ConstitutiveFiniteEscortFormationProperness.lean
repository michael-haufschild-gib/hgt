import GaloisForLFunctions.HTGeometry.ComplexTimeGenerativeMechanics

/-!
# Finite escort reflection properness

Finite positive exponential tilts carry an exact reflected Jeffreys work.  Its integer
amplification orbit is uniformly bounded exactly when the score is constant.  If any observer
reports uniformly bounded reflected work, the complementary hidden-information loss is unbounded
for every nonconstant score.

This is the unconditional finite-information realization of ULF-IFPM-1.  It contains no RH
premise and uses no arithmetic specialization.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {n : ℕ}

noncomputable def finiteTiltMean (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, finiteExponentialTilt w r t x * r x

noncomputable def finiteTiltVariance (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, finiteExponentialTilt w r t x * (r x - finiteTiltMean w r t) ^ (2 : ℕ)

noncomputable def finiteTiltSecondMoment (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, finiteExponentialTilt w r t x * r x ^ (2 : ℕ)

lemma finiteExponentialTilt_nonneg {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) (x : Fin n) :
    0 ≤ finiteExponentialTilt w r t x := by
  unfold finiteExponentialTilt
  exact div_nonneg (mul_nonneg (hw x) (Real.exp_pos _).le)
    (finiteExpPartition_pos hw hsum t).le

lemma finiteTiltMean_eq_div {w r : Fin n → ℝ} (t : ℝ) :
    finiteTiltMean w r t =
      (∑ x, w x * r x * Real.exp (t * r x)) / finiteExpPartition w r t := by
  unfold finiteTiltMean finiteExponentialTilt
  calc
    ∑ x, w x * Real.exp (t * r x) / finiteExpPartition w r t * r x =
        ∑ x, (w x * r x * Real.exp (t * r x)) / finiteExpPartition w r t := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [Finset.sum_div]

lemma finiteTiltSecondMoment_eq_div {w r : Fin n → ℝ} (t : ℝ) :
    finiteTiltSecondMoment w r t =
      (∑ x, w x * r x ^ (2 : ℕ) * Real.exp (t * r x)) / finiteExpPartition w r t := by
  unfold finiteTiltSecondMoment finiteExponentialTilt
  calc
    ∑ x, w x * Real.exp (t * r x) / finiteExpPartition w r t * r x ^ (2 : ℕ) =
        ∑ x, (w x * r x ^ (2 : ℕ) * Real.exp (t * r x)) / finiteExpPartition w r t := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [Finset.sum_div]

lemma finiteTiltVariance_eq_second_sub_sq {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    finiteTiltVariance w r t =
      finiteTiltSecondMoment w r t - finiteTiltMean w r t ^ (2 : ℕ) := by
  unfold finiteTiltVariance finiteTiltSecondMoment finiteTiltMean
  simp_rw [show ∀ x, finiteExponentialTilt w r t x *
      (r x - ∑ y, finiteExponentialTilt w r t y * r y) ^ (2 : ℕ) =
      finiteExponentialTilt w r t x * r x ^ (2 : ℕ) -
        2 * (∑ y, finiteExponentialTilt w r t y * r y) *
          (finiteExponentialTilt w r t x * r x) +
        (∑ y, finiteExponentialTilt w r t y * r y) ^ (2 : ℕ) *
          finiteExponentialTilt w r t x by intro x; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [finiteExponentialTilt_sum hw hsum]
  ring

lemma hasDerivAt_finiteTiltMean {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    HasDerivAt (finiteTiltMean w r) (finiteTiltVariance w r t) t := by
  have hden := hasDerivAt_finiteExpPartition w r t
  have hnum : HasDerivAt
      (fun s : ℝ => ∑ x, w x * r x * Real.exp (s * r x))
      (∑ x, w x * r x ^ (2 : ℕ) * Real.exp (t * r x)) t := by
    refine HasDerivAt.fun_sum fun x _ => ?_
    have hinner : HasDerivAt (fun s : ℝ => s * r x) (r x) t := by
      simpa using (hasDerivAt_id t).mul_const (r x)
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      hinner.exp.const_mul (w x * r x)
  have hZ : finiteExpPartition w r t ≠ 0 := (finiteExpPartition_pos hw hsum t).ne'
  have hfun : finiteTiltMean w r = fun s =>
      (∑ x, w x * r x * Real.exp (s * r x)) / finiteExpPartition w r s := by
    funext s
    exact finiteTiltMean_eq_div s
  have hquot := hnum.div hden hZ
  rw [hfun]
  convert hquot using 1 <;> try rfl
  · rw [finiteTiltVariance_eq_second_sub_sq hw hsum,
      finiteTiltSecondMoment_eq_div, finiteTiltMean_eq_div]
    field_simp [hZ]
    have hsumexp : (∑ x, w x * r x ^ (2 : ℕ) * Real.exp (r x * t)) =
        ∑ x, w x * r x ^ (2 : ℕ) * Real.exp (t * r x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_comm (r x) t]
    rw [hsumexp]
    ring

lemma finiteTiltVariance_nonneg {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    0 ≤ finiteTiltVariance w r t := by
  unfold finiteTiltVariance
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (finiteExponentialTilt_nonneg hw hsum t x) (sq_nonneg _)

lemma finiteExponentialTilt_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) (x : Fin n) :
    0 < finiteExponentialTilt w r t x := by
  unfold finiteExponentialTilt
  exact div_pos (mul_pos (hw x) (Real.exp_pos _)) (finiteExpPartition_pos (fun y => (hw y).le) hsum t)

lemma finiteTiltVariance_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (hvar : ∃ i j, r i ≠ r j) (t : ℝ) :
    0 < finiteTiltVariance w r t := by
  obtain ⟨i, j, hij⟩ := hvar
  have hi_or_hj : r i ≠ finiteTiltMean w r t ∨ r j ≠ finiteTiltMean w r t := by
    by_contra h
    push Not at h
    exact hij (h.1.trans h.2.symm)
  obtain hi | hj := hi_or_hj
  · unfold finiteTiltVariance
    exact Finset.sum_pos' (fun x _ =>
      mul_nonneg (finiteExponentialTilt_pos hw hsum t x).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i,
        mul_pos (finiteExponentialTilt_pos hw hsum t i) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))⟩
  · unfold finiteTiltVariance
    exact Finset.sum_pos' (fun x _ =>
      mul_nonneg (finiteExponentialTilt_pos hw hsum t x).le (sq_nonneg _))
      ⟨j, Finset.mem_univ j,
        mul_pos (finiteExponentialTilt_pos hw hsum t j) (sq_pos_of_ne_zero (sub_ne_zero.mpr hj))⟩

lemma finiteTiltMean_monotone {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) :
    Monotone (finiteTiltMean w r) := by
  apply monotone_of_deriv_nonneg
  · exact fun t => (hasDerivAt_finiteTiltMean hw hsum t).differentiableAt
  · intro t
    rw [(hasDerivAt_finiteTiltMean hw hsum t).deriv]
    exact finiteTiltVariance_nonneg hw hsum t

lemma finiteTiltMean_strictMono {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (hvar : ∃ i j, r i ≠ r j) :
    StrictMono (finiteTiltMean w r) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_finiteTiltMean (fun x => (hw x).le) hsum t).deriv]
  exact finiteTiltVariance_pos hw hsum hvar t

noncomputable def finiteReflectedTiltWork (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  t * (finiteTiltMean w r t - finiteTiltMean w r (-t))

lemma finiteReflectedTiltWork_linear_lower {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) {t : ℝ} (ht : 1 ≤ t) :
    t * finiteReflectedTiltWork w r 1 ≤ finiteReflectedTiltWork w r t := by
  have hm := finiteTiltMean_monotone (r := r) hw hsum
  have hp : finiteTiltMean w r 1 ≤ finiteTiltMean w r t := hm ht
  have hn : finiteTiltMean w r (-t) ≤ finiteTiltMean w r (-1) := hm (by linarith)
  unfold finiteReflectedTiltWork
  norm_num
  nlinarith

lemma finiteReflectedTiltWork_nat_unbounded {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (hpos : 0 < finiteReflectedTiltWork w r 1) :
    ¬ ∃ C : ℝ, ∀ k : ℕ, finiteReflectedTiltWork w r k ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max (C / finiteReflectedTiltWork w r 1) 1)
  have hkC : C / finiteReflectedTiltWork w r 1 < (k : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hk
  have hk1 : (1 : ℝ) ≤ k :=
    le_trans (le_max_right _ _) hk.le
  have hlower := finiteReflectedTiltWork_linear_lower (r := r) hw hsum hk1
  have hstrict : C < (k : ℝ) * finiteReflectedTiltWork w r 1 :=
    (div_lt_iff₀ hpos).mp hkC
  exact (not_lt_of_ge ((hlower.trans (hC k)))) hstrict

lemma finiteReflectedTiltWork_one_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (hvar : ∃ i j, r i ≠ r j) :
    0 < finiteReflectedTiltWork w r 1 := by
  unfold finiteReflectedTiltWork
  norm_num
  exact finiteTiltMean_strictMono hw hsum hvar (by norm_num)

lemma finiteReflectedTiltWork_unbounded_of_nonconstant {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) (hvar : ∃ i j, r i ≠ r j) :
    ¬ ∃ C : ℝ, ∀ k : ℕ, finiteReflectedTiltWork w r k ≤ C :=
  finiteReflectedTiltWork_nat_unbounded (fun x => (hw x).le) hsum
    (finiteReflectedTiltWork_one_pos hw hsum hvar)

lemma finiteTiltMean_eq_score {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hconst : ∀ i j, r i = r j) (i : Fin n) (t : ℝ) :
    finiteTiltMean w r t = r i := by
  unfold finiteTiltMean
  simp_rw [hconst _ i]
  rw [← Finset.sum_mul, finiteExponentialTilt_sum (fun x => (hw x).le) hsum]
  simp

lemma finiteReflectedTiltWork_zero_of_score_constant {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hconst : ∀ i j, r i = r j) (t : ℝ) :
    finiteReflectedTiltWork w r t = 0 := by
  haveI : Nonempty (Fin n) := by
    by_contra h
    have : ∑ x, w x = 0 := Finset.sum_eq_zero fun x _ => False.elim (h ⟨x⟩)
    linarith
  let i : Fin n := Classical.choice inferInstance
  have hct := finiteTiltMean_eq_score hw hsum hconst i t
  have hcn := finiteTiltMean_eq_score hw hsum hconst i (-t)
  unfold finiteReflectedTiltWork
  rw [hct, hcn, sub_self, mul_zero]

theorem finiteReflectedTiltWork_bounded_iff_score_constant {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) :
    (∃ C : ℝ, ∀ k : ℕ, finiteReflectedTiltWork w r k ≤ C) ↔
      ∀ i j, r i = r j := by
  constructor
  · intro hbounded i j
    by_contra hij
    exact finiteReflectedTiltWork_unbounded_of_nonconstant hw hsum ⟨i, j, hij⟩ hbounded
  · intro hconst
    exact ⟨0, fun k => by rw [finiteReflectedTiltWork_zero_of_score_constant hw hsum hconst]⟩

noncomputable def finiteTiltKLReal (w r : Fin n → ℝ) (s t : ℝ) : ℝ :=
  ∑ x, finiteExponentialTilt w r s x *
    Real.log (finiteExponentialTilt w r s x / finiteExponentialTilt w r t x)

noncomputable def finiteTiltJeffreysReal (w r : Fin n → ℝ) (s t : ℝ) : ℝ :=
  finiteTiltKLReal w r s t + finiteTiltKLReal w r t s

lemma finiteExponentialTilt_ratio {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (s t : ℝ) (x : Fin n) :
    finiteExponentialTilt w r s x / finiteExponentialTilt w r t x =
      Real.exp ((s - t) * r x) *
        (finiteExpPartition w r t / finiteExpPartition w r s) := by
  unfold finiteExponentialTilt
  have hZs := (finiteExpPartition_pos (r := r) (fun y => (hw y).le) hsum s).ne'
  have hZt := (finiteExpPartition_pos (r := r) (fun y => (hw y).le) hsum t).ne'
  rw [show (s - t) * r x = s * r x - t * r x by ring, Real.exp_sub]
  field_simp [hZs, hZt, (hw x).ne', (Real.exp_pos _).ne']

lemma log_finiteExponentialTilt_ratio {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (s t : ℝ) (x : Fin n) :
    Real.log (finiteExponentialTilt w r s x / finiteExponentialTilt w r t x) =
      (s - t) * r x + Real.log (finiteExpPartition w r t) -
        Real.log (finiteExpPartition w r s) := by
  rw [finiteExponentialTilt_ratio hw hsum]
  have hZs := finiteExpPartition_pos (r := r) (fun y => (hw y).le) hsum s
  have hZt := finiteExpPartition_pos (r := r) (fun y => (hw y).le) hsum t
  rw [Real.log_mul (Real.exp_ne_zero _) (div_ne_zero hZt.ne' hZs.ne'),
    Real.log_exp, Real.log_div hZt.ne' hZs.ne']
  ring

lemma finiteTiltKLReal_eq {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (s t : ℝ) :
    finiteTiltKLReal w r s t =
      (s - t) * finiteTiltMean w r s +
        Real.log (finiteExpPartition w r t) - Real.log (finiteExpPartition w r s) := by
  unfold finiteTiltKLReal finiteTiltMean
  simp_rw [log_finiteExponentialTilt_ratio hw hsum]
  have hsumexpand : (∑ x, finiteExponentialTilt w r s x *
      ((s - t) * r x + Real.log (finiteExpPartition w r t) -
        Real.log (finiteExpPartition w r s))) =
      (s - t) * (∑ x, finiteExponentialTilt w r s x * r x) +
        (Real.log (finiteExpPartition w r t) - Real.log (finiteExpPartition w r s)) *
          ∑ x, finiteExponentialTilt w r s x := by
    calc
      _ = ∑ x, ((s - t) * (finiteExponentialTilt w r s x * r x) +
          (Real.log (finiteExpPartition w r t) - Real.log (finiteExpPartition w r s)) *
            finiteExponentialTilt w r s x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsumexpand]
  rw [finiteExponentialTilt_sum (fun x => (hw x).le) hsum]
  ring

lemma finiteTiltJeffreysReal_eq {w r : Fin n → ℝ} (hw : ∀ x, 0 < w x)
    (hsum : ∑ x, w x = 1) (s t : ℝ) :
    finiteTiltJeffreysReal w r s t =
      (s - t) * (finiteTiltMean w r s - finiteTiltMean w r t) := by
  unfold finiteTiltJeffreysReal
  rw [finiteTiltKLReal_eq hw hsum, finiteTiltKLReal_eq hw hsum]
  ring

lemma finiteTiltJeffreysReal_reflection_eq {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    finiteTiltJeffreysReal w r t (-t) = 2 * finiteReflectedTiltWork w r t := by
  rw [finiteTiltJeffreysReal_eq hw hsum]
  unfold finiteReflectedTiltWork
  ring

theorem finiteTiltJeffreysReflection_bounded_iff_score_constant {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) :
    (∃ C : ℝ, ∀ k : ℕ, finiteTiltJeffreysReal w r k (-k) ≤ C) ↔
      ∀ i j, r i = r j := by
  constructor
  · rintro ⟨C, hC⟩
    apply (finiteReflectedTiltWork_bounded_iff_score_constant hw hsum).mp
    refine ⟨C / 2, fun k => ?_⟩
    have hk := hC k
    rw [finiteTiltJeffreysReal_reflection_eq hw hsum] at hk
    linarith
  · intro hconst
    refine ⟨0, fun k => ?_⟩
    rw [finiteTiltJeffreysReal_reflection_eq hw hsum,
      finiteReflectedTiltWork_zero_of_score_constant hw hsum hconst]
    norm_num

lemma finiteTiltJeffreysReflection_linear_lower {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1) {t : ℝ} (ht : 1 ≤ t) :
    t * finiteTiltJeffreysReal w r 1 (-1) ≤
      finiteTiltJeffreysReal w r t (-t) := by
  rw [finiteTiltJeffreysReal_reflection_eq hw hsum,
    finiteTiltJeffreysReal_reflection_eq hw hsum]
  have h := finiteReflectedTiltWork_linear_lower (r := r)
    (fun x => (hw x).le) hsum ht
  nlinarith

noncomputable def finiteEscortHiddenLoss (w r : Fin n → ℝ)
    (observed : ℕ → ℝ) (k : ℕ) : ℝ :=
  finiteTiltJeffreysReal w r k (-k) - observed k

lemma finiteEscortHiddenLoss_linear_lower {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (observed : ℕ → ℝ) (C : ℝ) (hobserved : ∀ k, observed k ≤ C)
    {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * finiteTiltJeffreysReal w r 1 (-1) - C ≤
      finiteEscortHiddenLoss w r observed k := by
  have hsource := finiteTiltJeffreysReflection_linear_lower (r := r) hw hsum
    (t := (k : ℝ)) (by exact_mod_cast hk)
  have hobserved_k := hobserved k
  unfold finiteEscortHiddenLoss
  norm_num at hsource ⊢
  linarith

theorem finiteEscortHiddenLoss_unbounded_of_nonconstant {w r : Fin n → ℝ}
    (hw : ∀ x, 0 < w x) (hsum : ∑ x, w x = 1)
    (hvar : ∃ i j, r i ≠ r j) (observed : ℕ → ℝ) (C : ℝ)
    (hobserved : ∀ k, observed k ≤ C) :
    ¬ ∃ B : ℝ, ∀ k : ℕ, finiteEscortHiddenLoss w r observed k ≤ B := by
  rintro ⟨B, hB⟩
  have htotal : ∃ D : ℝ, ∀ k : ℕ,
      finiteTiltJeffreysReal w r k (-k) ≤ D := by
    refine ⟨B + C, fun k => ?_⟩
    have hhidden := hB k
    have hobserved_k := hobserved k
    unfold finiteEscortHiddenLoss at hhidden
    linarith
  have hconstant :=
    (finiteTiltJeffreysReflection_bounded_iff_score_constant hw hsum).mp htotal
  obtain ⟨i, j, hij⟩ := hvar
  exact hij (hconstant i j)

end GaloisForLFunctions.HTGeometry
