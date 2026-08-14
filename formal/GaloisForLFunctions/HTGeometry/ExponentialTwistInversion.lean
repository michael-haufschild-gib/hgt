import GaloisForLFunctions.HTGeometry.ExponentialTwist

/-!
# Inversion of the exponential twist

The twist `w ↦ (∑_n (-A)^n w_{n+k} / n!)_k` is inverted by the opposite twist: applying
`∑_k A^k (·)/k!` to the twisted family returns `w 0`.  The mechanism is Fubini for the double
family indexed by `(k,n)`, reindexed by the total degree `j = k+n`, where the coefficient collapses
to the alternating binomial sum `∑_{n ≤ j} (-1)^n C(j,n)`, which vanishes except at `j = 0`.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- A power of the negative of an operator is the alternating multiple of the power. -/
theorem neg_pow_apply (A : X →L[ℂ] X) (n : ℕ) (y : X) :
    ((-A) ^ n) y = ((-1 : ℂ) ^ n) • ((A ^ n) y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((-A) ^ (n + 1)) y = (-A) (((-A) ^ n) y) := by rw [pow_succ']; rfl
    have h2 : ((A) ^ (n + 1)) y = A ((A ^ n) y) := by rw [pow_succ']; rfl
    rw [h1, ih, h2]
    calc (-A) (((-1 : ℂ) ^ n) • ((A ^ n) y))
        = -(A (((-1 : ℂ) ^ n) • ((A ^ n) y))) := rfl
      _ = -(((-1 : ℂ) ^ n) • (A ((A ^ n) y))) := by rw [map_smul]
      _ = ((-1 : ℂ) ^ (n + 1)) • (A ((A ^ n) y)) := by
          rw [pow_succ, mul_neg_one, neg_smul]

omit [CompleteSpace X] in
theorem pow_add_apply (A : X →L[ℂ] X) (k n : ℕ) (y : X) :
    (A ^ (k + n)) y = (A ^ k) ((A ^ n) y) := by
  rw [pow_add]; rfl

/-- The double family inverting the exponential twist. -/
def twistInvTerm (A : X →L[ℂ] X) (w : ℕ → X) (p : ℕ × ℕ) : X :=
  (((p.1.factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ p.2) •
    ((A ^ (p.1 + p.2)) (w (p.1 + p.2)))

/-- The inverting family reindexed by the total degree. -/
def twistInvGrouped (A : X →L[ℂ] X) (w : ℕ → X) (p : ℕ × ℕ) : X :=
  if p.2 ≤ p.1 then
    ((((p.1 - p.2).factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ p.2) •
      ((A ^ p.1) (w p.1))
  else 0

omit [CompleteSpace X] in
/-- The inverting family is the twist term composed with the opposite twist. -/
theorem twistInvTerm_eq (A : X →L[ℂ] X) (w : ℕ → X) (k n : ℕ) :
    twistInvTerm A w (k, n)
      = ((k.factorial : ℂ))⁻¹ •
          ((A ^ k) (((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k))))) := by
  rw [twistInvTerm, neg_pow_apply, map_smul, map_smul, smul_smul, smul_smul,
    pow_add_apply, add_comm n k]

omit [CompleteSpace X] in
theorem twistInvGrouped_reindex (A : X →L[ℂ] X) (w : ℕ → X) (p : ℕ × ℕ) :
    twistInvGrouped A w (p.1 + p.2, p.2) = twistInvTerm A w p := by
  have hle : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
  simp only [twistInvGrouped, twistInvTerm, if_pos hle, Nat.add_sub_cancel]

omit [CompleteSpace X] in
/-- The norm bound making both families summable. -/
theorem norm_twistInvTerm_le (A : X →L[ℂ] X) (w : ℕ → X) {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbd : ∀ j, ‖w j‖ ≤ C * D ^ j) (p : ℕ × ℕ) :
    ‖twistInvTerm A w p‖
      ≤ (C * ((‖A‖ * D) ^ p.1 / (p.1.factorial : ℝ))) * ((‖A‖ * D) ^ p.2 / (p.2.factorial : ℝ)) := by
  have hcoef : ‖(((p.1.factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ p.2)‖
      = ((p.1.factorial : ℝ))⁻¹ * ((p.2.factorial : ℝ))⁻¹ := by
    simp
  have hvec : ‖(A ^ (p.1 + p.2)) (w (p.1 + p.2))‖ ≤ ‖A‖ ^ (p.1 + p.2) * (C * D ^ (p.1 + p.2)) := by
    refine le_trans (norm_pow_apply_le A (p.1 + p.2) _) ?_
    exact mul_le_mul_of_nonneg_left (hbd _) (by positivity)
  rw [twistInvTerm, norm_smul, hcoef]
  calc ((p.1.factorial : ℝ))⁻¹ * ((p.2.factorial : ℝ))⁻¹ * ‖(A ^ (p.1 + p.2)) (w (p.1 + p.2))‖
      ≤ ((p.1.factorial : ℝ))⁻¹ * ((p.2.factorial : ℝ))⁻¹
          * (‖A‖ ^ (p.1 + p.2) * (C * D ^ (p.1 + p.2))) := by
        refine mul_le_mul_of_nonneg_left hvec ?_
        positivity
    _ = (C * ((‖A‖ * D) ^ p.1 / (p.1.factorial : ℝ)))
          * ((‖A‖ * D) ^ p.2 / (p.2.factorial : ℝ)) := by
        rw [mul_pow, mul_pow, pow_add, pow_add, div_eq_mul_inv, div_eq_mul_inv]
        ring

theorem summable_twistInvTerm (A : X →L[ℂ] X) (w : ℕ → X) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbd : ∀ j, ‖w j‖ ≤ C * D ^ j) : Summable (twistInvTerm A w) := by
  refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ =>
      (C * ((‖A‖ * D) ^ p.1 / (p.1.factorial : ℝ))) * ((‖A‖ * D) ^ p.2 / (p.2.factorial : ℝ)))
    ?_ (norm_twistInvTerm_le A w hC hD hbd)
  refine Summable.mul_of_nonneg
    ((Real.summable_pow_div_factorial (‖A‖ * D)).mul_left C)
    (Real.summable_pow_div_factorial (‖A‖ * D)) (fun k => ?_) (fun n => ?_)
  · have : (0 : ℝ) ≤ (‖A‖ * D) ^ k / (k.factorial : ℝ) := by positivity
    exact mul_nonneg hC this
  · positivity

theorem summable_twistInvGrouped (A : X →L[ℂ] X) (w : ℕ → X) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbd : ∀ j, ‖w j‖ ≤ C * D ^ j) : Summable (twistInvGrouped A w) := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + p.2, p.2)) := by
    rintro ⟨k, n⟩ ⟨k', n'⟩ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    subst h2
    have hkk : k = k' := by omega
    subst hkk
    rfl
  have hoff : ∀ x ∉ Set.range (fun p : ℕ × ℕ => (p.1 + p.2, p.2)), twistInvGrouped A w x = 0 := by
    intro x hx
    by_cases hle : x.2 ≤ x.1
    · have heq : ((x.1 - x.2 + x.2 : ℕ), x.2) = x := by
        have h : x.1 - x.2 + x.2 = x.1 := by omega
        rw [h]
      exact absurd ⟨(x.1 - x.2, x.2), heq⟩ hx
    · rw [twistInvGrouped, if_neg hle]
  refine (hinj.summable_iff hoff).mp ?_
  have hfun : (twistInvGrouped A w ∘ fun p : ℕ × ℕ => (p.1 + p.2, p.2)) = twistInvTerm A w :=
    funext fun p => twistInvGrouped_reindex A w p
  rw [hfun]
  exact summable_twistInvTerm A w hC hD hbd

theorem summable_twistInner (A : X →L[ℂ] X) (w : ℕ → X) {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbd : ∀ j, ‖w j‖ ≤ C * D ^ j) (k : ℕ) :
    Summable (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k)))) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (C * D ^ k) * ((‖A‖ * D) ^ n / (n.factorial : ℝ)))
    ((Real.summable_pow_div_factorial (‖A‖ * D)).mul_left (C * D ^ k)) fun n => ?_
  have hvec : ‖((-A) ^ n) (w (n + k))‖ ≤ ‖A‖ ^ n * (C * D ^ (n + k)) := by
    refine le_trans (norm_pow_apply_le (-A) n _) ?_
    rw [norm_neg]
    exact mul_le_mul_of_nonneg_left (hbd _) (by positivity)
  rw [norm_smul]
  have hc : ‖((n.factorial : ℂ))⁻¹‖ = ((n.factorial : ℝ))⁻¹ := by simp
  rw [hc]
  calc ((n.factorial : ℝ))⁻¹ * ‖((-A) ^ n) (w (n + k))‖
      ≤ ((n.factorial : ℝ))⁻¹ * (‖A‖ ^ n * (C * D ^ (n + k))) := by
        refine mul_le_mul_of_nonneg_left hvec ?_
        positivity
    _ = (C * D ^ k) * ((‖A‖ * D) ^ n / (n.factorial : ℝ)) := by
        rw [mul_pow, pow_add, div_eq_mul_inv]
        ring

/-- The alternating binomial collapse of the grouped coefficient. -/
theorem sum_twistInvGrouped_coeff (j : ℕ) :
    (∑ n ∈ Finset.range (j + 1),
        ((((j - n).factorial : ℂ))⁻¹ * ((n.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ n))
      = if j = 0 then 1 else 0 := by
  have hstep : ∀ n ∈ Finset.range (j + 1),
      ((((j - n).factorial : ℂ))⁻¹ * ((n.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ n)
        = ((j.factorial : ℂ))⁻¹ * (((-1 : ℂ)) ^ n * ((j.choose n : ℕ) : ℂ)) := by
    intro n hn
    have hle : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hfac := Nat.choose_mul_factorial_mul_factorial hle
    have hcast : ((j.choose n : ℕ) : ℂ) * ((n.factorial : ℕ) : ℂ) * (((j - n).factorial : ℕ) : ℂ)
        = ((j.factorial : ℕ) : ℂ) := by
      exact_mod_cast congrArg (fun m : ℕ => ((m : ℂ))) hfac
    have h1 : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : ((((j - n)).factorial : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    field_simp
    rw [← hcast]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have halt : (∑ n ∈ Finset.range (j + 1), (((-1 : ℂ)) ^ n * ((j.choose n : ℕ) : ℂ)))
      = if j = 0 then 1 else 0 := by
    have h := Int.alternating_sum_range_choose (n := j)
    have hcast := congrArg (fun z : ℤ => ((z : ℂ))) h
    push_cast at hcast
    exact hcast
  rw [halt]
  by_cases hj : j = 0
  · subst hj
    simp
  · rw [if_neg hj, mul_zero]

/-- **Inversion of the exponential twist.**  The opposite twist applied to the twisted family of a
geometrically bounded sequence returns its initial term. -/
theorem tsum_twistInv (A : X →L[ℂ] X) (w : ℕ → X) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbd : ∀ j, ‖w j‖ ≤ C * D ^ j) :
    ∑' k : ℕ, ((k.factorial : ℂ))⁻¹ •
        ((A ^ k) (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k))))) = w 0 := by
  have hFsum : Summable (twistInvTerm A w) := summable_twistInvTerm A w hC hD hbd
  have hGsum : Summable (twistInvGrouped A w) := summable_twistInvGrouped A w hC hD hbd
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + p.2, p.2)) := by
    rintro ⟨k, n⟩ ⟨k', n'⟩ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    subst h2
    have hkk : k = k' := by omega
    subst hkk
    rfl
  -- the twisted sum, computed by fixing the outer index
  have houter : ∑' p : ℕ × ℕ, twistInvTerm A w p
      = ∑' k : ℕ, ((k.factorial : ℂ))⁻¹ •
          ((A ^ k) (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k))))) := by
    rw [hFsum.tsum_prod]
    refine tsum_congr fun k => ?_
    have hinner := summable_twistInner A w hC hD hbd k
    calc ∑' n : ℕ, twistInvTerm A w (k, n)
        = ∑' n : ℕ, ((k.factorial : ℂ))⁻¹ •
            ((A ^ k) (((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k))))) :=
          tsum_congr fun n => twistInvTerm_eq A w k n
      _ = ((k.factorial : ℂ))⁻¹ • ∑' n : ℕ,
            ((A ^ k) (((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k))))) := by
          refine Summable.tsum_const_smul _ ?_
          exact hinner.map (A ^ k) (A ^ k).continuous
      _ = ((k.factorial : ℂ))⁻¹ •
            ((A ^ k) (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • (((-A) ^ n) (w (n + k))))) := by
          rw [ContinuousLinearMap.map_tsum (A ^ k) hinner]
  -- the same sum, computed by fixing the total degree
  have hgrouped : ∑' p : ℕ × ℕ, twistInvTerm A w p = w 0 := by
    have hsupport : Function.support (twistInvGrouped A w)
        ⊆ Set.range (fun p : ℕ × ℕ => (p.1 + p.2, p.2)) := by
      intro x hx
      by_cases hle : x.2 ≤ x.1
      · have heq : ((x.1 - x.2 + x.2 : ℕ), x.2) = x := by
          have h : x.1 - x.2 + x.2 = x.1 := by omega
          rw [h]
        exact ⟨(x.1 - x.2, x.2), heq⟩
      · exact absurd (by rw [twistInvGrouped, if_neg hle] : twistInvGrouped A w x = 0) hx
    have hre : ∑' p : ℕ × ℕ, twistInvTerm A w p = ∑' q : ℕ × ℕ, twistInvGrouped A w q := by
      rw [← hinj.tsum_eq hsupport]
      exact tsum_congr fun p => (twistInvGrouped_reindex A w p).symm
    rw [hre, hGsum.tsum_prod]
    have hrow : ∀ j : ℕ, (∑' n : ℕ, twistInvGrouped A w (j, n))
        = (if j = 0 then (1 : ℂ) else 0) • ((A ^ j) (w j)) := by
      intro j
      have hfin : ∀ n ∉ Finset.range (j + 1), twistInvGrouped A w (j, n) = 0 := by
        intro n hn
        have : ¬ n ≤ j := by
          simp only [Finset.mem_range] at hn
          omega
        rw [twistInvGrouped, if_neg this]
      rw [tsum_eq_sum hfin]
      have hval : ∀ n ∈ Finset.range (j + 1), twistInvGrouped A w (j, n)
          = ((((j - n).factorial : ℂ))⁻¹ * ((n.factorial : ℂ))⁻¹ * (-1 : ℂ) ^ n)
              • ((A ^ j) (w j)) := by
        intro n hn
        have hle : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        rw [twistInvGrouped, if_pos hle]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_smul, sum_twistInvGrouped_coeff]
    rw [tsum_congr hrow]
    rw [tsum_eq_single 0]
    · simp
    · intro j hj
      rw [if_neg hj, zero_smul]
  rw [← houter, hgrouped]

end

end GaloisForLFunctions.HTGeometry
