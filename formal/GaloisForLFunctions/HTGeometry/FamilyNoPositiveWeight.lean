import GaloisForLFunctions.HTGeometry.FlatFamilyFibres

/-!
# The family carries no positive weight, and what that forces

With nonpositive weights the extra variable is the only source of negative weight and nothing has
positive weight:

```text
famComp_eq_zero_of_pos          the homogeneous parts vanish above weight zero
familyIdeal_sub_one_saturated   ** the family ring has no (t-1)-torsion **
familyIdeal_separated           ** and it is separated for t **
```

Both consequences are the same downward sweep.  Multiplying by `t - 1` shifts the homogeneous parts
by one and subtracts, so the dehomogenizations satisfy a difference relation that starts at zero in
positive weight and propagates downwards; multiplying by `t ^ n` shifts by `n`, so a part in weight
`d` is unaffected by the correction once `n` exceeds `-d`.

These are the two graded facts the specialisation argument needs at the level of the ring.  The same
two facts about `Ext` — that `t`-divisibility kills a graded module bounded above, and that `t - 1`
acts injectively on one — are what turn depth on the special fibre into depth on the generic fibre;
they need `Ext` to carry the weight grading, which mathlib's `Ext` does not.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- With nonpositive weights the family carries no positive weight. -/
theorem famComp_eq_zero_of_pos {w : σ → ℤ} (hw : ∀ i, w i ≤ 0) {d : ℤ} (hd : 0 < d)
    (F : Polynomial (MvPolynomial σ K)) : famComp w d F = 0 := by
  refine Polynomial.ext fun j => ?_
  rw [famComp_coeff, Polynomial.coeff_zero]
  ext γ
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
  have hγ : Finsupp.weight w γ ≤ 0 := weight_nonpos hw γ
  rw [if_neg (by omega)]

/-- **The family ring has no `(t-1)`-torsion.**  Its homogeneous parts vanish in positive weight,
and multiplying by `t - 1` shifts them by one, so the dehomogenizations are determined downwards
from zero. -/
theorem familyIdeal_sub_one_saturated {w : σ → ℤ} (hw : ∀ i, w i ≤ 0)
    {I : Ideal (MvPolynomial σ K)} {F : Polynomial (MvPolynomial σ K)}
    (h : (Polynomial.X - 1) * F ∈ familyIdeal w I) :
    F ∈ familyIdeal w I := by
  rw [mem_familyIdeal_iff] at h ⊢
  have hstep : ∀ d : ℤ,
      Polynomial.eval 1 (famComp w (d + 1) F) - Polynomial.eval 1 (famComp w d F) ∈ I := by
    intro d
    have hd := h d
    have hexp : famComp w d ((Polynomial.X - 1) * F)
        = Polynomial.X * famComp w (d + 1) F - famComp w d F := by
      have h1 : (Polynomial.X - 1) * F = Polynomial.X * F - F := by ring
      rw [h1, show Polynomial.X * F - F = Polynomial.X * F + (-1 : Polynomial (MvPolynomial σ K)) * F
        from by ring, famComp_add,
        famComp_mul_left_of_isFamHomog (isFamHomog_X w),
        show d - (-1) = d + 1 from by ring]
      have hneg : famComp w d ((-1 : Polynomial (MvPolynomial σ K)) * F) = - famComp w d F := by
        rw [show ((-1 : Polynomial (MvPolynomial σ K)) * F) = -F from by ring]
        refine Polynomial.ext fun j => ?_
        rw [famComp_coeff, Polynomial.coeff_neg, map_neg, Polynomial.coeff_neg, famComp_coeff]
      rw [hneg]
      ring
    rw [hexp, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, one_mul] at hd
    exact hd
  have hzero : ∀ d : ℤ, 0 < d → Polynomial.eval 1 (famComp w d F) ∈ I := by
    intro d hd
    rw [famComp_eq_zero_of_pos hw hd, Polynomial.eval_zero]
    exact Ideal.zero_mem _
  have hneg : ∀ k : ℕ, Polynomial.eval 1 (famComp w (-(k : ℤ)) F) ∈ I := by
    intro k
    induction k with
    | zero =>
      have h1 := hstep 0
      have h2 := hzero 1 (by norm_num)
      have : Polynomial.eval 1 (famComp w (0 + 1) F) = Polynomial.eval 1 (famComp w 1 F) := by
        norm_num
      rw [this] at h1
      have := Ideal.sub_mem I h2 h1
      simpa using this
    | succ k ih =>
      have h1 := hstep (-((k : ℤ) + 1))
      rw [show -((k : ℤ) + 1) + 1 = -(k : ℤ) from by ring] at h1
      have := Ideal.sub_mem I ih h1
      have hcast : (-((k : ℤ) + 1)) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at this
      simpa using this
  intro d
  rcases lt_or_ge 0 d with hd | hd
  · exact hzero d hd
  · have hk : d = -((-d).toNat : ℤ) := by omega
    rw [hk]
    exact hneg _

theorem isFamHomog_X_pow (w : σ → ℤ) (n : ℕ) :
    IsFamHomog w (-(n : ℤ)) ((Polynomial.X : Polynomial (MvPolynomial σ K)) ^ n) := by
  classical
  intro j
  rw [Polynomial.coeff_X_pow]
  by_cases hj : j = n
  · rw [if_pos hj, hj]
    intro γ hγ
    rw [MvPolynomial.coeff_one] at hγ
    by_cases hγ0 : γ = 0
    · rw [hγ0]
      simp
    · rw [if_neg (fun h => hγ0 h.symm)] at hγ
      exact absurd rfl hγ
  · rw [if_neg hj]
    intro γ hγ
    simp at hγ

/-- **The family ring is separated for the extra variable.**  Positive weights are absent, so a
polynomial lying in every power of the extra variable modulo the family ideal already lies in the
family ideal. -/
theorem familyIdeal_separated {w : σ → ℤ} (hw : ∀ i, w i ≤ 0)
    {I : Ideal (MvPolynomial σ K)} {F : Polynomial (MvPolynomial σ K)}
    (h : ∀ n : ℕ, F ∈ Ideal.span {(Polynomial.X : Polynomial (MvPolynomial σ K)) ^ n}
      ⊔ familyIdeal w I) :
    F ∈ familyIdeal w I := by
  rw [mem_familyIdeal_iff]
  intro d
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < d + (n : ℤ) := by
    refine ⟨(1 - d).toNat, ?_⟩
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h n)
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton.mp ha
  have hFa : F = Polynomial.X ^ n * G + b := by rw [← hab, hG]
  rw [hFa, famComp_add, famComp_mul_left_of_isFamHomog (isFamHomog_X_pow w n),
    show d - -(n : ℤ) = d + (n : ℤ) from by ring,
    famComp_eq_zero_of_pos hw hn, mul_zero, zero_add]
  exact (mem_familyIdeal_iff.mp hb) d

end GaloisForLFunctions.HTGeometry
