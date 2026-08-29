import GaloisForLFunctions.HTGeometry.MahlerPerfectNoTelescoper

/-!
# No telescoper for the reduced-trace increment

Expanding the two-variable base in the twisting coordinate decouples a putative telescoping
identity into one equation for each power of the coordinate.  The equation carried by the power
`h^(-(j+1))` is a two-term inhomogeneous Mahler equation in the perfect base with multiplier
`p^(j+1)`, whose resonance is `−c·p^j·(p−1)²`; it is nonzero whenever the coefficient `c` is,
so no nonzero constant-coefficient combination of the increment's jets telescopes.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem single_neg_one_pow {R : Type*} [Field R] (m : ℕ) :
    (HahnSeries.single (-1 : ℤ) (1 : R)) ^ m = HahnSeries.single (-(m : ℤ)) 1 := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, neg_zero, HahnSeries.single_zero_one]
  | succ m ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single, mul_one]
      congr 1
      push_cast
      ring

theorem coeff_baseExp_dilation [CharZero k] (p : ℕ) (hp : 1 < p) (y : MahlerPBase k p hp)
    (n : ℤ) :
    (algebraMap (MahlerPBase k p hp) (LaurentSeries (perfectBase (k := k) p hp))
        (mahlerPBaseDilation p hp y)).coeff n
      = (perfectConst p hp (((p : k))⁻¹)) ^ n
        * perfectBaseEquiv p hp
          ((algebraMap (MahlerPBase k p hp)
            (LaurentSeries (perfectBase (k := k) p hp)) y).coeff n) := by
  rw [mahlerPBaseDilation, ratFuncTwistEquiv_apply, algebraMap_ratFuncTwist, hahnTwistHom_apply,
    coeff_hahnTwist, laurentChar_apply]
  rfl

theorem coeff_baseExp_increment (p : ℕ) (hp : 1 < p) (B : perfectBase (k := k) p hp) (m : ℕ)
    (n : ℤ) :
    (algebraMap (MahlerPBase k p hp) (LaurentSeries (perfectBase (k := k) p hp))
        (algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp) B
          * ((RatFunc.X : MahlerPBase k p hp)⁻¹) ^ m)).coeff n
      = if n = -(m : ℤ) then B else 0 := by
  rw [map_mul, algebraMap_const_laurentSeries, map_pow, algebraMap_ratFuncX_inv,
    single_neg_one_pow, HahnSeries.single_mul_single, zero_add, mul_one]
  by_cases h : n = -(m : ℤ)
  · subst h
    rw [HahnSeries.coeff_single_same, if_pos rfl]
  · rw [if_neg h]
    exact HahnSeries.coeff_single_of_ne h

/-! ## The telescoper obstruction in the two-variable base -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **No nonzero constant-coefficient combination of the reduced-trace increment's jets is a
coboundary of the Mahler substitution in the two-variable base.** -/
theorem no_traceIncrement_telescoper [CharZero k] (p : ℕ) (hp : 1 < p)
    (c : (Unit × ℕ) →₀ k) (hc : c ≠ 0) (y : MahlerPBase k p hp) :
    letI := perfectAlgebra (k := k) p hp
    letI := perfectDifferential (k := k) p hp
    letI := mahlerPBaseDifferential (k := k) p hp
    mahlerPBaseDilation p hp y - y ≠
      Finsupp.linearCombination (MahlerPBase k p hp)
        (fun q : Unit × ℕ => differentialJet q.2 (traceIncrement p hp))
        (Finsupp.mapRange (algebraMap k (MahlerPBase k p hp)) (map_zero _) c) := by
  letI := perfectAlgebra (k := k) p hp
  letI := perfectDifferential (k := k) p hp
  letI := mahlerPBaseDifferential (k := k) p hp
  classical
  intro heq
  obtain ⟨q₀, hq₀⟩ : ∃ q : Unit × ℕ, c q ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Finsupp.ext h)
  set j₀ : ℕ := q₀.2 with hj₀def
  have hq₀eq : (((), j₀) : Unit × ℕ) = q₀ := Prod.ext (Subsingleton.elim _ _) rfl
  have hcj : c ((), j₀) ≠ 0 := by rw [hq₀eq]; exact hq₀
  -- the jets of the increment, term by term
  have hterm : ∀ q : Unit × ℕ,
      (algebraMap k (MahlerPBase k p hp) (c q)) • differentialJet q.2 (traceIncrement p hp)
        = algebraMap (perfectBase (k := k) p hp) (MahlerPBase k p hp)
            (perfectConst p hp (c q) * traceCoeff p hp q.2)
          * ((RatFunc.X : MahlerPBase k p hp)⁻¹) ^ (q.2 + 1) := by
    intro q
    rw [differentialJet_traceIncrement, Algebra.smul_def, map_mul, ← mul_assoc]
    congr 2
  -- expand the identity in the twisting coordinate
  have hexp := congrArg
    (fun x : MahlerPBase k p hp =>
      (algebraMap (MahlerPBase k p hp) (LaurentSeries (perfectBase (k := k) p hp)) x).coeff
        (-((j₀ : ℤ) + 1))) heq
  rw [map_sub, HahnSeries.coeff_sub, coeff_baseExp_dilation] at hexp
  have hzs : ∀ q : Unit × ℕ,
      (0 : MahlerPBase k p hp) • differentialJet q.2 (traceIncrement (k := k) p hp)
        = (0 : MahlerPBase k p hp) :=
    fun q => zero_smul (MahlerPBase k p hp) (differentialJet q.2 (traceIncrement (k := k) p hp))
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index hzs,
    Finsupp.sum, map_sum, HahnSeries.coeff_sum] at hexp
  have hrhs : ∑ q ∈ c.support,
      (algebraMap (MahlerPBase k p hp) (LaurentSeries (perfectBase (k := k) p hp))
        ((algebraMap k (MahlerPBase k p hp) (c q)) •
          differentialJet q.2 (traceIncrement p hp))).coeff (-((j₀ : ℤ) + 1))
      = perfectConst p hp (c ((), j₀)) * traceCoeff p hp j₀ := by
    have hpoint : ∀ q ∈ c.support,
        (algebraMap (MahlerPBase k p hp) (LaurentSeries (perfectBase (k := k) p hp))
          ((algebraMap k (MahlerPBase k p hp) (c q)) •
            differentialJet q.2 (traceIncrement p hp))).coeff (-((j₀ : ℤ) + 1))
        = if q = ((), j₀) then perfectConst p hp (c ((), j₀)) * traceCoeff p hp j₀ else 0 := by
      intro q _
      rw [hterm q, coeff_baseExp_increment]
      by_cases hq : q = ((), j₀)
      · subst hq
        rw [if_pos rfl, if_pos (by push_cast; ring)]
      · rw [if_neg hq, if_neg ?_]
        intro hcon
        refine hq (Prod.ext (Subsingleton.elim _ _) ?_)
        have : ((q.2 : ℤ) + 1) = ((j₀ : ℤ) + 1) := by
          have := neg_injective hcon
          push_cast at this ⊢
          linarith
        exact_mod_cast (by linarith : (q.2 : ℤ) = (j₀ : ℤ))
    rw [Finset.sum_congr rfl hpoint, Finset.sum_ite_eq' c.support (((), j₀) : Unit × ℕ)]
    rw [if_pos (Finsupp.mem_support_iff.mpr hcj)]
  rw [hrhs] at hexp
  -- read the identity off in the perfect base
  have hzpow : (perfectConst p hp (((p : k))⁻¹)) ^ (-((j₀ : ℤ) + 1))
      = perfectConst p hp (((p : k)) ^ (j₀ + 1)) := by
    have hpk : ((p : k)) ≠ 0 := by
      have : (0 : ℕ) < p := by omega
      exact Nat.cast_ne_zero.mpr this.ne'
    have hmap : ∀ x : k, (algebraMap k (perfectBase (k := k) p hp) x) = perfectConst p hp x :=
      fun _ => rfl
    rw [← hmap, ← map_zpow₀, ← hmap]
    congr 1
    rw [inv_zpow, ← zpow_neg, neg_neg,
      show ((j₀ : ℤ) + 1) = ((j₀ + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
  rw [hzpow] at hexp
  refine no_perfectBase_telescoper p hp (j₀ + 1)
    (-(c ((), j₀) * (((p : k)) - 2))) (-(c ((), j₀) * ((p : k)) ^ j₀)) ?_
    ((algebraMap (MahlerPBase k p hp)
      (LaurentSeries (perfectBase (k := k) p hp)) y).coeff (-((j₀ : ℤ) + 1))) ?_
  · intro hcon
    have hpk : ((p : k)) ≠ 0 := by
      have : (0 : ℕ) < p := by omega
      exact Nat.cast_ne_zero.mpr this.ne'
    have hp1 : ((p : k)) - 1 ≠ 0 := by
      intro h1
      have : ((p : k)) = 1 := by linear_combination h1
      have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact this
      have := Nat.cast_injective (R := k) h2
      omega
    apply hcj
    have hfac : ((p : k)) ^ (j₀ + 1) * (-(c ((), j₀) * (((p : k)) - 2)))
        + (-(c ((), j₀) * ((p : k)) ^ j₀))
        = -(c ((), j₀) * ((p : k)) ^ j₀ * (((p : k)) - 1) ^ 2) := by
      rw [pow_succ]
      ring
    rw [hfac] at hcon
    have hzero : c ((), j₀) * ((p : k)) ^ j₀ * (((p : k)) - 1) ^ 2 = 0 := by
      linear_combination -hcon
    rcases mul_eq_zero.mp hzero with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' (pow_ne_zero _ hpk)
    · exact absurd h (pow_ne_zero _ hp1)
  · rw [hexp, traceCoeff]
    have hmul : ∀ x z : k, perfectConst (k := k) p hp x * perfectConst p hp z
        = perfectConst p hp (x * z) := perfectConst_mul p hp
    have hneg : ∀ x : k, perfectConst (k := k) p hp (-x) = -perfectConst p hp x := by
      intro x
      refine Subtype.ext ?_
      show (HahnSeries.C (-x) : HahnSeries ℚ k) = -HahnSeries.C x
      rw [map_neg]
    rw [mul_neg, mul_add, ← mul_assoc, ← mul_assoc, hmul, hmul, hneg, hneg]
    ring

end

end GaloisForLFunctions.HTGeometry
