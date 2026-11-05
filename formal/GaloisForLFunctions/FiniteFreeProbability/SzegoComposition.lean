import GaloisForLFunctions.FiniteFreeProbability.WalshHalfPlaneTheorem

/-!
# Szegő's composition theorem: the multiplicative finite free convolution

For polynomials of degree `≤ d` write `p = Σ_k C(d,k) a_k X^k`, `q = Σ_k C(d,k) b_k X^k`. The
Schur–Szegő composition (the multiplicative finite free convolution in binomial normalization) is

`p ⊠_d q = Σ_k C(d,k) a_k b_k X^k`.

It is the Hadamard product of binomially normalized coefficient sequences; Jensen polynomials of
Hadamard products of sequences are exactly such compositions.

**Theorem (Szegő).** If `p` has degree `d` and only real roots, and `q` has degree `d` and only
roots in `(−∞, 0]`, then `p ⊠_d q` has only real roots.

Mechanism. At `z` with `Im z > 0`, `d! (p ⊠_d q)(z)` is the apolarity pairing of `p` with the
reflected dilate `y^d q(z/y) = lc · Π (z − β y)`, whose roots `z/β` (`β < 0`) lie in the open lower
half-plane, while factors with `β = 0` are nonzero constants. The half-plane apolarity theorem
behind Walsh's theorem then makes the pairing nonzero.
-/

open Polynomial Complex Finset

namespace FiniteFreeProbability

noncomputable section

section Def

variable {K : Type*} [Field K]

/-- The Schur–Szegő composition `p ⊠_d q = Σ_k p_k q_k / C(d,k) · X^k`. -/
def ffMul (d : ℕ) (p q : K[X]) : K[X] :=
  ∑ k ∈ range (d + 1), C (p.coeff k * q.coeff k / (d.choose k : K)) * X ^ k

theorem ffMul_map {L : Type*} [Field L] (φ : K →+* L) (d : ℕ) (p q : K[X]) :
    (ffMul d p q).map φ = ffMul d (p.map φ) (q.map φ) := by
  simp [ffMul, Polynomial.map_sum, coeff_map, map_div₀]

theorem natDegree_ffMul_le (d : ℕ) (p q : K[X]) : (ffMul d p q).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

theorem coeff_comp_C_mul_X (q : K[X]) (z : K) (m : ℕ) :
    (q.comp (C z * X)).coeff m = q.coeff m * z ^ m := by
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow]
  rw [Polynomial.sum_comp, finsetSum_coeff]
  simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb; simp [hb.symm]
  · intro hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [if_pos rfl, coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

end Def

/-- **The Szegő pairing.** `d! (p ⊠_d q)(z) = ⟨p, y^d q(z/y)⟩_d`. -/
theorem apolarPairing_reflect_comp (d : ℕ) (p q : ℂ[X]) (z : ℂ) :
    apolarPairing d p (reflect d (q.comp (C z * X))) =
      (d.factorial : ℂ) * (ffMul d p q).eval z := by
  rw [apolarPairing, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ffMul, eval_finsetSum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only
  rw [coeff_reflect, revAt_le (Nat.sub_le d k), Nat.sub_sub_self hk', coeff_comp_C_mul_X,
    eval_mul, eval_C, eval_pow, eval_X]
  have hch : (d.choose k : ℂ) * (k.factorial : ℂ) * ((d - k).factorial : ℂ) = d.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hc0 : (d.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  rw [← hch]
  field_simp

/-- Reflection of a product of `d` dilated linear factors. -/
theorem reflect_prod_dilate (z : ℂ) (t : Multiset ℂ) :
    reflect (Multiset.card t) ((t.map fun β => C z * X - C β).prod) =
      (t.map fun β => C z - C β * X).prod := by
  have hlin : ∀ β : ℂ, (C z * X - C β).natDegree ≤ 1 := fun β =>
    (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  induction t using Multiset.induction_on with
  | empty => simp
  | cons β t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      reflect_mul _ _ (F := 1) (G := Multiset.card t)]
    · rw [ih, Multiset.map_cons, Multiset.prod_cons]
      congr 1
      ext i
      rw [coeff_reflect]
      rcases i with _ | _ | i
      · simp
      · simp
      · rw [revAt, Function.Embedding.coeFn_mk, if_neg (by omega)]
        simp
    · exact hlin β
    · refine (natDegree_multiset_prod_le _).trans ?_
      rw [Multiset.map_map]
      refine (Multiset.sum_le_card_nsmul _ 1 fun x hx => ?_).trans (by simp)
      obtain ⟨β', _, rfl⟩ := Multiset.mem_map.1 hx
      exact hlin β'

/-- The dilated reflected factors `z − β y` with `β ≤ 0` (real) and `Im z > 0` are a nonzero
constant times monic factors whose roots `z/β` lie in the open lower half-plane. -/
theorem prod_reflected_factors {z : ℂ} (hz : 0 < z.im) :
    ∀ t : Multiset ℂ, (∀ β ∈ t, β.im = 0 ∧ β.re ≤ 0) →
      ∃ (a : ℂ) (s : Multiset ℂ), a ≠ 0 ∧ Multiset.card s ≤ Multiset.card t ∧
        (∀ μ ∈ s, μ.im < 0) ∧
        (t.map fun β => C z - C β * X).prod = C a * (s.map fun μ => X - C μ).prod := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  intro t
  induction t using Multiset.induction_on with
  | empty => intro _; exact ⟨1, 0, one_ne_zero, le_rfl, by simp, by simp⟩
  | cons β t ih =>
    intro hβ
    obtain ⟨a, s, ha, hs, hsim, hprod⟩ := ih fun b hb => hβ b (Multiset.mem_cons_of_mem hb)
    obtain ⟨hβim, hβre⟩ := hβ β (Multiset.mem_cons_self β t)
    rw [Multiset.map_cons, Multiset.prod_cons, hprod]
    by_cases hb0 : β = 0
    · refine ⟨z * a, s, mul_ne_zero hz0 ha, by rw [Multiset.card_cons]; omega, hsim, ?_⟩
      rw [hb0]; simp [mul_assoc]
    · refine ⟨-β * a, (z / β) ::ₘ s, mul_ne_zero (neg_ne_zero.2 hb0) ha,
        by rw [Multiset.card_cons, Multiset.card_cons]; omega, fun μ hμ => ?_, ?_⟩
      · rcases Multiset.mem_cons.1 hμ with rfl | hμ
        · have hβreal : β = (β.re : ℂ) := Complex.ext (by simp) (by simp [hβim])
          have hβneg : β.re < 0 := lt_of_le_of_ne hβre (fun h => hb0 (by rw [hβreal, h]; simp))
          rw [hβreal, Complex.div_ofReal_im]
          exact div_neg_of_pos_of_neg hz hβneg
        · exact hsim μ hμ
      · rw [Multiset.map_cons, Multiset.prod_cons]
        have : C z - C β * X = C (-β) * (X - C (z / β)) := by
          rw [mul_sub, ← C_mul, show -β * (z / β) = -z by field_simp]
          simp only [map_neg]; ring
        rw [this, map_mul]; ring

/-- **Szegő's theorem, half-plane form.** -/
theorem eval_ffMul_ne_zero {d : ℕ} {p q : ℂ[X]} (hp0 : p ≠ 0) (hpd : p.natDegree = d)
    (hpr : ∀ r, p.IsRoot r → r.im ≤ 0) (hq0 : q ≠ 0) (hqd : q.natDegree = d)
    (hqr : ∀ β, q.IsRoot β → β.im = 0 ∧ β.re ≤ 0) {z : ℂ} (hz : 0 < z.im) :
    (ffMul d p q).eval z ≠ 0 := by
  have hfac := (IsAlgClosed.splits q).eq_prod_roots
  have hcard : Multiset.card q.roots = d := by
    rw [← hqd]; exact splits_iff_card_roots.1 (IsAlgClosed.splits q)
  have hcomp : q.comp (C z * X) =
      C q.leadingCoeff * (q.roots.map fun β => C z * X - C β).prod := by
    conv_lhs => rw [hfac]
    rw [mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
    simp
  have hrefl : reflect d (q.comp (C z * X)) =
      C q.leadingCoeff * (q.roots.map fun β => C z - C β * X).prod := by
    rw [hcomp, reflect_C_mul, ← hcard, reflect_prod_dilate]
  obtain ⟨a, s, ha, hs, hsim, hprod⟩ := prod_reflected_factors hz q.roots
    (fun β hβ => hqr β ((mem_roots hq0).1 hβ))
  have hfinal : reflect d (q.comp (C z * X)) =
      C (q.leadingCoeff * a) * (s.map fun μ => X - C μ).prod := by
    rw [hrefl, hprod, map_mul]; ring
  have hpair := apolarPairing_ne_zero (c := 0) s d p (q.leadingCoeff * a)
    (mul_ne_zero (leadingCoeff_ne_zero.2 hq0) ha) (by omega) hp0 hpd hpr
    (fun μ hμ => by simpa using hsim μ hμ)
  rw [← hfinal, apolarPairing_reflect_comp] at hpair
  exact fun h => hpair (by rw [h, mul_zero])

/-- **Szegő's composition theorem.** For real `p` of degree `d` with only real roots and real `q`
of degree `d` with only roots in `(−∞, 0]`, `p ⊠_d q` has only real roots. -/
theorem splits_ffMul {d : ℕ} {p q : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0) (hpd : p.natDegree = d)
    (hq : q.Splits) (hq0 : q ≠ 0) (hqd : q.natDegree = d) (hqneg : ∀ β ∈ q.roots, β ≤ 0) :
    (ffMul d p q).Splits := by
  set φ := algebraMap ℝ ℂ
  have hinj : Function.Injective φ := φ.injective
  have hp0' : p.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hp0
  have hq0' : q.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hq0
  have hpr : ∀ r, (p.map φ).IsRoot r → r.im ≤ 0 := by
    intro r hr
    have : (aeval r p : ℂ) = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    exact (GaloisForLFunctions.HTGeometry.im_eq_zero_of_splits hp hp0 this).le
  have hqr : ∀ β, (q.map φ).IsRoot β → β.im = 0 ∧ β.re ≤ 0 := by
    intro β hβ
    have hrootsmap : (q.map φ).roots = q.roots.map φ := hq.roots_map φ
    have hmem : β ∈ (q.map φ).roots := (mem_roots hq0').2 hβ
    rw [hrootsmap] at hmem
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hmem
    exact ⟨by simp [φ], by simpa [φ] using hqneg b hb⟩
  have hle : ∀ r : ℂ, (aeval r (ffMul d p q) : ℂ) = 0 → r.im ≤ 0 := by
    intro r hr
    by_contra hpos
    push Not at hpos
    have hr' : (ffMul d (p.map φ) (q.map φ)).eval r = 0 := by
      rw [← ffMul_map, ← eval₂_eq_eval_map, ← aeval_def]; exact hr
    exact eval_ffMul_ne_zero hp0' (by rw [natDegree_map_eq_of_injective hinj, hpd]) hpr hq0'
      (by rw [natDegree_map_eq_of_injective hinj, hqd]) hqr hpos hr'
  refine GaloisForLFunctions.HTGeometry.splits_of_forall_complex_root_real d _
    (natDegree_ffMul_le d p q) fun r hr => ?_
  have hconj : (aeval (starRingEnd ℂ r) (ffMul d p q) : ℂ) = 0 := by
    have h := Polynomial.aeval_algHom_apply Complex.conjAe r (ffMul d p q)
    simpa [hr] using h
  have h1 := hle r hr
  have h2 := hle _ hconj
  simp only [conj_im] at h2
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.splits_ffMul
