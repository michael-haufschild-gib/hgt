import GaloisForLFunctions.HTGeometry.RationalPoleOrder

/-!
# The signed order of a rational function at a point

The order of a rational function at a point is the multiplicity of the point as a root of the
reduced numerator minus its multiplicity as a root of the reduced denominator.  It is a
homomorphism from the multiplicative group of the rational function field to the integers, it
vanishes exactly at the points which are neither zeros nor poles, and for a fixed nonzero function
it vanishes at all but finitely many points.

This is the divisor bookkeeping that an invariance relation `Q ∘ R · (R')^k = λ Q` is read through:
the relation transports orders along the map, so a point carrying a nonzero order propagates its
order along the whole orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The signed order of a rational function at a point. -/
def ratOrder (Q : RatFunc K) (c : K) : ℤ :=
  (rootMultiplicity c Q.num : ℤ) - (rootMultiplicity c Q.denom : ℤ)

theorem algebraMap_num_eq (x : RatFunc K) :
    algebraMap K[X] (RatFunc K) x.num = x * algebraMap K[X] (RatFunc K) x.denom := by
  have hden : algebraMap K[X] (RatFunc K) x.denom ≠ 0 := by
    simpa using (RatFunc.algebraMap_injective K).ne (RatFunc.denom_ne_zero x)
  have h := RatFunc.num_div_denom x
  rw [div_eq_iff hden] at h
  exact h

/-- Cross multiplication of the reduced representations of a product. -/
theorem num_denom_cross_mul (f g : RatFunc K) :
    (f * g).num * (f.denom * g.denom) = f.num * g.num * (f * g).denom := by
  refine RatFunc.algebraMap_injective K ?_
  rw [map_mul, map_mul, map_mul, map_mul, algebraMap_num_eq, algebraMap_num_eq,
    algebraMap_num_eq]
  ring

/-- **The order is additive.** -/
theorem ratOrder_mul {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (c : K) :
    ratOrder (f * g) c = ratOrder f c + ratOrder g c := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hfn : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hgn : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hfd : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hgd : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hfgn : (f * g).num ≠ 0 := RatFunc.num_ne_zero hfg
  have hfgd : (f * g).denom ≠ 0 := RatFunc.denom_ne_zero (f * g)
  have hcross := num_denom_cross_mul f g
  have hL : rootMultiplicity c ((f * g).num * (f.denom * g.denom))
      = rootMultiplicity c (f.num * g.num * (f * g).denom) := by rw [hcross]
  rw [rootMultiplicity_mul (by exact mul_ne_zero hfgn (mul_ne_zero hfd hgd)),
    rootMultiplicity_mul (by exact mul_ne_zero hfd hgd),
    rootMultiplicity_mul (by exact mul_ne_zero (mul_ne_zero hfn hgn) hfgd),
    rootMultiplicity_mul (by exact mul_ne_zero hfn hgn)] at hL
  rw [ratOrder, ratOrder, ratOrder]
  omega

@[simp]
theorem ratOrder_algebraMap (p : K[X]) (c : K) :
    ratOrder (algebraMap K[X] (RatFunc K) p) c = rootMultiplicity c p := by
  rw [ratOrder, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

@[simp]
theorem ratOrder_one (c : K) : ratOrder (1 : RatFunc K) c = 0 := by
  have h : (1 : RatFunc K) = algebraMap K[X] (RatFunc K) 1 := by rw [map_one]
  rw [h, ratOrder_algebraMap, rootMultiplicity_eq_zero (by simp : ¬ (1 : K[X]).IsRoot c)]
  norm_num

@[simp]
theorem ratOrder_C (a : K) (c : K) : ratOrder (RatFunc.C a : RatFunc K) c = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, ratOrder, RatFunc.num_zero, RatFunc.denom_zero]
    simp
  · have h : (RatFunc.C a : RatFunc K) = algebraMap K[X] (RatFunc K) (Polynomial.C a) :=
      (RatFunc.algebraMap_C a).symm
    rw [h, ratOrder_algebraMap, rootMultiplicity_eq_zero (by simpa using ha)]
    norm_num

theorem ratOrder_inv {f : RatFunc K} (hf : f ≠ 0) (c : K) :
    ratOrder f⁻¹ c = -ratOrder f c := by
  have hinv : f⁻¹ ≠ 0 := inv_ne_zero hf
  have h := ratOrder_mul hf hinv c
  rw [mul_inv_cancel₀ hf, ratOrder_one] at h
  omega

theorem ratOrder_pow {f : RatFunc K} (hf : f ≠ 0) (n : ℕ) (c : K) :
    ratOrder (f ^ n) c = n * ratOrder f c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ratOrder_mul (pow_ne_zero n hf) hf, ih]
      push_cast
      ring

theorem ratOrder_zpow {f : RatFunc K} (hf : f ≠ 0) (n : ℤ) (c : K) :
    ratOrder (f ^ n) c = n * ratOrder f c := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, ratOrder_pow hf]
  · rw [zpow_negSucc, ratOrder_inv (pow_ne_zero (n + 1) hf), ratOrder_pow hf, Int.negSucc_eq]
    push_cast
    ring

/-! ## Vanishing of the order -/

theorem ratOrder_eq_zero_iff {Q : RatFunc K} (hQ : Q ≠ 0) (c : K) :
    ratOrder Q c = 0 ↔ ¬ Q.num.IsRoot c ∧ ¬ Q.denom.IsRoot c := by
  have hcop : IsCoprime Q.num Q.denom := RatFunc.isCoprime_num_denom Q
  constructor
  · intro h
    have hnot : ¬ (Q.num.IsRoot c ∧ Q.denom.IsRoot c) := by
      rintro ⟨h1, h2⟩
      have hdvd1 : (Polynomial.X - Polynomial.C c) ∣ Q.num := dvd_iff_isRoot.mpr h1
      have hdvd2 : (Polynomial.X - Polynomial.C c) ∣ Q.denom := dvd_iff_isRoot.mpr h2
      exact Polynomial.not_isUnit_X_sub_C c (hcop.isUnit_of_dvd' hdvd1 hdvd2)
    rw [ratOrder, sub_eq_zero] at h
    have hnat : rootMultiplicity c Q.num = rootMultiplicity c Q.denom := by exact_mod_cast h
    by_cases h1 : Q.num.IsRoot c
    · exact absurd ⟨h1, (rootMultiplicity_pos (RatFunc.denom_ne_zero Q)).mp
        (by rw [← hnat]; exact (rootMultiplicity_pos (RatFunc.num_ne_zero hQ)).mpr h1)⟩ hnot
    · refine ⟨h1, ?_⟩
      intro h2
      have hm2 : 0 < rootMultiplicity c Q.denom :=
        (rootMultiplicity_pos (RatFunc.denom_ne_zero Q)).mpr h2
      have hm1 : 0 < rootMultiplicity c Q.num := by rw [hnat]; exact hm2
      exact h1 ((rootMultiplicity_pos (RatFunc.num_ne_zero hQ)).mp hm1)
  · rintro ⟨h1, h2⟩
    rw [ratOrder, rootMultiplicity_eq_zero h1, rootMultiplicity_eq_zero h2]
    simp

/-- **The order vanishes outside a finite set.** -/
theorem finite_support_ratOrder {Q : RatFunc K} (hQ : Q ≠ 0) :
    {c : K | ratOrder Q c ≠ 0}.Finite := by
  classical
  have hsub : {c : K | ratOrder Q c ≠ 0}
      ⊆ (Q.num.roots.toFinset : Set K) ∪ (Q.denom.roots.toFinset : Set K) := by
    intro c hc
    by_contra hcn
    rw [Set.mem_union] at hcn
    obtain ⟨h1, h2⟩ := not_or.mp hcn
    have hr1 : ¬ Q.num.IsRoot c := by
      intro h
      exact h1 (by
        simp only [Multiset.mem_toFinset, Finset.mem_coe]
        exact (mem_roots (RatFunc.num_ne_zero hQ)).mpr h)
    have hr2 : ¬ Q.denom.IsRoot c := by
      intro h
      exact h2 (by
        simp only [Multiset.mem_toFinset, Finset.mem_coe]
        exact (mem_roots (RatFunc.denom_ne_zero Q)).mpr h)
    exact hc ((ratOrder_eq_zero_iff hQ c).mpr ⟨hr1, hr2⟩)
  exact Set.Finite.subset ((Q.num.roots.toFinset.finite_toSet).union
    (Q.denom.roots.toFinset.finite_toSet)) hsub

end

end GaloisForLFunctions.HTGeometry
