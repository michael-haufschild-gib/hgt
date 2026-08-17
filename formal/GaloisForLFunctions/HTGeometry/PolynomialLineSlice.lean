import GaloisForLFunctions.HTGeometry.PolynomialSublevelMeasure

/-!
# Sublevel sets of polynomials: the one-variable law and the line slices

A nonzero real polynomial of degree `d` factors over the complex numbers, so the set where it is
smaller than `ε` is covered by `d` intervals of half-length `(ε/|a|)^{1/d}` around the real parts of
its roots, where `a` is the leading coefficient: its measure is at most `2d(ε/|a|)^{1/d}`.

In several variables the restriction of a polynomial to a line is a one-variable polynomial whose
coefficient in the total degree is the value of the top homogeneous component at the direction of
the line -- independently of the base point.  Choosing a direction where the top form does not
vanish therefore produces a family of one-variable polynomials of constant degree and constant
leading coefficient, which is what a slicing estimate of a sublevel set consumes.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section


theorem eval_prod_list (t : ℂ) (M : List ℂ) :
    Polynomial.eval t (M.map fun a => Polynomial.X - Polynomial.C a).prod
      = (M.map fun a => t - a).prod := by
  induction M with
  | nil => simp
  | cons a M ih => simp [ih]

theorem norm_prod_list (M : List ℂ) : ‖M.prod‖ = (M.map (fun a => ‖a‖)).prod := by
  induction M with
  | nil => simp
  | cons a M ih => simp [ih]

theorem list_prod_eq_fin_prod (f : ℂ → ℝ) (M : List ℂ) :
    (M.map f).prod = ∏ i : Fin M.length, f (M.get i) := by
  have h1 : List.ofFn (fun i : Fin M.length => f (M.get i)) = M.map f := by
    rw [show (fun i : Fin M.length => f (M.get i)) = f ∘ M.get from rfl, ← List.map_ofFn,
      List.ofFn_get]
  rw [← h1, List.prod_ofFn]

/-- The complex roots of a nonzero real polynomial, indexed by a tuple of its degree. -/
theorem exists_roots_tuple (q : Polynomial ℝ) (hq : q ≠ 0) :
    ∃ z : Fin q.natDegree → ℂ, ∀ t : ℝ,
      |q.eval t| = |q.leadingCoeff| * ∏ i, ‖(t : ℂ) - z i‖ := by
  classical
  set qC : Polynomial ℂ := q.map (algebraMap ℝ ℂ) with hqC
  have hqC0 : qC ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hq
  have hdeg : qC.natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective q
  have hcard : Multiset.card qC.roots = q.natDegree := by
    rw [← hdeg]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits qC)
  set L : List ℂ := qC.roots.toList with hL
  have hlen : L.length = q.natDegree := by rw [hL, Multiset.length_toList, hcard]
  have hroots : qC.roots = (L : Multiset ℂ) := by rw [hL, Multiset.coe_toList]
  refine ⟨fun i => L.get (Fin.cast hlen.symm i), fun t => ?_⟩
  have hsplit := (IsAlgClosed.splits qC).eq_prod_roots
  have hevalC : qC.eval (t : ℂ) = ((q.eval t : ℝ) : ℂ) := by
    rw [hqC, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) t
  have hlead : ‖qC.leadingCoeff‖ = |q.leadingCoeff| := by
    rw [hqC]
    simp
  have key : |q.eval t| = |q.leadingCoeff| * (L.map fun a => ‖(t : ℂ) - a‖).prod := by
    have h1 : |q.eval t| = ‖qC.eval (t : ℂ)‖ := by
      rw [hevalC, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    conv_lhs => rw [hsplit]
    rw [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, hlead, hroots, Multiset.map_coe,
      Multiset.prod_coe, eval_prod_list, norm_prod_list, List.map_map]
    rfl
  rw [key, list_prod_eq_fin_prod]
  congr 1
  exact Fintype.prod_equiv (finCongr hlen) _ _ fun i => rfl

/-- **The one-variable sublevel bound.**  The set where a nonzero real polynomial of degree `d` is
smaller than `ε` has measure at most `2 d (ε/|a|)^{1/d}`, with `a` the leading coefficient. -/
theorem volume_polynomial_sublevel_le (q : Polynomial ℝ) (hq : q ≠ 0) (hdeg : 0 < q.natDegree)
    {ε : ℝ} (hε : 0 ≤ ε) :
    volume {t : ℝ | |q.eval t| ≤ ε}
      ≤ ENNReal.ofReal (2 * q.natDegree *
          (ε / |q.leadingCoeff|) ^ ((1 : ℝ) / q.natDegree)) := by
  obtain ⟨z, hz⟩ := exists_roots_tuple q hq
  have ha : 0 < |q.leadingCoeff| := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hquot : 0 ≤ ε / |q.leadingCoeff| := by positivity
  have hδ : 0 ≤ (ε / |q.leadingCoeff|) ^ ((1 : ℝ) / q.natDegree) := Real.rpow_nonneg hquot _
  have hd : (q.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdeg)
  have hεδ : ε / |q.leadingCoeff|
      ≤ ((ε / |q.leadingCoeff|) ^ ((1 : ℝ) / q.natDegree)) ^ q.natDegree := by
    rw [← Real.rpow_natCast ((ε / |q.leadingCoeff|) ^ ((1 : ℝ) / q.natDegree)) q.natDegree,
      ← Real.rpow_mul hquot, one_div, inv_mul_cancel₀ hd, Real.rpow_one]
  have hset : {t : ℝ | |q.eval t| ≤ ε}
      = {t : ℝ | |q.leadingCoeff| * ∏ i, ‖(t : ℂ) - z i‖ ≤ ε} := by
    ext t
    simp only [mem_setOf_eq, hz t]
  rw [hset]
  exact volume_sublevel_le ha hδ hdeg hεδ

section Slices


theorem coeff_prod_of_natDegree_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
      have hrest : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, n i :=
        le_trans (Polynomial.natDegree_prod_le _ _)
          (Finset.sum_le_sum fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hf a (Finset.mem_insert_self a s)) hrest,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem natDegree_linear_le (a b : ℝ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  simp [Polynomial.natDegree_C]
  exact le_trans (Polynomial.natDegree_mul_le) (by simp)

theorem coeff_linear_one (a b : ℝ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff 1 = b := by
  simp

theorem natDegree_linear_pow_le (a b : ℝ) (k : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k).natDegree ≤ k := by
  refine le_trans (Polynomial.natDegree_pow_le) ?_
  calc k * (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ k * 1 :=
        Nat.mul_le_mul_left k (natDegree_linear_le a b)
    _ = k := by ring

theorem coeff_linear_pow (a b : ℝ) (k : ℕ) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k).coeff k = b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Polynomial.coeff_mul_add_eq_of_natDegree_le (natDegree_linear_pow_le a b k)
        (natDegree_linear_le a b), ih, coeff_linear_one, pow_succ]

variable {m : ℕ}

/-- The one-variable restriction of a multivariate polynomial to a line. -/
def lineSlice (p : MvPolynomial (Fin m) ℝ) (v x : Fin m → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p

theorem lineSlice_eval (p : MvPolynomial (Fin m) ℝ) (v x : Fin m → ℝ) (t : ℝ) :
    (lineSlice p v x).eval t = MvPolynomial.eval (fun i => x i + t * v i) p := by
  rw [lineSlice]
  rw [show ((MvPolynomial.aeval fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p
        : Polynomial ℝ).eval t
      = Polynomial.aeval t ((MvPolynomial.aeval fun i =>
          Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) p) from rfl]
  rw [MvPolynomial.comp_aeval_apply]
  simp only [map_add, Polynomial.aeval_C, Polynomial.aeval_X, map_mul, MvPolynomial.aeval_eq_eval]
  congr 2
  funext i
  simp [mul_comm]

theorem lineSlice_monomial (u : Fin m →₀ ℕ) (c : ℝ) (v x : Fin m → ℝ) :
    lineSlice (MvPolynomial.monomial u c) v x
      = Polynomial.C c * ∏ i ∈ u.support, (Polynomial.C (x i) + Polynomial.C (v i) *
          Polynomial.X) ^ (u i) := by
  rw [lineSlice, MvPolynomial.aeval_monomial, Finsupp.prod]
  rfl

theorem degree_eq_sum (u : Fin m →₀ ℕ) : Finsupp.degree u = ∑ i ∈ u.support, u i := rfl

theorem natDegree_lineSlice_monomial_le (u : Fin m →₀ ℕ) (c : ℝ) (v x : Fin m → ℝ) :
    (lineSlice (MvPolynomial.monomial u c) v x).natDegree ≤ Finsupp.degree u := by
  rw [lineSlice_monomial]
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add, degree_eq_sum]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  exact Finset.sum_le_sum fun i _ => natDegree_linear_pow_le _ _ _

theorem coeff_lineSlice_monomial (u : Fin m →₀ ℕ) (c : ℝ) (v x : Fin m → ℝ) :
    (lineSlice (MvPolynomial.monomial u c) v x).coeff (Finsupp.degree u)
      = c * ∏ i ∈ u.support, v i ^ (u i) := by
  rw [lineSlice_monomial, Polynomial.coeff_C_mul, degree_eq_sum,
    coeff_prod_of_natDegree_le _ _ _ (fun i _ => natDegree_linear_pow_le _ _ _)]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => coeff_linear_pow _ _ _)

theorem homogeneousComponent_monomial_self (u : Fin m →₀ ℕ) (c : ℝ) :
    MvPolynomial.homogeneousComponent (Finsupp.degree u) (MvPolynomial.monomial u c)
      = MvPolynomial.monomial u c := by
  classical
  ext w
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases hw : w = u
  · subst hw
    rw [if_pos rfl]
  · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hw)]
    split <;> simp

theorem homogeneousComponent_monomial_of_lt {d : ℕ} (u : Fin m →₀ ℕ) (c : ℝ)
    (h : Finsupp.degree u < d) :
    MvPolynomial.homogeneousComponent d (MvPolynomial.monomial u c) = 0 := by
  classical
  ext w
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero]
  by_cases hw : w = u
  · subst hw
    rw [if_neg (by omega)]
  · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hw)]
    split <;> rfl

/-- **The top coefficient of a line slice.**  Above the total degree, the coefficient of the
restriction to a line is the value of the corresponding homogeneous component at the direction --
in particular it does not depend on the base point of the line. -/
theorem coeff_lineSlice {d : ℕ} (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ d)
    (v x : Fin m → ℝ) :
    (lineSlice p v x).coeff d = MvPolynomial.eval v (MvPolynomial.homogeneousComponent d p) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [lineSlice, map_sum, Polynomial.finsetSum_coeff, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg : Finsupp.degree u ≤ d := by
    have := MvPolynomial.le_totalDegree hu
    rw [degree_eq_sum]
    exact le_trans this hp
  have hslice : ((MvPolynomial.aeval fun i => Polynomial.C (x i) + Polynomial.C (v i) *
      Polynomial.X) (MvPolynomial.monomial u (MvPolynomial.coeff u p)) : Polynomial ℝ)
      = lineSlice (MvPolynomial.monomial u (MvPolynomial.coeff u p)) v x := rfl
  rw [hslice]
  rcases eq_or_lt_of_le hdeg with heq | hlt
  · rw [← heq, coeff_lineSlice_monomial, homogeneousComponent_monomial_self,
      MvPolynomial.eval_monomial, Finsupp.prod]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_lineSlice_monomial_le u _ v x) hlt),
      homogeneousComponent_monomial_of_lt u _ hlt, map_zero]

end Slices

end

end GaloisForLFunctions.HTGeometry
