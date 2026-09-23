import GaloisForLFunctions.HTGeometry.NodeWeightDecay
import GaloisForLFunctions.HTGeometry.MomentCharacterisation

/-!
# Nodes lie within the support

If a representing measure is carried below `M`, then every root of `Q_{n+1}` is at most `M`.  A root
`ξ > M` would make `Q_{n+1} = (X - ξ)G` pair with `G` as `∫ (x - ξ) G(x)² dμ`, an integral of a
nonpositive integrand; orthogonality forces it to vanish, hence `G = 0` almost everywhere, which is
impossible because a nonzero polynomial vanishes only on a finite set and the measure charges every
cofinite set.

Contrapositively, nodes escaping upward force the representing measures to have unbounded support.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Nodes do not exceed a bound on the support.** -/
theorem monicOrtho_root_le_of_ae_le (h : PositiveMomentForm s) {mu : Measure ℝ}
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    {M : ℝ} (hsupp : ∀ᵐ x ∂mu, x ≤ M) (n : ℕ) {xi : ℝ}
    (hxi : (monicOrtho s (n + 1)).eval xi = 0) : xi ≤ M := by
  classical
  by_contra hcon0
  have hcon : M < xi := not_le.mp hcon0
  obtain ⟨G, hG, _⟩ := exists_cofactor h n hxi
  have hGne : G ≠ 0 := cofactor_ne_zero s n hG
  -- degree of the cofactor is `n`
  have hdeg : G.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hsq : ((X - C xi) : Polynomial ℝ) ≠ 0 := X_sub_C_ne_zero xi
    have hnd : (monicOrtho s (n + 1)).natDegree = 1 + G.natDegree := by
      rw [hG, natDegree_mul hsq hGne, natDegree_X_sub_C]
    have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
      natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
    rw [degree_eq_natDegree hGne]
    exact_mod_cast (by omega : G.natDegree < n + 1)
  have hzero : momentInner s (monicOrtho s (n + 1)) G = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl G hdeg
  -- the pairing is an integral of a nonpositive integrand
  set F : Polynomial ℝ := (C xi - X) * G ^ (2 : ℕ) with hFdef
  have hFint : Integrable (fun x : ℝ => F.eval x) mu := integrable_eval hint F
  have hFval : ∫ x, F.eval x ∂mu = 0 := by
    have hpair : momentInner s (monicOrtho s (n + 1)) G
        = ∫ x, (monicOrtho s (n + 1)).eval x * G.eval x ∂mu := by
      rw [momentInner_def, momentFunctional_mul_eq_integral s hs hint]
    have hneg : ∫ x, F.eval x ∂mu
        = -∫ x, (monicOrtho s (n + 1)).eval x * G.eval x ∂mu := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [hFdef, hG]
      simp only [eval_mul, eval_sub, eval_C, eval_X, eval_pow]
      ring
    rw [hneg, ← hpair, hzero, neg_zero]
  have hFnn : 0 ≤ᵐ[mu] fun x : ℝ => F.eval x := by
    filter_upwards [hsupp] with x hx
    rw [hFdef]
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_pow]
    have : 0 ≤ xi - x := by linarith
    positivity
  have hFae : (fun x : ℝ => F.eval x) =ᵐ[mu] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hFnn hFint).mp hFval
  -- but `F` is a nonzero polynomial, so it vanishes only on a finite set
  have hFne : F ≠ 0 := by
    rw [hFdef]
    refine mul_ne_zero ?_ (pow_ne_zero 2 hGne)
    intro h0
    have := congrArg (Polynomial.eval (xi + 1)) h0
    simp at this
  have hcharge := measure_compl_finset_pos_of_positiveMomentForm h hs hint F.roots.toFinset
  rw [Filter.EventuallyEq, ae_iff] at hFae
  refine absurd hFae (ne_of_gt (lt_of_lt_of_le hcharge (measure_mono ?_)))
  intro x hx
  simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, mem_roots hFne, IsRoot.def] at hx ⊢
  exact fun hcontra => hx hcontra

/-- **Nodes do not fall below a bound on the support.**  The mirror of the previous theorem; the
integrand `(x - ξ)G(x)²` is now nonnegative rather than nonpositive, and nothing else changes. -/
theorem monicOrtho_root_ge_of_ae_ge (h : PositiveMomentForm s) {mu : Measure ℝ}
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    {m : ℝ} (hsupp : ∀ᵐ x ∂mu, m ≤ x) (n : ℕ) {xi : ℝ}
    (hxi : (monicOrtho s (n + 1)).eval xi = 0) : m ≤ xi := by
  classical
  by_contra hcon0
  have hcon : xi < m := not_le.mp hcon0
  obtain ⟨G, hG, _⟩ := exists_cofactor h n hxi
  have hGne : G ≠ 0 := cofactor_ne_zero s n hG
  have hdeg : G.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have hsq : ((X - C xi) : Polynomial ℝ) ≠ 0 := X_sub_C_ne_zero xi
    have hnd : (monicOrtho s (n + 1)).natDegree = 1 + G.natDegree := by
      rw [hG, natDegree_mul hsq hGne, natDegree_X_sub_C]
    have hQnd : (monicOrtho s (n + 1)).natDegree = n + 1 :=
      natDegree_eq_of_degree_eq_some (monicOrtho_degree s (n + 1))
    rw [degree_eq_natDegree hGne]
    exact_mod_cast (by omega : G.natDegree < n + 1)
  have hzero : momentInner s (monicOrtho s (n + 1)) G = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h (n + 1) (n + 1) le_rfl G hdeg
  set F : Polynomial ℝ := (X - C xi) * G ^ (2 : ℕ) with hFdef
  have hFint : Integrable (fun x : ℝ => F.eval x) mu := integrable_eval hint F
  have hFval : ∫ x, F.eval x ∂mu = 0 := by
    have hpair : momentInner s (monicOrtho s (n + 1)) G
        = ∫ x, (monicOrtho s (n + 1)).eval x * G.eval x ∂mu := by
      rw [momentInner_def, momentFunctional_mul_eq_integral s hs hint]
    have hsame : ∫ x, F.eval x ∂mu
        = ∫ x, (monicOrtho s (n + 1)).eval x * G.eval x ∂mu := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [hFdef, hG]
      simp only [eval_mul, eval_sub, eval_C, eval_X, eval_pow]
      ring
    rw [hsame, ← hpair, hzero]
  have hFnn : 0 ≤ᵐ[mu] fun x : ℝ => F.eval x := by
    filter_upwards [hsupp] with x hx
    rw [hFdef]
    simp only [eval_mul, eval_sub, eval_C, eval_X, eval_pow]
    have hxx : 0 ≤ x - xi := by linarith
    positivity
  have hFae : (fun x : ℝ => F.eval x) =ᵐ[mu] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hFnn hFint).mp hFval
  have hFne : F ≠ 0 := by
    rw [hFdef]
    refine mul_ne_zero ?_ (pow_ne_zero 2 hGne)
    intro h0
    have hbad := congrArg (Polynomial.eval (xi + 1)) h0
    simp at hbad
  have hcharge := measure_compl_finset_pos_of_positiveMomentForm h hs hint F.roots.toFinset
  rw [Filter.EventuallyEq, ae_iff] at hFae
  refine absurd hFae (ne_of_gt (lt_of_lt_of_le hcharge (measure_mono ?_)))
  intro x hx
  simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, mem_roots hFne, IsRoot.def] at hx ⊢
  exact fun hcontra => hx hcontra

/-- **Nodes lie in the convex hull of the support.** -/
theorem monicOrtho_root_mem_Icc (h : PositiveMomentForm s) {mu : Measure ℝ}
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    {m M : ℝ} (hlo : ∀ᵐ x ∂mu, m ≤ x) (hhi : ∀ᵐ x ∂mu, x ≤ M) (n : ℕ) {xi : ℝ}
    (hxi : (monicOrtho s (n + 1)).eval xi = 0) : xi ∈ Set.Icc m M :=
  ⟨monicOrtho_root_ge_of_ae_ge h hs hint hlo n hxi,
    monicOrtho_root_le_of_ae_le h hs hint hhi n hxi⟩

end HTGeometry
