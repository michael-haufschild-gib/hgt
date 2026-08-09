import Mathlib.RingTheory.Polynomial.Vieta
import GaloisForLFunctions.HTGeometry.DiscZeroFactorization

/-!
# The root multiset of a holomorphic function on a disc

Repackaging the weighted argument principle: the zeros inside a circle, counted with multiplicity,
form a multiset whose power sums are the weighted logarithmic-derivative integrals.  The multiset
form is what the symmetric-function machinery consumes, since Newton's identities relate power sums
to elementary symmetric functions of a multiset.

* `HTGeometry.multisetOfFinsetMultiplicities` and its power sums;
* `HTGeometry.multisetLinearProd` and its expansion in the elementary symmetric functions;
* `HTGeometry.exists_rootMultiset`, `HTGeometry.exists_rootMultiset_factorization`;
* `HTGeometry.multisetLinearProd_eq_monic`, `HTGeometry.multisetLinearProd_eq_zero_iff`.
-/

open Complex Metric Polynomial
open scoped Real

namespace HTGeometry

/-- The multiset assembled from a finite support and multiplicities. -/
def multisetOfFinsetMultiplicities (s : Finset ℂ) (m : ℂ → ℕ) : Multiset ℂ :=
  ∑ u ∈ s, Multiset.replicate (m u) u

/-- The power sums of an assembled multiset are the weighted sums of the base points. -/
theorem sum_map_pow_multisetOfFinsetMultiplicities (s : Finset ℂ) (m : ℂ → ℕ) (p : ℕ) :
    ((multisetOfFinsetMultiplicities s m).map (fun x => x ^ p)).sum
      = ∑ u ∈ s, (m u : ℂ) * u ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multisetOfFinsetMultiplicities]
  | insert a w ha ih =>
      rw [multisetOfFinsetMultiplicities, Finset.sum_insert ha, Multiset.map_add,
        Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate,
        Finset.sum_insert ha, ← multisetOfFinsetMultiplicities, ih, nsmul_eq_mul]

/-- Every element of an assembled multiset is one of the base points. -/
theorem mem_multisetOfFinsetMultiplicities {s : Finset ℂ} {m : ℂ → ℕ} {x : ℂ}
    (hx : x ∈ multisetOfFinsetMultiplicities s m) : x ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multisetOfFinsetMultiplicities] at hx
  | insert a w ha ih =>
      rw [multisetOfFinsetMultiplicities, Finset.sum_insert ha] at hx
      rcases Multiset.mem_add.1 hx with h | h
      · rw [Multiset.eq_of_mem_replicate h]
        exact Finset.mem_insert_self a w
      · exact Finset.mem_insert_of_mem (ih h)

/-- The product of the linear factors at the elements of a multiset. -/
noncomputable def multisetLinearProd (M : Multiset ℂ) (z : ℂ) : ℂ :=
  (M.map (fun r => z - r)).prod

/-- **The product of linear factors expanded in the elementary symmetric functions.** -/
theorem multisetLinearProd_eq_sum (M : Multiset ℂ) (z : ℂ) :
    multisetLinearProd M z
      = ∑ j ∈ Finset.range (Multiset.card M + 1),
          (-1) ^ (Multiset.card M - j) * M.esymm (Multiset.card M - j) * z ^ j := by
  classical
  set P : Polynomial ℂ := (M.map (fun r => Polynomial.X - Polynomial.C r)).prod with hP
  have hdeg : P.natDegree = Multiset.card M := by
    rw [hP]
    exact natDegree_multiset_prod_X_sub_C_eq_card M
  have heval : P.eval z = multisetLinearProd M z := by
    rw [hP, multisetLinearProd, eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun r _ => ?_)
    simp
  have hsum : P.eval z = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * z ^ j :=
    eval_eq_sum_range (p := P) z
  rw [← heval, hsum, hdeg]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ Multiset.card M := by
    have := Finset.mem_range.1 hj
    omega
  rw [hP, Multiset.prod_X_sub_C_coeff M hjle]

/-- **The product of linear factors is monic of degree the cardinality.**  Splitting off the top
term of the expansion leaves `z^k` with coefficient one, since the zeroth elementary symmetric
function is `1`. -/
theorem multisetLinearProd_eq_monic (M : Multiset ℂ) (z : ℂ) :
    multisetLinearProd M z
      = z ^ Multiset.card M
        + ∑ j ∈ Finset.range (Multiset.card M),
            (-1) ^ (Multiset.card M - j) * M.esymm (Multiset.card M - j) * z ^ j := by
  rw [multisetLinearProd_eq_sum, Finset.sum_range_succ]
  have htop : (-1 : ℂ) ^ (Multiset.card M - Multiset.card M)
      * M.esymm (Multiset.card M - Multiset.card M) * z ^ Multiset.card M
      = z ^ Multiset.card M := by
    simp [Multiset.esymm]
  rw [htop]
  ring

/-- The linear product of an assembled multiset is the product of the powers. -/
theorem multisetLinearProd_multisetOfFinsetMultiplicities (s : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    multisetLinearProd (multisetOfFinsetMultiplicities s m) z = ∏ u ∈ s, (z - u) ^ m u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multisetLinearProd, multisetOfFinsetMultiplicities]
  | insert a w ha ih =>
      rw [multisetOfFinsetMultiplicities, Finset.sum_insert ha, multisetLinearProd,
        Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate,
        Finset.prod_insert ha, ← multisetLinearProd, ← multisetOfFinsetMultiplicities, ih]

/-- The product of linear factors is continuous, being a polynomial. -/
theorem continuous_multisetLinearProd (M : Multiset ℂ) : Continuous (multisetLinearProd M) := by
  have heq : multisetLinearProd M = fun z => ∑ j ∈ Finset.range (Multiset.card M + 1),
      (-1) ^ (Multiset.card M - j) * M.esymm (Multiset.card M - j) * z ^ j := by
    funext z
    exact multisetLinearProd_eq_sum M z
  rw [heq]
  exact continuous_finsetSum _ fun j _ => by fun_prop

/-- **The product of linear factors vanishes exactly on the multiset.** -/
theorem multisetLinearProd_eq_zero_iff (M : Multiset ℂ) (z : ℂ) :
    multisetLinearProd M z = 0 ↔ z ∈ M := by
  rw [multisetLinearProd, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨r, hr, hzr⟩
    have hz : z = r := by
      have h0 : z - r = 0 := hzr
      linear_combination h0
    rw [hz]
    exact hr
  · intro hz
    exact ⟨z, hz, sub_self z⟩

/-- A product of linear factors does not vanish outside the base points. -/
theorem multisetLinearProd_ne_zero {M : Multiset ℂ} {t : ℝ} (hM : ∀ u ∈ M, ‖u‖ < t)
    {ζ : ℂ} (hζ : ‖ζ‖ = t) : multisetLinearProd M ζ ≠ 0 := by
  rw [multisetLinearProd]
  refine Multiset.prod_ne_zero ?_
  intro hmem
  obtain ⟨r, hr, hzero⟩ := Multiset.mem_map.1 hmem
  have hre : r = ζ := by
    have hz : ζ - r = 0 := hzero
    linear_combination -hz
  have hlt := hM r hr
  rw [hre, hζ] at hlt
  exact lt_irrefl t hlt

/-- **The root multiset of a holomorphic function on a disc.**  Its power sums are exactly the
weighted logarithmic-derivative integrals over the bounding circle. -/
theorem exists_rootMultiset
    {t : ℝ} (ht : 0 < t) {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall (0 : ℂ) t ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere (0 : ℂ) t, f ζ ≠ 0) :
    ∃ M : Multiset ℂ, (∀ u ∈ M, ‖u‖ < t) ∧
      ∀ p : ℕ, (∮ ζ in C(0, t), ζ ^ p * logDeriv f ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((M.map (fun x => x ^ p)).sum) := by
  obtain ⟨s, m, hs, hint⟩ := circleIntegral_weighted_logDeriv_eq_powerSum ht hU hsub hf hne
  refine ⟨multisetOfFinsetMultiplicities s m, ?_, ?_⟩
  · intro u hu
    have := hs u (mem_multisetOfFinsetMultiplicities hu)
    simpa using mem_ball_zero_iff.1 this
  · intro p
    rw [hint p, sum_map_pow_multisetOfFinsetMultiplicities]

/-- **The root multiset together with the factorization it comes from.**  On a slightly larger disc
the function is the monic product of the linear factors at its roots times a nowhere vanishing
holomorphic factor. -/
theorem exists_rootMultiset_factorization
    {t : ℝ} (ht : 0 < t) {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall (0 : ℂ) t ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : ∀ ζ ∈ sphere (0 : ℂ) t, f ζ ≠ 0) :
    ∃ (M : Multiset ℂ) (t₁ : ℝ) (g : ℂ → ℂ),
      (∀ u ∈ M, ‖u‖ < t) ∧ t < t₁ ∧ ball (0 : ℂ) t₁ ⊆ U ∧
      DifferentiableOn ℂ g (ball (0 : ℂ) t₁) ∧ (∀ z ∈ ball (0 : ℂ) t₁, g z ≠ 0) ∧
      Set.EqOn f (fun z => multisetLinearProd M z * g z) (ball (0 : ℂ) t₁) ∧
      ∀ p : ℕ, (∮ ζ in C(0, t), ζ ^ p * logDeriv f ζ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((M.map (fun x => x ^ p)).sum) := by
  obtain ⟨t₁, s, m, g, ht₁, hballU, hs, hgd, hgne, heq⟩ :=
    exists_factorization_of_analytic_disc ht hU hsub hf hne
  refine ⟨multisetOfFinsetMultiplicities s m, t₁, g, ?_, ht₁, hballU, hgd, hgne, ?_, ?_⟩
  · intro u hu
    have := hs u (mem_multisetOfFinsetMultiplicities hu)
    simpa using mem_ball_zero_iff.1 this
  · intro z hz
    show f z = multisetLinearProd (multisetOfFinsetMultiplicities s m) z * g z
    rw [multisetLinearProd_multisetOfFinsetMultiplicities]
    exact heq hz
  · intro p
    have hcircle : ∀ ζ ∈ sphere (0 : ℂ) t,
        ζ ^ p * logDeriv f ζ
          = ζ ^ p * logDeriv (fun z => (∏ u ∈ s, (z - u) ^ m u) * g z) ζ := by
      intro ζ hζ
      have hζt : ‖ζ‖ = t := by simpa using mem_sphere_iff_norm.1 hζ
      have hζball : ζ ∈ ball (0 : ℂ) t₁ := by
        rw [mem_ball_zero_iff, hζt]
        exact ht₁
      have hev : f =ᶠ[nhds ζ] fun z => (∏ u ∈ s, (z - u) ^ m u) * g z :=
        Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hζball) heq
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [circleIntegral.integral_congr ht.le hcircle,
      circleIntegral_weighted_logDeriv_prod ht isOpen_ball (closedBall_subset_ball ht₁) s m hs
        hgd hgne p, sum_map_pow_multisetOfFinsetMultiplicities]

end HTGeometry
