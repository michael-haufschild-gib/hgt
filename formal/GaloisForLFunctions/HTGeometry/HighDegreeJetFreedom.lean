import Mathlib

/-!
# High-degree coefficients prescribe jets freely

A polynomial supported in degrees `N, …, N + Km - 1` is `X ^ N` times a polynomial of degree below
`Km`.  If its first `m` derivatives vanish at each of `K` distinct nonzero points, that cofactor has
`Km` roots counted with multiplicity while its degree is below `Km`, hence it vanishes.  So the jet
map of the degree window is injective, and by equality of dimensions it is onto: the jets of order
below `m` at `K` distinct nonzero nodes can be prescribed arbitrarily using only coefficients of
degree at least `N`, for every `N`.

Scaling the target scales the coefficients, so every prescribable jet vector is reachable with
coefficients of arbitrarily small size — which is what a genericity argument on a bounded coefficient
box needs.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A polynomial of degree below `K · m` vanishing to order `m` at `K` distinct points is
zero.** -/
theorem eq_zero_of_le_rootMultiplicity
    {s : Finset ℂ} {m : ℕ} {q : Polynomial ℂ}
    (hdeg : q.natDegree < s.card * m)
    (hmult : q ≠ 0 → ∀ x ∈ s, m ≤ q.rootMultiplicity x) :
    q = 0 := by
  classical
  by_contra hq
  have hmult' := hmult hq
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hdeg
    · exact hm
  have hsub : s ⊆ q.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    have hpos : 0 < q.rootMultiplicity x := lt_of_lt_of_le hm (hmult' x hx)
    exact (Polynomial.rootMultiplicity_pos hq).mp hpos
  have hcount : ∀ x ∈ s, m ≤ Multiset.count x q.roots := by
    intro x hx
    rw [Polynomial.count_roots]
    exact hmult' x hx
  have hle : s.card * m ≤ q.roots.card := by
    calc s.card * m = ∑ _x ∈ s, m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ s, Multiset.count x q.roots := Finset.sum_le_sum hcount
      _ ≤ ∑ x ∈ q.roots.toFinset, Multiset.count x q.roots :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = q.roots.card := Multiset.toFinset_sum_count_eq _
  have hroots : q.roots.card ≤ q.natDegree := Polynomial.card_roots' q
  omega

/-- **The shifted form.**  Multiplying by `X ^ N` does not change the multiplicity at a nonzero
point, so the same conclusion holds for the jets of `X ^ N · q`. -/
theorem eq_zero_of_shifted_iterate_derivative_eval_eq_zero
    {s : Finset ℂ} (hs : (0 : ℂ) ∉ s) {m N : ℕ} {q : Polynomial ℂ}
    (hdeg : q.natDegree < s.card * m)
    (hjet : ∀ x ∈ s, ∀ r < m, (Polynomial.derivative^[r] (X ^ N * q)).eval x = 0) :
    q = 0 := by
  classical
  refine eq_zero_of_le_rootMultiplicity hdeg fun hq x hx => ?_
  have hx0 : x ≠ 0 := fun h => hs (h ▸ hx)
  have hp : (X : Polynomial ℂ) ^ N * q ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hq
  have hlt : m - 1 < ((X : Polynomial ℂ) ^ N * q).rootMultiplicity x := by
    refine (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hp).mpr ?_
    intro r hr
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hdeg
    · exact hjet x hx r (by omega)
  have hzero : ((X : Polynomial ℂ) ^ N).rootMultiplicity x = 0 := by
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simp [Polynomial.IsRoot, hx0]
  rw [Polynomial.rootMultiplicity_mul hp, hzero, zero_add] at hlt
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  · omega

/-! ### The window jet map -/

/-- The polynomial with prescribed coefficients in the degree window `[N, N + n)`, as a linear map
of the coefficient vector. -/
def windowLin (N n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] Polynomial ℂ :=
  ∑ i : Fin n, (Polynomial.monomial (N + (i : ℕ))).comp (LinearMap.proj i)

theorem windowLin_apply (N n : ℕ) (c : Fin n → ℂ) :
    windowLin N n c = ∑ i : Fin n, Polynomial.monomial (N + (i : ℕ)) (c i) := by
  rw [windowLin, LinearMap.coe_sum, Finset.sum_apply]
  rfl

theorem windowLin_eq_mul (N n : ℕ) (c : Fin n → ℂ) :
    windowLin N n c = X ^ N * ∑ i : Fin n, Polynomial.monomial (i : ℕ) (c i) := by
  rw [windowLin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm N (i : ℕ)]
  exact (Polynomial.X_pow_mul_monomial N (i : ℕ) (c i)).symm

/-- The jet map of the degree window: the derivatives of order below `m` at the `K` nodes. -/
def windowJetMap {K : ℕ} (x : Fin K → ℂ) (m N n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  LinearMap.pi fun p =>
    (Polynomial.leval (x p.1)).comp
      ((Polynomial.derivative (R := ℂ) ^ ((p.2 : ℕ))).comp (windowLin N n))

theorem windowJetMap_apply {K : ℕ} (x : Fin K → ℂ) (m N n : ℕ) (c : Fin n → ℂ)
    (p : Fin K × Fin m) :
    windowJetMap x m N n c p =
      (Polynomial.derivative^[(p.2 : ℕ)] (windowLin N n c)).eval (x p.1) := by
  rw [windowJetMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Module.End.pow_apply]
  rfl

theorem natDegree_window_cofactor_lt (n : ℕ) (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ i : Fin n, Polynomial.monomial (i : ℕ) (c i)).natDegree < n := by
  classical
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le (n := n - 1) Finset.univ _ fun i _ => ?_)
    (Nat.sub_lt hn Nat.one_pos)
  exact le_trans (Polynomial.natDegree_monomial_le (c i)) (by omega)

/-- **The window jet map is injective.** -/
theorem windowJetMap_injective {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) :
    Function.Injective (windowJetMap x m N (K * m)) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  refine LinearMap.ker_eq_bot'.mpr fun c hc => ?_
  rcases Nat.eq_zero_or_pos (K * m) with hKm | hKm
  · funext i
    exact absurd i.2 (by omega)
  set s : Finset ℂ := Finset.image x Finset.univ with hs
  set q : Polynomial ℂ := ∑ i : Fin (K * m), Polynomial.monomial (i : ℕ) (c i) with hq
  have hcard : s.card = K := by
    rw [hs, Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_fin]
  have hdeg : q.natDegree < s.card * m := by
    rw [hcard]
    exact natDegree_window_cofactor_lt (K * m) hKm c
  have hs0 : (0 : ℂ) ∉ s := by
    rw [hs]
    intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    exact hx0 a ha
  have hjet : ∀ y ∈ s, ∀ r < m, (Polynomial.derivative^[r] (X ^ N * q)).eval y = 0 := by
    intro y hy r hr
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    have hval := congrFun hc (a, (⟨r, hr⟩ : Fin m))
    rw [windowJetMap_apply, windowLin_eq_mul, ← hq] at hval
    simpa using hval
  have hqzero := eq_zero_of_shifted_iterate_derivative_eval_eq_zero hs0 hdeg hjet
  funext i
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (i : ℕ)) hqzero
  simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i] at hcoeff
  · simpa using hcoeff
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext h))]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The window jet map is onto.**  A prescribed jet vector at `K` distinct nonzero nodes is
realized by coefficients supported in the window `[N, N + K·m)`, for every `N`. -/
theorem windowJetMap_surjective {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) :
    Function.Surjective (windowJetMap x m N (K * m)) := by
  have hdim : Module.finrank ℂ (Fin (K * m) → ℂ) = Module.finrank ℂ (Fin K × Fin m → ℂ) := by
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (windowJetMap_injective hxinj hx0 m N)

/-- **Free jets from a high-degree window.**  For every jet target at `K` distinct nonzero nodes and
every starting degree `N`, some coefficient vector supported in `[N, N + K·m)` realizes it. -/
theorem exists_windowLin_jets {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) (J : Fin K × Fin m → ℂ) :
    ∃ c : Fin (K * m) → ℂ, ∀ (a : Fin K) (r : Fin m),
      (Polynomial.derivative^[(r : ℕ)] (windowLin N (K * m) c)).eval (x a) = J (a, r) := by
  obtain ⟨c, hc⟩ := windowJetMap_surjective hxinj hx0 m N J
  refine ⟨c, fun a r => ?_⟩
  rw [← windowJetMap_apply x m N (K * m) c (a, r), hc]

end

end GaloisForLFunctions.HTGeometry
