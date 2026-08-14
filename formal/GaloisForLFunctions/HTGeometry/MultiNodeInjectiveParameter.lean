import GaloisForLFunctions.HTGeometry.MultiNodePolynomialSeparation

/-!
# Node separation from injective parameter tuples alone

An orbit argument produces its identities only at *square-free* keys: the parameters must be
pairwise distinct and above the jet order.  The multi-node separation theorem, by contrast, asks
for every positive tuple.  The gap is closed by the triangular substitution

```text
k_s = K₀ + 1 + ∑_{t ≥ s} m_t ,
```

which is strictly decreasing in `s` — hence injective — and above `K₀`, for every tuple `m` of
positive integers.  Under it the node tuple `Z` is replaced by the tuple of its initial products
`W_t = ∏_{s ≤ t} Z_s`, and that replacement is injective: the smallest index where two node tuples
differ is the smallest index where their initial products differ.  The polynomial coefficients are
composed with an invertible affine substitution, so their vanishing after substitution is their
vanishing.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {D : ℕ}

/-! ### The triangular substitution -/

/-- A strictly decreasing tuple above a floor, built from a positive tuple. -/
def triSubst (K₀ : ℕ) (m : Fin D → ℕ) (s : Fin D) : ℕ := K₀ + 1 + ∑ t ∈ Finset.Ici s, m t

theorem lt_triSubst (K₀ : ℕ) (m : Fin D → ℕ) (s : Fin D) : K₀ < triSubst K₀ m s := by
  rw [triSubst]
  omega

theorem triSubst_strictAnti {K₀ : ℕ} {m : Fin D → ℕ} (hm : ∀ t, 1 ≤ m t) {s s' : Fin D}
    (hss : s < s') : triSubst K₀ m s' < triSubst K₀ m s := by
  have hsub : Finset.Ici s' ⊆ Finset.Ici s := by
    intro u hu
    exact Finset.mem_Ici.mpr (le_trans (le_of_lt hss) (Finset.mem_Ici.mp hu))
  have hmem : s ∈ Finset.Ici s := Finset.mem_Ici.mpr le_rfl
  have hnot : s ∉ Finset.Ici s' := by
    intro hcon
    exact absurd (Finset.mem_Ici.mp hcon) (not_le.mpr hss)
  have hlt : ∑ t ∈ Finset.Ici s', m t < ∑ t ∈ Finset.Ici s, m t := by
    refine Finset.sum_lt_sum_of_subset hsub hmem hnot (hm s) ?_
    exact fun u _ _ => Nat.zero_le _
  rw [triSubst, triSubst]
  omega

theorem triSubst_injective {K₀ : ℕ} {m : Fin D → ℕ} (hm : ∀ t, 1 ≤ m t) :
    Function.Injective (triSubst K₀ m) := by
  intro s s' hss
  rcases lt_trichotomy s s' with h | h | h
  · exact absurd hss (ne_of_gt (triSubst_strictAnti hm h))
  · exact h
  · exact absurd hss.symm (ne_of_gt (triSubst_strictAnti hm h))

/-! ### The substituted node tuple -/

/-- The product of a node tuple over an initial segment. -/
def prodIic (Z : Fin D → ℂ) (t : Fin D) : ℂ := ∏ s ∈ Finset.Iic t, Z s

theorem prodIic_ne_zero {Z : Fin D → ℂ} (hZ : ∀ s, Z s ≠ 0) (t : Fin D) : prodIic Z t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun s _ => hZ s

/-- **Initial products determine a nonvanishing node tuple.** -/
theorem prodIic_injective {Z Z' : Fin D → ℂ} (hZ : ∀ s, Z s ≠ 0)
    (h : prodIic Z = prodIic Z') : Z = Z' := by
  classical
  by_contra hne
  obtain ⟨t₀, ht₀, hmin⟩ :
      ∃ t₀ ∈ (Finset.univ.filter (fun t => Z t ≠ Z' t)),
        ∀ t ∈ (Finset.univ.filter (fun t => Z t ≠ Z' t)), t₀ ≤ t := by
    refine Finset.exists_min_image _ id ?_
    by_contra hempty
    refine hne (funext fun t => ?_)
    by_contra hcon
    exact hempty ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, hcon⟩⟩
  have hbelow : ∀ s ∈ Finset.Iio t₀, Z s = Z' s := by
    intro s hs
    by_contra hcon
    have hmem : s ∈ Finset.univ.filter (fun t => Z t ≠ Z' t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s, hcon⟩
    exact absurd (hmin s hmem) (not_le.mpr (Finset.mem_Iio.mp hs))
  have hIic : Finset.Iic t₀ = insert t₀ (Finset.Iio t₀) := (Finset.Iio_insert t₀).symm
  have hnotmem : t₀ ∉ Finset.Iio t₀ := by simp
  have hsplit : prodIic Z t₀ = Z t₀ * ∏ s ∈ Finset.Iio t₀, Z s := by
    rw [prodIic, hIic, Finset.prod_insert hnotmem]
  have hsplit' : prodIic Z' t₀ = Z' t₀ * ∏ s ∈ Finset.Iio t₀, Z' s := by
    rw [prodIic, hIic, Finset.prod_insert hnotmem]
  have hprodeq : ∏ s ∈ Finset.Iio t₀, Z s = ∏ s ∈ Finset.Iio t₀, Z' s :=
    Finset.prod_congr rfl hbelow
  have hpne : ∏ s ∈ Finset.Iio t₀, Z s ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => hZ s
  have hval := congrFun h t₀
  rw [hsplit, hsplit', ← hprodeq] at hval
  have := mul_right_cancel₀ hpne hval
  exact absurd this ((Finset.mem_filter.mp ht₀).2)

/-- **The substitution rewrites the exponential factor in the initial products.** -/
theorem prod_pow_triSubst (Z : Fin D → ℂ) (K₀ : ℕ) (m : Fin D → ℕ) :
    ∏ s, (Z s) ^ (triSubst K₀ m s)
      = (∏ s, Z s) ^ (K₀ + 1) * ∏ t, (prodIic Z t) ^ (m t) := by
  classical
  have hterm : ∀ s : Fin D, (Z s) ^ (triSubst K₀ m s)
      = (Z s) ^ (K₀ + 1) * ∏ t ∈ Finset.Ici s, (Z s) ^ (m t) := by
    intro s
    rw [triSubst, pow_add, Finset.prod_pow_eq_pow_sum]
  have hcomm : (∏ s : Fin D, ∏ t ∈ Finset.Ici s, (Z s) ^ (m t))
      = ∏ t : Fin D, ∏ s ∈ Finset.Iic t, (Z s) ^ (m t) := by
    refine Finset.prod_comm' ?_
    intro s t
    constructor
    · rintro ⟨-, ht⟩
      exact ⟨Finset.mem_Iic.mpr (Finset.mem_Ici.mp ht), Finset.mem_univ t⟩
    · rintro ⟨hs, -⟩
      exact ⟨Finset.mem_univ s, Finset.mem_Ici.mpr (Finset.mem_Iic.mp hs)⟩
  rw [Finset.prod_congr rfl (fun s (_ : s ∈ Finset.univ) => hterm s), Finset.prod_mul_distrib,
    Finset.prod_pow, hcomm]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [prodIic, Finset.prod_pow]

/-! ### The substitution on polynomials -/

/-- Evaluation after a polynomial substitution is evaluation at the substituted point. -/
theorem eval_aeval_comp {σ : Type*} (f : σ → MvPolynomial (Fin D) ℂ) (g : Fin D → ℂ)
    (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval g (MvPolynomial.aeval f p)
      = MvPolynomial.eval (fun s => MvPolynomial.eval g (f s)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]


/-- The triangular substitution, as a tuple of polynomials. -/
noncomputable def triSubstPoly (K₀ : ℕ) (s : Fin D) : MvPolynomial (Fin D) ℂ :=
  MvPolynomial.C (((K₀ + 1 : ℕ) : ℂ)) + ∑ t ∈ Finset.Ici s, MvPolynomial.X t

theorem eval_triSubstPoly (K₀ : ℕ) (x : Fin D → ℂ) (s : Fin D) :
    MvPolynomial.eval x (triSubstPoly K₀ s) = ((K₀ + 1 : ℕ) : ℂ) + ∑ t ∈ Finset.Ici s, x t := by
  rw [triSubstPoly, map_add, MvPolynomial.eval_C, map_sum]
  simp

/-- The linear part of the triangular substitution. -/
noncomputable def triLinear : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ) where
  toFun x := fun s => ∑ t ∈ Finset.Ici s, x t
  map_add' x y := by
    funext s
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    funext s
    simp [Finset.mul_sum]

theorem triLinear_apply (x : Fin D → ℂ) (s : Fin D) :
    triLinear x s = ∑ t ∈ Finset.Ici s, x t := rfl

theorem triLinear_injective : Function.Injective (triLinear (D := D)) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  by_contra hne
  obtain ⟨s₀, hs₀, hmax⟩ :
      ∃ s₀ ∈ (Finset.univ.filter (fun s => x s ≠ 0)),
        ∀ s ∈ (Finset.univ.filter (fun s => x s ≠ 0)), s ≤ s₀ := by
    refine Finset.exists_max_image _ id ?_
    by_contra hempty
    refine hne (funext fun s => ?_)
    by_contra hcon
    exact hempty ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hcon⟩⟩
  have hval := congrFun hx s₀
  rw [triLinear_apply] at hval
  have hsingle : ∑ t ∈ Finset.Ici s₀, x t = x s₀ := by
    refine Finset.sum_eq_single_of_mem s₀ (Finset.mem_Ici.mpr le_rfl) ?_
    intro t ht htne
    by_contra hcon
    have hmem : t ∈ Finset.univ.filter (fun s => x s ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ t, hcon⟩
    exact absurd (hmax t hmem) (not_le.mpr (lt_of_le_of_ne (Finset.mem_Ici.mp ht)
      (Ne.symm htne)))
  rw [hsingle] at hval
  exact absurd hval ((Finset.mem_filter.mp hs₀).2)

theorem triLinear_surjective : Function.Surjective (triLinear (D := D)) :=
  (LinearMap.injective_iff_surjective (f := triLinear (D := D))).mp triLinear_injective

/-- **The substituted polynomial vanishes only if the polynomial does.** -/
theorem aeval_triSubstPoly_eq_zero (K₀ : ℕ) {p : MvPolynomial (Fin D) ℂ}
    (h : MvPolynomial.aeval (triSubstPoly K₀) p = 0) : p = 0 := by
  classical
  refine MvPolynomial.funext fun z => ?_
  obtain ⟨y, hy⟩ := triLinear_surjective (fun s => z s - ((K₀ + 1 : ℕ) : ℂ))
  have hz : ∀ s, ((K₀ + 1 : ℕ) : ℂ) + ∑ t ∈ Finset.Ici s, y t = z s := by
    intro s
    have := congrFun hy s
    rw [triLinear_apply] at this
    rw [this]
    ring
  have heval := congrArg (MvPolynomial.eval y) h
  rw [map_zero, eval_aeval_comp] at heval
  rw [MvPolynomial.eval_zero]
  rw [← heval]
  congr 1
  funext s
  rw [eval_triSubstPoly, hz s]

/-! ### The separation theorem -/

/-- **Injective-parameter node separation.**  Vanishing of the exponential sum at every injective
parameter tuple above a floor already forces every polynomial coefficient to vanish. -/
theorem mvPolynomial_nodeSeparation_injective {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (Z : ι → Fin D → ℂ) (hZ0 : ∀ i s, Z i s ≠ 0) (hZinj : Set.InjOn Z ↑S)
    (P : ι → MvPolynomial (Fin D) ℂ) (K₀ : ℕ)
    (h : ∀ k : Fin D → ℕ, (∀ s, K₀ < k s) → Function.Injective k →
      ∑ i ∈ S, (MvPolynomial.eval (fun s => ((k s : ℕ) : ℂ)) (P i)) * ∏ s, (Z i s) ^ (k s) = 0) :
    ∀ i ∈ S, P i = 0 := by
  classical
  set W : ι → Fin D → ℂ := fun i => prodIic (Z i) with hW
  set P' : ι → MvPolynomial (Fin D) ℂ := fun i =>
    MvPolynomial.C ((∏ s, Z i s) ^ (K₀ + 1)) * MvPolynomial.aeval (triSubstPoly K₀) (P i) with hP'
  have hW0 : ∀ i s, W i s ≠ 0 := fun i s => prodIic_ne_zero (fun u => hZ0 i u) s
  have hWinj : Set.InjOn W ↑S := by
    intro i hi j hj hij
    refine hZinj hi hj ?_
    exact prodIic_injective (fun s => hZ0 i s) hij
  have hstep : ∀ i ∈ S, P i = 0 := by
    have hzero : ∀ i ∈ S, P' i = 0 := by
      refine mvPolynomial_nodeSeparation S W hW0 hWinj P' ?_
      intro m hm
      have hinj : Function.Injective (triSubst K₀ m) := triSubst_injective hm
      have hgt : ∀ s, K₀ < triSubst K₀ m s := fun s => lt_triSubst K₀ m s
      have hbase := h (triSubst K₀ m) hgt hinj
      rw [← hbase]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hP', map_mul, MvPolynomial.eval_C, eval_aeval_comp, prod_pow_triSubst]
      have hpt : (fun s => MvPolynomial.eval (fun t => ((m t : ℕ) : ℂ)) (triSubstPoly K₀ s))
          = fun s => ((triSubst K₀ m s : ℕ) : ℂ) := by
        funext s
        rw [eval_triSubstPoly, triSubst]
        push_cast
        ring
      rw [hpt]
      ring
    intro i hi
    have h0 := hzero i hi
    rw [hP'] at h0
    have hC : ((∏ s, Z i s) ^ (K₀ + 1)) ≠ 0 :=
      pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun s _ => hZ0 i s)
    have hCne : (MvPolynomial.C ((∏ s, Z i s) ^ (K₀ + 1)) : MvPolynomial (Fin D) ℂ) ≠ 0 :=
      fun hcon => hC (MvPolynomial.C_eq_zero.mp hcon)
    have hzero' : MvPolynomial.aeval (triSubstPoly K₀) (P i) = 0 := by
      rcases mul_eq_zero.mp h0 with hc | hp
      · exact absurd hc hCne
      · exact hp
    exact aeval_triSubstPoly_eq_zero K₀ hzero'
  exact hstep

end

end GaloisForLFunctions.HTGeometry
