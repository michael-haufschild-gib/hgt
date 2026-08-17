import Mathlib
import GaloisForLFunctions.HTGeometry.AlgebraicIndependenceFromDifferentials

/-!
# Bounded monomial secant rank detects every jet face

The order-`m` jet at the origin of `∑ i u i exp (s i x)` is `∑ i u i (1, s i, …, (s i)^m)`.  With
`k` terms this is a polynomial map `jetMap m k : ℂ^k × ℂ^k → ℂ^{m+1}`, and the question is how
many terms are needed before its image meets the complement of an arbitrary proper algebraic
subset.

At `k` distinct nodes the differential of `jetMap` is the truncated confluent Vandermonde matrix
whose columns are the jets and the jet derivatives at the nodes.  A functional annihilating all of
them is a polynomial of degree at most `m` with a double root at each node, hence zero once
`m + 1 ≤ 2k`; the differential is therefore surjective, `jetMap` is open at such a point, and a
polynomial vanishing on its whole image would vanish on an open subset of `ℂ^{m+1}`, so it is zero.
Consequently `⌈(m+1)/2⌉` terms suffice.

The bound is sharp in the strong sense: when `2k ≤ m` the `(k+1) × (k+1)` catalecticant
`det (y_{a+b})` is a nonzero polynomial that vanishes identically on the image of `jetMap m k`,
because the coefficient vector of `∏ i (X - s i)` lies in the kernel of that Hankel matrix.
-/

namespace GaloisForLFunctions.MonomialJetSecant

open Filter Polynomial Topology

/-- The order-`m` jet at the origin of the exponential `exp (s x)`, in monomial coordinates. -/
def jetVec (m : ℕ) (s : ℂ) : Fin (m + 1) → ℂ := fun j => s ^ (j : ℕ)

/-- The derivative in `s` of the order-`m` jet of `exp (s x)`. -/
def jetVecDeriv (m : ℕ) (s : ℂ) : Fin (m + 1) → ℂ := fun j => (j : ℕ) * s ^ ((j : ℕ) - 1)

/-- The polynomial whose coefficients are the values of a functional on the standard basis. -/
noncomputable def dualPoly (m : ℕ) (φ : Module.Dual ℂ (Fin (m + 1) → ℂ)) : Polynomial ℂ :=
  ∑ j : Fin (m + 1), Polynomial.C (φ (Pi.single j 1)) * Polynomial.X ^ (j : ℕ)

theorem natDegree_dualPoly_le (m : ℕ) (φ : Module.Dual ℂ (Fin (m + 1) → ℂ)) :
    (dualPoly m φ).natDegree ≤ m := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  simpa using Nat.lt_succ_iff.mp j.isLt

theorem coeff_dualPoly (m : ℕ) (φ : Module.Dual ℂ (Fin (m + 1) → ℂ)) (j : Fin (m + 1)) :
    (dualPoly m φ).coeff (j : ℕ) = φ (Pi.single j 1) := by
  classical
  rw [dualPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    exact fun h => hb (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem dualPoly_eq_zero_iff (m : ℕ) (φ : Module.Dual ℂ (Fin (m + 1) → ℂ)) :
    dualPoly m φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    refine LinearMap.ext fun x => ?_
    have hx : x = ∑ j : Fin (m + 1), x j • Pi.single j (1 : ℂ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [map_smul]
    have := coeff_dualPoly m φ j
    rw [h] at this
    simp at this
    simp [← this]
  · intro h
    simp [dualPoly, h]

theorem dual_apply_jetVec (m : ℕ) (φ : Module.Dual ℂ (Fin (m + 1) → ℂ)) (s : ℂ) :
    φ (jetVec m s) = (dualPoly m φ).eval s := by
  have hx : jetVec m s = ∑ j : Fin (m + 1), (s ^ (j : ℕ)) • Pi.single j (1 : ℂ) := by
    funext i
    simp [jetVec, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum, dualPoly]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem dual_apply_jetVecDeriv (m : ℕ) (φ : Module.Dual ℂ (Fin (m + 1) → ℂ)) (s : ℂ) :
    φ (jetVecDeriv m s) = (Polynomial.derivative (dualPoly m φ)).eval s := by
  have hx : jetVecDeriv m s
      = ∑ j : Fin (m + 1), (((j : ℕ) : ℂ) * s ^ ((j : ℕ) - 1)) • Pi.single j (1 : ℂ) := by
    funext i
    simp [jetVecDeriv, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum, dualPoly]
  simp only [map_sum, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
    Polynomial.derivative_X_pow, zero_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring


/-- **Confluent Vandermonde spanning.**  The jets and jet derivatives at `k` distinct nodes span
the whole order-`m` jet space as soon as `m + 1 ≤ 2k`. -/
theorem span_jet_eq_top (m k : ℕ) (hk : m + 1 ≤ 2 * k) (s : Fin k → ℂ)
    (hs : Function.Injective s) :
    Submodule.span ℂ
        (Set.range (fun i => jetVec m (s i)) ∪ Set.range (fun i => jetVecDeriv m (s i)))
      = (⊤ : Submodule ℂ (Fin (m + 1) → ℂ)) := by
  classical
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  have hvanish : ∀ x ∈ Submodule.span ℂ
      (Set.range (fun i => jetVec m (s i)) ∪ Set.range (fun i => jetVecDeriv m (s i))),
      φ x = 0 := by
    intro x hx
    have : φ x ∈ Submodule.map φ (Submodule.span ℂ
        (Set.range (fun i => jetVec m (s i)) ∪ Set.range (fun i => jetVecDeriv m (s i)))) :=
      ⟨x, hx, rfl⟩
    rw [hφ] at this
    simpa using this
  set p : Polynomial ℂ := dualPoly m φ with hp
  have hp0 : p ≠ 0 := fun h => hφ0 ((dualPoly_eq_zero_iff m φ).mp h)
  have hroot : ∀ i, p.IsRoot (s i) := by
    intro i
    have := hvanish (jetVec m (s i))
      (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
    rw [dual_apply_jetVec] at this
    exact this
  have hrootd : ∀ i, (Polynomial.derivative p).IsRoot (s i) := by
    intro i
    have := hvanish (jetVecDeriv m (s i))
      (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
    rw [dual_apply_jetVecDeriv] at this
    exact this
  have hk1 : 1 ≤ k := by omega
  have hd0 : Polynomial.derivative p ≠ 0 := by
    intro hd
    have hdeg : p.natDegree = 0 := Polynomial.derivative_eq_zero.mp hd
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    have h0 : c = 0 := by
      have := hroot ⟨0, by omega⟩
      rw [Polynomial.IsRoot, ← hc] at this
      simpa using this
    exact hp0 (by rw [← hc, h0, map_zero])
  have hmult : ∀ i, 2 ≤ p.rootMultiplicity (s i) := by
    intro i
    have h1 : 0 < (Polynomial.derivative p).rootMultiplicity (s i) :=
      (Polynomial.rootMultiplicity_pos hd0).mpr (hrootd i)
    have h2 : (Polynomial.derivative p).rootMultiplicity (s i)
        = p.rootMultiplicity (s i) - 1 :=
      Polynomial.derivative_rootMultiplicity_of_root (hroot i)
    omega
  have hcount : ∀ i, 2 ≤ p.roots.count (s i) := by
    intro i
    rw [Polynomial.count_roots]
    exact hmult i
  have hsub : (Finset.univ.image s) ⊆ p.roots.toFinset := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    exact lt_of_lt_of_le two_pos (hcount i)
  have hsum : 2 * k ≤ p.roots.card := by
    have h1 : ∑ a ∈ Finset.univ.image s, p.roots.count a ≤ p.roots.card := by
      rw [← Multiset.toFinset_sum_count_eq p.roots]
      exact Finset.sum_le_sum_of_subset hsub
    have h2 : ∑ a ∈ Finset.univ.image s, p.roots.count a
        = ∑ i : Fin k, p.roots.count (s i) :=
      Finset.sum_image (fun x _ y _ h => hs h)
    have h3 : 2 * k ≤ ∑ i : Fin k, p.roots.count (s i) := by
      calc 2 * k = ∑ _i : Fin k, 2 := by simp [Finset.sum_const, mul_comm]
        _ ≤ ∑ i : Fin k, p.roots.count (s i) :=
            Finset.sum_le_sum (fun i _ => hcount i)
    omega
  have hdeg : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  have hle : p.natDegree ≤ m := natDegree_dualPoly_le m φ
  omega


/-- The order-`m` jet at the origin of `∑ i, u i * exp (s i * x)`, in monomial coordinates. -/
def jetMap (m k : ℕ) (p : (Fin k → ℂ) × (Fin k → ℂ)) : Fin (m + 1) → ℂ :=
  fun j => ∑ i, p.1 i * (p.2 i) ^ (j : ℕ)

/-- One row of the confluent Vandermonde differential of `jetMap`. -/
noncomputable def jetRow (k : ℕ) (u s : Fin k → ℂ) (j : ℕ) :
    ((Fin k → ℂ) × (Fin k → ℂ)) →L[ℂ] ℂ :=
  ∑ i : Fin k,
    ((((s i) ^ j) • ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin k → ℂ) (Fin k → ℂ))))
      + ((u i * (j : ℂ) * (s i) ^ (j - 1)) • ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ)))))

theorem hasStrictFDerivAt_jetRow (k : ℕ) (u s : Fin k → ℂ) (j : ℕ) :
    HasStrictFDerivAt (fun p : (Fin k → ℂ) × (Fin k → ℂ) => ∑ i, p.1 i * (p.2 i) ^ j)
      (jetRow k u s j) (u, s) := by
  have key : ∀ i : Fin k,
      HasStrictFDerivAt (fun p : (Fin k → ℂ) × (Fin k → ℂ) => p.1 i * (p.2 i) ^ j)
        ((((s i) ^ j) • ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.fst ℂ (Fin k → ℂ) (Fin k → ℂ))))
          + ((u i * (j : ℂ) * (s i) ^ (j - 1)) • ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ))))) (u, s) := by
    intro i
    have h1 : HasStrictFDerivAt (fun p : (Fin k → ℂ) × (Fin k → ℂ) => p.1 i)
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.fst ℂ (Fin k → ℂ) (Fin k → ℂ))) (u, s) :=
      ContinuousLinearMap.hasStrictFDerivAt
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).comp
          (ContinuousLinearMap.fst ℂ (Fin k → ℂ) (Fin k → ℂ)))
    have h2 : HasStrictFDerivAt (fun p : (Fin k → ℂ) × (Fin k → ℂ) => p.2 i)
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ))) (u, s) :=
      ContinuousLinearMap.hasStrictFDerivAt
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).comp
          (ContinuousLinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ)))
    have h3 := h2.pow j
    have h4 := h1.mul h3
    refine h4.congr_fderiv ?_
    refine ContinuousLinearMap.ext (fun q => ?_)
    simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_eq_mul, nsmul_eq_mul]
    ring
  have hsum := HasStrictFDerivAt.sum (u := (Finset.univ : Finset (Fin k)))
    (A := fun i (p : (Fin k → ℂ) × (Fin k → ℂ)) => p.1 i * (p.2 i) ^ j)
    (A' := fun i => ((((s i) ^ j) • ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin k → ℂ) (Fin k → ℂ))))
      + ((u i * (j : ℂ) * (s i) ^ (j - 1)) • ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ)))))) (fun i _ => key i)
  refine hsum.congr_of_eventuallyEq ?_ |>.congr_fderiv rfl
  filter_upwards with q
  simp [Finset.sum_apply]


/-- The confluent Vandermonde differential of the `k`-term jet map. -/
noncomputable def jetMapDeriv (m k : ℕ) (u s : Fin k → ℂ) :
    ((Fin k → ℂ) × (Fin k → ℂ)) →L[ℂ] (Fin (m + 1) → ℂ) :=
  ContinuousLinearMap.pi (fun j : Fin (m + 1) => jetRow k u s (j : ℕ))

theorem hasStrictFDerivAt_jetMap (m k : ℕ) (u s : Fin k → ℂ) :
    HasStrictFDerivAt (jetMap m k) (jetMapDeriv m k u s) (u, s) :=
  hasStrictFDerivAt_pi'.mpr (fun j => hasStrictFDerivAt_jetRow k u s (j : ℕ))

theorem jetMapDeriv_apply (m k : ℕ) (u s : Fin k → ℂ)
    (p : (Fin k → ℂ) × (Fin k → ℂ)) (j : Fin (m + 1)) :
    jetMapDeriv m k u s p j
      = ∑ i : Fin k, ((s i) ^ (j : ℕ) * p.1 i
          + u i * ((j : ℕ) : ℂ) * (s i) ^ ((j : ℕ) - 1) * p.2 i) := by
  simp [jetMapDeriv, jetRow, ContinuousLinearMap.pi_apply]

theorem jetMapDeriv_single_fst (m k : ℕ) (u s : Fin k → ℂ) (i : Fin k) :
    jetMapDeriv m k u s (Pi.single i 1, 0) = jetVec m (s i) := by
  funext j
  rw [jetMapDeriv_apply]
  rw [Finset.sum_eq_single i]
  · simp [jetVec]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem jetMapDeriv_single_snd (m k : ℕ) (u s : Fin k → ℂ) (i : Fin k) :
    jetMapDeriv m k u s (0, Pi.single i 1) = u i • jetVecDeriv m (s i) := by
  funext j
  rw [jetMapDeriv_apply]
  rw [Finset.sum_eq_single i]
  · simp [jetVecDeriv, mul_assoc]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The confluent Vandermonde differential is surjective.** -/
theorem range_jetMapDeriv_eq_top (m k : ℕ) (hk : m + 1 ≤ 2 * k) (u s : Fin k → ℂ)
    (hs : Function.Injective s) (hu : ∀ i, u i ≠ 0) :
    LinearMap.range
        (jetMapDeriv m k u s : ((Fin k → ℂ) × (Fin k → ℂ)) →ₗ[ℂ] (Fin (m + 1) → ℂ)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← span_jet_eq_top m k hk s hs, Submodule.span_le]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨(Pi.single i 1, 0), jetMapDeriv_single_fst m k u s i⟩
  · refine ⟨(u i)⁻¹ • (0, Pi.single i 1), ?_⟩
    show (jetMapDeriv m k u s) ((u i)⁻¹ • (0, Pi.single i 1)) = jetVecDeriv m (s i)
    rw [map_smul, jetMapDeriv_single_snd, smul_smul, inv_mul_cancel₀ (hu i), one_smul]

/-- **A polynomial vanishing on the image of a submersion is zero.** -/
theorem mvPolynomial_eq_zero_of_hasStrictFDerivAt_surj {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {κ : Type*} [Fintype κ] {G : E → (κ → ℂ)} {z₀ : E}
    {L : E →L[ℂ] (κ → ℂ)} (hG : HasStrictFDerivAt G L z₀)
    (hsurj : LinearMap.range (L : E →ₗ[ℂ] (κ → ℂ)) = ⊤)
    {U : Set E} (hU : U ∈ 𝓝 z₀) {P : MvPolynomial κ ℂ}
    (h : ∀ z ∈ U, MvPolynomial.eval (G z) P = 0) : P = 0 := by
  have hmap : Filter.map G (𝓝 z₀) = 𝓝 (G z₀) := hG.map_nhds_eq_of_surj hsurj
  have himg : G '' U ∈ 𝓝 (G z₀) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.1 himg
  refine HTGeometry.mvPolynomial_eq_zero_of_eqOn_zero_isOpen hVopen hVmem (fun w hw => ?_)
  obtain ⟨z, hz, rfl⟩ := hVsub hw
  exact h z hz

/-- The secant detection rank `⌈(m+1)/2⌉`. -/
def secantRank (m : ℕ) : ℕ := (m + 2) / 2

theorem secantRank_spec (m : ℕ) : m + 1 ≤ 2 * secantRank m := by
  rw [secantRank]; omega

/-- **Bounded monomial secant rank detects every jet face.**  No nonzero polynomial on order-`m`
jet space vanishes on every sum of `⌈(m+1)/2⌉` monomial jets. -/
theorem mvPolynomial_eq_zero_of_eval_jetMap (m k : ℕ) (hk : m + 1 ≤ 2 * k)
    {P : MvPolynomial (Fin (m + 1)) ℂ}
    (h : ∀ p, MvPolynomial.eval (jetMap m k p) P = 0) : P = 0 := by
  have hk1 : 1 ≤ k := by omega
  refine mvPolynomial_eq_zero_of_hasStrictFDerivAt_surj
    (G := jetMap m k) (z₀ := ((fun _ => 1 : Fin k → ℂ), (fun i => ((i : ℕ) : ℂ))))
    (hasStrictFDerivAt_jetMap m k _ _) ?_ (U := Set.univ) Filter.univ_mem (fun z _ => h z)
  refine range_jetMapDeriv_eq_top m k hk _ _ ?_ (fun i => one_ne_zero)
  intro a b hab
  exact Fin.ext (Nat.cast_injective (R := ℂ) hab)

/-- The detection statement at the sharp rank. -/
theorem mvPolynomial_eq_zero_of_eval_jetMap_secantRank (m : ℕ)
    {P : MvPolynomial (Fin (m + 1)) ℂ}
    (h : ∀ p, MvPolynomial.eval (jetMap m (secantRank m) p) P = 0) : P = 0 :=
  mvPolynomial_eq_zero_of_eval_jetMap m (secantRank m) (secantRank_spec m) h

/-- **Secant detection rank.**  Every nonzero polynomial on order-`m` jet space is nonzero on
some sum of at most `⌈(m+1)/2⌉` monomial jets. -/
theorem exists_jetMap_eval_ne_zero (m : ℕ) {P : MvPolynomial (Fin (m + 1)) ℂ} (hP : P ≠ 0) :
    ∃ p, MvPolynomial.eval (jetMap m (secantRank m) p) P ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hP (mvPolynomial_eq_zero_of_eval_jetMap_secantRank m hcon)


/-- The catalecticant index: `a + b` read inside the jet coordinates. -/
def hankelIdx {m k : ℕ} (h : 2 * k ≤ m) (a b : Fin (k + 1)) : Fin (m + 1) :=
  ⟨(a : ℕ) + (b : ℕ), by have := a.isLt; have := b.isLt; omega⟩

/-- The `(k+1) × (k+1)` catalecticant of the order-`m` jet coordinates. -/
noncomputable def hankelPoly (m k : ℕ) (h : 2 * k ≤ m) : MvPolynomial (Fin (m + 1)) ℂ :=
  Matrix.det (Matrix.of fun a b : Fin (k + 1) => MvPolynomial.X (hankelIdx h a b))

theorem eval_hankelPoly (m k : ℕ) (h : 2 * k ≤ m) (y : Fin (m + 1) → ℂ) :
    MvPolynomial.eval y (hankelPoly m k h)
      = Matrix.det (Matrix.of fun a b : Fin (k + 1) => y (hankelIdx h a b)) := by
  rw [hankelPoly, RingHom.map_det]
  congr 1
  ext a b
  simp

/-- The catalecticant is a nonzero polynomial. -/
theorem hankelPoly_ne_zero (m k : ℕ) (h : 2 * k ≤ m) : hankelPoly m k h ≠ 0 := by
  classical
  intro hzero
  have hk : (k : ℕ) < m + 1 := by omega
  set y : Fin (m + 1) → ℂ := fun j => if (j : ℕ) = k then 1 else 0 with hy
  have hval := eval_hankelPoly m k h y
  rw [hzero] at hval
  simp only [map_zero] at hval
  have hmat : (Matrix.of fun a b : Fin (k + 1) => y (hankelIdx h a b))
      = Equiv.Perm.permMatrix ℂ (Fin.revPerm : Equiv.Perm (Fin (k + 1))) := by
    ext a b
    have ha : (a : ℕ) ≤ k := Nat.lt_succ_iff.mp a.isLt
    have hbk : (b : ℕ) ≤ k := Nat.lt_succ_iff.mp b.isLt
    have hv : ((((Fin.revPerm : Equiv.Perm (Fin (k + 1))) a) : Fin (k + 1)) : ℕ)
        = k - (a : ℕ) := by
      simp [Fin.val_rev]
    have hcond : ((Fin.revPerm : Equiv.Perm (Fin (k + 1))) a = b) ↔ (a : ℕ) + (b : ℕ) = k := by
      rw [Fin.ext_iff, hv]
      omega
    simp only [Matrix.of_apply, hy, hankelIdx, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    by_cases hc : (a : ℕ) + (b : ℕ) = k
    · rw [if_pos hc, if_pos (hcond.mpr hc)]
    · rw [if_neg hc, if_neg (fun hh => hc (hcond.mp hh))]
  rw [hmat, Matrix.det_permutation] at hval
  have : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (k + 1))) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (k + 1)))) with h1 | h1
      <;> rw [h1] <;> norm_num
  exact this hval.symm

/-- **Fewer than `⌈(m+1)/2⌉` monomial jets cannot fill jet space.**  If `2k ≤ m` then the
catalecticant is a nonzero polynomial vanishing on every `k`-term monomial jet. -/
theorem eval_hankelPoly_jetMap (m k : ℕ) (h : 2 * k ≤ m)
    (p : (Fin k → ℂ) × (Fin k → ℂ)) :
    MvPolynomial.eval (jetMap m k p) (hankelPoly m k h) = 0 := by
  classical
  rw [eval_hankelPoly]
  set q : Polynomial ℂ := ∏ i : Fin k, (Polynomial.X - Polynomial.C (p.2 i)) with hq
  have hqmonic : q.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have hqdeg : q.natDegree = k := by
    rw [hq, Polynomial.natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero _)]
    simp
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of fun a b : Fin (k + 1) =>
    jetMap m k p (hankelIdx h a b))).mp ?_
  refine ⟨fun b : Fin (k + 1) => q.coeff (b : ℕ), ?_, ?_⟩
  · intro hcon
    have hk : q.coeff k = 1 := by
      have := hqmonic.leadingCoeff
      rwa [Polynomial.leadingCoeff, hqdeg] at this
    have := congrFun hcon (⟨k, by omega⟩ : Fin (k + 1))
    simp only [Pi.zero_apply] at this
    rw [hk] at this
    exact one_ne_zero this
  · funext a
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.zero_apply]
    have hstep : ∀ b : Fin (k + 1), jetMap m k p (hankelIdx h a b) * q.coeff (b : ℕ)
        = ∑ i : Fin k, p.1 i * (p.2 i) ^ (a : ℕ) * (q.coeff (b : ℕ) * (p.2 i) ^ (b : ℕ)) := by
      intro b
      rw [jetMap, hankelIdx, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only []
      rw [pow_add]
      ring
    rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.mul_sum]
    have hev : ∑ b : Fin (k + 1), q.coeff (b : ℕ) * (p.2 i) ^ (b : ℕ) = q.eval (p.2 i) := by
      rw [Polynomial.eval_eq_sum_range, hqdeg]
      exact Fin.sum_univ_eq_sum_range (fun b => q.coeff b * (p.2 i) ^ b) (k + 1)
    rw [hev]
    have : q.eval (p.2 i) = 0 := by
      rw [hq, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp
    rw [this, mul_zero]

/-- **Sharpness.**  With `2k ≤ m` terms the image of the monomial jet map is contained in the
zero set of a nonzero polynomial, so it cannot detect every jet face. -/
theorem exists_ne_zero_vanishing_on_jetMap (m k : ℕ) (h : 2 * k ≤ m) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ, P ≠ 0 ∧
      ∀ p, MvPolynomial.eval (jetMap m k p) P = 0 :=
  ⟨hankelPoly m k h, hankelPoly_ne_zero m k h, eval_hankelPoly_jetMap m k h⟩

end GaloisForLFunctions.MonomialJetSecant
