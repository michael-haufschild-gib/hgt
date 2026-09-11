import GaloisForLFunctions.HTGeometry.WeightedMinimax.Alternation
import GaloisForLFunctions.HTGeometry.WeightedMinimax.PolyRoots

/-!
# Coefficient duality and uniqueness for the weighted minimax problem

For a weight whose positivity set lies in the open positive half-line, the monic minimizer `T` of
degree `n` has `n` distinct positive roots and is their product of linear factors; hence every
coefficient of `T` up to index `n` is nonzero. The de la Vallée Poussin comparison at the `n+1`
alternating extreme nodes then gives the sharp coefficient bound

  `|coeff j R| * wsup T ≤ |coeff j T| * wsup R`   for every `R` of degree at most `n`,

with equality exactly on the nonzero real multiples of `T`. Consequently the minimizer subject to
`coeff j = 1` is unique and equals `T / coeff j T`, its value is `wsup T / |coeff j T|`, and at
`j = n-1` that value is `wsup T` divided by the sum of the roots of `T`.
-/

namespace GaloisForLFunctions.HTGeometry.WeightedMinimax

noncomputable section
open Set Polynomial

variable {v : ℝ → ℝ} {a b : ℝ}

theorem ne_zero_of_mem_coeffSet {n j : ℕ} {T : Polynomial ℝ} (hT : T ∈ coeffSet n j) : T ≠ 0 := by
  intro h
  have h2 := hT.2
  rw [h] at h2
  simp at h2

theorem monic_of_mem_monicDeg {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n) :
    T.Monic ∧ T.natDegree = n := by
  have h1 : T.coeff n = 1 := hT.2
  have h3 : n ≤ T.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [h1]; exact one_ne_zero)
  have hdeg : T.natDegree = n := le_antisymm hT.1 h3
  refine ⟨?_, hdeg⟩
  show T.leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hdeg, h1]

/-- With a weight vanishing at the left endpoint, every extreme point is strictly positive. -/
theorem pos_of_extremeSet (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x) {R : Polynomial ℝ} (hR : R ≠ 0)
    {x : ℝ} (hx : x ∈ extremeSet v a b R) : 0 < x := by
  obtain ⟨hv, _⟩ := pos_of_mem_extremeSet hw hR hx
  exact hpos x hx.1 (ne_of_gt hv)

/-! ### Roots of the monic minimizer -/

/-- The monic minimizer of degree `n` has `n` distinct positive roots, and is their product. -/
theorem monicDeg_minimizer_roots (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) :
    ∃ s : Finset ℝ, s.card = n ∧ (∀ r ∈ s, 0 < r) ∧ (∀ r ∈ s, T.eval r = 0) ∧
      T = ∏ r ∈ s, (Polynomial.X - Polynomial.C r) ∧ (∀ r ∈ s, r < b) := by
  obtain ⟨z, hz, hzE, halt⟩ := exists_alternating_extreme_chain hw hT hmin
  have hTne : T ≠ 0 := ne_zero_of_mem_coeffSet hT
  have hz0 : 0 < z 0 := pos_of_extremeSet hw hpos hTne (hzE 0 (Nat.zero_le _))
  obtain ⟨s, hcard, hspos, hroots, hub⟩ := roots_finset_of_alternating hz hz0 halt
  obtain ⟨hmonic, hdeg⟩ := monic_of_mem_monicDeg hT
  refine ⟨s, hcard, hspos, hroots, eq_prod_X_sub_C_of_monic hmonic hdeg hcard hroots, ?_⟩
  intro r hr
  exact lt_of_lt_of_le (hub r hr) (extremeSet_subset T (hzE n le_rfl)).2

/-- Every coefficient of the monic minimizer up to index `n` is nonzero. -/
theorem coeff_monicDeg_minimizer_ne_zero (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) :
    ∀ j ≤ n, T.coeff j ≠ 0 := by
  obtain ⟨s, hcard, hspos, hroots, _, _⟩ := monicDeg_minimizer_roots hw hpos hT hmin
  exact coeff_ne_zero_of_positive_roots (ne_zero_of_mem_coeffSet hT) hT.1 hcard hspos hroots

/-! ### The sharp coefficient bound -/

/-- **Coefficient duality.** The monic minimizer dominates the coefficient-to-norm ratio of every
polynomial of degree at most `n`. -/
theorem coeff_mul_wsup_le (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p)
    {j : ℕ} (hj : j ≤ n) {R : Polynomial ℝ} (hR : R.natDegree ≤ n) :
    |R.coeff j| * wsup v a b T ≤ |T.coeff j| * wsup v a b R := by
  have hTne : T ≠ 0 := ne_zero_of_mem_coeffSet hT
  have ht : 0 < wsup v a b T := wsup_pos hw hTne
  by_cases hRj : R.coeff j = 0
  · rw [hRj]
    simpa using mul_nonneg (abs_nonneg (T.coeff j)) (wsup_nonneg hw R)
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz, hzE, halt⟩ := exists_alternating_extreme_chain hw hT hmin
  have hz0 : 0 < z 0 := pos_of_extremeSet hw hpos hTne (hzE 0 (Nat.zero_le _))
  set d := Polynomial.C (R.coeff j) * T - Polynomial.C (T.coeff j) * R with hd
  have hdj : d.coeff j = 0 := by
    rw [hd, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    ring
  have hddeg : d.natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hT.1
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hR
  have hdeval : ∀ x : ℝ, d.eval x = R.coeff j * T.eval x - T.coeff j * R.eval x := by
    intro x
    rw [hd]
    simp
  have habs : ∀ p ≤ n, |T.coeff j * R.eval (z p)| < |R.coeff j * T.eval (z p)| := by
    intro p hp
    have hzp := hzE p hp
    obtain ⟨hv, _⟩ := pos_of_mem_extremeSet hw hTne hzp
    have hTv : v (z p) * |T.eval (z p)| = wsup v a b T := hzp.2
    have hRv : v (z p) * |R.eval (z p)| ≤ wsup v a b R :=
      le_wsup hw R (extremeSet_subset T hzp)
    have h1 : |T.coeff j| * (v (z p) * |R.eval (z p)|)
        < |R.coeff j| * (v (z p) * |T.eval (z p)|) := by
      rw [hTv]
      nlinarith [mul_le_mul_of_nonneg_left hRv (abs_nonneg (T.coeff j))]
    rw [abs_mul, abs_mul]
    nlinarith
  have hstrict : ∀ i < n, d.eval (z i) * d.eval (z (i + 1)) < 0 := by
    intro i hi
    rw [hdeval, hdeval]
    refine sub_mul_sub_neg ?_ (habs i (by omega)) (habs (i + 1) (by omega))
    have hRj2 : 0 < (R.coeff j) ^ 2 := by positivity
    have h2 := halt i hi
    nlinarith [mul_pos hRj2 (neg_pos.mpr h2)]
  obtain ⟨s, hcard, hspos, hroots, _⟩ := roots_finset_of_alternating hz hz0 hstrict
  have hd0 : d = 0 := by
    by_contra hdne
    exact absurd hdj (coeff_ne_zero_of_positive_roots hdne hddeg hcard hspos hroots j hj)
  have heq : Polynomial.C (R.coeff j) * T = Polynomial.C (T.coeff j) * R := by
    rw [hd] at hd0
    exact sub_eq_zero.mp hd0
  have hw2 := congrArg (wsup v a b) heq
  rw [wsup_const_mul hw, wsup_const_mul hw] at hw2
  exact absurd hw2 (ne_of_gt hcon)

/-! ### Minimizers with a prescribed coefficient -/

/-- Every minimizer with a prescribed coefficient has at least `n` extreme points. -/
theorem exists_extremeSet_card (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n j : ℕ} {S : Polynomial ℝ} (hS : S ∈ coeffSet n j)
    (hmin : ∀ p ∈ coeffSet n j, wsup v a b S ≤ wsup v a b p) :
    ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s, x ∈ extremeSet v a b S := by
  classical
  have hSne : S ≠ 0 := ne_zero_of_mem_coeffSet hS
  by_contra hcon
  have hno : ∀ t : Finset ℝ, (∀ x ∈ t, x ∈ extremeSet v a b S) → t.card ≠ n := by
    intro t ht hc
    exact hcon ⟨t, hc, ht⟩
  have hfin : (extremeSet v a b S).Finite := by
    rw [← Set.not_infinite]
    intro hinf
    obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq n
    exact hno t (fun x hx => hts hx) htc
  have hFsub : ∀ x ∈ hfin.toFinset, x ∈ extremeSet v a b S := by
    intro x hx
    rwa [Set.Finite.mem_toFinset] at hx
  have hFcard : hfin.toFinset.card < n := by
    by_contra hc
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (not_lt.mp hc)
    exact hno t (fun x hx => hFsub x (hts hx)) htc
  have hFne : hfin.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := extremeSet_nonempty hw S
    exact ⟨x, by rwa [Set.Finite.mem_toFinset]⟩
  obtain ⟨y, L, hymono, hymem, hysurj, hLcard⟩ := exists_monotone_enumeration hfin.toFinset hFne
  have hLn : L + 1 ≤ n := by omega
  have hy0 : 0 < y 0 := pos_of_extremeSet hw hpos hSne (hFsub _ (hymem 0 (Nat.zero_le _)))
  have hmu : ∀ i ≤ L, S.eval (y i) ≠ 0 := by
    intro i hi
    exact (pos_of_mem_extremeSet hw hSne (hFsub _ (hymem i hi))).2
  obtain ⟨g, hgdeg, hgj, hgsign⟩ :=
    exists_sign_realizing_coeffKer (j := j) (n := n) hymono hy0 hmu hLn
  have hall : ∀ x ∈ extremeSet v a b S, 0 < S.eval x * g.eval x := by
    intro x hx
    obtain ⟨i, hi, hxy⟩ := hysurj x (by rwa [Set.Finite.mem_toFinset])
    rw [← hxy]
    exact hgsign i hi
  obtain ⟨ε, hε, hlt⟩ := exists_wsup_lt_of_sign_match hw hSne hall
  have hmem : S - Polynomial.C ε * g ∈ coeffSet n j := by
    refine ⟨?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le hS.1 ?_)
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) hgdeg
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hgj, hS.2]
      ring
  exact absurd (hmin _ hmem) (not_le.mpr hlt)

/-- **Uniqueness.** The minimizer with a prescribed coefficient is unique. -/
theorem coeffSet_minimizer_unique (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n j : ℕ} (hj : j ≤ n) {S₁ S₂ : Polynomial ℝ}
    (hS₁ : S₁ ∈ coeffSet n j) (hS₂ : S₂ ∈ coeffSet n j)
    (hm₁ : ∀ p ∈ coeffSet n j, wsup v a b S₁ ≤ wsup v a b p)
    (hm₂ : ∀ p ∈ coeffSet n j, wsup v a b S₂ ≤ wsup v a b p) : S₁ = S₂ := by
  classical
  have hD : wsup v a b S₁ = wsup v a b S₂ := le_antisymm (hm₁ _ hS₂) (hm₂ _ hS₁)
  set q := Polynomial.C (2⁻¹ : ℝ) * (S₁ + S₂) with hq
  have hqmem : q ∈ coeffSet n j := by
    refine ⟨?_, ?_⟩
    · rw [hq]
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hS₁.1 hS₂.1)
    · rw [hq, Polynomial.coeff_C_mul, Polynomial.coeff_add, hS₁.2, hS₂.2]
      norm_num
  have hqle : wsup v a b q ≤ wsup v a b S₁ := by
    rw [hq, wsup_const_mul hw, show |(2⁻¹ : ℝ)| = 2⁻¹ from by norm_num]
    have h1 := wsup_add_le hw S₁ S₂
    rw [← hD] at h1
    linarith
  have hqD : wsup v a b q = wsup v a b S₁ := le_antisymm hqle (hm₁ _ hqmem)
  have hqmin : ∀ p ∈ coeffSet n j, wsup v a b q ≤ wsup v a b p := by
    intro p hp
    rw [hqD]
    exact hm₁ p hp
  obtain ⟨s, hcard, hsub⟩ := exists_extremeSet_card hw hpos hqmem hqmin
  have hqne : q ≠ 0 := ne_zero_of_mem_coeffSet hqmem
  have hval : ∀ x ∈ s, S₁.eval x = S₂.eval x := by
    intro x hx
    have hxq := hsub x hx
    obtain ⟨hv, _⟩ := pos_of_mem_extremeSet hw hqne hxq
    have hqv : v x * |q.eval x| = wsup v a b q := hxq.2
    have h1 : v x * |S₁.eval x| ≤ wsup v a b S₁ := le_wsup hw S₁ hxq.1
    have h2 : v x * |S₂.eval x| ≤ wsup v a b S₂ := le_wsup hw S₂ hxq.1
    rw [← hD] at h2
    have hqe : q.eval x = 2⁻¹ * (S₁.eval x + S₂.eval x) := by
      rw [hq]
      simp
    have hstep : v x * |S₁.eval x + S₂.eval x| = 2 * wsup v a b S₁ := by
      rw [hqD, hqe, abs_mul, show |(2⁻¹ : ℝ)| = 2⁻¹ from by norm_num] at hqv
      linarith
    have h3 : (2 : ℝ) * wsup v a b S₁ ≤ v x * |S₁.eval x| + v x * |S₂.eval x| := by
      rw [← hstep]
      nlinarith [abs_add_le (S₁.eval x) (S₂.eval x)]
    have hA : v x * |S₁.eval x| = wsup v a b S₁ := by linarith
    have hB : v x * |S₂.eval x| = wsup v a b S₁ := by linarith
    have hvne : v x ≠ 0 := ne_of_gt hv
    have hc : 0 < wsup v a b S₁ / v x :=
      div_pos (wsup_pos hw (ne_zero_of_mem_coeffSet hS₁)) hv
    refine eq_of_abs_add_eq hc ?_ ?_ ?_
    · field_simp
      linarith
    · field_simp
      linarith
    · field_simp
      linarith
  have hddj : (S₁ - S₂).coeff j = 0 := by
    rw [Polynomial.coeff_sub, hS₁.2, hS₂.2]
    ring
  have hdddeg : (S₁ - S₂).natDegree ≤ n :=
    le_trans (Polynomial.natDegree_sub_le _ _) (max_le hS₁.1 hS₂.1)
  have hddroots : ∀ r ∈ s, (S₁ - S₂).eval r = 0 := by
    intro r hr
    rw [Polynomial.eval_sub, hval r hr, sub_self]
  have hspos : ∀ r ∈ s, 0 < r := fun r hr => pos_of_extremeSet hw hpos hqne (hsub r hr)
  by_contra hne
  have hddne : S₁ - S₂ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  exact absurd hddj (coeff_ne_zero_of_positive_roots hddne hdddeg hcard hspos hddroots j hj)

/-! ### The normalized optimizer -/

/-- `T / coeff j T` is the minimizer subject to `coeff j = 1`, and its value is
`wsup T / |coeff j T|`. -/
theorem coeffSet_minimizer_value (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) {j : ℕ} (hj : j ≤ n) :
    Polynomial.C (T.coeff j)⁻¹ * T ∈ coeffSet n j ∧
      (∀ p ∈ coeffSet n j,
        wsup v a b (Polynomial.C (T.coeff j)⁻¹ * T) ≤ wsup v a b p) ∧
      wsup v a b (Polynomial.C (T.coeff j)⁻¹ * T) = wsup v a b T / |T.coeff j| := by
  have hTj : T.coeff j ≠ 0 := coeff_monicDeg_minimizer_ne_zero hw hpos hT hmin j hj
  have hTjabs : 0 < |T.coeff j| := abs_pos.mpr hTj
  have hvalue : wsup v a b (Polynomial.C (T.coeff j)⁻¹ * T) = wsup v a b T / |T.coeff j| := by
    rw [wsup_const_mul hw, abs_inv]
    field_simp
  refine ⟨⟨?_, ?_⟩, ?_, hvalue⟩
  · exact le_trans (Polynomial.natDegree_C_mul_le _ _) hT.1
  · rw [Polynomial.coeff_C_mul, inv_mul_cancel₀ hTj]
  · intro p hp
    have hb := coeff_mul_wsup_le hw hpos hT hmin hj hp.1
    rw [hp.2, abs_one, one_mul] at hb
    rw [hvalue, div_le_iff₀ hTjabs]
    linarith

/-- The minimizer subject to `coeff j = 1` equals `T / coeff j T`. -/
theorem coeffSet_minimizer_eq (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) {j : ℕ} (hj : j ≤ n)
    {S : Polynomial ℝ} (hS : S ∈ coeffSet n j)
    (hSmin : ∀ p ∈ coeffSet n j, wsup v a b S ≤ wsup v a b p) :
    S = Polynomial.C (T.coeff j)⁻¹ * T := by
  obtain ⟨hmem, hminT, _⟩ := coeffSet_minimizer_value hw hpos hT hmin hj
  exact coeffSet_minimizer_unique hw hpos hj hS hmem hSmin hminT

/-- **Equality case.** Equality in the coefficient bound forces a nonzero real multiple of the
minimizer. -/
theorem eq_const_mul_of_coeff_eq (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) {j : ℕ} (hj : j ≤ n)
    {R : Polynomial ℝ} (hR : R.natDegree ≤ n) (hRne : R ≠ 0)
    (heq : |R.coeff j| * wsup v a b T = |T.coeff j| * wsup v a b R) :
    ∃ μ : ℝ, μ ≠ 0 ∧ R = Polynomial.C μ * T := by
  have hTj : T.coeff j ≠ 0 := coeff_monicDeg_minimizer_ne_zero hw hpos hT hmin j hj
  have hTjabs : 0 < |T.coeff j| := abs_pos.mpr hTj
  have hTne : T ≠ 0 := ne_zero_of_mem_coeffSet hT
  have ht : 0 < wsup v a b T := wsup_pos hw hTne
  have hRt : 0 < wsup v a b R := wsup_pos hw hRne
  have hRj : R.coeff j ≠ 0 := by
    intro h
    rw [h, abs_zero, zero_mul] at heq
    nlinarith
  have hRjabs : 0 < |R.coeff j| := abs_pos.mpr hRj
  set S := Polynomial.C (R.coeff j)⁻¹ * R with hS
  have hSmem : S ∈ coeffSet n j := by
    refine ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) hR, ?_⟩
    rw [hS, Polynomial.coeff_C_mul, inv_mul_cancel₀ hRj]
  have hSval : wsup v a b S = wsup v a b R / |R.coeff j| := by
    rw [hS, wsup_const_mul hw, abs_inv]
    field_simp
  obtain ⟨hmemT, hminT, hvalT⟩ := coeffSet_minimizer_value hw hpos hT hmin hj
  have hSeq : wsup v a b S = wsup v a b (Polynomial.C (T.coeff j)⁻¹ * T) := by
    rw [hSval, hvalT, div_eq_div_iff (ne_of_gt hRjabs) (ne_of_gt hTjabs)]
    linarith
  have hSmin : ∀ p ∈ coeffSet n j, wsup v a b S ≤ wsup v a b p := by
    intro p hp
    rw [hSeq]
    exact hminT p hp
  have hfinal := coeffSet_minimizer_eq hw hpos hT hmin hj hSmem hSmin
  refine ⟨R.coeff j * (T.coeff j)⁻¹, mul_ne_zero hRj (inv_ne_zero hTj), ?_⟩
  have hR' : R = Polynomial.C (R.coeff j) * S := by
    rw [hS, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hRj, Polynomial.C_1, one_mul]
  calc R = Polynomial.C (R.coeff j) * S := hR'
    _ = Polynomial.C (R.coeff j) * (Polynomial.C (T.coeff j)⁻¹ * T) := by rw [hfinal]
    _ = Polynomial.C (R.coeff j * (T.coeff j)⁻¹) * T := by
        rw [← mul_assoc, ← Polynomial.C_mul]

/-! ### The root-sum normalization -/

/-- At the penultimate index the minimizer's coefficient is minus the sum of its roots, so the
optimal normalized value is `wsup T` divided by that sum. -/
theorem coeff_pred_eq_neg_sum_roots (hw : IsWeight v a b)
    (hpos : ∀ x ∈ Set.Icc a b, v x ≠ 0 → 0 < x)
    {n : ℕ} (hn : 0 < n) {T : Polynomial ℝ} (hT : T ∈ monicDeg n)
    (hmin : ∀ p ∈ monicDeg n, wsup v a b T ≤ wsup v a b p) :
    ∃ s : Finset ℝ, s.card = n ∧ (∀ r ∈ s, 0 < r ∧ r < b) ∧
      T = ∏ r ∈ s, (Polynomial.X - Polynomial.C r) ∧
      T.coeff (n - 1) = -∑ r ∈ s, r ∧ 0 < ∑ r ∈ s, r := by
  obtain ⟨s, hcard, hspos, hroots, hprod, hub⟩ := monicDeg_minimizer_roots hw hpos hT hmin
  obtain ⟨_, hdeg⟩ := monic_of_mem_monicDeg hT
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨s, hcard, fun r hr => ⟨hspos r hr, hub r hr⟩, hprod, ?_,
    Finset.sum_pos hspos hsne⟩
  rw [hprod, ← hcard]
  exact prod_X_sub_C_coeff_pred s hsne


end
end GaloisForLFunctions.HTGeometry.WeightedMinimax
