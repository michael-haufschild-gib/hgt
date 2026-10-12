import GaloisForLFunctions.RHTower.XiShiftedIntervalLaguerrePolyaRH
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

/-!
# The number of nonreal zeros of `Ξ` is a window approximation budget

For a real polynomial `P` let `Z_c(P)` be its number of nonreal roots, with multiplicity
(`nonrealRootCount`).

**Theorem** (`sum_zeroMult_XiC_le_of_window`). Let `P_n` be real polynomials with `Z_c(P_n) ≤ m`
converging to `Ξ` uniformly on one real interval `[c − ε, c + ε]`, `ε > 0`. Then the nonreal zeros
of `Ξ` have total multiplicity at most `m`.

**Theorem** (`encard_nonrealCopies_le_iff_window`). Together with the polynomial
approximation of `Ξ` through its zero set, this gives an exact law: `Ξ` has at most `m` nonreal
zeros, counted with multiplicity, iff `Ξ` is a uniform limit on some, equivalently every, real
window of real polynomials with at most `m` nonreal roots. The case `m = 0` is RH.

**Proof.**
* Factor `P = r·q` over `ℝ`, with `r` real-rooted and `q` free of real roots, `deg q ≤ m`.
* Normalize `q` at a real base point `b` far from its roots:
  `q(z)/q(b) = ∏(1 + (z − b)u_j)` with `|u_j| ≤ 2/δ`. Among `m + 1` equally spaced candidates in
  a zero-free subwindow, one always keeps all `≤ m` roots at distance `δ/2`.
* Along a subsequence the base point is fixed and `u → v`, so `q(z)/q(b) → Q(z) = ∏(1 + (z − b)v_j)`
  uniformly on the window. Then the real-rooted parts `q(b)·r` converge there to `Ξ/Q`.
* Low-frequency rigidity (`exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window`)
  gives an entire `g`, with only real zeros (Hurwitz), and `g(z)·Q(b+z)Q(b−z) = Ξ(b+z)Ξ(b−z)`
  (identity theorem).
* At a nonreal `z` the order of `Ξ(b+z)Ξ(b−z)` is therefore the order of `Q(b+z)Q(b−z)`, a
  product of `2m` affine factors. Summing over the points `ρ − b` and `b − ρ` gives
  `2 Σ ord_ρ Ξ ≤ 2m`.
-/

open Complex Filter Topology Set Polynomial Metric

namespace RHTower.WindowNonrealBudget

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Splitting off the real roots -/

/-- A nonzero real polynomial is a real-rooted polynomial times a polynomial without real roots,
whose degree is the number of nonreal roots. -/
theorem exists_splits_mul_noRealRoots {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ r q : ℝ[X], r.Splits ∧ q ≠ 0 ∧ q.roots = 0 ∧ p = r * q ∧
      q.natDegree = nonrealRootCount p := by
  classical
  set r : ℝ[X] := (p.roots.map fun a => X - C a).prod with hr
  obtain ⟨q, hq⟩ := prod_multiset_X_sub_C_dvd p
  have hr0 : r ≠ 0 := (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hp hq
  have hroots : p.roots = r.roots + q.roots := by
    rw [hq, roots_mul (hq ▸ hp)]
  have hrr : r.roots = p.roots := roots_multiset_prod_X_sub_C _
  have hqr : q.roots = 0 := by
    rw [hrr] at hroots
    exact (add_eq_left.mp hroots.symm)
  have hdeg : p.natDegree = r.natDegree + q.natDegree := by
    rw [hq, natDegree_mul hr0 hq0]
  have hrdeg : r.natDegree = Multiset.card p.roots := natDegree_multiset_prod_X_sub_C_eq_card _
  refine ⟨r, q, ?_, hq0, hqr, hq, ?_⟩
  · rw [splits_iff_card_roots, hrr, hrdeg]
  · rw [nonrealRootCount, hdeg, hrdeg]
    omega

/-- The complex roots of a real polynomial without real roots are nonreal. -/
theorem im_ne_zero_of_mem_roots_map {q : ℝ[X]} (hq : q ≠ 0) (hqr : q.roots = 0) {w : ℂ}
    (hw : w ∈ (q.map (algebraMap ℝ ℂ)).roots) : w.im ≠ 0 := by
  intro him
  have hmap : q.map (algebraMap ℝ ℂ) ≠ 0 := (Polynomial.map_ne_zero_iff
    (algebraMap ℝ ℂ).injective).mpr hq
  have hroot := (mem_roots hmap).mp hw
  have hw' : w = ((w.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
  rw [hw', IsRoot, eval_map_algebraMap] at hroot
  change polyEvalC q (w.re : ℂ) = 0 at hroot
  rw [polyEvalC_ofReal] at hroot
  have : q.IsRoot w.re := by exact_mod_cast hroot
  have hmem : w.re ∈ q.roots := (mem_roots hq).mpr this
  rw [hqr] at hmem
  exact Multiset.notMem_zero _ hmem

/-- **Affine normalization at a real base point.** -/
theorem polyEvalC_eq_mul_prod {q : ℝ[X]} (hq : q ≠ 0) (hqr : q.roots = 0) (b : ℝ) (z : ℂ) :
    polyEvalC q z = polyEvalC q b *
      ((q.map (algebraMap ℝ ℂ)).roots.map fun w => 1 + (z - b) * (1 / ((b : ℂ) - w))).prod := by
  set Q := q.map (algebraMap ℝ ℂ) with hQ
  have hsplit : Q.roots.card = Q.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits Q)
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have heval : ∀ y : ℂ, polyEvalC q y = Q.leadingCoeff * (Q.roots.map fun w => y - w).prod := by
    intro y
    rw [polyEvalC_eq_eval_map, ← hQ]
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  have hne : ∀ w ∈ Q.roots, (b : ℂ) - w ≠ 0 := by
    intro w hw h
    have := im_ne_zero_of_mem_roots_map hq hqr hw
    apply this
    have h' : w = (b : ℂ) := (sub_eq_zero.mp h).symm
    rw [h', Complex.ofReal_im]
  rw [heval z, heval b, mul_assoc, ← Multiset.prod_map_mul]
  congr 1
  refine congrArg _ (Multiset.map_congr rfl fun w hw => ?_)
  have := hne w hw
  field_simp
  ring

/-! ## Padding to a fixed number of affine factors -/

/-- The multiset `U` of `m` affine parameters, as a vector. -/
def padVec (m : ℕ) (U : Multiset ℂ) (hU : Multiset.card U = m) : Fin m → ℂ :=
  fun j => U.toList[(j : ℕ)]'(by rw [Multiset.length_toList, hU]; exact j.2)

theorem prod_map_eq_prod_padVec {m : ℕ} (U : Multiset ℂ) (hU : Multiset.card U = m)
    (f : ℂ → ℂ) : (U.map f).prod = ∏ j : Fin m, f (padVec m U hU j) := by
  have hl : U.toList.length = m := by rw [Multiset.length_toList, hU]
  have h1 : (U.map f).prod = (U.toList.map f).prod := by
    conv_lhs => rw [← Multiset.coe_toList U]
    rw [Multiset.map_coe, Multiset.prod_coe]
  rw [h1, ← Fin.prod_univ_fun_getElem]
  exact Fintype.prod_equiv (finCongr hl) _ _ fun j => rfl

/-- The padded affine parameters of a real polynomial without real roots. -/
def rootParams (m : ℕ) (q : ℝ[X]) (b : ℝ) : Multiset ℂ :=
  ((q.map (algebraMap ℝ ℂ)).roots.map fun w => 1 / ((b : ℂ) - w)) +
    Multiset.replicate (m - (q.map (algebraMap ℝ ℂ)).roots.card) 0

theorem card_rootParams {m : ℕ} {q : ℝ[X]} (hm : q.natDegree ≤ m) (b : ℝ) :
    Multiset.card (rootParams m q b) = m := by
  have hc : Multiset.card (q.map (algebraMap ℝ ℂ)).roots ≤ m :=
    (card_roots' _).trans ((natDegree_map_le).trans hm)
  simp only [rootParams, Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
  omega

theorem polyEvalC_eq_mul_prod_padVec {m : ℕ} {q : ℝ[X]} (hq : q ≠ 0) (hqr : q.roots = 0)
    (hm : q.natDegree ≤ m) (b : ℝ) (z : ℂ) :
    polyEvalC q z = polyEvalC q b *
      ∏ j : Fin m, (1 + (z - b) * padVec m (rootParams m q b) (card_rootParams hm b) j) := by
  rw [polyEvalC_eq_mul_prod hq hqr b z,
    ← prod_map_eq_prod_padVec _ (card_rootParams hm b) (fun u => 1 + (z - b) * u)]
  congr 1
  simp only [rootParams, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
    Function.comp_def, Multiset.map_replicate, mul_zero, add_zero, Multiset.prod_replicate,
    one_pow, mul_one]

theorem norm_padVec_le {m : ℕ} {q : ℝ[X]} (hm : q.natDegree ≤ m) (b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hfar : ∀ w ∈ (q.map (algebraMap ℝ ℂ)).roots, δ ≤ ‖w - b‖) (j : Fin m) :
    ‖padVec m (rootParams m q b) (card_rootParams hm b) j‖ ≤ 1 / δ := by
  have hmem : padVec m (rootParams m q b) (card_rootParams hm b) j ∈ rootParams m q b := by
    unfold padVec
    exact Multiset.mem_toList.mp (List.getElem_mem _)
  rcases Multiset.mem_add.mp hmem with h | h
  · obtain ⟨w, hw, hwe⟩ := Multiset.mem_map.mp h
    rw [← hwe, norm_div, norm_one, norm_sub_rev]
    exact one_div_le_one_div_of_le hδ (hfar w hw)
  · rw [Multiset.eq_of_mem_replicate h, norm_zero]
    positivity

/-! ## Choosing the base point -/

/-- Among `m + 1` points spaced `2δ` apart, some point is at distance `≥ δ/2` from every member
of a multiset of at most `m` complex numbers. -/
theorem exists_far_basePoint {m : ℕ} {a δ : ℝ} (hδ : 0 < δ) (N : Multiset ℂ)
    (hN : Multiset.card N ≤ m) :
    ∃ i : Fin (m + 1), ∀ w ∈ N, δ / 2 ≤ ‖w - ((a + (2 * i + 1) * δ : ℝ) : ℂ)‖ := by
  classical
  by_contra hall
  push Not at hall
  choose w hwN hwlt using hall
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hne
    have h1 := hwlt i
    have h2 := hwlt j
    rw [hij] at h1
    have h3 : ‖((a + (2 * i + 1) * δ : ℝ) : ℂ) - ((a + (2 * j + 1) * δ : ℝ) : ℂ)‖ < δ := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (((a + (2 * i + 1) * δ : ℝ) : ℂ)) (w j)
        (((a + (2 * j + 1) * δ : ℝ) : ℂ))
      rw [norm_sub_rev _ (w j)] at ht
      linarith
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h3
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    have hdist : 2 * δ ≤ |(a + (2 * (i : ℝ) + 1) * δ) - (a + (2 * (j : ℝ) + 1) * δ)| := by
      rw [show (a + (2 * (i : ℝ) + 1) * δ) - (a + (2 * (j : ℝ) + 1) * δ) =
        2 * δ * ((i : ℝ) - j) by ring, abs_mul, abs_of_pos (by positivity : 0 < 2 * δ)]
      have : (1 : ℝ) ≤ |(i : ℝ) - j| := by
        rcases lt_or_gt_of_ne hij' with h | h
        · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
          rw [abs_of_neg (by linarith)]; linarith
        · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
          rw [abs_of_pos (by linarith)]; linarith
      nlinarith
    linarith
  have hcard : Fintype.card (Fin (m + 1)) ≤ N.toFinset.card := by
    have := Finset.card_le_card_of_injOn (s := Finset.univ) (t := N.toFinset) w
      (fun i _ => Multiset.mem_toFinset.mpr (hwN i)) (fun i _ j _ h => hinj h)
    simpa using this
  have := (Multiset.toFinset_card_le N).trans hN
  simp at hcard
  omega

/-! ## Convergence of the normalized products -/

/-- Telescoping bound for finite products of numbers of modulus at most `M ≥ 1`. -/
theorem norm_prod_sub_prod_le : ∀ {m : ℕ} (a b : Fin m → ℂ) {M : ℝ}, 1 ≤ M →
    (∀ j, ‖a j‖ ≤ M) → (∀ j, ‖b j‖ ≤ M) →
    ‖∏ j, a j - ∏ j, b j‖ ≤ (∑ j, ‖a j - b j‖) * M ^ m
  | 0, a, b, M, _, _, _ => by simp
  | m + 1, a, b, M, hM, ha, hb => by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have ih := norm_prod_sub_prod_le (fun j => a j.succ) (fun j => b j.succ) hM
      (fun j => ha _) (fun j => hb _)
    have hB : ‖∏ j : Fin m, b j.succ‖ ≤ M ^ m := by
      rw [norm_prod]
      calc ∏ j : Fin m, ‖b j.succ‖ ≤ ∏ _j : Fin m, M :=
            Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hb _
        _ = M ^ m := by simp
    have hM0 : 0 ≤ M := by linarith
    have e : a 0 * ∏ j : Fin m, a j.succ - b 0 * ∏ j : Fin m, b j.succ =
        a 0 * (∏ j : Fin m, a j.succ - ∏ j : Fin m, b j.succ) +
          (a 0 - b 0) * ∏ j : Fin m, b j.succ := by ring
    rw [e]
    have hS : 0 ≤ ∑ j : Fin m, ‖a j.succ - b j.succ‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hMm : M ^ m ≤ M ^ (m + 1) := pow_le_pow_right₀ hM (Nat.le_succ m)
    calc ‖a 0 * (∏ j : Fin m, a j.succ - ∏ j : Fin m, b j.succ) +
          (a 0 - b 0) * ∏ j : Fin m, b j.succ‖
        ≤ ‖a 0‖ * ‖∏ j : Fin m, a j.succ - ∏ j : Fin m, b j.succ‖ +
            ‖a 0 - b 0‖ * ‖∏ j : Fin m, b j.succ‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M * ((∑ j : Fin m, ‖a j.succ - b j.succ‖) * M ^ m) + ‖a 0 - b 0‖ * M ^ m := by
          gcongr
          exact ha 0
      _ ≤ (‖a 0 - b 0‖ + ∑ j : Fin m, ‖a j.succ - b j.succ‖) * M ^ (m + 1) := by
          have h1 : ‖a 0 - b 0‖ * M ^ m ≤ ‖a 0 - b 0‖ * M ^ (m + 1) :=
            mul_le_mul_of_nonneg_left hMm (norm_nonneg _)
          rw [show (‖a 0 - b 0‖ + ∑ j : Fin m, ‖a j.succ - b j.succ‖) * M ^ (m + 1) =
            M * ((∑ j : Fin m, ‖a j.succ - b j.succ‖) * M ^ m) + ‖a 0 - b 0‖ * M ^ (m + 1) by
              rw [pow_succ]; ring]
          linarith

/-- Products of affine factors converge uniformly on a bounded real set when their parameters
converge. -/
theorem tendstoUniformlyOn_prod_affine {m : ℕ} {V : ℕ → Fin m → ℂ} {v : Fin m → ℂ} {R : ℝ}
    (hV : ∀ k, ‖V k‖ ≤ R) (hv : ‖v‖ ≤ R) (hconv : Tendsto V atTop (𝓝 v)) (b : ℝ) {η : ℝ}
    (hη : 0 ≤ η) :
    TendstoUniformlyOn (fun k (t : ℝ) => ∏ j, (1 + ((t : ℂ) - b) * V k j))
      (fun t : ℝ => ∏ j, (1 + ((t : ℂ) - b) * v j)) atTop (Icc (b - η) (b + η)) := by
  set M : ℝ := 1 + η * R with hMdef
  have hR : 0 ≤ R := (norm_nonneg _).trans hv
  have hM : 1 ≤ M := by rw [hMdef]; nlinarith
  have hfac : ∀ (u : Fin m → ℂ), ‖u‖ ≤ R → ∀ t ∈ Icc (b - η) (b + η), ∀ j,
      ‖1 + ((t : ℂ) - b) * u j‖ ≤ M := by
    intro u hu t ht j
    have htb : ‖(t : ℂ) - b‖ ≤ η := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc ‖1 + ((t : ℂ) - b) * u j‖ ≤ 1 + ‖(t : ℂ) - b‖ * ‖u j‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_one, norm_mul]
      _ ≤ 1 + η * R := by
          gcongr
          exact (norm_le_pi_norm u j).trans hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hpos : 0 < (m + 1) * (η + 1) * M ^ m := by positivity
  filter_upwards [Metric.tendsto_nhds.mp hconv (ε / ((m + 1) * (η + 1) * M ^ m)) (by positivity)]
    with k hk t ht
  rw [dist_eq_norm]
  refine (norm_prod_sub_prod_le _ _ hM (hfac v hv t ht) (hfac (V k) (hV k) t ht)).trans_lt ?_
  have htb : ‖(t : ℂ) - b‖ ≤ η := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hterm : ∀ j, ‖1 + ((t : ℂ) - b) * v j - (1 + ((t : ℂ) - b) * V k j)‖ ≤
      (η + 1) * dist (V k) v := by
    intro j
    rw [show 1 + ((t : ℂ) - b) * v j - (1 + ((t : ℂ) - b) * V k j) =
      ((t : ℂ) - b) * (v j - V k j) by ring, norm_mul]
    have hj : ‖v j - V k j‖ ≤ dist (V k) v := by
      rw [dist_comm, dist_eq_norm]
      exact norm_le_pi_norm (v - V k) j
    calc ‖(t : ℂ) - b‖ * ‖v j - V k j‖ ≤ η * dist (V k) v :=
          mul_le_mul htb hj (norm_nonneg _) hη
      _ ≤ (η + 1) * dist (V k) v := by nlinarith [dist_nonneg (x := V k) (y := v)]
  calc (∑ j, ‖1 + ((t : ℂ) - b) * v j - (1 + ((t : ℂ) - b) * V k j)‖) * M ^ m
      ≤ (∑ _j : Fin m, (η + 1) * dist (V k) v) * M ^ m := by
        gcongr with j
        exact hterm j
    _ = m * (η + 1) * dist (V k) v * M ^ m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ (m + 1) * (η + 1) * M ^ m * dist (V k) v := by
        have := dist_nonneg (x := V k) (y := v)
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ M) m]
    _ < (m + 1) * (η + 1) * M ^ m * (ε / ((m + 1) * (η + 1) * M ^ m)) :=
        mul_lt_mul_of_pos_left hk hpos
    _ = ε := by field_simp

/-! ## Orders of reflected products -/

/-- `Ξ` has finite order at every point. -/
theorem analyticOrderAt_XiC_ne_top (w : ℂ) : analyticOrderAt XiC w ≠ ⊤ := by
  have h0 : analyticOrderAt XiC 0 ≠ ⊤ := by
    rw [(XiC_analytic 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr XiC_zero_ne]
    exact ENat.zero_ne_top
  exact XiC_analytic.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0)
    (mem_univ w) h0

theorem XiC_differentiable : Differentiable ℂ XiC := fun z =>
  (XiC_analytic z (mem_univ z)).differentiableAt

/-- The order of `Ξ(b + z)Ξ(b − z)` at `z` is the sum of the orders of `Ξ` at `b + z` and `b − z`. -/
theorem zeroMult_reflect_XiC (b z : ℂ) :
    zeroMult (fun w => XiC (b + w) * XiC (b - w)) z = zeroMult XiC (b + z) + zeroMult XiC (b - z) := by
  have han : ∀ w, AnalyticAt ℂ XiC w := fun w => XiC_analytic w (mem_univ w)
  obtain ⟨n₁, hn₁⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_XiC_ne_top (b + z))
  obtain ⟨n₂, hn₂⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_XiC_ne_top (b - z))
  have h1 : analyticOrderAt (fun w => XiC (1 * w + b)) z = n₁ :=
    analyticOrderAt_comp_affine one_ne_zero (han _) (by rw [show 1 * z + b = b + z by ring]; exact hn₁.symm)
  have h2 : analyticOrderAt (fun w => XiC ((-1) * w + b)) z = n₂ :=
    analyticOrderAt_comp_affine (by norm_num) (han _) (by rw [show (-1) * z + b = b - z by ring]; exact hn₂.symm)
  have e1 : (fun w => XiC (1 * w + b)) = fun w => XiC (b + w) := funext fun w => by ring_nf
  have e2 : (fun w => XiC ((-1) * w + b)) = fun w => XiC (b - w) := funext fun w => by ring_nf
  rw [e1] at h1
  rw [e2] at h2
  have ha1 : AnalyticAt ℂ (fun w => XiC (b + w)) z := (XiC_differentiable.comp
    ((differentiable_const b).add differentiable_id)).analyticAt z
  have ha2 : AnalyticAt ℂ (fun w => XiC (b - w)) z := (XiC_differentiable.comp
    ((differentiable_const b).sub differentiable_id)).analyticAt z
  have hmul : analyticOrderAt (fun w => XiC (b + w) * XiC (b - w)) z =
      analyticOrderAt (fun w => XiC (b + w)) z + analyticOrderAt (fun w => XiC (b - w)) z :=
    analyticOrderAt_mul ha1 ha2
  unfold zeroMult
  rw [hmul, h1, h2, ← hn₁, ← hn₂]
  rfl

/-! ## The polynomial of the reflected affine factors -/

/-- `∏(1 + z v_j)·∏(1 − z v_j)`. -/
def reflectAffinePoly {m : ℕ} (v : Fin m → ℂ) : ℂ[X] :=
  (∏ j, ((1 : ℂ[X]) + X * C (v j))) * ∏ j, ((1 : ℂ[X]) - X * C (v j))

theorem eval_reflectAffinePoly {m : ℕ} (v : Fin m → ℂ) (z : ℂ) :
    (reflectAffinePoly v).eval z = (∏ j, (1 + v j * z)) * ∏ j, (1 - v j * z) := by
  simp [reflectAffinePoly, eval_prod]

theorem reflectAffinePoly_ne_zero {m : ℕ} (v : Fin m → ℂ) : reflectAffinePoly v ≠ 0 := by
  intro h
  have := eval_reflectAffinePoly v 0
  rw [h, eval_zero] at this
  simp at this

theorem natDegree_reflectAffinePoly_le {m : ℕ} (v : Fin m → ℂ) :
    (reflectAffinePoly v).natDegree ≤ 2 * m := by
  have h1 : ∀ j, ((1 : ℂ[X]) + X * C (v j)).natDegree ≤ 1 := fun j => by
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_mul_le).trans (by simp)
  have h2 : ∀ j, ((1 : ℂ[X]) - X * C (v j)).natDegree ≤ 1 := fun j => by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_mul_le).trans (by simp)
  have hp1 : (∏ j, ((1 : ℂ[X]) + X * C (v j))).natDegree ≤ m := by
    refine (natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun j _ => h1 j).trans ?_)
    simp
  have hp2 : (∏ j, ((1 : ℂ[X]) - X * C (v j))).natDegree ≤ m := by
    refine (natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun j _ => h2 j).trans ?_)
    simp
  unfold reflectAffinePoly
  exact (natDegree_mul_le).trans (by omega)

/-- Root multiplicities of a nonzero polynomial over a finite set add up to at most its degree. -/
theorem sum_rootMultiplicity_le_natDegree (p : ℂ[X]) (T : Finset ℂ) :
    ∑ z ∈ T, p.rootMultiplicity z ≤ p.natDegree := by
  classical
  calc ∑ z ∈ T, p.rootMultiplicity z = ∑ z ∈ T, p.roots.count z := by
        simp_rw [count_roots]
    _ ≤ ∑ z ∈ T ∪ p.roots.toFinset, p.roots.count z :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ z ∈ p.roots.toFinset, p.roots.count z := by
        refine (Finset.sum_subset Finset.subset_union_right fun z _ hz => ?_).symm
        exact Multiset.count_eq_zero.mpr (fun h => hz (Multiset.mem_toFinset.mpr h))
    _ = Multiset.card p.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ p.natDegree := card_roots' p

/-! ## The budget theorem -/

theorem laguerrePolya_polyEvalC_of_splits {p : ℝ[X]} (hp : p.Splits) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (polyEvalC p) :=
  ⟨fun _ => p, fun _ => hp, Metric.tendstoLocallyUniformly_iff.2
    fun δ hδ _ => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => by simpa using hδ⟩⟩

/-- **The nonreal zeros of `Ξ` cost their multiplicity in every window approximation.** If real
polynomials with at most `m` nonreal roots converge to `Ξ` uniformly on one real interval, then the
nonreal zeros of `Ξ` have total multiplicity at most `m`. -/
theorem sum_zeroMult_XiC_le_of_window {m : ℕ} {P : ℕ → ℝ[X]}
    (hcount : ∀ n, nonrealRootCount (P n) ≤ m) {c ε : ℝ} (hε : 0 < ε)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (P n) t) (fun t : ℝ => XiC t) atTop
      (Icc (c - ε) (c + ε)))
    (E : Finset ℂ) (hE : ∀ e ∈ E, e.im ≠ 0) :
    ∑ e ∈ E, zeroMult XiC e ≤ m := by
  classical
  -- a zero-free subwindow and `m + 1` candidate base points in it
  obtain ⟨c₁, ε₁, hε₁, hsub, hne⟩ := IntervalLaguerrePolya.exists_zeroFree_subwindow (c := c) hε
  have hconv₁ := hconv.mono hsub
  set δ : ℝ := ε₁ / (m + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδm : (m + 1 : ℝ) * δ = ε₁ := by rw [hδdef]; field_simp
  set bpt : Fin (m + 1) → ℝ := fun i => (c₁ - ε₁) + (2 * i + 1) * δ with hbpt
  -- split off the real roots
  have hfac : ∀ n, ∃ r q : ℝ[X], P n ≠ 0 → (r.Splits ∧ q ≠ 0 ∧ q.roots = 0 ∧ P n = r * q ∧
      q.natDegree = nonrealRootCount (P n)) := by
    intro n
    by_cases hP : P n = 0
    · exact ⟨0, 0, fun h => absurd hP h⟩
    · obtain ⟨r, q, h⟩ := exists_splits_mul_noRealRoots hP
      exact ⟨r, q, fun _ => h⟩
  choose r q hrq using hfac
  have hc₁mem : c₁ ∈ Icc (c₁ - ε₁) (c₁ + ε₁) := ⟨by linarith, by linarith⟩
  have hPne : ∀ᶠ n in atTop, P n ≠ 0 := by
    have h := (hconv₁.tendsto_at hc₁mem).eventually_ne (hne c₁ hc₁mem)
    filter_upwards [h] with n hn hP
    apply hn
    rw [hP]
    simp [polyEvalC]
  -- one base point is good infinitely often
  have hgood : ∀ᶠ n in atTop, ∃ i : Fin (m + 1), P n ≠ 0 ∧
      ∀ w ∈ ((q n).map (algebraMap ℝ ℂ)).roots, δ / 2 ≤ ‖w - (bpt i : ℂ)‖ := by
    filter_upwards [hPne] with n hn
    obtain ⟨-, -, -, -, hdeg⟩ := hrq n hn
    have hcard : Multiset.card ((q n).map (algebraMap ℝ ℂ)).roots ≤ m :=
      (card_roots' _).trans (natDegree_map_le.trans (hdeg ▸ hcount n))
    obtain ⟨i, hi⟩ := exists_far_basePoint (a := c₁ - ε₁) hδ _ hcard
    exact ⟨i, hn, hi⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin (m + 1), ∃ᶠ n in atTop, P n ≠ 0 ∧
      ∀ w ∈ ((q n).map (algebraMap ℝ ℂ)).roots, δ / 2 ≤ ‖w - (bpt i : ℂ)‖ := by
    by_contra hall
    push Not at hall
    obtain ⟨n, hn1, hn2⟩ := ((Filter.eventually_all.mpr hall).and hgood).exists
    obtain ⟨j, hj0, hj⟩ := hn2
    obtain ⟨w, hw, hwlt⟩ := hn1 j hj0
    exact absurd (hj w hw) (not_le.mpr hwlt)
  obtain ⟨φ₁, hφ₁, hφ₁P⟩ := Filter.extraction_of_frequently_atTop hi
  set b : ℝ := bpt i with hbdef
  have hi_le : (i : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp i.2
  have hb_lo : c₁ - ε₁ + δ ≤ b := by
    rw [hbdef, hbpt]; dsimp only; nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hb_hi : b + δ ≤ c₁ + ε₁ := by
    rw [hbdef, hbpt]; dsimp only; nlinarith
  -- the data along the first subsequence
  have hP1 : ∀ k, P (φ₁ k) ≠ 0 := fun k => (hφ₁P k).1
  have hdegle : ∀ k, (q (φ₁ k)).natDegree ≤ m := fun k => by
    rw [(hrq _ (hP1 k)).2.2.2.2]; exact hcount _
  set V : ℕ → Fin m → ℂ := fun k =>
    padVec m (rootParams m (q (φ₁ k)) b) (card_rootParams (hdegle k) b) with hVdef
  have hVb : ∀ k, ‖V k‖ ≤ 2 / δ := by
    intro k
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    have h := norm_padVec_le (hdegle k) b (δ := δ / 2) (by positivity) (fun w hw => (hφ₁P k).2 w hw) j
    rwa [one_div_div] at h
  obtain ⟨v, hvmem, φ₂, hφ₂, hVconv⟩ := tendsto_subseq_of_bounded (isBounded_closedBall)
    (fun k => mem_closedBall_zero_iff.mpr (hVb k))
  have hv : ‖v‖ ≤ 2 / δ := by
    rw [isClosed_closedBall.closure_eq] at hvmem
    exact mem_closedBall_zero_iff.mp hvmem
  set ψ : ℕ → ℕ := φ₁ ∘ φ₂ with hψdef
  have hψ : Tendsto ψ atTop atTop := (hφ₁.comp hφ₂).tendsto_atTop
  -- the limit of the normalized nonreal parts
  set Qt : ℂ → ℂ := fun z => ∏ j, (1 + (z - b) * v j) with hQt
  have hQtc : Continuous Qt := by
    refine continuous_finsetProd _ fun j _ => ?_
    exact continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)
  have hQtb : Qt b = 1 := by simp [hQt]
  set Qk : ℕ → ℂ → ℂ := fun k z => ∏ j, (1 + (z - b) * V (φ₂ k) j) with hQk
  -- the real-rooted parts
  set Fp : ℕ → ℝ[X] := fun k => C ((q (ψ k)).eval b) * r (ψ k) with hFp
  have hdata : ∀ k, (r (ψ k)).Splits ∧ q (ψ k) ≠ 0 ∧ (q (ψ k)).roots = 0 ∧
      P (ψ k) = r (ψ k) * q (ψ k) := fun k => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hrq _ (hP1 (φ₂ k))
    exact ⟨h1, h2, h3, h4⟩
  have hqb : ∀ k, (q (ψ k)).eval b ≠ 0 := by
    intro k hk
    obtain ⟨-, hq0, hqr, -⟩ := hdata k
    have : b ∈ (q (ψ k)).roots := (mem_roots hq0).mpr hk
    rw [hqr] at this
    exact Multiset.notMem_zero _ this
  have hFpsplit : ∀ k, (Fp k).Splits := fun k => (Splits.C _).mul (hdata k).1
  have hFp0 : ∀ k, Fp k ≠ 0 := by
    intro k h
    rcases mul_eq_zero.mp h with h | h
    · exact hqb k (C_eq_zero.mp h)
    · apply hP1 (φ₂ k)
      show P (ψ k) = 0
      rw [(hdata k).2.2.2, h, zero_mul]
  have hPF : ∀ k z, polyEvalC (P (ψ k)) z = polyEvalC (Fp k) z * Qk k z := by
    intro k z
    obtain ⟨-, hq0, hqr, hPrq⟩ := hdata k
    rw [hPrq, polyEvalC_mul, polyEvalC_eq_mul_prod_padVec hq0 hqr (hdegle (φ₂ k)) b z, hFp]
    dsimp only
    rw [polyEvalC_mul, polyEvalC_C, polyEvalC_ofReal]
    simp only [hQk, hVdef, hψdef, Function.comp_apply]
    ring
  -- a window around `b` on which `Qt` stays near `1`
  obtain ⟨η₀, hη₀, hη₀Q⟩ := Metric.continuousAt_iff.mp
    ((hQtc.comp Complex.continuous_ofReal).continuousAt (x := b)) (1 / 2) (by norm_num)
  set η : ℝ := min δ (η₀ / 2) with hηdef
  have hη : 0 < η := lt_min hδ (by positivity)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηη₀ : η < η₀ := (min_le_right _ _).trans_lt (by linarith)
  set W : Set ℝ := Icc (b - η) (b + η) with hW
  have hWsub : W ⊆ Icc (c₁ - ε₁) (c₁ + ε₁) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hQlow : ∀ t ∈ W, 1 / 2 ≤ ‖Qt t‖ := by
    intro t ht
    have hd : dist t b < η₀ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have h := hη₀Q hd
    simp only [Function.comp_apply, hQtb] at h
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (1 : ℂ) (1 - Qt t)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  have hQunif : TendstoUniformlyOn (fun k (t : ℝ) => Qk k t) (fun t : ℝ => Qt t) atTop W :=
    tendstoUniformlyOn_prod_affine (fun k => hVb (φ₂ k)) hv hVconv b hη.le
  have hQklow : ∀ᶠ k in atTop, ∀ t ∈ W, 1 / 4 ≤ ‖Qk k t‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hQunif (1 / 4) (by norm_num)] with k hk t ht
    have h1 := hk t ht
    have h2 := hQlow t ht
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (Qt t) (Qk k t)
    linarith
  -- uniform convergence of the real-rooted parts to `Ξ/Qt`
  have hWc : IsCompact W := isCompact_Icc
  obtain ⟨MX, hMX⟩ := hWc.exists_bound_of_continuousOn
    ((XiC_differentiable.continuous.comp Complex.continuous_ofReal).continuousOn (s := W))
  obtain ⟨MQ, hMQ⟩ := hWc.exists_bound_of_continuousOn
    ((hQtc.comp Complex.continuous_ofReal).continuousOn (s := W))
  have hPψ : TendstoUniformlyOn (fun k (t : ℝ) => polyEvalC (P (ψ k)) t) (fun t : ℝ => XiC t)
      atTop W := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv₁ ⊢
    intro e he
    filter_upwards [hψ.eventually (hconv₁ e he)] with k hk t ht
    exact hk t (hWsub ht)
  have hFunif : TendstoUniformlyOn (fun k (t : ℝ) => polyEvalC (Fp k) t)
      (fun t : ℝ => XiC t / Qt t) atTop W := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    set A : ℝ := 8 * (|MQ| + |MX| + 1) with hA
    have hApos : 0 < A := by positivity
    filter_upwards [hQklow, Metric.tendstoUniformlyOn_iff.mp hPψ (e / A) (by positivity),
      Metric.tendstoUniformlyOn_iff.mp hQunif (e / A) (by positivity)] with k hk1 hk2 hk3 t ht
    have hq1 := hk1 t ht
    have hq2 := hQlow t ht
    have hQk0 : Qk k t ≠ 0 := fun h => by rw [h, norm_zero] at hq1; norm_num at hq1
    have hQt0 : Qt t ≠ 0 := fun h => by rw [h, norm_zero] at hq2; norm_num at hq2
    have hF : polyEvalC (Fp k) t = polyEvalC (P (ψ k)) t / Qk k t := by
      rw [hPF k t, mul_div_assoc, div_self hQk0, mul_one]
    rw [dist_eq_norm, hF]
    have e1 : XiC t / Qt t - polyEvalC (P (ψ k)) t / Qk k t =
        ((XiC t - polyEvalC (P (ψ k)) t) * Qt t + XiC t * (Qk k t - Qt t)) / (Qk k t * Qt t) := by
      field_simp
      ring
    have hd1 : ‖XiC t - polyEvalC (P (ψ k)) t‖ < e / A := by
      have := hk2 t ht; rwa [dist_eq_norm] at this
    have hd2 : ‖Qk k t - Qt t‖ < e / A := by
      have := hk3 t ht; rwa [dist_eq_norm, norm_sub_rev] at this
    have hX : ‖XiC t‖ ≤ |MX| := (hMX t ht).trans (le_abs_self _)
    have hQ : ‖Qt t‖ ≤ |MQ| := (hMQ t ht).trans (le_abs_self _)
    rw [e1, norm_div, norm_mul]
    have hden : 1 / 8 ≤ ‖Qk k t‖ * ‖Qt t‖ := by nlinarith
    rw [div_lt_iff₀ (by linarith)]
    have hnum : ‖(XiC t - polyEvalC (P (ψ k)) t) * Qt t + XiC t * (Qk k t - Qt t)‖ ≤
        e / A * |MQ| + |MX| * (e / A) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have h1 : ‖XiC t - polyEvalC (P (ψ k)) t‖ * ‖Qt t‖ ≤ e / A * |MQ| :=
        mul_le_mul hd1.le hQ (norm_nonneg _) (by positivity)
      have h2 : ‖XiC t‖ * ‖Qk k t - Qt t‖ ≤ |MX| * (e / A) :=
        mul_le_mul hX hd2.le (norm_nonneg _) (abs_nonneg _)
      linarith
    have hA' : e / A * (|MQ| + |MX|) * 8 < e := by
      rw [hA, div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ hApos]
      nlinarith [abs_nonneg MQ, abs_nonneg MX]
    nlinarith
  -- shift the window to the origin
  have hFLP : ∀ k, GaloisForLFunctions.HTGeometry.LaguerrePolya (fun z => polyEvalC (Fp k) (b + z)) :=
    fun k => IntervalLaguerrePolya.laguerrePolya_comp_add
      (laguerrePolya_polyEvalC_of_splits (hFpsplit k)) b
  set G' : ℂ → ℂ := fun z => XiC (b + z) / Qt (b + z) with hG'
  have hmapW : ∀ s ∈ Icc (-η) η, b + s ∈ W := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hQt0W : ∀ t ∈ W, Qt t ≠ 0 := fun t ht h => by
    have := hQlow t ht; rw [h, norm_zero] at this; norm_num at this
  have hG'c : ContinuousOn (fun s : ℝ => G' s) (Icc (-η) η) := by
    intro s hs
    have hQ0 : Qt (b + s) ≠ 0 := by
      have := hQt0W (b + s) (hmapW s hs); push_cast at this; exact this
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : Continuous fun s : ℝ => XiC (b + s) :=
      XiC_differentiable.continuous.comp (continuous_const.add Complex.continuous_ofReal)
    have h2 : Continuous fun s : ℝ => Qt (b + s) :=
      hQtc.comp (continuous_const.add Complex.continuous_ofReal)
    exact (h1.continuousAt).div h2.continuousAt hQ0
  have hG'ne : ∀ s : ℝ, |s| ≤ η → G' s ≠ 0 := by
    intro s hs
    have hsm : s ∈ Icc (-η) η := abs_le.mp hs
    have hX0 : XiC (b + s) ≠ 0 := by
      have := hne (b + s) (hWsub (hmapW s hsm)); push_cast at this; exact this
    have hQ0 : Qt (b + s) ≠ 0 := by
      have := hQt0W (b + s) (hmapW s hsm); push_cast at this; exact this
    exact div_ne_zero hX0 hQ0
  have hF'conv : TendstoUniformlyOn (fun k (t : ℝ) => polyEvalC (Fp k) (b + t)) (fun t : ℝ => G' t)
      atTop (Icc (-η) η) := by
    rw [Metric.tendstoUniformlyOn_iff] at hFunif ⊢
    intro e he
    filter_upwards [hFunif e he] with k hk t ht
    have := hk (b + t) (hmapW t ht)
    push_cast at this
    exact this
  obtain ⟨σ, g, hσ, hgdiff, hgconv, hgint⟩ :=
    IntervalLaguerrePolya.exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window hFLP hη
      hG'c hG'ne hF'conv
  have h0mem : (0 : ℝ) ∈ Icc (-η) η := ⟨by linarith, hη.le⟩
  have hg0 : g 0 ≠ 0 := by
    have h := hgint 0 h0mem
    simp only [Complex.ofReal_zero, neg_zero] at h
    rw [h]
    have := hG'ne 0 (by rw [abs_zero]; exact hη.le)
    simp only [Complex.ofReal_zero] at this
    exact mul_ne_zero this this
  -- the zeros of `g` are real
  have hgreal : ∀ z, g z = 0 → z.im = 0 := by
    intro z hz
    have hgan : AnalyticOnNhd ℂ g univ := fun w _ => hgdiff.analyticAt w
    refine zero_mem_closed_of_tendstoLocallyUniformly hgconv hgan
      (Eventually.of_forall fun k => (hFLP (σ k)).differentiable.mul
        ((hFLP (σ k)).differentiable.comp differentiable_neg))
      (isClosed_eq Complex.continuous_im continuous_const) (Eventually.of_forall fun k w hw => ?_)
      hg0 hz
    rcases mul_eq_zero.mp hw with h | h
    · have := im_eq_zero_of_splits (hFpsplit (σ k)) (hFp0 (σ k)) h
      simpa using this
    · have := im_eq_zero_of_splits (hFpsplit (σ k)) (hFp0 (σ k)) h
      simpa using this
  -- the identity `g(z)·Qt(b+z)Qt(b−z) = Ξ(b+z)Ξ(b−z)`
  have hid : ∀ z, g z * (Qt (b + z) * Qt (b - z)) = XiC (b + z) * XiC (b - z) := by
    have hLan : AnalyticOnNhd ℂ (fun z => g z * (Qt (b + z) * Qt (b - z))) univ := by
      have hd : Differentiable ℂ Qt := by
        intro z
        refine DifferentiableAt.fun_finsetProd fun j _ => ?_
        fun_prop
      exact fun z _ => (hgdiff.mul ((hd.comp ((differentiable_const _).add differentiable_id)).mul
        (hd.comp ((differentiable_const _).sub differentiable_id)))).analyticAt z
    have hRan : AnalyticOnNhd ℂ (fun z => XiC (b + z) * XiC (b - z)) univ := fun z _ =>
      ((XiC_differentiable.comp ((differentiable_const _).add differentiable_id)).mul
        (XiC_differentiable.comp ((differentiable_const _).sub differentiable_id))).analyticAt z
    have hseq : Tendsto (fun k : ℕ => ((η / (k + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η
        rw [mul_zero] at h
        have := (Complex.continuous_ofReal.tendsto 0).comp h
        simpa [Function.comp_def, div_eq_mul_inv] using this
      · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    have hmem : ∀ k : ℕ, η / (k + 1) ∈ Icc (-η) η := by
      intro k
      have hk : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      constructor
      · have : 0 ≤ η / (k + 1) := by positivity
        linarith
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    have hpt : ∀ t ∈ Icc (-η) η, g t * (Qt (b + t) * Qt (b - t)) = XiC (b + t) * XiC (b - t) := by
      intro t ht
      rw [hgint t ht]
      have hQ1 : Qt (b + t) ≠ 0 := by
        have := hQt0W (b + t) (hmapW t ht); push_cast at this; exact this
      have hQ2 : Qt (b - t) ≠ 0 := by
        have := hQt0W (b + -t) (hmapW (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
        push_cast at this
        rwa [← sub_eq_add_neg] at this
      simp only [hG', ← sub_eq_add_neg]
      field_simp
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
        g z * (Qt (b + z) * Qt (b - z)) = XiC (b + z) * XiC (b - z) :=
      hseq.frequently (Frequently.of_forall fun k => hpt _ (hmem k))
    intro z
    exact hLan.eqOn_of_preconnected_of_frequently_eq hRan isPreconnected_univ (mem_univ 0) hfreq
      (mem_univ z)
  -- counting orders at nonreal points
  set B : ℂ[X] := reflectAffinePoly v with hB
  have hB0 : B ≠ 0 := reflectAffinePoly_ne_zero v
  have hQB : ∀ z, Qt (b + z) * Qt (b - z) = B.eval z := by
    intro z
    rw [hB, eval_reflectAffinePoly]
    simp only [hQt]
    congr 1 <;> exact Finset.prod_congr rfl fun j _ => by ring
  have hcount_pt : ∀ z : ℂ, z.im ≠ 0 →
      zeroMult XiC (b + z) + zeroMult XiC (b - z) = B.rootMultiplicity z := by
    intro z hz
    rw [← zeroMult_reflect_XiC]
    have hfun : (fun w => XiC (b + w) * XiC (b - w)) = g * fun w => B.eval w := by
      funext w
      rw [Pi.mul_apply, ← hQB w, hid w]
    rw [hfun]
    have hgz : g z ≠ 0 := fun h => hz (hgreal z h)
    have hga : AnalyticAt ℂ g z := hgdiff.analyticAt z
    have hBa : AnalyticAt ℂ (fun w => B.eval w) z := B.differentiable.analyticAt z
    unfold zeroMult
    rw [analyticOrderAt_mul hga hBa, hga.analyticOrderAt_eq_zero.mpr hgz, zero_add,
      analyticOrderAt_eval_eq_rootMultiplicity hB0]
    simp
  set T : Finset ℂ := E.image (fun e => e - (b : ℂ)) ∪ E.image (fun e => (b : ℂ) - e) with hT
  have hTim : ∀ z ∈ T, z.im ≠ 0 := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      simpa using hE e he
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      simpa using hE e he
  have h1 : ∑ e ∈ E, zeroMult XiC e =
      ∑ z ∈ E.image (fun e => e - (b : ℂ)), zeroMult XiC (b + z) := by
    rw [Finset.sum_image (fun x _ y _ h => sub_left_inj.mp h)]
    exact Finset.sum_congr rfl fun e _ => by rw [add_sub_cancel]
  have h2 : ∑ e ∈ E, zeroMult XiC e =
      ∑ z ∈ E.image (fun e => (b : ℂ) - e), zeroMult XiC (b - z) := by
    rw [Finset.sum_image (fun x _ y _ h => sub_right_inj.mp h)]
    exact Finset.sum_congr rfl fun e _ => by rw [sub_sub_cancel]
  have h3 : ∑ z ∈ T, (zeroMult XiC (b + z) + zeroMult XiC (b - z)) ≤ 2 * m := by
    rw [Finset.sum_congr rfl fun z hz => hcount_pt z (hTim z hz)]
    exact (sum_rootMultiplicity_le_natDegree B T).trans (natDegree_reflectAffinePoly_le v)
  have h4 : ∑ z ∈ E.image (fun e => e - (b : ℂ)), zeroMult XiC (b + z) ≤
      ∑ z ∈ T, zeroMult XiC (b + z) := Finset.sum_le_sum_of_subset Finset.subset_union_left
  have h5 : ∑ z ∈ E.image (fun e => (b : ℂ) - e), zeroMult XiC (b - z) ≤
      ∑ z ∈ T, zeroMult XiC (b - z) := Finset.sum_le_sum_of_subset Finset.subset_union_right
  rw [Finset.sum_add_distrib] at h3
  omega

/-! ## The exact law -/

theorem one_le_zeroMult_XiC {z : ℂ} (hz : XiC z = 0) : 1 ≤ zeroMult XiC z := by
  unfold zeroMult
  have h0 : analyticOrderAt XiC z ≠ 0 := by
    rw [Ne, (XiC_analytic z (mem_univ z)).analyticOrderAt_eq_zero]
    exact not_not.mpr hz
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_XiC_ne_top z)
  rw [← hn] at h0 ⊢
  simp only [ENat.toNat_coe]
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h0)

/-- Window approximation with at most `m` nonreal roots forces finitely many nonreal zeros of `Ξ`,
at most `m` of them counted with multiplicity. -/
theorem encard_nonrealCopies_le_of_window {m : ℕ} {P : ℕ → ℝ[X]}
    (hcount : ∀ n, nonrealRootCount (P n) ≤ m) {c ε : ℝ} (hε : 0 < ε)
    (hconv : TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (P n) t) (fun t : ℝ => XiC t) atTop
      (Icc (c - ε) (c + ε))) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m := by
  classical
  have hbound := sum_zeroMult_XiC_le_of_window hcount hε hconv
  have hZ : {z : ℂ | DeBruijn.riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite := by
    by_contra hinf
    obtain ⟨E, hEsub, hEcard⟩ := Set.Infinite.exists_subset_card_eq hinf (m + 1)
    have hE : ∀ e ∈ E, e.im ≠ 0 := fun e he => (hEsub he).2
    have hle := hbound E hE
    have hge : m + 1 ≤ ∑ e ∈ E, zeroMult XiC e := by
      calc m + 1 = ∑ _e ∈ E, 1 := by simp [hEcard]
        _ ≤ ∑ e ∈ E, zeroMult XiC e := Finset.sum_le_sum fun e he => by
            have h := (hEsub he).1
            rw [DeBruijn.riemannHeat_zero_eq_XiC] at h
            exact one_le_zeroMult_XiC h
    omega
  have hfin := DeBruijn.finite_nonrealCopies_of_finite_zeros hZ
  rw [hfin.encard_eq_coe_toFinset_card, DeBruijn.card_nonrealCopies_eq_sum_zeroMult hfin,
    DeBruijn.riemannHeat_zero_eq_XiC]
  have hE : ∀ e ∈ hfin.toFinset.image xiSpectralPoint, e.im ≠ 0 := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    exact (hfin.mem_toFinset.mp hq)
  exact_mod_cast hbound _ hE

/-- **The nonreal zero count of `Ξ` is a window approximation budget.** For every real interval
`[c − ε, c + ε]`, `ε > 0`, and every `m`: `Ξ` has at most `m` nonreal zeros, counted with
multiplicity, iff `Ξ` is a uniform limit on that interval of real polynomials with at most `m`
nonreal roots each. For `m = 0` this is RH (MUST-1276). -/
theorem encard_nonrealCopies_le_iff_window {m : ℕ} {c ε : ℝ} (hε : 0 < ε) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ m ↔
      ∃ P : ℕ → ℝ[X], (∀ n, nonrealRootCount (P n) ≤ m) ∧
        TendstoUniformlyOn (fun n (t : ℝ) => polyEvalC (P n) t) (fun t : ℝ => XiC t) atTop
          (Icc (c - ε) (c + ε)) := by
  constructor
  · intro hle
    have hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite :=
      Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.coe_ne_top m) hle)
    have hcard : hfin.toFinset.card ≤ m := by
      rw [hfin.encard_eq_coe_toFinset_card] at hle
      exact_mod_cast hle
    refine ⟨DeBruijn.xiRealApprox, fun n =>
      (DeBruijn.nonrealRootCount_xiRealApprox_le hfin n).trans hcard, ?_⟩
    have hloc := DeBruijn.tendstoLocallyUniformly_xiRealApprox
    rw [DeBruijn.riemannHeat_zero_eq_XiC] at hloc
    have hK : IsCompact ((fun t : ℝ => (t : ℂ)) '' Icc (c - ε) (c + ε)) :=
      isCompact_Icc.image Complex.continuous_ofReal
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc) _ hK
    have hu' := (hu.comp (fun t : ℝ => (t : ℂ))).mono (fun t ht => ⟨t, ht, rfl⟩)
    refine hu'.congr (Eventually.of_forall fun n t _ => ?_)
    simp only [Function.comp_apply, polyEvalC_eq_eval_map]
    rfl
  · rintro ⟨P, hP, hconv⟩
    exact encard_nonrealCopies_le_of_window hP hε hconv

end

end RHTower.WindowNonrealBudget
