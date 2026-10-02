import GaloisForLFunctions.RHTower.DeBruijnNonrealCountApprox
import GaloisForLFunctions.RHTower.XiLaguerrePolya
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness

/-!
# Finitely many nonreal zeros of `Ξ` bound the nonreal count of every `H_t`

If `Ξ = H_0` has only finitely many nonreal zeros, `K` of them counted with multiplicity, then
every `H_t` with `t > 0` has at most `K` nonreal zeros.

`Ξ` is the locally uniform limit of the real polynomials `Ξ(0) ∏ (1 - z/a)`, the product over the
multiplicity copies of a finite zero set closed under `a ↦ -a` and `a ↦ conj a`.  Each has at most
`K` nonreal roots, and all of them are bounded by `|Ξ(0)| exp(2 Σ |a|⁻² |z|²)`, since
`|E₁(z)| ≤ exp(2|z|²)` and the genus-one exponentials cancel in pairs `±a`.  The polynomial
nonreal-count bound transfers to `H_t` for small `t > 0` through Pólya's polynomial heat theorem,
the Gaussian representation and Hurwitz; monotonicity of the count in `t` gives every `t > 0`.
-/

noncomputable section

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

/-! ## The genus-one factor -/

/-- `|E₁(z)| ≤ exp(2|z|²)` for every `z`. -/
theorem norm_weierstrassE1_le_exp_two_mul_sq (z : ℂ) :
    ‖weierstrassE1 z‖ ≤ Real.exp (2 * ‖z‖ ^ 2) := by
  rcases le_or_gt ‖z‖ 1 with hz | hz
  · have h1 := weierstrassE1_sub_one_norm_le hz
    calc ‖weierstrassE1 z‖ = ‖(weierstrassE1 z - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖weierstrassE1 z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖z‖ ^ 2 + 1 := by rw [norm_one]; linarith
      _ ≤ Real.exp (‖z‖ ^ 2) := Real.add_one_le_exp _
      _ ≤ Real.exp (2 * ‖z‖ ^ 2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖z‖])
  · calc ‖weierstrassE1 z‖ = ‖1 - z‖ * Real.exp z.re := by
          rw [weierstrassE1, norm_mul, Complex.norm_exp]
      _ ≤ (1 + ‖z‖) * Real.exp ‖z‖ :=
          mul_le_mul ((norm_sub_le _ _).trans_eq (by rw [norm_one]))
            (Real.exp_le_exp.mpr (Complex.re_le_norm z)) (Real.exp_pos _).le (by positivity)
      _ ≤ Real.exp ‖z‖ * Real.exp ‖z‖ := by
          gcongr
          linarith [Real.add_one_le_exp ‖z‖]
      _ = Real.exp (2 * ‖z‖) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (2 * ‖z‖ ^ 2) := Real.exp_le_exp.mpr (by nlinarith)

/-! ## Zero sets closed under conjugation and reflection -/

/-- A step of the exhaustion of the zeros of `ξ`, together with its complex conjugate. -/
def xiConjClosedFinset (n : ℕ) : Finset XiDivisorSupport :=
  xiSupportExhaustionFinset n ∪ (xiSupportExhaustionFinset n).image xiZeroConjEquiv

theorem xiConjClosedFinset_tendsto : Tendsto xiConjClosedFinset atTop atTop :=
  tendsto_atTop_mono (fun _ => Finset.subset_union_left) xiSupportExhaustionFinset_tendsto_atTop

/-- The reflected and conjugated zero sets are closed under `ρ ↦ 1 - conj ρ`. -/
theorem lineConj_mem_xiSupportSymmFinset {n : ℕ} {ρ : XiDivisorSupport}
    (hρ : ρ ∈ xiSupportSymmFinset (xiConjClosedFinset n)) :
    xiZeroReflectEquiv (xiZeroConjEquiv ρ) ∈ xiSupportSymmFinset (xiConjClosedFinset n) := by
  have hcc : ∀ μ, xiZeroConjEquiv (xiZeroConjEquiv μ) = μ := fun μ => Subtype.ext (by
    change (starRingEnd ℂ) ((starRingEnd ℂ) (μ : ℂ)) = μ
    simp)
  have hrcr : ∀ μ, xiZeroReflectEquiv (xiZeroConjEquiv (xiZeroReflectEquiv μ)) =
      xiZeroConjEquiv μ := fun μ => Subtype.ext (by
    change 1 - (starRingEnd ℂ) (1 - (μ : ℂ)) = (starRingEnd ℂ) (μ : ℂ)
    simp)
  simp only [xiSupportSymmFinset, xiConjClosedFinset, Finset.mem_union, Finset.mem_image] at hρ ⊢
  rcases hρ with (hρ | ⟨μ, hμ, rfl⟩) | ⟨μ, (hμ | ⟨ν, hν, rfl⟩), rfl⟩
  · exact Or.inr ⟨xiZeroConjEquiv ρ, Or.inr ⟨ρ, hρ, rfl⟩, rfl⟩
  · exact Or.inr ⟨μ, Or.inl hμ, by rw [hcc]⟩
  · rw [hrcr]
    exact Or.inl (Or.inr ⟨μ, hμ, rfl⟩)
  · rw [hrcr, hcc]
    exact Or.inl (Or.inl hν)

/-- The multiplicity copies of the closed zero sets are invariant under critical-line
conjugation. -/
theorem xiZeroCopyLineConjEquiv_mem_iff (n : ℕ) (q : XiZeroCopy) :
    q ∈ xiPairedCopyFinset (xiConjClosedFinset n) ↔
      xiZeroCopyLineConjEquiv q ∈ xiPairedCopyFinset (xiConjClosedFinset n) := by
  have hinv : ∀ ρ : XiDivisorSupport,
      xiZeroReflectEquiv (xiZeroConjEquiv (xiZeroReflectEquiv (xiZeroConjEquiv ρ))) = ρ :=
    fun ρ => Subtype.ext (by
      change 1 - (starRingEnd ℂ) (1 - (starRingEnd ℂ) (ρ : ℂ)) = ρ
      simp)
  simp only [xiPairedCopyFinset, Finset.mem_sigma, Finset.mem_univ, and_true]
  constructor
  · exact lineConj_mem_xiSupportSymmFinset
  · intro h
    have := lineConj_mem_xiSupportSymmFinset h
    change xiZeroReflectEquiv (xiZeroConjEquiv (xiZeroReflectEquiv (xiZeroConjEquiv q.1))) ∈ _
      at this
    rwa [hinv] at this

/-! ## The approximating polynomials -/

/-- The polynomial `∏ (1 - z/a)` over a finite set of multiplicity copies of zeros of `Ξ`. -/
def xiZeroPoly (T : Finset XiZeroCopy) : ℂ[X] :=
  ∏ q ∈ T, (1 - C (xiSpectralPoint q)⁻¹ * X)

theorem eval_xiZeroPoly (T : Finset XiZeroCopy) (z : ℂ) :
    (xiZeroPoly T).eval z = ∏ q ∈ T, (1 - z / xiSpectralPoint q) := by
  simp only [xiZeroPoly, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  exact Finset.prod_congr rfl fun q _ => by rw [div_eq_inv_mul]

theorem xiZeroPoly_ne_zero (T : Finset XiZeroCopy) : xiZeroPoly T ≠ 0 := by
  intro h
  have h0 := congrArg (eval 0) h
  rw [eval_xiZeroPoly] at h0
  simp at h0

/-- The roots of `∏ (1 - z/a)` are the points `a`, with multiplicity. -/
theorem roots_xiZeroPoly (T : Finset XiZeroCopy) :
    (xiZeroPoly T).roots = T.val.map xiSpectralPoint := by
  have hroot : ∀ q : XiZeroCopy,
      (1 - C (xiSpectralPoint q)⁻¹ * X : ℂ[X]).roots = {xiSpectralPoint q} := by
    intro q
    have ha := xiSpectralPoint_ne_zero q
    have hfac : (1 - C (xiSpectralPoint q)⁻¹ * X : ℂ[X]) =
        C (-(xiSpectralPoint q)⁻¹) * (X - C (xiSpectralPoint q)) := by
      rw [C_neg, neg_mul, mul_sub, ← C_mul, inv_mul_cancel₀ ha, C_1]
      ring
    rw [hfac, roots_C_mul _ (neg_ne_zero.mpr (inv_ne_zero ha)), roots_X_sub_C]
  have hne := xiZeroPoly_ne_zero T
  rw [xiZeroPoly] at hne ⊢
  rw [roots_prod _ _ hne]
  simp_rw [hroot]
  exact Multiset.bind_singleton _ _

/-- On a set closed under critical-line conjugation, `∏ (1 - z/a)` has real coefficients. -/
theorem map_conj_xiZeroPoly (n : ℕ) :
    (xiZeroPoly (xiPairedCopyFinset (xiConjClosedFinset n))).map (starRingEnd ℂ) =
      xiZeroPoly (xiPairedCopyFinset (xiConjClosedFinset n)) := by
  rw [xiZeroPoly, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X, map_inv₀]
  refine Finset.prod_equiv xiZeroCopyLineConjEquiv (xiZeroCopyLineConjEquiv_mem_iff n) ?_
  intro q _
  rw [xiSpectralPoint_lineConj]

theorem exists_real_xiZeroPoly (n : ℕ) : ∃ R : ℝ[X],
    R.map Complex.ofRealHom = xiZeroPoly (xiPairedCopyFinset (xiConjClosedFinset n)) := by
  have hmem : xiZeroPoly (xiPairedCopyFinset (xiConjClosedFinset n)) ∈
      lifts Complex.ofRealHom := by
    rw [lifts_iff_coeff_lifts]
    intro k
    have h := congrArg (fun P => P.coeff k) (map_conj_xiZeroPoly n)
    simp only [coeff_map] at h
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h
    exact ⟨r, hr.symm⟩
  exact (mem_lifts _).mp hmem

/-- The real polynomial `Ξ(0) ∏ (1 - z/a)` over the `n`-th closed zero set. -/
def xiRealApprox (n : ℕ) : ℝ[X] :=
  C (XiC 0).re * (exists_real_xiZeroPoly n).choose

theorem ofReal_re_XiC_zero : (((XiC 0).re : ℝ) : ℂ) = XiC 0 := by
  have h := XiC_ofReal 0
  rw [Complex.ofReal_zero] at h
  rw [h, Complex.ofReal_re]

theorem XiC_zero_ne_zero : XiC 0 ≠ 0 := by
  have h := riemannHeat_zero_ne (le_refl (0 : ℝ))
  rw [riemannHeat_zero, mul_zero, add_zero] at h
  rwa [XiC, zero_mul, add_zero]

theorem map_xiRealApprox (n : ℕ) :
    (xiRealApprox n).map Complex.ofRealHom =
      C (XiC 0) * xiZeroPoly (xiPairedCopyFinset (xiConjClosedFinset n)) := by
  rw [xiRealApprox, Polynomial.map_mul, map_C, (exists_real_xiZeroPoly n).choose_spec,
    Complex.ofRealHom_eq_coe, ofReal_re_XiC_zero]

theorem eval_map_xiRealApprox (n : ℕ) (z : ℂ) :
    ((xiRealApprox n).map Complex.ofRealHom).eval z =
      XiC 0 * xiPairedE1Product (xiConjClosedFinset n) z := by
  rw [map_xiRealApprox, eval_mul, eval_C, eval_xiZeroPoly, xiPairedE1Product_eq_linear_product]

theorem xiRealApprox_ne_zero (n : ℕ) : xiRealApprox n ≠ 0 := by
  intro h
  have h1 := map_xiRealApprox n
  rw [h, Polynomial.map_zero] at h1
  exact mul_ne_zero (C_ne_zero.mpr XiC_zero_ne_zero) (xiZeroPoly_ne_zero _) h1.symm

/-- The approximants have no more nonreal roots than `Ξ` has nonreal zeros. -/
theorem nonrealRootCount_xiRealApprox_le
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) (n : ℕ) :
    nonrealRootCount (xiRealApprox n) ≤ hfin.toFinset.card := by
  classical
  set T := xiPairedCopyFinset (xiConjClosedFinset n)
  rw [nonrealRootCount_eq, map_xiRealApprox, roots_C_mul _ XiC_zero_ne_zero, roots_xiZeroPoly,
    Multiset.filter_map, Multiset.card_map, ← Finset.filter_val, Finset.card_val]
  refine Finset.card_le_card fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [Set.Finite.mem_toFinset]
  exact hq.2

/-- Locally uniform convergence of the approximants to `H_0 = Ξ`. -/
theorem tendstoLocallyUniformly_xiRealApprox :
    TendstoLocallyUniformly (fun n z => ((xiRealApprox n).map Complex.ofRealHom).eval z)
      (riemannHeat 0) atTop := by
  have h1 : TendstoLocallyUniformly (fun n => xiPairedE1Product (xiConjClosedFinset n))
      xiCanonicalProduct atTop := by
    rw [← tendstoLocallyUniformlyOn_univ]
    intro u hu z hz
    obtain ⟨t, ht, hev⟩ := xiPairedE1Product_tendstoLocallyUniformlyOn u hu z hz
    exact ⟨t, ht, xiConjClosedFinset_tendsto.eventually hev⟩
  have h2 := (lipschitzWith_smul (XiC 0)).uniformContinuous.comp_tendstoLocallyUniformly h1
  have e1 : (fun n z => ((xiRealApprox n).map Complex.ofRealHom).eval z) =
      fun n => (fun w => XiC 0 • w) ∘ xiPairedE1Product (xiConjClosedFinset n) := by
    funext n z
    rw [eval_map_xiRealApprox, Function.comp_apply, smul_eq_mul]
  have e2 : riemannHeat 0 = (fun w => XiC 0 • w) ∘ xiCanonicalProduct := by
    funext z
    have h := congrFun XiC_eq_constant_mul_canonicalProduct z
    simp only [Pi.mul_apply] at h
    rw [riemannHeat_zero, Function.comp_apply, smul_eq_mul, ← h, XiC, mul_comm I z]
  rw [e1, e2]
  exact h2

/-- Gaussian growth of the paired products, uniformly in the zero set. -/
theorem norm_xiPairedE1Product_le (s : Finset XiDivisorSupport) (w : ℂ) :
    ‖xiPairedE1Product s w‖ ≤
      Real.exp (2 * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) * ‖w‖ ^ 2) := by
  rw [xiPairedE1Product]
  calc ‖∏ q ∈ xiPairedCopyFinset s, weierstrassE1 (w / xiSpectralPoint q)‖
      ≤ ∏ q ∈ xiPairedCopyFinset s, ‖weierstrassE1 (w / xiSpectralPoint q)‖ :=
        Finset.norm_prod_le _ _
    _ ≤ ∏ q ∈ xiPairedCopyFinset s,
        Real.exp (2 * ‖w‖ ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) := by
        refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
        refine (norm_weierstrassE1_le_exp_two_mul_sq _).trans_eq ?_
        congr 1
        rw [norm_div, div_pow]
        ring
    _ = Real.exp (2 * ‖w‖ ^ 2 * ∑ q ∈ xiPairedCopyFinset s, 1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (2 * ‖w‖ ^ 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) := by
        gcongr
        exact xiSpectralPoint_inv_sq_summable.sum_le_tsum _ (fun q _ => by positivity)
    _ = Real.exp (2 * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) * ‖w‖ ^ 2) := by
        ring_nf

theorem norm_eval_map_xiRealApprox_le (n : ℕ) (w : ℂ) :
    ‖((xiRealApprox n).map Complex.ofRealHom).eval w‖ ≤
      ‖XiC 0‖ * Real.exp (2 * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) * ‖w‖ ^ 2) := by
  rw [eval_map_xiRealApprox, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_xiPairedE1Product_le _ w) (norm_nonneg _)

/-! ## The transition -/

/-- **Finiteness transition.**  If `Ξ` has only finitely many nonreal zeros, then for every
`t > 0` the number of nonreal zeros of `H_t`, counted with multiplicity, is at most the number of
nonreal zeros of `Ξ`, counted with multiplicity. -/
theorem nonrealZeroCount_le_of_finite_nonreal_zeros
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) {t : ℝ} (ht : 0 < t) :
    nonrealZeroCount t ≤ hfin.toFinset.card := by
  set S : ℝ := 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 with hSdef
  have hS : 0 ≤ S := mul_nonneg zero_le_two (tsum_nonneg fun q => by positivity)
  set t' : ℝ := min t (1 / (8 * S + 8)) with ht'def
  have ht' : 0 < t' := lt_min ht (by positivity)
  have htS : 8 * S * t' < 1 := by
    calc 8 * S * t' ≤ 8 * S * (1 / (8 * S + 8)) := by
          gcongr
          exact min_le_right _ _
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]
          linarith
  have h1 := nonrealZeroCount_le_of_approx (norm_nonneg (XiC 0)) hS xiRealApprox_ne_zero
    (nonrealRootCount_xiRealApprox_le hfin) tendstoLocallyUniformly_xiRealApprox
    norm_eval_map_xiRealApprox_le ht' htS
  exact (nonrealZeroCount_antitoneOn ht' ht (min_le_left _ _)).trans h1

end RHTower.DeBruijn
