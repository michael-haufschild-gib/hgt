import GaloisForLFunctions.HTGeometry.WeierstrassProductMultiplicity

/-!
# The Weierstrass canonical product over a *padded* zero sequence

The corpus product `weierstrassGenusProduct a z = ∏' n, E_n (z / a n)` was set up for a sequence of
nonzero points with `‖a n‖ → ∞`.  That hypothesis cannot describe a function with only finitely
many zeros, which is exactly the case a general factorization theorem must also cover.

The fix costs nothing.  In Lean `z / 0 = 0` and `E_p 0 = 1`, so an entry `a n = 0` contributes the
*trivial* factor `1`: zeros of the sequence are inert.  Consequently the single hypothesis

`PaddedZeroSeq a : ∀ r, {n | a n ≠ 0 ∧ ‖a n‖ ≤ r}.Finite`

— every disc contains finitely many nonzero entries — already forces local uniform convergence, and
a finite zero set is handled by padding the sequence with zeros.  This file re-proves the whole
convergence and divisor package under that hypothesis:

* `hasProdLocallyUniformlyOn_padded` — local uniform convergence,
* `differentiable_weierstrassGenusProduct_padded` — the product is entire,
* `weierstrassGenusProduct_eq_zero_iff_padded` — its zero set is exactly the nonzero entries,
* `analyticOrderAt_weierstrassGenusProduct_padded` — its order at `z₀ ≠ 0` is the multiplicity of
  `z₀` in the sequence, and its order at the origin is `0`.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set

noncomputable section

/-- A **padded zero sequence**: every disc contains only finitely many nonzero entries.  Entries
equal to `0` are inert, so this single hypothesis covers finite and infinite zero sets alike. -/
def PaddedZeroSeq (a : ℕ → ℂ) : Prop := ∀ r : ℝ, {n : ℕ | a n ≠ 0 ∧ ‖a n‖ ≤ r}.Finite

theorem paddedZeroSeq_of_tendsto {a : ℕ → ℂ} (ha : Tendsto (fun n => ‖a n‖) atTop atTop) :
    PaddedZeroSeq a := by
  intro r
  refine (finite_setOf_norm_lt ha (r + 1)).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn ⊢
  linarith [hn.2]

/-! ### Inert entries -/

@[simp] theorem weierstrassGenusFactorAt_zero_point {a : ℕ → ℂ} {n : ℕ} (h : a n = 0) (z : ℂ) :
    weierstrassGenusFactorAt a n z = 1 := by
  rw [weierstrassGenusFactorAt, h, div_zero, weierstrassFactor_zero_arg]

@[simp] theorem weierstrassGenusFactorAt_at_zero (a : ℕ → ℂ) (n : ℕ) :
    weierstrassGenusFactorAt a n 0 = 1 := by
  rw [weierstrassGenusFactorAt, zero_div, weierstrassFactor_zero_arg]

@[simp] theorem weierstrassGenusProduct_at_zero (a : ℕ → ℂ) : weierstrassGenusProduct a 0 = 1 := by
  rw [weierstrassGenusProduct, tprod_congr (weierstrassGenusFactorAt_at_zero a), tprod_one]

theorem differentiable_weierstrassGenusFactorAt_padded (a : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (weierstrassGenusFactorAt a n) :=
  (differentiable_weierstrassFactor n).comp (differentiable_id.div_const (a n))

/-! ### The uniform estimate -/

theorem norm_paddedFactor_sub_one_le {a : ℕ → ℂ} {n : ℕ} {z : ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) (hn : a n = 0 ∨ 2 * R ≤ ‖a n‖) :
    ‖weierstrassGenusFactorAt a n z - 1‖ ≤ Real.exp 1 * (1 / 2 : ℝ) ^ (n + 1) := by
  by_cases hane : a n = 0
  · rw [weierstrassGenusFactorAt_zero_point hane, sub_self, norm_zero]
    positivity
  · have hfar : 2 * R ≤ ‖a n‖ := hn.resolve_left hane
    have hapos : 0 < ‖a n‖ := norm_pos_iff.mpr hane
    have hhalf : ‖z / a n‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ hapos]
      linarith
    refine le_trans (norm_weierstrassFactor_sub_one_le_uniform n hhalf) ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    exact pow_le_pow_left₀ (norm_nonneg _) hhalf _

theorem eventually_cofinite_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (r : ℝ) :
    ∀ᶠ n in Filter.cofinite, a n = 0 ∨ r ≤ ‖a n‖ := by
  rw [Filter.eventually_cofinite]
  refine (ha r).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq, not_or, not_le] at hn ⊢
  exact ⟨hn.1, hn.2.le⟩

theorem eventually_atTop_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (r : ℝ) :
    ∀ᶠ n in atTop, a n = 0 ∨ r ≤ ‖a n‖ := by
  rw [← Nat.cofinite_eq_atTop]
  exact eventually_cofinite_padded ha r

/-! ### Convergence -/

/-- **The padded Weierstrass product converges locally uniformly.** -/
theorem hasProdLocallyUniformlyOn_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) :
    HasProdLocallyUniformlyOn (weierstrassGenusFactorAt a) (weierstrassGenusProduct a) univ := by
  classical
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_norm (E := ℂ)).continuousOn
  set R : ℝ := max C 0 with hR
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz =>
    (hC (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hbound : ∀ᶠ n : ℕ in cofinite, ∀ z ∈ K,
      ‖weierstrassGenusFactorAt a n z - 1‖ ≤ Real.exp 1 * (1 / 2 : ℝ) ^ (n + 1) := by
    filter_upwards [eventually_cofinite_padded ha (2 * R)] with n hn z hz
    exact norm_paddedFactor_sub_one_le (hKR z hz) hn
  have hcont : ∀ n : ℕ, ContinuousOn (fun z => weierstrassGenusFactorAt a n z - 1) K := fun n =>
    ((differentiable_weierstrassGenusFactorAt_padded a n).continuous.sub
      continuous_const).continuousOn
  have hprod := Summable.hasProdUniformlyOn_one_add hK summable_uniform_bound hbound hcont
  have heq : (fun (n : ℕ) (z : ℂ) => 1 + (weierstrassGenusFactorAt a n z - 1))
      = weierstrassGenusFactorAt a := by
    funext n z; ring
  have heq2 : (fun z : ℂ => ∏' n : ℕ, (1 + (weierstrassGenusFactorAt a n z - 1)))
      = weierstrassGenusProduct a := by
    funext z
    rw [weierstrassGenusProduct]
    exact tprod_congr fun n => by ring
  rw [heq, heq2] at hprod
  exact hprod

/-- **The padded Weierstrass product is entire.** -/
theorem differentiable_weierstrassGenusProduct_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) :
    Differentiable ℂ (weierstrassGenusProduct a) := by
  have ht : TendstoLocallyUniformlyOn
      (fun (S : Finset ℕ) (z : ℂ) => ∏ n ∈ S, weierstrassGenusFactorAt a n z)
      (weierstrassGenusProduct a) atTop univ :=
    hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      (hasProdLocallyUniformlyOn_padded ha)
  have hd : ∀ᶠ S : Finset ℕ in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, weierstrassGenusFactorAt a n z) univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_weierstrassGenusFactorAt_padded a n).differentiableOn
  have := ht.differentiableOn hd isOpen_univ
  exact fun z => this.differentiableAt (by simp)

/-! ### The zero set -/

theorem weierstrassGenusFactorAt_eq_zero_iff_padded (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    weierstrassGenusFactorAt a n z = 0 ↔ (a n ≠ 0 ∧ z = a n) := by
  rw [weierstrassGenusFactorAt, weierstrassFactor_eq_zero_iff]
  constructor
  · intro h
    rcases eq_or_ne (a n) 0 with h0 | h0
    · rw [h0, div_zero] at h
      exact absurd h zero_ne_one
    · exact ⟨h0, (div_eq_one_iff_eq h0).mp h⟩
  · rintro ⟨h0, rfl⟩
    exact div_self h0

theorem summable_norm_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (z : ℂ) :
    Summable fun n : ℕ => ‖weierstrassGenusFactorAt a n z - 1‖ := by
  refine Summable.of_norm_bounded_eventually_nat summable_uniform_bound ?_
  filter_upwards [eventually_atTop_padded ha (2 * ‖z‖)] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_paddedFactor_sub_one_le le_rfl hn

theorem multipliable_weierstrassGenusFactorAt_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (z : ℂ) :
    Multipliable fun n : ℕ => weierstrassGenusFactorAt a n z := by
  have := multipliable_one_add_of_summable
    (f := fun n : ℕ => weierstrassGenusFactorAt a n z - 1) (summable_norm_padded ha z)
  exact this.congr fun n => by ring

/-- **The zero set of the padded Weierstrass product.**  It vanishes exactly at the nonzero entries
of the sequence. -/
theorem weierstrassGenusProduct_eq_zero_iff_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (z : ℂ) :
    weierstrassGenusProduct a z = 0 ↔ ∃ n : ℕ, a n ≠ 0 ∧ z = a n := by
  constructor
  · intro h
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hne : ∀ n : ℕ, 1 + (weierstrassGenusFactorAt a n z - 1) ≠ 0 := by
      intro n
      have heq : (1 : ℂ) + (weierstrassGenusFactorAt a n z - 1)
          = weierstrassGenusFactorAt a n z := by ring
      rw [heq]
      intro hz
      obtain ⟨h0, hzn⟩ := (weierstrassGenusFactorAt_eq_zero_iff_padded a n z).mp hz
      exact hcon n h0 hzn
    have hprod : ∏' n : ℕ, (1 + (weierstrassGenusFactorAt a n z - 1)) ≠ 0 :=
      tprod_one_add_ne_zero_of_summable hne (summable_norm_padded ha z)
    apply hprod
    rw [← h, weierstrassGenusProduct]
    exact tprod_congr fun n => by ring
  · rintro ⟨n, h0, hn⟩
    exact tprod_of_exists_eq_zero
      ⟨n, (weierstrassGenusFactorAt_eq_zero_iff_padded a n z).mpr ⟨h0, hn⟩⟩

/-! ### The exact order -/

theorem finite_zeroIndices_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) {z : ℂ} (hz : z ≠ 0) :
    {n : ℕ | a n = z}.Finite := by
  refine (ha ‖z‖).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn ⊢
  rw [hn]
  exact ⟨hz, le_rfl⟩

theorem multipliable_weierstrassGenusFactorAt_subtype_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a)
    (p : ℕ → Prop) (w : ℂ) :
    Multipliable fun n : {n : ℕ // p n} => weierstrassGenusFactorAt a (n : ℕ) w := by
  have hsum : Summable fun n : {n : ℕ // p n} => ‖weierstrassGenusFactorAt a (n : ℕ) w - 1‖ :=
    (summable_norm_padded ha w).subtype p
  have hmul := multipliable_one_add_of_summable
    (f := fun n : {n : ℕ // p n} => weierstrassGenusFactorAt a (n : ℕ) w - 1) hsum
  exact hmul.congr fun n => by ring

/-- **Splitting the padded product at a finite set of indices.** -/
theorem weierstrassGenusProduct_split_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (S : Finset ℕ)
    (w : ℂ) :
    weierstrassGenusProduct a w
      = (∏ n ∈ S, weierstrassGenusFactorAt a n w)
        * ∏' n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ}, weierstrassGenusFactorAt a (n : ℕ) w :=
  tprod_eq_prod_mul_tprod_compl (f := fun n => weierstrassGenusFactorAt a n w)
    (multipliable_weierstrassGenusFactorAt_padded ha w) S
    (multipliable_weierstrassGenusFactorAt_subtype_padded ha (fun n => n ∈ (↑S : Set ℕ)ᶜ) w)

theorem paddedZeroSeq_awaySeq {a : ℕ → ℂ} (ha : PaddedZeroSeq a) (S : Finset ℕ) (z₀ : ℂ) :
    PaddedZeroSeq (awaySeq a S z₀) := by
  intro r
  refine ((ha r).union S.finite_toSet).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn
  by_cases hS : n ∈ S
  · exact Set.mem_union_right _ (Finset.mem_coe.mpr hS)
  · rw [awaySeq_of_notMem hS] at hn
    exact Set.mem_union_left _ hn

/-- The padded product does not vanish at the origin. -/
theorem analyticOrderAt_weierstrassGenusProduct_padded_zero {a : ℕ → ℂ} (ha : PaddedZeroSeq a) :
    analyticOrderAt (weierstrassGenusProduct a) 0 = 0 := by
  have hPana : AnalyticAt ℂ (weierstrassGenusProduct a) 0 :=
    (differentiable_weierstrassGenusProduct_padded ha).analyticAt 0
  refine hPana.analyticOrderAt_eq_zero.mpr ?_
  rw [weierstrassGenusProduct_at_zero]
  exact one_ne_zero

set_option maxHeartbeats 2000000 in
/-- **The exact order of the padded Weierstrass product.**  At a nonzero point the product vanishes
to the order given by the multiplicity of that point in the sequence. -/
theorem analyticOrderAt_weierstrassGenusProduct_padded {a : ℕ → ℂ} (ha : PaddedZeroSeq a)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    analyticOrderAt (weierstrassGenusProduct a) z₀ = ({n : ℕ | a n = z₀}.ncard : ℕ) := by
  classical
  have hfin := finite_zeroIndices_padded ha hz₀
  set S : Finset ℕ := hfin.toFinset with hSdef
  have hmemS : ∀ n : ℕ, n ∈ S ↔ a n = z₀ := fun n => by
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcard : {n : ℕ | a n = z₀}.ncard = S.card := by
    rw [hSdef, Set.ncard_eq_toFinset_card _ hfin]
  have hPana : AnalyticAt ℂ (weierstrassGenusProduct a) z₀ :=
    (differentiable_weierstrassGenusProduct_padded ha).analyticAt z₀
  set b : ℕ → ℂ := awaySeq a S z₀ with hbdef
  have hout : ∀ n, n ∉ S → a n ≠ z₀ := fun n hn h => hn ((hmemS n).2 h)
  have hbz : ∀ n, b n ≠ z₀ := awaySeq_ne hout
  have hbpad : PaddedZeroSeq b := paddedZeroSeq_awaySeq ha S z₀
  have hbP : Differentiable ℂ (weierstrassGenusProduct b) :=
    differentiable_weierstrassGenusProduct_padded hbpad
  have hPb0 : weierstrassGenusProduct b z₀ ≠ 0 := by
    intro h
    obtain ⟨n, _, hn⟩ := (weierstrassGenusProduct_eq_zero_iff_padded hbpad z₀).1 h
    exact hbz n hn.symm
  have hDb : Differentiable ℂ (fun w => ∏ n ∈ S, weierstrassGenusFactorAt b n w) := by
    have hprod : (fun w : ℂ => ∏ n ∈ S, weierstrassGenusFactorAt b n w)
        = ∏ n ∈ S, weierstrassGenusFactorAt b n := by
      funext w
      rw [Finset.prod_apply]
    rw [hprod]
    exact Differentiable.finsetProd fun n _ => differentiable_weierstrassGenusFactorAt_padded b n
  have hDb0 : (∏ n ∈ S, weierstrassGenusFactorAt b n z₀) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun n _ => ?_
    intro h
    exact hbz n ((weierstrassGenusFactorAt_eq_zero_iff_padded b n z₀).1 h).2.symm
  set U : ℂ → ℂ := fun w => (-(z₀)⁻¹) ^ S.card
      * Complex.exp (∑ n ∈ S, weierstrassLog n (w / z₀)) with hUdef
  have hUdiff : Differentiable ℂ U := by
    rw [hUdef]
    refine (differentiable_const _).mul ?_
    refine Complex.differentiable_exp.comp ?_
    refine Differentiable.fun_sum fun n _ => ?_
    have hlog : Differentiable ℂ (weierstrassLog n) := fun w =>
      (hasDerivAt_weierstrassLog n w).differentiableAt
    exact hlog.comp (differentiable_id.div_const z₀)
  have hU0 : U z₀ ≠ 0 := by
    rw [hUdef]
    refine mul_ne_zero (pow_ne_zero _ ?_) (Complex.exp_ne_zero _)
    simp [hz₀]
  set G : ℂ → ℂ := fun w => U w
      * (weierstrassGenusProduct b w / ∏ n ∈ S, weierstrassGenusFactorAt b n w) with hGdef
  have hGana : AnalyticAt ℂ G z₀ :=
    (hUdiff.analyticAt z₀).mul (((hbP.analyticAt z₀)).div (hDb.analyticAt z₀) hDb0)
  have hG0 : G z₀ ≠ 0 := mul_ne_zero hU0 (div_ne_zero hPb0 hDb0)
  have hkey : ∀ᶠ w in nhds z₀, weierstrassGenusProduct a w = (w - z₀) ^ S.card • G w := by
    have hne : ∀ᶠ w in nhds z₀, (∏ n ∈ S, weierstrassGenusFactorAt b n w) ≠ 0 :=
      (hDb.continuous.continuousAt).eventually_ne hDb0
    filter_upwards [hne] with w hw
    have hsa := weierstrassGenusProduct_split_padded ha S w
    have hsb := weierstrassGenusProduct_split_padded hbpad S w
    have htail : (∏' n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ}, weierstrassGenusFactorAt a (n : ℕ) w)
        = ∏' n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ}, weierstrassGenusFactorAt b (n : ℕ) w := by
      refine tprod_congr fun n => ?_
      have hn : (n : ℕ) ∉ S := by
        have h2 := n.2
        rwa [Set.mem_compl_iff, Finset.mem_coe] at h2
      rw [weierstrassGenusFactorAt, weierstrassGenusFactorAt, hbdef, awaySeq_of_notMem hn]
    have hprodA : (∏ n ∈ S, weierstrassGenusFactorAt a n w) = (w - z₀) ^ S.card * U w := by
      have hterm : ∀ n ∈ S, weierstrassGenusFactorAt a n w
          = (w - z₀) * ((-(z₀)⁻¹) * Complex.exp (weierstrassLog n (w / z₀))) := by
        intro n hn
        have haz : a n = z₀ := (hmemS n).1 hn
        rw [weierstrassGenusFactorAt, haz, weierstrassFactor]
        have hlin : (1 : ℂ) - w / z₀ = (w - z₀) * (-(z₀)⁻¹) := by
          field_simp
          ring
        rw [hlin]
        ring
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_mul_distrib, Finset.prod_const, hUdef, ← Complex.exp_sum]
    have htailval : (∏' n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ}, weierstrassGenusFactorAt b (n : ℕ) w)
        = weierstrassGenusProduct b w / ∏ n ∈ S, weierstrassGenusFactorAt b n w := by
      rw [hsb]
      field_simp
    rw [hsa, htail, hprodA, htailval, hGdef]
    simp only [smul_eq_mul]
    ring
  rw [hcard]
  exact (hPana.analyticOrderAt_eq_natCast).2 ⟨G, hGana, hG0, hkey⟩

end

end GaloisForLFunctions
