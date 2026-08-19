import GaloisForLFunctions.HTGeometry.PrescribedDivisorRealization

/-!
# The exact order of a Weierstrass product

The canonical product with increasing genus vanishes at a point to the order given by the
multiplicity of that point in the zero sequence.  The proof splits the product at the finitely many
indices hitting the point, and identifies the remaining tail with the same tail of an auxiliary
sequence that has been moved away from the point — so the tail is analytic and nonvanishing there
without repeating the convergence argument.
-/

namespace GaloisForLFunctions

open Complex Filter Topology Set

noncomputable section

/-- The multiplicity with which a point occurs in a zero sequence. -/
def zeroMultiplicity (a : ℕ → ℂ) (z : ℂ) : ℕ := {n : ℕ | a n = z}.ncard

theorem finite_zeroIndices {a : ℕ → ℂ} (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (z : ℂ) :
    {n : ℕ | a n = z}.Finite := by
  refine (finite_setOf_norm_lt ha (‖z‖ + 1)).subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn ⊢
  rw [hn]
  linarith

/-- Multipliability of a subfamily of the Weierstrass factors. -/
theorem multipliable_weierstrassGenusFactorAt_subtype {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (p : ℕ → Prop) (w : ℂ) :
    Multipliable fun n : {n : ℕ // p n} => weierstrassGenusFactorAt a (n : ℕ) w := by
  have hsum : Summable fun n : {n : ℕ // p n} =>
      ‖weierstrassGenusFactorAt a (n : ℕ) w - 1‖ :=
    (summable_norm_weierstrassGenusFactorAt_sub_one ha hane w).subtype p
  have hmul := multipliable_one_add_of_summable
    (f := fun n : {n : ℕ // p n} => weierstrassGenusFactorAt a (n : ℕ) w - 1) hsum
  exact hmul.congr fun n => by ring

/-- A multipliable family splits at any finite set of indices. -/
theorem tprod_eq_prod_mul_tprod_compl {f : ℕ → ℂ} (hall : Multipliable f) (S : Finset ℕ)
    (hsub : Multipliable fun n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ} => f (n : ℕ)) :
    ∏' n, f n = (∏ n ∈ S, f n) * ∏' n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ}, f (n : ℕ) := by
  have hfin : HasProd (fun n : {n : ℕ // n ∈ (↑S : Set ℕ)} => f (n : ℕ)) (∏ n ∈ S, f n) := by
    have hft := hasProd_fintype (fun n : {n : ℕ // n ∈ (↑S : Set ℕ)} => f (n : ℕ))
    have hval : (∏ n : {n : ℕ // n ∈ (↑S : Set ℕ)}, f (n : ℕ)) = ∏ n ∈ S, f n :=
      Finset.prod_coe_sort S f
    rwa [hval] at hft
  exact hall.hasProd.unique (HasProd.mul_compl hfin hsub.hasProd)

/-- **Splitting the Weierstrass product at a finite set of indices.** -/
theorem weierstrassGenusProduct_split {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (S : Finset ℕ) (w : ℂ) :
    weierstrassGenusProduct a w
      = (∏ n ∈ S, weierstrassGenusFactorAt a n w)
        * ∏' n : {n : ℕ // n ∈ (↑S : Set ℕ)ᶜ}, weierstrassGenusFactorAt a (n : ℕ) w :=
  tprod_eq_prod_mul_tprod_compl (f := fun n => weierstrassGenusFactorAt a n w)
    (multipliable_weierstrassGenusFactorAt ha hane w) S
    (multipliable_weierstrassGenusFactorAt_subtype ha hane (fun n => n ∈ (↑S : Set ℕ)ᶜ) w)

/-- The auxiliary sequence: the indices hitting `z₀` are moved out to the far positive axis. -/
def awaySeq (a : ℕ → ℂ) (S : Finset ℕ) (z₀ : ℂ) : ℕ → ℂ :=
  fun n => if n ∈ S then (((n : ℝ) + ‖z₀‖ + 1 : ℝ) : ℂ) else a n

theorem awaySeq_of_notMem {a : ℕ → ℂ} {S : Finset ℕ} {z₀ : ℂ} {n : ℕ} (hn : n ∉ S) :
    awaySeq a S z₀ n = a n := by
  rw [awaySeq, if_neg hn]

theorem norm_awaySeq_of_mem {a : ℕ → ℂ} {S : Finset ℕ} {z₀ : ℂ} {n : ℕ} (hn : n ∈ S) :
    ‖awaySeq a S z₀ n‖ = (n : ℝ) + ‖z₀‖ + 1 := by
  rw [awaySeq, if_pos hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

theorem awaySeq_ne_zero {a : ℕ → ℂ} (hane : ∀ n, a n ≠ 0) (S : Finset ℕ) (z₀ : ℂ) (n : ℕ) :
    awaySeq a S z₀ n ≠ 0 := by
  by_cases hn : n ∈ S
  · intro h
    have := norm_awaySeq_of_mem (a := a) (S := S) (z₀ := z₀) hn
    rw [h, norm_zero] at this
    have hz : (0:ℝ) ≤ ‖z₀‖ := norm_nonneg _
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · rw [awaySeq_of_notMem hn]
    exact hane n

theorem awaySeq_ne {a : ℕ → ℂ} {S : Finset ℕ} {z₀ : ℂ}
    (hout : ∀ n ∉ S, a n ≠ z₀) (n : ℕ) : awaySeq a S z₀ n ≠ z₀ := by
  by_cases hn : n ∈ S
  · intro h
    have hnorm := norm_awaySeq_of_mem (a := a) (S := S) (z₀ := z₀) hn
    rw [h] at hnorm
    have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · rw [awaySeq_of_notMem hn]
    exact hout n hn

theorem tendsto_norm_awaySeq {a : ℕ → ℂ} (ha : Tendsto (fun n => ‖a n‖) atTop atTop)
    (S : Finset ℕ) (z₀ : ℂ) : Tendsto (fun n => ‖awaySeq a S z₀ n‖) atTop atTop := by
  refine ha.congr' ?_
  have hfin : ∀ᶠ n in atTop, n ∉ S := by
    filter_upwards [eventually_gt_atTop (S.sup id)] with n hn
    intro hmem
    have : n ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  filter_upwards [hfin] with n hn
  rw [awaySeq_of_notMem hn]

set_option maxHeartbeats 2000000 in
/-- **The exact order of the Weierstrass product.**  The canonical product vanishes at a point to
the order given by the multiplicity of that point in the zero sequence. -/
theorem analyticOrderAt_weierstrassGenusProduct {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0) (z₀ : ℂ) :
    analyticOrderAt (weierstrassGenusProduct a) z₀ = (zeroMultiplicity a z₀ : ℕ) := by
  classical
  have hfin := finite_zeroIndices ha z₀
  set S : Finset ℕ := hfin.toFinset with hSdef
  have hmemS : ∀ n : ℕ, n ∈ S ↔ a n = z₀ := fun n => by
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcard : zeroMultiplicity a z₀ = S.card := by
    rw [zeroMultiplicity, hSdef, Set.ncard_eq_toFinset_card _ hfin]
  have hPana : AnalyticAt ℂ (weierstrassGenusProduct a) z₀ :=
    (differentiable_weierstrassGenusProduct ha hane).analyticAt z₀
  rcases eq_or_ne z₀ 0 with rfl | hz₀
  · have hSempty : S = ∅ := Finset.eq_empty_of_forall_notMem fun n hn => hane n ((hmemS n).1 hn)
    have h0 : weierstrassGenusProduct a 0 ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff ha hane 0).1 h
      exact hane n hn.symm
    rw [hcard, hSempty, Finset.card_empty, Nat.cast_zero]
    exact analyticOrderAt_eq_zero.2 (Or.inr h0)
  · set b : ℕ → ℂ := awaySeq a S z₀ with hbdef
    have hbne : ∀ n, b n ≠ 0 := awaySeq_ne_zero hane S z₀
    have hout : ∀ n, n ∉ S → a n ≠ z₀ := fun n hn h => hn ((hmemS n).2 h)
    have hbz : ∀ n, b n ≠ z₀ := awaySeq_ne hout
    have hbtend : Tendsto (fun n => ‖b n‖) atTop atTop := tendsto_norm_awaySeq ha S z₀
    have hbP : Differentiable ℂ (weierstrassGenusProduct b) :=
      differentiable_weierstrassGenusProduct hbtend hbne
    have hPb0 : weierstrassGenusProduct b z₀ ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := (weierstrassGenusProduct_eq_zero_iff hbtend hbne z₀).1 h
      exact hbz n hn.symm
    have hDb : Differentiable ℂ (fun w => ∏ n ∈ S, weierstrassGenusFactorAt b n w) := by
      have hprod : (fun w : ℂ => ∏ n ∈ S, weierstrassGenusFactorAt b n w)
          = ∏ n ∈ S, weierstrassGenusFactorAt b n := by
        funext w
        rw [Finset.prod_apply]
      rw [hprod]
      exact Differentiable.finsetProd fun n _ => differentiable_weierstrassGenusFactorAt hbne n
    have hDb0 : (∏ n ∈ S, weierstrassGenusFactorAt b n z₀) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun n _ => ?_
      intro h
      exact hbz n ((weierstrassGenusFactorAt_eq_zero_iff hbne n z₀).1 h).symm
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
      have hsa := weierstrassGenusProduct_split ha hane S w
      have hsb := weierstrassGenusProduct_split hbtend hbne S w
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

/-- **The exact divisor of the realized function.**  Its order at every point is the multiplicity
of that point in the zero sequence minus its multiplicity in the pole sequence. -/
theorem meromorphicOrderAt_divisorFunction_eq_multiplicity {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0) (z : ℂ) :
    meromorphicOrderAt (divisorFunction a b) z
      = ((zeroMultiplicity a z : ℤ) : WithTop ℤ) - ((zeroMultiplicity b z : ℤ) : WithTop ℤ) := by
  have hA := (differentiable_weierstrassGenusProduct ha hane).analyticAt z
  have hB := (differentiable_weierstrassGenusProduct hb hbne).analyticAt z
  rw [meromorphicOrderAt_divisorFunction ha hane hb hbne z, hA.meromorphicOrderAt_eq,
    hB.meromorphicOrderAt_eq, analyticOrderAt_weierstrassGenusProduct ha hane z,
    analyticOrderAt_weierstrassGenusProduct hb hbne z]
  rfl

end

end GaloisForLFunctions
