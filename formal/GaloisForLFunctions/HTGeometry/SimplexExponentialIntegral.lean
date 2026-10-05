import GaloisForLFunctions.HTGeometry.HypoexponentialListLaw

/-!
# Exponential integrals over the finite-horizon simplex

For rates `c_1, …, c_n > 0` the integral of `exp(-Σ_k c_k u_k)` over the simplex
`{u ∈ ℝⁿ : u ≥ 0, Σ_k u_k ≤ t}` equals `(Π_k c_k)⁻¹` times the distribution function at `t` of the
independent sum `X_{c_1} + ⋯ + X_{c_n}`.  Splitting off the first coordinate (Fubini) gives the
recursion `Σ_c(t) = ∫₀ᵗ e^{-c_1 x} Σ_{c'}(t - x) dx`, which is the causal recursion of the
hypoexponential distribution function up to the factor `c_1`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- The finite-horizon simplex `{u ≥ 0, Σ_k u_k ≤ t}`. -/
def simplexSet (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ t}

theorem isClosed_simplexSet (n : ℕ) (t : ℝ) : IsClosed (simplexSet n t) := by
  have h1 : IsClosed {u : Fin n → ℝ | ∀ i, 0 ≤ u i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h1.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const)

theorem simplexSet_subset_Icc (n : ℕ) (t : ℝ) : simplexSet n t ⊆ Icc 0 fun _ => t := by
  intro u hu
  refine ⟨fun i => hu.1 i, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans hu.2

theorem isCompact_simplexSet (n : ℕ) (t : ℝ) : IsCompact (simplexSet n t) :=
  isCompact_Icc.of_isClosed_subset (isClosed_simplexSet n t) (simplexSet_subset_Icc n t)

theorem simplexSet_eq_empty {n : ℕ} {t : ℝ} (ht : t < 0) : simplexSet n t = ∅ := by
  ext u
  simp only [simplexSet, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact ht.trans_le (Finset.sum_nonneg fun i _ => h i)

/-- The simplex exponential integral `∫_{u ≥ 0, Σu ≤ t} exp(-Σ_k c_k u_k) du`. -/
def simplexExp {n : ℕ} (c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ u in simplexSet n t, Real.exp (-∑ k, c k * u k)

theorem simplexExp_of_neg {n : ℕ} (c : Fin n → ℝ) {t : ℝ} (ht : t < 0) : simplexExp c t = 0 := by
  rw [simplexExp, simplexSet_eq_empty ht, Measure.restrict_empty, integral_zero_measure]

theorem simplexExp_zero (c : Fin 0 → ℝ) {t : ℝ} (ht : 0 ≤ t) : simplexExp c t = 1 := by
  have hset : simplexSet 0 t = univ := by
    ext u
    simp [simplexSet, ht]
  rw [simplexExp, hset, Measure.restrict_univ, volume_pi, Measure.pi_of_empty, integral_dirac]
  simp

/-- **Fubini recursion**: `Σ_c(t) = ∫_{x ≥ 0} e^{-c_0 x} Σ_{c'}(t - x) dx`. -/
theorem simplexExp_succ {n : ℕ} (c : Fin (n + 1) → ℝ) (t : ℝ) :
    simplexExp c t =
      ∫ x in Ici (0 : ℝ), Real.exp (-(c 0 * x)) * simplexExp (fun j => c j.succ) (t - x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hepres := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let T : Set (ℝ × (Fin n → ℝ)) := {p | (0 ≤ p.1 ∧ ∀ j, 0 ≤ p.2 j) ∧ p.1 + ∑ j, p.2 j ≤ t}
  let F : ℝ × (Fin n → ℝ) → ℝ := fun p => Real.exp (-(c 0 * p.1)) *
    Real.exp (-∑ j, c j.succ * p.2 j)
  have hTclosed : IsClosed T := by
    have hT : T = ({p | 0 ≤ p.1} ∩ ⋂ j, {p | 0 ≤ p.2 j}) ∩ {p | p.1 + ∑ j, p.2 j ≤ t} := by
      ext p; simp [T]
    rw [hT]
    refine IsClosed.inter (IsClosed.inter (isClosed_le continuous_const continuous_fst)
      (isClosed_iInter fun j => isClosed_le continuous_const
        ((continuous_apply j).comp continuous_snd)))
      (isClosed_le (continuous_fst.add (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp continuous_snd)) continuous_const)
  have hTsub : T ⊆ Icc (0 : ℝ) t ×ˢ Icc 0 fun _ => t := by
    intro p hp
    have hs : 0 ≤ ∑ j, p.2 j := Finset.sum_nonneg fun j _ => hp.1.2 j
    refine ⟨⟨hp.1.1, by linarith [hp.2]⟩, fun j => hp.1.2 j, fun j => ?_⟩
    have := Finset.single_le_sum (fun k _ => hp.1.2 k) (Finset.mem_univ j)
    linarith [hp.2, hp.1.1]
  have hTcompact : IsCompact T :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hTclosed hTsub
  have hFcont : Continuous F := by fun_prop
  have hint : Integrable (T.indicator F) (volume.prod volume) :=
    (integrable_indicator_iff hTclosed.measurableSet).2
      (hFcont.continuousOn.integrableOn_compact hTcompact)
  have hmem : ∀ x : Fin (n + 1) → ℝ, x ∈ simplexSet (n + 1) t ↔ e x ∈ T := fun x => by
    simp only [simplexSet, mem_setOf_eq, T, e, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv, Fin.forall_fin_succ, Fin.sum_univ_succ]
    rfl
  have hval : ∀ x : Fin (n + 1) → ℝ, Real.exp (-∑ k, c k * x k) = F (e x) := fun x => by
    simp only [F, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv,
      Fin.sum_univ_succ, neg_add, Real.exp_add]
    rfl
  rw [simplexExp, ← integral_indicator (isClosed_simplexSet _ _).measurableSet]
  have h1 : ∫ x, (simplexSet (n + 1) t).indicator (fun u => Real.exp (-∑ k, c k * u k)) x =
      ∫ x, T.indicator F (e x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ simplexSet (n + 1) t
    · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx), hval]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
  rw [h1, hepres.integral_comp' (T.indicator F), Measure.volume_eq_prod,
    integral_prod _ hint, ← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), simplexExp,
      ← integral_indicator (isClosed_simplexSet _ _).measurableSet, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    beta_reduce
    by_cases hy : y ∈ simplexSet n (t - x)
    · have hT : (x, y) ∈ T := ⟨⟨hx, hy.1⟩, by linarith [hy.2]⟩
      rw [indicator_of_mem hT, indicator_of_mem hy]
    · have hT : (x, y) ∉ T := fun h => hy ⟨h.1.2, by linarith [h.2]⟩
      rw [indicator_of_notMem hT, indicator_of_notMem hy, mul_zero]
  · rw [indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    have hT : (x, y) ∉ T := fun h => hx h.1.1
    beta_reduce
    rw [indicator_of_notMem hT]
    rfl

/-- **The simplex exponential integral is a scaled hypoexponential distribution function**:
`Σ_c(t) = (Π_k c_k)⁻¹ P(X_{c_1} + ⋯ + X_{c_n} ≤ t)`. -/
theorem simplexExp_eq_hypoCDF :
    ∀ {n : ℕ} (c : Fin n → ℝ), (∀ k, 0 < c k) → ∀ {t : ℝ}, 0 ≤ t →
      simplexExp c t = (∏ k, c k)⁻¹ * hypoCDFList (List.ofFn c) t
  | 0, c, _, t, ht => by simp [simplexExp_zero c ht, hypoCDFList]
  | n + 1, c, hc, t, ht => by
    have ih := fun {s : ℝ} (hs : 0 ≤ s) =>
      simplexExp_eq_hypoCDF (fun j : Fin n => c j.succ) (fun j => hc j.succ) hs
    have hcont : Continuous fun x => Real.exp (-(c 0 * x)) *
        ((∏ j : Fin n, c j.succ)⁻¹ * hypoCDFList (List.ofFn fun j : Fin n => c j.succ) (t - x)) :=
      (by fun_prop : Continuous fun x => Real.exp (-(c 0 * x))).mul
        (continuous_const.mul ((continuous_hypoCDFList _).comp (continuous_sub_left t)))
    rw [simplexExp_succ, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      Icc_subset_Ici_self fun x hx => ?_, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht]
    · rw [intervalIntegral.integral_congr (g := fun x => Real.exp (-(c 0 * x)) *
          ((∏ j : Fin n, c j.succ)⁻¹ * hypoCDFList (List.ofFn fun j : Fin n => c j.succ) (t - x)))
          fun x hx => by
            rw [uIcc_of_le ht] at hx
            rw [ih (by linarith [hx.2])]]
      rw [List.ofFn_succ, hypoCDFList, expKernelConv, Fin.prod_univ_succ]
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun s => c 0 * Real.exp (-(c 0 * (t - s))) *
          hypoCDFList (List.ofFn fun j : Fin n => c j.succ) s) t (a := 0) (b := t)
      simp only [sub_sub_cancel, sub_self, sub_zero] at hsub
      rw [← hsub, mul_inv, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      have hc0 : c 0 ≠ 0 := (hc 0).ne'
      field_simp
    · obtain ⟨hx0, hxt⟩ := hx
      have hxt' : t < x := lt_of_not_ge fun h => hxt ⟨hx0, h⟩
      rw [simplexExp_of_neg _ (by linarith), mul_zero]

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
