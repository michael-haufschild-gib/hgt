import GaloisForLFunctions.HTGeometry.PolynomialHeatFlow
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer

/-!
# The heat flow does not increase the number of nonreal roots of a real polynomial

For a real polynomial `p ≠ 0` let `Z_c(p) = deg p − #(real roots)` be its number of nonreal roots,
with multiplicity.  Every heat step `1 − aD²`, `a > 0`, keeps the degree and does not increase
`Z_c` (`nonrealCount_heatStep_le`).  The heat flow `e^{−τD²}p` is the locally uniform limit on `ℂ`
of `n` heat steps of size `τ/n` (`tendstoLocallyUniformly_eval_heatStepOp_pow`).  By Hurwitz's
theorem every nonreal root of the limit attracts as many nonreal roots of the approximants, in
small discs off the real axis.  Hence `Z_c(e^{−τD²}p) ≤ Z_c(p)` for `τ > 0`
(`nonrealRootCount_polyHeat_le`).
-/

open Polynomial Finset Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The number of nonreal roots of a real polynomial, with multiplicity. -/
def nonrealRootCount (A : ℝ[X]) : ℕ := A.natDegree - Multiset.card A.roots

theorem natDegree_heatStepOp (a : ℝ) (p : ℝ[X]) : (heatStepOp a p).natDegree = p.natDegree := by
  rw [heatStepOp_apply]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [derivative_of_natDegree_zero h0]; simp
  · refine natDegree_sub_eq_left_of_natDegree_lt ((natDegree_C_mul_le a _).trans_lt ?_)
    have h1 := natDegree_derivative_le p
    have h2 := natDegree_derivative_le (derivative p)
    omega

theorem heatStepOp_pow_succ_apply (a : ℝ) (n : ℕ) (p : ℝ[X]) :
    (heatStepOp a ^ (n + 1)) p = heatStepOp a ((heatStepOp a ^ n) p) := by
  rw [pow_succ', Module.End.mul_apply]

theorem heatStepOp_ne_zero (a : ℝ) {q : ℝ[X]} (hq : q ≠ 0) : heatStepOp a q ≠ 0 := by
  intro h0
  have hdeg := natDegree_heatStepOp a q
  rw [h0, natDegree_zero] at hdeg
  rw [heatStepOp_apply, derivative_of_natDegree_zero (by
    have := natDegree_derivative_le q; omega), mul_zero, sub_zero] at h0
  exact hq h0

theorem heatStepOp_pow_ne_zero (a : ℝ) (n : ℕ) {p : ℝ[X]} (hp : p ≠ 0) :
    (heatStepOp a ^ n) p ≠ 0 := by
  induction n with
  | zero => simpa using hp
  | succ n ih => rw [heatStepOp_pow_succ_apply]; exact heatStepOp_ne_zero a ih

theorem nonrealRootCount_heatStepOp_pow_le {a : ℝ} (ha : 0 < a) (n : ℕ) (p : ℝ[X]) :
    nonrealRootCount ((heatStepOp a ^ n) p) ≤ nonrealRootCount p ∧
      ((heatStepOp a ^ n) p).natDegree = p.natDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [heatStepOp_pow_succ_apply]
    refine ⟨?_, by rw [natDegree_heatStepOp, ih.2]⟩
    refine le_trans ?_ ih.1
    unfold nonrealRootCount
    rw [heatStepOp_apply]
    exact nonrealCount_heatStep_le _ ha

/-! ## Nonreal roots through complex discs -/

theorem analyticOrderAt_eval_eq_rootMultiplicity {B : ℂ[X]} (hB : B ≠ 0) (z : ℂ) :
    analyticOrderAt (fun y : ℂ => B.eval y) z = (B.rootMultiplicity z : ℕ∞) := by
  have hBan : AnalyticAt ℂ (fun y : ℂ => B.eval y) z := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial B
  rw [hBan.analyticOrderAt_eq_natCast]
  obtain ⟨s, hps, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd B hB z
  have hs_ne : s.eval z ≠ 0 := fun hs => hnd ((Polynomial.dvd_iff_isRoot).mpr hs)
  refine ⟨fun y : ℂ => s.eval y, ?_, hs_ne, Filter.Eventually.of_forall fun y => ?_⟩
  · simpa using (analyticAt_id : AnalyticAt ℂ (fun y : ℂ => y) z).aeval_polynomial s
  · have h := congrArg (fun Q : Polynomial ℂ => Q.eval y) hps
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, smul_eq_mul] using h

theorem zeroMult_eval_eq_rootMultiplicity {B : ℂ[X]} (hB : B ≠ 0) (z : ℂ) :
    zeroMult (fun y : ℂ => B.eval y) z = B.rootMultiplicity z := by
  rw [zeroMult, analyticOrderAt_eval_eq_rootMultiplicity hB, ENat.toNat_coe]

theorem nonrealRootCount_eq (A : ℝ[X]) :
    nonrealRootCount A =
      Multiset.card ((A.map Complex.ofRealHom).roots.filter (fun z => z.im ≠ 0)) := by
  have h1 := Multiset.filter_add_not (fun z : ℂ => z.im = 0) (A.map Complex.ofRealHom).roots
  have hcard := congrArg Multiset.card h1
  rw [Multiset.card_add] at hcard
  have h2 : Multiset.card ((A.map Complex.ofRealHom).roots.filter (fun z => z.im = 0)) =
      Multiset.card A.roots := by
    have := congrArg Multiset.card (realPolynomialRealRootMultiset_eq_map_roots A)
    rw [Multiset.card_map] at this
    exact this
  have h3 : Multiset.card (A.map Complex.ofRealHom).roots = A.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree,
      natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  unfold nonrealRootCount
  simp only [ne_eq] at hcard ⊢
  omega

theorem card_filter_roots_eq_sum (B : ℂ[X]) :
    Multiset.card (B.roots.filter (fun z => z.im ≠ 0)) =
      ∑ z ∈ (B.roots.filter (fun z => z.im ≠ 0)).toFinset, B.rootMultiplicity z := by
  classical
  rw [← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun z hz => ?_
  have h := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)).2
  simp [h, count_roots]

/-- **Disc counts bound the nonreal root count.** -/
theorem sum_le_card_nonreal_roots {B : ℂ[X]} (hB : B ≠ 0) {E : Finset ℂ} {r : ℂ → ℝ}
    {n : ℂ → ℕ} (hr : ∀ e ∈ E, 0 < r e) (havoid : ∀ e ∈ E, ∀ w ∈ ball e (r e), w.im ≠ 0)
    (hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')))
    (hsph : ∀ e ∈ E, ∀ w ∈ sphere e (r e), B.eval w ≠ 0)
    (hn : ∀ e ∈ E, zeroSumBall (fun y => B.eval y) e (r e) = (n e : ℂ)) :
    ∑ e ∈ E, n e ≤ Multiset.card (B.roots.filter (fun z => z.im ≠ 0)) := by
  classical
  have hdiff : Differentiable ℂ (fun y : ℂ => B.eval y) := B.differentiable
  have hZ : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
      (∀ z ∈ ball e (r e), B.eval z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (fun y => B.eval y) e (r e) =
        ∑ ρ ∈ Z, (zeroMult (fun y : ℂ => B.eval y) ρ : ℂ) :=
    fun e he => exists_zeroSet_zeroSumBall (hr e he) (by linarith [hr e he] : r e < 2 * r e)
      isOpen_univ (Set.subset_univ _) hdiff.differentiableOn (hsph e he)
  choose! Z hZball hZzero hZsum using hZ
  set T := (B.roots.filter (fun z => z.im ≠ 0)).toFinset
  have hZT : ∀ e ∈ E, Z e ⊆ T := by
    intro e he z hz
    have hb := hZball e he z hz
    rw [Multiset.mem_toFinset, Multiset.mem_filter, mem_roots hB]
    exact ⟨(hZzero e he z hb).mpr hz, havoid e he z hb⟩
  have hpd : (E : Set ℂ).PairwiseDisjoint Z := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hZball e he z hz) (hZball e' he' z hz')
  have hnZ : ∀ e ∈ E, ∑ ρ ∈ Z e, B.roots.count ρ = n e := by
    intro e he
    have h := hZsum e he
    rw [hn e he] at h
    have h' : ((∑ ρ ∈ Z e, zeroMult (fun y : ℂ => B.eval y) ρ : ℕ) : ℂ) = (n e : ℂ) := by
      push_cast; exact h.symm
    have h'' : ∑ ρ ∈ Z e, zeroMult (fun y : ℂ => B.eval y) ρ = n e := by exact_mod_cast h'
    rw [← h'']
    exact Finset.sum_congr rfl fun ρ _ => by
      rw [count_roots, zeroMult_eval_eq_rootMultiplicity hB]
  have hcardT : Multiset.card (B.roots.filter (fun z => z.im ≠ 0)) =
      ∑ z ∈ T, B.roots.count z := by
    rw [← Multiset.toFinset_sum_count_eq]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Multiset.count_filter_of_pos]
    exact (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)).2
  rw [hcardT]
  calc ∑ e ∈ E, n e = ∑ z ∈ E.biUnion Z, B.roots.count z := by
        rw [Finset.sum_biUnion hpd]
        exact Finset.sum_congr rfl fun e he => (hnZ e he).symm
    _ ≤ ∑ z ∈ T, B.roots.count z :=
        Finset.sum_le_sum_of_subset (Finset.biUnion_subset.mpr hZT)

/-- Discs isolating the nonreal roots of a nonzero complex polynomial. -/
theorem exists_isolating_discs {B : ℂ[X]} (hB : B ≠ 0) :
    ∃ r : ℂ → ℝ, ∀ e ∈ (B.roots.filter (fun z => z.im ≠ 0)).toFinset,
      0 < r e ∧ (∀ w ∈ ball e (r e), w.im ≠ 0) ∧
      (∀ e' ∈ (B.roots.filter (fun z => z.im ≠ 0)).toFinset, e ≠ e' →
        Disjoint (ball e (r e)) (ball e' (r e'))) ∧
      (∀ w ∈ sphere e (r e), B.eval w ≠ 0) ∧
      zeroSumBall (fun y => B.eval y) e (r e) = (B.rootMultiplicity e : ℂ) := by
  classical
  set R := B.roots.toFinset
  obtain ⟨d, hd, hsep⟩ : ∃ d > 0, ∀ e ∈ R, ∀ e' ∈ R, e ≠ e' → d ≤ dist e e' := by
    rcases (R.offDiag).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun e he₁ e' he' hne => ?_⟩
      have : (e, e') ∈ R.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne⟩
      rw [he] at this; simp at this
    · refine ⟨R.offDiag.inf' hne (fun pr => dist pr.1 pr.2), ?_, fun e he₁ e' he' hne' => ?_⟩
      · refine (Finset.lt_inf'_iff hne).mpr fun pr hpr => ?_
        obtain ⟨-, -, hpr⟩ := Finset.mem_offDiag.mp hpr
        exact dist_pos.mpr hpr
      · have hmem : (e, e') ∈ R.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne'⟩
        exact Finset.inf'_le (fun pr : ℂ × ℂ => dist pr.1 pr.2) hmem
  refine ⟨fun e => min (|e.im| / 2) (d / 3), fun e he => ?_⟩
  have heR : e ∈ R := by
    rw [Multiset.mem_toFinset] at he ⊢
    exact (Multiset.mem_filter.mp he).1
  have him : e.im ≠ 0 := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp he)).2
  have hr : 0 < min (|e.im| / 2) (d / 3) := lt_min (by have := abs_pos.mpr him; linarith) (by linarith)
  have hroot : ∀ w, B.eval w = 0 → w ∈ R := fun w hw =>
    Multiset.mem_toFinset.mpr ((mem_roots hB).mpr hw)
  -- the only root in the closed disc is `e`
  have honly : ∀ w, dist w e ≤ min (|e.im| / 2) (d / 3) → B.eval w = 0 → w = e := by
    intro w hw hw0
    by_contra hne
    have := hsep w (hroot w hw0) e heR hne
    have h3 : min (|e.im| / 2) (d / 3) ≤ d / 3 := min_le_right _ _
    linarith
  refine ⟨hr, fun w hw hw0 => ?_, fun e' he' hne => ?_, fun w hw hw0 => ?_, ?_⟩
  · have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have := min_le_left (|e.im| / 2) (d / 3)
    have hpos := abs_pos.mpr him
    linarith
  · have he'R : e' ∈ R := by
      rw [Multiset.mem_toFinset] at he' ⊢
      exact (Multiset.mem_filter.mp he').1
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hsep e heR e' he'R hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have := min_le_right (|e.im| / 2) (d / 3)
    have := min_le_right (|e'.im| / 2) (d / 3)
    linarith
  · have hwe := honly w (le_of_eq (mem_sphere.mp hw)) hw0
    rw [hwe, mem_sphere, dist_self] at hw
    linarith
  · obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hr
      (by linarith : min (|e.im| / 2) (d / 3) < 2 * min (|e.im| / 2) (d / 3))
      isOpen_univ (Set.subset_univ _) B.differentiable.differentiableOn (fun w hw hw0 => by
        have hwe := honly w (le_of_eq (mem_sphere.mp hw)) hw0
        rw [hwe, mem_sphere, dist_self] at hw
        linarith)
    have he0 : B.eval e = 0 := (mem_roots hB).mp (Multiset.mem_toFinset.mp heR)
    have hZ : Z = {e} := by
      ext w
      rw [Finset.mem_singleton]
      constructor
      · intro hw
        exact honly w (le_of_lt (mem_ball.mp (hZb w hw))) ((hZz w (hZb w hw)).mpr hw)
      · rintro rfl
        exact (hZz w (mem_ball_self hr)).mp he0
    rw [hZs, hZ, Finset.sum_singleton, zeroMult_eval_eq_rootMultiplicity hB]

/-- Locally uniform convergence keeps a zero-free circle zero-free. -/
theorem eventually_ne_zero_on_sphere {α : Type*} {p : Filter α} {F : α → ℂ → ℂ} {f : ℂ → ℂ}
    (hf : Continuous f) (hconv : TendstoLocallyUniformly F f p) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hsph : ∀ w ∈ sphere c r, f w ≠ 0) : ∀ᶠ n in p, ∀ w ∈ sphere c r, F n w ≠ 0 := by
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere c r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr) hf.norm.continuousOn
  have hμ : 0 < ‖f w₀‖ := norm_pos_iff.mpr (hsph w₀ hw₀)
  have hunif := (Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ (isCompact_sphere c r))) _ hμ
  filter_upwards [hunif] with n hn w hw h0
  have h1 := hn w hw
  rw [dist_eq_norm, h0, sub_zero] at h1
  exact (not_lt.mpr (hmin hw)) h1

/-! ## The theorem -/

theorem polyHeat_eq_add (τ : ℝ) (p : ℝ[X]) :
    polyHeat τ p = p + ∑ k ∈ range p.natDegree,
      C ((-τ) ^ (k + 1) / ((k + 1).factorial : ℝ)) * derivative^[2 * (k + 1)] p := by
  rw [polyHeat, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, C_1, one_mul, mul_zero,
    Function.iterate_zero, id_eq]
  ring

theorem natDegree_polyHeat (τ : ℝ) {p : ℝ[X]} (hp : p ≠ 0) :
    (polyHeat τ p).natDegree = p.natDegree ∧ polyHeat τ p ≠ 0 := by
  rw [polyHeat_eq_add]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0, Finset.range_zero, Finset.sum_empty, add_zero]
    exact ⟨h0, hp⟩
  · have hlt : (∑ k ∈ range p.natDegree,
        C ((-τ) ^ (k + 1) / ((k + 1).factorial : ℝ)) * derivative^[2 * (k + 1)] p).natDegree <
          p.natDegree := by
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p.natDegree - 1)
        fun k _ => ?_) (by omega)
      refine (natDegree_C_mul_le _ _).trans ?_
      have := natDegree_iterate_derivative p (2 * (k + 1))
      omega
    have hdeg := natDegree_add_eq_left_of_natDegree_lt hlt
    refine ⟨hdeg, fun h0 => ?_⟩
    rw [h0, natDegree_zero] at hdeg
    omega

/-- **The heat flow does not increase the number of nonreal roots.** For `τ > 0` and `p ≠ 0`,
`Z_c(e^{−τD²}p) ≤ Z_c(p)`. -/
theorem nonrealRootCount_polyHeat_le {τ : ℝ} (hτ : 0 < τ) {p : ℝ[X]} (hp : p ≠ 0) :
    nonrealRootCount (polyHeat τ p) ≤ nonrealRootCount p := by
  classical
  obtain ⟨-, hL⟩ := natDegree_polyHeat τ hp
  set L := polyHeat τ p
  set B := L.map Complex.ofRealHom
  have hB : B ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hL
  obtain ⟨r, hr⟩ := exists_isolating_discs hB
  set T := (B.roots.filter (fun z => z.im ≠ 0)).toFinset
  set F : ℕ → ℂ → ℂ := fun n z => (((heatStepOp (τ / n) ^ n) p).map Complex.ofRealHom).eval z
  have hconv : TendstoLocallyUniformly F (fun z => B.eval z) atTop :=
    tendstoLocallyUniformly_eval_heatStepOp_pow τ p
  have hFd : ∀ n, Differentiable ℂ (F n) := fun n => Polynomial.differentiable _
  have hev : ∀ e ∈ T, ∀ᶠ n in atTop,
      zeroSumBall (F n) e (r e) = (B.rootMultiplicity e : ℂ) ∧
        ∀ w ∈ sphere e (r e), F n w ≠ 0 := by
    intro e he
    obtain ⟨hr0, -, -, hsph, hcount⟩ := hr e he
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hFd B.differentiable hconv hr0
      (by linarith : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere B.continuous hconv hr0.le hsph
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rw [hn1, hcount], hn2⟩
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset T).mpr hev).and (eventually_ge_atTop 1)
    |>.exists
  obtain ⟨hnT, hn1⟩ := hn
  set A := (heatStepOp (τ / n) ^ n) p
  have ha : 0 < τ / n := div_pos hτ (by exact_mod_cast hn1)
  have hAle := (nonrealRootCount_heatStepOp_pow_le ha n p).1
  have hA : A ≠ 0 := heatStepOp_pow_ne_zero _ n hp
  have hBA : A.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hA
  have hsum := sum_le_card_nonreal_roots hBA (E := T) (r := r)
    (n := fun e => B.rootMultiplicity e)
    (fun e he => (hr e he).1) (fun e he => (hr e he).2.1) (fun e he => (hr e he).2.2.1)
    (fun e he => (hnT e he).2) (fun e he => (hnT e he).1)
  rw [nonrealRootCount_eq L, card_filter_roots_eq_sum]
  rw [← nonrealRootCount_eq A] at hsum
  exact hsum.trans hAle

end

end GaloisForLFunctions.HTGeometry
