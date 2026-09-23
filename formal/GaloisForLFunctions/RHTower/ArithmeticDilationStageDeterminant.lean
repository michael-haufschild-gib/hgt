import GaloisForLFunctions.RHTower.ArithmeticDilationNegativeMass
import GaloisForLFunctions.RHTower.ArithmeticDilationDeterminantZeros
import GaloisForLFunctions.HTGeometry.ScheffeLemma
import GaloisForLFunctions.HTGeometry.ScheffeCounting
import GaloisForLFunctions.HTGeometry.GreedyCourantFischer

/-!
# Trace-norm continuity of self-adjoint Fredholm determinants

For compact self-adjoint Schatten-1 operators, the signed greedy spectrum has absolute values
equal to the singular values. Trace-norm convergence to a positive operator therefore gives
`ℓ¹` convergence of the full signed spectra: counting-measure Scheffé controls the absolute
values and the negative spectral mass estimate controls their signs.

An explicit Lipschitz estimate for finite products passes to bare infinite products and upgrades
this spectral convergence to uniform convergence of `det(I + zS)` on bounded sets. The final
specialization is the exact nondiagonal arithmetic-dilation determinant limit from the
constrained-prolate card.
-/

open Filter Topology MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem approxNumber_le_abs_sgVal {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (n : ℕ) :
    approxNumber S n ≤ |sgVal S n| := by
  classical
  set e : ℕ → H := sgVec S with he
  set F : H →L[ℂ] H := ∑ m ∈ Finset.range n, (innerSL ℂ (e m)).smulRight (S (e m)) with hF
  have hrank : HasRankLE F n := by
    refine ⟨Submodule.span ℂ (((Finset.range n).image fun m => S (e m) : Finset H) : Set H),
      FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
    · refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
      simp
    · intro x
      rw [hF, sum_apply]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hm)))
  refine (approxNumber_le S n F hrank).trans ?_
  refine opNorm_le_bound _ (abs_nonneg _) fun x => ?_
  set P : H := ∑ m ∈ Finset.range n, (inner ℂ (e m) x) • e m with hP
  have hFx : F x = S P := by
    rw [hF, sum_apply, hP, map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smulRight_apply, innerSL_apply_apply, map_smul]
  have hunit_sq : ∀ m, (inner ℂ (e m) x) * ((‖e m‖ : ℂ)) ^ (2 : ℕ) = inner ℂ (e m) x := by
    intro m
    rcases norm_sgVec_zero_or_one S m with h0 | h1
    · rw [he, h0]
      simp
    · rw [he, h1]
      simp
  have hy_orth : ∀ k < n, inner ℂ (e k) (x - P) = 0 := by
    intro k hk
    rw [inner_sub_right, hP, inner_sum]
    have hsum : ∑ m ∈ Finset.range n, inner ℂ (e k) ((inner ℂ (e m) x) • e m)
        = inner ℂ (e k) x := by
      rw [Finset.sum_eq_single k]
      · rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        exact hunit_sq k
      · intro m hm hmk
        rw [inner_smul_right, he, inner_sgVec_sgVec_of_ne S (Ne.symm hmk), mul_zero]
      · intro hk'
        exact absurd (Finset.mem_range.mpr hk) hk'
    rw [hsum, sub_self]
  have hy_le : ‖x - P‖ ≤ ‖x‖ := by
    have hyP : RCLike.re (inner ℂ (x - P) P) = 0 := by
      rw [hP, inner_sum]
      have hz : ∀ m ∈ Finset.range n, inner ℂ (x - P) ((inner ℂ (e m) x) • e m) = 0 := by
        intro m hm
        rw [inner_smul_right,
          show inner ℂ (x - P) (e m) = (starRingEnd ℂ) (inner ℂ (e m) (x - P)) from
            (inner_conj_symm _ _).symm,
          hy_orth m (Finset.mem_range.mp hm), map_zero, mul_zero]
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      simp
    have hsq := norm_add_sq (𝕜 := ℂ) (x - P) P
    rw [hyP, sub_add_cancel] at hsq
    nlinarith [norm_nonneg (x - P), norm_nonneg x, sq_nonneg ‖P‖]
  calc
    ‖(S - F) x‖ = ‖S (x - P)‖ := by rw [sub_apply, hFx, ← map_sub]
    _ ≤ orthSup S (sgVec S) n * ‖x - P‖ :=
      norm_le_orthSup_mul_norm S (sgVec S) n hy_orth
    _ ≤ orthSup S (sgVec S) n * ‖x‖ :=
      mul_le_mul_of_nonneg_left hy_le (orthSup_nonneg S (sgVec S) n)
    _ = |sgVal S n| * ‖x‖ := by rw [abs_sgVal hcpt hsym n]

theorem abs_sgVal_le_singVal {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (n : ℕ) :
    |sgVal S n| ≤ singVal S n := by
  classical
  rcases eq_or_ne (orthSup S (sgVec S) n) 0 with h0 | hne
  · rw [abs_sgVal hcpt hsym n, h0]
    exact singVal_nonneg S n
  · have hlive : ∀ m, m ≤ n → orthSup S (sgVec S) m ≠ 0 := by
      intro m hm h0'
      apply hne
      have hmono := orthSup_antitone S (sgVec S) hm
      have hn := orthSup_nonneg S (sgVec S) n
      rw [h0'] at hmono
      linarith
    have horth : Orthonormal ℂ (fun i : Fin (n + 1) => sgVec S i) := by
      rw [orthonormal_iff_ite]
      intro i j
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
        have hstep := isSignedStep_sgVec hcpt hsym i
          (hlive i (Nat.lt_succ_iff.mp i.2))
        rw [hstep.1]
        norm_num
      · rw [if_neg hij]
        exact inner_sgVec_sgVec_of_ne S fun h => hij (Fin.val_injective h)
    set V := Submodule.span ℂ (Set.range fun i : Fin (n + 1) => sgVec S i) with hV
    haveI : FiniteDimensional ℂ V :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    have hdim : Module.finrank ℂ V = n + 1 := by
      rw [hV, finrank_span_eq_card horth.linearIndependent]
      simp
    have hbound : ∀ x ∈ V, |sgVal S n| * ‖x‖ ≤ ‖S x‖ := by
      intro x hx
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
      have hSx : S x = ∑ i : Fin (n + 1),
          (c i * (sgVal S i : ℂ)) • sgVec S i := by
        rw [← hc, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, apply_sgVec, smul_smul]
      have hnormx : ‖x‖ ^ (2 : ℕ) = ∑ i : Fin (n + 1), ‖c i‖ ^ (2 : ℕ) := by
        rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← hc,
          horth.inner_sum c c Finset.univ, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
      have hnormS : ‖S x‖ ^ (2 : ℕ) =
          ∑ i : Fin (n + 1), ‖c i‖ ^ (2 : ℕ) * (sgVal S i) ^ (2 : ℕ) := by
        rw [hSx, ← inner_self_eq_norm_sq (𝕜 := ℂ),
          horth.inner_sum (fun i => c i * (sgVal S i : ℂ))
            (fun i => c i * (sgVal S i : ℂ)) Finset.univ, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        norm_num [norm_mul, sq_abs, mul_pow]
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hlowerSq : |sgVal S n| ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) ≤ ‖S x‖ ^ (2 : ℕ) := by
        rw [hnormx, hnormS, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        have hmono : orthSup S (sgVec S) n ≤ orthSup S (sgVec S) i :=
          orthSup_antitone S (sgVec S) (Nat.lt_succ_iff.mp i.2)
        rw [← abs_sgVal hcpt hsym n, ← abs_sgVal hcpt hsym i] at hmono
        have hsq : |sgVal S n| ^ (2 : ℕ) ≤ |sgVal S i| ^ (2 : ℕ) :=
          pow_le_pow_left₀ (abs_nonneg _) hmono 2
        calc
          |sgVal S n| ^ (2 : ℕ) * ‖c i‖ ^ (2 : ℕ)
              ≤ |sgVal S i| ^ (2 : ℕ) * ‖c i‖ ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
          _ = ‖c i‖ ^ (2 : ℕ) * sgVal S i ^ (2 : ℕ) := by rw [sq_abs]; ring
      have hnonneg : 0 ≤ |sgVal S n| * ‖x‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      nlinarith [norm_nonneg (S x)]
    have htrial : |sgVal S n| ≤ orthSup S (svVec (energyOp S)) n := by
      apply le_orthSup_of_trial S (svVec (energyOp S)) n V
      · rw [hdim]
        omega
      · exact hbound
    have hupper : orthSup S (svVec (energyOp S)) n ≤ singVal S n := by
      apply orthSup_le
      intro y hy hyorth
      calc
        ‖S y‖ ≤ singVal S n * ‖y‖ := norm_apply_le_singVal_of_orth S n hyorth
        _ ≤ singVal S n * 1 := mul_le_mul_of_nonneg_left hy (singVal_nonneg S n)
        _ = singVal S n := mul_one _
    exact htrial.trans hupper

theorem abs_sgVal_eq_singVal {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (n : ℕ) :
    |sgVal S n| = singVal S n := by
  apply le_antisymm (abs_sgVal_le_singVal hcpt hsym n)
  rw [← approxNumber_eq_singVal hcpt n]
  exact approxNumber_le_abs_sgVal hcpt hsym n

omit [CompleteSpace H] in
theorem abs_approxNumber_sub_le_norm (S T : H →L[ℂ] H) (n : ℕ) :
    |approxNumber S n - approxNumber T n| ≤ ‖S - T‖ := by
  rw [abs_le]
  constructor
  · have h := approxNumber_add_le (T - S) S 0 n
    rw [zero_add, approxNumber_zero_eq_norm, sub_add_cancel] at h
    rw [norm_sub_rev]
    linarith
  · have h := approxNumber_add_le (S - T) T 0 n
    rw [zero_add, approxNumber_zero_eq_norm, sub_add_cancel] at h
    linarith

omit [CompleteSpace H] in
theorem sgVal_nonneg_of_isPositive {S : H →L[ℂ] H} (hS : S.IsPositive) (n : ℕ) :
    0 ≤ sgVal S n := by
  rw [sgVal]
  have h := hS.2 (sgVec S n)
  rw [ContinuousLinearMap.reApplyInnerSelf_apply] at h
  rw [inner_re_symm] at h
  exact h

theorem summable_abs_sgVal {S : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hsym : S.IsSymmetric) :
    Summable fun n => |sgVal S n| := by
  have hcpt := hS.isCompactOperator one_pos
  exact hS.one_summable.congr fun n => by
    rw [abs_sgVal_eq_singVal hcpt hsym n, ← approxNumber_eq_singVal hcpt n]

theorem tsum_abs_sgVal_eq_traceNorm {S : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hsym : S.IsSymmetric) :
    ∑' n, |sgVal S n| = traceNorm H S := by
  unfold traceNorm
  apply tsum_congr
  intro n
  rw [abs_sgVal_eq_singVal (hS.isCompactOperator one_pos) hsym n,
    ← approxNumber_eq_singVal (hS.isCompactOperator one_pos) n]

theorem abs_traceNorm_sub_le_traceNorm_sub {S T : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    |traceNorm H S - traceNorm H T| ≤ traceNorm H (S - T) := by
  have hD : MemSchattenClass 1 (S - T) := hS.one_sub hT
  have hDrev : MemSchattenClass 1 (T - S) := hT.one_sub hS
  have hScpt := hS.isCompactOperator one_pos
  have hTcpt := hT.isCompactOperator one_pos
  have hDcpt := hD.isCompactOperator one_pos
  have hDrevcpt := hDrev.isCompactOperator one_pos
  have hnorm : traceNorm H (T - S) = traceNorm H (S - T) := by
    rw [show T - S = (-1 : ℂ) • (S - T) by module, traceNorm_smul]
    simp
  rw [abs_le]
  constructor
  · have htri := traceNorm_add_le hDrevcpt hScpt hDrev.one_summable hS.one_summable
    rw [sub_add_cancel, hnorm] at htri
    linarith
  · have htri := traceNorm_add_le hDcpt hTcpt hD.one_summable hT.one_summable
    rw [sub_add_cancel] at htri
    linarith

theorem traceNorm_tendsto_of_traceNorm_sub_tendsto
    {ι : Type*} {l : Filter ι} {S : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hS : ∀ i, MemSchattenClass 1 (S i)) (hT : MemSchattenClass 1 T)
    (hconv : Tendsto (fun i => traceNorm H (S i - T)) l (nhds 0)) :
    Tendsto (fun i => traceNorm H (S i)) l (nhds (traceNorm H T)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun i => dist_nonneg) ?_ hconv
  exact Eventually.of_forall fun i => by
    rw [Real.dist_eq]
    exact abs_traceNorm_sub_le_traceNorm_sub (hS i) hT

theorem tendsto_tsum_abs_sub_of_tendsto_filter
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℕ → ℝ} {g : ℕ → ℝ}
    (hfnn : ∀ᶠ i in l, ∀ n, 0 ≤ f i n)
    (hfi : ∀ᶠ i in l, Summable (f i))
    (hgnn : ∀ n, 0 ≤ g n) (hgi : Summable g)
    (hpoint : ∀ n, Tendsto (fun i => f i n) l (nhds (g n)))
    (hmass : Tendsto (fun i => ∑' n, f i n) l (nhds (∑' n, g n))) :
    Tendsto (fun i => ∑' n, |f i n - g n|) l (nhds 0) := by
  letI : MeasurableSpace ℕ := ⊤
  have hfnn' : ∀ᶠ i in l, 0 ≤ᵐ[Measure.count] f i := by
    filter_upwards [hfnn] with i hi
    exact Filter.Eventually.of_forall hi
  have hfi' : ∀ᶠ i in l, MeasureTheory.Integrable (f i) Measure.count := by
    filter_upwards [hfnn, hfi] with i hnn hsum
    rw [MeasureTheory.integrable_count_iff]
    exact hsum.congr fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn n)]
  have hgnn' : 0 ≤ᵐ[Measure.count] g := Filter.Eventually.of_forall hgnn
  have hgi' : MeasureTheory.Integrable g Measure.count := by
    rw [MeasureTheory.integrable_count_iff]
    exact hgi.congr fun n => by rw [Real.norm_eq_abs, abs_of_nonneg (hgnn n)]
  have hae : ∀ᵐ n ∂Measure.count, Tendsto (fun i => f i n) l (nhds (g n)) :=
    Filter.Eventually.of_forall hpoint
  have hint : Tendsto (fun i => ∫ n, f i n ∂Measure.count) l
      (nhds (∫ n, g n ∂Measure.count)) := by
    have hg : (∫ n, g n ∂Measure.count) = ∑' n, g n := by
      rw [MeasureTheory.integral_countable hgi']
      simp
    rw [hg]
    exact hmass.congr' (hfi'.mono fun i hi => by
      symm
      change (∫ n, f i n ∂Measure.count) = _
      rw [MeasureTheory.integral_countable hi]
      simp)
  have h := GaloisForLFunctions.tendsto_integral_abs_sub_of_tendsto_integral
    (μ := Measure.count) hfnn' hfi' hgnn' hgi' hae hint
  exact h.congr' (hfi'.mono fun i hi => by
    have habs : MeasureTheory.Integrable (fun n => |f i n - g n|) Measure.count :=
      (hi.sub hgi').abs
    rw [MeasureTheory.integral_countable habs]
    simp)

theorem abs_sgVal_l1_tendsto_of_traceNorm_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {S : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hS : ∀ i, MemSchattenClass 1 (S i)) (hT : MemSchattenClass 1 T)
    (hsymS : ∀ i, (S i).IsSymmetric) (hsymT : T.IsSymmetric)
    (hconv : Tendsto (fun i => traceNorm H (S i - T)) l (nhds 0)) :
    Tendsto (fun i => ∑' n, abs (|sgVal (S i) n| - |sgVal T n|)) l (nhds 0) := by
  have hop : Tendsto (fun i => ‖S i - T‖) l (nhds 0) := by
    refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hconv
    exact norm_le_traceNorm ((hS i).one_sub hT).one_summable
  have happ : ∀ n, Tendsto (fun i => approxNumber (S i) n) l
      (nhds (approxNumber T n)) := by
    intro n
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun i => dist_nonneg) ?_ hop
    exact Eventually.of_forall fun i => by
      rw [Real.dist_eq]
      exact abs_approxNumber_sub_le_norm (S i) T n
  have hpoint : ∀ n, Tendsto (fun i => |sgVal (S i) n|) l (nhds |sgVal T n|) := by
    intro n
    have heqS : (fun i => |sgVal (S i) n|) = fun i => approxNumber (S i) n := by
      funext i
      rw [abs_sgVal_eq_singVal ((hS i).isCompactOperator one_pos) (hsymS i) n,
        ← approxNumber_eq_singVal ((hS i).isCompactOperator one_pos) n]
    have heqT : |sgVal T n| = approxNumber T n := by
      rw [abs_sgVal_eq_singVal (hT.isCompactOperator one_pos) hsymT n,
        ← approxNumber_eq_singVal (hT.isCompactOperator one_pos) n]
    rw [heqS, heqT]
    exact happ n
  have hmass : Tendsto (fun i => ∑' n, |sgVal (S i) n|) l
      (nhds (∑' n, |sgVal T n|)) := by
    have ht := traceNorm_tendsto_of_traceNorm_sub_tendsto hS hT hconv
    rw [show (fun i => ∑' n, |sgVal (S i) n|) =
        fun i => traceNorm H (S i) by
      funext i
      exact tsum_abs_sgVal_eq_traceNorm (hS i) (hsymS i),
      tsum_abs_sgVal_eq_traceNorm hT hsymT]
    exact ht
  exact tendsto_tsum_abs_sub_of_tendsto_filter
    (Eventually.of_forall fun _ _ => abs_nonneg _)
    (Eventually.of_forall fun i => summable_abs_sgVal (hS i) (hsymS i))
    (fun _ => abs_nonneg _) (summable_abs_sgVal hT hsymT) hpoint hmass

omit [CompleteSpace H] in
theorem abs_sub_le_abs_abs_sub_add_two_negPart (a b : ℝ) (hb : 0 ≤ b) :
    |a - b| ≤ abs (|a| - |b|) + 2 * a⁻ := by
  rw [abs_of_nonneg hb]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha, negPart_eq_zero.mpr ha, mul_zero, add_zero]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos ha', negPart_of_nonpos ha',
      abs_of_nonpos (sub_nonpos.mpr (ha'.trans hb))]
    have habs := le_abs_self (a + b)
    rw [show -a - b = -(a + b) by ring_nf, abs_neg]
    linarith

theorem sgVal_l1_tendsto_of_traceNorm_tendsto_positive
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {S : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hS : ∀ i, MemSchattenClass 1 (S i)) (hT : MemSchattenClass 1 T)
    (hsymS : ∀ i, (S i).IsSymmetric) (hposT : T.IsPositive)
    (hconv : Tendsto (fun i => traceNorm H (S i - T)) l (nhds 0)) :
    Tendsto (fun i => ∑' n, |sgVal (S i) n - sgVal T n|) l (nhds 0) := by
  have habs := abs_sgVal_l1_tendsto_of_traceNorm_tendsto
    hS hT hsymS hposT.1 hconv
  have hneg : Tendsto (fun i => signedGreedyNegativeMass (S i)) l (nhds 0) := by
    refine squeeze_zero (fun _ => tsum_nonneg fun n => negPart_nonneg _)
      (fun i => signedGreedyNegativeMass_le_traceNorm_sub_of_positive hposT
        ((hS i).one_sub hT)) hconv
  have hbound : ∀ i, (∑' n, |sgVal (S i) n - sgVal T n|) ≤
      (∑' n, abs (|sgVal (S i) n| - |sgVal T n|)) +
        2 * signedGreedyNegativeMass (S i) := by
    intro i
    have hsabs := summable_abs_sgVal (hS i) (hsymS i)
    have hTabs := summable_abs_sgVal hT hposT.1
    have hfirst : Summable fun n => abs (|sgVal (S i) n| - |sgVal T n|) :=
      GaloisForLFunctions.HTGeometry.summable_abs_sub
        (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hsabs hTabs
    have hnegSum : Summable fun n => (sgVal (S i) n)⁻ := by
      refine Summable.of_nonneg_of_le (fun n => negPart_nonneg _) (fun n => ?_) hsabs
      by_cases hn : 0 ≤ sgVal (S i) n
      · rw [negPart_eq_zero.mpr hn]
        exact abs_nonneg _
      · rw [negPart_of_nonpos (le_of_not_ge hn)]
        exact neg_le_abs _
    apply Real.tsum_le_of_sum_le (fun n => abs_nonneg _)
    intro s
    calc
      ∑ n ∈ s, |sgVal (S i) n - sgVal T n|
          ≤ ∑ n ∈ s, (abs (|sgVal (S i) n| - |sgVal T n|) +
              2 * (sgVal (S i) n)⁻) :=
        Finset.sum_le_sum fun n _ =>
          abs_sub_le_abs_abs_sub_add_two_negPart _ _ (sgVal_nonneg_of_isPositive hposT n)
      _ = (∑ n ∈ s, abs (|sgVal (S i) n| - |sgVal T n|)) +
            2 * ∑ n ∈ s, (sgVal (S i) n)⁻ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (∑' n, abs (|sgVal (S i) n| - |sgVal T n|)) +
            2 * ∑' n, (sgVal (S i) n)⁻ := by
        gcongr
        · exact hfirst.sum_le_tsum s (fun _ _ => abs_nonneg _)
        · exact hnegSum.sum_le_tsum s (fun _ _ => negPart_nonneg _)
      _ = _ := rfl
  have hupper : Tendsto (fun i =>
      (∑' n, abs (|sgVal (S i) n| - |sgVal T n|)) +
        2 * signedGreedyNegativeMass (S i)) l (nhds 0) := by
    simpa using habs.add (hneg.const_mul 2)
  exact squeeze_zero (fun _ => tsum_nonneg fun _ => abs_nonneg _) hbound hupper

theorem norm_finset_prod_one_add_sub_prod_one_add_le
    {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖ ≤
      (∑ i ∈ s, ‖a i - b i‖) *
        ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx,
        Finset.sum_insert hx, Finset.prod_insert hx]
      have hsplit :
          (1 + a x) * ∏ i ∈ s, (1 + a i) -
              (1 + b x) * ∏ i ∈ s, (1 + b i) =
            (1 + a x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)) +
              (a x - b x) * ∏ i ∈ s, (1 + b i) := by ring
      rw [hsplit]
      have hprodB : ‖∏ i ∈ s, (1 + b i)‖ ≤
          ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
        rw [norm_prod]
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        calc
          ‖1 + b i‖ ≤ 1 + ‖b i‖ := by simpa using norm_add_le (1 : ℂ) (b i)
          _ ≤ 1 + ‖a i‖ + ‖b i‖ := by linarith [norm_nonneg (a i)]
      have hnormax : ‖1 + a x‖ ≤ 1 + ‖a x‖ := by
        simpa using norm_add_le (1 : ℂ) (a x)
      calc
        ‖(1 + a x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)) +
              (a x - b x) * ∏ i ∈ s, (1 + b i)‖
            ≤ ‖1 + a x‖ *
                ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖ +
              ‖a x - b x‖ * ‖∏ i ∈ s, (1 + b i)‖ := by
                simpa only [norm_mul] using norm_add_le
                  ((1 + a x) * ((∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)))
                  ((a x - b x) * ∏ i ∈ s, (1 + b i))
        _ ≤ (1 + ‖a x‖) *
                ((∑ i ∈ s, ‖a i - b i‖) *
                  ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) +
              ‖a x - b x‖ * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) := by
                gcongr
        _ ≤ (‖a x - b x‖ + ∑ i ∈ s, ‖a i - b i‖) *
              ((1 + ‖a x‖ + ‖b x‖) *
                ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) := by
              have hD : 0 ≤ ∑ i ∈ s, ‖a i - b i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
              have hP : 0 ≤ ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) :=
                Finset.prod_nonneg fun _ _ => by positivity
              have hax : 0 ≤ ‖a x‖ := norm_nonneg _
              have hbx : 0 ≤ ‖b x‖ := norm_nonneg _
              have hdx : 0 ≤ ‖a x - b x‖ := norm_nonneg _
              rw [show
                  (1 + ‖a x‖) *
                        ((∑ i ∈ s, ‖a i - b i‖) *
                          ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) +
                      ‖a x - b x‖ * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) =
                    ((1 + ‖a x‖) * (∑ i ∈ s, ‖a i - b i‖) +
                      ‖a x - b x‖) * ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) by ring,
                show
                  (‖a x - b x‖ + ∑ i ∈ s, ‖a i - b i‖) *
                        ((1 + ‖a x‖ + ‖b x‖) *
                          ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖)) =
                    ((‖a x - b x‖ + ∑ i ∈ s, ‖a i - b i‖) *
                      (1 + ‖a x‖ + ‖b x‖)) *
                        ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) by ring]
              gcongr
              nlinarith [mul_nonneg hD hbx,
                mul_nonneg hdx (add_nonneg hax hbx)]

theorem norm_tprod_one_add_sub_tprod_one_add_le
    {ι : Type*} (a b : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (hb : Summable fun i => ‖b i‖) :
    ‖(∏' i, (1 + a i)) - ∏' i, (1 + b i)‖ ≤
      (∑' i, ‖a i - b i‖) * Real.exp (∑' i, (‖a i‖ + ‖b i‖)) := by
  have hdiff : Summable fun i => ‖a i - b i‖ :=
    (ha.add hb).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => norm_sub_le _ _
  have hmass : Summable fun i => ‖a i‖ + ‖b i‖ := ha.add hb
  have hA : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + a i)) atTop
      (nhds (∏' i, (1 + a i))) := (multipliable_one_add_of_summable ha).hasProd
  have hB : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 + b i)) atTop
      (nhds (∏' i, (1 + b i))) := (multipliable_one_add_of_summable hb).hasProd
  have hleft : Tendsto (fun s : Finset ι =>
      ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖) atTop
      (nhds ‖(∏' i, (1 + a i)) - ∏' i, (1 + b i)‖) := (hA.sub hB).norm
  have hdiffT : Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖a i - b i‖) atTop
      (nhds (∑' i, ‖a i - b i‖)) := hdiff.hasSum
  have hmassT : Tendsto (fun s : Finset ι => ∑ i ∈ s, (‖a i‖ + ‖b i‖)) atTop
      (nhds (∑' i, (‖a i‖ + ‖b i‖))) := hmass.hasSum
  have hright : Tendsto (fun s : Finset ι =>
      (∑ i ∈ s, ‖a i - b i‖) *
        Real.exp (∑ i ∈ s, (‖a i‖ + ‖b i‖))) atTop
      (nhds ((∑' i, ‖a i - b i‖) *
        Real.exp (∑' i, (‖a i‖ + ‖b i‖)))) :=
    hdiffT.mul (Real.continuous_exp.continuousAt.tendsto.comp hmassT)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro s
  calc
    ‖(∏ i ∈ s, (1 + a i)) - ∏ i ∈ s, (1 + b i)‖
        ≤ (∑ i ∈ s, ‖a i - b i‖) *
            ∏ i ∈ s, (1 + ‖a i‖ + ‖b i‖) :=
      norm_finset_prod_one_add_sub_prod_one_add_le s a b
    _ ≤ (∑ i ∈ s, ‖a i - b i‖) *
          Real.exp (∑ i ∈ s, (‖a i‖ + ‖b i‖)) := by
      gcongr
      rw [Real.exp_sum]
      refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
      linarith [Real.add_one_le_exp (‖a i‖ + ‖b i‖)]

noncomputable def selfAdjointFredholmDeterminant (S : H →L[ℂ] H) (z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 + z * (sgVal S n : ℂ))

theorem summable_norm_mul_sgVal {S : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hsym : S.IsSymmetric) (z : ℂ) :
    Summable fun n => ‖z * (sgVal S n : ℂ)‖ := by
  exact ((summable_abs_sgVal hS hsym).mul_left ‖z‖).congr fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem tsum_norm_mul_sgVal {S : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hsym : S.IsSymmetric) (z : ℂ) :
    ∑' n, ‖z * (sgVal S n : ℂ)‖ = ‖z‖ * traceNorm H S := by
  rw [← tsum_abs_sgVal_eq_traceNorm hS hsym, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

omit [CompleteSpace H] in
theorem tsum_norm_mul_sgVal_sub_mul_sgVal
    (S T : H →L[ℂ] H) (z : ℂ) :
    ∑' n, ‖z * (sgVal S n : ℂ) - z * (sgVal T n : ℂ)‖ =
      ‖z‖ * ∑' n, |sgVal S n - sgVal T n| := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem tsum_norm_mul_sgVal_add_norm_mul_sgVal
    {S T : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T)
    (hsymS : S.IsSymmetric) (hsymT : T.IsSymmetric) (z : ℂ) :
    ∑' n, (‖z * (sgVal S n : ℂ)‖ + ‖z * (sgVal T n : ℂ)‖) =
      ‖z‖ * (traceNorm H S + traceNorm H T) := by
  rw [(summable_norm_mul_sgVal hS hsymS z).tsum_add
      (summable_norm_mul_sgVal hT hsymT z),
    tsum_norm_mul_sgVal hS hsymS z, tsum_norm_mul_sgVal hT hsymT z]
  ring

theorem selfAdjointFredholmDeterminant_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {S : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hS : ∀ i, MemSchattenClass 1 (S i)) (hT : MemSchattenClass 1 T)
    (hsymS : ∀ i, (S i).IsSymmetric) (hposT : T.IsPositive)
    (hconv : Tendsto (fun i => traceNorm H (S i - T)) l (nhds 0))
    {K : Set ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hKR : ∀ z ∈ K, ‖z‖ ≤ R) :
    TendstoUniformlyOn (fun i z => selfAdjointFredholmDeterminant (S i) z)
      (selfAdjointFredholmDeterminant T) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let d : ι → ℝ := fun i => ∑' n, |sgVal (S i) n - sgVal T n|
  let M : ℝ := traceNorm H T
  let C : ℝ := R * Real.exp (R * (2 * M + 1))
  have hd : Tendsto d l (nhds 0) :=
    sgVal_l1_tendsto_of_traceNorm_tendsto_positive hS hT hsymS hposT hconv
  have hC0 : 0 ≤ C := mul_nonneg hR0 (Real.exp_nonneg _)
  have hsmall : ∀ᶠ i in l, C * d i < ε :=
    (hd.const_mul C).eventually_lt_const (by simpa using hε)
  have hdiffSmall : ∀ᶠ i in l, traceNorm H (S i - T) < 1 :=
    hconv.eventually_lt_const zero_lt_one
  filter_upwards [hsmall, hdiffSmall] with i hi hdi
  intro z hz
  rw [dist_comm, dist_eq_norm]
  have hprod := norm_tprod_one_add_sub_tprod_one_add_le
    (fun n => z * (sgVal (S i) n : ℂ)) (fun n => z * (sgVal T n : ℂ))
    (summable_norm_mul_sgVal (hS i) (hsymS i) z)
    (summable_norm_mul_sgVal hT hposT.1 z)
  have hd0 : 0 ≤ d i := tsum_nonneg fun _ => abs_nonneg _
  have hM0 : 0 ≤ M := traceNorm_nonneg T
  have hmassS0 : 0 ≤ traceNorm H (S i) := traceNorm_nonneg _
  have hmassS : traceNorm H (S i) ≤ M + 1 := by
    have habs := abs_traceNorm_sub_le_traceNorm_sub (hS i) hT
    have hle := le_trans (le_abs_self (traceNorm H (S i) - traceNorm H T)) habs
    dsimp [M]
    linarith
  have hmass : traceNorm H (S i) + traceNorm H T ≤ 2 * M + 1 := by
    dsimp [M] at hmassS ⊢
    linarith
  have harg : ‖z‖ * (traceNorm H (S i) + traceNorm H T) ≤ R * (2 * M + 1) := by
    exact mul_le_mul (hKR z hz) hmass (add_nonneg hmassS0 (traceNorm_nonneg T)) hR0
  have hexp := Real.exp_le_exp.mpr harg
  change ‖selfAdjointFredholmDeterminant (S i) z -
      selfAdjointFredholmDeterminant T z‖ < ε
  calc
    ‖selfAdjointFredholmDeterminant (S i) z - selfAdjointFredholmDeterminant T z‖
        ≤ ‖z‖ * d i *
            Real.exp (‖z‖ * (traceNorm H (S i) + traceNorm H T)) := by
      simpa only [selfAdjointFredholmDeterminant,
        tsum_norm_mul_sgVal_sub_mul_sgVal,
        tsum_norm_mul_sgVal_add_norm_mul_sgVal (hS i) hT (hsymS i) hposT.1 z] using hprod
    _ ≤ R * d i *
          Real.exp (‖z‖ * (traceNorm H (S i) + traceNorm H T)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hKR z hz) hd0) (Real.exp_nonneg _)
    _ ≤ R * d i * Real.exp (R * (2 * M + 1)) := by
      exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hR0 hd0)
    _ = C * d i := by simp only [C]; ring
    _ < ε := hi

theorem approxNumber_constrainedProlateArithmeticLimitOperator (n : ℕ) :
    approxNumber constrainedProlateArithmeticLimitOperator n =
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n := by
  rw [constrainedProlateArithmeticLimitOperator_eq_diagonalOperator]
  exact approxNumber_diagonalOperator_eq
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg
    (fun {_ _} h => constrainedProlateArithmeticEigenvalue_strictAnti.antitone h) n

theorem sgVal_constrainedProlateArithmeticLimitOperator (n : ℕ) :
    sgVal constrainedProlateArithmeticLimitOperator n =
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n := by
  have hcpt := constrainedProlateArithmeticLimitOperator_memSchattenClass_one.isCompactOperator
    one_pos
  have habs := abs_sgVal_eq_singVal hcpt
    constrainedProlateArithmeticLimitOperator_isSelfAdjoint.isSymmetric n
  rw [← approxNumber_eq_singVal hcpt n,
    approxNumber_constrainedProlateArithmeticLimitOperator] at habs
  rw [abs_of_nonneg (sgVal_nonneg_of_isPositive
    constrainedProlateArithmeticLimitOperator_isPositive n)] at habs
  exact habs

theorem selfAdjointFredholmDeterminant_constrainedProlateArithmeticLimitOperator :
    selfAdjointFredholmDeterminant constrainedProlateArithmeticLimitOperator =
      constrainedProlateArithmeticFredholmDeterminant := by
  funext z
  unfold selfAdjointFredholmDeterminant constrainedProlateArithmeticFredholmDeterminant
    arithmeticDiagonalFredholmDeterminant
  apply tprod_congr
  intro n
  rw [sgVal_constrainedProlateArithmeticLimitOperator]

theorem selfAdjointFredholmDeterminant_tendstoUniformlyOn_constrainedProlate
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {S : ι → ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert}
    (hS : ∀ i, MemSchattenClass 1 (S i))
    (hsymS : ∀ i, (S i).IsSymmetric)
    (hconv : Tendsto (fun i => traceNorm ArithmeticDilationHilbert
      (S i - constrainedProlateArithmeticLimitOperator)) l (nhds 0))
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun i z => selfAdjointFredholmDeterminant (S i) z)
      constrainedProlateArithmeticFredholmDeterminant l K := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  have ht := selfAdjointFredholmDeterminant_tendstoUniformlyOn
    hS constrainedProlateArithmeticLimitOperator_memSchattenClass_one hsymS
    constrainedProlateArithmeticLimitOperator_isPositive hconv
    (show 0 ≤ max R 0 by exact le_max_right _ _)
    (fun z hz => (show ‖z‖ ≤ R by simpa using hR z hz).trans (le_max_left _ _))
  rw [selfAdjointFredholmDeterminant_constrainedProlateArithmeticLimitOperator] at ht
  exact ht

noncomputable def arithmeticDilationStageFredholmDeterminant
    {ι : Type*} (a : ι → ℕ → ℝ) (E : ι → ℕ → ℕ → ℝ)
    (w : ℕ → ℝ) (x : ι) (z : ℂ) : ℂ :=
  selfAdjointFredholmDeterminant
    (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x)) z

theorem arithmeticDilationLimitComplexOperator_eq_constrainedProlate
    {L w : ℕ → ℝ}
    (hkappa : ∀ n, 2 * L n * w n =
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n) :
    absoluteMatrixOperator (arithmeticDilationLimitComplexMatrix L w) =
      constrainedProlateArithmeticLimitOperator := by
  rw [arithmeticDilationLimitComplexMatrix_eq_diagMul]
  unfold constrainedProlateArithmeticLimitOperator
  congr 2
  funext n
  exact_mod_cast hkappa n

theorem arithmeticDilationStageFredholmDeterminant_tendstoUniformlyOn
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {E : α → ℕ → ℕ → ℝ} {w L Ω : ℕ → ℝ} {a : α → ℕ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hΩ : ∀ k, L k ≤ Ω k)
    (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ L k)
    (haev : ∀ k, ∀ᶠ x in l, a x k = L k)
    (hLw : Summable fun k => L k * w k)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ =>
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|)
    (hEtend : Tendsto (fun x => ∑' p : ℕ × ℕ,
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|) l (nhds 0))
    (hEsym : ∀ x i j, E x i j = E x j i)
    (hkappa : ∀ n, 2 * L n * w n =
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n)
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun x z => arithmeticDilationStageFredholmDeterminant a E w x z)
      constrainedProlateArithmeticFredholmDeterminant l K := by
  obtain ⟨hstage, _hlimit, htend⟩ := arithmeticDilation_traceClass_traceNorm_limit
    hw hΩ ha0 haL haev hLw hEsum hEtend
  have hlimit := arithmeticDilationLimitComplexOperator_eq_constrainedProlate hkappa
  rw [hlimit] at htend
  exact selfAdjointFredholmDeterminant_tendstoUniformlyOn_constrainedProlate
    hstage (fun x => (arithmeticDilationComplexOperator_isSelfAdjoint hEsym x).isSymmetric)
    htend K hK

end RHTower
