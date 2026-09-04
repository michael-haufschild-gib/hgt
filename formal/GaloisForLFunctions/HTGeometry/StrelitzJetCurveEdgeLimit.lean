import GaloisForLFunctions.HTGeometry.StrelitzJetCurveNewtonFaceDominance

/-!
# Numerical Strelitz roots converge to exact Newton-edge roots

Compact-annulus control supplies a convergent subsequence of normalized numerical roots with
nonzero limit.  Scaling the exact specialized curve equation by its maximal Newton weight makes
all lower-face terms vanish and identifies the surviving finite sum with the exact edge polynomial.
Thus the selected numerical branch genuinely converges to one of that edge polynomial's nonzero
complex roots.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Exact factorization of one Newton monomial after division by an arbitrary real base weight. -/
theorem strelitzNewtonMonomial_div_rpow
    {r : ℝ} (hr : 0 < r) (a t : ℂ) (d k : ℕ) (p w : ℝ) :
    (a * t ^ k) / ((r ^ w : ℝ) : ℂ) =
      (a / (r : ℂ) ^ d) * (t / ((r ^ p : ℝ) : ℂ)) ^ k *
        ((r ^ ((d : ℝ) + (k : ℝ) * p - w) : ℝ) : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  have hrp0 : ((r ^ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrp.ne'
  have hrw : 0 < r ^ w := Real.rpow_pos_of_pos hr w
  have hrw0 : ((r ^ w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrw.ne'
  have hscale : r ^ ((d : ℝ) + (k : ℝ) * p - w) =
      r ^ d * (r ^ p) ^ k / r ^ w := by
    rw [Real.rpow_sub hr, Real.rpow_add hr, Real.rpow_natCast]
    rw [mul_comm (k : ℝ) p, Real.rpow_mul hr.le, Real.rpow_natCast]
  have hscaleC : ((r ^ ((d : ℝ) + (k : ℝ) * p - w) : ℝ) : ℂ) =
      (r : ℂ) ^ d * ((r ^ p : ℝ) : ℂ) ^ k / ((r ^ w : ℝ) : ℂ) := by
    exact_mod_cast hscale
  rw [div_pow, hscaleC]
  field_simp [hr0, hrp0, hrw0]

/-- A fixed negative real power of any positive real scale tending to infinity tends to zero. -/
theorem tendsto_rpow_const_zero_of_tendsto_atTop
    {α : Type*} {l : Filter α} {r : α → ℝ} (hrTop : Tendsto r l atTop)
    {q : ℝ} (hq : q < 0) : Tendsto (fun x => r x ^ q) l (nhds 0) := by
  have hlog : Tendsto (fun x => Real.log (r x)) l atTop :=
    Real.tendsto_log_atTop.comp hrTop
  have hmul := hlog.atTop_mul_const_of_neg hq
  have hexp := Real.tendsto_exp_atBot.comp hmul
  refine hexp.congr' ?_
  filter_upwards [hrTop.eventually_gt_atTop 0] with x hx
  exact (Real.rpow_def_of_pos hx q).symm

/-- Compact-annulus control yields a cofinal normalized-root subsequence with nonzero complex limit. -/
theorem exists_strelitzJetCurveNormalizedRoot_tendsto_nonzero_subsequence
    {S : MvPolynomial (Fin 2) ℂ} {ν : ℕ → ℕ} {u root : ℕ → ℂ}
    {p : ℝ} {ns : ℕ → ℕ} (hns : StrictMono ns)
    (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0)
    (hslope : Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k))
      atTop (nhds p))
    {i : ℕ} (hi : i ∈ (strelitzJetCurvePolynomial S).support)
    (hmax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p i) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ τ : ℕ → ℕ, StrictMono τ ∧
      Tendsto (fun m => strelitzJetCurveNormalizedRoot u root p (ns (τ m)))
        atTop (nhds c) := by
  obtain ⟨c₀, C, hc₀, hannulus⟩ :=
    exists_eventually_strelitzJetCurveNormalizedRoot_mem_annulus
      hns hνTop hu hroot hroot0 hslope hi hmax
  have hupper : ∀ᶠ m : ℕ in atTop,
      ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ ≤ C :=
    hannulus.mono fun _ h => h.2
  have hlower : ∀ᶠ m : ℕ in atTop,
      c₀ ≤ ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ :=
    hannulus.mono fun _ h => h.1
  have hC : 0 ≤ C := by
    obtain ⟨m, hm⟩ := hupper.exists
    exact le_trans (norm_nonneg _) hm
  let clipped : ℕ → ℂ := fun m =>
    if ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ ≤ C then
      strelitzJetCurveNormalizedRoot u root p (ns m) else 0
  have hclipped : ∀ m, clipped m ∈ Metric.closedBall (0 : ℂ) C := by
    intro m
    rw [mem_closedBall_zero_iff]
    by_cases hm : ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ ≤ C
    · simpa only [clipped, if_pos hm] using hm
    · simp [clipped, hm, hC]
  obtain ⟨c, hcBall, τ, hτ, hlim⟩ :=
    (isCompact_closedBall (0 : ℂ) C).tendsto_subseq hclipped
  have hupperSub := hτ.tendsto_atTop.eventually hupper
  have heq : ∀ᶠ m : ℕ in atTop,
      clipped (τ m) = strelitzJetCurveNormalizedRoot u root p (ns (τ m)) := by
    filter_upwards [hupperSub] with m hm
    simp [clipped, hm]
  have hlimRoot : Tendsto
      (fun m => strelitzJetCurveNormalizedRoot u root p (ns (τ m)))
      atTop (nhds c) := by
    refine Tendsto.congr' ?_ hlim
    exact heq.mono fun _ hm => by simpa only [Function.comp_apply] using hm
  have hc : c ≠ 0 := by
    intro hzero
    have hnormZero : Tendsto
        (fun m => ‖strelitzJetCurveNormalizedRoot u root p (ns (τ m))‖)
        atTop (nhds 0) := by
      simpa [hzero] using hlimRoot.norm
    have hsmall := hnormZero.eventually_lt_const hc₀
    have hlowerSub := hτ.tendsto_atTop.eventually hlower
    obtain ⟨m, hmSmall, hmLower⟩ := (hsmall.and hlowerSub).exists
    exact (not_lt_of_ge hmLower) hmSmall
  exact ⟨c, hc, τ, hτ, hlimRoot⟩

/-- A normalized numerical Strelitz root branch has a cofinal subsequence converging to a nonzero root of its exact maximal Newton-edge polynomial. -/
theorem exists_strelitzJetCurveNormalizedRoot_tendsto_edgeRoot_subsequence
    {S : MvPolynomial (Fin 2) ℂ} {ν : ℕ → ℕ} {u root : ℕ → ℂ}
    {p : ℝ} {ns : ℕ → ℕ} (hns : StrictMono ns)
    (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0)
    (hslope : Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k))
      atTop (nhds p))
    {i : ℕ} (hi : i ∈ (strelitzJetCurvePolynomial S).support)
    (hmax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p i) :
    ∃ c : ℂ, c ≠ 0 ∧
      (strelitzJetCurveNewtonEdgePolynomial S p
        (strelitzJetCurveNewtonWeight S p i)).IsRoot c ∧
      ∃ τ : ℕ → ℕ, StrictMono τ ∧
        Tendsto (fun m => strelitzJetCurveNormalizedRoot u root p (ns (τ m)))
          atTop (nhds c) := by
  classical
  obtain ⟨c, hc, τ, hτ, hzLim⟩ :=
    exists_strelitzJetCurveNormalizedRoot_tendsto_nonzero_subsequence
      hns hνTop hu hroot hroot0 hslope hi hmax
  let R := strelitzJetCurvePolynomial S
  let q : ℕ → Polynomial ℂ := fun k => finOnePolynomial (R.coeff k)
  let w := strelitzJetCurveNewtonWeight S p i
  let z : ℕ → ℂ := fun m =>
    strelitzJetCurveNormalizedRoot u root p (ns (τ m))
  let scaled : ℕ → ℕ → ℂ := fun k m =>
    ((q k).eval (u (ns (τ m))) / ((‖u (ns (τ m))‖ : ℂ) ^ (q k).natDegree)) *
      (z m) ^ k *
      ((‖u (ns (τ m))‖ ^ (strelitzJetCurveNewtonWeight S p k - w) : ℝ) : ℂ)
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  have hστ : StrictMono (ns ∘ τ) := hns.comp hτ
  have huTopSub : Tendsto (fun m => ‖u (ns (τ m))‖) atTop atTop :=
    huTop.comp hστ.tendsto_atTop
  have hzLim' : Tendsto z atTop (nhds c) := by simpa [z] using hzLim
  have hterm : ∀ k ∈ R.support,
      Tendsto (scaled k) atTop
        (nhds (if strelitzJetCurveNewtonWeight S p k = w
          then (q k).leadingCoeff * c ^ k else 0)) := by
    intro k hk
    have hAk := (tendsto_strelitzJetCurveCoefficient_div_norm_pow S hνTop hu k).comp
      hστ.tendsto_atTop
    have hbase := hAk.mul (hzLim'.pow k)
    by_cases hw : strelitzJetCurveNewtonWeight S p k = w
    · rw [if_pos hw]
      simpa [scaled, hw] using hbase
    · rw [if_neg hw]
      have hlt : strelitzJetCurveNewtonWeight S p k < w :=
        lt_of_le_of_ne (hmax k (by simpa [R] using hk)) hw
      have hpow : Tendsto (fun m =>
          ‖u (ns (τ m))‖ ^ (strelitzJetCurveNewtonWeight S p k - w))
          atTop (nhds 0) :=
        tendsto_rpow_const_zero_of_tendsto_atTop huTopSub (sub_neg.mpr hlt)
      have hpowC : Tendsto (fun m =>
          ((‖u (ns (τ m))‖ ^ (strelitzJetCurveNewtonWeight S p k - w) : ℝ) : ℂ))
          atTop (nhds 0) := by
        refine Tendsto.congr' ?_ ((Complex.continuous_ofReal.tendsto 0).comp hpow)
        filter_upwards with m
        rfl
      have hfull := hbase.mul hpowC
      simpa [scaled] using hfull
  have hsumLim := tendsto_finsetSum R.support (fun k hk => hterm k hk)
  have hsumZero : ∀ᶠ m : ℕ in atTop, ∑ k ∈ R.support, scaled k m = 0 := by
    have hrootSub := hστ.tendsto_atTop.eventually hroot
    have hbasePos := huTopSub.eventually_gt_atTop 0
    filter_upwards [hrootSub, hbasePos] with m hm hrm
    have hm' : (strelitzJetCurveSpecialization S (u (ns (τ m)))).eval
        (root (ns (τ m))) = 0 := hm
    rw [strelitzJetCurveSpecialization, Polynomial.eval_map,
      Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hm'
    have hraw : ∑ k ∈ R.support,
        (q k).eval (u (ns (τ m))) * root (ns (τ m)) ^ k = 0 := by
      simpa [R, q, eval_finOnePolynomial] using hm'
    calc
      ∑ k ∈ R.support, scaled k m =
          ∑ k ∈ R.support,
            ((q k).eval (u (ns (τ m))) * root (ns (τ m)) ^ k) /
              ((‖u (ns (τ m))‖ ^ w : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (strelitzNewtonMonomial_div_rpow hrm
          ((q k).eval (u (ns (τ m)))) (root (ns (τ m))) (q k).natDegree k p w).symm
      _ = (∑ k ∈ R.support,
          (q k).eval (u (ns (τ m))) * root (ns (τ m)) ^ k) /
            ((‖u (ns (τ m))‖ ^ w : ℝ) : ℂ) := by rw [Finset.sum_div]
      _ = 0 := by rw [hraw, zero_div]
  have hsumTendsZero : Tendsto (fun m => ∑ k ∈ R.support, scaled k m)
      atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    exact hsumZero.mono fun _ hm => hm.symm
  have hlimitZero : (∑ k ∈ R.support,
      if strelitzJetCurveNewtonWeight S p k = w
      then (q k).leadingCoeff * c ^ k else 0) = 0 :=
    tendsto_nhds_unique hsumLim hsumTendsZero
  refine ⟨c, hc, ?_, τ, hτ, hzLim⟩
  rw [Polynomial.IsRoot]
  have hedge : (strelitzJetCurveNewtonEdgePolynomial S p w).eval c =
      ∑ k ∈ R.support,
        if strelitzJetCurveNewtonWeight S p k = w
        then (q k).leadingCoeff * c ^ k else 0 := by
    simp [strelitzJetCurveNewtonEdgePolynomial, strelitzJetCurveMaxNewtonFace,
      Polynomial.eval_finsetSum, R, q]
    rw [Finset.sum_filter]
  rw [show strelitzJetCurveNewtonWeight S p i = w from rfl, hedge]
  exact hlimitZero

end

end GaloisForLFunctions.HTGeometry

