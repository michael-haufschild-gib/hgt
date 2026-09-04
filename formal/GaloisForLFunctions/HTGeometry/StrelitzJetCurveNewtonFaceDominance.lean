import GaloisForLFunctions.HTGeometry.StrelitzJetCurveNormalizedRoot

/-!
# Newton-face dominance for normalized Strelitz roots

At an extracted Newton slope, the normalized numerical roots cannot escape to infinity or collapse
to zero.  In either case an extreme monomial on the finite maximal face dominates every other term
of the exact specialized root equation.  Constructive cofinal subsequence extraction upgrades these
two contradictions to one fixed compact annulus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Exact ratio of equal-weight Newton monomials when the numerator index is lower. -/
theorem strelitzNewtonMonomialRatio_of_le
    {r : ℝ} (hr : 0 < r) {a b t : ℂ} (hb : b ≠ 0) (ht : t ≠ 0)
    {d e k i : ℕ} {p : ℝ} (hki : k ≤ i)
    (hw : (d : ℝ) + (k : ℝ) * p = (e : ℝ) + (i : ℝ) * p) :
    (a * t ^ k) / (b * t ^ i) =
      ((a / (r : ℂ) ^ d) / (b / (r : ℂ) ^ e)) /
        (t / ((r ^ p : ℝ) : ℂ)) ^ (i - k) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  have hrp0 : ((r ^ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrp.ne'
  have hdelta : (e : ℝ) - d = -p * (i - k : ℕ) := by
    have hki' : (k : ℝ) ≤ i := by exact_mod_cast hki
    rw [Nat.cast_sub hki]
    linarith
  have hrpow : r ^ e / r ^ d = (r ^ p)⁻¹ ^ (i - k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hr]
    rw [hdelta, Real.rpow_mul hr.le, Real.rpow_neg hr.le]
    rw [Real.rpow_natCast]
  have hre : r ^ d * (r ^ p)⁻¹ ^ (i - k) = r ^ e := by
    rw [← hrpow]
    field_simp [hr.ne']
  have hreC : (r : ℂ) ^ d * (((r ^ p : ℝ) : ℂ)⁻¹) ^ (i - k) = (r : ℂ) ^ e := by
    exact_mod_cast hre
  rw [div_pow]
  field_simp [hb, ht, hr0, hrp0]
  rw [← hreC]
  field_simp [hrp0]
  have htpow : t ^ k * t ^ (i - k) = t ^ i := by
    rw [← pow_add, Nat.add_sub_of_le hki]
  have hcancel : (1 / ((r ^ p : ℝ) : ℂ)) ^ (i - k) *
      ((r ^ p : ℝ) : ℂ) ^ (i - k) = 1 := by
    rw [div_pow]
    field_simp [hrp0]
    simp
  calc
    a * t ^ k * t ^ (i - k) = a * (t ^ k * t ^ (i - k)) := by ring
    _ = a * t ^ i := by rw [htpow]
    _ = a * t ^ i * 1 := by ring
    _ = a * t ^ i * ((1 / ((r ^ p : ℝ) : ℂ)) ^ (i - k) *
        ((r ^ p : ℝ) : ℂ) ^ (i - k)) := by rw [hcancel]
    _ = a * t ^ i * (1 / ((r ^ p : ℝ) : ℂ)) ^ (i - k) *
        ((r ^ p : ℝ) : ℂ) ^ (i - k) := by ring

/-- Exact ratio of equal-weight Newton monomials when the numerator index is higher. -/
theorem strelitzNewtonMonomialRatio_of_ge
    {r : ℝ} (hr : 0 < r) {a b t : ℂ} (hb : b ≠ 0) (ht : t ≠ 0)
    {d e k i : ℕ} {p : ℝ} (hik : i ≤ k)
    (hw : (d : ℝ) + (k : ℝ) * p = (e : ℝ) + (i : ℝ) * p) :
    (a * t ^ k) / (b * t ^ i) =
      ((a / (r : ℂ) ^ d) / (b / (r : ℂ) ^ e)) *
        (t / ((r ^ p : ℝ) : ℂ)) ^ (k - i) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr p
  have hrp0 : ((r ^ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrp.ne'
  have hdelta : (e : ℝ) - d = p * (k - i : ℕ) := by
    have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
    rw [Nat.cast_sub hik]
    linarith
  have hrpow : r ^ e / r ^ d = (r ^ p) ^ (k - i) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hr]
    rw [hdelta, Real.rpow_mul hr.le, Real.rpow_natCast]
  have hre : r ^ d * (r ^ p) ^ (k - i) = r ^ e := by
    rw [← hrpow]
    field_simp [hr.ne']
  have hreC : (r : ℂ) ^ d * (((r ^ p : ℝ) : ℂ)) ^ (k - i) = (r : ℂ) ^ e := by
    exact_mod_cast hre
  rw [div_pow]
  field_simp [hb, ht, hr0, hrp0]
  rw [← hreC]
  have htpow : t ^ i * t ^ (k - i) = t ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hik]
  rw [← htpow]
  ring

/-- A finite sum is eventually nonzero when every other summand divided by one nonzero summand tends to zero. -/
theorem eventually_finset_sum_ne_zero_of_dominant_div
    {α ι : Type*} {l : Filter α} [DecidableEq ι]
    (s : Finset ι) (g : ι → α → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hi₀ne : ∀ᶠ x in l, g i₀ x ≠ 0)
    (hsmall : ∀ i ∈ s, i ≠ i₀ →
      Tendsto (fun x => g i x / g i₀ x) l (nhds 0)) :
    ∀ᶠ x in l, ∑ i ∈ s, g i x ≠ 0 := by
  have hterm : ∀ i ∈ s,
      Tendsto (fun x => g i x / g i₀ x) l (nhds (if i = i₀ then 1 else 0)) := by
    intro i hi
    by_cases h : i = i₀
    · subst i
      rw [if_pos rfl]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hi₀ne] with x hx
      exact (div_self hx).symm
    · rw [if_neg h]
      exact hsmall i hi h
  have hsum := tendsto_finsetSum s (fun i hi => hterm i hi)
  have hval : (∑ i ∈ s, if i = i₀ then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_eq_single_of_mem i₀ hi₀]
    · simp
    · intro i hi hne
      simp [hne]
  rw [hval] at hsum
  have hratio : Tendsto (fun x => (∑ i ∈ s, g i x) / g i₀ x) l (nhds 1) := by
    refine hsum.congr' ?_
    filter_upwards with x
    rw [Finset.sum_div]
  have hhalf : ∀ᶠ x in l, (1 : ℝ) / 2 < ‖(∑ i ∈ s, g i x) / g i₀ x‖ := by
    have hnorm := hratio.norm
    exact hnorm.eventually_const_lt (by norm_num)
  filter_upwards [hhalf, hi₀ne] with x hx hden
  intro hzero
  rw [hzero, zero_div, norm_zero] at hx
  norm_num at hx

/-- An unbounded real sequence has a strictly increasing cofinal subsequence tending to infinity. -/
theorem exists_strictMono_tendsto_atTop_of_frequently_gt
    (a : ℕ → ℝ) (hfreq : ∀ C : ℝ, ∃ᶠ n : ℕ in atTop, C < a n) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun k => a (ns k)) atTop atTop := by
  classical
  have hunbounded : ∀ N M : ℕ, ∃ n : ℕ, M ≤ n ∧ (N : ℝ) < a n := by
    intro N M
    obtain ⟨n, hnval, hnM⟩ :=
      ((hfreq N).and_eventually (eventually_ge_atTop M)).exists
    exact ⟨n, hnM, hnval⟩
  let pick : ℕ → ℕ → ℕ := fun N M => Classical.choose (hunbounded N M)
  have hpick_ge : ∀ N M : ℕ, M ≤ pick N M := fun N M =>
    (Classical.choose_spec (hunbounded N M)).1
  have hpick_gt : ∀ N M : ℕ, (N : ℝ) < a (pick N M) := fun N M =>
    (Classical.choose_spec (hunbounded N M)).2
  let ns : ℕ → ℕ := Nat.rec (pick 0 0) (fun k previous => pick (k + 1) (previous + 1))
  have hstep : ∀ k : ℕ, ns k < ns (k + 1) := by
    intro k
    change ns k < pick (k + 1) (ns k + 1)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hpick_ge (k + 1) (ns k + 1))
  have hval : ∀ k : ℕ, (k : ℝ) < a (ns k) := by
    intro k
    cases k with
    | zero => exact hpick_gt 0 0
    | succ k => exact hpick_gt (k + 1) (ns k + 1)
  refine ⟨ns, strictMono_nat_of_lt_succ hstep, ?_⟩
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N : ℕ, hNb : b < N⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with k hk
  exact le_trans hNb.le (lt_of_le_of_lt (by exact_mod_cast hk) (hval k)).le

/-- A nonnegative real sequence with no eventual positive floor has a strictly increasing cofinal
subsequence tending to zero. -/
theorem exists_strictMono_tendsto_zero_of_frequently_lt
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hfreq : ∀ c : ℝ, 0 < c → ∃ᶠ n : ℕ in atTop, a n < c) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun k => a (ns k)) atTop (nhds 0) := by
  classical
  have hunbounded : ∀ N M : ℕ, ∃ n : ℕ, M ≤ n ∧ a n < 1 / ((N : ℝ) + 1) := by
    intro N M
    have hpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    obtain ⟨n, hnval, hnM⟩ :=
      ((hfreq _ hpos).and_eventually (eventually_ge_atTop M)).exists
    exact ⟨n, hnM, hnval⟩
  let pick : ℕ → ℕ → ℕ := fun N M => Classical.choose (hunbounded N M)
  have hpick_ge : ∀ N M : ℕ, M ≤ pick N M := fun N M =>
    (Classical.choose_spec (hunbounded N M)).1
  have hpick_lt : ∀ N M : ℕ, a (pick N M) < 1 / ((N : ℝ) + 1) := fun N M =>
    (Classical.choose_spec (hunbounded N M)).2
  let ns : ℕ → ℕ := Nat.rec (pick 0 0) (fun k previous => pick (k + 1) (previous + 1))
  have hstep : ∀ k : ℕ, ns k < ns (k + 1) := by
    intro k
    change ns k < pick (k + 1) (ns k + 1)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (hpick_ge (k + 1) (ns k + 1))
  have hval : ∀ k : ℕ, a (ns k) < 1 / ((k : ℝ) + 1) := by
    intro k
    cases k with
    | zero => exact hpick_lt 0 0
    | succ k => exact hpick_lt (k + 1) (ns k + 1)
  refine ⟨ns, strictMono_nat_of_lt_succ hstep, ?_⟩
  refine squeeze_zero' (Filter.Eventually.of_forall fun k => ha (ns k))
    (Filter.Eventually.of_forall fun k => (hval k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The largest index on a maximal Newton face prevents normalized exact roots from escaping to infinity. -/
theorem not_tendsto_strelitzJetCurveNormalizedRoot_norm_atTop
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
    {i₀ : ℕ} (hi₀ : i₀ ∈ (strelitzJetCurvePolynomial S).support)
    (hmax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p i₀)
    (hindex : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p i₀ → k ≤ i₀) :
    ¬ Tendsto (fun m =>
      ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖) atTop atTop := by
  classical
  intro hzTop
  let R := strelitzJetCurvePolynomial S
  let q : ℕ → Polynomial ℂ := fun k => finOnePolynomial (R.coeff k)
  let g : ℕ → ℕ → ℂ := fun k m => (q k).eval (u (ns m)) * root (ns m) ^ k
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  have huTopSub : Tendsto (fun m => ‖u (ns m)‖) atTop atTop :=
    huTop.comp hns.tendsto_atTop
  have huExp : HasLogScaleExponent atTop (fun m => ‖u (ns m)‖)
      (fun m => u (ns m)) 1 := hasLogScaleExponent_self_norm huTopSub
  have hroot0Sub : ∀ᶠ m : ℕ in atTop, root (ns m) ≠ 0 :=
    hns.tendsto_atTop.eventually hroot0
  have hrootExp : HasLogScaleExponent atTop (fun m => ‖u (ns m)‖)
      (fun m => root (ns m)) p := by
    exact ⟨hroot0Sub, by simpa [strelitzJetCurveRootLogSlope] using hslope⟩
  have hq : ∀ k ∈ R.support, q k ≠ 0 := by
    intro k hk
    exact finOnePolynomial_ne_zero (Polynomial.mem_support_iff.mp hk)
  have hg : ∀ k ∈ R.support,
      HasLogScaleExponent atTop (fun m => ‖u (ns m)‖) (g k)
        (strelitzJetCurveNewtonWeight S p k) := by
    intro k hk
    simpa [g, q, R, strelitzJetCurveNewtonWeight] using
      hasLogScaleExponent_newton_monomial huTopSub huExp hrootExp (hq k hk) k
  have hi₀R : i₀ ∈ R.support := by simpa [R] using hi₀
  have hi₀ne : ∀ᶠ m : ℕ in atTop, g i₀ m ≠ 0 := (hg i₀ hi₀R).1
  have hzInv : Tendsto (fun m =>
      (strelitzJetCurveNormalizedRoot u root p (ns m))⁻¹) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ hzTop.inv_tendsto_atTop
    filter_upwards with m
    simp only [Pi.inv_apply, norm_inv]
  have hsmall : ∀ k ∈ R.support, k ≠ i₀ →
      Tendsto (fun m => g k m / g i₀ m) atTop (nhds 0) := by
    intro k hk hki
    by_cases hw : strelitzJetCurveNewtonWeight S p k =
        strelitzJetCurveNewtonWeight S p i₀
    · have hkle : k ≤ i₀ := hindex k (by simpa [R] using hk) hw
      have hklt : k < i₀ := lt_of_le_of_ne hkle hki
      have hAk := (tendsto_strelitzJetCurveCoefficient_div_norm_pow S hνTop hu k).comp
        hns.tendsto_atTop
      have hAi := (tendsto_strelitzJetCurveCoefficient_div_norm_pow S hνTop hu i₀).comp
        hns.tendsto_atTop
      have hlead : (q i₀).leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (hq i₀ hi₀R)
      have hratio := hAk.div hAi hlead
      have hpow := hzInv.pow (i₀ - k)
      have hdelta : i₀ - k ≠ 0 := (Nat.sub_pos_iff_lt.mpr hklt).ne'
      have hpow0 : Tendsto (fun m =>
          (strelitzJetCurveNormalizedRoot u root p (ns m))⁻¹ ^ (i₀ - k))
          atTop (nhds 0) := by
        simpa [zero_pow hdelta] using hpow
      have hprod := hratio.mul hpow0
      have hprod0 : Tendsto (fun m =>
          (((q k).eval (u (ns m)) / ((‖u (ns m)‖ : ℂ) ^ (q k).natDegree)) /
            ((q i₀).eval (u (ns m)) / ((‖u (ns m)‖ : ℂ) ^ (q i₀).natDegree))) *
            (strelitzJetCurveNormalizedRoot u root p (ns m))⁻¹ ^ (i₀ - k))
          atTop (nhds 0) := by
        simpa [q, R] using hprod
      refine hprod0.congr' ?_
      filter_upwards [hi₀ne, huTopSub.eventually_gt_atTop 0, hroot0Sub] with m hgm hum hrm
      have hqi : (q i₀).eval (u (ns m)) ≠ 0 := by
        exact (mul_ne_zero_iff.mp hgm).1
      have hratioEq := strelitzNewtonMonomialRatio_of_le
        (a := (q k).eval (u (ns m)))
        (d := (q k).natDegree) (e := (q i₀).natDegree)
        (k := k) (i := i₀) (p := p) hum hqi hrm hklt.le hw
      rw [inv_pow, ← div_eq_mul_inv]
      simpa only [g, strelitzJetCurveNormalizedRoot] using hratioEq.symm
    · have hlt : strelitzJetCurveNewtonWeight S p k <
          strelitzJetCurveNewtonWeight S p i₀ :=
        lt_of_le_of_ne (hmax k (by simpa [R] using hk)) hw
      exact (isLittleO_of_hasLogScaleExponent_lt huTopSub
        (hg k hk) (hg i₀ hi₀R) hlt).tendsto_div_nhds_zero
  have hsum : ∀ᶠ m : ℕ in atTop, ∑ k ∈ R.support, g k m = 0 := by
    have hrootSub := hns.tendsto_atTop.eventually hroot
    filter_upwards [hrootSub] with m hm
    have hm' : (strelitzJetCurveSpecialization S (u (ns m))).eval (root (ns m)) = 0 := hm
    rw [strelitzJetCurveSpecialization, Polynomial.eval_map,
      Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hm'
    simpa [R, q, g, eval_finOnePolynomial] using hm'
  have hne := eventually_finset_sum_ne_zero_of_dominant_div
    R.support g hi₀R hi₀ne hsmall
  exact (hsum.and hne).exists.elim fun _ h => h.2 h.1

/-- The smallest index on a maximal Newton face prevents normalized exact roots from collapsing to zero. -/
theorem not_tendsto_strelitzJetCurveNormalizedRoot_norm_zero
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
    {i₀ : ℕ} (hi₀ : i₀ ∈ (strelitzJetCurvePolynomial S).support)
    (hmax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p i₀)
    (hindex : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p i₀ → i₀ ≤ k) :
    ¬ Tendsto (fun m =>
      ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖) atTop (nhds 0) := by
  classical
  intro hzNorm
  let R := strelitzJetCurvePolynomial S
  let q : ℕ → Polynomial ℂ := fun k => finOnePolynomial (R.coeff k)
  let g : ℕ → ℕ → ℂ := fun k m => (q k).eval (u (ns m)) * root (ns m) ^ k
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  have huTopSub : Tendsto (fun m => ‖u (ns m)‖) atTop atTop :=
    huTop.comp hns.tendsto_atTop
  have huExp : HasLogScaleExponent atTop (fun m => ‖u (ns m)‖)
      (fun m => u (ns m)) 1 := hasLogScaleExponent_self_norm huTopSub
  have hroot0Sub : ∀ᶠ m : ℕ in atTop, root (ns m) ≠ 0 :=
    hns.tendsto_atTop.eventually hroot0
  have hrootExp : HasLogScaleExponent atTop (fun m => ‖u (ns m)‖)
      (fun m => root (ns m)) p := by
    exact ⟨hroot0Sub, by simpa [strelitzJetCurveRootLogSlope] using hslope⟩
  have hq : ∀ k ∈ R.support, q k ≠ 0 := by
    intro k hk
    exact finOnePolynomial_ne_zero (Polynomial.mem_support_iff.mp hk)
  have hg : ∀ k ∈ R.support,
      HasLogScaleExponent atTop (fun m => ‖u (ns m)‖) (g k)
        (strelitzJetCurveNewtonWeight S p k) := by
    intro k hk
    simpa [g, q, R, strelitzJetCurveNewtonWeight] using
      hasLogScaleExponent_newton_monomial huTopSub huExp hrootExp (hq k hk) k
  have hi₀R : i₀ ∈ R.support := by simpa [R] using hi₀
  have hi₀ne : ∀ᶠ m : ℕ in atTop, g i₀ m ≠ 0 := (hg i₀ hi₀R).1
  have hzZero : Tendsto (fun m =>
      strelitzJetCurveNormalizedRoot u root p (ns m)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hzNorm
  have hsmall : ∀ k ∈ R.support, k ≠ i₀ →
      Tendsto (fun m => g k m / g i₀ m) atTop (nhds 0) := by
    intro k hk hki
    by_cases hw : strelitzJetCurveNewtonWeight S p k =
        strelitzJetCurveNewtonWeight S p i₀
    · have hik : i₀ ≤ k := hindex k (by simpa [R] using hk) hw
      have hiklt : i₀ < k := lt_of_le_of_ne hik hki.symm
      have hAk := (tendsto_strelitzJetCurveCoefficient_div_norm_pow S hνTop hu k).comp
        hns.tendsto_atTop
      have hAi := (tendsto_strelitzJetCurveCoefficient_div_norm_pow S hνTop hu i₀).comp
        hns.tendsto_atTop
      have hlead : (q i₀).leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr (hq i₀ hi₀R)
      have hratio := hAk.div hAi hlead
      have hpow := hzZero.pow (k - i₀)
      have hdelta : k - i₀ ≠ 0 := (Nat.sub_pos_iff_lt.mpr hiklt).ne'
      have hpow0 : Tendsto (fun m =>
          (strelitzJetCurveNormalizedRoot u root p (ns m)) ^ (k - i₀))
          atTop (nhds 0) := by
        simpa [zero_pow hdelta] using hpow
      have hprod := hratio.mul hpow0
      have hprod0 : Tendsto (fun m =>
          (((q k).eval (u (ns m)) / ((‖u (ns m)‖ : ℂ) ^ (q k).natDegree)) /
            ((q i₀).eval (u (ns m)) / ((‖u (ns m)‖ : ℂ) ^ (q i₀).natDegree))) *
            (strelitzJetCurveNormalizedRoot u root p (ns m)) ^ (k - i₀))
          atTop (nhds 0) := by
        simpa [q, R] using hprod
      refine hprod0.congr' ?_
      filter_upwards [hi₀ne, huTopSub.eventually_gt_atTop 0, hroot0Sub] with m hgm hum hrm
      have hqi : (q i₀).eval (u (ns m)) ≠ 0 := by
        exact (mul_ne_zero_iff.mp hgm).1
      have hratioEq := strelitzNewtonMonomialRatio_of_ge
        (a := (q k).eval (u (ns m)))
        (d := (q k).natDegree) (e := (q i₀).natDegree)
        (k := k) (i := i₀) (p := p) hum hqi hrm hik hw
      simpa only [g, strelitzJetCurveNormalizedRoot] using hratioEq.symm
    · have hlt : strelitzJetCurveNewtonWeight S p k <
          strelitzJetCurveNewtonWeight S p i₀ :=
        lt_of_le_of_ne (hmax k (by simpa [R] using hk)) hw
      exact (isLittleO_of_hasLogScaleExponent_lt huTopSub
        (hg k hk) (hg i₀ hi₀R) hlt).tendsto_div_nhds_zero
  have hsum : ∀ᶠ m : ℕ in atTop, ∑ k ∈ R.support, g k m = 0 := by
    have hrootSub := hns.tendsto_atTop.eventually hroot
    filter_upwards [hrootSub] with m hm
    have hm' : (strelitzJetCurveSpecialization S (u (ns m))).eval (root (ns m)) = 0 := hm
    rw [strelitzJetCurveSpecialization, Polynomial.eval_map,
      Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hm'
    simpa [R, q, g, eval_finOnePolynomial] using hm'
  have hne := eventually_finset_sum_ne_zero_of_dominant_div
    R.support g hi₀R hi₀ne hsmall
  exact (hsum.and hne).exists.elim fun _ h => h.2 h.1

/-- Maximal-face dominance gives an eventual upper bound for normalized exact roots. -/
theorem exists_eventually_strelitzJetCurveNormalizedRoot_norm_le
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
    {i₀ : ℕ} (hi₀ : i₀ ∈ (strelitzJetCurvePolynomial S).support)
    (hmax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p i₀)
    (hindex : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p i₀ → k ≤ i₀) :
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ ≤ C := by
  by_contra hC
  push Not at hC
  obtain ⟨τ, hτ, hτTop⟩ :=
    exists_strictMono_tendsto_atTop_of_frequently_gt
      (fun m => ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖) hC
  have hcontra := not_tendsto_strelitzJetCurveNormalizedRoot_norm_atTop
    (ns := ns ∘ τ) (hns.comp hτ) hνTop hu hroot hroot0
    (hslope.comp hτ.tendsto_atTop) hi₀ hmax hindex
  apply hcontra
  simpa only [Function.comp_apply] using hτTop

/-- Minimal-face dominance gives an eventual positive lower bound for normalized exact roots. -/
theorem exists_eventually_strelitzJetCurveNormalizedRoot_norm_ge
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
    {i₀ : ℕ} (hi₀ : i₀ ∈ (strelitzJetCurvePolynomial S).support)
    (hmax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p i₀)
    (hindex : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p i₀ → i₀ ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c ≤ ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ := by
  by_contra hc
  push Not at hc
  obtain ⟨τ, hτ, hτZero⟩ :=
    exists_strictMono_tendsto_zero_of_frequently_lt
      (fun m => ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖)
      (fun _ => norm_nonneg _) hc
  have hcontra := not_tendsto_strelitzJetCurveNormalizedRoot_norm_zero
    (ns := ns ∘ τ) (hns.comp hτ) hνTop hu hroot hroot0
    (hslope.comp hτ.tendsto_atTop) hi₀ hmax hindex
  apply hcontra
  simpa only [Function.comp_apply] using hτZero

/-- The extreme indices of the finite maximal Newton face force the normalized root into one fixed
annulus. -/
theorem exists_eventually_strelitzJetCurveNormalizedRoot_mem_annulus
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
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c ≤ ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ ∧
        ‖strelitzJetCurveNormalizedRoot u root p (ns m)‖ ≤ C := by
  classical
  let face := (strelitzJetCurvePolynomial S).support.filter fun k =>
    strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p i
  have hiFace : i ∈ face := Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hface : face.Nonempty := ⟨i, hiFace⟩
  obtain ⟨iMax, hiMax, hMaxIndex⟩ := Finset.exists_max_image face id hface
  obtain ⟨iMin, hiMin, hMinIndex⟩ := Finset.exists_min_image face id hface
  have hiMaxSupport : iMax ∈ (strelitzJetCurvePolynomial S).support :=
    (Finset.mem_filter.mp hiMax).1
  have hiMinSupport : iMin ∈ (strelitzJetCurvePolynomial S).support :=
    (Finset.mem_filter.mp hiMin).1
  have hweightMax : strelitzJetCurveNewtonWeight S p iMax =
      strelitzJetCurveNewtonWeight S p i := (Finset.mem_filter.mp hiMax).2
  have hweightMin : strelitzJetCurveNewtonWeight S p iMin =
      strelitzJetCurveNewtonWeight S p i := (Finset.mem_filter.mp hiMin).2
  have hmaxWeightMax : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p iMax := by
    intro k hk
    rw [hweightMax]
    exact hmax k hk
  have hmaxWeightMin : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k ≤ strelitzJetCurveNewtonWeight S p iMin := by
    intro k hk
    rw [hweightMin]
    exact hmax k hk
  have hMaximalIndex : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p iMax →
        k ≤ iMax := by
    intro k hk hw
    apply hMaxIndex k
    exact Finset.mem_filter.mpr ⟨hk, by rw [hw, hweightMax]⟩
  have hMinimalIndex : ∀ k ∈ (strelitzJetCurvePolynomial S).support,
      strelitzJetCurveNewtonWeight S p k = strelitzJetCurveNewtonWeight S p iMin →
        iMin ≤ k := by
    intro k hk hw
    apply hMinIndex k
    exact Finset.mem_filter.mpr ⟨hk, by rw [hw, hweightMin]⟩
  obtain ⟨C, hC⟩ := exists_eventually_strelitzJetCurveNormalizedRoot_norm_le
    hns hνTop hu hroot hroot0 hslope hiMaxSupport hmaxWeightMax hMaximalIndex
  obtain ⟨c, hc, hcBound⟩ := exists_eventually_strelitzJetCurveNormalizedRoot_norm_ge
    hns hνTop hu hroot hroot0 hslope hiMinSupport hmaxWeightMin hMinimalIndex
  exact ⟨c, C, hc, hcBound.and hC⟩

end

end GaloisForLFunctions.HTGeometry

