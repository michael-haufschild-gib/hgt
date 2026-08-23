import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import Mathlib.Analysis.Calculus.Taylor

/-!
# Higher Löwner collision confluence

`[LEAN-PROVED] [NOVELTY UNVERIFIED]`

Finite-difference congruences of a positive Löwner kernel have an all-order collision limit.
For an analytic real germ `f`, the mixed order-`(p,q)` collision of its removable divided-slope
kernel converges to `f⁽ᵖ⁺ᑫ⁺¹⁾(X)/(p+q+1)!`.  The proof identifies every moving-kernel derivative
with a homogeneous geometric sum, then uses the exact binomial annihilation laws already present
in the corpus.  Entrywise convergence and closedness of the finite positive-semidefinite cone
give the matrix endpoint.

This file does not assert positivity of any particular Löwner kernel.
-/

open Filter Finset Set Topology Asymptotics
open scoped Matrix MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

lemma iteratedDeriv_affineLine_zero
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (u : ℝ) (n : ℕ) :
    iteratedDeriv n (fun h : ℝ => f (X + u * h)) 0 =
      u ^ n * iteratedDeriv n f X := by
  obtain ⟨p, hp⟩ := hf
  have hshift : HasFPowerSeriesAt (fun z : ℝ => f (X + z)) p 0 := by
    simpa [sub_neg_eq_add, add_comm] using hp.comp_sub (-X)
  let U : ℝ →L[ℝ] ℝ := u • ContinuousLinearMap.id ℝ ℝ
  have hscaled : HasFPowerSeriesAt
      ((fun z : ℝ => f (X + z)) ∘ U) (p.compContinuousLinearMap U) 0 := by
    have hshiftU : HasFPowerSeriesAt (fun z : ℝ => f (X + z)) p (U 0) := by
      simpa using hshift
    exact hshiftU.compContinuousLinearMap
  obtain ⟨r, hr⟩ := hscaled
  obtain ⟨s, hs⟩ := hp
  have hscaledDeriv := hr.factorial_smul (1 : ℝ) n
  have hbaseDeriv := hs.factorial_smul (1 : ℝ) n
  change n.factorial • ((p.compContinuousLinearMap U) n (fun _ => (1 : ℝ))) =
      iteratedDeriv n ((fun z : ℝ => f (X + z)) ∘ U) 0 at hscaledDeriv
  change n.factorial • (p n (fun _ => (1 : ℝ))) = iteratedDeriv n f X at hbaseDeriv
  simp only [nsmul_eq_mul] at hscaledDeriv hbaseDeriv
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply] at hscaledDeriv
  have hcoeff : p n (U ∘ (fun _ : Fin n => (1 : ℝ))) =
      u ^ n * p n (fun _ : Fin n => (1 : ℝ)) := by
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    simp only [Function.comp_apply, U, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one, Finset.prod_const,
      Finset.card_fin, one_pow, one_mul]
  rw [hcoeff] at hscaledDeriv
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  change iteratedDeriv n (fun h : ℝ => f (X + u * h)) 0 = _
  have hscaledDeriv' :
      (n.factorial : ℝ) * (u ^ n * p n (fun _ : Fin n => (1 : ℝ))) =
        iteratedDeriv n (fun h : ℝ => f (X + u * h)) 0 := by
    simpa [Function.comp_def, U] using hscaledDeriv
  rw [← hscaledDeriv', ← hbaseDeriv]
  ring

def movingDslope (f : ℝ → ℝ) (X u v h : ℝ) : ℝ :=
  dslope f (X + u * h) (X + v * h)

lemma iteratedDeriv_movingDslope_zero
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X)
    (u v : ℝ) (n : ℕ) :
    iteratedDeriv n (movingDslope f X u v) 0 =
      (iteratedDeriv (n + 1) f X / (n + 1 : ℝ)) *
        ∑ a ∈ Finset.range (n + 1), u ^ a * v ^ (n - a) := by
  have hu : AnalyticAt ℝ (fun h : ℝ => f (X + u * h)) 0 := by
    have hf' : AnalyticAt ℝ f (X + u * 0) := by simpa using hf
    have hinner : AnalyticAt ℝ (fun h : ℝ => X + u * h) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact AnalyticAt.comp (x := (0 : ℝ)) (g := f)
      (f := fun h : ℝ => X + u * h) hf' hinner
  have hv : AnalyticAt ℝ (fun h : ℝ => f (X + v * h)) 0 := by
    have hf' : AnalyticAt ℝ f (X + v * 0) := by simpa using hf
    have hinner : AnalyticAt ℝ (fun h : ℝ => X + v * h) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact AnalyticAt.comp (x := (0 : ℝ)) (g := f)
      (f := fun h : ℝ => X + v * h) hf' hinner
  by_cases huv : u = v
  · subst v
    have hcurve : movingDslope f X u u = fun h : ℝ => deriv f (X + u * h) := by
      funext h
      simp [movingDslope]
    rw [hcurve, iteratedDeriv_affineLine_zero hf.deriv u n,
      ← congrFun (iteratedDeriv_succ' (n := n) (f := f)) X]
    have hsum :
        (∑ a ∈ Finset.range (n + 1), u ^ a * u ^ (n - a)) =
          (n + 1 : ℝ) * u ^ n := by
      simpa using (geom_sum₂_self u (n + 1))
    rw [hsum]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  · let g : ℝ → ℝ := fun h => f (X + v * h) - f (X + u * h)
    have hg : AnalyticAt ℝ g 0 := hv.sub hu
    have hgderiv (m : ℕ) :
        iteratedDeriv m g 0 =
          (v ^ m - u ^ m) * iteratedDeriv m f X := by
      rw [show iteratedDeriv m g 0 =
          iteratedDeriv m (fun h : ℝ => f (X + v * h)) 0 -
            iteratedDeriv m (fun h : ℝ => f (X + u * h)) 0 by
        exact iteratedDeriv_sub hv.contDiffAt hu.contDiffAt]
      rw [iteratedDeriv_affineLine_zero hf v m,
        iteratedDeriv_affineLine_zero hf u m]
      ring
    have hcurve : movingDslope f X u v = fun h : ℝ => dslope g 0 h / (v - u) := by
      funext h
      by_cases hh : h = 0
      · subst h
        rw [movingDslope]
        simp only [mul_zero, add_zero]
        rw [dslope_same, dslope_same]
        have hg1 := hgderiv 1
        rw [iteratedDeriv_one, iteratedDeriv_one] at hg1
        rw [hg1]
        simp only [pow_one]
        have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
        field_simp [hvu]
      · have hp : X + v * h ≠ X + u * h := by
          intro heq
          apply huv
          apply mul_right_cancel₀ hh
          linarith
        rw [movingDslope, dslope_of_ne _ hp, dslope_of_ne _ hh,
          slope_def_module, slope_def_module]
        dsimp [g]
        have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
        rw [show X + v * h - (X + u * h) = (v - u) * h by ring]
        simp only [mul_zero, add_zero, sub_self, sub_zero]
        change (((v - u) * h)⁻¹ *
            (f (X + v * h) - f (X + u * h))) =
          (h⁻¹ * (f (X + v * h) - f (X + u * h))) / (v - u)
        field_simp [hh, hvu]
    rw [hcurve, iteratedDeriv_div_const,
      HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hg n,
      hgderiv (n + 1)]
    have hgeom :
        (v ^ (n + 1) - u ^ (n + 1)) / (v - u) =
          ∑ a ∈ Finset.range (n + 1), u ^ a * v ^ (n - a) := by
      have h := (Commute.geom_sum₂ (Commute.all u v) huv (n + 1)).symm
      calc
        (v ^ (n + 1) - u ^ (n + 1)) / (v - u) =
            (u ^ (n + 1) - v ^ (n + 1)) / (u - v) := by
              field_simp [sub_ne_zero.mpr huv, sub_ne_zero.mpr (Ne.symm huv)]
              ring
        _ = ∑ a ∈ Finset.range (n + 1), u ^ a * v ^ (n + 1 - 1 - a) := h
        _ = ∑ a ∈ Finset.range (n + 1), u ^ a * v ^ (n - a) := by
          apply Finset.sum_congr rfl
          intro a ha
          congr 2
    rw [show (v ^ (n + 1) - u ^ (n + 1)) * iteratedDeriv (n + 1) f X /
          (n + 1 : ℝ) / (v - u) =
        (iteratedDeriv (n + 1) f X / (n + 1 : ℝ)) *
          ((v ^ (n + 1) - u ^ (n + 1)) / (v - u)) by ring,
      hgeom]

lemma analyticAt_movingDslope_zero
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (u v : ℝ) :
    AnalyticAt ℝ (movingDslope f X u v) 0 := by
  have haffine (w : ℝ) : AnalyticAt ℝ (fun h : ℝ => f (X + w * h)) 0 := by
    have hf' : AnalyticAt ℝ f (X + w * 0) := by simpa using hf
    have hinner : AnalyticAt ℝ (fun h : ℝ => X + w * h) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact AnalyticAt.comp (x := (0 : ℝ)) (g := f)
      (f := fun h : ℝ => X + w * h) hf' hinner
  by_cases huv : u = v
  · subst v
    have hcurve : movingDslope f X u u = fun h : ℝ => deriv f (X + u * h) := by
      funext h
      simp [movingDslope]
    rw [hcurve]
    have hf' : AnalyticAt ℝ (deriv f) (X + u * 0) := by simpa using hf.deriv
    have hinner : AnalyticAt ℝ (fun h : ℝ => X + u * h) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact AnalyticAt.comp (x := (0 : ℝ)) (g := deriv f)
      (f := fun h : ℝ => X + u * h) hf' hinner
  · let g : ℝ → ℝ := fun h => f (X + v * h) - f (X + u * h)
    have hg : AnalyticAt ℝ g 0 := (haffine v).sub (haffine u)
    have hgderiv : deriv g 0 = (v - u) * deriv f X := by
      have h := iteratedDeriv_sub (n := 1) (x := (0 : ℝ))
        (haffine v).contDiffAt (haffine u).contDiffAt
      have hv := iteratedDeriv_affineLine_zero hf v 1
      have hu := iteratedDeriv_affineLine_zero hf u 1
      rw [iteratedDeriv_one, iteratedDeriv_one] at h hv hu
      change deriv ((fun h : ℝ => f (X + v * h)) -
        (fun h : ℝ => f (X + u * h))) 0 = _
      rw [h, iteratedDeriv_one, hv, hu]
      ring
    have hcurve : movingDslope f X u v = fun h : ℝ => dslope g 0 h / (v - u) := by
      funext h
      by_cases hh : h = 0
      · subst h
        rw [movingDslope]
        simp only [mul_zero, add_zero]
        rw [dslope_same, dslope_same, hgderiv]
        have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
        field_simp [hvu]
      · have hp : X + v * h ≠ X + u * h := by
          intro heq
          apply huv
          apply mul_right_cancel₀ hh
          linarith
        rw [movingDslope, dslope_of_ne _ hp, dslope_of_ne _ hh,
          slope_def_module, slope_def_module]
        dsimp [g]
        have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
        rw [show X + v * h - (X + u * h) = (v - u) * h by ring]
        simp only [mul_zero, add_zero, sub_self, sub_zero]
        change (((v - u) * h)⁻¹ *
            (f (X + v * h) - f (X + u * h))) =
          (h⁻¹ * (f (X + v * h) - f (X + u * h))) / (v - u)
        field_simp [hh, hvu]
    rw [hcurve]
    obtain ⟨p, hp⟩ := hg
    exact hp.has_fpower_series_dslope_fslope.analyticAt.div_const

theorem tendsto_div_pow_of_analyticAt_flat
    {f : ℝ → ℝ} {n : ℕ} (hf : AnalyticAt ℝ f 0)
    (hflat : ∀ k < n, iteratedDeriv k f 0 = 0) :
    Tendsto (fun h : ℝ => f h / h ^ n) (nhdsWithin 0 {0}ᶜ)
      (nhds (iteratedDeriv n f 0 / (n.factorial : ℝ))) := by
  obtain ⟨r, hr, han⟩ := hf.exists_ball_analyticOnNhd
  let d : ℝ := r / 2
  let s : Set ℝ := Set.Icc (-d) d
  have hd : 0 < d := by dsimp [d]; linarith
  have hsconv : Convex ℝ s := convex_Icc _ _
  have hzero : (0 : ℝ) ∈ s := by simp [s, hd.le]
  have hsball : s ⊆ Metric.ball (0 : ℝ) r := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_0_eq_abs]
    have hx' : -d ≤ x ∧ x ≤ d := hx
    have habs : |x| ≤ d := abs_le.mpr hx'
    dsimp [d] at habs
    linarith
  have hcont : ContDiffOn ℝ n f s := by
    intro x hx
    exact (han x (hsball hx)).contDiffAt.contDiffWithinAt
  have hIcc : s ∈ 𝓝 (0 : ℝ) := by
    exact Icc_mem_nhds (by simpa [s] using neg_lt_zero.mpr hd) (by simpa [s] using hd)
  have hwithin (k : ℕ) :
      iteratedDerivWithin k f s 0 = iteratedDeriv k f 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by linarith))
      (hf.contDiffAt.of_le le_top) hzero
  have htaylorExact (h : ℝ) :
      taylorWithinEval f n s 0 h =
        (iteratedDeriv n f 0 / (n.factorial : ℝ)) * h ^ n := by
    rw [taylor_within_apply]
    simp_rw [hwithin, sub_zero, smul_eq_mul]
    calc
      (∑ k ∈ Finset.range (n + 1),
          (k.factorial : ℝ)⁻¹ * h ^ k * iteratedDeriv k f 0) =
          (n.factorial : ℝ)⁻¹ * h ^ n * iteratedDeriv n f 0 := by
        apply Finset.sum_eq_single n
        · intro k hk hkn
          have hklt : k < n := lt_of_le_of_ne
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn
          rw [hflat k hklt]
          ring
        · simp
      _ = (iteratedDeriv n f 0 / (n.factorial : ℝ)) * h ^ n := by ring
  have htaylor := Real.taylor_tendsto hsconv hzero hcont
  rw [show nhdsWithin (0 : ℝ) s = 𝓝 0 by
    rw [nhdsWithin, inf_eq_left]
    exact le_principal_iff.mpr hIcc] at htaylor
  simp_rw [sub_zero, htaylorExact] at htaylor
  have hlim : Tendsto (fun h : ℝ =>
      iteratedDeriv n f 0 / (n.factorial : ℝ) +
        (f h - (iteratedDeriv n f 0 / (n.factorial : ℝ)) * h ^ n) / h ^ n)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (iteratedDeriv n f 0 / (n.factorial : ℝ))) := by
    have htaylor' := htaylor.mono_left
      (show nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [add_zero] using tendsto_const_nhds.add htaylor'
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  field_simp [pow_ne_zero n hh0]
  ring

def finiteDifferenceWeight (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)

def mixedMovingDslopeDifference
    (f : ℝ → ℝ) (X : ℝ) (p q : ℕ) (h : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
    finiteDifferenceWeight p i * finiteDifferenceWeight q j *
      movingDslope f X (i : ℝ) (j : ℝ) h

lemma analyticAt_mixedMovingDslopeDifference
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (p q : ℕ) :
    AnalyticAt ℝ (mixedMovingDslopeDifference f X p q) 0 := by
  have hsum : AnalyticAt ℝ
      (∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        fun h : ℝ => finiteDifferenceWeight p i * finiteDifferenceWeight q j *
          movingDslope f X (i : ℝ) (j : ℝ) h) 0 := by
    apply Finset.analyticAt_sum
    intro i hi
    apply Finset.analyticAt_sum
    intro j hj
    exact analyticAt_const.mul
      (analyticAt_movingDslope_zero hf (i : ℝ) (j : ℝ))
  change AnalyticAt ℝ (fun h : ℝ =>
    ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
      finiteDifferenceWeight p i * finiteDifferenceWeight q j *
        movingDslope f X (i : ℝ) (j : ℝ) h) 0
  simpa [Finset.sum_fn] using hsum

private lemma sum_sum_sum_rotate
    {α β γ M : Type*} [AddCommMonoid M]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → M) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c) =
      ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  calc
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, F a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := Finset.sum_comm

lemma iteratedDeriv_mixedMovingDslopeDifference_zero
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X)
    (p q r : ℕ) :
    iteratedDeriv r (mixedMovingDslopeDifference f X p q) 0 =
      (iteratedDeriv (r + 1) f X / (r + 1 : ℝ)) *
        ∑ a ∈ Finset.range (r + 1),
          (∑ i ∈ Finset.range (p + 1), finiteDifferenceWeight p i * (i : ℝ) ^ a) *
          (∑ j ∈ Finset.range (q + 1), finiteDifferenceWeight q j * (j : ℝ) ^ (r - a)) := by
  have hana (i j : ℕ) :
      AnalyticAt ℝ (fun h : ℝ => finiteDifferenceWeight p i * finiteDifferenceWeight q j *
        movingDslope f X (i : ℝ) (j : ℝ) h) 0 :=
    analyticAt_const.mul (analyticAt_movingDslope_zero hf (i : ℝ) (j : ℝ))
  change iteratedDeriv r (fun h : ℝ =>
    ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
      finiteDifferenceWeight p i * finiteDifferenceWeight q j *
        movingDslope f X (i : ℝ) (j : ℝ) h) 0 = _
  rw [show (fun h : ℝ =>
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        finiteDifferenceWeight p i * finiteDifferenceWeight q j *
          movingDslope f X (i : ℝ) (j : ℝ) h) =
      ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        fun h : ℝ => finiteDifferenceWeight p i * finiteDifferenceWeight q j *
          movingDslope f X (i : ℝ) (j : ℝ) h by
        funext h
        simp]
  rw [iteratedDeriv_sum (fun i hi =>
      (Finset.analyticAt_sum _ fun j hj => hana i j).contDiffAt)]
  simp_rw [iteratedDeriv_sum (fun j hj => (hana _ j).contDiffAt),
    iteratedDeriv_const_mul_field,
    iteratedDeriv_movingDslope_zero hf]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [sum_sum_sum_rotate]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteDifferenceWeight_moment_eq_zero
    {a n : ℕ} (h : a < n) :
    ∑ k ∈ Finset.range (n + 1),
      finiteDifferenceWeight n k * (k : ℝ) ^ a = 0 := by
  simpa [finiteDifferenceWeight] using
    (alternating_binomial_sum_pow_eq_zero (R := ℝ) h)

lemma finiteDifferenceWeight_moment_eq_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      finiteDifferenceWeight n k * (k : ℝ) ^ n = (n.factorial : ℝ) := by
  simpa [finiteDifferenceWeight] using
    (alternating_binomial_sum_pow_eq_factorial (R := ℝ) (n := n))

lemma iteratedDeriv_mixedMovingDslopeDifference_zero_of_lt
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X)
    {p q r : ℕ} (hr : r < p + q) :
    iteratedDeriv r (mixedMovingDslopeDifference f X p q) 0 = 0 := by
  rw [iteratedDeriv_mixedMovingDslopeDifference_zero hf]
  suffices hsum :
      (∑ a ∈ Finset.range (r + 1),
        (∑ i ∈ Finset.range (p + 1), finiteDifferenceWeight p i * (i : ℝ) ^ a) *
        (∑ j ∈ Finset.range (q + 1), finiteDifferenceWeight q j * (j : ℝ) ^ (r - a))) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro a ha
  have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  by_cases hap : a < p
  · rw [finiteDifferenceWeight_moment_eq_zero hap, zero_mul]
  · have hq : r - a < q := by omega
    rw [finiteDifferenceWeight_moment_eq_zero hq, mul_zero]

lemma iteratedDeriv_mixedMovingDslopeDifference_add
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (p q : ℕ) :
    iteratedDeriv (p + q) (mixedMovingDslopeDifference f X p q) 0 =
      (iteratedDeriv (p + q + 1) f X / (p + q + 1 : ℝ)) *
        (p.factorial : ℝ) * (q.factorial : ℝ) := by
  rw [iteratedDeriv_mixedMovingDslopeDifference_zero hf]
  have hsum :
      (∑ a ∈ Finset.range (p + q + 1),
        (∑ i ∈ Finset.range (p + 1), finiteDifferenceWeight p i * (i : ℝ) ^ a) *
        (∑ j ∈ Finset.range (q + 1), finiteDifferenceWeight q j *
          (j : ℝ) ^ (p + q - a))) =
        (p.factorial : ℝ) * (q.factorial : ℝ) := by
    calc
      (∑ a ∈ Finset.range (p + q + 1),
        (∑ i ∈ Finset.range (p + 1), finiteDifferenceWeight p i * (i : ℝ) ^ a) *
        (∑ j ∈ Finset.range (q + 1), finiteDifferenceWeight q j *
          (j : ℝ) ^ (p + q - a))) =
          (∑ i ∈ Finset.range (p + 1), finiteDifferenceWeight p i * (i : ℝ) ^ p) *
          (∑ j ∈ Finset.range (q + 1), finiteDifferenceWeight q j *
            (j : ℝ) ^ (p + q - p)) := by
        apply Finset.sum_eq_single p
        · intro a ha hap
          have haM : a ≤ p + q := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          by_cases halt : a < p
          · rw [finiteDifferenceWeight_moment_eq_zero halt, zero_mul]
          · have hpalt : p < a := lt_of_le_of_ne (Nat.le_of_not_gt halt) (Ne.symm hap)
            have hq : p + q - a < q := by omega
            rw [finiteDifferenceWeight_moment_eq_zero hq, mul_zero]
        · simp
      _ = (p.factorial : ℝ) * (q.factorial : ℝ) := by
        have hsub : p + q - p = q := by omega
        rw [hsub, finiteDifferenceWeight_moment_eq_factorial,
          finiteDifferenceWeight_moment_eq_factorial]
  rw [hsum]
  push_cast
  ring

def normalizedMixedMovingDslopeDifference
    (f : ℝ → ℝ) (X : ℝ) (p q : ℕ) (h : ℝ) : ℝ :=
  mixedMovingDslopeDifference f X p q h /
    ((p.factorial : ℝ) * (q.factorial : ℝ) * h ^ (p + q))

theorem tendsto_normalizedMixedMovingDslopeDifference
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (p q : ℕ) :
    Tendsto (normalizedMixedMovingDslopeDifference f X p q)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (iteratedDeriv (p + q + 1) f X /
        ((p + q + 1).factorial : ℝ))) := by
  have hflat : ∀ r < p + q,
      iteratedDeriv r (mixedMovingDslopeDifference f X p q) 0 = 0 :=
    fun r hr => iteratedDeriv_mixedMovingDslopeDifference_zero_of_lt hf hr
  have hlim := tendsto_div_pow_of_analyticAt_flat
    (analyticAt_mixedMovingDslopeDifference hf p q) hflat
  have hfacp : (p.factorial : ℝ) ≠ 0 := by positivity
  have hfacq : (q.factorial : ℝ) ≠ 0 := by positivity
  have hfacM : ((p + q).factorial : ℝ) ≠ 0 := by positivity
  have htop := iteratedDeriv_mixedMovingDslopeDifference_add hf p q
  have hlim' := hlim.div_const ((p.factorial : ℝ) * (q.factorial : ℝ))
  convert hlim' using 1
  · funext h
    rw [normalizedMixedMovingDslopeDifference]
    field_simp [hfacp, hfacq]
  · rw [htop]
    push_cast [Nat.factorial_succ]
    field_simp [hfacp, hfacq, hfacM]

def normalizedMovingDslopeMatrix
    (f : ℝ → ℝ) (X : ℝ) (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => normalizedMixedMovingDslopeDifference f X i j h

def normalizedLoewnerJetMatrix
    (f : ℝ → ℝ) (X : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => iteratedDeriv ((i : ℕ) + (j : ℕ) + 1) f X /
    (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ)

theorem tendsto_normalizedMovingDslopeMatrix
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (N : ℕ) :
    Tendsto (normalizedMovingDslopeMatrix f X N)
      (nhdsWithin 0 {0}ᶜ) (nhds (normalizedLoewnerJetMatrix f X N)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact tendsto_normalizedMixedMovingDslopeDifference hf i j

theorem normalizedLoewnerJetMatrix_posSemidef_of_eventually_collision
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (N : ℕ)
    (hpos : ∀ᶠ h in nhdsWithin 0 {0}ᶜ,
      (normalizedMovingDslopeMatrix f X N h).PosSemidef) :
    (normalizedLoewnerJetMatrix f X N).PosSemidef := by
  exact GaloisForLFunctions.HilbertMetric.Matrix.PosSemidef.of_tendsto hpos
    (tendsto_normalizedMovingDslopeMatrix hf N)

/-! ## Finite-difference congruence -/

private lemma sum_fin_prefix {N : ℕ} (p : Fin N) (F : ℕ → ℝ) :
    (∑ k : Fin N, if (k : ℕ) ≤ (p : ℕ) then F k else 0) =
      ∑ k ∈ Finset.range ((p : ℕ) + 1), F k := by
  change (∑ k : Fin N,
    (fun m : ℕ => if m ≤ (p : ℕ) then F m else 0) k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun m : ℕ => if m ≤ (p : ℕ) then F m else 0) N]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Löwner divided-slope matrix on the uniform collision nodes `X + i h`. -/
def uniformMovingDslopeMatrix
    (f : ℝ → ℝ) (X : ℝ) (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => movingDslope f X i j h

/-- Lower-triangular normalized finite-difference transform. -/
def normalizedDifferenceTransform (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun p k => if (k : ℕ) ≤ (p : ℕ) then
    finiteDifferenceWeight p k / ((((p : ℕ).factorial : ℕ) : ℝ) * h ^ (p : ℕ))
  else 0

/-- The mixed finite-difference matrix is exactly a congruence of the original Löwner matrix.
This algebraic identity is the positivity-preserving core of arbitrary-order confluence. -/
theorem normalizedMovingDslopeMatrix_eq_congruence
    (f : ℝ → ℝ) (X : ℝ) (N : ℕ) {h : ℝ} (hh : h ≠ 0) :
    normalizedMovingDslopeMatrix f X N h =
      normalizedDifferenceTransform N h * uniformMovingDslopeMatrix f X N h *
        (normalizedDifferenceTransform N h)ᴴ := by
  ext p q
  simp only [normalizedMovingDslopeMatrix, normalizedMixedMovingDslopeDifference,
    mixedMovingDslopeDifference, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_id_of_comm, normalizedDifferenceTransform, uniformMovingDslopeMatrix]
  have hinner (l : Fin N) :
      (∑ k : Fin N,
        (if (k : ℕ) ≤ (p : ℕ) then
          finiteDifferenceWeight p k /
            (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ))
        else 0) * movingDslope f X k l h) =
      ∑ k ∈ Finset.range ((p : ℕ) + 1),
        (finiteDifferenceWeight p k /
          (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ))) *
            movingDslope f X k l h := by
    rw [show (∑ k : Fin N,
        (if (k : ℕ) ≤ (p : ℕ) then
          finiteDifferenceWeight p k /
            (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ))
        else 0) * movingDslope f X k l h) =
      ∑ k : Fin N, if (k : ℕ) ≤ (p : ℕ) then
        (finiteDifferenceWeight p k /
          (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ))) *
            movingDslope f X k l h else 0 by
          apply Finset.sum_congr rfl
          intro k hk
          split <;> simp_all]
    exact sum_fin_prefix p (fun k =>
      (finiteDifferenceWeight p k /
        (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ))) *
          movingDslope f X k l h)
  simp_rw [hinner]
  rw [show (∑ l : Fin N,
      (∑ k ∈ Finset.range ((p : ℕ) + 1),
        finiteDifferenceWeight p k /
          (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ)) *
            movingDslope f X (k : ℝ) l h) *
        (if (l : ℕ) ≤ (q : ℕ) then
          finiteDifferenceWeight q l /
            (((q : ℕ).factorial : ℝ) * h ^ (q : ℕ)) else 0)) =
      ∑ l : Fin N, if (l : ℕ) ≤ (q : ℕ) then
        (∑ k ∈ Finset.range ((p : ℕ) + 1),
          finiteDifferenceWeight p k /
            (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ)) *
              movingDslope f X (k : ℝ) l h) *
          (finiteDifferenceWeight q l /
            (((q : ℕ).factorial : ℝ) * h ^ (q : ℕ))) else 0 by
        apply Finset.sum_congr rfl
        intro l hl
        split <;> simp_all]
  rw [sum_fin_prefix q (fun l =>
    (∑ k ∈ Finset.range ((p : ℕ) + 1),
      finiteDifferenceWeight p k /
        (((p : ℕ).factorial : ℝ) * h ^ (p : ℕ)) *
          movingDslope f X (k : ℝ) (l : ℝ) h) *
      (finiteDifferenceWeight q l /
        (((q : ℕ).factorial : ℝ) * h ^ (q : ℕ))))]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_div]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hfacp : ((p : ℕ).factorial : ℝ) ≠ 0 := by positivity
  have hfacq : ((q : ℕ).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfacp, hfacq, hh, pow_add]
  ring

/-- Finite-difference confluence preserves positive semidefiniteness at every nonzero scale. -/
theorem normalizedMovingDslopeMatrix_posSemidef_of_uniform
    (f : ℝ → ℝ) (X : ℝ) (N : ℕ) {h : ℝ} (hh : h ≠ 0)
    (hpos : (uniformMovingDslopeMatrix f X N h).PosSemidef) :
    (normalizedMovingDslopeMatrix f X N h).PosSemidef := by
  rw [normalizedMovingDslopeMatrix_eq_congruence f X N hh]
  exact hpos.mul_mul_conjTranspose_same (normalizedDifferenceTransform N h)

/-- Eventual positivity of uniform finite Löwner matrices forces positivity of the full diagonal
jet matrix.  No invertibility or condition-number bound for the difference transform is needed. -/
theorem normalizedLoewnerJetMatrix_posSemidef_of_eventually_uniform
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (N : ℕ)
    (hpos : ∀ᶠ h in nhdsWithin 0 {0}ᶜ,
      (uniformMovingDslopeMatrix f X N h).PosSemidef) :
    (normalizedLoewnerJetMatrix f X N).PosSemidef := by
  apply normalizedLoewnerJetMatrix_posSemidef_of_eventually_collision hf N
  filter_upwards [hpos, self_mem_nhdsWithin] with h hmatrix hh
  exact normalizedMovingDslopeMatrix_posSemidef_of_uniform f X N
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh) hmatrix

end


end GaloisForLFunctions.HTGeometry
