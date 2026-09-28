import GaloisForLFunctions.RHTower.ThetaDerivativePacketLogConcavity

/-!
# All-order derivative moderation on the theta tail

For a smooth positive `h`, the derivative ratios `ρ_j = h^{(j)}/h` satisfy
`ρ_j' = ρ_{j+1} - ρ_j ρ_1`, so by strong induction and the Leibniz rule every derivative of every
`ρ_j` is moderate (at most a power of `q = π e^{2x}` on the tail) once the `ρ_j` are; the same then
holds for every derivative of positive order of `log h`. This applies to the literal source `k`
and to every deformation `k_t = k + t k^{(4m)}` with `t ≥ 0`, hence to all derivatives of
`L = log k_t - log k`.

On the tail, uniformly in `t ≥ 0`, `(log k_t)'' ≤ -4π e^{2x} + (8m)² + 2`; also
`(log k)'' ≤ -4π e^{2x} + 1`, `|L'| ≤ 8m + 1`, and `L ≤ ε π e^{2x}` for every `ε > 0`.
-/
open Filter Topology Set
open scoped ContDiff

namespace RHTower

noncomputable section

theorem ThetaTailModerate.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, ThetaTailModerate (f i)) :
    ThetaTailModerate (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ThetaTailModerate.const 0
  | insert a s ha ih =>
      have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
      exact (h1.add h2).congr' (Eventually.of_forall fun x => by
        simp only [Finset.sum_insert ha])

/-! ## Derivatives of logarithmic ratios -/

section Ratio

variable {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hpos : ∀ x, 0 < h x)
include hh hpos

/-- The derivative ratio `ρ_j = h^{(j)}/h` satisfies `ρ_j' = ρ_{j+1} - ρ_j ρ_1`. -/
theorem deriv_iteratedDeriv_div (j : ℕ) :
    deriv (fun x => iteratedDeriv j h x / h x) =
      fun x => iteratedDeriv (j + 1) h x / h x -
        iteratedDeriv j h x / h x * (iteratedDeriv 1 h x / h x) := by
  funext x
  have hd : ∀ i, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h x) x := by
    intro i
    have hi : ContDiff ℝ ∞ (iteratedDeriv i h) := by
      rw [iteratedDeriv_eq_iterate]; exact hh.iterate_deriv i
    have hdiff : Differentiable ℝ (iteratedDeriv i h) := hi.differentiable (by norm_num)
    rw [iteratedDeriv_succ]
    exact (hdiff x).hasDerivAt
  have h0 : HasDerivAt h (iteratedDeriv 1 h x) x := by
    have := hd 0
    rwa [iteratedDeriv_zero] at this
  show deriv (iteratedDeriv j h / h) x = _
  rw [((hd j).div h0 (hpos x).ne').deriv]
  have := (hpos x).ne'
  field_simp

theorem contDiff_iteratedDeriv_div (j : ℕ) :
    ContDiff ℝ ∞ (fun x => iteratedDeriv j h x / h x) := by
  have h1 : ContDiff ℝ ∞ (iteratedDeriv j h) := by
    rw [iteratedDeriv_eq_iterate]; exact hh.iterate_deriv j
  exact h1.div hh fun x => (hpos x).ne'

/-- **All derivatives of the derivative ratios are moderate** once the ratios themselves are:
`ρ_j^{(n+1)} = ρ_{j+1}^{(n)} - Σ binom(n,a) ρ_j^{(a)} ρ_1^{(n-a)}`. -/
theorem thetaTailModerate_iteratedDeriv_ratio
    (hmod : ∀ j, ThetaTailModerate (fun x => iteratedDeriv j h x / h x)) (n j : ℕ) :
    ThetaTailModerate (iteratedDeriv n (fun x => iteratedDeriv j h x / h x)) := by
  induction n using Nat.strong_induction_on generalizing j with
  | _ n ih =>
    rcases n with _ | n
    · simpa using hmod j
    · have hcd := contDiff_iteratedDeriv_div hh hpos
      have hfun : iteratedDeriv (n + 1) (fun x => iteratedDeriv j h x / h x) =
          fun x => iteratedDeriv n (fun x => iteratedDeriv (j + 1) h x / h x) x -
            ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) *
              iteratedDeriv a (fun x => iteratedDeriv j h x / h x) x *
                iteratedDeriv (n - a) (fun x => iteratedDeriv 1 h x / h x) x := by
        rw [iteratedDeriv_succ', deriv_iteratedDeriv_div hh hpos]
        funext x
        have hsub : (fun x => iteratedDeriv (j + 1) h x / h x -
            iteratedDeriv j h x / h x * (iteratedDeriv 1 h x / h x)) =
            (fun x => iteratedDeriv (j + 1) h x / h x) -
              ((fun x => iteratedDeriv j h x / h x) * fun x => iteratedDeriv 1 h x / h x) := rfl
        rw [hsub, iteratedDeriv_sub (f := fun x => iteratedDeriv (j + 1) h x / h x)
          (g := (fun x => iteratedDeriv j h x / h x) * fun x => iteratedDeriv 1 h x / h x)
          ((hcd (j + 1)).contDiffAt.of_le (by exact_mod_cast le_top))
          (((hcd j).mul (hcd 1)).contDiffAt.of_le (by exact_mod_cast le_top)),
          iteratedDeriv_mul ((hcd j).contDiffAt.of_le (by exact_mod_cast le_top))
            ((hcd 1).contDiffAt.of_le (by exact_mod_cast le_top))]
      rw [hfun]
      refine (ih n (Nat.lt_succ_self n) (j + 1)).sub
        (ThetaTailModerate.finset_sum _ fun a ha => ?_)
      have ha' := Finset.mem_range.1 ha
      exact ((ThetaTailModerate.const _).mul (ih a (by omega) j)).mul
        (ih (n - a) (by omega) 1)

theorem iteratedDeriv_succ_log (n : ℕ) :
    iteratedDeriv (n + 1) (fun x => Real.log (h x)) =
      iteratedDeriv n (fun x => iteratedDeriv 1 h x / h x) := by
  rw [iteratedDeriv_succ']
  congr 1
  funext x
  have hd : HasDerivAt h (iteratedDeriv 1 h x) x := by
    have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
    rw [iteratedDeriv_one]
    exact (hdiff x).hasDerivAt
  exact (hd.log (hpos x).ne').deriv

/-- Every derivative of positive order of `log h` is moderate. -/
theorem thetaTailModerate_iteratedDeriv_log
    (hmod : ∀ j, ThetaTailModerate (fun x => iteratedDeriv j h x / h x)) (n : ℕ) :
    ThetaTailModerate (iteratedDeriv (n + 1) (fun x => Real.log (h x))) := by
  rw [iteratedDeriv_succ_log hh hpos]
  exact thetaTailModerate_iteratedDeriv_ratio hh hpos hmod n 1

end Ratio

/-! ## The literal source and its deformations -/

theorem thetaTailModerate_iteratedDeriv_thetaSourceRatio (n j : ℕ) :
    ThetaTailModerate (iteratedDeriv n (thetaSourceRatio j)) :=
  thetaTailModerate_iteratedDeriv_ratio contDiff_thetaCuspFullSource thetaCuspFullSource_pos_all
    thetaSourceRatio_moderate n j

theorem thetaDerivativePacket_ratio_eq (m : ℕ) (t : ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (thetaDerivativePacket m t) x / thetaDerivativePacket m t x =
      (thetaSourceRatio j x + t * thetaSourceRatio (j + 4 * m) x) /
        (1 + t * thetaSourceRatio (4 * m) x) := by
  have hk := (thetaCuspFullSource_pos_all x).ne'
  rw [iteratedDeriv_thetaDerivativePacket]
  simp only [thetaSourceRatio, thetaDerivativePacket]
  by_cases h : thetaCuspFullSource x + t * iteratedDeriv (4 * m) thetaCuspFullSource x = 0
  · have h' : 1 + t * (iteratedDeriv (4 * m) thetaCuspFullSource x / thetaCuspFullSource x) = 0 := by
      field_simp; linarith
    rw [h, h', div_zero, div_zero]
  · have h' : 1 + t * (iteratedDeriv (4 * m) thetaCuspFullSource x / thetaCuspFullSource x) ≠ 0 := by
      intro h''; apply h; field_simp at h''; linarith
    field_simp

/-- The derivative ratios of `k_t` are moderate for every `t ≥ 0`. -/
theorem thetaDerivativePacket_ratio_moderate (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    ThetaTailModerate (fun x => iteratedDeriv j (thetaDerivativePacket m t) x /
      thetaDerivativePacket m t x) := by
  have hden : ThetaTailModerate (fun x => (1 + t * thetaSourceRatio (4 * m) x)⁻¹) := by
    refine ThetaTailModerate.inv_of_ge one_pos ?_
    filter_upwards [eventually_half_le_thetaSourceRatio m hm] with x hx
    nlinarith
  have hnum := (thetaSourceRatio_moderate j).add
    ((ThetaTailModerate.const t).mul (thetaSourceRatio_moderate (j + 4 * m)))
  exact (hnum.mul hden).congr' (Eventually.of_forall fun x => by
    beta_reduce
    rw [thetaDerivativePacket_ratio_eq, div_eq_mul_inv])

/-- The logarithmic ratio `L = log k_t - log k`. -/
def thetaPacketLogRatio (m : ℕ) (t x : ℝ) : ℝ :=
  Real.log (thetaDerivativePacket m t x) - Real.log (thetaCuspFullSource x)

theorem thetaPacketLogRatio_eq (m : ℕ) (t x : ℝ) (hpos : 0 < thetaDerivativePacket m t x) :
    thetaPacketLogRatio m t x = Real.log (1 + t * thetaSourceRatio (4 * m) x) := by
  have hk := thetaCuspFullSource_pos_all x
  unfold thetaPacketLogRatio
  rw [← Real.log_div hpos.ne' hk.ne']
  congr 1
  simp only [thetaDerivativePacket, thetaSourceRatio]
  field_simp

theorem contDiff_thetaPacketLogRatio (m : ℕ) (t : ℝ)
    (hpos : ∀ x, 0 < thetaDerivativePacket m t x) :
    ContDiff ℝ ∞ (thetaPacketLogRatio m t) :=
  ((contDiff_thetaDerivativePacket m t).log fun x => (hpos x).ne').sub
    (contDiff_thetaCuspFullSource.log fun x => (thetaCuspFullSource_pos_all x).ne')

/-- On the positive tail `L ≥ 0`, and `L` is moderate. -/
theorem eventually_thetaPacketLogRatio_nonneg (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ x in atTop, 0 ≤ thetaPacketLogRatio m t x := by
  filter_upwards [eventually_half_le_thetaSourceRatio m hm] with x hx
  have hpos : 0 < thetaDerivativePacket m t x := by
    have := (thetaCuspFullSource_pos_all x)
    have h2 : thetaDerivativePacket m t x =
        thetaCuspFullSource x * (1 + t * thetaSourceRatio (4 * m) x) := by
      simp only [thetaDerivativePacket, thetaSourceRatio]; field_simp
    rw [h2]; have : 0 ≤ t * thetaSourceRatio (4 * m) x := by nlinarith
    positivity
  rw [thetaPacketLogRatio_eq m t x hpos]
  exact Real.log_nonneg (by nlinarith)

/-- Every derivative of `L = log k_t - log k` is moderate for fixed small `t ≥ 0`. -/
theorem thetaTailModerate_iteratedDeriv_thetaPacketLogRatio (m : ℕ) (hm : 0 < m) {t : ℝ}
    (ht : 0 ≤ t) (hpos : ∀ x, 0 < thetaDerivativePacket m t x) (n : ℕ) :
    ThetaTailModerate (iteratedDeriv n (thetaPacketLogRatio m t)) := by
  rcases n with _ | n
  · rw [iteratedDeriv_zero]
    obtain ⟨C, d, hC⟩ := thetaSourceRatio_moderate (4 * m)
    refine ⟨|t| * |C|, d, ?_⟩
    filter_upwards [hC, eventually_half_le_thetaSourceRatio m hm] with x hx hx'
    rw [thetaPacketLogRatio_eq m t x (hpos x)]
    have hσ : 0 ≤ t * thetaSourceRatio (4 * m) x := by nlinarith
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    calc Real.log (1 + t * thetaSourceRatio (4 * m) x) ≤ t * thetaSourceRatio (4 * m) x := by
          have := Real.add_one_le_exp (t * thetaSourceRatio (4 * m) x)
          rw [Real.log_le_iff_le_exp (by linarith)]
          linarith
      _ ≤ |t| * (|C| * thetaCuspSingleAtomReflectionScale 1 x ^ d) := by
          rw [abs_of_nonneg ht]
          exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hx.trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (thetaTailScale_pos x).le _))))
            ht
      _ = |t| * |C| * thetaCuspSingleAtomReflectionScale 1 x ^ d := by ring
  · have hk := thetaTailModerate_iteratedDeriv_log contDiff_thetaCuspFullSource
      thetaCuspFullSource_pos_all thetaSourceRatio_moderate n
    have hkt := thetaTailModerate_iteratedDeriv_log (contDiff_thetaDerivativePacket m t) hpos
      (thetaDerivativePacket_ratio_moderate m hm ht) n
    have hL : iteratedDeriv (n + 1) (thetaPacketLogRatio m t) =
        fun x => iteratedDeriv (n + 1) (fun y => Real.log (thetaDerivativePacket m t y)) x -
          iteratedDeriv (n + 1) (fun y => Real.log (thetaCuspFullSource y)) x := by
      funext x
      have h1 : ContDiff ℝ ∞ (fun y => Real.log (thetaDerivativePacket m t y)) :=
        (contDiff_thetaDerivativePacket m t).log fun x => (hpos x).ne'
      have h2 : ContDiff ℝ ∞ (fun y => Real.log (thetaCuspFullSource y)) :=
        contDiff_thetaCuspFullSource.log fun x => (thetaCuspFullSource_pos_all x).ne'
      exact iteratedDeriv_sub (h1.contDiffAt.of_le (by exact_mod_cast le_top))
        (h2.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [hL]
    exact hkt.sub hk

/-! ## Tail curvature of `k`, `k_t` and the logarithmic ratio -/

/-- `(log k)'' ≤ -4π e^{2x} + 1` far out on the positive tail. -/
theorem eventually_iteratedDeriv_two_log_thetaCuspFullSource_le :
    ∀ᶠ x in atTop, iteratedDeriv 2 (fun y => Real.log (thetaCuspFullSource y)) x ≤
      -4 * thetaCuspSingleAtomReflectionScale 1 x + 1 := by
  filter_upwards [tendsto_thetaSourceRatio_curvature_add_scale.eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)] with x hx
  have h := iteratedDeriv_two_thetaCuspLogSource_eq x
  unfold thetaCuspLogSource at h
  rw [h]
  have hk := (thetaCuspFullSource_pos_all x).ne'
  have heq : thetaCuspLogConcavityNumerator x / thetaCuspFullSource x ^ 2 =
      thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2 := by
    unfold thetaCuspLogConcavityNumerator thetaSourceRatio
    field_simp
  rw [heq]
  linarith

theorem thetaPacket_numerator_le_mul {a s1 s2 u v t c : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (hc : 0 ≤ c) (hM : (v / a - (u / a) ^ 2 - (s2 - s1 ^ 2)) + (u / a - s1) ^ 2 ≤ c) :
    (s2 + t * v) * (1 + t * a) - (s1 + t * u) ^ 2 ≤ (1 + t * a) ^ 2 * ((s2 - s1 ^ 2) + c) := by
  rw [thetaPacket_numerator_algebra a s1 s2 u v t ha.ne']
  set M := (v / a - (u / a) ^ 2 - (s2 - s1 ^ 2)) + (u / a - s1) ^ 2
  have hta : 0 ≤ t * a := mul_nonneg ht ha.le
  have h1 : t * (1 + t * a) * a * M ≤ t * (1 + t * a) * a * c :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have h2 : t * (1 + t * a) * a * c ≤ (1 + t * a) ^ 2 * c := by
    have h3 : (1 + t * a) ^ 2 * c - t * (1 + t * a) * a * c = (1 + t * a) * c := by ring
    have h4 : 0 ≤ (1 + t * a) * c := mul_nonneg (by positivity) hc
    linarith
  have h5 : 0 ≤ t ^ 2 * a ^ 2 * (u / a - s1) ^ 2 := by positivity
  nlinarith

/-- **Uniform tail curvature with the scale.** Far out on the positive tail, uniformly in `t ≥ 0`,
`k_t'' k_t - (k_t')² ≤ (-4π e^{2x} + (8m)² + 2) k_t²`. -/
theorem eventually_thetaDerivativePacketNumerator_le_scale (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x in atTop, ∀ t : ℝ, 0 ≤ t →
      thetaDerivativePacketNumerator m t x ≤
        (-4 * thetaCuspSingleAtomReflectionScale 1 x + ((2 * (4 * m : ℕ) : ℝ) ^ 2 + 2)) *
          thetaDerivativePacket m t x ^ 2 := by
  set r := 4 * m
  set c : ℝ := (2 * (r : ℕ) : ℝ) ^ 2 + 1
  have hc : 0 ≤ c := by positivity
  have hM := (tendsto_thetaSourceRatio_logCurvature m hm).add
    ((tendsto_thetaSourceRatio_logSlope m hm).pow 2)
  rw [zero_add] at hM
  have hMev := hM.eventually_lt_const (show ((2 * (r : ℕ) : ℝ)) ^ 2 < c by simp [c])
  have hℓev := tendsto_thetaSourceRatio_curvature_add_scale.eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hMev, hℓev, eventually_half_le_thetaSourceRatio m hm] with x hMx hℓx ha
  intro t ht
  set K := thetaCuspFullSource x
  have hK : 0 < K := thetaCuspFullSource_pos_all x
  have ha0 : 0 < thetaSourceRatio r x := by linarith
  have hσ : ∀ i, iteratedDeriv i thetaCuspFullSource x = K * thetaSourceRatio i x := by
    intro i
    have hk0 : thetaCuspFullSource x ≠ 0 := hK.ne'
    simp only [thetaSourceRatio, K]
    field_simp
  have hkt : thetaDerivativePacket m t x = K * (1 + t * thetaSourceRatio r x) := by
    simp only [thetaDerivativePacket]
    rw [hσ r]
    ring
  have hN : thetaDerivativePacketNumerator m t x =
      K ^ 2 * ((thetaSourceRatio 2 x + t * thetaSourceRatio (r + 2) x) *
        (1 + t * thetaSourceRatio r x) -
          (thetaSourceRatio 1 x + t * thetaSourceRatio (r + 1) x) ^ 2) := by
    unfold thetaDerivativePacketNumerator
    rw [iteratedDeriv_thetaDerivativePacket, iteratedDeriv_thetaDerivativePacket]
    simp only
    rw [hkt, hσ 2, hσ 1, show 2 + 4 * m = r + 2 by ring, show 1 + 4 * m = r + 1 by ring,
      hσ (r + 2), hσ (r + 1)]
    ring
  have hbound := thetaPacket_numerator_le_mul (a := thetaSourceRatio r x)
    (s1 := thetaSourceRatio 1 x) (s2 := thetaSourceRatio 2 x) (u := thetaSourceRatio (r + 1) x)
    (v := thetaSourceRatio (r + 2) x) ha0 ht hc (by simpa [add_comm] using hMx.le)
  rw [hN, hkt, mul_pow]
  have hK2 : 0 < K ^ 2 := by positivity
  have hℓ : thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2 + c ≤
      -4 * thetaCuspSingleAtomReflectionScale 1 x + ((2 * (r : ℕ) : ℝ) ^ 2 + 2) := by
    simp only [c]; linarith
  have hsq : 0 ≤ (1 + t * thetaSourceRatio r x) ^ 2 := sq_nonneg _
  calc K ^ 2 * ((thetaSourceRatio 2 x + t * thetaSourceRatio (r + 2) x) *
        (1 + t * thetaSourceRatio r x) - (thetaSourceRatio 1 x + t * thetaSourceRatio (r + 1) x) ^ 2)
      ≤ K ^ 2 * ((1 + t * thetaSourceRatio r x) ^ 2 *
          (thetaSourceRatio 2 x - thetaSourceRatio 1 x ^ 2 + c)) :=
        mul_le_mul_of_nonneg_left hbound hK2.le
    _ ≤ K ^ 2 * ((1 + t * thetaSourceRatio r x) ^ 2 *
          (-4 * thetaCuspSingleAtomReflectionScale 1 x + ((2 * (r : ℕ) : ℝ) ^ 2 + 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hℓ hsq) hK2.le
    _ = _ := by ring

/-- The first derivative of `L = log k_t - log k` is `t σ_r A/(1 + t σ_r)` with
`A = σ_{r+1}/σ_r - σ_1`; it stays bounded by `2·4m + 1` on the tail. -/
theorem eventually_abs_deriv_thetaPacketLogRatio_le (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ x, 0 < thetaDerivativePacket m t x) :
    ∀ᶠ x in atTop, |iteratedDeriv 1 (thetaPacketLogRatio m t) x| ≤ 2 * (4 * m : ℕ) + 1 := by
  have hA := tendsto_thetaSourceRatio_logSlope m hm
  have hAev := hA.abs.eventually_lt_const (show |(2 * (4 * m : ℕ) : ℝ)| < 2 * (4 * m : ℕ) + 1 by
    rw [abs_of_nonneg (by positivity)]; linarith)
  filter_upwards [hAev, eventually_half_le_thetaSourceRatio m hm] with x hAx ha
  have h1 : iteratedDeriv 1 (thetaPacketLogRatio m t) x =
      iteratedDeriv 1 (fun y => Real.log (thetaDerivativePacket m t y)) x -
        iteratedDeriv 1 (fun y => Real.log (thetaCuspFullSource y)) x := by
    have c1 : ContDiff ℝ ∞ (fun y => Real.log (thetaDerivativePacket m t y)) :=
      (contDiff_thetaDerivativePacket m t).log fun x => (hpos x).ne'
    have c2 : ContDiff ℝ ∞ (fun y => Real.log (thetaCuspFullSource y)) :=
      contDiff_thetaCuspFullSource.log fun x => (thetaCuspFullSource_pos_all x).ne'
    exact iteratedDeriv_sub (c1.contDiffAt.of_le (by exact_mod_cast le_top))
      (c2.contDiffAt.of_le (by exact_mod_cast le_top))
  have hkt := iteratedDeriv_succ_log (contDiff_thetaDerivativePacket m t) hpos 0
  have hk := iteratedDeriv_succ_log contDiff_thetaCuspFullSource thetaCuspFullSource_pos_all 0
  rw [zero_add] at hkt hk
  rw [h1, hkt, hk, iteratedDeriv_zero, iteratedDeriv_zero, thetaDerivativePacket_ratio_eq]
  set a := thetaSourceRatio (4 * m) x
  have ha0 : 0 < a := by linarith
  have hta : 0 ≤ t * a := mul_nonneg ht ha0.le
  have heq : (thetaSourceRatio 1 x + t * thetaSourceRatio (1 + 4 * m) x) / (1 + t * a) -
      iteratedDeriv 1 thetaCuspFullSource x / thetaCuspFullSource x =
      (t * a / (1 + t * a)) * (thetaSourceRatio (4 * m + 1) x / a - thetaSourceRatio 1 x) := by
    rw [show 1 + 4 * m = 4 * m + 1 by ring]
    change _ - thetaSourceRatio 1 x = _
    field_simp
    ring
  rw [heq, abs_mul]
  have hfrac : |t * a / (1 + t * a)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith
  calc |t * a / (1 + t * a)| * |thetaSourceRatio (4 * m + 1) x / a - thetaSourceRatio 1 x|
      ≤ 1 * (2 * (4 * m : ℕ) + 1) :=
        mul_le_mul hfrac hAx.le (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- `L = log k_t - log k` is `o(e^{2x})`: for every `ε > 0`, eventually `L ≤ ε π e^{2x}`. -/
theorem eventually_thetaPacketLogRatio_le_mul_scale (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ x, 0 < thetaDerivativePacket m t x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, thetaPacketLogRatio m t x ≤ ε * thetaCuspSingleAtomReflectionScale 1 x := by
  obtain ⟨C, d, hC⟩ := thetaSourceRatio_moderate (4 * m)
  set K := Real.log (1 + t * |C|)
  have hK : 0 ≤ K := Real.log_nonneg (by nlinarith [abs_nonneg C])
  have hsqrt := (Real.tendsto_sqrt_atTop.comp tendsto_thetaTailScale).eventually_ge_atTop
    (max 1 ((2 * d + K) / ε))
  filter_upwards [hC, hsqrt, eventually_one_le_thetaTailScale,
    eventually_half_le_thetaSourceRatio m hm] with x hx hs hq ha
  set q := thetaCuspSingleAtomReflectionScale 1 x
  simp only [Function.comp] at hs
  rw [thetaPacketLogRatio_eq m t x (hpos x)]
  have hσ : t * thetaSourceRatio (4 * m) x ≤ t * |C| * q ^ d := by
    have := (le_abs_self _).trans hx
    calc t * thetaSourceRatio (4 * m) x ≤ t * (C * q ^ d) := mul_le_mul_of_nonneg_left this ht
      _ ≤ t * (|C| * q ^ d) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) d)) ht
      _ = _ := by ring
  have hqd : 1 ≤ q ^ d := one_le_pow₀ hq
  have hlog1 : Real.log (1 + t * thetaSourceRatio (4 * m) x) ≤ Real.log ((1 + t * |C|) * q ^ d) := by
    apply Real.log_le_log (by nlinarith)
    nlinarith [abs_nonneg C]
  rw [Real.log_mul (by nlinarith [abs_nonneg C]) (by positivity), Real.log_pow] at hlog1
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by linarith)
  have hlogq : Real.log q ≤ 2 * Real.sqrt q := by
    have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
    have := Real.log_le_sub_one_of_pos hs0
    have hq' : Real.log q = 2 * Real.log (Real.sqrt q) := by
      have h := Real.log_pow (Real.sqrt q) 2
      rw [Real.sq_sqrt (by linarith)] at h
      rw [h]; norm_num
    rw [hq']
    linarith
  have hs1 : 1 ≤ Real.sqrt q := (le_max_left _ _).trans hs
  have hs2 : (2 * d + K) / ε ≤ Real.sqrt q := (le_max_right _ _).trans hs
  have hs3 : 2 * d + K ≤ ε * Real.sqrt q := by
    rw [div_le_iff₀ hε] at hs2; linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc Real.log (1 + t * thetaSourceRatio (4 * m) x) ≤ K + d * Real.log q := hlog1
    _ ≤ K + d * (2 * Real.sqrt q) := by gcongr
    _ ≤ (2 * d + K) * Real.sqrt q := by nlinarith
    _ ≤ ε * Real.sqrt q * Real.sqrt q := by nlinarith
    _ = ε * q := by rw [mul_assoc, hsq]

end

end RHTower
