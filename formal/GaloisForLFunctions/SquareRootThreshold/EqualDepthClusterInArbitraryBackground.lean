import GaloisForLFunctions.SquareRootThreshold.IsolatedPairHodgeViolation

/-!
# Equal-depth clusters in an arbitrary on-line background

Open problem 2 of the field asks for the visibility aperture of a cluster of comparable depths with
no depth gap. This module treats the extreme case: `n` simple off-line pairs `½ ± δ + iγ_k` of one
common depth `δ`, inside an arbitrary tempered on-line background.

The pairs no longer dominate one another; their lag terms can cancel. With a bump `b` and lags on a
grid `v = mℓ`, the cluster contributes to `S_b(v) + conj S_b(−v)` the weighted exponential sum

`2 Σ_k e^{iγ_k v} (Q_k e^{δv} + Q̄_k e^{−δv})`,  `Q_k = h_b(γ_k − iδ) conj h_b(γ_k + iδ)`,

whose leading part is `2e^{δv} Σ_k Q_k z_k^m`, `z_k = e^{iγ_kℓ}`.

* **Weighted windows** (`exists_weighted_powerSum_window_lower`). For distinct unit nodes and
  nonzero weights there is `c > 0` such that every window of `n` consecutive exponents contains an
  `m` with `|Σ_k Q_k z_k^m| ≥ c`. (Compactness of the orbit closure on the torus, and Lagrange
  interpolation.)
* **Cluster visibility** (`equalDepthCluster_visible`). If the grid separates the heights
  (`e^{iγ_kℓ}` distinct) and the weights are nonzero, the configuration is visible at every aperture

  `a ≥ (1/2δ) log⁺((2M + 3Σ_k |Q_k|)/c) + (n + 2)ℓ/2 + w`,

  `M` the on-line mass seen by `b`. Cancellations among the pairs can delay visibility only by
  `(n + 2)ℓ/2` and the factor `1/c`: the aperture stays logarithmic in the local on-line mass,
  whatever the on-line zeros do.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Weighted power sums on windows.** For distinct unit nodes and nonzero weights there is
`c > 0` with: every window of `|ι|` consecutive exponents contains an `m` with
`|Σ_r q_r z_r^m| ≥ c`. -/
theorem exists_weighted_powerSum_window_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (z : ι → ℂ) (hz : ∀ r, ‖z r‖ = 1) (hinj : Function.Injective z) (q : ι → ℂ)
    (hq : ∀ r, q r ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ j : ℕ, j < Fintype.card ι ∧
      c ≤ ‖∑ r, q r * z r ^ (k + j)‖ := by
  set K : Set (ι → ℂ) := Set.univ.pi fun _ => Metric.sphere (0 : ℂ) 1 with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_sphere 0 1
  have hKne : K.Nonempty := ⟨fun _ => 1, fun r _ => by simp⟩
  set F : (ι → ℂ) → ℝ := fun u => ∑ j ∈ Finset.range (Fintype.card ι),
    ‖∑ r, q r * u r * z r ^ j‖ with hFdef
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact (continuous_finsetSum _ fun r _ =>
      (continuous_const.mul (continuous_apply r)).mul continuous_const).norm
  obtain ⟨u₀, hu₀, hmin⟩ := hK.exists_isMinOn hKne hF.continuousOn
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hpos : 0 < F u₀ := by
    by_contra hle
    push Not at hle
    have hzero : F u₀ = 0 := le_antisymm hle (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hall : ∀ j, j < Fintype.card ι → ∑ r, (q r * u₀ r) * z r ^ j = 0 := fun j hj =>
      norm_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).mp hzero j
        (Finset.mem_range.mpr hj))
    obtain ⟨r₀⟩ := (inferInstance : Nonempty ι)
    have h0 := eq_zero_of_moments_eq_zero z hinj (fun r => q r * u₀ r) hall r₀
    have h1 : ‖u₀ r₀‖ = 1 := by
      have := hu₀ r₀ (Set.mem_univ _)
      simpa using this
    rcases mul_eq_zero.mp h0 with h | h
    · exact hq r₀ h
    · rw [h, norm_zero] at h1; norm_num at h1
  refine ⟨F u₀ / Fintype.card ι, by positivity, fun k => ?_⟩
  have hmem : (fun r => z r ^ k) ∈ K := fun r _ => by simp [norm_pow, hz r]
  have hk : F u₀ ≤ F (fun r => z r ^ k) := isMinOn_iff.mp hmin _ hmem
  by_contra hcon
  push Not at hcon
  have hlt : F (fun r => z r ^ k) < F u₀ := by
    calc F (fun r => z r ^ k) =
          ∑ j ∈ Finset.range (Fintype.card ι), ‖∑ r, q r * z r ^ (k + j)‖ := by
          simp only [hFdef, pow_add, mul_assoc]
      _ < ∑ _j ∈ Finset.range (Fintype.card ι), F u₀ / Fintype.card ι :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hcard.ne')
            fun j hj => hcon j (Finset.mem_range.mp hj)
      _ = F u₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  linarith

/-- **The lag structure of an equal-depth cluster.** If all zeros of a tempered configuration are
on the critical line except `n` simple pairs `½ ± δ + iγ_k` of one depth, and
`e^{δv} |Σ_k Q_k e^{iγ_k v}| > 2M_b + 3Σ_k |Q_k|`, the two-point minor fails at lag `v`. -/
theorem equalDepthCluster_lagStructure_gt (Z : ZeroConfig) (hZ : TemperedConfig Z) {n : ℕ}
    (γ : Fin n → ℝ) (hγ : Function.Injective γ) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ k, heightPoint δ (γ k) ∈ Z.carrier) (hm : ∀ k, heightPoint (-δ) (γ k) ∈ Z.carrier)
    (hmp : ∀ k, Z.mult (heightPoint δ (γ k)) = 1) (hmm : ∀ k, Z.mult (heightPoint (-δ) (γ k)) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨
      ∃ k, ρ = heightPoint δ (γ k) ∨ ρ = heightPoint (-δ) (γ k))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 ≤ v) (hvis : 2 * onLineMassOf Z b + 3 * ∑ k, ‖pairWeight b δ (γ k)‖ <
      ‖∑ k, pairWeight b δ (γ k) * cexp (I * γ k * v)‖ * Real.exp (δ * v)) :
    2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  classical
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set F : ℝ → Z.carrier → ℂ := fun v ρ => (Z.mult ρ : ℂ) *
    paperFT (EF.weilTest b b) (gammaOf ρ) * cexp (I * gammaOf ρ * v) with hF
  have hFs : ∀ v, Summable (F v) := fun v => summable_lagStructure Z hZ hb hbs v
  set Pp : Fin n → Z.carrier := fun k => ⟨heightPoint δ (γ k), hp k⟩ with hPp
  set Pm : Fin n → Z.carrier := fun k => ⟨heightPoint (-δ) (γ k), hm k⟩ with hPm
  have hrePp : ∀ k, ((Pp k : Z.carrier) : ℂ).re ≠ 1 / 2 := fun k => by
    simp [hPp, heightPoint]; linarith
  have hrePm : ∀ k, ((Pm k : Z.carrier) : ℂ).re ≠ 1 / 2 := fun k => by
    simp [hPm, heightPoint]; linarith
  have hPpinj : ∀ k j, Pp k = Pp j → k = j := fun k j h => hγ (by
    have := congrArg (fun x : Z.carrier => (x : ℂ).im) h
    simpa [hPp, heightPoint] using this)
  have hPminj : ∀ k j, Pm k = Pm j → k = j := fun k j h => hγ (by
    have := congrArg (fun x : Z.carrier => (x : ℂ).im) h
    simpa [hPm, heightPoint] using this)
  have hPpm : ∀ k j, Pp k ≠ Pm j := fun k j h => by
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp [hPp, hPm, heightPoint] at this
    linarith
  set R : ℝ → Z.carrier → ℂ := fun v ρ => if (ρ : ℂ).re = 1 / 2 then F v ρ else 0 with hR
  have hRs : ∀ v, Summable (R v) := fun v => Summable.of_norm_bounded (hFs v).norm fun ρ => by
    simp only [hR]; split_ifs <;> simp
  set A : ℝ → Fin n → Z.carrier → ℂ := fun v k ρ =>
    (if ρ = Pp k then F v (Pp k) else 0) + (if ρ = Pm k then F v (Pm k) else 0) with hA
  have hAs : ∀ v k, Summable (A v k) := fun v k =>
    summable_of_ne_finset_zero (s := {Pp k, Pm k}) fun ρ hρ => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
      simp [hA, hρ.1, hρ.2]
  have hpt : ∀ v ρ, F v ρ = ∑ k, A v k ρ + R v ρ := by
    intro v ρ
    rcases hon ρ.1 ρ.2 with h | ⟨k₀, h | h⟩
    · have h1 : ∀ k, ρ ≠ Pp k := fun k e => hrePp k (e ▸ h)
      have h2 : ∀ k, ρ ≠ Pm k := fun k e => hrePm k (e ▸ h)
      simp [hA, hR, h, h1, h2]
    · have hρ : ρ = Pp k₀ := Subtype.ext h
      subst hρ
      rw [Finset.sum_eq_single k₀ (fun k _ hk => by
        simp only [hA]; rw [if_neg fun e => hk (hPpinj _ _ e).symm, if_neg (hPpm _ _)]; simp)
        (by simp), show R v (Pp k₀) = 0 from if_neg (hrePp k₀)]
      simp only [hA]
      rw [if_pos trivial, if_neg (hPpm k₀ k₀)]
      ring
    · have hρ : ρ = Pm k₀ := Subtype.ext h
      subst hρ
      have hne' : Pm k₀ ≠ Pp k₀ := fun e => hPpm k₀ k₀ e.symm
      rw [Finset.sum_eq_single k₀ (fun k _ hk => by
        simp only [hA]; rw [if_neg fun e => (hPpm _ _ e.symm), if_neg fun e => hk (hPminj _ _ e).symm]
        simp) (by simp), show R v (Pm k₀) = 0 from if_neg (hrePm k₀)]
      simp [hA, hne']
  have hsplit : ∀ v, lagStructure Z b v = ∑ k, (F v (Pp k) + F v (Pm k)) + ∑' ρ, R v ρ := by
    intro v
    rw [lagStructure, show (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b)
      (gammaOf ρ) * cexp (I * gammaOf ρ * v)) = ∑' ρ, F v ρ from rfl, tsum_congr (hpt v),
      Summable.tsum_add (summable_sum fun k _ => hAs v k) (hRs v),
      Summable.tsum_finsetSum fun k _ => hAs v k]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : Summable fun ρ : Z.carrier => if ρ = Pp k then F v (Pp k) else 0 :=
      summable_of_ne_finset_zero (s := {Pp k}) fun ρ hρ => by
        rw [Finset.mem_singleton] at hρ; simp [hρ]
    have h2 : Summable fun ρ : Z.carrier => if ρ = Pm k then F v (Pm k) else 0 :=
      summable_of_ne_finset_zero (s := {Pm k}) fun ρ hρ => by
        rw [Finset.mem_singleton] at hρ; simp [hρ]
    simp only [hA]
    rw [Summable.tsum_add h1 h2, tsum_ite_eq, tsum_ite_eq]
  -- on-line part
  set R₀ : Z.carrier → ℝ := fun ρ => if (ρ : ℂ).re = 1 / 2 then
    (Z.mult ρ : ℝ) * ‖paperFT b (gammaOf ρ)‖ ^ 2 else 0 with hR₀
  have hon_term : ∀ v ρ, R v ρ + conj (R (-v) ρ) = 2 * R v ρ ∧ ‖R v ρ‖ = R₀ ρ ∧
      R 0 ρ = (R₀ ρ : ℂ) := by
    intro v ρ
    by_cases h : (ρ : ℂ).re = 1 / 2
    · have hg := gammaOf_eq_ofReal_of_re h
      obtain ⟨h1, h2, h3⟩ := onLine_summand hb.continuous hbc (Z.mult ρ) (ρ : ℂ).im v
      simp only [hR, hR₀, if_pos h, hF, hg]
      exact ⟨h1, h2, h3⟩
    · simp only [hR, hR₀, if_neg h]
      simp
  have hR₀s : Summable R₀ := by
    refine Summable.of_norm_bounded (hRs 0).norm fun ρ => ?_
    rw [← (hon_term 0 ρ).2.1, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hM : onLineMassOf Z b = ∑' ρ, R₀ ρ := rfl
  have hconj : Summable fun ρ => conj (R (-v) ρ) :=
    ((hRs (-v)).map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj)
  have hX_on : ‖(∑' ρ, R v ρ) + conj (∑' ρ, R (-v) ρ)‖ ≤ 2 * onLineMassOf Z b := by
    rw [Complex.conj_tsum, ← Summable.tsum_add (hRs v) hconj,
      tsum_congr fun ρ => (hon_term v ρ).1]
    have hn : Summable fun ρ => ‖2 * R v ρ‖ := ((hRs v).mul_left 2).norm
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    rw [hM, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun ρ => ?_) hn (hR₀s.mul_left 2)
    rw [norm_mul, Complex.norm_ofNat, (hon_term v ρ).2.1]
  have hS0_on : (∑' ρ, R 0 ρ).re = onLineMassOf Z b := by
    rw [Complex.re_tsum (hRs 0), hM]
    exact tsum_congr fun ρ => by rw [(hon_term 0 ρ).2.2, Complex.ofReal_re]
  -- the cluster
  set Q : Fin n → ℂ := fun k => pairWeight b δ (γ k) with hQ
  have hFpp : ∀ v k, F v (Pp k) = Q k * cexp (I * ((γ k : ℂ) - I * δ) * v) := by
    intro v k
    simp only [hF, hPp, hmp, Nat.cast_one, one_mul, hQ]
    exact (pair_summand hb.continuous hbc (γ k) δ v).1
  have hFpm : ∀ v k, F v (Pm k) = conj (Q k) * cexp (I * ((γ k : ℂ) - I * (-δ : ℝ)) * v) := by
    intro v k
    simp only [hF, hPm, hmm, Nat.cast_one, one_mul, hQ]
    exact (pair_summand hb.continuous hbc (γ k) δ v).2
  have hX : lagStructure Z b v + conj (lagStructure Z b (-v)) =
      ∑ k, 2 * cexp (I * γ k * v) *
        (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ)) +
        ((∑' ρ, R v ρ) + conj (∑' ρ, R (-v) ρ)) := by
    rw [hsplit, hsplit, map_add, map_sum]
    have hk : ∀ k, (F v (Pp k) + F v (Pm k)) + conj (F (-v) (Pp k) + F (-v) (Pm k)) =
        2 * cexp (I * γ k * v) *
          (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ)) := by
      intro k
      rw [hFpp, hFpp, hFpm, hFpm, ← pair_lag_identity (Q k) (γ k) δ v]
    rw [show (∑ k, 2 * cexp (I * γ k * v) *
        (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ))) =
        ∑ k, ((F v (Pp k) + F v (Pm k)) + conj (F (-v) (Pp k) + F (-v) (Pm k))) from
      Finset.sum_congr rfl fun k _ => (hk k).symm]
    simp only [Finset.sum_add_distrib]
    abel
  have hS0 : (lagStructure Z b 0).re = ∑ k, 2 * (Q k).re + onLineMassOf Z b := by
    rw [hsplit, Complex.add_re, Complex.re_sum, hS0_on]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hFpp, hFpm]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Complex.add_re,
      Complex.conj_re]
    ring
  have hvis' : 2 * onLineMassOf Z b + 3 * ∑ k, ‖Q k‖ <
      ‖∑ k, Q k * cexp (I * γ k * v)‖ * Real.exp (δ * v) := by simpa only [hQ] using hvis
  clear_value Q
  -- lower bound for the cluster term
  have hE : ∀ k, ‖cexp (I * γ k * v)‖ = 1 := fun k => by
    rw [show I * (γ k : ℂ) * (v : ℂ) = ((γ k * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hcl : 2 * Real.exp (δ * v) * ‖∑ k, Q k * cexp (I * γ k * v)‖ -
      2 * ∑ k, ‖Q k‖ ≤ ‖∑ k, 2 * cexp (I * γ k * v) *
        (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ))‖ := by
    have hsplit2 : ∑ k, 2 * cexp (I * γ k * v) *
        (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ)) =
        ((2 * Real.exp (δ * v) : ℝ) : ℂ) * ∑ k, Q k * cexp (I * γ k * v) +
          ∑ k, 2 * cexp (I * γ k * v) * (conj (Q k) * (Real.exp (-(δ * v)) : ℂ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    rw [hsplit2]
    have h1 := norm_sub_norm_le (((2 * Real.exp (δ * v) : ℝ) : ℂ) * ∑ k, Q k * cexp (I * γ k * v))
      (-∑ k, 2 * cexp (I * γ k * v) * (conj (Q k) * (Real.exp (-(δ * v)) : ℂ)))
    rw [norm_neg, sub_neg_eq_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at h1
    have h2 : ‖∑ k, 2 * cexp (I * γ k * v) * (conj (Q k) * (Real.exp (-(δ * v)) : ℂ))‖ ≤
        2 * ∑ k, ‖Q k‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, hE, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(δ * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith [norm_nonneg (Q k)]
    linarith
  rw [hX, hS0]
  have hsum_re : ∑ k, 2 * (Q k).re ≤ 2 * ∑ k, ‖Q k‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by linarith [Complex.re_le_norm (Q k)]
  have hsplitn := norm_sub_norm_le (∑ k, 2 * cexp (I * γ k * v) *
      (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ)))
    (-((∑' ρ, R v ρ) + conj (∑' ρ, R (-v) ρ)))
  rw [norm_neg, sub_neg_eq_add] at hsplitn
  have hcl' : 2 * (‖∑ k, Q k * cexp (I * γ k * v)‖ * Real.exp (δ * v)) - 2 * ∑ k, ‖Q k‖ ≤
      ‖∑ k, 2 * cexp (I * γ k * v) *
        (Q k * (Real.exp (δ * v) : ℂ) + conj (Q k) * (Real.exp (-(δ * v)) : ℂ))‖ := by
    linarith [hcl, mul_comm (Real.exp (δ * v)) ‖∑ k, Q k * cexp (I * γ k * v)‖]
  linarith

/-- **Equal-depth clusters are visible at a logarithmic aperture.** Under the hypotheses of
`equalDepthCluster_lagStructure_gt`, let the lag grid `ℓ` separate the heights (`e^{iγ_kℓ}`
distinct) and let the weights `Q_k` be nonzero. Then there is `c > 0`, depending only on the
cluster and `b`, such that the configuration is visible at every aperture
`a ≥ (1/2δ) max(0, log((2M + 3Σ_k|Q_k|)/c)) + (n + 2)ℓ/2 + w`. -/
theorem equalDepthCluster_visible (Z : ZeroConfig) (hZ : TemperedConfig Z) {n : ℕ} (hn : 0 < n)
    (γ : Fin n → ℝ) (hγ : Function.Injective γ) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ k, heightPoint δ (γ k) ∈ Z.carrier) (hm : ∀ k, heightPoint (-δ) (γ k) ∈ Z.carrier)
    (hmp : ∀ k, Z.mult (heightPoint δ (γ k)) = 1) (hmm : ∀ k, Z.mult (heightPoint (-δ) (γ k)) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨
      ∃ k, ρ = heightPoint δ (γ k) ∨ ρ = heightPoint (-δ) (γ k))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hsep : Function.Injective fun k => cexp (I * γ k * ℓ))
    (hQ : ∀ k, pairWeight b δ (γ k) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ,
      1 / (2 * δ) * max 0 (Real.log ((2 * onLineMassOf Z b +
        3 * ∑ k, ‖pairWeight b δ (γ k)‖) / c)) + (n + 2) * ℓ / 2 + w ≤ a →
        ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hz : ∀ k, ‖cexp (I * γ k * ℓ)‖ = 1 := fun k => by
    rw [show I * (γ k : ℂ) * (ℓ : ℂ) = ((γ k * ℓ : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  obtain ⟨c, hc, hwin⟩ := exists_weighted_powerSum_window_lower
    (fun k => cexp (I * γ k * ℓ)) hz hsep (fun k => pairWeight b δ (γ k)) hQ
  refine ⟨c, hc, fun a ha => ?_⟩
  set K := 2 * onLineMassOf Z b + 3 * ∑ k, ‖pairWeight b δ (γ k)‖ with hK
  have hM0 : 0 ≤ onLineMassOf Z b := tsum_nonneg fun ρ => by split_ifs <;> positivity
  set x := max 0 (Real.log (K / c)) with hx
  set m₀ : ℕ := ⌈x / (δ * ℓ)⌉₊ + 1 with hm₀
  obtain ⟨j, hj, hjc⟩ := hwin m₀
  rw [Fintype.card_fin] at hj
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = ((m₀ + j : ℕ) : ℝ) * ℓ := ⟨_, rfl⟩
  have hv : 0 ≤ v := by rw [hvdef]; positivity
  -- the phases at lag `v`
  have hphase : ∑ k, pairWeight b δ (γ k) * cexp (I * γ k * v) =
      ∑ k, pairWeight b δ (γ k) * cexp (I * γ k * ℓ) ^ (m₀ + j) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.exp_nat_mul, hvdef]
    congr 2
    push_cast
    ring
  -- `e^{δv} > K/c`
  have hδℓ : 0 < δ * ℓ := mul_pos hδ hℓ
  have hxm : x < δ * (m₀ * ℓ) := by
    have h1 : x / (δ * ℓ) < m₀ := by
      have := Nat.le_ceil (x / (δ * ℓ))
      rw [hm₀]; push_cast; linarith
    rw [div_lt_iff₀ hδℓ] at h1
    linarith
  have hexp : K / c < Real.exp (δ * v) := by
    have hKpos : 0 < K / c := by
      have : 0 < ∑ k, ‖pairWeight b δ (γ k)‖ :=
        Finset.sum_pos (fun k _ => norm_pos_iff.mpr (hQ k)) Finset.univ_nonempty
      positivity
    calc K / c = Real.exp (Real.log (K / c)) := (Real.exp_log hKpos).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr (le_max_right _ _)
      _ < Real.exp (δ * (m₀ * ℓ)) := Real.exp_lt_exp.mpr hxm
      _ ≤ Real.exp (δ * v) := Real.exp_le_exp.mpr (by
          rw [hvdef]; push_cast
          have : (m₀ : ℝ) * ℓ ≤ ((m₀ : ℝ) + j) * ℓ := mul_le_mul_of_nonneg_right
            (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith) hℓ.le
          nlinarith)
  have hvis : K < ‖∑ k, pairWeight b δ (γ k) * cexp (I * γ k * v)‖ * Real.exp (δ * v) := by
    rw [hphase]
    have := (div_lt_iff₀ hc).mp hexp
    nlinarith [Real.exp_pos (δ * v)]
  have hgt := equalDepthCluster_lagStructure_gt Z hZ γ hγ hδ hp hm hmp hmm hon hb hbs hv hvis
  obtain ⟨f, hf, hfs, hneg⟩ := exists_visible_of_lagStructure Z hZ hb hbs hv hgt
  suffices hva : v / 2 + w ≤ a from
    ⟨f, hf, hfs.trans (Icc_subset_Icc (neg_le_neg hva) hva), hneg⟩
  have hm₀le : (m₀ : ℝ) ≤ x / (δ * ℓ) + 2 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ x / (δ * ℓ))
    rw [hm₀]; push_cast; linarith
  have hjle : (j : ℝ) ≤ n := by exact_mod_cast hj.le
  have hxx : x / (δ * ℓ) * ℓ / 2 = 1 / (2 * δ) * x := by field_simp
  have h1 : ((m₀ : ℝ) + j) * ℓ ≤ (x / (δ * ℓ) + 2 + n) * ℓ :=
    mul_le_mul_of_nonneg_right (by linarith) hℓ.le
  have h2 : (x / (δ * ℓ) + 2 + n) * ℓ / 2 = 1 / (2 * δ) * x + (n + 2) * ℓ / 2 := by
    field_simp
    ring
  rw [hvdef]
  push_cast
  linarith

end GaloisForLFunctions.SquareRootThreshold
