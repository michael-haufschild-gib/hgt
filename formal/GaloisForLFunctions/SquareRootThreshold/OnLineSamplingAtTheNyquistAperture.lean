import GaloisForLFunctions.SquareRootThreshold.DepthTomographyAtTwiceNyquist

/-!
# Sampling by on-line configurations stops exactly at the Nyquist aperture

On-line zeros contribute `Σ_γ |h_f(γ)|² ≥ 0` to the Weil form. Whether they contribute *mass*,
`Σ_γ |h_f(γ)|² ≥ A ∫|f|²` with `A > 0` on all tests of aperture `a`, is the question whether the
ordinates form a set of sampling for the tests of aperture `a`. `RHTower.NyquistDichotomy` takes
such a bound for the critical zeros of `ζ` as its input (`RHTower.sampling_forces_mass`), with the
Beurling–Landau density heuristic placing its threshold at the Nyquist aperture.

For periodic on-line configurations the threshold is exact.

**Sampling law** (`onLineShadow_sampling_iff`). A weighted on-line periodic configuration with `r`
distinct ordinates per period `2π/ℓ` and positive weights (`onLineShadow`) satisfies a lower bound
`Sh(f) ≥ A ∫|f|²`, `A > 0`, on all tests of aperture `a` iff `⌈2a/ℓ⌉ ≤ r`, i.e. iff `a` does not
exceed the Nyquist aperture `rℓ/2` of its ordinates.

* **Below Nyquist** the Toeplitz section of the moments is the atomic form `Σ_k w_k |P_c(z_k)|²`
  of degree `< r` polynomials at `r` distinct nodes; it is positive definite
  (`atomic_form_pos`), hence bounded below on the unit sphere (`exists_atomic_floor`), and the
  ground-state law turns the floor into the sampling constant.
* **Above Nyquist** the vanishing polynomial `Π_k (z − z_k)` of degree `r` is a coefficient vector
  of length `⌈2a/ℓ⌉`; its lag-point test has positive mass and zero shadow.

So the mass that critical zeros can contribute against an off-line pair is a sub-Nyquist
phenomenon, exactly: beyond the Nyquist aperture of their ordinates the critical zeros can be
dodged by a test of positive mass.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Atomic forms of low-degree polynomials -/

/-- The polynomial with coefficient vector `c`. -/
def coeffPoly {n : ℕ} (c : Fin n → ℂ) : Polynomial ℂ :=
  ∑ j : Fin n, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

theorem eval_coeffPoly {n : ℕ} (c : Fin n → ℂ) (x : ℂ) :
    (coeffPoly c).eval x = ∑ j, c j * x ^ (j : ℕ) := by
  simp [coeffPoly, Polynomial.eval_finsetSum]

theorem coeff_coeffPoly {n : ℕ} (c : Fin n → ℂ) (j : Fin n) : (coeffPoly c).coeff j = c j := by
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j (fun i _ hi => if_neg fun h => hi (Fin.ext h).symm) (by simp),
    if_pos rfl]

theorem natDegree_coeffPoly_lt {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (coeffPoly c).natDegree < n := by
  refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_) (by omega :
    n - 1 < n)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- **Positivity below the node count.** A nonzero polynomial of degree `< n ≤ r` cannot vanish at
`r` distinct nodes, so `Σ_k w_k |P_c(z_k)|² > 0`. -/
theorem atomic_form_pos {r n : ℕ} (hnr : n ≤ r) (z : Fin r → ℂ) (hinj : Function.Injective z)
    (w : Fin r → ℝ) (hw : ∀ k, 0 < w k) (c : Fin n → ℂ) (hc : c ≠ 0) :
    0 < ∑ k, w k * ‖∑ j, c j * z k ^ (j : ℕ)‖ ^ 2 := by
  by_contra hle
  push Not at hle
  have hzero : ∀ k, ∑ j, c j * z k ^ (j : ℕ) = 0 := by
    intro k
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hw k).le (sq_nonneg _)).mp
      (le_antisymm hle (Finset.sum_nonneg fun k _ => mul_nonneg (hw k).le (sq_nonneg _))) k
      (Finset.mem_univ k)
    have := (mul_eq_zero.mp h0).resolve_left (hw k).ne'
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  apply hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext j; exact j.elim0
  have hp : coeffPoly c = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj (fun k => ?_) ?_
    · rw [eval_coeffPoly]; exact hzero k
    · rw [Fintype.card_fin]; exact lt_of_lt_of_le (natDegree_coeffPoly_lt hn c) hnr
  funext j
  rw [← coeff_coeffPoly c j, hp, Polynomial.coeff_zero, Pi.zero_apply]

/-- **Uniform floor below the node count.** For `n ≤ r` distinct nodes there is `A₀ > 0` with
`Σ_k w_k |P_c(z_k)|² ≥ A₀ ‖c‖²` for all `c`. -/
theorem exists_atomic_floor {r n : ℕ} (hnr : n ≤ r) (z : Fin r → ℂ) (hinj : Function.Injective z)
    (w : Fin r → ℝ) (hw : ∀ k, 0 < w k) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ c : Fin n → ℂ,
      A₀ * ∑ j, ‖c j‖ ^ 2 ≤ ∑ k, w k * ‖∑ j, c j * z k ^ (j : ℕ)‖ ^ 2 := by
  set F : (Fin n → ℂ) → ℝ := fun c => ∑ k, w k * ‖∑ j, c j * z k ^ (j : ℕ)‖ ^ 2 with hF
  have hF0 : ∀ c, 0 ≤ F c := fun c => Finset.sum_nonneg fun k _ => mul_nonneg (hw k).le (sq_nonneg _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun c => ?_⟩
    rw [show (∑ j : Fin 0, ‖c j‖ ^ 2) = 0 from Fin.sum_univ_zero _, mul_zero]
    exact hF0 c
  set S : Set (Fin n → ℂ) := {c | ∑ j, ‖c j‖ ^ 2 = 1} with hS
  have hcont : Continuous fun c : Fin n → ℂ => ∑ j, ‖c j‖ ^ 2 := by fun_prop
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq hcont continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℂ)) (r := 1)).subset fun c hc => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    have h1 : ‖c j‖ ^ 2 ≤ 1 := by
      rw [← hc]
      exact Finset.single_le_sum (f := fun j => ‖c j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (c j)]
  have hSne : S.Nonempty := ⟨fun j : Fin n => if j = ⟨0, hn⟩ then (1 : ℂ) else 0, by
    show ∑ j : Fin n, ‖(if j = ⟨0, hn⟩ then (1 : ℂ) else 0)‖ ^ 2 = 1
    rw [Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj => by simp [hj]) (by simp)]
    simp⟩
  have hFc : Continuous F := by fun_prop
  obtain ⟨c₀, hc₀, hmin⟩ := hSc.exists_isMinOn hSne hFc.continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    have : ∑ j : Fin n, ‖(0 : Fin n → ℂ) j‖ ^ 2 = 1 := hc₀
    simp at this
  have hA₀ : 0 < F c₀ := atomic_form_pos hnr z hinj w hw c₀ hc₀ne
  refine ⟨F c₀, hA₀, fun c => ?_⟩
  set s := ∑ j, ‖c j‖ ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact hF0 c
  -- normalize
  set t : ℝ := 1 / Real.sqrt s with ht
  have hts : t ^ 2 * s = 1 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hpos.le, one_div, inv_mul_cancel₀ hpos.ne']
  have hmem : (fun j => (t : ℂ) * c j) ∈ S := by
    show ∑ j, ‖(t : ℂ) * c j‖ ^ 2 = 1
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [← Finset.mul_sum, hts]
  have hle := isMinOn_iff.mp hmin _ hmem
  have hscale : F (fun j => (t : ℂ) * c j) = t ^ 2 * F c := by
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ∑ j, (t : ℂ) * c j * z k ^ (j : ℕ) = (t : ℂ) * ∑ j, c j * z k ^ (j : ℕ) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hscale] at hle
  have ht2 : 0 < t ^ 2 := by positivity
  have : F c₀ * s ≤ F c := by
    have h1 : t ^ 2 * (F c₀ * s) ≤ t ^ 2 * F c := by
      calc t ^ 2 * (F c₀ * s) = F c₀ * (t ^ 2 * s) := by ring
        _ = F c₀ := by rw [hts, mul_one]
        _ ≤ t ^ 2 * F c := hle
    exact le_of_mul_le_mul_left h1 ht2
  linarith

/-! ### The sampling law -/

theorem toeplitzForm_shadowMoment {ℓ : ℝ} {r : ℕ} (c w : Fin r → ℝ) {n : ℕ} (v : Fin n → ℂ) :
    toeplitzForm (shadowMoment ℓ c w) n v =
      ∑ k, (w k : ℂ) * ((‖∑ j, v j * shadowNode ℓ c k ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [show shadowMoment ℓ c w = fun m => ∑ k, (w k : ℂ) * shadowNode ℓ c k ^ m from
    funext fun m => shadowMoment_eq_nodes ℓ c w m]
  exact toeplitzForm_atomic _ (norm_shadowNode ℓ c) w v

/-- **Sampling law for periodic on-line configurations.** A weighted on-line periodic
configuration with `r` distinct ordinates per period `2π/ℓ` and positive weights satisfies
`Sh(f) ≥ A ∫|f|²` with some `A > 0` on all tests of aperture `a` iff `⌈2a/ℓ⌉ ≤ r`. -/
theorem onLineShadow_sampling_iff {ℓ : ℝ} (hℓ : 0 < ℓ) {r : ℕ} (c w : Fin r → ℝ)
    (hw : ∀ k, 0 < w k) (hc : Function.Injective (shadowNode ℓ c)) {a : ℝ} (ha : 0 < a) :
    (∃ A : ℝ, 0 < A ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        A * ∫ t, ‖f t‖ ^ 2 ≤ onLineShadow ℓ c w f) ↔ ⌈2 * a / ℓ⌉₊ ≤ r := by
  constructor
  · -- above Nyquist the vanishing polynomial is a massive test with zero shadow
    rintro ⟨A, hA, hsamp⟩
    by_contra hlt
    push Not at hlt
    set n := ⌈2 * a / ℓ⌉₊ with hn
    set Q : Polynomial ℂ := ∏ k, (Polynomial.X - Polynomial.C (shadowNode ℓ c k)) with hQ
    have hQm : Q.Monic := Polynomial.monic_prod_of_monic _ _ fun k _ =>
      Polynomial.monic_X_sub_C _
    have hQd : Q.natDegree = r := by
      rw [hQ, Polynomial.natDegree_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _]
      simp
    set v : Fin n → ℂ := fun j => Q.coeff j with hv
    have hvr : v ⟨r, hlt⟩ = 1 := by
      simp only [hv]
      rw [← hQd]
      exact hQm.coeff_natDegree
    have heval : ∀ k, ∑ j, v j * shadowNode ℓ c k ^ (j : ℕ) = 0 := by
      intro k
      have h1 : Q.eval (shadowNode ℓ c k) = 0 := by
        rw [hQ, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
      rw [← h1, Polynomial.eval_eq_sum_range' (by omega : Q.natDegree < n),
        ← Fin.sum_univ_eq_sum_range (fun j => Q.coeff j * shadowNode ℓ c k ^ j)]
    obtain ⟨f, hf, hfs, B, hB, hlag⟩ := exists_bumpTest_universal hℓ ha v
    have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
    -- zero shadow
    have hsh : onLineShadow ℓ c w f = 0 := by
      have h1 := onLineShadow_eq_lagSum hℓ c w hf hfc
      have hzero : (∑ k, (w k : ℂ) *
          ((‖∑ j, v j * shadowNode ℓ c k ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ)) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [heval k, norm_zero]
        simp
      rw [hlag, toeplitzForm_shadowMoment, hzero, mul_zero, mul_zero] at h1
      exact_mod_cast h1
    -- positive mass
    have hmass : ∫ t, ‖f t‖ ^ 2 = B * ∑ j, ‖v j‖ ^ 2 := by
      have h1 := hlag lagDelta
      have hl : ∑' m : ℤ, EF.weilTest f f (m * ℓ) * lagDelta m = EF.weilTest f f 0 := by
        rw [tsum_eq_single 0 fun m hm => by rw [lagDelta, if_neg hm, mul_zero]]
        rw [lagDelta, if_pos rfl, mul_one, Int.cast_zero, zero_mul]
      rw [hl, weilTest_self_zero, toeplitzForm_lagDelta, ← Complex.ofReal_mul] at h1
      exact_mod_cast h1
    have hv0 : 0 < ∑ j, ‖v j‖ ^ 2 := by
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ ⟨r, hlt⟩))
      simp [hvr]
    have := hsamp f hf hfs
    rw [hsh, hmass] at this
    have : 0 < A * (B * ∑ j, ‖v j‖ ^ 2) := by positivity
    linarith
  · -- below Nyquist the atomic floor is a sampling constant
    intro hnr
    obtain ⟨A₀, hA₀, hfloor⟩ := exists_atomic_floor hnr (shadowNode ℓ c) hc w hw
    refine ⟨ℓ * A₀, by positivity, fun f hf hfs => ?_⟩
    have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
    have hT' : ∀ v : Fin ⌈2 * a / ℓ⌉₊ → ℂ,
        0 ≤ (toeplitzForm (shiftSymbol (shadowMoment ℓ c w) A₀) ⌈2 * a / ℓ⌉₊ v).re := by
      intro v
      rw [toeplitzForm_shiftSymbol, toeplitzForm_shadowMoment, Complex.sub_re, Complex.ofReal_re]
      have h1 := hfloor v
      have h2 : (∑ k, (w k : ℂ) * ((‖∑ j, v j * shadowNode ℓ c k ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ)).re =
          ∑ k, w k * ‖∑ j, v j * shadowNode ℓ c k ^ (j : ℕ)‖ ^ 2 := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      rw [h2]
      linarith
    have h := re_lagSum_nonneg_of_toeplitz hℓ _ hT' hf hfs
    rw [lagSum_shiftSymbol hℓ hfc, mul_sub, ← onLineShadow_eq_lagSum hℓ c w hf hfc,
      Complex.sub_re, Complex.ofReal_re,
      show ((ℓ : ℝ) : ℂ) * ((A₀ : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
        ((ℓ * A₀ * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re] at h
    linarith

end GaloisForLFunctions.SquareRootThreshold
