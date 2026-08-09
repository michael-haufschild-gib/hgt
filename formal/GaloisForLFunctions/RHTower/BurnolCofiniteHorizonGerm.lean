import GaloisForLFunctions.RHTower.BurnolPrimeCartierWallTrace

/-!
# Cofinite prime-dilation horizons and the maximal-germ nonclosed range

The genuine poles of the forward completion `C_p` lie on the frequency lattice
`λ_{p,k} = 2πik/log p`, `k ≠ 0`, all on the imaginary axis.  Hence the pole-free radius around
`ρ = σ + it` is at least `σ`, and choosing `k` nearest to `t log p /(2π)` shows it is at most
`√(σ² + 9π²/(log p)²)`.  As `log p → ∞` the radius therefore converges exactly to `σ`; the
reflected radius converges to `1 - σ`.

Interior analytic data cannot repair inverse completion.  On every disc of radius `R < σ` the
completion obeys `|C_p(ρ+z)| ≤ A p^{-(σ-R)}`, so the unit coordinates go to zero uniformly while
keeping norm one, and the coefficient field `u_p = p^{-1/2}` — which is not square summable — has
square-summable compact-open germ data.  Its finite truncations therefore converge in every
compact-open seminorm to a germ that is not in the image.
-/

open Complex Real Filter Topology Metric

noncomputable section

namespace RHTower

/-! ## The prime-dilation pole lattice -/

/-- The genuine pole set of the forward completion at logarithmic scale `L`. -/
def burnolSidebandSet (L : ℝ) : Set ℂ :=
  {z : ℂ | ∃ k : ℤ, k ≠ 0 ∧ z = 2 * π * Complex.I * (k : ℂ) / (L : ℂ)}

theorem burnolSidebandSet_re {L : ℝ} {z : ℂ} (hz : z ∈ burnolSidebandSet L) : z.re = 0 := by
  obtain ⟨k, _, rfl⟩ := hz
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_apply]
  ring

theorem burnolSidebandSet_nonempty {L : ℝ} : (burnolSidebandSet L).Nonempty :=
  ⟨2 * π * Complex.I * ((1 : ℤ) : ℂ) / (L : ℂ), 1, one_ne_zero, rfl⟩

/-- **Lower horizon bound.**  Every genuine pole is at distance at least `σ`. -/
theorem burnolSideband_re_le_infDist {L : ℝ} (ρ : ℂ) :
    ρ.re ≤ Metric.infDist ρ (burnolSidebandSet L) := by
  refine (Metric.le_infDist burnolSidebandSet_nonempty).mpr ?_
  intro z hz
  have hre : z.re = 0 := burnolSidebandSet_re hz
  have h := Complex.abs_re_le_norm (ρ - z)
  rw [Complex.dist_eq]
  have hsub : (ρ - z).re = ρ.re := by
    rw [Complex.sub_re, hre, sub_zero]
  rw [hsub] at h
  exact le_trans (le_abs_self _) h

/-- A nonzero lattice index within `3π/L` of the imaginary part. -/
theorem burnolSideband_exists_index {L t : ℝ} (hL : 0 < L) :
    ∃ k : ℤ, k ≠ 0 ∧ |2 * π * (k : ℝ) / L - t| ≤ 3 * π / L := by
  have hπ : 0 < π := Real.pi_pos
  set m : ℤ := round (t * L / (2 * π)) with hm
  by_cases hm0 : m = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have hround : |t * L / (2 * π) - (m : ℝ)| ≤ 1 / 2 := abs_sub_round _
    rw [hm0] at hround
    simp only [Int.cast_zero, sub_zero] at hround
    have ht : |t| ≤ π / L := by
      have h2π : (0 : ℝ) < 2 * π := by positivity
      have habs : |t * L / (2 * π)| = |t| * L / (2 * π) := by
        rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos h2π]
      rw [habs, div_le_iff₀ h2π] at hround
      rw [le_div_iff₀ hL]
      linarith
    have h1 : |2 * π * ((1 : ℤ) : ℝ) / L - t| ≤ |2 * π / L| + |t| := by
      push_cast
      rw [mul_one]
      exact (abs_sub _ _).trans_eq rfl
    have h2 : |2 * π / L| = 2 * π / L := abs_of_pos (by positivity)
    rw [h2] at h1
    have hb : (2 : ℝ) * π / L + π / L = 3 * π / L := by field_simp; ring
    linarith [h1, ht, hb.le, hb.ge]
  · refine ⟨m, hm0, ?_⟩
    have hround : |t * L / (2 * π) - (m : ℝ)| ≤ 1 / 2 := abs_sub_round _
    have hround' : |(m : ℝ) - t * L / (2 * π)| ≤ 1 / 2 := by
      rw [abs_sub_comm]
      exact hround
    have hkey : |2 * π * (m : ℝ) / L - t| = (2 * π / L) * |(m : ℝ) - t * L / (2 * π)| := by
      rw [← abs_of_pos (show (0:ℝ) < 2 * π / L by positivity), ← abs_mul]
      congr 1
      field_simp
    rw [hkey]
    have hpos : (0 : ℝ) < 2 * π / L := by positivity
    have := mul_le_mul_of_nonneg_left hround' hpos.le
    have hval : (2 * π / L) * (1 / 2) = π / L := by field_simp
    rw [hval] at this
    have h3 : π / L ≤ 3 * π / L := by
      rw [div_le_div_iff₀ hL hL]
      nlinarith [hπ, hL]
    linarith

/-- **Upper horizon bound.** -/
theorem burnolSideband_infDist_le {L : ℝ} (hL : 0 < L) (ρ : ℂ) :
    Metric.infDist ρ (burnolSidebandSet L) ≤ Real.sqrt (ρ.re ^ 2 + (3 * π / L) ^ 2) := by
  obtain ⟨k, hk, hkb⟩ := burnolSideband_exists_index (t := ρ.im) hL
  set z : ℂ := 2 * π * Complex.I * (k : ℂ) / (L : ℂ) with hz
  have hzmem : z ∈ burnolSidebandSet L := ⟨k, hk, rfl⟩
  have hzre : z.re = 0 := burnolSidebandSet_re hzmem
  have hzim : z.im = 2 * π * (k : ℝ) / L := by
    rw [hz, Complex.div_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_apply]
    field_simp
    ring
  refine (Metric.infDist_le_dist_of_mem hzmem).trans ?_
  rw [Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq, Complex.sub_re, Complex.sub_im,
    hzre, hzim, sub_zero]
  refine Real.sqrt_le_sqrt ?_
  have habs : |ρ.im - 2 * π * (k : ℝ) / L| ≤ 3 * π / L := by
    rw [abs_sub_comm]
    exact hkb
  nlinarith [abs_nonneg (ρ.im - 2 * π * (k : ℝ) / L), sq_abs (ρ.im - 2 * π * (k : ℝ) / L),
    habs, (by positivity : (0:ℝ) ≤ 3 * π / L)]

/-- **The cofinite radius law.**  As the logarithmic scale grows the forward pole-free radius
converges exactly to the horizontal coordinate. -/
theorem burnolSideband_infDist_tendsto {ρ : ℂ} (hσ : 0 ≤ ρ.re) :
    Tendsto (fun L : ℝ => Metric.infDist ρ (burnolSidebandSet L)) atTop (𝓝 ρ.re) := by
  have hupper : Tendsto (fun L : ℝ => Real.sqrt (ρ.re ^ 2 + (3 * π / L) ^ 2)) atTop
      (𝓝 (Real.sqrt (ρ.re ^ 2 + 0 ^ 2))) := by
    refine (Real.continuous_sqrt.tendsto _).comp ?_
    refine Filter.Tendsto.const_add _ ?_
    have h : Tendsto (fun L : ℝ => 3 * π / L) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    simpa using h.pow 2
  rw [show Real.sqrt (ρ.re ^ 2 + 0 ^ 2) = ρ.re by
    rw [show ρ.re ^ 2 + 0 ^ 2 = ρ.re ^ 2 by ring, Real.sqrt_sq hσ]] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall (fun L => burnolSideband_re_le_infDist ρ)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact burnolSideband_infDist_le hL ρ

/-- **The reflected radius law.**  The reflected pole set is the image of the forward one under
`z ↦ 1 - z`, so its horizon converges to `1 - σ`. -/
theorem burnolSidebandReflected_infDist_tendsto {ρ : ℂ} (hσ : ρ.re ≤ 1) :
    Tendsto (fun L : ℝ => Metric.infDist ((1 : ℂ) - ρ) (burnolSidebandSet L)) atTop
      (𝓝 (1 - ρ.re)) := by
  have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by
    rw [Complex.sub_re, Complex.one_re]
  have h := burnolSideband_infDist_tendsto (ρ := (1 : ℂ) - ρ) (by rw [hre]; linarith)
  rwa [hre] at h

/-! ## The maximal germ has nonclosed range -/

/-- **The uniform interior decay `(CH15)`.** -/
theorem burnolGerm_uniform_decay (ρ : ℂ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < ρ.re) :
    ∃ (A : ℝ) (N : ℕ), 0 < A ∧ ∀ p : ℕ, N ≤ p → 2 ≤ p → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖burnolAllPrimeCompletionMultiplier p (ρ + z)‖ ≤
        A * (p : ℝ) ^ (-(ρ.re - R)) := by
  set δ : ℝ := ρ.re - R with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ x : ℝ, (N : ℝ) ≤ x → 2 ≤ x ^ δ := by
    obtain ⟨M, hM⟩ := (burnolEventually_log_pow_le_rpow hδpos 0).exists_forall_of_atTop
    refine ⟨max 2 ⌈Real.exp (Real.log 2 / δ)⌉₊, ?_⟩
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := le_trans (by exact_mod_cast le_max_left 2 _) hx
    have hexp : Real.exp (Real.log 2 / δ) ≤ x :=
      le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast le_max_right 2 _) hx)
    have hlog : Real.log 2 / δ ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    have hxpos : (0 : ℝ) < x := by linarith
    have : Real.log 2 ≤ δ * Real.log x := by
      rw [div_le_iff₀ hδpos] at hlog
      linarith
    have hpow : (2 : ℝ) ≤ Real.exp (δ * Real.log x) := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (δ * Real.log x) := Real.exp_le_exp.mpr this
    rwa [Real.rpow_def_of_pos hxpos, mul_comm (Real.log x) δ]
  refine ⟨(‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1, max N 2, by positivity, ?_⟩
  intro p hp hp2 z hz
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hpN : (N : ℝ) ≤ (p : ℝ) := by
    have : N ≤ p := le_trans (le_max_left N 2) hp
    exact_mod_cast this
  have hge2 : (2 : ℝ) ≤ (p : ℝ) ^ δ := hN _ hpN
  have hre : (ρ + z).re ≥ δ := by
    have hzre : |z.re| ≤ R := le_trans (Complex.abs_re_le_norm z) hz
    rw [Complex.add_re, hδ]
    have := abs_le.mp hzre
    linarith [this.1]
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ (ρ + z)‖ = (p : ℝ) ^ (ρ + z).re := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hppos]
  have hmono : (p : ℝ) ^ δ ≤ (p : ℝ) ^ (ρ + z).re := by
    refine Real.rpow_le_rpow_of_exponent_le ?_ hre
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_trans (le_max_right N 2) hp
    linarith
  have hden : (p : ℝ) ^ δ / 2 ≤ ‖(p : ℂ) ^ (ρ + z) - 1‖ := by
    have h := norm_sub_norm_le ((p : ℂ) ^ (ρ + z)) 1
    rw [hnorm, norm_one] at h
    linarith [hge2, hmono]
  have hnum : ‖(ρ + z) ^ 2 * ((ρ + z) - 1)‖ ≤ (‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) := by
    have h1 : ‖ρ + z‖ ≤ ‖ρ‖ + R := (norm_add_le _ _).trans (by linarith)
    have h2 : ‖(ρ + z) - 1‖ ≤ ‖ρ‖ + R + 1 := (norm_sub_le _ _).trans (by
      rw [norm_one]; linarith [h1])
    rw [norm_mul, norm_pow]
    have hnn : (0 : ℝ) ≤ ‖ρ + z‖ := norm_nonneg _
    have hsq : ‖ρ + z‖ ^ 2 ≤ (‖ρ‖ + R) ^ 2 := pow_le_pow_left₀ hnn h1 2
    exact mul_le_mul hsq h2 (norm_nonneg _) (by positivity)
  have hdenpos : (0 : ℝ) < (p : ℝ) ^ δ / 2 := by positivity
  have hnormpos : (0 : ℝ) < ‖(p : ℂ) ^ (ρ + z) - 1‖ := lt_of_lt_of_le hdenpos hden
  have hrpow : (p : ℝ) ^ (-δ) * (p : ℝ) ^ δ = 1 := by
    rw [← Real.rpow_add hppos]
    norm_num
  have hCnorm : ‖burnolAllPrimeCompletionMultiplier p (ρ + z)‖ =
      ‖(ρ + z) ^ 2 * ((ρ + z) - 1)‖ / (2 * ‖(p : ℂ) ^ (ρ + z) - 1‖) := by
    rw [burnolAllPrimeCompletionMultiplier, norm_div, norm_mul]
    congr 1
    norm_num
  rw [hCnorm, div_le_iff₀ (by positivity), hδ] at *
  have hAge : (‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) ≤ (‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1 := by linarith
  have hApos : (0 : ℝ) ≤ (‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1 := by positivity
  have hfac : (p : ℝ) ^ δ ≤ 2 * ‖(p : ℂ) ^ (ρ + z) - 1‖ := by linarith [hden]
  calc ‖(ρ + z) ^ 2 * ((ρ + z) - 1)‖
      ≤ (‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1 := by linarith [hnum]
    _ = ((‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1) * ((p : ℝ) ^ (-δ) * (p : ℝ) ^ δ) := by
        rw [hrpow]; ring
    _ ≤ ((‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1) *
        ((p : ℝ) ^ (-δ) * (2 * ‖(p : ℂ) ^ (ρ + z) - 1‖)) := by
        have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ (-δ) := (Real.rpow_pos_of_pos hppos _).le
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac hp0) hApos
    _ = ((‖ρ‖ + R) ^ 2 * (‖ρ‖ + R + 1) + 1) * (p : ℝ) ^ (-δ) *
        (2 * ‖(p : ℂ) ^ (ρ + z) - 1‖) := by ring

/-- Any fixed multiple of a negative real power eventually drops below any positive threshold. -/
theorem burnolDecay_eventually_lt {A δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ x : ℝ, (M : ℝ) ≤ x → A * x ^ (-δ) < ε := by
  have htend : Tendsto (fun x : ℝ => A * x ^ (-δ)) atTop (𝓝 0) := by
    have h := (_root_.tendsto_rpow_neg_atTop hδ).const_mul A
    simpa using h
  obtain ⟨M, hM⟩ := (htend.eventually (eventually_lt_nhds hε)).exists_forall_of_atTop
  exact ⟨⌈M⌉₊, fun x hx => hM x (le_trans (Nat.le_ceil M) hx)⟩

/-- **`(CH16)`.**  The unit coordinates go to zero uniformly on every safe disc, while their
`ℓ²`-norm is one. -/
theorem burnolGerm_unit_tendsto_zero (ρ : ℂ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < ρ.re) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, N ≤ p → 2 ≤ p → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖burnolAllPrimeCompletionMultiplier p (ρ + z)‖ < ε := by
  intro ε hε
  obtain ⟨A, N, hA, hbound⟩ := burnolGerm_uniform_decay ρ hR0 hR
  have hδpos : 0 < ρ.re - R := by linarith
  obtain ⟨M, hM⟩ := burnolDecay_eventually_lt (A := A) hδpos hε
  refine ⟨max N (max M 2), ?_⟩
  intro p hp hp2 z hz
  have hpN : N ≤ p := le_trans (le_max_left N _) hp
  have hpM : (M : ℝ) ≤ (p : ℝ) := by
    have : M ≤ p := le_trans (le_trans (le_max_left M 2) (le_max_right N _)) hp
    exact_mod_cast this
  exact lt_of_le_of_lt (hbound p hpN hp2 z hz) (hM _ hpM)

/-- The critical witness field `u_p = p^{-1/2}` is not square summable. -/
theorem burnolGermWitness_not_summable :
    ¬ Summable (fun p : Nat.Primes =>
      ‖((1 : ℂ) / ((Real.sqrt ((p : ℕ) : ℝ) : ℝ) : ℂ))‖ ^ 2) := by
  intro hsum
  refine burnolNotSummable_prime_one_div (hsum.congr (fun p => ?_))
  have hp : 2 ≤ (p : ℕ) := p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
    have : (0 : ℕ) < (p : ℕ) := by omega
    exact_mod_cast this
  have hsq : Real.sqrt ((p : ℕ) : ℝ) ^ 2 = ((p : ℕ) : ℝ) := Real.sq_sqrt hppos.le
  have hspos : 0 < Real.sqrt ((p : ℕ) : ℝ) := Real.sqrt_pos.mpr hppos
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos, div_pow,
    one_pow, hsq]

/-- **`(CH17)` witness.**  On every safe disc the germ data of the witness field is square
summable, so its finite truncations converge in every compact-open seminorm. -/
theorem burnolGermWitness_summable (ρ : ℂ) {R : ℝ} (hR : R < ρ.re) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * (ρ.re - R) + 1))) := by
  have hδ : 1 < 2 * (ρ.re - R) + 1 := by linarith
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * (ρ.re - R) + 1))⁻¹) :=
    summable_nat_rpow_inv.mpr hδ
  refine (hnat.subtype _).congr (fun p => ?_)
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _)]

/-- **`(CH13)`--`(CH17)`.**  The only possible preimage of the witness germ is the witness field
itself, which is not square summable; hence the maximal-germ image is not closed. -/
theorem burnolGerm_preimage_forced {ρ : ℂ} (hσ0 : 0 < ρ.re) (hσ1 : ρ.re < 1)
    (v : Nat.Primes → ℂ)
    (hv : ∀ p : Nat.Primes, burnolAllPrimeCompletionMultiplier (p : ℕ) ρ * v p =
      burnolAllPrimeCompletionMultiplier (p : ℕ) ρ *
        ((1 : ℂ) / ((Real.sqrt ((p : ℕ) : ℝ) : ℝ) : ℂ))) :
    ¬ Summable (fun p : Nat.Primes => ‖v p‖ ^ 2) := by
  have hvals : ∀ p : Nat.Primes, v p = (1 : ℂ) / ((Real.sqrt ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro p
    have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hCne : burnolAllPrimeCompletionMultiplier (p : ℕ) ρ ≠ 0 :=
      burnolAllPrimeCompletionMultiplier_ne_zero hp hσ0 hσ1
    exact mul_left_cancel₀ hCne (hv p)
  intro hsum
  exact burnolGermWitness_not_summable (hsum.congr (fun p => by rw [hvals p]))

/-! ## The reflected orientation -/

/-- **`(CH17)`.**  The reflected completion decays at rate `p^{-((1-σ)-R)}` on every safe disc. -/
theorem burnolGermReflected_uniform_decay (ρ : ℂ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 - ρ.re) :
    ∃ (A : ℝ) (N : ℕ), 0 < A ∧ ∀ p : ℕ, N ≤ p → 2 ≤ p → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖burnolAllPrimeCompletionMultiplier p (1 - ρ - z)‖ ≤
        A * (p : ℝ) ^ (-((1 - ρ.re) - R)) := by
  have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by rw [Complex.sub_re, Complex.one_re]
  obtain ⟨A, N, hA, hb⟩ := burnolGerm_uniform_decay ((1 : ℂ) - ρ) hR0 (by rw [hre]; exact hR)
  refine ⟨A, N, hA, fun p hp hp2 z hz => ?_⟩
  have h := hb p hp hp2 (-z) (by rwa [norm_neg])
  rw [show (1 : ℂ) - ρ + -z = 1 - ρ - z by ring, hre] at h
  exact h

/-- **`(CH14)`, `(CH16)`, `(CH17)` jointly.**  The unit coordinates collapse to zero in both
orientations simultaneously, while keeping norm one. -/
theorem burnolGermJoint_unit_tendsto_zero (ρ : ℂ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R < ρ.re)
    (hR' : R < 1 - ρ.re) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p : ℕ, N ≤ p → 2 ≤ p → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖burnolAllPrimeCompletionMultiplier p (ρ + z)‖ < ε ∧
      ‖burnolAllPrimeCompletionMultiplier p (1 - ρ - z)‖ < ε := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := burnolGerm_unit_tendsto_zero ρ hR0 hR ε hε
  obtain ⟨A, N₂, hA, hb⟩ := burnolGermReflected_uniform_decay ρ hR0 hR'
  obtain ⟨M, hM⟩ := burnolDecay_eventually_lt (A := A) (show 0 < 1 - ρ.re - R by linarith) hε
  refine ⟨max N₁ (max N₂ M), fun p hp hp2 z hz => ⟨h₁ p (le_trans (le_max_left _ _) hp) hp2 z hz,
    ?_⟩⟩
  have hpM : (M : ℝ) ≤ (p : ℝ) := by
    have : M ≤ p := le_trans (le_trans (le_max_right N₂ M) (le_max_right N₁ _)) hp
    exact_mod_cast this
  exact lt_of_le_of_lt (hb p (le_trans (le_trans (le_max_left N₂ M) (le_max_right N₁ _)) hp)
    hp2 z hz) (hM _ hpM)

/-! ## The reflected sideband trace -/

theorem burnolTendsto_reflect_nhdsWithin (a : ℂ) :
    Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] ((1 : ℂ) - a)) (𝓝[≠] a) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : Tendsto (fun s : ℂ => 1 - s) (𝓝 ((1 : ℂ) - a)) (𝓝 (1 - (1 - a))) :=
      (continuous_const.sub continuous_id).tendsto _
    rw [show (1 : ℂ) - (1 - a) = a by ring] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 1 - a := hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    exact hs' (by linear_combination -hcon)

/-- **`(CH6)`.**  The reflected orientation has a simple pole at `1 - λ_{p,k}` with the sign
reversed residue. -/
theorem tendsto_burnolAllPrimeCompletionReflected_sidebandResidue {p : ℕ} (hp : 2 ≤ p) (k : ℤ) :
    Tendsto (fun s : ℂ => (s - (1 - burnolPrimeSideband p k)) *
        burnolAllPrimeCompletionMultiplierReflected p s)
      (𝓝[≠] ((1 : ℂ) - burnolPrimeSideband p k))
      (𝓝 (-(burnolPrimeSideband p k ^ 2 * (burnolPrimeSideband p k - 1) /
        (2 * ((Real.log (p : ℝ) : ℝ) : ℂ))))) := by
  have h := ((tendsto_burnolAllPrimeCompletion_sidebandResidue hp k).comp
    (burnolTendsto_reflect_nhdsWithin (burnolPrimeSideband p k))).neg
  refine h.congr (fun s => ?_)
  simp only [Function.comp_apply, burnolAllPrimeCompletionMultiplierReflected]
  ring

/-- **`(CH4)`, reflected half.**  Unit-gain recovery of the coefficient from the reflected
sideband principal part. -/
theorem tendsto_burnolCartierReflectedSidebandTrace {p : ℕ} (hp : 2 ≤ p) {k : ℤ}
    (hk : burnolPrimeSideband p k ≠ 0) (u : ℂ) :
    Tendsto (fun s : ℂ => -(2 * ((Real.log (p : ℝ) : ℝ) : ℂ) /
        ((burnolPrimeSideband p k) ^ 2 * (burnolPrimeSideband p k - 1))) *
        ((s - (1 - burnolPrimeSideband p k)) *
          (burnolAllPrimeCompletionMultiplierReflected p s * u)))
      (𝓝[≠] ((1 : ℂ) - burnolPrimeSideband p k)) (𝓝 u) := by
  set lam : ℂ := burnolPrimeSideband p k with hlam
  have hLne := burnolPrimeLogC_ne_zero hp
  have hlamOne : lam - 1 ≠ 0 := burnolPrimeSideband_sub_one_ne_zero p k
  have h := ((tendsto_burnolAllPrimeCompletionReflected_sidebandResidue hp k).mul_const
    u).const_mul (-(2 * ((Real.log (p : ℝ) : ℝ) : ℂ) / (lam ^ 2 * (lam - 1))))
  have hval : -(2 * ((Real.log (p : ℝ) : ℝ) : ℂ) / (lam ^ 2 * (lam - 1))) *
      (-(lam ^ 2 * (lam - 1) / (2 * ((Real.log (p : ℝ) : ℝ) : ℂ))) * u) = u := by
    field_simp
  rw [hval] at h
  refine h.congr (fun s => ?_)
  ring

end RHTower
