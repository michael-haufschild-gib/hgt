import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ANonRealPairAloneOnTopOfATwoSidedEdit
import GaloisForLFunctions.FloorFreeArithmetic.SystemsThatOnlyAddPrimesVanishAtTheirRealAbscissa

/-!
# The balance law of two-sided edits

For a set `T` of primes let `κ(T)` be its exponent: the abscissa of `Σ_{p ∈ T} p^{−σ}` (`expo`).
An edit has the exponents `κ₊` of its doubled primes and `κ₋` of its deleted primes.  Let `G` be a
holomorphic continuation of `(s − 1) ζ_B(s)` to `Re s > 1/2`.

* **A positive Euler factor does not continue** (`not_differentiableOn_exp_gdSeries`).  If `D` is
  a general Dirichlet series with nonnegative coefficients and real abscissa `σ_c`, no function
  holomorphic on a disc around `σ_c` equals `exp D` right of `σ_c`: such a function would vanish
  at `σ_c`, and `|exp D| ≥ 1` on the real axis.
* **Thickness** (`re_le_of_fake_zero`).  Every fake zero has `Re ρ ≤ max(κ₊, κ₋, 1/2)`: right of
  both exponents `G = (s − 1) ζ(s) · exp(convergent)`.  An edit with both exponents at most `1/2`
  is no fake (`not_isIntegerNormFakeAt_of_expo_le`).
* **No surplus of doubled primes** (`expo_plus_le`).  `κ₊ ≤ max(κ₋, 1/2)`: otherwise
  `exp(Σ_{p doubled} p^{−s})` would continue across `κ₊`.
* **A surplus of deleted primes is a real zero** (`zero_at_expo_minus`).  If
  `κ₋ > max(κ₊, 1/2)` then `G(κ₋) = 0`: Landau's zero on top of a deletion.
* **Balance** (`balance`).  If `G` has no real zero in `(1/2, ∞)` then
  `max(κ₊, 1/2) = max(κ₋, 1/2)`.  For the greedy edit at a non-real `ρ` with `ζ(ρ) ≠ 0`:
  `κ₊ = κ₋ = Re ρ` (`expo_edit_eq`).

So a finite non-real layer on top of an edit of the rational primes exists exactly at balance,
and it costs both sides the exponent of its real part.
-/

open Complex Metric Filter Topology
open RHTower RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.RigidArithmeticOfCuts GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw

open PrimeEdits TwoSidedEdits

/-! ## Positive Euler factors do not continue across their real abscissa -/

section Landau

variable {ι : Type*} {a lam : ι → ℝ}

theorem re_gdSeries_ofReal_nonneg (ha : ∀ j, 0 ≤ a j) (σ : ℝ) :
    0 ≤ (gdSeries a lam (σ : ℂ)).re := by
  have h : gdSeries a lam (σ : ℂ) = ((∑' j, a j * Real.exp (-(σ * lam j)) : ℝ) : ℂ) := by
    rw [gdSeries, Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    simp [Complex.ofReal_exp]
  rw [h, Complex.ofReal_re]
  exact tsum_nonneg fun j => mul_nonneg (ha j) (Real.exp_pos _).le

/-- **A positive Euler factor does not continue across its real abscissa.** -/
theorem not_differentiableOn_exp_gdSeries (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σc : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0))
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0))
    {r : ℝ} (hr : 0 < r) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball (σc : ℂ) r))
    (hagree : ∀ s ∈ ball (σc : ℂ) r, σc < s.re → F s = cexp (gdSeries a lam s)) : False := by
  classical
  set E : ℂ → ℂ := fun s => if σc < s.re then cexp (gdSeries a lam s) else F s with hE
  have hEF : ∀ s ∈ ball (σc : ℂ) r, E s = F s := by
    intro s hs
    by_cases h : σc < s.re
    · simp only [hE, if_pos h]
      exact (hagree s hs h).symm
    · simp only [hE, if_neg h]
  have hzero := FloorFreeArithmetic.eulerFactor_abscissa_eq_zero ha hlam hsum hdiv (E := E)
    (fun s hs => by simp only [hE, if_pos hs]) hr (hF.congr hEF)
  have hF0 : F (σc : ℂ) = 0 := by
    rw [← hEF _ (mem_ball_self hr)]
    exact hzero
  -- but `‖F‖ ≥ 1` on the real axis right of `σ_c`
  have hcont : ContinuousAt F (σc : ℂ) := hF.continuousOn.continuousAt (ball_mem_nhds _ hr)
  have hev : ∀ᶠ s in 𝓝 (σc : ℂ), ‖F s‖ < 1 := by
    have h := hcont.norm
    rw [ContinuousAt, hF0, norm_zero] at h
    exact h.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := min ε r / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hε hr)
  have hdist : dist (((σc + δ : ℝ)) : ℂ) (σc : ℂ) = δ := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      add_sub_cancel_left, abs_of_pos hδ0]
  have hmem : ((σc + δ : ℝ) : ℂ) ∈ ball (σc : ℂ) r := by
    rw [mem_ball, hdist, hδ]
    linarith [min_le_right ε r]
  have h1 := hεF (y := ((σc + δ : ℝ) : ℂ)) (by rw [hdist, hδ]; linarith [min_le_left ε r])
  rw [hagree _ hmem (by rw [Complex.ofReal_re]; linarith), Complex.norm_exp] at h1
  have h2 : 1 ≤ Real.exp (gdSeries a lam ((σc + δ : ℝ) : ℂ)).re :=
    Real.one_le_exp (re_gdSeries_ofReal_nonneg ha (σc + δ))
  linarith

end Landau

/-! ## Sets of primes as general Dirichlet series -/

/-- The weight of a set: its indicator. -/
def wt (T : Set ℕ) (p : ℕ) : ℝ := T.indicator (fun _ => (1 : ℝ)) p

/-- The frequency `log p`. -/
def freq (p : ℕ) : ℝ := Real.log p

theorem wt_nonneg (T : Set ℕ) (p : ℕ) : 0 ≤ wt T p :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) p

theorem wt_le_one (T : Set ℕ) (p : ℕ) : wt T p ≤ 1 := by
  classical
  unfold wt
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

theorem freq_nonneg (p : ℕ) : 0 ≤ freq p := Real.log_natCast_nonneg p

/-- `Σ_{p ∈ T} p^{−σ}` converges. -/
def SummableAt (T : Set ℕ) (σ : ℝ) : Prop := Summable (gdTwistTerm (wt T) freq σ 0)

theorem gdTwistTerm_wt (T : Set ℕ) (σ : ℝ) (p : ℕ) :
    gdTwistTerm (wt T) freq σ 0 p = wt T p * Real.exp (-(σ * freq p)) := by
  rw [gdTwistTerm, pow_zero, mul_one]

theorem SummableAt.mono {T : Set ℕ} {σ σ' : ℝ} (h : SummableAt T σ) (hσ : σ ≤ σ') :
    SummableAt T σ' := by
  refine Summable.of_nonneg_of_le (fun p => gdTwistTerm_nonneg (wt_nonneg T) freq_nonneg _ _ p)
    (fun p => ?_) h
  rw [gdTwistTerm_wt, gdTwistTerm_wt]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (wt_nonneg T p)
  nlinarith [freq_nonneg p]

theorem exp_neg_mul_freq {p : ℕ} (hp : 0 < p) (σ : ℝ) :
    Real.exp (-(σ * freq p)) = (p : ℝ) ^ (-σ) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hp), freq]
  congr 1
  ring

/-- Every set is summable right of `1`. -/
theorem summableAt_of_one_lt (T : Set ℕ) {σ : ℝ} (hσ : 1 < σ) : SummableAt T σ := by
  classical
  have hfin : Summable fun p : ℕ => if p = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun p hp => by
      rw [Finset.mem_singleton] at hp
      exact if_neg hp
  refine Summable.of_nonneg_of_le (fun p => gdTwistTerm_nonneg (wt_nonneg T) freq_nonneg _ _ p)
    (fun p => ?_) ((Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)).add hfin)
  rw [gdTwistTerm_wt]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h0 : freq 0 = 0 := by simp [freq]
    rw [h0, mul_zero, neg_zero, Real.exp_zero, mul_one, if_pos rfl]
    have := wt_le_one T 0
    have h00 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (by simp) _
    linarith
  · rw [exp_neg_mul_freq hp, if_neg hp.ne', add_zero]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p) _) (wt_le_one T p)

/-- The doubled and the deleted primes of an edit that is summable at `σ`. -/
theorem summableAt_of_edit {e : ℕ → ℤ} (he : IsEdit e) {σ : ℝ}
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-σ)) :
    SummableAt (plusSet e) σ ∧ SummableAt (minusSet e) σ := by
  classical
  have hterm : ∀ (T : Set ℕ), (∀ p ∈ T, |(e p : ℝ)| = 1) → SummableAt T σ := by
    intro T hT
    refine Summable.of_nonneg_of_le
      (fun p => gdTwistTerm_nonneg (wt_nonneg T) freq_nonneg _ _ p) (fun p => ?_) hS
    rw [gdTwistTerm_wt, wt]
    by_cases h : p ∈ T
    · have hpp : p.Prime := by
        by_contra hnp
        have h1 := hT p h
        rw [he.prime p hnp] at h1
        norm_num at h1
      rw [Set.indicator_of_mem h, one_mul, hT p h, one_mul, exp_neg_mul_freq hpp.pos]
    · rw [Set.indicator_of_notMem h, zero_mul]
      exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  refine ⟨hterm _ fun p hp => ?_, hterm _ fun p hp => ?_⟩
  · have h : e p = 1 := hp
    rw [h]; simp
  · have h : e p = -1 := hp
    rw [h]; simp

theorem norm_gd_term (T : Set ℕ) (s : ℂ) (p : ℕ) :
    ‖(wt T p : ℂ) * cexp (-(s * (freq p : ℂ)))‖ = gdTwistTerm (wt T) freq s.re 0 p := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg T p),
    Complex.norm_exp, gdTwistTerm_wt]
  congr 2
  simp

/-- The edit series is the difference of the two prime series. -/
theorem LSeries_edit_eq {e : ℕ → ℤ} (he : IsEdit e) {s : ℂ}
    (hp : SummableAt (plusSet e) s.re) (hm : SummableAt (minusSet e) s.re) :
    LSeries (fun k => (e k : ℂ)) s =
      gdSeries (wt (plusSet e)) freq s - gdSeries (wt (minusSet e)) freq s := by
  classical
  have hsp : Summable fun p : ℕ => (wt (plusSet e) p : ℂ) * cexp (-(s * (freq p : ℂ))) :=
    Summable.of_norm ((show Summable (gdTwistTerm (wt (plusSet e)) freq s.re 0) from hp).congr
      fun p => (norm_gd_term _ s p).symm)
  have hsm : Summable fun p : ℕ => (wt (minusSet e) p : ℂ) * cexp (-(s * (freq p : ℂ))) :=
    Summable.of_norm ((show Summable (gdTwistTerm (wt (minusSet e)) freq s.re 0) from hm).congr
      fun p => (norm_gd_term _ s p).symm)
  rw [gdSeries, gdSeries, ← hsp.tsum_sub hsm, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : e 0 = 0 := he.prime 0 Nat.not_prime_zero
    simp [wt, plusSet, minusSet, h0]
  · have hexp : cexp (-(s * (freq n : ℂ))) = ((n : ℂ) ^ s)⁻¹ := by
      rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), freq,
        Complex.natCast_log]
      congr 1
      ring
    rw [LSeries.term_of_ne_zero hn, ← sub_mul, hexp, div_eq_mul_inv]
    congr 1
    rcases he.range n with h | h | h <;> simp [wt, plusSet, minusSet, h]

/-! ## The continuation right of both exponents -/

/-- Identity theorem on a right half-plane, from agreement on `Re s > 1`. -/
theorem eqOn_halfPlane {c : ℝ} {F₁ F₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ F₁ {s : ℂ | c < s.re})
    (h₂ : DifferentiableOn ℂ F₂ {s : ℂ | c < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → F₁ s = F₂ s) : Set.EqOn F₁ F₂ {s : ℂ | c < s.re} := by
  have hU : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  set z₀ : ℂ := ((max c 1 + 1 : ℝ) : ℂ) with hz₀
  have hmem : z₀ ∈ {s : ℂ | c < s.re} := by
    show c < z₀.re
    rw [hz₀, Complex.ofReal_re]
    linarith [le_max_left c 1]
  have hev : F₁ =ᶠ[𝓝 z₀] F₂ := by
    have hU1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    refine eventuallyEq_of_mem (hU1.mem_nhds ?_) fun s hs => heq s hs
    show 1 < z₀.re
    rw [hz₀, Complex.ofReal_re]
    linarith [le_max_right c 1]
  exact (h₁.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (h₂.analyticOnNhd hU)
    (convex_halfSpace_re_gt c).isPreconnected hmem hev

theorem differentiableOn_gdSeries_wt {T : Set ℕ} {c : ℝ} (h : ∀ σ, c < σ → SummableAt T σ) :
    DifferentiableOn ℂ (gdSeries (wt T) freq) {s : ℂ | c < s.re} := fun s hs =>
  (differentiableAt_gdSeries (wt_nonneg T) freq_nonneg (h ((c + s.re) / 2)
    (by have : c < s.re := hs; linarith)) (by have : c < s.re := hs; linarith)).differentiableWithinAt

/-- **The continuation right of both exponents**: `G = (s − 1) ζ(s) exp(D₊ − D₋ + Q)`, on every
half-plane `Re s > c₀` on which `G` and the prime-power remainder `Q` are holomorphic. -/
theorem continuation_eq {e : ℕ → ℤ} (he : IsEdit e) {G : ℂ → ℂ} {c₀ : ℝ}
    (hG : DifferentiableOn ℂ G {s : ℂ | c₀ < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hQ : DifferentiableOn ℂ (editRem e) {s : ℂ | c₀ < s.re})
    {c : ℝ} (hc : c₀ ≤ c) (hc1 : c ≤ 1)
    (hp : ∀ σ, c < σ → SummableAt (plusSet e) σ) (hm : ∀ σ, c < σ → SummableAt (minusSet e) σ)
    {s : ℂ} (hs : c < s.re) :
    G s = zetaResidueUnit s * cexp (gdSeries (wt (plusSet e)) freq s -
      gdSeries (wt (minusSet e)) freq s + editRem e s) := by
  have hsub : {s : ℂ | c < s.re} ⊆ {s : ℂ | c₀ < s.re} := fun z hz => by
    have : c < z.re := hz
    show c₀ < z.re
    linarith
  refine eqOn_halfPlane (c := c) (F₂ := fun z => zetaResidueUnit z *
    cexp (gdSeries (wt (plusSet e)) freq z - gdSeries (wt (minusSet e)) freq z + editRem e z))
    (hG.mono hsub) ?_ (fun z hz => ?_) hs
  · refine differentiable_zetaResidueUnit.differentiableOn.mul (DifferentiableOn.cexp ?_)
    exact ((differentiableOn_gdSeries_wt hp).sub (differentiableOn_gdSeries_wt hm)).add
      (hQ.mono hsub)
  · have hz1 : z ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
    rw [hGeq z hz, editSystem_zetaSeriesC he hz,
      LSeries_edit_eq he (hp _ (lt_of_le_of_lt hc1 hz)) (hm _ (lt_of_le_of_lt hc1 hz)),
      zetaResidueUnit_of_ne hz1]
    ring

/-- Right of both exponents the continuation vanishes only at the zeros of `ζ`. -/
theorem zero_iff_of_re_gt {e : ℕ → ℤ} (he : IsEdit e) {G : ℂ → ℂ} {c₀ : ℝ}
    (hG : DifferentiableOn ℂ G {s : ℂ | c₀ < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hQ : DifferentiableOn ℂ (editRem e) {s : ℂ | c₀ < s.re})
    {c : ℝ} (hc : c₀ ≤ c) (hc1 : c ≤ 1)
    (hp : ∀ σ, c < σ → SummableAt (plusSet e) σ) (hm : ∀ σ, c < σ → SummableAt (minusSet e) σ)
    {z : ℂ} (hz : c < z.re) (hz1 : z ≠ 1) : G z = 0 ↔ riemannZeta z = 0 := by
  rw [continuation_eq he hG hGeq hQ hc hc1 hp hm hz, zetaResidueUnit_of_ne hz1]
  simp [Complex.exp_ne_zero, sub_eq_zero, hz1]

/-! ## The two unbalanced cases -/

/-- A small disc around a real point `κ > c₀` inside `Re s > c₀` on which a function that is
continuous and nonzero at `κ` does not vanish. -/
theorem exists_ball_ne_zero {f : ℂ → ℂ} {κ c₀ : ℝ} (hκ : c₀ < κ)
    (hcont : ContinuousAt f (κ : ℂ)) (hne : f (κ : ℂ) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ (∀ s ∈ ball (κ : ℂ) r, c₀ < s.re) ∧ ∀ s ∈ ball (κ : ℂ) r, f s ≠ 0 := by
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hne)
  refine ⟨min ε (κ - c₀), lt_min hε (by linarith), fun s hs => ?_, fun s hs => ?_⟩
  · have h1 : dist s (κ : ℂ) < κ - c₀ := lt_of_lt_of_le (mem_ball.mp hs) (min_le_right _ _)
    have h2 := Complex.abs_re_le_norm (s - (κ : ℂ))
    rw [Complex.dist_eq] at h1
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    have h3 := neg_abs_le (s.re - κ)
    linarith
  · exact hεf (lt_of_lt_of_le (mem_ball.mp hs) (min_le_left _ _))

/-- **No surplus of doubled primes.**  If the doubled primes have a real abscissa `κ > 1/2` and
the deleted primes are summable left of `κ`, `(s − 1) ζ_B(s)` has no holomorphic continuation to
`Re s > 1/2`. -/
theorem not_plus_heavy {e : ℕ → ℤ} (he : IsEdit e) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    {κ κ' : ℝ} (hκ : 1 / 2 < κ) (hκ1 : κ ≤ 1) (hκ' : κ' < κ)
    (hm : SummableAt (minusSet e) κ') (hp : ∀ σ, κ < σ → SummableAt (plusSet e) σ)
    (hpd : ∀ σ, σ < κ → ¬ SummableAt (plusSet e) σ) : False := by
  set c₀ : ℝ := max κ' (1 / 2) with hc₀
  have hc₀κ : c₀ < κ := max_lt hκ' hκ
  have hu : zetaResidueUnit (κ : ℂ) ≠ 0 := zetaResidueUnit_ofReal_ne_zero hκ
  obtain ⟨r, hr, hre, hune⟩ := exists_ball_ne_zero hc₀κ
    (differentiable_zetaResidueUnit.continuous.continuousAt) hu
  have hsubh : ball (κ : ℂ) r ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    lt_of_le_of_lt (le_max_right κ' (1 / 2)) (hre s hs)
  have hsubm : ball (κ : ℂ) r ⊆ {s : ℂ | κ' < s.re} := fun s hs =>
    lt_of_le_of_lt (le_max_left κ' (1 / 2)) (hre s hs)
  have hDm : DifferentiableOn ℂ (gdSeries (wt (minusSet e)) freq) (ball (κ : ℂ) r) := fun s hs =>
    (differentiableAt_gdSeries (wt_nonneg _) freq_nonneg hm (hsubm hs)).differentiableWithinAt
  set F : ℂ → ℂ := fun s =>
    G s * cexp (gdSeries (wt (minusSet e)) freq s - editRem e s) / zetaResidueUnit s with hF
  have hFd : DifferentiableOn ℂ F (ball (κ : ℂ) r) :=
    ((hG.mono hsubh).mul (DifferentiableOn.cexp
      (hDm.sub ((differentiableOn_editRem he).mono hsubh)))).div
      differentiable_zetaResidueUnit.differentiableOn hune
  refine not_differentiableOn_exp_gdSeries (wt_nonneg (plusSet e)) freq_nonneg hp hpd hr hFd
    fun s hs hsκ => ?_
  have hGs := continuation_eq he hG hGeq (differentiableOn_editRem he) hκ.le hκ1 hp
    (fun σ hσ => hm.mono (by linarith)) hsκ
  have hsplit : cexp (gdSeries (wt (plusSet e)) freq s - gdSeries (wt (minusSet e)) freq s +
      editRem e s) * cexp (gdSeries (wt (minusSet e)) freq s - editRem e s) =
      cexp (gdSeries (wt (plusSet e)) freq s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [hF]
  rw [hGs, mul_assoc, hsplit, mul_div_assoc, mul_comm, div_mul_cancel₀ _ (hune s hs)]

/-- **A surplus of deleted primes is a real zero.**  Let `G` continue `(s − 1) ζ_B(s)` to
`Re s > c₀`, where the prime-power remainder is holomorphic.  If the deleted primes have a real
abscissa `κ > c₀` and the doubled primes are summable left of `κ`, then `G(κ) = 0`. -/
theorem zero_of_minus_heavy {e : ℕ → ℤ} (he : IsEdit e) {G : ℂ → ℂ} {c₀ : ℝ}
    (hG : DifferentiableOn ℂ G {s : ℂ | c₀ < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hQ : DifferentiableOn ℂ (editRem e) {s : ℂ | c₀ < s.re})
    {κ κ' : ℝ} (hκ : c₀ < κ) (hκ1 : κ ≤ 1) (hκ' : κ' < κ)
    (hp : SummableAt (plusSet e) κ') (hm : ∀ σ, κ < σ → SummableAt (minusSet e) σ)
    (hmd : ∀ σ, σ < κ → ¬ SummableAt (minusSet e) σ) : G (κ : ℂ) = 0 := by
  by_contra hne
  set c₁ : ℝ := max κ' c₀ with hc₁
  have hc₁κ : c₁ < κ := max_lt hκ' hκ
  have hUo : IsOpen {s : ℂ | c₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hκmem : (κ : ℂ) ∈ {s : ℂ | c₀ < s.re} := by
    show c₀ < (κ : ℂ).re
    rw [Complex.ofReal_re]; exact hκ
  obtain ⟨r, hr, hre, hGne⟩ := exists_ball_ne_zero hc₁κ
    (hG.continuousOn.continuousAt (hUo.mem_nhds hκmem)) hne
  have hsubh : ball (κ : ℂ) r ⊆ {s : ℂ | c₀ < s.re} := fun s hs =>
    lt_of_le_of_lt (le_max_right κ' c₀) (hre s hs)
  have hsubp : ball (κ : ℂ) r ⊆ {s : ℂ | κ' < s.re} := fun s hs =>
    lt_of_le_of_lt (le_max_left κ' c₀) (hre s hs)
  have hDp : DifferentiableOn ℂ (gdSeries (wt (plusSet e)) freq) (ball (κ : ℂ) r) := fun s hs =>
    (differentiableAt_gdSeries (wt_nonneg _) freq_nonneg hp (hsubp hs)).differentiableWithinAt
  set F : ℂ → ℂ := fun s =>
    zetaResidueUnit s * cexp (gdSeries (wt (plusSet e)) freq s + editRem e s) / G s with hF
  have hFd : DifferentiableOn ℂ F (ball (κ : ℂ) r) :=
    (differentiable_zetaResidueUnit.differentiableOn.mul (DifferentiableOn.cexp
      (hDp.add (hQ.mono hsubh)))).div (hG.mono hsubh) hGne
  refine not_differentiableOn_exp_gdSeries (wt_nonneg (minusSet e)) freq_nonneg hm hmd hr hFd
    fun s hs hsκ => ?_
  have hGs := continuation_eq he hG hGeq hQ hκ.le hκ1
    (fun σ hσ => hp.mono (by linarith)) hm hsκ
  have hGs0 := hGne s hs
  have hsplit : cexp (gdSeries (wt (plusSet e)) freq s + editRem e s) =
      cexp (gdSeries (wt (minusSet e)) freq s) *
        cexp (gdSeries (wt (plusSet e)) freq s - gdSeries (wt (minusSet e)) freq s +
          editRem e s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [hF]
  rw [eq_comm, eq_div_iff hGs0, hGs, hsplit]
  ring

/-! ## The exponent of a set of primes -/

/-- The exponent of a set: the infimum of the `σ ≥ 0` at which `Σ_{p ∈ T} p^{−σ}` converges. -/
def expo (T : Set ℕ) : ℝ := sInf {σ : ℝ | 0 ≤ σ ∧ SummableAt T σ}

theorem expo_set_nonempty (T : Set ℕ) : {σ : ℝ | 0 ≤ σ ∧ SummableAt T σ}.Nonempty :=
  ⟨2, by norm_num, summableAt_of_one_lt T (by norm_num)⟩

theorem expo_set_bddBelow (T : Set ℕ) : BddBelow {σ : ℝ | 0 ≤ σ ∧ SummableAt T σ} :=
  ⟨0, fun _ hσ => hσ.1⟩

theorem expo_nonneg (T : Set ℕ) : 0 ≤ expo T :=
  le_csInf (expo_set_nonempty T) fun _ hσ => hσ.1

theorem summableAt_of_expo_lt {T : Set ℕ} {σ : ℝ} (h : expo T < σ) : SummableAt T σ := by
  obtain ⟨σ', hσ', hlt⟩ := exists_lt_of_csInf_lt (expo_set_nonempty T) h
  exact hσ'.2.mono hlt.le

theorem expo_le_of_summableAt {T : Set ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (h : SummableAt T σ) :
    expo T ≤ σ :=
  csInf_le (expo_set_bddBelow T) ⟨hσ, h⟩

theorem expo_le_one (T : Set ℕ) : expo T ≤ 1 := by
  by_contra h
  have h1 : 1 < expo T := not_le.mp h
  have := expo_le_of_summableAt (T := T) (σ := (1 + expo T) / 2) (by linarith [expo_nonneg T])
    (summableAt_of_one_lt T (by linarith))
  linarith

theorem not_summableAt_of_lt_expo {T : Set ℕ} {σ : ℝ} (hpos : 0 < expo T) (h : σ < expo T) :
    ¬ SummableAt T σ := by
  intro hs
  have := expo_le_of_summableAt (T := T) (σ := max σ 0) (le_max_right _ _)
    (hs.mono (le_max_left _ _))
  exact absurd this (not_le.mpr (max_lt h hpos))

/-! ## Thickness, the two surpluses, balance -/

variable {e : ℕ → ℤ} {G : ℂ → ℂ}

/-- **Thickness.**  A fake zero lies at or left of the larger exponent. -/
theorem re_le_of_fake_zero (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    {z : ℂ} (hz1 : z ≠ 1) (hz : G z = 0) (hζ : riemannZeta z ≠ 0) :
    z.re ≤ max (max (expo (plusSet e)) (expo (minusSet e))) (1 / 2) := by
  by_contra h
  have h' : max (max (expo (plusSet e)) (expo (minusSet e))) (1 / 2) < z.re := not_le.mp h
  refine hζ ((zero_iff_of_re_gt he hG hGeq (differentiableOn_editRem he) (le_max_right _ _)
    (max_le (max_le (expo_le_one _) (expo_le_one _)) (by norm_num))
    (fun σ hσ => summableAt_of_expo_lt ?_) (fun σ hσ => summableAt_of_expo_lt ?_) h' hz1).mp hz)
  · exact lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hσ
  · exact lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hσ

/-- An edit with both exponents at most `1/2` is no fake. -/
theorem not_isIntegerNormFakeAt_of_expo_le (he : IsEdit e) (hp : expo (plusSet e) ≤ 1 / 2)
    (hm : expo (minusSet e) ≤ 1 / 2) (β : ℝ) : ¬ IsIntegerNormFakeAt (editSystem e) β := by
  rintro ⟨-, -, -, -, G, hG, hGeq, ρ₀, hρ₀, hρ₀1, hzero, hζ⟩
  have h := re_le_of_fake_zero he hG hGeq hρ₀1 hzero hζ
  have : max (max (expo (plusSet e)) (expo (minusSet e))) (1 / 2) ≤ 1 / 2 :=
    max_le (max_le hp hm) le_rfl
  linarith

/-- **No surplus of doubled primes.** -/
theorem expo_plus_le (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) :
    expo (plusSet e) ≤ max (expo (minusSet e)) (1 / 2) := by
  by_contra h
  have h' : max (expo (minusSet e)) (1 / 2) < expo (plusSet e) := not_le.mp h
  have hκ : 1 / 2 < expo (plusSet e) := lt_of_le_of_lt (le_max_right _ _) h'
  have hκm : expo (minusSet e) < expo (plusSet e) := lt_of_le_of_lt (le_max_left _ _) h'
  exact not_plus_heavy he hG hGeq hκ (expo_le_one _)
    (κ' := (expo (minusSet e) + expo (plusSet e)) / 2) (by linarith)
    (summableAt_of_expo_lt (by linarith)) (fun σ hσ => summableAt_of_expo_lt hσ)
    (fun σ hσ => not_summableAt_of_lt_expo (by linarith) hσ)

/-- **A surplus of deleted primes is a real zero** at their exponent. -/
theorem zero_at_expo_minus (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (h : max (expo (plusSet e)) (1 / 2) < expo (minusSet e)) :
    G ((expo (minusSet e) : ℝ) : ℂ) = 0 := by
  have hκ : 1 / 2 < expo (minusSet e) := lt_of_le_of_lt (le_max_right _ _) h
  have hκp : expo (plusSet e) < expo (minusSet e) := lt_of_le_of_lt (le_max_left _ _) h
  exact zero_of_minus_heavy he hG hGeq (differentiableOn_editRem he) hκ (expo_le_one _)
    (κ' := (expo (plusSet e) + expo (minusSet e)) / 2) (by linarith)
    (summableAt_of_expo_lt (by linarith)) (fun σ hσ => summableAt_of_expo_lt hσ)
    (fun σ hσ => not_summableAt_of_lt_expo (by linarith) hσ)

/-- **The balance law.**  If the continuation of `(s − 1) ζ_B(s)` has no real zero in
`(1/2, ∞)`, the doubled and the deleted primes have the same exponent above `1/2`. -/
theorem balance (he : IsEdit e)
    (hG : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    (hreal : ∀ x : ℝ, 1 / 2 < x → G (x : ℂ) ≠ 0) :
    max (expo (plusSet e)) (1 / 2) = max (expo (minusSet e)) (1 / 2) := by
  refine le_antisymm (max_le (expo_plus_le he hG hGeq) (le_max_right _ _))
    (max_le ?_ (le_max_right _ _))
  by_contra h
  have h' : max (expo (plusSet e)) (1 / 2) < expo (minusSet e) := not_le.mp h
  exact hreal _ (lt_of_le_of_lt (le_max_right _ _) h') (zero_at_expo_minus he hG hGeq h')

/-- **The greedy edit at a non-real `ρ` is balanced at `Re ρ`**: the doubled and the deleted
primes both have the exponent `Re ρ`. -/
theorem expo_edit_eq {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15) (him : ρ.im ≠ 0)
    (hζ : riemannZeta ρ ≠ 0) :
    expo (plusSet (edit ρ)) = ρ.re ∧ expo (minusSet (edit ρ)) = ρ.re := by
  have he := isEdit_edit ρ
  obtain ⟨C, H, hC, hdiff, hfac⟩ := (isPairTwin_editSystem hρ hρ1).exists_continuation
  set G : ℂ → ℂ := fun s => zetaResidueUnit s *
    (C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * cexp (H s)) with hGdef
  have hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem (edit ρ)).zetaSeriesC s :=
    fun s hs => (hfac s hs).symm
  have hreal : ∀ x : ℝ, 1 / 2 < x → G (x : ℂ) ≠ 0 := by
    intro x hx
    have h1 : (x : ℂ) - ρ ≠ 0 := fun h0 => him (by
      have h' := congrArg Complex.im h0
      simpa using h')
    have h2 : (x : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := fun h0 => him (by
      have h' := congrArg Complex.im h0
      simpa using h')
    exact mul_ne_zero (zetaResidueUnit_ofReal_ne_zero hx)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hC h1) h2) (Complex.exp_ne_zero _))
  have hρne : ρ ≠ 1 := fun h => by rw [h] at hρ1; norm_num at hρ1
  have hGρ : G ρ = 0 := by simp [hGdef]
  -- thinness: both exponents are at most `Re ρ`
  have hupper : ∀ T : Set ℕ, (∀ σ, ρ.re < σ → SummableAt T σ) → expo T ≤ ρ.re := by
    intro T hT
    by_contra h
    have h' : ρ.re < expo T := not_le.mp h
    have := expo_le_of_summableAt (T := T) (σ := (ρ.re + expo T) / 2) (by linarith)
      (hT _ (by linarith))
    linarith
  have hsum : ∀ σ, ρ.re < σ →
      SummableAt (plusSet (edit ρ)) σ ∧ SummableAt (minusSet (edit ρ)) σ := fun σ hσ =>
    summableAt_of_edit he (summable_abs_edit_rpow (by linarith) (by linarith) hσ)
  have hp := hupper _ fun σ hσ => (hsum σ hσ).1
  have hm := hupper _ fun σ hσ => (hsum σ hσ).2
  -- thickness and balance: both are at least `Re ρ`
  have hthick := re_le_of_fake_zero he hdiff hGeq hρne hGρ hζ
  have hbal := balance he hdiff hGeq hreal
  have hmax : ρ.re ≤ max (expo (plusSet (edit ρ))) (expo (minusSet (edit ρ))) := by
    rcases le_max_iff.mp hthick with h | h
    · exact h
    · linarith
  have hp' : ρ.re ≤ expo (plusSet (edit ρ)) := by
    rcases le_max_iff.mp hmax with h | h
    · exact h
    · have h1 : 1 / 2 < expo (minusSet (edit ρ)) := by linarith
      rw [max_eq_left h1.le] at hbal
      rcases le_max_iff.mp hbal.ge with h2 | h2
      · linarith
      · linarith
  have hm' : ρ.re ≤ expo (minusSet (edit ρ)) := by
    have h1 : 1 / 2 < expo (plusSet (edit ρ)) := by linarith
    rw [max_eq_left h1.le] at hbal
    rcases le_max_iff.mp hbal.le with h2 | h2
    · linarith
    · linarith
  exact ⟨le_antisymm hp hp', le_antisymm hm hm'⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw
