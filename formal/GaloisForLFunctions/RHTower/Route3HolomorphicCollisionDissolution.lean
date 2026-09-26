import GaloisForLFunctions.RHTower.XiHorizontalCollisionTwoPrimeCesaroCarrier
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus

/-!
# Route 3 closure: holomorphic two-prime clocks dissolve the collision quantum

The two-prime Cesàro carrier of `XiHorizontalCollisionTwoPrimeCesaroCarrier` uses the reflected
character product `χ_p(ρ) χ_p(1 - conj ρ)`, a pure phase that depends on `Im ρ` alone.  Its Cesàro
excess tends to the collision charge `K(T) ∈ 2ℕ`, so it carries a quantum of two.

That summand is holomorphic in `ρ` times antiholomorphic in `ρ` at the same point, so no explicit
formula produces it.  The clock that an explicit formula does produce at the lattice point
`X = 4^a 9^b` is the holomorphic one, `χ_p(ρ)^2 = p^{2(ρ - 1/2)}`.  This module proves the
exchange law between the two:

* on a window whose zeros are all critical the two pencils coincide, so the holomorphic excess
  tends to `0`;
* on a window with an off-line zero the holomorphic excess is not eventually bounded by any
  constant.

So the source-realizable excess reads `∞ · K(T)`: it has no finite quantum, any finite bound would
already force RH, and the quantum margin of two exists only on the zero-indexed side.  The
mechanism is the reflection law `‖χ_p(1 - conj s)‖ · ‖χ_p(s)‖ = 1`: every free orbit contributes
exactly one exponentially growing mode.  Positive multiplicities forbid alias cancellation among
the dominant modes.

The last theorem records why no transversality argument can exclude collisions.  Under the
functional-equation symmetry `F(1 - conj s) = conj (F s)` an off-line zero forces a collision, and
such collisions persist under locally uniform symmetric perturbation (Hurwitz).
-/

open Complex Set Metric Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Reflection law for prime clocks -/

theorem route3_lineReflect_eq_self_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) :
    lineReflect z = z := by
  apply Complex.ext
  · simp only [lineReflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp [lineReflect]

theorem route3_lineReflect_im (z : ℂ) : (lineReflect z).im = z.im := by
  simp [lineReflect]

theorem route3_norm_burnolPrimeCharacter {p : ℝ} (hp : 0 < p) (s : ℂ) :
    ‖burnolPrimeCharacter p s‖ = p ^ (s.re - 1 / 2) := by
  rw [burnolPrimeCharacter, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  simp

/-- **Reflection law.**  A prime clock and its critical-line reflection have reciprocal moduli:
one partner of every free orbit grows exactly as fast as the other decays. -/
theorem route3_norm_burnolPrimeCharacter_lineReflect_mul {p : ℝ} (hp : 0 < p) (s : ℂ) :
    ‖burnolPrimeCharacter p (lineReflect s)‖ * ‖burnolPrimeCharacter p s‖ = 1 := by
  rw [route3_norm_burnolPrimeCharacter hp, route3_norm_burnolPrimeCharacter hp,
    ← Real.rpow_add hp, lineReflect_re]
  have hexp : 1 - s.re - 1 / 2 + (s.re - 1 / 2) = 0 := by ring
  rw [hexp, Real.rpow_zero]

/-! ## The holomorphic two-prime pencil -/

/-- The explicit-formula-realizable two-prime pencil: clocks `p^{2(ρ - 1/2)}`. -/
def xiHolomorphicTwoPrimePencil (T : ℝ) (a b : ℕ) : ℂ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    ((analyticOrderAt xi rho).toNat : ℂ) *
      (burnolPrimeCharacter 2 rho * burnolPrimeCharacter 2 rho) ^ a *
      (burnolPrimeCharacter 3 rho * burnolPrimeCharacter 3 rho) ^ b

/-- Centered two-prime Cesàro energy of the holomorphic pencil. -/
def xiHolomorphicTwoPrimeExcess (T : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹ ^ (2 : ℕ)) *
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        ‖xiHolomorphicTwoPrimePencil T a b‖ ^ (2 : ℕ) -
    xiStripWindowLocalSquareSum T

/-- On a critical window the holomorphic pencil is the reflected-character pencil. -/
theorem xiHolomorphicTwoPrimePencil_eq_source_of_onLine {T : ℝ}
    (hline : ∀ rho ∈ (stripZeros_finite T).toFinset, rho.re = 1 / 2) (a b : ℕ) :
    xiHolomorphicTwoPrimePencil T a b =
      xiHorizontalCollisionTwoPrimeSourcePencil T a b := by
  unfold xiHolomorphicTwoPrimePencil xiHorizontalCollisionTwoPrimeSourcePencil
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [route3_lineReflect_eq_self_of_re_eq_half (hline rho hrho)]

/-- Zero collision charge forces every zero of the window onto the critical line. -/
theorem route3_re_eq_half_of_collisionCharge_eq_zero {T : ℝ}
    (h : xiHorizontalCollisionCharge T = 0) {rho : ℂ}
    (hrho : rho ∈ (stripZeros_finite T).toFinset) : rho.re = 1 / 2 := by
  by_contra hne
  have hle := xiStripWindowOffLineOrder_le_horizontalCollisionCharge T
  rw [h] at hle
  have hzero : xiStripWindowOffLineOrder T = 0 := Nat.le_zero.mp hle
  unfold xiStripWindowOffLineOrder at hzero
  have hmem : rho ∈ (stripZeros_finite T).toFinset.filter (fun r => r.re ≠ 1 / 2) :=
    Finset.mem_filter.mpr ⟨hrho, hne⟩
  have hterm := (Finset.sum_eq_zero_iff.mp hzero) rho hmem
  have hxi : xi rho = 0 := ((stripZeros_finite T).mem_toFinset.mp hrho).2
  exact xi_order_toNat_ne_zero hxi hterm

/-- A window whose zeros are all critical has zero collision charge: two distinct critical points
never share an ordinate. -/
theorem route3_collisionCharge_eq_zero_of_onLine {T : ℝ}
    (hline : ∀ rho ∈ (stripZeros_finite T).toFinset, rho.re = 1 / 2) :
    xiHorizontalCollisionCharge T = 0 := by
  unfold xiHorizontalCollisionCharge
  apply Finset.sum_eq_zero
  intro rho hrho
  rw [horizontalMultiplicity_sub_order_eq_sum_same_im_erase hrho]
  have hempty : (((stripZeros_finite T).toFinset.filter
      (fun z => z.im = rho.im)).erase rho) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    have hzne := (Finset.mem_erase.mp hz).1
    have hzF := (Finset.mem_erase.mp hz).2
    have hzS := (Finset.mem_filter.mp hzF).1
    have hzim := (Finset.mem_filter.mp hzF).2
    apply hzne
    apply Complex.ext
    · rw [hline z hzS, hline rho hrho]
    · exact hzim
  rw [hempty, Finset.sum_empty, mul_zero]

/-- **Exchange law, critical side.**  Zero collision charge makes the holomorphic excess tend to
zero. -/
theorem tendsto_xiHolomorphicTwoPrimeExcess_zero_of_charge_eq_zero {T : ℝ}
    (h : xiHorizontalCollisionCharge T = 0) :
    Tendsto (xiHolomorphicTwoPrimeExcess T) atTop (nhds 0) := by
  have hsrc := tendsto_xiHorizontalCollisionTwoPrimeSourceExcess T
  rw [h, Nat.cast_zero] at hsrc
  have hline : ∀ rho ∈ (stripZeros_finite T).toFinset, rho.re = 1 / 2 :=
    fun rho hrho => route3_re_eq_half_of_collisionCharge_eq_zero h hrho
  refine hsrc.congr' (Eventually.of_forall fun N => ?_)
  unfold xiHolomorphicTwoPrimeExcess xiHorizontalCollisionTwoPrimeSourceExcess
  simp_rw [xiHolomorphicTwoPrimePencil_eq_source_of_onLine hline]

/-! ## Off-line windows: exponential growth -/

/-- Diagonal clock `36^{ρ - 1/2}`. -/
def route3DiagonalClock (rho : ℂ) : ℂ :=
  (burnolPrimeCharacter 2 rho * burnolPrimeCharacter 2 rho) *
    (burnolPrimeCharacter 3 rho * burnolPrimeCharacter 3 rho)

theorem xiHolomorphicTwoPrimePencil_diag (T : ℝ) (n : ℕ) :
    xiHolomorphicTwoPrimePencil T n n =
      ∑ rho ∈ (stripZeros_finite T).toFinset,
        ((analyticOrderAt xi rho).toNat : ℂ) * route3DiagonalClock rho ^ n := by
  unfold xiHolomorphicTwoPrimePencil route3DiagonalClock
  apply Finset.sum_congr rfl
  intro rho _
  simp only [mul_pow]
  ring

theorem route3_norm_diagonalClock (rho : ℂ) :
    ‖route3DiagonalClock rho‖ = (36 : ℝ) ^ (rho.re - 1 / 2) := by
  unfold route3DiagonalClock
  rw [norm_mul, norm_mul, norm_mul, route3_norm_burnolPrimeCharacter (by norm_num),
    route3_norm_burnolPrimeCharacter (by norm_num)]
  rw [← Real.mul_rpow (by norm_num) (by norm_num), ← Real.mul_rpow (by norm_num) (by norm_num),
    ← Real.mul_rpow (by norm_num) (by norm_num)]
  norm_num

theorem route3_one_lt_norm_diagonalClock {rho : ℂ} (h : 1 / 2 < rho.re) :
    1 < ‖route3DiagonalClock rho‖ := by
  rw [route3_norm_diagonalClock]
  exact Real.one_lt_rpow (by norm_num) (by linarith)

/-- A finite exponential pencil whose maximal modes carry a nonzero aggregated coefficient does
not decay after division by the maximal radius. -/
theorem route3_not_tendsto_normalized_finitePencil
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c z : ι → ℂ) {r : ℝ} (hr : 0 < r)
    (hle : ∀ i ∈ S, ‖z i‖ ≤ r)
    (hfiber : ∃ u ∈ (S.filter fun i => ‖z i‖ = r).image (fun i => z i / (r : ℂ)),
      finiteExponentialFiberCoefficient (S.filter fun i => ‖z i‖ = r) c
        (fun i => z i / (r : ℂ)) u ≠ 0) :
    ¬ Tendsto (fun n : ℕ => ∑ i ∈ S, c i * (z i / (r : ℂ)) ^ n) atTop (nhds 0) := by
  set D := S.filter fun i => ‖z i‖ = r with hD
  set E := S.filter fun i => ¬ ‖z i‖ = r with hE
  have hsplit (n : ℕ) :
      (∑ i ∈ S, c i * (z i / (r : ℂ)) ^ n) =
        finiteExponentialPencil D c (fun i => z i / (r : ℂ)) n +
          ∑ i ∈ E, c i * (z i / (r : ℂ)) ^ n := by
    rw [finiteExponentialPencil, hD, hE, Finset.sum_filter_add_sum_filter_not]
  have hnormr (i : ι) : ‖z i / (r : ℂ)‖ = ‖z i‖ / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have htail : Tendsto (fun n : ℕ => ∑ i ∈ E, c i * (z i / (r : ℂ)) ^ n)
      atTop (nhds 0) := by
    have hterm : ∀ i ∈ E, Tendsto (fun n : ℕ => c i * (z i / (r : ℂ)) ^ n)
        atTop (nhds 0) := by
      intro i hi
      have hiS := (Finset.mem_filter.mp hi).1
      have hne := (Finset.mem_filter.mp hi).2
      have hlt : ‖z i / (r : ℂ)‖ < 1 := by
        rw [hnormr, div_lt_one hr]
        exact lt_of_le_of_ne (hle i hiS) hne
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt)
    simpa using tendsto_finsetSum E hterm
  have hunit : ∀ i ∈ D, ‖z i / (r : ℂ)‖ = 1 := by
    intro i hi
    rw [hnormr, (Finset.mem_filter.mp hi).2, div_self hr.ne']
  have hdom := not_tendsto_finiteExponentialPencil_zero_of_fiberCoefficient D c
    (fun i => z i / (r : ℂ)) hunit hfiber
  intro hfull
  apply hdom
  have hdiff := hfull.sub htail
  simpa using hdiff.congr' (Eventually.of_forall fun n => by
    rw [hsplit n]
    ring)

/-- **Exchange law, off-line side.**  A window with nonzero collision charge has a holomorphic
two-prime excess that is not eventually bounded by any constant. -/
theorem not_eventually_bounded_xiHolomorphicTwoPrimeExcess_of_charge_ne_zero {T : ℝ}
    (h : xiHorizontalCollisionCharge T ≠ 0) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, xiHolomorphicTwoPrimeExcess T N ≤ C := by
  classical
  set S := (stripZeros_finite T).toFinset with hS
  -- an off-line zero, hence a zero strictly right of the line
  have hoff : ∃ rho ∈ S, rho.re ≠ 1 / 2 := by
    by_contra hall
    push Not at hall
    apply h
    exact route3_collisionCharge_eq_zero_of_onLine hall
  obtain ⟨rho₀, hrho₀S, hrho₀ne⟩ := hoff
  have hright : ∃ rho ∈ S, 1 / 2 < rho.re := by
    rcases lt_or_gt_of_ne hrho₀ne with hlt | hgt
    · refine ⟨lineReflect rho₀, ?_, ?_⟩
      · rw [hS, Set.Finite.mem_toFinset]
        exact lineReflect_mem_stripZeros ((stripZeros_finite T).mem_toFinset.mp hrho₀S)
      · rw [lineReflect_re]
        linarith
    · exact ⟨rho₀, hrho₀S, hgt⟩
  obtain ⟨rho₁, hrho₁S, hrho₁⟩ := hright
  have hSne : S.Nonempty := ⟨rho₁, hrho₁S⟩
  obtain ⟨rmax, hrmaxS, hrmax⟩ := S.exists_max_image (fun rho => ‖route3DiagonalClock rho‖) hSne
  set r := ‖route3DiagonalClock rmax‖ with hr
  have hr1 : 1 < r := lt_of_lt_of_le (route3_one_lt_norm_diagonalClock hrho₁) (hrmax rho₁ hrho₁S)
  have hr0 : 0 < r := by linarith
  let c : ℂ → ℂ := fun rho => ((analyticOrderAt xi rho).toNat : ℂ)
  -- the dominant fiber through `rmax` has positive integer coefficient
  have hfiber : ∃ u ∈ (S.filter fun i => ‖route3DiagonalClock i‖ = r).image
        (fun i => route3DiagonalClock i / (r : ℂ)),
      finiteExponentialFiberCoefficient (S.filter fun i => ‖route3DiagonalClock i‖ = r) c
        (fun i => route3DiagonalClock i / (r : ℂ)) u ≠ 0 := by
    refine ⟨route3DiagonalClock rmax / (r : ℂ),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hrmaxS, rfl⟩), ?_⟩
    unfold finiteExponentialFiberCoefficient
    have hcast : (∑ i ∈ (S.filter fun i => ‖route3DiagonalClock i‖ = r) with
          route3DiagonalClock i / (r : ℂ) = route3DiagonalClock rmax / (r : ℂ), c i) =
        (((∑ i ∈ (S.filter fun i => ‖route3DiagonalClock i‖ = r) with
          route3DiagonalClock i / (r : ℂ) = route3DiagonalClock rmax / (r : ℂ),
            (analyticOrderAt xi i).toNat : ℕ) : ℂ)) := by
      push_cast
      rfl
    rw [hcast, Nat.cast_ne_zero]
    have hmem : rmax ∈ (S.filter fun i => ‖route3DiagonalClock i‖ = r).filter
        (fun i => route3DiagonalClock i / (r : ℂ) = route3DiagonalClock rmax / (r : ℂ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hrmaxS, rfl⟩, rfl⟩
    have hpos : 0 < (analyticOrderAt xi rmax).toNat :=
      Nat.pos_of_ne_zero (xi_order_toNat_ne_zero
        ((stripZeros_finite T).mem_toFinset.mp hrmaxS).2)
    have hle := Finset.single_le_sum
      (f := fun i => (analyticOrderAt xi i).toNat) (fun i _ => Nat.zero_le _) hmem
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le hpos hle)
  have hnot := route3_not_tendsto_normalized_finitePencil S c route3DiagonalClock hr0
    (fun i hi => hrmax i hi) hfiber
  -- frequent lower bound for the normalized diagonal pencil
  have hfreq : ∃ ε > 0, ∃ᶠ n : ℕ in atTop,
      ε ≤ ‖∑ i ∈ S, c i * (route3DiagonalClock i / (r : ℂ)) ^ n‖ := by
    by_contra hcon
    push Not at hcon
    apply hnot
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(hcon ε hε).mono fun n hn => hn] with n hn
    simpa [dist_zero_right] using hn
  obtain ⟨ε, hε, hfreqε⟩ := hfreq
  -- rescaling identity on the diagonal
  have hdiag (n : ℕ) : ‖xiHolomorphicTwoPrimePencil T n n‖ =
      r ^ n * ‖∑ i ∈ S, c i * (route3DiagonalClock i / (r : ℂ)) ^ n‖ := by
    rw [xiHolomorphicTwoPrimePencil_diag]
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have : (∑ rho ∈ S, ((analyticOrderAt xi rho).toNat : ℂ) * route3DiagonalClock rho ^ n) =
        (r : ℂ) ^ n * ∑ i ∈ S, c i * (route3DiagonalClock i / (r : ℂ)) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [div_pow]
      field_simp
      exact mul_comm _ _
    rw [← hS, this, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  -- the excess at `n + 1` dominates the diagonal term
  have hexcess (n : ℕ) : ((n + 1 : ℕ) : ℝ)⁻¹ ^ (2 : ℕ) * ‖xiHolomorphicTwoPrimePencil T n n‖ ^ 2 -
      xiStripWindowLocalSquareSum T ≤ xiHolomorphicTwoPrimeExcess T (n + 1) := by
    unfold xiHolomorphicTwoPrimeExcess
    have hn : n ∈ Finset.range (n + 1) := Finset.self_mem_range_succ n
    have h1 : ‖xiHolomorphicTwoPrimePencil T n n‖ ^ 2 ≤
        ∑ b ∈ Finset.range (n + 1), ‖xiHolomorphicTwoPrimePencil T n b‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun b => ‖xiHolomorphicTwoPrimePencil T n b‖ ^ (2 : ℕ))
        (fun b _ => sq_nonneg _) hn
    have h2 : (∑ b ∈ Finset.range (n + 1), ‖xiHolomorphicTwoPrimePencil T n b‖ ^ (2 : ℕ)) ≤
        ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1),
          ‖xiHolomorphicTwoPrimePencil T a b‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (n + 1),
          ‖xiHolomorphicTwoPrimePencil T a b‖ ^ (2 : ℕ))
        (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) hn
    have hw : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ ^ (2 : ℕ) := by positivity
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hw
    linarith
  -- growth beats the polynomial normalization
  rintro ⟨C, hC⟩
  set L : ℝ := (xiStripWindowLocalSquareSum T : ℝ)
  have hr2 : 1 < r ^ 2 := by nlinarith
  have hpoly : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 / (r ^ 2) ^ n) atTop (nhds 0) := by
    have hbase := tendsto_pow_const_div_const_pow_of_one_lt 2 hr2
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    have hmul := hshift.const_mul (r ^ 2)
    rw [mul_zero] at hmul
    refine hmul.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have hK : 0 < ε ^ 2 / (|C| + |L| + 1) := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ 2 / (r ^ 2) ^ n < ε ^ 2 / (|C| + |L| + 1) :=
    (tendsto_order.mp hpoly).2 _ hK
  have hCshift : ∀ᶠ n : ℕ in atTop, xiHolomorphicTwoPrimeExcess T (n + 1) ≤ C :=
    (tendsto_add_atTop_nat 1).eventually hC
  obtain ⟨n, hnε, hnsmall, hnC⟩ := (hfreqε.and_eventually (hsmall.and hCshift)).exists
  have hden : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hpow : 0 < (r ^ 2) ^ n := by positivity
  have hlower : ε ^ 2 * (r ^ 2) ^ n ≤ ‖xiHolomorphicTwoPrimePencil T n n‖ ^ 2 := by
    rw [hdiag, mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]
    have := pow_le_pow_left₀ hε.le hnε 2
    nlinarith [pow_pos hr0 n, sq_nonneg (r ^ n)]
  have hbig : |C| + |L| + 1 < ε ^ 2 * (r ^ 2) ^ n / ((n : ℝ) + 1) ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hnsmall
    rw [lt_div_iff₀ hden]
    nlinarith
  have hex := hexcess n
  have hcastn : ((n + 1 : ℕ) : ℝ)⁻¹ ^ (2 : ℕ) = 1 / ((n : ℝ) + 1) ^ 2 := by
    push_cast
    rw [inv_pow, one_div]
  rw [hcastn] at hex
  have hdivle : ε ^ 2 * (r ^ 2) ^ n / ((n : ℝ) + 1) ^ 2 ≤
      1 / ((n : ℝ) + 1) ^ 2 * ‖xiHolomorphicTwoPrimePencil T n n‖ ^ 2 := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hlower hden.le
  have hCabs : C ≤ |C| := le_abs_self C
  have hLabs : L ≤ |L| := le_abs_self L
  linarith

/-- **Exchange law.**  The holomorphic excess is eventually bounded exactly when the collision
charge vanishes, whereas the reflected excess always converges to the charge itself. -/
theorem route3_exchangeLaw (T : ℝ) :
    Tendsto (xiHorizontalCollisionTwoPrimeSourceExcess T) atTop
        (nhds (xiHorizontalCollisionCharge T : ℝ)) ∧
      ((∃ C : ℝ, ∀ᶠ N : ℕ in atTop, xiHolomorphicTwoPrimeExcess T N ≤ C) ↔
        xiHorizontalCollisionCharge T = 0) := by
  refine ⟨tendsto_xiHorizontalCollisionTwoPrimeSourceExcess T, ?_, ?_⟩
  · intro hbound
    by_contra hne
    exact not_eventually_bounded_xiHolomorphicTwoPrimeExcess_of_charge_ne_zero hne hbound
  · intro h0
    refine ⟨1, ?_⟩
    exact (tendsto_xiHolomorphicTwoPrimeExcess_zero_of_charge_eq_zero h0).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))

/-- RH through the holomorphic pencil: every finite constant bound suffices, the margin is
infinite. -/
theorem riemannHypothesis_iff_forall_xiHolomorphicTwoPrimeExcess_bounded :
    RiemannHypothesis ↔
      ∀ T : ℝ, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, xiHolomorphicTwoPrimeExcess T N ≤ C := by
  rw [riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero]
  exact forall_congr' fun T => ((route3_exchangeLaw T).2).symm

/-! ## Collisions are Hurwitz-stable under the functional-equation symmetry -/

/-- **Collision stability.**  Let `Fn → F` locally uniformly with every `Fn` symmetric under the
critical-line reflection, `Fn (1 - conj s) = conj (Fn s)`.  If `F` has an off-line zero isolated
by a sphere of radius smaller than its distance to the line, then eventually every `Fn` has two
distinct zeros with the same ordinate.  Collisions of symmetric functions are an open condition,
not a codimension condition. -/
theorem eventually_exists_horizontalCollision_of_tendstoLocallyUniformly
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn F atTop)
    (hF : Differentiable ℂ F) (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hsym : ∀ n s, Fn n (lineReflect s) = starRingEnd ℂ (Fn n s))
    {rho : ℂ} {r : ℝ} (hr : 0 < r) (hrδ : r < |rho.re - 1 / 2|) (hz : F rho = 0)
    (hsphere : ∀ w ∈ sphere rho r, F w ≠ 0) :
    ∀ᶠ n in atTop, ∃ w w' : ℂ, Fn n w = 0 ∧ Fn n w' = 0 ∧ w.im = w'.im ∧ w ≠ w' := by
  filter_upwards [GaloisForLFunctions.HTGeometry.eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
    hconv hF hFn hr hz hsphere] with n hn
  obtain ⟨w, hw, hw0⟩ := hn
  refine ⟨w, lineReflect w, hw0, ?_, (route3_lineReflect_im w).symm, ?_⟩
  · rw [hsym, hw0, map_zero]
  · intro heq
    have hre : w.re = 1 / 2 := by
      have := congrArg Complex.re heq
      rw [lineReflect_re] at this
      linarith
    have hdist : |w.re - rho.re| ≤ r := by
      have h1 : |w.re - rho.re| ≤ ‖w - rho‖ := by
        rw [← Complex.sub_re]
        exact Complex.abs_re_le_norm _
      exact h1.trans (by simpa [dist_eq_norm] using hw)
    rw [hre] at hdist
    have : |rho.re - 1 / 2| ≤ r := by
      rw [abs_sub_comm]
      exact hdist
    linarith

end

end RHTower
