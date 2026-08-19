import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound

/-!
# The high-height tail law for centered reciprocal square tests

With `w_ρ = ρ − 1/2` and `y_ρ = −w_ρ^{-2}` (the corpus's `xiCentralReciprocalSquare`), and
`p = X^j q`, the reciprocal square test

```text
Q_r[p] = ∑_ρ m_ρ ‖y_ρ‖^r ‖p(y_ρ)‖²
```

has high-height tail

```text
∑_{|γ_ρ| > G} m_ρ ‖y_ρ‖^r ‖p(y_ρ)‖² = O(G^{1−2r−4j} log G).
```

The mechanism is elementary once the corpus's Jensen zero count is in hand: on the critical strip
`‖w_ρ‖ ≥ |γ_ρ|`, so `‖y_ρ‖ ≤ |γ_ρ|^{-2}`; a polynomial with a zero of order `j` at the origin
satisfies `‖p(y)‖ ≤ C_q ‖y‖^j` on the closed unit disc; and dyadic summation against the divisor
mass of a disc, which the Jensen bound controls by `O(R log R)`, converges for every exponent
`2r + 4j > 1`.
-/

open Complex Metric Filter MeromorphicOn Finset

namespace RHTower

noncomputable section

/-! ## Divisor mass of a disc -/

/-- **`mass(|z| ≤ R) ≪ R log R`.**  The Jensen bound in the form used by the dyadic tail. -/
theorem exists_xiRegionOrderSum_closedBall_upper_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 2 ≤ R →
      (xiRegionOrderSum (closedBall (0 : ℂ) R) : ℝ) ≤ c * R * Real.log R := by
  obtain ⟨C, hC, hgrow⟩ := orderOneEnvelope_xi
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(9 * C + 1) / Real.log 2, by positivity, fun R hR => ?_⟩
  have hR0 : (0 : ℝ) < R := by linarith
  have hlogR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hlogR0 : (0 : ℝ) < Real.log R := lt_of_lt_of_le hlog2 hlogR
  refine le_trans (xiRegionOrderSum_closedBall_le hC hgrow hR0) ?_
  rw [div_le_iff₀ hlog2]
  have hlogbound : Real.log (2 + 2 * R) ≤ 3 * Real.log R := by
    have hstep : Real.log (2 + 2 * R) ≤ Real.log (4 * R) :=
      Real.log_le_log (by linarith) (by linarith)
    have hval : Real.log (4 * R) = Real.log 4 + Real.log R :=
      Real.log_mul (by norm_num) hR0.ne'
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have hle : Real.log 4 ≤ 2 * Real.log R := by rw [h4]; linarith
    linarith [hstep, hval]
  have hlin : C * (1 + 2 * R) * Real.log (2 + 2 * R) ≤ 9 * C * (R * Real.log R) := by
    calc C * (1 + 2 * R) * Real.log (2 + 2 * R)
        ≤ (C * (3 * R)) * (3 * Real.log R) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) hlogbound
            (Real.log_nonneg (by linarith)) (by positivity)
      _ = 9 * C * (R * Real.log R) := by ring
  have hlog2le : Real.log 2 ≤ R * Real.log R := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ R - 1) hlogR0.le, hlogR]
  have hrhs : (9 * C + 1) / Real.log 2 * R * Real.log R * Real.log 2
      = (9 * C + 1) * (R * Real.log R) := by field_simp
  rw [hrhs]
  linarith [hlin, hlog2le]

/-! ## Finite multiplicity sums are dominated by region masses -/

theorem sum_multiplicity_le_xiRegionOrderSum {S : Set ℂ} (hS : IsCompact S)
    (s : Finset ↥(MeromorphicOn.divisor xi Set.univ).support)
    (hmem : ∀ ρ ∈ s, (ρ : ℂ) ∈ S) :
    (∑ ρ ∈ s, ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ))
      ≤ (xiRegionOrderSum S : ℝ) := by
  classical
  set F := ((MeromorphicOn.divisor xi S).finiteSupport hS).toFinset with hF
  have hsupp : Function.support ⇑(MeromorphicOn.divisor xi S) ⊆ ↑F := by
    rw [hF, Set.Finite.coe_toFinset]
  have hsum : xiRegionOrderSum S = ∑ u ∈ F, MeromorphicOn.divisor xi S u := by
    rw [xiRegionOrderSum, finsum_eq_sum_of_support_subset _ hsupp]
  have hval : ∀ ρ ∈ s, MeromorphicOn.divisor xi S (ρ : ℂ)
      = MeromorphicOn.divisor xi Set.univ (ρ : ℂ) := by
    intro ρ hρ
    rw [xi_divisor_apply_of_mem (hmem ρ hρ), xi_divisor_apply_of_mem (Set.mem_univ _)]
  set T : Finset ℂ :=
    Finset.image (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support => (ρ : ℂ)) s with hT
  have himg : T ⊆ F := by
    intro z hz
    rw [hT, Finset.mem_image] at hz
    obtain ⟨ρ, hρs, hzeq⟩ := hz
    refine hsupp ?_
    have hpos := xi_divisor_pos_on_support ρ
    refine Function.mem_support.mpr ?_
    rw [← hzeq, hval ρ hρs]
    omega
  have hstep1 : (∑ ρ ∈ s, (MeromorphicOn.divisor xi Set.univ (ρ : ℂ) : ℤ))
      = ∑ ρ ∈ s, (MeromorphicOn.divisor xi S (ρ : ℂ) : ℤ) :=
    (Finset.sum_congr rfl fun ρ hρ => (hval ρ hρ).symm)
  have hstep2 : (∑ ρ ∈ s, (MeromorphicOn.divisor xi S (ρ : ℂ) : ℤ))
      = ∑ z ∈ T, (MeromorphicOn.divisor xi S z : ℤ) := by
    rw [hT, Finset.sum_image (fun x _ y _ hxy => Subtype.ext hxy)]
  have hstep3 : (∑ z ∈ T, (MeromorphicOn.divisor xi S z : ℤ))
      ≤ ∑ u ∈ F, MeromorphicOn.divisor xi S u :=
    Finset.sum_le_sum_of_subset_of_nonneg himg (fun u _ _ => xi_divisor_nonneg S u)
  have hfinal : (∑ ρ ∈ s, (MeromorphicOn.divisor xi Set.univ (ρ : ℂ) : ℤ))
      ≤ xiRegionOrderSum S := by
    rw [hsum, hstep1, hstep2]
    exact hstep3
  exact_mod_cast hfinal

/-! ## The pointwise high-height bound -/

theorem abs_im_le_norm_centered (ρ : ℂ) : |ρ.im| ≤ ‖ρ - 1 / 2‖ := by
  have hre : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
  have him : (ρ - 1 / 2).im = ρ.im := by simp
  have hsq : ‖ρ - 1 / 2‖ ^ 2 = (ρ.re - 1 / 2) ^ 2 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hnn : (0 : ℝ) ≤ ‖ρ - 1 / 2‖ := norm_nonneg _
  nlinarith [sq_nonneg (ρ.re - 1 / 2), sq_abs ρ.im]

theorem norm_xiCentralReciprocalSquare_le {ρ : ℂ} (him : 0 < |ρ.im|) :
    ‖xiCentralReciprocalSquare ρ‖ ≤ 1 / |ρ.im| ^ 2 := by
  have hle := abs_im_le_norm_centered ρ
  have hpos : (0 : ℝ) < ‖ρ - 1 / 2‖ := lt_of_lt_of_le him hle
  rw [xiCentralReciprocalSquare, norm_neg, norm_pow, norm_inv]
  rw [inv_pow, div_eq_mul_inv, one_mul]
  have hsq : |ρ.im| ^ 2 ≤ ‖ρ - 1 / 2‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
  have hres := (inv_le_inv₀ (by positivity : (0:ℝ) < ‖ρ - 1 / 2‖ ^ 2)
    (by positivity : (0:ℝ) < |ρ.im| ^ 2)).mpr hsq
  simpa [one_div] using hres

/-- A polynomial is bounded on the closed unit disc by its coefficient mass. -/
def polyCoeffMass (q : Polynomial ℂ) : ℝ :=
  ∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖

theorem polyCoeffMass_nonneg (q : Polynomial ℂ) : 0 ≤ polyCoeffMass q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_eval_le_polyCoeffMass (q : Polynomial ℂ) {y : ℂ} (hy : ‖y‖ ≤ 1) :
    ‖q.eval y‖ ≤ polyCoeffMass q := by
  rw [Polynomial.eval_eq_sum_range, polyCoeffMass]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_pow]
  have hpow : ‖y‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hy
  nlinarith [norm_nonneg (q.coeff i), norm_nonneg y, pow_nonneg (norm_nonneg y) i]

theorem norm_eval_shifted_le (j : ℕ) (q : Polynomial ℂ) {y : ℂ} (hy : ‖y‖ ≤ 1) :
    ‖(Polynomial.X ^ j * q).eval y‖ ≤ polyCoeffMass q * ‖y‖ ^ j := by
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_eval_le_polyCoeffMass q hy) (by positivity)

/-! ## Dyadic bookkeeping -/

/-- The dyadic level of a zero above the cutoff `G`. -/
def dyadicLevel (G : ℝ) (z : ℂ) : ℕ := Nat.log 2 ⌊|z.im| / G⌋₊

theorem dyadicLevel_bounds {G : ℝ} (hG : 2 ≤ G) {z : ℂ} (hz : G < |z.im|) :
    2 ^ (dyadicLevel G z) * G ≤ |z.im| ∧ |z.im| < 2 ^ (dyadicLevel G z + 1) * G := by
  have hG0 : (0 : ℝ) < G := by linarith
  set x : ℝ := |z.im| / G with hx
  have hx1 : 1 < x := by
    rw [hx, lt_div_iff₀ hG0]
    linarith
  have hn1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx1.le
  have hn0 : ⌊x⌋₊ ≠ 0 := by omega
  have hlow : (2 : ℕ) ^ (Nat.log 2 ⌊x⌋₊) ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 hn0
  have hhigh : ⌊x⌋₊ < 2 ^ (Nat.log 2 ⌊x⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hfloorle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hltfloor : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  constructor
  · have hcast : ((2 : ℕ) ^ (Nat.log 2 ⌊x⌋₊) : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hlow
    have hle : (2 : ℝ) ^ (dyadicLevel G z) ≤ x := by
      rw [dyadicLevel, ← hx]
      push_cast at hcast
      linarith
    rw [hx, le_div_iff₀ hG0] at hle
    linarith
  · have hcast : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 : ℕ) ^ (Nat.log 2 ⌊x⌋₊ + 1) : ℝ) := by
      exact_mod_cast hhigh
    have hlt : x < (2 : ℝ) ^ (dyadicLevel G z + 1) := by
      rw [dyadicLevel, ← hx]
      push_cast at hcast
      linarith
    rw [hx, div_lt_iff₀ hG0] at hlt
    linarith

theorem sum_geom_half_le (t : Finset ℕ) : ∑ k ∈ t, ((1 : ℝ) / 2) ^ k ≤ 2 := by
  have hsum : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hval : ∑' k : ℕ, ((1 : ℝ) / 2) ^ k = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have := hsum.sum_le_tsum t (fun i _ => by positivity)
  rw [hval] at this
  exact this

theorem sum_lin_geom_half_le (t : Finset ℕ) :
    ∑ k ∈ t, ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k ≤ 6 := by
  have hnorm : ‖((1 : ℝ) / 2)‖ < 1 := by
    rw [Real.norm_eq_abs]
    norm_num
  have hlin : Summable (fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hgeo : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k) := by
    have hrep : ∀ k : ℕ, ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k
        = (k : ℝ) * ((1 : ℝ) / 2) ^ k + 2 * ((1 : ℝ) / 2) ^ k := by
      intro k; ring
    rw [show (fun k : ℕ => ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k)
        = fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ k + 2 * ((1 : ℝ) / 2) ^ k from funext hrep]
    exact hlin.add (hgeo.mul_left 2)
  have hval : ∑' k : ℕ, ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k = 6 := by
    have hrep : ∀ k : ℕ, ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k
        = (k : ℝ) * ((1 : ℝ) / 2) ^ k + 2 * ((1 : ℝ) / 2) ^ k := by
      intro k; ring
    rw [show (fun k : ℕ => ((k : ℝ) + 2) * ((1 : ℝ) / 2) ^ k)
        = fun k : ℕ => (k : ℝ) * ((1 : ℝ) / 2) ^ k + 2 * ((1 : ℝ) / 2) ^ k from funext hrep]
    rw [Summable.tsum_add hlin (hgeo.mul_left 2), tsum_mul_left]
    rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have := hsum.sum_le_tsum t (fun i _ => by positivity)
  rw [hval] at this
  exact this

/-- The dyadic level of a divisor-support point. -/
def dyadicLevelSupport (G : ℝ) (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : ℕ :=
  dyadicLevel G (ρ : ℂ)

/-! ## The tail law -/

set_option maxHeartbeats 1600000 in
/-- **The high-height tail law for centered reciprocal square tests.**
`∑_{|γ_ρ| > G} m_ρ ‖y_ρ‖^r ‖p(y_ρ)‖² = O(G^{1−2r−4j} log G)` for `p = X^j q`. -/
theorem xi_central_tail_law (j r : ℕ) (hr : 1 ≤ r) (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, 2 ≤ G →
      ∀ s : Finset ↥(MeromorphicOn.divisor xi Set.univ).support,
        (∀ ρ ∈ s, G < |(ρ : ℂ).im|) →
        (∑ ρ ∈ s, ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
           ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2))
          ≤ C * Real.log G / G ^ (2 * r + 4 * j - 1) := by
  classical
  obtain ⟨c, hc, hball⟩ := exists_xiRegionOrderSum_closedBall_upper_bound
  set M : ℝ := polyCoeffMass q with hM
  have hM0 : 0 ≤ M := polyCoeffMass_nonneg q
  set A : ℝ := M ^ 2 + 1 with hA
  have hApos : (0 : ℝ) < A := by positivity
  refine ⟨32 * A * c, by positivity, ?_⟩
  intro G hG s hs
  have hG0 : (0 : ℝ) < G := by linarith
  have hlogG : Real.log 2 ≤ Real.log G := Real.log_le_log (by norm_num) hG
  have hlogG0 : (0 : ℝ) < Real.log G := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogG
  set α : ℕ := 2 * r + 4 * j with hαdef
  have hα2 : 2 ≤ α := by omega
  set t : Finset ℕ := s.image (dyadicLevelSupport G) with ht
  have hmaps : ∀ ρ ∈ s, dyadicLevelSupport G ρ ∈ t := fun ρ hρ =>
    Finset.mem_image_of_mem _ hρ
  -- fiberwise decomposition
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- bound each fiber
  have hfiber : ∀ k ∈ t,
      (∑ ρ ∈ s with dyadicLevelSupport G ρ = k,
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
           ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2))
        ≤ 4 * A * c * ((1 / 2 : ℝ) ^ k *
            (((k : ℝ) + 2) * Real.log 2 + Real.log G)) / G ^ (α - 1) := by
    intro k _
    set R : ℝ := 2 ^ (k + 2) * G with hR
    have hRpos : (0 : ℝ) < 2 ^ (k + 2) := by positivity
    have hR2 : (2 : ℝ) ≤ R := by
      rw [hR]
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 2) := one_le_pow₀ (by norm_num)
      nlinarith
    -- pointwise bound on the fiber
    have hpt : ∀ ρ ∈ s.filter (fun ρ => dyadicLevelSupport G ρ = k),
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
           ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2)
          ≤ (A / (2 ^ k * G) ^ α) *
            ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρs, hρk⟩ := hρ
      simp only [dyadicLevelSupport] at hρk
      have him := hs ρ hρs
      have him1 : (1 : ℝ) ≤ |(ρ : ℂ).im| := by linarith
      have himpos : (0 : ℝ) < |(ρ : ℂ).im| := by linarith
      have hy : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ≤ 1 / |(ρ : ℂ).im| ^ 2 :=
        norm_xiCentralReciprocalSquare_le himpos
      have hy1 : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ≤ 1 := by
        refine le_trans hy ?_
        rw [div_le_one (by positivity)]
        nlinarith
      have hp : ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖
          ≤ M * ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ j :=
        norm_eval_shifted_le j q hy1
      have hy0 : (0 : ℝ) ≤ ‖xiCentralReciprocalSquare (ρ : ℂ)‖ := norm_nonneg _
      have hΦ : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
          ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2
          ≤ M ^ 2 * ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ (r + 2 * j) := by
        have hsq : ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2
            ≤ (M * ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ j) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hp 2
        calc ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
              ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2
            ≤ ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
                (M * ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ j) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = M ^ 2 * ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ (r + 2 * j) := by
              rw [mul_pow, ← pow_mul, pow_add]
              ring
      have hpow : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ (r + 2 * j)
          ≤ (1 / |(ρ : ℂ).im| ^ 2) ^ (r + 2 * j) :=
        pow_le_pow_left₀ hy0 hy _
      have hval : (1 / |(ρ : ℂ).im| ^ 2) ^ (r + 2 * j) = 1 / |(ρ : ℂ).im| ^ α := by
        rw [div_pow, one_pow, ← pow_mul, hαdef]
        congr 2
        ring
      have hlow : 2 ^ k * G ≤ |(ρ : ℂ).im| := by
        have hd := (dyadicLevel_bounds hG him).1
        rw [hρk] at hd
        exact hd
      have hlowpos : (0 : ℝ) < 2 ^ k * G := by positivity
      have hpowmono : (2 ^ k * G) ^ α ≤ |(ρ : ℂ).im| ^ α :=
        pow_le_pow_left₀ hlowpos.le hlow α
      have hfinal : ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
          ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2
          ≤ A / (2 ^ k * G) ^ α := by
        have h1 : M ^ 2 * ‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ (r + 2 * j)
            ≤ M ^ 2 * (1 / |(ρ : ℂ).im| ^ α) := by
          rw [← hval]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
        have h2 : M ^ 2 * (1 / |(ρ : ℂ).im| ^ α) ≤ M ^ 2 * (1 / (2 ^ k * G) ^ α) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith [hpowmono]
        have h3 : M ^ 2 * (1 / (2 ^ k * G) ^ α) ≤ A / (2 ^ k * G) ^ α := by
          rw [hA, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_pos hlowpos α]
        linarith [hΦ, h1, h2, h3]
      have hm0 : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
        exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
      calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
            (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
             ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2)
          ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (A / (2 ^ k * G) ^ α) :=
            mul_le_mul_of_nonneg_left hfinal hm0
        _ = (A / (2 ^ k * G) ^ α) * ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by ring
    -- the multiplicity mass of the fiber
    have hmass : (∑ ρ ∈ s with dyadicLevelSupport G ρ = k,
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ))
          ≤ (xiRegionOrderSum (closedBall (0 : ℂ) R) : ℝ) := by
      refine sum_multiplicity_le_xiRegionOrderSum (isCompact_closedBall _ _) _ ?_
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      obtain ⟨hρs, hρk⟩ := hρ
      simp only [dyadicLevelSupport] at hρk
      have him := hs ρ hρs
      have hup := (dyadicLevel_bounds hG him).2
      rw [hρk] at hup
      have hre := xi_divisor_support_re_mem_open_unit ρ
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
      have h1 : |(ρ : ℂ).re| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hre.1], hre.2.le⟩
      have h2 : (1 : ℝ) ≤ 2 ^ (k + 1) * G := by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        nlinarith
      have h3 : (2 : ℝ) ^ (k + 1) * G + 2 ^ (k + 1) * G = R := by
        rw [hR, pow_succ, pow_succ]
        ring
      linarith [hup, h1, h2, h3]
    -- combine
    have hAdiv : (0 : ℝ) ≤ A / (2 ^ k * G) ^ α := by positivity
    have hstep : (∑ ρ ∈ s with dyadicLevelSupport G ρ = k,
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
          (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
           ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2))
        ≤ (A / (2 ^ k * G) ^ α) * (xiRegionOrderSum (closedBall (0 : ℂ) R) : ℝ) := by
      calc (∑ ρ ∈ s with dyadicLevelSupport G ρ = k,
            ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
              (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
               ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2))
          ≤ ∑ ρ ∈ s with dyadicLevelSupport G ρ = k,
              (A / (2 ^ k * G) ^ α) *
                ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) :=
            Finset.sum_le_sum hpt
        _ = (A / (2 ^ k * G) ^ α) * ∑ ρ ∈ s with dyadicLevelSupport G ρ = k,
              ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (A / (2 ^ k * G) ^ α) * (xiRegionOrderSum (closedBall (0 : ℂ) R) : ℝ) :=
            mul_le_mul_of_nonneg_left hmass hAdiv
    refine le_trans hstep ?_
    have hballbound := hball R hR2
    have hlogR : Real.log R = ((k : ℝ) + 2) * Real.log 2 + Real.log G := by
      rw [hR, Real.log_mul (by positivity) hG0.ne', Real.log_pow]
      push_cast
      ring
    have hRbound : (xiRegionOrderSum (closedBall (0 : ℂ) R) : ℝ)
        ≤ c * (2 ^ (k + 2) * G) * (((k : ℝ) + 2) * Real.log 2 + Real.log G) := by
      rw [← hlogR, ← hR]
      exact hballbound
    have hmul : (A / (2 ^ k * G) ^ α) * (xiRegionOrderSum (closedBall (0 : ℂ) R) : ℝ)
        ≤ (A / (2 ^ k * G) ^ α) *
          (c * (2 ^ (k + 2) * G) * (((k : ℝ) + 2) * Real.log 2 + Real.log G)) :=
      mul_le_mul_of_nonneg_left hRbound hAdiv
    refine le_trans hmul ?_
    -- pure algebra
    have hL : (0 : ℝ) ≤ ((k : ℝ) + 2) * Real.log 2 + Real.log G := by
      have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    have hkey : (A / (2 ^ k * G) ^ α) * (c * (2 ^ (k + 2) * G))
        ≤ 4 * A * c * (1 / 2 : ℝ) ^ k / G ^ (α - 1) := by
      have hexp : k * α = k + k * (α - 1) := by
        have h1 : α - 1 + 1 = α := by omega
        conv_lhs => rw [← h1]
        ring
      have hGα : G ^ α = G ^ (α - 1) * G := by
        rw [← pow_succ]
        congr 1
        omega
      have h2k2 : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by
        rw [pow_add]
        ring
      have hpos1 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hpos2 : (0 : ℝ) < (2 : ℝ) ^ (k * (α - 1)) := by positivity
      have hpos3 : (0 : ℝ) < G ^ (α - 1) := by positivity
      have h1 : (2 : ℝ) ^ k ≠ 0 := ne_of_gt hpos1
      have h2 : (2 : ℝ) ^ (k * (α - 1)) ≠ 0 := ne_of_gt hpos2
      have h3 : G ^ (α - 1) ≠ 0 := ne_of_gt hpos3
      have h4 : G ≠ 0 := ne_of_gt hG0
      have hL : (A / (2 ^ k * G) ^ α) * (c * (2 ^ (k + 2) * G))
          = 4 * A * c / ((2 : ℝ) ^ (k * (α - 1)) * G ^ (α - 1)) := by
        rw [h2k2, mul_pow, ← pow_mul, hexp, pow_add, hGα]
        field_simp
      have hRr : 4 * A * c * (1 / 2 : ℝ) ^ k / G ^ (α - 1)
          = 4 * A * c / ((2 : ℝ) ^ k * G ^ (α - 1)) := by
        rw [div_pow, one_pow]
        field_simp
      have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k * (α - 1)) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right k (by omega))
      rw [hL, hRr, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * A * c) hpos3.le)
        (sub_nonneg.mpr hmono)]
    calc (A / (2 ^ k * G) ^ α) *
          (c * (2 ^ (k + 2) * G) * (((k : ℝ) + 2) * Real.log 2 + Real.log G))
        = ((A / (2 ^ k * G) ^ α) * (c * (2 ^ (k + 2) * G))) *
            (((k : ℝ) + 2) * Real.log 2 + Real.log G) := by ring
      _ ≤ (4 * A * c * (1 / 2 : ℝ) ^ k / G ^ (α - 1)) *
            (((k : ℝ) + 2) * Real.log 2 + Real.log G) := by
          exact mul_le_mul_of_nonneg_right hkey hL
      _ = 4 * A * c * ((1 / 2 : ℝ) ^ k *
            (((k : ℝ) + 2) * Real.log 2 + Real.log G)) / G ^ (α - 1) := by ring
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  have hsplit : (∑ k ∈ t, 4 * A * c * ((1 / 2 : ℝ) ^ k *
        (((k : ℝ) + 2) * Real.log 2 + Real.log G)) / G ^ (α - 1))
      = (4 * A * c / G ^ (α - 1)) *
        (Real.log 2 * ∑ k ∈ t, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k
          + Real.log G * ∑ k ∈ t, (1 / 2 : ℝ) ^ k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsplit]
  have hb1 := sum_lin_geom_half_le t
  have hb2 := sum_geom_half_le t
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hbound : Real.log 2 * ∑ k ∈ t, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k
      + Real.log G * ∑ k ∈ t, (1 / 2 : ℝ) ^ k ≤ 8 * Real.log G := by
    have h1 : Real.log 2 * ∑ k ∈ t, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k ≤ 6 * Real.log 2 := by
      nlinarith [hb1, hlog2nn]
    have h2 : Real.log G * ∑ k ∈ t, (1 / 2 : ℝ) ^ k ≤ 2 * Real.log G := by
      nlinarith [hb2, hlogG0.le]
    linarith
  have hfac : (0 : ℝ) ≤ 4 * A * c / G ^ (α - 1) := by positivity
  calc (4 * A * c / G ^ (α - 1)) *
        (Real.log 2 * ∑ k ∈ t, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k
          + Real.log G * ∑ k ∈ t, (1 / 2 : ℝ) ^ k)
      ≤ (4 * A * c / G ^ (α - 1)) * (8 * Real.log G) :=
        mul_le_mul_of_nonneg_left hbound hfac
    _ = 32 * A * c * Real.log G / G ^ (α - 1) := by ring

/-! ## The tail law as a convergent sum over all high zeros -/

/-- A divisor-support point lies above height `G`. -/
def AboveHeight (G : ℝ) (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : Prop :=
  G < |(ρ : ℂ).im|

instance instDecidableAboveHeight (G : ℝ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : Decidable (AboveHeight G ρ) :=
  Real.decidableLT _ _

/-- The reciprocal square test mass carried by a zero above height `G`. -/
def tailTestTerm (j r : ℕ) (q : Polynomial ℂ) (G : ℝ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : ℝ :=
  if AboveHeight G ρ then
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
      (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
       ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2)
  else 0

theorem tailTestTerm_nonneg (j r : ℕ) (q : Polynomial ℂ) (G : ℝ)
    (ρ : ↥(MeromorphicOn.divisor xi Set.univ).support) : 0 ≤ tailTestTerm j r q G ρ := by
  rw [tailTestTerm]
  split
  · have hm : (0 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
    positivity
  · exact le_rfl

/-- **The tail law.**  For `p = X^j q` with `r ≥ 1` the high-height reciprocal square test mass
converges and obeys `∑_{|γ_ρ| > G} m_ρ ‖y_ρ‖^r ‖p(y_ρ)‖² ≤ C G^{1−2r−4j} log G`. -/
theorem xi_central_tail_law_tsum (j r : ℕ) (hr : 1 ≤ r) (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, 2 ≤ G →
      Summable (tailTestTerm j r q G) ∧
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, tailTestTerm j r q G ρ
        ≤ C * Real.log G / G ^ (2 * r + 4 * j - 1) := by
  classical
  obtain ⟨C, hC, hbound⟩ := xi_central_tail_law j r hr q
  refine ⟨C, hC, fun G hG => ?_⟩
  have hpartial : ∀ s : Finset ↥(MeromorphicOn.divisor xi Set.univ).support,
      (∑ ρ ∈ s, tailTestTerm j r q G ρ) ≤ C * Real.log G / G ^ (2 * r + 4 * j - 1) := by
    intro s
    have hfilter : (∑ ρ ∈ s, tailTestTerm j r q G ρ)
        = ∑ ρ ∈ s with AboveHeight G ρ,
            ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) *
              (‖xiCentralReciprocalSquare (ρ : ℂ)‖ ^ r *
               ‖(Polynomial.X ^ j * q).eval (xiCentralReciprocalSquare (ρ : ℂ))‖ ^ 2) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun ρ _ => rfl
    rw [hfilter]
    refine hbound G hG _ ?_
    intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2
  have hsummable : Summable (tailTestTerm j r q G) :=
    summable_of_sum_le (fun ρ => tailTestTerm_nonneg j r q G ρ) hpartial
  exact ⟨hsummable, hsummable.tsum_le_of_sum_le hpartial⟩

/-! ## The four shifted towers -/

/-- `Q₀` with a nonvanishing hard-edge value: tail `O(G^{-1} log G)` — the slow bottleneck. -/
theorem xi_central_tail_law_Q0_hardEdge (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, 2 ≤ G →
      Summable (tailTestTerm 0 1 q G) ∧
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, tailTestTerm 0 1 q G ρ
        ≤ C * Real.log G / G ^ 1 := by
  simpa using xi_central_tail_law_tsum 0 1 le_rfl q

/-- `Q₁` with a nonvanishing hard-edge value: tail `O(G^{-3} log G)`. -/
theorem xi_central_tail_law_Q1_hardEdge (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, 2 ≤ G →
      Summable (tailTestTerm 0 2 q G) ∧
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, tailTestTerm 0 2 q G ρ
        ≤ C * Real.log G / G ^ 3 := by
  simpa using xi_central_tail_law_tsum 0 2 (by norm_num) q

/-- `Q₀` with a simple zero at the hard edge: tail `O(G^{-5} log G)`. -/
theorem xi_central_tail_law_Q0_simpleZero (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, 2 ≤ G →
      Summable (tailTestTerm 1 1 q G) ∧
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, tailTestTerm 1 1 q G ρ
        ≤ C * Real.log G / G ^ 5 := by
  simpa using xi_central_tail_law_tsum 1 1 le_rfl q

/-- `Q₁` with a simple zero at the hard edge: tail `O(G^{-7} log G)`. -/
theorem xi_central_tail_law_Q1_simpleZero (q : Polynomial ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ G : ℝ, 2 ≤ G →
      Summable (tailTestTerm 1 2 q G) ∧
      ∑' ρ : ↥(MeromorphicOn.divisor xi Set.univ).support, tailTestTerm 1 2 q G ρ
        ≤ C * Real.log G / G ^ 7 := by
  simpa using xi_central_tail_law_tsum 1 2 (by norm_num) q

/-- Each hard-edge zero of the test polynomial improves the tail by four powers of `G`. -/
theorem xi_central_tail_exponent_step (j r : ℕ) (hr : 1 ≤ r) :
    2 * r + 4 * (j + 1) - 1 = (2 * r + 4 * j - 1) + 4 := by
  omega

end

end RHTower
