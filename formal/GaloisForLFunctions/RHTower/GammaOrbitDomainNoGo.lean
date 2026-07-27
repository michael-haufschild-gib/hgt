import GaloisForLFunctions.HTGeometry.OrbitDiagonalReflectionIntertwiner
import GaloisForLFunctions.RHTower.SquarefreeDensityLowerBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.PSeries

/-!
# The undamped Gamma orbit synthesis leaves the Hilbert domain

The pointed time-one Gamma cyclic carrier has covariance

```text
φ(h) = (cosh h)^(-1/2) ,
```

positive everywhere and decreasing in `|h|`.  The undamped orbit synthesis of the squarefree source
is the positive even series

```text
∑_d μ(d)² d^(-σ/2) (U_{log d} + U_{-log d}) ξ .
```

Inside a dyadic block `(N, 2N]` all logarithmic differences are at most `log 2`, so every pairwise
covariance is at least `2 φ(log 2) > 0`, and the block carries squarefree weight at least
`(N/50)·(2N)^(-σ/2) ≥ 1/100` for `σ ≤ 2`.  Hence every dyadic block contributes energy bounded
below by a fixed positive constant, and the series is not summable: the distinguished source state
does not lie in the target Hilbert domain for any `1 < σ ≤ 2`.

The carrier appears through its Gram relation only, which is the abstract content of the proved
logarithmic Sonin scattering carrier; nothing is assumed about how it is realized.
-/

open Finset Filter

namespace RHTower

noncomputable section

/-! ### The Gamma cyclic covariance -/

/-- The covariance of the pointed time-one Gamma cyclic carrier, `φ(h) = (cosh h)^(-1/2)`. -/
def gammaCyclicCovariance (h : ℝ) : ℝ := (Real.sqrt (Real.cosh h))⁻¹

theorem gammaCyclicCovariance_pos (h : ℝ) : 0 < gammaCyclicCovariance h := by
  rw [gammaCyclicCovariance]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Real.cosh_pos h))

theorem gammaCyclicCovariance_neg (h : ℝ) :
    gammaCyclicCovariance (-h) = gammaCyclicCovariance h := by
  rw [gammaCyclicCovariance, gammaCyclicCovariance, Real.cosh_neg]

/-- The covariance is decreasing in the absolute value of its argument. -/
theorem gammaCyclicCovariance_le (h L : ℝ) (hle : |h| ≤ |L|) :
    gammaCyclicCovariance L ≤ gammaCyclicCovariance h := by
  have hcosh : Real.cosh h ≤ Real.cosh L := (Real.cosh_le_cosh).mpr hle
  have h1 : 0 < Real.sqrt (Real.cosh h) := Real.sqrt_pos.mpr (Real.cosh_pos h)
  have h2 : Real.sqrt (Real.cosh h) ≤ Real.sqrt (Real.cosh L) := Real.sqrt_le_sqrt hcosh
  rw [gammaCyclicCovariance, gammaCyclicCovariance]
  exact inv_anti₀ h1 h2

/-! ### The dyadic block bound -/

/-- Inside a dyadic block the logarithmic separation is at most `log 2`. -/
theorem abs_log_sub_log_le_log_two {N d e : ℕ} (hd : d ∈ Finset.Ioc N (2 * N))
    (he : e ∈ Finset.Ioc N (2 * N)) :
    |Real.log d - Real.log e| ≤ Real.log 2 := by
  have key : ∀ x y : ℕ, x ∈ Finset.Ioc N (2 * N) → y ∈ Finset.Ioc N (2 * N) →
      Real.log x - Real.log y ≤ Real.log 2 := by
    intro x y hx hy
    rw [Finset.mem_Ioc] at hx hy
    have hxpos : (0 : ℝ) < (x : ℝ) := by
      have : 0 < x := lt_of_le_of_lt (Nat.zero_le N) hx.1
      exact_mod_cast this
    have hypos : (0 : ℝ) < (y : ℝ) := by
      have : 0 < y := lt_of_le_of_lt (Nat.zero_le N) hy.1
      exact_mod_cast this
    have hle : (x : ℝ) ≤ 2 * (y : ℝ) := by
      have hnat : x ≤ 2 * y := by omega
      exact_mod_cast hnat
    have hlog : Real.log x ≤ Real.log (2 * y) := Real.log_le_log hxpos hle
    rw [Real.log_mul (by norm_num) hypos.ne'] at hlog
    linarith
  rw [abs_le]
  exact ⟨by linarith [key e d he hd], key d e hd he⟩

/-! ### The orbit synthesis -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The symmetric orbit vector of the clock value `log d`. -/
def gammaOrbitVector (U : ℝ → K →L[ℂ] K) (xi : K) (d : ℕ) : K :=
  U (Real.log d) xi + U (-Real.log d) xi

/-- The undamped orbit weight of the squarefree source. -/
def gammaOrbitWeight (σ : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then (d : ℝ) ^ (-σ / 2) else 0

/-- The pairwise covariance of two symmetric orbit vectors is twice the sum of the difference and
sum covariances, hence at least `2 φ` of the logarithmic separation. -/
theorem two_mul_gammaCyclicCovariance_le_inner_re
    {U : ℝ → K →L[ℂ] K} {xi : K}
    (hgram : ∀ h k : ℝ, (inner ℂ (U h xi) (U k xi) : ℂ).re = gammaCyclicCovariance (h - k))
    (d e : ℕ) :
    2 * gammaCyclicCovariance (Real.log d - Real.log e)
      ≤ (inner ℂ (gammaOrbitVector U xi d) (gammaOrbitVector U xi e) : ℂ).re := by
  have hexp : (inner ℂ (gammaOrbitVector U xi d) (gammaOrbitVector U xi e) : ℂ)
      = inner ℂ (U (Real.log d) xi) (U (Real.log e) xi)
        + inner ℂ (U (Real.log d) xi) (U (-Real.log e) xi)
        + inner ℂ (U (-Real.log d) xi) (U (Real.log e) xi)
        + inner ℂ (U (-Real.log d) xi) (U (-Real.log e) xi) := by
    rw [gammaOrbitVector, gammaOrbitVector, inner_add_left, inner_add_right, inner_add_right]
    ring
  rw [hexp]
  simp only [Complex.add_re]
  rw [hgram, hgram, hgram, hgram]
  have h1 : Real.log d - -Real.log e = Real.log d + Real.log e := by ring
  have h2 : -Real.log d - Real.log e = -(Real.log d + Real.log e) := by ring
  have h3 : -Real.log d - -Real.log e = -(Real.log d - Real.log e) := by ring
  rw [h1, h2, h3, gammaCyclicCovariance_neg, gammaCyclicCovariance_neg]
  have hpos := gammaCyclicCovariance_pos (Real.log d + Real.log e)
  linarith

/-- **Undamped orbit-domain no-go.**  For every `1 < σ ≤ 2` the undamped orbit synthesis of the
squarefree source is not summable in the Gamma cyclic carrier. -/
theorem not_summable_gammaOrbit
    {U : ℝ → K →L[ℂ] K} {xi : K}
    (hgram : ∀ h k : ℝ, (inner ℂ (U h xi) (U k xi) : ℂ).re = gammaCyclicCovariance (h - k))
    {σ : ℝ} (hσ : σ ≤ 2) :
    ¬ Summable (fun d : ℕ => ((gammaOrbitWeight σ d : ℝ) : ℂ) • gammaOrbitVector U xi d) := by
  classical
  set γ : ℝ := 2 * gammaCyclicCovariance (Real.log 2) with hγdef
  have hγ : 0 < γ := by
    rw [hγdef]
    have := gammaCyclicCovariance_pos (Real.log 2)
    linarith
  refine HTGeometry.not_summable_of_cofinal_blocks (γ := Real.sqrt (γ / 10000)) ?_ ?_
  · exact Real.sqrt_pos.mpr (by positivity)
  intro s
  -- a dyadic block beyond every element of `s`
  set N : ℕ := s.sup id + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  set B : Finset ℕ := (Finset.Ioc N (2 * N)).filter Squarefree with hBdef
  refine ⟨B, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hxs
    rw [hBdef, Finset.mem_filter, Finset.mem_Ioc] at hx
    have hle : x ≤ s.sup id := Finset.le_sup (f := id) hxs
    omega
  · -- covariance lower bound on the block
    have hcov : ∀ d ∈ B, ∀ e ∈ B,
        γ ≤ (inner ℂ (gammaOrbitVector U xi d) (gammaOrbitVector U xi e) : ℂ).re := by
      intro d hd e he
      rw [hBdef, Finset.mem_filter] at hd he
      have hsep := abs_log_sub_log_le_log_two hd.1 he.1
      have hmono : gammaCyclicCovariance (Real.log 2)
          ≤ gammaCyclicCovariance (Real.log d - Real.log e) := by
        refine gammaCyclicCovariance_le _ _ ?_
        rw [abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
        exact hsep
      have hkey := two_mul_gammaCyclicCovariance_le_inner_re hgram d e
      rw [hγdef]
      linarith
    -- weight lower bound on the block
    have hwpos : ∀ d ∈ B, 0 ≤ gammaOrbitWeight σ d := by
      intro d _
      rw [gammaOrbitWeight]
      split_ifs with h
      · positivity
      · exact le_rfl
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hweight : ∀ d ∈ B, (1 : ℝ) / (2 * (N : ℝ)) ≤ gammaOrbitWeight σ d := by
      intro d hd
      rw [hBdef, Finset.mem_filter, Finset.mem_Ioc] at hd
      rw [gammaOrbitWeight, if_pos hd.2]
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
        have : 1 ≤ d := by omega
        exact_mod_cast this
      have hdle : (d : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hd.1.2
      have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
      have hexp : (d : ℝ) ^ (-1 : ℝ) ≤ (d : ℝ) ^ (-σ / 2) :=
        Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
      have hinv : (d : ℝ) ^ (-1 : ℝ) = 1 / (d : ℝ) := by
        rw [Real.rpow_neg_one, one_div]
      have hdiv : (1 : ℝ) / (2 * (N : ℝ)) ≤ 1 / (d : ℝ) :=
        one_div_le_one_div_of_le hdpos hdle
      rw [hinv] at hexp
      linarith
    have hcard : (N : ℝ) / 50 ≤ (B.card : ℝ) := by
      rw [hBdef]
      exact card_filter_squarefree_Ioc_ge N
    have hsumw : (1 : ℝ) / 100 ≤ ∑ d ∈ B, gammaOrbitWeight σ d := by
      have hcards := Finset.card_nsmul_le_sum B (gammaOrbitWeight σ) (1 / (2 * (N : ℝ))) hweight
      rw [nsmul_eq_mul] at hcards
      have hstep : (1 : ℝ) / 100 ≤ (B.card : ℝ) * (1 / (2 * (N : ℝ))) := by
        have hpos : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
        have := mul_le_mul_of_nonneg_right hcard hpos.le
        calc (1 : ℝ) / 100 = ((N : ℝ) / 50) * (1 / (2 * (N : ℝ))) := by
              field_simp
              ring
          _ ≤ (B.card : ℝ) * (1 / (2 * (N : ℝ))) := this
      linarith
    have hsumnn : (0 : ℝ) ≤ ∑ d ∈ B, gammaOrbitWeight σ d :=
      Finset.sum_nonneg hwpos
    have henergy := HTGeometry.mul_sq_sum_le_norm_sq_sum (B := B)
      (v := gammaOrbitVector U xi) (w := gammaOrbitWeight σ) (γ := γ) hwpos hcov
    have hlow : γ / 10000 ≤ ‖∑ d ∈ B, ((gammaOrbitWeight σ d : ℝ) : ℂ) • gammaOrbitVector U xi d‖ ^ 2 := by
      refine le_trans ?_ henergy
      have hsq : (1 : ℝ) / 10000 ≤ (∑ d ∈ B, gammaOrbitWeight σ d) ^ 2 := by
        nlinarith [hsumw, hsumnn]
      nlinarith [hγ.le, hsq]
    have hnorm : Real.sqrt (γ / 10000)
        ≤ ‖∑ d ∈ B, ((gammaOrbitWeight σ d : ℝ) : ℂ) • gammaOrbitVector U xi d‖ := by
      have h := Real.sqrt_le_sqrt hlow
      rwa [Real.sqrt_sq (norm_nonneg _)] at h
    exact hnorm

/-! ### The canonical Gamma damping repairs the domain -/

/-- The Gamma sum-frequency damping factor `η_d = (1 + d^(-4))^(-1/4)`. -/
def gammaDampingFactor (d : ℕ) : ℝ := (1 + (d : ℝ) ^ (-4 : ℝ)) ^ (-(1 : ℝ) / 4)

theorem gammaDampingFactor_pos (d : ℕ) : 0 < gammaDampingFactor d := by
  rw [gammaDampingFactor]
  refine Real.rpow_pos_of_pos ?_ _
  have h : (0 : ℝ) ≤ (d : ℝ) ^ (-4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  linarith

theorem gammaDampingFactor_le_one (d : ℕ) : gammaDampingFactor d ≤ 1 := by
  rw [gammaDampingFactor]
  refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
  have h : (0 : ℝ) ≤ (d : ℝ) ^ (-4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  linarith

/-- The canonical time-one Gamma damping `b_d = 2^(1/4) d^(-1/2) η_d`. -/
def gammaDampingWeight (d : ℕ) : ℝ :=
  2 ^ ((1 : ℝ) / 4) * (d : ℝ) ^ (-(1 : ℝ) / 2) * gammaDampingFactor d

theorem gammaDampingWeight_nonneg (d : ℕ) : 0 ≤ gammaDampingWeight d := by
  have h1 : (0 : ℝ) < 2 ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) ≤ (d : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have h3 := (gammaDampingFactor_pos d).le
  rw [gammaDampingWeight]
  positivity

theorem gammaOrbitWeight_nonneg (σ : ℝ) (d : ℕ) : 0 ≤ gammaOrbitWeight σ d := by
  rw [gammaOrbitWeight]
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  · exact le_rfl

/-- **The damped orbit weights are absolutely summable above the critical line.**  This is the
domain repair of the card: after the canonical Gamma damping the orbit coefficients are summable
for every `σ > 1`, in contrast with the undamped no-go. -/
theorem summable_gammaDampedWeight {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun d : ℕ => gammaOrbitWeight σ d * gammaDampingWeight d) := by
  have hbase : Summable (fun d : ℕ => (1 : ℝ) / (d : ℝ) ^ ((σ + 1) / 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hneg : Summable (fun d : ℕ => (d : ℝ) ^ (-(σ + 1) / 2)) := by
    refine hbase.congr fun d => ?_
    rw [show (-(σ + 1) / 2 : ℝ) = -((σ + 1) / 2) by ring,
      Real.rpow_neg (Nat.cast_nonneg d), one_div]
  have hdom : Summable (fun d : ℕ => 2 ^ ((1 : ℝ) / 4) * (d : ℝ) ^ (-(σ + 1) / 2)) :=
    hneg.mul_left _
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hdom
  · exact mul_nonneg (gammaOrbitWeight_nonneg σ d) (gammaDampingWeight_nonneg d)
  · rw [gammaOrbitWeight]
    split_ifs with hsq
    · have hd0 : d ≠ 0 := by
        intro h
        rw [h] at hsq
        exact not_squarefree_zero hsq
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        have : 0 < d := Nat.pos_of_ne_zero hd0
        exact_mod_cast this
      have hsplit : (d : ℝ) ^ (-σ / 2) * (d : ℝ) ^ (-(1 : ℝ) / 2)
          = (d : ℝ) ^ (-(σ + 1) / 2) := by
        rw [← Real.rpow_add hdpos]
        congr 1
        ring
      have hpow : (0 : ℝ) ≤ (d : ℝ) ^ (-σ / 2) := Real.rpow_nonneg (Nat.cast_nonneg d) _
      have htwo : (0 : ℝ) < 2 ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
      have hhalf : (0 : ℝ) ≤ (d : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg d) _
      calc (d : ℝ) ^ (-σ / 2) * gammaDampingWeight d
          = ((d : ℝ) ^ (-σ / 2) * (d : ℝ) ^ (-(1 : ℝ) / 2)) *
              (2 ^ ((1 : ℝ) / 4) * gammaDampingFactor d) := by
            rw [gammaDampingWeight]; ring
        _ ≤ ((d : ℝ) ^ (-σ / 2) * (d : ℝ) ^ (-(1 : ℝ) / 2)) * (2 ^ ((1 : ℝ) / 4) * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (gammaDampingFactor_le_one d) htwo.le
        _ = 2 ^ ((1 : ℝ) / 4) * (d : ℝ) ^ (-(σ + 1) / 2) := by rw [← hsplit]; ring
    · have : (0 : ℝ) ≤ 2 ^ ((1 : ℝ) / 4) * (d : ℝ) ^ (-(σ + 1) / 2) := by
        have h1 : (0 : ℝ) < 2 ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
        have h2 : (0 : ℝ) ≤ (d : ℝ) ^ (-(σ + 1) / 2) := Real.rpow_nonneg (Nat.cast_nonneg d) _
        positivity
      simpa using this

/-- The orbit vectors are uniformly bounded: the carrier is pointed at a unit vector. -/
theorem norm_gammaOrbitVector_le {U : ℝ → K →L[ℂ] K} {xi : K}
    (hgram : ∀ h k : ℝ, (inner ℂ (U h xi) (U k xi) : ℂ).re = gammaCyclicCovariance (h - k))
    (d : ℕ) : ‖gammaOrbitVector U xi d‖ ≤ 2 := by
  have hzero : gammaCyclicCovariance 0 = 1 := by
    rw [gammaCyclicCovariance, Real.cosh_zero, Real.sqrt_one, inv_one]
  have hunit : ∀ h : ℝ, ‖U h xi‖ = 1 := by
    intro h
    have hsq : ‖U h xi‖ ^ 2 = 1 := by
      have h1 := hgram h h
      rw [sub_self, hzero] at h1
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (U h xi)]
      exact h1
    nlinarith [norm_nonneg (U h xi), hsq]
  calc ‖gammaOrbitVector U xi d‖ ≤ ‖U (Real.log d) xi‖ + ‖U (-Real.log d) xi‖ :=
        norm_add_le _ _
    _ = 2 := by rw [hunit, hunit]; norm_num

/-- **The damped orbit synthesis is a Hilbert vector.**  Together with `not_summable_gammaOrbit`
this is the card's domain dichotomy: the undamped synthesis leaves the carrier, the canonically
damped one does not. -/
theorem summable_gammaDampedOrbit [CompleteSpace K] {U : ℝ → K →L[ℂ] K} {xi : K}
    (hgram : ∀ h k : ℝ, (inner ℂ (U h xi) (U k xi) : ℂ).re = gammaCyclicCovariance (h - k))
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun d : ℕ =>
      ((gammaOrbitWeight σ d * gammaDampingWeight d : ℝ) : ℂ) • gammaOrbitVector U xi d) := by
  refine Summable.of_norm_bounded ((summable_gammaDampedWeight hσ).mul_left 2) fun d => ?_
  have hnn : 0 ≤ gammaOrbitWeight σ d * gammaDampingWeight d :=
    mul_nonneg (gammaOrbitWeight_nonneg σ d) (gammaDampingWeight_nonneg d)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (gammaOrbitWeight σ d * gammaDampingWeight d) * ‖gammaOrbitVector U xi d‖
      ≤ (gammaOrbitWeight σ d * gammaDampingWeight d) * 2 :=
        mul_le_mul_of_nonneg_left (norm_gammaOrbitVector_le hgram d) hnn
    _ = 2 * (gammaOrbitWeight σ d * gammaDampingWeight d) := by ring

end

end RHTower
