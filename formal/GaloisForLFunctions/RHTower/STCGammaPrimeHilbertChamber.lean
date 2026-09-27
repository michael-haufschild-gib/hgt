import GaloisForLFunctions.RHTower.STCHyperbolicGapFlatCompletionSource
import GaloisForLFunctions.RHTower.STCOrderedCurvatureRank
import GaloisForLFunctions.RHTower.XiPrimeSeamCofinalAnchoredEssentialNormDecay
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Sharp Hilbert chamber of the literal two-channel Gamma kernel

On the depth-zero prime face, `b_u(p)² = (log p)² p^{-1-u}` and
`Q_{u,g}(p,q) = b_u(p) b_u(q) sinh(g(log p + log q)/2)
             = [b_{u-g}(p) b_{u-g}(q) - b_{u+g}(p) b_{u+g}(q)]/2`.

For `g ≠ 0` the following are equivalent: `u > |g|`; both channels are square summable; every
column is square summable; `Q_{u,g}` is the matrix of a bounded operator on `ℓ²(primes)`.  In
the chamber the operator has rank at most two and is compact (zero Calkin class); outside, no
bounded operator has these entries.

The analytic Stokes gauge `C_{u,g} = b_u(p) b_u(q) c_pq(g)` has a second, sharper wall: it is the
matrix of a bounded operator exactly when `u > 2|g|`, where it has rank at most four; the ordered
kernel (sign change below the prime-order diagonal) has the same threshold and is
Hilbert--Schmidt in the chamber, although its finite packets have unbounded rank.  Bounded
two-sided transport of any admitted operator stays compact, and the height-weighted exterior
`(h_p - h_q) Q_{u,g}` is again of finite rank in the chamber.
-/

open Filter Topology Matrix
open scoped InnerProductSpace ComplexConjugate ENNReal
open GaloisForLFunctions.HTGeometry InnerProductSpace

namespace RHTower

noncomputable section

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

private theorem cofinite_prime_ge (N : ℕ) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite, N ≤ (p : ℕ) := by
  have hfin : {p : Nat.Primes | (p : ℕ) < N}.Finite :=
    (Set.finite_lt_nat N).preimage Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  simpa using hp

/-- `b_u(p) p^{c/2} = b_{u-c}(p)`. -/
theorem stcDepthZeroAmplitude_shift (u c : ℝ) (p : Nat.Primes) :
    stcDepthZeroAmplitude u p * (p : ℝ) ^ (c / 2) = stcDepthZeroAmplitude (u - c) p := by
  have := stcDepthZeroAmplitude_mul_rpow u (c / 2) p
  rwa [show u - 2 * (c / 2) = u - c by ring] at this

/-! ### The literal two-channel kernel -/

/-- The literal depth-zero source kernel `b_u(p) b_u(q) sinh(g(log p + log q)/2)`. -/
def stcGammaKernel (u g : ℝ) (p q : Nat.Primes) : ℂ :=
  ((stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
    Real.sinh (g * (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2) : ℝ) : ℂ)

/-- **(2) Two-channel decomposition** of the source kernel. -/
theorem stcGammaKernel_two_channel_real (u g : ℝ) (p q : Nat.Primes) :
    stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
        Real.sinh (g * (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2) =
      (stcDepthZeroAmplitude (u - g) p * stcDepthZeroAmplitude (u - g) q -
        stcDepthZeroAmplitude (u + g) p * stcDepthZeroAmplitude (u + g) q) / 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hq : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  rw [← stcDepthZeroAmplitude_shift u g p, ← stcDepthZeroAmplitude_shift u g q,
    show u + g = u - (-g) by ring, ← stcDepthZeroAmplitude_shift u (-g) p,
    ← stcDepthZeroAmplitude_shift u (-g) q, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hq,
    Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hq, Real.sinh_eq]
  have e1 : Real.exp (Real.log p * (g / 2)) * Real.exp (Real.log q * (g / 2)) =
      Real.exp (g * (Real.log p + Real.log q) / 2) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (Real.log p * (-g / 2)) * Real.exp (Real.log q * (-g / 2)) =
      Real.exp (-(g * (Real.log p + Real.log q) / 2)) := by rw [← Real.exp_add]; ring_nf
  rw [← e1, ← e2]
  ring

theorem stcGammaKernel_neg_grade (u g : ℝ) (p q : Nat.Primes) :
    stcGammaKernel u (-g) p q = -stcGammaKernel u g p q := by
  unfold stcGammaKernel
  rw [show -g * (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2 =
    -(g * (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2) by ring, Real.sinh_neg]
  push_cast
  ring

/-- At the neutral grade the kernel vanishes. -/
theorem stcGammaKernel_zero_grade (u : ℝ) (p q : Nat.Primes) : stcGammaKernel u 0 p q = 0 := by
  simp [stcGammaKernel]

/-- Both source channels are square summable exactly when `u > |g|`. -/
theorem stcGammaChannels_summable_iff (u g : ℝ) :
    (Summable (fun p : Nat.Primes => stcDepthZeroAmplitude (u - g) p ^ 2) ∧
      Summable (fun p : Nat.Primes => stcDepthZeroAmplitude (u + g) p ^ 2)) ↔ |g| < u := by
  rw [summable_stcDepthZeroAmplitude_sq_iff, summable_stcDepthZeroAmplitude_sq_iff, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

private theorem summable_sq_combo {f g : Nat.Primes → ℝ} (hf : Summable (fun p => f p ^ 2))
    (hg : Summable (fun p => g p ^ 2)) (a b : ℝ) :
    Summable (fun p => (a * f p - b * g p) ^ 2) := by
  refine ((hf.mul_left (2 * a ^ 2)).add (hg.mul_left (2 * b ^ 2))).of_nonneg_of_le
    (fun p => sq_nonneg _) fun p => ?_
  nlinarith [sq_nonneg (a * f p + b * g p)]

/-- **Column classification.** For `g ≠ 0`, a fixed column of `Q_{u,g}` is square summable
exactly when `u > |g|`. -/
theorem summable_sq_col_stcGammaKernel_iff {u g : ℝ} (hg : g ≠ 0) (q : Nat.Primes) :
    Summable (fun p => ‖stcGammaKernel u g p q‖ ^ 2) ↔ |g| < u := by
  constructor
  · intro hs
    by_contra hu
    push Not at hu
    set a := |g| with hadef
    have ha : 0 < a := abs_pos.mpr hg
    -- reduce to positive grade
    have hnorm : ∀ p, ‖stcGammaKernel u g p q‖ = ‖stcGammaKernel u a p q‖ := by
      intro p
      rcases lt_or_gt_of_ne hg with hneg | hpos
      · rw [hadef, abs_of_neg hneg, stcGammaKernel_neg_grade, norm_neg]
      · rw [hadef, abs_of_pos hpos]
    have hq2 : (2 : ℝ) * q ≥ 2 := by
      have : (1 : ℝ) ≤ q := by exact_mod_cast q.property.one_lt.le
      linarith
    set κ : ℝ := 1 - (2 * (q : ℝ)) ^ (-a) with hκ
    have hκ0 : 0 < κ := by
      have : (2 * (q : ℝ)) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      linarith
    have hbq := stcDepthZeroAmplitude_pos (u - a) q
    set c : ℝ := stcDepthZeroAmplitude (u - a) q * κ / 2 with hc
    have hc0 : 0 < c := by positivity
    have hlow : ∀ p : Nat.Primes, c ^ 2 * stcDepthZeroAmplitude (u - a) p ^ 2 ≤
        ‖stcGammaKernel u g p q‖ ^ 2 := by
      intro p
      rw [hnorm]
      unfold stcGammaKernel
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, stcGammaKernel_two_channel_real]
      have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
      have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
      have hsp := stcDepthZeroAmplitude_mul_rpow (u - a) (-a) p
      have hsq := stcDepthZeroAmplitude_mul_rpow (u - a) (-a) q
      rw [show u - a - 2 * -a = u + a by ring] at hsp hsq
      rw [← hsp, ← hsq]
      have hpq : (p : ℝ) ^ (-a) * (q : ℝ) ^ (-a) ≤ (2 * (q : ℝ)) ^ (-a) := by
        rw [← Real.mul_rpow hp.le hq0.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast p.property.two_le) hq0.le) (by linarith)
      have hbp := stcDepthZeroAmplitude_pos (u - a) p
      have hexpand : (stcDepthZeroAmplitude (u - a) p * stcDepthZeroAmplitude (u - a) q -
          stcDepthZeroAmplitude (u - a) p * (p : ℝ) ^ (-a) *
            (stcDepthZeroAmplitude (u - a) q * (q : ℝ) ^ (-a))) / 2 =
          stcDepthZeroAmplitude (u - a) p * (stcDepthZeroAmplitude (u - a) q *
            (1 - (p : ℝ) ^ (-a) * (q : ℝ) ^ (-a)) / 2) := by ring
      rw [hexpand, mul_pow]
      have hge : c ≤ stcDepthZeroAmplitude (u - a) q * (1 - (p : ℝ) ^ (-a) * (q : ℝ) ^ (-a)) / 2 := by
        rw [hc, hκ]
        have := mul_le_mul_of_nonneg_left (by linarith : (1 - (2 * (q : ℝ)) ^ (-a)) ≤
          1 - (p : ℝ) ^ (-a) * (q : ℝ) ^ (-a)) hbq.le
        linarith
      rw [mul_comm (stcDepthZeroAmplitude (u - a) p ^ 2)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0.le hge 2) (sq_nonneg _)
    have hsum : Summable (fun p : Nat.Primes => stcDepthZeroAmplitude (u - a) p ^ 2) := by
      refine (hs.mul_left (c ^ 2)⁻¹).of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
      exact hlow p
    have := (summable_stcDepthZeroAmplitude_sq_iff (u - a)).mp hsum
    linarith
  · intro hu
    obtain ⟨h1, h2⟩ := (stcGammaChannels_summable_iff u g).mpr hu
    refine (summable_sq_combo h1 h2 (stcDepthZeroAmplitude (u - g) q / 2)
      (stcDepthZeroAmplitude (u + g) q / 2)).congr fun p => ?_
    unfold stcGammaKernel
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, stcGammaKernel_two_channel_real]
    ring

/-- In the chamber, `Q_{u,g} = (|x⟩⟨x| - |y⟩⟨y|)/2` with `x = b_{u-g}`, `y = b_{u+g}`. -/
theorem hasLpMatrix_stcGammaKernel_chamber {u g : ℝ} (hu : |g| < u) :
    let x := lpOfReal (stcDepthZeroAmplitude (u - g))
      ((stcGammaChannels_summable_iff u g).mpr hu).1
    let y := lpOfReal (stcDepthZeroAmplitude (u + g))
      ((stcGammaChannels_summable_iff u g).mpr hu).2
    HasLpMatrix ((1 / 2 : ℂ) • (rankOne ℂ x x - rankOne ℂ y y)) (stcGammaKernel u g) := by
  intro x y
  refine (((hasLpMatrix_rankOne x x).sub (hasLpMatrix_rankOne y y)).smul (1 / 2 : ℂ)).congr
    fun i j => ?_
  simp only [x, y, lpOfReal_apply, Complex.conj_ofReal, stcGammaKernel]
  rw [stcGammaKernel_two_channel_real]
  push_cast
  ring

/-- **Chamber theorem.** For `g ≠ 0`: `Q_{u,g}` is the matrix of a bounded operator on
`ℓ²(primes)` iff `u > |g|` iff both channels are square summable iff every column is. -/
theorem exists_hasLpMatrix_stcGammaKernel_iff {u g : ℝ} (hg : g ≠ 0) :
    (∃ T, HasLpMatrix T (stcGammaKernel u g)) ↔ |g| < u := by
  constructor
  · rintro ⟨T, hT⟩
    let two : Nat.Primes := ⟨2, Nat.prime_two⟩
    exact (summable_sq_col_stcGammaKernel_iff hg two).mp (hT.summable_col two)
  · intro hu
    exact ⟨_, hasLpMatrix_stcGammaKernel_chamber hu⟩

/-- In the chamber the realizing operator is unique, compact, of rank at most two, and has zero
Calkin class; bounded two-sided transport keeps it compact. -/
theorem stcGammaKernel_chamber_compact {u g : ℝ} (hu : |g| < u) :
    ∃ T, HasLpMatrix T (stcGammaKernel u g) ∧ IsCompactOperator T ∧
      Module.finrank ℂ (LinearMap.range ((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 2 ∧
      essentialNorm T = 0 ∧ (∀ L R : ℓ²P →L[ℂ] ℓ²P, IsCompactOperator (L ∘L T ∘L R)) ∧
      ∀ S, HasLpMatrix S (stcGammaKernel u g) → S = T := by
  classical
  have h := hasLpMatrix_stcGammaKernel_chamber hu
  set x := lpOfReal (stcDepthZeroAmplitude (u - g)) ((stcGammaChannels_summable_iff u g).mpr hu).1
  set y := lpOfReal (stcDepthZeroAmplitude (u + g)) ((stcGammaChannels_summable_iff u g).mpr hu).2
  have hc : IsCompactOperator ((1 / 2 : ℂ) • (rankOne ℂ x x - rankOne ℂ y y)) := by
    have h2 := ((isCompactOperator_innerRankOne x x).sub
      (isCompactOperator_innerRankOne y y)).smul (1 / 2 : ℂ)
    have heq : (⇑((1 / 2 : ℂ) • (rankOne ℂ x x - rankOne ℂ y y)) : ℓ²P → ℓ²P) =
        (1 / 2 : ℂ) • (⇑(rankOne ℂ x x) - ⇑(rankOne ℂ y y)) := by
      funext z; simp
    rw [heq]
    exact h2
  refine ⟨_, h, hc, ?_, essentialNorm_eq_zero_of_isCompactOperator hc,
    fun L R => isCompactOperator_transport hc L R, fun S hS => hS.ext h⟩
  refine finrank_range_le_two (x := x) (y := y) ?_
  rintro _ ⟨z, rfl⟩
  simp only [ContinuousLinearMap.coe_coe, _root_.smul_apply, FunLike.coe_sub,
    Pi.sub_apply, rankOne_apply]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _
    (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

/-! ### The analytic Stokes gauge: a second wall at `u = 2|g|` -/

/-- The source-weighted analytic Stokes curvature `b_u(p) b_u(q) c_pq(g)`. -/
def stcStokesSourceKernel (u g : ℝ) (p q : Nat.Primes) : ℂ :=
  ((stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
    routeRCrossPrimeStokesOddCurvature p q g : ℝ) : ℂ)

/-- `C_{u,g} = -2 Q_{u,g} G_pq(g)` with the positive Stokes gauge `G`. -/
theorem stcStokesSourceKernel_eq (u g : ℝ) (p q : Nat.Primes) :
    stcStokesSourceKernel u g p q =
      -2 * stcGammaKernel u g p q * (routeRCrossPrimeStokesGauge p q g : ℂ) := by
  unfold stcStokesSourceKernel stcGammaKernel
  rw [routeRCrossPrimeStokesOddCurvature_eq, routeRCrossPrimeStokesPhase]
  push_cast
  ring

theorem stcStokesSourceKernel_neg_grade (u g : ℝ) (p q : Nat.Primes) :
    stcStokesSourceKernel u (-g) p q = -stcStokesSourceKernel u g p q := by
  unfold stcStokesSourceKernel
  rw [routeRCrossPrimeStokesOddCurvature_neg_grade]
  push_cast
  ring

theorem stcStokesSourceKernel_comm (u g : ℝ) (p q : Nat.Primes) :
    stcStokesSourceKernel u g q p = stcStokesSourceKernel u g p q := by
  unfold stcStokesSourceKernel
  rw [routeRCrossPrimeStokesOddCurvature_comm]
  push_cast
  ring

private theorem coth_le {t τ : ℝ} (hτ : 0 < τ) (ht : τ ≤ t) :
    Real.cosh t / Real.sinh t ≤ 1 + 2 / (Real.exp (2 * τ) - 1) := by
  have h1 : 0 < Real.exp (2 * τ) - 1 := by
    have := Real.add_one_lt_exp (by positivity : (2 * τ) ≠ 0); linarith
  have hst : 0 < Real.sinh t := Real.sinh_pos_iff.mpr (by linarith)
  have hE : Real.exp (2 * τ) ≤ Real.exp (2 * t) := Real.exp_le_exp.mpr (by linarith)
  have hcoth : Real.cosh t / Real.sinh t = 1 + 2 / (Real.exp (2 * t) - 1) := by
    have he : Real.exp (2 * t) = Real.exp t ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have hEt := Real.exp_pos t
    have hgt : 1 < Real.exp t := Real.one_lt_exp_iff.mpr (by linarith)
    have hne : Real.exp t ^ 2 - 1 ≠ 0 := by nlinarith
    rw [he, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
    have hne2 : Real.exp t - (Real.exp t)⁻¹ ≠ 0 := by
      have h' := hst
      rw [Real.sinh_eq, Real.exp_neg] at h'
      exact ne_of_gt (by linarith)
    field_simp
    ring
  rw [hcoth]
  have : 2 / (Real.exp (2 * t) - 1) ≤ 2 / (Real.exp (2 * τ) - 1) :=
    div_le_div_of_nonneg_left (by norm_num) h1 (by linarith)
  linarith

/-- Four one-prime Stokes channels, weighted by the source amplitude. -/
private def stcStokesChannelVec (u g : ℝ) (k : Fin 4) (p : Nat.Primes) : ℝ :=
  stcDepthZeroAmplitude u p *
    ![stokesChannelU p g, 1, stokesChannelV p g, stokesChannelW p g] k

private def stcStokesChannelDual (u g : ℝ) (k : Fin 4) (p : Nat.Primes) : ℝ :=
  stcDepthZeroAmplitude u p *
    ![-2, -2 * stokesChannelU p g, -2 * stokesChannelW p g, -2 * stokesChannelV p g] k

private theorem stcStokesSourceKernel_four (u g : ℝ) (hg : g ≠ 0) (p q : Nat.Primes) :
    stcStokesSourceKernel u g p q =
      ((∑ k : Fin 4, stcStokesChannelVec u g k p * stcStokesChannelDual u g k q : ℝ) : ℂ) := by
  unfold stcStokesSourceKernel
  rw [stokes_odd_four_channel p.property.one_lt q.property.one_lt hg]
  simp only [Fin.sum_univ_four, stcStokesChannelVec, stcStokesChannelDual, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  congr 1
  simp
  ring

private theorem channel_bounds {g : ℝ} (hg : 0 < g) (p : Nat.Primes) :
    |stokesChannelU p g| ≤ (p : ℝ) ^ g ∧ |stokesChannelV p g| ≤ (p : ℝ) ^ g ∧
      |stokesChannelW p g| ≤ 1 + 2 / (Real.exp (2 * (g * Real.log 2 / 2)) - 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.property.two_le)
  set t := g * Real.log (p : ℝ) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; exact div_pos (mul_pos hg (hlog2.trans_le hlogp)) two_pos
  have hcosh : Real.cosh t ≤ (p : ℝ) ^ (g / 2) := by
    rw [Real.rpow_def_of_pos hp, Real.cosh_eq, show Real.log p * (g / 2) = t by rw [ht]; ring]
    have : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hsinh : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht0.le
  have hsc : Real.sinh t ≤ Real.cosh t := (Real.sinh_lt_cosh t).le
  have hpg : (p : ℝ) ^ (g / 2) * (p : ℝ) ^ (g / 2) = (p : ℝ) ^ g := by
    rw [← Real.rpow_add hp]; ring_nf
  have hc0 := Real.cosh_pos t
  refine ⟨?_, ?_, ?_⟩
  · unfold stokesChannelU
    rw [← ht, abs_of_nonneg (mul_nonneg hsinh hc0.le), ← hpg]
    exact mul_le_mul (hsc.trans hcosh) hcosh hc0.le (by positivity)
  · unfold stokesChannelV
    rw [← ht, abs_of_nonneg (sq_nonneg _), sq, ← hpg]
    exact mul_le_mul (hsc.trans hcosh) (hsc.trans hcosh) hsinh (by positivity)
  · unfold stokesChannelW
    rw [← ht, abs_of_nonneg (div_nonneg hc0.le hsinh)]
    exact coth_le (div_pos (mul_pos hg hlog2) two_pos) (by rw [ht]; nlinarith)

private theorem summable_channel {u g : ℝ} (hg : 0 < g) (hu : 2 * g < u) (k : Fin 4) :
    Summable (fun p => stcStokesChannelVec u g k p ^ 2) ∧
      Summable (fun p => stcStokesChannelDual u g k p ^ 2) := by
  have hb := (summable_stcDepthZeroAmplitude_sq_iff u).mpr (by linarith)
  have hb2 := (summable_stcDepthZeroAmplitude_sq_iff (u - 2 * g)).mpr (by linarith)
  set MW := 1 + 2 / (Real.exp (2 * (g * Real.log 2 / 2)) - 1)
  have hgrow : ∀ (f : Nat.Primes → ℝ) (K : ℝ), (∀ p, |f p| ≤ K * (p : ℝ) ^ g) →
      Summable (fun p => (stcDepthZeroAmplitude u p * f p) ^ 2) := by
    intro f K hf
    refine (hb2.mul_left (K ^ 2)).of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
    rw [← stcDepthZeroAmplitude_mul_rpow, ← sq_abs, abs_mul,
      abs_of_pos (stcDepthZeroAmplitude_pos u p)]
    have hbp := stcDepthZeroAmplitude_pos u p
    have hK : 0 ≤ K := by
      have := (abs_nonneg (f p)).trans (hf p)
      have hpg : 0 < (p : ℝ) ^ g := Real.rpow_pos_of_pos (by exact_mod_cast p.property.pos) _
      nlinarith
    calc (stcDepthZeroAmplitude u p * |f p|) ^ 2
        ≤ (stcDepthZeroAmplitude u p * (K * (p : ℝ) ^ g)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hf p) hbp.le) 2
      _ = K ^ 2 * (stcDepthZeroAmplitude u p * (p : ℝ) ^ g) ^ 2 := by ring
  have hbdd : ∀ (f : Nat.Primes → ℝ) (M : ℝ), (∀ p, |f p| ≤ M) →
      Summable (fun p => (stcDepthZeroAmplitude u p * f p) ^ 2) := by
    intro f M hf
    refine (hb.mul_left (M ^ 2)).of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
    have h1 : f p ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf p) 2
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hB := fun p => channel_bounds hg p
  have hU2 : ∀ p : Nat.Primes, |-2 * stokesChannelU p g| ≤ 2 * (p : ℝ) ^ g := fun p => by
    rw [abs_mul]; norm_num; linarith [(hB p).1]
  have hV2 : ∀ p : Nat.Primes, |-2 * stokesChannelV p g| ≤ 2 * (p : ℝ) ^ g := fun p => by
    rw [abs_mul]; norm_num; linarith [(hB p).2.1]
  have hW2 : ∀ p : Nat.Primes, |-2 * stokesChannelW p g| ≤ 2 * MW := fun p => by
    rw [abs_mul]; norm_num; linarith [(hB p).2.2]
  fin_cases k
  · exact ⟨by simpa [stcStokesChannelVec] using hgrow _ 1 fun p => by simpa using (hB p).1,
      by simpa [stcStokesChannelDual] using hbdd (fun _ => -2) 2 fun p => by norm_num⟩
  · exact ⟨by simpa [stcStokesChannelVec] using hbdd (fun _ => 1) 1 fun p => by norm_num,
      by simpa [stcStokesChannelDual] using hgrow _ 2 hU2⟩
  · exact ⟨by simpa [stcStokesChannelVec] using hgrow _ 1 fun p => by simpa using (hB p).2.1,
      by simpa [stcStokesChannelDual] using hbdd _ _ hW2⟩
  · exact ⟨by simpa [stcStokesChannelVec] using hbdd _ _ fun p => (hB p).2.2,
      by simpa [stcStokesChannelDual] using hgrow _ 2 hV2⟩

private theorem sinh_half_log_ge {g : ℝ} (hg : 0 < g) (p : Nat.Primes) :
    (p : ℝ) ^ (g / 2) * (1 - (2 : ℝ) ^ (-g)) / 2 ≤ Real.sinh (g * Real.log (p : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  rw [Real.sinh_eq]
  have e1 : Real.exp (g * Real.log (p : ℝ) / 2) = (p : ℝ) ^ (g / 2) := by
    rw [Real.rpow_def_of_pos hp]; ring_nf
  have e2 : Real.exp (-(g * Real.log (p : ℝ) / 2)) = (p : ℝ) ^ (g / 2) * (p : ℝ) ^ (-g) := by
    rw [← Real.rpow_add hp, Real.rpow_def_of_pos hp]; ring_nf
  rw [e1, e2]
  have hpg : (p : ℝ) ^ (-g) ≤ (2 : ℝ) ^ (-g) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have hpos : 0 < (p : ℝ) ^ (g / 2) := Real.rpow_pos_of_pos hp _
  nlinarith

/-- For `g > 0` and `u ≤ 2g`, no column of the source-weighted Stokes kernel is square summable. -/
private theorem not_summable_sq_col_stcStokesSourceKernel_pos {u g : ℝ} (hg : 0 < g)
    (hu : u ≤ 2 * g) (q : Nat.Primes) :
    ¬ Summable (fun p => ‖stcStokesSourceKernel u g p q‖ ^ 2) := by
  intro hs
  have hq1 := q.property.one_lt
  set tq := g * Real.log (q : ℝ) / 2
  have htq : 0 < tq := div_pos (mul_pos hg (Real.log_pos (by exact_mod_cast hq1))) two_pos
  have hWq : 0 < stokesChannelW q g :=
    div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.mpr htq)
  set κ : ℝ := (1 - (2 : ℝ) ^ (-g)) / 2
  have hκ : 0 < κ := by
    have : (2 : ℝ) ^ (-g) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    simp only [κ]; linarith
  set c : ℝ := 2 * stcDepthZeroAmplitude u q * stokesChannelW q g * κ ^ 2
  have hc : 0 < c :=
    mul_pos (mul_pos (mul_pos two_pos (stcDepthZeroAmplitude_pos u q)) hWq) (pow_pos hκ 2)
  have hlow : ∀ p : Nat.Primes, c ^ 2 * stcDepthZeroAmplitude (u - 2 * g) p ^ 2 ≤
      ‖stcStokesSourceKernel u g p q‖ ^ 2 := by
    intro p
    have hp1 := p.property.one_lt
    have htp : 0 < g * Real.log (p : ℝ) / 2 :=
      div_pos (mul_pos hg (Real.log_pos (by exact_mod_cast hp1))) two_pos
    have hsp := sinh_half_log_ge hg p
    have hUp : 0 < stokesChannelU p g :=
      mul_pos (Real.sinh_pos_iff.mpr htp) (Real.cosh_pos _)
    have hUq : 0 < stokesChannelU q g := mul_pos (Real.sinh_pos_iff.mpr htq) (Real.cosh_pos _)
    have hVq : 0 < stokesChannelV q g := pow_pos (Real.sinh_pos_iff.mpr htq) 2
    have hWp : 0 < stokesChannelW p g :=
      div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.mpr htp)
    have hV : (p : ℝ) ^ g * κ ^ 2 ≤ stokesChannelV p g := by
      unfold stokesChannelV
      have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
      have hpg : (p : ℝ) ^ g = (p : ℝ) ^ (g / 2) * (p : ℝ) ^ (g / 2) := by
        rw [← Real.rpow_add hp]; ring_nf
      have h0 : 0 ≤ (p : ℝ) ^ (g / 2) * (1 - (2 : ℝ) ^ (-g)) / 2 := by
        have h1 : (2 : ℝ) ^ (-g) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
        have h2 := Real.rpow_pos_of_pos hp (g / 2)
        exact div_nonneg (mul_nonneg h2.le (by linarith)) two_pos.le
      have := pow_le_pow_left₀ h0 hsp 2
      rw [hpg]
      calc (p : ℝ) ^ (g / 2) * (p : ℝ) ^ (g / 2) * κ ^ 2
          = ((p : ℝ) ^ (g / 2) * (1 - (2 : ℝ) ^ (-g)) / 2) ^ 2 := by simp only [κ]; ring
        _ ≤ _ := this
    have hbp := stcDepthZeroAmplitude_pos u p
    have hbq := stcDepthZeroAmplitude_pos u q
    have habs : c * stcDepthZeroAmplitude (u - 2 * g) p ≤ ‖stcStokesSourceKernel u g p q‖ := by
      unfold stcStokesSourceKernel
      rw [Complex.norm_real, Real.norm_eq_abs, stokes_odd_four_channel hp1 hq1 hg.ne']
      rw [← stcDepthZeroAmplitude_mul_rpow]
      have hsum : 0 < stokesChannelU p g + stokesChannelU q g +
          stokesChannelV p g * stokesChannelW q g + stokesChannelW p g * stokesChannelV q g := by
        have := mul_pos hWp hVq
        have hVp : 0 < stokesChannelV p g := pow_pos (Real.sinh_pos_iff.mpr htp) 2
        have := mul_pos hVp hWq
        linarith
      rw [show stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
          (-2 * (stokesChannelU p g + stokesChannelU q g +
            stokesChannelV p g * stokesChannelW q g + stokesChannelW p g * stokesChannelV q g)) =
          -(2 * stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
            (stokesChannelU p g + stokesChannelU q g +
            stokesChannelV p g * stokesChannelW q g + stokesChannelW p g * stokesChannelV q g))
          by ring, abs_neg, abs_of_pos (by positivity)]
      have hmain : c * (stcDepthZeroAmplitude u p * (p : ℝ) ^ g) ≤
          2 * stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
            (stokesChannelV p g * stokesChannelW q g) := by
        simp only [c]
        have := mul_le_mul_of_nonneg_left hV (by positivity :
          (0 : ℝ) ≤ 2 * stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q * stokesChannelW q g)
        nlinarith
      have hmore : stokesChannelV p g * stokesChannelW q g ≤ stokesChannelU p g +
          stokesChannelU q g + stokesChannelV p g * stokesChannelW q g +
            stokesChannelW p g * stokesChannelV q g := by
        have := mul_pos hWp hVq; linarith
      calc c * (stcDepthZeroAmplitude u p * (p : ℝ) ^ g)
          ≤ 2 * stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
              (stokesChannelV p g * stokesChannelW q g) := hmain
        _ ≤ _ := mul_le_mul_of_nonneg_left hmore (by positivity)
    have h0 : 0 ≤ c * stcDepthZeroAmplitude (u - 2 * g) p := by
      have := stcDepthZeroAmplitude_pos (u - 2 * g) p; positivity
    calc c ^ 2 * stcDepthZeroAmplitude (u - 2 * g) p ^ 2
        = (c * stcDepthZeroAmplitude (u - 2 * g) p) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 habs 2
  have hsum : Summable (fun p : Nat.Primes => stcDepthZeroAmplitude (u - 2 * g) p ^ 2) := by
    refine (hs.mul_left (c ^ 2)⁻¹).of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
    rw [inv_mul_eq_div, le_div_iff₀ (pow_pos hc 2), mul_comm]
    exact hlow p
  have := (summable_stcDepthZeroAmplitude_sq_iff (u - 2 * g)).mp hsum
  linarith

/-- The four-channel operator realizing the source-weighted Stokes kernel for `g > 0`. -/
private theorem hasLpMatrix_stcStokesSourceKernel_pos {u g : ℝ} (hg : 0 < g) (hu : 2 * g < u) :
    HasLpMatrix (∑ k : Fin 4, rankOne ℂ
        (lpOfReal (stcStokesChannelVec u g k) (summable_channel hg hu k).1)
        (lpOfReal (stcStokesChannelDual u g k) (summable_channel hg hu k).2))
      (stcStokesSourceKernel u g) := by
  intro i j
  rw [stcStokesSourceKernel_four u g hg.ne']
  simp only [FunLike.coe_sum, Finset.sum_apply, lp.coeFn_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hasLpMatrix_rankOne]
  simp [Complex.conj_ofReal]

/-- **The analytic Stokes wall.** For `g ≠ 0`, the source-weighted analytic Stokes curvature is
the matrix of a bounded operator on `ℓ²(primes)` iff `u > 2|g|`; at `u ≤ 2|g|` every column is
non-square-summable. -/
theorem exists_hasLpMatrix_stcStokesSourceKernel_iff {u g : ℝ} (hg : g ≠ 0) :
    (∃ T, HasLpMatrix T (stcStokesSourceKernel u g)) ↔ 2 * |g| < u := by
  rcases lt_or_gt_of_ne hg with hneg | hpos
  · have hng : 0 < -g := neg_pos.mpr hneg
    rw [abs_of_neg hneg]
    constructor
    · rintro ⟨T, hT⟩
      by_contra hu
      push Not at hu
      have hT' : HasLpMatrix ((-1 : ℂ) • T) (stcStokesSourceKernel u (-g)) := by
        refine (hT.smul (-1)).congr fun i j => ?_
        rw [stcStokesSourceKernel_neg_grade]; ring
      let two : Nat.Primes := ⟨2, Nat.prime_two⟩
      exact not_summable_sq_col_stcStokesSourceKernel_pos hng (by linarith) two
        (hT'.summable_col two)
    · intro hu
      exact ⟨_, ((hasLpMatrix_stcStokesSourceKernel_pos hng (by linarith)).smul (-1)).congr
        fun i j => by rw [stcStokesSourceKernel_neg_grade]; ring⟩
  · rw [abs_of_pos hpos]
    constructor
    · rintro ⟨T, hT⟩
      by_contra hu
      push Not at hu
      let two : Nat.Primes := ⟨2, Nat.prime_two⟩
      exact not_summable_sq_col_stcStokesSourceKernel_pos hpos hu two (hT.summable_col two)
    · intro hu
      exact ⟨_, hasLpMatrix_stcStokesSourceKernel_pos hpos hu⟩

/-- Column form of the analytic Stokes wall. -/
theorem not_summable_sq_col_stcStokesSourceKernel {u g : ℝ} (hg : g ≠ 0) (hu : u ≤ 2 * |g|)
    (q : Nat.Primes) : ¬ Summable (fun p => ‖stcStokesSourceKernel u g p q‖ ^ 2) := by
  rcases lt_or_gt_of_ne hg with hneg | hpos
  · rw [abs_of_neg hneg] at hu
    have h := not_summable_sq_col_stcStokesSourceKernel_pos (u := u) (neg_pos.mpr hneg)
      (by linarith) q
    intro hs
    apply h
    refine hs.congr fun p => ?_
    rw [stcStokesSourceKernel_neg_grade, norm_neg]
  · rw [abs_of_pos hpos] at hu
    exact not_summable_sq_col_stcStokesSourceKernel_pos hpos hu q

private theorem stcStokesSourceKernel_chamber_pos {u g : ℝ} (hg : 0 < g) (hu : 2 * g < u) :
    ∃ T, HasLpMatrix T (stcStokesSourceKernel u g) ∧ IsCompactOperator T ∧
      Module.finrank ℂ (LinearMap.range ((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 4 := by
  classical
  let v : Fin 4 → ℓ²P := fun k => lpOfReal (stcStokesChannelVec u g k) (summable_channel hg hu k).1
  let w : Fin 4 → ℓ²P := fun k => lpOfReal (stcStokesChannelDual u g k) (summable_channel hg hu k).2
  let T₀ : ℓ²P →L[ℂ] ℓ²P := ∑ k : Fin 4, rankOne ℂ (v k) (w k)
  refine ⟨T₀, hasLpMatrix_stcStokesSourceKernel_pos hg hu, ?_, ?_⟩
  · have : ∀ s : Finset (Fin 4), IsCompactOperator (∑ k ∈ s, rankOne ℂ (v k) (w k)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using isCompactOperator_zero
      | insert k s hk ih =>
        rw [Finset.sum_insert hk]
        exact (isCompactOperator_innerRankOne _ _).add ih
    exact this Finset.univ
  · have hle := finrank_range_le_card (T := T₀) (Finset.univ.image v) (by
      rintro _ ⟨z, rfl⟩
      have hz : (T₀ z) = ∑ k : Fin 4, ⟪w k, z⟫_ℂ • v k := by
        simp only [T₀, _root_.sum_apply, rankOne_apply]
      rw [ContinuousLinearMap.coe_coe, hz]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    exact hle.trans (Finset.card_image_le.trans (by simp))

/-- In the chamber `u > 2|g|` the source-weighted Stokes operator is compact, of rank at most
four, unique, and has zero Calkin class. -/
theorem stcStokesSourceKernel_chamber {u g : ℝ} (hg : g ≠ 0) (hu : 2 * |g| < u) :
    ∃ T, HasLpMatrix T (stcStokesSourceKernel u g) ∧ IsCompactOperator T ∧
      Module.finrank ℂ (LinearMap.range ((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 4 ∧
      essentialNorm T = 0 ∧ ∀ S, HasLpMatrix S (stcStokesSourceKernel u g) → S = T := by
  have key : ∃ T, HasLpMatrix T (stcStokesSourceKernel u g) ∧ IsCompactOperator T ∧
      Module.finrank ℂ (LinearMap.range ((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 4 := by
    rcases lt_or_gt_of_ne hg with hneg | hpos
    · rw [abs_of_neg hneg] at hu
      obtain ⟨T, hT, hc, hr⟩ := stcStokesSourceKernel_chamber_pos (neg_pos.mpr hneg)
        (by linarith)
      refine ⟨-T, fun i j => ?_, hc.neg, ?_⟩
      · rw [_root_.neg_apply, lp.coeFn_neg, Pi.neg_apply, hT i j,
          stcStokesSourceKernel_neg_grade, neg_neg]
      · have : ((-T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P) =
            -((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P) := rfl
        rw [this, LinearMap.range_neg]
        exact hr
    · rw [abs_of_pos hpos] at hu
      exact stcStokesSourceKernel_chamber_pos hpos hu
  obtain ⟨T, hT, hc, hr⟩ := key
  exact ⟨T, hT, hc, hr, essentialNorm_eq_zero_of_isCompactOperator hc, fun S hS => hS.ext hT⟩

/-! ### The ordered kernel -/

/-- The ordered source-weighted curvature: `+C` above and `-C` below the prime-order diagonal. -/
def stcOrderedStokesSourceKernel (u g : ℝ) (p q : Nat.Primes) : ℂ :=
  if (p : ℕ) < q then stcStokesSourceKernel u g p q
  else if (q : ℕ) < p then -stcStokesSourceKernel u g q p else 0

theorem norm_stcOrderedStokesSourceKernel_le (u g : ℝ) (p q : Nat.Primes) :
    ‖stcOrderedStokesSourceKernel u g p q‖ ≤ ‖stcStokesSourceKernel u g p q‖ := by
  unfold stcOrderedStokesSourceKernel
  split_ifs
  · exact le_rfl
  · rw [norm_neg, stcStokesSourceKernel_comm]
  · simp

theorem norm_stcOrderedStokesSourceKernel_of_ne (u g : ℝ) {p q : Nat.Primes} (hpq : p ≠ q) :
    ‖stcOrderedStokesSourceKernel u g p q‖ = ‖stcStokesSourceKernel u g p q‖ := by
  unfold stcOrderedStokesSourceKernel
  have hne : (p : ℕ) ≠ q := fun h => hpq (Subtype.ext h)
  split_ifs with h1 h2
  · rfl
  · rw [norm_neg, stcStokesSourceKernel_comm]
  · omega

private theorem sq_sum_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The source-weighted Stokes kernel is Hilbert--Schmidt in the chamber `u > 2|g|`. -/
private theorem isHS_stcStokesSourceKernel {u g : ℝ} (hg : 0 < g) (hu : 2 * g < u) :
    HilbertSchmidt.IsHS (fun pq : Nat.Primes × Nat.Primes => stcStokesSourceKernel u g pq.1 pq.2) := by
  have hterm : ∀ k : Fin 4, Summable (fun pq : Nat.Primes × Nat.Primes =>
      stcStokesChannelVec u g k pq.1 ^ 2 * stcStokesChannelDual u g k pq.2 ^ 2) := fun k =>
    Summable.mul_of_nonneg (summable_channel hg hu k).1 (summable_channel hg hu k).2
      (fun p => sq_nonneg _) (fun p => sq_nonneg _)
  have hsum : Summable (fun pq : Nat.Primes × Nat.Primes => ∑ k : Fin 4,
      4 * (stcStokesChannelVec u g k pq.1 ^ 2 * stcStokesChannelDual u g k pq.2 ^ 2)) :=
    summable_sum fun k _ => (hterm k).mul_left 4
  refine hsum.of_nonneg_of_le (fun pq => sq_nonneg _) fun pq => ?_
  show ‖stcStokesSourceKernel u g pq.1 pq.2‖ ^ 2 ≤ _
  rw [stcStokesSourceKernel_four u g hg.ne', Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [Fin.sum_univ_four]
  refine (sq_sum_four_le _ _ _ _).trans (le_of_eq ?_)
  ring

/-- **Ordered kernel.** The ordered source-weighted Stokes kernel has the same threshold
`u > 2|g|`; in the chamber it is the matrix of a Hilbert--Schmidt, hence compact, operator, and
bounded two-sided transport keeps it compact. -/
theorem exists_hasLpMatrix_stcOrderedStokesSourceKernel_iff {u g : ℝ} (hg : g ≠ 0) :
    (∃ T, HasLpMatrix T (stcOrderedStokesSourceKernel u g)) ↔ 2 * |g| < u := by
  constructor
  · rintro ⟨T, hT⟩
    by_contra hu
    push Not at hu
    let two : Nat.Primes := ⟨2, Nat.prime_two⟩
    apply not_summable_sq_col_stcStokesSourceKernel hg hu two
    have hcol := hT.summable_col two
    have hfin : Summable (fun p : Nat.Primes =>
        if p = two then ‖stcStokesSourceKernel u g two two‖ ^ 2 else 0) :=
      summable_of_ne_finset_zero (s := {two}) fun p hp => by
        rw [if_neg (by simpa using hp)]
    refine (hcol.add hfin).of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
    by_cases hp : p = two
    · subst hp; simp
    · rw [if_neg hp, add_zero, norm_stcOrderedStokesSourceKernel_of_ne u g hp]
  · intro hu
    have hK : HilbertSchmidt.IsHS
        (fun pq : Nat.Primes × Nat.Primes => stcOrderedStokesSourceKernel u g pq.1 pq.2) := by
      have ha : 0 < |g| := abs_pos.mpr hg
      have hC := isHS_stcStokesSourceKernel ha hu
      refine hC.of_nonneg_of_le (fun pq => sq_nonneg _) fun pq => ?_
      have h1 := norm_stcOrderedStokesSourceKernel_le u g pq.1 pq.2
      have h2 : ‖stcStokesSourceKernel u g pq.1 pq.2‖ = ‖stcStokesSourceKernel u |g| pq.1 pq.2‖ := by
        rcases lt_or_gt_of_ne hg with hneg | hpos
        · rw [abs_of_neg hneg, stcStokesSourceKernel_neg_grade, norm_neg]
        · rw [abs_of_pos hpos]
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2.le) 2
    exact ⟨HilbertSchmidt.toOperator hK, fun i j => by
      rw [lpBasisVec, HilbertSchmidt.toOperator_single]⟩

theorem stcOrderedStokesSourceKernel_chamber {u g : ℝ} (hg : g ≠ 0) (hu : 2 * |g| < u) :
    ∃ T, HasLpMatrix T (stcOrderedStokesSourceKernel u g) ∧ T.IsHilbertSchmidt ∧
      IsCompactOperator T ∧ essentialNorm T = 0 ∧
      ∀ L R : ℓ²P →L[ℂ] ℓ²P, IsCompactOperator (L ∘L T ∘L R) := by
  have hK : HilbertSchmidt.IsHS
      (fun pq : Nat.Primes × Nat.Primes => stcOrderedStokesSourceKernel u g pq.1 pq.2) := by
    have ha : 0 < |g| := abs_pos.mpr hg
    have hC := isHS_stcStokesSourceKernel ha hu
    refine hC.of_nonneg_of_le (fun pq => sq_nonneg _) fun pq => ?_
    have h1 := norm_stcOrderedStokesSourceKernel_le u g pq.1 pq.2
    have h2 : ‖stcStokesSourceKernel u g pq.1 pq.2‖ = ‖stcStokesSourceKernel u |g| pq.1 pq.2‖ := by
      rcases lt_or_gt_of_ne hg with hneg | hpos
      · rw [abs_of_neg hneg, stcStokesSourceKernel_neg_grade, norm_neg]
      · rw [abs_of_pos hpos]
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2.le) 2
  have hHS := HilbertSchmidt.isHilbertSchmidt_toOperator hK
  have hc := hHS.isCompactOperator
  exact ⟨_, fun i j => by rw [lpBasisVec, HilbertSchmidt.toOperator_single], hHS, hc,
    essentialNorm_eq_zero_of_isCompactOperator hc, fun L R => isCompactOperator_transport hc L R⟩

/-- **Growing finite rank without a Calkin class.** For every `g ≠ 0`, every `u`, every even `n`
and threshold `N`, the ordered source-weighted curvature has prime packets of full rank `n`. -/
theorem exists_prime_packet_orderedStokesSource_rank {g : ℝ} (hg : g ≠ 0) (u : ℝ) {n : ℕ}
    (hn : Even n) (N : ℕ) :
    ∃ P : Fin n → Nat.Primes, StrictMono (fun i => (P i : ℕ)) ∧ (∀ i, N < (P i : ℕ)) ∧
      (Matrix.of fun i j => stcOrderedStokesSourceKernel u g (P i) (P j)).rank = n := by
  obtain ⟨p, hmono, hprime, hN, hdet⟩ := exists_prime_packet_orderedStokesMatrix_det_ne_zero hg hn N
  let P : Fin n → Nat.Primes := fun i => ⟨p i, hprime i⟩
  refine ⟨P, hmono, hN, ?_⟩
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i => stcDepthZeroAmplitude u (P i)
  have hM : (Matrix.of fun i j => stcOrderedStokesSourceKernel u g (P i) (P j)) =
      (D * orderedStokesMatrix p g * D).map (Complex.ofRealHom : ℝ →+* ℂ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.map_apply, D, Matrix.diagonal_mul, Matrix.mul_diagonal,
      orderedStokesMatrix, stcOrderedStokesSourceKernel, stcStokesSourceKernel, P]
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_pos (hmono hij), if_pos hij]
      simp only [Complex.ofRealHom_eq_coe]
      push_cast
      ring
    · subst hij
      simp
    · rw [if_neg (not_lt.mpr (hmono hij).le), if_pos (hmono hij), if_neg (not_lt.mpr hij.le),
        if_pos hij]
      simp only [Complex.ofRealHom_eq_coe]
      push_cast
      ring
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (stcDepthZeroAmplitude_pos u (P i)).ne'
  have hdetM : (Matrix.of fun i j => stcOrderedStokesSourceKernel u g (P i) (P j)).det ≠ 0 := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul, Matrix.det_mul]
    exact (map_ne_zero _).mpr (mul_ne_zero (mul_ne_zero hD hdet) hD)
  have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetM))
  simpa using this

/-! ### The height-weighted exterior -/

/-- The literal height-weighted exterior `(h_p - h_q) Q_{u,g}(p,q)` at depth `e`. -/
def stcHeightWeightedGammaKernel (e : ℕ) (u g : ℝ) (p q : Nat.Primes) : ℂ :=
  ((xiGammaEulerBoundaryHalfHeight p e - xiGammaEulerBoundaryHalfHeight q e : ℝ) : ℂ) *
    stcGammaKernel u g p q

private theorem summable_height_channel (e : ℕ) {v : ℝ} (hv : 0 < v) :
    Summable (fun p : Nat.Primes =>
      (xiGammaEulerBoundaryHalfHeight p e * stcDepthZeroAmplitude v p) ^ 2) := by
  have h := (summable_abs_log_natCast_pow_mul_rpow_neg 4 (1 + v) (by linarith)).comp_injective
    (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  refine (h.mul_left ((((e : ℝ) + 1) / 2) ^ 2)).congr fun p => ?_
  simp only [Function.comp_apply]
  rw [mul_pow, stcDepthZeroAmplitude_sq, xiGammaEulerBoundaryHalfHeight,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)),
    show (-(1 + v) : ℝ) = -1 - v by ring]
  ring

/-- **Height-weighted exterior in the chamber.** For `u > |g|` the literal height-weighted
exterior is realized by a compact operator of rank at most four with zero Calkin class. -/
theorem stcHeightWeightedGammaKernel_chamber (e : ℕ) {u g : ℝ} (hu : |g| < u) :
    ∃ T, HasLpMatrix T (stcHeightWeightedGammaKernel e u g) ∧ IsCompactOperator T ∧
      Module.finrank ℂ (LinearMap.range ((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 4 ∧
      essentialNorm T = 0 := by
  classical
  obtain ⟨hx, hy⟩ := (stcGammaChannels_summable_iff u g).mpr hu
  have hv1 : 0 < u - g := by have := abs_lt.mp hu; linarith
  have hv2 : 0 < u + g := by have := abs_lt.mp hu; linarith
  let x := lpOfReal (stcDepthZeroAmplitude (u - g)) hx
  let y := lpOfReal (stcDepthZeroAmplitude (u + g)) hy
  let hxv := lpOfReal (fun p => xiGammaEulerBoundaryHalfHeight p e * stcDepthZeroAmplitude (u - g) p)
    (summable_height_channel e hv1)
  let hyv := lpOfReal (fun p => xiGammaEulerBoundaryHalfHeight p e * stcDepthZeroAmplitude (u + g) p)
    (summable_height_channel e hv2)
  let T : ℓ²P →L[ℂ] ℓ²P := (1 / 2 : ℂ) • (rankOne ℂ hxv x - rankOne ℂ hyv y -
    rankOne ℂ x hxv + rankOne ℂ y hyv)
  have hT : HasLpMatrix T (stcHeightWeightedGammaKernel e u g) := by
    refine (((((hasLpMatrix_rankOne hxv x).sub (hasLpMatrix_rankOne hyv y)).sub
      (hasLpMatrix_rankOne x hxv)).add (hasLpMatrix_rankOne y hyv)).smul (1 / 2 : ℂ)).congr
        fun i j => ?_
    simp only [x, y, hxv, hyv, lpOfReal_apply, Complex.conj_ofReal, stcHeightWeightedGammaKernel,
      stcGammaKernel]
    rw [stcGammaKernel_two_channel_real]
    push_cast
    ring
  have hc : IsCompactOperator T := by
    have h2 := ((((isCompactOperator_innerRankOne hxv x).sub (isCompactOperator_innerRankOne hyv y)).sub
      (isCompactOperator_innerRankOne x hxv)).add (isCompactOperator_innerRankOne y hyv)).smul
        (1 / 2 : ℂ)
    have heq : (⇑T : ℓ²P → ℓ²P) = (1 / 2 : ℂ) • (⇑(rankOne ℂ hxv x) - ⇑(rankOne ℂ hyv y) -
        ⇑(rankOne ℂ x hxv) + ⇑(rankOne ℂ y hyv)) := by
      funext z; simp [T]
    rw [heq]
    exact h2
  refine ⟨T, hT, hc, ?_, essentialNorm_eq_zero_of_isCompactOperator hc⟩
  refine (finrank_range_le_card ({hxv, hyv, x, y} : Finset ℓ²P) ?_).trans Finset.card_le_four
  rintro _ ⟨z, rfl⟩
  simp only [T, ContinuousLinearMap.coe_coe, _root_.smul_apply, FunLike.coe_sub, FunLike.coe_add,
    Pi.sub_apply, Pi.add_apply, rankOne_apply, Finset.coe_insert, Finset.coe_singleton]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

end

end RHTower
