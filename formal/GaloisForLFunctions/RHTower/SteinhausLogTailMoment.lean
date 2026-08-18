import GaloisForLFunctions.RHTower.SteinhausPhaseRotation
import GaloisForLFunctions.HTGeometry.HelsonLogTailSum
import GaloisForLFunctions.HTGeometry.IndependentCoordSeriesConvergence

/-!
# The prime-power layer of the Euler logarithm has bounded second moment

The tail layer `H_χ(s) = ∑_p logTail(χ(p) p^{-s})` is *pointwise* of size `∑_p p^{-2σ}`, which
diverges as `σ` decreases to the half line.  Its second moment does not: the terms sit on distinct
coordinates of the phase space, each has mean zero, and each has mean square at most `4 p^{-4σ}`.
So

```text
E ‖H_χ(σ)‖²  ≤  4 ∑_p p^{-2}  <  7          uniformly for σ ≥ 1/2 .
```

Mean zero is the statement that every layer of the tail carries a nontrivial character: expanding
`logTail (a X_p) = ∑_{k ≥ 2} a^k X_{p^k} / k`, each `p^k` with `k ≥ 2` is a nontrivial index, so
each term averages to zero.  That is why the whole randomness of the Euler logarithm at the half
line sits in the *linear* prime layer, and the tail is a bounded perturbation.
-/

noncomputable section

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- Powers of a prime character are the characters of the prime powers. -/
theorem X_pow_eq {p : ℕ} (hp : p ≠ 0) (m : ℕ) (ω : Omega) : X p ω ^ m = X (p ^ m) ω := by
  induction m with
  | zero => simp [X_one]
  | succ k ih =>
      rw [pow_succ, ih, pow_succ, X_mul (pow_ne_zero k hp) hp]

/-- A nontrivial Steinhaus character averages to zero. -/
theorem integral_X_eq_zero {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    ∫ ω, X n ω ∂steinhausMeasure = 0 := by
  have h := integral_X_mul_conj hn0 (one_ne_zero)
  rw [if_neg hn1] at h
  have hfun : ∀ ω : Omega, X n ω * (starRingEnd ℂ) (X 1 ω) = X n ω := by
    intro ω
    rw [X_one]
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)] at h
  exact h

/-! ### One tail term -/

/-- The tail contribution of one prime, as a function of its phase coordinate. -/
def tailTerm (a : ℝ) (t : ℝ) : ℂ :=
  logTail ((a : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ)))

theorem norm_exp_phase (t : ℝ) :
    ‖Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero]

theorem norm_tailTerm_arg (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(a : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))‖ = a := by
  rw [norm_mul, norm_exp_phase, mul_one, Complex.norm_real, Real.norm_of_nonneg ha]

theorem measurable_tailTerm (a : ℝ) : Measurable (tailTerm a) := by
  unfold tailTerm logTail
  fun_prop

theorem norm_tailTerm_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 3 / 4) (t : ℝ) :
    ‖tailTerm a t‖ ≤ 2 * a ^ 2 := by
  have hz : ‖(a : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))‖ = a :=
    norm_tailTerm_arg a ha t
  have hz1 : ‖(a : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))‖ < 1 := by
    rw [hz]; linarith
  refine le_trans (norm_logTail_le hz1) ?_
  rw [hz]
  have hden : (1 : ℝ) / 4 ≤ 1 - a := by linarith
  have hpos : (0:ℝ) < 2 * (1 - a) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg a]

/-- **Each tail term is centred.**  Every layer of the tail carries a nontrivial character. -/
theorem integral_tailTerm {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ∫ t, tailTerm a t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  classical
  set μ₀ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ₀
  set f : ℕ → ℝ → ℂ := fun k t =>
    ((a : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))) ^ (k + 2)
      / (((k + 2 : ℕ) : ℂ)) with hfdef
  have hpt : ∀ t : ℝ, tailTerm a t = ∑' k : ℕ, f k t := by
    intro t
    have hz : ‖(a : ℂ) * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))‖ < 1 := by
      rw [norm_tailTerm_arg a ha t]; exact ha1
    exact (hasSum_logTail hz).tsum_eq.symm
  have hmeas : ∀ k, AEStronglyMeasurable (f k) μ₀ := by
    intro k
    refine Measurable.aestronglyMeasurable ?_
    rw [hfdef]
    fun_prop
  have hnormf : ∀ k : ℕ, ∀ t : ℝ, ‖f k t‖ = a ^ (k + 2) / ((k : ℝ) + 2) := by
    intro k t
    rw [hfdef]
    simp only
    rw [norm_div, norm_pow, norm_tailTerm_arg a ha t, Complex.norm_natCast]
    congr 1
    push_cast
    ring
  have hlint : ∀ k : ℕ, ∫⁻ t, ‖f k t‖ₑ ∂μ₀ = ENNReal.ofReal (a ^ (k + 2) / ((k : ℝ) + 2)) := by
    intro k
    have hconst : ∀ t : ℝ, ‖f k t‖ₑ = ENNReal.ofReal (a ^ (k + 2) / ((k : ℝ) + 2)) := by
      intro t
      rw [← ofReal_norm, hnormf k t]
    rw [lintegral_congr hconst, lintegral_const, hμ₀]
    have : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
      rw [Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
    rw [this, mul_one]
  have hsum : ∑' k : ℕ, ∫⁻ t, ‖f k t‖ₑ ∂μ₀ ≠ ⊤ := by
    have hgeo : Summable fun k : ℕ => a ^ (k + 2) / ((k : ℝ) + 2) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        ((summable_geometric_of_lt_one ha ha1).mul_left (a ^ 2))
      have h2 : (1:ℝ) ≤ (k : ℝ) + 2 := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      rw [div_le_iff₀ (by linarith)]
      have hpow : a ^ (k + 2) = a ^ 2 * a ^ k := by ring
      nlinarith [pow_nonneg ha k, pow_nonneg ha 2, pow_nonneg ha (k + 2)]
    rw [funext hlint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeo]
    exact ENNReal.ofReal_ne_top
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_tsum hmeas hsum]
  have hzero : ∀ k : ℕ, ∫ t, f k t ∂μ₀ = 0 := by
    intro k
    have hfk : ∀ t : ℝ, f k t
        = ((a : ℂ) ^ (k + 2) / (((k + 2 : ℕ) : ℂ))) * charFactor ((k : ℤ) + 2) t := by
      intro t
      rw [hfdef, charFactor]
      simp only
      rw [mul_pow, ← Complex.exp_nat_mul]
      have harg : ((k + 2 : ℕ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t : ℝ) : ℂ))
          = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((((k : ℤ) + 2 : ℤ) : ℝ) * t : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfk), integral_const_mul, hμ₀,
      charInt ((k : ℤ) + 2), if_neg (by omega), mul_zero]
  rw [funext hzero]
  exact tsum_zero


/-! ### The tail layer on the phase space -/

/-- The unimodular phase carried by a point of the Steinhaus space. -/
def helsonPhaseOf (ω : Omega) : Nat.Primes → ℂ := fun p => X (p : ℕ) ω

theorem norm_helsonPhaseOf (ω : Omega) (p : Nat.Primes) : ‖helsonPhaseOf ω p‖ = 1 :=
  norm_X _ _

theorem norm_helsonPhaseOf_le (ω : Omega) : ∀ p, ‖helsonPhaseOf ω p‖ ≤ 1 :=
  fun p => le_of_eq (norm_helsonPhaseOf ω p)

/-- A prime power on the closed half plane is at most `3/4`. -/
theorem real_prime_rpow_le {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (p : ℝ) ^ (-σ) ≤ 3 / 4 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  calc (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ ≤ 3 / 4 := rpow_two_neg_half_le

/-- The tail layer term at index `n`, reading the `n`-th coordinate. -/
def logTailCoordTerm (σ : ℝ) (n : ℕ) : ℝ → ℂ :=
  if n.Prime then tailTerm ((n : ℝ) ^ (-σ)) else 0

/-- The coefficient bound of the tail layer term. -/
def logTailBound (σ : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then 2 * ((n : ℝ) ^ (-σ)) ^ 2 else 0

theorem logTailBound_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ logTailBound σ n := by
  rw [logTailBound]
  by_cases h : n.Prime
  · rw [if_pos h]; positivity
  · rw [if_neg h]

theorem measurable_logTailCoordTerm (σ : ℝ) (n : ℕ) : Measurable (logTailCoordTerm σ n) := by
  rw [logTailCoordTerm]
  by_cases h : n.Prime
  · rw [if_pos h]; exact measurable_tailTerm _
  · rw [if_neg h]; exact measurable_const

theorem norm_logTailCoordTerm_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (n : ℕ) (t : ℝ) :
    ‖logTailCoordTerm σ n t‖ ≤ logTailBound σ n := by
  rw [logTailCoordTerm, logTailBound]
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h]
    exact norm_tailTerm_le (Real.rpow_nonneg (by positivity) _) (real_prime_rpow_le h hσ) t
  · rw [if_neg h, if_neg h, Pi.zero_apply, norm_zero]

theorem integral_logTailCoordTerm {σ : ℝ} (hσ : 1 / 2 ≤ σ) (n : ℕ) :
    ∫ t, logTailCoordTerm σ n t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  rw [logTailCoordTerm]
  by_cases h : n.Prime
  · rw [if_pos h]
    refine integral_tailTerm (Real.rpow_nonneg (by positivity) _) ?_
    exact lt_of_le_of_lt (real_prime_rpow_le h hσ) (by norm_num)
  · rw [if_neg h]
    exact integral_zero _ _

/-- The mean square of one tail term, bounded by the square of the pointwise bound. -/
theorem integral_normSq_logTailCoordTerm_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (n : ℕ) :
    ∫ t, ‖logTailCoordTerm σ n t‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ (logTailBound σ n) ^ 2 := by
  have hprob : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  have hint : Integrable (fun t => ‖logTailCoordTerm σ n t‖ ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine Integrable.mono' (integrable_const ((logTailBound σ n) ^ 2))
      (((measurable_logTailCoordTerm σ n).norm.pow_const 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logTailCoordTerm_le hσ n t) 2
  have hmono : ∫ t, ‖logTailCoordTerm σ n t‖ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ ∫ _t, (logTailBound σ n) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integral_mono hint (integrable_const _) fun t =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_logTailCoordTerm_le hσ n t) 2
  refine le_trans hmono (le_of_eq ?_)
  rw [integral_const, measureReal_def, hprob]
  simp


/-! ### The second moment of the tail layer -/

theorem summable_nat_rpow_neg_two : Summable fun n : ℕ => ((n : ℝ) ^ (-(2 : ℝ))) :=
  Real.summable_nat_rpow.mpr (by norm_num)

/-- The uniform bound on the tail second moment. -/
def tailMomentBound : ℝ := 4 * ∑' n : ℕ, ((n : ℝ) ^ (-(2 : ℝ)))

theorem tailMomentBound_nonneg : 0 ≤ tailMomentBound := by
  refine mul_nonneg (by norm_num) (tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _)

theorem logTailBound_sq_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (n : ℕ) :
    (logTailBound σ n) ^ 2 ≤ 4 * ((n : ℝ) ^ (-(2 : ℝ))) := by
  rw [logTailBound]
  by_cases h : n.Prime
  · rw [if_pos h]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.one_lt.le
    have hsq : (2 * ((n : ℝ) ^ (-σ)) ^ 2) ^ 2 = 4 * ((n : ℝ) ^ (-(4 * σ))) := by
      have h1 : ((n : ℝ) ^ (-σ)) ^ (2 : ℕ) = (n : ℝ) ^ (-(2 * σ)) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul (by positivity)]
        norm_num
        rw [show -(σ * (2 : ℝ)) = -(2 * σ) by ring]
      have h2 : ((n : ℝ) ^ (-(2 * σ))) ^ (2 : ℕ) = (n : ℝ) ^ (-(4 * σ)) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ (-(2 * σ))) 2, ← Real.rpow_mul (by positivity)]
        norm_num
        rw [show -(2 * σ * (2 : ℝ)) = -(4 * σ) by ring]
      calc (2 * ((n : ℝ) ^ (-σ)) ^ 2) ^ 2 = 4 * (((n : ℝ) ^ (-σ)) ^ (2:ℕ)) ^ (2:ℕ) := by ring
        _ = 4 * ((n : ℝ) ^ (-(4 * σ))) := by rw [h1, h2]
    rw [hsq]
    have : (n : ℝ) ^ (-(4 * σ)) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    linarith
  · rw [if_neg h]
    have : (0:ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    nlinarith

theorem integral_normSq_logTailPartial {σ : ℝ} (hσ : 1 / 2 ≤ σ) (N : ℕ) :
    ∫ ω, ‖coordPartialSum (logTailCoordTerm σ) N ω‖ ^ 2 ∂steinhausMeasure ≤ tailMomentBound := by
  have hid := integral_normSq_coordPartialSum (logTailCoordTerm σ)
    (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (c := logTailBound σ)
    (measurable_logTailCoordTerm σ) (norm_logTailCoordTerm_le hσ)
    (integral_logTailCoordTerm hσ) N
  rw [← steinhausMeasure] at hid
  rw [hid]
  refine le_trans (Finset.sum_le_sum fun n _ =>
    le_trans (integral_normSq_logTailCoordTerm_le hσ n) (logTailBound_sq_le hσ n)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact summable_nat_rpow_neg_two.sum_le_tsum _
    (fun n _ => Real.rpow_nonneg (by positivity) _)

/-! ### The tail layer is the limit of its partial sums -/

theorem logTailCoordTerm_prime {σ : ℝ} (p : Nat.Primes) (ω : Omega) :
    logTailCoordTerm σ (p : ℕ) (ω (p : ℕ))
      = logTail (helsonPhaseOf ω p * (((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))) := by
  rw [logTailCoordTerm, if_pos p.2, tailTerm, helsonPhaseOf, X_prime_eq p.2]
  congr 1
  have hpow : ((((p : ℕ) : ℂ))) ^ (-((σ : ℝ) : ℂ)) = (((((p : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ ((p : ℕ) : ℝ))]
    push_cast
    ring_nf
  rw [hpow]
  ring

theorem hasSum_logTailCoordTerm {σ : ℝ} (hσ : 1 / 2 < σ) (ω : Omega) :
    HasSum (fun n : ℕ => logTailCoordTerm σ n (ω n))
      (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)) := by
  classical
  have hre : (((σ : ℝ) : ℂ)).re = σ := Complex.ofReal_re σ
  have hsum : HasSum (fun p : Nat.Primes =>
      logTail (helsonPhaseOf ω p * (((p : ℕ) : ℂ)) ^ (-((σ : ℝ) : ℂ))))
      (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)) :=
    (summable_helsonLogTail (norm_helsonPhaseOf_le ω) (by rw [hre]; exact hσ)).hasSum
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun p q h => Subtype.ext h
  have hzero : ∀ n ∉ Set.range (fun p : Nat.Primes => (p : ℕ)),
      logTailCoordTerm σ n (ω n) = 0 := by
    intro n hn
    have hnp : ¬ n.Prime := fun hp => hn ⟨⟨n, hp⟩, rfl⟩
    rw [logTailCoordTerm, if_neg hnp]
    rfl
  refine (Function.Injective.hasSum_iff (f := fun n : ℕ => logTailCoordTerm σ n (ω n))
    hinj hzero).mp ?_
  refine hsum.congr_fun fun p => ?_
  rw [Function.comp_apply]
  exact logTailCoordTerm_prime p ω

theorem tendsto_logTailPartial {σ : ℝ} (hσ : 1 / 2 < σ) (ω : Omega) :
    Filter.Tendsto (fun N => coordPartialSum (logTailCoordTerm σ) N ω) Filter.atTop
      (nhds (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ))) :=
  (hasSum_logTailCoordTerm hσ ω).tendsto_sum_nat

theorem measurable_logTailSum {σ : ℝ} (hσ : 1 / 2 < σ) :
    Measurable fun ω : Omega => helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ) :=
  measurable_of_tendsto_metrizable
    (fun N => measurable_coordPartialSum (logTailCoordTerm σ) (measurable_logTailCoordTerm σ) N)
    (tendsto_pi_nhds.mpr fun ω => tendsto_logTailPartial hσ ω)


/-! ### The tail layer is uniformly small in probability -/

theorem integrable_normSq_logTailPartial {σ : ℝ} (hσ : 1 / 2 ≤ σ) (N : ℕ) :
    Integrable (fun ω => ‖coordPartialSum (logTailCoordTerm σ) N ω‖ ^ 2) steinhausMeasure := by
  refine Integrable.mono' (integrable_const ((∑ n ∈ Finset.range N, logTailBound σ n) ^ 2))
    (((measurable_coordPartialSum (logTailCoordTerm σ) (measurable_logTailCoordTerm σ)
      N).norm.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_coordPartialSum_le (logTailCoordTerm σ) (norm_logTailCoordTerm_le hσ) N ω) 2

set_option maxHeartbeats 1000000 in
/-- **The tail layer exceeds a level with probability at most `4 C / λ²`, uniformly in `σ`.** -/
theorem measure_re_logTail_gt {σ : ℝ} (hσ : 1 / 2 < σ) {lam : ℝ} (hlam : 0 < lam) :
    (steinhausMeasure {ω | lam < |(helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re|}).toReal
      ≤ 4 * tailMomentBound / lam ^ 2 := by
  classical
  set H : Omega → ℂ := fun ω => helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ) with hHdef
  set HN : ℕ → Omega → ℂ := fun N ω => coordPartialSum (logTailCoordTerm σ) N ω with hHNdef
  have hHmeas : Measurable H := measurable_logTailSum hσ
  have hHNmeas : ∀ N, Measurable (HN N) := fun N =>
    measurable_coordPartialSum (logTailCoordTerm σ) (measurable_logTailCoordTerm σ) N
  have htim : TendstoInMeasure steinhausMeasure HN Filter.atTop H :=
    tendstoInMeasure_of_tendsto_ae (fun N => (hHNmeas N).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => tendsto_logTailPartial hσ ω)
  -- Chebyshev at each level
  have hcheb : ∀ N, (steinhausMeasure {ω | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2}).toReal
      ≤ 4 * tailMomentBound / lam ^ 2 := by
    intro N
    set A : Set Omega := {ω | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2} with hAdef
    have hAmeas : MeasurableSet A :=
      measurableSet_le measurable_const ((hHNmeas N).norm.pow_const 2)
    have hint := integrable_normSq_logTailPartial hσ.le N
    have h1 : ∫ _ω in A, (lam / 2) ^ 2 ∂steinhausMeasure
        ≤ ∫ ω in A, ‖HN N ω‖ ^ 2 ∂steinhausMeasure :=
      setIntegral_mono_on (integrableOn_const (by exact measure_ne_top _ _))
        hint.restrict hAmeas fun ω hω => hω
    have h2 : ∫ ω in A, ‖HN N ω‖ ^ 2 ∂steinhausMeasure
        ≤ ∫ ω, ‖HN N ω‖ ^ 2 ∂steinhausMeasure :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun ω => by positivity)
    have h3 : ∫ _ω in A, (lam / 2) ^ 2 ∂steinhausMeasure
        = (steinhausMeasure A).toReal * (lam / 2) ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
    have h4 : (steinhausMeasure A).toReal * (lam / 2) ^ 2 ≤ tailMomentBound := by
      rw [← h3]
      exact le_trans h1 (le_trans h2 (integral_normSq_logTailPartial hσ.le N))
    rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 2)]
    nlinarith [h4]
  -- the union bound
  have hsub : ∀ N, {ω : Omega | lam < |(H ω).re|}
      ⊆ {ω : Omega | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2}
        ∪ {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)} := by
    intro N ω hω
    by_cases hd : ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)
    · exact Or.inr hd
    · refine Or.inl ?_
      have hdist : dist (HN N ω) (H ω) < lam / 2 := by
        have hlt : edist (HN N ω) (H ω) < ENNReal.ofReal (lam / 2) := not_le.mp hd
        rw [edist_dist] at hlt
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hlt
      have hre : lam < |(H ω).re| := hω
      have h1 : |(H ω).re| ≤ ‖H ω‖ := Complex.abs_re_le_norm _
      have h2 : ‖H ω‖ ≤ ‖HN N ω‖ + dist (HN N ω) (H ω) := by
        rw [dist_eq_norm]
        calc ‖H ω‖ = ‖HN N ω - (HN N ω - H ω)‖ := by ring_nf
          _ ≤ ‖HN N ω‖ + ‖HN N ω - H ω‖ := norm_sub_le _ _
      have hlow : lam / 2 < ‖HN N ω‖ := by linarith
      have hnn : (0:ℝ) ≤ lam / 2 := by linarith
      exact pow_le_pow_left₀ hnn hlow.le 2
  have hbound : ∀ N, (steinhausMeasure {ω : Omega | lam < |(H ω).re|}).toReal
      ≤ 4 * tailMomentBound / lam ^ 2
        + (steinhausMeasure {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)}).toReal := by
    intro N
    have hle : steinhausMeasure {ω : Omega | lam < |(H ω).re|}
        ≤ steinhausMeasure ({ω : Omega | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2}
          ∪ {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)}) := measure_mono (hsub N)
    have hunion : steinhausMeasure ({ω : Omega | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2}
          ∪ {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)})
        ≤ steinhausMeasure {ω : Omega | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2}
          + steinhausMeasure {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)} :=
      measure_union_le _ _
    have htotal := le_trans hle hunion
    have hfin1 : steinhausMeasure {ω : Omega | (lam / 2) ^ 2 ≤ ‖HN N ω‖ ^ 2} ≠ ⊤ :=
      measure_ne_top _ _
    have hfin2 : steinhausMeasure {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)} ≠ ⊤ :=
      measure_ne_top _ _
    have := ENNReal.toReal_mono (by finiteness) htotal
    rw [ENNReal.toReal_add hfin1 hfin2] at this
    linarith [hcheb N]
  have h0 : Filter.Tendsto
      (fun N => steinhausMeasure {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)})
      Filter.atTop (nhds 0) := htim (ENNReal.ofReal (lam / 2)) (by
        simp only [ENNReal.ofReal_pos]
        linarith)
  have h1 : Filter.Tendsto
      (fun N => (steinhausMeasure {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)}).toReal)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp h0
  have htend : Filter.Tendsto
      (fun N => 4 * tailMomentBound / lam ^ 2
        + (steinhausMeasure {ω : Omega | ENNReal.ofReal (lam / 2) ≤ edist (HN N ω) (H ω)}).toReal)
      Filter.atTop (nhds (4 * tailMomentBound / lam ^ 2 + 0)) :=
    Filter.Tendsto.const_add _ h1
  rw [add_zero] at htend
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hbound)

end GaloisForLFunctions.RHTower

end
