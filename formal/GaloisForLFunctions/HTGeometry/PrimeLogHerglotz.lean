import GaloisForLFunctions.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# A prime-log discrete Herglotz source

This file constructs the actual positive Cauchy series used as the analytic source for facet-sewn
HT geometry.  Prime logarithms replace transcendental powers as pole locations: their rational
linear independence is already unconditional in the formal tree, and it gives an infinite-rank,
locally finite real support.  Dyadic prime-indexed weights give absolute convergence on every upper
half-plane point and the Herglotz sign.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A discrete positive Cauchy carrier. -/
def discreteHerglotz {ι : Type*} (support weight : ι → ℝ) (z : ℂ) : ℂ :=
  ∑' i, (weight i : ℂ) * ((support i : ℂ) - z)⁻¹

/-- Absolute convergence of a discrete Cauchy carrier in the upper half-plane. -/
theorem summable_discreteHerglotz_term
    {ι : Type*} (support weight : ι → ℝ) (z : ℂ) (hz : 0 < z.im)
    (hw : Summable fun i => ‖(weight i : ℂ)‖) :
    Summable fun i => (weight i : ℂ) * ((support i : ℂ) - z)⁻¹ := by
  have hb : ∀ i, z.im ≤ ‖(support i : ℂ) - z‖ := by
    intro i
    have h1 : |((support i : ℂ) - z).im| ≤ ‖(support i : ℂ) - z‖ :=
      Complex.abs_im_le_norm _
    have h2 : ((support i : ℂ) - z).im = -z.im := by simp [Complex.sub_im]
    rw [h2, abs_neg, abs_of_pos hz] at h1
    exact h1
  have hmajor : Summable fun i => ‖(weight i : ℂ)‖ * (z.im)⁻¹ := hw.mul_right _
  apply Summable.of_norm_bounded hmajor
  intro i
  rw [norm_mul, norm_inv]
  gcongr
  exact hb i

/-- Positive weights make the discrete Cauchy carrier Herglotz. -/
theorem discreteHerglotz_im_nonneg
    {ι : Type*} (support weight : ι → ℝ) (z : ℂ) (hz : 0 < z.im)
    (hweight : ∀ i, 0 ≤ weight i)
    (hw : Summable fun i => ‖(weight i : ℂ)‖) :
    0 ≤ (discreteHerglotz support weight z).im := by
  have hs := summable_discreteHerglotz_term support weight z hz hw
  rw [discreteHerglotz, Complex.im_tsum hs]
  apply tsum_nonneg
  intro i
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  exact mul_nonneg (hweight i) (div_nonneg hz.le (Complex.normSq_nonneg _))

/-- The open complex upper half-plane. -/
def upperHalfPlane : Set ℂ := {z | 0 < z.im}

theorem isOpen_upperHalfPlane : IsOpen upperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

/-- A discrete Cauchy series with absolutely summable weights converges locally uniformly on the
upper half-plane. -/
theorem summableLocallyUniformlyOn_discreteHerglotz
    {ι : Type*} (support weight : ι → ℝ)
    (hw : Summable fun i => ‖(weight i : ℂ)‖) :
    SummableLocallyUniformlyOn
      (fun i z => (weight i : ℂ) * ((support i : ℂ) - z)⁻¹) upperHalfPlane := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  have hzpos : 0 < z.im := hz
  refine ⟨Metric.ball z (z.im / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z (half_pos hzpos)), ?_⟩
  apply HasSumUniformlyOn.of_norm_le_summable
    (hw.mul_right (z.im / 2)⁻¹)
  intro i x hx
  have hnorm : ‖x - z‖ < z.im / 2 := by
    simpa [dist_eq_norm] using (Metric.mem_ball.mp hx)
  have himnorm : |(x - z).im| ≤ ‖x - z‖ := Complex.abs_im_le_norm _
  have habs : |x.im - z.im| < z.im / 2 := by
    exact lt_of_le_of_lt (by simpa [Complex.sub_im] using himnorm) hnorm
  have hxim : z.im / 2 < x.im := by
    rw [abs_lt] at habs
    linarith
  have hxim0 : 0 < x.im := (half_pos hzpos).trans hxim
  have hden : z.im / 2 ≤ ‖(support i : ℂ) - x‖ := by
    have hi : x.im ≤ ‖(support i : ℂ) - x‖ := by
      have h1 : |((support i : ℂ) - x).im| ≤ ‖(support i : ℂ) - x‖ :=
        Complex.abs_im_le_norm _
      have h2 : ((support i : ℂ) - x).im = -x.im := by simp [Complex.sub_im]
      rw [h2, abs_neg, abs_of_pos hxim0] at h1
      exact h1
    exact hxim.le.trans hi
  rw [norm_mul, norm_inv]
  gcongr

/-- The sum of a discrete Cauchy series is holomorphic on the upper half-plane. -/
theorem differentiableOn_discreteHerglotz_upperHalfPlane
    {ι : Type*} (support weight : ι → ℝ)
    (hw : Summable fun i => ‖(weight i : ℂ)‖) :
    DifferentiableOn ℂ (discreteHerglotz support weight) upperHalfPlane := by
  apply SummableLocallyUniformlyOn.differentiableOn isOpen_upperHalfPlane
    (summableLocallyUniformlyOn_discreteHerglotz support weight hw)
  intro i z hz
  have hne : (support i : ℂ) - z ≠ 0 := by
    intro h
    have heq : (support i : ℂ) = z := sub_eq_zero.mp h
    have hz0 : z.im = 0 := by rw [← heq]; simp
    exact (ne_of_gt hz) hz0
  exact (((differentiableAt_const (c := (support i : ℂ))).sub differentiableAt_id).inv hne).const_mul _

/-- The real support indexed by prime logarithms. -/
def primeLogSupport (p : Nat.Primes) : ℝ := Real.log (p : ℕ)

/-- Positive dyadic weights with a bounded logarithmic gauge. -/
def primeDyadicWeight (u : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  ((2 : ℝ)⁻¹) ^ (p : ℕ) * Real.exp (u p)

/-- A bounded-above gauge gives absolutely summable prime weights. -/
theorem summable_norm_primeDyadicWeight
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    Summable fun p => ‖(primeDyadicWeight u p : ℂ)‖ := by
  have hgeomNat : Summable fun n : ℕ => ((2 : ℝ)⁻¹) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hgeom : Summable fun p : Nat.Primes => ((2 : ℝ)⁻¹) ^ (p : ℕ) :=
    hgeomNat.subtype Nat.Prime
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (hgeom.mul_right (Real.exp C))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hu p)) (by positivity)
  · exact mul_nonneg (by positivity) (Real.exp_pos _).le

/-- Every prime weight is strictly positive. -/
theorem primeDyadicWeight_pos (u : Nat.Primes → ℝ) (p : Nat.Primes) :
    0 < primeDyadicWeight u p :=
  mul_pos (by positivity) (Real.exp_pos _)

/-- The prime-log Herglotz source with a bounded logarithmic gauge. -/
def primeLogHerglotz (u : Nat.Primes → ℝ) (z : ℂ) : ℂ :=
  discreteHerglotz primeLogSupport (primeDyadicWeight u) z

/-- The actual prime-log source has nonnegative imaginary part in the upper half-plane. -/
theorem primeLogHerglotz_im_nonneg
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (primeLogHerglotz u z).im := by
  exact discreteHerglotz_im_nonneg _ _ z hz
    (fun p => (primeDyadicWeight_pos u p).le)
    (summable_norm_primeDyadicWeight u C hu)

/-- The prime-log Herglotz carrier is holomorphic on the upper half-plane. -/
theorem differentiableOn_primeLogHerglotz_upperHalfPlane
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    DifferentiableOn ℂ (primeLogHerglotz u) upperHalfPlane :=
  differentiableOn_discreteHerglotz_upperHalfPlane _ _
    (summable_norm_primeDyadicWeight u C hu)

/-- Prime-log support is rationally linearly independent. -/
theorem primeLogSupport_linearIndependent :
    LinearIndependent ℚ primeLogSupport := by
  simpa [primeLogSupport] using GaloisForLFunctions.linearIndependent_log_primes

/-- The prime-log support has infinite rational rank: it is contained in no finite-dimensional
rational span generated by finitely many real numbers. -/
theorem primeLogSupport_not_contained_finite_span :
    ¬ ∃ s : Set ℝ, s.Finite ∧
      Set.range primeLogSupport ⊆ Submodule.span ℚ s := by
  rintro ⟨s, hs, hsub⟩
  let W : Submodule ℚ ℝ := Submodule.span ℚ s
  let f : Nat.Primes → W := fun p =>
    ⟨primeLogSupport p, hsub ⟨p, rfl⟩⟩
  letI : Module.Finite ℚ W := Module.Finite.of_fg (Submodule.fg_span hs)
  have hli : LinearIndependent ℚ f := by
    apply LinearIndependent.of_comp W.subtype
    simpa [f, Function.comp_def] using primeLogSupport_linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite f hli

/-- Every prime-log support point is positive. -/
theorem primeLogSupport_pos (p : Nat.Primes) : 0 < primeLogSupport p := by
  apply Real.log_pos
  exact_mod_cast p.2.one_lt

/-- The exponent-one Cauchy-feature energy after exponential transport by `b`, with `m`
additional prime-log decay factors.  Every finite rational cancellation of Cauchy sections has
this form up to a constant and a finite exceptional set. -/
def primeLogHerglotzTransportMassOrder (m : ℕ) (b : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (2 * b - 1) / (1 + (Real.log (p : ℝ)) ^ 2) ^ m

/-- **Every finite prime-log cancellation order still crosses every positive transport wall.**
For `b > 0` and every finite `m`, the transported energy with denominator
`(1 + (log p)^2)^m` diverges.  Thus no finite order of cancellation at infinity repairs the
prime-log Cauchy features after positive exponential transport. -/
theorem not_summable_primeLogHerglotzTransportMassOrder_of_pos
    (m : ℕ) {b : ℝ} (hb : 0 < b) :
    ¬ Summable (primeLogHerglotzTransportMassOrder m b) := by
  intro hsum
  by_cases hm : m = 0
  · subst m
    have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (2 * b - 1)) := by
      change Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (2 * b - 1) / (1 + (Real.log (p : ℝ)) ^ 2) ^ 0) at hsum
      simpa using hsum
    rw [Nat.Primes.summable_rpow] at hpow
    linarith
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let beta : ℝ := b / m
    let C : ℝ := 1 + ((beta / 2)⁻¹) ^ 2
    have hbeta : 0 < beta := by
      dsimp [beta]
      positivity
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hden : ∀ p : Nat.Primes,
        1 + (Real.log (p : ℝ)) ^ 2 ≤ C * (p : ℝ) ^ beta := by
      intro p
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_lt.le
      have heps : 0 < beta / 2 := by linarith
      have hlog := Real.log_le_rpow_div hp0.le heps
      have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
      have hright : 0 ≤ (p : ℝ) ^ (beta / 2) / (beta / 2) := by positivity
      have hlogsq0 : (Real.log (p : ℝ)) ^ 2 ≤
          ((p : ℝ) ^ (beta / 2) / (beta / 2)) ^ 2 :=
        (sq_le_sq₀ hlog0 hright).2 hlog
      have hrpow_sq : ((p : ℝ) ^ (beta / 2) / (beta / 2)) ^ 2 =
          ((beta / 2)⁻¹) ^ 2 * (p : ℝ) ^ beta := by
        calc
          ((p : ℝ) ^ (beta / 2) / (beta / 2)) ^ 2 =
              ((beta / 2)⁻¹) ^ 2 * (((p : ℝ) ^ (beta / 2)) ^ 2) := by ring
          _ = ((beta / 2)⁻¹) ^ 2 * (p : ℝ) ^ ((beta / 2) * 2) := by
            rw [← Real.rpow_mul_natCast hp0.le]
            norm_num
          _ = ((beta / 2)⁻¹) ^ 2 * (p : ℝ) ^ beta := by ring_nf
      have hlogsq : (Real.log (p : ℝ)) ^ 2 ≤
          ((beta / 2)⁻¹) ^ 2 * (p : ℝ) ^ beta := by
        rw [← hrpow_sq]
        exact hlogsq0
      have hpow1 : 1 ≤ (p : ℝ) ^ beta := Real.one_le_rpow hp1 hbeta.le
      change 1 + (Real.log (p : ℝ)) ^ 2 ≤
        (1 + ((beta / 2)⁻¹) ^ 2) * (p : ℝ) ^ beta
      nlinarith [sq_nonneg ((beta / 2)⁻¹), Real.rpow_nonneg hp0.le beta]
    have hdenpow : ∀ p : Nat.Primes,
        (1 + (Real.log (p : ℝ)) ^ 2) ^ m ≤ C ^ m * (p : ℝ) ^ b := by
      intro p
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
      calc
        (1 + (Real.log (p : ℝ)) ^ 2) ^ m ≤ (C * (p : ℝ) ^ beta) ^ m := by
          gcongr
          exact hden p
        _ = C ^ m * ((p : ℝ) ^ beta) ^ m := by rw [mul_pow]
        _ = C ^ m * (p : ℝ) ^ (beta * m) := by
          rw [← Real.rpow_mul_natCast hp0.le]
        _ = C ^ m * (p : ℝ) ^ b := by
          congr 2
          dsimp [beta]
          field_simp
    have hmajor : ∀ p : Nat.Primes,
        (C ^ m)⁻¹ * (p : ℝ) ^ (b - 1) ≤
          primeLogHerglotzTransportMassOrder m b p := by
      intro p
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hdenpos : 0 < (1 + (Real.log (p : ℝ)) ^ 2) ^ m := by positivity
      rw [primeLogHerglotzTransportMassOrder, le_div_iff₀ hdenpos]
      calc
        (C ^ m)⁻¹ * (p : ℝ) ^ (b - 1) *
              (1 + (Real.log (p : ℝ)) ^ 2) ^ m
            ≤ (C ^ m)⁻¹ * (p : ℝ) ^ (b - 1) *
              (C ^ m * (p : ℝ) ^ b) := by
                gcongr
                exact hdenpow p
        _ = (p : ℝ) ^ (2 * b - 1) := by
          calc
            (C ^ m)⁻¹ * (p : ℝ) ^ (b - 1) * (C ^ m * (p : ℝ) ^ b) =
                ((C ^ m)⁻¹ * C ^ m) *
                  ((p : ℝ) ^ (b - 1) * (p : ℝ) ^ b) := by ring
            _ = (p : ℝ) ^ (b - 1) * (p : ℝ) ^ b := by
              rw [inv_mul_cancel₀ (pow_ne_zero m hCpos.ne'), one_mul]
            _ = (p : ℝ) ^ ((b - 1) + b) := by rw [Real.rpow_add hp0]
            _ = (p : ℝ) ^ (2 * b - 1) := by ring_nf
    have hscaled : Summable
        (fun p : Nat.Primes => (C ^ m)⁻¹ * (p : ℝ) ^ (b - 1)) := by
      apply Summable.of_nonneg_of_le
      · intro p
        positivity
      · exact hmajor
      · exact hsum
    have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (b - 1)) :=
      (summable_mul_left_iff (inv_ne_zero (pow_ne_zero m hCpos.ne'))).mp hscaled
    rw [Nat.Primes.summable_rpow] at hpow
    linarith

/-- The canonical one-denominator Cauchy-feature energy after exponential transport by `b`. -/
def primeLogHerglotzTransportMass (b : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (2 * b - 1) / (1 + (Real.log (p : ℝ)) ^ 2)

/-- **Every positive exponential transport crosses the prime-log Herglotz domain wall.** -/
theorem not_summable_primeLogHerglotzTransportMass_of_pos
    {b : ℝ} (hb : 0 < b) :
    ¬ Summable (primeLogHerglotzTransportMass b) := by
  intro hsum
  apply not_summable_primeLogHerglotzTransportMassOrder_of_pos 1 hb
  change Summable (fun p : Nat.Primes =>
    (p : ℝ) ^ (2 * b - 1) / (1 + (Real.log (p : ℝ)) ^ 2)) at hsum
  change Summable (fun p : Nat.Primes =>
    (p : ℝ) ^ (2 * b - 1) / (1 + (Real.log (p : ℝ)) ^ 2) ^ 1)
  simpa using hsum

/-- Distinct primes give distinct support points. -/
theorem primeLogSupport_injective : Function.Injective primeLogSupport :=
  primeLogSupport_linearIndependent.injective

/-- Prime-log support is locally finite on the real line. -/
theorem finite_primeLogSupport_le (R : ℝ) :
    Set.Finite {p : Nat.Primes | primeLogSupport p ≤ R} := by
  let N : ℕ := ⌈Real.exp R⌉₊
  have hfinite : Set.Finite {p : Nat.Primes | (p : ℕ) ≤ N} := by
    change (Subtype.val ⁻¹' Set.Iic N).Finite
    exact Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective) (Set.finite_Iic N)
  apply hfinite.subset
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hpreal : ((p : ℕ) : ℝ) ≤ Real.exp R := by
    calc
      ((p : ℕ) : ℝ) = Real.exp (Real.log ((p : ℕ) : ℝ)) :=
        (Real.exp_log hp0).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hp
  have hceil : ((p : ℕ) : ℝ) ≤ (N : ℝ) :=
    hpreal.trans (Nat.le_ceil (Real.exp R))
  exact_mod_cast hceil

/-- The complex pole carrier of the prime-log source. -/
def primeLogPoleSet : Set ℂ :=
  Set.range fun p : Nat.Primes => (primeLogSupport p : ℂ)

/-- Local finiteness of prime logarithms makes their complex complement open. -/
theorem isOpen_compl_primeLogPoleSet : IsOpen (primeLogPoleSetᶜ) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := z.re + 1
  let F : Set Nat.Primes := {p | primeLogSupport p ≤ R}
  have hF : F.Finite := finite_primeLogSupport_le R
  let E : Set ℂ := (fun p : Nat.Primes => (primeLogSupport p : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨{w : ℂ | w.re < R} \ E, ?_, ?_, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    rcases hwPole with ⟨p, hpw⟩
    apply hw.2
    refine ⟨p, ?_, hpw⟩
    change primeLogSupport p ≤ R
    have hwre : w.re < R := hw.1
    rw [← hpw] at hwre
    simpa using hwre.le
  · exact (isOpen_lt Complex.continuous_re continuous_const).sdiff hE.isClosed
  · constructor
    · simp [R]
    · intro hzE
      rcases hzE with ⟨p, hpF, hpz⟩
      apply hz
      exact ⟨p, hpz⟩

/-- The prime-log Cauchy series converges locally uniformly away from its pole carrier. -/
theorem summableLocallyUniformlyOn_primeLogHerglotz_off_poles
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    SummableLocallyUniformlyOn
      (fun p z => (primeDyadicWeight u p : ℂ) *
        ((primeLogSupport p : ℂ) - z)⁻¹) primeLogPoleSetᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    isOpen_compl_primeLogPoleSet
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨fun p => ‖(primeDyadicWeight u p : ℂ)‖,
    summable_norm_primeDyadicWeight u C hu, ?_⟩
  have hfinite := finite_primeLogSupport_le (R + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
  intro z hz
  have hpLarge : R + 1 < primeLogSupport p := by
    simpa using lt_of_not_ge hp
  have hzNorm : ‖z‖ ≤ R := hR z hz
  have hpNorm : ‖(primeLogSupport p : ℂ)‖ = primeLogSupport p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeLogSupport_pos p)]
  have hden : 1 ≤ ‖(primeLogSupport p : ℂ) - z‖ := by
    calc
      (1 : ℝ) ≤ primeLogSupport p - R := by linarith
      _ ≤ ‖(primeLogSupport p : ℂ)‖ - ‖z‖ := by rw [hpNorm]; linarith
      _ ≤ ‖(primeLogSupport p : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv]
  have hinv : ‖(primeLogSupport p : ℂ) - z‖⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
  simpa using
    (mul_le_mul_of_nonneg_left hinv (norm_nonneg (primeDyadicWeight u p : ℂ)))

/-- The prime-log source is holomorphic on the complement of its full pole carrier. -/
theorem differentiableOn_primeLogHerglotz_off_poles
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    DifferentiableOn ℂ (primeLogHerglotz u) primeLogPoleSetᶜ := by
  apply SummableLocallyUniformlyOn.differentiableOn isOpen_compl_primeLogPoleSet
    (summableLocallyUniformlyOn_primeLogHerglotz_off_poles u C hu)
  intro p z hz
  have hne : (primeLogSupport p : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    exact ⟨p, sub_eq_zero.mp h⟩
  exact (((differentiableAt_const (c := (primeLogSupport p : ℂ))).sub
    differentiableAt_id).inv hne).const_mul _

/-- The defining prime-log series is absolutely summable at every non-exceptional Lean value;
at a pole, inversion sends the single singular denominator to zero, while the remaining series is
still absolutely summable.  Analytic pole behavior is recorded separately by regularization. -/
theorem summable_primeLogHerglotz_term
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (z : ℂ) :
    Summable fun p => (primeDyadicWeight u p : ℂ) *
      ((primeLogSupport p : ℂ) - z)⁻¹ := by
  apply Summable.of_norm_bounded_eventually (summable_norm_primeDyadicWeight u C hu)
  have hfinite := finite_primeLogSupport_le (‖z‖ + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
  have hpLarge : ‖z‖ + 1 < primeLogSupport p := by
    simpa using lt_of_not_ge hp
  have hpNorm : ‖(primeLogSupport p : ℂ)‖ = primeLogSupport p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeLogSupport_pos p)]
  have hden : 1 ≤ ‖(primeLogSupport p : ℂ) - z‖ := by
    calc
      (1 : ℝ) ≤ primeLogSupport p - ‖z‖ := by linarith
      _ = ‖(primeLogSupport p : ℂ)‖ - ‖z‖ := by rw [hpNorm]
      _ ≤ ‖(primeLogSupport p : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv]
  have hinv : ‖(primeLogSupport p : ℂ) - z‖⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
  simpa using
    (mul_le_mul_of_nonneg_left hinv (norm_nonneg (primeDyadicWeight u p : ℂ)))

/-- Pole carrier restricted to an arbitrary subfamily of primes.  This is the form needed to
remove one pole and study its analytic regular part. -/
def primeLogPoleSetOn (S : Set Nat.Primes) : Set ℂ :=
  Set.range fun p : S => (primeLogSupport p : ℂ)

theorem finite_primeLogSupport_le_on (S : Set Nat.Primes) (R : ℝ) :
    Set.Finite {p : S | primeLogSupport p ≤ R} := by
  change ((Subtype.val : S → Nat.Primes) ⁻¹' {p | primeLogSupport p ≤ R}).Finite
  exact (finite_primeLogSupport_le R).preimage
    (Set.injOn_of_injective Subtype.val_injective)

theorem isOpen_compl_primeLogPoleSetOn (S : Set Nat.Primes) :
    IsOpen ((primeLogPoleSetOn S)ᶜ) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := z.re + 1
  let F : Set S := {p | primeLogSupport p ≤ R}
  have hF : F.Finite := finite_primeLogSupport_le_on S R
  let E : Set ℂ := (fun p : S => (primeLogSupport p : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨{w : ℂ | w.re < R} \ E, ?_, ?_, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    intro hwPole
    rcases hwPole with ⟨p, hpw⟩
    apply hw.2
    refine ⟨p, ?_, hpw⟩
    change primeLogSupport p ≤ R
    have hwre : w.re < R := hw.1
    rw [← hpw] at hwre
    simpa using hwre.le
  · exact (isOpen_lt Complex.continuous_re continuous_const).sdiff hE.isClosed
  · constructor
    · simp [R]
    · intro hzE
      rcases hzE with ⟨p, hpF, hpz⟩
      apply hz
      exact ⟨p, hpz⟩

theorem summableLocallyUniformlyOn_primeLogHerglotz_on_off_poles
    (S : Set Nat.Primes) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    SummableLocallyUniformlyOn
      (fun p : S => fun z => (primeDyadicWeight u p : ℂ) *
        ((primeLogSupport p : ℂ) - z)⁻¹) (primeLogPoleSetOn S)ᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_compl_primeLogPoleSetOn S)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  refine ⟨fun p : S => ‖(primeDyadicWeight u p : ℂ)‖,
    (summable_norm_primeDyadicWeight u C hu).subtype S, ?_⟩
  have hfinite := finite_primeLogSupport_le_on S (R + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
  intro z hz
  have hpLarge : R + 1 < primeLogSupport p := by
    simpa using lt_of_not_ge hp
  have hzNorm : ‖z‖ ≤ R := hR z hz
  have hpNorm : ‖(primeLogSupport p : ℂ)‖ = primeLogSupport p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (primeLogSupport_pos p)]
  have hden : 1 ≤ ‖(primeLogSupport p : ℂ) - z‖ := by
    calc
      (1 : ℝ) ≤ primeLogSupport p - R := by linarith
      _ ≤ ‖(primeLogSupport p : ℂ)‖ - ‖z‖ := by rw [hpNorm]; linarith
      _ ≤ ‖(primeLogSupport p : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv]
  have hinv : ‖(primeLogSupport p : ℂ) - z‖⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
  simpa using
    (mul_le_mul_of_nonneg_left hinv (norm_nonneg (primeDyadicWeight u p : ℂ)))

/-- The regular part obtained by deleting one prime-log atom. -/
def primeLogTail (u : Nat.Primes → ℝ) (p₀ : Nat.Primes) (z : ℂ) : ℂ :=
  ∑' q : {q : Nat.Primes // q ∉ ({p₀} : Finset Nat.Primes)},
    (primeDyadicWeight u q : ℂ) * ((primeLogSupport q : ℂ) - z)⁻¹

theorem primeLogCenter_notMem_otherPoleSet (p₀ : Nat.Primes) :
    (primeLogSupport p₀ : ℂ) ∈
      (primeLogPoleSetOn {q : Nat.Primes | q ∉ ({p₀} : Finset Nat.Primes)})ᶜ := by
  rw [Set.mem_compl_iff]
  rintro ⟨q, hq⟩
  apply q.property
  simp only [Finset.mem_singleton]
  apply primeLogSupport_injective
  exact Complex.ofReal_injective hq

/-- Deleting one atom leaves a holomorphic germ at that atom's former pole. -/
theorem differentiableAt_primeLogTail
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (p₀ : Nat.Primes) :
    DifferentiableAt ℂ (primeLogTail u p₀) (primeLogSupport p₀ : ℂ) := by
  let S : Set Nat.Primes := {q | q ∉ ({p₀} : Finset Nat.Primes)}
  have hsum := summableLocallyUniformlyOn_primeLogHerglotz_on_off_poles S u C hu
  have hdiff : DifferentiableOn ℂ (primeLogTail u p₀) (primeLogPoleSetOn S)ᶜ := by
    apply SummableLocallyUniformlyOn.differentiableOn
      (isOpen_compl_primeLogPoleSetOn S) hsum
    intro q z hz
    have hne : (primeLogSupport q : ℂ) - z ≠ 0 := by
      intro h
      apply hz
      exact ⟨q, sub_eq_zero.mp h⟩
    exact (((differentiableAt_const (c := (primeLogSupport q : ℂ))).sub
      differentiableAt_id).inv hne).const_mul _
  exact (hdiff _ (primeLogCenter_notMem_otherPoleSet p₀)).differentiableAt
    ((isOpen_compl_primeLogPoleSetOn S).mem_nhds
      (primeLogCenter_notMem_otherPoleSet p₀))

/-- Exact polar splitting: the source plus its cancelling principal part is the regular tail. -/
theorem primeLogHerglotz_add_polar_eq_tail
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (p₀ : Nat.Primes) (z : ℂ) :
    primeLogHerglotz u z + (primeDyadicWeight u p₀ : ℂ) *
      (z - (primeLogSupport p₀ : ℂ))⁻¹ = primeLogTail u p₀ z := by
  let f : Nat.Primes → ℂ := fun p => (primeDyadicWeight u p : ℂ) *
    ((primeLogSupport p : ℂ) - z)⁻¹
  have hsum : Summable f := summable_primeLogHerglotz_term u C hu z
  have hsplit := hsum.sum_add_tsum_subtype_compl {p₀}
  have heq : f p₀ + primeLogTail u p₀ z = primeLogHerglotz u z := by
    simpa [f, primeLogTail, primeLogHerglotz, discreteHerglotz] using hsplit
  rw [← heq]
  have hinv : ((primeLogSupport p₀ : ℂ) - z)⁻¹ =
      -(z - (primeLogSupport p₀ : ℂ))⁻¹ := by
    rw [← inv_neg, neg_sub]
  rw [show f p₀ = (primeDyadicWeight u p₀ : ℂ) *
      ((primeLogSupport p₀ : ℂ) - z)⁻¹ by rfl, hinv]
  ring

/-- Intrinsic simple-pole predicate: a nonzero polar coefficient whose subtraction leaves a
continuous germ at the center. -/
def HasSimplePoleAt (f : ℂ → ℂ) (a residue : ℂ) : Prop :=
  residue ≠ 0 ∧ ContinuousAt (fun z => f z - residue * (z - a)⁻¹) a

/-- Every prime logarithm is an exact simple pole, with the explicit nonzero negative residue. -/
theorem hasSimplePoleAt_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (p₀ : Nat.Primes) :
    HasSimplePoleAt (primeLogHerglotz u) (primeLogSupport p₀ : ℂ)
      (-(primeDyadicWeight u p₀ : ℂ)) := by
  constructor
  · exact neg_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (primeDyadicWeight_pos u p₀)))
  · have htail := (differentiableAt_primeLogTail u C hu p₀).continuousAt
    convert htail using 1
    funext z
    simpa using primeLogHerglotz_add_polar_eq_tail u C hu p₀ z

end

end GaloisForLFunctions.HTGeometry
