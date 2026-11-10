import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.EulerPhaseCurvature
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.QuadraticGaugeRigidity

/-!
# The prime metric of a pole residue

For a uniformly bounded holomorphic family of prime phases through the
trivial gauge, joint holomorphic continuation of the actual regularized
Euler fibre forces an exact residue-curvature identity:

`-∂² log |U(t,1)| = ∑_p a_p² p/(p-1)²`, where `u_p'(0)=i a_p`.

The proof derives convergence from the finite boundary curvature.
Its nullspace consists exactly of vanishing first prime-phase variations.
Finite energy is equivalent to square summability for the prime harmonic
measure, excluding the constant unit prime speed.
-/

open Complex Filter Topology Metric
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open GaloisForLFunctions.ArithmeticWeightTheory
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Prime damping on the real Euler half-plane. -/
def primeDamping (σ : ℝ) (p : Nat.Primes) : ℝ := ((p : ℕ) : ℝ) ^ (-σ)

theorem primeDamping_pos (σ : ℝ) (p : Nat.Primes) : 0 < primeDamping σ p :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

theorem primeDamping_le_inv {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) :
    primeDamping σ p ≤ 1 / (p : ℕ) := by
  calc primeDamping σ p ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
         Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)
       _ = 1 / (p : ℕ) := by rw [Real.rpow_neg_one, one_div]

theorem primeDamping_le_half {σ : ℝ} (hσ : 1 ≤ σ) (p : Nat.Primes) :
    primeDamping σ p ≤ 1 / 2 :=
  (primeDamping_le_inv hσ p).trans
    (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast p.2.two_le))

theorem summable_primeDamping {σ : ℝ} (hσ : 1 < σ) : Summable (primeDamping σ) :=
  summable_primes_rpow (by linarith : -σ < -1)

theorem ofReal_primeDamping (σ : ℝ) (p : Nat.Primes) :
    (primeDamping σ p : ℂ) = ((p : ℕ) : ℂ) ^ (-(σ : ℂ)) := by
  rw [primeDamping, ← prime_exp_decay, ← prime_cexp_decay, Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

/-- The logarithmic parameter sum is the actual gauge fibre on the Euler half-plane. -/
theorem exp_phaseEulerLog_eq_gaugeFibre {u : Nat.Primes → ℂ → ℂ}
    {t : ℂ} {x : GaugeTorus} {σ : ℝ} (hσ : 1 < σ)
    (hu : ∀ p, u p t = twist x p) :
    Complex.exp (∑' p, phaseEulerLog (primeDamping σ p) (u p) t) = gaugeFibre x (σ : ℂ) := by
  have hs : 1 < (σ : ℂ).re := hσ
  rw [← exp_tsum_eq_gaugeFibre x hs, hullRem,
    ← (summable_eulerVar (norm_twist_prime x) hs).tsum_add
      (summable_localRem (norm_twist_prime x) (by linarith : 1 / 2 < (σ : ℂ).re))]
  congr 1
  apply tsum_congr
  intro p
  simp only [phaseEulerLog, localRem, eulerVar, powCoeff, hu p, ofReal_primeDamping]
  ring

/-- Continuation through the zeta fibre fixes its initial pole residue. -/
theorem regularized_gauge_initial_residue {E : Type*} [TopologicalSpace E] [Zero E]
    {x : ℝ → GaugeTorus} {U : E × ℂ → ℂ}
    {ε : ℝ} (hε : 0 < ε) (hx : x 0 = 0) (hU : ContinuousAt U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + ε →
      U (0, (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x 0) (σ : ℂ)) :
    U (0, 1) = 1 := by
  have hu : Tendsto (fun σ : ℝ => U (0, (σ : ℂ))) (𝓝[>] 1) (𝓝 (U (0, 1))) := by
    have hp : ContinuousAt (fun σ : ℝ => ((0 : E), (σ : ℂ))) 1 :=
      continuousAt_const.prodMk Complex.continuous_ofReal.continuousAt
    exact hU.tendsto.comp (hp.tendsto.mono_left nhdsWithin_le_nhds)
  have hz : Tendsto (fun σ : ℝ => U (0, (σ : ℂ))) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    refine (riemannZeta_residue_one.comp RHTower.tendsto_ofReal_nhdsWithin_ne_one).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + ε)).filter_mono nhdsWithin_le_nhds] with σ hσ hσε
    rw [hagree σ hσ hσε, hx, gaugeFibre_trivial (s := (σ : ℂ)) hσ]
    rfl
  exact tendsto_nhds_unique hu hz

/-- The logarithmic curvature weight increases with its Euler damping. -/
theorem phase_weight_mono {a q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r < 1) :
    a ^ 2 * q / (1 - q) ^ 2 ≤ a ^ 2 * r / (1 - r) ^ 2 := by
  apply div_le_div₀ (mul_nonneg (sq_nonneg a) (hq.trans hqr))
    (mul_le_mul_of_nonneg_left hqr (sq_nonneg _))
    (sq_pos_of_pos (sub_pos.mpr hr))
  exact pow_le_pow_left₀ (sub_nonneg.mpr hr.le) (sub_le_sub_left hqr 1) 2

theorem prime_boundary_weight (a : ℝ) (p : Nat.Primes) :
    a ^ 2 * primeDamping 1 p / (1 - primeDamping 1 p) ^ 2 =
      a ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2 := by
  rw [primeDamping, Real.rpow_neg_one]
  have hp : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hp1 : ((p : ℕ) : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast p.2.one_lt)).ne'
  field_simp

/-- A jointly holomorphic regularization forces the exact convergent prime residue metric. -/
theorem gauge_residue_curvature_hasSum {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ t : ℝ, |t| < R →
      U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x t) (σ : ℂ)) :
    HasSum (fun p : Nat.Primes =>
      (deriv (u p) 0).im ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2)
      (-deriv (deriv (fun t : ℝ => Real.log ‖U ((t : ℂ), 1)‖)) 0) := by
  have ht0 : |(0 : ℝ)| < R := by simpa using hR
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hbd (⟨2, Nat.prime_two⟩ : Nat.Primes) 0 (mem_ball_self hR))
  have hu0 : ∀ p, u p 0 = 1 := by
    intro p
    simpa only [Complex.ofReal_zero, hx0, twist_trivial] using hphase 0 ht0 p
  have hphaseNear : ∀ᶠ t : ℝ in 𝓝 0, ∀ p, u p (t : ℂ) = twist (x t) p := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR : (0 : ℝ) ∈ ball 0 R)] with t ht
    exact hphase t (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht)
  have hunit : ∀ p, ∀ᶠ t : ℝ in 𝓝 0, ‖u p (t : ℂ)‖ = 1 := by
    intro p
    filter_upwards [hphaseNear] with t ht
    rw [ht p, norm_twist]
  have hU0 : U (0, 1) = 1 := regularized_gauge_initial_residue hR hx0 hU.continuousAt
    (fun σ hσ hσR => by simpa only [Complex.ofReal_zero] using hagree σ hσ hσR 0 ht0)
  have hsl : U (0, 1) ∈ Complex.slitPlane := by rw [hU0]; exact Or.inl (by norm_num)
  let a : Nat.Primes → ℝ := fun p => (deriv (u p) 0).im
  let f : ℝ → Nat.Primes → ℝ := fun σ p =>
    a p ^ 2 * primeDamping σ p / (1 - primeDamping σ p) ^ 2
  have hseries (σ : ℝ) (hσ : 1 < σ) :
      HasSum (f σ) (-(deriv (deriv
        (fun z => ∑' p, phaseEulerLog (primeDamping σ p) (u p) z)) 0).re) :=
    hasSum_phaseEulerLog_curvature hR hM hu hbd hu0 hunit
      (fun p => (primeDamping_pos σ p).le) (primeDamping_le_half hσ.le)
      (summable_primeDamping hσ)
  have hlim (p : Nat.Primes) : Tendsto (fun σ => f σ p) (𝓝[>] 1) (𝓝 (f 1 p)) := by
    have hq : ContinuousAt (fun σ : ℝ => primeDamping σ p) 1 :=
      (Real.continuous_const_rpow (by exact_mod_cast p.2.ne_zero)).continuousAt.comp continuousAt_id.neg
    have hn : 1 - primeDamping 1 p ≠ 0 :=
      (sub_pos.mpr ((primeDamping_le_half le_rfl p).trans_lt (by norm_num))).ne'
    exact ((continuousAt_const.mul hq).div ((continuousAt_const.sub hq).pow 2)
      (pow_ne_zero _ hn)).tendsto.mono_left nhdsWithin_le_nhds
  have htotal : Tendsto (fun σ => ∑' p, f σ p) (𝓝[>] 1) (𝓝 (residueCurvature U 1)) := by
    have hc : Tendsto (fun σ : ℝ => residueCurvature U (σ : ℂ)) (𝓝[>] 1)
        (𝓝 (residueCurvature U 1)) := by
      have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
        simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
      exact (residueCurvature_continuousAt hU hsl).tendsto.comp hc
    have hp : ContinuousAt (fun σ : ℝ => ((0 : ℂ), (σ : ℂ))) 1 :=
      continuousAt_const.prodMk Complex.continuous_ofReal.continuousAt
    have ha : ∀ᶠ σ : ℝ in 𝓝 1, AnalyticAt ℂ U (0, (σ : ℂ)) := by
      exact hp.tendsto.eventually (by simpa using hU.eventually_analyticAt)
    have hsn : ∀ᶠ σ : ℝ in 𝓝 1, U (0, (σ : ℂ)) ∈ Complex.slitPlane := by
      exact (hU.continuousAt.tendsto.comp hp.tendsto).eventually
        (Complex.isOpen_slitPlane.mem_nhds hsl)
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      ha.filter_mono nhdsWithin_le_nhds, hsn.filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + R)).filter_mono nhdsWithin_le_nhds]
      with σ hσ haσ hsσ hσR
    rw [(hseries σ hσ).tsum_eq, residueCurvature_eq_real_second haσ hsσ]
    have hG := (phaseEulerLog_tsum_regular hR hM hu hbd hu0
      (fun p => (primeDamping_pos σ p).le) (primeDamping_le_half hσ.le)
      (summable_primeDamping hσ)).1
    rw [real_second_logNorm_of_const_exp
      (show (σ : ℂ) - 1 ≠ 0 by exact_mod_cast (sub_pos.mpr hσ).ne') hG (by
        filter_upwards [hphaseNear,
          isOpen_ball.mem_nhds (mem_ball_self hR : (0 : ℝ) ∈ ball 0 R)] with t ht hp
        rw [hagree σ hσ hσR t (by
          simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hp),
          exp_phaseEulerLog_eq_gaugeFibre hσ (ht)])]
  have hright : ∀ᶠ σ : ℝ in 𝓝[>] 1, 1 < σ := self_mem_nhdsWithin
  have hb : HasSum (f 1) (residueCurvature U 1) :=
    hasSum_of_nonneg_dominated_boundary
      (Eventually.of_forall fun σ p =>
        div_nonneg (mul_nonneg (sq_nonneg _) (primeDamping_pos σ p).le) (sq_nonneg _))
      (hright.mono fun σ hσ => (hseries σ hσ).summable) hlim
      (hright.mono fun σ hσ p => phase_weight_mono (primeDamping_pos σ p).le
        (by simpa only [primeDamping, Real.rpow_neg_one, one_div] using primeDamping_le_inv hσ.le p)
        ((primeDamping_le_half le_rfl p).trans_lt (by norm_num))) htotal
  rw [residueCurvature_eq_real_second hU hsl] at hb
  simpa only [f, a, prime_boundary_weight] using hb


/-- Euler curvature is uniformly comparable to its first prime-power term. -/
theorem phase_weight_bounds (a : ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    a ^ 2 * q ≤ a ^ 2 * q / (1 - q) ^ 2 ∧
      a ^ 2 * q / (1 - q) ^ 2 ≤ 4 * (a ^ 2 * q) := by
  have hn : 0 ≤ a ^ 2 * q := mul_nonneg (sq_nonneg _) hq0
  have hd : 0 < (1 - q) ^ 2 := sq_pos_of_pos (by linarith)
  have hd1 : (1 - q) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - q) (by linarith : 1 - q ≤ 1) 2
    simpa only [one_pow] using h
  have hd0 : (1 / 4 : ℝ) ≤ (1 - q) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : (1 / 2 : ℝ) ≤ 1 - q) 2
    norm_num at h ⊢
    exact h
  constructor
  · calc a ^ 2 * q = a ^ 2 * q / 1 := by rw [div_one]
         _ ≤ a ^ 2 * q / (1 - q) ^ 2 := div_le_div₀ hn le_rfl hd hd1
  · calc a ^ 2 * q / (1 - q) ^ 2 ≤ a ^ 2 * q / (1 / 4) :=
           div_le_div₀ hn le_rfl (by norm_num) hd0
         _ = 4 * (a ^ 2 * q) := by ring

/-- Finite residue energy is exactly square summability for the prime harmonic measure. -/
theorem prime_residue_metric_summable_iff (a : Nat.Primes → ℝ) :
    Summable (fun p : Nat.Primes => a p ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2) ↔
      Summable (fun p : Nat.Primes => a p ^ 2 / (p : ℕ)) := by
  have he : (fun p : Nat.Primes => a p ^ 2 * (p : ℕ) / ((p : ℕ) - 1 : ℝ) ^ 2) =
      (fun p => a p ^ 2 * primeDamping 1 p / (1 - primeDamping 1 p) ^ 2) :=
    funext fun p => (prime_boundary_weight (a p) p).symm
  have he' : (fun p : Nat.Primes => a p ^ 2 / (p : ℕ)) =
      (fun p => a p ^ 2 * primeDamping 1 p) := by
    funext p
    rw [primeDamping, Real.rpow_neg_one, div_eq_mul_inv]
  rw [he, he']
  have hp (p : Nat.Primes) := phase_weight_bounds (a p) (primeDamping_pos 1 p).le
    (primeDamping_le_half le_rfl p)
  constructor
  · intro hs
    exact hs.of_nonneg_of_le (fun p => mul_nonneg (sq_nonneg _) (primeDamping_pos 1 p).le)
      (fun p => (hp p).1)
  · intro hs
    exact (hs.mul_left 4).of_nonneg_of_le
      (fun p => div_nonneg (mul_nonneg (sq_nonneg _) (primeDamping_pos 1 p).le) (sq_nonneg _))
      (fun p => (hp p).2)

/-- The constant unit prime speed has infinite residue energy. -/
theorem not_summable_prime_residue_weights_one :
    ¬Summable (fun p : Nat.Primes => (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  intro hs
  have h := (prime_residue_metric_summable_iff (fun _ => 1)).mp (by simpa using hs)
  have hp : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-1 : ℝ)) := by
    simpa only [one_pow, Real.rpow_neg_one, one_div] using h
  have hh := Nat.Primes.summable_rpow.mp hp
  norm_num at hh


/-- The residue metric detects exactly the prime-phase tangent directions. -/
theorem gauge_residue_tangent_classification {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ t : ℝ, |t| < R →
      U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x t) (σ : ℂ)) :
    Summable (fun p : Nat.Primes => (deriv (u p) 0).im ^ 2 / (p : ℕ)) ∧
      ((-deriv (deriv (fun t : ℝ => Real.log ‖U ((t : ℂ), 1)‖)) 0) = 0 ↔
        ∀ p, deriv (u p) 0 = 0) ∧
      ¬(∀ p, deriv (u p) 0 = Complex.I) := by
  have hsum := gauge_residue_curvature_hasSum hR hx0 hu hbd hphase hU hagree
  have hspeed (p : Nat.Primes) : (deriv (u p) 0).re = 0 := by
    have hu0 : u p 0 = 1 := by
      simpa only [Complex.ofReal_zero, hx0, twist_trivial] using
        hphase 0 (by simpa using hR) p
    have hunit : ∀ᶠ t : ℝ in 𝓝 0, ‖u p (t : ℂ)‖ = 1 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR : (0 : ℝ) ∈ ball 0 R)] with t ht
      rw [hphase t (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht) p,
        norm_twist]
    exact (unit_phase_jets ((hu p).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR)))
      hu0 hunit).1
  have hqsum : HasSum (fun p => (deriv (u p) 0).im ^ 2 * primeDamping 1 p /
      (1 - primeDamping 1 p) ^ 2)
      (-deriv (deriv (fun t : ℝ => Real.log ‖U ((t : ℂ), 1)‖)) 0) := by
    simpa only [prime_boundary_weight] using hsum
  have hz := phase_curvature_zero_iff (a := fun p => (deriv (u p) 0).im)
    (primeDamping_pos 1) (fun p => (primeDamping_le_half le_rfl p).trans_lt (by norm_num))
    hqsum.summable
  rw [hqsum.tsum_eq] at hz
  refine ⟨(prime_residue_metric_summable_iff _).mp hsum.summable, hz.trans ?_, ?_⟩
  · constructor
    · intro h p
      exact Complex.ext (by simpa using hspeed p) (by simpa using h p)
    · intro h p
      rw [h p, Complex.zero_im]
  · intro h
    apply not_summable_prime_residue_weights_one
    simpa only [h, Complex.I_im, one_pow, one_mul] using hsum.summable

#print axioms regularized_gauge_initial_residue
#print axioms gauge_residue_curvature_hasSum
#print axioms prime_residue_metric_summable_iff
#print axioms not_summable_prime_residue_weights_one
#print axioms gauge_residue_tangent_classification
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
