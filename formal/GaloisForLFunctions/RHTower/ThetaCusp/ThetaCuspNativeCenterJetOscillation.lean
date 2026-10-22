import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspImaginaryAllOrderFlatness
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeSixthRankBoundary
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Sign oscillation of the actual native center jets

The complete source's imaginary square is flat at the odd-cusp endpoint.
Its Taylor jets cannot have either eventual sign: a one-signed tail would
vanish by the endpoint limit, and descending through the remaining finite
Taylor polynomial would kill its positive center value.
-/

open Complex Filter Topology Set
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem analytic_jet {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (m : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv m f) U := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv m

private theorem hasSum_real_jet {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) (m : ℕ) {x : ℝ}
    (hx : |x| < R) :
    HasSum (fun n : ℕ => (n.factorial:ℝ)⁻¹ * x^n *
      (iteratedDeriv (n+m) f 0).re) (iteratedDeriv m f (x:ℂ)).re := by
  have hz : (x:ℂ) ∈ Metric.ball (0:ℂ) R := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hs := Complex.hasSum_re
    (Complex.hasSum_taylorSeries_on_ball (analytic_jet hf m).differentiableOn hz)
  convert hs using 1
  funext n
  simp only [sub_zero, smul_eq_mul, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem flat_eventually_nonneg_jets_zero {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hflat : ∀ m : ℕ, Tendsto (fun x : ℝ => iteratedDeriv m f (x:ℂ))
      (𝓝[<] R) (𝓝 0))
    (N : ℕ) (hpos : ∀ n, N ≤ n → 0 ≤ (iteratedDeriv n f 0).re) :
    (f 0).re = 0 := by
  have hr (m : ℕ) : Tendsto (fun x : ℝ => (iteratedDeriv m f (x:ℂ)).re)
      (𝓝[<] R) (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp (hflat m)
  have htail : ∀ m, N ≤ m → (iteratedDeriv m f 0).re = 0 := by
    intro m hm
    apply le_antisymm _ (hpos m hm)
    apply ge_of_tendsto (hr m)
    filter_upwards [Ioo_mem_nhdsLT hR] with x hx
    have hs := hasSum_real_jet hf m (abs_of_pos hx.1 ▸ hx.2)
    have hl := hs.summable.le_tsum 0 (fun n _ =>
      mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (pow_nonneg hx.1.le _)) (hpos (n+m) (by omega)))
    simpa only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul,
      Nat.zero_add, hs.tsum_eq] using hl
  have hdescend : ∀ K : ℕ, (∀ m, K ≤ m → (iteratedDeriv m f 0).re = 0) →
      (f 0).re = 0 := by
    intro K
    induction K with
    | zero => intro h; simpa using h 0 le_rfl
    | succ K ih =>
      intro h
      have hK : (iteratedDeriv K f 0).re = 0 := by
        have hconst : ∀ x : ℝ, x ∈ Ioo 0 R →
            (iteratedDeriv K f (x:ℂ)).re = (iteratedDeriv K f 0).re := by
          intro x hx
          have hs := hasSum_real_jet hf K (abs_of_pos hx.1 ▸ hx.2)
          rw [← hs.tsum_eq, tsum_eq_single 0]
          · simp
          · intro n hn
            rw [h (n+K) (by omega), mul_zero]
        have he : (fun x : ℝ => (iteratedDeriv K f (x:ℂ)).re)
            =ᶠ[𝓝[<] R] fun _ => (iteratedDeriv K f 0).re := by
          filter_upwards [Ioo_mem_nhdsLT hR] with x hx
          exact hconst x hx
        exact tendsto_nhds_unique (tendsto_const_nhds.congr' he.symm)
          (hr K)
      apply ih
      intro m hm
      rcases eq_or_lt_of_le hm with he | he
      · simpa only [← he] using hK
      · exact h m (by omega)
  exact hdescend N htail

private theorem flat_jets_both_signs {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hflat : ∀ m : ℕ, Tendsto (fun x : ℝ => iteratedDeriv m f (x:ℂ))
      (𝓝[<] R) (𝓝 0)) (h0 : (f 0).re ≠ 0) (N : ℕ) :
    (∃ n, N ≤ n ∧ (iteratedDeriv n f 0).re < 0) ∧
      (∃ n, N ≤ n ∧ 0 < (iteratedDeriv n f 0).re) := by
  constructor
  · by_contra h
    push Not at h
    exact h0 (flat_eventually_nonneg_jets_zero hR hf hflat N h)
  · by_contra h
    push Not at h
    have hnflat (m : ℕ) : Tendsto (fun x : ℝ => iteratedDeriv m (-f) (x:ℂ))
        (𝓝[<] R) (𝓝 0) := by
      simpa only [iteratedDeriv_neg, neg_zero] using (hflat m).neg
    have hz := flat_eventually_nonneg_jets_zero hR hf.neg hnflat N (fun n hn => by
      simpa only [iteratedDeriv_neg, Complex.neg_re, neg_nonneg] using h n hn)
    exact h0 (by simpa using hz)

/-- Imaginary rotation of the complete source's central reflection product. -/
def thetaCuspImaginaryCenterSquare (z : ℂ) : ℂ :=
  thetaCuspStripSource (Complex.I*z) * thetaCuspStripSource (Complex.I*z)

private theorem square_real_jet (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun z => thetaCuspStripSource z * thetaCuspStripSource z) (x:ℂ) =
      ((iteratedDeriv n (fun t : ℝ => thetaCuspFullSource t * thetaCuspFullSource t) x : ℝ) : ℂ) := by
  have ha := analyticOnNhd_thetaCuspStripSource.mul analyticOnNhd_thetaCuspStripSource
  have hmem (y : ℝ) : (y:ℂ) ∈ thetaCuspStrip := by
    simp [thetaCuspStrip, Real.pi_pos]
  induction n generalizing x with
  | zero => simp [thetaCuspStripSource_ofReal]
  | succ n ih =>
    have hc := ((analytic_jet ha n) _ (hmem x)).differentiableAt.hasDerivAt.comp_ofReal
    have hr : ContDiff ℝ (n+1) (fun t => thetaCuspFullSource t * thetaCuspFullSource t) :=
      (contDiff_thetaCuspFullSource.mul contDiff_thetaCuspFullSource).of_le
        (WithTop.coe_le_coe.mpr (show (n+1:ℕ∞) ≤ ⊤ from le_top))
    have hd := ((hr.differentiable_iteratedDeriv' n) x).hasDerivAt.ofReal_comp
    have hc' : HasDerivAt
        (fun y : ℝ => ((iteratedDeriv n
          (fun t : ℝ => thetaCuspFullSource t * thetaCuspFullSource t) y : ℝ) : ℂ))
        (deriv (iteratedDeriv n
          (fun z => thetaCuspStripSource z * thetaCuspStripSource z)) (x:ℂ)) x := by
      simpa only [ih] using hc
    simpa only [iteratedDeriv_succ] using hc'.unique hd

private theorem square_real_jet_zero (n : ℕ) :
    iteratedDeriv n (fun z => thetaCuspStripSource z * thetaCuspStripSource z) 0 =
      (thetaCuspNativeReflectionJet n 0 : ℂ) := by
  have heq : (fun t => thetaCuspFullSource (0+t) * thetaCuspFullSource (0-t)) =
      fun t => thetaCuspFullSource t * thetaCuspFullSource t := by
    funext t
    simp only [zero_add, zero_sub, thetaCuspFullSource_neg]
  simpa only [Complex.ofReal_zero, thetaCuspNativeReflectionJet, heq] using square_real_jet n 0

/-- The rotated square's even jets are precisely the signed native center jets. -/
theorem thetaCuspImaginaryCenterSquare_even_jet (k : ℕ) :
    iteratedDeriv (2*k) thetaCuspImaginaryCenterSquare 0 =
      (((-1:ℝ)^k * thetaCuspNativeReflectionJet (2*k) 0 : ℝ) : ℂ) := by
  change iteratedDeriv (2*k)
    (fun y => (fun z => thetaCuspStripSource z * thetaCuspStripSource z) (Complex.I*y)) 0 = _
  rw [iteratedDeriv_comp_const_mul_of_ne
    (fun z => thetaCuspStripSource z * thetaCuspStripSource z) (2*k) Complex.I_ne_zero 0, mul_zero,
    square_real_jet_zero, pow_mul, Complex.I_sq]
  push_cast
  rfl

private theorem imaginary_square_odd_jet {n : ℕ} (hn : Odd n) :
    iteratedDeriv n thetaCuspImaginaryCenterSquare 0 = 0 := by
  change iteratedDeriv n
    (fun y => (fun z => thetaCuspStripSource z * thetaCuspStripSource z) (Complex.I*y)) 0 = _
  rw [iteratedDeriv_comp_const_mul_of_ne
    (fun z => thetaCuspStripSource z * thetaCuspStripSource z) n Complex.I_ne_zero 0, mul_zero,
    square_real_jet_zero, thetaCuspNativeReflectionJet_odd 0 hn, Complex.ofReal_zero, mul_zero]

private theorem analytic_imaginary_square :
    AnalyticOnNhd ℂ thetaCuspImaginaryCenterSquare (Metric.ball 0 ThetaImaginaryArc.arcEnd) := by
  intro z hz
  have hs : Complex.I*z ∈ thetaCuspStrip := by
    have hn : ‖z‖ < Real.pi/4 := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, ThetaImaginaryArc.arcEnd] using hz
    change |(Complex.I*z).im| < Real.pi/4
    simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
      using (Complex.abs_re_le_norm z).trans_lt hn
  have ha := (analyticOnNhd_thetaCuspStripSource _ hs).comp
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.I*z) z)
  exact ha.mul ha

/-- Every rotated-square jet has zero limit at the same actual odd cusp. -/
theorem tendsto_thetaCuspImaginaryCenterSquare_jet_zero (m : ℕ) :
    Tendsto (fun x : ℝ => iteratedDeriv m thetaCuspImaginaryCenterSquare (x:ℂ))
      (𝓝[<] ThetaImaginaryArc.arcEnd) (𝓝 0) := by
  have heq (z : ℂ) : iteratedDeriv m thetaCuspImaginaryCenterSquare z =
      Complex.I^m * iteratedDeriv m
        (fun w => thetaCuspStripSource w * thetaCuspStripSource w) (Complex.I*z) :=
    iteratedDeriv_comp_const_mul_of_ne
      (fun w => thetaCuspStripSource w * thetaCuspStripSource w) m Complex.I_ne_zero z
  simp_rw [heq, mul_comm Complex.I]
  simpa only [mul_zero] using
    (ThetaImaginaryArc.tendsto_sourceSquare_iteratedDeriv_axis_zero m).const_mul (Complex.I^m)

/-- The actual signed native center jets have both signs above every order. -/
theorem thetaCuspNativeCenterJet_sign_oscillation (N : ℕ) :
    (∃ k, N ≤ k ∧ (-1:ℝ)^k * thetaCuspNativeReflectionJet (2*k) 0 < 0) ∧
      (∃ k, N ≤ k ∧ 0 < (-1:ℝ)^k * thetaCuspNativeReflectionJet (2*k) 0) := by
  have h0 : (thetaCuspImaginaryCenterSquare 0).re ≠ 0 := by
    have hp := HedenmalmThetaSource.thetaCuspFullSource_pos 0
    simp only [thetaCuspImaginaryCenterSquare, mul_zero]
    rw [← Complex.ofReal_zero, thetaCuspStripSource_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    exact (mul_pos hp hp).ne'
  obtain ⟨⟨n,hn,hneg⟩,⟨m,hm,hpos⟩⟩ := flat_jets_both_signs
    ThetaImaginaryArc.arcEnd_pos analytic_imaginary_square
    tendsto_thetaCuspImaginaryCenterSquare_jet_zero h0 (2*N)
  constructor
  · rcases Nat.even_or_odd n with ⟨k,hk⟩ | ho
    · have hn' : n = 2*k := by omega
      refine ⟨k, by omega, ?_⟩
      simpa only [hn', thetaCuspImaginaryCenterSquare_even_jet, Complex.ofReal_re] using hneg
    · rw [imaginary_square_odd_jet ho, Complex.zero_re] at hneg
      exact (lt_irrefl 0 hneg).elim
  · rcases Nat.even_or_odd m with ⟨k,hk⟩ | ho
    · have hm' : m = 2*k := by omega
      refine ⟨k, by omega, ?_⟩
      simpa only [hm', thetaCuspImaginaryCenterSquare_even_jet, Complex.ofReal_re] using hpos
    · rw [imaginary_square_odd_jet ho, Complex.zero_re] at hpos
      exact (lt_irrefl 0 hpos).elim

/-- Arbitrarily high native diagonal orders are negative on genuine positive-center intervals. -/
theorem thetaCuspNative_negative_diagonals_unbounded (N : ℕ) :
    ∃ k, N ≤ k ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < x → x < δ →
      (-1:ℝ)^k * thetaCuspNativeReflectionJet (2*k) x < 0 := by
  obtain ⟨k,hk,hneg⟩ := (thetaCuspNativeCenterJet_sign_oscillation N).1
  have hc : Continuous (fun x => (-1:ℝ)^k * thetaCuspNativeReflectionJet (2*k) x) :=
    continuous_const.mul (continuous_thetaCuspNativeReflectionJet (2*k))
  have he := hc.continuousAt.tendsto.eventually_lt_const hneg
  obtain ⟨δ,hδ,hδneg⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨k,hk,δ,hδ,fun x hx hxδ => hδneg ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hx] using hxδ

end RHTower
