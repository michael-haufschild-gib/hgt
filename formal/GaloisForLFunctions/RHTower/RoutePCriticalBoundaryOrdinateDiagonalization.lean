import GaloisForLFunctions.RHTower.RoutePFiniteSigmaCubicEulerTangentGram
import GaloisForLFunctions.RHTower.DeningerInvZetaPole
import GaloisForLFunctions.RHTower.GammaShiftZetaReadout

/-!
# Route P: critical-boundary ordinate diagonalization

Horizontal projective damping and vertical ordinate phase are the real and imaginary parts of one
moving full-Hardy node.  Scaling the imaginary node coordinate by the reciprocal critical clock
keeps its Euler phase fixed while leaving its Hilbert norm unchanged.  The zeta pole then acts as
an intrinsic ordinate projector: equal-ordinate source overlaps retain the Hardy residue, whereas
unequal-ordinate overlaps land at a regular boundary point and vanish after source normalization.
-/

open Complex Filter Set
open scoped BigOperators Topology ComplexOrder

namespace RHTower

noncomputable section

/-- Projective Hardy node carrying a fixed physical ordinate phase at finite `sigma`. -/
def routePProjectiveOrdinateNode
    (sigma R a gamma : ℝ) : ℂ :=
  routePProjectiveHardyNode R a +
    ((gamma / (sigma - 1) : ℝ) : ℂ) * I

@[simp] theorem routePProjectiveOrdinateNode_re
    (sigma R a gamma : ℝ) :
    (routePProjectiveOrdinateNode sigma R a gamma).re = R * a - 1 / 2 := by
  simp only [routePProjectiveOrdinateNode, add_re, mul_re,
    routePProjectiveHardyNode_re, Complex.ofReal_re, Complex.ofReal_im,
    I_re, I_im]
  ring

theorem neg_half_lt_routePProjectiveOrdinateNode_re
    {sigma R a gamma : ℝ} (hR : 0 < R) (ha : 0 < a) :
    -1 / 2 < (routePProjectiveOrdinateNode sigma R a gamma).re := by
  rw [routePProjectiveOrdinateNode_re]
  nlinarith [mul_pos hR ha]

/-- Exact complex Dirichlet exponent seen by two moving ordinate columns. -/
def routePProjectiveOrdinatePairParameter
    (sigma R a gamma b delta : ℝ) : ℂ :=
  ((1 + R * (a + b) * (sigma - 1) : ℝ) : ℂ) +
    ((delta - gamma : ℝ) : ℂ) * I

@[simp] theorem routePProjectiveOrdinatePairParameter_re
    (sigma R a gamma b delta : ℝ) :
    (routePProjectiveOrdinatePairParameter
      sigma R a gamma b delta).re =
      routePProjectiveFullEulerPairExponent sigma R a b := by
  simp [routePProjectiveOrdinatePairParameter,
    routePProjectiveFullEulerPairExponent]

/-- Reciprocal-clock imaginary blow-up cancels exactly inside the Euler boundary parameter. -/
theorem eulerPositiveComplexBoundaryParameter_ordinatePair
    {sigma R a gamma b delta : ℝ} (hsigma : 1 < sigma) :
    eulerPositiveComplexBoundaryParameter sigma
        (routePProjectiveOrdinateNode sigma R b delta +
          (starRingEnd ℂ) (routePProjectiveOrdinateNode sigma R a gamma)) =
      routePProjectiveOrdinatePairParameter sigma R a gamma b delta := by
  have hsigmaOne : sigma - 1 ≠ 0 := sub_ne_zero.mpr hsigma.ne'
  have hsigmaOneC : (sigma : ℂ) - 1 ≠ 0 := by
    exact_mod_cast hsigmaOne
  unfold eulerPositiveComplexBoundaryParameter
    routePProjectiveOrdinateNode routePProjectiveHardyNode
    routePProjectiveOrdinatePairParameter
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  field_simp [hsigmaOne, hsigmaOneC]
  ring

/-- Exact finite-sigma Hermitian overlap of the genuine moving-ordinate Euler columns. -/
theorem inner_eulerPositiveComplexHardy_ordinate_eq_zetaRatio
    {sigma R a gamma b delta : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    inner ℂ
        (eulerPositiveCriticalComplexHardyStateLp sigma
          (routePProjectiveOrdinateNode sigma R a gamma) hsigma
          (neg_half_lt_routePProjectiveOrdinateNode_re hR ha))
        (eulerPositiveCriticalComplexHardyStateLp sigma
          (routePProjectiveOrdinateNode sigma R b delta) hsigma
          (neg_half_lt_routePProjectiveOrdinateNode_re hR hb)) =
      riemannZeta
          (routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta) /
        riemannZeta (sigma : ℂ) := by
  rw [inner_eulerPositiveComplexHardy_complexHardy_eq_affineOverlap]
  change
    riemannZeta
          (eulerPositiveComplexBoundaryParameter sigma
            (routePProjectiveOrdinateNode sigma R b delta +
              (starRingEnd ℂ)
                (routePProjectiveOrdinateNode sigma R a gamma))) /
        riemannZeta (sigma : ℂ) = _
  rw [eulerPositiveComplexBoundaryParameter_ordinatePair hsigma]

/-- Projectively rescaled overlap of two moving-ordinate full-Euler columns. -/
def routePProjectiveOrdinateZetaOverlap
    (R a gamma b delta sigma : ℝ) : ℂ :=
  (R : ℂ) *
    (riemannZeta
        (routePProjectiveOrdinatePairParameter sigma R a gamma b delta) /
      riemannZeta (sigma : ℂ))

/-- The ordinate overlap is exactly a scaled Hilbert inner product before any boundary limit. -/
theorem routePProjectiveOrdinateZetaOverlap_eq_scaled_inner
    {sigma R a gamma b delta : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    routePProjectiveOrdinateZetaOverlap R a gamma b delta sigma =
      (R : ℂ) *
        inner ℂ
          (eulerPositiveCriticalComplexHardyStateLp sigma
            (routePProjectiveOrdinateNode sigma R a gamma) hsigma
            (neg_half_lt_routePProjectiveOrdinateNode_re hR ha))
          (eulerPositiveCriticalComplexHardyStateLp sigma
            (routePProjectiveOrdinateNode sigma R b delta) hsigma
            (neg_half_lt_routePProjectiveOrdinateNode_re hR hb)) := by
  rw [inner_eulerPositiveComplexHardy_ordinate_eq_zetaRatio hsigma hR ha hb]
  rfl

theorem routePProjectiveOrdinateZetaOverlap_diagonal
    (R a b gamma sigma : ℝ) :
    routePProjectiveOrdinateZetaOverlap R a gamma b gamma sigma =
      routePProjectiveFullEulerZetaOverlap R a b sigma := by
  simp [routePProjectiveOrdinateZetaOverlap,
    routePProjectiveOrdinatePairParameter,
    routePProjectiveFullEulerZetaOverlap]

private theorem tendsto_routePRealParameter_nhdsNE_one :
    Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using!
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h
    have : sigma = 1 := by exact_mod_cast h
    exact hsigma.ne' this

/-- Equal ordinates retain the same Hardy residue as the horizontal P-G169 overlap. -/
theorem tendsto_routePProjectiveOrdinateZetaOverlap_diagonal
    {R a b gamma : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (routePProjectiveOrdinateZetaOverlap R a gamma b gamma)
      (nhdsWithin 1 (Ioi 1))
      (nhds (((1 / (a + b) : ℝ) : ℂ))) := by
  have hfun :
      routePProjectiveOrdinateZetaOverlap R a gamma b gamma =
        routePProjectiveFullEulerZetaOverlap R a b := by
    funext sigma
    exact routePProjectiveOrdinateZetaOverlap_diagonal R a b gamma sigma
  rw [hfun]
  exact tendsto_routePProjectiveFullEulerZetaOverlap hR ha hb

/-- Unequal ordinates land away from the zeta pole, so source normalization annihilates their
overlap without any external Cesaro or Bohr projector. -/
theorem tendsto_routePProjectiveOrdinateZetaOverlap_offDiagonal
    {R a gamma b delta : ℝ} (hgammaDelta : gamma ≠ delta) :
    Tendsto
      (routePProjectiveOrdinateZetaOverlap R a gamma b delta)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  let p : ℂ := (1 : ℂ) + ((delta - gamma : ℝ) : ℂ) * I
  have hpole : p ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [p] at him
    apply hgammaDelta
    linarith
  have hparam : Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinatePairParameter
          sigma R a gamma b delta)
      (nhdsWithin 1 (Ioi 1)) (nhds p) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ =>
          routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta) 1 := by
      unfold routePProjectiveOrdinatePairParameter
      fun_prop
    simpa [p, routePProjectiveOrdinatePairParameter] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hnumerator : Tendsto
      (fun sigma : ℝ =>
        riemannZeta
          (routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta))
      (nhdsWithin 1 (Ioi 1)) (nhds (riemannZeta p)) :=
    (differentiableAt_riemannZeta hpole).continuousAt.tendsto.comp hparam
  have hdenominator : Tendsto
      (fun sigma : ℝ => (riemannZeta (sigma : ℂ))⁻¹)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
    deningerInvZeta_tendsto_zero.comp
      tendsto_routePRealParameter_nhdsNE_one
  have hproduct := (hnumerator.mul hdenominator).const_mul (R : ℂ)
  have hfun :
      routePProjectiveOrdinateZetaOverlap R a gamma b delta =
        fun sigma : ℝ =>
          (R : ℂ) *
            (riemannZeta
                (routePProjectiveOrdinatePairParameter
                  sigma R a gamma b delta) *
              (riemannZeta (sigma : ℂ))⁻¹) := by
    funext sigma
    simp [routePProjectiveOrdinateZetaOverlap, div_eq_mul_inv]
  rw [hfun]
  simpa using hproduct

/-- **Source-native ordinate projector.** The critical full-Euler Gram converges to the Hardy
kernel on equal-ordinate fibres and to zero on every unequal-ordinate fibre. -/
theorem tendsto_routePProjectiveOrdinateZetaOverlap
    {R a gamma b delta : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (routePProjectiveOrdinateZetaOverlap R a gamma b delta)
      (nhdsWithin 1 (Ioi 1))
      (nhds (if gamma = delta then
        (((1 / (a + b) : ℝ) : ℂ)) else 0)) := by
  by_cases hgammaDelta : gamma = delta
  · subst delta
    simpa using
      tendsto_routePProjectiveOrdinateZetaOverlap_diagonal
        (gamma := gamma) hR ha hb
  · simpa [hgammaDelta] using
      tendsto_routePProjectiveOrdinateZetaOverlap_offDiagonal
        (R := R) (a := a) (b := b) hgammaDelta

/-! ## Log-weighted ordinate source -/

/-- The positive-PNat second logarithmic Dirichlet series is the second zeta jet. -/
theorem tsum_pnat_log_sq_div_cpow_eq_iteratedDeriv_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ+,
      (Real.log (n : ℕ) : ℂ) ^ (2 : ℕ) / ((n : ℕ) : ℂ) ^ s) =
      iteratedDeriv 2 riemannZeta s := by
  let f : ℕ → ℂ := fun n =>
    (Real.log n : ℂ) ^ (2 : ℕ) / (n : ℂ) ^ s
  have hterm : ∀ n : ℕ,
      LSeries.term (⇑(GaloisForLFunctions.zetaJetA 2)) s n = f n := by
    intro n
    rcases n with _ | n
    · simp [LSeries.term, f]
    rcases n with _ | n
    · simp [LSeries.term, f, GaloisForLFunctions.zetaJetA_apply]
    · have hn : 2 ≤ n + 2 := by omega
      simp only [LSeries.term, Nat.succ_ne_zero, if_false,
        GaloisForLFunctions.zetaJetA_apply, hn, if_true, f]
  have hsum : Summable f :=
    (GaloisForLFunctions.zetaJetA_LSeriesSummable 2 hs).congr hterm
  have hshift : (∑' n : ℕ, f (n + 1)) = ∑' n : ℕ, f n := by
    have h := hsum.sum_add_tsum_nat_add 1
    simpa [f] using h
  calc
    (∑' n : ℕ+,
        (Real.log (n : ℕ) : ℂ) ^ (2 : ℕ) / ((n : ℕ) : ℂ) ^ s) =
        ∑' n : ℕ, f (n + 1) := by
          simpa only [f] using
            (tsum_pnat_eq_tsum_succ (f := f))
    _ = ∑' n : ℕ, f n := hshift
    _ = LSeries (⇑(GaloisForLFunctions.zetaJetA 2)) s := by
      unfold LSeries
      exact tsum_congr fun n => (hterm n).symm
    _ = iteratedDeriv 2 riemannZeta s := by
      have h := GaloisForLFunctions.iteratedDeriv_riemannZeta_eq_signed_LSeries
        2 (by omega) hs
      norm_num at h
      exact h.symm

/-- Product of two moving-ordinate columns is the exact complex Dirichlet atom at their pair
parameter, divided by the original Euler partition function. -/
theorem routePProjectiveOrdinatePairWeight_eq_cpow
    (sigma R a gamma b delta : ℝ) (hsigma : 1 < sigma) (n : ℕ+) :
    eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveOrdinateNode sigma R b delta) n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalComplexDampedStateWeight sigma
            (routePProjectiveOrdinateNode sigma R a gamma) n) =
      (1 / ((n : ℕ) : ℂ) ^
          (routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta)) /
        (eulerPositiveTotal sigma : ℂ) := by
  rw [complexDamped_pair_apply,
    eulerPositiveCriticalComplexDampedStateWeight_eq_exp]
  have hnorm : eulerPositiveStateWeight sigma n *
      (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
      (eulerPositiveProbability sigma n : ℂ) := by
    calc
      _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ (2 : ℕ)) :=
        RCLike.mul_conj (eulerPositiveStateWeight sigma n)
      _ = _ := by
        rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
  rw [show
      Complex.exp
            (-(routePProjectiveOrdinateNode sigma R b delta +
                (starRingEnd ℂ)
                  (routePProjectiveOrdinateNode sigma R a gamma)) *
              ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        Complex.exp
            (-(routePProjectiveOrdinateNode sigma R b delta +
                (starRingEnd ℂ)
                  (routePProjectiveOrdinateNode sigma R a gamma)) *
              ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) by ring,
    hnorm, eulerPositiveProbability, Complex.ofReal_div]
  rw [← mul_div_assoc, complexDamping_mul_eulerPositiveMass,
    eulerPositiveComplexBoundaryParameter_ordinatePair hsigma]

/-- Log-weighted moving-ordinate Euler column. -/
def routePProjectiveOrdinateLogStateWeight
    (sigma R a gamma : ℝ) (n : ℕ+) : ℂ :=
  (Real.log (n : ℕ) : ℂ) *
    eulerPositiveCriticalComplexDampedStateWeight sigma
      (routePProjectiveOrdinateNode sigma R a gamma) n

private theorem summable_norm_sq_routePProjectiveOrdinateLogStateWeight
    {sigma R a gamma : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) :
    Summable (fun n : ℕ+ =>
      ‖routePProjectiveOrdinateLogStateWeight sigma R a gamma n‖ ^ (2 : ℕ)) := by
  have h := HilbertSchmidt.summable_coe_sq
    (routePProjectiveFullEulerLogStateLp sigma R a hsigma hR ha)
  exact h.congr fun n => by
    change
      ‖routePProjectiveFullEulerLogStateWeight sigma R a n‖ ^ (2 : ℕ) =
        ‖routePProjectiveOrdinateLogStateWeight sigma R a gamma n‖ ^ (2 : ℕ)
    rw [routePProjectiveOrdinateLogStateWeight,
      routePProjectiveFullEulerLogStateWeight, norm_mul, norm_mul,
      norm_eulerPositiveCriticalComplexDampedStateWeight,
      norm_eulerPositiveCriticalComplexDampedStateWeight,
      routePProjectiveOrdinateNode_re, routePProjectiveHardyNode_re]

/-- Genuine square-summable log-weighted column with fixed physical ordinate phase. -/
def routePProjectiveOrdinateLogStateLp
    (sigma R a gamma : ℝ) (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) : EulerPositiveL2 :=
  ⟨routePProjectiveOrdinateLogStateWeight sigma R a gamma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_routePProjectiveOrdinateLogStateWeight
        hsigma hR ha)⟩

/-- Exact second-zeta-jet Gram of two genuine moving-ordinate log columns. -/
theorem inner_routePProjectiveOrdinateLogStateLp_eq_iteratedDeriv
    {sigma R a gamma b delta : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    inner ℂ
        (routePProjectiveOrdinateLogStateLp
          sigma R a gamma hsigma hR ha)
        (routePProjectiveOrdinateLogStateLp
          sigma R b delta hsigma hR hb) =
      iteratedDeriv 2 riemannZeta
          (routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta) /
        riemannZeta (sigma : ℂ) := by
  let s := routePProjectiveOrdinatePairParameter
    sigma R a gamma b delta
  have hs : 1 < s.re := by
    rw [routePProjectiveOrdinatePairParameter_re]
    exact one_lt_routePProjectiveFullEulerPairExponent hsigma hR ha hb
  rw [lp.inner_eq_tsum]
  simp only [routePProjectiveOrdinateLogStateLp, RCLike.inner_apply]
  rw [show
      (∑' n : ℕ+,
        routePProjectiveOrdinateLogStateWeight sigma R b delta n *
          (starRingEnd ℂ)
            (routePProjectiveOrdinateLogStateWeight
              sigma R a gamma n)) =
      ∑' n : ℕ+,
        ((Real.log (n : ℕ) : ℂ) ^ (2 : ℕ) /
          ((n : ℕ) : ℂ) ^ s) /
            (eulerPositiveTotal sigma : ℂ) by
    apply tsum_congr
    intro n
    rw [routePProjectiveOrdinateLogStateWeight,
      routePProjectiveOrdinateLogStateWeight, map_mul,
      Complex.conj_ofReal]
    rw [show
        (Real.log (n : ℕ) : ℂ) *
              eulerPositiveCriticalComplexDampedStateWeight sigma
                (routePProjectiveOrdinateNode sigma R b delta) n *
            ((Real.log (n : ℕ) : ℂ) *
              (starRingEnd ℂ)
                (eulerPositiveCriticalComplexDampedStateWeight sigma
                  (routePProjectiveOrdinateNode sigma R a gamma) n)) =
          (Real.log (n : ℕ) : ℂ) ^ (2 : ℕ) *
            (eulerPositiveCriticalComplexDampedStateWeight sigma
                (routePProjectiveOrdinateNode sigma R b delta) n *
              (starRingEnd ℂ)
                (eulerPositiveCriticalComplexDampedStateWeight sigma
                  (routePProjectiveOrdinateNode sigma R a gamma) n)) by ring,
      routePProjectiveOrdinatePairWeight_eq_cpow
        sigma R a gamma b delta hsigma n]
    dsimp only [s]
    ring]
  rw [tsum_div_const,
    tsum_pnat_log_sq_div_cpow_eq_iteratedDeriv_riemannZeta hs,
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]

private theorem one_div_pnat_cpow_eq_ofReal_eulerPositiveMass
    (tau : ℝ) (n : ℕ+) :
    1 / ((n : ℕ) : ℂ) ^ (tau : ℂ) =
      (eulerPositiveMass tau n : ℂ) := by
  rw [eulerPositiveMass, Complex.ofReal_cpow (by positivity)]
  rw [show ((-tau : ℝ) : ℂ) = -(tau : ℂ) by norm_cast,
    Complex.cpow_neg]
  rw [one_div]
  congr 1

/-- On the real Euler half-plane the second zeta jet is exactly total mass times normalized
second logarithmic moment. -/
theorem iteratedDeriv_two_riemannZeta_ofReal_eq_total_mul_logMoment
    {tau : ℝ} (htau : 1 < tau) :
    iteratedDeriv 2 riemannZeta (tau : ℂ) =
      ((eulerPositiveTotal tau * eulerPositiveLogMoment 2 tau : ℝ) : ℂ) := by
  rw [← tsum_pnat_log_sq_div_cpow_eq_iteratedDeriv_riemannZeta
    (by simpa using htau)]
  rw [Complex.ofReal_mul, eulerPositiveLogMoment, Complex.ofReal_tsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [eulerPositiveProbability, div_eq_mul_inv, ← one_div,
    one_div_pnat_cpow_eq_ofReal_eulerPositiveMass tau n]
  push_cast
  have htotal : (eulerPositiveTotal tau : ℂ) ≠ 0 := by
    exact_mod_cast (eulerPositiveTotal_pos htau).ne'
  field_simp [htotal]

/-- One complex second-log-moment Gram term with physical ordinate phases. -/
def routePProjectiveOrdinateLogMomentGramTerm
    (R a gamma b delta sigma : ℝ) : ℂ :=
  ((R * (R * (sigma - 1)) ^ (2 : ℕ) : ℝ) : ℂ) *
    (iteratedDeriv 2 riemannZeta
        (routePProjectiveOrdinatePairParameter
          sigma R a gamma b delta) /
      riemannZeta (sigma : ℂ))

/-- Exact scaled Hilbert inner product behind one complex tangent Gram term. -/
theorem routePProjectiveOrdinateLogMomentGramTerm_eq_scaled_inner
    {sigma R a gamma b delta : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ((((Real.sqrt R * (R * (sigma - 1))) ^ (2 : ℕ) : ℝ) : ℂ) *
      inner ℂ
        (routePProjectiveOrdinateLogStateLp
          sigma R a gamma hsigma hR ha)
        (routePProjectiveOrdinateLogStateLp
          sigma R b delta hsigma hR hb)) =
      routePProjectiveOrdinateLogMomentGramTerm
        R a gamma b delta sigma := by
  rw [inner_routePProjectiveOrdinateLogStateLp_eq_iteratedDeriv
    hsigma hR ha hb]
  rw [routePProjectiveOrdinateLogMomentGramTerm,
    mul_pow, Real.sq_sqrt hR.le]

/-- At equal ordinates the complex second-jet term is exactly P-G170's real log-moment term. -/
theorem routePProjectiveOrdinateLogMomentGramTerm_diagonal
    {sigma R a b gamma : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    routePProjectiveOrdinateLogMomentGramTerm
        R a gamma b gamma sigma =
      routePProjectiveFullEulerLogMomentGramTerm R a b sigma := by
  let tau := routePProjectiveFullEulerPairExponent sigma R a b
  have htau : 1 < tau :=
    one_lt_routePProjectiveFullEulerPairExponent hsigma hR ha hb
  have hjet :=
    iteratedDeriv_two_riemannZeta_ofReal_eq_total_mul_logMoment htau
  rw [routePProjectiveOrdinateLogMomentGramTerm,
    routePProjectiveFullEulerLogMomentGramTerm,
    routePProjectiveFullEulerZetaOverlap]
  have hparam :
      routePProjectiveOrdinatePairParameter
          sigma R a gamma b gamma = (tau : ℂ) := by
    simp [routePProjectiveOrdinatePairParameter, tau,
      routePProjectiveFullEulerPairExponent]
  rw [hparam, hjet]
  have htotal : (eulerPositiveTotal tau : ℂ) =
      riemannZeta (tau : ℂ) :=
    ofReal_eulerPositiveTotal_eq_riemannZeta htau
  change
    ((R * (R * (sigma - 1)) ^ (2 : ℕ) : ℝ) : ℂ) *
          (((eulerPositiveTotal tau *
              eulerPositiveLogMoment 2 tau : ℝ) : ℂ) /
            riemannZeta (sigma : ℂ)) =
      (R : ℂ) *
          (riemannZeta (tau : ℂ) / riemannZeta (sigma : ℂ)) *
        (((R * (sigma - 1)) ^ (2 : ℕ) *
          eulerPositiveLogMoment 2 tau : ℝ) : ℂ)
  rw [← htotal]
  push_cast
  ring

/-- Equal-ordinate complex log-moment terms retain the cubic pole residue. -/
theorem tendsto_routePProjectiveOrdinateLogMomentGramTerm_diagonal
    {R a b gamma : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (routePProjectiveOrdinateLogMomentGramTerm R a gamma b gamma)
      (nhdsWithin 1 (Ioi 1))
      (nhds (((2 / (a + b) ^ (3 : ℕ) : ℝ) : ℂ))) := by
  have hbase :=
    tendsto_routePProjectiveFullEulerLogMomentGramTerm hR ha hb
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  exact (routePProjectiveOrdinateLogMomentGramTerm_diagonal
    hsigma hR ha hb).symm

/-- Away from the ordinate diagonal the regular second zeta jet is annihilated by critical source
normalization. -/
theorem tendsto_routePProjectiveOrdinateLogMomentGramTerm_offDiagonal
    {R a gamma b delta : ℝ} (hgammaDelta : gamma ≠ delta) :
    Tendsto
      (routePProjectiveOrdinateLogMomentGramTerm R a gamma b delta)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  let p : ℂ := (1 : ℂ) + ((delta - gamma : ℝ) : ℂ) * I
  have hpole : p ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [p] at him
    apply hgammaDelta
    linarith
  have hparam : Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinatePairParameter
          sigma R a gamma b delta)
      (nhdsWithin 1 (Ioi 1)) (nhds p) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ =>
          routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta) 1 := by
      unfold routePProjectiveOrdinatePairParameter
      fun_prop
    simpa [p, routePProjectiveOrdinatePairParameter] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hjet : Tendsto
      (fun sigma : ℝ =>
        iteratedDeriv 2 riemannZeta
          (routePProjectiveOrdinatePairParameter
            sigma R a gamma b delta))
      (nhdsWithin 1 (Ioi 1))
      (nhds (iteratedDeriv 2 riemannZeta p)) :=
    (GaloisForLFunctions.analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_riemannZeta_of_ne_one hpole) 2).continuousAt.tendsto.comp hparam
  have hinv : Tendsto
      (fun sigma : ℝ => (riemannZeta (sigma : ℂ))⁻¹)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
    deningerInvZeta_tendsto_zero.comp
      tendsto_routePRealParameter_nhdsNE_one
  have hscale : Tendsto
      (fun sigma : ℝ =>
        ((R * (R * (sigma - 1)) ^ (2 : ℕ) : ℝ) : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hcont : ContinuousAt
        (fun sigma : ℝ =>
          ((R * (R * (sigma - 1)) ^ (2 : ℕ) : ℝ) : ℂ)) 1 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hproduct := hscale.mul (hjet.mul hinv)
  have hfun :
      routePProjectiveOrdinateLogMomentGramTerm R a gamma b delta =
        fun sigma : ℝ =>
          ((R * (R * (sigma - 1)) ^ (2 : ℕ) : ℝ) : ℂ) *
            (iteratedDeriv 2 riemannZeta
                (routePProjectiveOrdinatePairParameter
                  sigma R a gamma b delta) *
              (riemannZeta (sigma : ℂ))⁻¹) := by
    funext sigma
    simp [routePProjectiveOrdinateLogMomentGramTerm, div_eq_mul_inv]
  rw [hfun]
  simpa using hproduct

/-! ## Actual Hellinger tangents with ordinate phase -/

/-- Coordinate derivative of a moving-ordinate projective Euler column. The reciprocal-clock
ordinate phase is independent of depth, so horizontal differentiation inserts the same literal
Euler logarithm as in P-G170. -/
theorem hasDerivAt_routePProjectiveOrdinateStateWeight
    (sigma R gamma x : ℝ) (n : ℕ+) :
    HasDerivAt
      (fun a : ℝ =>
        eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveOrdinateNode sigma R a gamma) n)
      (-((R * (sigma - 1) * Real.log (n : ℕ) : ℝ) : ℂ) *
        eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveOrdinateNode sigma R x gamma) n)
      x := by
  have hnodeReal : HasDerivAt
      (fun a : ℝ => R * a - 1 / 2) R x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul R).sub_const (1 / 2)
  have hnodeBase : HasDerivAt
      (fun a : ℝ => routePProjectiveHardyNode R a) (R : ℂ) x := by
    simpa only [routePProjectiveHardyNode] using hnodeReal.ofReal_comp
  have hnode : HasDerivAt
      (fun a : ℝ => routePProjectiveOrdinateNode sigma R a gamma)
      (R : ℂ) x := by
    simpa only [routePProjectiveOrdinateNode] using
      hnodeBase.add_const (((gamma / (sigma - 1) : ℝ) : ℂ) * I)
  have harg := ((hnode.neg.mul_const (((sigma - 1 : ℝ) : ℂ))).mul_const
    ((Real.log (n : ℕ) : ℝ) : ℂ))
  have hexp := harg.cexp.mul_const (eulerPositiveStateWeight sigma n)
  have hder :
      Complex.exp
            (-routePProjectiveOrdinateNode sigma R x gamma *
              (((sigma - 1 : ℝ) : ℂ)) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (-((R : ℂ)) * (((sigma - 1 : ℝ) : ℂ)) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n =
        -((R * (sigma - 1) * Real.log (n : ℕ) : ℝ) : ℂ) *
          (Complex.exp
              (-routePProjectiveOrdinateNode sigma R x gamma *
                (((sigma - 1 : ℝ) : ℂ)) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            eulerPositiveStateWeight sigma n) := by
    push_cast
    ring
  simpa only [eulerPositiveCriticalComplexDampedStateWeight_eq_exp,
    Pi.neg_apply] using hexp.congr_deriv hder

/-- Half-weighted two-scale projective packet with fixed physical ordinate phase. -/
def routePProjectiveOrdinateHalfWeightedStateWeight
    (sigma R a gamma : ℝ) (n : ℕ+) : ℂ :=
  (Real.sqrt R : ℂ) *
    (eulerPositiveCriticalComplexDampedStateWeight sigma
        (routePProjectiveOrdinateNode sigma R a gamma) n -
      (1 / 2 : ℂ) *
        eulerPositiveCriticalComplexDampedStateWeight sigma
          (routePProjectiveOrdinateNode sigma R (2 * a) gamma) n)

/-- Direct coordinate formula for the moving-ordinate Hellinger source tangent. -/
def routePProjectiveOrdinateHellingerTangentWeight
    (sigma R a gamma : ℝ) (n : ℕ+) : ℂ :=
  ((Real.sqrt R * (R * (sigma - 1)) : ℝ) : ℂ) *
    (routePProjectiveOrdinateLogStateWeight sigma R (2 * a) gamma n -
      routePProjectiveOrdinateLogStateWeight sigma R a gamma n)

/-- Doubled-node chain rule still cancels the half weight exactly in the presence of physical
ordinate phase. -/
theorem hasDerivAt_routePProjectiveOrdinateHalfWeightedStateWeight
    (sigma R a gamma : ℝ) (n : ℕ+) :
    HasDerivAt
      (fun x : ℝ =>
        routePProjectiveOrdinateHalfWeightedStateWeight
          sigma R x gamma n)
      (routePProjectiveOrdinateHellingerTangentWeight
        sigma R a gamma n)
      a := by
  have h1 := hasDerivAt_routePProjectiveOrdinateStateWeight
    sigma R gamma a n
  have h2base := hasDerivAt_routePProjectiveOrdinateStateWeight
    sigma R gamma (2 * a) n
  have hdouble : HasDerivAt (fun x : ℝ => 2 * x) 2 a := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id a).const_mul 2
  have h2 := h2base.scomp a hdouble
  have hpacket :=
    (h1.sub (h2.const_mul (1 / 2 : ℂ))).const_mul (Real.sqrt R : ℂ)
  have hpacket' := hpacket.congr_deriv
    (g' := routePProjectiveOrdinateHellingerTangentWeight
      sigma R a gamma n) (by
    unfold routePProjectiveOrdinateHellingerTangentWeight
      routePProjectiveOrdinateLogStateWeight
    simp only [two_smul]
    push_cast
    ring)
  apply hpacket'.congr_of_eventuallyEq
  filter_upwards with x
  simp only [routePProjectiveOrdinateHalfWeightedStateWeight,
    Function.comp_apply, Pi.sub_apply]

/-- Genuine finite-sigma Hellinger tangent with fixed physical ordinate phase. -/
def routePProjectiveOrdinateHellingerTangentLp
    (sigma R a gamma : ℝ) (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) : EulerPositiveL2 :=
  (((Real.sqrt R * (R * (sigma - 1)) : ℝ) : ℂ) •
    (routePProjectiveOrdinateLogStateLp
        sigma R (2 * a) gamma hsigma hR (mul_pos two_pos ha) -
      routePProjectiveOrdinateLogStateLp
        sigma R a gamma hsigma hR ha))

@[simp] theorem routePProjectiveOrdinateHellingerTangentLp_apply
    {sigma R a gamma : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (n : ℕ+) :
    routePProjectiveOrdinateHellingerTangentLp
        sigma R a gamma hsigma hR ha n =
      routePProjectiveOrdinateHellingerTangentWeight
        sigma R a gamma n := by
  rfl

/-- Four-term complex Euler Gram of two moving-ordinate Hellinger tangents. -/
def routePProjectiveOrdinateCubicTangentGram
    (R a gamma b delta sigma : ℝ) : ℂ :=
  routePProjectiveOrdinateLogMomentGramTerm R a gamma b delta sigma -
    routePProjectiveOrdinateLogMomentGramTerm R a gamma (2 * b) delta sigma -
    routePProjectiveOrdinateLogMomentGramTerm R (2 * a) gamma b delta sigma +
    routePProjectiveOrdinateLogMomentGramTerm
      R (2 * a) gamma (2 * b) delta sigma

/-- The complex four-term arithmetic expression is exactly the Hilbert Gram of actual
finite-sigma moving-ordinate tangent vectors. -/
theorem inner_routePProjectiveOrdinateHellingerTangentLp_eq_cubicTangentGram
    {sigma R a gamma b delta : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    inner ℂ
        (routePProjectiveOrdinateHellingerTangentLp
          sigma R a gamma hsigma hR ha)
        (routePProjectiveOrdinateHellingerTangentLp
          sigma R b delta hsigma hR hb) =
      routePProjectiveOrdinateCubicTangentGram
        R a gamma b delta sigma := by
  have h2a : 0 < 2 * a := mul_pos two_pos ha
  have h2b : 0 < 2 * b := mul_pos two_pos hb
  have hab := routePProjectiveOrdinateLogMomentGramTerm_eq_scaled_inner
    (gamma := gamma) (delta := delta) hsigma hR ha hb
  have ha2b := routePProjectiveOrdinateLogMomentGramTerm_eq_scaled_inner
    (gamma := gamma) (delta := delta) hsigma hR ha h2b
  have h2ab := routePProjectiveOrdinateLogMomentGramTerm_eq_scaled_inner
    (gamma := gamma) (delta := delta) hsigma hR h2a hb
  have h2a2b := routePProjectiveOrdinateLogMomentGramTerm_eq_scaled_inner
    (gamma := gamma) (delta := delta) hsigma hR h2a h2b
  rw [routePProjectiveOrdinateHellingerTangentLp,
    routePProjectiveOrdinateHellingerTangentLp,
    routePProjectiveOrdinateCubicTangentGram,
    ← hab, ← ha2b, ← h2ab, ← h2a2b]
  simp only [inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, Complex.conj_ofReal]
  push_cast
  ring

theorem routePProjectiveOrdinateCubicTangentGram_diagonal
    {sigma R a b gamma : ℝ} (hsigma : 1 < sigma)
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    routePProjectiveOrdinateCubicTangentGram
        R a gamma b gamma sigma =
      routePProjectiveFullEulerCubicTangentGram R a b sigma := by
  have h2a : 0 < 2 * a := mul_pos two_pos ha
  have h2b : 0 < 2 * b := mul_pos two_pos hb
  rw [routePProjectiveOrdinateCubicTangentGram,
    routePProjectiveFullEulerCubicTangentGram,
    routePProjectiveOrdinateLogMomentGramTerm_diagonal hsigma hR ha hb,
    routePProjectiveOrdinateLogMomentGramTerm_diagonal hsigma hR ha h2b,
    routePProjectiveOrdinateLogMomentGramTerm_diagonal hsigma hR h2a hb,
    routePProjectiveOrdinateLogMomentGramTerm_diagonal hsigma hR h2a h2b]

/-- Equal-ordinate tangent fibres retain the cubic Hellinger kernel. -/
theorem tendsto_routePProjectiveOrdinateCubicTangentGram_diagonal
    {R a b gamma : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (routePProjectiveOrdinateCubicTangentGram R a gamma b gamma)
      (nhdsWithin 1 (Ioi 1))
      (nhds (cubicLogMomentHellingerHorizontalKernel a b : ℂ)) := by
  have hbase :=
    tendsto_routePProjectiveFullEulerCubicTangentGram hR ha hb
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  exact (routePProjectiveOrdinateCubicTangentGram_diagonal
    hsigma hR ha hb).symm

/-- Unequal-ordinate tangent fibres vanish termwise; no external harmonic projector is needed. -/
theorem tendsto_routePProjectiveOrdinateCubicTangentGram_offDiagonal
    {R a gamma b delta : ℝ} (hgammaDelta : gamma ≠ delta) :
    Tendsto
      (routePProjectiveOrdinateCubicTangentGram R a gamma b delta)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have h1 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_offDiagonal
    (R := R) (a := a) (gamma := gamma) (b := b) (delta := delta)
    hgammaDelta
  have h2 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_offDiagonal
    (R := R) (a := a) (gamma := gamma) (b := 2 * b) (delta := delta)
    hgammaDelta
  have h3 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_offDiagonal
    (R := R) (a := 2 * a) (gamma := gamma) (b := b) (delta := delta)
    hgammaDelta
  have h4 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_offDiagonal
    (R := R) (a := 2 * a) (gamma := gamma) (b := 2 * b) (delta := delta)
    hgammaDelta
  have h := ((h1.sub h2).sub h3).add h4
  change Tendsto
    (fun sigma : ℝ =>
      routePProjectiveOrdinateLogMomentGramTerm R a gamma b delta sigma -
          routePProjectiveOrdinateLogMomentGramTerm
            R a gamma (2 * b) delta sigma -
        routePProjectiveOrdinateLogMomentGramTerm
          R (2 * a) gamma b delta sigma +
      routePProjectiveOrdinateLogMomentGramTerm
        R (2 * a) gamma (2 * b) delta sigma)
    (nhdsWithin 1 (Ioi 1)) (nhds 0)
  simpa using h

/-- **Cubic source-native ordinate projector.** The actual finite-sigma Euler tangent Gram tends
to the cubic Hellinger kernel on equal-ordinate fibres and to zero on unequal fibres. -/
theorem tendsto_routePProjectiveOrdinateCubicTangentGram
    {R a gamma b delta : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (routePProjectiveOrdinateCubicTangentGram R a gamma b delta)
      (nhdsWithin 1 (Ioi 1))
      (nhds (if gamma = delta then
        (cubicLogMomentHellingerHorizontalKernel a b : ℂ) else 0)) := by
  by_cases hgammaDelta : gamma = delta
  · subst delta
    simpa using
      tendsto_routePProjectiveOrdinateCubicTangentGram_diagonal
        (gamma := gamma) hR ha hb
  · simpa [hgammaDelta] using
      tendsto_routePProjectiveOrdinateCubicTangentGram_offDiagonal
        (R := R) (a := a) (b := b) hgammaDelta

/-! ## Finite packet consequence -/

/-- Quadratic form of a finite packet of moving-ordinate cubic Euler tangents. -/
def routePFiniteOrdinateCubicQuadraticForm
    {ι : Type*} [Fintype ι]
    (R sigma : ℝ) (a gamma : ι → ℝ) (c : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι,
    (c j * (starRingEnd ℂ) (c i)) *
      routePProjectiveOrdinateCubicTangentGram
        R (a i) (gamma i) (a j) (gamma j) sigma

/-- Every finite source packet converges to the exact ordinate-block projection. Distinct
ordinates become orthogonal; repeated ordinates retain their horizontal cubic Gram block. -/
theorem tendsto_routePFiniteOrdinateCubicQuadraticForm
    {ι : Type*} [Fintype ι]
    {R : ℝ} {a gamma : ι → ℝ} (c : ι → ℂ)
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    Tendsto
      (fun sigma : ℝ =>
        routePFiniteOrdinateCubicQuadraticForm R sigma a gamma c)
      (nhdsWithin 1 (Ioi 1))
      (nhds
        (∑ i : ι, ∑ j : ι,
          (c j * (starRingEnd ℂ) (c i)) *
            (if gamma i = gamma j then
              (cubicLogMomentHellingerHorizontalKernel
                (a i) (a j) : ℂ)
            else 0))) := by
  have hentry : ∀ i j : ι,
      Tendsto
        (fun sigma : ℝ =>
          (c j * (starRingEnd ℂ) (c i)) *
            routePProjectiveOrdinateCubicTangentGram
              R (a i) (gamma i) (a j) (gamma j) sigma)
        (nhdsWithin 1 (Ioi 1))
        (nhds
          ((c j * (starRingEnd ℂ) (c i)) *
            (if gamma i = gamma j then
              (cubicLogMomentHellingerHorizontalKernel
                (a i) (a j) : ℂ)
            else 0))) := by
    intro i j
    exact
      (tendsto_routePProjectiveOrdinateCubicTangentGram
        hR (ha i) (ha j)).const_mul
          (c j * (starRingEnd ℂ) (c i))
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset ι) fun j _ => hentry i j
  simpa [routePFiniteOrdinateCubicQuadraticForm] using hsum

end

end RHTower
