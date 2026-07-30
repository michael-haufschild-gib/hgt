import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardJuliaTransport
import GaloisForLFunctions.RHTower.CCMRectangularDirichletLandau

/-!
# Non-diagonal Möbius--Gamma transport to the anti-causal Xi Ward column

The full Xi logarithmic trace is not the anti-causal Ward response.  This file performs the
missing half-plane factorization before taking the Julia tangent.

The strict-right canonical factor is formed directly from the actual Xi divisor with
multiplicity.  It is one factor in an exact Wiener--Hopf splitting of the full genus-one
canonical product; no enumeration or finite cutoff is chosen.  Its centered logarithmic
derivative is therefore the canonical, absolutely convergent strict-right relative trace.

The source transport is the two-point Julia cross-defect of this factor.  It is genuinely
non-diagonal in its two spectral nodes.  Anchoring one node at the functional-equation centre and
differentiating the aperture gives the strict-right relative trace.  Its genus-one subtraction
produces the absolutely convergent centered Hardy response.

The raw Ward response has a nonzero boundary contact.  Summing reciprocal contacts separately
would diverge, but the Xi Schwarz involution canonically pairs them before summation.  The pair
contact is reciprocal-square summable.  Adding this source-fixed self-symbol to the Julia
transport gives a tangent whose value is proved below to be the raw continued anti-causal response

`2 * sum_{upper Schwarz pairs q}
  ((w + lambda_q)⁻¹ + (w + conj(lambda_q))⁻¹)`.
-/

open Complex Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Canonical strict-right Wiener--Hopf factor -/

/-- Strict-right Xi spectral point, retaining exact analytic multiplicity. -/
def xiRightSpectralPoint (q : XiRightZeroCopy) : ℂ :=
  xiSpectralPoint q.1

theorem xiRightSpectralPoint_ne_zero (q : XiRightZeroCopy) :
    xiRightSpectralPoint q ≠ 0 :=
  xiSpectralPoint_ne_zero q.1

/-- The reciprocal-square convergence of the full Xi divisor restricts to its strict-right
half without an enumeration. -/
theorem xiRightSpectralPoint_inv_sq_summable :
    Summable (fun q : XiRightZeroCopy => 1 / ‖xiRightSpectralPoint q‖ ^ 2) := by
  simpa only [xiRightSpectralPoint] using!
    xiSpectralPoint_inv_sq_summable.subtype
      (fun q : XiZeroCopy => 0 < (I * xiSpectralPoint q).re)

/-- Genus-one canonical product of the strict-right Xi divisor.  This is the source-selected
anti-causal Wiener--Hopf factor, defined before any Ward response is read from it. -/
def xiRightCanonicalProduct : ℂ → ℂ :=
  canonicalProductE1Indexed xiRightSpectralPoint

theorem xiRightCanonicalProduct_hasProdLocallyUniformlyOn :
    HasProdLocallyUniformlyOn
      (fun q z => weierstrassE1 (z / xiRightSpectralPoint q))
      xiRightCanonicalProduct Set.univ :=
  canonicalProductE1Indexed_hasProdLocallyUniformlyOn xiRightSpectralPoint
    xiRightSpectralPoint_ne_zero xiRightSpectralPoint_inv_sq_summable

theorem xiRightCanonicalProduct_analytic :
    AnalyticOnNhd ℂ xiRightCanonicalProduct Set.univ :=
  canonicalProductE1Indexed_analytic xiRightSpectralPoint
    xiRightSpectralPoint_ne_zero xiRightSpectralPoint_inv_sq_summable

@[simp] theorem xiRightCanonicalProduct_zero :
    xiRightCanonicalProduct 0 = 1 := by
  rw [xiRightCanonicalProduct, canonicalProductE1Indexed]
  simp [weierstrassE1]

/-- Every strict-right multiplicity copy is a zero of the strict-right factor. -/
theorem xiRightCanonicalProduct_eq_zero (q : XiRightZeroCopy) :
    xiRightCanonicalProduct (xiRightSpectralPoint q) = 0 := by
  rw [xiRightCanonicalProduct, canonicalProductE1Indexed]
  apply tprod_of_exists_eq_zero
  refine ⟨q, ?_⟩
  rw [div_self (xiRightSpectralPoint_ne_zero q), weierstrassE1_one]

/-- The strict-right factor has no zeros other than the strict-right Xi divisor. -/
theorem xiRightCanonicalProduct_eq_zero_iff_exists (z : ℂ) :
    xiRightCanonicalProduct z = 0 ↔
      ∃ q : XiRightZeroCopy, xiRightSpectralPoint q = z := by
  constructor
  · intro hz
    by_contra hnone
    have haway : ∀ q : XiRightZeroCopy, z ≠ xiRightSpectralPoint q := by
      intro q heq
      exact hnone ⟨q, heq.symm⟩
    exact (canonicalProductE1Indexed_ne_zero xiRightSpectralPoint
      xiRightSpectralPoint_ne_zero xiRightSpectralPoint_inv_sq_summable haway) hz
  · rintro ⟨q, rfl⟩
    exact xiRightCanonicalProduct_eq_zero q

/-- Source-canonical complementary factor.  Away from the strict-right divisor it is the quotient
of the full Xi canonical product by its strict-right canonical factor. -/
def xiNonrightCanonicalProduct (z : ℂ) : ℂ :=
  xiCanonicalProduct z / xiRightCanonicalProduct z

/-- Exact infinite Wiener--Hopf splitting of the Xi canonical product.  At a strict-right zero
both the right factor and the full source product vanish; away from that divisor this is exact
quotient cancellation. -/
theorem xiCanonicalProduct_eq_right_mul_nonright (z : ℂ) :
    xiCanonicalProduct z =
      xiRightCanonicalProduct z * xiNonrightCanonicalProduct z := by
  by_cases hright : xiRightCanonicalProduct z = 0
  · have hfull : xiCanonicalProduct z = 0 := by
      obtain ⟨q, hq⟩ :=
        (xiRightCanonicalProduct_eq_zero_iff_exists z).mp hright
      rw [← hq]
      simpa only [xiRightSpectralPoint] using
        xiCanonicalProduct_eq_zero q.1
    simp [xiNonrightCanonicalProduct, hright, hfull]
  · rw [xiNonrightCanonicalProduct]
    field_simp [hright]

/-- Complementary source factor, including the nonvanishing Hadamard quotient. -/
def xiNonrightSourceFactor (z : ℂ) : ℂ :=
  xiHadamardQuotient z * xiNonrightCanonicalProduct z

/-- Exact source-level Wiener--Hopf factorization.  The strict-right factor used by the transport
is a genuine factor of the completed Xi source, not an independently prescribed response
function. -/
theorem xiRightCanonicalProduct_mul_nonrightSourceFactor
    (z : ℂ) :
    xiRightCanonicalProduct z * xiNonrightSourceFactor z = XiC z := by
  have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct z
  rw [Pi.mul_apply] at hsource
  calc
    xiRightCanonicalProduct z * xiNonrightSourceFactor z =
        xiHadamardQuotient z *
          (xiRightCanonicalProduct z *
            xiNonrightCanonicalProduct z) := by
      rw [xiNonrightSourceFactor]
      ring
    _ = xiHadamardQuotient z * xiCanonicalProduct z := by
      rw [← xiCanonicalProduct_eq_right_mul_nonright z]
    _ = XiC z := hsource

/-! ## The centered strict-right relative trace -/

/-- One centered strict-right genus-one resolvent term. -/
def xiRightRelativeResolventTerm (z : ℂ) (q : XiRightZeroCopy) : ℂ :=
  (xiRightSpectralPoint q)⁻¹ - (xiRightSpectralPoint q - z)⁻¹

/-- The strict-right rational majorant is absolutely summable. -/
theorem summable_xiRight_relativeResolventTerms (z : ℂ) :
    Summable (fun q : XiRightZeroCopy =>
      -z / (xiRightSpectralPoint q * (xiRightSpectralPoint q - z))) := by
  simpa only [xiRightSpectralPoint] using!
    (summable_xi_relativeResolventTerms z).subtype
      (fun q : XiZeroCopy => 0 < (I * xiSpectralPoint q).re)

/-- The centered strict-right relative trace.  This is an unconditional `tsum`; it has no
enumeration or exhaustion parameter. -/
def xiRightRelativeResolventTrace (z : ℂ) : ℂ :=
  ∑' q : XiRightZeroCopy, xiRightRelativeResolventTerm z q

theorem summable_xiRightRelativeResolventTerm
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    Summable (xiRightRelativeResolventTerm z) := by
  apply (summable_xiRight_relativeResolventTerms z).congr
  intro q
  rw [xiRightRelativeResolventTerm]
  have ha := xiRightSpectralPoint_ne_zero q
  have hzq : z ≠ xiRightSpectralPoint q := by
    intro h
    exact hz (by
      rw [h]
      exact xiRightCanonicalProduct_eq_zero q)
  have haz : xiRightSpectralPoint q - z ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hzq)
  rw [inv_eq_one_div]
  field_simp [ha, haz]
  ring

/-- The centered logarithmic derivative of the strict-right Wiener--Hopf factor is exactly its
absolutely convergent strict-right relative trace. -/
theorem logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    logDeriv xiRightCanonicalProduct z = xiRightRelativeResolventTrace z := by
  have hza (q : XiRightZeroCopy) : z ≠ xiRightSpectralPoint q := by
    intro h
    exact hz (by rw [h]; exact xiRightCanonicalProduct_eq_zero q)
  have hfac (q : XiRightZeroCopy) :
      weierstrassE1 (z / xiRightSpectralPoint q) ≠ 0 := by
    rw [weierstrassE1]
    apply mul_ne_zero
    · intro hzero
      have hdiv : z / xiRightSpectralPoint q = 1 :=
        (sub_eq_zero.mp hzero).symm
      apply hza q
      calc
        z = z / xiRightSpectralPoint q * xiRightSpectralPoint q :=
          (div_mul_cancel₀ z (xiRightSpectralPoint_ne_zero q)).symm
        _ = 1 * xiRightSpectralPoint q := by rw [hdiv]
        _ = xiRightSpectralPoint q := one_mul _
    · exact Complex.exp_ne_zero _
  have hsum : Summable (fun q : XiRightZeroCopy =>
      logDeriv
        (fun w : ℂ => weierstrassE1 (w / xiRightSpectralPoint q)) z) := by
    apply (summable_xiRight_relativeResolventTerms z).congr
    intro q
    exact (logDeriv_weierstrassE1_div
      (xiRightSpectralPoint_ne_zero q) (hza q)).symm
  have hlog := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    hfac (by
      intro q
      simp only [weierstrassE1]
      fun_prop) hsum
    (xiRightCanonicalProduct_hasProdLocallyUniformlyOn
      |>.multipliableLocallyUniformlyOn)
    hz
  rw [xiRightRelativeResolventTrace]
  calc
    logDeriv xiRightCanonicalProduct z =
        ∑' q : XiRightZeroCopy,
          logDeriv
            (fun w : ℂ => weierstrassE1 (w / xiRightSpectralPoint q)) z := by
      simpa only [xiRightCanonicalProduct, canonicalProductE1Indexed] using! hlog
    _ = ∑' q : XiRightZeroCopy,
          -z /
            (xiRightSpectralPoint q * (xiRightSpectralPoint q - z)) := by
      apply tsum_congr
      intro q
      exact logDeriv_weierstrassE1_div
        (xiRightSpectralPoint_ne_zero q) (hza q)
    _ = ∑' q : XiRightZeroCopy, xiRightRelativeResolventTerm z q := by
      apply tsum_congr
      intro q
      have ha := xiRightSpectralPoint_ne_zero q
      have haz : xiRightSpectralPoint q - z ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hza q))
      rw [xiRightRelativeResolventTerm]
      field_simp [ha, haz]
      ring

@[simp] theorem xiRightRelativeResolventTrace_zero :
    xiRightRelativeResolventTrace 0 = 0 := by
  simp [xiRightRelativeResolventTrace, xiRightRelativeResolventTerm]

private theorem logDeriv_xiRightCanonicalProduct_zero :
    logDeriv xiRightCanonicalProduct 0 = 0 := by
  rw [logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace
    (by simp), xiRightRelativeResolventTrace_zero]

/-! ## Source-defined continued anti-causal Ward response -/

/-- Centered coefficient-two Hardy response of one strict-right Xi mode.  The second term is the
genus-one boundary contact counterterm. -/
def xiCenteredAntiCausalWardModeResponse (q : XiRightZeroCopy) (w : ℂ) : ℂ :=
  2 * ((w + xiRightCenteredZero q)⁻¹ - (xiRightCenteredZero q)⁻¹)

/-- Continued anti-causal Xi Ward response at one right-half Cauchy node.  It is defined as the
Laplace rotation of the source-selected strict-right relative trace. -/
def continuedXiCenteredAntiCausalWardResponse (w : ℂ) : ℂ :=
  2 * I * xiRightRelativeResolventTrace (I * w)

private theorem xiCenteredAntiCausalWardMode_algebra (a w : ℂ) :
    2 * I * (a⁻¹ - (a - I * w)⁻¹) =
      2 * ((w + I * a)⁻¹ - (I * a)⁻¹) := by
  have hfactor : a - I * w = -I * (w + I * a) := by
    symm
    have hnegII : (-I) * I = (1 : ℂ) := by
      rw [neg_mul, I_mul_I]
      ring
    calc
      -I * (w + I * a) = -I * w + (-I * I) * a := by ring
      _ = -I * w + a := by rw [hnegII, one_mul]
      _ = a - I * w := by ring
  have hleft : (a - I * w)⁻¹ = I * (w + I * a)⁻¹ := by
    rw [hfactor, mul_inv_rev, inv_neg, inv_I]
    ring
  have hright : (I * a)⁻¹ = -I * a⁻¹ := by
    rw [mul_inv_rev, inv_I]
    rw [mul_comm]
  rw [hleft, hright]
  calc
    2 * I * (a⁻¹ - I * (w + I * a)⁻¹) =
        2 * I * a⁻¹ - 2 * (I * I) * (w + I * a)⁻¹ := by ring
    _ = 2 * ((w + I * a)⁻¹ - -I * a⁻¹) := by
      rw [I_mul_I]
      ring

theorem summable_xiCenteredAntiCausalWardModeResponse
    {w : ℂ} (hw : 0 < w.re) :
    Summable (fun q : XiRightZeroCopy =>
      xiCenteredAntiCausalWardModeResponse q w) := by
  have hprod : xiRightCanonicalProduct (I * w) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ :=
      (xiRightCanonicalProduct_eq_zero_iff_exists (I * w)).mp hzero
    have hright := q.2
    change xiSpectralPoint q.1 = I * w at hq
    rw [hq] at hright
    have hIIw : I * (I * w) = -w := by
      rw [← mul_assoc, I_mul_I, neg_one_mul]
    rw [hIIw] at hright
    simp only [neg_re] at hright
    linarith
  have hsum :=
    (summable_xiRightRelativeResolventTerm hprod).mul_left (2 * I)
  apply hsum.congr
  intro q
  rw [xiCenteredAntiCausalWardModeResponse, xiRightRelativeResolventTerm,
    xiRightSpectralPoint, xiRightCenteredZero]
  exact xiCenteredAntiCausalWardMode_algebra (xiSpectralPoint q.1) w

/-- Source-frame expansion of the Ward response into all strict-right Hardy modes.  This
expansion is a theorem; it is not the definition of the transport. -/
theorem continuedXiCenteredAntiCausalWardResponse_eq_tsum_modes
    {w : ℂ} (_hw : 0 < w.re) :
    continuedXiCenteredAntiCausalWardResponse w =
      ∑' q : XiRightZeroCopy, xiCenteredAntiCausalWardModeResponse q w := by
  rw [continuedXiCenteredAntiCausalWardResponse, xiRightRelativeResolventTrace,
    ← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [xiCenteredAntiCausalWardModeResponse, xiRightRelativeResolventTerm,
    xiRightSpectralPoint, xiRightCenteredZero]
  exact xiCenteredAntiCausalWardMode_algebra (xiSpectralPoint q.1) w

/-- Finite continued Xi Ward column obtained by observing the one infinite anti-causal response
at a finite packet of Cauchy nodes. -/
def continuedXiCenteredAntiCausalWardColumn {n : ℕ}
    (node : Fin n → ℂ) : Fin n → ℂ :=
  fun i => continuedXiCenteredAntiCausalWardResponse (node i)

/-! ## Schwarz-paired boundary self-symbol -/

/-- One representative from every Schwarz pair in the strict-right divisor.  The known
unconditional Xi ordinate gap makes the sign strict. -/
abbrev XiRightUpperZeroCopy :=
  {q : XiRightZeroCopy // 0 < (xiRightCenteredZero q).im}

theorem xiRightCenteredZero_im_ne_zero (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).im ≠ 0 := by
  obtain ⟨eta, heta, hgap⟩ :=
    exists_xiRightCenteredZero_abs_im_lower_bound
  intro hzero
  have h := hgap q
  rw [hzero, abs_zero] at h
  linarith

/-- Schwarz conjugation identifies upper representatives with the complement of the upper
half.  No zero-ordinate exceptional class exists. -/
def xiRightUpperComplConjEquiv :
    XiRightUpperZeroCopy ≃
      {q : XiRightZeroCopy // ¬0 < (xiRightCenteredZero q).im} :=
  Equiv.subtypeEquiv xiRightZeroCopyConjEquiv (fun q => by
    rw [xiRightCenteredZero_conj]
    change 0 < (xiRightCenteredZero q).im ↔
      ¬0 < -(xiRightCenteredZero q).im
    constructor
    · intro hpos hneg
      linarith
    · intro hnonpos
      have hne := xiRightCenteredZero_im_ne_zero q
      have hge : 0 ≤ (xiRightCenteredZero q).im := by
        linarith
      exact lt_of_le_of_ne hge (Ne.symm hne))

/-- Every strict-right Xi multiplicity copy belongs to exactly one canonical Schwarz pair. -/
def xiRightSchwarzPairEquiv :
    XiRightUpperZeroCopy ⊕ XiRightUpperZeroCopy ≃ XiRightZeroCopy :=
  (Equiv.sumCongr (Equiv.refl XiRightUpperZeroCopy)
      xiRightUpperComplConjEquiv).trans
    (Equiv.sumCompl
      (fun q : XiRightZeroCopy => 0 < (xiRightCenteredZero q).im))

@[simp] theorem xiRightSchwarzPairEquiv_inl
    (q : XiRightUpperZeroCopy) :
    xiRightSchwarzPairEquiv (Sum.inl q) = q.1 := by
  simp [xiRightSchwarzPairEquiv]

@[simp] theorem xiRightSchwarzPairEquiv_inr
    (q : XiRightUpperZeroCopy) :
    xiRightSchwarzPairEquiv (Sum.inr q) =
      xiRightZeroCopyConjEquiv q.1 := by
  simp [xiRightSchwarzPairEquiv, xiRightUpperComplConjEquiv]

/-- Boundary contact contributed by one complete Schwarz pair.  Pairing occurs before summation,
so the apparent reciprocal-first-order divergence cancels to reciprocal-square size. -/
def xiAntiCausalWardBoundaryPairTerm
    (q : XiRightUpperZeroCopy) : ℂ :=
  2 * ((xiRightCenteredZero q.1)⁻¹ +
    ((starRingEnd ℂ) (xiRightCenteredZero q.1))⁻¹)

theorem xiAntiCausalWardBoundaryPairTerm_eq_pair
    (q : XiRightUpperZeroCopy) :
    xiAntiCausalWardBoundaryPairTerm q =
      2 * ((xiRightCenteredZero q.1)⁻¹ +
        (xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1))⁻¹) := by
  rw [xiAntiCausalWardBoundaryPairTerm, xiRightCenteredZero_conj]

/-- Schwarz pairing makes the raw Ward boundary self-symbol absolutely summable. -/
theorem summable_xiAntiCausalWardBoundaryPairTerm :
    Summable xiAntiCausalWardBoundaryPairTerm := by
  have hbase : Summable (fun q : XiRightUpperZeroCopy =>
      1 / ‖xiRightCenteredZero q.1‖ ^ 2) := by
    simpa only [xiRightCenteredZero, norm_mul, norm_I, one_mul,
      xiRightSpectralPoint] using!
      xiRightSpectralPoint_inv_sq_summable.subtype
        (fun q : XiRightZeroCopy => 0 < (xiRightCenteredZero q).im)
  apply Summable.of_norm_bounded (hbase.mul_left 2)
  intro q
  let lam : ℂ := xiRightCenteredZero q.1
  have hlam : lam ≠ 0 := xiRightCenteredZero_ne_zero q.1
  have hlamc : (starRingEnd ℂ) lam ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).2 hlam
  have hinv :
      lam⁻¹ + ((starRingEnd ℂ) lam)⁻¹ =
        (lam + (starRingEnd ℂ) lam) /
          (lam * (starRingEnd ℂ) lam) := by
    field_simp [hlam, hlamc]
    ring
  have hreal :
      lam + (starRingEnd ℂ) lam = ((2 * lam.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
      ring
    · simp
  have hnum : ‖lam + (starRingEnd ℂ) lam‖ ≤ 1 := by
    rw [hreal, norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
    have htrans := abs_xiRightCenteredZero_re_lt_half q.1
    linarith
  have hinvnorm :
      ‖lam⁻¹ + ((starRingEnd ℂ) lam)⁻¹‖ ≤ 1 / ‖lam‖ ^ 2 := by
    rw [hinv, norm_div, norm_mul, Complex.norm_conj]
    calc
      ‖lam + (starRingEnd ℂ) lam‖ / (‖lam‖ * ‖lam‖) ≤
          1 / (‖lam‖ * ‖lam‖) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = 1 / ‖lam‖ ^ 2 := by ring
  change ‖2 * (lam⁻¹ + ((starRingEnd ℂ) lam)⁻¹)‖ ≤
    2 * (1 / ‖lam‖ ^ 2)
  calc
    ‖2 * (lam⁻¹ + ((starRingEnd ℂ) lam)⁻¹)‖ =
        2 * ‖lam⁻¹ + ((starRingEnd ℂ) lam)⁻¹‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 2 * (1 / ‖lam‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hinvnorm (by norm_num)

/-- Centered genus-one response of one complete Schwarz pair. -/
def xiCenteredAntiCausalWardSchwarzPairResponse
    (q : XiRightUpperZeroCopy) (w : ℂ) : ℂ :=
  xiCenteredAntiCausalWardModeResponse q.1 w +
    xiCenteredAntiCausalWardModeResponse
      (xiRightZeroCopyConjEquiv q.1) w

/-- Raw anti-causal Ward response of one complete Schwarz pair.  Pairing is part of the
definition, so this is an unambiguous absolutely convergent expansion rather than a conditionally
ordered sum over individual zeros. -/
def xiAntiCausalWardSchwarzPairResponse
    (q : XiRightUpperZeroCopy) (w : ℂ) : ℂ :=
  2 * ((w + xiRightCenteredZero q.1)⁻¹ +
    (w + xiRightCenteredZero
      (xiRightZeroCopyConjEquiv q.1))⁻¹)

set_option maxHeartbeats 800000 in
/-- The strict-right centered trace splits canonically into complete Schwarz-pair responses. -/
theorem continuedXiCenteredAntiCausalWardResponse_eq_tsum_schwarzPairs
    {w : ℂ} (hw : 0 < w.re) :
    continuedXiCenteredAntiCausalWardResponse w =
      ∑' q : XiRightUpperZeroCopy,
        xiCenteredAntiCausalWardSchwarzPairResponse q w := by
  let f : XiRightZeroCopy → ℂ :=
    fun q => xiCenteredAntiCausalWardModeResponse q w
  have hfull : Summable f :=
    summable_xiCenteredAntiCausalWardModeResponse hw
  have hinl :
      Summable (fun q : XiRightUpperZeroCopy =>
        f (xiRightSchwarzPairEquiv (Sum.inl q))) := by
    simpa only [xiRightSchwarzPairEquiv_inl] using!
      hfull.comp_injective Subtype.val_injective
  have hinr :
      Summable (fun q : XiRightUpperZeroCopy =>
        f (xiRightSchwarzPairEquiv (Sum.inr q))) := by
    apply hfull.comp_injective
    exact xiRightZeroCopyConjEquiv.injective.comp Subtype.val_injective
  rw [continuedXiCenteredAntiCausalWardResponse_eq_tsum_modes hw,
    ← xiRightSchwarzPairEquiv.tsum_eq f]
  calc
    (∑' x : XiRightUpperZeroCopy ⊕ XiRightUpperZeroCopy,
        f (xiRightSchwarzPairEquiv x)) =
        (∑' q : XiRightUpperZeroCopy,
          f (xiRightSchwarzPairEquiv (Sum.inl q))) +
        ∑' q : XiRightUpperZeroCopy,
          f (xiRightSchwarzPairEquiv (Sum.inr q)) :=
      (hinl.hasSum.sum hinr.hasSum).tsum_eq
    _ = ∑' q : XiRightUpperZeroCopy,
          (f (xiRightSchwarzPairEquiv (Sum.inl q)) +
            f (xiRightSchwarzPairEquiv (Sum.inr q))) :=
      (hinl.tsum_add hinr).symm
    _ = ∑' q : XiRightUpperZeroCopy,
          xiCenteredAntiCausalWardSchwarzPairResponse q w := by
      apply tsum_congr
      intro q
      simp only [xiRightSchwarzPairEquiv_inl,
        xiRightSchwarzPairEquiv_inr, f,
        xiCenteredAntiCausalWardSchwarzPairResponse]

/-- Pairwise contact law: adding the Schwarz boundary self-symbol exactly removes both genus-one
subtractions and produces the raw Ward pair. -/
theorem xiCentered_add_boundary_eq_raw_schwarzPair
    (q : XiRightUpperZeroCopy) (w : ℂ) :
    xiCenteredAntiCausalWardSchwarzPairResponse q w +
        xiAntiCausalWardBoundaryPairTerm q =
      xiAntiCausalWardSchwarzPairResponse q w := by
  rw [xiCenteredAntiCausalWardSchwarzPairResponse,
    xiAntiCausalWardSchwarzPairResponse,
    xiAntiCausalWardBoundaryPairTerm_eq_pair]
  simp only [xiCenteredAntiCausalWardModeResponse]
  ring

theorem summable_xiCenteredAntiCausalWardSchwarzPairResponse
    {w : ℂ} (hw : 0 < w.re) :
    Summable (fun q : XiRightUpperZeroCopy =>
      xiCenteredAntiCausalWardSchwarzPairResponse q w) := by
  have hfull :=
    summable_xiCenteredAntiCausalWardModeResponse hw
  have hleft :
      Summable (fun q : XiRightUpperZeroCopy =>
        xiCenteredAntiCausalWardModeResponse q.1 w) :=
    hfull.comp_injective Subtype.val_injective
  have hright :
      Summable (fun q : XiRightUpperZeroCopy =>
        xiCenteredAntiCausalWardModeResponse
          (xiRightZeroCopyConjEquiv q.1) w) := by
    apply hfull.comp_injective
    exact xiRightZeroCopyConjEquiv.injective.comp Subtype.val_injective
  simpa only [xiCenteredAntiCausalWardSchwarzPairResponse] using
    hleft.add hright

/-- The raw paired anti-causal Xi response is absolutely summable on every Cauchy node. -/
theorem summable_xiAntiCausalWardSchwarzPairResponse
    {w : ℂ} (hw : 0 < w.re) :
    Summable (fun q : XiRightUpperZeroCopy =>
      xiAntiCausalWardSchwarzPairResponse q w) := by
  exact
    ((summable_xiCenteredAntiCausalWardSchwarzPairResponse hw).add
      summable_xiAntiCausalWardBoundaryPairTerm).congr
      (fun q => xiCentered_add_boundary_eq_raw_schwarzPair q w)

/-- Raw boundary contact of the continued strict-right Xi Hardy current.  This is the
Schwarz-paired source normalization missing from the center-anchored genus-one trace. -/
def xiAntiCausalWardBoundarySelfSymbol : ℂ :=
  ∑' q : XiRightUpperZeroCopy, xiAntiCausalWardBoundaryPairTerm q

/-- Paper Ward response: centered genus-one response plus the source-canonical Schwarz-paired
boundary contact. -/
def continuedXiAntiCausalWardResponse (w : ℂ) : ℂ :=
  continuedXiCenteredAntiCausalWardResponse w +
    xiAntiCausalWardBoundarySelfSymbol

/-- Identification with the raw paper response.  The equality is unconditional and its right side
is an absolutely convergent Schwarz-paired sum over the complete strict-right Xi divisor. -/
theorem continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs
    {w : ℂ} (hw : 0 < w.re) :
    continuedXiAntiCausalWardResponse w =
      ∑' q : XiRightUpperZeroCopy,
        xiAntiCausalWardSchwarzPairResponse q w := by
  have hcenter :=
    summable_xiCenteredAntiCausalWardSchwarzPairResponse hw
  rw [continuedXiAntiCausalWardResponse,
    continuedXiCenteredAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    xiAntiCausalWardBoundarySelfSymbol,
    ← hcenter.tsum_add summable_xiAntiCausalWardBoundaryPairTerm]
  apply tsum_congr
  intro q
  exact xiCentered_add_boundary_eq_raw_schwarzPair q w

/-- Finite paper Ward column obtained from the one infinite anti-causal response. -/
def continuedXiAntiCausalWardColumn {n : ℕ}
    (node : Fin n → ℂ) : Fin n → ℂ :=
  fun i => continuedXiAntiCausalWardResponse (node i)

/-! ## Non-diagonal Julia transport of the strict-right factor -/

/-- Aperture phase of the strict-right Xi Wiener--Hopf factor. -/
def xiRightWardSourcePhase (z alpha : ℂ) : ℂ :=
  xiRightCanonicalProduct (z - alpha * I) /
    xiRightCanonicalProduct (z + alpha * I)

/-- Complementary phase in the exact source factorization. -/
def xiNonrightWardSourcePhase (z alpha : ℂ) : ℂ :=
  xiNonrightSourceFactor (z - alpha * I) /
    xiNonrightSourceFactor (z + alpha * I)

/-- The completed-Xi source phase splits exactly into the strict-right phase transported below
and its complementary source phase. -/
theorem xiWardSourcePhase_eq_right_mul_nonrightSourcePhase
    {z alpha : ℂ}
    (hright : xiRightCanonicalProduct (z + alpha * I) ≠ 0)
    (hnonright : xiNonrightSourceFactor (z + alpha * I) ≠ 0) :
    xiWardSourcePhase z alpha =
      xiRightWardSourcePhase z alpha *
        xiNonrightWardSourcePhase z alpha := by
  rw [xiWardSourcePhase, xiRightWardSourcePhase,
    xiNonrightWardSourcePhase,
    ← xiRightCanonicalProduct_mul_nonrightSourceFactor
      (z - alpha * I),
    ← xiRightCanonicalProduct_mul_nonrightSourceFactor
      (z + alpha * I)]
  field_simp [hright, hnonright]

@[simp] theorem xiRightWardSourcePhase_zero
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    xiRightWardSourcePhase z 0 = 1 := by
  simp [xiRightWardSourcePhase, hz]

theorem hasDerivAt_xiRightWardSourcePhase_zero
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    HasDerivAt (xiRightWardSourcePhase z)
      (-2 * I * logDeriv xiRightCanonicalProduct z) 0 := by
  have hminus : HasDerivAt (fun alpha : ℂ => z - alpha * I) (-I) 0 := by
    simpa using!
      (hasDerivAt_const (x := (0 : ℂ)) (c := z)).sub
        ((hasDerivAt_id (𝕜 := ℂ) (x := (0 : ℂ))).mul_const I)
  have hplus : HasDerivAt (fun alpha : ℂ => z + alpha * I) I 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℂ) (x := (0 : ℂ))).mul_const I).const_add z
  have hnum :
      HasDerivAt
        (fun alpha : ℂ => xiRightCanonicalProduct (z - alpha * I))
        (deriv xiRightCanonicalProduct z * (-I)) 0 := by
    have hF : HasDerivAt xiRightCanonicalProduct
        (deriv xiRightCanonicalProduct z) z :=
      (xiRightCanonicalProduct_analytic z
        (Set.mem_univ z)).differentiableAt.hasDerivAt
    have hF' : HasDerivAt xiRightCanonicalProduct
        (deriv xiRightCanonicalProduct z) (z - 0 * I) := by
      simpa using hF
    simpa using! hF'.comp 0 hminus
  have hden :
      HasDerivAt
        (fun alpha : ℂ => xiRightCanonicalProduct (z + alpha * I))
        (deriv xiRightCanonicalProduct z * I) 0 := by
    have hF : HasDerivAt xiRightCanonicalProduct
        (deriv xiRightCanonicalProduct z) z :=
      (xiRightCanonicalProduct_analytic z
        (Set.mem_univ z)).differentiableAt.hasDerivAt
    have hF' : HasDerivAt xiRightCanonicalProduct
        (deriv xiRightCanonicalProduct z) (z + 0 * I) := by
      simpa using hF
    simpa using! hF'.comp 0 hplus
  have hquot := hnum.div hden (by simpa using hz)
  simpa only [xiRightWardSourcePhase, logDeriv_apply] using!
    hquot.congr_deriv (by
      field_simp [hz]
      ring_nf)

/-- Analytic two-node sharp ratio of the strict-right phase. -/
def xiRightWardSourcePhaseCrossRatio (z w alpha : ℂ) : ℂ :=
  xiRightWardSourcePhase z alpha /
    xiRightWardSourcePhase ((starRingEnd ℂ) w) alpha

/-- Non-diagonal Julia cross-defect of the strict-right source factor. -/
def xiRightWardJuliaCrossDefect (z w alpha : ℂ) : ℂ :=
  (xiRightWardSourcePhaseCrossRatio z w alpha - 1) /
    (2 * I * (z - (starRingEnd ℂ) w))

/-- Exact Julia identity for the anti-causal factor: transported cross-Gram minus the original
cross-Gram. -/
theorem xiRightWardJuliaCrossDefect_eq_transport_sub_gram
    (z w alpha : ℂ) :
    xiRightWardJuliaCrossDefect z w alpha =
      xiRightWardSourcePhaseCrossRatio z w alpha *
          xiWardCauchyGramCell z w -
        xiWardCauchyGramCell z w := by
  simp only [xiRightWardJuliaCrossDefect, xiWardCauchyGramCell]
  ring

theorem hasDerivAt_xiRightWardSourcePhaseCrossRatio_zero
    {z w : ℂ} (hz : xiRightCanonicalProduct z ≠ 0)
    (hw : xiRightCanonicalProduct ((starRingEnd ℂ) w) ≠ 0) :
    HasDerivAt (xiRightWardSourcePhaseCrossRatio z w)
      (2 * I *
        (logDeriv xiRightCanonicalProduct ((starRingEnd ℂ) w) -
          logDeriv xiRightCanonicalProduct z)) 0 := by
  have hzphase := hasDerivAt_xiRightWardSourcePhase_zero hz
  have hwphase := hasDerivAt_xiRightWardSourcePhase_zero hw
  have hwzero : xiRightWardSourcePhase ((starRingEnd ℂ) w) 0 ≠ 0 := by
    rw [xiRightWardSourcePhase_zero hw]
    exact one_ne_zero
  have hquot := hzphase.div hwphase hwzero
  rw [xiRightWardSourcePhase_zero hz, xiRightWardSourcePhase_zero hw] at hquot
  simpa only [xiRightWardSourcePhaseCrossRatio, one_pow, mul_one, one_mul,
    div_one] using! hquot.congr_deriv (by ring)

/-- The Julia cross-defect tangent is the divided difference of the strict-right relative trace,
so causal and critical-line factors have already been removed. -/
theorem hasDerivAt_xiRightWardJuliaCrossDefect_zero
    {z w : ℂ} (hz : xiRightCanonicalProduct z ≠ 0)
    (hw : xiRightCanonicalProduct ((starRingEnd ℂ) w) ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    HasDerivAt (xiRightWardJuliaCrossDefect z w)
      ((xiRightRelativeResolventTrace ((starRingEnd ℂ) w) -
          xiRightRelativeResolventTrace z) /
        (z - (starRingEnd ℂ) w)) 0 := by
  have hcross := hasDerivAt_xiRightWardSourcePhaseCrossRatio_zero hz hw
  have h :=
    (hcross.sub_const 1).div_const
      (2 * I * (z - (starRingEnd ℂ) w))
  rw [logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace hz,
    logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace hw] at h
  simpa only [xiRightWardJuliaCrossDefect] using!
    h.congr_deriv (by
      field_simp [I_ne_zero, sub_ne_zero.mpr hzw])

/-- Common-anchor non-diagonal transport of the strict-right factor. -/
def xiRightWardAnchoredSourceTransportV (z alpha : ℂ) : ℂ :=
  -z * xiRightWardJuliaCrossDefect z 0 alpha

/-- The anchored Julia tangent is exactly the strict-right relative trace. -/
theorem hasDerivAt_xiRightWardAnchoredSourceTransportV_zero
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) (hz0 : z ≠ 0) :
    HasDerivAt (xiRightWardAnchoredSourceTransportV z)
      (xiRightRelativeResolventTrace z) 0 := by
  have hzero : xiRightCanonicalProduct ((starRingEnd ℂ) (0 : ℂ)) ≠ 0 := by
    simp
  have hzconj : z ≠ (starRingEnd ℂ) (0 : ℂ) := by
    simpa only [map_zero] using hz0
  have hcross := hasDerivAt_xiRightWardJuliaCrossDefect_zero
    (w := (0 : ℂ)) hz hzero hzconj
  change HasDerivAt
    (fun alpha : ℂ => -z * xiRightWardJuliaCrossDefect z 0 alpha)
    (xiRightRelativeResolventTrace z) 0
  apply (hcross.const_mul (-z)).congr_deriv
  simp only [map_zero, xiRightRelativeResolventTrace_zero, zero_sub]
  field_simp [hz0]
  ring

/-! ## Schwarz boundary phase inside the Julia cell -/

/-- Source-fixed boundary phase.  Its infinitesimal generator is the Schwarz-paired boundary
self-symbol; placing it in the denominator makes the contact part of the same multiplicative
transport as the strict-right Xi phase. -/
def xiAntiCausalWardBoundarySourcePhase (alpha : ℂ) : ℂ :=
  Complex.exp (alpha * xiAntiCausalWardBoundarySelfSymbol)

@[simp] theorem xiAntiCausalWardBoundarySourcePhase_zero :
    xiAntiCausalWardBoundarySourcePhase 0 = 1 := by
  simp [xiAntiCausalWardBoundarySourcePhase]

theorem hasDerivAt_xiAntiCausalWardBoundarySourcePhase_zero :
    HasDerivAt xiAntiCausalWardBoundarySourcePhase
      xiAntiCausalWardBoundarySelfSymbol 0 := by
  have hlinear :
      HasDerivAt
        (fun alpha : ℂ =>
          alpha * xiAntiCausalWardBoundarySelfSymbol)
        xiAntiCausalWardBoundarySelfSymbol 0 := by
    simpa using
      (hasDerivAt_id (𝕜 := ℂ) (x := (0 : ℂ))).mul_const
        xiAntiCausalWardBoundarySelfSymbol
  simpa only [xiAntiCausalWardBoundarySourcePhase, zero_mul,
    Complex.exp_zero, one_mul] using!
    (Complex.hasDerivAt_exp
      (0 * xiAntiCausalWardBoundarySelfSymbol)).comp 0 hlinear

/-- Two-channel source phase: strict-right Xi channel divided by the independently transported
Schwarz boundary channel. -/
def xiRightWardBoundarySourcePhaseCrossRatio
    (z alpha : ℂ) : ℂ :=
  xiRightWardSourcePhase z alpha /
    xiAntiCausalWardBoundarySourcePhase alpha

/-- Non-diagonal Julia defect coupling a strict-right spectral node to the boundary self-symbol
channel. -/
def xiRightWardBoundaryJuliaCrossDefect
    (z alpha : ℂ) : ℂ :=
  (xiRightWardBoundarySourcePhaseCrossRatio z alpha - 1) /
    (2 * I * z)

/-- Exact two-channel Julia identity.  The left side is not an appended scalar correction: it is
transported boundary-to-spectral Cauchy Gram minus the original cross-Gram. -/
theorem xiRightWardBoundaryJuliaCrossDefect_eq_transport_sub_gram
    (z alpha : ℂ) :
    xiRightWardBoundaryJuliaCrossDefect z alpha =
      xiRightWardBoundarySourcePhaseCrossRatio z alpha *
          xiWardCauchyGramCell z 0 -
        xiWardCauchyGramCell z 0 := by
  simp only [xiRightWardBoundaryJuliaCrossDefect,
    xiWardCauchyGramCell, map_zero, sub_zero]
  ring

theorem hasDerivAt_xiRightWardBoundarySourcePhaseCrossRatio_zero
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    HasDerivAt (xiRightWardBoundarySourcePhaseCrossRatio z)
      (-2 * I * logDeriv xiRightCanonicalProduct z -
        xiAntiCausalWardBoundarySelfSymbol) 0 := by
  have hzphase := hasDerivAt_xiRightWardSourcePhase_zero hz
  have hboundary :=
    hasDerivAt_xiAntiCausalWardBoundarySourcePhase_zero
  have hboundaryZero :
      xiAntiCausalWardBoundarySourcePhase 0 ≠ 0 := by simp
  have hquot := hzphase.div hboundary hboundaryZero
  rw [xiRightWardSourcePhase_zero hz,
    xiAntiCausalWardBoundarySourcePhase_zero] at hquot
  simpa only [xiRightWardBoundarySourcePhaseCrossRatio, one_pow,
    mul_one, one_mul, div_one] using! hquot.congr_deriv (by ring)

theorem hasDerivAt_xiRightWardBoundaryJuliaCrossDefect_zero
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) :
    HasDerivAt (xiRightWardBoundaryJuliaCrossDefect z)
      ((-2 * I * xiRightRelativeResolventTrace z -
          xiAntiCausalWardBoundarySelfSymbol) /
        (2 * I * z)) 0 := by
  have hcross :=
    hasDerivAt_xiRightWardBoundarySourcePhaseCrossRatio_zero hz
  have h :=
    (hcross.sub_const 1).div_const (2 * I * z)
  rw [logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace hz] at h
  simpa only [xiRightWardBoundaryJuliaCrossDefect] using! h

/-- Boundary-anchored non-diagonal source transport before the spectral-to-Laplace rotation. -/
def xiRightWardBoundaryAnchoredSourceTransportV
    (z alpha : ℂ) : ℂ :=
  -z * xiRightWardBoundaryJuliaCrossDefect z alpha

/-- The boundary-channel Julia tangent is the centered strict-right trace plus exactly the
Schwarz contact required by the raw Ward normalization. -/
theorem hasDerivAt_xiRightWardBoundaryAnchoredSourceTransportV_zero
    {z : ℂ} (hz : xiRightCanonicalProduct z ≠ 0) (hz0 : z ≠ 0) :
    HasDerivAt (xiRightWardBoundaryAnchoredSourceTransportV z)
      (xiRightRelativeResolventTrace z +
        xiAntiCausalWardBoundarySelfSymbol / (2 * I)) 0 := by
  have h :=
    hasDerivAt_xiRightWardBoundaryJuliaCrossDefect_zero hz
  apply (h.const_mul (-z)).congr_deriv
  field_simp [I_ne_zero, hz0]
  ring

/-- Center-anchored non-diagonal source transport. -/
def mobiusGammaXiCenteredAntiCausalWardTransportV (w alpha : ℂ) : ℂ :=
  2 * I * xiRightWardAnchoredSourceTransportV (I * w) alpha

/-- Its first aperture tangent is the genus-one centered anti-causal response. -/
theorem hasDerivAt_mobiusGammaXiCenteredAntiCausalWardTransportV_zero
    {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (mobiusGammaXiCenteredAntiCausalWardTransportV w)
      (continuedXiCenteredAntiCausalWardResponse w) 0 := by
  have hprod : xiRightCanonicalProduct (I * w) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ :=
      (xiRightCanonicalProduct_eq_zero_iff_exists (I * w)).mp hzero
    have hright := q.2
    change xiSpectralPoint q.1 = I * w at hq
    rw [hq] at hright
    have hIIw : I * (I * w) = -w := by
      rw [← mul_assoc, I_mul_I, neg_one_mul]
    rw [hIIw] at hright
    simp only [neg_re] at hright
    linarith
  have hw0 : I * w ≠ 0 := by
    exact mul_ne_zero I_ne_zero (by
      intro hwzero
      rw [hwzero] at hw
      simp at hw)
  have h :=
    hasDerivAt_xiRightWardAnchoredSourceTransportV_zero hprod hw0
  exact (h.const_mul (2 * I)).congr_deriv rfl

/-- **Requested transport `V`.**  One multiplicative Julia cell couples the strict-right Xi phase
to the Schwarz boundary phase.  Thus both centered infinite response and raw boundary contact are
inside the non-diagonal source transport before the Ward column is evaluated. -/
def mobiusGammaXiAntiCausalWardTransportV (w alpha : ℂ) : ℂ :=
  2 * I *
    xiRightWardBoundaryAnchoredSourceTransportV (I * w) alpha

/-- Exact Julia/defect output law: the first aperture tangent of `V` is the paper anti-causal Xi
Ward response, not the full Xi trace and not only its centered relative version. -/
theorem hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero
    {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (mobiusGammaXiAntiCausalWardTransportV w)
      (continuedXiAntiCausalWardResponse w) 0 := by
  have hproduct : xiRightCanonicalProduct (I * w) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ :=
      (xiRightCanonicalProduct_eq_zero_iff_exists (I * w)).mp hzero
    have hright := q.2
    change xiSpectralPoint q.1 = I * w at hq
    rw [hq] at hright
    have hIIw : I * (I * w) = -w := by
      rw [← mul_assoc, I_mul_I, neg_one_mul]
    rw [hIIw] at hright
    simp only [neg_re] at hright
    linarith
  have hw0 : I * w ≠ 0 := by
    exact mul_ne_zero I_ne_zero (by
      intro hwzero
      rw [hwzero] at hw
      simp at hw)
  have h :=
    hasDerivAt_xiRightWardBoundaryAnchoredSourceTransportV_zero
      hproduct hw0
  apply (h.const_mul (2 * I)).congr_deriv
  rw [continuedXiAntiCausalWardResponse,
    continuedXiCenteredAntiCausalWardResponse]
  field_simp [I_ne_zero]

/-- Fully expanded output law: the same Julia tangent is the absolutely convergent raw
Schwarz-paired Ward response, with no centered counterterm left in the statement. -/
theorem hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero_eq_raw
    {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (mobiusGammaXiAntiCausalWardTransportV w)
      (∑' q : XiRightUpperZeroCopy,
        xiAntiCausalWardSchwarzPairResponse q w) 0 := by
  rw [← continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw]
  exact hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw

/-! ## Non-scalar augmented Julia transport -/

/-- Packet nodes together with the distinguished Schwarz boundary channel. -/
abbrev XiWardBoundaryAugmentedIndex (n : ℕ) :=
  Fin n ⊕ Unit

/-- Spectral coordinate of the augmented packet; the boundary channel is centered at zero. -/
def xiWardBoundaryAugmentedCoordinate {n : ℕ}
    (node : Fin n → ℂ) : XiWardBoundaryAugmentedIndex n → ℂ
  | Sum.inl i => I * node i
  | Sum.inr _ => 0

/-- Left phase vector of the augmented source packet. -/
def xiWardBoundaryAugmentedLeftPhase {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) :
    XiWardBoundaryAugmentedIndex n → ℂ
  | Sum.inl i => xiRightWardSourcePhase (I * node i) alpha
  | Sum.inr _ => xiAntiCausalWardBoundarySourcePhase alpha

/-- Sharp right phase vector.  Spectral nodes use the reflected coordinate; the boundary
self-symbol is its own distinguished channel. -/
def xiWardBoundaryAugmentedRightPhase {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) :
    XiWardBoundaryAugmentedIndex n → ℂ
  | Sum.inl j =>
      xiRightWardSourcePhase
        ((starRingEnd ℂ) (I * node j)) alpha
  | Sum.inr _ => xiAntiCausalWardBoundarySourcePhase alpha

/-- Full non-scalar sharp phase-ratio matrix. -/
def xiWardBoundaryAugmentedCrossRatioMatrix {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) :
    Matrix (XiWardBoundaryAugmentedIndex n)
      (XiWardBoundaryAugmentedIndex n) ℂ :=
  fun i j =>
    xiWardBoundaryAugmentedLeftPhase node alpha i /
      xiWardBoundaryAugmentedRightPhase node alpha j

/-- Augmented two-channel Cauchy cross-Gram. -/
def xiWardBoundaryAugmentedCauchyGram {n : ℕ}
    (node : Fin n → ℂ) :
    Matrix (XiWardBoundaryAugmentedIndex n)
      (XiWardBoundaryAugmentedIndex n) ℂ :=
  fun i j =>
    xiWardCauchyGramCell
      (xiWardBoundaryAugmentedCoordinate node i)
      (xiWardBoundaryAugmentedCoordinate node j)

/-- Source-phase transported augmented cross-Gram. -/
def xiWardBoundaryAugmentedTransportedGram {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) :
    Matrix (XiWardBoundaryAugmentedIndex n)
      (XiWardBoundaryAugmentedIndex n) ℂ :=
  fun i j =>
    xiWardBoundaryAugmentedCrossRatioMatrix node alpha i j *
      xiWardBoundaryAugmentedCauchyGram node i j

/-- Full augmented Julia defect matrix.  Its node--node block carries cross-node divided
differences; its boundary column carries the continued Ward response. -/
def xiWardBoundaryAugmentedJuliaDefectMatrix {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) :
    Matrix (XiWardBoundaryAugmentedIndex n)
      (XiWardBoundaryAugmentedIndex n) ℂ :=
  xiWardBoundaryAugmentedTransportedGram node alpha -
    xiWardBoundaryAugmentedCauchyGram node

/-- **Non-scalar transport `V`.**  Row calibration converts the full augmented Julia defect into
the spectral-to-Laplace normalization.  No coordinatewise definition of its boundary column is
used. -/
def mobiusGammaXiAntiCausalWardMatrixTransportV {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) :
    Matrix (XiWardBoundaryAugmentedIndex n)
      (XiWardBoundaryAugmentedIndex n) ℂ :=
  fun i j =>
    2 * I * (-xiWardBoundaryAugmentedCoordinate node i) *
      xiWardBoundaryAugmentedJuliaDefectMatrix node alpha i j

/-- Exact matrix Julia/defect identity for `V`. -/
theorem mobiusGammaXiAntiCausalWardMatrixTransportV_eq_juliaDefect
    {n : ℕ} (node : Fin n → ℂ) (alpha : ℂ)
    (i j : XiWardBoundaryAugmentedIndex n) :
    mobiusGammaXiAntiCausalWardMatrixTransportV node alpha i j =
      2 * I * (-xiWardBoundaryAugmentedCoordinate node i) *
        (xiWardBoundaryAugmentedTransportedGram node alpha i j -
          xiWardBoundaryAugmentedCauchyGram node i j) :=
  rfl

/-- Every off-diagonal node--node entry is the genuine two-spectral-node Julia cross-defect. -/
theorem mobiusGammaXiAntiCausalWardMatrixTransportV_nodeNode
    {n : ℕ} (node : Fin n → ℂ) (alpha : ℂ) (i j : Fin n) :
    mobiusGammaXiAntiCausalWardMatrixTransportV node alpha
        (Sum.inl i) (Sum.inl j) =
      2 * I * (-(I * node i)) *
        xiRightWardJuliaCrossDefect
          (I * node i) (I * node j) alpha := by
  simp only [mobiusGammaXiAntiCausalWardMatrixTransportV,
    xiWardBoundaryAugmentedJuliaDefectMatrix, Matrix.sub_apply,
    xiWardBoundaryAugmentedTransportedGram,
    xiWardBoundaryAugmentedCrossRatioMatrix,
    xiWardBoundaryAugmentedCauchyGram,
    xiWardBoundaryAugmentedCoordinate,
    xiWardBoundaryAugmentedLeftPhase,
    xiWardBoundaryAugmentedRightPhase,
    xiRightWardJuliaCrossDefect_eq_transport_sub_gram,
    xiRightWardSourcePhaseCrossRatio]

/-- The distinguished off-diagonal boundary column of matrix `V` is the scalar entry transport
constructed above. -/
theorem mobiusGammaXiAntiCausalWardMatrixTransportV_boundaryColumn
    {n : ℕ} (node : Fin n → ℂ) (alpha : ℂ) (i : Fin n) :
    mobiusGammaXiAntiCausalWardMatrixTransportV node alpha
        (Sum.inl i) (Sum.inr ()) =
      mobiusGammaXiAntiCausalWardTransportV (node i) alpha := by
  simp only [mobiusGammaXiAntiCausalWardMatrixTransportV,
    xiWardBoundaryAugmentedJuliaDefectMatrix, Matrix.sub_apply,
    xiWardBoundaryAugmentedTransportedGram,
    xiWardBoundaryAugmentedCrossRatioMatrix,
    xiWardBoundaryAugmentedCauchyGram,
    xiWardBoundaryAugmentedCoordinate,
    xiWardBoundaryAugmentedLeftPhase,
    xiWardBoundaryAugmentedRightPhase,
    mobiusGammaXiAntiCausalWardTransportV,
    xiRightWardBoundaryAnchoredSourceTransportV,
    xiRightWardBoundaryJuliaCrossDefect,
    xiRightWardBoundarySourcePhaseCrossRatio,
    xiWardCauchyGramCell, map_zero, sub_zero]
  ring

/-- Centered packet transport, retained to expose the two independently verified legs. -/
def mobiusGammaXiCenteredAntiCausalWardPacketTransportV {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) : Fin n → ℂ :=
  fun i => mobiusGammaXiCenteredAntiCausalWardTransportV (node i) alpha

theorem hasDerivAt_mobiusGammaXiCenteredAntiCausalWardPacketTransportV_zero
    {n : ℕ} {node : Fin n → ℂ} (hnode : ∀ i, 0 < (node i).re)
    (i : Fin n) :
    HasDerivAt
      (fun alpha =>
        mobiusGammaXiCenteredAntiCausalWardPacketTransportV node alpha i)
      (continuedXiCenteredAntiCausalWardColumn node i) 0 :=
  hasDerivAt_mobiusGammaXiCenteredAntiCausalWardTransportV_zero (hnode i)

/-- Packet form: one source-defined non-diagonal transport produces every entry of the paper
continued Xi Ward column. -/
def mobiusGammaXiAntiCausalWardPacketTransportV {n : ℕ}
    (node : Fin n → ℂ) (alpha : ℂ) : Fin n → ℂ :=
  fun i =>
    mobiusGammaXiAntiCausalWardMatrixTransportV node alpha
      (Sum.inl i) (Sum.inr ())

theorem hasDerivAt_mobiusGammaXiAntiCausalWardPacketTransportV_zero
    {n : ℕ} {node : Fin n → ℂ} (hnode : ∀ i, 0 < (node i).re)
    (i : Fin n) :
    HasDerivAt
      (fun alpha =>
        mobiusGammaXiAntiCausalWardPacketTransportV node alpha i)
      (continuedXiAntiCausalWardColumn node i) 0 :=
  by
    simpa only [mobiusGammaXiAntiCausalWardPacketTransportV,
      mobiusGammaXiAntiCausalWardMatrixTransportV_boundaryColumn] using!
      hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero (hnode i)

/-- Complete source-transport package.  The same actual Möbius Fisher tangent has the four-unit
critical norm and reconstructs the completed Xi source current; the canonical strict-right
Wiener--Hopf factor of that source has a non-diagonal Julia transport whose tangent is the
continued anti-causal Ward column. -/
theorem mobiusGammaFourUnitTangent_to_continuedXiAntiCausalWardColumn :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
      else 0)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 4) ∧
    (∀ ⦃sigma u : ℝ⦄ (hsigma : 1 < sigma) (hu : 0 ≤ u),
      inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
          (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) =
        GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ)) ∧
    (∀ ⦃sigma u : ℝ⦄ (_hsigma : 1 < sigma) (_hu : 0 ≤ u),
      squarefreeMobiusGammaXiWardTransportV
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
          (fun v =>
            GaloisForLFunctions.squarefreeFisherScore
              (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v)
          (u : ℂ) =
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter sigma u : ℂ))) ∧
    (∀ ⦃n : ℕ⦄ ⦃node : Fin n → ℂ⦄ (_hnode : ∀ i, 0 < (node i).re)
        (i : Fin n),
      HasDerivAt
        (fun alpha =>
          mobiusGammaXiAntiCausalWardPacketTransportV node alpha i)
        (continuedXiAntiCausalWardColumn node i) 0) := by
  exact ⟨tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq,
    fun {_ _} hsigma hu =>
      inner_fisherTangent_damped_eq_squarefreeFisherScore hsigma hu,
    fun {_ _} hsigma hu =>
      squarefreeMobiusGammaXiWardTransportV_actualTangent hsigma hu,
    fun {_} {_} hnode i =>
      hasDerivAt_mobiusGammaXiAntiCausalWardPacketTransportV_zero hnode i⟩

end

end RHTower
