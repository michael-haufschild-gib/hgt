import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyThetaMirrorScattering
import GaloisForLFunctions.RHTower.ThetaCuspHawkingNonlinearChiralTeukolskyReturnProducer

/-!
# Topological Darboux--Starobinsky spectral flow

At fixed `s = u x²`, Birmingham--Mokhtari's exact `d = 4` scalar and vector
gravitational potentials form a Darboux pair.  Their reduced superpotential has
algebraic constant `Q(Q + 2)/6`, fixing `Q(Q + 2)` as the curvature `-1`
Teukolsky--Starobinsky polynomial.

Theta reflection gives a signed Starobinsky defect with one positive confluence
mass in every tilted divisor fibre.  At that mass, the exact AIME chiral source
component still has nonzero reflected transfer.  The last statement concerns
that evaluated component, not the unevaluated remainder of the full nonlinear
Einstein--Teukolsky source.
-/

open Complex Real

namespace RHTower

noncomputable section

def d4TopologicalDarbouxRadialPolynomial (s : ℝ) : ℝ → ℝ :=
  (fun _ => s) - id ^ 2 - id ^ 3

def d4TopologicalDarbouxAlgebraicConstant (Q : ℝ) : ℝ :=
  Q * (Q + 2) / 6

def d4TopologicalDarbouxReducedSuperpotential (Q s : ℝ) : ℝ → ℝ :=
  (fun _ => d4TopologicalDarbouxAlgebraicConstant Q) +
    fun x => 3 * (d4TopologicalDarbouxRadialPolynomial s /
      fun y => (Q + 2) + 3 * y) x

lemma hasDerivAt_d4TopologicalDarbouxRadialPolynomial (s x : ℝ) :
    HasDerivAt (d4TopologicalDarbouxRadialPolynomial s)
      (-2 * x - 3 * x ^ 2) x := by
  have h := (((hasDerivAt_const (x := x) s).sub ((hasDerivAt_id x).pow 2)).sub
    ((hasDerivAt_id x).pow 3))
  change HasDerivAt (d4TopologicalDarbouxRadialPolynomial s)
    ((0 - 2 * x ^ (2 - 1) * 1) - 3 * x ^ (3 - 1) * 1) x at h
  convert h using 1
  norm_num

lemma d4ScalarU_fixedScale (Q s x : ℝ) (hx : x ≠ 0) :
    d4ScalarU Q x (s / x ^ 2) =
      16 * (18 * s + 9 * x ^ 3 + 9 * (Q + 2) * x ^ 2 +
        3 * (Q + 2) ^ 2 * x + (Q + 2) ^ 2 * Q) := by
  unfold d4ScalarU
  field_simp [hx]
  ring

lemma d4ScalarBracket_fixedScale (Q s x : ℝ) (hx : x ≠ 0) :
    d4ScalarBracket Q x (s / x ^ 2) =
      (18 * s + 9 * x ^ 3 + 9 * (Q + 2) * x ^ 2 +
        3 * (Q + 2) ^ 2 * x + (Q + 2) ^ 2 * Q) /
        ((Q + 2) + 3 * x) ^ 2 := by
  rw [d4ScalarBracket, d4ScalarU_fixedScale Q s x hx]
  by_cases hD : (Q + 2) + 3 * x = 0
  · simp [hD]
  · field_simp [hD]

lemma d4TopologicalDarboux_bracket_sum
    (Q s x : ℝ) (hx : x ≠ 0) (hD : (Q + 2) + 3 * x ≠ 0) :
    d4ScalarBracket Q x (s / x ^ 2) + d4VectorBracket Q x =
      2 * (Q * (Q + 2) * ((Q + 2) + 3 * x) +
        9 * d4TopologicalDarbouxRadialPolynomial s x) /
        ((Q + 2) + 3 * x) ^ 2 := by
  rw [d4ScalarBracket_fixedScale Q s x hx]
  apply (eq_div_iff (pow_ne_zero 2 hD)).2
  rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
  unfold d4VectorBracket d4TopologicalDarbouxRadialPolynomial
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  ring

lemma d4TopologicalDarboux_bracket_difference
    (Q s x : ℝ) (hx : x ≠ 0) (hD : (Q + 2) + 3 * x ≠ 0) :
    d4ScalarBracket Q x (s / x ^ 2) - d4VectorBracket Q x =
      6 * (3 * s + 2 * (Q + 2) * x + 3 * (Q + 3) * x ^ 2 + 6 * x ^ 3) /
        ((Q + 2) + 3 * x) ^ 2 := by
  rw [d4ScalarBracket_fixedScale Q s x hx]
  apply (eq_div_iff (pow_ne_zero 2 hD)).2
  rw [sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
  unfold d4VectorBracket
  ring

theorem d4TopologicalDarboux_average_factorization
    (Q s x : ℝ) (hx : x ≠ 0) (hD : (Q + 2) + 3 * x ≠ 0) :
    d4TopologicalDarbouxRadialPolynomial s x *
        (d4ScalarBracket Q x (s / x ^ 2) + d4VectorBracket Q x) / 2 =
      d4TopologicalDarbouxReducedSuperpotential Q s x ^ 2 -
        d4TopologicalDarbouxAlgebraicConstant Q ^ 2 := by
  rw [d4TopologicalDarboux_bracket_sum Q s x hx hD]
  unfold d4TopologicalDarbouxReducedSuperpotential
    d4TopologicalDarbouxAlgebraicConstant
  simp only [Pi.add_apply, Pi.div_apply]
  field_simp [hD]
  ring

theorem d4TopologicalDarboux_scalar_factorization
    (Q s x : ℝ) (hx : x ≠ 0) (hD : (Q + 2) + 3 * x ≠ 0) :
    d4TopologicalDarbouxRadialPolynomial s x *
        d4ScalarBracket Q x (s / x ^ 2) =
      d4TopologicalDarbouxReducedSuperpotential Q s x ^ 2 -
        d4TopologicalDarbouxAlgebraicConstant Q ^ 2 +
        d4TopologicalDarbouxRadialPolynomial s x *
          (d4ScalarBracket Q x (s / x ^ 2) - d4VectorBracket Q x) / 2 := by
  have havg := d4TopologicalDarboux_average_factorization Q s x hx hD
  linear_combination havg

theorem d4TopologicalDarboux_vector_factorization
    (Q s x : ℝ) (hx : x ≠ 0) (hD : (Q + 2) + 3 * x ≠ 0) :
    d4TopologicalDarbouxRadialPolynomial s x * d4VectorBracket Q x =
      d4TopologicalDarbouxReducedSuperpotential Q s x ^ 2 -
        d4TopologicalDarbouxAlgebraicConstant Q ^ 2 -
        d4TopologicalDarbouxRadialPolynomial s x *
          (d4ScalarBracket Q x (s / x ^ 2) - d4VectorBracket Q x) / 2 := by
  have havg := d4TopologicalDarboux_average_factorization Q s x hx hD
  linear_combination havg

theorem hasDerivAt_d4TopologicalDarbouxReducedSuperpotential
    (Q s x : ℝ) (hx : x ≠ 0) (hD : (Q + 2) + 3 * x ≠ 0) :
    HasDerivAt (d4TopologicalDarbouxReducedSuperpotential Q s)
      (-(d4ScalarBracket Q x (s / x ^ 2) - d4VectorBracket Q x) / 2) x := by
  have hp := hasDerivAt_d4TopologicalDarbouxRadialPolynomial s x
  have hden : HasDerivAt (fun y : ℝ => (Q + 2) + 3 * y) 3 x := by
    have h := (hasDerivAt_const (x := x) (Q + 2)).add
      ((hasDerivAt_id x).const_mul 3)
    change HasDerivAt (fun y : ℝ => (Q + 2) + 3 * y) (0 + 3 * 1) x at h
    convert h using 1
    norm_num
  have hquot := hp.div hden hD
  have hW :=
    (hasDerivAt_const (x := x) (d4TopologicalDarbouxAlgebraicConstant Q)).add
      (hquot.const_mul 3)
  change HasDerivAt (d4TopologicalDarbouxReducedSuperpotential Q s) _ x
  have hW' : HasDerivAt (d4TopologicalDarbouxReducedSuperpotential Q s)
      (0 + 3 * (((-2 * x - 3 * x ^ 2) * ((Q + 2) + 3 * x) -
        d4TopologicalDarbouxRadialPolynomial s x * 3) /
          ((Q + 2) + 3 * x) ^ 2)) x := by
    simpa only [d4TopologicalDarbouxReducedSuperpotential] using hW
  convert hW' using 1
  rw [d4TopologicalDarboux_bracket_difference Q s x hx hD]
  unfold d4TopologicalDarbouxRadialPolynomial
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  field_simp [hD]
  ring

def d4TopologicalTeukolskyStarobinskyConstant (M Q omega : ℂ) : ℂ :=
  Q * (Q + 2) + 12 * Complex.I * M * omega

lemma d4TopologicalTeukolskyStarobinskyConstant_eq_shift
    (M Q omega : ℂ) :
    d4TopologicalTeukolskyStarobinskyConstant M Q omega =
      teukolskyStarobinskyConstant M (Q + 2) omega := by
  unfold d4TopologicalTeukolskyStarobinskyConstant teukolskyStarobinskyConstant
  ring

def d4BMXiThetaMirrorTopologicalStarobinskyWeight
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℝ :=
  let Q := d4BMXiReflectedRealPairMediatorAngularQ q
  Q * (Q + 2) + 12 * M * (4 * n + 3 - (q.1 : ℂ).re)

lemma d4BMXiThetaMirrorTopologicalStarobinskyWeight_eq_complex
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4TopologicalTeukolskyStarobinskyConstant (M : ℂ)
        (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ)
        (d4BMXiReflectedRealPairFrequency n q) =
      (d4BMXiThetaMirrorTopologicalStarobinskyWeight n M q : ℂ) := by
  rw [d4BMXiReflectedRealPairFrequency_eq]
  unfold d4TopologicalTeukolskyStarobinskyConstant
    d4BMXiThetaMirrorTopologicalStarobinskyWeight
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

def d4BMXiThetaMirrorCriticalMass (q : XiZeroCopy) : ℝ :=
  (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) / 3

def d4BMXiThetaMirrorTopologicalStarobinskyDefect
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℝ :=
  d4BMXiThetaMirrorTopologicalStarobinskyWeight n M q -
    d4BMXiThetaMirrorTopologicalStarobinskyWeight n M
      (xiZeroCopyReflectEquiv q)

theorem d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorTopologicalStarobinskyDefect n M q =
      24 * ((q.1 : ℂ).re - 1 / 2) *
        (d4BMXiThetaMirrorCriticalMass q - M) := by
  unfold d4BMXiThetaMirrorTopologicalStarobinskyDefect
    d4BMXiThetaMirrorTopologicalStarobinskyWeight
  rw [d4BMXiReflectedRealPairMediatorAngularQ_reflect,
    xiZeroCopyReflectEquiv_rho]
  unfold d4BMXiThetaMirrorCriticalMass
    d4BMXiReflectedRealPairMediatorAngularQ
  simp only [Complex.sub_re, Complex.one_re]
  ring

lemma d4BMXiThetaMirrorCriticalMass_pos (q : XiZeroCopy) :
    0 < d4BMXiThetaMirrorCriticalMass q := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  unfold d4BMXiThetaMirrorCriticalMass
  exact div_pos (mul_pos hstrip.1 (by linarith)) (by norm_num)

theorem d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq_zero_iff_of_tilted
    (n : ℕ) (M : ℝ) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorTopologicalStarobinskyDefect n M q = 0 ↔
      M = d4BMXiThetaMirrorCriticalMass q := by
  rw [d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · norm_num at h
      exfalso
      apply htilt
      linarith
    · linarith
  · intro h
    rw [h]
    ring

theorem d4BMXiThetaMirrorTopologicalStarobinsky_two_mass_rigidity
    (n : ℕ) (M₁ M₂ : ℝ) (q : XiZeroCopy) (hM : M₁ ≠ M₂)
    (h₁ : d4BMXiThetaMirrorTopologicalStarobinskyWeight n M₁ q =
      d4BMXiThetaMirrorTopologicalStarobinskyWeight n M₁
        (xiZeroCopyReflectEquiv q))
    (h₂ : d4BMXiThetaMirrorTopologicalStarobinskyWeight n M₂ q =
      d4BMXiThetaMirrorTopologicalStarobinskyWeight n M₂
        (xiZeroCopyReflectEquiv q)) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra htilt
  have hz₁ : d4BMXiThetaMirrorTopologicalStarobinskyDefect n M₁ q = 0 :=
    sub_eq_zero.mpr h₁
  have hz₂ : d4BMXiThetaMirrorTopologicalStarobinskyDefect n M₂ q = 0 :=
    sub_eq_zero.mpr h₂
  have hm₁ :=
    (d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq_zero_iff_of_tilted
      n M₁ q htilt).mp hz₁
  have hm₂ :=
    (d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq_zero_iff_of_tilted
      n M₂ q htilt).mp hz₂
  exact hM (hm₁.trans hm₂.symm)

def d4BMXiThetaMirrorAIMEChiralKernel (q : XiZeroCopy) : ℝ :=
  let Q := d4BMXiReflectedRealPairMediatorAngularQ q
  (-3 : ℝ) / (Q * (Q + 2))

lemma d4BMXiReflectedRealPairMediatorAngularQ_ne_zero (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q ≠ 0 :=
  ne_of_lt (d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q).2

lemma d4BMXiReflectedRealPairMediatorAngularQ_add_two_ne_zero (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q + 2 ≠ 0 := by
  have h := (d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q).1
  linarith

theorem d4BMXiThetaMirrorAIMEChiralKernel_eq_complex (q : XiZeroCopy) :
    d4FundamentalQNMChiralSourceKernel
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) =
      (d4BMXiThetaMirrorAIMEChiralKernel q : ℂ) := by
  rw [d4FundamentalQNMChiralSourceKernel_eq]
  unfold d4ThetaTeukolskyAngularQ
  rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue]
  · unfold d4BMXiThetaMirrorAIMEChiralKernel
    push_cast
    rfl
  · unfold d4ThetaTeukolskyAngularQ
    rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue]
    exact_mod_cast d4BMXiReflectedRealPairMediatorAngularQ_ne_zero q
  · unfold d4ThetaTeukolskyAngularQ
    rw [d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue]
    exact_mod_cast d4BMXiReflectedRealPairMediatorAngularQ_add_two_ne_zero q

def d4BMXiThetaMirrorAIMEDenominator (q : XiZeroCopy) : ℝ :=
  let a := (q.1 : ℂ).re
  a * (1 - a) * (2 - a) * (3 - a) * (a + 1) * (a + 2)

lemma d4BMXiThetaMirrorAIMEDenominator_pos (q : XiZeroCopy) :
    0 < d4BMXiThetaMirrorAIMEDenominator q := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  unfold d4BMXiThetaMirrorAIMEDenominator
  have h1 : 0 < 1 - (q.1 : ℂ).re := by linarith
  have h2 : 0 < 2 - (q.1 : ℂ).re := by linarith
  have h3 : 0 < 3 - (q.1 : ℂ).re := by linarith
  have hp1 : 0 < (q.1 : ℂ).re + 1 := by linarith
  have hp2 : 0 < (q.1 : ℂ).re + 2 := by linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hstrip.1 h1) h2) h3) hp1) hp2

def d4BMXiThetaMirrorAIMEChiralKernelDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiThetaMirrorAIMEChiralKernel q -
    d4BMXiThetaMirrorAIMEChiralKernel (xiZeroCopyReflectEquiv q)

theorem d4BMXiThetaMirrorAIMEChiralKernelDefect_eq (q : XiZeroCopy) :
    d4BMXiThetaMirrorAIMEChiralKernelDefect q =
      24 * ((q.1 : ℂ).re - 1 / 2) /
        d4BMXiThetaMirrorAIMEDenominator q := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : (q.1 : ℂ).re ≠ 0 := ne_of_gt hstrip.1
  have h1a : 1 - (q.1 : ℂ).re ≠ 0 := by linarith
  have h2a : 2 - (q.1 : ℂ).re ≠ 0 := by linarith
  have h3a : 3 - (q.1 : ℂ).re ≠ 0 := by linarith
  have ha1 : (q.1 : ℂ).re + 1 ≠ 0 := by linarith
  have ha2 : (q.1 : ℂ).re + 2 ≠ 0 := by linarith
  have hqfactor :
      ((2 - (q.1 : ℂ).re) * ((q.1 : ℂ).re - 1)) *
          (((2 - (q.1 : ℂ).re) * ((q.1 : ℂ).re - 1)) + 2) =
        -(q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
          (2 - (q.1 : ℂ).re) * (3 - (q.1 : ℂ).re) := by
    ring
  have hrfactor :
      (-(q.1 : ℂ).re * ((q.1 : ℂ).re + 1)) *
          (-(q.1 : ℂ).re * ((q.1 : ℂ).re + 1) + 2) =
        -(q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
          ((q.1 : ℂ).re + 1) * ((q.1 : ℂ).re + 2) := by
    ring
  unfold d4BMXiThetaMirrorAIMEChiralKernelDefect
    d4BMXiThetaMirrorAIMEChiralKernel
  rw [d4BMXiReflectedRealPairMediatorAngularQ_reflect]
  unfold d4BMXiThetaMirrorAIMEDenominator
    d4BMXiReflectedRealPairMediatorAngularQ
  simp only
  rw [hqfactor, hrfactor]
  field_simp [ha, h1a, h2a, h3a, ha1, ha2]
  ring

theorem d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff (q : XiZeroCopy) :
    d4BMXiThetaMirrorAIMEChiralKernelDefect q ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro h hline
    rw [d4BMXiThetaMirrorAIMEChiralKernelDefect_eq, hline] at h
    norm_num at h
  · intro htilt
    rw [d4BMXiThetaMirrorAIMEChiralKernelDefect_eq]
    exact div_ne_zero
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr htilt))
      (ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q))

theorem d4BMXiThetaMirrorAIMEOrientedFlow_eq (q : XiZeroCopy) :
    ((q.1 : ℂ).re - 1 / 2) * d4BMXiThetaMirrorAIMEChiralKernelDefect q =
      24 * ((q.1 : ℂ).re - 1 / 2) ^ 2 /
        d4BMXiThetaMirrorAIMEDenominator q := by
  rw [d4BMXiThetaMirrorAIMEChiralKernelDefect_eq]
  ring

theorem d4BMXiThetaMirrorAIMEOrientedFlow_pos_iff (q : XiZeroCopy) :
    0 < ((q.1 : ℂ).re - 1 / 2) *
        d4BMXiThetaMirrorAIMEChiralKernelDefect q ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [d4BMXiThetaMirrorAIMEOrientedFlow_eq]
  constructor
  · intro h hline
    rw [hline] at h
    norm_num at h
  · intro htilt
    exact div_pos
      (mul_pos (by norm_num) (sq_pos_of_ne_zero (sub_ne_zero.mpr htilt)))
      (d4BMXiThetaMirrorAIMEDenominator_pos q)

def d4BMXiThetaMirrorComponentMixingInvariant
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℝ × ℝ :=
  (d4BMXiThetaMirrorTopologicalStarobinskyDefect n M q / 2,
    d4BMXiThetaMirrorAIMEChiralKernelDefect q / 2)

theorem d4BMXiThetaMirrorComponentMixingInvariant_eq_zero_iff
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorComponentMixingInvariant n M q = (0, 0) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hs := congrArg Prod.snd h
    simp only [d4BMXiThetaMirrorComponentMixingInvariant] at hs
    by_contra htilt
    have hn := (d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff q).2 htilt
    exact hn (by linarith)
  · intro hline
    apply Prod.ext
    · simp only [d4BMXiThetaMirrorComponentMixingInvariant]
      rw [d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq, hline]
      ring
    · simp only [d4BMXiThetaMirrorComponentMixingInvariant]
      rw [d4BMXiThetaMirrorAIMEChiralKernelDefect_eq, hline]
      norm_num

theorem d4BMXiThetaMirrorComponentMixingInvariant_at_criticalMass
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorComponentMixingInvariant n
        (d4BMXiThetaMirrorCriticalMass q) q =
      (0, d4BMXiThetaMirrorAIMEChiralKernelDefect q / 2) := by
  apply Prod.ext
  · simp only [d4BMXiThetaMirrorComponentMixingInvariant]
    rw [d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq]
    ring
  · rfl

end

end RHTower
