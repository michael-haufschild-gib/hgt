import GaloisForLFunctions.RHTower.GaussHodgeWeilKreinDecomposition
import GaloisForLFunctions.RHTower.XiQuotientRealDecay

/-!
# The fundamental symmetry of the Weil-Pontryagin form

The Krein signature decomposition presents the diagonal Weil polarization as a difference of two
convergent sums of squares.  This module identifies the geometry behind that signature: the
parity flip `J F = F ∘ conj` is a *fundamental symmetry* of the Weil form in the sense of Krein
space theory, unconditionally.

* `J` is an involution, `J`-twisting the second slot turns the Weil form into the literal
  `ell^2` inner product of divisor evaluations (`xiWeilPolarization_parityFlip_right`), and `J`
  is self-adjoint for the form (`xiWeilPolarization_parityFlip_symm`).  In particular the GNS
  Hilbert space that a square realization would generate *already exists* unconditionally: it is
  the divisor-coordinate `ell^2` space carried by the `J`-metric, and every square-summable test
  satisfies the `J`-metric square-sum law (`xiWeilParityFlip_hasSum_sq`).
* The associated parity decomposition is `W`-orthogonal: divisor-even and divisor-odd tests are
  orthogonal for the full sesquilinear form (`xiWeilPolarization_even_odd`), the form restricted
  to divisor-even tests is exactly the positive `ell^2` diagonal
  (`xiWeilPolarization_diagonal_of_divisorEven`, giving the unconditional even-sector square
  realization `xiWeilEvenSector_hasSum_sq`), and restricted to divisor-odd tests it is minus the
  `ell^2` diagonal (`xiWeilPolarization_diagonal_of_divisorOdd`).
* Every square-summable diagonal value splits as even-sector energy minus odd-sector energy at
  the level of complex values, not just real parts
  (`xiWeilPolarization_parity_decomposition`, `xiWeilPolarization_self_eq_parity_energies`); in
  particular the diagonal Weil form is real-valued (`xiWeilPolarization_self_im`).
* RH is exactly the degeneracy of the whole structure: the Riemann hypothesis holds iff every
  divisor-odd test vanishes identically on the divisor
  (`riemannHypothesis_iff_forall_divisorOdd_eval_eq_zero`), iff the Weil form is invariant under
  `J`-twisting (`riemannHypothesis_iff_polarization_parityFlip_invariant`) — that is, iff the
  Weil form coincides with the positive `ell^2` form it is `J`-equivalent to.

No positivity input and no zero-free region is used anywhere: every statement except the RH
equivalences is unconditional, and the equivalences use only an indicator test at a hypothetical
off-line zero.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The parity flip and the divisor parity classes -/

/-- The parity flip `J F = F ∘ conj` on Weil test functions. -/
def xiWeilParityFlip (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F ((starRingEnd ℂ) z)

/-- The parity flip is an involution. -/
theorem xiWeilParityFlip_parityFlip (F : ℂ → ℂ) :
    xiWeilParityFlip (xiWeilParityFlip F) = F := by
  funext z
  rw [xiWeilParityFlip, xiWeilParityFlip, Complex.conj_conj]

/-- A test is divisor-even when its divisor evaluations are invariant under the critical-line
reflection, which acts as conjugation in centered spectral coordinates. -/
def XiWeilDivisorEven (F : ℂ → ℂ) : Prop :=
  ∀ q : XiZeroCopy,
    F ((starRingEnd ℂ) (xiSpectralPoint q)) = F (xiSpectralPoint q)

/-- A test is divisor-odd when the critical-line reflection negates its divisor evaluations. -/
def XiWeilDivisorOdd (F : ℂ → ℂ) : Prop :=
  ∀ q : XiZeroCopy,
    F ((starRingEnd ℂ) (xiSpectralPoint q)) = -F (xiSpectralPoint q)

/-- The even part of a test under the parity flip. -/
def xiWeilEvenPart (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F z + F ((starRingEnd ℂ) z)) / 2

/-- The odd part of a test under the parity flip. -/
def xiWeilOddPart (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F z - F ((starRingEnd ℂ) z)) / 2

theorem xiWeilEvenPart_add_oddPart (F : ℂ → ℂ) (z : ℂ) :
    xiWeilEvenPart F z + xiWeilOddPart F z = F z := by
  rw [xiWeilEvenPart, xiWeilOddPart]
  ring

/-- The parity flip is the fundamental symmetry of the parity decomposition: it fixes the even
part and negates the odd part. -/
theorem xiWeilParityFlip_eq_evenPart_sub_oddPart (F : ℂ → ℂ) (z : ℂ) :
    xiWeilParityFlip F z = xiWeilEvenPart F z - xiWeilOddPart F z := by
  rw [xiWeilParityFlip, xiWeilEvenPart, xiWeilOddPart]
  ring

theorem xiWeilEvenPart_divisorEven (F : ℂ → ℂ) :
    XiWeilDivisorEven (xiWeilEvenPart F) := by
  intro q
  rw [xiWeilEvenPart, xiWeilEvenPart, Complex.conj_conj]
  ring

theorem xiWeilOddPart_divisorOdd (F : ℂ → ℂ) :
    XiWeilDivisorOdd (xiWeilOddPart F) := by
  intro q
  rw [xiWeilOddPart, xiWeilOddPart, Complex.conj_conj]
  ring

/-- On the divisor the even part is half the Krein pair sum. -/
theorem xiWeilEvenPart_spectral (F : ℂ → ℂ) (q : XiZeroCopy) :
    xiWeilEvenPart F (xiSpectralPoint q) = xiWeilPairSum F q / 2 := by
  rw [xiWeilEvenPart, xiWeilPairSum, xiSpectralPoint_lineConj]

/-- On the divisor the odd part is half the Krein pair difference. -/
theorem xiWeilOddPart_spectral (F : ℂ → ℂ) (q : XiZeroCopy) :
    xiWeilOddPart F (xiSpectralPoint q) = xiWeilPairDif F q / 2 := by
  rw [xiWeilOddPart, xiWeilPairDif, xiSpectralPoint_lineConj]

theorem xiWeilEvenPart_squareSummable {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    XiWeilSquareSummable (xiWeilEvenPart F) := by
  rw [XiWeilSquareSummable]
  refine ((xiWeilPairSum_squareSummable hF).div_const 4).congr fun q => ?_
  rw [xiWeilEvenPart_spectral, norm_div, div_pow]
  norm_num

theorem xiWeilOddPart_squareSummable {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    XiWeilSquareSummable (xiWeilOddPart F) := by
  rw [XiWeilSquareSummable]
  refine ((xiWeilPairDif_squareSummable hF).div_const 4).congr fun q => ?_
  rw [xiWeilOddPart_spectral, norm_div, div_pow]
  norm_num

/-! ## The J-metric is the divisor ell^2 inner product -/

/-- Twisting the second slot by the parity flip turns the Weil polarization into the plain
`ell^2` pairing of divisor evaluations, unconditionally. -/
theorem xiWeilPolarization_parityFlip_right (F G : ℂ → ℂ) :
    xiWeilPolarization F (xiWeilParityFlip G) =
      ∑' q : XiZeroCopy,
        F (xiSpectralPoint q) * (starRingEnd ℂ) (G (xiSpectralPoint q)) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp, xiWeilParityFlip, Complex.conj_conj]

/-- The `J`-metric diagonal is the divisor `ell^2` energy, term by term. -/
theorem xiWeilPolarization_parityFlip_diagonal (F : ℂ → ℂ) :
    xiWeilPolarization F (xiWeilParityFlip F) =
      ∑' q : XiZeroCopy, ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) := by
  rw [xiWeilPolarization_parityFlip_right]
  apply tsum_congr
  intro q
  simpa [Complex.sq_norm] using Complex.mul_conj (F (xiSpectralPoint q))

/-- The parity flip is self-adjoint for the Weil polarization, unconditionally. -/
theorem xiWeilPolarization_parityFlip_symm (F G : ℂ → ℂ) :
    xiWeilPolarization (xiWeilParityFlip F) G =
      xiWeilPolarization F (xiWeilParityFlip G) := by
  rw [xiWeilPolarization_parityFlip_right]
  unfold xiWeilPolarization
  have hpt : ∀ q : XiZeroCopy,
      xiWeilParityFlip F (xiSpectralPoint q) * xiWeilSharp G (xiSpectralPoint q) =
        (fun r : XiZeroCopy =>
          F (xiSpectralPoint r) * (starRingEnd ℂ) (G (xiSpectralPoint r)))
          (xiZeroCopyLineConjEquiv q) := by
    intro q
    show xiWeilParityFlip F (xiSpectralPoint q) * xiWeilSharp G (xiSpectralPoint q) =
      F (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) *
        (starRingEnd ℂ) (G (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))
    rw [xiSpectralPoint_lineConj, xiWeilParityFlip, xiWeilSharp]
  rw [tsum_congr hpt]
  exact xiZeroCopyLineConjEquiv.tsum_eq
    (fun r : XiZeroCopy =>
      F (xiSpectralPoint r) * (starRingEnd ℂ) (G (xiSpectralPoint r)))

/-- **The unconditional GNS law of the `J`-metric**: every square-summable test satisfies the
square-sum identity for the parity-twisted diagonal.  The Hilbert space a square realization
would generate exists already; only the twist separates it from the Weil form itself. -/
theorem xiWeilParityFlip_hasSum_sq {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    HasSum (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ 2)
      ((xiWeilPolarization F (xiWeilParityFlip F)).re) := by
  have hsumC : Summable (fun q : XiZeroCopy =>
      ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [Function.comp_apply] using!
      hF.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hre : (xiWeilPolarization F (xiWeilParityFlip F)).re =
      ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 := by
    rw [xiWeilPolarization_parityFlip_diagonal, Complex.re_tsum hsumC]
    exact tsum_congr fun q => Complex.ofReal_re _
  rw [hre]
  exact hF.hasSum

/-- The `J`-metric is positive semidefinite on square-summable tests, unconditionally. -/
theorem xiWeilPolarization_parityFlip_re_nonneg {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) :
    0 ≤ (xiWeilPolarization F (xiWeilParityFlip F)).re := by
  rw [← (xiWeilParityFlip_hasSum_sq hF).tsum_eq]
  exact tsum_nonneg fun q => sq_nonneg _

/-! ## Parity orthogonality -/

/-- A divisor sequence negated by the critical-line reflection has vanishing sum. -/
theorem tsum_eq_zero_of_lineConj_neg {f : XiZeroCopy → ℂ}
    (hf : ∀ q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q) = -f q) :
    ∑' q : XiZeroCopy, f q = 0 := by
  have h1 : ∑' q : XiZeroCopy, f q =
      ∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q) :=
    (xiZeroCopyLineConjEquiv.tsum_eq f).symm
  rw [tsum_congr hf, tsum_neg] at h1
  have h2 : (2 : ℂ) * ∑' q : XiZeroCopy, f q = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The `ell^2` pairing of a divisor-even against a divisor-odd test vanishes. -/
theorem tsum_even_mul_conj_odd {E O : ℂ → ℂ}
    (hE : XiWeilDivisorEven E) (hO : XiWeilDivisorOdd O) :
    ∑' q : XiZeroCopy,
      E (xiSpectralPoint q) * (starRingEnd ℂ) (O (xiSpectralPoint q)) = 0 := by
  apply tsum_eq_zero_of_lineConj_neg
  intro q
  show E (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) *
      (starRingEnd ℂ) (O (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) =
    -(E (xiSpectralPoint q) * (starRingEnd ℂ) (O (xiSpectralPoint q)))
  rw [xiSpectralPoint_lineConj, hE q, hO q, map_neg]
  ring

/-- **Parity orthogonality**: divisor-even and divisor-odd tests are orthogonal for the full
sesquilinear Weil polarization, unconditionally. -/
theorem xiWeilPolarization_even_odd {E O : ℂ → ℂ}
    (hE : XiWeilDivisorEven E) (hO : XiWeilDivisorOdd O) :
    xiWeilPolarization E O = 0 := by
  unfold xiWeilPolarization
  have hpt : ∀ q : XiZeroCopy,
      E (xiSpectralPoint q) * xiWeilSharp O (xiSpectralPoint q) =
        -(E (xiSpectralPoint q) * (starRingEnd ℂ) (O (xiSpectralPoint q))) := by
    intro q
    rw [xiWeilSharp, hO q, map_neg]
    ring
  rw [tsum_congr hpt, tsum_neg, tsum_even_mul_conj_odd hE hO, neg_zero]

theorem xiWeilPolarization_odd_even {E O : ℂ → ℂ}
    (hE : XiWeilDivisorEven E) (hO : XiWeilDivisorOdd O) :
    xiWeilPolarization O E = 0 := by
  rw [xiWeilPolarization_conj_symm E O, xiWeilPolarization_even_odd hE hO, map_zero]

/-! ## The two sector diagonals -/

/-- On divisor-even tests the Weil form is the positive `ell^2` diagonal, term by term and
unconditionally: the even sector needs no Riemann hypothesis to be a sum of squares. -/
theorem xiWeilPolarization_diagonal_of_divisorEven {F : ℂ → ℂ}
    (hE : XiWeilDivisorEven F) :
    xiWeilPolarization F F =
      ∑' q : XiZeroCopy, ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [xiWeilSharp, hE q]
  simpa [Complex.sq_norm] using Complex.mul_conj (F (xiSpectralPoint q))

/-- On divisor-odd tests the Weil form is minus the `ell^2` diagonal: the odd sector is the
entire negative Krein sector. -/
theorem xiWeilPolarization_diagonal_of_divisorOdd {F : ℂ → ℂ}
    (hO : XiWeilDivisorOdd F) :
    xiWeilPolarization F F =
      -∑' q : XiZeroCopy, ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) := by
  unfold xiWeilPolarization
  rw [← tsum_neg]
  apply tsum_congr
  intro q
  rw [xiWeilSharp, hO q, map_neg]
  have hmc : F (xiSpectralPoint q) * (starRingEnd ℂ) (F (xiSpectralPoint q)) =
      ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.sq_norm] using Complex.mul_conj (F (xiSpectralPoint q))
  rw [mul_neg, hmc]

/-- **The unconditional even-sector square realization**: on divisor-even square-summable tests
the diagonal Weil value is a convergent sum of squares with no hypothesis.  This is the half of
the GNS construction that exists without RH. -/
theorem xiWeilEvenSector_hasSum_sq {F : ℂ → ℂ} (hE : XiWeilDivisorEven F)
    (hF : XiWeilSquareSummable F) :
    HasSum (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ 2)
      ((xiWeilPolarization F F).re) := by
  have hsumC : Summable (fun q : XiZeroCopy =>
      ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [Function.comp_apply] using!
      hF.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hre : (xiWeilPolarization F F).re =
      ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 := by
    rw [xiWeilPolarization_diagonal_of_divisorEven hE, Complex.re_tsum hsumC]
    exact tsum_congr fun q => Complex.ofReal_re _
  rw [hre]
  exact hF.hasSum

/-! ## The parity decomposition of every square-summable diagonal -/

/-- **The `W`-orthogonal parity decomposition**: every square-summable diagonal Weil value is
the even-part diagonal plus the odd-part diagonal — the cross terms vanish exactly.  Combined
with the sector diagonals this is the Krein signature decomposition at the level of complex
values. -/
theorem xiWeilPolarization_parity_decomposition {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) :
    xiWeilPolarization F F =
      xiWeilPolarization (xiWeilEvenPart F) (xiWeilEvenPart F) +
        xiWeilPolarization (xiWeilOddPart F) (xiWeilOddPart F) := by
  have he := xiWeilEvenPart_squareSummable hF
  have ho := xiWeilOddPart_squareSummable hF
  have hEO := xiWeilPolarization_even_odd
    (xiWeilEvenPart_divisorEven F) (xiWeilOddPart_divisorOdd F)
  have hOE := xiWeilPolarization_odd_even
    (xiWeilEvenPart_divisorEven F) (xiWeilOddPart_divisorOdd F)
  have hsplit : F = xiWeilEvenPart F + xiWeilOddPart F := by
    funext z
    rw [Pi.add_apply, xiWeilEvenPart_add_oddPart]
  have hsum : XiWeilSquareSummable (xiWeilEvenPart F + xiWeilOddPart F) := he.add ho
  calc xiWeilPolarization F F
      = xiWeilPolarization (xiWeilEvenPart F + xiWeilOddPart F)
          (xiWeilEvenPart F + xiWeilOddPart F) := by rw [← hsplit]
    _ = xiWeilPolarization (xiWeilEvenPart F) (xiWeilEvenPart F + xiWeilOddPart F) +
        xiWeilPolarization (xiWeilOddPart F) (xiWeilEvenPart F + xiWeilOddPart F) :=
        xiWeilPolarization_add_left he ho hsum
    _ = (xiWeilPolarization (xiWeilEvenPart F) (xiWeilEvenPart F) +
          xiWeilPolarization (xiWeilEvenPart F) (xiWeilOddPart F)) +
        (xiWeilPolarization (xiWeilOddPart F) (xiWeilEvenPart F) +
          xiWeilPolarization (xiWeilOddPart F) (xiWeilOddPart F)) := by
        rw [xiWeilPolarization_add_right he he ho, xiWeilPolarization_add_right ho he ho]
    _ = xiWeilPolarization (xiWeilEvenPart F) (xiWeilEvenPart F) +
        xiWeilPolarization (xiWeilOddPart F) (xiWeilOddPart F) := by
        rw [hEO, hOE]
        ring

/-- The complex-valued Krein identity: every square-summable diagonal Weil value is the real
number "even-sector energy minus odd-sector energy". -/
theorem xiWeilPolarization_self_eq_parity_energies {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) :
    xiWeilPolarization F F =
      ((((∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) -
          ∑' q : XiZeroCopy, ‖xiWeilOddPart F (xiSpectralPoint q)‖ ^ 2 : ℝ)) : ℂ) := by
  rw [xiWeilPolarization_parity_decomposition hF,
    xiWeilPolarization_diagonal_of_divisorEven (xiWeilEvenPart_divisorEven F),
    xiWeilPolarization_diagonal_of_divisorOdd (xiWeilOddPart_divisorOdd F),
    Complex.ofReal_sub, Complex.ofReal_tsum, Complex.ofReal_tsum]
  ring

/-- The diagonal Weil form is real-valued on square-summable tests, unconditionally. -/
theorem xiWeilPolarization_self_im {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    (xiWeilPolarization F F).im = 0 := by
  rw [xiWeilPolarization_self_eq_parity_energies hF, Complex.ofReal_im]

/-! ## RH as degeneracy of the fundamental symmetry -/

/-- **RH ⟺ the divisor-odd sector is null**: the Riemann hypothesis holds exactly when every
divisor-odd test vanishes identically on the divisor.  The converse is an elementary two-point
indicator at a hypothetical off-line zero — no summation is involved. -/
theorem riemannHypothesis_iff_forall_divisorOdd_eval_eq_zero :
    RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, XiWeilDivisorOdd F →
        ∀ q : XiZeroCopy, F (xiSpectralPoint q) = 0 := by
  constructor
  · intro hRH F hOdd q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have h := hOdd q
    rw [ht, Complex.conj_ofReal] at h
    rw [ht]
    have h2 : (2 : ℂ) * F ((t : ℝ) : ℂ) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  · intro hodd
    by_contra hnRH
    rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hnRH
    obtain ⟨rho, hrho⟩ := not_forall.mp hnRH
    obtain ⟨hzero, hre⟩ := Classical.not_imp.mp hrho
    have hXiC : XiC (((rho : ℂ) - 1 / 2) * (-Complex.I)) = 0 := by
      rw [XiC]
      have harg : 1 / 2 + ((rho : ℂ) - 1 / 2) * -Complex.I * Complex.I = rho := by
        have hI : (-Complex.I) * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]
          ring
        linear_combination ((rho : ℂ) - 1 / 2) * hI
      rw [harg]
      exact hzero
    obtain ⟨q0, hq0⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hXiC
    set alpha : ℂ := ((rho : ℂ) - 1 / 2) * (-Complex.I) with halpha
    have himalpha : alpha.im ≠ 0 := by
      have him : alpha.im = -(rho.re - 1 / 2) := by
        rw [halpha]
        simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
      rw [him]
      intro hcontra
      apply hre
      linarith [neg_eq_zero.mp hcontra]
    have hconjne : (starRingEnd ℂ) alpha ≠ alpha := by
      intro hcontra
      apply himalpha
      have := congrArg Complex.im hcontra
      simp only [Complex.conj_im] at this
      linarith
    set O : ℂ → ℂ := fun z =>
      if z = alpha then 1 else if z = (starRingEnd ℂ) alpha then -1 else 0 with hOdef
    have hOddO : XiWeilDivisorOdd O := by
      intro q
      by_cases h1 : xiSpectralPoint q = alpha
      · rw [h1]
        show (if (starRingEnd ℂ) alpha = alpha then (1 : ℂ)
            else if (starRingEnd ℂ) alpha = (starRingEnd ℂ) alpha then -1 else 0) =
          -(if alpha = alpha then (1 : ℂ)
            else if alpha = (starRingEnd ℂ) alpha then -1 else 0)
        rw [if_neg hconjne, if_pos rfl, if_pos rfl]
      · by_cases h2 : xiSpectralPoint q = (starRingEnd ℂ) alpha
        · rw [h2, Complex.conj_conj]
          show (if alpha = alpha then (1 : ℂ)
              else if alpha = (starRingEnd ℂ) alpha then -1 else 0) =
            -(if (starRingEnd ℂ) alpha = alpha then (1 : ℂ)
              else if (starRingEnd ℂ) alpha = (starRingEnd ℂ) alpha then -1 else 0)
          rw [if_pos rfl, if_neg hconjne, if_pos rfl]
          norm_num
        · have h3 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ alpha := by
            intro hc
            apply h2
            have := congrArg (starRingEnd ℂ) hc
            rwa [Complex.conj_conj] at this
          have h4 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ (starRingEnd ℂ) alpha := by
            intro hc
            apply h1
            have := congrArg (starRingEnd ℂ) hc
            rwa [Complex.conj_conj, Complex.conj_conj] at this
          show (if (starRingEnd ℂ) (xiSpectralPoint q) = alpha then (1 : ℂ)
              else if (starRingEnd ℂ) (xiSpectralPoint q) = (starRingEnd ℂ) alpha
                then -1 else 0) =
            -(if xiSpectralPoint q = alpha then (1 : ℂ)
              else if xiSpectralPoint q = (starRingEnd ℂ) alpha then -1 else 0)
          rw [if_neg h3, if_neg h4, if_neg h1, if_neg h2]
          norm_num
    have heval := hodd O hOddO q0
    rw [hq0] at heval
    have hOa : O alpha = 1 := by
      show (if alpha = alpha then (1 : ℂ)
          else if alpha = (starRingEnd ℂ) alpha then -1 else 0) = 1
      rw [if_pos rfl]
    exact one_ne_zero (hOa.symm.trans heval)

/-- **RH ⟺ the Weil form is its own `J`-twist**: the Riemann hypothesis holds exactly when
twisting by the fundamental symmetry is invisible — when the Weil polarization already equals
the positive `ell^2` form carried by its `J`-metric.  The converse is an indicator test at a
hypothetical off-line zero, for which the untwisted diagonal vanishes while the `J`-metric
diagonal is at least one. -/
theorem riemannHypothesis_iff_polarization_parityFlip_invariant :
    RiemannHypothesis ↔
      ∀ F G : ℂ → ℂ,
        xiWeilPolarization F G = xiWeilPolarization F (xiWeilParityFlip G) := by
  constructor
  · intro hRH F G
    unfold xiWeilPolarization
    apply tsum_congr
    intro q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [xiWeilSharp, xiWeilSharp, xiWeilParityFlip, ht]
    simp only [Complex.conj_ofReal]
  · intro hinv
    by_contra hnRH
    rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hnRH
    obtain ⟨rho, hrho⟩ := not_forall.mp hnRH
    obtain ⟨hzero, hre⟩ := Classical.not_imp.mp hrho
    have hXiC : XiC (((rho : ℂ) - 1 / 2) * (-Complex.I)) = 0 := by
      rw [XiC]
      have harg : 1 / 2 + ((rho : ℂ) - 1 / 2) * -Complex.I * Complex.I = rho := by
        have hI : (-Complex.I) * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]
          ring
        linear_combination ((rho : ℂ) - 1 / 2) * hI
      rw [harg]
      exact hzero
    obtain ⟨q0, hq0⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hXiC
    set alpha : ℂ := ((rho : ℂ) - 1 / 2) * (-Complex.I) with halpha
    have himalpha : alpha.im ≠ 0 := by
      have him : alpha.im = -(rho.re - 1 / 2) := by
        rw [halpha]
        simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
      rw [him]
      intro hcontra
      apply hre
      linarith [neg_eq_zero.mp hcontra]
    have hconjne : (starRingEnd ℂ) alpha ≠ alpha := by
      intro hcontra
      apply himalpha
      have := congrArg Complex.im hcontra
      simp only [Complex.conj_im] at this
      linarith
    set F : ℂ → ℂ := fun z => if z = alpha then 1 else 0 with hFdef
    have hFsq : XiWeilSquareSummable F := by
      unfold XiWeilSquareSummable
      apply summable_of_hasFiniteSupport
      apply (finite_xiSpectralPoint_fiber alpha).subset
      intro q hq
      simp only [Function.mem_support] at hq
      by_contra hne
      apply hq
      have hne' : xiSpectralPoint q ≠ alpha := fun hc => hne hc
      have hzeroF : F (xiSpectralPoint q) = 0 := by
        show (if xiSpectralPoint q = alpha then (1 : ℂ) else 0) = 0
        rw [if_neg hne']
      rw [hzeroF, norm_zero]
      norm_num
    have hzeroW : xiWeilPolarization F F = 0 := by
      unfold xiWeilPolarization
      have hpt : ∀ q : XiZeroCopy,
          F (xiSpectralPoint q) * xiWeilSharp F (xiSpectralPoint q) = 0 := by
        intro q
        by_cases h1 : xiSpectralPoint q = alpha
        · rw [xiWeilSharp, h1]
          show (if alpha = alpha then (1 : ℂ) else 0) *
            (starRingEnd ℂ) (if (starRingEnd ℂ) alpha = alpha then (1 : ℂ) else 0) = 0
          rw [if_neg hconjne, map_zero, mul_zero]
        · show (if xiSpectralPoint q = alpha then (1 : ℂ) else 0) *
            xiWeilSharp F (xiSpectralPoint q) = 0
          rw [if_neg h1, zero_mul]
      rw [tsum_congr hpt, tsum_zero]
    have heq := hinv F F
    rw [hzeroW, xiWeilPolarization_parityFlip_diagonal F] at heq
    have hsumC : Summable (fun q : XiZeroCopy =>
        ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ)) := by
      simpa only [Function.comp_apply] using!
        hFsq.map Complex.ofRealCLM Complex.ofRealCLM.continuous
    have hre2 : (0 : ℝ) = ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 := by
      have hcast := congrArg Complex.re heq
      rw [Complex.zero_re, Complex.re_tsum hsumC] at hcast
      rw [hcast]
      exact tsum_congr fun q => Complex.ofReal_re _
    have hFsum : Summable (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ 2) := hFsq
    have hle : ‖F (xiSpectralPoint q0)‖ ^ 2 ≤
        ∑' q : XiZeroCopy, ‖F (xiSpectralPoint q)‖ ^ 2 :=
      hFsum.le_tsum q0 fun q _ => sq_nonneg _
    rw [← hre2, hq0] at hle
    have hFa : F alpha = 1 := by
      show (if alpha = alpha then (1 : ℂ) else 0) = 1
      rw [if_pos rfl]
    rw [hFa] at hle
    norm_num at hle

end

end RHTower
