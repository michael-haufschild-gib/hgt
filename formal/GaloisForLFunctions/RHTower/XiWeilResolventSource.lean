import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Prime--Gamma realization of the Xi Weil polarization on the Cauchy core

The Cauchy tests `a ↦ (a-z)^{-1}` have pairwise products of inverse-square size on the
multiplicity-exact centered Xi divisor.  Partial fractions identify their Weil polarization with a
divided difference of the regulator-independent Xi relative resolvent trace.  Existing source
identities then replace both target traces by the actual von-Mangoldt plus archimedean expression,
either in its absolutely convergent half-plane or in its meromorphically continued domain.

This gives an unconditional prime--Gamma source realization on a concrete nontrivial Weil test
core.  It does not assert the full Guinand--Weil explicit formula for every admissible test.
-/

open Complex

namespace RHTower

noncomputable section

/-- The centered Cauchy test based at `z`. -/
def xiWeilCauchyTest (z a : ℂ) : ℂ := (a - z)⁻¹

/-- The Weil involution sends the Cauchy parameter to its complex conjugate. -/
theorem xiWeilSharp_cauchy (w a : ℂ) :
    xiWeilSharp (xiWeilCauchyTest w) a =
      xiWeilCauchyTest ((starRingEnd ℂ) w) a := by
  rw [xiWeilSharp, xiWeilCauchyTest, xiWeilCauchyTest, map_inv₀, map_sub]
  simp

/-- Partial fractions turn a polarized Cauchy product into a divided difference of centered
relative-resolvent terms. -/
theorem xiWeilCauchy_product_eq_relativeResolvent_dividedDifference
    {z v : ℂ} (hzv : z ≠ v) (q : XiZeroCopy)
    (hqz : xiSpectralPoint q ≠ z) (hqv : xiSpectralPoint q ≠ v) :
    xiWeilCauchyTest z (xiSpectralPoint q) *
        xiWeilCauchyTest v (xiSpectralPoint q) =
      (xiRelativeResolventTerm v q - xiRelativeResolventTerm z q) / (z - v) := by
  have ha := xiSpectralPoint_ne_zero q
  have haz : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr hqz
  have hav : xiSpectralPoint q - v ≠ 0 := sub_ne_zero.mpr hqv
  have hzv0 : z - v ≠ 0 := sub_ne_zero.mpr hzv
  rw [xiWeilCauchyTest, xiWeilCauchyTest, xiRelativeResolventTerm,
    xiRelativeResolventTerm]
  field_simp [ha, haz, hav, hzv0]
  ring

/-- Cauchy pairs are absolutely summable on the actual centered Xi divisor. -/
theorem xiWeilPairSummable_cauchy
    {z w : ℂ} (hz : XiC z ≠ 0)
    (hw : XiC ((starRingEnd ℂ) w) ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    XiWeilPairSummable (xiWeilCauchyTest z) (xiWeilCauchyTest w) := by
  let v : ℂ := (starRingEnd ℂ) w
  have hzsum := summable_xiRelativeResolventTerm hz
  have hvsum := summable_xiRelativeResolventTerm hw
  have hdiff : Summable (fun q : XiZeroCopy =>
      (xiRelativeResolventTerm v q - xiRelativeResolventTerm z q) / (z - v)) :=
    (hvsum.sub hzsum).div_const (z - v)
  apply hdiff.congr
  intro q
  rw [xiWeilSharp_cauchy]
  symm
  apply xiWeilCauchy_product_eq_relativeResolvent_dividedDifference hzw
  · intro h
    apply hz
    exact (XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h⟩
  · intro h
    apply hw
    exact (XiC_eq_zero_iff_exists_xiZeroCopy v).mpr ⟨q, h⟩

/-- Exact target-side Cauchy polarization as a divided difference of the Xi relative trace. -/
theorem xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference
    {z w : ℂ} (hz : XiC z ≠ 0)
    (hw : XiC ((starRingEnd ℂ) w) ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) =
      (xiRelativeResolventTrace ((starRingEnd ℂ) w) - xiRelativeResolventTrace z) /
        (z - (starRingEnd ℂ) w) := by
  let v : ℂ := (starRingEnd ℂ) w
  have hzsum := summable_xiRelativeResolventTerm hz
  have hvsum := summable_xiRelativeResolventTerm hw
  rw [xiWeilPolarization]
  calc
    (∑' q : XiZeroCopy,
        xiWeilCauchyTest z (xiSpectralPoint q) *
          xiWeilSharp (xiWeilCauchyTest w) (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy,
          (xiRelativeResolventTerm v q - xiRelativeResolventTerm z q) / (z - v) := by
      apply tsum_congr
      intro q
      rw [xiWeilSharp_cauchy]
      apply xiWeilCauchy_product_eq_relativeResolvent_dividedDifference hzw
      · intro h
        apply hz
        exact (XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h⟩
      · intro h
        apply hw
        exact (XiC_eq_zero_iff_exists_xiZeroCopy v).mpr ⟨q, h⟩
    _ = ((∑' q : XiZeroCopy,
          (xiRelativeResolventTerm v q - xiRelativeResolventTerm z q)) / (z - v)) := by
      rw [tsum_div_const]
    _ = (xiRelativeResolventTrace v - xiRelativeResolventTrace z) / (z - v) := by
      rw [hvsum.tsum_sub hzsum]
      rfl

/-- The continued prime--archimedean pole-free domain contains no centered Xi zero. -/
theorem XiC_ne_zero_of_continuedPrimeArch_domain
    {z : ℂ} (hspos : 0 < (1 / 2 + z * I).re)
    (hs1 : 1 / 2 + z * I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    XiC z ≠ 0 := by
  let s : ℂ := 1 / 2 + z * I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    change 0 < s.re at hspos
    linarith
  have hG := Gammaℝ_ne_zero_of_re_pos hspos
  change xi s ≠ 0
  rw [xi_eq_archFactor_mul_zeta hs0 hs1 hG]
  exact mul_ne_zero (archFactor_ne_zero hs0 hs1 hG) hzeta

/-- The absolutely convergent prime-source half-plane contains no centered Xi zero. -/
theorem XiC_ne_zero_of_one_lt_centered_re
    {z : ℂ} (hs : 1 < (1 / 2 + z * I).re) :
    XiC z ≠ 0 := by
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.one_re] at hre
    linarith
  exact XiC_ne_zero_of_continuedPrimeArch_domain (lt_trans zero_lt_one hs) hs1
    (riemannZeta_ne_zero_of_one_lt_re hs)

/-- Absolutely convergent von-Mangoldt plus archimedean realization of the Cauchy polarization. -/
theorem xiWeilPolarization_cauchy_eq_primeArchSource_dividedDifference
    {z w : ℂ}
    (hzhalf : 1 < (1 / 2 + z * I).re)
    (hwhalf : 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) =
      (primeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
        primeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w) := by
  have hsourceZ := primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hzhalf
  have hsourceW := primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hwhalf
  have hzXi := XiC_ne_zero_of_one_lt_centered_re hzhalf
  have hwXi := XiC_ne_zero_of_one_lt_centered_re hwhalf
  rw [xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference hzXi hwXi hzw,
    hsourceZ, hsourceW]

/-- Meromorphically continued prime--archimedean realization on the natural pole-free domain. -/
theorem xiWeilPolarization_cauchy_eq_continuedPrimeArchSource_dividedDifference
    {z w : ℂ}
    (hzpos : 0 < (1 / 2 + z * I).re)
    (hz1 : 1 / 2 + z * I ≠ 1)
    (hzzeta : riemannZeta (1 / 2 + z * I) ≠ 0)
    (hwpos : 0 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hw1 : 1 / 2 + (starRingEnd ℂ) w * I ≠ 1)
    (hwzeta : riemannZeta (1 / 2 + (starRingEnd ℂ) w * I) ≠ 0)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) =
      (continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
        continuedPrimeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w) := by
  have hzSource := continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hzpos hz1 hzzeta
  have hwSource := continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hwpos hw1 hwzeta
  have hzXi := XiC_ne_zero_of_continuedPrimeArch_domain hzpos hz1 hzzeta
  have hwXi := XiC_ne_zero_of_continuedPrimeArch_domain hwpos hw1 hwzeta
  rw [xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference hzXi hwXi hzw,
    hzSource, hwSource]

/-! ## Finite Cauchy packets -/

/-- A finite linear combination of centered Cauchy tests. -/
def xiWeilCauchyPacket (s : Finset ℂ) (c : ℂ → ℂ) (a : ℂ) : ℂ :=
  ∑ z ∈ s, c z * xiWeilCauchyTest z a

/-- The Weil involution conjugates both the packet coefficients and its Cauchy parameters. -/
theorem xiWeilSharp_cauchyPacket (s : Finset ℂ) (c : ℂ → ℂ) (a : ℂ) :
    xiWeilSharp (xiWeilCauchyPacket s c) a =
      ∑ z ∈ s, (starRingEnd ℂ) (c z) *
        xiWeilCauchyTest ((starRingEnd ℂ) z) a := by
  rw [xiWeilSharp, xiWeilCauchyPacket]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [show (starRingEnd ℂ) (xiWeilCauchyTest z ((starRingEnd ℂ) a)) =
      xiWeilCauchyTest ((starRingEnd ℂ) z) a by
    simpa only [xiWeilSharp] using xiWeilSharp_cauchy z a]

/-- Polarization of finite Cauchy packets is the finite sesquilinear sum of their pairwise
polarizations. -/
theorem xiWeilPolarization_cauchyPacket
    {s t : Finset ℂ} {c d : ℂ → ℂ}
    (hz : ∀ z ∈ s, XiC z ≠ 0)
    (hw : ∀ w ∈ t, XiC ((starRingEnd ℂ) w) ≠ 0)
    (hsep : ∀ z ∈ s, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyPacket s c) (xiWeilCauchyPacket t d) =
      ∑ z ∈ s, ∑ w ∈ t,
        c z * (starRingEnd ℂ) (d w) *
          xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) := by
  let term : ℂ → ℂ → XiZeroCopy → ℂ := fun z w q =>
    c z * (starRingEnd ℂ) (d w) *
      (xiWeilCauchyTest z (xiSpectralPoint q) *
        xiWeilSharp (xiWeilCauchyTest w) (xiSpectralPoint q))
  have hterm (z : ℂ) (hzs : z ∈ s) (w : ℂ) (hwt : w ∈ t) :
      Summable (term z w) := by
    have hp := xiWeilPairSummable_cauchy (hz z hzs) (hw w hwt) (hsep z hzs w hwt)
    exact (show Summable (fun q : XiZeroCopy =>
      xiWeilCauchyTest z (xiSpectralPoint q) *
        xiWeilSharp (xiWeilCauchyTest w) (xiSpectralPoint q)) from hp).mul_left _
  rw [xiWeilPolarization]
  calc
    (∑' q : XiZeroCopy,
        xiWeilCauchyPacket s c (xiSpectralPoint q) *
          xiWeilSharp (xiWeilCauchyPacket t d) (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy, ∑ z ∈ s, ∑ w ∈ t, term z w q := by
      apply tsum_congr
      intro q
      rw [xiWeilCauchyPacket, xiWeilSharp_cauchyPacket, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _hzs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _hwt
      simp only [term]
      rw [xiWeilSharp_cauchy]
      ring
    _ = ∑ z ∈ s, ∑ w ∈ t, ∑' q : XiZeroCopy, term z w q := by
      rw [Summable.tsum_finsetSum (fun z hzs =>
        summable_sum fun w hwt => hterm z hzs w hwt)]
      apply Finset.sum_congr rfl
      intro z hzs
      rw [Summable.tsum_finsetSum (fun w hwt => hterm z hzs w hwt)]
    _ = ∑ z ∈ s, ∑ w ∈ t,
        c z * (starRingEnd ℂ) (d w) *
          xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) := by
      apply Finset.sum_congr rfl
      intro z _hzs
      apply Finset.sum_congr rfl
      intro w _hwt
      change (∑' q : XiZeroCopy,
        c z * (starRingEnd ℂ) (d w) *
          (xiWeilCauchyTest z (xiSpectralPoint q) *
            xiWeilSharp (xiWeilCauchyTest w) (xiSpectralPoint q))) = _
      rw [tsum_mul_left]
      rfl

/-- The complete finite-packet source formula on the absolutely convergent prime half-plane. -/
theorem xiWeilPolarization_cauchyPacket_eq_primeArchSource
    {s t : Finset ℂ} {c d : ℂ → ℂ}
    (hzhalf : ∀ z ∈ s, 1 < (1 / 2 + z * I).re)
    (hwhalf : ∀ w ∈ t, 1 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hsep : ∀ z ∈ s, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyPacket s c) (xiWeilCauchyPacket t d) =
      ∑ z ∈ s, ∑ w ∈ t,
        c z * (starRingEnd ℂ) (d w) *
          ((primeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
            primeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w)) := by
  rw [xiWeilPolarization_cauchyPacket
    (fun z hz => XiC_ne_zero_of_one_lt_centered_re (hzhalf z hz))
    (fun w hw => XiC_ne_zero_of_one_lt_centered_re (hwhalf w hw)) hsep]
  apply Finset.sum_congr rfl
  intro z hzs
  apply Finset.sum_congr rfl
  intro w hwt
  rw [xiWeilPolarization_cauchy_eq_primeArchSource_dividedDifference
    (hzhalf z hzs) (hwhalf w hwt) (hsep z hzs w hwt)]

/-- The complete finite-packet source formula on the continued pole-free domain. -/
theorem xiWeilPolarization_cauchyPacket_eq_continuedPrimeArchSource
    {s t : Finset ℂ} {c d : ℂ → ℂ}
    (hzpos : ∀ z ∈ s, 0 < (1 / 2 + z * I).re)
    (hz1 : ∀ z ∈ s, 1 / 2 + z * I ≠ 1)
    (hzzeta : ∀ z ∈ s, riemannZeta (1 / 2 + z * I) ≠ 0)
    (hwpos : ∀ w ∈ t, 0 < (1 / 2 + (starRingEnd ℂ) w * I).re)
    (hw1 : ∀ w ∈ t, 1 / 2 + (starRingEnd ℂ) w * I ≠ 1)
    (hwzeta : ∀ w ∈ t,
      riemannZeta (1 / 2 + (starRingEnd ℂ) w * I) ≠ 0)
    (hsep : ∀ z ∈ s, ∀ w ∈ t, z ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization (xiWeilCauchyPacket s c) (xiWeilCauchyPacket t d) =
      ∑ z ∈ s, ∑ w ∈ t,
        c z * (starRingEnd ℂ) (d w) *
          ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
            continuedPrimeArchSourceRelativeTrace z) / (z - (starRingEnd ℂ) w)) := by
  rw [xiWeilPolarization_cauchyPacket
    (fun z hz => XiC_ne_zero_of_continuedPrimeArch_domain
      (hzpos z hz) (hz1 z hz) (hzzeta z hz))
    (fun w hw => XiC_ne_zero_of_continuedPrimeArch_domain
      (hwpos w hw) (hw1 w hw) (hwzeta w hw)) hsep]
  apply Finset.sum_congr rfl
  intro z hzs
  apply Finset.sum_congr rfl
  intro w hwt
  rw [xiWeilPolarization_cauchy_eq_continuedPrimeArchSource_dividedDifference
    (hzpos z hzs) (hz1 z hzs) (hzzeta z hzs)
    (hwpos w hwt) (hw1 w hwt) (hwzeta w hwt) (hsep z hzs w hwt)]

end

end RHTower
