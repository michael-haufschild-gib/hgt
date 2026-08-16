import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorRouteTZeroFree

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- Fixed broad rectangle carrying every moving-threshold detector packet. -/
def inghamRouteTCommonZeroPacket (X : ℕ) : Finset ℂ :=
  zetaResidueUnitClosedRectangleZeros
    (((inghamUniformGabrielCenter (7 / 10 : ℝ) : ℝ) : ℂ) +
      (-((X : ℝ) - 2) : ℝ) * I)
    ((4 : ℂ) + ((X : ℝ) - 2) * I)

theorem inghamUniformGabrielCenter_mono_on_routeT
    {sigma tau : ℝ} (h : sigma ≤ tau) :
    inghamUniformGabrielCenter sigma ≤ inghamUniformGabrielCenter tau := by
  unfold inghamUniformGabrielCenter
  linarith

theorem inghamUniformGabrielCenter_le_self
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    inghamUniformGabrielCenter sigma ≤ sigma := by
  unfold inghamUniformGabrielCenter
  linarith

/-- Moving Gabriel rectangles select exactly the threshold filter of one fixed broad packet. -/
theorem zetaLittlewoodZeroCountAbove_eq_commonZeroPacket
    {X : ℕ} {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter sigma) 4
        ((X : ℝ) - 2) sigma =
      ∑ w ∈ (inghamRouteTCommonZeroPacket X).filter (fun w => sigma ≤ w.re),
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) := by
  let Zsigma : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    (((inghamUniformGabrielCenter sigma : ℝ) : ℂ) +
      (-((X : ℝ) - 2) : ℝ) * I)
    (((4 : ℝ) : ℂ) + ((((X : ℝ) - 2) : ℝ) : ℂ) * I)
  have hcenterSigma : inghamUniformGabrielCenter sigma ≤ sigma :=
    inghamUniformGabrielCenter_le_self hsigma1.le
  have hcenterCommon :
      inghamUniformGabrielCenter (7 / 10 : ℝ) ≤
        inghamUniformGabrielCenter sigma :=
    inghamUniformGabrielCenter_mono_on_routeT hsigma0
  have hcenterFour : inghamUniformGabrielCenter sigma ≤ 4 := by
    linarith
  have hcommonFour : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 4 :=
    hcenterCommon.trans hcenterFour
  have hfilter : Zsigma.filter (fun w => sigma ≤ w.re) =
      (inghamRouteTCommonZeroPacket X).filter (fun w => sigma ≤ w.re) := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, hwreSigma⟩
      have hwdata := mem_zetaResidueUnitClosedRectangleZeros.mp hw
      have hwK := Complex.mem_reProdIm.mp hwdata.1
      have hwre : w.re ∈ Set.Icc (inghamUniformGabrielCenter sigma) 4 := by
        simpa [Zsigma, uIcc_of_le hcenterFour] using hwK.1
      have hwreCommon :
          w.re ∈ Set.Icc (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4 :=
        ⟨hcenterCommon.trans hwre.1, hwre.2⟩
      refine ⟨mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_, hwdata.2⟩, hwreSigma⟩
      apply Complex.mem_reProdIm.mpr
      constructor
      · simpa [inghamRouteTCommonZeroPacket, uIcc_of_le hcommonFour] using hwreCommon
      · simpa [inghamRouteTCommonZeroPacket, Zsigma] using hwK.2
    · rintro ⟨hw, hwreSigma⟩
      have hwdata := mem_zetaResidueUnitClosedRectangleZeros.mp hw
      have hwK := Complex.mem_reProdIm.mp hwdata.1
      have hwreCommon :
          w.re ∈ Set.Icc (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4 := by
        simpa [inghamRouteTCommonZeroPacket, uIcc_of_le hcommonFour] using hwK.1
      have hwre : w.re ∈ Set.Icc (inghamUniformGabrielCenter sigma) 4 :=
        ⟨hcenterSigma.trans hwreSigma, hwreCommon.2⟩
      refine ⟨mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_, hwdata.2⟩, hwreSigma⟩
      apply Complex.mem_reProdIm.mpr
      constructor
      · simpa [Zsigma, uIcc_of_le hcenterFour] using hwre
      · simpa [inghamRouteTCommonZeroPacket, Zsigma] using hwK.2
  unfold zetaLittlewoodZeroCountAbove
  rw [show zetaResidueUnitClosedRectangleZeros
      (((inghamUniformGabrielCenter sigma : ℝ) : ℂ) +
        (-((X : ℝ) - 2) : ℝ) * I)
      (((4 : ℝ) : ℂ) + ((((X : ℝ) - 2) : ℝ) : ℂ) * I) = Zsigma by rfl]
  rw [hfilter]

end

end RHTower.Sieve
