import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCutoffAtoms
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureGroundEnergy

/-!
# Continuous prime-cutoff hinges and fixed-parity first contact

The literal moving prime cutoff in the CCM pole energies is a finite superposition of continuous
positive-part hinges: every entering prime atom vanishes at its entry radius.  Consequently the
full diagonal and cross pole energies are globally continuous, including across prime-power
entries.  Combining this with small-aperture positivity and the fixed-parity pole criterion shows
that failure of RH has a first zero on one of the two literal coefficient vectors `(1, 1)` or
`(1, -1)`, with strict positivity at every smaller aperture.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

/-- Continuous activation of one diagonal prime atom at its literal entry radius. -/
def ccmWeilPolePrimeDiagonalHinge (n : ℕ) (s : ℝ) : ℝ :=
  max (ccmWeilPolePrimeDiagonalAtom n s) 0

/-- Continuous activation of one cross prime atom at its literal entry radius. -/
def ccmWeilPolePrimeCrossHinge (n : ℕ) (s : ℝ) : ℝ :=
  max (ccmWeilPolePrimeCrossAtom n s) 0

private theorem diagonalAtom_nonneg_of_le_floor {n : ℕ} (hn : 1 ≤ n) {s : ℝ}
    (hentry : n ≤ ⌊Real.exp (2 * s)⌋₊) :
    0 ≤ ccmWeilPolePrimeDiagonalAtom n s := by
  have hnfloor : (n : ℝ) ≤ (⌊Real.exp (2 * s)⌋₊ : ℕ) := by exact_mod_cast hentry
  have hnexp : (n : ℝ) ≤ Real.exp (2 * s) :=
    hnfloor.trans (Nat.floor_le (Real.exp_pos _).le)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hmul := mul_le_mul_of_nonneg_left hnexp (Real.exp_pos (-s)).le
  have hexp : Real.exp (-s) * Real.exp (2 * s) = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiv : Real.exp (-s) ≤ Real.exp s / n := by
    rw [le_div_iff₀ hnpos]
    simpa only [mul_comm] using hmul.trans_eq hexp
  unfold ccmWeilPolePrimeDiagonalAtom
  exact mul_nonneg (mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
    (sub_nonneg.mpr hdiv)

private theorem diagonalAtom_nonpos_of_floor_lt {n : ℕ} (hn : 1 ≤ n) {s : ℝ}
    (hentry : ⌊Real.exp (2 * s)⌋₊ < n) :
    ccmWeilPolePrimeDiagonalAtom n s ≤ 0 := by
  have hexpn : Real.exp (2 * s) < (n : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp hentry
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hmul := mul_le_mul_of_nonneg_left hexpn.le (Real.exp_pos (-s)).le
  have hexp : Real.exp (-s) * Real.exp (2 * s) = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiv : Real.exp s / n ≤ Real.exp (-s) := by
    rw [div_le_iff₀ hnpos]
    calc
      Real.exp s = Real.exp (-s) * Real.exp (2 * s) := hexp.symm
      _ ≤ Real.exp (-s) * n := hmul
  unfold ccmWeilPolePrimeDiagonalAtom
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
    (sub_nonpos.mpr hdiv)

private theorem crossAtom_nonneg_of_le_floor {n : ℕ} (hn : 1 ≤ n) {s : ℝ}
    (hentry : n ≤ ⌊Real.exp (2 * s)⌋₊) :
    0 ≤ ccmWeilPolePrimeCrossAtom n s := by
  have hnfloor : (n : ℝ) ≤ (⌊Real.exp (2 * s)⌋₊ : ℕ) := by exact_mod_cast hentry
  have hnexp : (n : ℝ) ≤ Real.exp (2 * s) :=
    hnfloor.trans (Nat.floor_le (Real.exp_pos _).le)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : Real.log n ≤ 2 * s :=
    (Real.log_le_iff_le_exp hnpos).2 hnexp
  unfold ccmWeilPolePrimeCrossAtom
  exact mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (sub_nonneg.mpr hlog)

private theorem crossAtom_nonpos_of_floor_lt {n : ℕ} (hn : 1 ≤ n) {s : ℝ}
    (hentry : ⌊Real.exp (2 * s)⌋₊ < n) :
    ccmWeilPolePrimeCrossAtom n s ≤ 0 := by
  have hexpn : Real.exp (2 * s) < (n : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp hentry
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : 2 * s ≤ Real.log n :=
    (Real.le_log_iff_exp_le hnpos).2 hexpn.le
  unfold ccmWeilPolePrimeCrossAtom
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (sub_nonpos.mpr hlog)

theorem continuous_ccmWeilPolePrimeDiagonalHinge (n : ℕ) :
    Continuous (ccmWeilPolePrimeDiagonalHinge n) := by
  unfold ccmWeilPolePrimeDiagonalHinge ccmWeilPolePrimeDiagonalAtom
  fun_prop

theorem continuous_ccmWeilPolePrimeCrossHinge (n : ℕ) :
    Continuous (ccmWeilPolePrimeCrossHinge n) := by
  unfold ccmWeilPolePrimeCrossHinge ccmWeilPolePrimeCrossAtom
  fun_prop

private theorem continuousAt_ccmWeilPoleDiagonalSmooth {s : ℝ} (hs : 0 < s) :
    ContinuousAt ccmWeilPoleDiagonalSmooth s := by
  have hboundary := (hasDerivAt_ccmGammaPoleSelfBoundaryPrimitive hs).continuousAt
  unfold ccmWeilPoleDiagonalSmooth
  fun_prop

private theorem continuousAt_ccmWeilPoleCrossSmooth {s : ℝ} (hs : 0 < s) :
    ContinuousAt ccmWeilPoleCrossSmooth s := by
  have hboundary := (hasDerivAt_ccmGammaPoleCrossBoundaryPrimitive hs).continuousAt
  unfold ccmWeilPoleCrossSmooth
  fun_prop

theorem ccmWeilPoleDiagonal_eq_smooth_sub_sum_hinges
    (a : SuzukiPositiveAperture) {N : ℕ}
    (hN : ⌊Real.exp (2 * a.1)⌋₊ ≤ N) :
    ccmWeilPoleDiagonal a = ccmWeilPoleDiagonalSmooth a.1 -
      ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeDiagonalHinge n a.1 := by
  rw [ccmWeilPoleDiagonal_eq_chamber_of_floor_eq a a rfl,
    ccmWeilPoleChamberDiagonal_eq_sum_atoms]
  congr 1
  calc
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ccmWeilPolePrimeDiagonalAtom n a.1) =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          ccmWeilPolePrimeDiagonalHinge n a.1 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn1 : 1 ≤ n := hn2.trans' (by omega)
      rw [ccmWeilPolePrimeDiagonalHinge,
        max_eq_left (diagonalAtom_nonneg_of_le_floor hn1
          (Finset.mem_Icc.mp hn).2)]
    _ = ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeDiagonalHinge n a.1 := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
      intro n hnN hnsmall
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnN).1
      have hfloor : ⌊Real.exp (2 * a.1)⌋₊ < n := by
        by_contra h
        exact hnsmall (Finset.mem_Icc.mpr ⟨hn2, le_of_not_gt h⟩)
      rw [ccmWeilPolePrimeDiagonalHinge,
        max_eq_right (diagonalAtom_nonpos_of_floor_lt (by omega) hfloor)]

theorem ccmWeilPoleCross_eq_smooth_sub_sum_hinges
    (a : SuzukiPositiveAperture) {N : ℕ}
    (hN : ⌊Real.exp (2 * a.1)⌋₊ ≤ N) :
    ccmWeilPoleCross a = ccmWeilPoleCrossSmooth a.1 -
      ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeCrossHinge n a.1 := by
  rw [ccmWeilPoleCross_eq_chamber_of_floor_eq a a rfl,
    ccmWeilPoleChamberCross_eq_sum_atoms]
  congr 1
  calc
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ccmWeilPolePrimeCrossAtom n a.1) =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          ccmWeilPolePrimeCrossHinge n a.1 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn1 : 1 ≤ n := hn2.trans' (by omega)
      rw [ccmWeilPolePrimeCrossHinge,
        max_eq_left (crossAtom_nonneg_of_le_floor hn1
          (Finset.mem_Icc.mp hn).2)]
    _ = ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeCrossHinge n a.1 := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hN)
      intro n hnN hnsmall
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnN).1
      have hfloor : ⌊Real.exp (2 * a.1)⌋₊ < n := by
        by_contra h
        exact hnsmall (Finset.mem_Icc.mpr ⟨hn2, le_of_not_gt h⟩)
      rw [ccmWeilPolePrimeCrossHinge,
        max_eq_right (crossAtom_nonpos_of_floor_lt (by omega) hfloor)]

/-- The literal full Weil pole diagonal is continuous across every prime-power entry. -/
theorem continuous_ccmWeilPoleDiagonal : Continuous ccmWeilPoleDiagonal := by
  rw [continuous_iff_continuousAt]
  intro a
  let N : ℕ := ⌊Real.exp (2 * (a.1 + 1))⌋₊
  let fixed : SuzukiPositiveAperture → ℝ := fun b =>
    ccmWeilPoleDiagonalSmooth b.1 -
      ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeDiagonalHinge n b.1
  have hsmooth : ContinuousAt (fun b : SuzukiPositiveAperture =>
      ccmWeilPoleDiagonalSmooth b.1) a :=
    (continuousAt_ccmWeilPoleDiagonalSmooth a.2).comp_of_eq
      continuousAt_subtype_val rfl
  have hsum : Continuous (fun b : SuzukiPositiveAperture =>
      ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeDiagonalHinge n b.1) :=
    continuous_finsetSum _ fun n _ =>
      (continuous_ccmWeilPolePrimeDiagonalHinge n).comp continuous_subtype_val
  have hfixed : ContinuousAt fixed a := hsmooth.sub hsum.continuousAt
  have hbelow : ∀ᶠ b : SuzukiPositiveAperture in 𝓝 a, b.1 < a.1 + 1 :=
    continuousAt_subtype_val (Iio_mem_nhds (lt_add_one a.1))
  have heq : ccmWeilPoleDiagonal =ᶠ[𝓝 a] fixed := by
    filter_upwards [hbelow] with b hb
    apply ccmWeilPoleDiagonal_eq_smooth_sub_sum_hinges
    dsimp only [N]
    apply Nat.floor_mono
    rw [Real.exp_le_exp]
    linarith
  exact hfixed.congr_of_eventuallyEq heq

/-- The literal opposite-pole entry is continuous across every prime-power entry. -/
theorem continuous_ccmWeilPoleCross : Continuous ccmWeilPoleCross := by
  rw [continuous_iff_continuousAt]
  intro a
  let N : ℕ := ⌊Real.exp (2 * (a.1 + 1))⌋₊
  let fixed : SuzukiPositiveAperture → ℝ := fun b =>
    ccmWeilPoleCrossSmooth b.1 -
      ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeCrossHinge n b.1
  have hsmooth : ContinuousAt (fun b : SuzukiPositiveAperture =>
      ccmWeilPoleCrossSmooth b.1) a :=
    (continuousAt_ccmWeilPoleCrossSmooth a.2).comp_of_eq
      continuousAt_subtype_val rfl
  have hsum : Continuous (fun b : SuzukiPositiveAperture =>
      ∑ n ∈ Finset.Icc 2 N, ccmWeilPolePrimeCrossHinge n b.1) :=
    continuous_finsetSum _ fun n _ =>
      (continuous_ccmWeilPolePrimeCrossHinge n).comp continuous_subtype_val
  have hfixed : ContinuousAt fixed a := hsmooth.sub hsum.continuousAt
  have hbelow : ∀ᶠ b : SuzukiPositiveAperture in 𝓝 a, b.1 < a.1 + 1 :=
    continuousAt_subtype_val (Iio_mem_nhds (lt_add_one a.1))
  have heq : ccmWeilPoleCross =ᶠ[𝓝 a] fixed := by
    filter_upwards [hbelow] with b hb
    apply ccmWeilPoleCross_eq_smooth_sub_sum_hinges
    dsimp only [N]
    apply Nat.floor_mono
    rw [Real.exp_le_exp]
    linarith
  exact hfixed.congr_of_eventuallyEq heq

/-- A fixed even or odd pole-source energy varies continuously with aperture, including at every
prime-power entry. -/
theorem continuous_ccmRestrictedWeil_parityPoleSourceQuadratic
    (r : ℝ) (hr : r = 1 ∨ r = -1) :
    Continuous (fun a : SuzukiPositiveAperture =>
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r)) := by
  have heq : (fun a : SuzukiPositiveAperture =>
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r)) =
      fun a => 2 * (ccmWeilPoleDiagonal a + r * ccmWeilPoleCross a) := by
    funext a
    exact ccmWeilPoleCompression_parity_energy a hr
  rw [heq]
  exact continuous_const.mul
    (continuous_ccmWeilPoleDiagonal.add
      (continuous_const.mul continuous_ccmWeilPoleCross))

private theorem parityPoleSourceQuadratic_pos_of_ground_pos
    (a : SuzukiPositiveAperture) (r : ℝ) (hr : r = 1 ∨ r = -1)
    (hground : 0 < ccmRestrictedWeilGroundEnergy a) :
    0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) := by
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a
    (ccmPolarParityFormVector a r)
  rw [norm_sq_ccmPolarParityFormVector_physical a hr] at hfloor
  have hgram := polarParityGram_pos a hr
  nlinarith

/-- Failure of RH reaches the sign wall through one literal fixed-coefficient parity pole. -/
def CCMFixedParityPoleFirstContact : Prop :=
  ∃ (a : SuzukiPositiveAperture) (r : ℝ),
    (r = 1 ∨ r = -1) ∧
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) = 0 ∧
      ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        0 < ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b r)

/-- Route-level fixed-source alternative. If RH fails, first loss of sign occurs on one of the two
literal prime--polar--Gamma vectors with coefficients `(1,1)` or `(1,-1)`. -/
theorem riemannHypothesis_or_ccmFixedParityPoleFirstContact :
    RiemannHypothesis ∨ CCMFixedParityPoleFirstContact := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    obtain ⟨A, r, hr, hAneg⟩ :=
      not_riemannHypothesis_implies_exists_negative_parityPole hRH
    obtain ⟨delta, hdelta, hsmall⟩ :=
      exists_suzukiSmallAperture_ccmGroundEnergy_pos
    let p : SuzukiPositiveAperture := ⟨delta / 2, by linarith⟩
    have hAδ : delta ≤ A.1 := by
      by_contra hnot
      have hground : 0 < ccmRestrictedWeilGroundEnergy A :=
        hsmall A (lt_of_not_ge hnot)
      have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source A
        (ccmPolarParityFormVector A r)
      rw [norm_sq_ccmPolarParityFormVector_physical A hr] at hfloor
      have hgram := polarParityGram_pos A hr
      have hprod : 0 < ccmRestrictedWeilGroundEnergy A *
          (2 * (2 * Real.sinh A.1 + 2 * A.1 * r)) :=
        mul_pos hground (mul_pos (by norm_num) hgram)
      linarith
    have hpA : p.1 < A.1 := by
      dsimp only [p]
      linarith
    have hpEnergy : 0 < ccmRestrictedWeilSourceQuadratic p
        (ccmPolarParityFormVector p r) := by
      have hground : 0 < ccmRestrictedWeilGroundEnergy p := by
        apply hsmall
        dsimp only [p]
        linarith
      have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source p
        (ccmPolarParityFormVector p r)
      rw [norm_sq_ccmPolarParityFormVector_physical p hr] at hfloor
      have hgram := polarParityGram_pos p hr
      nlinarith
    let apertureAt : ℝ → SuzukiPositiveAperture := fun x =>
      ⟨max p.1 x, p.2.trans_le (le_max_left _ _)⟩
    let energy : ℝ → ℝ := fun x =>
      ccmRestrictedWeilSourceQuadratic (apertureAt x)
        (ccmPolarParityFormVector (apertureAt x) r)
    have hapertureContinuous : Continuous apertureAt := by
      exact (continuous_const.max continuous_id).subtype_mk _
    have henergyContinuous : Continuous energy :=
      (continuous_ccmRestrictedWeil_parityPoleSourceQuadratic r hr).comp
        hapertureContinuous
    have henergy_eq (x : ℝ) (hx : p.1 ≤ x) :
        energy x = ccmRestrictedWeilSourceQuadratic ⟨x, p.2.trans_le hx⟩
          (ccmPolarParityFormVector ⟨x, p.2.trans_le hx⟩ r) := by
      have haperture : apertureAt x = ⟨x, p.2.trans_le hx⟩ := by
        apply Subtype.ext
        exact max_eq_right hx
      change ccmRestrictedWeilSourceQuadratic (apertureAt x)
          (ccmPolarParityFormVector (apertureAt x) r) = _
      rw [haperture]
    let S : Set ℝ := Icc p.1 A.1 ∩ energy ⁻¹' Iic 0
    have hSClosed : IsClosed S :=
      isClosed_Icc.inter (isClosed_Iic.preimage henergyContinuous)
    have hAmem : A.1 ∈ S := by
      refine ⟨right_mem_Icc.mpr hpA.le, ?_⟩
      change energy A.1 ≤ 0
      rw [henergy_eq A.1 hpA.le]
      simpa only using hAneg.le
    have hSNonempty : S.Nonempty := ⟨A.1, hAmem⟩
    have hSBdd : BddBelow S := by
      refine ⟨p.1, ?_⟩
      intro x hx
      exact hx.1.1
    let c : ℝ := sInf S
    have hcS : c ∈ S := hSClosed.csInf_mem hSNonempty hSBdd
    have hpc : p.1 ≤ c := hcS.1.1
    have hcA : c ≤ A.1 := hcS.1.2
    have hcEnergyNonpos : energy c ≤ 0 := hcS.2
    have hpEnergyReal : 0 < energy p.1 := by
      rw [henergy_eq p.1 le_rfl]
      exact hpEnergy
    have hpcStrict : p.1 < c := by
      apply hpc.lt_of_ne
      intro hEq
      rw [hEq] at hpEnergyReal
      linarith
    have hcEnergy : energy c = 0 := by
      apply le_antisymm hcEnergyNonpos
      by_contra hnotNonneg
      have hcNeg : energy c < 0 := lt_of_not_ge hnotNonneg
      have hzeroMem : (0 : ℝ) ∈ Icc (energy c) (energy p.1) :=
        ⟨hcNeg.le, hpEnergyReal.le⟩
      obtain ⟨e, heIcc, heZero⟩ :=
        intermediate_value_Icc' hpc henergyContinuous.continuousOn hzeroMem
      have heStrict : e < c := by
        apply heIcc.2.lt_of_ne
        intro hec
        subst e
        linarith
      have heS : e ∈ S := by
        refine ⟨⟨heIcc.1, heIcc.2.trans hcA⟩, ?_⟩
        change energy e ≤ 0
        rw [heZero]
      have hce : c ≤ e := csInf_le hSBdd heS
      exact (not_lt_of_ge hce) heStrict
    let C : SuzukiPositiveAperture := ⟨c, p.2.trans hpcStrict⟩
    have hCEnergy : ccmRestrictedWeilSourceQuadratic C
        (ccmPolarParityFormVector C r) = 0 := by
      rw [← hcEnergy]
      exact (henergy_eq c hpc).symm
    refine ⟨C, r, hr, hCEnergy, ?_⟩
    intro b hbC
    by_cases hbp : b.1 < p.1
    · have hground : 0 < ccmRestrictedWeilGroundEnergy b := by
        apply hsmall
        dsimp only [p] at hbp
        linarith
      have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source b
        (ccmPolarParityFormVector b r)
      rw [norm_sq_ccmPolarParityFormVector_physical b hr] at hfloor
      have hgram := polarParityGram_pos b hr
      nlinarith
    · have hpb : p.1 ≤ b.1 := le_of_not_gt hbp
      by_contra hbNotPos
      have hbNonpos : ccmRestrictedWeilSourceQuadratic b
          (ccmPolarParityFormVector b r) ≤ 0 := le_of_not_gt hbNotPos
      have hbEnergy : energy b.1 = ccmRestrictedWeilSourceQuadratic b
          (ccmPolarParityFormVector b r) := by
        simpa only using henergy_eq b.1 hpb
      have hbS : b.1 ∈ S := by
        refine ⟨⟨hpb, hbC.le.trans hcA⟩, ?_⟩
        change energy b.1 ≤ 0
        rw [hbEnergy]
        exact hbNonpos
      have hcb : c ≤ b.1 := csInf_le hSBdd hbS
      exact (not_lt_of_ge hcb) hbC

/-- Earliest loss of positivity of the entire literal two-pole compression. At contact one fixed
parity eigenvector is null, its companion is nonnegative, and both eigenvalues were strictly
positive at every smaller aperture. -/
def CCMPoleCompressionFirstContact : Prop :=
  ∃ (a : SuzukiPositiveAperture) (r : ℝ),
    (r = 1 ∨ r = -1) ∧
      ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) = 0 ∧
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-r)) ∧
      ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        0 < ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b 1) ∧
        0 < ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1))

/-- Route-level matrix alternative. False RH reaches the pole wall for the first time through a
positive-semidefinite singular literal pole compression, rather than through an unspecified source
or an already-indefinite companion parity. -/
theorem riemannHypothesis_or_ccmPoleCompressionFirstContact :
    RiemannHypothesis ∨ CCMPoleCompressionFirstContact := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    obtain ⟨A, r, hr, hAneg⟩ :=
      not_riemannHypothesis_implies_exists_negative_parityPole hRH
    obtain ⟨delta, hdelta, hsmall⟩ :=
      exists_suzukiSmallAperture_ccmGroundEnergy_pos
    have hAδ : delta ≤ A.1 := by
      by_contra hnot
      exact (not_lt_of_ge
        (parityPoleSourceQuadratic_pos_of_ground_pos A r hr
          (hsmall A (lt_of_not_ge hnot))).le) hAneg
    let p : SuzukiPositiveAperture := ⟨delta / 2, by linarith⟩
    have hpA : p.1 < A.1 := by
      dsimp only [p]
      linarith
    have hpGround : 0 < ccmRestrictedWeilGroundEnergy p := by
      apply hsmall
      dsimp only [p]
      linarith
    have hpPlus : 0 < ccmRestrictedWeilSourceQuadratic p
        (ccmPolarParityFormVector p 1) :=
      parityPoleSourceQuadratic_pos_of_ground_pos p 1 (Or.inl rfl) hpGround
    have hpMinus : 0 < ccmRestrictedWeilSourceQuadratic p
        (ccmPolarParityFormVector p (-1)) :=
      parityPoleSourceQuadratic_pos_of_ground_pos p (-1) (Or.inr rfl) hpGround
    let apertureAt : ℝ → SuzukiPositiveAperture := fun x =>
      ⟨max p.1 x, p.2.trans_le (le_max_left _ _)⟩
    let plus : ℝ → ℝ := fun x =>
      ccmRestrictedWeilSourceQuadratic (apertureAt x)
        (ccmPolarParityFormVector (apertureAt x) 1)
    let minus : ℝ → ℝ := fun x =>
      ccmRestrictedWeilSourceQuadratic (apertureAt x)
        (ccmPolarParityFormVector (apertureAt x) (-1))
    let least : ℝ → ℝ := fun x => min (plus x) (minus x)
    have hapertureContinuous : Continuous apertureAt :=
      (continuous_const.max continuous_id).subtype_mk _
    have hplusContinuous : Continuous plus :=
      (continuous_ccmRestrictedWeil_parityPoleSourceQuadratic 1 (Or.inl rfl)).comp
        hapertureContinuous
    have hminusContinuous : Continuous minus :=
      (continuous_ccmRestrictedWeil_parityPoleSourceQuadratic (-1) (Or.inr rfl)).comp
        hapertureContinuous
    have hleastContinuous : Continuous least := hplusContinuous.min hminusContinuous
    have hplus_eq (x : ℝ) (hx : p.1 ≤ x) :
        plus x = ccmRestrictedWeilSourceQuadratic ⟨x, p.2.trans_le hx⟩
          (ccmPolarParityFormVector ⟨x, p.2.trans_le hx⟩ 1) := by
      have haperture : apertureAt x = ⟨x, p.2.trans_le hx⟩ := by
        apply Subtype.ext
        exact max_eq_right hx
      change ccmRestrictedWeilSourceQuadratic (apertureAt x)
          (ccmPolarParityFormVector (apertureAt x) 1) = _
      rw [haperture]
    have hminus_eq (x : ℝ) (hx : p.1 ≤ x) :
        minus x = ccmRestrictedWeilSourceQuadratic ⟨x, p.2.trans_le hx⟩
          (ccmPolarParityFormVector ⟨x, p.2.trans_le hx⟩ (-1)) := by
      have haperture : apertureAt x = ⟨x, p.2.trans_le hx⟩ := by
        apply Subtype.ext
        exact max_eq_right hx
      change ccmRestrictedWeilSourceQuadratic (apertureAt x)
          (ccmPolarParityFormVector (apertureAt x) (-1)) = _
      rw [haperture]
    have hpLeast : 0 < least p.1 := by
      apply lt_min_iff.mpr
      constructor
      · rw [hplus_eq p.1 le_rfl]
        simpa only using hpPlus
      · rw [hminus_eq p.1 le_rfl]
        simpa only using hpMinus
    have hALeast : least A.1 < 0 := by
      rcases hr with rfl | rfl
      · calc
          least A.1 ≤ plus A.1 := min_le_left _ _
          _ = ccmRestrictedWeilSourceQuadratic
              ⟨A.1, p.2.trans_le hpA.le⟩
              (ccmPolarParityFormVector ⟨A.1, p.2.trans_le hpA.le⟩ 1) :=
            hplus_eq A.1 hpA.le
          _ < 0 := by simpa only using hAneg
      · calc
          least A.1 ≤ minus A.1 := min_le_right _ _
          _ = ccmRestrictedWeilSourceQuadratic
              ⟨A.1, p.2.trans_le hpA.le⟩
              (ccmPolarParityFormVector ⟨A.1, p.2.trans_le hpA.le⟩ (-1)) :=
            hminus_eq A.1 hpA.le
          _ < 0 := by simpa only using hAneg
    let S : Set ℝ := Icc p.1 A.1 ∩ least ⁻¹' Iic 0
    have hSClosed : IsClosed S :=
      isClosed_Icc.inter (isClosed_Iic.preimage hleastContinuous)
    have hAmem : A.1 ∈ S :=
      ⟨right_mem_Icc.mpr hpA.le, hALeast.le⟩
    have hSNonempty : S.Nonempty := ⟨A.1, hAmem⟩
    have hSBdd : BddBelow S := by
      refine ⟨p.1, ?_⟩
      intro x hx
      exact hx.1.1
    let c : ℝ := sInf S
    have hcS : c ∈ S := hSClosed.csInf_mem hSNonempty hSBdd
    have hpc : p.1 ≤ c := hcS.1.1
    have hcA : c ≤ A.1 := hcS.1.2
    have hcLeastNonpos : least c ≤ 0 := hcS.2
    have hpcStrict : p.1 < c := by
      apply hpc.lt_of_ne
      intro hEq
      rw [hEq] at hpLeast
      linarith
    have hcLeast : least c = 0 := by
      apply le_antisymm hcLeastNonpos
      by_contra hnotNonneg
      have hcNeg : least c < 0 := lt_of_not_ge hnotNonneg
      have hzeroMem : (0 : ℝ) ∈ Icc (least c) (least p.1) :=
        ⟨hcNeg.le, hpLeast.le⟩
      obtain ⟨e, heIcc, heZero⟩ :=
        intermediate_value_Icc' hpc hleastContinuous.continuousOn hzeroMem
      have heStrict : e < c := by
        apply heIcc.2.lt_of_ne
        intro hec
        subst e
        linarith
      have heS : e ∈ S := by
        refine ⟨⟨heIcc.1, heIcc.2.trans hcA⟩, ?_⟩
        change least e ≤ 0
        rw [heZero]
      have hce : c ≤ e := csInf_le hSBdd heS
      exact (not_lt_of_ge hce) heStrict
    have hcPlus : 0 ≤ plus c := by
      have h := min_le_left (plus c) (minus c)
      change least c ≤ plus c at h
      rwa [hcLeast] at h
    have hcMinus : 0 ≤ minus c := by
      have h := min_le_right (plus c) (minus c)
      change least c ≤ minus c at h
      rwa [hcLeast] at h
    let C : SuzukiPositiveAperture := ⟨c, p.2.trans hpcStrict⟩
    have hbefore : ∀ b : SuzukiPositiveAperture, b.1 < C.1 →
        0 < ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b 1) ∧
        0 < ccmRestrictedWeilSourceQuadratic b (ccmPolarParityFormVector b (-1)) := by
      intro b hbC
      by_cases hbp : b.1 < p.1
      · have hground : 0 < ccmRestrictedWeilGroundEnergy b := by
          apply hsmall
          dsimp only [p] at hbp
          linarith
        exact ⟨parityPoleSourceQuadratic_pos_of_ground_pos b 1 (Or.inl rfl) hground,
          parityPoleSourceQuadratic_pos_of_ground_pos b (-1) (Or.inr rfl) hground⟩
      · have hpb : p.1 ≤ b.1 := le_of_not_gt hbp
        have hbLeast : 0 < least b.1 := by
          by_contra hbNotPos
          have hbNonpos : least b.1 ≤ 0 := le_of_not_gt hbNotPos
          have hbS : b.1 ∈ S := by
            refine ⟨⟨hpb, hbC.le.trans hcA⟩, hbNonpos⟩
          have hcb : c ≤ b.1 := csInf_le hSBdd hbS
          exact (not_lt_of_ge hcb) hbC
        have hpair : 0 < plus b.1 ∧ 0 < minus b.1 := lt_min_iff.mp hbLeast
        rw [hplus_eq b.1 hpb] at hpair
        rw [hminus_eq b.1 hpb] at hpair
        simpa only using hpair
    by_cases hplusZero : plus c = 0
    · refine ⟨C, 1, Or.inl rfl, ?_, ?_, hbefore⟩
      · rw [← hplus_eq c hpc]
        exact hplusZero
      · rw [← hminus_eq c hpc]
        exact hcMinus
    · have hplusPos : 0 < plus c := lt_of_le_of_ne hcPlus (Ne.symm hplusZero)
      have hminusZero : minus c = 0 := by
        apply le_antisymm
        · by_contra hnot
          have hminusPos : 0 < minus c := lt_of_not_ge hnot
          have : 0 < least c := lt_min_iff.mpr ⟨hplusPos, hminusPos⟩
          linarith
        · exact hcMinus
      refine ⟨C, -1, Or.inr rfl, ?_, ?_, hbefore⟩
      · rw [← hminus_eq c hpc]
        exact hminusZero
      · have hCPlus : 0 ≤ ccmRestrictedWeilSourceQuadratic C
            (ccmPolarParityFormVector C 1) := by
          rw [← hplus_eq c hpc]
          exact hcPlus
        simpa only [neg_neg] using hCPlus

/-- A pole-compression first contact is exactly first arrival at the arithmetic matrix wall
`|cross| = diagonal`; every smaller aperture lies in the strict interior. -/
theorem ccmPoleCompressionFirstContact_exact_wall
    (hcontact : CCMPoleCompressionFirstContact) :
    ∃ a : SuzukiPositiveAperture,
      |ccmWeilPoleCross a| = ccmWeilPoleDiagonal a ∧
      ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
        |ccmWeilPoleCross b| < ccmWeilPoleDiagonal b := by
  obtain ⟨a, r, hr, hzero, hcompanion, hbefore⟩ := hcontact
  refine ⟨a, ?_, ?_⟩
  · rcases hr with rfl | rfl
    · rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl)] at hzero
      rw [ccmWeilPoleCompression_parity_energy a (Or.inr rfl)] at hcompanion
      have hdiag : 0 ≤ ccmWeilPoleDiagonal a := by linarith
      have hcross : ccmWeilPoleCross a = -ccmWeilPoleDiagonal a := by linarith
      rw [hcross, abs_neg, abs_of_nonneg hdiag]
    · rw [ccmWeilPoleCompression_parity_energy a (Or.inr rfl)] at hzero
      have hplus : 0 ≤ ccmRestrictedWeilSourceQuadratic a
          (ccmPolarParityFormVector a 1) := by
        simpa only [neg_neg] using hcompanion
      rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl)] at hplus
      have hdiag : 0 ≤ ccmWeilPoleDiagonal a := by linarith
      have hcross : ccmWeilPoleCross a = ccmWeilPoleDiagonal a := by linarith
      rw [hcross, abs_of_nonneg hdiag]
  · intro b hb
    obtain ⟨hplus, hminus⟩ := hbefore b hb
    rw [ccmWeilPoleCompression_parity_energy b (Or.inl rfl)] at hplus
    rw [ccmWeilPoleCompression_parity_energy b (Or.inr rfl)] at hminus
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Closed first-wall alternative in literal matrix coordinates. It removes all moving source
coefficients: either RH holds, or the exact prime--polar--Gamma pole matrix reaches its singular
wall at a least positive aperture. -/
theorem riemannHypothesis_or_exists_ccmPoleCompression_exact_first_wall :
    RiemannHypothesis ∨
      ∃ a : SuzukiPositiveAperture,
        |ccmWeilPoleCross a| = ccmWeilPoleDiagonal a ∧
        ∀ b : SuzukiPositiveAperture, b.1 < a.1 →
          |ccmWeilPoleCross b| < ccmWeilPoleDiagonal b := by
  rcases riemannHypothesis_or_ccmPoleCompressionFirstContact with hRH | hcontact
  · exact Or.inl hRH
  · exact Or.inr (ccmPoleCompressionFirstContact_exact_wall hcontact)

end RHTower
