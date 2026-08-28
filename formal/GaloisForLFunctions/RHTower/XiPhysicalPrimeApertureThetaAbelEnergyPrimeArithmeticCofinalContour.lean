import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeCanonicalVanishingLimit
import GaloisForLFunctions.RHTower.XiGuinandWeilFiniteHermiteCriterion

/-!
# Universal arithmetic cofinal corrected-prime contours

Earlier canonical contour limits selected a new rectangle from a finite Xi-zero packet and a
target Weil energy.  This module removes both dependencies.  At stage `m`, rational endpoint
pairs are enumerated and the least code is chosen whose box has horizontal radius greater than
`m + 1`, top edge greater than `1/2 - 1/(m+2)`, and admissible zeta boundary.  Its bottom is fixed
at height `-1`, so every box crosses the unique centered archimedean pole.

Finite zero avoidance proves this arithmetic predicate inhabited.  Pure geometric exhaustion then
shows that the resulting single rectangle sequence eventually contains every finite copied Xi
packet.  Consequently, for every physical theta--Abel detector, its corrected direct-prime
contours on this same sequence converge to complete Weil energy.  RH is therefore equivalent to
asymptotic nonnegativity of a fixed, countable, rational, target-independent prime-contour array.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Lower corner of a rational arithmetic box; height `-1` crosses the centered archimedean pole. -/
def xiPhysicalThetaAbelEnergyArithmeticBoxLower (R : ℚ) : ℂ :=
  (-(R : ℝ) : ℂ) - I

/-- Upper corner of a rational arithmetic box. -/
def xiPhysicalThetaAbelEnergyArithmeticBoxUpper (R c : ℚ) : ℂ :=
  ((R : ℝ) : ℂ) + ((c : ℝ) : ℂ) * I

/-- Every edge of the rational arithmetic box is in the continued explicit-formula domain. -/
def XiPhysicalThetaAbelEnergyArithmeticBoxAdmissible (R c : ℚ) : Prop :=
  let z₁ := xiPhysicalThetaAbelEnergyArithmeticBoxLower R
  let z₂ := xiPhysicalThetaAbelEnergyArithmeticBoxUpper R c
  (∀ x ∈ uIcc z₁.re z₂.re,
    XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) ∧
  (∀ x ∈ uIcc z₁.re z₂.re,
    XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) ∧
  (∀ y ∈ uIcc z₁.im z₂.im,
    XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) ∧
  (∀ y ∈ uIcc z₁.im z₂.im,
    XiExplicitAdmissible ((z₁.re : ℂ) + y * I))

/-- Target-independent stage predicate: geometric exhaustion plus arithmetic boundary admission. -/
def XiPhysicalThetaAbelEnergyArithmeticBoxStage (m : ℕ) (p : ℚ × ℚ) : Prop :=
  (m : ℝ) + 1 < (p.1 : ℝ) ∧
  1 / 2 - 1 / ((m : ℝ) + 2) < (p.2 : ℝ) ∧
  (p.2 : ℝ) < 1 / 2 ∧
  XiPhysicalThetaAbelEnergyArithmeticBoxAdmissible p.1 p.2

private theorem exists_ratCast_Ioo_not_mem_finset_loop88 {a b : ℝ} (hab : a < b)
    (F : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ F ∧ ∃ q : ℚ, x = (q : ℝ) := by
  let U : Set ℝ := Set.Ioo a b \ (F : Set ℝ)
  have hIoo : IsOpen (Set.Ioo a b) := _root_.isOpen_Ioo
  have hUopen : IsOpen U := IsOpen.sdiff hIoo F.finite_toSet.isClosed
  have hUinfinite : U.Infinite := (Set.Ioo_infinite hab).sdiff F.finite_toSet
  have hUne : U.Nonempty := hUinfinite.nonempty
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hUopen hUne
  refine ⟨(q : ℝ), hq.1, ?_, q, rfl⟩
  simpa using hq.2

/-- Every stage admits a rational pole-crossing box satisfying the arithmetic predicate. -/
theorem exists_arithmeticBoxStage (m : ℕ) :
    ∃ p : ℚ × ℚ, XiPhysicalThetaAbelEnergyArithmeticBoxStage m p := by
  classical
  let R₀ : ℝ := (m : ℝ) + 2
  let R₁ : ℝ := R₀ + 1
  let c₀ : ℝ := 1 / 2 - 1 / ((m : ℝ) + 2)
  let raw₁ : ℂ := (-R₁ : ℂ) - I
  let raw₂ : ℂ := (R₁ : ℂ) + (1 / 2 : ℝ) * I
  let Z : Finset ℂ := xiCClosedRectangleZeros raw₁ raw₂
  let Fre : Finset ℝ := Z.image (fun z => |z.re|)
  let Fim : Finset ℝ := Z.image (fun z => z.im)
  have hR₀R₁ : R₀ < R₁ := by dsimp only [R₁]; linarith
  have hc₀half : c₀ < 1 / 2 := by
    dsimp only [c₀]
    have : 0 < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  obtain ⟨R, hRI, hRavoid, Rq, hRq⟩ :=
    exists_ratCast_Ioo_not_mem_finset_loop88 hR₀R₁ Fre
  obtain ⟨c, hcI, hcavoid, cq, hcq⟩ :=
    exists_ratCast_Ioo_not_mem_finset_loop88 hc₀half Fim
  have hRpos : 0 < R := by
    dsimp only [R₀] at hRI
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith [hRI.1]
  have hcpos : 0 < c := by
    dsimp only [c₀] at hcI
    have hden : 0 < (m : ℝ) + 2 := by positivity
    have hinv : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      have hm : 0 ≤ (m : ℝ) := by positivity
      norm_num
      linarith
    have hc₀nonneg : 0 ≤ 1 / 2 - 1 / ((m : ℝ) + 2) := by
      linarith
    linarith [hcI.1]
  have hraw_mem {z : ℂ} (hre : |z.re| ≤ R₁) (himL : -1 ≤ z.im)
      (himR : z.im ≤ 1 / 2) :
      z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
    apply Complex.mem_reProdIm.mpr
    have hR₁pos : 0 < R₁ := hRpos.trans (hRI.2)
    rw [Set.uIcc_of_le (by simp [raw₁, raw₂]; linarith),
      Set.uIcc_of_le (by simp [raw₁, raw₂]; norm_num)]
    constructor
    · simpa [raw₁, raw₂] using (abs_le.mp hre)
    · simpa [raw₁, raw₂] using And.intro himL himR
  have hzero_mem_Z {z : ℂ}
      (hraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im))
      (hz : XiC z = 0) : z ∈ Z :=
    mem_xiCClosedRectangleZeros.mpr ⟨hraw, hz⟩
  have hbottomZero : ∀ x ∈ Set.uIcc (-R) R,
      XiC ((x : ℂ) - I) ≠ 0 := by
    intro x hx hzero
    have him := (xiC_zero_im_mem_openHalf hzero).1
    norm_num at him
  have htopZero : ∀ x ∈ Set.uIcc (-R) R,
      XiC ((x : ℂ) + (c : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hxI : -R ≤ x ∧ x ≤ R := by
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact hx
    let z : ℂ := (x : ℂ) + (c : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, zero_mul, I_im,
          mul_zero]
        rw [abs_le]
        constructor <;> linarith [hxI.1, hxI.2, hRI.2]
      · dsimp only [z]
        simp
        linarith
      · dsimp only [z]
        simp
        norm_num at hcI ⊢
        exact hcI.2.le
    have hzZ := hzero_mem_Z hzraw hzero
    apply hcavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z]⟩
  have hrightZero : ∀ y ∈ Set.uIcc (-1) c,
      XiC ((R : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -1 ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    let z : ℂ := (R : ℂ) + (y : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        simp [abs_of_pos hRpos]
        exact hRI.2.le
      · dsimp only [z]
        simpa using hyI.1
      · dsimp only [z]
        simp
        norm_num at hcI ⊢
        exact hyI.2.trans hcI.2.le
    have hzZ := hzero_mem_Z hzraw hzero
    apply hRavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z, abs_of_pos hRpos]⟩
  have hleftZero : ∀ y ∈ Set.uIcc (-1) c,
      XiC ((-R : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy hzero
    have hyI : -1 ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    let z : ℂ := (-R : ℂ) + (y : ℂ) * I
    have hzraw : z ∈ (Set.uIcc raw₁.re raw₂.re ×ℂ Set.uIcc raw₁.im raw₂.im) := by
      apply hraw_mem
      · dsimp only [z]
        simp [abs_of_pos hRpos]
        exact hRI.2.le
      · dsimp only [z]
        simpa using hyI.1
      · dsimp only [z]
        simp
        norm_num at hcI ⊢
        exact hyI.2.trans hcI.2.le
    have hzZ := hzero_mem_Z hzraw hzero
    apply hRavoid
    exact Finset.mem_image.mpr ⟨z, hzZ, by simp [z, abs_of_pos hRpos]⟩
  have hne_one_of_im_ne {z : ℂ} (hzim : z.im ≠ -1 / 2) :
      (1 / 2 + z * I) ≠ 1 := by
    intro h
    have hreEq := congrArg Complex.re h
    simp [Complex.mul_re] at hreEq
    apply hzim
    linarith
  have hne_one_of_re_ne_zero {z : ℂ} (hzre : z.re ≠ 0) :
      (1 / 2 + z * I) ≠ 1 := by
    intro h
    have himEq := congrArg Complex.im h
    simp [Complex.mul_im] at himEq
    exact hzre himEq
  have hbottomAdm : ∀ x ∈ Set.uIcc (-R) R,
      XiExplicitAdmissible ((x : ℂ) - I) := by
    intro x hx
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      norm_num
    · apply hne_one_of_im_ne
      simp
      norm_num
    · exact hbottomZero x hx
  have htopAdm : ∀ x ∈ Set.uIcc (-R) R,
      XiExplicitAdmissible ((x : ℂ) + (c : ℂ) * I) := by
    intro x hx
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simpa using hcI.2
    · apply hne_one_of_im_ne
      simp
      linarith [hcpos]
    · exact htopZero x hx
  have hrightAdm : ∀ y ∈ Set.uIcc (-1) c,
      XiExplicitAdmissible ((R : ℂ) + (y : ℂ) * I) := by
    intro y hy
    have hyI : -1 ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      norm_num at hcI ⊢
      exact hyI.2.trans_lt hcI.2
    · apply hne_one_of_re_ne_zero
      simp [ne_of_gt hRpos]
    · exact hrightZero y hy
  have hleftAdm : ∀ y ∈ Set.uIcc (-1) c,
      XiExplicitAdmissible ((-R : ℂ) + (y : ℂ) * I) := by
    intro y hy
    have hyI : -1 ≤ y ∧ y ≤ c := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      exact hy
    apply XiExplicitAdmissible_of_im_lt_half_of_ne_one_of_XiC_ne_zero
    · simp
      norm_num at hcI ⊢
      exact hyI.2.trans_lt hcI.2
    · apply hne_one_of_re_ne_zero
      simp [ne_of_gt hRpos]
    · exact hleftZero y hy
  subst R
  subst c
  refine ⟨(Rq, cq), ?_, ?_, ?_, ?_⟩
  · dsimp only [R₀] at hRI
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith [hRI.1]
  · exact hcI.1
  · exact hcI.2
  · simpa [XiPhysicalThetaAbelEnergyArithmeticBoxAdmissible, sub_eq_add_neg,
      xiPhysicalThetaAbelEnergyArithmeticBoxLower,
      xiPhysicalThetaAbelEnergyArithmeticBoxUpper] using
      And.intro hbottomAdm (And.intro htopAdm (And.intro hrightAdm hleftAdm))

/-- Fixed surjective enumeration of rational endpoint pairs. -/
def xiPhysicalThetaAbelEnergyRationalPair (N : ℕ) : ℚ × ℚ :=
  (Encodable.decode (α := ℚ × ℚ) N).getD (0, 0)

theorem xiPhysicalThetaAbelEnergyRationalPair_surjective (p : ℚ × ℚ) :
    ∃ N : ℕ, xiPhysicalThetaAbelEnergyRationalPair N = p := by
  obtain ⟨N, hN⟩ := Encodable.surjective_decode_getD (ℚ × ℚ) (0, 0) p
  exact ⟨N, hN⟩

/-- Some rational-pair code satisfies every stage predicate. -/
theorem exists_arithmeticBoxStageCode (m : ℕ) :
    ∃ N : ℕ,
      XiPhysicalThetaAbelEnergyArithmeticBoxStage m
        (xiPhysicalThetaAbelEnergyRationalPair N) := by
  obtain ⟨p, hp⟩ := exists_arithmeticBoxStage m
  obtain ⟨N, rfl⟩ := xiPhysicalThetaAbelEnergyRationalPair_surjective p
  exact ⟨N, hp⟩

/-- Least code of a rational admissible pole-crossing box at geometric stage `m`. -/
noncomputable def xiPhysicalThetaAbelEnergyArithmeticBoxCode (m : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_arithmeticBoxStageCode m)

/-- Rational endpoint pair decoded from the least admissible code. -/
noncomputable def xiPhysicalThetaAbelEnergyArithmeticBox (m : ℕ) : ℚ × ℚ :=
  xiPhysicalThetaAbelEnergyRationalPair
    (xiPhysicalThetaAbelEnergyArithmeticBoxCode m)

theorem xiPhysicalThetaAbelEnergyArithmeticBox_spec (m : ℕ) :
    XiPhysicalThetaAbelEnergyArithmeticBoxStage m
      (xiPhysicalThetaAbelEnergyArithmeticBox m) := by
  classical
  simpa [xiPhysicalThetaAbelEnergyArithmeticBox,
    xiPhysicalThetaAbelEnergyArithmeticBoxCode] using
    (Nat.find_spec (exists_arithmeticBoxStageCode m))

theorem xiPhysicalThetaAbelEnergyArithmeticBoxCode_minimal (m N : ℕ)
    (hN : XiPhysicalThetaAbelEnergyArithmeticBoxStage m
      (xiPhysicalThetaAbelEnergyRationalPair N)) :
    xiPhysicalThetaAbelEnergyArithmeticBoxCode m ≤ N := by
  classical
  simpa [xiPhysicalThetaAbelEnergyArithmeticBoxCode] using
    (Nat.find_min' (exists_arithmeticBoxStageCode m) hN)

/-- Lower and upper corners of the least-coded arithmetic box. -/
noncomputable def xiPhysicalThetaAbelEnergyArithmeticLower (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyArithmeticBoxLower
    (xiPhysicalThetaAbelEnergyArithmeticBox m).1

noncomputable def xiPhysicalThetaAbelEnergyArithmeticUpper (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyArithmeticBoxUpper
    (xiPhysicalThetaAbelEnergyArithmeticBox m).1
    (xiPhysicalThetaAbelEnergyArithmeticBox m).2

theorem xiPhysicalThetaAbelEnergyArithmetic_geometry (m : ℕ) :
    (m : ℝ) + 1 < (xiPhysicalThetaAbelEnergyArithmeticUpper m).re ∧
    (xiPhysicalThetaAbelEnergyArithmeticLower m).re =
      -(xiPhysicalThetaAbelEnergyArithmeticUpper m).re ∧
    (xiPhysicalThetaAbelEnergyArithmeticLower m).im = -1 ∧
    1 / 2 - 1 / ((m : ℝ) + 2) <
      (xiPhysicalThetaAbelEnergyArithmeticUpper m).im ∧
    (xiPhysicalThetaAbelEnergyArithmeticUpper m).im < 1 / 2 := by
  have h := xiPhysicalThetaAbelEnergyArithmeticBox_spec m
  rcases h with ⟨hR, hcL, hcU, _⟩
  constructor
  · simpa [xiPhysicalThetaAbelEnergyArithmeticUpper,
      xiPhysicalThetaAbelEnergyArithmeticBoxUpper] using hR
  constructor
  · simp [xiPhysicalThetaAbelEnergyArithmeticLower,
      xiPhysicalThetaAbelEnergyArithmeticUpper,
      xiPhysicalThetaAbelEnergyArithmeticBoxLower,
      xiPhysicalThetaAbelEnergyArithmeticBoxUpper]
  constructor
  · simp [xiPhysicalThetaAbelEnergyArithmeticLower,
      xiPhysicalThetaAbelEnergyArithmeticBoxLower]
  constructor
  · simpa [xiPhysicalThetaAbelEnergyArithmeticUpper,
      xiPhysicalThetaAbelEnergyArithmeticBoxUpper] using hcL
  · simpa [xiPhysicalThetaAbelEnergyArithmeticUpper,
      xiPhysicalThetaAbelEnergyArithmeticBoxUpper] using hcU

/-- The selected least-coded box has four admissible edges. -/
theorem xiPhysicalThetaAbelEnergyArithmetic_admissible (m : ℕ) :
    (∀ x ∈ uIcc (xiPhysicalThetaAbelEnergyArithmeticLower m).re
        (xiPhysicalThetaAbelEnergyArithmeticUpper m).re,
      XiExplicitAdmissible
        ((x : ℂ) + (xiPhysicalThetaAbelEnergyArithmeticLower m).im * I)) ∧
    (∀ x ∈ uIcc (xiPhysicalThetaAbelEnergyArithmeticLower m).re
        (xiPhysicalThetaAbelEnergyArithmeticUpper m).re,
      XiExplicitAdmissible
        ((x : ℂ) + (xiPhysicalThetaAbelEnergyArithmeticUpper m).im * I)) ∧
    (∀ y ∈ uIcc (xiPhysicalThetaAbelEnergyArithmeticLower m).im
        (xiPhysicalThetaAbelEnergyArithmeticUpper m).im,
      XiExplicitAdmissible
        (((xiPhysicalThetaAbelEnergyArithmeticUpper m).re : ℂ) + y * I)) ∧
    (∀ y ∈ uIcc (xiPhysicalThetaAbelEnergyArithmeticLower m).im
        (xiPhysicalThetaAbelEnergyArithmeticUpper m).im,
      XiExplicitAdmissible
        (((xiPhysicalThetaAbelEnergyArithmeticLower m).re : ℂ) + y * I)) := by
  exact (xiPhysicalThetaAbelEnergyArithmeticBox_spec m).2.2.2

/-- Every copied Xi divisor point is eventually enclosed by the universal arithmetic boxes. -/
theorem eventually_mem_xiPhysicalThetaAbelEnergyArithmeticRectangle
    (q : XiZeroCopy) :
    ∀ᶠ m : ℕ in atTop,
      q ∈ xiZeroCopyClosedRectangle
        (xiPhysicalThetaAbelEnergyArithmeticLower m)
        (xiPhysicalThetaAbelEnergyArithmeticUpper m) := by
  have hreEvent : ∀ᶠ m : ℕ in atTop,
      |(xiSpectralPoint q).re| < (m : ℝ) + 1 := by
    obtain ⟨M, hM⟩ := exists_nat_gt |(xiSpectralPoint q).re|
    filter_upwards [eventually_ge_atTop M] with m hm
    have hcast : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have himGap : 0 < (1 / 2 : ℝ) - (xiSpectralPoint q).im := by
    linarith [(xiSpectralPoint_im_mem_openHalf q).2]
  have hinvTend : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1) using 1
    funext m
    simp [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have himEvent : ∀ᶠ m : ℕ in atTop,
      1 / ((m : ℝ) + 2) < (1 / 2 : ℝ) - (xiSpectralPoint q).im :=
    hinvTend.eventually (Iio_mem_nhds himGap)
  filter_upwards [hreEvent, himEvent] with m hre him
  rw [mem_xiZeroCopyClosedRectangle]
  apply Complex.mem_reProdIm.mpr
  have hgeom := xiPhysicalThetaAbelEnergyArithmetic_geometry m
  rcases hgeom with ⟨hR, hsymm, hbot, htopL, htopU⟩
  have hLR : (xiPhysicalThetaAbelEnergyArithmeticLower m).re ≤
      (xiPhysicalThetaAbelEnergyArithmeticUpper m).re := by
    rw [hsymm]
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hBT : (xiPhysicalThetaAbelEnergyArithmeticLower m).im ≤
      (xiPhysicalThetaAbelEnergyArithmeticUpper m).im := by
    have hden : 0 < (m : ℝ) + 2 := by positivity
    have hinv : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      have hm : 0 ≤ (m : ℝ) := by positivity
      norm_num
      linarith
    rw [hbot]
    linarith [htopL]
  rw [uIcc_of_le hLR, uIcc_of_le hBT]
  constructor
  · rw [hsymm]
    have habs := abs_lt.mp (hre.trans hR)
    exact ⟨habs.1.le, habs.2.le⟩
  · constructor
    · rw [hbot]
      linarith [(xiSpectralPoint_im_mem_openHalf q).1]
    · linarith

/-- Every finite copied Xi packet is eventually enclosed by the universal arithmetic boxes. -/
theorem eventually_finset_subset_xiPhysicalThetaAbelEnergyArithmeticRectangle
    (t : Finset XiZeroCopy) :
    ∀ᶠ m : ℕ in atTop,
      t ≤ xiZeroCopyClosedRectangle
        (xiPhysicalThetaAbelEnergyArithmeticLower m)
        (xiPhysicalThetaAbelEnergyArithmeticUpper m) := by
  change ∀ᶠ m : ℕ in atTop, ∀ q ∈ t,
    q ∈ xiZeroCopyClosedRectangle
      (xiPhysicalThetaAbelEnergyArithmeticLower m)
      (xiPhysicalThetaAbelEnergyArithmeticUpper m)
  rw [Finset.eventually_all]
  intro q hq
  exact eventually_mem_xiPhysicalThetaAbelEnergyArithmeticRectangle q

/-- Finite zero sums on the universal arithmetic boxes converge to complete Weil energy. -/
theorem tendsto_xiPhysicalThetaAbelEnergyArithmeticZeroSum_weil
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      ∑ q ∈ xiZeroCopyClosedRectangle
          (xiPhysicalThetaAbelEnergyArithmeticLower m)
          (xiPhysicalThetaAbelEnergyArithmeticUpper m),
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
          (xiSpectralPoint q) ^ 2) atTop
      (𝓝 (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a))) := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
      (xiSpectralPoint q) ^ 2
  have hsum : Summable f :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_summable hA hc L a
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hball : Metric.ball (∑' q, f q) ε ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hε
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) ε :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  filter_upwards [eventually_finset_subset_xiPhysicalThetaAbelEnergyArithmeticRectangle t]
      with m hm
  have hnear := ht
    (xiZeroCopyClosedRectangle
      (xiPhysicalThetaAbelEnergyArithmeticLower m)
      (xiPhysicalThetaAbelEnergyArithmeticUpper m)) hm
  rw [Metric.mem_ball] at hnear
  simpa [f, xiWeilPolarization_physicalThetaAbelEnergy_eq_tsum_sq] using hnear

/-- Every universal arithmetic box has the pole-crossing geometry required by prime correction. -/
theorem xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry (m : ℕ) :
    (xiPhysicalThetaAbelEnergyArithmeticLower m).re <
        (xiPhysicalThetaAbelEnergyArithmeticUpper m).re ∧
    (xiPhysicalThetaAbelEnergyArithmeticLower m).im <
        (xiPhysicalThetaAbelEnergyArithmeticUpper m).im ∧
    (xiPhysicalThetaAbelEnergyArithmeticLower m).re < 0 ∧
    0 < (xiPhysicalThetaAbelEnergyArithmeticUpper m).re ∧
    (xiPhysicalThetaAbelEnergyArithmeticLower m).im < -(1 / 2) ∧
    -(1 / 2) < (xiPhysicalThetaAbelEnergyArithmeticUpper m).im ∧
    (xiPhysicalThetaAbelEnergyArithmeticUpper m).im < 1 / 2 := by
  obtain ⟨hR, hsymm, hbot, htopL, htopU⟩ :=
    xiPhysicalThetaAbelEnergyArithmetic_geometry m
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hRpos : 0 < (xiPhysicalThetaAbelEnergyArithmeticUpper m).re := by
    linarith
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hinv : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).2
    norm_num
    linarith
  have hctop : 0 < (xiPhysicalThetaAbelEnergyArithmeticUpper m).im := by
    linarith
  constructor
  · rw [hsymm]
    linarith
  constructor
  · rw [hbot]
    linarith
  constructor
  · rw [hsymm]
    linarith
  exact ⟨hRpos, by rw [hbot]; norm_num, by linarith, htopU⟩

/-- Corrected direct-prime contour on the universal least-coded rational box. -/
noncomputable def xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample
    (L A c a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour L A c a
    (xiPhysicalThetaAbelEnergyArithmeticLower m)
    (xiPhysicalThetaAbelEnergyArithmeticUpper m)

/-- Raw direct-prime contour on the same universal arithmetic box. -/
noncomputable def xiPhysicalThetaAbelEnergyArithmeticPrimeSample
    (L A c a : ℝ) (m : ℕ) : ℂ :=
  xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour L A c a
    (xiPhysicalThetaAbelEnergyArithmeticLower m)
    (xiPhysicalThetaAbelEnergyArithmeticUpper m)

theorem xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_eq_zeroSum
    (L A c a : ℝ) (m : ℕ) :
    xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample L A c a m =
      ∑ q ∈ xiZeroCopyClosedRectangle
          (xiPhysicalThetaAbelEnergyArithmeticLower m)
          (xiPhysicalThetaAbelEnergyArithmeticUpper m),
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
          (xiSpectralPoint q) ^ 2 := by
  obtain ⟨hbot, htop, hright, hleft⟩ :=
    xiPhysicalThetaAbelEnergyArithmetic_admissible m
  obtain ⟨hre, him, hleftGeom, hrightGeom, hbelow, habove, htopGeom⟩ :=
    xiPhysicalThetaAbelEnergyArithmetic_poleCrossing_geometry m
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a)
      hre him hbot htop hright hleft
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample,
    ← xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
      hbot htop hright hleft him hleftGeom hrightGeom hbelow habove htopGeom,
    xiPhysicalThetaAbelEnergyNormalizedSourceContour, hcontour,
    ← mul_assoc, inv_mul_cancel₀ hC, one_mul]

/-- The target-independent arithmetic corrected-prime contours converge exactly to Weil energy. -/
theorem tendsto_xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_weil
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample L A c a m) atTop
      (𝓝 (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a))) := by
  simpa only [xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_eq_zeroSum]
    using tendsto_xiPhysicalThetaAbelEnergyArithmeticZeroSum_weil hA hc L a

/-- The raw arithmetic prime contours converge after subtracting the explicit archimedean square. -/
theorem tendsto_xiPhysicalThetaAbelEnergyArithmeticPrimeSample_weil_sub_archSq
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (L a : ℝ) :
    Tendsto (fun m : ℕ =>
      xiPhysicalThetaAbelEnergyArithmeticPrimeSample L A c a m) atTop
      (𝓝 (xiWeilPolarization
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a) -
        (((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ 2))) := by
  have h := tendsto_xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_weil
    hA hc L a
  let K : ℂ :=
    (((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ 2)
  have hconst : Tendsto (fun _ : ℕ => K) atTop (𝓝 K) := tendsto_const_nhds
  have hsub := h.sub hconst
  dsimp only [K] at hsub
  simpa [xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample,
    xiPhysicalThetaAbelEnergyArithmeticPrimeSample,
    xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour] using hsub

/-- Asymptotic zero-floor condition along the universal least-coded arithmetic rectangles. -/
def XiPhysicalThetaAbelEnergyArithmeticAsymptoticallyNonnegative
    (L A c : ℝ) : Prop :=
  ∀ n : ℕ, L < Real.log n / 2 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ m : ℕ in atTop,
      -ε < (xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample
        L A c (Real.log n / 2) m).re

/-- RH is exactly zero-floor asymptotic nonnegativity on the universal arithmetic contour array. -/
theorem arithmeticAsymptoticallyNonnegative_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyArithmeticAsymptoticallyNonnegative L A c ↔
      RiemannHypothesis := by
  constructor
  · intro hasym
    rw [riemannHypothesis_iff_physicalThetaAbelEnergy_logSample_weil_nonneg
      hL hA hc]
    intro n hLn
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    have hrelim : Tendsto
        (fun m : ℕ =>
          (xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample
            L A c (Real.log n / 2) m).re) atTop (𝓝 W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (tendsto_xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_weil
          hA hc L (Real.log n / 2))
    by_contra hW
    have hWneg : W.re < 0 := lt_of_not_ge hW
    let ε : ℝ := -W.re / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    have hlower := hasym n hLn ε hε
    have hupper : ∀ᶠ m : ℕ in atTop,
        (xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample
          L A c (Real.log n / 2) m).re < -ε := by
      exact hrelim.eventually (Iio_mem_nhds (by
        dsimp only [ε]
        linarith))
    obtain ⟨m, hmLower, hmUpper⟩ := (hlower.and hupper).exists
    linarith
  · intro hRH n _hLn ε hε
    let W : ℂ := xiWeilPolarization
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
    have hweil : 0 ≤ W.re :=
      (riemannHypothesis_iff_xiWeilPolarization_nonneg.mp hRH)
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2))
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform_squareSummable
          hA hc L (Real.log n / 2))
    have hrelim : Tendsto
        (fun m : ℕ =>
          (xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample
            L A c (Real.log n / 2) m).re) atTop (𝓝 W.re) :=
      (Complex.continuous_re.tendsto _).comp
        (tendsto_xiPhysicalThetaAbelEnergyArithmeticCorrectedPrimeSample_weil
          hA hc L (Real.log n / 2))
    exact hrelim.eventually
      (Ioi_mem_nhds (lt_of_lt_of_le (neg_lt_zero.mpr hε) hweil))

/-- Closed unit-parameter arithmetic corrected-prime criterion for RH. -/
theorem unitArithmeticAsymptoticallyNonnegative_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyArithmeticAsymptoticallyNonnegative 1 1 1 ↔
      RiemannHypothesis := by
  exact arithmeticAsymptoticallyNonnegative_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
