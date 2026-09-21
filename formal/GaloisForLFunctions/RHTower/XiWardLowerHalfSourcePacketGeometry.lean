import GaloisForLFunctions.RHTower.XiWardTriangularSourceRectangle

/-!
# Lower-half source packet geometry for the Ward route

A finite source rectangle in the lower spectral half-plane is not an abstract
zero packet.  If its real coordinate is positive, it contains precisely the
strict-right, positive-ordinate Xi copies.  Reflection across the imaginary
axis remains in the lower half-plane and contains precisely their Schwarz
mates.  Thus the two literal Cauchy source rectangles required by the Ward
annulus have one common finite packet before any sign choice or scalarization.

The remaining Ward problem is global: select and average these literal
rectangles cofinally with a uniform source integrability estimate.
-/

open Complex Set intervalIntegral
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Lower-left corner of the source rectangle obtained by Schwarz-reflecting
a lower-half spectral rectangle across the imaginary axis. -/
def xiWardLowerHalfSourceMirrorLower (z₁ z₂ : ℂ) : ℂ :=
  (-(z₂.re) : ℂ) + z₁.im * I

/-- Upper-right corner of the source rectangle obtained by Schwarz-reflecting
a lower-half spectral rectangle across the imaginary axis. -/
def xiWardLowerHalfSourceMirrorUpper (z₁ z₂ : ℂ) : ℂ :=
  (-(z₁.re) : ℂ) + z₂.im * I

/-- Every lower-right spectral rectangle is exactly a finite packet of strict-right
upper Xi multiplicity copies.  This is a geometric identification, independent
of any zero-density estimate or source-sign choice. -/
theorem exists_xiRightUpper_packet_eq_lowerRight_rectangle
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hrepos : 0 < z₁.re) (himneg : z₂.im < 0) :
    ∃ S : Finset XiRightUpperZeroCopy,
      xiZeroCopyClosedRectangle z₁ z₂ = S.map xiRightUpperZeroCopyEmbedding := by
  classical
  let A : Finset XiZeroCopy := xiZeroCopyClosedRectangle z₁ z₂
  let e : {q : XiZeroCopy // q ∈ A} ↪ XiRightUpperZeroCopy :=
    { toFun := fun q =>
        ⟨⟨q.1, by
          have hcoord := Complex.mem_reProdIm.mp
            ((mem_xiZeroCopyClosedRectangle.mp q.2))
          rw [uIcc_of_le hre.le, uIcc_of_le him.le] at hcoord
          change 0 < (I * xiSpectralPoint q.1).re
          simp only [Complex.mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
          linarith [hcoord.2.2]
        ⟩, by
          change 0 < (I * xiSpectralPoint q.1).im
          simp only [Complex.mul_im, I_re, zero_mul, I_im, one_mul]
          have hcoord := Complex.mem_reProdIm.mp
            ((mem_xiZeroCopyClosedRectangle.mp q.2))
          rw [uIcc_of_le hre.le, uIcc_of_le him.le] at hcoord
          linarith [hcoord.1.1]
        ⟩
      inj' := by
        intro q r h
        apply Subtype.ext
        exact congrArg (fun s : XiRightUpperZeroCopy => s.1.1) h }
  refine ⟨A.attach.map e, ?_⟩
  ext q
  constructor
  · intro hq
    have hattach : ⟨q, hq⟩ ∈ A.attach := A.mem_attach _
    refine Finset.mem_map.mpr ⟨e ⟨q, hq⟩,
      Finset.mem_map.mpr ⟨⟨q, hq⟩, hattach, rfl⟩, ?_⟩
    rfl
  · intro hq
    obtain ⟨r, hr, hrq⟩ := Finset.mem_map.mp hq
    obtain ⟨q', hq', hq'r⟩ := Finset.mem_map.mp hr
    rw [← hq'r] at hrq
    change q'.1 = q at hrq
    rw [← hrq]
    exact q'.2

/-- Membership in the reflected lower-half rectangle is exactly membership of
the Schwarz-conjugate copy in the original rectangle. -/
theorem mem_xiWardLowerHalfSourceMirror_iff_copyConj_mem
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (q : XiZeroCopy) :
    q ∈ xiZeroCopyClosedRectangle
      (xiWardLowerHalfSourceMirrorLower z₁ z₂)
      (xiWardLowerHalfSourceMirrorUpper z₁ z₂) ↔
      xiZeroCopyConjEquiv q ∈ xiZeroCopyClosedRectangle z₁ z₂ := by
  rw [mem_xiZeroCopyClosedRectangle, mem_xiZeroCopyClosedRectangle,
    xiSpectralPoint_copyConj]
  have hmirrorLowerRe :
      (xiWardLowerHalfSourceMirrorLower z₁ z₂).re = -z₂.re := by
    simp [xiWardLowerHalfSourceMirrorLower, Complex.mul_re]
  have hmirrorUpperRe :
      (xiWardLowerHalfSourceMirrorUpper z₁ z₂).re = -z₁.re := by
    simp [xiWardLowerHalfSourceMirrorUpper, Complex.mul_re]
  have hmirrorLowerIm :
      (xiWardLowerHalfSourceMirrorLower z₁ z₂).im = z₁.im := by
    simp [xiWardLowerHalfSourceMirrorLower, Complex.mul_im]
  have hmirrorUpperIm :
      (xiWardLowerHalfSourceMirrorUpper z₁ z₂).im = z₂.im := by
    simp [xiWardLowerHalfSourceMirrorUpper, Complex.mul_im]
  constructor
  · intro h
    have hcoord := Complex.mem_reProdIm.mp h
    rw [uIcc_of_le (by rw [hmirrorLowerRe, hmirrorUpperRe]; linarith),
      hmirrorLowerIm, hmirrorUpperIm, uIcc_of_le him.le] at hcoord
    rw [hmirrorLowerRe, hmirrorUpperRe] at hcoord
    rcases hcoord with ⟨⟨hReLower, hReUpper⟩, ⟨hImLower, hImUpper⟩⟩
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le hre.le, uIcc_of_le him.le]
    simp only [Complex.conj_re, Complex.neg_re, Complex.conj_im,
      Complex.neg_im, neg_neg]
    constructor <;> constructor <;> linarith
  · intro h
    have hcoord := Complex.mem_reProdIm.mp h
    rw [uIcc_of_le hre.le, uIcc_of_le him.le] at hcoord
    simp only [Complex.conj_re, Complex.neg_re, Complex.conj_im,
      Complex.neg_im, neg_neg] at hcoord
    rcases hcoord with ⟨⟨hReLower, hReUpper⟩, ⟨hImLower, hImUpper⟩⟩
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le (by rw [hmirrorLowerRe, hmirrorUpperRe]; linarith),
      hmirrorLowerIm, hmirrorUpperIm, uIcc_of_le him.le]
    rw [hmirrorLowerRe, hmirrorUpperRe]
    constructor <;> constructor <;> linarith

/-- A lower-right source rectangle and its lower-half mirror carry exactly one
finite strict-right-upper packet and its Schwarz mate packet, respectively. -/
theorem exists_xiRightUpper_pair_packets_eq_lowerRight_and_mirror
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hrepos : 0 < z₁.re) (himneg : z₂.im < 0) :
    ∃ S : Finset XiRightUpperZeroCopy,
      xiZeroCopyClosedRectangle z₁ z₂ = S.map xiRightUpperZeroCopyEmbedding ∧
      xiZeroCopyClosedRectangle
          (xiWardLowerHalfSourceMirrorLower z₁ z₂)
          (xiWardLowerHalfSourceMirrorUpper z₁ z₂) =
        S.map xiRightUpperConjZeroCopyEmbedding := by
  obtain ⟨S, hS⟩ := exists_xiRightUpper_packet_eq_lowerRight_rectangle
    hre him hrepos himneg
  refine ⟨S, hS, ?_⟩
  ext q
  apply (mem_xiWardLowerHalfSourceMirror_iff_copyConj_mem hre him q).trans
  rw [hS]
  constructor
  · intro h
    obtain ⟨r, hr, hrq⟩ := Finset.mem_map.mp h
    refine Finset.mem_map.mpr ⟨r, hr, ?_⟩
    change r.1.1 = xiZeroCopyConjEquiv q at hrq
    change xiZeroCopyConjEquiv r.1.1 = q
    rw [hrq]
    exact xiZeroCopyConjEquiv_apply_apply _
  · intro h
    obtain ⟨r, hr, hrq⟩ := Finset.mem_map.mp h
    refine Finset.mem_map.mpr ⟨r, hr, ?_⟩
    change xiZeroCopyConjEquiv r.1.1 = q at hrq
    change r.1.1 = xiZeroCopyConjEquiv q
    rw [← hrq]
    exact (xiZeroCopyConjEquiv_apply_apply _).symm

end

end RHTower
