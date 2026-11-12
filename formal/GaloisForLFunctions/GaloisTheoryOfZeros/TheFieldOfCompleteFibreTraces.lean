import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility
import Mathlib.Algebra.Field.Subfield.Basic
import GaloisForLFunctions.RHTower.XiArithmeticSourceMomentTorelli
import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiCircleAtomicMeasure
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Complete fibre source traces and the infinite zero field

Stable continued-source moments over narrow slabs recover complete ordinate
fibres, uniformly as the transverse band approaches the full critical strip.
Newton identities identify their source field with the coefficient field of
all complete fibre equations, retaining analytic multiplicity.

The entire centered zero field is the compositum of these splitting fields:
it is algebraic and normal over the real source field. Each nonempty fibre's
first trace recovers its ordinate. Consequently every automorphism preserves
that finite fibre and commutes with conjugation, since `conj w = 2t-w` there.
Critical-line zeros are fixed individually; no transitive action on the
infinite zero carrier is possible over this ground field.

The two fields coincide exactly when every centered zero is real. Thus the
centrality theorem supplies no independent purity assertion. Conjugation in
the centered coordinate represents `ρ ↦ 1-conj ρ`; changing to original zero
coordinates requires a separate Gaussian extension.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower RHTower.SlabGermResidueTransport
open RHTower.SlabFullWidthAdmissibility
open Polynomial Finset
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- A source moment that is constant for all sufficiently narrow slabs and
all bands sufficiently close to the full critical strip. -/
def FullFibreSourceGerm (t : ℝ) (k : ℕ) (z : ℂ) : Prop :=
  ∃ c₀ h₀ : ℝ, 0 < c₀ ∧ c₀ < 1/2 ∧ 0 < h₀ ∧
    ∀ c : ℝ, c₀ < c → c < 1/2 → ∀ h : ℝ, 0 < h → h ≤ h₀ →
      slabContourMoment k t h c = z

private theorem fullFibreSourceGerm_unique {t : ℝ} {k : ℕ} {z w : ℂ}
    (hz : FullFibreSourceGerm t k z) (hw : FullFibreSourceGerm t k w) : z = w := by
  rcases hz with ⟨a, h₀, ha0, ha, hh₀, hz⟩
  rcases hw with ⟨b, h₁, hb0, hb, hh₁, hw⟩
  let c := (max a b + 1/2)/2
  have hc : c < 1/2 := by dsimp [c]; linarith [max_lt ha hb]
  have hca : a < c := by dsimp [c]; linarith [le_max_left a b, max_lt ha hb]
  have hcb : b < c := by dsimp [c]; linarith [le_max_right a b, max_lt ha hb]
  let h := min h₀ h₁
  exact (hz c hca hc h (lt_min hh₀ hh₁) (min_le_left _ _)).symm.trans
    (hw c hcb hc h (lt_min hh₀ hh₁) (min_le_right _ _))

/-- The full-width germ is uniform in both the transverse band and the slab width. -/
theorem fullFibreSourceGerm_moment (t : ℝ) (k : ℕ) :
    FullFibreSourceGerm t k (packetDivisorMoment (heightFiber t (1/2)) k) := by
  obtain ⟨c₀, h₁, hc₀, hc₀half, _, hfibre, _⟩ := exists_slabAdmissible_family t
  obtain ⟨h₀, hh₀, _, hgap⟩ := exists_slabGap t (1/2) (by norm_num)
  refine ⟨c₀, h₀, hc₀, hc₀half, hh₀, ?_⟩
  intro c hcc₀ hchalf h hh hh₀'
  have hc : 0 < c := hc₀.trans hcc₀
  have hfull {z : ℂ} (hre : t-h ≤ z.re ∧ z.re ≤ t+h)
      (him : -c ≤ z.im ∧ z.im ≤ c) (hz : XiC z = 0) :
      z.re = t ∧ -c₀ ≤ z.im ∧ z.im ≤ c₀ := by
    have hzfull : z ∈ slabPacket t h (1/2) :=
      (mem_slabPacket hh.le (by norm_num)).mpr
        ⟨⟨hre, ⟨by linarith [him.1], by linarith [him.2]⟩⟩, hz⟩
    rw [hgap h hh hh₀', ← hfibre] at hzfull
    exact ⟨((mem_heightFiber hc₀.le).mp hzfull).1,
      ((mem_heightFiber hc₀.le).mp hzfull).2.1⟩
  have hpacket : slabPacket t h c = heightFiber t (1/2) := by
    ext z
    rw [mem_slabPacket hh.le hc.le, mem_heightFiber (by norm_num : (0:ℝ) ≤ 1/2)]
    constructor
    · rintro ⟨⟨hre, him⟩, hz⟩
      exact ⟨(hfull hre him hz).1, ⟨by linarith [him.1], by linarith [him.2]⟩, hz⟩
    · rintro ⟨hre, him, hz⟩
      have hzfull : z ∈ heightFiber t (1/2) :=
        (mem_heightFiber (by norm_num)).mpr ⟨hre, him, hz⟩
      rw [← hfibre] at hzfull
      have him₀ := ((mem_heightFiber hc₀.le).mp hzfull).2.1
      exact ⟨⟨⟨by linarith, by linarith⟩,
        ⟨by linarith [him₀.1], by linarith [him₀.2]⟩⟩, hz⟩
  have hadm : SlabAdmissible t h c := by
    apply slabAdmissible_of_slabEdgeNonvanishing hc.le hchalf
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx hz
      rw [uIcc_of_le (by linarith : t-h ≤ t+h)] at hx
      have hf := hfull (z := (x:ℂ) + (-c:ℝ)*I)
        (by simpa using hx) (by simp; linarith) hz
      have hb : -c₀ ≤ -c := by simpa using hf.2.1
      linarith
    · intro x hx hz
      rw [uIcc_of_le (by linarith : t-h ≤ t+h)] at hx
      have hf := hfull (z := (x:ℂ) + (c:ℝ)*I)
        (by simpa using hx) (by simp; linarith) hz
      have hb : c ≤ c₀ := by simpa using hf.2.2
      linarith
    · intro y hy hz
      rw [uIcc_of_le (by linarith : -c ≤ c)] at hy
      have hf := hfull (z := ((t+h:ℝ):ℂ) + (y:ℝ)*I)
        (by simp; linarith) (by simpa using hy) hz
      have hr : t+h = t := by simpa using hf.1
      linarith
    · intro y hy hz
      rw [uIcc_of_le (by linarith : -c ≤ c)] at hy
      have hf := hfull (z := ((t-h:ℝ):ℂ) + (y:ℝ)*I)
        (by simp; linarith) (by simpa using hy) hz
      have hr : t-h = t := by simpa using hf.1
      linarith
  rw [slabContourMoment_eq_packetDivisorMoment hh hc hadm k, hpacket]

/-- Stable full-fibre source germs are exactly the complete divisor moments. -/
theorem fullFibreSourceGerm_iff (t : ℝ) (k : ℕ) (z : ℂ) :
    FullFibreSourceGerm t k z ↔ z = packetDivisorMoment (heightFiber t (1/2)) k := by
  constructor
  · intro hz
    exact fullFibreSourceGerm_unique hz (fullFibreSourceGerm_moment t k)
  · rintro rfl
    exact fullFibreSourceGerm_moment t k

/-- The field of full-fibre contour germs, defined entirely by the continued source. -/
def fullFibreSourceField : Subfield ℂ :=
  Subfield.closure {z | ∃ t : ℝ, ∃ k : ℕ, FullFibreSourceGerm t k z}

/-- All occurrences in an ordinate fibre, with analytic multiplicity. -/
def ordinateFibreCopies (t : ℝ) : Finset XiZeroCopy :=
  (xiZeroCopyClosedRectangle (slabLower t 1 (1/2)) (slabUpper t 1 (1/2))).filter
    fun q => (xiSpectralPoint q).re = t

theorem mem_ordinateFibreCopies (t : ℝ) (q : XiZeroCopy) :
    q ∈ ordinateFibreCopies t ↔ (xiSpectralPoint q).re = t := by
  classical
  rw [ordinateFibreCopies, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rw [mem_xiZeroCopyClosedRectangle, Complex.mem_reProdIm,
    slabLower_re, slabUpper_re, slabLower_im, slabUpper_im,
    uIcc_of_le (by linarith : t-1 ≤ t+1),
    uIcc_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2)]
  have him := xiSpectralPoint_im_mem_openHalf q
  exact ⟨⟨by rw [h]; linarith, by rw [h]; linarith⟩,
    ⟨by linarith [him.1], him.2.le⟩⟩

private theorem copy_in_slab_iff {t h c : ℝ} (hh : 0 ≤ h) (hc : 0 ≤ c)
    (q : XiZeroCopy) :
    q ∈ xiZeroCopyClosedRectangle (slabLower t h c) (slabUpper t h c) ↔
      xiSpectralPoint q ∈ slabPacket t h c := by
  rw [mem_xiZeroCopyClosedRectangle, Complex.mem_reProdIm,
    slabLower_re, slabUpper_re, slabLower_im, slabUpper_im,
    uIcc_of_le (by linarith : t-h ≤ t+h), uIcc_of_le (by linarith : -c ≤ c),
    mem_slabPacket hh hc]
  exact (and_iff_left (XiC_xiSpectralPoint_eq_zero q)).symm

private theorem copy_in_full_fibre_iff (t : ℝ) (q : XiZeroCopy) :
    xiSpectralPoint q ∈ heightFiber t (1/2) ↔ (xiSpectralPoint q).re = t := by
  rw [mem_heightFiber (by norm_num : (0:ℝ) ≤ 1/2)]
  have him := xiSpectralPoint_im_mem_openHalf q
  exact and_iff_left ⟨⟨by linarith [him.1], him.2.le⟩, XiC_xiSpectralPoint_eq_zero q⟩

/-- The full divisor moment is the power sum over all multiplicity copies in the fibre. -/
theorem fullFibreMoment_eq_copy_sum (t : ℝ) (k : ℕ) :
    packetDivisorMoment (heightFiber t (1/2)) k =
      ∑ q ∈ ordinateFibreCopies t, xiSpectralPoint q ^ k := by
  classical
  obtain ⟨c, h₁, hc, hchalf, hh₁, hfc, hadm⟩ := exists_slabAdmissible_family t
  obtain ⟨h₂, hh₂, _, hgap⟩ := exists_slabGap t c hc.le
  let h := min h₁ h₂
  have hh : 0 < h := lt_min hh₁ hh₂
  have had := hadm h hh (min_le_left _ _)
  have hp : slabPacket t h c = heightFiber t (1/2) :=
    (hgap h hh (min_le_right _ _)).trans hfc
  have hcopies : xiZeroCopyClosedRectangle (slabLower t h c) (slabUpper t h c) =
      ordinateFibreCopies t := by
    ext q
    rw [copy_in_slab_iff hh.le hc.le, hp, copy_in_full_fibre_iff,
      mem_ordinateFibreCopies]
  have hm := slabContourMoment_eq_packetDivisorMoment hh hc had k
  rw [hp] at hm
  rw [← hm]
  change xiArithmeticSourceRectangleMoment (slabLower t h c) (slabUpper t h c) k = _
  rw [xiArithmeticSourceRectangleMoment_eq_zeroPowerSum
    (by simp; linarith) (by simp; linarith)
    (by simpa only [slabLower_re, slabUpper_re, slabLower_im] using had.bottom)
    (by simpa only [slabLower_re, slabUpper_re, slabUpper_im] using had.top)
    (by simpa only [slabLower_im, slabUpper_im, slabUpper_re] using had.right)
    (by simpa only [slabLower_im, slabUpper_im, slabLower_re] using had.left), hcopies]

private def fibreConjEquiv (t : ℝ) :
    ↥(ordinateFibreCopies t) ≃ ↥(ordinateFibreCopies t) where
  toFun q := ⟨xiZeroCopyLineConjEquiv q.1, by
    rw [mem_ordinateFibreCopies, xiSpectralPoint_lineConj]
    simpa only [Complex.conj_re] using (mem_ordinateFibreCopies t q.1).mp q.2⟩
  invFun q := ⟨xiZeroCopyLineConjEquiv.symm q.1, by
    rw [mem_ordinateFibreCopies]
    have h := xiSpectralPoint_lineConj (xiZeroCopyLineConjEquiv.symm q.1)
    rw [Equiv.apply_symm_apply] at h
    have hr := congrArg Complex.re h
    simp only [Complex.conj_re] at hr
    exact hr.symm.trans ((mem_ordinateFibreCopies t q.1).mp q.2)⟩
  left_inv q := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv q := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

/-- Full-fibre power traces are real, by multiplicity-preserving conjugation. -/
theorem fullFibreMoment_conj (t : ℝ) (k : ℕ) :
    star (packetDivisorMoment (heightFiber t (1/2)) k) =
      packetDivisorMoment (heightFiber t (1/2)) k := by
  classical
  rw [fullFibreMoment_eq_copy_sum]
  change (starRingEnd ℂ) (∑ q ∈ ordinateFibreCopies t, xiSpectralPoint q ^ k) = _
  rw [map_sum]
  simp only [map_pow]
  have h := (fibreConjEquiv t).sum_comp
    (fun q : ↥(ordinateFibreCopies t) => xiSpectralPoint q.1 ^ k)
  simp only [fibreConjEquiv, Equiv.coe_fn_mk, xiSpectralPoint_lineConj,
    Finset.univ_eq_attach] at h
  rw [Finset.sum_attach _ (fun q => (starRingEnd ℂ) (xiSpectralPoint q) ^ k),
    Finset.sum_attach _ (fun q => xiSpectralPoint q ^ k)] at h
  exact h

/-- The first complete trace is the positive integer fibre mass times its ordinate. -/
theorem fullFibreMoment_one (t : ℝ) :
    packetDivisorMoment (heightFiber t (1/2)) 1 =
      ((ordinateFibreCopies t).card : ℂ) * (t : ℂ) := by
  have hi := congrArg Complex.im (fullFibreMoment_conj t 1)
  change -(packetDivisorMoment (heightFiber t (1/2)) 1).im =
    (packetDivisorMoment (heightFiber t (1/2)) 1).im at hi
  apply Complex.ext
  · rw [fullFibreMoment_eq_copy_sum]
    simp only [pow_one, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      (∑ q ∈ ordinateFibreCopies t, (xiSpectralPoint q).re) =
          ∑ _q ∈ ordinateFibreCopies t, t :=
        Finset.sum_congr rfl (fun q hq => (mem_ordinateFibreCopies t q).mp hq)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  · simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
    linarith only [hi]

/-- Newton's identities descend every elementary symmetric coefficient to
the field containing the power traces. -/
private theorem esymm_mem_of_powerSums_mem {n : ℕ} (K : Subfield ℂ) (f : Fin n → ℂ)
    (hp : ∀ k, (univ.val.map (fun i => f i ^ k)).sum ∈ K) :
    ∀ k, (univ.val.map f).esymm k ∈ K := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k
      simp [Multiset.esymm]
    · have hn := GaloisForLFunctions.multiset_newton f k hk
      have hsum : (∑ a ∈ {a ∈ antidiagonal k | a.1 ∈ Set.Ioo 0 k},
          (-1:ℂ)^a.1 * (univ.val.map f).esymm a.1 *
            (univ.val.map (fun i => f i^a.2)).sum) ∈ K := by
        apply K.sum_mem
        intro a ha
        have halt : a.1 < k := (Finset.mem_filter.mp ha).2.2
        exact K.mul_mem
          (K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) a.1) (ih a.1 halt)) (hp a.2)
      have hlead : (-1:ℂ)^(k+1)*(k:ℂ)*(univ.val.map f).esymm k ∈ K := by
        have h := K.add_mem (hp k) hsum
        rw [hn, sub_add_cancel] at h
        exact h
      have hc : (-1:ℂ)^(k+1)*(k:ℂ) ∈ K :=
        K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) _) (natCast_mem K k)
      have hc0 : (-1:ℂ)^(k+1)*(k:ℂ) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr hk.ne')
      have h := K.mul_mem (K.inv_mem hc) hlead
      simpa only [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] using h

/-- The complete root polynomial has coefficients in the field of its power traces. -/
private theorem rootPolynomial_coeff_mem_of_powerSums_mem {n : ℕ}
    (K : Subfield ℂ) (f : Fin n → ℂ)
    (hp : ∀ k, (univ.val.map (fun i => f i ^ k)).sum ∈ K) (j : ℕ) :
    (((univ.val.map f).map (fun z => X-C z)).prod).coeff j ∈ K := by
  have hcard : (univ.val.map f).card = n := by simp
  by_cases hj : j ≤ n
  · rw [Multiset.prod_X_sub_C_coeff _ (by simpa only [hcard] using hj), hcard]
    exact K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) _)
      (esymm_mem_of_powerSums_mem K f hp _)
  · rw [coeff_eq_zero_of_natDegree_lt
      (by rw [natDegree_multiset_prod_X_sub_C_eq_card, hcard]; omega)]
    exact K.zero_mem

/-- Reverse Newton identities recover every power trace from the root coefficients. -/
private theorem powerSums_mem_of_coeff_mem {n : ℕ} (K : Subfield ℂ) (f : Fin n → ℂ)
    (hc : ∀ j, (((univ.val.map f).map (fun z => X-C z)).prod).coeff j ∈ K) :
    ∀ k, (univ.val.map (fun i => f i ^ k)).sum ∈ K := by
  have hcard : (univ.val.map f).card = n := by simp
  have he : ∀ k, (univ.val.map f).esymm k ∈ K := by
    intro k
    by_cases hk : k ≤ n
    · have h := hc (n-k)
      rw [Multiset.prod_X_sub_C_coeff _ (by rw [hcard]; omega),
        hcard, Nat.sub_sub_self hk] at h
      have hs : (-1:ℂ)^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
      have hh := K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) k) h
      simpa only [← mul_assoc, hs, one_mul] using hh
    · rw [Multiset.esymm,
        Multiset.powersetCard_eq_empty k (by rw [hcard]; omega),
        Multiset.map_zero, Multiset.sum_zero]
      exact K.zero_mem
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst k
      simp only [pow_zero, Multiset.map_const', Multiset.sum_replicate,
        nsmul_eq_mul, mul_one]
      simp
    · rw [GaloisForLFunctions.multiset_newton f k hk]
      apply K.sub_mem
      · exact K.mul_mem
          (K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) _) (natCast_mem K k)) (he k)
      · apply K.sum_mem
        intro a ha
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
        have hpos := (Finset.mem_filter.mp ha).2.1
        have halt : a.2 < k := by omega
        exact K.mul_mem
          (K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) a.1) (he a.1)) (ih a.2 halt)

/-- Every member of a finite fibre is algebraic over its power-trace field. -/
private theorem isAlgebraic_of_powerSums_mem {n : ℕ} (K : Subfield ℂ) (f : Fin n → ℂ)
    (hp : ∀ k, (univ.val.map (fun i => f i ^ k)).sum ∈ K) (i : Fin n) :
    IsAlgebraic K (f i) := by
  let P : ℂ[X] := ((univ.val.map f).map (fun z => X-C z)).prod
  have hlift : P ∈ Polynomial.lifts (algebraMap K ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨P.coeff j, rootPolynomial_coeff_mem_of_powerSums_mem K f hp j⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := hlift
  change Polynomial.map (algebraMap K ℂ) Q = P at hQ
  have hP : P ≠ 0 := (monic_multisetProd_X_sub_C _).ne_zero
  have hQ0 : Q ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hQ
    exact hP hQ.symm
  have hroot : f i ∈ P.roots := by
    rw [show P = ((univ.val.map f).map (fun z => X-C z)).prod from rfl,
      roots_multiset_prod_X_sub_C]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  refine ⟨Q, hQ0, ?_⟩
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, hQ]
  exact (Polynomial.mem_roots'.mp hroot).2

theorem fullFibreMoment_mem_sourceField (t : ℝ) (k : ℕ) :
    packetDivisorMoment (heightFiber t (1/2)) k ∈ fullFibreSourceField :=
  Subfield.subset_closure ⟨t, k, fullFibreSourceGerm_moment t k⟩

/-- Complete-fibre source traces generate a real field. -/
theorem fullFibreSourceField_le_real :
    fullFibreSourceField ≤ Complex.ofRealHom.fieldRange := by
  apply Subfield.closure_le.mpr
  rintro z ⟨t, k, hz⟩
  rw [(fullFibreSourceGerm_iff t k z).mp hz]
  have hi := congrArg Complex.im (fullFibreMoment_conj t k)
  change -(packetDivisorMoment (heightFiber t (1/2)) k).im =
    (packetDivisorMoment (heightFiber t (1/2)) k).im at hi
  refine ⟨(packetDivisorMoment (heightFiber t (1/2)) k).re, ?_⟩
  apply Complex.ext
  · rfl
  · change 0 = (packetDivisorMoment (heightFiber t (1/2)) k).im
    linarith only [hi]

/-- Every trace belongs to the field of the entire zero carrier. -/
theorem fullFibreSourceField_le_zeroClosure :
    fullFibreSourceField ≤ Subfield.closure (Set.range xiSpectralPoint) := by
  apply Subfield.closure_le.mpr
  rintro z ⟨t, k, hz⟩
  rw [(fullFibreSourceGerm_iff t k z).mp hz, fullFibreMoment_eq_copy_sum]
  apply Subfield.sum_mem
  intro q _
  have hq : xiSpectralPoint q ∈ Subfield.closure (Set.range xiSpectralPoint) :=
    Subfield.subset_closure ⟨q, rfl⟩
  exact (Subfield.closure (Set.range xiSpectralPoint)).pow_mem hq k

/-- A nonempty fibre's first trace recovers its ordinate by division by its integer mass. -/
theorem ordinate_mem_fullFibreSourceField (q : XiZeroCopy) :
    ((xiSpectralPoint q).re : ℂ) ∈ fullFibreSourceField := by
  let t := (xiSpectralPoint q).re
  have hm : 0 < (ordinateFibreCopies t).card :=
    Finset.card_pos.mpr ⟨q, (mem_ordinateFibreCopies t q).mpr rfl⟩
  have h := fullFibreMoment_mem_sourceField t 1
  rw [fullFibreMoment_one] at h
  have hm0 : ((ordinateFibreCopies t).card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hp := fullFibreSourceField.mul_mem
    (fullFibreSourceField.inv_mem
      (natCast_mem fullFibreSourceField (ordinateFibreCopies t).card)) h
  change (t : ℂ) ∈ fullFibreSourceField
  simpa only [← mul_assoc, inv_mul_cancel₀ hm0, one_mul] using hp

/-- Critical-line zeros are individually fixed by the source ground field. -/
theorem real_zero_mem_fullFibreSourceField (q : XiZeroCopy)
    (hq : (xiSpectralPoint q).im = 0) : xiSpectralPoint q ∈ fullFibreSourceField := by
  have he : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hq
  rw [he]
  exact ordinate_mem_fullFibreSourceField q

/-- The source field equals the zero field precisely when every centered zero is real. -/
theorem fullFibreSourceField_eq_zeroClosure_iff :
    fullFibreSourceField = Subfield.closure (Set.range xiSpectralPoint) ↔
      ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 := by
  constructor
  · intro heq q
    have hq : xiSpectralPoint q ∈ fullFibreSourceField := by
      rw [heq]
      exact Subfield.subset_closure ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := fullFibreSourceField_le_real hq
    rw [← hx]
    rfl
  · intro h
    apply le_antisymm fullFibreSourceField_le_zeroClosure
    apply Subfield.closure_le.mpr
    rintro z ⟨q, rfl⟩
    exact real_zero_mem_fullFibreSourceField q (h q)

private def fibreEnumeration (t : ℝ) : Fin (ordinateFibreCopies t).card → ℂ :=
  fun i => xiSpectralPoint ((ordinateFibreCopies t).equivFin.symm i).1

private theorem fibreEnumeration_mem (t : ℝ) (i : Fin (ordinateFibreCopies t).card) :
    ∃ q ∈ ordinateFibreCopies t, fibreEnumeration t i = xiSpectralPoint q :=
  ⟨_, ((ordinateFibreCopies t).equivFin.symm i).2, rfl⟩

private theorem fibreEnumeration_surj (t : ℝ) (q : XiZeroCopy)
    (hq : q ∈ ordinateFibreCopies t) : ∃ i, fibreEnumeration t i = xiSpectralPoint q := by
  refine ⟨(ordinateFibreCopies t).equivFin ⟨q, hq⟩, ?_⟩
  simp only [fibreEnumeration, Equiv.symm_apply_apply]

private theorem fibreEnumeration_powerSum (t : ℝ) (k : ℕ) :
    (univ.val.map (fun i => fibreEnumeration t i ^ k)).sum =
      packetDivisorMoment (heightFiber t (1/2)) k := by
  rw [fullFibreMoment_eq_copy_sum]
  change (∑ i : Fin (ordinateFibreCopies t).card, fibreEnumeration t i ^ k) = _
  have he := (ordinateFibreCopies t).equivFin.symm.sum_comp
    (fun q : ↥(ordinateFibreCopies t) => xiSpectralPoint q.1 ^ k)
  simp only [Finset.univ_eq_attach] at he
  rw [Finset.sum_attach _ (fun q => xiSpectralPoint q ^ k)] at he
  exact he

private def fibreRootPolynomial (t : ℝ) : ℂ[X] :=
  ((univ.val.map (fibreEnumeration t)).map (fun z => X-C z)).prod

/-- The coefficient field of all complete fibre equations, with multiplicity. -/
def fullFibreCoefficientField : Subfield ℂ :=
  Subfield.closure {a : ℂ | ∃ t : ℝ, ∃ j : ℕ, a = (fibreRootPolynomial t).coeff j}

/-- Complete source traces and complete fibre coefficients generate exactly the same field. -/
theorem fullFibreCoefficientField_eq_sourceField :
    fullFibreCoefficientField = fullFibreSourceField := by
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro a ⟨t, j, rfl⟩
    apply rootPolynomial_coeff_mem_of_powerSums_mem
    intro k
    rw [fibreEnumeration_powerSum]
    exact fullFibreMoment_mem_sourceField t k
  · apply Subfield.closure_le.mpr
    rintro a ⟨t, k, ha⟩
    rw [(fullFibreSourceGerm_iff t k a).mp ha, ← fibreEnumeration_powerSum]
    apply powerSums_mem_of_coeff_mem
    intro j
    exact Subfield.subset_closure ⟨t, j, rfl⟩

private theorem fibreRootPolynomial_lifts (t : ℝ) :
    ∃ Q : fullFibreSourceField[X], Q.map (algebraMap fullFibreSourceField ℂ) =
      fibreRootPolynomial t := by
  change fibreRootPolynomial t ∈ Polynomial.lifts (algebraMap fullFibreSourceField ℂ)
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro j
  refine ⟨⟨(fibreRootPolynomial t).coeff j, ?_⟩, rfl⟩
  apply rootPolynomial_coeff_mem_of_powerSums_mem
  intro k
  rw [fibreEnumeration_powerSum]
  exact fullFibreMoment_mem_sourceField t k

/-- The complete fibre equation over the field defined by source germs. -/
def sourceFibrePolynomial (t : ℝ) : fullFibreSourceField[X] :=
  Classical.choose (fibreRootPolynomial_lifts t)

private theorem sourceFibrePolynomial_map (t : ℝ) :
    (sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ) =
      fibreRootPolynomial t := Classical.choose_spec (fibreRootPolynomial_lifts t)

/-- The source equation maps to the product over every analytic-multiplicity copy. -/
theorem sourceFibrePolynomial_map_eq_prod (t : ℝ) :
    (sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ) =
      ∏ q ∈ ordinateFibreCopies t, (X-C (xiSpectralPoint q) : ℂ[X]) := by
  rw [sourceFibrePolynomial_map, fibreRootPolynomial, Multiset.map_map]
  change (∏ i : Fin (ordinateFibreCopies t).card,
    (X-C (fibreEnumeration t i) : ℂ[X])) = _
  have he := (ordinateFibreCopies t).equivFin.symm.prod_comp
    (fun q : ↥(ordinateFibreCopies t) => (X-C (xiSpectralPoint q.1) : ℂ[X]))
  simp only [Finset.univ_eq_attach] at he
  rw [Finset.prod_attach _ (fun q => (X-C (xiSpectralPoint q) : ℂ[X]))] at he
  exact he

/-- The source polynomial retains the complete divisor, not only its support. -/
theorem sourceFibrePolynomial_roots (t : ℝ) :
    ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ)).roots =
      (ordinateFibreCopies t).val.map xiSpectralPoint := by
  rw [sourceFibrePolynomial_map_eq_prod]
  change ((ordinateFibreCopies t).val.map
    (fun q => (X-C (xiSpectralPoint q) : ℂ[X]))).prod.roots = _
  have he : (ordinateFibreCopies t).val.map
      (fun q => (X-C (xiSpectralPoint q) : ℂ[X])) =
      ((ordinateFibreCopies t).val.map xiSpectralPoint).map (fun z => X-C z) := by
    rw [Multiset.map_map]
    rfl
  rw [he, roots_multiset_prod_X_sub_C]

theorem sourceFibrePolynomial_monic (t : ℝ) : (sourceFibrePolynomial t).Monic := by
  have hm : ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ)).Monic := by
    rw [sourceFibrePolynomial_map, fibreRootPolynomial]
    exact monic_multisetProd_X_sub_C _
  exact Polynomial.monic_map_iff.mp hm

/-- Degree is the full analytic mass of the fibre. -/
theorem sourceFibrePolynomial_natDegree (t : ℝ) :
    (sourceFibrePolynomial t).natDegree = (ordinateFibreCopies t).card := by
  calc
    (sourceFibrePolynomial t).natDegree =
        ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ)).natDegree :=
      ((sourceFibrePolynomial_monic t).natDegree_map _).symm
    _ = (ordinateFibreCopies t).card := by
      rw [sourceFibrePolynomial_map, fibreRootPolynomial,
        natDegree_multiset_prod_X_sub_C_eq_card]
      simp

/-- Every centered zero is algebraic over the complete-fibre source field. -/
theorem xiSpectralPoint_isAlgebraic_fullFibreSourceField (q : XiZeroCopy) :
    IsAlgebraic fullFibreSourceField (xiSpectralPoint q) := by
  let t := (xiSpectralPoint q).re
  obtain ⟨i, hi⟩ := fibreEnumeration_surj t q ((mem_ordinateFibreCopies t q).mpr rfl)
  rw [← hi]
  apply isAlgebraic_of_powerSums_mem fullFibreSourceField (fibreEnumeration t)
  intro k
  rw [fibreEnumeration_powerSum]
  exact fullFibreMoment_mem_sourceField t k

/-- The whole zero field regarded as an extension of the source ground field. -/
def fullFibreZeroExtension : IntermediateField fullFibreSourceField ℂ :=
  IntermediateField.adjoin fullFibreSourceField (Set.range xiSpectralPoint)

theorem fullFibreZeroExtension_toSubfield :
    fullFibreZeroExtension.toSubfield = Subfield.closure (Set.range xiSpectralPoint) := by
  rw [fullFibreZeroExtension, IntermediateField.adjoin_toSubfield]
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro x (⟨k, rfl⟩ | hx)
    · exact fullFibreSourceField_le_zeroClosure k.property
    · exact Subfield.subset_closure hx
  · exact Subfield.closure_mono Set.subset_union_right

/-- The complete fibre polynomial has exactly that fibre as its root set. -/
theorem sourceFibrePolynomial_rootSet (t : ℝ) (z : ℂ) :
    z ∈ (sourceFibrePolynomial t).rootSet ℂ ↔
      ∃ q ∈ ordinateFibreCopies t, xiSpectralPoint q = z := by
  rw [Polynomial.mem_rootSet', sourceFibrePolynomial_map]
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, sourceFibrePolynomial_map]
  change fibreRootPolynomial t ≠ 0 ∧ (fibreRootPolynomial t).IsRoot z ↔ _
  rw [← Polynomial.mem_roots', fibreRootPolynomial, roots_multiset_prod_X_sub_C]
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hz
    obtain ⟨q, hq, heq⟩ := fibreEnumeration_mem t i
    exact ⟨q, hq, heq.symm.trans hi⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, hi⟩ := fibreEnumeration_surj t q hq
    exact Multiset.mem_map.mpr ⟨i, by simp, hi⟩

private theorem union_sourceFibre_rootSet :
    (⋃ t : ℝ, (sourceFibrePolynomial t).rootSet ℂ) = Set.range xiSpectralPoint := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_range, sourceFibrePolynomial_rootSet]
  constructor
  · rintro ⟨t, q, _, hq⟩
    exact ⟨q, hq⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(xiSpectralPoint q).re, q, (mem_ordinateFibreCopies _ q).mpr rfl, rfl⟩

/-- The infinite zero extension is the compositum of its source fibre splitting fields. -/
theorem fullFibreZeroExtension_eq_iSup :
    fullFibreZeroExtension = ⨆ t : ℝ,
      IntermediateField.adjoin fullFibreSourceField ((sourceFibrePolynomial t).rootSet ℂ) := by
  rw [fullFibreZeroExtension, ← union_sourceFibre_rootSet, IntermediateField.adjoin_iUnion]

/-- Normality and algebraicity hold for the entire extension, with no height cutoff. -/
instance fullFibreZeroExtension_normal : Normal fullFibreSourceField fullFibreZeroExtension := by
  have hn (t : ℝ) : Normal fullFibreSourceField
      (IntermediateField.adjoin fullFibreSourceField ((sourceFibrePolynomial t).rootSet ℂ)) := by
    letI := IntermediateField.adjoin_rootSet_isSplittingField
      (IsAlgClosed.splits ((sourceFibrePolynomial t).map (algebraMap fullFibreSourceField ℂ)))
    exact Normal.of_isSplittingField (sourceFibrePolynomial t)
  letI := hn
  rw [fullFibreZeroExtension_eq_iSup]
  infer_instance

private theorem conj_mem_fullFibreZeroExtension (z : ℂ) (hz : z ∈ fullFibreZeroExtension) :
    (starRingEnd ℂ) z ∈ fullFibreZeroExtension := by
  have hstable : Subfield.closure (Set.range xiSpectralPoint) ≤
      (Subfield.closure (Set.range xiSpectralPoint)).comap (starRingEnd ℂ) := by
    apply Subfield.closure_le.mpr
    rintro w ⟨q, rfl⟩
    change (starRingEnd ℂ) (xiSpectralPoint q) ∈ Subfield.closure (Set.range xiSpectralPoint)
    rw [← xiSpectralPoint_lineConj]
    exact Subfield.subset_closure ⟨_, rfl⟩
  change (starRingEnd ℂ) z ∈ fullFibreZeroExtension.toSubfield
  rw [fullFibreZeroExtension_toSubfield]
  apply hstable
  have hz' : z ∈ fullFibreZeroExtension.toSubfield := hz
  rw [fullFibreZeroExtension_toSubfield] at hz'
  exact hz'

/-- Conjugation on the entire zero extension over its real source field. -/
def fullFibreZeroConjugation : fullFibreZeroExtension ≃ₐ[fullFibreSourceField]
    fullFibreZeroExtension where
  toFun z := ⟨(starRingEnd ℂ) z.1, conj_mem_fullFibreZeroExtension z.1 z.2⟩
  invFun z := ⟨(starRingEnd ℂ) z.1, conj_mem_fullFibreZeroExtension z.1 z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; exact map_mul (starRingEnd ℂ) x.1 y.1
  map_add' x y := by apply Subtype.ext; exact map_add (starRingEnd ℂ) x.1 y.1
  commutes' k := by
    apply Subtype.ext
    change (starRingEnd ℂ) (k : ℂ) = (k : ℂ)
    obtain ⟨x, hx⟩ := fullFibreSourceField_le_real k.property
    rw [← hx]
    simp

def centeredZeroInFibreExtension (q : XiZeroCopy) : fullFibreZeroExtension :=
  ⟨xiSpectralPoint q, IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩⟩

/-- A source-field automorphism of any containing field preserves the complete fibre. -/
theorem sourceFibrePolynomial_aut_image
    (E : IntermediateField fullFibreSourceField ℂ)
    (σ : E ≃ₐ[fullFibreSourceField] E)
    (q : XiZeroCopy) (hqE : xiSpectralPoint q ∈ E) :
    ∃ q' ∈ ordinateFibreCopies (xiSpectralPoint q).re,
      (σ ⟨xiSpectralPoint q, hqE⟩ : ℂ) = xiSpectralPoint q' := by
  let t := (xiSpectralPoint q).re
  let P := sourceFibrePolynomial t
  have hq : xiSpectralPoint q ∈ P.rootSet ℂ :=
    (sourceFibrePolynomial_rootSet t _).mpr
      ⟨q, (mem_ordinateFibreCopies t q).mpr rfl, rfl⟩
  have heval : aeval (⟨xiSpectralPoint q, hqE⟩ : E) P = 0 := by
    apply (IntermediateField.val E).injective
    change (IntermediateField.val E) (aeval (⟨xiSpectralPoint q, hqE⟩ : E) P) =
      (IntermediateField.val E) 0
    rw [map_zero, ← Polynomial.aeval_algHom_apply (IntermediateField.val E)]
    exact (Polynomial.mem_rootSet'.mp hq).2
  have hσeval : aeval (σ ⟨xiSpectralPoint q, hqE⟩) P = 0 := by
    rw [Polynomial.aeval_algHom_apply σ _ P, heval, map_zero]
  have hC : aeval (σ ⟨xiSpectralPoint q, hqE⟩ : ℂ) P = 0 := by
    change aeval ((IntermediateField.val E) (σ ⟨xiSpectralPoint q, hqE⟩)) P = 0
    rw [Polynomial.aeval_algHom_apply (IntermediateField.val E) _ P, hσeval, map_zero]
  have hroot : (σ ⟨xiSpectralPoint q, hqE⟩ : ℂ) ∈ P.rootSet ℂ :=
    Polynomial.mem_rootSet'.mpr ⟨(Polynomial.mem_rootSet'.mp hq).1, hC⟩
  obtain ⟨q', hq', heq⟩ := (sourceFibrePolynomial_rootSet t _).mp hroot
  exact ⟨q', hq', heq.symm⟩

/-- Every automorphism of the entire zero field stays inside each finite ordinate fibre. -/
theorem fullFibre_aut_preserves_ordinate
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (q : XiZeroCopy) :
    ∃ q' ∈ ordinateFibreCopies (xiSpectralPoint q).re,
      (σ (centeredZeroInFibreExtension q) : ℂ) = xiSpectralPoint q' :=
  sourceFibrePolynomial_aut_image fullFibreZeroExtension σ q
    (centeredZeroInFibreExtension q).property

private theorem conj_eq_ordinate_reflection {z : ℂ} {t : ℝ} (ht : z.re = t) :
    (starRingEnd ℂ) z = 2*(t:ℂ)-z := by
  apply Complex.ext
  · change z.re = 2*t-0*0-z.re
    linarith only [ht]
  · simp

/-- Conjugation is central in the full Galois group of the infinite zero extension. -/
theorem fullFibreZeroConjugation_central
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension) :
    fullFibreZeroConjugation.trans σ = σ.trans fullFibreZeroConjugation := by
  have hzero (q : XiZeroCopy) :
      σ (fullFibreZeroConjugation (centeredZeroInFibreExtension q)) =
        fullFibreZeroConjugation (σ (centeredZeroInFibreExtension q)) := by
    let t : fullFibreSourceField :=
      ⟨((xiSpectralPoint q).re : ℂ), ordinate_mem_fullFibreSourceField q⟩
    let a : fullFibreZeroExtension := algebraMap fullFibreSourceField fullFibreZeroExtension t
    have hqconj : fullFibreZeroConjugation (centeredZeroInFibreExtension q) =
        2*a - centeredZeroInFibreExtension q := by
      apply Subtype.ext
      exact conj_eq_ordinate_reflection rfl
    obtain ⟨q', hq', heq⟩ := fullFibre_aut_preserves_ordinate σ q
    have hre : (σ (centeredZeroInFibreExtension q) : ℂ).re = (xiSpectralPoint q).re := by
      rw [heq]
      exact (mem_ordinateFibreCopies _ q').mp hq'
    have hσconj : fullFibreZeroConjugation (σ (centeredZeroInFibreExtension q)) =
        2*a - σ (centeredZeroInFibreExtension q) := by
      apply Subtype.ext
      exact conj_eq_ordinate_reflection hre
    rw [hqconj, hσconj, map_sub, map_mul, map_ofNat, σ.commutes t]
  have heq := IntermediateField.algHom_ext_of_eq_adjoin fullFibreSourceField
    (S := fullFibreZeroExtension) rfl
    (φ₁ := (fullFibreZeroConjugation.trans σ).toAlgHom)
    (φ₂ := (σ.trans fullFibreZeroConjugation).toAlgHom)
    (by rintro z ⟨q, rfl⟩; exact hzero q)
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun heq z

/-- Every orbit in the entire zero carrier is finite. -/
theorem fullFibre_zero_orbit_finite (q : XiZeroCopy) :
    (Set.range (fun σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension =>
      (σ (centeredZeroInFibreExtension q) : ℂ))).Finite := by
  have hf := (ordinateFibreCopies (xiSpectralPoint q).re).finite_toSet.image xiSpectralPoint
  apply hf.subset
  rintro z ⟨σ, rfl⟩
  obtain ⟨q', hq', heq⟩ := fullFibre_aut_preserves_ordinate σ q
  exact ⟨q', hq', heq.symm⟩

/-- This source field cannot support a transitive action on all ξ zeros. -/
theorem fullFibre_zero_action_not_transitive :
    ¬ ∀ q q' : XiZeroCopy,
      ∃ σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension,
        (σ (centeredZeroInFibreExtension q) : ℂ) = xiSpectralPoint q' := by
  intro htrans
  obtain ⟨z, q, rfl⟩ := range_xiSpectralPoint_infinite.nonempty
  apply range_xiSpectralPoint_infinite
  apply (fullFibre_zero_orbit_finite q).subset
  rintro z ⟨q', rfl⟩
  exact htrans q q'

/-- Each critical-line zero is fixed individually, without assuming all zeros are critical. -/
theorem fullFibre_aut_fixes_real_zero
    (σ : fullFibreZeroExtension ≃ₐ[fullFibreSourceField] fullFibreZeroExtension)
    (q : XiZeroCopy) (hq : (xiSpectralPoint q).im = 0) :
    σ (centeredZeroInFibreExtension q) = centeredZeroInFibreExtension q := by
  let t : fullFibreSourceField := ⟨xiSpectralPoint q, real_zero_mem_fullFibreSourceField q hq⟩
  have he : algebraMap fullFibreSourceField fullFibreZeroExtension t =
      centeredZeroInFibreExtension q := by apply Subtype.ext; rfl
  calc
    σ (centeredZeroInFibreExtension q) =
        σ (algebraMap fullFibreSourceField fullFibreZeroExtension t) := by rw [he]
    _ = algebraMap fullFibreSourceField fullFibreZeroExtension t := σ.commutes t
    _ = centeredZeroInFibreExtension q := he

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibreSourceGerm_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibreSourceField_le_real
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibreCoefficientField_eq_sourceField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceFibrePolynomial_roots
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibreSourceField_eq_zeroClosure_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.xiSpectralPoint_isAlgebraic_fullFibreSourceField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibreZeroExtension_normal
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibreZeroConjugation_central
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.fullFibre_zero_action_not_transitive
