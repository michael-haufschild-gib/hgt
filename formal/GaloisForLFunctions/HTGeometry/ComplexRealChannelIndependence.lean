import GaloisForLFunctions.HTGeometry.ContinuousFiniteSupportTailIndependence

/-!
# Complex families observed through tagged real channels

A complex-valued feature can be observed without information loss by tagging its real and
imaginary coordinates in the sample domain.  For real coefficient relations, vanishing of both
tagged channels reconstructs a complex relation.  Consequently complex linear independence
implies real linear independence of the tagged family.

For continuous families on a perfect T₁ domain, the product with the discrete channel tag remains
perfect.  The existing continuous finite-support bridge therefore preserves tagged-channel
independence after every finite deletion.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped BigOperators

noncomputable section

/-- Real or imaginary observation of a complex feature, with the selected coordinate recorded in
the sample domain. -/
def complexRealChannelFeature
    {J X : Type*} (u : J → X → ℂ) (j : J) (sample : X × Bool) : ℝ :=
  match sample.2 with
  | false => (u j sample.1).re
  | true => (u j sample.1).im

/-- Realification of a complex coefficient dictionary.  The Boolean index selects the real
coefficient direction `u j` or the imaginary coefficient direction `I * u j`; the Boolean sample
tag selects the real or imaginary observation channel.  Thus `J × Bool` records both real
coordinates of every complex coefficient without discarding phase information. -/
def complexCoefficientRealChannelFeature
    {J X : Type*} (u : J → X → ℂ) (index : J × Bool)
    (sample : X × Bool) : ℝ :=
  complexRealChannelFeature
    (fun j x => if index.2 then Complex.I * u j x else u j x)
    index.1 sample

/-- Tagged real/imaginary observations of continuous complex features are continuous. -/
theorem continuous_complexRealChannelFeature
    {J X : Type*} [TopologicalSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j)) :
    ∀ j, Continuous (complexRealChannelFeature u j) := by
  intro j
  rw [continuous_iff_continuousAt]
  intro sample
  rw [continuousAt_prod_of_discrete_right]
  cases sample.2 with
  | false =>
      simpa [complexRealChannelFeature] using
        (Complex.continuous_re.comp (hu j)).continuousAt
  | true =>
      simpa [complexRealChannelFeature] using
        (Complex.continuous_im.comp (hu j)).continuousAt

/-- Full complex-coefficient realification preserves continuity. -/
theorem continuous_complexCoefficientRealChannelFeature
    {J X : Type*} [TopologicalSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j)) :
    ∀ index, Continuous (complexCoefficientRealChannelFeature u index) := by
  rintro ⟨j, channel⟩
  cases channel with
  | false =>
      simpa [complexCoefficientRealChannelFeature] using
        continuous_complexRealChannelFeature u hu j
  | true =>
      simpa [complexCoefficientRealChannelFeature] using
        continuous_complexRealChannelFeature
          (fun j x => Complex.I * u j x)
          (fun j => continuous_const.mul (hu j)) j

/-- Complex linear independence implies real linear independence after splitting every feature
into tagged real and imaginary observation channels. -/
theorem linearIndependent_complexRealChannelFeature_of_complex
    {J X : Type*} [Fintype J] (u : J → X → ℂ)
    (hlin : LinearIndependent ℂ u) :
    LinearIndependent ℝ (complexRealChannelFeature u) := by
  classical
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro q hq
  have hcomplex : ∑ j, (q j : ℂ) • u j = 0 := by
    funext x
    apply Complex.ext
    · have hre := congrFun hq (x, false)
      simpa [complexRealChannelFeature, Finset.sum_apply,
        Pi.smul_apply] using hre
    · have him := congrFun hq (x, true)
      simpa [complexRealChannelFeature, Finset.sum_apply,
        Pi.smul_apply] using him
  have hqcomplex := hlin (fun j => (q j : ℂ)) hcomplex
  intro j
  have hj := congrArg Complex.re (hqcomplex j)
  simpa using hj

/-- **Full complex-coefficient realification.**  A complex-linearly independent dictionary
remains real-linearly independent after replacing every complex coefficient by its two real
coordinates and every complex observation by tagged real/imaginary channels. -/
theorem linearIndependent_complexCoefficientRealChannelFeature_of_complex
    {J X : Type*} [Fintype J] (u : J → X → ℂ)
    (hlin : LinearIndependent ℂ u) :
    LinearIndependent ℝ (complexCoefficientRealChannelFeature u) := by
  classical
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro q hq
  let c : J → ℂ := fun j => (q (j, false) : ℂ) + Complex.I * q (j, true)
  have hcomplex : ∑ j, c j • u j = 0 := by
    funext x
    apply Complex.ext
    · have hre := congrFun hq (x, false)
      convert hre using 1
      simp [c, complexCoefficientRealChannelFeature, complexRealChannelFeature,
        Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply,
        Complex.mul_re, Finset.sum_add_distrib]
      ring
    · have him := congrFun hq (x, true)
      convert him using 1
      simp [c, complexCoefficientRealChannelFeature, complexRealChannelFeature,
        Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply,
        Complex.mul_im, Finset.sum_add_distrib]
      ring
  have hc := hlin c hcomplex
  intro index
  rcases index with ⟨j, channel⟩
  cases channel with
  | false =>
      have hj := congrArg Complex.re (hc j)
      simpa [c] using hj
  | true =>
      have hj := congrArg Complex.im (hc j)
      simpa [c] using hj

/-- Full complex-coefficient realification preserves and reflects linear independence.  Hence no
information is lost by replacing complex coefficients and observations by their doubled tagged
real coordinates. -/
theorem linearIndependent_complexCoefficientRealChannelFeature_iff_complex
    {J X : Type*} [Fintype J] (u : J → X → ℂ) :
    LinearIndependent ℝ (complexCoefficientRealChannelFeature u) ↔
      LinearIndependent ℂ u := by
  constructor
  · intro hreal
    classical
    rw [Fintype.linearIndependent_iff] at hreal ⊢
    intro c hc
    let q : J × Bool → ℝ :=
      fun index => if index.2 then (c index.1).im else (c index.1).re
    have hq :
        ∑ index, q index • complexCoefficientRealChannelFeature u index = 0 := by
      funext sample
      rcases sample with ⟨x, channel⟩
      cases channel with
      | false =>
          have hre := congrArg Complex.re (congrFun hc x)
          convert hre using 1
          simp [q, complexCoefficientRealChannelFeature, complexRealChannelFeature,
            Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply,
            Complex.mul_re, Finset.sum_add_distrib]
          ring
      | true =>
          have him := congrArg Complex.im (congrFun hc x)
          convert him using 1
          simp [q, complexCoefficientRealChannelFeature, complexRealChannelFeature,
            Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply,
            Complex.mul_im, Finset.sum_add_distrib]
          ring
    have hqzero := hreal q hq
    intro j
    apply Complex.ext
    · simpa [q] using hqzero (j, false)
    · simpa [q] using hqzero (j, true)
  · exact linearIndependent_complexCoefficientRealChannelFeature_of_complex u

/-- Complex coefficient independence modulo finite support implies real tagged-channel independence
after deleting any finite collection of tagged observations. No topology or continuity is
required: a surviving real-channel relation can be nonzero as a complex function only over the
finite projection of the deleted tagged set. -/
theorem linearIndependent_complexRealChannelFeature_restrict_compl_of_tailCoefficientIndependent
    {J X : Type*} [Fintype J] (u : J → X → ℂ)
    (htail : TailCoefficientIndependent u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
      (fun j => fun sample : {sample : X × Bool // sample ∉ F} =>
        complexRealChannelFeature u j sample) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq
  have hsupp :
      {x : X | ∑ j, (q j : ℂ) * u j x ≠ 0}.Finite := by
    apply (hF.image Prod.fst).subset
    intro x hx
    by_contra hximage
    apply hx
    apply Complex.ext
    · have hfalse : (x, false) ∉ F := by
        intro hmem
        exact hximage ⟨(x, false), hmem, rfl⟩
      have hre := congrFun hq ⟨(x, false), hfalse⟩
      simpa [complexRealChannelFeature, Finset.sum_apply,
        Pi.smul_apply] using hre
    · have htrue : (x, true) ∉ F := by
        intro hmem
        exact hximage ⟨(x, true), hmem, rfl⟩
      have him := congrFun hq ⟨(x, true), htrue⟩
      simpa [complexRealChannelFeature, Finset.sum_apply,
        Pi.smul_apply] using him
  have hqzero := htail (fun j => (q j : ℂ)) hsupp
  intro j
  have hj := congrArg Complex.re (congrFun hqzero j)
  simpa using hj

/-- Full complex-coefficient realification preserves independence after arbitrary finite tagged
deletions whenever the original complex family is independent modulo finite support.  Both real
coordinates of every complex coefficient are recovered; no topology is required. -/
theorem
    linearIndependent_complexCoefficientRealChannelFeature_restrict_compl_of_tailCoefficientIndependent
    {J X : Type*} [Fintype J] (u : J → X → ℂ)
    (htail : TailCoefficientIndependent u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
      (fun index => fun sample : {sample : X × Bool // sample ∉ F} =>
        complexCoefficientRealChannelFeature u index sample) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq
  let c : J → ℂ := fun j => (q (j, false) : ℂ) + Complex.I * q (j, true)
  have hsupp :
      {x : X | ∑ j, c j * u j x ≠ 0}.Finite := by
    apply (hF.image Prod.fst).subset
    intro x hx
    by_contra hximage
    apply hx
    apply Complex.ext
    · have hfalse : (x, false) ∉ F := by
        intro hmem
        exact hximage ⟨(x, false), hmem, rfl⟩
      have hre := congrFun hq ⟨(x, false), hfalse⟩
      convert hre using 1
      simp [c, complexCoefficientRealChannelFeature, complexRealChannelFeature,
        Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply,
        Complex.mul_re, Finset.sum_add_distrib]
      ring
    · have htrue : (x, true) ∉ F := by
        intro hmem
        exact hximage ⟨(x, true), hmem, rfl⟩
      have him := congrFun hq ⟨(x, true), htrue⟩
      convert him using 1
      simp [c, complexCoefficientRealChannelFeature, complexRealChannelFeature,
        Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply,
        Complex.mul_im, Finset.sum_add_distrib]
      ring
  have hc := htail c hsupp
  intro index
  rcases index with ⟨j, channel⟩
  cases channel with
  | false =>
      have hj := congrArg Complex.re (congrFun hc j)
      simpa [c] using hj
  | true =>
      have hj := congrArg Complex.im (congrFun hc j)
      simpa [c] using hj

/-- Complex independence of a continuous family implies real tagged-channel independence after
deleting any finite collection of tagged observations. -/
theorem linearIndependent_complexRealChannelFeature_restrict_compl_of_complex
    {J X : Type*} [Fintype J] [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent ℂ u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
      (fun j => fun sample : {sample : X × Bool // sample ∉ F} =>
        complexRealChannelFeature u j sample) := by
  letI : PerfectSpace (X × Bool) := perfectSpace_prod_left X Bool
  exact linearIndependent_restrict_compl_of_continuous
    (complexRealChannelFeature u)
    (continuous_complexRealChannelFeature u hu)
    (linearIndependent_complexRealChannelFeature_of_complex u hlin) F hF

/-- Continuous complex independence also preserves the full doubled complex-coefficient
realification after every finite tagged deletion. -/
theorem linearIndependent_complexCoefficientRealChannelFeature_restrict_compl_of_complex
    {J X : Type*} [Fintype J] [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent ℂ u)
    (F : Set (X × Bool)) (hF : F.Finite) :
    LinearIndependent ℝ
      (fun index => fun sample : {sample : X × Bool // sample ∉ F} =>
        complexCoefficientRealChannelFeature u index sample) := by
  letI : PerfectSpace (X × Bool) := perfectSpace_prod_left X Bool
  exact linearIndependent_restrict_compl_of_continuous
    (complexCoefficientRealChannelFeature u)
    (continuous_complexCoefficientRealChannelFeature u hu)
    (linearIndependent_complexCoefficientRealChannelFeature_of_complex u hlin) F hF

end

end GaloisForLFunctions.HTGeometry
