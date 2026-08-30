import GaloisForLFunctions.HTGeometry.RotatedExponentialIndependence

/-!
# `exp z + sin z` has differential rank three and primitive defect zero

The function `A = exp + sin` and its derivative generate the same differential field
`ℂ(z, exp z, exp (i z))`: from `A′ = exp + cos` and `A‴ = exp − cos` one recovers `exp z`, then
`cos z` and `sin z`, and finally `exp (i z) = cos z + i sin z`.  Since the coordinate and the two
exponentials are algebraically independent, both the jet field and the shadow field of `A` have
transcendence degree three, so `A` has primitive defect zero.

The autonomous cap therefore costs a full state on `A` — `daRank (exp ∘ A) = 4` — while it costs
nothing on the Gaussian primitive, whose differential rank is also three.  The primitive defect, not
the scalar order, decides the cost of a composition.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### The circular functions inside the meromorphic field -/

theorem analyticOnNhd_csin : AnalyticOnNhd ℂ Complex.sin (Set.univ : Set ℂ) :=
  Complex.differentiable_sin.differentiableOn.analyticOnNhd isOpen_univ

theorem analyticOnNhd_ccos : AnalyticOnNhd ℂ Complex.cos (Set.univ : Set ℂ) :=
  Complex.differentiable_cos.differentiableOn.analyticOnNhd isOpen_univ

theorem analyticOnNhd_expINeg :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-(Complex.I * z))) (Set.univ : Set ℂ) := by
  have h : Differentiable ℂ fun z : ℂ => Complex.exp (-(Complex.I * z)) := by
    intro z
    have hmul : HasDerivAt (fun w : ℂ => Complex.I * w) Complex.I z := by
      simpa using (hasDerivAt_id z).const_mul Complex.I
    have hlin : HasDerivAt (fun w : ℂ => -(Complex.I * w)) (-Complex.I) z := hmul.neg
    exact (hlin.cexp).differentiableAt
  exact h.differentiableOn.analyticOnNhd isOpen_univ

/-- The sine as an element of the meromorphic field. -/
def sinElem : meroField (Set.univ : Set ℂ) := analyticMeroElement Complex.sin analyticOnNhd_csin

/-- The cosine as an element of the meromorphic field. -/
def cosElem : meroField (Set.univ : Set ℂ) := analyticMeroElement Complex.cos analyticOnNhd_ccos

/-- The inverse rotated exponential `exp (-i z)`. -/
def expINegElem : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z : ℂ => Complex.exp (-(Complex.I * z))) analyticOnNhd_expINeg

/-! ### The pointwise identities -/

theorem exp_I_mul (z : ℂ) :
    Complex.exp (Complex.I * z) = Complex.cos z + Complex.sin z * Complex.I := by
  rw [mul_comm]
  exact Complex.exp_mul_I z

theorem exp_neg_I_mul (z : ℂ) :
    Complex.exp (-(Complex.I * z)) = Complex.cos z - Complex.sin z * Complex.I := by
  have h : -(Complex.I * z) = (-z) * Complex.I := by ring
  rw [h, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

theorem exp_I_mul_mul_exp_neg (z : ℂ) :
    Complex.exp (Complex.I * z) * Complex.exp (-(Complex.I * z)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem two_mul_cos (z : ℂ) :
    (2 : ℂ) * Complex.cos z = Complex.exp (Complex.I * z) + Complex.exp (-(Complex.I * z)) := by
  rw [exp_I_mul, exp_neg_I_mul]
  ring

theorem two_mul_sin (z : ℂ) :
    (2 : ℂ) * Complex.sin z
      = (Complex.exp (-(Complex.I * z)) - Complex.exp (Complex.I * z)) * Complex.I := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [exp_I_mul, exp_neg_I_mul]
  linear_combination (2 * Complex.sin z) * hI

theorem exp_I_mul_eq_cos_add (z : ℂ) :
    Complex.exp (Complex.I * z) = Complex.cos z + Complex.I * Complex.sin z := by
  rw [exp_I_mul]
  ring

/-! ### The field identities -/

theorem expIElem_mul_expINegElem : expIElem * expINegElem = 1 := by
  rw [expIElem, expINegElem, ← analyticMeroElement_mul analyticOnNhd_expI analyticOnNhd_expINeg,
    show (1 : meroField (Set.univ : Set ℂ))
      = analyticMeroElement (fun _ : ℂ => (1 : ℂ)) analyticOnNhd_const by
      rw [analyticMeroElement_const]; exact (map_one _).symm]
  exact analyticMeroElement_congr _ _ (funext fun z => exp_I_mul_mul_exp_neg z)

theorem two_mul_cosElem :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 : ℂ) * cosElem = expIElem + expINegElem := by
  rw [algebraMap_complex_eq_analyticMeroElement, cosElem, expIElem, expINegElem,
    ← analyticMeroElement_mul analyticOnNhd_const analyticOnNhd_ccos,
    ← analyticMeroElement_add analyticOnNhd_expI analyticOnNhd_expINeg]
  exact analyticMeroElement_congr _ _ (funext fun z => two_mul_cos z)

theorem two_mul_sinElem :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 : ℂ) * sinElem
      = (expINegElem - expIElem) * algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I := by
  have hsub : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.exp (-(Complex.I * z)) - Complex.exp (Complex.I * z))
      (Set.univ : Set ℂ) := analyticOnNhd_expINeg.sub analyticOnNhd_expI
  rw [algebraMap_complex_eq_analyticMeroElement, algebraMap_complex_eq_analyticMeroElement,
    sinElem, expIElem, expINegElem,
    ← analyticMeroElement_mul analyticOnNhd_const analyticOnNhd_csin,
    ← analyticMeroElement_sub analyticOnNhd_expINeg analyticOnNhd_expI,
    ← analyticMeroElement_mul hsub analyticOnNhd_const]
  exact analyticMeroElement_congr _ _ (funext fun z => two_mul_sin z)

theorem expIElem_eq_cos_add_I_sin :
    expIElem = cosElem + algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I * sinElem := by
  have hmul : AnalyticOnNhd ℂ (fun z : ℂ => Complex.I * Complex.sin z) (Set.univ : Set ℂ) :=
    analyticOnNhd_const.mul analyticOnNhd_csin
  rw [algebraMap_complex_eq_analyticMeroElement, expIElem, cosElem, sinElem,
    ← analyticMeroElement_mul analyticOnNhd_const analyticOnNhd_csin,
    ← analyticMeroElement_add analyticOnNhd_ccos hmul]
  exact analyticMeroElement_congr _ _ (funext fun z => exp_I_mul_eq_cos_add z)

theorem cosElem_eq :
    cosElem = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2⁻¹ : ℂ) * (expIElem + expINegElem) := by
  rw [← two_mul_cosElem, ← mul_assoc, ← map_mul]
  norm_num

theorem sinElem_eq :
    sinElem = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2⁻¹ : ℂ)
      * ((expINegElem - expIElem) * algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I) := by
  rw [← two_mul_sinElem, ← mul_assoc, ← map_mul]
  norm_num

/-! ### The function `exp + sin` and its jets -/

/-- The entire function `exp z + sin z`. -/
def sumES : ℂ → ℂ := fun z => Complex.exp z + Complex.sin z

theorem differentiable_sumES : Differentiable ℂ sumES :=
  Complex.differentiable_exp.add Complex.differentiable_sin

theorem iteratedDeriv_sumES_zero :
    iteratedDeriv 0 sumES = fun z : ℂ => Complex.exp z + Complex.sin z := by
  rw [iteratedDeriv_zero]
  rfl

theorem iteratedDeriv_sumES_one :
    iteratedDeriv 1 sumES = fun z : ℂ => Complex.exp z + Complex.cos z := by
  rw [iteratedDeriv_one]
  funext z
  exact ((Complex.hasDerivAt_exp z).add (Complex.hasDerivAt_sin z)).deriv

theorem iteratedDeriv_sumES_two :
    iteratedDeriv 2 sumES = fun z : ℂ => Complex.exp z - Complex.sin z := by
  have h : iteratedDeriv 2 sumES = deriv (iteratedDeriv 1 sumES) := iteratedDeriv_succ
  rw [h, iteratedDeriv_sumES_one]
  funext z
  have hd : HasDerivAt (fun w : ℂ => Complex.exp w + Complex.cos w)
      (Complex.exp z + -Complex.sin z) z :=
    (Complex.hasDerivAt_exp z).add (Complex.hasDerivAt_cos z)
  rw [hd.deriv]
  ring

theorem iteratedDeriv_sumES_three :
    iteratedDeriv 3 sumES = fun z : ℂ => Complex.exp z - Complex.cos z := by
  have h : iteratedDeriv 3 sumES = deriv (iteratedDeriv 2 sumES) := iteratedDeriv_succ
  rw [h, iteratedDeriv_sumES_two]
  funext z
  have hd : HasDerivAt (fun w : ℂ => Complex.exp w - Complex.sin w)
      (Complex.exp z - Complex.cos z) z :=
    (Complex.hasDerivAt_exp z).sub (Complex.hasDerivAt_sin z)
  rw [hd.deriv]

theorem jetElem_sumES_zero : jetElem differentiable_sumES 0 = expElem + sinElem := by
  rw [jetElem, expElem, sinElem, ← analyticMeroElement_add analyticOnNhd_cexp analyticOnNhd_csin]
  exact analyticMeroElement_congr _ _ iteratedDeriv_sumES_zero

theorem jetElem_sumES_one : jetElem differentiable_sumES 1 = expElem + cosElem := by
  rw [jetElem, expElem, cosElem, ← analyticMeroElement_add analyticOnNhd_cexp analyticOnNhd_ccos]
  exact analyticMeroElement_congr _ _ iteratedDeriv_sumES_one

theorem jetElem_sumES_two : jetElem differentiable_sumES 2 = expElem - sinElem := by
  rw [jetElem, expElem, sinElem, ← analyticMeroElement_sub analyticOnNhd_cexp analyticOnNhd_csin]
  exact analyticMeroElement_congr _ _ iteratedDeriv_sumES_two

theorem jetElem_sumES_three : jetElem differentiable_sumES 3 = expElem - cosElem := by
  rw [jetElem, expElem, cosElem, ← analyticMeroElement_sub analyticOnNhd_cexp analyticOnNhd_ccos]
  exact analyticMeroElement_congr _ _ iteratedDeriv_sumES_three

/-! ### The differential field of the two exponentials -/

/-- The field generated by the coordinate and the two exponentials. -/
def sumESField : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
  IntermediateField.adjoin ℂ (insert expIElem (insert expElem
    ({coordElem} : Set (meroField (Set.univ : Set ℂ)))))

theorem expIElem_mem_sumESField : expIElem ∈ sumESField :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)

theorem expElem_mem_sumESField : expElem ∈ sumESField :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem coordElem_mem_sumESField : coordElem ∈ sumESField :=
  IntermediateField.subset_adjoin ℂ _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem expINegElem_mem_sumESField : expINegElem ∈ sumESField := by
  have hinv : expIElem⁻¹ = expINegElem := inv_eq_of_mul_eq_one_right expIElem_mul_expINegElem
  rw [← hinv]
  exact IntermediateField.inv_mem _ expIElem_mem_sumESField

theorem cosElem_mem_sumESField : cosElem ∈ sumESField := by
  rw [cosElem_eq]
  exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
    (IntermediateField.add_mem _ expIElem_mem_sumESField expINegElem_mem_sumESField)

theorem sinElem_mem_sumESField : sinElem ∈ sumESField := by
  rw [sinElem_eq]
  refine IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _) ?_
  exact IntermediateField.mul_mem _
    (IntermediateField.sub_mem _ expINegElem_mem_sumESField expIElem_mem_sumESField)
    (IntermediateField.algebraMap_mem _ _)

theorem derivationClosed_sumESField : DerivationClosed sumESField := by
  have hbase : ∀ c : ℂ, (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ ∈ sumESField := by
    intro c
    rw [deriv_complexConst]
    exact zero_mem _
  have hgen : ∀ x ∈ insert expIElem (insert expElem
      ({coordElem} : Set (meroField (Set.univ : Set ℂ)))),
      x ∈ sumESField ∧ x′ ∈ sumESField := by
    rintro x (rfl | rfl | rfl)
    · refine ⟨expIElem_mem_sumESField, ?_⟩
      rw [deriv_expIElem]
      exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
        expIElem_mem_sumESField
    · refine ⟨expElem_mem_sumESField, ?_⟩
      rw [deriv_expElem]
      exact expElem_mem_sumESField
    · exact ⟨coordElem_mem_sumESField, by rw [deriv_coordElem]; exact one_mem _⟩
  intro x hx
  have hle := adjoin_le_derivStableField (C := ℂ) (L := sumESField) (hbase := hbase) hgen
  exact (mem_derivStableField_iff.mp (hle hx)).2

theorem jetElem_sumES_mem (k : ℕ) : jetElem differentiable_sumES k ∈ sumESField := by
  induction k with
  | zero =>
      rw [jetElem_sumES_zero]
      exact IntermediateField.add_mem _ expElem_mem_sumESField sinElem_mem_sumESField
  | succ k ih =>
      rw [jetElem_succ_eq_deriv]
      exact derivationClosed_sumESField ih

/-! ### The shadow field recovers the two exponentials -/

theorem expElem_eq_jets :
    expElem = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2⁻¹ : ℂ)
      * (jetElem differentiable_sumES 1 + jetElem differentiable_sumES 3) := by
  rw [jetElem_sumES_one, jetElem_sumES_three]
  have h2 : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2⁻¹ : ℂ)
      * algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 : ℂ) = 1 := by
    rw [← map_mul]
    norm_num
  have hsum : expElem + cosElem + (expElem - cosElem)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 : ℂ) * expElem := by
    have h2' : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 : ℂ)
        = (2 : meroField (Set.univ : Set ℂ)) := map_ofNat _ 2
    rw [h2']
    ring
  rw [hsum, ← mul_assoc, h2, one_mul]

theorem cosElem_eq_jets :
    cosElem = jetElem differentiable_sumES 1 - expElem := by
  rw [jetElem_sumES_one]
  ring

theorem sinElem_eq_jets :
    sinElem = expElem - jetElem differentiable_sumES 2 := by
  rw [jetElem_sumES_two]
  ring

theorem adjoin_shadowSet_sumES :
    IntermediateField.adjoin ℂ
        (insert coordElem (Set.range fun j : ℕ => jetElem differentiable_sumES (j + 1)))
      = sumESField := by
  set S : Set (meroField (Set.univ : Set ℂ)) :=
    insert coordElem (Set.range fun j : ℕ => jetElem differentiable_sumES (j + 1)) with hS
  have hjet : ∀ j : ℕ, jetElem differentiable_sumES (j + 1) ∈ IntermediateField.adjoin ℂ S :=
    fun j => IntermediateField.subset_adjoin ℂ S (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
  have hcoord : coordElem ∈ IntermediateField.adjoin ℂ S :=
    IntermediateField.subset_adjoin ℂ S (Set.mem_insert _ _)
  have hexp : expElem ∈ IntermediateField.adjoin ℂ S := by
    rw [expElem_eq_jets]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.add_mem _ (hjet 0) (hjet 2))
  have hcos : cosElem ∈ IntermediateField.adjoin ℂ S := by
    rw [cosElem_eq_jets]
    exact IntermediateField.sub_mem _ (hjet 0) hexp
  have hsin : sinElem ∈ IntermediateField.adjoin ℂ S := by
    rw [sinElem_eq_jets]
    exact IntermediateField.sub_mem _ hexp (hjet 1)
  have hexpI : expIElem ∈ IntermediateField.adjoin ℂ S := by
    rw [expIElem_eq_cos_add_I_sin]
    exact IntermediateField.add_mem _ hcos
      (IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _) hsin)
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | ⟨j, rfl⟩)
    · exact coordElem_mem_sumESField
    · exact jetElem_sumES_mem _
  · rw [sumESField, IntermediateField.adjoin_le_iff]
    rintro y (rfl | rfl | rfl)
    · exact hexpI
    · exact hexp
    · exact hcoord

theorem adjoin_jetSet_sumES :
    IntermediateField.adjoin ℂ
        (insert coordElem (Set.range fun k : ℕ => jetElem differentiable_sumES k))
      = sumESField := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro y (rfl | ⟨k, rfl⟩)
    · exact coordElem_mem_sumESField
    · exact jetElem_sumES_mem _
  · rw [← adjoin_shadowSet_sumES, IntermediateField.adjoin_le_iff]
    rintro y (rfl | ⟨j, rfl⟩)
    · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
    · exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ ⟨j + 1, rfl⟩)

/-! ### The two ranks of `exp + sin` -/

theorem trdeg_sumESField : Algebra.trdeg ℂ ↥sumESField = 3 :=
  trdeg_adjoin_coordElem_expElem_expIElem

/-- **`exp + sin` has differential rank three.** -/
theorem daRank_sumES : daRank differentiable_sumES = 3 := by
  rw [daRank, adjoin_jetSet_sumES]
  exact trdeg_sumESField

/-- **`exp + sin` has shadow rank three: its primitive defect vanishes.** -/
theorem shadowRank_sumES : shadowRank' differentiable_sumES = 3 := by
  rw [shadowRank', adjoin_shadowSet_sumES]
  exact trdeg_sumESField

theorem daRank_eq_shadowRank_sumES :
    daRank differentiable_sumES = shadowRank' differentiable_sumES := by
  rw [daRank_sumES, shadowRank_sumES]

end

end GaloisForLFunctions.HTGeometry
