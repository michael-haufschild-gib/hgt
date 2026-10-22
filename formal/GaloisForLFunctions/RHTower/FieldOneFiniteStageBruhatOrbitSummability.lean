import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassInvariantL2
import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzLattice
import GaloisForLFunctions.RHTower.FieldOneLocallyConstantWeylMultiplier

/-!
# Finite-stage Bruhat--Schwartz orbit summability

This file starts the exact finite-stage periodization theorem of Connes--Marcolli.  It defines the
genuine Bruhat--Schwartz carrier on `A_S`, proves common-denominator control for compact subsets of
the finite product of local fields, and proves the missing global fact that a rational `S`-unit is
integral at every place outside `S`.

Combining those facts gives one integer denominator for every nonzero value of a compactly
supported locally constant finite-stage function along an arbitrary `S`-unit orbit.  This is the
arithmetic input that injects the contributing orbit into an integer lattice, where Schwartz
summability proves Connes--Marcolli Lemma 2.29.
-/

open scoped TensorProduct algebraMap

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- Finite nonarchimedean factor of `A_S`. -/
abbrev FieldOneFiniteStageFinitePart
    (S : Finset (HeightOneSpectrum ℤ)) :=
  (v : ↥S) → v.1.adicCompletion ℚ

/-- Compactly supported locally constant functions on the finite factor of `A_S`. -/
abbrev FieldOneFiniteStageFiniteBruhatSchwartz
    (S : Finset (HeightOneSpectrum ℤ)) :=
  compactlySupportedLocallyConstant (FieldOneFiniteStageFinitePart S)

/-- The algebraic Bruhat--Schwartz space `𝒮(ℝ) ⊗ C_c^∞(∏_{v∈S} ℚ_v)` of `A_S`. -/
abbrev FieldOneFiniteStageBruhatSchwartz
    (S : Finset (HeightOneSpectrum ℤ)) :=
  SchwartzMap ℝ ℂ ⊗[ℂ] FieldOneFiniteStageFiniteBruhatSchwartz S

/-- Finite-stage vectors whose denominators divide `d`. -/
def fieldOneFiniteStageFiniteIntegerDenominatorSet
    (S : Finset (HeightOneSpectrum ℤ)) (d : ℤ) :
    Set (FieldOneFiniteStageFinitePart S) :=
  {x | ∀ v : ↥S,
    algebraMap ℤ (v.1.adicCompletion ℚ) d * x v ∈
      v.1.adicCompletionIntegers ℚ}

theorem fieldOneFiniteStageFinite_exists_integerDenominator
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageFinitePart S) :
    ∃ d : ℤ, d ≠ 0 ∧
      x ∈ fieldOneFiniteStageFiniteIntegerDenominatorSet S d := by
  classical
  choose b hb hxb using fun v : ↥S =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v.1 (x v)
  let d : ℤ := ∏ v : ↥S, b v
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      nonZeroDivisors.ne_zero (hb v)
  refine ⟨d, hd, fun v => ?_⟩
  let r : ℤ := ∏ w ∈ Finset.univ.erase v, b w
  have hdr : d = b v * r := by
    dsimp [d, r]
    symm
    exact Finset.mul_prod_erase Finset.univ b (Finset.mem_univ v)
  have hr :
      algebraMap ℤ (v.1.adicCompletion ℚ) r ∈
        v.1.adicCompletionIntegers ℚ :=
    coe_mem_adicCompletionIntegers (K := ℚ) v.1 r
  have hxbv :
      algebraMap ℤ (v.1.adicCompletion ℚ) (b v) * x v ∈
        v.1.adicCompletionIntegers ℚ := by
    simpa [mul_comm] using hxb v
  rw [hdr, map_mul, mul_right_comm]
  exact mul_mem hxbv hr

theorem fieldOneFiniteStageFiniteIntegerDenominatorSet_isOpen
    (S : Finset (HeightOneSpectrum ℤ)) (d : ℤ) :
    IsOpen (fieldOneFiniteStageFiniteIntegerDenominatorSet S d) := by
  rw [show fieldOneFiniteStageFiniteIntegerDenominatorSet S d =
      ⋂ v : ↥S,
        {x : FieldOneFiniteStageFinitePart S |
          algebraMap ℤ (v.1.adicCompletion ℚ) d * x v ∈
            v.1.adicCompletionIntegers ℚ} by
    ext x
    simp [fieldOneFiniteStageFiniteIntegerDenominatorSet]]
  apply isOpen_iInter_of_finite
  intro v
  exact (Valued.isOpen_valuationSubring (v.1.adicCompletion ℚ)).preimage
    (continuous_const.mul (continuous_apply v))

theorem fieldOneFiniteStageFiniteIntegerDenominatorSet_mul
    (S : Finset (HeightOneSpectrum ℤ))
    {d r : ℤ} {x : FieldOneFiniteStageFinitePart S}
    (hx : x ∈ fieldOneFiniteStageFiniteIntegerDenominatorSet S d) :
    x ∈ fieldOneFiniteStageFiniteIntegerDenominatorSet S (r * d) := by
  intro v
  change algebraMap ℤ (v.1.adicCompletion ℚ) (r * d) * x v ∈
    v.1.adicCompletionIntegers ℚ
  rw [map_mul, mul_assoc]
  exact mul_mem
    (coe_mem_adicCompletionIntegers (K := ℚ) v.1 r)
    (hx v)

theorem fieldOneFiniteStageFinite_isCompact_exists_commonIntegerDenominator
    (S : Finset (HeightOneSpectrum ℤ))
    {K : Set (FieldOneFiniteStageFinitePart S)} (hK : IsCompact K) :
    ∃ d : ℤ, d ≠ 0 ∧
      K ⊆ fieldOneFiniteStageFiniteIntegerDenominatorSet S d := by
  classical
  let D := {d : ℤ // d ≠ 0}
  let U : D → Set (FieldOneFiniteStageFinitePart S) :=
    fun d => fieldOneFiniteStageFiniteIntegerDenominatorSet S d.1
  have hcover : K ⊆ ⋃ d, U d := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ :=
      fieldOneFiniteStageFinite_exists_integerDenominator S x
    exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, hdx⟩
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover U
      (fun d => fieldOneFiniteStageFiniteIntegerDenominatorSet_isOpen S d.1)
      hcover
  let d : ℤ := ∏ e ∈ t, e.1
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Finset.prod_ne_zero_iff.mpr fun e _ => e.2
  refine ⟨d, hd, fun x hx => ?_⟩
  have hxu := ht hx
  rw [Set.mem_iUnion] at hxu
  obtain ⟨e, hxu⟩ := hxu
  rw [Set.mem_iUnion] at hxu
  obtain ⟨he, hxe⟩ := hxu
  let r : ℤ := ∏ z ∈ t.erase e, z.1
  have hdr : d = r * e.1 := by
    dsimp [d, r]
    exact (Finset.prod_erase_mul t (fun z : D => z.1) he).symm
  rw [hdr]
  exact fieldOneFiniteStageFiniteIntegerDenominatorSet_mul S hxe

/-- Rational units having norm one at a given finite place. -/
def fieldOneRationalLocalNormOneSubgroup
    (v : HeightOneSpectrum ℤ) : Subgroup ℚˣ where
  carrier := {q | ‖algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro q r hq hr
    change ‖algebraMap ℚ (v.adicCompletion ℚ) ((q * r : ℚˣ) : ℚ)‖ = 1
    rw [Units.val_mul, map_mul, norm_mul, hq, hr, one_mul]
  inv_mem' := by
    intro q hq
    change ‖algebraMap ℚ (v.adicCompletion ℚ) ((q⁻¹ : ℚˣ) : ℚ)‖ = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, norm_inv, hq, inv_one]

/-- An `S`-unit has local norm one at every finite place outside `S`. -/
theorem fieldOneSUnitSubgroup_le_localNormOne_of_not_mem
    (S : Finset (HeightOneSpectrum ℤ))
    {v : HeightOneSpectrum ℤ} (hv : v ∉ S) :
    fieldOneSUnitSubgroup S ≤ fieldOneRationalLocalNormOneSubgroup v := by
  rw [fieldOneSUnitSubgroup]
  apply (Subgroup.closure_le (fieldOneRationalLocalNormOneSubgroup v)).2
  intro q hq
  rcases hq with (rfl | ⟨w, rfl⟩)
  · change ‖algebraMap ℚ (v.adicCompletion ℚ) ((-1 : ℚˣ) : ℚ)‖ = 1
    simp
  · change ‖algebraMap ℚ (v.adicCompletion ℚ)
      (Rat.HeightOneSpectrum.primesEquiv w.1 : ℚ)‖ = 1
    exact fieldOneRationalPrimeUnit_localNorm_of_ne w.1 v
      (fun h => hv (h ▸ w.2))

theorem fieldOneSUnit_localNorm_one_of_not_mem
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S)
    {v : HeightOneSpectrum ℤ} (hv : v ∉ S) :
    ‖algebraMap ℚ (v.adicCompletion ℚ) (q.1 : ℚ)‖ = 1 :=
  fieldOneSUnitSubgroup_le_localNormOne_of_not_mem S hv q.2

/-- The finite component of a finite-stage idele as a unit in the finite product ring. -/
def fieldOneFiniteStageLocalIdeleUnit
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    (FieldOneFiniteStageFinitePart S)ˣ :=
  MulEquiv.piUnits.symm u.2

/-- One integer denominator controls every contributing `S`-unit in a translated compactly
supported locally constant finite-stage function. -/
theorem fieldOneFiniteStageFiniteBruhatMulRight_exists_integerDenominator
    (S : Finset (HeightOneSpectrum ℤ))
    (φ : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ q : fieldOneSUnitSubgroup S,
      φ.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (u.2 v : v.1.adicCompletion ℚ)) ≠ 0 →
        algebraMap ℤ ℚ d * (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range := by
  let ψ := compactlySupportedLocallyConstantMulRight
    (fieldOneFiniteStageLocalIdeleUnit S u) φ
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFinite_isCompact_exists_commonIntegerDenominator S ψ.2
  refine ⟨d, hd, fun q hq => ?_⟩
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
  intro v
  have hlocalMem :
      algebraMap ℚ (v.adicCompletion ℚ)
          (algebraMap ℤ ℚ d * (q.1 : ℚ)) ∈
        v.adicCompletionIntegers ℚ := by
    by_cases hv : v ∈ S
    · let w : ↥S := ⟨v, hv⟩
      have hdiag :
          (fun z : ↥S => algebraMap ℚ (z.1.adicCompletion ℚ) (q.1 : ℚ)) ∈
            tsupport (ψ.1 : FieldOneFiniteStageFinitePart S → ℂ) := by
        apply subset_tsupport
        change φ.1 (fun z =>
          algebraMap ℚ (z.1.adicCompletion ℚ) (q.1 : ℚ) *
            (u.2 z : z.1.adicCompletion ℚ)) ≠ 0
        exact hq
      have hw := hden hdiag w
      change algebraMap ℤ (v.adicCompletion ℚ) d *
          algebraMap ℚ (v.adicCompletion ℚ) (q.1 : ℚ) ∈
        v.adicCompletionIntegers ℚ at hw
      simpa [map_mul] using hw
    · have hqnorm := fieldOneSUnit_localNorm_one_of_not_mem S q hv
      have hqint :
          algebraMap ℚ (v.adicCompletion ℚ) (q.1 : ℚ) ∈
            v.adicCompletionIntegers ℚ := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hqnorm.le
      rw [map_mul]
      exact mul_mem
        (coe_mem_adicCompletionIntegers (K := ℚ) v d) hqint
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hlocalMem
  change Valued.v
      (algebraMap ℚ (v.adicCompletion ℚ)
        (algebraMap ℤ ℚ d * (q.1 : ℚ))) ≤ 1 at hlocalMem
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (v := v) (algebraMap ℤ ℚ d * (q.1 : ℚ))]
  exact hlocalMem

/-! ## Absolute summability of the `Q_S*` orbit -/

theorem fieldOneFiniteStageFiniteBruhat_exists_norm_bound
    (S : Finset (HeightOneSpectrum ℤ))
    (φ : FieldOneFiniteStageFiniteBruhatSchwartz S) :
    ∃ C : ℝ, ∀ x, ‖φ.1 x‖ ≤ C :=
  φ.1.continuous.bounded_above_of_compact_support φ.2

/-- Evaluation of one pure Bruhat--Schwartz tensor on the `q`-translate of an idele. -/
def fieldOneFiniteStageBruhatPureTensorOrbit
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (φ : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S)
    (q : fieldOneSUnitSubgroup S) : ℂ :=
  f ((u.1 : ℝ) * ((q.1 : ℚ) : ℝ)) *
    φ.1 (fun v =>
      algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
        (u.2 v : v.1.adicCompletion ℚ))

/-- Connes--Marcolli Lemma 2.29, absolute-convergence part, for a pure tensor. -/
theorem fieldOneFiniteStageBruhatPureTensorOrbit_summable
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (φ : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    Summable (fun q : fieldOneSUnitSubgroup S =>
      ‖fieldOneFiniteStageBruhatPureTensorOrbit S f φ u q‖) := by
  classical
  obtain ⟨C, hC⟩ := fieldOneFiniteStageFiniteBruhat_exists_norm_bound S φ
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFiniteBruhatMulRight_exists_integerDenominator S φ u
  let P : Set (fieldOneSUnitSubgroup S) :=
    {q | φ.1 (fun v =>
      algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
        (u.2 v : v.1.adicCompletion ℚ)) ≠ 0}
  choose n hn using fun q : P => hden q.1 q.2
  have hn_injective : Function.Injective n := by
    intro q r hnr
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hdQ : algebraMap ℤ ℚ d ≠ 0 := by
      simpa using (Int.cast_ne_zero.mpr hd : (d : ℚ) ≠ 0)
    apply mul_left_cancel₀ hdQ
    calc
      algebraMap ℤ ℚ d * (q.1.1 : ℚ) = algebraMap ℤ ℚ (n q) := (hn q).symm
      _ = algebraMap ℤ ℚ (n r) := by rw [hnr]
      _ = algebraMap ℤ ℚ d * (r.1.1 : ℚ) := hn r
  let a : ℝ := (u.1 : ℝ) / (d : ℝ)
  have huReal : (u.1 : ℝ) ≠ 0 := Units.ne_zero u.1
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have ha : a ≠ 0 := div_ne_zero huReal hdR
  have harg (q : P) :
      (u.1 : ℝ) * (((q.1.1 : ℚ) : ℝ)) = a * (n q : ℝ) := by
    have hreal : (n q : ℝ) = (d : ℝ) * (((q.1.1 : ℚ) : ℝ)) := by
      exact_mod_cast hn q
    dsimp [a]
    rw [hreal]
    field_simp
  have harch :
      Summable (fun q : P =>
        ‖f ((u.1 : ℝ) * (((q.1.1 : ℚ) : ℝ)))‖) := by
    have hs :=
      (ccmRationalArchimedeanSchwartz_lattice_summable f ha).comp_injective
        hn_injective
    exact hs.congr fun q => by
      simp only [Function.comp_apply]
      rw [harg q]
  have hsub :
      Summable (fun q : P =>
        ‖fieldOneFiniteStageBruhatPureTensorOrbit S f φ u q.1‖) := by
    apply Summable.of_nonneg_of_le
      (fun q => norm_nonneg _)
      (fun q => ?_)
      (harch.mul_right C)
    rw [fieldOneFiniteStageBruhatPureTensorOrbit, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hC _) (norm_nonneg _)
  have hind :
      Summable (P.indicator
        (fun q : fieldOneSUnitSubgroup S =>
          ‖fieldOneFiniteStageBruhatPureTensorOrbit S f φ u q‖)) :=
    summable_subtype_iff_indicator.mp hsub
  exact hind.congr fun q => by
    by_cases hq : q ∈ P
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      have hφ :
          φ.1 (fun v =>
            algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
              (u.2 v : v.1.adicCompletion ℚ)) = 0 := by
        simpa [P] using hq
      change 0 = ‖fieldOneFiniteStageBruhatPureTensorOrbit S f φ u q‖
      rw [fieldOneFiniteStageBruhatPureTensorOrbit, hφ, mul_zero, norm_zero]

/-- Bilinear pure-tensor orbit evaluation at an idele and an `S`-unit. -/
def fieldOneFiniteStageBruhatOrbitBilinear
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S)
    (q : fieldOneSUnitSubgroup S) :
    SchwartzMap ℝ ℂ →ₗ[ℂ]
      FieldOneFiniteStageFiniteBruhatSchwartz S →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := fun φ => fieldOneFiniteStageBruhatPureTensorOrbit S f φ u q
      map_add' := by
        intro φ ψ
        simp [fieldOneFiniteStageBruhatPureTensorOrbit, mul_add]
      map_smul' := by
        intro z φ
        simp [fieldOneFiniteStageBruhatPureTensorOrbit]
        ring }
  map_add' := by
    intro f g
    ext φ
    simp [fieldOneFiniteStageBruhatPureTensorOrbit, add_mul]
  map_smul' := by
    intro z f
    ext φ
    simp [fieldOneFiniteStageBruhatPureTensorOrbit]
    ring

/-- Evaluation of an arbitrary finite-stage Bruhat--Schwartz tensor on an `S`-unit orbit. -/
def fieldOneFiniteStageBruhatOrbit
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S)
    (q : fieldOneSUnitSubgroup S) : ℂ :=
  TensorProduct.lift (fieldOneFiniteStageBruhatOrbitBilinear S u q) t

@[simp]
theorem fieldOneFiniteStageBruhatOrbit_tmul
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ)
    (φ : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S)
    (q : fieldOneSUnitSubgroup S) :
    fieldOneFiniteStageBruhatOrbit S (f ⊗ₜ[ℂ] φ) u q =
      fieldOneFiniteStageBruhatPureTensorOrbit S f φ u q :=
  rfl

/-- Connes--Marcolli Lemma 2.29: the `Q_S*` orbit series of every finite-stage
Bruhat--Schwartz function is absolutely convergent at every idele. -/
theorem fieldOneFiniteStageBruhatOrbit_summable
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    Summable (fun q : fieldOneSUnitSubgroup S =>
      ‖fieldOneFiniteStageBruhatOrbit S t u q‖) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      simp [fieldOneFiniteStageBruhatOrbit]
  | tmul f φ =>
      simpa only [fieldOneFiniteStageBruhatOrbit_tmul] using
        fieldOneFiniteStageBruhatPureTensorOrbit_summable S f φ u
  | add x y hx hy =>
      apply summable_norm_iff.mpr
      have hadd := (summable_norm_iff.mp hx).add (summable_norm_iff.mp hy)
      exact hadd.congr fun q => by
        simp [fieldOneFiniteStageBruhatOrbit]

/-- The finite-stage Connes--Marcolli periodization series `Σ(t)(u)`. -/
def fieldOneFiniteStageBruhatPeriodization
    (S : Finset (HeightOneSpectrum ℤ))
    (t : FieldOneFiniteStageBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) : ℂ :=
  ∑' q : fieldOneSUnitSubgroup S,
    fieldOneFiniteStageBruhatOrbit S t u q

end

end GaloisForLFunctions.RHTower
