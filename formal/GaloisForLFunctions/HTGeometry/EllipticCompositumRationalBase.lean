import GaloisForLFunctions.HTGeometry.RelativeTwoShiftGaugeCharacterization
import GaloisForLFunctions.HTGeometry.MeromorphicEllipticRationalCompositum
import GaloisForLFunctions.HTGeometry.DifferentialMatroid
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import GaloisForLFunctions.HTGeometry.EllipticGammaQuotientPeriodCosetMatroid
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# The paired elliptic compositum is differentially algebraic over `ℂ(z)`

The classical route to this statement is the generation theorem for elliptic functions: the field
of `Λ`-elliptic functions is `ℂ(℘, ℘′)`, so it has transcendence degree one and every element is
differentially algebraic.  That theorem is not available in mathlib for the meromorphic elliptic
subfield used here.  It is also not needed: doubly periodic meromorphic germs are differentially
algebraic directly, by `differentialAlgebraicOver_of_mem_ellipticMeroField`.

This file turns that into the base-change interface the elliptic-gamma matroid needs.

* **`differentialAlgebraicOver_of_base_differentialAlgebraic`** — a general differential-field
  tower law: if every element of an intermediate field is differentially algebraic over the base,
  then differential algebraicity over the intermediate field descends to the base.  The relation
  witnessing algebraicity has finitely many coefficients, so finite transitivity applies;
* **`meromorphicEllipticCompositum_differentialAlgebraicOver_ratFunc`** — every element of the
  paired elliptic compositum is differentially algebraic over the rational coordinate field;
* **`differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_ellipticCompositum`** — hence
  every statement of differential algebraicity over the paired elliptic compositum upgrades to the
  rational base.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-! ## A tower law with a differentially algebraic intermediate field -/

set_option maxHeartbeats 1000000 in
/-- **Differential algebraicity descends through a differentially algebraic intermediate field.**
A witnessing jet relation has finitely many coefficients, each differentially algebraic over the
base, so finite differential-algebraic transitivity applies. -/
theorem differentialAlgebraicOver_of_base_differentialAlgebraic
    {F K B : Type} [Field F] [Field K] [Field B] [Algebra F K] [Algebra B K]
    [Differential F] [Differential K] [Differential B] [DifferentialAlgebra F K] [CharZero K]
    (hB : ∀ b : B, DifferentialAlgebraicOver F (algebraMap B K b))
    {x : K} (hx : DifferentialAlgebraicOver B x) :
    DifferentialAlgebraicOver F x := by
  classical
  obtain ⟨n, Q, hQ0, hQ⟩ := exists_jet_relation_of_differentialAlgebraicOver hx
  -- the finitely many coefficients of the relation, as elements of `K`
  set ι : Type _ := {d : Fin (n + 1) →₀ ℕ // d ∈ Q.support} with hι
  haveI : Finite ι := Q.support.finite_toSet.to_subtype
  haveI : Nonempty ι := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ0
    exact ⟨⟨d, hd⟩⟩
  set c : ι → K := fun d => algebraMap B K (Q.coeff d.1) with hc
  set L : IntermediateField F K := differentialAdjoin F (Set.range c) with hL
  letI : Differential L :=
    derivationClosedDifferential L (derivationClosed_differentialAdjoin F (Set.range c))
  letI : DifferentialAlgebra L K :=
    ⟨fun z => derivationClosedDifferential_apply L
      (derivationClosed_differentialAdjoin F (Set.range c)) z⟩
  have hcL : ∀ d : ι, c d ∈ L :=
    fun d => subset_differentialAdjoin F (Set.range c) ⟨d, rfl⟩
  -- descend the relation to `L`
  set Q' : MvPolynomial (Fin (n + 1)) L :=
    ∑ d ∈ Q.support.attach, MvPolynomial.monomial d.1 (⟨c d, hcL d⟩ : L) with hQ'
  have hcoeff : ∀ d : ι, MvPolynomial.coeff d.1 Q' = (⟨c d, hcL d⟩ : L) := by
    intro d
    rw [hQ', MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single d]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro e _ hne
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hcon
      exact hne (Subtype.ext hcon)
    · intro hmem
      exact absurd (Finset.mem_attach _ d) hmem
  have hQ'0 : Q' ≠ 0 := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ0
    intro hzero
    have h1 := hcoeff ⟨d, hd⟩
    rw [hzero, MvPolynomial.coeff_zero] at h1
    have h2 : c ⟨d, hd⟩ = 0 := congrArg (Subtype.val) h1.symm
    rw [hc] at h2
    have h3 : Q.coeff d = 0 := (algebraMap B K).injective (by simpa using h2)
    exact (MvPolynomial.mem_support_iff.mp hd) h3
  have hmapeq : MvPolynomial.map (algebraMap L K) Q' = MvPolynomial.map (algebraMap B K) Q := by
    ext d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
    by_cases hd : d ∈ Q.support
    · rw [hcoeff ⟨d, hd⟩]
      rfl
    · have h1 : MvPolynomial.coeff d Q = 0 := by
        simpa using MvPolynomial.notMem_support_iff.mp hd
      have h2 : MvPolynomial.coeff d Q' = 0 := by
        rw [hQ', MvPolynomial.coeff_sum]
        refine Finset.sum_eq_zero fun e _ => ?_
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro hcon
        exact hd (hcon ▸ e.2)
      rw [h1, h2, map_zero, map_zero]
  have hQ'ann : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q' = 0 := by
    have h1 : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q' =
        MvPolynomial.eval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
          (MvPolynomial.map (algebraMap L K) Q') := by
      rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have h2 : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q =
        MvPolynomial.eval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
          (MvPolynomial.map (algebraMap B K) Q) := by
      rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    rw [h1, hmapeq, ← h2, hQ]
  have hxL : DifferentialAlgebraicOver L x :=
    differentialAlgebraicOver_of_finiteJetRelation hQ'0 hQ'ann
  exact differentialAlgebraicOver_trans_finite_nonempty c (fun d => hB (Q.coeff d.1)) x hxL

/-! ## The elliptic compositum over the rational coordinate field -/

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

/-- A complex number in the open upper half-plane is `ℝ`-independent from `1`. -/
theorem linearIndependent_one_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    LinearIndependent ℝ ![(1 : ℂ), τ] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have him : b * τ.im = 0 := by
    have h := congrArg Complex.im hab
    simpa using h
  have hb : b = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h (ne_of_gt hτ)
  subst hb
  have ha : a = 0 := by
    have h := hab
    simp at h
    exact h
  exact ⟨ha, rfl⟩

/-! ## The elliptic compositum is differentially algebraic over the rational base -/

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-- The germs differentially algebraic over the rational coordinate field form an intermediate
field of the global meromorphic field over the constants. -/
def daOverRatFuncField : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) where
  carrier := {x | DifferentialAlgebraicOver (RatFunc ℂ) x}
  mul_mem' := fun hx hy => differentialAlgebraicOver_mul hx hy
  one_mem' := by
    have h := differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
      (E := meroField (Set.univ : Set ℂ)) 1
    simpa using h
  add_mem' := fun hx hy => differentialAlgebraicOver_add hx hy
  zero_mem' := by
    have h := differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
      (E := meroField (Set.univ : Set ℂ)) 0
    simpa using h
  algebraMap_mem' := fun c => by
    have h := differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
      (E := meroField (Set.univ : Set ℂ)) (algebraMap ℂ (RatFunc ℂ) c)
    rwa [meromorphicRatFunc_algebraMap_complex] at h
  inv_mem' := fun x hx => differentialAlgebraicOver_inv hx

@[simp]
theorem mem_daOverRatFuncField_iff (x : meroField (Set.univ : Set ℂ)) :
    x ∈ daOverRatFuncField ↔ DifferentialAlgebraicOver (RatFunc ℂ) x := Iff.rfl

/-- **The elliptic field of a modular parameter is differentially algebraic over `ℂ(z)`.**  No
generation theorem is used: doubly periodic meromorphic germs are differentially algebraic
directly. -/
theorem ellipticMeroField_le_daOverRatFuncField {τ : ℂ} (hτ : 0 < τ.im) :
    ellipticMeroField τ ≤ daOverRatFuncField := by
  intro x hx
  exact differentialAlgebraicOver_of_mem_ellipticMeroField (linearIndependent_one_of_im_pos hτ) hx

/-- **The paired elliptic compositum is differentially algebraic over `ℂ(z)`.**  This is the
classical elliptic-field generation bridge, obtained without the generation theorem. -/
theorem meromorphicEllipticCompositum_le_daOverRatFuncField {σ τ : ℂ}
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    meromorphicEllipticCompositum σ τ ≤ daOverRatFuncField :=
  sup_le (ellipticMeroField_le_daOverRatFuncField hσ) (ellipticMeroField_le_daOverRatFuncField hτ)

/-- Every element of the paired elliptic compositum is differentially algebraic over the rational
coordinate field. -/
theorem differentialAlgebraicOver_ratFunc_of_mem_meromorphicEllipticCompositum {σ τ : ℂ}
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticCompositum σ τ) :
    DifferentialAlgebraicOver (RatFunc ℂ) x :=
  meromorphicEllipticCompositum_le_daOverRatFuncField hσ hτ hx

/-- **Base change from the paired elliptic compositum to the rational coordinate field.**  Every
differential algebraicity statement over the natural elliptic base upgrades to `ℂ(z)`. -/
theorem differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum {σ τ : ℂ}
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) {x : meroField (Set.univ : Set ℂ)}
    (hx : letI := meromorphicEllipticCompositumDifferential σ τ
      DifferentialAlgebraicOver (meromorphicEllipticCompositum σ τ) x) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  letI := meromorphicEllipticCompositumDifferential σ τ
  refine differentialAlgebraicOver_of_base_differentialAlgebraic
    (B := meromorphicEllipticCompositum σ τ) (fun b => ?_) hx
  exact differentialAlgebraicOver_ratFunc_of_mem_meromorphicEllipticCompositum hσ hτ b.2

/-- **The theta logarithmic-derivative defect is differentially algebraic over `ℂ(z)`.**  It is
elliptic for the modular parameter, so the rational-base upper bound needs no generation
theorem. -/
theorem differentialAlgebraicOver_ratFunc_thetaLogDerivDefectMero (h τ : ℂ) (hτ : 0 < τ.im) :
    DifferentialAlgebraicOver (RatFunc ℂ) (thetaLogDerivDefectMero h τ hτ) :=
  differentialAlgebraicOver_of_mem_ellipticMeroField (linearIndependent_one_of_im_pos hτ)
    (thetaLogDerivDefectMero_mem_ellipticMeroField h τ hτ)

/-! ## The rational-base upper half of the elliptic-gamma shift matroid -/

/-- **Resonant additive defects are differentially algebraic over `ℂ(z)`.**  The natural-base
spectrum theorem gives differential algebraicity over the paired elliptic compositum; the compositum
is itself differentially algebraic over the rational coordinate field, so the statement descends. -/
theorem differentialAlgebraicOver_ratFunc_ellipticGammaExternalLogDerivDefectMero_of_resonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hres : ∃ a b n : ℤ, h = a + b * tau + n * sigma) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) :=
  differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum hsigma htau
    ((differentialAlgebraicOver_ellipticGammaExternalLogDerivDefectMero_iff_resonant
      h sigma tau hsigma htau hindependent).mpr hres)

/-- **Resonant multiplicative shift quotients are differentially algebraic over `ℂ(z)`.**  This is
the upper half of the rational-base shift matroid: the zero coset of the period group carries no
differential transcendence over the natural coefficient field of algebraic differential
equations. -/
theorem differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_of_resonant
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hres : ∃ a b n : ℤ, h = a + b * tau + n * sigma) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (ellipticGammaExternalQuotientMero h sigma tau hsigma htau) :=
  differentialAlgebraicOver_ratFunc_of_differentialAlgebraicOver_compositum hsigma htau
    ((differentialAlgebraicOver_ellipticGammaExternalQuotientMero_iff_resonant
      h sigma tau hsigma htau hindependent).mpr hres)

/-! ## Transfer to the embedded rational coordinate field and to the constants -/

/-- The embedded rational coordinate field, as the target of the coordinate embedding. -/
def ratFuncToRationalCoordinateField :
    RatFunc ℂ →+* meromorphicRationalCoordinateField where
  toFun := fun r => ⟨algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r, ⟨r, rfl⟩⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := fun a b => by apply Subtype.ext; simp
  map_zero' := by apply Subtype.ext; simp
  map_add' := fun a b => by apply Subtype.ext; simp

theorem ratFuncToRationalCoordinateField_injective :
    Function.Injective ratFuncToRationalCoordinateField := by
  intro a b hab
  have h := congrArg (Subtype.val) hab
  exact (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective h

/-- Differential algebraicity over the abstract rational function field transfers to the embedded
rational coordinate field. -/
theorem differentialAlgebraicOver_rationalCoordinateField_of_ratFunc
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver meromorphicRationalCoordinateField x := by
  obtain ⟨n, Q, hQ0, hQ⟩ := exists_jet_relation_of_differentialAlgebraicOver hx
  refine differentialAlgebraicOver_of_finiteJetRelation
    (Q := MvPolynomial.map ratFuncToRationalCoordinateField Q) ?_ ?_
  · intro hzero
    exact hQ0 (MvPolynomial.map_injective _ ratFuncToRationalCoordinateField_injective
      (by simpa using hzero))
  · have hmap : MvPolynomial.map
        (algebraMap meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)))
        (MvPolynomial.map ratFuncToRationalCoordinateField Q) =
        MvPolynomial.map (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) Q := by
      rw [MvPolynomial.map_map]
      rfl
    have h1 : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
        (MvPolynomial.map ratFuncToRationalCoordinateField Q) =
        MvPolynomial.eval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
          (MvPolynomial.map
            (algebraMap meromorphicRationalCoordinateField (meroField (Set.univ : Set ℂ)))
            (MvPolynomial.map ratFuncToRationalCoordinateField Q)) := by
      rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    have h2 : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q =
        MvPolynomial.eval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
          (MvPolynomial.map (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))) Q) := by
      rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    rw [h1, hmap, ← h2, hQ]

/-- **Differential algebraicity over the constants.**  For a global meromorphic germ, the rational
coordinate is a differentially algebraic coefficient extension, so the two statements agree. -/
theorem differentialAlgebraicOver_complex_of_ratFunc
    {x : meroField (Set.univ : Set ℂ)} (hx : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentialAlgebraicOver ℂ x :=
  differentialAlgebraicOver_meromorphicRationalCoordinateField_iff.mp
    (differentialAlgebraicOver_rationalCoordinateField_of_ratFunc hx)

/-- **Every element of the paired elliptic compositum is differentially algebraic over the
constants.**  This is the exact statement the classical generation theorem `C(P, P')` is invoked
for, proved here without it. -/
theorem differentialAlgebraicOver_complex_of_mem_meromorphicEllipticCompositum {σ τ : ℂ}
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ meromorphicEllipticCompositum σ τ) :
    DifferentialAlgebraicOver ℂ x :=
  differentialAlgebraicOver_complex_of_ratFunc
    (differentialAlgebraicOver_ratFunc_of_mem_meromorphicEllipticCompositum hσ hτ hx)

end

end GaloisForLFunctions.HTGeometry
