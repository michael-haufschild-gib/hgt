import GaloisForLFunctions.HTGeometry.MultivariateEntireVanishingPower
import GaloisForLFunctions.HTGeometry.QuasiAbelianAutomorphicForms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Explicit all-order separators for Abe's integer-lattice base case

The normalized complex sinc is the removable quotient `sin (πz) / (πz)`, represented without
a piecewise singularity as `dslope sin 0 (πz)`.  Products of these functions isolate one integer
lattice translate.  One additional sine factor for each other packet point kills all its integer
translates.  Raising the resulting separator to the packet order then kills all lower mixed jets.
-/

open Filter Function Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinatewise embedding of the standard integer lattice into `ℂ^d`. -/
def integerCastVector {d : ℕ} (k : Fin d → ℤ) : Fin d → ℂ :=
  fun i => (k i : ℂ)

/-- Standard integer translation lattice in `ℂ^d`. -/
def standardIntegerLattice (d : ℕ) : AddSubgroup (Fin d → ℂ) where
  carrier := Set.range integerCastVector
  zero_mem' := ⟨0, by ext i; simp [integerCastVector]⟩
  add_mem' := by
    rintro x y ⟨k, rfl⟩ ⟨l, rfl⟩
    refine ⟨k + l, ?_⟩
    ext i
    simp [integerCastVector]
  neg_mem' := by
    rintro x ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    ext i
    simp [integerCastVector]

@[simp]
theorem mem_standardIntegerLattice_iff {d : ℕ} (x : Fin d → ℂ) :
    x ∈ standardIntegerLattice d ↔ ∃ k : Fin d → ℤ, integerCastVector k = x :=
  Iff.rfl

/-- Coordinatewise integer casting into `ℂ^d` is injective. -/
theorem integerCastVector_injective {d : ℕ} :
    Function.Injective (integerCastVector : (Fin d → ℤ) → Fin d → ℂ) := by
  intro k l hkl
  funext i
  have hi : (k i : ℂ) = (l i : ℂ) := by
    simpa only [integerCastVector] using congrFun hkl i
  exact_mod_cast hi

/-- The standard integer lattice is canonically equivalent to its integer coordinate lattice. -/
noncomputable def standardIntegerLatticeEquiv (d : ℕ) :
    (Fin d → ℤ) ≃ standardIntegerLattice d where
  toFun k := ⟨integerCastVector k, ⟨k, rfl⟩⟩
  invFun γ := Classical.choose γ.property
  left_inv k := by
    apply integerCastVector_injective
    exact Classical.choose_spec
      (show integerCastVector k ∈ standardIntegerLattice d from ⟨k, rfl⟩)
  right_inv γ := by
    apply Subtype.ext
    exact Classical.choose_spec γ.property

@[simp]
theorem standardIntegerLatticeEquiv_apply {d : ℕ} (k : Fin d → ℤ) :
    (standardIntegerLatticeEquiv d k).1 = integerCastVector k :=
  rfl

/-- Distinct classes modulo the standard integer lattice differ by a nonintegral coordinate. -/
theorem exists_coordinate_sub_not_intCast_of_distinctModulo
    {d : ℕ} {I : Type*} {w : I → Fin d → ℂ}
    (h : PairwiseDistinctModulo (standardIntegerLattice d) w)
    {ı j : I} (hij : ı ≠ j) :
    ∃ c : Fin d, ∀ k : ℤ, w ı c - w j c ≠ (k : ℂ) := by
  by_contra hnone
  push Not at hnone
  let k : Fin d → ℤ := fun c => Classical.choose (hnone c)
  have hk : w ı - w j = integerCastVector k := by
    funext c
    exact Classical.choose_spec (hnone c)
  exact h hij ⟨k, hk.symm⟩

/-- Normalized complex sinc, entire because `dslope` removes the zero of `sin` at the origin. -/
def complexIntegerSinc (z : ℂ) : ℂ :=
  dslope Complex.sin 0 ((Real.pi : ℂ) * z)

theorem differentiable_complexIntegerSinc : Differentiable ℂ complexIntegerSinc := by
  have hds : Differentiable ℂ (dslope Complex.sin 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope univ_mem).mpr
      Complex.differentiable_sin.differentiableOn
  apply hds.comp
  fun_prop

@[simp]
theorem complexIntegerSinc_zero : complexIntegerSinc 0 = 1 := by
  simp [complexIntegerSinc, Complex.deriv_sin]

theorem complexIntegerSinc_intCast_eq_zero {k : ℤ} (hk : k ≠ 0) :
    complexIntegerSinc (k : ℂ) = 0 := by
  have harg : (Real.pi : ℂ) * (k : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Int.cast_ne_zero.mpr hk)
  rw [complexIntegerSinc, dslope_of_ne _ harg]
  have hsin : Complex.sin ((Real.pi : ℂ) * (k : ℂ)) = 0 := by
    simpa only [mul_comm] using Complex.sin_int_mul_pi k
  simp [slope, hsin]

/-- Pull an entire one-variable function back along one affine coordinate. -/
def coordinateEntire {d : ℕ} (phi : ℂ → ℂ) (hphi : Differentiable ℂ phi)
    (c : Fin d) (a : Fin d → ℂ) : MultivariateEntire d :=
  ⟨⟨fun x => phi (x c - a c),
      hphi.continuous.comp ((continuous_apply c).sub continuous_const)⟩,
    fun x v => by
      apply hphi.comp
      fun_prop⟩

@[simp]
theorem coordinateEntire_apply {d : ℕ} (phi : ℂ → ℂ)
    (hphi : Differentiable ℂ phi) (c : Fin d) (a x : Fin d → ℂ) :
    (coordinateEntire phi hphi c a).1 x = phi (x c - a c) :=
  rfl

/-- Product of normalized sinc factors in all integer-lattice coordinates. -/
def integerSincProduct {d : ℕ} (a : Fin d → ℂ) : MultivariateEntire d :=
  multivariateEntireFinsetProd Finset.univ fun c =>
    coordinateEntire complexIntegerSinc differentiable_complexIntegerSinc c a

@[simp]
theorem integerSincProduct_center {d : ℕ} (a : Fin d → ℂ) :
    (integerSincProduct a).1 a = 1 := by
  simp [integerSincProduct]

theorem integerSincProduct_translate_eq_zero {d : ℕ}
    (a : Fin d → ℂ) (k : Fin d → ℤ) (hk : k ≠ 0) :
    (integerSincProduct a).1 (a + integerCastVector k) = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, k c ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hk (funext hall)
  apply Finset.prod_eq_zero (Finset.mem_univ c)
  simp [integerCastVector,
    complexIntegerSinc_intCast_eq_zero hc]

/-- Sine factor vanishing on every integer translate of `a` in coordinate `c`. -/
def integerTranslateSine {d : ℕ} (c : Fin d) (a : Fin d → ℂ) :
    MultivariateEntire d :=
  coordinateEntire (fun z => Complex.sin ((Real.pi : ℂ) * z))
    (Complex.differentiable_sin.comp (by fun_prop)) c a

@[simp]
theorem integerTranslateSine_translate {d : ℕ}
    (c : Fin d) (a : Fin d → ℂ) (k : Fin d → ℤ) :
    (integerTranslateSine c a).1 (a + integerCastVector k) = 0 := by
  have hsin : Complex.sin ((Real.pi : ℂ) * (k c : ℂ)) = 0 := by
    simpa only [mul_comm] using Complex.sin_int_mul_pi (k c)
  simpa [integerTranslateSine, integerCastVector] using hsin

theorem integerTranslateSine_target_ne_zero {d : ℕ}
    (c : Fin d) (a b : Fin d → ℂ)
    (hnot : ∀ k : ℤ, b c - a c ≠ (k : ℂ)) :
    (integerTranslateSine c a).1 b ≠ 0 := by
  intro hzero
  rw [integerTranslateSine, coordinateEntire_apply,
    Complex.sin_eq_zero_iff] at hzero
  obtain ⟨k, hk⟩ := hzero
  apply hnot k
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply mul_left_cancel₀ hpi
  simpa only [mul_comm] using hk

/-- **Abe integer-lattice packet separator.** For any selected packet point there is one explicit
line-entire source nonzero at that point and zero at every other packet translate, including every
nontrivial integer translate of the selected point. -/
theorem exists_integerLatticePacketSeparator
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) :
    ∃ separator : MultivariateEntire d,
      separator.1 (w target) ≠ 0 ∧
      ∀ (j : I) (k : Fin d → ℤ),
        (j ≠ target ∨ k ≠ 0) →
          separator.1 (w j + integerCastVector k) = 0 := by
  let Other := {j : I // j ≠ target}
  let coord : Other → Fin d := fun j =>
    Classical.choose
      (exists_coordinate_sub_not_intCast_of_distinctModulo hdistinct j.2.symm)
  have hcoord : ∀ j : Other, ∀ k : ℤ,
      w target (coord j) - w j.1 (coord j) ≠ (k : ℂ) := fun j =>
    Classical.choose_spec
      (exists_coordinate_sub_not_intCast_of_distinctModulo hdistinct j.2.symm)
  let otherProduct : MultivariateEntire d :=
    multivariateEntireFinsetProd Finset.univ fun j : Other =>
      integerTranslateSine (coord j) (w j.1)
  let separator := multivariateEntireMul (integerSincProduct (w target)) otherProduct
  refine ⟨separator, ?_, ?_⟩
  · rw [show separator.1 (w target) =
        (integerSincProduct (w target)).1 (w target) * otherProduct.1 (w target) by rfl,
      integerSincProduct_center, one_mul]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact integerTranslateSine_target_ne_zero (coord j) (w j.1) (w target) (hcoord j)
  · intro j k hjk
    rcases eq_or_ne j target with rfl | hj
    · have hk : k ≠ 0 := by simpa using hjk
      exact mul_eq_zero_of_left
        (integerSincProduct_translate_eq_zero (w j) k hk) _
    · apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ ⟨j, hj⟩)
      exact integerTranslateSine_translate (coord ⟨j, hj⟩) (w j) k

/-- Raising Abe's explicit separator to order `m` annihilates every mixed jet of total degree
`< m` at every undesired packet translate while remaining nonzero at the selected point. -/
theorem exists_integerLatticePacketSeparatorPower
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) (m : ℕ) (_hm : 0 < m) :
    ∃ separatorPower : MultivariateEntire d,
      separatorPower.1 (w target) ≠ 0 ∧
      ∀ (j : I) (k : Fin d → ℤ) (a : Fin d →₀ ℕ),
        (j ≠ target ∨ k ≠ 0) → Finsupp.degree a < m →
          multiIndexJetEvalCLM (w j + integerCastVector k) a separatorPower = 0 := by
  obtain ⟨separator, htarget, hzero⟩ :=
    exists_integerLatticePacketSeparator w hdistinct target
  let one : MultivariateEntire d := mvPolynomialMultivariateEntire 1
  refine ⟨multivariateEntireMul (multivariateEntirePow separator m) one, ?_, ?_⟩
  · apply mul_ne_zero
    · exact pow_ne_zero m htarget
    · have hone : one.1 (w target) = 1 := by
        simp [one, mvPolynomialMultivariateEntire]
      rw [hone]
      exact one_ne_zero
  · intro j k a hjk ha
    exact multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt
      separator one (w j + integerCastVector k) (hzero j k hjk) a ha

/-- **Flat Abe packet separator.** At the selected point this multiplier has the same complete
jet below order `m` as the constant `1`; at every undesired integer translate it vanishes through
order `m`.  Consequently it preserves all selected jets and kills all undesired jets after
multiplication by an arbitrary line-entire source.

The explicit algebraic bump is

`B = 1 - (1 - (S / S(target))^m)^m`.

No local inverse or derivative product formula is assumed.  Both assertions reduce to the
vanishing-power theorem and the finite geometric-sum identity. -/
theorem exists_flatIntegerLatticePacketSeparator
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) (m : ℕ) (_hm : 0 < m) :
    ∃ bump normalized geom : MultivariateEntire d,
      bump.1 (w target) = 1 ∧
      bump = multivariateEntireMul (multivariateEntirePow normalized m) geom ∧
      (∀ (j : I) (k : Fin d → ℤ),
        (j ≠ target ∨ k ≠ 0) →
          normalized.1 (w j + integerCastVector k) = 0) ∧
      (∀ (P : MultivariateEntire d) (a : Fin d →₀ ℕ), Finsupp.degree a < m →
        multiIndexJetEvalCLM (w target) a (multivariateEntireMul bump P) =
          multiIndexJetEvalCLM (w target) a P) ∧
      (∀ (P : MultivariateEntire d) (j : I) (k : Fin d → ℤ)
          (a : Fin d →₀ ℕ),
        (j ≠ target ∨ k ≠ 0) → Finsupp.degree a < m →
          multiIndexJetEvalCLM (w j + integerCastVector k) a
            (multivariateEntireMul bump P) = 0) := by
  obtain ⟨separator, htarget, hzero⟩ :=
    exists_integerLatticePacketSeparator w hdistinct target
  let one : MultivariateEntire d := mvPolynomialMultivariateEntire 1
  let normalized : MultivariateEntire d := (separator.1 (w target))⁻¹ • separator
  let U : MultivariateEntire d := multivariateEntirePow normalized m
  let complement : MultivariateEntire d := one - U
  let V : MultivariateEntire d := multivariateEntirePow complement m
  let bump : MultivariateEntire d := one - V
  let geom : MultivariateEntire d :=
    ∑ r ∈ Finset.range m, multivariateEntirePow complement r
  have hone (x : Fin d → ℂ) : one.1 x = 1 := by
    simp [one, mvPolynomialMultivariateEntire]
  have hnormalizedTarget : normalized.1 (w target) = 1 := by
    change (separator.1 (w target))⁻¹ * separator.1 (w target) = 1
    exact inv_mul_cancel₀ htarget
  have hcomplementTarget : complement.1 (w target) = 0 := by
    simp [complement, U, hnormalizedTarget, hone]
  have hbumpTarget : bump.1 (w target) = 1 := by
    simp [bump, V, hcomplementTarget, hone, _hm.ne']
  have hbumpFactor (P : MultivariateEntire d) :
      multivariateEntireMul bump P =
      multivariateEntireMul U (multivariateEntireMul geom P) := by
    ext x
    have hgeom := geom_sum_mul_neg (1 - U.1 x) m
    have hbumpx : bump.1 x = one.1 x - (complement.1 x) ^ m := by
      rfl
    have hgeomx : geom.1 x =
        ∑ r ∈ Finset.range m, (complement.1 x) ^ r := by
      simp [geom]
    rw [multivariateEntireMul_apply, multivariateEntireMul_apply,
      multivariateEntireMul_apply, hbumpx, hgeomx]
    rw [hone]
    have hcomp : complement.1 x = 1 - U.1 x := by
      change one.1 x - U.1 x = 1 - U.1 x
      rw [hone]
    rw [hcomp]
    have hfactor :
        (∑ r ∈ Finset.range m, (1 - U.1 x) ^ r) * U.1 x =
          1 - (1 - U.1 x) ^ m := by
      calc
        (∑ r ∈ Finset.range m, (1 - U.1 x) ^ r) * U.1 x =
            (∑ r ∈ Finset.range m, (1 - U.1 x) ^ r) *
              (1 - (1 - U.1 x)) := by ring
        _ = 1 - (1 - U.1 x) ^ m := hgeom
    rw [← hfactor]
    ring
  have hbumpEq : bump = multivariateEntireMul U geom := by
    ext x
    have h := congrArg (fun f : MultivariateEntire d ↦ f.1 x) (hbumpFactor one)
    simpa [hone] using h
  refine ⟨bump, normalized, geom, hbumpTarget, hbumpEq, ?_, ?_, ?_⟩
  · intro j k hjk
    change (separator.1 (w target))⁻¹ *
      separator.1 (w j + integerCastVector k) = 0
    rw [hzero j k hjk, mul_zero]
  · intro P a ha
    have hvanish := multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt
      complement P (w target) hcomplementTarget a ha
    have hsource : multivariateEntireMul bump P =
        P - multivariateEntireMul V P := by
      ext x
      change (one.1 x - V.1 x) * P.1 x = P.1 x - V.1 x * P.1 x
      rw [hone]
      ring
    rw [hsource]
    calc
      multiIndexJetEvalCLM (w target) a
          (P - multivariateEntireMul V P) =
          multiIndexJetEvalCLM (w target) a P -
            multiIndexJetEvalCLM (w target) a (multivariateEntireMul V P) :=
        map_sub (multiIndexJetEvalCLM (w target) a) P
          (multivariateEntireMul V P)
      _ = multiIndexJetEvalCLM (w target) a P := by
        rw [show V = multivariateEntirePow complement m by rfl, hvanish, sub_zero]
  · intro P j k a hjk ha
    have hnormalizedZero : normalized.1 (w j + integerCastVector k) = 0 := by
      change (separator.1 (w target))⁻¹ *
        separator.1 (w j + integerCastVector k) = 0
      rw [hzero j k hjk, mul_zero]
    rw [hbumpFactor]
    exact multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt
      normalized (multivariateEntireMul geom P)
      (w j + integerCastVector k) hnormalizedZero a ha

/-- Bundled exact output of the explicit flat integer-lattice separator construction. -/
structure FlatIntegerLatticePacketSeparatorData
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (target : I) (m : ℕ) where
  bump : MultivariateEntire d
  normalized : MultivariateEntire d
  geom : MultivariateEntire d
  bump_target : bump.1 (w target) = 1
  factorization :
    bump = multivariateEntireMul (multivariateEntirePow normalized m) geom
  normalized_zero : ∀ (j : I) (k : Fin d → ℤ),
    (j ≠ target ∨ k ≠ 0) →
      normalized.1 (w j + integerCastVector k) = 0
  preserves_target : ∀ (P : MultivariateEntire d) (a : Fin d →₀ ℕ),
    Finsupp.degree a < m →
      multiIndexJetEvalCLM (w target) a (multivariateEntireMul bump P) =
        multiIndexJetEvalCLM (w target) a P
  kills_undesired : ∀ (P : MultivariateEntire d) (j : I) (k : Fin d → ℤ)
      (a : Fin d →₀ ℕ),
    (j ≠ target ∨ k ≠ 0) → Finsupp.degree a < m →
      multiIndexJetEvalCLM (w j + integerCastVector k) a
        (multivariateEntireMul bump P) = 0

/-- The explicit construction supplies bundled flat separator data at every positive order. -/
theorem nonempty_flatIntegerLatticePacketSeparatorData
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) (m : ℕ) (hm : 0 < m) :
    Nonempty (FlatIntegerLatticePacketSeparatorData w target m) := by
  obtain ⟨bump, normalized, geom, hbump, hfactor, hzero, hpreserve, hkill⟩ :=
    exists_flatIntegerLatticePacketSeparator w hdistinct target m hm
  exact ⟨⟨bump, normalized, geom, hbump, hfactor, hzero, hpreserve, hkill⟩⟩

/-- Canonical choice of the explicit separator, used only to name its analytically estimated
Poincare seeds.  Every mathematical property is exposed by the bundled fields above. -/
noncomputable def flatIntegerLatticePacketSeparatorData
    {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) (m : ℕ) (hm : 0 < m) :
    FlatIntegerLatticePacketSeparatorData w target m :=
  Classical.choice
    (nonempty_flatIntegerLatticePacketSeparatorData w hdistinct target m hm)

end

end GaloisForLFunctions.HTGeometry
