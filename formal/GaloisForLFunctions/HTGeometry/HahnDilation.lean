import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Dilations and gradings of Hahn series

A Hahn series field `HahnSeries Γ R` carries two commuting families of coefficientwise operators
attached to characters of the value group `Γ`.

* An *exponential* character `χ : Multiplicative Γ →* Rˣ` scales the coefficient of the exponent
  `g` by `χ g`.  Because `χ` is multiplicative on exponents and the product of Hahn series is the
  convolution over the antidiagonal of exponents, this is a ring automorphism: the dilation
  `z ↦ q z` of a Laurent series is the case `Γ = ℤ`, `χ n = qⁿ`.

* An *additive* character `μ : Γ →+ R` multiplies the coefficient of the exponent `g` by `μ g`.
  The same antidiagonal computation now gives the Leibniz rule, so this is a derivation: the Euler
  operator `z d/dz` is the case `μ = id`.

The two operators commute, and the fixed field of a dilation is described exactly by the kernel of
its character: if `χ g ≠ 1` for every `g ≠ 0`, the only dilation-invariant Hahn series are the
constants.  This is the property that makes a Hahn series field a difference field with no
extra invariants.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Multiplicative

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section Semiring

variable [CommRing R]

/-- The product coefficient computed over any pair of point-well-ordered sets containing the two
supports.  Terms outside the supports vanish, so enlarging the index sets does not change the
sum. -/
theorem coeff_mul_of_support_subset {x y : HahnSeries Γ R} {s t : Set Γ}
    (hs : s.IsPWO) (ht : t.IsPWO) (hxs : x.support ⊆ s) (hyt : y.support ⊆ t) (a : Γ) :
    (x * y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  classical
  rw [coeff_mul_left' hs hxs]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rcases Finset.mem_antidiagonal.mp hp with ⟨h1, h2, h3⟩
    exact Finset.mem_antidiagonal.mpr ⟨h1, hyt h2, h3⟩
  · intro p hp hnot
    rcases Finset.mem_antidiagonal.mp hp with ⟨h1, _, h3⟩
    have : p.2 ∉ y.support := by
      intro hmem
      exact hnot (Finset.mem_antidiagonal.mpr ⟨h1, hmem, h3⟩)
    have : y.coeff p.2 = 0 := by
      simpa [HahnSeries.mem_support] using this
    simp [this]

/-- Coefficientwise scaling of a Hahn series by an exponential character of the value group. -/
def hahnScale (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) : HahnSeries Γ R where
  coeff g := (χ (ofAdd g) : R) * f.coeff g
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro g hg
    simp only [Function.mem_support] at hg ⊢
    intro h
    exact hg (by simp [h])

@[simp]
theorem coeff_hahnScale (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) (g : Γ) :
    (hahnScale χ f).coeff g = (χ (ofAdd g) : R) * f.coeff g := rfl

theorem support_hahnScale_subset (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) :
    (hahnScale χ f).support ⊆ f.support := by
  intro g hg
  simp only [HahnSeries.mem_support, coeff_hahnScale] at hg ⊢
  intro h
  exact hg (by simp [h])

theorem hahnScale_add (χ : Multiplicative Γ →* Rˣ) (x y : HahnSeries Γ R) :
    hahnScale χ (x + y) = hahnScale χ x + hahnScale χ y := by
  ext g; simp [mul_add]

theorem hahnScale_one (χ : Multiplicative Γ →* Rˣ) :
    hahnScale χ (1 : HahnSeries Γ R) = 1 := by
  ext g
  by_cases h : g = 0
  · subst h
    simp [HahnSeries.coeff_one]
  · simp [HahnSeries.coeff_one, h]

theorem hahnScale_mul (χ : Multiplicative Γ →* Rˣ) (x y : HahnSeries Γ R) :
    hahnScale χ (x * y) = hahnScale χ x * hahnScale χ y := by
  classical
  ext a
  rw [coeff_hahnScale,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support subset_rfl subset_rfl a,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support
      (support_hahnScale_subset χ x) (support_hahnScale_subset χ y) a,
    Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsum : p.1 + p.2 = a := (Finset.mem_antidiagonal.mp hp).2.2
  have : (χ (ofAdd a) : R) = (χ (ofAdd p.1) : R) * (χ (ofAdd p.2) : R) := by
    rw [← hsum, ofAdd_add, map_mul, Units.val_mul]
  rw [coeff_hahnScale, coeff_hahnScale, this]
  ring

/-- Coefficientwise scaling by the trivial character is the identity. -/
theorem hahnScale_one_char (f : HahnSeries Γ R) :
    hahnScale (1 : Multiplicative Γ →* Rˣ) f = f := by
  ext g; simp

theorem hahnScale_hahnScale (χ ψ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) :
    hahnScale χ (hahnScale ψ f) = hahnScale (χ * ψ) f := by
  ext g; simp [mul_assoc]

/-- **The dilation automorphism of a Hahn series ring** attached to an exponential character of
its value group. -/
def hahnDilation (χ : Multiplicative Γ →* Rˣ) : HahnSeries Γ R ≃+* HahnSeries Γ R where
  toFun := hahnScale χ
  invFun := hahnScale χ⁻¹
  left_inv f := by
    rw [hahnScale_hahnScale, inv_mul_cancel χ, hahnScale_one_char]
  right_inv f := by
    rw [hahnScale_hahnScale, mul_inv_cancel χ, hahnScale_one_char]
  map_add' := hahnScale_add χ
  map_mul' := hahnScale_mul χ

@[simp]
theorem hahnDilation_apply (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) :
    hahnDilation χ f = hahnScale χ f := rfl

@[simp]
theorem coeff_hahnDilation (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) (g : Γ) :
    (hahnDilation χ f).coeff g = (χ (ofAdd g) : R) * f.coeff g := rfl

/-- A Hahn series is fixed by a dilation exactly when the character is trivial on its support. -/
theorem hahnDilation_eq_self_iff [NoZeroDivisors R] (χ : Multiplicative Γ →* Rˣ)
    (f : HahnSeries Γ R) :
    hahnDilation χ f = f ↔ ∀ g ∈ f.support, (χ (ofAdd g) : R) = 1 := by
  constructor
  · intro h g hg
    have := congrArg (fun x => HahnSeries.coeff x g) h
    simp only [coeff_hahnDilation] at this
    have hne : f.coeff g ≠ 0 := by simpa [HahnSeries.mem_support] using hg
    have : ((χ (ofAdd g) : R) - 1) * f.coeff g = 0 := by
      rw [sub_mul, one_mul, this, sub_self]
    rcases mul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hne
  · intro h
    ext g
    by_cases hg : f.coeff g = 0
    · simp [hg]
    · have : (χ (ofAdd g) : R) = 1 := h g (by simpa [HahnSeries.mem_support] using hg)
      simp [this]

end Semiring

section Grading

variable [CommRing R]

/-- Coefficientwise multiplication of a Hahn series by an additive character of the value group. -/
def hahnGrade (μ : Γ →+ R) (f : HahnSeries Γ R) : HahnSeries Γ R where
  coeff g := μ g * f.coeff g
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro g hg
    simp only [Function.mem_support] at hg ⊢
    intro h
    exact hg (by simp [h])

@[simp]
theorem coeff_hahnGrade (μ : Γ →+ R) (f : HahnSeries Γ R) (g : Γ) :
    (hahnGrade μ f).coeff g = μ g * f.coeff g := rfl

theorem support_hahnGrade_subset (μ : Γ →+ R) (f : HahnSeries Γ R) :
    (hahnGrade μ f).support ⊆ f.support := by
  intro g hg
  simp only [HahnSeries.mem_support, coeff_hahnGrade] at hg ⊢
  intro h
  exact hg (by simp [h])

theorem hahnGrade_add (μ : Γ →+ R) (x y : HahnSeries Γ R) :
    hahnGrade μ (x + y) = hahnGrade μ x + hahnGrade μ y := by
  ext g; simp [mul_add]

theorem hahnGrade_zero (μ : Γ →+ R) : hahnGrade μ (0 : HahnSeries Γ R) = 0 := by
  ext g; simp

theorem hahnGrade_one (μ : Γ →+ R) : hahnGrade μ (1 : HahnSeries Γ R) = 0 := by
  ext g
  by_cases h : g = 0
  · subst h; simp
  · simp [HahnSeries.coeff_one, h]

/-- **Leibniz rule for a coefficient grading.**  An additive character of the exponent group is
additive along the antidiagonal, which is exactly the product rule for the convolution. -/
theorem hahnGrade_mul (μ : Γ →+ R) (x y : HahnSeries Γ R) :
    hahnGrade μ (x * y) = hahnGrade μ x * y + x * hahnGrade μ y := by
  classical
  ext a
  rw [coeff_hahnGrade,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support subset_rfl subset_rfl a,
    HahnSeries.coeff_add,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support
      (support_hahnGrade_subset μ x) subset_rfl a,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support subset_rfl
      (support_hahnGrade_subset μ y) a,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsum : p.1 + p.2 = a := (Finset.mem_antidiagonal.mp hp).2.2
  have hmu : μ a = μ p.1 + μ p.2 := by rw [← hsum, map_add]
  rw [coeff_hahnGrade, coeff_hahnGrade, hmu]
  ring

/-- The grading operator as an additive homomorphism. -/
def hahnGradeHom (μ : Γ →+ R) : HahnSeries Γ R →+ HahnSeries Γ R where
  toFun := hahnGrade μ
  map_zero' := hahnGrade_zero μ
  map_add' := hahnGrade_add μ

@[simp]
theorem hahnGradeHom_apply (μ : Γ →+ R) (f : HahnSeries Γ R) :
    hahnGradeHom μ f = hahnGrade μ f := rfl

/-- **The derivation of a Hahn series ring** attached to an additive character of its value
group.  For `Γ = ℤ` and the identity character this is the Euler operator `z d/dz`. -/
noncomputable def hahnDerivation (μ : Γ →+ R) : Derivation ℤ (HahnSeries Γ R) (HahnSeries Γ R) :=
  Derivation.mk' (hahnGradeHom μ).toIntLinearMap (by
    intro a b
    simp only [AddMonoidHom.coe_toIntLinearMap, hahnGradeHom_apply, smul_eq_mul, hahnGrade_mul]
    ring)

@[simp]
theorem hahnDerivation_apply (μ : Γ →+ R) (f : HahnSeries Γ R) :
    hahnDerivation μ f = hahnGrade μ f := rfl

/-- The differential ring structure on a Hahn series ring given by an additive character. -/
@[reducible] noncomputable def hahnDifferential (μ : Γ →+ R) : Differential (HahnSeries Γ R) :=
  ⟨hahnDerivation μ⟩

/-- The differential ring structure given by an additive character rescaled by a series. -/
@[reducible] noncomputable def hahnScaledDifferential (μ : Γ →+ R) (u : HahnSeries Γ R) :
    Differential (HahnSeries Γ R) :=
  ⟨u • hahnDerivation μ⟩

theorem hahnScaledDifferential_deriv (μ : Γ →+ R) (u f : HahnSeries Γ R) :
    (hahnScaledDifferential μ u).deriv f = u * hahnGrade μ f := rfl

/-- Dilations commute with gradings: both act diagonally on coefficients. -/
theorem hahnScale_hahnGrade (χ : Multiplicative Γ →* Rˣ) (μ : Γ →+ R) (f : HahnSeries Γ R) :
    hahnScale χ (hahnGrade μ f) = hahnGrade μ (hahnScale χ f) := by
  ext g; simp [mul_left_comm]

end Grading

section Constants

variable [CommRing R]

/-- A Hahn series supported at the origin is the image of its constant coefficient. -/
theorem eq_single_zero_of_support_subset {f : HahnSeries Γ R} (h : f.support ⊆ {0}) :
    f = HahnSeries.single 0 (f.coeff 0) := by
  ext g
  by_cases hg : g = 0
  · subst hg; simp
  · have : f.coeff g = 0 := by
      by_contra hne
      exact hg (h (by simpa [HahnSeries.mem_support] using hne))
    simp [this, hg]

/-- **The invariants of a faithful dilation are the constants.**  If the exponential character is
nontrivial at every nonzero exponent, a Hahn series fixed by the dilation is supported at the
origin, hence is a constant. -/
theorem hahnDilation_eq_self_iff_single [NoZeroDivisors R] {χ : Multiplicative Γ →* Rˣ}
    (hχ : ∀ g : Γ, g ≠ 0 → (χ (ofAdd g) : R) ≠ 1) (f : HahnSeries Γ R) :
    hahnDilation χ f = f ↔ f = HahnSeries.single 0 (f.coeff 0) := by
  constructor
  · intro h
    refine eq_single_zero_of_support_subset ?_
    intro g hg
    by_contra hne
    exact hχ g (by simpa using hne) ((hahnDilation_eq_self_iff χ f).mp h g hg)
  · intro h
    refine (hahnDilation_eq_self_iff χ f).mpr ?_
    intro g hg
    have hsupp : g = 0 := by
      rw [h] at hg
      by_contra hne
      simp [HahnSeries.mem_support, hne] at hg
    subst hsupp
    simp

/-- The invariant field of a faithful dilation is the image of the coefficient ring. -/
theorem exists_single_of_hahnDilation_eq_self [NoZeroDivisors R] {χ : Multiplicative Γ →* Rˣ}
    (hχ : ∀ g : Γ, g ≠ 0 → (χ (ofAdd g) : R) ≠ 1) {f : HahnSeries Γ R}
    (h : hahnDilation χ f = f) : ∃ c : R, f = HahnSeries.single 0 c :=
  ⟨f.coeff 0, (hahnDilation_eq_self_iff_single hχ f).mp h⟩

end Constants

section Twist

variable [CommRing R]

/-- Coefficientwise twist of a Hahn series: apply a ring endomorphism to every coefficient and
scale the coefficient of the exponent `g` by `χ g`. -/
def hahnTwist (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) : HahnSeries Γ R where
  coeff g := (χ (ofAdd g) : R) * φ (f.coeff g)
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro g hg
    simp only [Function.mem_support] at hg ⊢
    intro h
    exact hg (by simp [h])

@[simp]
theorem coeff_hahnTwist (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) (g : Γ) :
    (hahnTwist φ χ f).coeff g = (χ (ofAdd g) : R) * φ (f.coeff g) := rfl

theorem support_hahnTwist_subset (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) :
    (hahnTwist φ χ f).support ⊆ f.support := by
  intro g hg
  simp only [HahnSeries.mem_support, coeff_hahnTwist] at hg ⊢
  intro h
  exact hg (by simp [h])

theorem hahnTwist_add (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (x y : HahnSeries Γ R) :
    hahnTwist φ χ (x + y) = hahnTwist φ χ x + hahnTwist φ χ y := by
  ext g; simp [mul_add]

theorem hahnTwist_one (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) :
    hahnTwist φ χ (1 : HahnSeries Γ R) = 1 := by
  ext g
  by_cases h : g = 0
  · subst h; simp [HahnSeries.coeff_one]
  · simp [HahnSeries.coeff_one, h]

theorem hahnTwist_mul (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (x y : HahnSeries Γ R) :
    hahnTwist φ χ (x * y) = hahnTwist φ χ x * hahnTwist φ χ y := by
  classical
  ext a
  rw [coeff_hahnTwist,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support subset_rfl subset_rfl a,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support
      (support_hahnTwist_subset φ χ x) (support_hahnTwist_subset φ χ y) a,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsum : p.1 + p.2 = a := (Finset.mem_antidiagonal.mp hp).2.2
  have hchi : (χ (ofAdd a) : R) = (χ (ofAdd p.1) : R) * (χ (ofAdd p.2) : R) := by
    rw [← hsum, ofAdd_add, map_mul, Units.val_mul]
  rw [coeff_hahnTwist, coeff_hahnTwist, hchi, map_mul]
  ring

/-- The twisted dilation as a ring homomorphism. -/
def hahnTwistHom (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) :
    HahnSeries Γ R →+* HahnSeries Γ R where
  toFun := hahnTwist φ χ
  map_one' := hahnTwist_one φ χ
  map_mul' := hahnTwist_mul φ χ
  map_zero' := by ext g; simp
  map_add' := hahnTwist_add φ χ

@[simp]
theorem hahnTwistHom_apply (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (f : HahnSeries Γ R) :
    hahnTwistHom φ χ f = hahnTwist φ χ f := rfl

end Twist

section CoeffMap

variable [CommRing R]

/-- The coefficientwise extension of an additive operator on the coefficient ring. -/
def hahnCoeffMap (D : R →+ R) (f : HahnSeries Γ R) : HahnSeries Γ R where
  coeff g := D (f.coeff g)
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro g hg
    simp only [Function.mem_support] at hg ⊢
    intro h
    exact hg (by simp [h])

@[simp]
theorem coeff_hahnCoeffMap (D : R →+ R) (f : HahnSeries Γ R) (g : Γ) :
    (hahnCoeffMap D f).coeff g = D (f.coeff g) := rfl

theorem support_hahnCoeffMap_subset (D : R →+ R) (f : HahnSeries Γ R) :
    (hahnCoeffMap D f).support ⊆ f.support := by
  intro g hg
  simp only [HahnSeries.mem_support, coeff_hahnCoeffMap] at hg ⊢
  intro h
  exact hg (by simp [h])

theorem hahnCoeffMap_add (D : R →+ R) (x y : HahnSeries Γ R) :
    hahnCoeffMap D (x + y) = hahnCoeffMap D x + hahnCoeffMap D y := by
  ext g; simp

theorem hahnCoeffMap_zero (D : R →+ R) : hahnCoeffMap D (0 : HahnSeries Γ R) = 0 := by
  ext g; simp

/-- **A coefficient derivation extends to a derivation of the Hahn series ring.** -/
theorem hahnCoeffMap_leibniz (D : R →+ R) (hD : ∀ x y : R, D (x * y) = D x * y + x * D y)
    (x y : HahnSeries Γ R) :
    hahnCoeffMap D (x * y) = hahnCoeffMap D x * y + x * hahnCoeffMap D y := by
  classical
  ext a
  rw [coeff_hahnCoeffMap,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support subset_rfl subset_rfl a,
    HahnSeries.coeff_add,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support
      (support_hahnCoeffMap_subset D x) subset_rfl a,
    coeff_mul_of_support_subset x.isPWO_support y.isPWO_support subset_rfl
      (support_hahnCoeffMap_subset D y) a,
    map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => hD _ _

theorem hahnCoeffMap_one (D : R →+ R) (hD : ∀ x y : R, D (x * y) = D x * y + x * D y) :
    hahnCoeffMap D (1 : HahnSeries Γ R) = 0 := by
  have h := hD 1 1
  rw [mul_one, mul_one, one_mul] at h
  have h0 : (0 : R) + D 1 = D 1 + D 1 := by rw [zero_add]; exact h
  have hD1 : D 1 = 0 := (add_right_cancel h0).symm
  ext g
  by_cases hg : g = 0
  · subst hg; simp [HahnSeries.coeff_one, hD1]
  · simp [HahnSeries.coeff_one, hg]

/-- A coefficient operator commuting with the coefficient twist commutes with the twisted
dilation. -/
theorem hahnTwist_hahnCoeffMap (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (D : R →+ R)
    (hcomm : ∀ x : R, φ (D x) = D (φ x))
    (hlin : ∀ (g : Γ) (x : R), D ((χ (ofAdd g) : R) * x) = (χ (ofAdd g) : R) * D x)
    (f : HahnSeries Γ R) :
    hahnTwist φ χ (hahnCoeffMap D f) = hahnCoeffMap D (hahnTwist φ χ f) := by
  ext g
  rw [coeff_hahnTwist, coeff_hahnCoeffMap, coeff_hahnCoeffMap, coeff_hahnTwist, hlin, hcomm]

/-- The twisted dilation commutes with a grading whose character values are fixed by the
coefficient twist. -/
theorem hahnTwist_hahnGrade (φ : R →+* R) (χ : Multiplicative Γ →* Rˣ) (μ : Γ →+ R)
    (hfix : ∀ g : Γ, φ (μ g) = μ g) (f : HahnSeries Γ R) :
    hahnTwist φ χ (hahnGrade μ f) = hahnGrade μ (hahnTwist φ χ f) := by
  ext g
  rw [coeff_hahnTwist, coeff_hahnGrade, coeff_hahnGrade, coeff_hahnTwist, map_mul, hfix]
  ring

/-- The coefficientwise operator as an additive homomorphism. -/
def hahnCoeffMapHom (D : R →+ R) : HahnSeries Γ R →+ HahnSeries Γ R where
  toFun := hahnCoeffMap D
  map_zero' := hahnCoeffMap_zero D
  map_add' := hahnCoeffMap_add D

@[simp]
theorem hahnCoeffMapHom_apply (D : R →+ R) (f : HahnSeries Γ R) :
    hahnCoeffMapHom D f = hahnCoeffMap D f := rfl

end CoeffMap

section CoeffRingHom

variable {S : Type*} [CommRing R] [CommRing S]

/-- The coefficientwise application of a ring homomorphism, as a ring homomorphism of Hahn
series. -/
def hahnMapRingHom (f : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun x := x.map f
  map_one' := by
    ext g
    by_cases h : g = 0
    · subst h; simp [HahnSeries.coeff_one, HahnSeries.map_coeff]
    · simp [HahnSeries.coeff_one, HahnSeries.map_coeff, h]
  map_mul' x y := by
    ext g
    simp only [HahnSeries.map_coeff]
    exact congrArg (fun t : HahnSeries Γ S => t.coeff g) (HahnSeries.map_mul (f : R →ₙ+* S))
  map_zero' := by ext g; simp [HahnSeries.map_coeff]
  map_add' x y := by ext g; simp [HahnSeries.map_coeff]

@[simp]
theorem coeff_hahnMapRingHom (f : R →+* S) (x : HahnSeries Γ R) (g : Γ) :
    (hahnMapRingHom (Γ := Γ) f x).coeff g = f (x.coeff g) :=
  HahnSeries.map_coeff x f g

/-- The coefficient map intertwines two twisted dilations whose data correspond. -/
theorem hahnMapRingHom_hahnTwist (ψ : R →+* S) (φ : R →+* R) (φ' : S →+* S)
    (χ : Multiplicative Γ →* Rˣ) (χ' : Multiplicative Γ →* Sˣ)
    (hφ : ∀ x : R, ψ (φ x) = φ' (ψ x))
    (hχ : ∀ g : Γ, ψ (χ (ofAdd g) : R) = (χ' (ofAdd g) : S))
    (f : HahnSeries Γ R) :
    hahnMapRingHom ψ (hahnTwist φ χ f) = hahnTwist φ' χ' (hahnMapRingHom ψ f) := by
  ext g
  rw [coeff_hahnMapRingHom, coeff_hahnTwist, coeff_hahnTwist, coeff_hahnMapRingHom, map_mul,
    hχ, hφ]

theorem coeff_C_mul_hahn (c : R) (x : HahnSeries Γ R) (g : Γ) :
    ((HahnSeries.C c : HahnSeries Γ R) * x).coeff g = c * x.coeff g := by
  rw [mul_comm, HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero, mul_comm]

end CoeffRingHom

end GaloisForLFunctions.HTGeometry
