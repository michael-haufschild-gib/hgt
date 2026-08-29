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
noncomputable def hahnDifferential (μ : Γ →+ R) : Differential (HahnSeries Γ R) :=
  ⟨hahnDerivation μ⟩

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
    simp [this, HahnSeries.coeff_single, hg]

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
      simp [HahnSeries.mem_support, HahnSeries.coeff_single, hne] at hg
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

end GaloisForLFunctions.HTGeometry
