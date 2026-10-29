import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
/-!
# The projective charts of the finite-field elliptic function field

Inside `K=Frac(𝔽₃[x,y]/(y²−x³+x))`, the two affine coordinate algebras are
`𝔽₃[x,y]` and `𝔽₃[x/y,1/y]`. They cover the projective cubic and their intersection
is precisely `𝔽₃`.

The norm degree of `p(x)+q(x)y` is `max(2 deg p,2 deg q+3)`. It is additive on
products and subadditive on sums. Fractions with numerator norm degree at most the
denominator norm degree form a subalgebra containing the infinity chart. An affine
function in that subalgebra must have norm degree at most zero, hence be constant.
-/

open Polynomial
open scoped nonZeroDivisors
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
noncomputable section
abbrev A := CoordinateRing
abbrev K := FunctionField
def xA : A := algebraMap Constants[X] A X
def yA : A := AdjoinRoot.root curve.toAffine.polynomial
def x : K := algebraMap A K xA
def y : K := algebraMap A K yA
lemma yA_eq : yA = WeierstrassCurve.Affine.CoordinateRing.mk curve.toAffine X := rfl
lemma curve_polynomial : curve.toAffine.polynomial = X ^ 2 - C cubic := by
  simp [WeierstrassCurve.Affine.polynomial, curve, cubic, sub_eq_add_neg]
lemma relationA : yA ^ 2 = xA ^ 3 - xA := by
  have h := AdjoinRoot.eval₂_root curve.toAffine.polynomial
  change eval₂ (algebraMap Constants[X] A) yA curve.toAffine.polynomial = 0 at h
  simp only [curve_polynomial] at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, cubic, map_sub, map_pow] at h
  exact sub_eq_zero.mp h
lemma relation : y ^ 2 = x ^ 3 - x := by
  simpa only [x, y, map_pow, map_sub] using congrArg (algebraMap A K) relationA
lemma yA_ne_zero : yA ≠ 0 := by
  intro h
  have hh := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
    (W' := curve.toAffine) (p := 0) (q := 1) (by simpa only [zero_smul, one_smul, zero_add, ← yA_eq] using h)
  exact one_ne_zero hh.2
lemma y_ne_zero : y ≠ 0 := by
  simpa only [y, map_zero] using (IsFractionRing.injective A K).ne yA_ne_zero
/-- Norm degree, assigning weights two to `x` and three to `y`. -/
def poleDegree (a : A) : WithBot ℕ := (Algebra.norm Constants[X] a).degree
lemma poleDegree_basis (p q : Constants[X]) :
    poleDegree (p • (1 : A) + q • yA) = max (2 • p.degree) (2 • q.degree + 3) := by
  exact WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis p q
lemma poleDegree_zero : poleDegree 0 = ⊥ := by
  simpa using poleDegree_basis 0 0
lemma poleDegree_one : poleDegree 1 = 0 := by
  simp [poleDegree]
lemma poleDegree_mul (a b : A) : poleDegree (a * b) = poleDegree a + poleDegree b := by
  simp only [poleDegree, map_mul, degree_mul]
lemma twice_max (a b : WithBot ℕ) : 2 • max a b = max (2 • a) (2 • b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (nsmul_le_nsmul_right h 2)]
  · rw [max_eq_left h, max_eq_left (nsmul_le_nsmul_right h 2)]
lemma poleDegree_add (a b : A) : poleDegree (a + b) ≤ max (poleDegree a) (poleDegree b) := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  obtain ⟨r, s, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq b
  simp only [← yA_eq]
  rw [show p • (1 : A) + q • yA + (r • 1 + s • yA) =
    (p + r) • 1 + (q + s) • yA by simp only [add_smul]; abel]
  simp only [poleDegree_basis]
  apply max_le
  · calc 2 • (p + r).degree ≤ 2 • max p.degree r.degree := nsmul_le_nsmul_right (degree_add_le p r) 2
         _ = max (2 • p.degree) (2 • r.degree) := by simp only [twice_max]
         _ ≤ _ := max_le_max (le_max_left _ _) (le_max_left _ _)
  · calc 2 • (q + s).degree + 3 ≤ 2 • max q.degree s.degree + 3 :=
           add_le_add (nsmul_le_nsmul_right (degree_add_le q s) 2) le_rfl
         _ = max (2 • q.degree + 3) (2 • s.degree + 3) := by rw [twice_max, max_add_add_right]
         _ ≤ _ := max_le_max (le_max_right _ _) (le_max_right _ _)

lemma poleDegree_eq_bot_iff (a : A) : poleDegree a = ⊥ ↔ a = 0 := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  simp only [← yA_eq, poleDegree_basis]
  constructor
  · intro h
    have hp : p = 0 := by
      by_contra hp
      have hh := (le_max_left (2 • p.degree) (2 • q.degree + 3)).trans_eq h
      rw [degree_eq_natDegree hp] at hh
      norm_cast at hh
    have hq : q = 0 := by
      by_contra hq
      have hh := (le_max_right (2 • p.degree) (2 • q.degree + 3)).trans_eq h
      rw [degree_eq_natDegree hq] at hh
      norm_cast at hh
    simp only [hp, hq, zero_smul, add_zero]
  · intro h
    have hh := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero (W' := curve.toAffine) h
    simp [hh.1, hh.2]
lemma scalar_eq_basis (c : Constants) :
    algebraMap Constants A c = C c • (1 : A) + (0 : Constants[X]) • yA := by
  simp only [Algebra.smul_def, map_zero, zero_mul, add_zero, mul_one]
  exact IsScalarTower.algebraMap_apply Constants Constants[X] A c
lemma poleDegree_scalar (c : Constants) : poleDegree (algebraMap Constants A c) ≤ 0 := by
  rw [scalar_eq_basis, poleDegree_basis]
  simpa using (nsmul_le_nsmul_right (degree_C_le (a := c)) 2)
lemma poleDegree_le_zero_iff (a : A) :
    poleDegree a ≤ 0 ↔ ∃ c : Constants, a = algebraMap Constants A c := by
  constructor
  · intro h
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
    simp only [← yA_eq, poleDegree_basis, max_le_iff] at h ⊢
    have hq : q = 0 := by
      by_contra hq
      have hh := h.2
      rw [degree_eq_natDegree hq] at hh
      norm_cast at hh
    have hp : p.degree ≤ 0 := by
      by_cases hp : p = 0
      · simp [hp]
      · have hh := h.1
        rw [degree_eq_natDegree hp] at hh ⊢
        simp only [two_nsmul] at hh
        have hh' : p.natDegree + p.natDegree ≤ 0 := by exact_mod_cast hh
        have hp0 : p.natDegree = 0 := by omega
        simp [hp0]
    refine ⟨p.coeff 0, ?_⟩
    rw [degree_le_zero_iff.mp hp, hq, ← scalar_eq_basis]
    simp only [coeff_C_zero]
  · rintro ⟨c, rfl⟩
    exact poleDegree_scalar c

lemma poleDegree_xA : poleDegree xA = 2 := by
  have hx : xA = (X : Constants[X]) • (1 : A) + (0 : Constants[X]) • yA := by
    simp [xA, Algebra.smul_def]
  rw [hx, poleDegree_basis]
  norm_num
lemma poleDegree_yA : poleDegree yA = 3 := by
  have h := poleDegree_basis 0 1
  simpa using h
lemma map_ne_zero {a : A} (ha : a ≠ 0) : algebraMap A K a ≠ 0 := by
  simpa only [map_zero] using (IsFractionRing.injective A K).ne ha
/-- Fractions whose numerator has no larger infinity pole than their denominator. -/
def infinityRegular : Subalgebra Constants K where
  carrier := {z | ∃ a b : A, b ≠ 0 ∧ z = algebraMap A K a / algebraMap A K b ∧
    poleDegree a ≤ poleDegree b}
  zero_mem' := ⟨0, 1, one_ne_zero, by simp, by rw [poleDegree_zero, poleDegree_one]; exact bot_le⟩
  one_mem' := ⟨1, 1, one_ne_zero, by simp, le_rfl⟩
  add_mem' := by
    rintro z w ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, rfl, hcd⟩
    refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · simp only [map_add, map_mul]
      field_simp [map_ne_zero hb, map_ne_zero hd]
    · calc poleDegree (a * d + c * b) ≤ max (poleDegree (a * d)) (poleDegree (c * b)) :=
             poleDegree_add _ _
           _ ≤ poleDegree (b * d) := by
             rw [poleDegree_mul, poleDegree_mul, poleDegree_mul]
             exact max_le (add_le_add hab le_rfl)
               (by simpa only [add_comm] using add_le_add hcd (le_refl (poleDegree b)))
  mul_mem' := by
    rintro z w ⟨a, b, hb, rfl, hab⟩ ⟨c, d, hd, rfl, hcd⟩
    refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · simp only [map_mul, div_mul_div_comm]
    · rw [poleDegree_mul, poleDegree_mul]
      exact add_le_add hab hcd
  algebraMap_mem' c := by
    refine ⟨algebraMap Constants A c, 1, one_ne_zero, ?_, ?_⟩
    · rw [map_one, div_one, ← IsScalarTower.algebraMap_apply]
    · rw [poleDegree_one]
      exact poleDegree_scalar c
/-- The two affine charts, as subalgebras of the same function field. -/
def affineChart : Subalgebra Constants K := (IsScalarTower.toAlgHom Constants A K).range
def infinityChart : Subalgebra Constants K := Algebra.adjoin Constants ({x / y, y⁻¹} : Set K)
lemma infinityChart_le : infinityChart ≤ infinityRegular := by
  apply Algebra.adjoin_le_iff.mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz
  · exact ⟨xA, yA, yA_ne_zero, rfl, by rw [poleDegree_xA, poleDegree_yA]; norm_num⟩
  · rcases Set.mem_singleton_iff.mp hz with rfl
    exact ⟨1, yA, yA_ne_zero, by simp [y, one_div],
      by rw [poleDegree_one, poleDegree_yA]; norm_num⟩
lemma affine_mem_infinityRegular_iff (a : A) :
    algebraMap A K a ∈ infinityRegular ↔ ∃ c : Constants, a = algebraMap Constants A c := by
  constructor
  · rintro ⟨b, d, hd, heq, hbd⟩
    have had : a * d = b := (IsFractionRing.injective A K) (by
      rw [map_mul]
      exact (eq_div_iff (map_ne_zero hd)).mp heq)
    have hh : poleDegree a + poleDegree d ≤ 0 + poleDegree d := by
      rw [← poleDegree_mul, had, zero_add]
      exact hbd
    exact (poleDegree_le_zero_iff a).mp
      ((WithBot.add_le_add_iff_right (mt (poleDegree_eq_bot_iff d).mp hd)).mp hh)
  · rintro ⟨c, rfl⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact infinityRegular.algebraMap_mem c
/-- Every function regular on both projective charts is constant. -/
lemma mem_both_charts_iff (z : K) :
    z ∈ affineChart ∧ z ∈ infinityChart ↔ ∃ c : Constants, z = algebraMap Constants K c := by
  constructor
  · rintro ⟨⟨a, rfl⟩, hz⟩
    obtain ⟨c, hc⟩ := (affine_mem_infinityRegular_iff a).mp (infinityChart_le hz)
    exact ⟨c, by rw [hc]; exact (IsScalarTower.toAlgHom Constants A K).commutes c⟩
  · rintro ⟨c, rfl⟩
    exact ⟨affineChart.algebraMap_mem c, infinityChart.algebraMap_mem c⟩

/-- The infinity chart has the equation obtained by setting the projective Y-coordinate to one. -/
lemma infinity_chart_equation : (x / y) ^ 3 - (x / y) * (y⁻¹) ^ 2 - y⁻¹ = 0 := by
  field_simp [y_ne_zero]
  linear_combination -relation
/-- The two displayed charts cover every nonzero homogeneous solution over every extension. -/
lemma projective_chart_cover {E : Type*} [Field E] (a b c : E)
    (h : b ^ 2 * c = a ^ 3 - a * c ^ 2) (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    b ≠ 0 ∨ c ≠ 0 := by
  by_contra hh
  push Not at hh
  obtain ⟨rfl, rfl⟩ := hh
  have ha : a = 0 := by simpa using h.symm
  exact hn.elim (fun h => h ha) (fun h => h.elim (fun h => h rfl) (fun h => h rfl))
end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
