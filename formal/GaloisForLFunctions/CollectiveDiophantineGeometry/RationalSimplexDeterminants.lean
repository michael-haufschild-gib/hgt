import GaloisForLFunctions.HTGeometry.RationalRankStratumTopology
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.PNat.Basic

/-!
# Determinant spacing of rational simplices

In Streck's simplex lemma (arXiv:2610.23797, Lemma 3) the determinant of
homogeneous rational rows lies on a grid. Its mesh is the reciprocal of
the product of the denominators. For rows projected from a primitive
hyperplane, the last normal coefficient multiplies the mesh.
-/

noncomputable section
open Matrix Finset
namespace GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Homogeneous rows divided by their individual positive denominators. -/
def rows (A : Matrix ι ι ℤ) (q : ι → ℕ+) : Matrix ι ι ℚ :=
  Matrix.of fun i j => (A i j : ℚ) / (q i : ℕ)

/-- The numerator of the signed determinant is the integer determinant before reduction. -/
theorem clear_determinant (A : Matrix ι ι ℤ) (q : ι → ℕ+) :
    (∏ i, ((q i : ℕ) : ℚ)) * (rows A q).det = (A.det : ℚ) := by
  rw [← det_mul_column]
  change _ = Int.castRingHom ℚ A.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  change ((q i : ℕ) : ℚ) * ((A i j : ℚ) / (q i : ℕ)) = (A i j : ℚ)
  field_simp

/-- Below one grid spacing, the determinant vanishes, and this threshold is exact. -/
theorem subunit_iff (A : Matrix ι ι ℤ) (q : ι → ℕ+) :
    (∏ i, ((q i : ℕ) : ℚ)) * |(rows A q).det| < 1 ↔ A.det = 0 := by
  have hpos : 0 ≤ ∏ i, ((q i : ℕ) : ℚ) := by positivity
  rw [← abs_of_nonneg hpos, ← abs_mul, clear_determinant, ← Int.cast_abs]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (by exact_mod_cast Int.one_le_abs hn)) h
  · rintro h
    simp [h]

/-- The exact determinant test finds one rational hyperplane containing all the rows. -/
theorem common_hyperplane_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (q : Fin n → ℕ+) :
    (∃ c : Fin n → ℚ, c ≠ 0 ∧ ∀ i,
      (fun j => ((rows A q i j : ℚ) : ℝ)) ∈ HTGeometry.ratHyperplane c) ↔
        (∏ i, ((q i : ℕ) : ℚ)) * |(rows A q).det| < 1 := by
  have hpos : 0 < ∏ i, ((q i : ℕ) : ℚ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast (q i).pos
  rw [subunit_iff]
  have hzero : (rows A q).det = 0 ↔ A.det = 0 := by
    have eq := clear_determinant A q
    constructor
    · intro h
      rw [h, mul_zero] at eq
      exact_mod_cast eq.symm
    · intro h
      rw [h, Int.cast_zero] at eq
      exact (mul_eq_zero.mp eq).resolve_left hpos.ne'
  rw [← hzero, ← Matrix.exists_mulVec_eq_zero_iff]
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  constructor
  · intro h
    funext i
    have hi := (HTGeometry.mem_ratHyperplane.mp (h i))
    change ∑ j, rows A q i j * c j = 0
    rw [show (∑ j, rows A q i j * c j) = ∑ j, c j * rows A q i j by
      simp_rw [mul_comm]]
    exact_mod_cast hi
  · intro h i
    have hi := congrFun h i
    change ∑ j, rows A q i j * c j = 0 at hi
    apply HTGeometry.mem_ratHyperplane.mpr
    simp_rw [mul_comm (c _ : ℝ)]
    exact_mod_cast hi

/-- The content is the normalized integer gcd of all coordinates. -/
def content (v : ι → ℤ) : ℤ := univ.gcd v

omit [DecidableEq ι] in
/-- Applying an integral matrix preserves every common coordinate divisor. -/
theorem content_dvd_image (A : Matrix ι ι ℤ) (v : ι → ℤ) :
    content v ∣ content (A *ᵥ v) := by
  apply Finset.dvd_gcd
  intro i _
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right (Finset.gcd_dvd (mem_univ j)) _

/-- Applying the adjugate bounds all new common divisors by the determinant. -/
theorem image_content_dvd (A : Matrix ι ι ℤ) (v : ι → ℤ) :
    content (A *ᵥ v) ∣ A.det * content v := by
  have h := content_dvd_image A.adjugate (A *ᵥ v)
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec] at h
  exact h.trans ((univ.gcd_mul_left' v A.det).dvd)

/-- Primitive modular relations force divisibility of the projected minor, including
the case when the projected coordinates of the normal share a common factor. -/
theorem projection_modulus (A : Matrix ι ι ℤ) (v : ι → ℤ) (m : ℤ) :
    IsCoprime m (content v) → (∀ i, m ∣ (A *ᵥ v) i) → m ∣ A.det := by
  intro hc hm
  apply hc.dvd_of_dvd_mul_right
  exact (Finset.dvd_gcd fun i _ => hm i).trans (image_content_dvd A v)

/-- On a rational hyperplane the projected determinant is an integral multiple of
m divided by the denominator product. This retains the sign as well as the spacing. -/
theorem projected_grid (A : Matrix ι ι ℤ) (q : ι → ℕ+) (v : ι → ℤ) (m : ℤ) :
    IsCoprime m (content v) → (∀ i, m ∣ (A *ᵥ v) i) →
      ∃ z : ℤ, (∏ i, ((q i : ℕ) : ℚ)) * (rows A q).det = (m : ℚ) * z := by
  intro hc hm
  obtain ⟨z,hz⟩ := projection_modulus A v m hc hm
  exact ⟨z, by rw [clear_determinant, hz, Int.cast_mul]⟩

/-- The projected simplex either collapses or pays the full primitive normal coefficient. -/
theorem projected_gap (A : Matrix ι ι ℤ) (q : ι → ℕ+) (v : ι → ℤ) (m : ℤ) :
    IsCoprime m (content v) → (∀ i, m ∣ (A *ᵥ v) i) →
      (rows A q).det = 0 ∨ |(m : ℚ)| ≤ (∏ i, ((q i : ℕ) : ℚ)) * |(rows A q).det| := by
  intro hc hm
  obtain ⟨z,hz⟩ := projected_grid A q v m hc hm
  have hp : 0 < ∏ i, ((q i : ℕ) : ℚ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast (q i).pos
  by_cases he : z = 0
  · left
    rw [he, Int.cast_zero, mul_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hp.ne'
  · right
    have hh := congrArg abs hz
    rw [abs_mul, abs_mul, abs_of_pos hp] at hh
    rw [hh]
    exact le_mul_of_one_le_right (abs_nonneg _) (by exact_mod_cast Int.one_le_abs he)

end GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex

#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.clear_determinant
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.subunit_iff
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.common_hyperplane_iff
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.content_dvd_image
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.image_content_dvd
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.projection_modulus
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.projected_grid
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.projected_gap
