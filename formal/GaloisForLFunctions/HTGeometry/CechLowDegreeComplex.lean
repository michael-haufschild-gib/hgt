import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The low-degree multiplicative Čech complex

The anomaly cochains of the bi-anomaly live in Čech degrees zero, one and two of a cover, with
multiplicative coefficients.  In those degrees the differential is explicit and the complex property
is a two-line computation in a commutative group, so no simplicial machinery is needed.

The three degrees carried here are exactly the ones the gerbe cochain uses: a degree-zero cochain on
patches, a degree-one cochain on overlaps, and a degree-two cochain on triple overlaps.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} {G : Type*} [CommGroup G]

/-- The Čech differential from patches to overlaps. -/
def cechD0 (f : ι → G) : ι → ι → G := fun a b => f b / f a

/-- The Čech differential from overlaps to triple overlaps. -/
def cechD1 (g : ι → ι → G) : ι → ι → ι → G := fun a b c => g b c / g a c * g a b

/-- The Čech differential from triple to quadruple overlaps. -/
def cechD2 (h : ι → ι → ι → G) : ι → ι → ι → ι → G :=
  fun a b c d => h b c d / h a c d * h a b d / h a b c

/-- The six-fold cancellation behind the second complex property. -/
theorem sixfold_cancel (p q r s t u : G) :
    (p / q * r) / (p / s * t) * (q / s * u) / (r / t * u) = 1 := by
  have hrw : (p / q * r) / (p / s * t) * (q / s * u) / (r / t * u)
      = (p * q * r * s * t * u) * (p * q * r * s * t * u)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [hrw, mul_inv_cancel]

/-- **The complex property in the first degree.** -/
theorem cechD1_cechD0 (f : ι → G) : cechD1 (cechD0 f) = fun _ _ _ => (1 : G) := by
  funext a b c
  simp only [cechD1, cechD0]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- **The complex property in the second degree.** -/
theorem cechD2_cechD1 (g : ι → ι → G) : cechD2 (cechD1 g) = fun _ _ _ _ => (1 : G) := by
  funext a b c d
  simp only [cechD2, cechD1]
  exact sixfold_cancel _ _ _ _ _ _

/-- A coefficient sector: a subset of the group closed under the group operations. -/
structure Sector (G : Type*) [CommGroup G] where
  /-- The underlying set. -/
  carrier : Set G
  /-- It contains the unit. -/
  one_mem : (1 : G) ∈ carrier
  /-- It is closed under products. -/
  mul_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x * y ∈ carrier
  /-- It is closed under inverses. -/
  inv_mem : ∀ {x}, x ∈ carrier → x⁻¹ ∈ carrier

theorem Sector.div_mem {S : Sector G} {x y : G} (hx : x ∈ S.carrier) (hy : y ∈ S.carrier) :
    x / y ∈ S.carrier := by
  rw [div_eq_mul_inv]
  exact S.mul_mem hx (S.inv_mem hy)

/-- **A sector is a subcomplex in the first degree.** -/
theorem cechD0_mem (S : Sector G) {f : ι → G} (hf : ∀ a, f a ∈ S.carrier) (a b : ι) :
    cechD0 f a b ∈ S.carrier :=
  S.div_mem (hf b) (hf a)

/-- **A sector is a subcomplex in the second degree.** -/
theorem cechD1_mem (S : Sector G) {g : ι → ι → G} (hg : ∀ a b, g a b ∈ S.carrier) (a b c : ι) :
    cechD1 g a b c ∈ S.carrier :=
  S.mul_mem (S.div_mem (hg b c) (hg a c)) (hg a b)

/-- **A sector is a subcomplex in the third degree.** -/
theorem cechD2_mem (S : Sector G) {h : ι → ι → ι → G} (hh : ∀ a b c, h a b c ∈ S.carrier)
    (a b c d : ι) : cechD2 h a b c d ∈ S.carrier :=
  S.div_mem (S.mul_mem (S.div_mem (hh b c d) (hh a c d)) (hh a b d)) (hh a b c)

/-- A degree-one cochain whose differential lands in a sector defines a relative class: the
differential is a sector-valued cocycle. -/
theorem cechD2_cechD1_mem_of_mem (S : Sector G) {g : ι → ι → G}
    (hd : ∀ a b c, cechD1 g a b c ∈ S.carrier) (a b c d : ι) :
    cechD2 (cechD1 g) a b c d ∈ S.carrier ∧ cechD2 (cechD1 g) a b c d = 1 := by
  refine ⟨cechD2_mem S hd a b c d, ?_⟩
  rw [cechD2_cechD1]

end GaloisForLFunctions.HTGeometry
