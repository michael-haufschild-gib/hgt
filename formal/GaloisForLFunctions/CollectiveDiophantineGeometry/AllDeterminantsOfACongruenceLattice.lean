import GaloisForLFunctions.CollectiveDiophantineGeometry.RationalSimplexDeterminants
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# All determinants on an integral congruence hyperplane

For rows satisfying the congruence against v modulo m, the divisibility
condition on the determinant in Streck's simplex lemma is also sufficient.
A rank-one change scales the primitive direction of v and fixes its
Bézout complement. This produces every allowed signed determinant.
-/

noncomputable section
open Finset Matrix
namespace GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integer linear probes of a vector produce exactly the multiples of its content. -/
theorem dot_range (v : ι → ℤ) (t : ℤ) :
    (∃ u, u ⬝ᵥ v = t) ↔ content v ∣ t := by
  constructor
  · rintro ⟨u,rfl⟩
    exact dvd_sum fun i _ => dvd_mul_of_dvd_right (gcd_dvd (mem_univ i)) _
  · rintro ⟨a,rfl⟩
    obtain ⟨u,hu₀⟩ := univ.gcd_eq_sum_mul v
    have hu : (∑ i, u i*v i) = content v := by
      simpa only [content,mul_comm] using hu₀.symm
    refine ⟨a • u,?_⟩
    rw [smul_dotProduct]
    change a*(∑ i, u i*v i)=content v*a
    rw [hu,mul_comm]

/-- Dividing a nonzero normal by its content yields a primitive vector with an integral dual. -/
theorem primitive_direction (v : ι → ℤ) (hv : v ≠ 0) :
    ∃ w u : ι → ℤ, v = content v • w ∧ u ⬝ᵥ w = 1 := by
  have hd (i : ι) : content v ∣ v i := gcd_dvd (mem_univ i)
  have hC : content v ≠ 0 := by
    intro hc
    apply hv
    funext i
    simpa only [hc,zero_dvd_iff] using hd i
  let w (i : ι) := v i / content v
  have he : v = content v • w := by
    funext i
    exact (Int.mul_ediv_cancel' (hd i)).symm
  obtain ⟨u,hu⟩ := (dot_range v (content v)).2 dvd_rfl
  refine ⟨w,u,he,?_⟩
  calc
    _ = 1 := by
      apply mul_left_cancel₀ hC
      rw [← show (content v : ℤ) • (u ⬝ᵥ w) = content v*(u ⬝ᵥ w) from rfl,
        ← dotProduct_smul,← he,hu,mul_one]

/-- Dilation in the w direction along the kernel of the integral dual u. -/
def dilation (w u : ι → ℤ) (d : ℤ) : Matrix ι ι ℤ :=
  1 + vecMulVec ((d-1) • w) u

theorem dilation_apply (w u x : ι → ℤ) (d : ℤ) (i : ι) :
    (dilation w u d *ᵥ x) i = x i+(d-1)*(u ⬝ᵥ x)*w i := by
  rw [dilation,add_mulVec,one_mulVec,vecMulVec_mulVec]
  change x i+((d-1)*w i)*(u ⬝ᵥ x)=_
  ring

theorem dilation_det (w u : ι → ℤ) (d : ℤ) (h : u ⬝ᵥ w = 1) :
    (dilation w u d).det=d := by
  rw [dilation,HTGeometry.bgv_det_add_vecMulVec,det_one,adjugate_one,one_mulVec,dotProduct_smul,h]
  change 1+(d-1)*1=d
  ring

/-- A single rank-one dilation achieves any requested determinant permitted by
the congruence, including zero and negative determinants. -/
theorem determinant_realizability (v : ι → ℤ) (m d : ℤ) (hv : v ≠ 0) :
    (∃ A : Matrix ι ι ℤ, A.det=d ∧ ∀ i, m ∣ (A *ᵥ v) i) ↔ m ∣ d*content v := by
  constructor
  · rintro ⟨A,rfl,h⟩
    exact (Finset.dvd_gcd fun i _ => h i).trans (image_content_dvd A v)
  · intro h
    obtain ⟨w,u,he,hu⟩ := primitive_direction v hv
    refine ⟨dilation w u d,dilation_det _ _ _ hu,fun i => ?_⟩
    have h₁ : u ⬝ᵥ v = content v := by
      conv_lhs => rw [he,dotProduct_smul,hu]
      exact mul_one _
    rw [dilation_apply,h₁]
    have h₂ := congrFun he i
    change v i=content v*w i at h₂
    rw [h₂,show content v*w i+(d-1)*content v*w i=(d*content v)*w i by ring]
    exact dvd_mul_of_dvd_left h _

/-- Classification including the zero normal and the zero-dimensional
lattice. In positive dimension the congruence imposes exactly one
divisibility condition on the signed determinant. -/
theorem all_determinants (v : ι → ℤ) (m d : ℤ) :
    (∃ A : Matrix ι ι ℤ, A.det=d ∧ ∀ i, m ∣ (A *ᵥ v) i) ↔
      m ∣ d*content v ∧ (IsEmpty ι → d=1) := by
  constructor
  · rintro ⟨A,rfl,h⟩
    refine ⟨(Finset.dvd_gcd fun i _ => h i).trans (image_content_dvd A v),fun hι => ?_⟩
    letI := hι
    rw [Subsingleton.elim A (1 : Matrix ι ι ℤ),det_one]
  · rintro ⟨hd,h₀⟩
    rcases isEmpty_or_nonempty ι with hι | ⟨i⟩
    · exact ⟨1,(det_one).trans (h₀ hι).symm,fun i => (hι.false i).elim⟩
    · by_cases hz : v=0
      · subst v
        let w := Pi.single i (1 : ℤ)
        have hw : w ⬝ᵥ w=1 := by simp [w,single_dotProduct]
        exact ⟨dilation w w d,dilation_det _ _ _ hw,fun j => by simp⟩
      · exact (determinant_realizability v m d hz).2 hd

/-- The attainable cleared rational determinants form the same exact grid,
independently of the individual positive row denominators. -/
theorem rational_realizability (v : ι → ℤ) (q : ι → ℕ+) (m d : ℤ) (hv : v ≠ 0) :
    (∃ A : Matrix ι ι ℤ, (∏ i, ((q i : ℕ) : ℚ))*(rows A q).det=d ∧
      ∀ i, m ∣ (A *ᵥ v) i) ↔ m ∣ d*content v := by
  simp only [clear_determinant,Int.cast_inj]
  exact determinant_realizability v m d hv

end GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex

#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.dot_range
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.primitive_direction
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.dilation_apply
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.dilation_det
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.determinant_realizability
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.all_determinants
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.Simplex.rational_realizability
