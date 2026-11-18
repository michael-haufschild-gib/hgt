import GaloisForLFunctions.HTGeometry.TraceZeroNonrealDivisorMicroblock
import Mathlib.Algebra.Group.Conj

/-!
# Borel restrictions of quadratic adjoint orbits

Braverman–Kazhdan, Lemma 5.12 (arXiv:2604.11735), distinguishes elliptic
adjoint orbits by transitivity on their restrictions. The companion matrix
gives one construction over every field, including characteristic two.
For an imaginary trace-zero microblock the real companion has a single
restricted orbit, while complexification produces two additional fixed points.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open Matrix
variable {K : Type*} [Field K]
local notation "Mat" => Matrix (Fin 2) (Fin 2) K

/-- Cyclic representative of the quadratic orbit with negative determinant q. -/
def quadraticCompanion (q : K) : Mat := !![0,q;1,0]

/-- Restriction to the two coordinates dual to the upper triangular Lie algebra. -/
def borelProjection (Y : Mat) : K × K := (Y 0 0, Y 1 0)

/-- Actual image of the entire matrix conjugacy class. -/
def quadraticRestrictedOrbit (q : K) : Set (K × K) :=
  {x | ∃ Y : Mat, IsConj (quadraticCompanion q) Y ∧ borelProjection Y = x}

private theorem matrix_intertwiner {A B C : Mat} (hd : B.det ≠ 0) (h : B * A = C * B) :
    IsConj A C := by
  obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hd)
  refine ⟨g, ?_⟩
  change (g : Mat) * A = C * g
  rw [hg]
  exact h

private theorem companion_sq (q : K) : (quadraticCompanion q)^2 = q • (1 : Mat) := by
  rw [pow_two, quadraticCompanion, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- All actual conjugates, over any ground field, obey the same scalar quadratic equation. -/
theorem quadraticCompanion_orbit_square (q : K) (Y : Mat) (h : IsConj (quadraticCompanion q) Y) :
    Y^2 = q • (1 : Mat) := by
  obtain ⟨g,hg⟩ := h.pow 2
  have he := hg.eq
  rw [companion_sq, mul_smul_comm, mul_one] at he
  apply g.isUnit.mul_right_cancel
  simpa only [smul_mul_assoc, one_mul] using he.symm

/-- A restriction is present exactly when its lower coordinate is nonzero or its upper
coordinate is a square root of the orbit parameter. -/
theorem quadraticRestrictedOrbit_mem (q a c : K) :
    (a,c) ∈ quadraticRestrictedOrbit q ↔ c ≠ 0 ∨ a^2 = q := by
  constructor
  · rintro ⟨Y, hY, hx⟩
    by_cases hc : c = 0
    · right
      have h0 : Y 0 0 = a := congrArg Prod.fst hx
      have h1 : Y 1 0 = 0 := (congrArg Prod.snd hx).trans hc
      have he := congrArg (fun A : Mat => A 0 0) (quadraticCompanion_orbit_square q Y hY)
      simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h0, h1] using he
    · exact Or.inl hc
  · intro h
    by_cases hc : c = 0
    · have ha := h.resolve_left (not_not_intro hc)
      subst c
      refine ⟨!![a,1;0,-a], ?_, rfl⟩
      apply matrix_intertwiner (B := !![0,1;1,-a])
      · simp [Matrix.det_fin_two_of]
      · rw [← ha, quadraticCompanion, Matrix.mul_fin_two, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
        ring
    · refine ⟨!![a,(q-a^2)/c;c,-a], ?_, rfl⟩
      apply matrix_intertwiner (B := !![1,a;0,c])
      · simpa [Matrix.det_fin_two_of] using hc
      · rw [quadraticCompanion, Matrix.mul_fin_two, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- Change of a restricted covector by an upper triangular projective matrix. -/
def borelTransport (s : Kˣ) (u : K) (x : K × K) : K × K :=
  (x.1 + u * (x.2 / s), x.2 / s)

private def upperMatrix (s : Kˣ) (u : K) : Mat := !![(s : K),u;0,1]

/-- The coordinate transport is conjugation by the indicated Borel element. -/
theorem borelProjection_conjugate (s : Kˣ) (u : K) (Y : Mat) :
    borelProjection (upperMatrix s u * Y * upperMatrix s⁻¹ (-u / s)) =
      borelTransport s u (borelProjection Y) := by
  apply Prod.ext <;> simp only [borelProjection, borelTransport, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [upperMatrix, div_eq_mul_inv, mul_comm]
    rw [mul_add,inv_mul_cancel_left₀ s.ne_zero]
    ring
  · simp [upperMatrix, div_eq_mul_inv]

/-- Conjugation by the Borel preserves the full restricted image. -/
theorem quadraticRestrictedOrbit_transport (q : K) (s : Kˣ) (u : K) (x : K × K) :
    borelTransport s u x ∈ quadraticRestrictedOrbit q ↔ x ∈ quadraticRestrictedOrbit q := by
  obtain ⟨a,c⟩ := x
  simp only [borelTransport, quadraticRestrictedOrbit_mem, ne_eq, div_eq_zero_iff, s.ne_zero, or_false]
  by_cases h : c = 0 <;> simp [h]

/-- Nonzero lower coordinates form a single orbit; every boundary point is fixed. -/
theorem borelTransport_exists_iff (x y : K × K) :
    (∃ (s : Kˣ) (u : K), borelTransport s u x = y) ↔
      (x.2 ≠ 0 ∧ y.2 ≠ 0) ∨ x = y := by
  constructor
  · rintro ⟨s,u,rfl⟩
    by_cases h : x.2 = 0
    · right
      exact Prod.ext (by simp [borelTransport,h]) (by simp [borelTransport,h])
    · exact Or.inl ⟨h, div_ne_zero h s.ne_zero⟩
  · rintro (⟨hx,hy⟩ | rfl)
    · let s := Units.mk0 (x.2/y.2) (div_ne_zero hx hy)
      have hs : x.2 / (s : K) = y.2 := by change _ / (_ / _) = _; field_simp
      refine ⟨s, (y.1-x.1)/y.2, Prod.ext ?_ hs⟩
      change x.1 + (y.1-x.1)/y.2 * (x.2/(s : K)) = y.1
      rw [hs, div_mul_cancel₀ _ hy]; ring
    · exact ⟨1,0, by simp [borelTransport]⟩

/-- The restricted adjoint orbit is homogeneous precisely in the nonsquare case. -/
theorem quadraticRestrictedOrbit_transitive_iff (q : K) :
    (∀ x ∈ quadraticRestrictedOrbit q, ∀ y ∈ quadraticRestrictedOrbit q,
      ∃ (s : Kˣ) (u : K), borelTransport s u x = y) ↔ ¬ ∃ a : K, a^2 = q := by
  constructor
  · rintro h ⟨a,ha⟩
    have hx := (quadraticRestrictedOrbit_mem q 0 1).2 (Or.inl one_ne_zero)
    have hy := (quadraticRestrictedOrbit_mem q a 0).2 (Or.inr ha)
    have he := (borelTransport_exists_iff _ _).1 (h _ hx _ hy)
    rcases he with ⟨_,hp⟩ | he
    · exact hp rfl
    · exact one_ne_zero (congrArg Prod.snd he)
  · rintro hn ⟨a,b⟩ hb ⟨c,d⟩ hd
    apply (borelTransport_exists_iff _ _).2
    exact Or.inl ⟨((quadraticRestrictedOrbit_mem q a b).1 hb).resolve_right (fun h => hn ⟨a,h⟩),
      ((quadraticRestrictedOrbit_mem q c d).1 hd).resolve_right (fun h => hn ⟨c,h⟩)⟩

/-- The imaginary trace-zero microblock lies in the complex orbit of its real companion. -/
theorem imaginaryMicroblock_complex_orbit (a : ℝ) (ha : a ≠ 0) :
    IsConj (quadraticCompanion (-(a:ℂ)^2)) (HTGeometry.traceZeroImaginaryMicroblock a) := by
  let t := (a:ℂ)*Complex.I
  have ht : t ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  have hq : t^2 = -(a:ℂ)^2 := by rw [show t = _ from rfl, mul_pow, Complex.I_sq, mul_neg_one]
  apply matrix_intertwiner (B := !![1,t;1,-t])
  · rw [Matrix.det_fin_two_of]
    change 1 * -t - t * 1 ≠ 0
    rw [one_mul, mul_one, sub_eq_add_neg, ← two_mul]
    exact mul_ne_zero (by norm_num) (neg_ne_zero.mpr ht)
  · change _ * quadraticCompanion _ = !![t,0;0,-t] * _
    rw [← hq, quadraticCompanion, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The restricted real companion orbit of a nonzero imaginary microblock is transitive. -/
theorem imaginaryMicroblock_real_restriction (a : ℝ) (ha : a ≠ 0) :
    ∀ x ∈ quadraticRestrictedOrbit (-a^2), ∀ y ∈ quadraticRestrictedOrbit (-a^2),
      ∃ (s : ℝˣ) (u : ℝ), borelTransport s u x = y := by
  apply (quadraticRestrictedOrbit_transitive_iff _).2
  rintro ⟨b,h⟩
  linarith only [sq_nonneg b, sq_pos_of_ne_zero ha, h]

/-- Complexification creates precisely the two boundary points corresponding to the imaginary eigenlines. -/
theorem imaginaryMicroblock_complex_boundary (a : ℝ) (t : ℂ) :
    (t,0) ∈ quadraticRestrictedOrbit (-(a:ℂ)^2) ↔
      t = (a:ℂ)*Complex.I ∨ t = -((a:ℂ)*Complex.I) := by
  have hq : ((a:ℂ)*Complex.I)^2 = -(a:ℂ)^2 := by rw [mul_pow, Complex.I_sq, mul_neg_one]
  rw [quadraticRestrictedOrbit_mem, or_iff_right (not_not_intro rfl), ← hq, sq_eq_sq_iff_eq_or_eq_neg]

#print axioms quadraticCompanion_orbit_square
#print axioms quadraticRestrictedOrbit_mem
#print axioms borelProjection_conjugate
#print axioms quadraticRestrictedOrbit_transport
#print axioms borelTransport_exists_iff
#print axioms quadraticRestrictedOrbit_transitive_iff
#print axioms imaginaryMicroblock_complex_orbit
#print axioms imaginaryMicroblock_real_restriction
#print axioms imaginaryMicroblock_complex_boundary

end GaloisForLFunctions.RepresentationLifting
