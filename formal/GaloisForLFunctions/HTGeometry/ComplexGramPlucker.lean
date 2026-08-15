import Mathlib

/-!
# Hermitian Gram determinant and the Pluecker norm

For a finite family of vectors in a coordinate complex space, the determinant of the Hermitian
Gram matrix equals the sum of the squared moduli of all maximal coordinate minors.  This is the
complex Cauchy–Binet law: the Gram determinant is the squared norm of the top exterior power of the
family, computed in the induced coordinate basis of the exterior power.

Two consequences are recorded.  The Gram determinant is a nonnegative real, and it is nonzero
exactly when the family is linearly independent — equivalently, exactly when the top exterior power
of the family is nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Set Matrix

noncomputable section

variable {κ : Type*} [Fintype κ] [LinearOrder κ]

/-- A maximal coordinate minor of a finite complex feature family. -/
def hermFeatureMinor {n : ℕ} (v : Fin n → κ → ℂ) (s : Set.powersetCard κ n) : ℂ :=
  (Matrix.of fun i j => v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det

/-- The top exterior wedge of a finite complex feature family. -/
def hermFeatureWedge {n : ℕ} (v : Fin n → κ → ℂ) : ⋀[ℂ]^n (κ → ℂ) :=
  exteriorPower.ιMulti ℂ n v

/-- The Hermitian Gram matrix of a finite complex feature family. -/
def hermFeatureGram {n : ℕ} (v : Fin n → κ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ∑ k, star (v i k) * v j k

/-- The squared Pluecker norm: the sum of the squared moduli of all maximal coordinate minors. -/
def hermPluckerNormSq {n : ℕ} (v : Fin n → κ → ℂ) : ℝ :=
  ∑ s : Set.powersetCard κ n, ‖hermFeatureMinor v s‖ ^ 2

/-- The Hermitian pairing functional attached to one feature row. -/
def finiteHermDual (u : κ → ℂ) : Module.Dual ℂ (κ → ℂ) where
  toFun z := ∑ k, star (u k) * z k
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The exterior dual wedge attached to a finite complex feature family. -/
def hermFeatureWedgeDual {n : ℕ} (v : Fin n → κ → ℂ) :
    Module.Dual ℂ (⋀[ℂ]^n (κ → ℂ)) :=
  exteriorPower.pairingDual ℂ (κ → ℂ) n
    (exteriorPower.ιMulti ℂ n fun i => finiteHermDual (v i))

/-- Every standard exterior coordinate of the feature wedge is the matching maximal minor. -/
theorem hermFeatureWedge_coordinate {n : ℕ} (v : Fin n → κ → ℂ)
    (s : Set.powersetCard κ n) :
    ((Pi.basisFun ℂ κ).exteriorPower n).repr (hermFeatureWedge v) s = hermFeatureMinor v s := by
  rw [exteriorPower.basis_repr_apply]
  unfold hermFeatureWedge hermFeatureMinor
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/-- The exterior dual wedge evaluates on a standard exterior basis vector as the conjugate of the
matching minor. -/
theorem hermFeatureWedgeDual_basis_apply {n : ℕ} (v : Fin n → κ → ℂ)
    (s : Set.powersetCard κ n) :
    hermFeatureWedgeDual v ((Pi.basisFun ℂ κ).exteriorPower n s) =
      star (hermFeatureMinor v s) := by
  have hstar : star (hermFeatureMinor v s) =
      ((Matrix.of fun i j => v i (Set.powersetCard.ofFinEmbEquiv.symm s j) :
        Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ)).det := by
    rw [← RingHom.mapMatrix_apply]
    exact RingHom.map_det (starRingEnd ℂ) _
  rw [exteriorPower.basis_apply]
  unfold hermFeatureWedgeDual exteriorPower.ιMulti_family
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose, hstar]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Function.comp_apply,
    Pi.basisFun_apply, finiteHermDual, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (Set.powersetCard.ofFinEmbEquiv.symm s j)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [LinearOrder κ] in
/-- Pairing the exterior dual wedge with the feature wedge gives the Hermitian Gram determinant. -/
theorem hermFeatureWedgeDual_wedge_apply {n : ℕ} (v : Fin n → κ → ℂ) :
    hermFeatureWedgeDual v (hermFeatureWedge v) = (hermFeatureGram v).det := by
  unfold hermFeatureWedgeDual hermFeatureWedge
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose (hermFeatureGram v)]
  congr 1

/-- **Complex Cauchy–Binet.**  The determinant of the Hermitian Gram matrix of a finite complex
feature family is the sum of the squared moduli of its maximal coordinate minors, that is, the
squared Pluecker norm of the top exterior power of the family. -/
theorem det_hermFeatureGram_eq_pluckerNormSq {n : ℕ} (v : Fin n → κ → ℂ) :
    (hermFeatureGram v).det = (hermPluckerNormSq v : ℂ) := by
  classical
  set B := (Pi.basisFun ℂ κ).exteriorPower n with hB
  calc (hermFeatureGram v).det
      = hermFeatureWedgeDual v (hermFeatureWedge v) :=
        (hermFeatureWedgeDual_wedge_apply v).symm
    _ = hermFeatureWedgeDual v (∑ s, B.repr (hermFeatureWedge v) s • B s) := by
        rw [B.sum_repr]
    _ = ∑ s, B.repr (hermFeatureWedge v) s * hermFeatureWedgeDual v (B s) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [map_smul]; rfl
    _ = (hermPluckerNormSq v : ℂ) := by
        unfold hermPluckerNormSq
        push_cast
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hB, hermFeatureWedge_coordinate, hermFeatureWedgeDual_basis_apply]
        exact Complex.mul_conj' _

theorem hermPluckerNormSq_nonneg {n : ℕ} (v : Fin n → κ → ℂ) : 0 ≤ hermPluckerNormSq v :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The feature wedge vanishes exactly when every maximal minor vanishes. -/
theorem hermFeatureWedge_eq_zero_iff_minors {n : ℕ} (v : Fin n → κ → ℂ) :
    hermFeatureWedge v = 0 ↔ ∀ s : Set.powersetCard κ n, hermFeatureMinor v s = 0 := by
  classical
  constructor
  · intro h s
    rw [← hermFeatureWedge_coordinate, h, map_zero]
    rfl
  · intro h
    have hrepr : ((Pi.basisFun ℂ κ).exteriorPower n).repr (hermFeatureWedge v) = 0 := by
      ext s
      simpa [hermFeatureWedge_coordinate] using h s
    have := congrArg ((Pi.basisFun ℂ κ).exteriorPower n).repr.symm hrepr
    simpa using this

omit [LinearOrder κ] in
/-- The Gram matrix acts on a coefficient vector through the linear combination it defines. -/
theorem hermFeatureGram_mulVec_apply {n : ℕ} (v : Fin n → κ → ℂ) (c : Fin n → ℂ) (i : Fin n) :
    ((hermFeatureGram v).mulVec c) i = ∑ k, star (v i k) * ∑ j, c j * v j k := by
  have hrow : ∀ j : Fin n, (∑ k, star (v i k) * v j k) * c j
      = ∑ k, star (v i k) * (c j * v j k) := by
    intro j
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [Matrix.mulVec, dotProduct, hermFeatureGram, Matrix.of_apply, hrow]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

omit [LinearOrder κ] in
/-- The Hermitian energy of a coefficient vector is the squared norm of the combination. -/
theorem sum_conj_mul_hermFeatureGram_mulVec {n : ℕ} (v : Fin n → κ → ℂ) (c : Fin n → ℂ) :
    ∑ i, star (c i) * ((hermFeatureGram v).mulVec c) i =
      ∑ k, star (∑ j, c j * v j k) * ∑ j, c j * v j k := by
  have hexp : ∀ i : Fin n, star (c i) * ((hermFeatureGram v).mulVec c) i
      = ∑ k, star (c i) * (star (v i k) * ∑ j, c j * v j k) := by
    intro i
    rw [hermFeatureGram_mulVec_apply, Finset.mul_sum]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hstar : star (∑ j, c j * v j k) = ∑ j, star (c j) * star (v j k) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun j _ => star_mul' _ _
  rw [hstar, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [LinearOrder κ] in
/-- **The Gram determinant detects the kernel.**  The Hermitian Gram determinant of a finite
complex feature family is nonzero exactly when the family is linearly independent. -/
theorem det_hermFeatureGram_ne_zero_iff {n : ℕ} (v : Fin n → κ → ℂ) :
    (hermFeatureGram v).det ≠ 0 ↔ LinearIndependent ℂ v := by
  classical
  constructor
  · intro hdet
    refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    by_contra hne
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
    refine hdet (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, fun h => hi₀ (by rw [h]; rfl), ?_⟩)
    funext i
    rw [hermFeatureGram_mulVec_apply]
    have hzero : ∀ k, (∑ j, c j * v j k) = 0 := by
      intro k
      have := congrArg (fun f : κ → ℂ => f k) hc
      simpa [Finset.sum_apply, mul_comm] using this
    simp [hzero]
  · intro hind hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hkey : ∑ k, star (∑ j, c j * v j k) * ∑ j, c j * v j k = 0 := by
      rw [← sum_conj_mul_hermFeatureGram_mulVec]
      simp [hc]
    have hnorm : ∑ k, (‖∑ j, c j * v j k‖ : ℝ) ^ 2 = 0 := by
      have hcast : (∑ k, ((‖∑ j, c j * v j k‖ : ℝ) ^ 2 : ℂ)) = 0 := by
        rw [← hkey]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm, show star (∑ j, c j * v j k) = (starRingEnd ℂ) (∑ j, c j * v j k) from rfl,
          Complex.mul_conj']
      exact_mod_cast hcast
    have hall : ∀ k, (∑ j, c j * v j k) = 0 := by
      intro k
      have hterm : (‖∑ j, c j * v j k‖ : ℝ) ^ 2 = 0 := by
        by_contra hcon
        have hposk : 0 < (‖∑ j, c j * v j k‖ : ℝ) ^ 2 :=
          lt_of_le_of_ne (by positivity) (Ne.symm hcon)
        have hsum : 0 < ∑ k, (‖∑ j, c j * v j k‖ : ℝ) ^ 2 :=
          Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ k, hposk⟩
        exact absurd hnorm hsum.ne'
      have hz : ‖∑ j, c j * v j k‖ = 0 := by
        nlinarith [norm_nonneg (∑ j, c j * v j k)]
      exact norm_eq_zero.1 hz
    have hcomb : ∑ j, c j • v j = 0 := by
      funext k
      simpa [Finset.sum_apply, mul_comm] using hall k
    exact hc0 (funext fun i => Fintype.linearIndependent_iff.1 hind c hcomb i)

/-- The top exterior power of a finite complex feature family vanishes exactly when the family is
linearly dependent: the Pluecker vector detects the kernel. -/
theorem hermFeatureWedge_eq_zero_iff {n : ℕ} (v : Fin n → κ → ℂ) :
    hermFeatureWedge v = 0 ↔ ¬ LinearIndependent ℂ v := by
  rw [hermFeatureWedge_eq_zero_iff_minors, ← det_hermFeatureGram_ne_zero_iff, not_not,
    det_hermFeatureGram_eq_pluckerNormSq]
  constructor
  · intro h
    have hz : hermPluckerNormSq v = 0 := by simp [hermPluckerNormSq, h]
    simp [hz]
  · intro h s
    have hz : hermPluckerNormSq v = 0 := by exact_mod_cast h
    have hterm : ‖hermFeatureMinor v s‖ ^ 2 = 0 := by
      by_contra hcon
      have hpos : 0 < ‖hermFeatureMinor v s‖ ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hcon)
      have hsum : 0 < hermPluckerNormSq v :=
        Finset.sum_pos' (fun _ _ => by positivity) ⟨s, Finset.mem_univ s, hpos⟩
      exact absurd hz hsum.ne'
    have hz0 : ‖hermFeatureMinor v s‖ = 0 := by
      nlinarith [norm_nonneg (hermFeatureMinor v s)]
    exact norm_eq_zero.1 hz0

end

end GaloisForLFunctions.HTGeometry
