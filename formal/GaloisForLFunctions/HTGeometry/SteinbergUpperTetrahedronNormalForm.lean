import GaloisForLFunctions.HTGeometry.SteinbergUpperTriangleNormalForm

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*}

def steinbergUpperColumn {i j k l : n} (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (d e f : R) : SteinbergGroup R n :=
  steinbergX hil d * steinbergX hjl e * steinbergX hkl f

theorem steinbergUpperColumn_mul {i j k l : n} (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (d e f d' e' f' : R) :
    steinbergUpperColumn hil hjl hkl d e f * steinbergUpperColumn hil hjl hkl d' e' f'
      = steinbergUpperColumn hil hjl hkl (d + d') (e + e') (f + f') := by
  have hcomm_id' : steinbergX hil d' * steinbergX hjl e
      = steinbergX hjl e * steinbergX hil d' :=
    steinbergX_commute_col hil hjl d' e
  have hcomm_id'' : steinbergX hil d' * steinbergX hkl f
      = steinbergX hkl f * steinbergX hil d' :=
    steinbergX_commute_col hil hkl d' f
  have hcomm_je' : steinbergX hjl e' * steinbergX hkl f
      = steinbergX hkl f * steinbergX hjl e' :=
    steinbergX_commute_col hjl hkl e' f
  rw [steinbergUpperColumn, steinbergUpperColumn, steinbergUpperColumn]
  calc steinbergX hil d * steinbergX hjl e * steinbergX hkl f
        * (steinbergX hil d' * steinbergX hjl e' * steinbergX hkl f')
      = steinbergX hil d * steinbergX hjl e * steinbergX hil d'
        * steinbergX hkl f * steinbergX hjl e' * steinbergX hkl f' := by
          calc
            _ = steinbergX hil d * steinbergX hjl e * steinbergX hkl f
              * steinbergX hil d' * steinbergX hjl e' * steinbergX hkl f' := by group
            _ = steinbergX hil d * steinbergX hjl e * steinbergX hil d'
              * steinbergX hkl f * steinbergX hjl e' * steinbergX hkl f' := by
                calc
                  _ = steinbergX hil d * steinbergX hjl e * (steinbergX hkl f * steinbergX hil d')
                    * steinbergX hjl e' * steinbergX hkl f' := by group
                  _ = _ := by rw [hcomm_id''.symm]; group
    _ = steinbergX hil d * steinbergX hil d' * steinbergX hjl e
        * steinbergX hkl f * steinbergX hjl e' * steinbergX hkl f' := by
          calc
            _ = steinbergX hil d * (steinbergX hjl e * steinbergX hil d')
              * steinbergX hkl f * steinbergX hjl e' * steinbergX hkl f' := by group
            _ = _ := by rw [hcomm_id'.symm]; group
    _ = steinbergX hil (d + d') * steinbergX hjl e * steinbergX hkl f
        * steinbergX hjl e' * steinbergX hkl f' := by rw [steinbergX_mul]
    _ = steinbergX hil (d + d') * steinbergX hjl e * steinbergX hjl e'
        * steinbergX hkl f * steinbergX hkl f' := by
          calc
            _ = steinbergX hil (d + d') * steinbergX hjl e
              * (steinbergX hkl f * steinbergX hjl e') * steinbergX hkl f' := by group
            _ = _ := by rw [hcomm_je'.symm]; group
    _ = steinbergX hil (d + d') * steinbergX hjl (e + e') * steinbergX hkl (f + f') := by
          calc
            _ = steinbergX hil (d + d') * (steinbergX hjl e * steinbergX hjl e')
              * (steinbergX hkl f * steinbergX hkl f') := by group
            _ = _ := by rw [steinbergX_mul, steinbergX_mul]

theorem steinbergUpperColumn_inv {i j k l : n} (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (d e f : R) :
    (steinbergUpperColumn hil hjl hkl d e f)⁻¹ = steinbergUpperColumn hil hjl hkl (-d) (-e) (-f) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [steinbergUpperColumn_mul]
  have hd : -d + d = (0 : R) := neg_add_cancel d
  have he : -e + e = (0 : R) := neg_add_cancel e
  have hf : -f + f = (0 : R) := neg_add_cancel f
  rw [hd, he, hf, steinbergUpperColumn, steinbergX_zero, steinbergX_zero, steinbergX_zero]
  simp

theorem steinbergX_ij_conj_upperColumn {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a d e f : R) :
    steinbergX hij a * steinbergUpperColumn hil hjl hkl d e f * (steinbergX hij a)⁻¹
      = steinbergUpperColumn hil hjl hkl (d + a * e) e f := by
  have hfirst : steinbergX hij a * steinbergX hil d * (steinbergX hij a)⁻¹
      = steinbergX hil d := by
    have hcomm := steinbergX_commute_row hij hil a d
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hmid : steinbergX hij a * steinbergX hjl e * (steinbergX hij a)⁻¹
      = steinbergX hil (a * e) * steinbergX hjl e :=
    steinbergX_conj_chain hij hjl hil a e
  have hlast : steinbergX hij a * steinbergX hkl f * (steinbergX hij a)⁻¹
      = steinbergX hkl f := by
    have hcomm := steinbergX_commute hij hkl hjk hil a f
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [steinbergUpperColumn, steinbergUpperColumn]
  calc steinbergX hij a * (steinbergX hil d * steinbergX hjl e * steinbergX hkl f)
        * (steinbergX hij a)⁻¹
      = (steinbergX hij a * steinbergX hil d * (steinbergX hij a)⁻¹)
        * (steinbergX hij a * steinbergX hjl e * (steinbergX hij a)⁻¹)
        * (steinbergX hij a * steinbergX hkl f * (steinbergX hij a)⁻¹) := by group
    _ = steinbergX hil d * (steinbergX hil (a * e) * steinbergX hjl e)
        * steinbergX hkl f := by rw [hfirst, hmid, hlast]
    _ = steinbergX hil (d + a * e) * steinbergX hjl e * steinbergX hkl f := by
      rw [← mul_assoc, steinbergX_mul]

theorem steinbergX_ik_conj_upperColumn {i j k l : n} (_hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (b d e f : R) :
    steinbergX hik b * steinbergUpperColumn hil hjl hkl d e f * (steinbergX hik b)⁻¹
      = steinbergUpperColumn hil hjl hkl (d + b * f) e f := by
  have hfirst : steinbergX hik b * steinbergX hil d * (steinbergX hik b)⁻¹
      = steinbergX hil d := by
    have hcomm := steinbergX_commute_row hik hil b d
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hmid : steinbergX hik b * steinbergX hjl e * (steinbergX hik b)⁻¹
      = steinbergX hjl e := by
    have hcomm := steinbergX_commute hik hjl (Ne.symm hjk) hil b e
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hlast : steinbergX hik b * steinbergX hkl f * (steinbergX hik b)⁻¹
      = steinbergX hil (b * f) * steinbergX hkl f :=
    steinbergX_conj_chain hik hkl hil b f
  have hcol : steinbergX hjl e * steinbergX hil (b * f)
      = steinbergX hil (b * f) * steinbergX hjl e :=
    (steinbergX_commute_col hil hjl (b * f) e).symm
  rw [steinbergUpperColumn, steinbergUpperColumn]
  calc steinbergX hik b * (steinbergX hil d * steinbergX hjl e * steinbergX hkl f)
        * (steinbergX hik b)⁻¹
      = (steinbergX hik b * steinbergX hil d * (steinbergX hik b)⁻¹)
        * (steinbergX hik b * steinbergX hjl e * (steinbergX hik b)⁻¹)
        * (steinbergX hik b * steinbergX hkl f * (steinbergX hik b)⁻¹) := by group
    _ = steinbergX hil d * steinbergX hjl e
        * (steinbergX hil (b * f) * steinbergX hkl f) := by rw [hfirst, hmid, hlast]
    _ = steinbergX hil d * steinbergX hil (b * f) * steinbergX hjl e * steinbergX hkl f := by
      calc
        _ = steinbergX hil d * (steinbergX hjl e * steinbergX hil (b * f))
          * steinbergX hkl f := by group
        _ = _ := by rw [hcol]; group
    _ = steinbergX hil (d + b * f) * steinbergX hjl e * steinbergX hkl f := by
      rw [steinbergX_mul]

theorem steinbergX_jk_conj_upperColumn {i j k l : n} (_hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (c d e f : R) :
    steinbergX hjk c * steinbergUpperColumn hil hjl hkl d e f * (steinbergX hjk c)⁻¹
      = steinbergUpperColumn hil hjl hkl d (e + c * f) f := by
  have hfirst : steinbergX hjk c * steinbergX hil d * (steinbergX hjk c)⁻¹
      = steinbergX hil d := by
    have hcomm := steinbergX_commute hjk hil (Ne.symm hik) hjl c d
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hmid : steinbergX hjk c * steinbergX hjl e * (steinbergX hjk c)⁻¹
      = steinbergX hjl e := by
    have hcomm := steinbergX_commute_row hjk hjl c e
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hlast : steinbergX hjk c * steinbergX hkl f * (steinbergX hjk c)⁻¹
      = steinbergX hjl (c * f) * steinbergX hkl f :=
    steinbergX_conj_chain hjk hkl hjl c f
  rw [steinbergUpperColumn, steinbergUpperColumn]
  calc steinbergX hjk c * (steinbergX hil d * steinbergX hjl e * steinbergX hkl f)
        * (steinbergX hjk c)⁻¹
      = (steinbergX hjk c * steinbergX hil d * (steinbergX hjk c)⁻¹)
        * (steinbergX hjk c * steinbergX hjl e * (steinbergX hjk c)⁻¹)
        * (steinbergX hjk c * steinbergX hkl f * (steinbergX hjk c)⁻¹) := by group
    _ = steinbergX hil d * steinbergX hjl e
        * (steinbergX hjl (c * f) * steinbergX hkl f) := by rw [hfirst, hmid, hlast]
    _ = steinbergX hil d * steinbergX hjl (e + c * f) * steinbergX hkl f := by
      calc
        _ = steinbergX hil d * (steinbergX hjl e * steinbergX hjl (c * f))
          * steinbergX hkl f := by group
        _ = _ := by rw [steinbergX_mul]

def steinbergUpperTetrahedron {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) : SteinbergGroup R n :=
  steinbergUpperTriangle hij hjk hik a b c * steinbergUpperColumn hil hjl hkl d e f

theorem steinbergUpperTriangle_conj_upperColumn {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    steinbergUpperTriangle hij hjk hik a b c * steinbergUpperColumn hil hjl hkl d e f
      * (steinbergUpperTriangle hij hjk hik a b c)⁻¹
      = steinbergUpperColumn hil hjl hkl (d + a * e + (b + a * c) * f) (e + c * f) f := by
  rw [steinbergUpperTriangle]
  calc (steinbergX hij a * steinbergX hik b * steinbergX hjk c)
        * steinbergUpperColumn hil hjl hkl d e f
        * (steinbergX hij a * steinbergX hik b * steinbergX hjk c)⁻¹
      = steinbergX hij a
        * (steinbergX hik b
          * (steinbergX hjk c * steinbergUpperColumn hil hjl hkl d e f * (steinbergX hjk c)⁻¹)
          * (steinbergX hik b)⁻¹)
        * (steinbergX hij a)⁻¹ := by group
    _ = steinbergX hij a
        * (steinbergX hik b
          * steinbergUpperColumn hil hjl hkl d (e + c * f) f
          * (steinbergX hik b)⁻¹)
        * (steinbergX hij a)⁻¹ := by
          rw [steinbergX_jk_conj_upperColumn hij hjk hik hil hjl hkl]
    _ = steinbergX hij a
        * steinbergUpperColumn hil hjl hkl (d + b * f) (e + c * f) f
        * (steinbergX hij a)⁻¹ := by
          rw [steinbergX_ik_conj_upperColumn hij hjk hik hil hjl hkl]
    _ = steinbergUpperColumn hil hjl hkl ((d + b * f) + a * (e + c * f)) (e + c * f) f := by
          rw [steinbergX_ij_conj_upperColumn hij hjk hil hjl hkl]
    _ = steinbergUpperColumn hil hjl hkl (d + a * e + (b + a * c) * f) (e + c * f) f := by
          congr 1
          ring

theorem steinbergUpperTriangle_inv_conj_upperColumn {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (steinbergUpperTriangle hij hjk hik a b c)⁻¹ * steinbergUpperColumn hil hjl hkl d e f
      * steinbergUpperTriangle hij hjk hik a b c
      = steinbergUpperColumn hil hjl hkl (d - a * e - b * f) (e - c * f) f := by
  have hforward := steinbergUpperTriangle_conj_upperColumn hij hjk hik hil hjl hkl a b c
    (d - a * e - b * f) (e - c * f) f
  have hforward' : steinbergUpperTriangle hij hjk hik a b c
      * steinbergUpperColumn hil hjl hkl (d - a * e - b * f) (e - c * f) f
      * (steinbergUpperTriangle hij hjk hik a b c)⁻¹
      = steinbergUpperColumn hil hjl hkl d e f := by
    rw [hforward]
    congr 1 <;> ring
  rw [← hforward']
  group

theorem steinbergUpperTetrahedron_mul {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f a' b' c' d' e' f' : R) :
    steinbergUpperTetrahedron hij hjk hik hil hjl hkl a b c d e f
      * steinbergUpperTetrahedron hij hjk hik hil hjl hkl a' b' c' d' e' f'
      = steinbergUpperTetrahedron hij hjk hik hil hjl hkl
          (a + a') (b + b' - a' * c) (c + c')
          (d + d' - a' * e - b' * f) (e + e' - c' * f) (f + f') := by
  rw [steinbergUpperTetrahedron, steinbergUpperTetrahedron, steinbergUpperTetrahedron]
  calc (steinbergUpperTriangle hij hjk hik a b c * steinbergUpperColumn hil hjl hkl d e f)
        * (steinbergUpperTriangle hij hjk hik a' b' c' * steinbergUpperColumn hil hjl hkl d' e' f')
      = (steinbergUpperTriangle hij hjk hik a b c * steinbergUpperTriangle hij hjk hik a' b' c')
        * ((steinbergUpperTriangle hij hjk hik a' b' c')⁻¹
          * steinbergUpperColumn hil hjl hkl d e f * steinbergUpperTriangle hij hjk hik a' b' c')
        * steinbergUpperColumn hil hjl hkl d' e' f' := by group
    _ = steinbergUpperTriangle hij hjk hik (a + a') (b + b' - a' * c) (c + c')
        * (steinbergUpperColumn hil hjl hkl (d - a' * e - b' * f) (e - c' * f) f
          * steinbergUpperColumn hil hjl hkl d' e' f') := by
          rw [steinbergUpperTriangle_mul, steinbergUpperTriangle_inv_conj_upperColumn]
          group
    _ = steinbergUpperTriangle hij hjk hik (a + a') (b + b' - a' * c) (c + c')
        * steinbergUpperColumn hil hjl hkl
            ((d - a' * e - b' * f) + d') ((e - c' * f) + e') (f + f') := by
          rw [steinbergUpperColumn_mul]
    _ = steinbergUpperTriangle hij hjk hik (a + a') (b + b' - a' * c) (c + c')
        * steinbergUpperColumn hil hjl hkl
            (d + d' - a' * e - b' * f) (e + e' - c' * f) (f + f') := by
          congr 1
          congr 1 <;> ring

theorem steinbergUpperTetrahedron_inv {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (steinbergUpperTetrahedron hij hjk hik hil hjl hkl a b c d e f)⁻¹
      = steinbergUpperTetrahedron hij hjk hik hil hjl hkl
          (-a) (-b - a * c) (-c)
          (-d - a * e - (b + a * c) * f) (-e - c * f) (-f) := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [steinbergUpperTetrahedron_mul]
  have ha : -a + a = (0 : R) := neg_add_cancel a
  have hb : (-b - a * c) + b - a * -c = (0 : R) := by ring
  have hc : -c + c = (0 : R) := neg_add_cancel c
  have hd : (-d - a * e - (b + a * c) * f) + d - a * (-e - c * f) - b * -f = (0 : R) := by ring
  have he : (-e - c * f) + e - c * -f = (0 : R) := by ring
  have hf : -f + f = (0 : R) := neg_add_cancel f
  rw [ha, hb, hc, hd, he, hf, steinbergUpperTetrahedron, steinbergUpperTriangle,
    steinbergUpperColumn, steinbergX_zero, steinbergX_zero, steinbergX_zero,
    steinbergX_zero, steinbergX_zero, steinbergX_zero]
  simp

def steinbergUpperTetrahedronSubgroup {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) : Subgroup (SteinbergGroup R n) where
  carrier := {x | ∃ (a b c d e f : R), x = steinbergUpperTetrahedron hij hjk hik hil hjl hkl a b c d e f}
  one_mem' := ⟨0, 0, 0, 0, 0, 0, by
    simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
      steinbergX_zero, mul_one]⟩
  mul_mem' := by
    rintro x y ⟨a, b, c, d, e, f, rfl⟩ ⟨a', b', c', d', e', f', rfl⟩
    exact ⟨a + a', b + b' - a' * c, c + c', d + d' - a' * e - b' * f,
      e + e' - c' * f, f + f', steinbergUpperTetrahedron_mul hij hjk hik hil hjl hkl _ _ _ _ _ _ _ _ _ _ _ _⟩
  inv_mem' := by
    rintro x ⟨a, b, c, d, e, f, rfl⟩
    exact ⟨-a, -b - a * c, -c, -d - a * e - (b + a * c) * f, -e - c * f, -f,
      steinbergUpperTetrahedron_inv hij hjk hik hil hjl hkl a b c d e f⟩

def steinbergUpperTetrahedronGens {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) : Set (SteinbergGroup R n) :=
  {x | (∃ a : R, x = steinbergX hij a) ∨ (∃ b : R, x = steinbergX hik b)
    ∨ (∃ c : R, x = steinbergX hjk c) ∨ (∃ d : R, x = steinbergX hil d)
    ∨ (∃ e : R, x = steinbergX hjl e) ∨ ∃ f : R, x = steinbergX hkl f}

theorem steinbergUpperTetrahedronSubgroup_eq_closure {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) :
    steinbergUpperTetrahedronSubgroup (R := R) hij hjk hik hil hjl hkl
      = Subgroup.closure (steinbergUpperTetrahedronGens (R := R) hij hjk hik hil hjl hkl) := by
  apply le_antisymm
  · rintro x ⟨a, b, c, d, e, f, rfl⟩
    rw [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn]
    let H := Subgroup.closure (steinbergUpperTetrahedronGens (R := R) hij hjk hik hil hjl hkl)
    have ha : steinbergX hij a ∈ H := Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
    have hb : steinbergX hik b ∈ H := Subgroup.subset_closure (Or.inr (Or.inl ⟨b, rfl⟩))
    have hc : steinbergX hjk c ∈ H := Subgroup.subset_closure (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩)))
    have hd : steinbergX hil d ∈ H := Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩))))
    have he : steinbergX hjl e ∈ H :=
      Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩)))))
    have hf : steinbergX hkl f ∈ H :=
      Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, rfl⟩)))))
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) hc) (H.mul_mem (H.mul_mem hd he) hf)
  · apply (Subgroup.closure_le _).2
    rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩ | ⟨d, rfl⟩ | ⟨e, rfl⟩ | ⟨f, rfl⟩)
    · exact ⟨a, 0, 0, 0, 0, 0, by
        simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
          steinbergX_zero, mul_one]⟩
    · exact ⟨0, b, 0, 0, 0, 0, by
        simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
          steinbergX_zero, one_mul, mul_one]⟩
    · exact ⟨0, 0, c, 0, 0, 0, by
        simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
          steinbergX_zero, one_mul, mul_one]⟩
    · exact ⟨0, 0, 0, d, 0, 0, by
        simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
          steinbergX_zero, one_mul, mul_one]⟩
    · exact ⟨0, 0, 0, 0, e, 0, by
        simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
          steinbergX_zero, one_mul, mul_one]⟩
    · exact ⟨0, 0, 0, 0, 0, f, by
        simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
          steinbergX_zero, one_mul]⟩

section MatrixNormalForm

open Matrix

variable [DecidableEq n] [Fintype n]

theorem transvection_upperTetrahedron {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (_hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f
      = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
        + Matrix.single i l (d + a * e + (b + a * c) * f)
        + Matrix.single j l (e + c * f) + Matrix.single k l f := by
  have hAil : (Matrix.single i j a : Matrix n n R) * Matrix.single i l d = 0 := by
    simp [Ne.symm hij]
  have hBil : (Matrix.single i k (b + a * c) : Matrix n n R) * Matrix.single i l d = 0 := by
    simp [Ne.symm hik]
  have hCil : (Matrix.single j k c : Matrix n n R) * Matrix.single i l d = 0 := by
    simp [Ne.symm hik]
  have hAje : (Matrix.single i j a : Matrix n n R) * Matrix.single j l e
      = Matrix.single i l (a * e) := by simp
  have hBje : (Matrix.single i k (b + a * c) : Matrix n n R) * Matrix.single j l e = 0 := by
    simp [Ne.symm hjk]
  have hCje : (Matrix.single j k c : Matrix n n R) * Matrix.single j l e = 0 := by
    simp [Ne.symm hjk]
  have hDje : (Matrix.single i l d : Matrix n n R) * Matrix.single j l e = 0 := by
    simp [Ne.symm hjl]
  have hAkl : (Matrix.single i j a : Matrix n n R) * Matrix.single k l f = 0 := by
    simp [hjk]
  have hBkl : (Matrix.single i k (b + a * c) : Matrix n n R) * Matrix.single k l f
      = Matrix.single i l ((b + a * c) * f) := by simp
  have hCkl : (Matrix.single j k c : Matrix n n R) * Matrix.single k l f
      = Matrix.single j l (c * f) := by simp
  have hDkl : (Matrix.single i l (d + a * e) : Matrix n n R) * Matrix.single k l f = 0 := by
    simp [Ne.symm hkl]
  have hEkl : (Matrix.single j l e : Matrix n n R) * Matrix.single k l f = 0 := by
    simp [Ne.symm hkl]
  have hstep1 :
      (1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c)
        * Matrix.transvection i l d
        = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l d := by
    rw [show Matrix.transvection i l d = 1 + Matrix.single i l d from rfl]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      hAil, hBil, hCil, add_zero]
  have hstep2 :
      (1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l d) * Matrix.transvection j l e
        = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l (d + a * e) + Matrix.single j l e := by
    rw [show Matrix.transvection j l e = 1 + Matrix.single j l e from rfl]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      hAje, hBje, hCje, hDje, add_zero]
    calc
      _ = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
        + (Matrix.single i l d + Matrix.single i l (a * e)) + Matrix.single j l e := by abel
      _ = _ := by rw [← Matrix.single_add]
  have hstep3 :
      (1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l (d + a * e) + Matrix.single j l e) * Matrix.transvection k l f
        = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l (d + a * e + (b + a * c) * f)
          + Matrix.single j l (e + c * f) + Matrix.single k l f := by
    rw [show Matrix.transvection k l f = 1 + Matrix.single k l f from rfl]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      hAkl, hBkl, hCkl, hDkl, hEkl, add_zero]
    calc
      _ = 1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
        + (Matrix.single i l (d + a * e) + Matrix.single i l ((b + a * c) * f))
        + (Matrix.single j l e + Matrix.single j l (c * f)) + Matrix.single k l f := by abel
      _ = _ := by rw [← Matrix.single_add, ← Matrix.single_add]
  rw [transvection_upperTriangle hij hjk hik]
  calc (1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c)
        * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f
      = (1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l d) * Matrix.transvection j l e * Matrix.transvection k l f := by rw [hstep1]
    _ = (1 + Matrix.single i j a + Matrix.single i k (b + a * c) + Matrix.single j k c
          + Matrix.single i l (d + a * e) + Matrix.single j l e) * Matrix.transvection k l f := by rw [hstep2]
    _ = _ := hstep3

theorem transvection_upperTetrahedron_apply_ij {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f) i j = a := by
  rw [transvection_upperTetrahedron hij hjk hik hil hjl hkl]
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hli : l ≠ i := Ne.symm hil
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  simp_all

theorem transvection_upperTetrahedron_apply_ik {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f) i k = b + a * c := by
  rw [transvection_upperTetrahedron hij hjk hik hil hjl hkl]
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hli : l ≠ i := Ne.symm hil
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  simp_all

theorem transvection_upperTetrahedron_apply_jk {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f) j k = c := by
  rw [transvection_upperTetrahedron hij hjk hik hil hjl hkl]
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hli : l ≠ i := Ne.symm hil
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  simp_all

theorem transvection_upperTetrahedron_apply_il {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f) i l
      = d + a * e + (b + a * c) * f := by
  rw [transvection_upperTetrahedron hij hjk hik hil hjl hkl]
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hli : l ≠ i := Ne.symm hil
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  simp_all

theorem transvection_upperTetrahedron_apply_jl {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f) j l = e + c * f := by
  rw [transvection_upperTetrahedron hij hjk hik hil hjl hkl]
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hli : l ≠ i := Ne.symm hil
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  simp_all

theorem transvection_upperTetrahedron_apply_kl {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    (Matrix.transvection i j a * Matrix.transvection i k b * Matrix.transvection j k c
      * Matrix.transvection i l d * Matrix.transvection j l e * Matrix.transvection k l f) k l = f := by
  rw [transvection_upperTetrahedron hij hjk hik hil hjl hkl]
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  have hli : l ≠ i := Ne.symm hil
  have hlj : l ≠ j := Ne.symm hjl
  have hlk : l ≠ k := Ne.symm hkl
  simp_all

theorem steinbergUpperTetrahedron_injective {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    {a b c d e f a' b' c' d' e' f' : R}
    (h : steinbergUpperTetrahedron hij hjk hik hil hjl hkl a b c d e f
      = steinbergUpperTetrahedron hij hjk hik hil hjl hkl a' b' c' d' e' f') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  have himage := congrArg
    (fun x : SteinbergGroup R n => ((steinbergToGL x : (Matrix n n R)ˣ) : Matrix n n R)) h
  simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn, map_mul,
    steinbergToGL_x, Units.val_mul, elemUnit_val] at himage
  repeat' rw [← mul_assoc] at himage
  have ha := congrFun (congrFun himage i) j
  have hbplus := congrFun (congrFun himage i) k
  have hc := congrFun (congrFun himage j) k
  have hdplus := congrFun (congrFun himage i) l
  have heplus := congrFun (congrFun himage j) l
  have hf := congrFun (congrFun himage k) l
  rw [transvection_upperTetrahedron_apply_ij hij hjk hik hil hjl hkl,
    transvection_upperTetrahedron_apply_ij hij hjk hik hil hjl hkl] at ha
  rw [transvection_upperTetrahedron_apply_ik hij hjk hik hil hjl hkl,
    transvection_upperTetrahedron_apply_ik hij hjk hik hil hjl hkl] at hbplus
  rw [transvection_upperTetrahedron_apply_jk hij hjk hik hil hjl hkl,
    transvection_upperTetrahedron_apply_jk hij hjk hik hil hjl hkl] at hc
  rw [transvection_upperTetrahedron_apply_il hij hjk hik hil hjl hkl,
    transvection_upperTetrahedron_apply_il hij hjk hik hil hjl hkl] at hdplus
  rw [transvection_upperTetrahedron_apply_jl hij hjk hik hil hjl hkl,
    transvection_upperTetrahedron_apply_jl hij hjk hik hil hjl hkl] at heplus
  rw [transvection_upperTetrahedron_apply_kl hij hjk hik hil hjl hkl,
    transvection_upperTetrahedron_apply_kl hij hjk hik hil hjl hkl] at hf
  have hb : b = b' := by
    rw [ha, hc] at hbplus
    exact add_right_cancel hbplus
  have he : e = e' := by
    rw [hc, hf] at heplus
    exact add_right_cancel heplus
  have hd : d = d' := by
    rw [ha, hb, hc, he, hf] at hdplus
    apply add_right_cancel
    simpa only [add_assoc] using hdplus
  exact ⟨ha, hb, hc, hd, he, hf⟩

end MatrixNormalForm

end GaloisForLFunctions.HTGeometry
