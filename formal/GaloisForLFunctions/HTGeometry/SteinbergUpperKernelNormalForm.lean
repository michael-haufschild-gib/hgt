import GaloisForLFunctions.HTGeometry.SteinbergUpperTetrahedronNormalForm

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

theorem steinbergUpperTetrahedron_mem_KTwo_iff {i j k l : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (a b c d e f : R) :
    steinbergUpperTetrahedron hij hjk hik hil hjl hkl a b c d e f ∈ KTwo R n
      ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  constructor
  · intro h
    rw [mem_KTwo_iff] at h
    have hmat := congrArg (fun u : (Matrix n n R)ˣ => (u : Matrix n n R)) h
    simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn, map_mul,
      steinbergToGL_x, Units.val_mul, elemUnit_val, Units.val_one] at hmat
    repeat' rw [← mul_assoc] at hmat
    have ha := congrFun (congrFun hmat i) j
    have hbplus := congrFun (congrFun hmat i) k
    have hc := congrFun (congrFun hmat j) k
    have hdplus := congrFun (congrFun hmat i) l
    have heplus := congrFun (congrFun hmat j) l
    have hf := congrFun (congrFun hmat k) l
    rw [transvection_upperTetrahedron_apply_ij hij hjk hik hil hjl hkl] at ha
    rw [transvection_upperTetrahedron_apply_ik hij hjk hik hil hjl hkl] at hbplus
    rw [transvection_upperTetrahedron_apply_jk hij hjk hik hil hjl hkl] at hc
    rw [transvection_upperTetrahedron_apply_il hij hjk hik hil hjl hkl] at hdplus
    rw [transvection_upperTetrahedron_apply_jl hij hjk hik hil hjl hkl] at heplus
    rw [transvection_upperTetrahedron_apply_kl hij hjk hik hil hjl hkl] at hf
    rw [Matrix.one_apply, if_neg hij] at ha
    rw [Matrix.one_apply, if_neg hjk] at hc
    rw [Matrix.one_apply, if_neg hkl] at hf
    rw [Matrix.one_apply, if_neg hik] at hbplus
    rw [Matrix.one_apply, if_neg hjl] at heplus
    rw [Matrix.one_apply, if_neg hil] at hdplus
    have hb : b = 0 := by simpa [ha, hc] using hbplus
    have he : e = 0 := by simpa [hc, hf] using heplus
    have hd : d = 0 := by simpa [ha, hb, hc, he, hf] using hdplus
    exact ⟨ha, hb, hc, hd, he, hf⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [steinbergUpperTetrahedron, steinbergUpperTriangle, steinbergUpperColumn,
      steinbergX_zero, mul_one]
    exact Subgroup.one_mem _

end GaloisForLFunctions.HTGeometry
