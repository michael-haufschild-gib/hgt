import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import GaloisForLFunctions.HTGeometry.StarMultiplicativeDefectChain

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Algebraic right Hilbert-module operations, with the standard convention that the
`B`-valued inner product is conjugate-linear in its first entry.  Positivity and completion are
separate from these identities; this structure is the exact algebraic interface used by KSGNS. -/
structure RightInnerModuleData (B E : Type*) [Ring B] [StarRing B] [Module ℂ B]
    [AddCommGroup E] [Module ℂ E] where
  inner : E → E → B
  rmul : E → B → E
  inner_add_right : ∀ x y z, inner x (y + z) = inner x y + inner x z
  inner_smul_right : ∀ (c : ℂ) x y, inner x (c • y) = c • inner x y
  inner_rmul_right : ∀ x y b, inner x (rmul y b) = inner x y * b
  star_inner : ∀ x y, star (inner x y) = inner y x
  rmul_one : ∀ x, rmul x 1 = x
  rmul_mul : ∀ x b c, rmul (rmul x b) c = rmul x (b * c)
  rmul_add_left : ∀ x y b, rmul (x + y) b = rmul x b + rmul y b
  rmul_add_right : ∀ x b c, rmul x (b + c) = rmul x b + rmul x c
  rmul_smul : ∀ (c : ℂ) x b, rmul (c • x) b = c • rmul x b

namespace RightInnerModuleData

variable {B E : Type*} [Ring B] [StarRing B] [Module ℂ B]
    [AddCommGroup E] [Module ℂ E]
    (M : RightInnerModuleData B E)

theorem inner_add_left (x y z : E) :
    M.inner (x + y) z = M.inner x z + M.inner y z := by
  rw [← star_star (M.inner (x + y) z), M.star_inner, M.inner_add_right, star_add,
    M.star_inner, M.star_inner]

theorem inner_sub_right (x y z : E) :
    M.inner x (y - z) = M.inner x y - M.inner x z := by
  rw [sub_eq_add_neg, M.inner_add_right]
  have hzero : M.inner x 0 = 0 := by
    have h := M.inner_add_right x 0 0
    have hz : 0 = M.inner x 0 :=
      add_left_cancel (by simpa only [add_zero] using h)
    exact hz.symm
  have hneg : M.inner x (-z) = -M.inner x z := by
    have h := M.inner_add_right x z (-z)
    rw [add_neg_cancel, hzero] at h
    apply eq_neg_of_add_eq_zero_left
    rw [add_comm]
    exact h.symm
  rw [hneg, sub_eq_add_neg]

theorem inner_sub_left (x y z : E) :
    M.inner (x - y) z = M.inner x z - M.inner y z := by
  rw [sub_eq_add_neg, M.inner_add_left]
  have hneg : M.inner (-y) z = -M.inner y z := by
    rw [← star_star (M.inner (-y) z), M.star_inner]
    have hz : M.inner z 0 = 0 := by
      have h := M.inner_add_right z 0 0
      have hz' : 0 = M.inner z 0 :=
        add_left_cancel (by simpa only [add_zero] using h)
      exact hz'.symm
    have h := M.inner_add_right z y (-y)
    rw [add_neg_cancel, hz] at h
    have hneg' : M.inner z (-y) = -M.inner z y := by
      apply eq_neg_of_add_eq_zero_left
      rw [add_comm]
      exact h.symm
    rw [hneg',
      star_neg, M.star_inner]
  rw [hneg, sub_eq_add_neg]

theorem inner_rmul_left (x y : E) (b : B) :
    M.inner (M.rmul x b) y = star b * M.inner x y := by
  rw [← star_star (M.inner (M.rmul x b) y), M.star_inner, M.inner_rmul_right,
    star_mul, M.star_inner]

theorem inner_zero_right (x : E) : M.inner x 0 = 0 := by
  have h := M.inner_add_right x 0 0
  have hz : 0 = M.inner x 0 :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hz.symm

theorem inner_zero_left (x : E) : M.inner 0 x = 0 := by
  rw [← star_eq_zero, M.star_inner, M.inner_zero_right]

end RightInnerModuleData

/-- Algebraic pointed KSGNS presentation of a unital map.  `minimal` is intentionally not part of
this algebraic layer; it enters the completion/uniqueness construction. -/
structure UnitalPointedKSGNSData (A B E : Type*) [Ring A] [StarRing A]
    [Ring B] [StarRing B] [Module ℂ B] [AddCommGroup E] [Module ℂ E]
    (phi : A → B) where
  moduleData : RightInnerModuleData B E
  act : A → E → E
  xi : E
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ a b x, act (a * b) x = act a (act b x)
  act_add_ring : ∀ a b x, act (a + b) x = act a x + act b x
  act_add_module : ∀ a x y, act a (x + y) = act a x + act a y
  act_smul : ∀ (c : ℂ) a x, act a (c • x) = c • act a x
  act_rmul : ∀ a x b, act a (moduleData.rmul x b) = moduleData.rmul (act a x) b
  act_adjoint : ∀ a x y,
    moduleData.inner (act a x) y = moduleData.inner x (act (star a) y)
  recover : ∀ a, moduleData.inner xi (act a xi) = phi a
  map_one : phi 1 = 1

namespace UnitalPointedKSGNSData

variable {A B E : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B] [Module ℂ B]
    [AddCommGroup E] [Module ℂ E] {phi : A → B}

def centered (P : UnitalPointedKSGNSData A B E phi) (x : A) : E :=
  P.act x P.xi - P.moduleData.rmul P.xi (phi x)

def cyclicProjection (P : UnitalPointedKSGNSData A B E phi) (x : E) : E :=
  P.moduleData.rmul P.xi (P.moduleData.inner P.xi x)

theorem inner_xi_xi (P : UnitalPointedKSGNSData A B E phi) :
    P.moduleData.inner P.xi P.xi = 1 := by
  calc
    P.moduleData.inner P.xi P.xi =
        P.moduleData.inner P.xi (P.act 1 P.xi) := by rw [P.act_one]
    _ = phi 1 := P.recover 1
    _ = 1 := P.map_one

theorem cyclicProjection_act_xi (P : UnitalPointedKSGNSData A B E phi) (x : A) :
    P.cyclicProjection (P.act x P.xi) = P.moduleData.rmul P.xi (phi x) := by
  rw [cyclicProjection, P.recover]

theorem centered_eq_one_sub_cyclicProjection
    (P : UnitalPointedKSGNSData A B E phi) (x : A) :
    P.centered x = P.act x P.xi - P.cyclicProjection (P.act x P.xi) := by
  rw [centered, cyclicProjection_act_xi]

theorem cyclicProjection_idempotent
    (P : UnitalPointedKSGNSData A B E phi) (x : E) :
    P.cyclicProjection (P.cyclicProjection x) = P.cyclicProjection x := by
  rw [cyclicProjection, cyclicProjection, P.moduleData.inner_rmul_right,
    inner_xi_xi, one_mul]

theorem inner_cyclicProjection_left
    (P : UnitalPointedKSGNSData A B E phi) (x y : E) :
    P.moduleData.inner (P.cyclicProjection x) y =
      P.moduleData.inner x (P.cyclicProjection y) := by
  rw [cyclicProjection, cyclicProjection,
    P.moduleData.inner_rmul_left, P.moduleData.inner_rmul_right,
    P.moduleData.star_inner]

theorem inner_xi_centered (P : UnitalPointedKSGNSData A B E phi) (x : A) :
    P.moduleData.inner P.xi (P.centered x) = 0 := by
  rw [centered, P.moduleData.inner_sub_right, P.recover,
    P.moduleData.inner_rmul_right, inner_xi_xi, one_mul, sub_self]

theorem inner_centered_xi (P : UnitalPointedKSGNSData A B E phi) (x : A) :
    P.moduleData.inner (P.centered x) P.xi = 0 := by
  rw [← P.moduleData.star_inner]
  simp only [inner_xi_centered, star_zero]

theorem inner_act_xi_act_xi
    (P : UnitalPointedKSGNSData A B E phi) (x y : A) :
    P.moduleData.inner (P.act x P.xi) (P.act y P.xi) = phi (star x * y) := by
  rw [P.act_adjoint, ← P.act_mul, P.recover]

theorem inner_act_xi_xi
    (P : UnitalPointedKSGNSData A B E phi) (x : A) :
    P.moduleData.inner (P.act x P.xi) P.xi = star (phi x) := by
  rw [← P.moduleData.star_inner, P.recover]

theorem inner_rmul_xi_rmul_xi
    (P : UnitalPointedKSGNSData A B E phi) (b c : B) :
    P.moduleData.inner (P.moduleData.rmul P.xi b)
      (P.moduleData.rmul P.xi c) = star b * c := by
  rw [P.moduleData.inner_rmul_right, P.moduleData.inner_rmul_left,
    inner_xi_xi, mul_one]

/-- Equation (4): centered KSGNS vectors realize the unital covariance kernel exactly. -/
theorem inner_centered_centered
    (P : UnitalPointedKSGNSData A B E phi) (x y : A) :
    P.moduleData.inner (P.centered x) (P.centered y) =
      phi (star x * y) - star (phi x) * phi y := by
  change P.moduleData.inner
      (P.act x P.xi - P.moduleData.rmul P.xi (phi x))
      (P.act y P.xi - P.moduleData.rmul P.xi (phi y)) = _
  rw [P.moduleData.inner_sub_left, P.moduleData.inner_sub_right,
    P.moduleData.inner_sub_right, P.moduleData.inner_rmul_right,
    P.moduleData.inner_rmul_left, inner_act_xi_act_xi, inner_act_xi_xi,
    P.recover, inner_rmul_xi_rmul_xi]
  abel

theorem inner_centered_centered_eq_starMultiplicativeDefect
    (P : UnitalPointedKSGNSData A B E phi) (x y : A) :
    P.moduleData.inner (P.centered x) (P.centered y) =
      starMultiplicativeDefect phi x y := by
  exact P.inner_centered_centered x y

end UnitalPointedKSGNSData

/-- Algebraic internal-tensor interface needed for the KSGNS succession formula. -/
structure CorrespondenceTensorData (B C E F T : Type*) [Ring B] [StarRing B]
    [Module ℂ B] [Ring C] [StarRing C] [Module ℂ C] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup T] [Module ℂ T]
    (ME : RightInnerModuleData B E) (MF : RightInnerModuleData C F)
    (MT : RightInnerModuleData C T) (leftF : B → F → F) where
  tensor : E → F → T
  tensor_add_left : ∀ x y u, tensor (x + y) u = tensor x u + tensor y u
  tensor_add_right : ∀ x u v, tensor x (u + v) = tensor x u + tensor x v
  tensor_smul_left : ∀ (c : ℂ) x u, tensor (c • x) u = c • tensor x u
  tensor_smul_right : ∀ (c : ℂ) x u, tensor x (c • u) = c • tensor x u
  balanced : ∀ x b u, tensor (ME.rmul x b) u = tensor x (leftF b u)
  leftF_zero : ∀ u, leftF 0 u = 0
  inner_tensor : ∀ x y u v,
    MT.inner (tensor x u) (tensor y v) =
      MF.inner u (leftF (ME.inner x y) v)

namespace CorrespondenceTensorData

variable {B C E F T : Type*} [Ring B] [StarRing B] [Module ℂ B]
    [Ring C] [StarRing C] [Module ℂ C]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup T] [Module ℂ T]
    {ME : RightInnerModuleData B E} {MF : RightInnerModuleData C F}
    {MT : RightInnerModuleData C T} {leftF : B → F → F}
    (Q : CorrespondenceTensorData B C E F T ME MF MT leftF)

theorem tensor_zero_left (u : F) : Q.tensor 0 u = 0 := by
  have h := Q.tensor_add_left 0 0 u
  have hz : 0 = Q.tensor 0 u :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hz.symm

theorem tensor_zero_right (x : E) : Q.tensor x 0 = 0 := by
  have h := Q.tensor_add_right x 0 0
  have hz : 0 = Q.tensor x 0 :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hz.symm

theorem tensor_neg_left (x : E) (u : F) : Q.tensor (-x) u = -Q.tensor x u := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Q.tensor_add_left, neg_add_cancel, Q.tensor_zero_left]

theorem tensor_neg_right (x : E) (u : F) : Q.tensor x (-u) = -Q.tensor x u := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Q.tensor_add_right, neg_add_cancel, Q.tensor_zero_right]

theorem tensor_sub_left (x y : E) (u : F) :
    Q.tensor (x - y) u = Q.tensor x u - Q.tensor y u := by
  rw [sub_eq_add_neg, Q.tensor_add_left, Q.tensor_neg_left, sub_eq_add_neg]

theorem tensor_sub_right (x : E) (u v : F) :
    Q.tensor x (u - v) = Q.tensor x u - Q.tensor x v := by
  rw [sub_eq_add_neg, Q.tensor_add_right, Q.tensor_neg_right, sub_eq_add_neg]

end CorrespondenceTensorData

namespace UnitalPointedKSGNSData

variable {A B C E F T : Type*}
    [Ring A] [StarRing A] [Ring B] [StarRing B] [Module ℂ B]
    [Ring C] [StarRing C] [Module ℂ C]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup T] [Module ℂ T]
    {phi : A → B} {psi : B →+ C}
    (Pphi : UnitalPointedKSGNSData A B E phi)
    (Ppsi : UnitalPointedKSGNSData B C F psi)
    (MT : RightInnerModuleData C T)
    (Q : CorrespondenceTensorData B C E F T Pphi.moduleData Ppsi.moduleData MT Ppsi.act)

/-- Earlier centered channel transported into the correspondence tensor product. -/
def successionEarlier (x : A) : T := Q.tensor (Pphi.centered x) Ppsi.xi

/-- Later centered channel evaluated on the output of the earlier map. -/
def successionLater (x : A) : T := Q.tensor Pphi.xi (Ppsi.centered (phi x))

/-- Equation (6), before extending the cyclic-generator map to the completed KSGNS isometry. -/
theorem succession_centered_decomposition (x : A) :
    Q.tensor (Pphi.act x Pphi.xi) Ppsi.xi -
        Q.tensor Pphi.xi (Ppsi.moduleData.rmul Ppsi.xi (psi (phi x))) =
      successionEarlier Pphi Ppsi MT Q x +
        successionLater Pphi Ppsi MT Q x := by
  change Q.tensor (Pphi.act x Pphi.xi) Ppsi.xi -
      Q.tensor Pphi.xi (Ppsi.moduleData.rmul Ppsi.xi (psi (phi x))) =
    Q.tensor (Pphi.act x Pphi.xi - Pphi.moduleData.rmul Pphi.xi (phi x)) Ppsi.xi +
      Q.tensor Pphi.xi
        (Ppsi.act (phi x) Ppsi.xi - Ppsi.moduleData.rmul Ppsi.xi (psi (phi x)))
  rw [Q.tensor_sub_left, Q.tensor_sub_right, Q.balanced]
  abel

theorem inner_successionEarlier_successionLater (x y : A) :
    MT.inner (successionEarlier Pphi Ppsi MT Q x)
      (successionLater Pphi Ppsi MT Q y) = 0 := by
  rw [successionEarlier, successionLater, Q.inner_tensor,
    Pphi.inner_centered_xi, Q.leftF_zero, Ppsi.moduleData.inner_zero_right]

theorem inner_successionLater_successionEarlier (x y : A) :
    MT.inner (successionLater Pphi Ppsi MT Q x)
      (successionEarlier Pphi Ppsi MT Q y) = 0 := by
  rw [← star_eq_zero, MT.star_inner,
    inner_successionEarlier_successionLater Pphi Ppsi MT Q y x]

theorem inner_successionEarlier (x y : A) :
    MT.inner (successionEarlier Pphi Ppsi MT Q x)
      (successionEarlier Pphi Ppsi MT Q y) =
        psi (starMultiplicativeDefect phi x y) := by
  change MT.inner (Q.tensor (Pphi.centered x) Ppsi.xi)
      (Q.tensor (Pphi.centered y) Ppsi.xi) = _
  rw [Q.inner_tensor, Ppsi.recover,
    Pphi.inner_centered_centered_eq_starMultiplicativeDefect]

theorem inner_successionLater (x y : A) :
    MT.inner (successionLater Pphi Ppsi MT Q x)
      (successionLater Pphi Ppsi MT Q y) =
        starMultiplicativeDefect psi (phi x) (phi y) := by
  change MT.inner (Q.tensor Pphi.xi (Ppsi.centered (phi x)))
      (Q.tensor Pphi.xi (Ppsi.centered (phi y))) = _
  rw [Q.inner_tensor, Pphi.inner_xi_xi,
    Ppsi.act_one, Ppsi.inner_centered_centered_eq_starMultiplicativeDefect]

/-- Equation (7): orthogonal tensor succession realizes the exact covariance chain law. -/
theorem inner_succession_sum (x y : A) :
    MT.inner
        (successionEarlier Pphi Ppsi MT Q x +
          successionLater Pphi Ppsi MT Q x)
        (successionEarlier Pphi Ppsi MT Q y +
          successionLater Pphi Ppsi MT Q y) =
      starMultiplicativeDefect (fun a => psi (phi a)) x y := by
  rw [MT.inner_add_left, MT.inner_add_right, MT.inner_add_right,
    inner_successionEarlier_successionLater Pphi Ppsi MT Q,
    inner_successionLater_successionEarlier Pphi Ppsi MT Q,
    inner_successionEarlier Pphi Ppsi MT Q,
    inner_successionLater Pphi Ppsi MT Q, add_zero, zero_add]
  exact (starMultiplicativeDefect_comp phi psi x y).symm

end UnitalPointedKSGNSData

end GaloisForLFunctions.HTGeometry
