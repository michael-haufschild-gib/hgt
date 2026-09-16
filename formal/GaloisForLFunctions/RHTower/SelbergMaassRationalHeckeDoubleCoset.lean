import GaloisForLFunctions.RHTower.SelbergMaassPositiveRationalHeckePair
import GaloisForLFunctions.RHTower.SelbergMaassMackeyTraceComposition
import GaloisForLFunctions.RHTower.SelbergMaassHeckeEigenspace

/-!
# First double-coset identity for rational Maass traces

The finite rational trace is unchanged when its rational correspondence matrix
is multiplied on the right by an element of the principal source group. This
is an actual double-coset invariance law: base change carries relative cosets
to the conjugated source, while source invariance removes the remaining
principal pullback. It is one half of the factorization needed to turn
source-attached rational traces into operators indexed by Hecke-pair double
cosets.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction Subgroup
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- Replacing only the target presentation of a finite trace by an equal
subgroup leaves the trace unchanged. -/
private theorem maassTraceFunction_congr_target
    {G H K : Subgroup (GL (Fin 2) ℝ)}
    [G.IsFiniteRelIndex H] [G.IsFiniteRelIndex K]
    (hHK : H = K) (f : glUpperHalfPlaneInvariantFunctions G) :
    maassTraceFunction (H := H) f = maassTraceFunction (H := K) f := by
  subst K
  rfl

/-- Pullback-conjugating the principal group by one of its rational lifts fixes
that group. -/
private theorem rationalPullback_principal_eq
    (N : ℕ) (a : GL (Fin 2) ℚ) (p : principalCongruenceGL N)
    (ha : a.map (algebraMap ℚ ℝ) = p.val) :
    rationalPullbackConjugateGroup (principalCongruenceGL N) a =
      principalCongruenceGL N := by
  unfold rationalPullbackConjugateGroup
  rw [ha]
  exact Subgroup.conjAct_pointwise_smul_eq_self
    (Subgroup.le_normalizer ((principalCongruenceGL N).inv_mem p.2))

/-- Right multiplication by a principal source transformation leaves the
literal rational finite trace unchanged. The rational matrix `a` is a lift of
that source transformation; finite-index witnesses come from rational
commensurability. -/
theorem rationalPrincipalTrace_right_mul_principal
    (N : ℕ) (g a : GL (Fin 2) ℚ) (p : principalCongruenceGL N)
    (ha : a.map (algebraMap ℚ ℝ) = p.val)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalConjugateGroup N (g * a)).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N (g * a)
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) (g * a) f) =
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f) := by
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let Γ : Subgroup (GL (Fin 2) ℝ) := rationalPullbackConjugateGroup P g
  let fΓ : glUpperHalfPlaneInvariantFunctions Γ :=
    rationalMaassPullbackInvariant_general P g f
  letI : (rationalConjugateGroup N (g * a)).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N (g * a)
  letI : Γ.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N g
  have hP : rationalPullbackConjugateGroup P a = P :=
    rationalPullback_principal_eq N a p ha
  have hΓ : rationalPullbackConjugateGroup Γ a =
      rationalPullbackConjugateGroup P (g * a) := by
    simpa only [Γ] using rationalPullbackConjugateGroup_mul P g a
  have hfunc : (rationalMaassPullbackInvariant_general Γ a fΓ).1 =
      (rationalMaassPullbackInvariant_general P (g * a) f).1 := by
    funext z
    change f.1 (g.map (algebraMap ℚ ℝ) •
      (a.map (algebraMap ℚ ℝ) • z)) =
      f.1 ((g * a).map (algebraMap ℚ ℝ) • z)
    rw [← mul_smul, ← Matrix.GeneralLinearGroup.map_mul]
  have hbase := maassTrace_rationalPullback_baseChange Γ P a fΓ
  letI : (rationalPullbackConjugateGroup Γ a).IsFiniteRelIndex P := by
    rw [hΓ]
    exact rationalConjugateGroup_isFiniteRelIndex N (g * a)
  letI : (rationalPullbackConjugateGroup Γ a).IsFiniteRelIndex
      (rationalPullbackConjugateGroup P a) :=
    rationalPullback_isFiniteRelIndex Γ P a
  have hbaseP :
      maassTraceFunction (H := P) (rationalMaassPullbackInvariant_general Γ a fΓ) =
        (rationalMaassPullbackInvariant_general P a
          (maassTraceInvariant (H := P) fΓ)).1 := by
    calc
      maassTraceFunction (H := P) (rationalMaassPullbackInvariant_general Γ a fΓ) =
          maassTraceFunction (H := rationalPullbackConjugateGroup P a)
            (rationalMaassPullbackInvariant_general Γ a fΓ) :=
        (maassTraceFunction_congr_target hP
          (rationalMaassPullbackInvariant_general Γ a fΓ)).symm
      _ = _ := hbase
  have hsubΓ : (rationalPullbackConjugateGroup Γ a).subgroupOf P =
      (rationalPullbackConjugateGroup P (g * a)).subgroupOf P := by
    rw [hΓ]
  have hleft :
      maassTraceFunction (H := P) (rationalMaassPullbackInvariant_general Γ a fΓ) =
        maassTraceFunction (H := P)
          (rationalMaassPullbackInvariant_general P (g * a) f) :=
    maassTraceFunction_congr_source hsubΓ
      (rationalMaassPullbackInvariant_general Γ a fΓ)
      (rationalMaassPullbackInvariant_general P (g * a) f) hfunc
  have hright : (rationalMaassPullbackInvariant_general P a
      (maassTraceInvariant (H := P) fΓ)).1 =
      (maassTraceInvariant (H := P) fΓ).1 := by
    funext z
    change maassTraceFunction (H := P) fΓ (a.map (algebraMap ℚ ℝ) • z) =
      maassTraceFunction (H := P) fΓ z
    rw [ha]
    exact (maassTraceInvariant (H := P) fΓ).2 p z
  change maassTraceFunction (H := P)
      (rationalMaassPullbackInvariant_general P (g * a) f) =
    maassTraceFunction (H := P) fΓ
  rw [← hleft, hbaseP, hright]
  rfl

/-- Left multiplication by a principal source transformation leaves the
literal rational finite trace unchanged. -/
theorem rationalPrincipalTrace_left_mul_principal
    (N : ℕ) (a g : GL (Fin 2) ℚ) (p : principalCongruenceGL N)
    (ha : a.map (algebraMap ℚ ℝ) = p.val)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalConjugateGroup N (a * g)).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N (a * g)
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) (a * g) f) =
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f) := by
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  letI : (rationalConjugateGroup N (a * g)).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N (a * g)
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  have hP : rationalPullbackConjugateGroup P a = P :=
    rationalPullback_principal_eq N a p ha
  have hsource : rationalPullbackConjugateGroup P (a * g) =
      rationalPullbackConjugateGroup P g := by
    rw [← rationalPullbackConjugateGroup_mul P a g, hP]
  have hfunc :
      (rationalMaassPullbackInvariant_general P (a * g) f).1 =
      (rationalMaassPullbackInvariant_general P g f).1 := by
    funext z
    change f.1 ((a * g).map (algebraMap ℚ ℝ) • z) =
      f.1 (g.map (algebraMap ℚ ℝ) • z)
    rw [Matrix.GeneralLinearGroup.map_mul, mul_smul, ha]
    exact f.2 p _
  have hsub : (rationalPullbackConjugateGroup P (a * g)).subgroupOf P =
      (rationalPullbackConjugateGroup P g).subgroupOf P := by
    rw [hsource]
  change maassTraceFunction (H := P)
      (rationalMaassPullbackInvariant_general P (a * g) f) =
    maassTraceFunction (H := P)
      (rationalMaassPullbackInvariant_general P g f)
  exact maassTraceFunction_congr_source hsub
    (rationalMaassPullbackInvariant_general P (a * g) f)
    (rationalMaassPullbackInvariant_general P g f) hfunc

/-- A rational finite trace depends only on the principal double coset of its
correspondence matrix. This is the source-level descent law required before a
Hecke-coset action can be defined. -/
theorem rationalPrincipalTrace_eq_of_principal_doubleCoset
    (N : ℕ) (g h : GL (Fin 2) ℚ)
    (hgh : DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N) (g.map (algebraMap ℚ ℝ))
      (h.map (algebraMap ℚ ℝ)))
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalConjugateGroup N h).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N h
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) h f) =
    maassTraceFunction (H := principalCongruenceGL N)
      (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f) := by
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  obtain ⟨p₁, hp₁, p₂, hp₂, hEq⟩ := (DoubleCoset.rel_iff.mp hgh)
  let p₁' : P := ⟨p₁, hp₁⟩
  let p₂' : P := ⟨p₂, hp₂⟩
  have hp₁rat : p₁ ∈ rationalConjugateGroup N (1 : GL (Fin 2) ℚ) := by
    simpa [P, rationalConjugateGroup, rationalPullbackConjugateGroup] using hp₁
  have hp₂rat : p₂ ∈ rationalConjugateGroup N (1 : GL (Fin 2) ℚ) := by
    simpa [P, rationalConjugateGroup, rationalPullbackConjugateGroup] using hp₂
  let p₁rat : rationalConjugateGroup N (1 : GL (Fin 2) ℚ) := ⟨p₁, hp₁rat⟩
  let p₂rat : rationalConjugateGroup N (1 : GL (Fin 2) ℚ) := ⟨p₂, hp₂rat⟩
  obtain ⟨a₁, ha₁, _⟩ :=
    rationalConjugateGroup_exists_positive_rational_lift N (1 : GL (Fin 2) ℚ) p₁rat
  obtain ⟨a₂, ha₂, _⟩ :=
    rationalConjugateGroup_exists_positive_rational_lift N (1 : GL (Fin 2) ℚ) p₂rat
  letI : (rationalConjugateGroup N h).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N h
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : (rationalConjugateGroup N (a₁ * g * a₂)).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N (a₁ * g * a₂)
  letI : (rationalConjugateGroup N (a₁ * g)).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N (a₁ * g)
  have hmap : h.map (algebraMap ℚ ℝ) = (a₁ * g * a₂).map (algebraMap ℚ ℝ) := by
    rw [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul, ha₁, ha₂]
    exact hEq
  have hsource : rationalPullbackConjugateGroup P h =
      rationalPullbackConjugateGroup P (a₁ * g * a₂) := by
    unfold rationalPullbackConjugateGroup
    rw [hmap]
  let fh : glUpperHalfPlaneInvariantFunctions (rationalPullbackConjugateGroup P h) :=
    rationalMaassPullbackInvariant_general P h f
  let fprod : glUpperHalfPlaneInvariantFunctions
      (rationalPullbackConjugateGroup P (a₁ * g * a₂)) :=
    rationalMaassPullbackInvariant_general P (a₁ * g * a₂) f
  let fg : glUpperHalfPlaneInvariantFunctions (rationalPullbackConjugateGroup P g) :=
    rationalMaassPullbackInvariant_general P g f
  have hfunc : fh.1 = fprod.1 := by
    funext z
    change f.1 (h.map (algebraMap ℚ ℝ) • z) =
      f.1 ((a₁ * g * a₂).map (algebraMap ℚ ℝ) • z)
    rw [hmap]
  have hsub : (rationalPullbackConjugateGroup P h).subgroupOf P =
      (rationalPullbackConjugateGroup P (a₁ * g * a₂)).subgroupOf P := by
    rw [hsource]
  have htrace : maassTraceFunction (H := P) fh =
      maassTraceFunction (H := P) fprod :=
    maassTraceFunction_congr_source hsub fh fprod hfunc
  have hright := rationalPrincipalTrace_right_mul_principal N (a₁ * g) a₂ p₂' ha₂ f
  have hleft := rationalPrincipalTrace_left_mul_principal N a₁ g p₁' ha₁ f
  change maassTraceFunction (H := P) fh = maassTraceFunction (H := P) fg
  calc
    maassTraceFunction (H := P) fh = maassTraceFunction (H := P) fprod := htrace
    _ = maassTraceFunction (H := P)
        (rationalMaassPullbackInvariant_general P (a₁ * g) f) := by
      simpa only [P] using hright
    _ = maassTraceFunction (H := P) fg := by
      simpa only [P, fg] using hleft

/-- A chosen positive rational lift of an element of the source Hecke-pair
monoid. Choice is used only to select a representative; the next theorem
proves that its trace does not depend on that representative. -/
noncomputable def positiveRationalHeckeLift (d : positiveRationalGLRealImage) : GL (Fin 2) ℚ :=
  d.2.choose

theorem positiveRationalHeckeLift_map (d : positiveRationalGLRealImage) :
    (positiveRationalHeckeLift d).map (algebraMap ℚ ℝ) = d.val :=
  d.2.choose_spec.1

theorem positiveRationalHeckeLift_det_pos (d : positiveRationalGLRealImage) :
    0 < ((positiveRationalHeckeLift d).map (algebraMap ℚ ℝ)).val.det :=
  d.2.choose_spec.2

/-- The literal finite trace attached to one positive rational Hecke-pair
element. -/
noncomputable def rationalPrincipalHeckeTrace
    (N : ℕ) (d : positiveRationalGLRealImage)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) : ℍ → ℂ := by
  letI : (rationalConjugateGroup N (positiveRationalHeckeLift d)).IsFiniteRelIndex
      (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N (positiveRationalHeckeLift d)
  exact maassTraceFunction (H := principalCongruenceGL N)
    (rationalMaassPullbackInvariant_general (principalCongruenceGL N)
      (positiveRationalHeckeLift d) f)

/-- The rational finite trace is constant on the equivalence relation defining
Mathlib's principal Hecke cosets. -/
theorem rationalPrincipalHeckeTrace_congr
    (N : ℕ) (d e : positiveRationalGLRealImage)
    (hde : HeckeCoset.setoid positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N) d e)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    rationalPrincipalHeckeTrace N d f = rationalPrincipalHeckeTrace N e f := by
  have hdouble : DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N)
      ((positiveRationalHeckeLift d).map (algebraMap ℚ ℝ))
      ((positiveRationalHeckeLift e).map (algebraMap ℚ ℝ)) := by
    change DoubleCoset.setoid (principalCongruenceGL N : Set (GL (Fin 2) ℝ))
      (principalCongruenceGL N) d.val e.val at hde
    simpa only [positiveRationalHeckeLift_map] using hde
  simpa only [rationalPrincipalHeckeTrace] using
    (rationalPrincipalTrace_eq_of_principal_doubleCoset N
      (positiveRationalHeckeLift d) (positiveRationalHeckeLift e) hdouble f).symm

/-- The source-attached rational finite trace descends to every principal
Hecke double coset. This supplies the basis-level finite-place operators;
convolution compatibility remains a separate theorem. -/
noncomputable def rationalPrincipalHeckeCosetTrace
    (N : ℕ)
    (D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N))
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) : ℍ → ℂ :=
  Quotient.liftOn D (fun d => rationalPrincipalHeckeTrace N d f)
    (fun d e hde => rationalPrincipalHeckeTrace_congr N d e hde f)

@[simp] theorem rationalPrincipalHeckeCosetTrace_mk
    (N : ℕ) (d : positiveRationalGLRealImage)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    rationalPrincipalHeckeCosetTrace N
      (HeckeCoset.mk (principalCongruenceGL N) (principalCongruenceGL N) d) f =
      rationalPrincipalHeckeTrace N d f :=
  rfl

/-- The trace attached to one positive rational Hecke-pair element is a
complex-linear endomorphism of the zero-inclusive source Maass eigenspace. -/
noncomputable def rationalPrincipalHeckeLinear
    (N : ℕ) (lam : ℝ) (d : positiveRationalGLRealImage) :
    Module.End ℂ (glMaassCuspEigenspace (principalCongruenceGL N) lam) :=
  rationalPrincipalTraceLinear N (positiveRationalHeckeLift d)
    (positiveRationalHeckeLift_det_pos d) lam

/-- The source eigenspace endomorphism is independent of the representative
of a principal Hecke double coset. -/
theorem rationalPrincipalHeckeLinear_congr
    (N : ℕ) (lam : ℝ) (d e : positiveRationalGLRealImage)
    (hde : HeckeCoset.setoid positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N) d e) :
    rationalPrincipalHeckeLinear N lam d = rationalPrincipalHeckeLinear N lam e := by
  ext u z
  change rationalPrincipalHeckeTrace N d (maassEigenspaceToInvariant u) z =
    rationalPrincipalHeckeTrace N e (maassEigenspaceToInvariant u) z
  exact congrFun (rationalPrincipalHeckeTrace_congr N d e hde
    (maassEigenspaceToInvariant u)) z

/-- Principal-Hecke double cosets act individually by closed complex-linear
endomorphisms on every fixed source Maass eigenspace. -/
noncomputable def rationalPrincipalHeckeCosetLinear
    (N : ℕ) (lam : ℝ)
    (D : HeckeCoset positiveRationalGLRealImage
      (principalCongruenceGL N) (principalCongruenceGL N)) :
    Module.End ℂ (glMaassCuspEigenspace (principalCongruenceGL N) lam) :=
  Quotient.liftOn D (fun d => rationalPrincipalHeckeLinear N lam d)
    (fun d e hde => rationalPrincipalHeckeLinear_congr N lam d e hde)

@[simp] theorem rationalPrincipalHeckeCosetLinear_mk
    (N : ℕ) (lam : ℝ) (d : positiveRationalGLRealImage) :
    rationalPrincipalHeckeCosetLinear N lam
      (HeckeCoset.mk (principalCongruenceGL N) (principalCongruenceGL N) d) =
      rationalPrincipalHeckeLinear N lam d :=
  rfl

end

end GaloisForLFunctions.RHTower
