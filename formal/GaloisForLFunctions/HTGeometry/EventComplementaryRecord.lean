import GaloisForLFunctions.HTGeometry.EventInterfaceIndex

/-!
# Complementary records for noninvertible events

This file proves the exact linear-algebraic boundary behind a complementary event record.

If an event map `T : V → W` erases a source direction, every later report obtained by
postcomposing `T` erases it as well.  A second map `R : V → E` makes the combined event
`(T, R)` faithful only if its restriction to `ker T` is injective.  Consequently, the record
space has dimension at least `dim ker T`.  When source and target have equal finite dimension
and the record is valued in `coker T`, this restriction is a bijection.

For the ten-to-ten rank-six interface, a faithful cokernel-valued record therefore pairs a
four-dimensional erased kernel with a four-dimensional created cokernel.

The final scaling lemma isolates the noncanonicity boundary: a linear record invariant under
one nontrivial scalar rescaling of every source vector must vanish.  Thus a bare event map
cannot select a nonzero kernel record while remaining invariant under all kernel
automorphisms.

These results are unconditional linear algebra.  They do not identify the record with
spacetime, construct a quantum channel, or derive dynamics.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {K V W E X : Type*} [Field K]

section AlgebraicBoundary

variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup E] [Module K E]
variable [AddCommGroup X] [Module K X]

/-- Restrict a proposed complementary record to the directions erased by the event. -/
def eventRecordOnKernel (T : V →ₗ[K] W) (R : V →ₗ[K] E) :
    LinearMap.ker T →ₗ[K] E :=
  R.domRestrict (LinearMap.ker T)

/-- Every report obtained after an event erases every direction already erased by the event. -/
theorem eventKernel_le_postReportKernel (T : V →ₗ[K] W) (F : W →ₗ[K] X) :
    LinearMap.ker T ≤ LinearMap.ker (F.comp T) :=
  T.ker_le_ker_comp F

/-- If event plus record is faithful, the record is injective on the event kernel. -/
theorem eventRecordOnKernel_injective
    (T : V →ₗ[K] W) (R : V →ₗ[K] E)
    (hTR : Function.Injective (T.prod R)) :
    Function.Injective (eventRecordOnKernel T R) := by
  intro x y hxy
  apply Subtype.ext
  apply hTR
  apply Prod.ext
  · simp
  · exact hxy

section

variable [FiniteDimensional K E]

/-- Any faithful complementary record has at least the dimension of the erased kernel. -/
theorem eventRecord_finrank_lower_bound
    (T : V →ₗ[K] W) (R : V →ₗ[K] E)
    (hTR : Function.Injective (T.prod R)) :
    Module.finrank K (LinearMap.ker T) ≤ Module.finrank K E :=
  (eventRecordOnKernel T R).finrank_le_finrank_of_injective
    (eventRecordOnKernel_injective T R hTR)

end

end AlgebraicBoundary

section FiniteDimensionalBoundary

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Equal-dimensional source and target give equal-dimensional kernel and cokernel. -/
theorem eventKernel_finrank_eq_coker_of_equal_finrank
    (T : V →ₗ[K] W)
    (hdim : Module.finrank K V = Module.finrank K W) :
    Module.finrank K (LinearMap.ker T) =
      Module.finrank K (W ⧸ LinearMap.range T) := by
  have hrank := T.finrank_range_add_finrank_ker
  have hcoker := Submodule.finrank_quotient_add_finrank (LinearMap.range T)
  omega

/--
A faithful cokernel-valued record on an equal-dimensional event restricts to a bijection from
the erased kernel to the created cokernel.
-/
theorem eventRecordOnKernel_bijective_of_combined_injective
    (T : V →ₗ[K] W)
    (R : V →ₗ[K] (W ⧸ LinearMap.range T))
    (hdim : Module.finrank K V = Module.finrank K W)
    (hTR : Function.Injective (T.prod R)) :
    Function.Bijective (eventRecordOnKernel T R) := by
  have hinj := eventRecordOnKernel_injective T R hTR
  exact
    ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (eventKernel_finrank_eq_coker_of_equal_finrank T hdim)).mp hinj⟩

end FiniteDimensionalBoundary

/--
A faithful cokernel-valued record for a ten-to-ten event restricts to a kernel--cokernel
bijection.  At rank six, both spaces have dimension four by
`rank_six_map_has_four_kernel_and_cokernel`.
-/
theorem rankSixEvent_recordOnKernel_bijective
    (T : Matrix (Fin 10) (Fin 10) ℂ)
    (R : (Fin 10 → ℂ) →ₗ[ℂ] ((Fin 10 → ℂ) ⧸ LinearMap.range T.toLin'))
    (hTR : Function.Injective (T.toLin'.prod R)) :
    Function.Bijective (eventRecordOnKernel T.toLin' R) :=
  eventRecordOnKernel_bijective_of_combined_injective T.toLin' R (by simp) hTR

/--
A linear record invariant under a nontrivial global scalar rescaling is zero.  In particular,
invariance under every automorphism of a nonzero event kernel cannot canonically select a
nonzero linear record.
-/
theorem linearRecord_eq_zero_of_scaling_invariant
    {U Y : Type*} [AddCommGroup U] [Module K U] [AddCommGroup Y] [Module K Y]
    (S : U →ₗ[K] Y) (c : K) (hc : c ≠ 1)
    (hinv : ∀ x, S (c • x) = S x) :
    S = 0 := by
  ext x
  have hfixed : c • S x = S x := by
    rw [← S.map_smul]
    exact hinv x
  have hz : (c - 1) • S x = 0 := by
    rw [sub_smul, one_smul, hfixed, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

end GaloisForLFunctions.HTGeometry
