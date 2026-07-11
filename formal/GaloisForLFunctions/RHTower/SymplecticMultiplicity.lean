import GaloisForLFunctions.RHTower.RHLadderTheory
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Even multiplicity from symplectic self-adjointness, and the Kramers reading of `RH₂`

A finite-dimensional complex endomorphism that is self-adjoint for a nondegenerate alternating
bilinear form has every algebraic multiplicity even — at real and non-real eigenvalues alike.
Distinct generalized eigenspaces are orthogonal for the form, so on each generalized eigenspace
the form restricts nondegenerately; a nondegenerate alternating form forces even dimension,
because its Gram matrix is skew-symmetric and a skew-symmetric matrix of odd size has zero
determinant.  This is the non-self-adjoint counterpart of Kramers degeneracy: a quaternionic
(symplectic) symmetry doubles multiplicities without constraining the location of the spectrum.

Applied to the base rung of the multiplicity-parity ladder: `RHLadder 1` holds iff at every
right-half ξ-zero the vanishing order is the algebraic multiplicity, at that zero, of a
symplectically self-adjoint endomorphism of a finite-dimensional space.  Backward is the parity
mechanism; forward is the scalar realization on a split space.  Reality of a spectrum
(Hilbert–Pólya) is thereby replaced by evenness of its multiplicities as the operator-theoretic
face of a zero statement: the rung asks for symmetry structure on the off-line root spaces, not
for a location constraint on the spectrum.
-/

open Complex Module

namespace RHTower

section Mechanism

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Generalized eigenvectors of a symplectically self-adjoint endomorphism at distinct
eigenvalues are orthogonal for the form: iterated peeling of `(K - λ)` and `(K - μ)` against
`ω (K x) y = ω x (K y)` shrinks both nilpotency indices at once. -/
private theorem ortho_aux (ω : LinearMap.BilinForm ℂ V) (K : Module.End ℂ V)
    (hK : ∀ x y, ω (K x) y = ω x (K y)) {lam mu : ℂ} (hne : lam ≠ mu) :
    ∀ N a b : ℕ, a + b ≤ N →
      ∀ x y : V, ((K - lam • 1) ^ a) x = 0 → ((K - mu • 1) ^ b) y = 0 → ω x y = 0 := by
  have hsub : ∀ (c : ℂ) (x : V), (K - c • 1) x = K x - c • x := by
    intro c x
    simp [LinearMap.sub_apply, LinearMap.smul_apply]
  have hexpL : ∀ x y : V, ω ((K - lam • 1) x) y = ω (K x) y - lam * ω x y := by
    intro x y
    rw [hsub]
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hexpR : ∀ x y : V, ω x ((K - mu • 1) y) = ω x (K y) - mu * ω x y := by
    intro x y
    rw [hsub]
    simp [map_sub, map_smul, smul_eq_mul]
  have hkey : ∀ x y : V, (lam - mu) * ω x y = ω x ((K - mu • 1) y) - ω ((K - lam • 1) x) y := by
    intro x y
    rw [hexpL, hexpR, hK x y]
    ring
  intro N
  induction N with
  | zero =>
    intro a b hab x y hx hy
    have ha : a = 0 := by omega
    subst ha
    rw [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ N ih =>
    intro a b hab x y hx hy
    cases a with
    | zero =>
      rw [pow_zero, Module.End.one_apply] at hx
      simp [hx]
    | succ a' =>
      cases b with
      | zero =>
        rw [pow_zero, Module.End.one_apply] at hy
        simp [hy]
      | succ b' =>
        have hx' : ((K - lam • 1) ^ a') ((K - lam • 1) x) = 0 := by
          rw [← Module.End.mul_apply, ← pow_succ]
          exact hx
        have hy' : ((K - mu • 1) ^ b') ((K - mu • 1) y) = 0 := by
          rw [← Module.End.mul_apply, ← pow_succ]
          exact hy
        have h1 : ω ((K - lam • 1) x) y = 0 := ih a' (b' + 1) (by omega) _ y hx' hy
        have h2 : ω x ((K - mu • 1) y) = 0 := ih (a' + 1) b' (by omega) x _ hx hy'
        have h0 : (lam - mu) * ω x y = 0 := by rw [hkey x y, h1, h2, sub_zero]
        exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero_of_ne hne)

/-- **Orthogonality of distinct generalized eigenspaces** under a symplectically self-adjoint
endomorphism. -/
theorem orthogonal_maxGenEigenspace (ω : LinearMap.BilinForm ℂ V) (K : Module.End ℂ V)
    (hK : ∀ x y, ω (K x) y = ω x (K y)) {lam mu : ℂ} (hne : lam ≠ mu) {x y : V}
    (hx : x ∈ K.maxGenEigenspace lam) (hy : y ∈ K.maxGenEigenspace mu) : ω x y = 0 := by
  obtain ⟨a, ha⟩ := (Module.End.mem_maxGenEigenspace K lam x).mp hx
  obtain ⟨b, hb⟩ := (Module.End.mem_maxGenEigenspace K mu y).mp hy
  exact ortho_aux ω K hK hne (a + b) a b le_rfl x y ha hb

/-- An alternating form restricts to an alternating form on any submodule. -/
theorem isAlt_restrict (ω : LinearMap.BilinForm ℂ V) (halt : ω.IsAlt) (W : Submodule ℂ V) :
    (ω.restrict W).IsAlt := fun x => by
  rw [LinearMap.BilinForm.restrict_apply]
  exact halt x

/-- A nondegenerate alternating form stays nondegenerate on each generalized eigenspace of a
symplectically self-adjoint endomorphism: the complementary generalized eigenspaces are
orthogonal to it and together they span. -/
theorem nondegenerate_restrict_maxGenEigenspace [FiniteDimensional ℂ V]
    (ω : LinearMap.BilinForm ℂ V) (hnd : ω.Nondegenerate) (halt : ω.IsAlt)
    (K : Module.End ℂ V) (hK : ∀ x y, ω (K x) y = ω x (K y)) (lam : ℂ) :
    (ω.restrict (K.maxGenEigenspace lam)).Nondegenerate := by
  refine (isAlt_restrict ω halt _).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  have hzero : ∀ v : V, ω (x : V) v = 0 := by
    intro v
    have hv : v ∈ ⨆ mu : ℂ, K.maxGenEigenspace mu := by
      rw [Module.End.iSup_maxGenEigenspace_eq_top]
      trivial
    refine Submodule.iSup_induction (motive := fun v => ω (x : V) v = 0)
      (fun mu : ℂ => K.maxGenEigenspace mu) hv ?_ ?_ ?_
    · intro mu w hw
      by_cases hmu : mu = lam
      · subst hmu
        have := hx ⟨w, hw⟩
        rwa [LinearMap.BilinForm.restrict_apply] at this
      · exact orthogonal_maxGenEigenspace ω K hK (fun h => hmu h.symm) x.2 hw
    · simp
    · intro u w hu hw
      rw [map_add (ω (x : V)), hu, hw, add_zero]
  exact Subtype.ext (hnd.1 _ hzero)

/-- **A nondegenerate alternating form forces even dimension**: its Gram matrix is
skew-symmetric with nonzero determinant, and an odd skew-symmetric determinant vanishes. -/
theorem even_finrank_of_nondegenerate_isAlt {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {ω : LinearMap.BilinForm ℂ W} (hnd : ω.Nondegenerate)
    (halt : ω.IsAlt) : Even (Module.finrank ℂ W) := by
  classical
  by_contra hodd
  have hodd' : Odd (Module.finrank ℂ W) := Nat.not_even_iff_odd.mp hodd
  let b := Module.finBasis ℂ W
  set M := LinearMap.BilinForm.toMatrix b ω with hM
  have hdet : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  have hskew : M.transpose = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, hM,
      LinearMap.BilinForm.toMatrix_apply]
    exact (LinearMap.IsAlt.neg halt (b i) (b j)).symm
  have hdet2 := congrArg Matrix.det hskew
  rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin, hodd'.neg_one_pow,
    neg_one_mul] at hdet2
  exact hdet (by linear_combination hdet2 / 2)

/-- **Kramers parity for symplectically self-adjoint endomorphisms.**  Every algebraic
multiplicity — the dimension of the generalized eigenspace at any eigenvalue, real or not —
is even.  The quaternionic mechanism constrains multiplicities without constraining the
location of the spectrum. -/
theorem even_finrank_maxGenEigenspace [FiniteDimensional ℂ V]
    (ω : LinearMap.BilinForm ℂ V) (hnd : ω.Nondegenerate) (halt : ω.IsAlt)
    (K : Module.End ℂ V) (hK : ∀ x y, ω (K x) y = ω x (K y)) (lam : ℂ) :
    Even (Module.finrank ℂ (K.maxGenEigenspace lam)) :=
  even_finrank_of_nondegenerate_isAlt
    (nondegenerate_restrict_maxGenEigenspace ω hnd halt K hK lam) (isAlt_restrict ω halt _)

end Mechanism

/-! ## The Kramers reading of the base rung -/

/-- A symplectic realization of a point `ρ`: a symplectically self-adjoint endomorphism of a
finite-dimensional split space whose algebraic multiplicity at `ρ` equals ξ's vanishing order
there.  Every finite-dimensional symplectic space is isomorphic to a split space, so the split
shape costs no generality; the parity content is that the multiplicity at the single eigenvalue
`ρ` — a priori any part of the total even dimension — is itself forced even. -/
def SymplecticRealization (ρ : ℂ) : Prop :=
  ∃ (m : ℕ) (ω : LinearMap.BilinForm ℂ ((Fin m → ℂ) × (Fin m → ℂ)))
    (K : Module.End ℂ ((Fin m → ℂ) × (Fin m → ℂ))),
    ω.Nondegenerate ∧ ω.IsAlt ∧ (∀ x y, ω (K x) y = ω x (K y)) ∧
      Module.finrank ℂ (K.maxGenEigenspace ρ) = (analyticOrderAt xi ρ).toNat

/-- **The parity mechanism yields the base rung**: if every right-half ξ-zero order is the
algebraic multiplicity of a symplectically self-adjoint endomorphism, every such order is even,
which is `RHLadder 1`. -/
theorem rhLadder_one_of_symplecticRealization
    (h : ∀ ρ ∈ rightHalf, xi ρ = 0 → SymplecticRealization ρ) : RHLadder 1 := by
  rw [rhLadder_iff_toNat_dvd]
  intro ρ hρ hzero
  obtain ⟨m, ω, K, hnd, halt, hK, hmult⟩ := h ρ hρ hzero
  rw [pow_one, ← hmult]
  exact (even_finrank_maxGenEigenspace ω hnd halt K hK ρ).two_dvd

/-- The standard split symplectic form `ω((a,b),(c,d)) = a ⬝ᵥ d − b ⬝ᵥ c` on
`(Fin m → ℂ) × (Fin m → ℂ)`. -/
noncomputable def standardSymplectic (m : ℕ) :
    LinearMap.BilinForm ℂ ((Fin m → ℂ) × (Fin m → ℂ)) :=
  LinearMap.mk₂ ℂ (fun p q => dotProduct p.1 q.2 - dotProduct p.2 q.1)
    (fun p p' q => by simp [add_dotProduct]; ring)
    (fun c p q => by simp [smul_dotProduct, smul_eq_mul]; ring)
    (fun p q q' => by simp [dotProduct_add]; ring)
    (fun c p q => by simp [dotProduct_smul, smul_eq_mul]; ring)

theorem standardSymplectic_apply (m : ℕ) (p q : (Fin m → ℂ) × (Fin m → ℂ)) :
    standardSymplectic m p q = dotProduct p.1 q.2 - dotProduct p.2 q.1 := rfl

theorem standardSymplectic_isAlt (m : ℕ) : (standardSymplectic m).IsAlt := by
  intro p
  rw [standardSymplectic_apply, dotProduct_comm, sub_self]

theorem standardSymplectic_nondegenerate (m : ℕ) : (standardSymplectic m).Nondegenerate := by
  refine (standardSymplectic_isAlt m).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro p hp
  have h1 : p.1 = 0 := by
    funext i
    have h := hp (0, Pi.single i 1)
    rw [standardSymplectic_apply] at h
    simpa [dotProduct_single, dotProduct_zero] using h
  have h2 : p.2 = 0 := by
    funext i
    have h := hp (Pi.single i 1, 0)
    rw [standardSymplectic_apply] at h
    have : -(p.2 i) = 0 := by simpa [dotProduct_single, dotProduct_zero] using h
    simpa using this
  exact Prod.ext h1 h2

/-- **Even orders admit symplectic realizations**: the scalar endomorphism of the split space
of half the order realizes the multiplicity, and scalars are self-adjoint for every form. -/
theorem symplecticRealization_of_even_order {ρ : ℂ}
    (h : Even (analyticOrderAt xi ρ).toNat) : SymplecticRealization ρ := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, standardSymplectic m, ρ • 1, standardSymplectic_nondegenerate m,
    standardSymplectic_isAlt m, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]
  · have htop : (ρ • (1 : Module.End ℂ ((Fin m → ℂ) × (Fin m → ℂ)))).maxGenEigenspace ρ = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Module.End.mem_maxGenEigenspace]
      exact ⟨1, by simp⟩
    rw [htop, finrank_top, hm]
    simp [Module.finrank_prod]

/-- **The Kramers reading of `RH₂`.**  The base rung of the multiplicity-parity ladder holds
iff every right-half ξ-zero order is the algebraic multiplicity, at that zero, of a
symplectically self-adjoint endomorphism of a finite-dimensional space.  The parity of a
vanishing order is exactly the existence of a quaternionic symmetry on a finite-dimensional
model of the local divisor. -/
theorem rhLadder_one_iff_symplecticRealization :
    RHLadder 1 ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → SymplecticRealization ρ := by
  constructor
  · intro hlad ρ hρ hzero
    have h2 : 2 ∣ (analyticOrderAt xi ρ).toNat := by
      have := (rhLadder_iff_toNat_dvd 1).mp hlad ρ hρ hzero
      simpa using this
    exact symplecticRealization_of_even_order (even_iff_two_dvd.mpr h2)
  · exact rhLadder_one_of_symplecticRealization

end RHTower
