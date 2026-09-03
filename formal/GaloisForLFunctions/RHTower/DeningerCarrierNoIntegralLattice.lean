import GaloisForLFunctions.RHTower.FrobeniusLatticeRigidity
import GaloisForLFunctions.RHTower.DeningerDivisorFlow

/-!
# The graded divisor carrier has no finitely generated Frobenius-stable integral lattice

On the graded carrier `XiZeroCopy →₀ ℂ` the Frobenius at a prime `p` acts on the `ρ`-mode by
`p^ρ`.  Every coordinate functional is an eigen-functional of every Frobenius, so a finitely
generated `ℤ`-submodule stable under the Frobenii at three distinct primes would carry a nonzero
joint eigen-functional with eigenvalues `p^ρ, q^ρ, r^ρ` on a finite free `ℤ`-module, which is
impossible because those three numbers are never all algebraic for a nonreal `ρ`.  Hence the only
such submodule is zero: an integral structure on the carrier cannot be a lattice in the modes.
-/

namespace RHTower

/-- The Frobenius at `p` on the graded divisor carrier: multiplication by `p^ρ` on the `ρ`-mode. -/
noncomputable def deningerPrimeFrobenius (p : ℕ) :
    DeningerDivisorH1 →ₗ[ℤ] DeningerDivisorH1 :=
  (finsuppDiagonal (fun q : XiZeroCopy => (p : ℂ) ^ ((q.1 : ℂ)))).restrictScalars ℤ

theorem deningerPrimeFrobenius_apply (p : ℕ) (v : DeningerDivisorH1) (q : XiZeroCopy) :
    deningerPrimeFrobenius p v q = (p : ℂ) ^ ((q.1 : ℂ)) * v q := by
  unfold deningerPrimeFrobenius
  rw [LinearMap.restrictScalars_apply, finsuppDiagonal_apply]

/-- A complex vector space is torsion-free over `ℤ`. -/
theorem isTorsionFree_int_of_module_complex (V : Type*) [AddCommGroup V] [Module ℂ V] :
    Module.IsTorsionFree ℤ V := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    have h' : (r : ℂ) • m = 0 := by rw [Int.cast_smul_eq_zsmul]; exact h
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    exact (smul_eq_zero.mp h').resolve_left hr'

instance : Module.IsTorsionFree ℤ DeningerDivisorH1 :=
  isTorsionFree_int_of_module_complex _

/-- **No finitely generated Frobenius-stable integral lattice.**  A finitely generated
`ℤ`-submodule of the graded divisor carrier stable under the Frobenii at three distinct primes is
zero. -/
theorem deningerDivisorH1_no_finite_frobenius_lattice {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (L : Submodule ℤ DeningerDivisorH1) [Module.Finite ℤ L]
    (hLp : ∀ v ∈ L, deningerPrimeFrobenius p v ∈ L)
    (hLq : ∀ v ∈ L, deningerPrimeFrobenius q v ∈ L)
    (hLr : ∀ v ∈ L, deningerPrimeFrobenius r v ∈ L) : L = ⊥ := by
  classical
  by_contra hne
  obtain ⟨v, hvL, hv0⟩ : ∃ v ∈ L, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne ((Submodule.eq_bot_iff L).mpr h)
  obtain ⟨q₀, hq₀⟩ := Finsupp.support_nonempty_iff.mpr hv0
  have hq₀v : v q₀ ≠ 0 := Finsupp.mem_support_iff.mp hq₀
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let Fp : L →ₗ[ℤ] L := (deningerPrimeFrobenius p).restrict hLp
  let Fq : L →ₗ[ℤ] L := (deningerPrimeFrobenius q).restrict hLq
  let Fr : L →ₗ[ℤ] L := (deningerPrimeFrobenius r).restrict hLr
  let φ : L →ₗ[ℤ] ℂ :=
    ((Finsupp.lapply q₀ : (XiZeroCopy →₀ ℂ) →ₗ[ℂ] ℂ).restrictScalars ℤ) ∘ₗ L.subtype
  have hφ : φ ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : L →ₗ[ℤ] ℂ => f ⟨v, hvL⟩) h
    simp only [φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.subtype_apply,
      Finsupp.lapply_apply, LinearMap.zero_apply] at h1
    exact hq₀v h1
  have hρ : ((q₀.1 : ℂ)).im ≠ 0 := xi_divisor_support_im_ne_zero q₀.1
  refine not_exists_joint_eigenfunctional_three_primes hρ hp hq hr hpq hpr hqr Fp Fq Fr
    ⟨φ, hφ, ?_, ?_, ?_⟩
  · intro a
    simp only [φ, Fp, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply, Finsupp.lapply_apply, LinearMap.restrict_apply,
      deningerPrimeFrobenius_apply]
  · intro a
    simp only [φ, Fq, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply, Finsupp.lapply_apply, LinearMap.restrict_apply,
      deningerPrimeFrobenius_apply]
  · intro a
    simp only [φ, Fr, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply, Finsupp.lapply_apply, LinearMap.restrict_apply,
      deningerPrimeFrobenius_apply]

end RHTower
