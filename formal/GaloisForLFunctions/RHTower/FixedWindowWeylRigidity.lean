/-
# Fixed-window Weyl rigidity (abstract core)

Support theorem for the covering-descent index-divisibility card
(`docs/drafts/pipeline/1-in-progress/prime-covering-descent-index-divisibility-rh.md`,
OPEN CORE 1; Lean half of its Support Theorem 1, necessity direction), strengthening
kill-condition 4 of the socle–Weyl card.

Content: for a finite-dimensional complex space, any linear conjugation
`W f W⁻¹ = ζ • f` forces every stabilized generalized-kernel dimension (algebraic
multiplicity) of `f` to be invariant under eigenvalue rotation `ν ↦ ζ * ν`. Orbit sums
of multiplicities are then `n * algMult f ν` along the rotation orbit. Applied to the
multiplication operator by `p^{-s}` on a window zero algebra, whose eigenvalues are the
values `p^{-ρ}` on the window divisor, this says: a fixed-window Weyl partner for the
prime multiplication operator exists only if the window divisor already carries the
vertical arithmetic-progression symmetry `ρ ↦ ρ + 2πi·a/(2^k log p)` — divisibility of
the count is the *hypothesis* of such a construction, never its output.
-/
import Mathlib

namespace GaloisForLFunctions
namespace RHTower
namespace FixedWindowWeylRigidity

open Module LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Algebraic-multiplicity reader: dimension of the stabilized generalized kernel of
`f - ν•1` (exponent `finrank ℂ V` stabilizes every generalized eigenspace). -/
noncomputable def algMult (f : Module.End ℂ V) (ν : ℂ) : ℕ :=
  Module.finrank ℂ
    (LinearMap.ker ((f - ν • (1 : Module.End ℂ V)) ^ (Module.finrank ℂ V)))

/-- Conjugation by a linear equivalence is unital on endomorphisms. -/
lemma conj_one (e : V ≃ₗ[ℂ] V) : e.conj (1 : Module.End ℂ V) = 1 := by
  ext x
  simp [LinearEquiv.conj_apply]

/-- Conjugation commutes with the affine pencil `f - ν•1`. -/
lemma conj_sub_smul_one (e : V ≃ₗ[ℂ] V) (f : Module.End ℂ V) (ν : ℂ) :
    e.conj (f - ν • (1 : Module.End ℂ V)) = e.conj f - ν • (1 : Module.End ℂ V) := by
  have h := conj_one e
  calc e.conj (f - ν • (1 : Module.End ℂ V))
      = e.conj f - ν • e.conj (1 : Module.End ℂ V) := by
        simp [map_sub, map_smul]
    _ = e.conj f - ν • (1 : Module.End ℂ V) := by rw [h]

/-- Conjugation is multiplicative on endomorphisms. -/
lemma conj_mul (e : V ≃ₗ[ℂ] V) (g h : Module.End ℂ V) :
    e.conj (g * h) = e.conj g * e.conj h := by
  ext x
  simp [LinearEquiv.conj_apply, Module.End.mul_apply]

/-- Conjugation commutes with powers. -/
lemma conj_pow (e : V ≃ₗ[ℂ] V) (g : Module.End ℂ V) (n : ℕ) :
    e.conj (g ^ n) = (e.conj g) ^ n := by
  induction n with
  | zero => simpa [pow_zero] using conj_one e
  | succ n ih => rw [pow_succ, pow_succ, conj_mul, ih]

/-- The kernel of a conjugated endomorphism is the image of the kernel. -/
lemma ker_conj (e : V ≃ₗ[ℂ] V) (h : Module.End ℂ V) :
    LinearMap.ker (e.conj h) = (LinearMap.ker h).map (e : V →ₗ[ℂ] V) := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    have hx' : e (h (e.symm x)) = 0 := by
      simpa [LinearEquiv.conj_apply] using hx
    have := congrArg e.symm hx'
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have hy' : h y = 0 := hy
    simp [LinearEquiv.conj_apply, hy']

/-- Algebraic multiplicities are conjugation invariants. -/
lemma algMult_conj [FiniteDimensional ℂ V] (e : V ≃ₗ[ℂ] V) (f : Module.End ℂ V) (ν : ℂ) :
    algMult (e.conj f) ν = algMult f ν := by
  unfold algMult
  rw [← conj_sub_smul_one, ← conj_pow, ker_conj]
  exact LinearEquiv.finrank_map_eq e _

/-- Scaling an endomorphism divides the eigenvalue: `algMult (ζ•f) ν = algMult f (ν/ζ)`. -/
lemma algMult_smul [FiniteDimensional ℂ V] {ζ : ℂ} (hζ : ζ ≠ 0)
    (f : Module.End ℂ V) (ν : ℂ) :
    algMult (ζ • f) ν = algMult f (ν / ζ) := by
  unfold algMult
  have hpencil : ζ • f - ν • (1 : Module.End ℂ V)
      = ζ • (f - (ν / ζ) • (1 : Module.End ℂ V)) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ ν hζ]
  rw [hpencil, smul_pow, LinearMap.ker_smul _ _ (pow_ne_zero _ hζ)]

/-- **Fixed-window Weyl rigidity (necessity).** If some linear equivalence conjugates
`f` to `ζ • f`, then every algebraic multiplicity of `f` is invariant under the
eigenvalue rotation `ν ↦ ζ * ν`. -/
theorem algMult_rotation [FiniteDimensional ℂ V] {W : V ≃ₗ[ℂ] V} {f : Module.End ℂ V}
    {ζ : ℂ} (hζ : ζ ≠ 0) (h : W.conj f = ζ • f) (ν : ℂ) :
    algMult f (ζ * ν) = algMult f ν := by
  have h1 : algMult f (ζ * ν) = algMult (W.conj f) (ζ * ν) :=
    (algMult_conj W f (ζ * ν)).symm
  rw [h, algMult_smul hζ] at h1
  rwa [mul_div_cancel_left₀ ν hζ] at h1

/-- Iterated rotation invariance along the orbit. -/
theorem algMult_orbit [FiniteDimensional ℂ V] {W : V ≃ₗ[ℂ] V} {f : Module.End ℂ V}
    {ζ : ℂ} (hζ : ζ ≠ 0) (h : W.conj f = ζ • f) (ν : ℂ) (j : ℕ) :
    algMult f (ζ ^ j * ν) = algMult f ν := by
  induction j with
  | zero => simp
  | succ j ih =>
      have : ζ ^ (j + 1) * ν = ζ * (ζ ^ j * ν) := by ring
      rw [this, algMult_rotation hζ h, ih]

/-- Orbit sums of algebraic multiplicities: along `n` rotation steps the total mass is
`n * algMult f ν`. In particular, whenever the `n` orbit points are pairwise distinct
(e.g. `ζ` a primitive `n`-th root of unity and `ν ≠ 0`), the total algebraic
multiplicity carried by the orbit is divisible by `n`. -/
theorem algMult_orbit_sum [FiniteDimensional ℂ V] {W : V ≃ₗ[ℂ] V} {f : Module.End ℂ V}
    {ζ : ℂ} (hζ : ζ ≠ 0) (h : W.conj f = ζ • f) (ν : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range n, algMult f (ζ ^ j * ν) = n * algMult f ν := by
  have hconst : ∀ j ∈ Finset.range n, algMult f (ζ ^ j * ν) = algMult f ν :=
    fun j _ => algMult_orbit hζ h ν j
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Divisibility reading of the orbit sum. -/
theorem dvd_orbit_sum [FiniteDimensional ℂ V] {W : V ≃ₗ[ℂ] V} {f : Module.End ℂ V}
    {ζ : ℂ} (hζ : ζ ≠ 0) (h : W.conj f = ζ • f) (ν : ℂ) (n : ℕ) :
    n ∣ ∑ j ∈ Finset.range n, algMult f (ζ ^ j * ν) := by
  rw [algMult_orbit_sum hζ h ν n]
  exact Dvd.intro _ rfl

/-- **No-go reading.** If one algebraic multiplicity of `f` fails the `ζ`-rotation
invariance, then no linear equivalence conjugates `f` to `ζ • f`: a fixed-window Weyl
partner cannot exist without the rotation symmetry of the spectrum. -/
theorem no_weyl_partner_of_asymmetric [FiniteDimensional ℂ V] {f : Module.End ℂ V}
    {ζ : ℂ} (hζ : ζ ≠ 0) {ν : ℂ} (hasym : algMult f (ζ * ν) ≠ algMult f ν) :
    ¬ ∃ W : V ≃ₗ[ℂ] V, W.conj f = ζ • f := by
  rintro ⟨W, hW⟩
  exact hasym (algMult_rotation hζ hW ν)

end FixedWindowWeylRigidity
end RHTower
end GaloisForLFunctions
