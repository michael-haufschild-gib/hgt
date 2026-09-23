import GaloisForLFunctions.HTGeometry.RittEigenSliceDescent
import GaloisForLFunctions.HTGeometry.RittPrefixFieldStability

/-!
# A rational second jet of a linearizer is a rational affine connection

Let `τ` solve `σ τ = q · τ` in a Ritt frame with `q` a derivation constant, and suppose the first two
jets are independent: `τ` transcendental over the base and `d τ` transcendental over `K⟮τ⟯`.  The
Galoisian proof of Ritt's theorem must rule out that the *second* jet is rational in them.

Writing `s = τ / d τ`, the shift scales `s` by the chain-rule factor, `σ s = ρ · s`, and the
normalised second jet `W = d²τ · τ / (d τ)²` satisfies the inhomogeneous relation

`σ W = W − (dK ρ / ρ) · s`.

If `d²τ ∈ K⟮τ, d τ⟯ = K⟮τ⟯⟮s⟯`, the inhomogeneous coprime descent in `s` over `K⟮τ⟯` produces an
element of `K⟮τ⟯` solving `φ(a)·ρ = a − dK ρ / ρ`, and the eigen-inhomogeneous descent in `τ` over
`K` pushes it down to the base.  The resulting equation

`ψ(a)·ρ = a − dK ρ / ρ`

is exactly the rational affine-connection equation `a(R)·(R′)² = R′·a − R″` of
`RationalAffineConnection`, which the corpus excludes for concrete non-exceptional maps.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace RittFrame

variable (Fr : RittFrame K L)

/-- The shift scales the jet ratio by the chain-rule factor. -/
theorem sigma_jetRatio {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (τ / Fr.d τ) = algebraMap K L Fr.ρ * (τ / Fr.d τ) := by
  have hd := Fr.sigma_d_eq_of_shift hqconst hshift
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq
  have hρL : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr Fr.ρ_ne
  rw [map_div₀, hshift, hd, map_div₀]
  field_simp

/-- The shift of the second jet, with its explicit lower-order coefficient. -/
theorem sigma_second_jet {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (Fr.d (Fr.d τ))
      = algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) * Fr.d (Fr.d τ)
        + algebraMap K L (Fr.dK (q / Fr.ρ) / Fr.ρ) * Fr.d τ := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hρL : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hd := Fr.sigma_d_eq_of_shift hqconst hshift
  have hchain := Fr.chain (Fr.d τ)
  rw [hd, Fr.d_mul, Fr.d_base] at hchain
  have hpow : algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) * algebraMap K L Fr.ρ
      = algebraMap K L (q / Fr.ρ) := by
    rw [← map_mul]
    congr 1
    field_simp
  have hdiv : algebraMap K L (Fr.dK (q / Fr.ρ) / Fr.ρ) * algebraMap K L Fr.ρ
      = algebraMap K L (Fr.dK (q / Fr.ρ)) := by
    rw [← map_mul]
    congr 1
    field_simp
  refine mul_left_cancel₀ hρL ?_
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_comm (algebraMap K L Fr.ρ)
    (algebraMap K L (q / Fr.ρ ^ (2 : ℕ))), mul_comm (algebraMap K L Fr.ρ)
    (algebraMap K L (Fr.dK (q / Fr.ρ) / Fr.ρ)), hpow, hdiv]
  linear_combination -hchain

/-- The normalised second jet solves an inhomogeneous shift equation over the jet ratio. -/
theorem sigma_normalizedSecondJet {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (Fr.d (Fr.d τ) * τ / (Fr.d τ) ^ (2 : ℕ))
      = Fr.d (Fr.d τ) * τ / (Fr.d τ) ^ (2 : ℕ)
        + algebraMap K L (Fr.ρ * Fr.dK (q / Fr.ρ) / q) * (τ / Fr.d τ) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hρL : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq
  have hd := Fr.sigma_d_eq_of_shift hqconst hshift
  have h2 := Fr.sigma_second_jet hqconst hshift
  rw [map_div₀, map_mul, map_pow, h2, hd, hshift]
  rw [show algebraMap K L (q / Fr.ρ ^ (2 : ℕ)) = algebraMap K L q / algebraMap K L Fr.ρ ^ (2 : ℕ) by
    rw [map_div₀, map_pow]]
  rw [show algebraMap K L (Fr.dK (q / Fr.ρ) / Fr.ρ)
      = algebraMap K L (Fr.dK (q / Fr.ρ)) / algebraMap K L Fr.ρ by rw [map_div₀]]
  rw [show algebraMap K L (q / Fr.ρ) = algebraMap K L q / algebraMap K L Fr.ρ by rw [map_div₀]]
  rw [show algebraMap K L (Fr.ρ * Fr.dK (q / Fr.ρ) / q)
      = algebraMap K L Fr.ρ * algebraMap K L (Fr.dK (q / Fr.ρ)) / algebraMap K L q by
    rw [map_div₀, map_mul]]
  field_simp

end RittFrame

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

/-- The base derivation of a frame satisfies the Leibniz rule. -/
theorem dK_mul (a b : K) : Fr.dK (a * b) = Fr.dK a * b + a * Fr.dK b := by
  refine (algebraMap K L).injective ?_
  rw [map_add, map_mul, map_mul, ← Fr.d_base, ← Fr.d_base, ← Fr.d_base,
    show algebraMap K L (a * b) = algebraMap K L a * algebraMap K L b from map_mul _ _ _,
    Fr.d_mul]

/-- The quotient rule for the base derivation. -/
theorem dK_div {a b : K} (hb : b ≠ 0) :
    Fr.dK (a / b) = (Fr.dK a * b - a * Fr.dK b) / b ^ (2 : ℕ) := by
  have hab : a / b * b = a := by field_simp
  have h := Fr.dK_mul (a / b) b
  rw [hab] at h
  rw [eq_div_iff (pow_ne_zero 2 hb)]
  linear_combination -b * h - Fr.dK b * hab

/-- With a constant multiplier the inhomogeneity of the normalised second jet is the logarithmic
derivative of the chain-rule factor. -/
theorem normalizedSecondJet_coeff {q : K} (hq : q ≠ 0) (hqconst : Fr.dK q = 0) :
    Fr.ρ * Fr.dK (q / Fr.ρ) / q = -(Fr.dK Fr.ρ / Fr.ρ) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  rw [Fr.dK_div hρ0, hqconst]
  field_simp
  ring

end RittFrame

/-- **A rational second jet is a rational affine connection.**  If the first two jets of a
linearizer are independent and the second jet lies in the field they generate, the base carries a
solution of `ψ(a)·ρ = a − dK ρ / ρ` — the rational affine-connection equation. -/
theorem exists_affineConnection_of_secondJet_mem
    {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)
    {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0) (hq : q ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (hτtr : Transcendental K τ)
    (hdτtr : Transcendental ↥(IntermediateField.adjoin K ({τ} : Set L)) (Fr.d τ))
    (hmem : Fr.d (Fr.d τ) ∈ IntermediateField.adjoin K ({τ, Fr.d τ} : Set L)) :
    ∃ a : K, Fr.ψ a * Fr.ρ = a - Fr.dK Fr.ρ / Fr.ρ := by
  classical
  set E₀ : IntermediateField K L := IntermediateField.adjoin K ({τ} : Set L) with hE₀
  have hτE : τ ∈ E₀ := IntermediateField.subset_adjoin K _ (by simp)
  have hE₀σ : ∀ x ∈ E₀, Fr.σ x ∈ E₀ := by
    refine Fr.sigma_mem_of_mem_adjoin ?_
    intro x hx
    rw [show x = τ by simpa using hx, hshift]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) hτE
  set φ₀ : ↥E₀ →+* ↥E₀ :=
    { toFun := fun a => ⟨Fr.σ (a : L), hE₀σ (a : L) a.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp } with hφ₀
  have hcomp₀ : ∀ a : ↥E₀, Fr.σ (algebraMap ↥E₀ L a) = algebraMap ↥E₀ L (φ₀ a) := fun _ => rfl
  -- the jet ratio
  set s : L := τ / Fr.d τ with hs
  have hs0 : s ≠ 0 := div_ne_zero hτ hdτ
  have hdτs : Fr.d τ = τ / s := by rw [hs]; field_simp
  set ρ₀ : ↥E₀ := ⟨algebraMap K L Fr.ρ, IntermediateField.algebraMap_mem _ _⟩ with hρ₀
  have hρ₀0 : ρ₀ ≠ 0 := by
    intro h
    have : algebraMap K L Fr.ρ = 0 := congrArg Subtype.val h
    exact ((map_ne_zero_iff _ (algebraMap K L).injective).mpr Fr.ρ_ne) this
  have hσs : Fr.σ s = algebraMap ↥E₀ L ρ₀ * s :=
    Fr.sigma_jetRatio hτ hdτ hq hqconst hshift
  -- the jet ratio is transcendental over the first prefix field
  have hstr : Transcendental ↥E₀ s := by
    intro halg
    refine hdτtr ?_
    have hτalg : IsAlgebraic ↥E₀ τ := isAlgebraic_algebraMap (⟨τ, hτE⟩ : ↥E₀)
    have : IsAlgebraic ↥E₀ (τ * s⁻¹) := hτalg.mul halg.inv
    rw [hdτs, div_eq_mul_inv]
    exact this
  -- the normalised second jet lies in the simple extension by the jet ratio
  set W : L := Fr.d (Fr.d τ) * τ / (Fr.d τ) ^ (2 : ℕ) with hW
  have hsmem : s ∈ IntermediateField.adjoin ↥E₀ ({s} : Set L) :=
    IntermediateField.subset_adjoin _ _ (by simp)
  have hτmem : τ ∈ IntermediateField.adjoin ↥E₀ ({s} : Set L) := by
    have h := (IntermediateField.adjoin ↥E₀ ({s} : Set L)).algebraMap_mem ⟨τ, hτE⟩
    simpa using h
  have hdτmem : Fr.d τ ∈ IntermediateField.adjoin ↥E₀ ({s} : Set L) := by
    rw [hdτs]
    exact div_mem hτmem hsmem
  have hddmem : Fr.d (Fr.d τ) ∈ IntermediateField.adjoin ↥E₀ ({s} : Set L) := by
    have hle : IntermediateField.adjoin K ({τ, Fr.d τ} : Set L)
        ≤ (IntermediateField.adjoin ↥E₀ ({s} : Set L)).restrictScalars K := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact hτmem
      · rw [show x = Fr.d τ by simpa using hx]; exact hdτmem
    exact hle hmem
  have hWmem : W ∈ IntermediateField.adjoin ↥E₀ ({s} : Set L) := by
    rw [hW, div_eq_mul_inv]
    exact mul_mem (mul_mem hddmem hτmem) (inv_mem (pow_mem hdτmem 2))
  -- the first descent, in the jet ratio over the first prefix field
  set β : K := Fr.ρ * Fr.dK (q / Fr.ρ) / q with hβ
  set β₀ : ↥E₀ := ⟨algebraMap K L β, IntermediateField.algebraMap_mem _ _⟩ with hβ₀
  have hrel : Fr.σ W = W + algebraMap ↥E₀ L β₀ * s :=
    Fr.sigma_normalizedSecondJet hτ hdτ hq hqconst hshift
  obtain ⟨a, ha⟩ :=
    exists_shift_solution_of_mem_adjoin Fr.σ φ₀ hcomp₀ hstr hρ₀0 hσs hWmem hrel
  -- the second descent, in the linearizer over the base
  have haL : algebraMap K L Fr.ρ * Fr.σ (a : L) = (a : L) + algebraMap K L β := by
    have h := congrArg (fun z : ↥E₀ => (z : L)) ha
    simp only [hφ₀, hρ₀, hβ₀] at h
    push_cast at h
    linear_combination h
  have hamem : (a : L) ∈ IntermediateField.adjoin K ({τ} : Set L) := a.2
  obtain ⟨a₀, ha₀⟩ :=
    exists_eigen_shift_solution_of_mem_adjoin Fr.σ Fr.ψ Fr.comp hτtr (μ := q) (ν := Fr.ρ) hq
      hshift hamem haL
  refine ⟨a₀, ?_⟩
  rw [hβ, Fr.normalizedSecondJet_coeff hq hqconst] at ha₀
  linear_combination ha₀

end GaloisForLFunctions.HTGeometry
