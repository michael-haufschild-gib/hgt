import GaloisForLFunctions.HeckeLFunctions.IdealsOfARayClassAreConePoints
import GaloisForLFunctions.HeckeLFunctions.LatticeCosetsInSignedNormBalls

/-!
# Cone points of a ray class are lattice cosets

For a ray class `c`, an integral `𝔟` prime to `𝔪` in the inverse ideal class, `r = [𝔟]` in `Cl_𝔪`
and `T = x N𝔟`, a cone point `e(γ)` has `(γ) = 𝔞𝔟` with `𝔞 ∈ c`, `N𝔞 ≤ x` iff `N(γ) ≤ T` and
`γ` has residue/sign data `g ∈ rayHom(K_𝔪)` with `φ(g) = c r` (`exists_rayClassIdeal_iff`). For
fixed data `g = (ρ, σ)` these points are the lattice coset `e(β_g) + Λ_{𝔪𝔟}` inside the dilate
`T^{1/n} Y_σ` of a signed norm ball (`setOf_elemCond_eq`), so
`#{𝔞 ∈ c : N𝔞 ≤ x} · w = Σ_{φ(g) = c r} #((−e(β_g) + T^{1/n} Y_{σ_g}) ∩ Λ_{𝔪𝔟})`
(`ncard_rayClassIdeals_mul_torsionOrder_eq_sum`).
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal Set
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone NumberField.Units Module
open scoped Classical nonZeroDivisors Pointwise

namespace GaloisForLFunctions.HeckeLFunctions

open GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- `γ` lies in `𝔟`, has residue `g.1` modulo `𝔪₀` and signs `g.2` at `𝔪∞`. -/
def ElemCond (𝔟 : Ideal (𝓞 K)) (g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) (γ : 𝓞 K) : Prop :=
  γ ∈ 𝔟 ∧ Ideal.Quotient.mk 𝔪.fin γ = g.1 ∧
    ∀ w : 𝔪.inf, 0 < ((g.2 w : ℤ) : ℝ) * InfinitePlace.embedding_of_isReal w.1.2 (γ : K)

omit [NumberField K] in
/-- The signs of `α` at `𝔪∞` are `σ` iff `σ_w w(α) > 0` for every `w ∈ 𝔪∞`. -/
theorem signAtInf_eq_iff (α : Kˣ) (σ : 𝔪.inf → ℤˣ) :
    signAtInf 𝔪 α = σ ↔ ∀ w : 𝔪.inf,
      0 < ((σ w : ℤ) : ℝ) * InfinitePlace.embedding_of_isReal w.1.2 (α : K) := by
  rw [funext_iff]
  refine forall_congr' fun w => ?_
  have he : InfinitePlace.embedding_of_isReal w.1.2 (α : K) ≠ 0 := by simp
  rw [signAtInf_apply]
  rcases Int.units_eq_one_or (σ w) with h | h <;> rw [h] <;>
    rcases he.lt_or_gt with h' | h' <;> simp [h', not_lt.mpr h'.le]

/-- The norm of a cone point `e(γ)` is `N(γ)`. -/
theorem norm_mixedEmbedding_eq_absNorm (γ : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K (γ : K)) = (Ideal.absNorm (Ideal.span {γ}) : ℝ) := by
  rw [norm_eq_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  push_cast
  simp [Nat.cast_natAbs, Int.cast_abs]

variable {𝔪} {c : RayClassGroup 𝔪} {𝔟 : Ideal (𝓞 K)} (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟 : 𝔟 ⊔ 𝔪.fin = ⊤)

/-- `(γ)` as a unit fractional ideal is `toPrincipalIdeal γ`. -/
theorem idealUnit_span_eq {γ : 𝓞 K} (hγ0 : algebraMap (𝓞 K) K γ ≠ 0)
    (hγ : Ideal.span {γ} ≠ ⊥) :
    idealUnit hγ = toPrincipalIdeal (𝓞 K) K (Units.mk0 _ hγ0) :=
  Units.ext (by rw [coe_idealUnit, coe_toPrincipalIdeal, Units.val_mk0, coeIdeal_span_singleton])

/-- **The ray class condition at cone points**: `(γ) = 𝔞𝔟` with `𝔞 ∈ c`, `N𝔞 ≤ x` iff
`N(γ) ≤ x N𝔟` and the residue/sign data `g` of `γ` has `φ(g) = c [𝔟]`. -/
theorem exists_rayClassIdeal_iff {x : ℝ} {γ : 𝓞 K} (hγ0 : algebraMap (𝓞 K) K γ ≠ 0) :
    (∃ I ∈ rayClassIdeals 𝔪 c x, Ideal.span {γ} = I * 𝔟) ↔
      (Ideal.absNorm (Ideal.span {γ}) : ℝ) ≤ x * Ideal.absNorm 𝔟 ∧
        ∃ g : (rayHom 𝔪).range, rayResidueClass 𝔪 g =
          c * rayClass 𝔪 ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩ ∧
          ElemCond 𝔪 𝔟 g.1 γ := by
  have hspan0 : Ideal.span {γ} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact hγ0 (map_zero _)
  have hN𝔟 : (0 : ℝ) < Ideal.absNorm 𝔟 := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.mp h))
  constructor
  · rintro ⟨I, ⟨hI0, hm, hc, hx⟩, hspan⟩
    -- `γ` is prime to `𝔪`
    have hsup : Ideal.span {γ} ⊔ 𝔪.fin = ⊤ := by
      rw [hspan, ← Ideal.isCoprime_iff_sup_eq]
      exact (Ideal.isCoprime_iff_sup_eq.mpr ((idealUnit_mem_idealGroup_iff 𝔪 hI0).mp hm)).mul_left
        (Ideal.isCoprime_iff_sup_eq.mpr h𝔟)
    have hγ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → γ ∉ v.asIdeal := fun v hv hγv =>
      v.isPrime.ne_top (eq_top_iff.mpr (hsup ▸ sup_le
        ((Ideal.span_singleton_le_iff_mem _).mpr hγv) (Ideal.dvd_iff_le.mp hv)))
    refine ⟨?_, ⟨rayHom 𝔪 ⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩, _, rfl⟩, ?_, ?_⟩
    · rw [hspan, map_mul, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)
    · rw [rayResidueClass_apply, rayClassOfElt, MonoidHom.comp_apply, ← hc, ← map_mul]
      congr 1
      apply Subtype.ext
      show toPrincipalIdeal (𝓞 K) K (Units.mk0 _ hγ0) = idealUnit hI0 * idealUnit h𝔟0
      rw [← idealUnit_span_eq hγ0 hspan0, ← idealUnit_mul hI0 h𝔟0]
      exact Units.ext (by rw [coe_idealUnit, coe_idealUnit, hspan])
    · show ElemCond 𝔪 𝔟 (rayHom 𝔪 ⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩) γ
      rw [rayHom_algebraMap 𝔪 hγ0 hγ]
      have hγI : γ ∈ I * 𝔟 := hspan ▸ Ideal.mem_span_singleton_self γ
      refine ⟨Ideal.mul_le_left hγI, rfl, ?_⟩
      exact (signAtInf_eq_iff 𝔪 _ _).mp rfl
  · rintro ⟨hx, g, hg, hγ𝔟, hres, hsign⟩
    have hunit : IsUnit (Ideal.Quotient.mk 𝔪.fin γ) := hres ▸ g.1.1.isUnit
    have hγ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.fin → γ ∉ v.asIdeal :=
      fun v hv => not_mem_of_isUnit_mk 𝔪 hunit v hv
    have hrh : rayHom 𝔪 ⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩ = g.1 := by
      rw [rayHom_algebraMap 𝔪 hγ0 hγ]
      refine Prod.ext (Units.ext ?_) ((signAtInf_eq_iff 𝔪 _ _).mpr hsign)
      rw [coe_unitMod, hres]
    obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hγ𝔟)
    have hI0 : I ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot] at hI
      exact hspan0 hI
    have hsupγ : Ideal.span {γ} ⊔ 𝔪.fin = ⊤ := by
      obtain ⟨s, hs⟩ := hunit.exists_right_inv
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔪.fin), Ideal.Quotient.eq] at hs
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have h1 : γ * s ∈ Ideal.span {γ} ⊔ 𝔪.fin :=
        Ideal.mem_sup_left (Ideal.mul_mem_right s _ (Ideal.mem_span_singleton_self γ))
      have h2 : γ * s - 1 ∈ Ideal.span {γ} ⊔ 𝔪.fin := Ideal.mem_sup_right hs
      simpa using sub_mem h1 h2
    have hIm : idealUnit hI0 ∈ idealGroup 𝔪 := by
      rw [idealUnit_mem_idealGroup_iff]
      exact eq_top_iff.mpr (hsupγ ▸ sup_le_sup_right (hI ▸ Ideal.mul_le_left) _)
    refine ⟨I, ⟨hI0, hIm, ?_, ?_⟩, by rw [hI, mul_comm]⟩
    · -- `[(γ)] = [𝔞] [𝔟]`
      have h1 : rayResidueClass 𝔪 g = rayClass 𝔪 ⟨idealUnit hI0, hIm⟩ *
          rayClass 𝔪 ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩ := by
        have hg' : g = ⟨rayHom 𝔪 ⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩, _, rfl⟩ :=
          Subtype.ext hrh.symm
        rw [hg', rayResidueClass_apply, rayClassOfElt, MonoidHom.comp_apply, ← map_mul]
        congr 1
        apply Subtype.ext
        show toPrincipalIdeal (𝓞 K) K (Units.mk0 _ hγ0) = idealUnit hI0 * idealUnit h𝔟0
        rw [← idealUnit_span_eq hγ0 hspan0, ← idealUnit_mul hI0 h𝔟0]
        exact Units.ext (by rw [coe_idealUnit, coe_idealUnit, hI, mul_comm])
      rw [hg] at h1
      have h2 := congrArg (· * (rayClass 𝔪
        ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩)⁻¹) h1
      simp only [mul_inv_cancel_right] at h2
      exact h2.symm
    · rw [hI, map_mul, Nat.cast_mul] at hx
      exact le_of_mul_le_mul_right hx hN𝔟

end GaloisForLFunctions.HeckeLFunctions
