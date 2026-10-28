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
    · rw [hI, map_mul, Nat.cast_mul, mul_comm] at hx
      exact le_of_mul_le_mul_right hx hN𝔟

omit [NumberField K] in
omit [NumberField K] in
variable (𝔪) in
/-- Every residue modulo `𝔪₀` has a representative in `𝔟` when `𝔟 + 𝔪₀ = (1)`. -/
theorem exists_mem_mk_eq (h𝔟 : 𝔟 ⊔ 𝔪.fin = ⊤) (ρ : 𝓞 K ⧸ 𝔪.fin) :
    ∃ β ∈ 𝔟, Ideal.Quotient.mk 𝔪.fin β = ρ := by
  obtain ⟨β₀, rfl⟩ := Ideal.Quotient.mk_surjective ρ
  have h1 : (1 : 𝓞 K) ∈ 𝔟 ⊔ 𝔪.fin := by
    rw [h𝔟]
    exact Submodule.mem_top
  obtain ⟨b, hb, m, hm, hbm⟩ := Submodule.mem_sup.mp h1
  refine ⟨β₀ * b, Ideal.mul_mem_left _ _ hb, ?_⟩
  rw [Ideal.Quotient.eq, show β₀ * b - β₀ = -(β₀ * m) by linear_combination β₀ * hbm]
  exact neg_mem (Ideal.mul_mem_left _ _ hm)

variable (𝔪) in
/-- A representative in `𝔟` of a residue modulo `𝔪₀`. -/
def residueRep (h𝔟 : 𝔟 ⊔ 𝔪.fin = ⊤) (ρ : 𝓞 K ⧸ 𝔪.fin) : 𝓞 K :=
  (exists_mem_mk_eq 𝔪 h𝔟 ρ).choose

theorem residueRep_mem (ρ : 𝓞 K ⧸ 𝔪.fin) : residueRep 𝔪 h𝔟 ρ ∈ 𝔟 :=
  (exists_mem_mk_eq 𝔪 h𝔟 ρ).choose_spec.1

theorem mk_residueRep (ρ : 𝓞 K ⧸ 𝔪.fin) :
    Ideal.Quotient.mk 𝔪.fin (residueRep 𝔪 h𝔟 ρ) = ρ :=
  (exists_mem_mk_eq 𝔪 h𝔟 ρ).choose_spec.2

/-- The points of `Λ_{𝔪₀𝔟}` are the `e(y)`, `y ∈ 𝔪₀𝔟`. -/
theorem mem_idealLattice_mul {x : mixedSpace K} :
    x ∈ idealLattice K (idealUnit (mul_ne_zero 𝔪.fin_ne_bot h𝔟0)) ↔
      ∃ y ∈ 𝔪.fin * 𝔟, mixedEmbedding K (y : K) = x := by
  simp only [mem_idealLattice, SetLike.mem_coe, coe_idealUnit, mem_coeIdeal]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩

omit [NumberField K] in
theorem smul_mem_signRegion_iff {S : Set {w : InfinitePlace K // w.IsReal}} {σ : S → ℤˣ} {t : ℝ}
    (ht : 0 < t) {x : mixedSpace K} : t • x ∈ signRegion S σ ↔ x ∈ signRegion S σ := by
  simp only [signRegion, mem_setOf_eq, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun w => by rw [mul_left_comm, mul_pos_iff_of_pos_left ht]

/-- `T^{1/n} Y_σ` is the set of cone points of norm `≤ T` with signs `σ`. -/
theorem mem_smul_signedNormBall {T : ℝ} (hT : 0 < T) {S : Set {w : InfinitePlace K // w.IsReal}}
    {σ : S → ℤˣ} {x : mixedSpace K} :
    x ∈ (T ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall S σ ↔
      x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ T ∧ x ∈ signRegion S σ := by
  have ht : 0 < T ^ ((finrank ℚ K : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  rw [signedNormBall, smul_set_inter₀ ht.ne', ← setOf_norm_le_eq_smul hT, mem_inter_iff,
    mem_setOf_eq, mem_smul_set_iff_inv_smul_mem₀ ht.ne', smul_mem_signRegion_iff (inv_pos.mpr ht),
    and_assoc]

variable (𝔪) in
/-- The cone points `e(γ)` with `N(γ) ≤ T` and residue/sign data `g`. -/
def conePoints (𝔟 : Ideal (𝓞 K)) (g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) (T : ℝ) :
    Set (mixedSpace K) :=
  {a | a ∈ fundamentalCone K ∧ ∃ γ : 𝓞 K, mixedEmbedding K (γ : K) = a ∧
    (Ideal.absNorm (Ideal.span {γ}) : ℝ) ≤ T ∧ ElemCond 𝔪 𝔟 g γ}

omit [NumberField K] in
omit [NumberField K] in
/-- `γ` determines its data `g`. -/
theorem elemCond_unique {g g' : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)} {γ : 𝓞 K}
    (h : ElemCond 𝔪 𝔟 g γ) (h' : ElemCond 𝔪 𝔟 g' γ) : g = g' := by
  refine Prod.ext (Units.ext (h.2.1.symm.trans h'.2.1)) (funext fun w => ?_)
  have h1 := h.2.2 w
  have h2 := h'.2.2 w
  rcases Int.units_eq_one_or (g.2 w) with e | e <;> rcases Int.units_eq_one_or (g'.2 w) with e' | e'
    <;> rw [e, e'] <;> rw [e] at h1 <;> rw [e'] at h2 <;> simp at h1 h2 <;> linarith

/-- **Cone points with fixed data form a lattice coset**: with `β ∈ 𝔟`, `β ≡ ρ mod 𝔪₀`, the
cone points with data `g = (ρ, σ)` and norm `≤ T` are `e(β) + ((−e(β) + T^{1/n} Y_σ) ∩ Λ_{𝔪₀𝔟})`. -/
theorem conePoints_eq_image {g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)} {T : ℝ} (hT : 0 < T) :
    conePoints 𝔪 𝔟 g T = (mixedEmbedding K (residueRep 𝔪 h𝔟 g.1 : K) + ·) ''
      ((-mixedEmbedding K (residueRep 𝔪 h𝔟 g.1 : K) +ᵥ
        (T ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall 𝔪.inf g.2) ∩
          (idealLattice K (idealUnit (mul_ne_zero 𝔪.fin_ne_bot h𝔟0)) : Set (mixedSpace K))) := by
  set β := residueRep 𝔪 h𝔟 g.1
  have hβ : β ∈ 𝔟 := residueRep_mem h𝔟 _
  have hβg : Ideal.Quotient.mk 𝔪.fin β = g.1 := mk_residueRep h𝔟 _
  have hinf : 𝔪.fin * 𝔟 = 𝔪.fin ⊓ 𝔟 :=
    Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm, h𝔟]))
  ext a
  simp only [conePoints, mem_setOf_eq, mem_image, mem_inter_iff, mem_vadd_set_iff_neg_vadd_mem,
    neg_neg, vadd_eq_add, SetLike.mem_coe, mem_idealLattice_mul h𝔟0, mem_smul_signedNormBall hT,
    signRegion]
  constructor
  · rintro ⟨hcone, γ, rfl, hN, hγ𝔟, hres, hsign⟩
    have hy : γ - β ∈ 𝔪.fin * 𝔟 := by
      rw [hinf]
      refine ⟨?_, sub_mem hγ𝔟 hβ⟩
      rw [SetLike.mem_coe, ← Ideal.Quotient.eq, hres, hβg]
    have he : mixedEmbedding K (β : K) + mixedEmbedding K ((γ - β : 𝓞 K) : K) =
        mixedEmbedding K (γ : K) := by
      rw [← map_add]
      congr 1
      push_cast
      ring
    refine ⟨mixedEmbedding K ((γ - β : 𝓞 K) : K), ⟨?_, γ - β, hy, rfl⟩, he⟩
    rw [he, norm_mixedEmbedding_eq_absNorm]
    exact ⟨hcone, hN, fun w => by simpa [mixedEmbedding_apply_isReal] using hsign w⟩
  · rintro ⟨z, ⟨⟨hcone, hN, hsign⟩, y, hy, rfl⟩, rfl⟩
    have he : mixedEmbedding K (β : K) + mixedEmbedding K (y : K) =
        mixedEmbedding K ((β + y : 𝓞 K) : K) := by
      rw [← map_add]
      push_cast
      rfl
    rw [he] at hcone hN hsign ⊢
    rw [norm_mixedEmbedding_eq_absNorm] at hN
    refine ⟨hcone, β + y, rfl, hN, add_mem hβ (Ideal.mul_le_left hy), ?_, fun w => ?_⟩
    · rw [map_add, hβg, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hy), add_zero]
    · simpa [mixedEmbedding_apply_isReal] using hsign w

/-- The number of cone points with data `g` is a lattice count in a translated signed ball. -/
theorem ncard_conePoints {g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)} {T : ℝ} (hT : 0 < T) :
    (conePoints 𝔪 𝔟 g T).ncard =
      ((-mixedEmbedding K (residueRep 𝔪 h𝔟 g.1 : K) +ᵥ
        (T ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall 𝔪.inf g.2) ∩
          (idealLattice K (idealUnit (mul_ne_zero 𝔪.fin_ne_bot h𝔟0)) :
            Set (mixedSpace K))).ncard := by
  rw [conePoints_eq_image h𝔟0 h𝔟 hT, ncard_image_of_injective _ (add_right_injective _)]

include h𝔟0 h𝔟 in
include h𝔟0 h𝔟 in
theorem finite_conePoints {g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)} {T : ℝ} (hT : 0 < T) :
    (conePoints 𝔪 𝔟 g T).Finite := by
  rw [conePoints_eq_image h𝔟0 h𝔟 hT]
  refine Finite.image _ (finite_inter_lattice _ ?_)
  exact (((isBounded_normLeOne K).subset inter_subset_left).smul₀ _).vadd _

noncomputable instance : Fintype (rayHom 𝔪).range := Fintype.ofFinite _

noncomputable instance : Fintype (rayHom 𝔪).range := Fintype.ofFinite _

/-- **Ray class cone points split by their data**: with `T = x N𝔟`, the cone points
`e(γ)`, `(γ) = 𝔞𝔟`, `𝔞 ∈ c`, `N𝔞 ≤ x`, are the disjoint union over `g ∈ rayHom(K_𝔪)` with
`φ(g) = c [𝔟]` of the cone points with data `g` and norm `≤ T`. -/
theorem setOf_rayClassIdeals_eq_biUnion (x : ℝ) :
    {a : mixedSpace K | a ∈ integerSet K ∧ ∃ γ : 𝓞 K, mixedEmbedding K γ = a ∧
        ∃ I ∈ rayClassIdeals 𝔪 c x, Ideal.span {γ} = I * 𝔟} =
      ⋃ g ∈ ((Finset.univ.filter fun g : (rayHom 𝔪).range => rayResidueClass 𝔪 g =
          c * rayClass 𝔪 ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩ :
            Finset _) : Set _),
        conePoints 𝔪 𝔟 g.1 (x * Ideal.absNorm 𝔟) := by
  ext a
  simp only [mem_setOf_eq, mem_iUnion, Finset.coe_filter, Finset.mem_univ, true_and,
    exists_prop, mem_integerSet, conePoints]
  constructor
  · rintro ⟨⟨hcone, -⟩, γ, rfl, h⟩
    have hγ0 : algebraMap (𝓞 K) K γ ≠ 0 := by
      intro h0
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
      have := normAtPlace_pos_of_mem hcone w
      rw [show (γ : K) = algebraMap (𝓞 K) K γ from rfl, h0] at this
      simp at this
    obtain ⟨hN, g, hg, hE⟩ := (exists_rayClassIdeal_iff h𝔟0 h𝔟 hγ0).mp h
    exact ⟨g, hg, hcone, γ, rfl, hN, hE⟩
  · rintro ⟨g, hg, hcone, γ, rfl, hN, hE⟩
    have hγ0 : algebraMap (𝓞 K) K γ ≠ 0 := by
      intro h0
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
      have := normAtPlace_pos_of_mem hcone w
      rw [show (γ : K) = algebraMap (𝓞 K) K γ from rfl, h0] at this
      simp at this
    exact ⟨⟨hcone, γ, rfl⟩, γ, rfl, (exists_rayClassIdeal_iff h𝔟0 h𝔟 hγ0).mpr ⟨hN, g, hg, hE⟩⟩

/-- **Ray class counts are sums of lattice-coset counts**: for `x > 0`, `T = x N𝔟`,
`#{𝔞 ∈ c : N𝔞 ≤ x} · w = Σ_{φ(g) = c [𝔟]} #((−e(β_g) + T^{1/n} Y_{σ_g}) ∩ Λ_{𝔪₀𝔟})`. -/
theorem ncard_rayClassIdeals_mul_torsionOrder_eq_sum
    (h𝔟c : ClassGroup.mk K (idealUnit h𝔟0) = (toClassGroup 𝔪 c)⁻¹) {x : ℝ} (hx : 0 < x) :
    (rayClassIdeals 𝔪 c x).ncard * torsionOrder K =
      ∑ g ∈ (Finset.univ.filter fun g : (rayHom 𝔪).range => rayResidueClass 𝔪 g =
          c * rayClass 𝔪 ⟨idealUnit h𝔟0, (idealUnit_mem_idealGroup_iff 𝔪 h𝔟0).mpr h𝔟⟩),
        ((-mixedEmbedding K (residueRep 𝔪 h𝔟 g.1.1 : K) +ᵥ
          ((x * Ideal.absNorm 𝔟) ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall 𝔪.inf g.1.2) ∩
            (idealLattice K (idealUnit (mul_ne_zero 𝔪.fin_ne_bot h𝔟0)) :
              Set (mixedSpace K))).ncard := by
  have hT : 0 < x * Ideal.absNorm 𝔟 := mul_pos hx (by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.mp h)))
  rw [ncard_rayClassIdeals_mul_torsionOrder h𝔟0 h𝔟c, setOf_rayClassIdeals_eq_biUnion h𝔟0 h𝔟,
    Finite.ncard_biUnion (Finset.finite_toSet _) (fun g _ => finite_conePoints h𝔟0 h𝔟 hT),
    finsum_mem_coe_finset]
  · exact Finset.sum_congr rfl fun g _ => ncard_conePoints h𝔟0 h𝔟 hT
  · intro g _ g' _ hne
    refine disjoint_left.mpr ?_
    rintro a ⟨-, γ, rfl, -, hE⟩ ⟨-, γ', hγ', -, hE'⟩
    have hγγ' : γ' = γ := RingOfIntegers.coe_injective (mixedEmbedding_injective K hγ')
    exact hne (Subtype.ext (elemCond_unique hE (hγγ' ▸ hE')))

end GaloisForLFunctions.HeckeLFunctions
