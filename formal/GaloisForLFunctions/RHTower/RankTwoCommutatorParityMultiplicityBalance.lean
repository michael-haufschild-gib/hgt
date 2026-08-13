import Mathlib

/-!
# Rank-two commutator parity-multiplicity balance

For a reflection-invariant symmetric operator whose commutator with the reflection-odd frequency
operator has the Connes--van Suijlekom rank-two form `[D,Q] = |β⟩⟨η| - |η⟩⟨β|` with even `η` and
odd `β`, the even and odd multiplicities of every real eigenvalue differ by at most one.  The
frequency map sends an even eigenvector annihilated by the single functional `⟨η,·⟩` to an odd
eigenvector of the same eigenvalue and conversely, and each restriction is injective under the
literal kernel conditions of the truncated model; a one-functional kernel loses at most one
dimension.  Consequently an eigenvalue lying strictly below the opposite-parity Rayleigh floor is
automatically simple, and a zero-mode/odd-level pair carries the exact reciprocal gap current
`⟨Df,g⟩ = -1/λ`.
-/

open scoped RealInnerProductSpace
open Submodule

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The rank-two commutator relation `[D,Q] = |β⟩⟨η| - |η⟩⟨β|`. -/
def RankTwoCommutator (D Q : H →ₗ[ℝ] H) (η β : H) : Prop :=
  ∀ f : H, D (Q f) - Q (D f) = ⟪η, f⟫ • β - ⟪β, f⟫ • η

/-- Even eigenspace of `Q` at `λ` for the reflection `Γ`. -/
def evenEigenspace (Q Γ : H →ₗ[ℝ] H) (lam : ℝ) : Submodule ℝ H where
  carrier := {f | Q f = lam • f ∧ Γ f = f}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨by rw [map_add, hf1, hg1, smul_add], by rw [map_add, hf2, hg2]⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨by rw [map_smul, hf1, smul_comm], by rw [map_smul, hf2]⟩

/-- Odd eigenspace of `Q` at `λ` for the reflection `Γ`. -/
def oddEigenspace (Q Γ : H →ₗ[ℝ] H) (lam : ℝ) : Submodule ℝ H where
  carrier := {f | Q f = lam • f ∧ Γ f = -f}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨by rw [map_add, hf1, hg1, smul_add], by rw [map_add, hf2, hg2]; abel⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨by rw [map_smul, hf1, smul_comm], by rw [map_smul, hf2, smul_neg]⟩

omit [FiniteDimensional ℝ H] in
@[simp] theorem mem_evenEigenspace {Q Γ : H →ₗ[ℝ] H} {lam : ℝ} {f : H} :
    f ∈ evenEigenspace Q Γ lam ↔ Q f = lam • f ∧ Γ f = f := Iff.rfl

omit [FiniteDimensional ℝ H] in
@[simp] theorem mem_oddEigenspace {Q Γ : H →ₗ[ℝ] H} {lam : ℝ} {f : H} :
    f ∈ oddEigenspace Q Γ lam ↔ Q f = lam • f ∧ Γ f = -f := Iff.rfl

section Parity

variable {Γ : H →ₗ[ℝ] H}
variable (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)

omit [FiniteDimensional ℝ H] in
/-- An even and an odd vector are orthogonal for a symmetric involution. -/
theorem inner_eq_zero_of_even_odd (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    {u v : H} (hu : Γ u = u) (hv : Γ v = -v) : ⟪v, u⟫ = 0 := by
  have h := hΓsym v u
  rw [hv, hu] at h
  have : -⟪v, u⟫ = ⟪v, u⟫ := by
    rw [← inner_neg_left]
    exact h
  linarith

end Parity

section Balance

variable {D Q Γ : H →ₗ[ℝ] H} {η β : H} {lam : ℝ}

omit [FiniteDimensional ℝ H] in
/-- The frequency image of an even eigenvector killed by the source functional is an odd
eigenvector. -/
theorem frequency_maps_even_to_odd
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hβ : Γ β = -β)
    {f : H} (hf : f ∈ evenEigenspace Q Γ lam) (hηf : ⟪η, f⟫ = 0) :
    D f ∈ oddEigenspace Q Γ lam := by
  obtain ⟨hQf, hΓf⟩ := hf
  have hβf : ⟪β, f⟫ = 0 := inner_eq_zero_of_even_odd hΓsym hΓf hβ
  have hDQ := hcomm f
  rw [hηf, hβf, zero_smul, zero_smul, sub_zero, sub_eq_zero] at hDQ
  constructor
  · rw [← hDQ, hQf, map_smul]
  · have hDf := hanti f
    rw [hΓf] at hDf
    have hneg := congrArg (fun x : H => -x) hDf
    simpa using hneg.symm

omit [FiniteDimensional ℝ H] in
/-- The frequency image of an odd eigenvector killed by the odd source functional is an even
eigenvector. -/
theorem frequency_maps_odd_to_even
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hη : Γ η = η)
    {g : H} (hg : g ∈ oddEigenspace Q Γ lam) (hβg : ⟪β, g⟫ = 0) :
    D g ∈ evenEigenspace Q Γ lam := by
  obtain ⟨hQg, hΓg⟩ := hg
  have hηg : ⟪η, g⟫ = 0 := by
    have h := hΓsym η g
    rw [hη, hΓg] at h
    have h2 : ⟪η, g⟫ = -⟪η, g⟫ := by
      rw [← inner_neg_right]
      exact h
    linarith
  have hDQ := hcomm g
  rw [hηg, hβg, zero_smul, zero_smul, sub_zero, sub_eq_zero] at hDQ
  constructor
  · rw [← hDQ, hQg, map_smul]
  · have := hanti g
    rw [hΓg, map_neg] at this
    rw [← neg_neg (Γ (D g)), ← this, neg_neg]

/-- One-functional codimension bound: intersecting with the kernel of a single inner-product
functional loses at most one dimension. -/
theorem finrank_inf_ker_functional_ge (E : Submodule ℝ H) (w : H) :
    Module.finrank ℝ E ≤
      Module.finrank ℝ ↥(E ⊓ (LinearMap.ker (innerSL ℝ w : H →L[ℝ] ℝ).toLinearMap :
        Submodule ℝ H)) + 1 := by
  classical
  set L : Submodule ℝ H := LinearMap.ker (innerSL ℝ w : H →L[ℝ] ℝ).toLinearMap with hLdef
  set φ : E →ₗ[ℝ] ℝ := ((innerSL ℝ w : H →L[ℝ] ℝ).toLinearMap).comp E.subtype with hφdef
  have hmem : ∀ y : E, y ∈ LinearMap.ker φ ↔ (y : H) ∈ L := by
    intro y
    simp [hφdef, hLdef, LinearMap.mem_ker]
  have hmap : Submodule.map E.subtype (LinearMap.ker φ) = E ⊓ L := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hmem y).1 hy⟩
    · rintro ⟨hxE, hxL⟩
      exact ⟨⟨x, hxE⟩, (hmem ⟨x, hxE⟩).2 hxL, rfl⟩
  have hkereq : Module.finrank ℝ ↥(LinearMap.ker φ) = Module.finrank ℝ ↥(E ⊓ L) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective E.subtype E.injective_subtype
      (LinearMap.ker φ)).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank ℝ ↥(LinearMap.range φ) ≤ 1 := by
    have hle := Submodule.finrank_le (LinearMap.range φ)
    simpa using hle
  omega

/-- **Parity-multiplicity balance, even side.**  The even multiplicity exceeds the odd
multiplicity by at most one. -/
theorem finrank_evenEigenspace_le
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hβ : Γ β = -β)
    (hkerEven : ∀ f : H, Γ f = f → ⟪η, f⟫ = 0 → D f = 0 → f = 0) :
    Module.finrank ℝ (evenEigenspace Q Γ lam) ≤
      Module.finrank ℝ (oddEigenspace Q Γ lam) + 1 := by
  classical
  have hcut := finrank_inf_ker_functional_ge (evenEigenspace Q Γ lam) η
  have hmaps : ∀ x ∈ (evenEigenspace Q Γ lam ⊓
      (LinearMap.ker (innerSL ℝ η : H →L[ℝ] ℝ).toLinearMap : Submodule ℝ H)),
      D x ∈ oddEigenspace Q Γ lam := by
    intro x hx
    obtain ⟨hxE, hxK⟩ := Submodule.mem_inf.mp hx
    exact frequency_maps_even_to_odd hΓsym hanti hcomm hβ hxE hxK
  have hinj : Function.Injective (D.restrict hmaps) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    obtain ⟨hxE, hxK⟩ := Submodule.mem_inf.mp hx
    have hDx : D x = 0 := by
      have hv : ((D.restrict hmaps) ⟨x, hx⟩ : H) = (0 : H) := by
        rw [hker]
        rfl
      rw [LinearMap.restrict_apply] at hv
      exact hv
    exact Subtype.ext (hkerEven x hxE.2 hxK hDx)
  have hWle := LinearMap.finrank_le_finrank_of_injective hinj
  omega

/-- **Parity-multiplicity balance, odd side.**  The odd multiplicity exceeds the even
multiplicity by at most one. -/
theorem finrank_oddEigenspace_le
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hη : Γ η = η)
    (hkerOdd : ∀ g : H, Γ g = -g → D g = 0 → g = 0) :
    Module.finrank ℝ (oddEigenspace Q Γ lam) ≤
      Module.finrank ℝ (evenEigenspace Q Γ lam) + 1 := by
  classical
  have hcut := finrank_inf_ker_functional_ge (oddEigenspace Q Γ lam) β
  have hmaps : ∀ x ∈ (oddEigenspace Q Γ lam ⊓
      (LinearMap.ker (innerSL ℝ β : H →L[ℝ] ℝ).toLinearMap : Submodule ℝ H)),
      D x ∈ evenEigenspace Q Γ lam := by
    intro x hx
    obtain ⟨hxE, hxK⟩ := Submodule.mem_inf.mp hx
    exact frequency_maps_odd_to_even hΓsym hanti hcomm hη hxE hxK
  have hinj : Function.Injective (D.restrict hmaps) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    obtain ⟨hxE, _⟩ := Submodule.mem_inf.mp hx
    have hDx : D x = 0 := by
      have hv : ((D.restrict hmaps) ⟨x, hx⟩ : H) = (0 : H) := by
        rw [hker]
        rfl
      rw [LinearMap.restrict_apply] at hv
      exact hv
    exact Subtype.ext (hkerOdd x hxE.2 hDx)
  have hWle := LinearMap.finrank_le_finrank_of_injective hinj
  omega

omit [FiniteDimensional ℝ H] in
/-- Below the even Rayleigh floor the even eigenspace is trivial. -/
theorem evenEigenspace_eq_bot_of_lt_floor {α : ℝ}
    (hfloor : ∀ f : H, Γ f = f → α * ⟪f, f⟫ ≤ ⟪Q f, f⟫) (hlt : lam < α) :
    evenEigenspace Q Γ lam = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f ⟨hQf, hΓf⟩
  by_contra hne
  have hpos : 0 < ⟪f, f⟫ := real_inner_self_pos.mpr hne
  have hray : ⟪Q f, f⟫ = lam * ⟪f, f⟫ := by
    rw [hQf, real_inner_smul_left]
  have := hfloor f hΓf
  rw [hray] at this
  nlinarith

/-- **Strict parity-floor simplicity.**  An occupied odd level strictly below the even floor is
automatically simple. -/
theorem finrank_oddEigenspace_eq_one_of_lt_evenFloor {α : ℝ}
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hη : Γ η = η)
    (hkerOdd : ∀ g : H, Γ g = -g → D g = 0 → g = 0)
    (hfloor : ∀ f : H, Γ f = f → α * ⟪f, f⟫ ≤ ⟪Q f, f⟫) (hlt : lam < α)
    (hne : oddEigenspace Q Γ lam ≠ ⊥) :
    Module.finrank ℝ (oddEigenspace Q Γ lam) = 1 := by
  have hbot := evenEigenspace_eq_bot_of_lt_floor hfloor hlt
  have hle := finrank_oddEigenspace_le hΓsym hanti hcomm hη hkerOdd (lam := lam)
  rw [hbot] at hle
  simp only [finrank_bot] at hle
  have hpos : 0 < Module.finrank ℝ (oddEigenspace Q Γ lam) := by
    rw [Module.finrank_pos_iff]
    exact (Submodule.nontrivial_iff_ne_bot).mpr hne
  omega

omit [FiniteDimensional ℝ H] in
/-- **Exact reciprocal gap current.**  A normalized even zero mode and a normalized odd level at
`λ ≠ 0` are coupled through the frequency map by exactly `-1/λ`.  The even parity of the zero
mode and the odd parity of `β` are part of the literal setting; the computation itself consumes
the even parity of `η` and the odd parity of the level. -/
theorem rankTwo_gap_current
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hDsym : ∀ f g : H, ⟪D f, g⟫ = ⟪f, D g⟫)
    (hQsym : ∀ f g : H, ⟪Q f, g⟫ = ⟪f, Q g⟫)
    (hcomm : RankTwoCommutator D Q η β)
    (hη : Γ η = η) (_hβ : Γ β = -β)
    {f g : H} (_hfeven : Γ f = f) (hf0 : Q f = 0)
    (hgodd : Γ g = -g) (hlam : lam ≠ 0) (hg : Q g = lam • g)
    (hηf : ⟪η, f⟫ = 1) (hβg : ⟪β, g⟫ = 1) :
    ⟪D f, g⟫ = -(1 / lam) ∧ ⟪f, D g⟫ = -(1 / lam) := by
  have hηg : ⟪η, g⟫ = 0 := by
    have h := hΓsym η g
    rw [hη, hgodd] at h
    have h2 : ⟪η, g⟫ = -⟪η, g⟫ := by
      rw [← inner_neg_right]
      exact h
    linarith
  -- `(Q - λ)(D g) = η`
  have hcg := hcomm g
  rw [hηg, hβg, zero_smul, one_smul, zero_sub] at hcg
  -- hcg : D (Q g) - Q (D g) = -η
  rw [hg, map_smul] at hcg
  -- pair with `f`
  have hpair := congrArg (fun v : H => ⟪v, f⟫) hcg
  simp only [inner_sub_left, inner_neg_left, real_inner_smul_left] at hpair
  have hQDgf : ⟪Q (D g), f⟫ = 0 := by
    rw [hQsym, hf0, inner_zero_right]
  rw [hQDgf, sub_zero, hηf] at hpair
  have hDgf : ⟪D g, f⟫ = -(1 / lam) := by
    field_simp at hpair ⊢
    linarith
  constructor
  · rw [hDsym, real_inner_comm]
    exact hDgf
  · rw [real_inner_comm]
    exact hDgf

end Balance

/-! ## The literal truncated frequency model -/

section Truncated

variable (N : ℕ)

/-- The literal truncated frequency operator `D e_j = j e_j` on indices `j = i - N ∈ [-N, N]`. -/
def truncatedFrequency :
    EuclideanSpace ℝ (Fin (2 * N + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * N + 1)) where
  toFun f := WithLp.toLp 2 fun i => ((i : ℝ) - N) * f i
  map_add' f g := by
    ext i
    simp only [PiLp.add_apply]
    ring
  map_smul' c f := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem truncatedFrequency_apply (f : EuclideanSpace ℝ (Fin (2 * N + 1)))
    (i : Fin (2 * N + 1)) :
    truncatedFrequency N f i = ((i : ℝ) - N) * f i := rfl

/-- Reflection index `i ↦ 2N - i` on `Fin (2N + 1)`. -/
def truncatedReflectionIndex (i : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  ⟨2 * N - i, by omega⟩

theorem truncatedReflectionIndex_involutive :
    Function.Involutive (truncatedReflectionIndex N) := by
  intro i
  have hi : (i : ℕ) ≤ 2 * N := by omega
  simp only [truncatedReflectionIndex]
  ext
  simp only
  omega

/-- The literal truncated reflection `Γ e_j = e_{-j}`. -/
def truncatedReflection :
    EuclideanSpace ℝ (Fin (2 * N + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * N + 1)) where
  toFun f := WithLp.toLp 2 fun i => f (truncatedReflectionIndex N i)
  map_add' f g := by
    ext i
    simp only [PiLp.add_apply]
  map_smul' c f := by
    ext i
    simp only [PiLp.smul_apply, RingHom.id_apply]

@[simp] theorem truncatedReflection_apply (f : EuclideanSpace ℝ (Fin (2 * N + 1)))
    (i : Fin (2 * N + 1)) :
    truncatedReflection N f i = f (truncatedReflectionIndex N i) := rfl

theorem truncatedReflection_symm (f g : EuclideanSpace ℝ (Fin (2 * N + 1))) :
    ⟪truncatedReflection N f, g⟫ = ⟪f, truncatedReflection N g⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    truncatedReflection_apply]
  refine Fintype.sum_equiv
    (Function.Involutive.toPerm _ (truncatedReflectionIndex_involutive N)) _ _ fun i => ?_
  simp only [Function.Involutive.coe_toPerm]
  rw [truncatedReflectionIndex_involutive N i]

theorem truncatedFrequency_anticommutes (f : EuclideanSpace ℝ (Fin (2 * N + 1))) :
    truncatedFrequency N (truncatedReflection N f) =
      -truncatedReflection N (truncatedFrequency N f) := by
  ext i
  have hi : (i : ℕ) ≤ 2 * N := by omega
  have hval : ((truncatedReflectionIndex N i : ℕ) : ℝ) = 2 * (N : ℝ) - (i : ℝ) := by
    simp only [truncatedReflectionIndex]
    push_cast [Nat.cast_sub hi]
    ring
  simp only [truncatedFrequency_apply, truncatedReflection_apply, PiLp.neg_apply]
  rw [hval]
  ring

/-- Center coordinate of the truncated model. -/
def truncatedCenter : Fin (2 * N + 1) := ⟨N, by omega⟩

/-- The truncated frequency operator is injective on odd vectors. -/
theorem truncatedFrequency_odd_injective (g : EuclideanSpace ℝ (Fin (2 * N + 1)))
    (hodd : truncatedReflection N g = -g) (hD : truncatedFrequency N g = 0) : g = 0 := by
  ext i
  have hDi : ((i : ℝ) - N) * g i = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (2 * N + 1)) => v i) hD
    simpa only [truncatedFrequency_apply, PiLp.zero_apply] using h
  simp only [PiLp.zero_apply]
  rcases eq_or_ne ((i : ℝ) - N) 0 with hzero | hne
  · -- `i = N`: the center coordinate of an odd vector vanishes
    have hiN : (i : ℕ) = N := by
      have hreal : (i : ℝ) = N := by linarith
      exact_mod_cast hreal
    have hoddi : g (truncatedReflectionIndex N i) = -g i := by
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (2 * N + 1)) => v i) hodd
      simpa only [truncatedReflection_apply, PiLp.neg_apply] using h
    have hfix : truncatedReflectionIndex N i = i := by
      simp only [truncatedReflectionIndex]
      ext
      simp only
      omega
    rw [hfix] at hoddi
    linarith
  · rcases mul_eq_zero.mp hDi with h | h
    · exact absurd h hne
    · exact h

/-- On even vectors annihilated by a center-charged source functional, the truncated frequency
operator is injective. -/
theorem truncatedFrequency_even_center_injective
    (η : EuclideanSpace ℝ (Fin (2 * N + 1))) (hηN : η (truncatedCenter N) ≠ 0)
    (f : EuclideanSpace ℝ (Fin (2 * N + 1)))
    (_heven : truncatedReflection N f = f) (hηf : ⟪η, f⟫ = 0)
    (hD : truncatedFrequency N f = 0) : f = 0 := by
  have hsupp : ∀ i : Fin (2 * N + 1), i ≠ truncatedCenter N → f i = 0 := by
    intro i hi
    have hDi : ((i : ℝ) - N) * f i = 0 := by
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (2 * N + 1)) => v i) hD
      simpa only [truncatedFrequency_apply, PiLp.zero_apply] using h
    have hne : ((i : ℝ) - N) ≠ 0 := by
      intro hzero
      apply hi
      have hiN : (i : ℕ) = N := by
        have hreal : (i : ℝ) = N := by linarith
        exact_mod_cast hreal
      exact Fin.ext hiN
    rcases mul_eq_zero.mp hDi with h | h
    · exact absurd h hne
    · exact h
  have hinner : ⟪η, f⟫ = η (truncatedCenter N) * f (truncatedCenter N) := by
    have hexp : ⟪η, f⟫ = ∑ i, η i * f i := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [hexp, Finset.sum_eq_single (truncatedCenter N)
      (fun i _ hi => by rw [hsupp i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [hinner] at hηf
  have hfN : f (truncatedCenter N) = 0 := by
    rcases mul_eq_zero.mp hηf with h | h
    · exact absurd h hηN
    · exact h
  ext i
  simp only [PiLp.zero_apply]
  rcases eq_or_ne i (truncatedCenter N) with rfl | hi
  · exact hfN
  · exact hsupp i hi

/-- **Parity-multiplicity balance in the literal truncated model.**  For every symmetric operator
with the rank-two commutator against the literal truncated frequency operator, even and odd
multiplicities of every eigenvalue differ by at most one. -/
theorem truncated_parity_multiplicity_balance
    (Q : EuclideanSpace ℝ (Fin (2 * N + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * N + 1)))
    (η β : EuclideanSpace ℝ (Fin (2 * N + 1))) (lam : ℝ)
    (hcomm : RankTwoCommutator (truncatedFrequency N) Q η β)
    (hη : truncatedReflection N η = η) (hβ : truncatedReflection N β = -β)
    (hηN : η (truncatedCenter N) ≠ 0) :
    Module.finrank ℝ (evenEigenspace Q (truncatedReflection N) lam) ≤
        Module.finrank ℝ (oddEigenspace Q (truncatedReflection N) lam) + 1 ∧
      Module.finrank ℝ (oddEigenspace Q (truncatedReflection N) lam) ≤
        Module.finrank ℝ (evenEigenspace Q (truncatedReflection N) lam) + 1 := by
  constructor
  · exact finrank_evenEigenspace_le (truncatedReflection_symm N)
      (truncatedFrequency_anticommutes N) hcomm hβ
      (truncatedFrequency_even_center_injective N η hηN)
  · exact finrank_oddEigenspace_le (truncatedReflection_symm N)
      (truncatedFrequency_anticommutes N) hcomm hη
      (truncatedFrequency_odd_injective N)

end Truncated

end RHTower

end
