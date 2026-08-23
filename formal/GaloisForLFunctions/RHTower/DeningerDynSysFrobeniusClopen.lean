import GaloisForLFunctions.RHTower.DeningerDynSysFrobeniusRange
import GaloisForLFunctions.RHTower.DeningerDynSysCharacterTopology
import GaloisForLFunctions.RHTower.DeningerDynSysColimitTopology

/-!
# The image of the Frobenius operator is open and closed

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 7.3 (`t9`), the
clopen assertion.

Equation (21) describes `F_ν (X̂ (C))` as the set of character points whose character kills the
`ν`-th roots of unity of the residue field.  When those roots of unity are values of `ν`-th roots
of unity in the sections over an affine open — which is what Deninger's setting supplies, the
scheme being integrally closed in a radically closed field with `μ_ν (R) = μ_ν (K)` — that
condition becomes finitely many evaluation conditions.  The finitely many possible restrictions to
the finite group `μ_ν (Γ (X, U))` then partition the trace over `U` into closed pieces, and a
finite partition into closed sets is a partition into open sets.  Hence `F_ν (X̂ (C))` is open and
closed.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C] [TopologicalSpace C]

/-- In a domain there are only finitely many `ν`-th roots of unity. -/
theorem deningerRootsOfUnity_finite {R : Type*} [CommRing R] [IsDomain R] {ν : ℕ} (hν : 0 < ν) :
    {z : R | z ^ ν = 1}.Finite := by
  have hne : (Polynomial.X ^ ν - Polynomial.C (1 : R)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hν 1
  have hsub : {z : R | z ^ ν = 1}
      ⊆ {z : R | (Polynomial.X ^ ν - Polynomial.C (1 : R)).IsRoot z} := by
    intro z hz
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [Set.mem_setOf_eq] at hz
    rw [hz, sub_self]
  exact Set.Finite.subset (Polynomial.finite_setOf_isRoot hne) hsub

/-- **Deninger, §7.**  The `ν`-th roots of unity of the residue fields over an open subset are
values of `ν`-th roots of unity in the sections over it. -/
def DeningerRootsFromSections (X : Scheme.{u}) (U : X.Opens) (ν : ℕ) : Prop :=
  ∀ (x : X) (hx : x ∈ U) (u : (X.residueField x)ˣ), u ^ ν = 1 →
    ∃ z : Γ(X, U), z ^ ν = 1 ∧ X.evaluation U x hx z = (u : X.residueField x)

omit [TopologicalSpace C] in
/-- Under `DeningerRootsFromSections` the condition of equation (21) is a condition on finitely
many evaluations. -/
theorem deningerCharOver_killsRoots_iff {U : X.Opens} {ν : ℕ} (hν : 0 < ν)
    (hroots : DeningerRootsFromSections X U ν) (P : DeningerCharOver X C U) :
    (∀ u : (X.residueField P.val.1)ˣ, u ^ ν = 1 → P.val.2 u = 1)
      ↔ ∀ z : Γ(X, U), z ^ ν = 1 → deningerCharEval U z P.val = 1 := by
  classical
  constructor
  · intro h z hz
    have hval : X.evaluation U P.val.1 P.mem z ^ ν = 1 := by
      rw [← map_pow, hz, map_one]
    have hne : X.evaluation U P.val.1 P.mem z ≠ 0 := by
      intro h0
      rw [h0, zero_pow hν.ne'] at hval
      exact zero_ne_one hval
    have hu : (Units.mk0 _ hne) ^ ν = 1 := Units.ext hval
    rw [deningerCharEval, dif_pos P.mem, deningerUnitExtend, dif_neg hne, h _ hu]
    rfl
  · intro h u hu
    obtain ⟨z, hz1, hz2⟩ := hroots P.val.1 P.mem u hu
    have hne : X.evaluation U P.val.1 P.mem z ≠ 0 := by
      rw [hz2]
      exact u.ne_zero
    have hkey := h z hz1
    rw [deningerCharEval, dif_pos P.mem, deningerUnitExtend, dif_neg hne] at hkey
    have hmk : Units.mk0 (X.evaluation U P.val.1 P.mem z) hne = u := Units.ext hz2
    rw [hmk] at hkey
    exact Units.ext hkey

/-- The trace over `U` of the image of the Frobenius operator. -/
def deningerCharOverKillsRoots (U : X.Opens) (ν : ℕ) : Set (DeningerCharOver X C U) :=
  {P | ∀ z : Γ(X, U), z ^ ν = 1 → deningerCharEval U z P.val = 1}

variable [T1Space C]

/-- **Deninger, Lemma 7.3 (`t9`).**  The trace over an affine open of the image of the Frobenius
operator is open and closed: it is one block of the finite partition of the trace by the
restriction of the character to the finite group of `ν`-th roots of unity of the sections. -/
theorem deningerCharOverKillsRoots_isClopen {U : X.Opens} [IsDomain Γ(X, U)] {ν : ℕ}
    (hν : 0 < ν) : IsClopen (deningerCharOverKillsRoots (X := X) (C := C) U ν) := by
  classical
  set S : Set Γ(X, U) := {z : Γ(X, U) | z ^ ν = 1} with hS
  haveI : Finite ↥S := (deningerRootsOfUnity_finite hν).to_subtype
  set res : DeningerCharOver X C U → (↥S → C) :=
    fun P z => deningerCharEval U (z : Γ(X, U)) P.val with hres
  have hcont : Continuous res :=
    continuous_pi fun z => deningerCharEval_continuous U (z : Γ(X, U))
  have hvals : ∀ (P : DeningerCharOver X C U) (z : ↥S), res P z ∈ {c : C | c ^ ν = 1} := by
    intro P z
    have hz : ((z : Γ(X, U))) ^ ν = 1 := z.2
    show (deningerCharEval U (z : Γ(X, U)) P.val) ^ ν = 1
    rw [← deningerCharEval_pow U _ ν P.val P.mem, hz, deningerCharEval_one U P.val P.mem]
  have hrangefin : (Set.range res).Finite := by
    refine Set.Finite.subset (Set.Finite.pi (fun _ : ↥S =>
      deningerRootsOfUnity_finite (R := C) hν)) ?_
    rintro θ ⟨P, rfl⟩
    intro z _
    exact hvals P z
  have hclosed : ∀ θ : ↥S → C, IsClosed (res ⁻¹' {θ}) := fun θ =>
    (isClosed_singleton).preimage hcont
  have hset : deningerCharOverKillsRoots (X := X) (C := C) U ν = res ⁻¹' {(1 : ↥S → C)} := by
    ext P
    simp only [deningerCharOverKillsRoots, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · intro h
      funext z
      exact h (z : Γ(X, U)) z.2
    · intro h z hz
      exact congrFun h ⟨z, hz⟩
  rw [hset]
  refine ⟨hclosed 1, ?_⟩
  rw [← isClosed_compl_iff]
  have hcompl : (res ⁻¹' {(1 : ↥S → C)})ᶜ = ⋃ θ ∈ Set.range res \ {(1 : ↥S → C)},
      res ⁻¹' {θ} := by
    ext P
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Set.mem_sdiff, exists_prop]
    constructor
    · intro hP
      exact ⟨res P, ⟨⟨P, rfl⟩, hP⟩, rfl⟩
    · rintro ⟨θ, ⟨-, hθ1⟩, hPθ⟩
      rw [hPθ]
      exact hθ1
  rw [hcompl]
  exact Set.Finite.isClosed_biUnion (hrangefin.sdiff) fun θ _ => hclosed θ

omit [TopologicalSpace C] [T1Space C] in
/-- The trace over an affine open of the image of the Frobenius operator. -/
theorem deningerCharOver_preimage_range {U : X.Opens} {ν : ℕ} (hν : 0 < ν)
    (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hroots : DeningerRootsFromSections X U ν) :
    (DeningerCharOver.val (X := X) (C := C) (U := U)) ⁻¹'
        (Set.range (deningerCharFrobenius (X := X) (C := C) ν))
      = deningerCharOverKillsRoots U ν := by
  ext P
  rw [Set.mem_preimage, deningerCharFrobenius_range halg hν]
  exact deningerCharOver_killsRoots_iff hν hroots P

/-- **Deninger, Lemma 7.3 (`t9`).**  The image of the Frobenius operator on `X̂ (C)` is open and
closed. -/
theorem deningerCharFrobenius_isClopen_range {ν : ℕ} (hν : 0 < ν)
    (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hdom : ∀ U : X.affineOpens, IsDomain Γ(X, U.1))
    (hroots : ∀ U : X.affineOpens, DeningerRootsFromSections X U.1 ν) :
    IsClopen (Set.range (deningerCharFrobenius (X := X) (C := C) ν)) := by
  have hpre : ∀ U : X.affineOpens,
      IsClopen ((DeningerCharOver.val (X := X) (C := C) (U := U.1)) ⁻¹'
        (Set.range (deningerCharFrobenius (X := X) (C := C) ν))) := by
    intro U
    haveI := hdom U
    rw [deningerCharOver_preimage_range hν halg (hroots U)]
    exact deningerCharOverKillsRoots_isClopen hν
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff, deningerCharPoints_isOpen_iff]
    intro U
    rw [Set.preimage_compl]
    exact (hpre U).1.isOpen_compl
  · rw [deningerCharPoints_isOpen_iff]
    exact fun U => (hpre U).2

/-- **Deninger, Proposition 7.4(a) (`t10`).**  `X̂ (C)` is an open and closed subspace of
`X̌ (C)`. -/
theorem deningerColimUnit_isClopen_range {N₀ : Submonoid ℕ}
    (halg : ∀ x : X, IsAlgClosed (X.residueField x)) (hN₀ : ∀ ν ∈ N₀, 0 < ν)
    (hdom : ∀ U : X.affineOpens, IsDomain Γ(X, U.1))
    (hroots : ∀ (ν : ℕ), ν ∈ N₀ → ∀ U : X.affineOpens, DeningerRootsFromSections X U.1 ν) :
    IsClopen (Set.range (deningerColimUnit (X := X) (C := C) N₀)) := by
  have hpre : ∀ ν : N₀, (deningerColimMk (X := X) (C := C) N₀ ν) ⁻¹'
      (Set.range (deningerColimUnit (X := X) (C := C) N₀))
      = Set.range (deningerCharFrobenius (X := X) (C := C) (ν : ℕ)) := by
    intro ν
    ext P
    simp only [Set.mem_preimage, Set.mem_range, deningerColimUnit]
    constructor
    · rintro ⟨Q, hQ⟩
      rw [deningerColimMk_eq_iff] at hQ
      obtain ⟨a, b, h1, h2⟩ := hQ
      have hab : (a : ℕ) = (ν : ℕ) * (b : ℕ) := by simpa using h1
      have hcomp : deningerCharFrobenius (b : ℕ)
          (deningerCharFrobenius (ν : ℕ) Q) = deningerCharFrobenius (a : ℕ) Q := by
        rw [deningerCharFrobenius_comp, hab]
      have hinj := deningerCharFrobenius_injective (X := X) (C := C) halg (hN₀ b b.2)
      exact ⟨Q, hinj (by rw [hcomp, h2])⟩
    · rintro ⟨Q, rfl⟩
      refine ⟨Q, (deningerColimMk_eq_iff).2 ⟨ν, 1, ?_, ?_⟩⟩
      · simp
      · simp [deningerCharFrobenius_one]
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff, deningerColim_isOpen_iff]
    intro ν
    rw [Set.preimage_compl, hpre ν]
    exact (deningerCharFrobenius_isClopen_range (hN₀ ν ν.2) halg hdom
      (hroots (ν : ℕ) ν.2)).1.isOpen_compl
  · rw [deningerColim_isOpen_iff]
    intro ν
    rw [hpre ν]
    exact (deningerCharFrobenius_isClopen_range (hN₀ ν ν.2) halg hdom
      (hroots (ν : ℕ) ν.2)).2

end RHTower
