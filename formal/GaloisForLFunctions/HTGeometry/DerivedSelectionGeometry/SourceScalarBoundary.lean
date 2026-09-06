import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.SourceOrientation

/-!
# The full cyclic-source quotient when its landing scalar may vanish

For every commutative ring and every q,c, the literal cyclic-source quotient is
`R/(c) × R/(c*q*(q-1))`. Its annihilator is `(c*q*(q-1))`.
The coordinate change `(-x, y+q*x)` diagonalizes the two boundary generators without
any division. Every invariant surjective source trace has the same boundary.

In particular zero landing retains the whole ambient two-coordinate module for every
rotation parameter. The unit-scalar orientation theorem cannot be specialized by setting
its unit scalar to a vanishing source response. This classification supplies no zeta
zero-location constraint.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.DerivedSelection.NonunitSource
universe u v
variable {R : Type u} [CommRing R]

/-- Boundary of the canonical source with identity reflection and trace. -/
abbrev boundary (q c : R) : Submodule R (R × R) :=
  srcBoundary (LinearMap.id : R →ₗ[R] R) LinearMap.id q c

/-- Canonical cyclic-source quotient before any scalar is inverted. -/
abbrev SourceQuotient (q c : R) := (R × R) ⧸ boundary q c

/-- The first literal boundary generator, with the landing scalar retained. -/
theorem first_defect (q c a : R) :
    srcDefect (LinearMap.id : R →ₗ[R] R) LinearMap.id q c a =
      (-c * a, c * q * a) := by
  rw [srcDefect_apply (fun _ => rfl)]
  ext <;> simp [Prod.smul_def, smul_eq_mul]
  ring

/-- The rotated literal boundary generator, with the landing scalar retained. -/
theorem second_defect (q c b : R) :
    srcRotDefect (LinearMap.id : R →ₗ[R] R) LinearMap.id q c b =
      (c * q * b, -c * q * b) := by
  rw [srcRotDefect_apply (fun _ => rfl)]
  ext <;> simp [Prod.smul_def, smul_eq_mul] <;> ring

/-- Every boundary element is an explicit linear combination of the two generators. -/
theorem mem_boundary (q c : R) (p : R × R) :
    p ∈ boundary q c ↔ ∃ a b : R,
      p = (-c * a + c * q * b, c * q * a - c * q * b) := by
  simp only [boundary, srcBoundary, Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, h⟩
    refine ⟨a, b, ?_⟩
    simpa [first_defect, second_defect, sub_eq_add_neg] using h.symm
  · rintro ⟨a, b, rfl⟩
    refine ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, ?_⟩
    simp [first_defect, second_defect, Prod.ext_iff]
    ring

/-- Diagonal coordinate reduction into the two principal-ideal quotients. -/
def reduce (q c : R) : (R × R) →ₗ[R]
    (R ⧸ Ideal.span {c}) × (R ⧸ Ideal.span {c * q * (q - 1)}) :=
  LinearMap.prod
    ((Ideal.span {c} : Ideal R).mkQ ∘ₗ (-LinearMap.fst R R R))
    ((Ideal.span {c * q * (q - 1)} : Ideal R).mkQ ∘ₗ
      (LinearMap.snd R R R + q • LinearMap.fst R R R))

theorem reduce_apply (q c : R) (p : R × R) :
    reduce q c p =
      (Ideal.Quotient.mk (Ideal.span {c}) (-p.1),
       Ideal.Quotient.mk (Ideal.span {c * q * (q - 1)}) (p.2 + q * p.1)) := rfl

theorem reduce_surjective (q c : R) : Function.Surjective (reduce q c) := by
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := (Ideal.span {c} : Ideal R).mkQ_surjective a
  obtain ⟨y, rfl⟩ := (Ideal.span {c * q * (q - 1)} : Ideal R).mkQ_surjective b
  refine ⟨(-x, y + q * x), ?_⟩
  rw [reduce_apply]
  simp

theorem ker_reduce (q c : R) : LinearMap.ker (reduce q c) = boundary q c := by
  ext p
  rw [mem_boundary]
  simp only [LinearMap.mem_ker, reduce_apply, Prod.mk_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, dvd_def]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a + q * b, b, ?_⟩
    ext
    · dsimp
      linear_combination -ha
    · dsimp
      linear_combination hb + q * ha
  · rintro ⟨a, b, rfl⟩
    constructor
    · exact ⟨a - q * b, by ring⟩
    · exact ⟨b, by ring⟩

/-- Complete cyclic-source quotient, without any unit or regularity premise on q or c. -/
def quotientEquiv (q c : R) : SourceQuotient q c ≃ₗ[R]
    (R ⧸ Ideal.span {c}) × (R ⧸ Ideal.span {c * q * (q - 1)}) :=
  (Submodule.quotEquivOfEq _ _ (ker_reduce q c).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (reduce_surjective q c))

/-- The full annihilator retains the source scalar. -/
theorem annihilator (q c : R) :
    Module.annihilator R (SourceQuotient q c) = Ideal.span {c * q * (q - 1)} := by
  rw [(quotientEquiv q c).annihilator_eq, Module.annihilator_prod,
    Ideal.annihilator_quotient, Ideal.annihilator_quotient]
  apply inf_eq_right.mpr
  apply Ideal.span_le.mpr
  intro x hx
  have hx' : x = c * q * (q - 1) := Set.mem_singleton_iff.mp hx
  rw [hx']
  change c * q * (q - 1) ∈ (Ideal.span {c} : Ideal R)
  exact Ideal.mem_span_singleton.mpr ⟨q * (q - 1), by ring⟩

/-- A vanishing source leaves no boundary at all, independently of rotation. -/
theorem boundary_zero (q : R) : boundary q 0 = ⊥ := by
  ext p
  simp [mem_boundary, Submodule.mem_bot]
  rfl

/-- The full two-coordinate source survives at every zero landing. -/
def quotientZeroEquiv (q : R) : SourceQuotient q 0 ≃ₗ[R] R × R :=
  (boundary q 0).quotEquivOfEqBot (boundary_zero q)


/-- Every invariant surjective trace has the same full scalar-dependent boundary. -/
theorem general_boundary_eq {S : Type v} [AddCommGroup S] [Module R S]
    (tau : S →ₗ[R] S) (eps : S →ₗ[R] R)
    (hinv : ∀ x, eps (tau x) = eps x) (heps : Function.Surjective eps) (q c : R) :
    srcBoundary tau eps q c = boundary q c := by
  apply le_antisymm
  · rw [srcBoundary, sup_le_iff]
    constructor
    · rintro p ⟨x, rfl⟩
      rw [mem_boundary]
      refine ⟨eps x, 0, ?_⟩
      rw [srcDefect_apply hinv]
      ext <;> simp [Prod.smul_def, smul_eq_mul]
      ring
    · rintro p ⟨x, rfl⟩
      rw [mem_boundary]
      refine ⟨0, eps x, ?_⟩
      rw [srcRotDefect_apply hinv]
      ext <;> simp [Prod.smul_def, smul_eq_mul] <;> ring
  · intro p hp
    obtain ⟨a, b, rfl⟩ := (mem_boundary q c p).1 hp
    obtain ⟨x, hx⟩ := heps a
    obtain ⟨y, hy⟩ := heps b
    apply Submodule.mem_sup.mpr
    refine ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, ?_⟩
    rw [srcDefect_apply hinv, srcRotDefect_apply hinv, hx, hy]
    ext <;> simp [Prod.smul_def, smul_eq_mul] <;> ring

/-- Full quotient classification for the original invariant cyclic-source interface. -/
def generalQuotientEquiv {S : Type v} [AddCommGroup S] [Module R S]
    (tau : S →ₗ[R] S) (eps : S →ₗ[R] R)
    (hinv : ∀ x, eps (tau x) = eps x) (heps : Function.Surjective eps) (q c : R) :
    srcIncompatModule tau eps q c ≃ₗ[R]
      (R ⧸ Ideal.span {c}) × (R ⧸ Ideal.span {c * q * (q - 1)}) :=
  (Submodule.quotEquivOfEq _ _ (general_boundary_eq tau eps hinv heps q c)).trans
    (quotientEquiv q c)

/-- The full annihilator for every invariant surjective trace, including nonunit scalars. -/
theorem general_annihilator {S : Type v} [AddCommGroup S] [Module R S]
    (tau : S →ₗ[R] S) (eps : S →ₗ[R] R)
    (hinv : ∀ x, eps (tau x) = eps x) (heps : Function.Surjective eps) (q c : R) :
    Module.annihilator R (srcIncompatModule tau eps q c) = Ideal.span {c * q * (q - 1)} := by
  change Module.annihilator R ((R × R) ⧸ srcBoundary tau eps q c) = _
  rw [general_boundary_eq tau eps hinv heps]
  exact annihilator q c

section Field
variable {K : Type u} [Field K]

private theorem finrank_ideal_top : Module.finrank K (K ⧸ (⊤ : Ideal K)) = 0 := by
  change Module.finrank K (K ⧸ (⊤ : Submodule K K)) = 0
  exact Module.finrank_eq_zero_of_subsingleton K _

private theorem finrank_ideal_bot : Module.finrank K (K ⧸ (⊥ : Ideal K)) = 1 := by
  change Module.finrank K (K ⧸ (⊥ : Submodule K K)) = 1
  rw [((⊥ : Submodule K K).quotEquivOfEqBot rfl).finrank_eq]
  exact Module.finrank_self K

/-- Zero landing has dimension two at every rotation parameter. -/
theorem finrank_zero (q : K) : Module.finrank K (SourceQuotient q 0) = 2 := by
  rw [(quotientZeroEquiv q).finrank_eq]
  simp

/-- Away from source vanishing and the two singular rotations the quotient is zero. -/
theorem finrank_of_nonsingular {q c : K} (hc : c ≠ 0) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    Module.finrank K (SourceQuotient q c) = 0 := by
  have hC : (Ideal.span {c} : Ideal K) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr hc)
  have hD : (Ideal.span {c * q * (q - 1)} : Ideal K) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero hc hq0) (sub_ne_zero.mpr hq1)))
  rw [(quotientEquiv q c).finrank_eq, hC, hD, Module.finrank_prod,
    finrank_ideal_top, zero_add]

/-- A nonzero landing at either singular rotation leaves one coordinate. -/
theorem finrank_of_singular_rotation {q c : K} (hc : c ≠ 0) (hq : q = 0 ∨ q = 1) :
    Module.finrank K (SourceQuotient q c) = 1 := by
  have hC : (Ideal.span {c} : Ideal K) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr hc)
  have hd : c * q * (q - 1) = 0 := by
    rcases hq with rfl | rfl <;> simp
  have hD : (Ideal.span {c * q * (q - 1)} : Ideal K) = ⊥ :=
    Ideal.span_singleton_eq_bot.mpr hd
  rw [(quotientEquiv q c).finrank_eq, hC, hD, Module.finrank_prod,
    finrank_ideal_top, finrank_ideal_bot, zero_add]

local instance : DecidableEq K := Classical.decEq K

/-- Complete field-valued dimension classification, including every zero-source fibre. -/
theorem field_finrank_classification (q c : K) :
    Module.finrank K (SourceQuotient q c) =
      if c = 0 then 2 else if q = 0 ∨ q = 1 then 1 else 0 := by
  classical
  by_cases hc : c = 0
  · subst c
    simpa using finrank_zero q
  · by_cases hq : q = 0 ∨ q = 1
    · simpa [hc, hq] using finrank_of_singular_rotation hc hq
    · simpa [hc, hq] using finrank_of_nonsingular hc
        (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h))

end Field

end GaloisForLFunctions.HTGeometry.DerivedSelection.NonunitSource
