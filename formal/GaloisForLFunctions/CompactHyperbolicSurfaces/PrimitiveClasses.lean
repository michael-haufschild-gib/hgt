import GaloisForLFunctions.CompactHyperbolicSurfaces.TraceFormula

/-!
# Primitive conjugacy classes

In a cocompact free group of hyperbolic elements, call `γ ≠ 1` *primitive* if its length equals its
primitive length.  Every `γ ≠ 1` is `γ₀^m` with `γ₀` primitive and `m ≥ 1`, uniquely up to
conjugation (`isConj_of_isConj_pow`), and `ℓ(γ₀^m) = m ℓ(γ₀)`, `ℓ₀(γ₀^m) = ℓ(γ₀)`.  On classes this is
a bijection `primPowEquiv : {primitive classes} × ℕ ≃ {classes ≠ 1}`, `([γ₀], n) ↦ [γ₀^{n+1}]`.
-/

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry RHTower

noncomputable section

section Roots

variable {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ)
  (hhyp : ∀ γ : Γ, γ ≠ 1 → 2 < |trSL γ|)
include hΓ hhyp

omit hΓ in
theorem hypLen_pos {γ : Γ} (hγ : γ ≠ 1) : 0 < hypLen (γ : SL(2, ℝ)) := by
  have h := hhyp γ hγ
  unfold hypLen
  have : 1 < |trSL (γ : SL(2, ℝ))| / 2 := by linarith
  have := Real.arcosh_pos this
  linarith

omit hΓ in
theorem primLen_le_hypLen {γ δ : Γ} (hδ : δ ≠ 1) (hc : δ * γ = γ * δ) :
    primLen γ ≤ hypLen (δ : SL(2, ℝ)) := by
  refine csInf_le ⟨0, ?_⟩ ⟨δ, hδ, hc, rfl⟩
  rintro r ⟨δ', hδ', -, rfl⟩
  exact (hypLen_pos hhyp hδ').le

/-- **Primitive roots, with lengths.**  `γ = γ₀^m`, `m ≥ 1`, the centralizer of `γ` is `⟨γ₀⟩`, and
`ℓ(γ₀) = ℓ₀(γ₀) = ℓ₀(γ)`, `ℓ(γ) = m ℓ(γ₀)`. -/
theorem exists_root_lengths (γ : Γ) (hγ : γ ≠ 1) :
    ∃ (γ₀ : Γ) (m : ℕ), 0 < m ∧ γ = γ₀ ^ m ∧ γ₀ ≠ 1 ∧
      (∀ δ : Γ, δ * γ = γ * δ ↔ ∃ k : ℤ, δ = γ₀ ^ k) ∧
      (∀ δ : Γ, δ * γ₀ = γ₀ * δ ↔ ∃ k : ℤ, δ = γ₀ ^ k) ∧
      hypLen (γ₀ : SL(2, ℝ)) = primLen γ₀ ∧ primLen γ = hypLen (γ₀ : SL(2, ℝ)) ∧
      hypLen (γ : SL(2, ℝ)) = m * hypLen (γ₀ : SL(2, ℝ)) ∧
      (∀ k : ℤ, γ₀ ^ k = 1 → k = 0) := by
  obtain ⟨σ, γ₀, ℓ₀, m, hℓ₀, hm, hγm, hC, hf⟩ := exists_primitive_root hΓ hhyp γ hγ
  have hinf : ∀ k : ℤ, γ₀ ^ k = 1 → k = 0 := fun k hk =>
    zpow_eq_one_of_frame hℓ₀ hf (by rw [← Subgroup.coe_zpow, hk]; rfl)
  have hC₀ : ∀ δ : Γ, δ * γ₀ = γ₀ * δ ↔ ∃ k : ℤ, δ = γ₀ ^ k := by
    intro δ
    constructor
    · intro h
      exact (hC δ).mp (by rw [hγm]; exact (Commute.pow_right h m).eq)
    · rintro ⟨k, rfl⟩; exact (Commute.zpow_left (Commute.refl γ₀) k).eq
  have hlen₀ : hypLen (γ₀ : SL(2, ℝ)) = ℓ₀ := by
    have := hypLen_zpow_frame hf 1
    rw [zpow_one, Int.cast_one, one_mul, abs_of_pos hℓ₀] at this
    exact this
  refine ⟨γ₀, m, hm, hγm, fun h => by have := hinf 1 (by rw [zpow_one, h]); omega, hC, hC₀,
    by rw [hlen₀, primLen_eq hℓ₀ hC₀ hf], by rw [hlen₀, primLen_eq hℓ₀ hC hf], ?_, hinf⟩
  have := hypLen_zpow_frame hf m
  rw [zpow_natCast, ← Subgroup.coe_pow, ← hγm, abs_of_pos (by positivity), Int.cast_natCast]
    at this
  rw [this, hlen₀]

omit hΓ in
/-- Primitive elements are their own roots. -/
theorem eq_root_of_primitive {γ γ₀ : Γ} {m : ℕ} (hγ : γ ≠ 1)
    (hprim : hypLen (γ : SL(2, ℝ)) = primLen γ) (hlen : hypLen (γ : SL(2, ℝ)) = m * hypLen (γ₀ : SL(2, ℝ)))
    (hp : primLen γ = hypLen (γ₀ : SL(2, ℝ))) : m = 1 := by
  have hpos := hypLen_pos hhyp hγ
  rw [hprim, hp] at hlen
  have h0 : hypLen (γ₀ : SL(2, ℝ)) ≠ 0 := by
    intro h; rw [hp, h] at hprim; rw [hprim] at hpos; exact lt_irrefl _ hpos
  have : (m : ℝ) = 1 := by
    have := mul_right_cancel₀ h0 (hlen.symm.trans (one_mul _).symm)
    exact this
  exact_mod_cast this

/-- In a cyclic centralizer, a primitive element is a generator up to inverse. -/
theorem zpow_eq_pm_one_of_primitive {g δ : Γ} {i : ℤ} (hδ : δ ≠ 1) (hδg : δ = g ^ i)
    (hprim : hypLen (δ : SL(2, ℝ)) = primLen δ) (hg1 : g ≠ 1)
    (hlen : ∀ k : ℤ, hypLen ((g ^ k : Γ) : SL(2, ℝ)) = |k| * hypLen (g : SL(2, ℝ))) :
    i = 1 ∨ i = -1 := by
  have hc : g * δ = δ * g := by rw [hδg]; exact (Commute.zpow_right (Commute.refl g) i).eq
  have hle := primLen_le_hypLen hhyp hg1 hc
  rw [← hprim, hδg, hlen] at hle
  have hpos := hypLen_pos hhyp hg1
  have hi : |(i : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; nlinarith
  have hi0 : i ≠ 0 := by rintro rfl; exact hδ (by rw [hδg, zpow_zero])
  have : |i| ≤ 1 := by exact_mod_cast (show ((|i| : ℤ) : ℝ) ≤ 1 by rw [Int.cast_abs]; exact hi)
  have := abs_le.mp this
  omega

/-- The length of a power of a framed generator. -/
theorem hypLen_zpow_root {γ : Γ} (hγ : γ ≠ 1) :
    ∃ (g : Γ), g ≠ 1 ∧ (∀ δ : Γ, δ * γ = γ * δ ↔ ∃ k : ℤ, δ = g ^ k) ∧
      (∀ k : ℤ, hypLen ((g ^ k : Γ) : SL(2, ℝ)) = |k| * hypLen (g : SL(2, ℝ))) ∧
      (∀ k : ℤ, g ^ k = 1 → k = 0) ∧ ∃ m : ℕ, 0 < m ∧ γ = g ^ m := by
  obtain ⟨σ, γ₀, ℓ₀, m, hℓ₀, hm, hγm, hC, hf⟩ := exists_primitive_root hΓ hhyp γ hγ
  have hinf : ∀ k : ℤ, γ₀ ^ k = 1 → k = 0 := fun k hk =>
    zpow_eq_one_of_frame hℓ₀ hf (by rw [← Subgroup.coe_zpow, hk]; rfl)
  refine ⟨γ₀, fun h => by have := hinf 1 (by rw [zpow_one, h]); omega, hC, fun k => ?_, hinf,
    m, hm, hγm⟩
  rw [Subgroup.coe_zpow, hypLen_zpow_frame hf, abs_mul, abs_of_pos hℓ₀, Int.cast_abs]
  have := hypLen_zpow_frame hf 1
  rw [zpow_one, Int.cast_one, one_mul, abs_of_pos hℓ₀] at this
  rw [this]

/-- **Uniqueness of roots.**  If `γ₀^m ~ γ₁^n` with `γ₀, γ₁` primitive and `m, n ≥ 1`, then
`γ₀ ~ γ₁` and `m = n`. -/
theorem isConj_of_isConj_pow {γ₀ γ₁ : Γ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h₀ : γ₀ ≠ 1) (h₁ : γ₁ ≠ 1)
    (hp₀ : hypLen (γ₀ : SL(2, ℝ)) = primLen γ₀) (hp₁ : hypLen (γ₁ : SL(2, ℝ)) = primLen γ₁)
    (hconj : IsConj (γ₀ ^ m) (γ₁ ^ n)) : IsConj γ₀ γ₁ ∧ m = n := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  set γ₀' := c * γ₀ * c⁻¹ with hγ₀'
  have hγ₀'1 : γ₀' ≠ 1 := fun h => h₀ (by
    calc γ₀ = c⁻¹ * γ₀' * c := by rw [hγ₀']; group
      _ = 1 := by rw [h]; group)
  have hp₀' : hypLen (γ₀' : SL(2, ℝ)) = primLen γ₀' := by
    rw [hγ₀', hypLen_conj, primLen_conj, hp₀]
  have hpow : γ₀' ^ m = γ₁ ^ n := by
    rw [hγ₀', ← hc]; simp only [conj_pow]
  set γ := γ₁ ^ n
  have hγ1 : γ ≠ 1 := by
    intro h
    obtain ⟨g, -, -, -, hinf, -⟩ := hypLen_zpow_root hΓ hhyp h₁
    obtain ⟨γr, mr, hmr, hγr, -, -, -, -, -, -, hinfr⟩ := exists_root_lengths hΓ hhyp γ₁ h₁
    have : γr ^ ((mr * n : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, pow_mul, ← hγr]; exact h
    have := hinfr _ this
    have : mr * n = 0 := by exact_mod_cast this
    rcases Nat.mul_eq_zero.mp this with h | h <;> omega
  obtain ⟨g, hg1, hC, hlen, hinf, -⟩ := hypLen_zpow_root hΓ hhyp hγ1
  obtain ⟨i, hi⟩ := (hC γ₀').mp (by rw [← hpow]; exact (Commute.pow_right (Commute.refl _) m).eq)
  obtain ⟨j, hj⟩ := (hC γ₁).mp (Commute.pow_right (Commute.refl _) n).eq
  have hi' := zpow_eq_pm_one_of_primitive hΓ hhyp hγ₀'1 hi hp₀' hg1 hlen
  have hj' := zpow_eq_pm_one_of_primitive hΓ hhyp h₁ hj hp₁ hg1 hlen
  have hij : i * m = j * n := by
    have e : g ^ (i * m - j * n) = 1 := by
      rw [zpow_sub, zpow_mul, zpow_mul, ← hi, ← hj, zpow_natCast, zpow_natCast, hpow,
        mul_inv_cancel]
    have := hinf _ e
    omega
  have hmn : m = n ∧ i = j := by
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact ⟨by omega, rfl⟩
    · omega
    · omega
    · exact ⟨by omega, rfl⟩
  refine ⟨isConj_iff.mpr ⟨c, ?_⟩, hmn.1⟩
  rw [← hγ₀', hi, hj, hmn.2]

end Roots

/-! ### Classes -/

namespace CompactQuotient

variable (X : CompactQuotient)

theorem isConj_classRep (γ : X.Γ) : IsConj (X.classRep (ConjClasses.mk γ)) γ := by
  rw [← ConjClasses.mk_eq_mk_iff_isConj, X.mk_classRep]

theorem classLen_mk (γ : X.Γ) : X.classLen (ConjClasses.mk γ) = hypLen (γ : SL(2, ℝ)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (X.isConj_classRep γ)
  unfold classLen
  conv_rhs => rw [← hc]
  rw [hypLen_conj]

theorem classPrimLen_mk (γ : X.Γ) : X.classPrimLen (ConjClasses.mk γ) = primLen γ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (X.isConj_classRep γ)
  unfold classPrimLen
  conv_rhs => rw [← hc]
  rw [primLen_conj]

/-- Nontrivial conjugacy classes. -/
abbrev NClass := {c : ConjClasses X.Γ // c ≠ 1}

/-- Primitive classes: length equal to primitive length. -/
abbrev PClass := {c : X.NClass // X.classLen c = X.classPrimLen c}

variable {X} (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|)
include hhyp

/-- `([γ₀], n) ↦ [γ₀^{n+1}]`. -/
def primPow (p : X.PClass × ℕ) : X.NClass :=
  ⟨ConjClasses.mk (X.classRep p.1.1 ^ (p.2 + 1)), by
    intro h
    have h1 : X.classRep p.1.1 ^ (p.2 + 1) = 1 := by
      have h' : ConjClasses.mk (X.classRep p.1.1 ^ (p.2 + 1)) = ConjClasses.mk 1 := h
      rw [ConjClasses.mk_eq_mk_iff_isConj] at h'
      exact isConj_one_right.mp h'.symm
    have hne := X.classRep_ne_one p.1.1.2
    obtain ⟨γ₀, m, hm, hγm, -, -, -, -, -, -, hinf⟩ :=
      exists_root_lengths X.cocompactFree hhyp _ hne
    have : γ₀ ^ ((m * (p.2 + 1) : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, pow_mul, ← hγm, h1]
    have := hinf _ this
    have : m * (p.2 + 1) = 0 := by exact_mod_cast this
    rcases Nat.mul_eq_zero.mp this with h | h <;> omega⟩

theorem primPow_bijective : Function.Bijective (primPow hhyp (X := X)) := by
  have hΓ := X.cocompactFree
  constructor
  · rintro ⟨p, n⟩ ⟨q, k⟩ h
    have h' : ConjClasses.mk (X.classRep p.1.1 ^ (n + 1)) =
        ConjClasses.mk (X.classRep q.1.1 ^ (k + 1)) := congrArg Subtype.val h
    rw [ConjClasses.mk_eq_mk_iff_isConj] at h'
    have hp1 := X.classRep_ne_one p.1.2
    have hq1 := X.classRep_ne_one q.1.2
    have hpp : hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) = primLen (X.classRep p.1.1) := p.2
    have hqp : hypLen ((X.classRep q.1.1 : X.Γ) : SL(2, ℝ)) = primLen (X.classRep q.1.1) := q.2
    obtain ⟨hc, hnk⟩ := isConj_of_isConj_pow hΓ hhyp (by omega) (by omega) hp1 hq1 hpp hqp h'
    have hpq : p.1.1 = q.1.1 := by
      rw [← X.mk_classRep p.1.1, ← X.mk_classRep q.1.1]
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr hc
    have : p = q := Subtype.ext (Subtype.ext hpq)
    subst this
    simp only [Prod.mk.injEq, true_and]
    omega
  · rintro ⟨c, hc⟩
    have hne := X.classRep_ne_one hc
    obtain ⟨γ₀, m, hm, hγm, h₀, -, hC₀, hp₀, -, -, -⟩ :=
      exists_root_lengths hΓ hhyp _ hne
    -- the class of `γ₀` is primitive
    have hmk0 : ConjClasses.mk γ₀ ≠ 1 := by
      intro h
      have h' : ConjClasses.mk γ₀ = ConjClasses.mk 1 := h
      rw [ConjClasses.mk_eq_mk_iff_isConj] at h'
      exact h₀ (isConj_one_right.mp h'.symm)
    let p : X.PClass := ⟨⟨ConjClasses.mk γ₀, hmk0⟩, by
      show X.classLen (ConjClasses.mk γ₀) = X.classPrimLen (ConjClasses.mk γ₀)
      rw [classLen_mk, classPrimLen_mk, hp₀]⟩
    refine ⟨(p, m - 1), Subtype.ext ?_⟩
    show ConjClasses.mk (X.classRep (ConjClasses.mk γ₀) ^ (m - 1 + 1)) = c
    rw [Nat.sub_add_cancel hm, ← X.mk_classRep c, ConjClasses.mk_eq_mk_iff_isConj, hγm]
    obtain ⟨d, hd⟩ := isConj_iff.mp (X.isConj_classRep γ₀)
    refine isConj_iff.mpr ⟨d, ?_⟩
    rw [← conj_pow, hd]

/-- **Classes ≠ 1 are powers of primitive classes.** -/
def primPowEquiv : X.PClass × ℕ ≃ X.NClass :=
  Equiv.ofBijective _ (primPow_bijective hhyp)

theorem classLen_primPow (p : X.PClass × ℕ) :
    X.classLen (primPow hhyp p) = (p.2 + 1) * X.classLen p.1 := by
  have hne := X.classRep_ne_one p.1.1.2
  obtain ⟨γ₀, m, hm, hγm, h₀, hC, hC₀, hp₀, hpγ, hlen, hinf⟩ :=
    exists_root_lengths X.cocompactFree hhyp _ hne
  have hprim : hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) = primLen (X.classRep p.1.1) := p.1.2
  have hm1 := eq_root_of_primitive hhyp hne hprim hlen hpγ
  subst hm1
  rw [pow_one] at hγm
  show X.classLen (ConjClasses.mk (X.classRep p.1.1 ^ (p.2 + 1))) = _
  rw [classLen_mk, show X.classLen p.1 = hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) from rfl]
  obtain ⟨σ, g, ℓ₀, m', hℓ₀, hm', hgm, hCg, hf⟩ :=
    exists_primitive_root X.cocompactFree hhyp _ hne
  -- `classRep p = g^{m'}` with `m' = 1` by primitivity
  have hlen' : hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) = m' * ℓ₀ := by
    have := hypLen_zpow_frame hf m'
    rw [zpow_natCast, ← Subgroup.coe_pow, ← hgm, abs_of_pos (by positivity),
      Int.cast_natCast] at this
    exact this
  have hpl : primLen (X.classRep p.1.1) = ℓ₀ := primLen_eq hℓ₀ hCg hf
  have hm'1 : m' = 1 := by
    rw [hprim, hpl] at hlen'
    have : (m' : ℝ) = 1 := by
      have := mul_right_cancel₀ hℓ₀.ne' (hlen'.symm.trans (one_mul ℓ₀).symm)
      exact this
    exact_mod_cast this
  subst hm'1
  rw [pow_one] at hgm
  have h1 := hypLen_zpow_frame hf ((p.2 + 1 : ℕ) : ℤ)
  rw [zpow_natCast, ← Subgroup.coe_pow, ← hgm] at h1
  rw [h1, hlen', abs_of_pos (by positivity)]
  push_cast
  ring

theorem classPrimLen_primPow (p : X.PClass × ℕ) :
    X.classPrimLen (primPow hhyp p) = X.classLen p.1 := by
  have hne := X.classRep_ne_one p.1.1.2
  have hprim : hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) = primLen (X.classRep p.1.1) := p.1.2
  obtain ⟨σ, g, ℓ₀, m', hℓ₀, hm', hgm, hCg, hf⟩ :=
    exists_primitive_root X.cocompactFree hhyp _ hne
  have hpl : primLen (X.classRep p.1.1) = ℓ₀ := primLen_eq hℓ₀ hCg hf
  have hlen' : hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) = m' * ℓ₀ := by
    have := hypLen_zpow_frame hf m'
    rw [zpow_natCast, ← Subgroup.coe_pow, ← hgm, abs_of_pos (by positivity),
      Int.cast_natCast] at this
    exact this
  have hm'1 : m' = 1 := by
    rw [hprim, hpl] at hlen'
    have : (m' : ℝ) = 1 := by
      have := mul_right_cancel₀ hℓ₀.ne' (hlen'.symm.trans (one_mul ℓ₀).symm)
      exact this
    exact_mod_cast this
  subst hm'1
  rw [pow_one] at hgm
  show X.classPrimLen (ConjClasses.mk (X.classRep p.1.1 ^ (p.2 + 1))) = _
  rw [classPrimLen_mk, show X.classLen p.1 = hypLen ((X.classRep p.1.1 : X.Γ) : SL(2, ℝ)) from rfl,
    hprim, hpl, hgm]
  -- the centralizer of `g^{n+1}` is `⟨g⟩`
  apply primLen_eq hℓ₀ _ hf
  intro δ
  constructor
  · intro h
    have hne' : (g ^ (p.2 + 1) : X.Γ) ≠ 1 := by
      intro h1
      have := zpow_eq_one_of_frame hℓ₀ hf (k := ((p.2 + 1 : ℕ) : ℤ))
        (by rw [zpow_natCast, ← Subgroup.coe_pow, h1]; rfl)
      omega
    obtain ⟨g', hg'1, hC', hlen', hinf', -⟩ := hypLen_zpow_root X.cocompactFree hhyp hne'
    obtain ⟨i, hi⟩ := (hC' g).mp (Commute.pow_right (Commute.refl g) _).eq
    have hgprim : hypLen (g : SL(2, ℝ)) = primLen g := by rw [← hgm, hprim, hgm]
    have hg1 : g ≠ 1 := by rw [← hgm]; exact hne
    rcases zpow_eq_pm_one_of_primitive X.cocompactFree hhyp hg1 hi hgprim hg'1 hlen' with
      rfl | rfl
    · obtain ⟨k, hk⟩ := (hC' δ).mp h
      exact ⟨k, by rw [hk, hi, zpow_one]⟩
    · obtain ⟨k, hk⟩ := (hC' δ).mp h
      exact ⟨-k, by rw [hk, hi, zpow_neg_one, inv_zpow', neg_neg]⟩
  · rintro ⟨k, rfl⟩
    exact (Commute.zpow_left (Commute.pow_right (Commute.refl g) _) k).eq

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
