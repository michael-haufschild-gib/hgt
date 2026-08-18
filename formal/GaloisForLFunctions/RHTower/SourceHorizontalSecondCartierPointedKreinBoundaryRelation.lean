import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPhysicalOrderModerationNoGo

open Complex
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

abbrev SourceHorizontalSecondCartierKreinJet := ℂ × (ℂ × ℂ)

def sourceHorizontalSecondCartierKreinUnit :
    SourceHorizontalSecondCartierKreinJet := (1, (0, 0))

def sourceHorizontalSecondCartierKreinGhost (c : ℂ) :
    SourceHorizontalSecondCartierKreinJet := (0, (c, c))

def sourceHorizontalSecondCartierKreinDifference :
    SourceHorizontalSecondCartierKreinJet := (0, (1, -1))

def sourceHorizontalSecondCartierKreinForm
    (x y : SourceHorizontalSecondCartierKreinJet) : ℂ :=
  star x.1 * (y.2.1 + y.2.2) +
    star (x.2.1 + x.2.2) * y.1 +
    star (x.2.1 - x.2.2) * (y.2.1 - y.2.2)

theorem sourceHorizontalSecondCartierPointedKrein_form_hermitian
    (x y : SourceHorizontalSecondCartierKreinJet) :
    star (sourceHorizontalSecondCartierKreinForm y x) =
      sourceHorizontalSecondCartierKreinForm x y := by
  rcases x with ⟨u, a, b⟩
  rcases y with ⟨v, d, e⟩
  simp [sourceHorizontalSecondCartierKreinForm, star_add, star_sub, star_mul]
  ring

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_form_unit_self :
    sourceHorizontalSecondCartierKreinForm
      sourceHorizontalSecondCartierKreinUnit
      sourceHorizontalSecondCartierKreinUnit = 0 := by
  simp [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinUnit]

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_form_ghost_self (c : ℂ) :
    sourceHorizontalSecondCartierKreinForm
      (sourceHorizontalSecondCartierKreinGhost c)
      (sourceHorizontalSecondCartierKreinGhost c) = 0 := by
  simp [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinGhost]

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_form_unit_ghost (c : ℂ) :
    sourceHorizontalSecondCartierKreinForm
      sourceHorizontalSecondCartierKreinUnit
      (sourceHorizontalSecondCartierKreinGhost c) = 2 * c := by
  simp [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinUnit,
    sourceHorizontalSecondCartierKreinGhost]
  ring

theorem sourceHorizontalSecondCartierPointedKrein_ghost_not_radical {c : ℂ} (hc : c ≠ 0) :
    sourceHorizontalSecondCartierKreinGhost c ≠ 0 ∧
      sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinGhost c)
        (sourceHorizontalSecondCartierKreinGhost c) = 0 ∧
      sourceHorizontalSecondCartierKreinForm
        sourceHorizontalSecondCartierKreinUnit
        (sourceHorizontalSecondCartierKreinGhost c) ≠ 0 := by
  refine ⟨?_, sourceHorizontalSecondCartierPointedKrein_form_ghost_self c, ?_⟩
  · intro h
    have hforward := congrArg (fun z => z.2.1) h
    simpa [sourceHorizontalSecondCartierKreinGhost] using hc hforward
  · rw [sourceHorizontalSecondCartierPointedKrein_form_unit_ghost]
    exact mul_ne_zero (by norm_num) hc

theorem sourceHorizontalSecondCartierPointedKrein_form_nondegenerate
    {x : SourceHorizontalSecondCartierKreinJet}
    (h : ∀ y, sourceHorizontalSecondCartierKreinForm x y = 0) :
    x = 0 := by
  rcases x with ⟨u, a, b⟩
  have hunit := h sourceHorizontalSecondCartierKreinUnit
  have hghost := h (sourceHorizontalSecondCartierKreinGhost 1)
  have hdiff := h sourceHorizontalSecondCartierKreinDifference
  simp [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinUnit,
    sourceHorizontalSecondCartierKreinGhost,
    sourceHorizontalSecondCartierKreinDifference] at hunit hghost hdiff
  have hsa : star a = 0 := by
    linear_combination (hunit + hdiff) / 2
  have hsb : star b = 0 := by
    linear_combination (hunit - hdiff) / 2
  have ha : a = 0 := by
    have ha' := congrArg star hsa
    simpa using ha'
  have hb : b = 0 := by
    have hb' := congrArg star hsb
    simpa using hb'
  simp [hghost, ha, hb]

theorem sourceHorizontalSecondCartierPointedKrein_form_indefinite :
    sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinUnit +
          sourceHorizontalSecondCartierKreinGhost 1)
        (sourceHorizontalSecondCartierKreinUnit +
          sourceHorizontalSecondCartierKreinGhost 1) = 4 ∧
      sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinUnit -
          sourceHorizontalSecondCartierKreinGhost 1)
        (sourceHorizontalSecondCartierKreinUnit -
          sourceHorizontalSecondCartierKreinGhost 1) = -4 := by
  constructor <;>
    simp [sourceHorizontalSecondCartierKreinForm,
      sourceHorizontalSecondCartierKreinUnit,
      sourceHorizontalSecondCartierKreinGhost] <;>
    ring

def sourceHorizontalSecondCartierKreinCanonicalLift
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource) :
    SourceHorizontalSecondCartierKreinJet :=
  (0, (c * v.1, c * v.2))

def sourceHorizontalSecondCartierKreinBoundaryRelation (c : ℂ) :
    Submodule ℂ
      (SourceHorizontalBilateralSecondJetSource ×
        SourceHorizontalSecondCartierKreinJet) where
  carrier := {p | p.2.2.1 = c * p.1.1 ∧ p.2.2.2 = c * p.1.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    constructor
    · simp only [Prod.fst_add, Prod.snd_add]
      rw [hx1, hy1]
      ring
    · simp only [Prod.fst_add, Prod.snd_add]
      rw [hx2, hy2]
      ring
  smul_mem' := by
    intro a x hx
    rcases hx with ⟨hx1, hx2⟩
    constructor
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [hx1]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [hx2]
      ring

theorem sourceHorizontalSecondCartierPointedKrein_relation_iff
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet) :
    (v, w) ∈ sourceHorizontalSecondCartierKreinBoundaryRelation c ↔
      ∃ u : ℂ, w = (u, (c * v.1, c * v.2)) := by
  change (w.2.1 = c * v.1 ∧ w.2.2 = c * v.2) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨w.1, by ext <;> simp [h1, h2]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨rfl, rfl⟩

theorem sourceHorizontalSecondCartierPointedKrein_canonical_mem
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource) :
    (v, sourceHorizontalSecondCartierKreinCanonicalLift c v) ∈
      sourceHorizontalSecondCartierKreinBoundaryRelation c := by
  change c * v.1 = c * v.1 ∧ c * v.2 = c * v.2
  exact ⟨rfl, rfl⟩

theorem sourceHorizontalSecondCartierPointedKrein_vertical_iff
    (c : ℂ) (w : SourceHorizontalSecondCartierKreinJet) :
    ((0 : SourceHorizontalBilateralSecondJetSource), w) ∈
        sourceHorizontalSecondCartierKreinBoundaryRelation c ↔
      ∃ u : ℂ, w = u • sourceHorizontalSecondCartierKreinUnit := by
  rw [sourceHorizontalSecondCartierPointedKrein_relation_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by ext <;> simp [sourceHorizontalSecondCartierKreinUnit]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, by ext <;> simp [sourceHorizontalSecondCartierKreinUnit]⟩

theorem sourceHorizontalSecondCartierPointedKrein_relation_multivalued (c : ℂ) :
    ∃ w₁ w₂ : SourceHorizontalSecondCartierKreinJet,
      w₁ ≠ w₂ ∧
      ((0 : SourceHorizontalBilateralSecondJetSource), w₁) ∈
        sourceHorizontalSecondCartierKreinBoundaryRelation c ∧
      ((0 : SourceHorizontalBilateralSecondJetSource), w₂) ∈
        sourceHorizontalSecondCartierKreinBoundaryRelation c := by
  refine ⟨0, sourceHorizontalSecondCartierKreinUnit, ?_, ?_, ?_⟩
  · intro h
    have hanchor := congrArg Prod.fst h
    norm_num [sourceHorizontalSecondCartierKreinUnit] at hanchor
  · exact (sourceHorizontalSecondCartierPointedKrein_vertical_iff c 0).2 ⟨0, by simp⟩
  · exact (sourceHorizontalSecondCartierPointedKrein_vertical_iff c sourceHorizontalSecondCartierKreinUnit).2
      ⟨1, by simp⟩

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_lift_forward (c : ℂ) :
    sourceHorizontalSecondCartierKreinCanonicalLift c
        sourceHorizontalBilateralSecondJetForward = (0, (c, 0)) := by
  simp [sourceHorizontalSecondCartierKreinCanonicalLift,
    sourceHorizontalBilateralSecondJetForward]

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_lift_inverse (c : ℂ) :
    sourceHorizontalSecondCartierKreinCanonicalLift c
        sourceHorizontalBilateralSecondJetInverse = (0, (0, c)) := by
  simp [sourceHorizontalSecondCartierKreinCanonicalLift,
    sourceHorizontalBilateralSecondJetInverse]

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_lift_ghost (c : ℂ) :
    sourceHorizontalSecondCartierKreinCanonicalLift c
        sourceHorizontalBilateralSecondJetGhost =
      sourceHorizontalSecondCartierKreinGhost c := by
  simp [sourceHorizontalSecondCartierKreinCanonicalLift,
    sourceHorizontalBilateralSecondJetGhost,
    sourceHorizontalSecondCartierKreinGhost]

def sourceHorizontalSecondCartierKreinSourceTransfer
    (lam : ℂ) (v : SourceHorizontalBilateralSecondJetSource) :
    SourceHorizontalBilateralSecondJetSource :=
  ((((star lam)⁻¹ * (v.1 + v.2) + (v.1 - v.2)) / 2),
    (((star lam)⁻¹ * (v.1 + v.2) - (v.1 - v.2)) / 2))

def sourceHorizontalSecondCartierKreinJetTransfer
    (lam : ℂ) (x : SourceHorizontalSecondCartierKreinJet) :
    SourceHorizontalSecondCartierKreinJet :=
  (lam * x.1, sourceHorizontalSecondCartierKreinSourceTransfer lam x.2)

theorem sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sum (lam : ℂ)
    (v : SourceHorizontalBilateralSecondJetSource) :
    (sourceHorizontalSecondCartierKreinSourceTransfer lam v).1 +
        (sourceHorizontalSecondCartierKreinSourceTransfer lam v).2 =
      (star lam)⁻¹ * (v.1 + v.2) := by
  simp [sourceHorizontalSecondCartierKreinSourceTransfer]
  ring

theorem sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sub (lam : ℂ)
    (v : SourceHorizontalBilateralSecondJetSource) :
    (sourceHorizontalSecondCartierKreinSourceTransfer lam v).1 -
        (sourceHorizontalSecondCartierKreinSourceTransfer lam v).2 =
      v.1 - v.2 := by
  simp [sourceHorizontalSecondCartierKreinSourceTransfer]
  ring

theorem sourceHorizontalSecondCartierPointedKrein_transfer_form {lam : ℂ} (hlam : lam ≠ 0)
    (x y : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinJetTransfer lam x)
        (sourceHorizontalSecondCartierKreinJetTransfer lam y) =
      sourceHorizontalSecondCartierKreinForm x y := by
  rw [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinJetTransfer]
  simp only [sourceHorizontalSecondCartierKreinJetTransfer]
  rw [
    sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sum, sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sum,
    sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sub, sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sub]
  rw [star_mul, star_mul, star_inv₀, star_star]
  have hstar : star lam ≠ 0 := star_ne_zero.mpr hlam
  field_simp
  rw [sourceHorizontalSecondCartierKreinForm]

theorem sourceHorizontalSecondCartierPointedKrein_relation_covariant
    (c lam : ℂ) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : (v, w) ∈ sourceHorizontalSecondCartierKreinBoundaryRelation c) :
    (sourceHorizontalSecondCartierKreinSourceTransfer lam v,
      sourceHorizontalSecondCartierKreinJetTransfer lam w) ∈
        sourceHorizontalSecondCartierKreinBoundaryRelation c := by
  change (w.2.1 = c * v.1 ∧ w.2.2 = c * v.2) at h
  rcases h with ⟨h1, h2⟩
  change
    (sourceHorizontalSecondCartierKreinSourceTransfer lam w.2).1 =
        c * (sourceHorizontalSecondCartierKreinSourceTransfer lam v).1 ∧
      (sourceHorizontalSecondCartierKreinSourceTransfer lam w.2).2 =
        c * (sourceHorizontalSecondCartierKreinSourceTransfer lam v).2
  rw [sourceHorizontalSecondCartierKreinSourceTransfer,
    sourceHorizontalSecondCartierKreinSourceTransfer]
  simp only
  rw [h1, h2]
  constructor <;> ring

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_transfer_unit (lam : ℂ) :
    sourceHorizontalSecondCartierKreinJetTransfer lam
        sourceHorizontalSecondCartierKreinUnit =
      lam • sourceHorizontalSecondCartierKreinUnit := by
  ext <;> simp [sourceHorizontalSecondCartierKreinJetTransfer,
    sourceHorizontalSecondCartierKreinSourceTransfer,
    sourceHorizontalSecondCartierKreinUnit]

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_transfer_ghost (lam c : ℂ) :
    sourceHorizontalSecondCartierKreinJetTransfer lam
        (sourceHorizontalSecondCartierKreinGhost c) =
      (star lam)⁻¹ • sourceHorizontalSecondCartierKreinGhost c := by
  ext <;> simp [sourceHorizontalSecondCartierKreinJetTransfer,
    sourceHorizontalSecondCartierKreinSourceTransfer,
    sourceHorizontalSecondCartierKreinGhost] <;> ring

/-- The relation is not the graph of a single-valued map: its free anchor is essential. -/
theorem sourceHorizontalSecondCartierPointedKrein_relation_not_graph (c : ℂ) :
    ¬ ∃ f : SourceHorizontalBilateralSecondJetSource →
        SourceHorizontalSecondCartierKreinJet,
      ∀ v w, (v, w) ∈ sourceHorizontalSecondCartierKreinBoundaryRelation c ↔
        w = f v := by
  rintro ⟨f, hf⟩
  have hzero : (0 : SourceHorizontalSecondCartierKreinJet) = f 0 :=
    (hf 0 0).1 ((sourceHorizontalSecondCartierPointedKrein_vertical_iff c 0).2 ⟨0, by simp⟩)
  have hunit : sourceHorizontalSecondCartierKreinUnit = f 0 :=
    (hf 0 sourceHorizontalSecondCartierKreinUnit).1
      ((sourceHorizontalSecondCartierPointedKrein_vertical_iff c sourceHorizontalSecondCartierKreinUnit).2
        ⟨1, by simp⟩)
  have h := hzero.trans hunit.symm
  have hanchor := congrArg Prod.fst h
  norm_num [sourceHorizontalSecondCartierKreinUnit] at hanchor

/-- Any antisymmetric additive physical order must reject at least one of `G` and `-G`. -/
theorem sourceHorizontalSecondCartierPointedKrein_ghost_not_bipositive
    [PartialOrder SourceHorizontalSecondCartierKreinJet]
    [IsOrderedAddMonoid SourceHorizontalSecondCartierKreinJet]
    {c : ℂ} (hc : c ≠ 0) :
    ¬ (0 ≤ sourceHorizontalSecondCartierKreinGhost c ∧
      0 ≤ -sourceHorizontalSecondCartierKreinGhost c) := by
  rintro ⟨hpos, hneg⟩
  have hle : sourceHorizontalSecondCartierKreinGhost c ≤ 0 :=
    (neg_nonneg.mp hneg)
  exact (sourceHorizontalSecondCartierPointedKrein_ghost_not_radical hc).1 (le_antisymm hle hpos)

def sourceHorizontalSecondCartierKreinSourceSwap
    (v : SourceHorizontalBilateralSecondJetSource) :
    SourceHorizontalBilateralSecondJetSource := (v.2, v.1)

def sourceHorizontalSecondCartierKreinJetSwap
    (w : SourceHorizontalSecondCartierKreinJet) :
    SourceHorizontalSecondCartierKreinJet := (w.1, (w.2.2, w.2.1))

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_sourceSwap_involutive
    (v : SourceHorizontalBilateralSecondJetSource) :
    sourceHorizontalSecondCartierKreinSourceSwap
        (sourceHorizontalSecondCartierKreinSourceSwap v) = v := by
  rcases v with ⟨a, b⟩
  rfl

@[simp] theorem sourceHorizontalSecondCartierPointedKrein_jetSwap_involutive
    (w : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinJetSwap
        (sourceHorizontalSecondCartierKreinJetSwap w) = w := by
  rcases w with ⟨u, a, b⟩
  rfl

theorem sourceHorizontalSecondCartierPointedKrein_swap_form
    (x y : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinJetSwap x)
        (sourceHorizontalSecondCartierKreinJetSwap y) =
      sourceHorizontalSecondCartierKreinForm x y := by
  rcases x with ⟨u, a, b⟩
  rcases y with ⟨v, d, e⟩
  simp [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinJetSwap, star_sub]
  ring

theorem sourceHorizontalSecondCartierPointedKrein_swap_relation
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : (v, w) ∈ sourceHorizontalSecondCartierKreinBoundaryRelation c) :
    (sourceHorizontalSecondCartierKreinSourceSwap v,
      sourceHorizontalSecondCartierKreinJetSwap w) ∈
        sourceHorizontalSecondCartierKreinBoundaryRelation c := by
  change (w.2.1 = c * v.1 ∧ w.2.2 = c * v.2) at h
  change (w.2.2 = c * v.2 ∧ w.2.1 = c * v.1)
  exact h.symm

theorem sourceHorizontalSecondCartierPointedKrein_sourceTransfer_swap_commute
    (lam : ℂ) (v : SourceHorizontalBilateralSecondJetSource) :
    sourceHorizontalSecondCartierKreinSourceTransfer lam
        (sourceHorizontalSecondCartierKreinSourceSwap v) =
      sourceHorizontalSecondCartierKreinSourceSwap
        (sourceHorizontalSecondCartierKreinSourceTransfer lam v) := by
  rcases v with ⟨a, b⟩
  ext <;> simp [sourceHorizontalSecondCartierKreinSourceTransfer,
    sourceHorizontalSecondCartierKreinSourceSwap] <;> ring

theorem sourceHorizontalSecondCartierPointedKrein_jetTransfer_swap_commute
    (lam : ℂ) (w : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinJetTransfer lam
        (sourceHorizontalSecondCartierKreinJetSwap w) =
      sourceHorizontalSecondCartierKreinJetSwap
        (sourceHorizontalSecondCartierKreinJetTransfer lam w) := by
  rcases w with ⟨u, a, b⟩
  ext <;> simp [sourceHorizontalSecondCartierKreinJetTransfer,
    sourceHorizontalSecondCartierKreinSourceTransfer,
    sourceHorizontalSecondCartierKreinJetSwap] <;> ring

/-- A complex-linear transverse anchor cannot turn the reciprocal-star ghost leg into the unit
anchor leg unless the transfer character is unitary.  This is the sharp boundary between the
constructed multivalued relation and the already-impossible single-valued linear reporter. -/
theorem sourceHorizontalSecondCartierPointedKrein_anchor_covariance_norm_eq_one
    {lam : ℂ} (hlam : lam ≠ 0)
    (A : SourceHorizontalBilateralSecondJetSource →ₗ[ℂ] ℂ)
    (hA : A sourceHorizontalBilateralSecondJetGhost ≠ 0)
    (hcov : A (sourceHorizontalSecondCartierKreinSourceTransfer lam
        sourceHorizontalBilateralSecondJetGhost) =
      lam * A sourceHorizontalBilateralSecondJetGhost) :
    ‖lam‖ = 1 := by
  have hsource : sourceHorizontalSecondCartierKreinSourceTransfer lam
        sourceHorizontalBilateralSecondJetGhost =
      (star lam)⁻¹ • sourceHorizontalBilateralSecondJetGhost := by
    ext <;> simp [sourceHorizontalSecondCartierKreinSourceTransfer,
      sourceHorizontalBilateralSecondJetGhost] <;> ring
  rw [hsource, map_smul] at hcov
  simp only [smul_eq_mul] at hcov
  have hcoeff : (star lam)⁻¹ = lam := mul_right_cancel₀ hA hcov
  have hmul : star lam * lam = 1 := by
    calc
      star lam * lam = star lam * (star lam)⁻¹ := by rw [hcoeff]
      _ = 1 := mul_inv_cancel₀ (star_ne_zero.mpr hlam)
  have hnorm := congrArg norm hmul
  simp only [norm_mul, norm_star, norm_one] at hnorm
  nlinarith [norm_nonneg lam]

/-! ## Actual Xi-selected coefficient-faithful relation -/

def sourceHorizontalActualXiSecondCartierKreinScale
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) : ℂ :=
  (sourceHorizontalWoldBVKreinGhostEnergy
    (sourceHorizontalActualXiConormalCoefficient x u q r) N : ℂ)

def sourceHorizontalActualXiSecondCartierKreinBoundaryRelation
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :=
  sourceHorizontalSecondCartierKreinBoundaryRelation
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

def sourceHorizontalActualXiSecondCartierKreinGhost
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :=
  sourceHorizontalSecondCartierKreinGhost
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

def sourceHorizontalActualXiSecondCartierKreinPrimeCharacter
    (q : XiRightZeroCopy) (p : Nat.Primes) : ℂ :=
  bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)

theorem sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    sourceHorizontalActualXiSecondCartierKreinScale x u q r N ≠ 0 := by
  have hc : sourceHorizontalActualXiConormalCoefficient x u q r ≠ 0 :=
    sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  have hscale : sourceHorizontalWoldBVKreinGhostEnergy
      (sourceHorizontalActualXiConormalCoefficient x u q r) N ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (by norm_num)
      (Complex.normSq_pos.mpr hc)) hjet)
  rw [sourceHorizontalActualXiSecondCartierKreinScale]
  exact_mod_cast hscale

theorem sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p ≠ 0 := by
  have hp0 : 0 < (p : ℕ) := lt_of_lt_of_le two_pos p.2.two_le
  exact bilateralHalfDensityCharacter_ne_zero hp0 _

theorem sourceHorizontalSecondCartierPointedKrein_actual_ghost_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1) (N : ℕ) :
    sourceHorizontalActualXiSecondCartierKreinGhost x u s r N =
      sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by
  rw [sourceHorizontalActualXiSecondCartierKreinGhost,
    sourceHorizontalActualXiSecondCartierKreinGhost,
    sourceHorizontalActualXiSecondCartierKreinScale,
    sourceHorizontalActualXiSecondCartierKreinScale,
    sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h]

theorem sourceHorizontalSecondCartierPointedKrein_actual_ghost_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiSecondCartierKreinGhost x u s.1 r N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by
  calc
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiSecondCartierKreinGhost x u s.1 r N) =
        ∑ _s : XiRightSupportFiber q,
          sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact sourceHorizontalSecondCartierPointedKrein_actual_ghost_eq_of_support x u r s.2 N
    _ = Fintype.card (XiRightSupportFiber q) •
          sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by simp
    _ = xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by
            rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

theorem sourceHorizontalSecondCartierPointedKrein_actual_relation_vertical_iff
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (w : SourceHorizontalSecondCartierKreinJet) :
    ((0 : SourceHorizontalBilateralSecondJetSource), w) ∈
        sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N ↔
      ∃ a : ℂ, w = a • sourceHorizontalSecondCartierKreinUnit := by
  exact sourceHorizontalSecondCartierPointedKrein_vertical_iff
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) w

theorem sourceHorizontalSecondCartierPointedKrein_actual_relation_not_graph
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    ¬ ∃ f : SourceHorizontalBilateralSecondJetSource →
        SourceHorizontalSecondCartierKreinJet,
      ∀ v w,
        (v, w) ∈
            sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N ↔
          w = f v := by
  exact sourceHorizontalSecondCartierPointedKrein_relation_not_graph
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

theorem sourceHorizontalSecondCartierPointedKrein_actual_forward_mem
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (sourceHorizontalBilateralSecondJetForward,
      sourceHorizontalSecondCartierKreinCanonicalLift
        (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)
        sourceHorizontalBilateralSecondJetForward) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N := by
  exact sourceHorizontalSecondCartierPointedKrein_canonical_mem _ _

theorem sourceHorizontalSecondCartierPointedKrein_actual_inverse_mem
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (sourceHorizontalBilateralSecondJetInverse,
      sourceHorizontalSecondCartierKreinCanonicalLift
        (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)
        sourceHorizontalBilateralSecondJetInverse) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N := by
  exact sourceHorizontalSecondCartierPointedKrein_canonical_mem _ _

theorem sourceHorizontalSecondCartierPointedKrein_actual_ghost_mem
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (sourceHorizontalBilateralSecondJetGhost,
      sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N := by
  simpa [sourceHorizontalActualXiSecondCartierKreinGhost,
    sourceHorizontalActualXiSecondCartierKreinBoundaryRelation] using
    (sourceHorizontalSecondCartierPointedKrein_canonical_mem
      (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)
      sourceHorizontalBilateralSecondJetGhost)

theorem sourceHorizontalSecondCartierPointedKrein_actual_ghost_null_not_radical
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    sourceHorizontalActualXiSecondCartierKreinGhost x u q r N ≠ 0 ∧
      sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N)
        (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) = 0 ∧
      sourceHorizontalSecondCartierKreinForm
        sourceHorizontalSecondCartierKreinUnit
        (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) ≠ 0 := by
  exact sourceHorizontalSecondCartierPointedKrein_ghost_not_radical
    (sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero q hkappa hr N hjet)

theorem sourceHorizontalSecondCartierPointedKrein_actual_primeTransfer_form
    (q : XiRightZeroCopy) (p : Nat.Primes)
    (a b : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinJetTransfer
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) a)
        (sourceHorizontalSecondCartierKreinJetTransfer
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) b) =
      sourceHorizontalSecondCartierKreinForm a b := by
  exact sourceHorizontalSecondCartierPointedKrein_transfer_form (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p) a b

theorem sourceHorizontalSecondCartierPointedKrein_actual_relation_primeTransfer_covariant
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : (v, w) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N) :
    (sourceHorizontalSecondCartierKreinSourceTransfer
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) v,
      sourceHorizontalSecondCartierKreinJetTransfer
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) w) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N := by
  exact sourceHorizontalSecondCartierPointedKrein_relation_covariant _ _ _ _ h

theorem sourceHorizontalSecondCartierPointedKrein_actual_ghost_primeTransfer_eigen
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) :
    sourceHorizontalSecondCartierKreinJetTransfer
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
        (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) =
      (star (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p))⁻¹ •
        sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by
  exact sourceHorizontalSecondCartierPointedKrein_transfer_ghost _ _

theorem sourceHorizontalSecondCartierPointedKrein_actual_relation_swap_covariant
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : (v, w) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N) :
    (sourceHorizontalSecondCartierKreinSourceSwap v,
      sourceHorizontalSecondCartierKreinJetSwap w) ∈
      sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N := by
  exact sourceHorizontalSecondCartierPointedKrein_swap_relation _ _ _ h

theorem sourceHorizontalSecondCartierPointedKrein_actual_ghost_not_bipositive
    [PartialOrder SourceHorizontalSecondCartierKreinJet]
    [IsOrderedAddMonoid SourceHorizontalSecondCartierKreinJet]
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    ¬ (0 ≤ sourceHorizontalActualXiSecondCartierKreinGhost x u q r N ∧
      0 ≤ -sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) := by
  exact sourceHorizontalSecondCartierPointedKrein_ghost_not_bipositive
    (sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero q hkappa hr N hjet)

/-- On a strict-right Xi fibre no nonzero complex-linear anchor can intertwine the ghost's
reciprocal-star source action with the unit anchor action.  Thus the surviving producer is
genuinely relational: completing it by a linear physical section would already force criticality. -/
theorem sourceHorizontalSecondCartierPointedKrein_strictRight_no_linear_transverse_anchor
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    ¬ ∃ A : SourceHorizontalBilateralSecondJetSource →ₗ[ℂ] ℂ,
      A sourceHorizontalBilateralSecondJetGhost ≠ 0 ∧
        A (sourceHorizontalSecondCartierKreinSourceTransfer
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
            sourceHorizontalBilateralSecondJetGhost) =
          sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p *
            A sourceHorizontalBilateralSecondJetGhost := by
  rintro ⟨A, hA, hcov⟩
  have hnorm :
      ‖sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p‖ = 1 :=
    sourceHorizontalSecondCartierPointedKrein_anchor_covariance_norm_eq_one
      (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p)
      A hA hcov
  have hline := (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le
    (q.1.1 : XiDivisorSupport)).1 hnorm
  have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  exact (ne_of_gt hright) hline

/-- **Producer capstone.** Literal completed Xi coefficient enters a genuinely multivalued
pointed Krein relation.  Its sole vertical freedom is the unit anchor; the quadratic source ghost
is retained, null but nonradical; prime transfer preserves both relation and indefinite form; and
support-fibre summation restores analytic multiplicity. -/
theorem sourceHorizontalSecondCartierPointedKrein_actual_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    sourceHorizontalActualXiSecondCartierKreinScale x u q r N ≠ 0 ∧
      (¬ ∃ f : SourceHorizontalBilateralSecondJetSource →
          SourceHorizontalSecondCartierKreinJet,
        ∀ v w,
          (v, w) ∈ sourceHorizontalActualXiSecondCartierKreinBoundaryRelation
              x u q r N ↔ w = f v) ∧
      (∀ w : SourceHorizontalSecondCartierKreinJet,
        ((0 : SourceHorizontalBilateralSecondJetSource), w) ∈
            sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N ↔
          ∃ a : ℂ, w = a • sourceHorizontalSecondCartierKreinUnit) ∧
      (sourceHorizontalBilateralSecondJetGhost,
          sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) ∈
        sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N ∧
      (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N ≠ 0 ∧
        sourceHorizontalSecondCartierKreinForm
          (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N)
          (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) = 0 ∧
        sourceHorizontalSecondCartierKreinForm
          sourceHorizontalSecondCartierKreinUnit
          (sourceHorizontalActualXiSecondCartierKreinGhost x u q r N) ≠ 0) ∧
      (∀ a b : SourceHorizontalSecondCartierKreinJet,
        sourceHorizontalSecondCartierKreinForm
            (sourceHorizontalSecondCartierKreinJetTransfer
              (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) a)
            (sourceHorizontalSecondCartierKreinJetTransfer
              (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) b) =
          sourceHorizontalSecondCartierKreinForm a b) ∧
      (∀ v w,
        (v, w) ∈ sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N →
          (sourceHorizontalSecondCartierKreinSourceTransfer
              (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) v,
            sourceHorizontalSecondCartierKreinJetTransfer
              (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) w) ∈
            sourceHorizontalActualXiSecondCartierKreinBoundaryRelation x u q r N) ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiSecondCartierKreinGhost x u s.1 r N) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinGhost x u q r N := by
  refine ⟨sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero q hkappa hr N hjet,
    sourceHorizontalSecondCartierPointedKrein_actual_relation_not_graph x u q r N,
    sourceHorizontalSecondCartierPointedKrein_actual_relation_vertical_iff x u q r N,
    sourceHorizontalSecondCartierPointedKrein_actual_ghost_mem x u q r N,
    sourceHorizontalSecondCartierPointedKrein_actual_ghost_null_not_radical q hkappa hr N hjet,
    sourceHorizontalSecondCartierPointedKrein_actual_primeTransfer_form q p,
    ?_, sourceHorizontalSecondCartierPointedKrein_actual_ghost_fiber_sum x u q r N⟩
  intro v w h
  exact sourceHorizontalSecondCartierPointedKrein_actual_relation_primeTransfer_covariant x u q r N p v w h

end

end RHTower
