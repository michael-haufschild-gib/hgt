import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy

/-!
# Support--grade inverse-semigroup fusion

This file formalizes the complete abstract and operator-theoretic surface of ULF-RFHM-1.
A meet-semilattice records native support, a group records reversible history, and a compatible
group action transports support before intersection.  Their semidirect product is an inverse
semigroup.  Its canonical representation on `ℓ²(E × G)` is faithful, uniformly norm-separated,
and proper on compact sets.  Compatible support/history symmetries act by unitary conjugation.
-/

open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- A group action on a meet-semilattice with bottom which preserves both native operations. -/
class SupportGradeAction (G : Type v) (E : Type u) [Group G] [SemilatticeInf E] [OrderBot E]
    extends MulAction G E where
  smul_inf : ∀ (g : G) (e f : E), g • (e ⊓ f) = (g • e) ⊓ (g • f)
  smul_bot : ∀ (g : G), g • (⊥ : E) = ⊥

variable {E : Type u} {G : Type v}
variable [SemilatticeInf E] [OrderBot E] [Group G] [SupportGradeAction G E]

@[simp] theorem supportGrade_smul_inf (g : G) (e f : E) :
    g • (e ⊓ f) = (g • e) ⊓ (g • f) :=
  SupportGradeAction.smul_inf g e f

@[simp] theorem supportGrade_smul_bot (g : G) : g • (⊥ : E) = ⊥ :=
  SupportGradeAction.smul_bot g

theorem supportGrade_smul_mono (g : G) {e f : E} (hef : e ≤ f) : g • e ≤ g • f := by
  calc
    g • e = g • (e ⊓ f) := congrArg (g • ·) (inf_eq_left.2 hef).symm
    _ = (g • e) ⊓ (g • f) := supportGrade_smul_inf g e f
    _ ≤ g • f := inf_le_right

theorem supportGrade_smul_le_smul_iff (g : G) {e f : E} :
    g • e ≤ g • f ↔ e ≤ f := by
  constructor
  · intro h
    have := supportGrade_smul_mono (g := g⁻¹) h
    simpa using this
  · exact supportGrade_smul_mono g

theorem supportGrade_smul_le_iff (g : G) {e f : E} :
    g • e ≤ f ↔ e ≤ g⁻¹ • f := by
  constructor
  · intro h
    have := supportGrade_smul_mono (g := g⁻¹) h
    simpa using this
  · intro h
    have := supportGrade_smul_mono (g := g) h
    simpa [mul_smul] using this

/-! ## Native-support no-go -/

/-- Every meet-multiplicative map from a semilattice to a group is trivial. -/
theorem semilatticeToGroup_trivial {H : Type w} [Group H] (φ : E → H)
    (map_inf : ∀ e f, φ (e ⊓ f) = φ e * φ f) (e : E) : φ e = 1 := by
  have hidem : φ e = φ e * φ e := by simpa using map_inf e e
  have h := congrArg (fun z : H => (φ e)⁻¹ * z) hidem
  simpa [mul_assoc] using h.symm

/-! ## The fused inverse semigroup -/

/-- A packet carries native support and reversible grade. -/
structure RestrictionPacket (E : Type u) (G : Type v) where
  support : E
  grade : G
  deriving DecidableEq

namespace RestrictionPacket

instance : Mul (RestrictionPacket E G) where
  mul s t := ⟨s.support ⊓ s.grade • t.support, s.grade * t.grade⟩

@[simp] theorem support_mul (s t : RestrictionPacket E G) :
    (s * t).support = s.support ⊓ s.grade • t.support := rfl

@[simp] theorem grade_mul (s t : RestrictionPacket E G) :
    (s * t).grade = s.grade * t.grade := rfl

/-- The inverse-semigroup involution. -/
def star (s : RestrictionPacket E G) : RestrictionPacket E G :=
  ⟨s.grade⁻¹ • s.support, s.grade⁻¹⟩

@[simp] theorem support_star (s : RestrictionPacket E G) :
    s.star.support = s.grade⁻¹ • s.support := rfl

@[simp] theorem grade_star (s : RestrictionPacket E G) : s.star.grade = s.grade⁻¹ := rfl

@[ext] theorem ext {s t : RestrictionPacket E G}
    (hs : s.support = t.support) (hg : s.grade = t.grade) : s = t := by
  cases s
  cases t
  simp_all

theorem packet_mul_assoc (s t u : RestrictionPacket E G) : (s * t) * u = s * (t * u) := by
  apply ext
  · simp [supportGrade_smul_inf, mul_smul, inf_assoc]
  · simp [mul_assoc]

instance : Semigroup (RestrictionPacket E G) where
  mul_assoc := packet_mul_assoc

/-- Range support, retained in the native semilattice. -/
def rangeSupport (s : RestrictionPacket E G) : E := s.support

/-- Source support, obtained by pulling range support back through history. -/
def sourceSupport (s : RestrictionPacket E G) : E := s.grade⁻¹ • s.support

@[simp] theorem mul_star (s : RestrictionPacket E G) :
    s * s.star = ⟨s.support, 1⟩ := by
  apply ext
  · simp [star]
  · simp [star]

@[simp] theorem star_mul (s : RestrictionPacket E G) :
    s.star * s = ⟨s.grade⁻¹ • s.support, 1⟩ := by
  apply ext
  · simp [star, supportGrade_smul_inf]
  · simp [star]

@[simp] theorem mul_star_mul (s : RestrictionPacket E G) : s * s.star * s = s := by
  rw [mul_star]
  apply ext <;> simp

@[simp] theorem star_mul_star (s : RestrictionPacket E G) : s.star * s * s.star = s.star := by
  rw [star_mul]
  apply ext <;> simp [star]

/-- The algebraic inverse equations in a semigroup. -/
def IsInverseOf (s t : RestrictionPacket E G) : Prop :=
  s * t * s = s ∧ t * s * t = t

theorem star_isInverseOf (s : RestrictionPacket E G) : IsInverseOf s s.star :=
  ⟨mul_star_mul s, star_mul_star s⟩

theorem idempotent_iff_grade_eq_one (s : RestrictionPacket E G) : s * s = s ↔ s.grade = 1 := by
  constructor
  · intro h
    have hg : s.grade * s.grade = s.grade := congrArg grade h
    have hi := congrArg (fun z : G => s.grade⁻¹ * z) hg
    simpa [mul_assoc] using hi
  · intro hg
    apply ext
    · simp [hg]
    · simp [hg]

theorem idempotent_iff_exists_support (s : RestrictionPacket E G) :
    s * s = s ↔ ∃ e : E, s = ⟨e, 1⟩ := by
  rw [idempotent_iff_grade_eq_one]
  constructor
  · intro h
    exact ⟨s.support, ext rfl h⟩
  · rintro ⟨e, rfl⟩
    rfl

theorem idempotents_commute {s t : RestrictionPacket E G}
    (hs : s * s = s) (ht : t * t = t) : s * t = t * s := by
  rw [idempotent_iff_grade_eq_one] at hs ht
  apply ext <;> simp [hs, ht, inf_comm]

/-- The displayed star is the unique inverse, so the fused carrier is an inverse semigroup. -/
theorem inverse_unique {s t : RestrictionPacket E G} (h : IsInverseOf s t) : t = s.star := by
  rcases h with ⟨hst, hts⟩
  have hgrade : t.grade = s.grade⁻¹ := by
    have hg := congrArg grade hst
    simp only [grade_mul] at hg
    have hright : t.grade * s.grade = 1 := by
      exact mul_left_cancel (a := s.grade) (by simpa [mul_assoc] using hg)
    have hi := congrArg (fun z : G => z * s.grade⁻¹) hright
    simpa [mul_assoc] using hi
  apply ext
  · have hle₁ : s.support ≤ s.grade • t.support := by
      have hsupp := congrArg support hst
      simp only [support_mul, grade_mul] at hsupp
      rw [hgrade] at hsupp
      have heq : s.support ⊓ (s.grade • t.support) = s.support := by
        simpa [inf_assoc] using hsupp
      exact inf_eq_left.mp heq
    have hle₂ : t.support ≤ s.grade⁻¹ • s.support := by
      have tsupp := congrArg support hts
      simp only [support_mul, grade_mul] at tsupp
      rw [hgrade] at tsupp
      have heq : t.support ⊓ (s.grade⁻¹ • s.support) = t.support := by
        simpa [inf_assoc, inf_left_comm, inf_comm, mul_smul] using tsupp
      exact inf_eq_left.mp heq
    apply le_antisymm hle₂
    have hback := supportGrade_smul_mono (g := s.grade⁻¹) hle₁
    simpa using hback
  · exact hgrade

@[simp] theorem star_star (s : RestrictionPacket E G) : s.star.star = s := by
  apply ext <;> simp [star, mul_smul]

@[simp] theorem star_mul_rev (s t : RestrictionPacket E G) : (s * t).star = t.star * s.star := by
  apply ext
  · simp [star, mul_smul, supportGrade_smul_inf, inf_comm]
  · simp [star]

theorem rangeSupport_mul (s t : RestrictionPacket E G) :
    rangeSupport (s * t) = rangeSupport s ⊓ s.grade • rangeSupport t := rfl

theorem grade_conservation (s t : RestrictionPacket E G) :
    (s * t).grade = s.grade * t.grade := rfl

theorem range_grade_jointly_injective :
    Function.Injective (fun s : RestrictionPacket E G => (rangeSupport s, s.grade)) := by
  intro s t h
  exact ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem rangeSupport_not_injective (hg : ∃ g : G, g ≠ 1) :
    ¬ Function.Injective (rangeSupport : RestrictionPacket E G → E) := by
  rintro hinj
  rcases hg with ⟨g, hg⟩
  have := hinj (show rangeSupport (⟨⊥, g⟩ : RestrictionPacket E G) =
    rangeSupport ⟨⊥, 1⟩ by rfl)
  exact hg (congrArg grade this)

theorem grade_not_injective (he : ∃ e : E, e ≠ ⊥) :
    ¬ Function.Injective (grade : RestrictionPacket E G → G) := by
  rintro hinj
  rcases he with ⟨e, he⟩
  have := hinj (show (⟨e, 1⟩ : RestrictionPacket E G).grade =
    (⟨⊥, 1⟩ : RestrictionPacket E G).grade by rfl)
  exact he (congrArg support this)

/-- Every group-valued multiplicative quotient erases the entire native-support sector. -/
theorem groupQuotient_erases_support {H : Type w} [Group H]
    (ψ : RestrictionPacket E G → H) (map_mul : ∀ s t, ψ (s * t) = ψ s * ψ t) (e : E) :
    ψ ⟨e, 1⟩ = 1 := by
  apply semilatticeToGroup_trivial (φ := fun e : E => ψ ⟨e, 1⟩) (e := e)
  intro a b
  have h := map_mul (⟨a, 1⟩ : RestrictionPacket E G) ⟨b, 1⟩
  have hm : (⟨a, 1⟩ : RestrictionPacket E G) * ⟨b, 1⟩ = ⟨a ⊓ b, 1⟩ := by
    apply ext <;> simp
  rw [hm] at h
  exact h

/-! ## Canonical partial-isometry representation -/

local instance constitutiveRestrictionFormationHistoryLocalInst1 : DecidableEq E := Classical.decEq E
local instance constitutiveRestrictionFormationHistoryLocalInst2 : DecidableEq G := Classical.decEq G
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The canonical Hilbert receiver `ℓ²(E × G)`. -/
abbrev PacketHilbert := LpDiagonal.LpTwo (E × G)

/-- Coordinate vector in the canonical Hilbert receiver. -/
def packetBasis (i : E × G) : PacketHilbert (E := E) (G := G) :=
  lp.single 2 i (1 : ℂ)

@[simp] theorem norm_packetBasis (i : E × G) :
    ‖packetBasis (E := E) (G := G) i‖ = 1 := by
  rw [packetBasis, lp.norm_single (by norm_num), norm_one]

/-- The action of a grade on support/history indices. -/
def gradeIndexEquiv (g : G) : (E × G) ≃ (E × G) where
  toFun i := (g • i.1, g * i.2)
  invFun i := (g⁻¹ • i.1, g⁻¹ * i.2)
  left_inv i := by ext <;> simp
  right_inv i := by ext <;> simp

@[simp] theorem gradeIndexEquiv_apply (g : G) (i : E × G) :
    gradeIndexEquiv (E := E) g i = (g • i.1, g * i.2) := rfl

@[simp] theorem gradeIndexEquiv_symm_apply (g : G) (i : E × G) :
    (gradeIndexEquiv (E := E) g).symm i = (g⁻¹ • i.1, g⁻¹ * i.2) := rfl

/-- Coordinate projection onto the principal support downset. -/
def supportIndicator (e : E) (i : E × G) : ℂ := if i.1 ≤ e then 1 else 0

theorem norm_supportIndicator_le_one (e : E) (i : E × G) :
    ‖supportIndicator (G := G) e i‖ ≤ 1 := by
  simp only [supportIndicator]
  split_ifs <;> simp

/-- The native-support projection `P_e`. -/
def supportProjection (e : E) : PacketHilbert (E := E) (G := G) →L[ℂ]
    PacketHilbert (E := E) (G := G) :=
  _root_.HTGeometry.ellTwoDiagonal (supportIndicator (G := G) e)
    (norm_supportIndicator_le_one (G := G) e)

@[simp] theorem supportProjection_apply (e : E) (x : PacketHilbert (E := E) (G := G))
    (i : E × G) :
    (supportProjection (G := G) e x : E × G → ℂ) i =
      if i.1 ≤ e then (x : E × G → ℂ) i else 0 := by
  rw [supportProjection, _root_.HTGeometry.ellTwoDiagonal_apply]
  simp [supportIndicator]

theorem norm_supportProjection_le_one (e : E) : ‖supportProjection (G := G) e‖ ≤ 1 :=
  _root_.HTGeometry.norm_ellTwoDiagonal_le _ _ zero_le_one

/-- The reversible grade shift `U_g`. -/
def gradeUnitary (g : G) : PacketHilbert (E := E) (G := G) →L[ℂ]
    PacketHilbert (E := E) (G := G) :=
  LpDiagonal.lpReindexCLM (gradeIndexEquiv (E := E) g)

@[simp] theorem gradeUnitary_apply (g : G) (x : PacketHilbert (E := E) (G := G))
    (i : E × G) :
    (gradeUnitary (E := E) g x : E × G → ℂ) i =
      (x : E × G → ℂ) (g⁻¹ • i.1, g⁻¹ * i.2) := rfl

theorem norm_gradeUnitary_le_one (g : G) : ‖gradeUnitary (E := E) g‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

/-- The canonical partial-symmetry shadow `V_(e,g) = P_e U_g`. -/
def packetOperator (s : RestrictionPacket E G) : PacketHilbert (E := E) (G := G) →L[ℂ]
    PacketHilbert (E := E) (G := G) :=
  supportProjection (G := G) s.support ∘L gradeUnitary (E := E) s.grade

@[simp] theorem packetOperator_apply (s : RestrictionPacket E G)
    (x : PacketHilbert (E := E) (G := G)) (i : E × G) :
    (packetOperator s x : E × G → ℂ) i =
      if i.1 ≤ s.support then
        (x : E × G → ℂ) (s.grade⁻¹ • i.1, s.grade⁻¹ * i.2)
      else 0 := by
  rw [packetOperator, ContinuousLinearMap.comp_apply, supportProjection_apply,
    gradeUnitary_apply]

theorem norm_packetOperator_le_one (s : RestrictionPacket E G) : ‖packetOperator s‖ ≤ 1 := by
  calc
    ‖packetOperator s‖ ≤ ‖supportProjection (G := G) s.support‖ *
        ‖gradeUnitary (E := E) s.grade‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 := by
      nlinarith [norm_supportProjection_le_one (G := G) s.support,
        norm_gradeUnitary_le_one (E := E) s.grade,
        norm_nonneg (supportProjection (G := G) s.support),
        norm_nonneg (gradeUnitary (E := E) s.grade)]

theorem packetOperator_mul (s t : RestrictionPacket E G) :
    packetOperator s ∘L packetOperator t = packetOperator (s * t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, packetOperator_apply, support_mul, grade_mul]
  have htransport : s.grade⁻¹ • i.1 ≤ t.support ↔ i.1 ≤ s.grade • t.support := by
    simpa using (supportGrade_smul_le_iff (g := s.grade⁻¹)
      (e := i.1) (f := t.support))
  by_cases he : i.1 ≤ s.support
  · by_cases hf : s.grade⁻¹ • i.1 ≤ t.support
    · rw [if_pos he, if_pos hf, if_pos (le_inf he (htransport.mp hf))]
      simp [mul_smul, mul_assoc]
    · rw [if_pos he, if_neg hf,
        if_neg (fun h => hf (htransport.mpr ((le_inf_iff.mp h).2)))]
  · rw [if_neg he, if_neg (fun h => he ((le_inf_iff.mp h).1))]

theorem packetOperator_neutralGrade (e : E) :
    packetOperator (⟨e, 1⟩ : RestrictionPacket E G) = supportProjection (G := G) e := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp [packetOperator_apply, supportProjection_apply]

theorem supportProjection_mul (e f : E) :
    supportProjection (G := G) e ∘L supportProjection (G := G) f =
      supportProjection (G := G) (e ⊓ f) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, supportProjection_apply]
  by_cases he : i.1 ≤ e <;> by_cases hf : i.1 ≤ f <;> simp [he, hf]

theorem supportProjection_idempotent (e : E) :
    supportProjection (G := G) e ∘L supportProjection (G := G) e =
      supportProjection (G := G) e := by
  simpa using supportProjection_mul (G := G) e e

theorem adjoint_supportProjection (e : E) :
    ContinuousLinearMap.adjoint (supportProjection (G := G) e) =
      supportProjection (G := G) e := by
  rw [supportProjection, _root_.HTGeometry.adjoint_ellTwoDiagonal]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp [_root_.HTGeometry.ellTwoDiagonal_apply, supportIndicator]

theorem adjoint_gradeUnitary (g : G) :
    ContinuousLinearMap.adjoint (gradeUnitary (E := E) g) =
      gradeUnitary (E := E) g⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simpa [gradeUnitary_apply] using
    (gradeIndexEquiv (E := E) g).tsum_eq
      (fun i => ⟪(x : E × G → ℂ) i,
        (y : E × G → ℂ) ((gradeIndexEquiv (E := E) g).symm i)⟫_ℂ)

theorem gradeUnitary_supportProjection (g : G) (e : E) :
    gradeUnitary (E := E) g⁻¹ ∘L supportProjection (G := G) e =
      supportProjection (G := G) (g⁻¹ • e) ∘L gradeUnitary (E := E) g⁻¹ := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, gradeUnitary_apply, supportProjection_apply]
  simp only [inv_inv]
  have hiff : g • i.1 ≤ e ↔ i.1 ≤ g⁻¹ • e := supportGrade_smul_le_iff g
  by_cases h : g • i.1 ≤ e
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (not_congr hiff |>.mp h)]

theorem gradeUnitary_conjugates_supportProjection (g : G) (e : E) :
    gradeUnitary (E := E) g ∘L supportProjection (G := G) e ∘L
        gradeUnitary (E := E) g⁻¹ = supportProjection (G := G) (g • e) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, gradeUnitary_apply, supportProjection_apply,
    inv_inv]
  have hiff : g⁻¹ • i.1 ≤ e ↔ i.1 ≤ g • e := by
    simpa using (supportGrade_smul_le_iff (g := g⁻¹) (e := i.1) (f := e))
  by_cases h : g⁻¹ • i.1 ≤ e
  · rw [if_pos h, if_pos (hiff.mp h)]
    simp
  · rw [if_neg h, if_neg (not_congr hiff |>.mp h)]

theorem adjoint_packetOperator (s : RestrictionPacket E G) :
    ContinuousLinearMap.adjoint (packetOperator s) = packetOperator s.star := by
  rw [packetOperator, ContinuousLinearMap.adjoint_comp, adjoint_supportProjection,
    adjoint_gradeUnitary, packetOperator, support_star, grade_star]
  exact gradeUnitary_supportProjection s.grade s.support

theorem packetOperator_mul_adjoint (s : RestrictionPacket E G) :
    packetOperator s ∘L ContinuousLinearMap.adjoint (packetOperator s) =
      supportProjection (G := G) (rangeSupport s) := by
  rw [adjoint_packetOperator, packetOperator_mul, mul_star]
  exact packetOperator_neutralGrade s.support

theorem packetOperator_adjoint_mul (s : RestrictionPacket E G) :
    ContinuousLinearMap.adjoint (packetOperator s) ∘L packetOperator s =
      supportProjection (G := G) (sourceSupport s) := by
  rw [adjoint_packetOperator, packetOperator_mul, star_mul]
  exact packetOperator_neutralGrade (s.grade⁻¹ • s.support)

/-- Exact operator certificate of partial-isometry status. -/
theorem packetOperator_partialIsometry (s : RestrictionPacket E G) :
    (packetOperator s ∘L ContinuousLinearMap.adjoint (packetOperator s) =
        supportProjection (G := G) (rangeSupport s)) ∧
      (ContinuousLinearMap.adjoint (packetOperator s) ∘L packetOperator s =
        supportProjection (G := G) (sourceSupport s)) ∧
      (supportProjection (G := G) (rangeSupport s) ∘L packetOperator s =
        packetOperator s) := by
  refine ⟨packetOperator_mul_adjoint s, packetOperator_adjoint_mul s, ?_⟩
  rw [← packetOperator_neutralGrade, packetOperator_mul]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp [packetOperator_apply, rangeSupport]

theorem packetOperator_basis (s : RestrictionPacket E G) (i : E × G) :
    packetOperator s (packetBasis i) =
      if s.grade • i.1 ≤ s.support then
        packetBasis (s.grade • i.1, s.grade * i.2)
      else 0 := by
  simp only [packetBasis]
  rw [packetOperator, ContinuousLinearMap.comp_apply, gradeUnitary,
    LpDiagonal.lpReindexCLM_single]
  rw [supportProjection, ← _root_.HTGeometry.ellTwoCoordinateBasis_apply,
    _root_.HTGeometry.ellTwoDiagonal_coordinateBasis]
  simp [supportIndicator, packetBasis, _root_.HTGeometry.ellTwoCoordinateBasis_apply]

@[simp] theorem packetOperator_basis_bot (s : RestrictionPacket E G) :
    packetOperator s (packetBasis (⊥, 1)) = packetBasis (⊥, s.grade) := by
  rw [packetOperator_basis]
  simp

theorem inner_packetBasis_eq_zero {i j : E × G} (hij : i ≠ j) :
    ⟪packetBasis (E := E) (G := G) i, packetBasis j⟫_ℂ = 0 := by
  rw [packetBasis, lp.inner_single_left]
  simp [packetBasis, lp.single_apply, Pi.single_apply, hij]

theorem norm_sq_packetBasis_sub {i j : E × G} (hij : i ≠ j) :
    ‖packetBasis (E := E) (G := G) i - packetBasis j‖ ^ 2 = 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_packetBasis, norm_packetBasis,
    inner_packetBasis_eq_zero hij]
  norm_num

theorem norm_packetOperator_sub_ge_sqrt_two_of_grade_ne
    {s t : RestrictionPacket E G} (hgrade : s.grade ≠ t.grade) :
    Real.sqrt 2 ≤ ‖packetOperator s - packetOperator t‖ := by
  have hout :
      (packetOperator s - packetOperator t) (packetBasis (⊥, 1)) =
        packetBasis (⊥, s.grade) - packetBasis (⊥, t.grade) := by
    simp
  have hsq : ‖(packetOperator s - packetOperator t) (packetBasis (⊥, 1))‖ ^ 2 = 2 := by
    rw [hout, norm_sq_packetBasis_sub]
    exact fun h => hgrade (congrArg Prod.snd h)
  have hop := (packetOperator s - packetOperator t).le_opNorm (packetBasis (⊥, 1))
  rw [norm_packetBasis, mul_one] at hop
  have hsqrt : Real.sqrt 2 ≤
      ‖(packetOperator s - packetOperator t) (packetBasis (⊥, 1))‖ := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2,
      norm_nonneg ((packetOperator s - packetOperator t) (packetBasis (⊥, 1)))]
  exact hsqrt.trans hop

theorem norm_packetOperator_sub_ge_one_of_grade_eq
    {s t : RestrictionPacket E G} (hst : s ≠ t) (hgrade : s.grade = t.grade) :
    1 ≤ ‖packetOperator s - packetOperator t‖ := by
  have hsupp : s.support ≠ t.support := by
    intro h
    exact hst (ext h hgrade)
  rcases not_and_or.mp (fun h => hsupp (le_antisymm h.1 h.2)) with hnot | hnot
  · let i : E × G := (s.grade⁻¹ • s.support, s.grade⁻¹)
    have hs : packetOperator s (packetBasis i) = packetBasis (s.support, 1) := by
      rw [packetOperator_basis]
      simp [i]
    have ht : packetOperator t (packetBasis i) = 0 := by
      rw [packetOperator_basis, if_neg]
      simpa [i, hgrade] using hnot
    have hout : (packetOperator s - packetOperator t) (packetBasis i) =
        packetBasis (s.support, 1) := by simp [hs, ht]
    have hop := (packetOperator s - packetOperator t).le_opNorm (packetBasis i)
    rw [norm_packetBasis, mul_one, hout, norm_packetBasis] at hop
    exact hop
  · let i : E × G := (s.grade⁻¹ • t.support, s.grade⁻¹)
    have hs : packetOperator s (packetBasis i) = 0 := by
      rw [packetOperator_basis, if_neg]
      simpa [i] using hnot
    have ht : packetOperator t (packetBasis i) = packetBasis (t.support, 1) := by
      rw [packetOperator_basis]
      simp [i, hgrade]
    have hout : (packetOperator s - packetOperator t) (packetBasis i) =
        -packetBasis (t.support, 1) := by simp [hs, ht]
    have hop := (packetOperator s - packetOperator t).le_opNorm (packetBasis i)
    rw [norm_packetBasis, mul_one, hout, norm_neg, norm_packetBasis] at hop
    exact hop

theorem packetOperator_uniform_separation {s t : RestrictionPacket E G} (hst : s ≠ t) :
    1 ≤ ‖packetOperator s - packetOperator t‖ ∧
      ‖packetOperator s - packetOperator t‖ ≤ 2 := by
  constructor
  · by_cases hg : s.grade = t.grade
    · exact norm_packetOperator_sub_ge_one_of_grade_eq hst hg
    · exact (by
        have hsqrt := norm_packetOperator_sub_ge_sqrt_two_of_grade_ne hg
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have : (1 : ℝ) ≤ Real.sqrt 2 := by
          nlinarith [hs, Real.sqrt_nonneg 2]
        exact this.trans hsqrt)
  · calc
      ‖packetOperator s - packetOperator t‖ ≤
          ‖packetOperator s‖ + ‖packetOperator t‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [norm_packetOperator_le_one s, norm_packetOperator_le_one t]

theorem packetOperator_injective :
    Function.Injective (packetOperator : RestrictionPacket E G →
      PacketHilbert (E := E) (G := G) →L[ℂ] PacketHilbert (E := E) (G := G)) := by
  intro s t h
  by_contra hst
  have hsep := (packetOperator_uniform_separation hst).1
  rw [h, sub_self, norm_zero] at hsep
  norm_num at hsep

/-- A one-separated family meets every compact set in only finitely many points. -/
theorem finite_preimage_of_oneSeparated {α X : Type*} [PseudoMetricSpace X] (f : α → X)
    (hsep : ∀ {a b}, a ≠ b → 1 ≤ dist (f a) (f b)) {K : Set X} (hK : IsCompact K) :
    {a | f a ∈ K}.Finite := by
  have htot : TotallyBounded K := (isCompact_iff_totallyBounded_isComplete.mp hK).1
  rcases (Metric.totallyBounded_iff.mp htot (1 / 3 : ℝ) (by norm_num)) with
    ⟨centres, hcentres, hcover⟩
  let fibre : X → Set α := fun y => {a | f a ∈ Metric.ball y (1 / 3 : ℝ)}
  have hfibre : ∀ y : X, (fibre y).Finite := by
    intro y
    apply Set.Subsingleton.finite
    intro a ha b hb
    by_contra hab
    have hlarge := hsep hab
    have htri := dist_triangle (f a) y (f b)
    have ha' : dist (f a) y < 1 / 3 := Metric.mem_ball.mp ha
    have hb' : dist y (f b) < 1 / 3 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hb
    linarith
  have hunion : (⋃ y ∈ centres, fibre y).Finite :=
    hcentres.biUnion fun y _ => hfibre y
  apply hunion.subset
  intro a ha
  simpa [fibre] using hcover ha

/-- The canonical packet representation is proper for the discrete source: compact operator sets
have finite packet preimages. -/
theorem packetOperator_compact_preimage_finite
    {K : Set (PacketHilbert (E := E) (G := G) →L[ℂ] PacketHilbert (E := E) (G := G))}
    (hK : IsCompact K) : {s : RestrictionPacket E G | packetOperator s ∈ K}.Finite := by
  apply finite_preimage_of_oneSeparated packetOperator
  · intro s t hst
    simpa [dist_eq_norm] using (packetOperator_uniform_separation hst).1
  · exact hK

/-! ## Compatible functional symmetries -/

/-- A simultaneous support/history symmetry compatible with transported support. -/
structure CompatibleSymmetry where
  supportEquiv : E ≃o E
  gradeEquiv : G ≃* G
  compatible : ∀ g e, supportEquiv (g • e) = gradeEquiv g • supportEquiv e

/-- Packet transport under a compatible symmetry. -/
def CompatibleSymmetry.mapPacket (σ : CompatibleSymmetry (E := E) (G := G))
    (s : RestrictionPacket E G) : RestrictionPacket E G :=
  ⟨σ.supportEquiv s.support, σ.gradeEquiv s.grade⟩

@[simp] theorem CompatibleSymmetry.mapPacket_support
    (σ : CompatibleSymmetry (E := E) (G := G)) (s : RestrictionPacket E G) :
    (σ.mapPacket s).support = σ.supportEquiv s.support := rfl

@[simp] theorem CompatibleSymmetry.mapPacket_grade
    (σ : CompatibleSymmetry (E := E) (G := G)) (s : RestrictionPacket E G) :
    (σ.mapPacket s).grade = σ.gradeEquiv s.grade := rfl

theorem CompatibleSymmetry.mapPacket_mul (σ : CompatibleSymmetry (E := E) (G := G))
    (s t : RestrictionPacket E G) : σ.mapPacket (s * t) = σ.mapPacket s * σ.mapPacket t := by
  apply ext
  · simp [CompatibleSymmetry.mapPacket, σ.compatible]
  · simp [CompatibleSymmetry.mapPacket]

theorem CompatibleSymmetry.mapPacket_star (σ : CompatibleSymmetry (E := E) (G := G))
    (s : RestrictionPacket E G) : σ.mapPacket s.star = (σ.mapPacket s).star := by
  apply ext
  · simp [CompatibleSymmetry.mapPacket, star, σ.compatible]
  · simp [CompatibleSymmetry.mapPacket, star]

theorem CompatibleSymmetry.mapPacket_injective (σ : CompatibleSymmetry (E := E) (G := G)) :
    Function.Injective σ.mapPacket := by
  intro s t h
  apply ext
  · exact σ.supportEquiv.injective (congrArg support h)
  · exact σ.gradeEquiv.injective (congrArg grade h)

theorem CompatibleSymmetry.mapPacket_surjective (σ : CompatibleSymmetry (E := E) (G := G)) :
    Function.Surjective σ.mapPacket := by
  intro s
  refine ⟨⟨σ.supportEquiv.symm s.support, σ.gradeEquiv.symm s.grade⟩, ?_⟩
  apply ext <;> simp [CompatibleSymmetry.mapPacket]

theorem CompatibleSymmetry.mapPacket_bijective (σ : CompatibleSymmetry (E := E) (G := G)) :
    Function.Bijective σ.mapPacket :=
  ⟨σ.mapPacket_injective, σ.mapPacket_surjective⟩

/-- Basis permutation implementing a compatible symmetry. -/
def CompatibleSymmetry.indexEquiv (σ : CompatibleSymmetry (E := E) (G := G)) :
    (E × G) ≃ (E × G) := σ.supportEquiv.toEquiv.prodCongr σ.gradeEquiv.toEquiv

@[simp] theorem CompatibleSymmetry.indexEquiv_apply
    (σ : CompatibleSymmetry (E := E) (G := G)) (i : E × G) :
    σ.indexEquiv i = (σ.supportEquiv i.1, σ.gradeEquiv i.2) := rfl

@[simp] theorem CompatibleSymmetry.indexEquiv_symm_apply
    (σ : CompatibleSymmetry (E := E) (G := G)) (i : E × G) :
    σ.indexEquiv.symm i = (σ.supportEquiv.symm i.1, σ.gradeEquiv.symm i.2) := rfl

/-- The unitary basis permutation implementing a compatible symmetry. -/
def CompatibleSymmetry.unitary (σ : CompatibleSymmetry (E := E) (G := G)) :
    PacketHilbert (E := E) (G := G) →L[ℂ] PacketHilbert (E := E) (G := G) :=
  LpDiagonal.lpReindexCLM σ.indexEquiv

/-- Inverse unitary basis permutation. -/
def CompatibleSymmetry.unitaryInv (σ : CompatibleSymmetry (E := E) (G := G)) :
    PacketHilbert (E := E) (G := G) →L[ℂ] PacketHilbert (E := E) (G := G) :=
  LpDiagonal.lpReindexCLM σ.indexEquiv.symm

@[simp] theorem CompatibleSymmetry.unitary_apply
    (σ : CompatibleSymmetry (E := E) (G := G))
    (x : PacketHilbert (E := E) (G := G)) (i : E × G) :
    (σ.unitary x : E × G → ℂ) i =
      (x : E × G → ℂ) (σ.supportEquiv.symm i.1, σ.gradeEquiv.symm i.2) := rfl

@[simp] theorem CompatibleSymmetry.unitaryInv_apply
    (σ : CompatibleSymmetry (E := E) (G := G))
    (x : PacketHilbert (E := E) (G := G)) (i : E × G) :
    (σ.unitaryInv x : E × G → ℂ) i =
      (x : E × G → ℂ) (σ.supportEquiv i.1, σ.gradeEquiv i.2) := rfl

theorem CompatibleSymmetry.norm_unitary_apply
    (σ : CompatibleSymmetry (E := E) (G := G))
    (x : PacketHilbert (E := E) (G := G)) : ‖σ.unitary x‖ = ‖x‖ :=
  (LpDiagonal.lpReindex σ.indexEquiv).norm_map x

theorem CompatibleSymmetry.unitary_comp_inverse
    (σ : CompatibleSymmetry (E := E) (G := G)) :
    σ.unitary ∘L σ.unitaryInv = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp

theorem CompatibleSymmetry.inverse_comp_unitary
    (σ : CompatibleSymmetry (E := E) (G := G)) :
    σ.unitaryInv ∘L σ.unitary = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp

/-- Compatible functional symmetries act on packet operators by exact unitary conjugation. -/
theorem CompatibleSymmetry.unitary_conjugates_packetOperator
    (σ : CompatibleSymmetry (E := E) (G := G)) (s : RestrictionPacket E G) :
    σ.unitary ∘L packetOperator s ∘L σ.unitaryInv = packetOperator (σ.mapPacket s) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, CompatibleSymmetry.unitary_apply,
    CompatibleSymmetry.unitaryInv_apply, packetOperator_apply,
    CompatibleSymmetry.mapPacket_support, CompatibleSymmetry.mapPacket_grade]
  have hsupp : σ.supportEquiv.symm i.1 ≤ s.support ↔
      i.1 ≤ σ.supportEquiv s.support := by
    constructor
    · intro h
      simpa using σ.supportEquiv.monotone h
    · intro h
      simpa using σ.supportEquiv.symm.monotone h
  have hact : σ.supportEquiv (s.grade⁻¹ • σ.supportEquiv.symm i.1) =
      (σ.gradeEquiv s.grade)⁻¹ • i.1 := by
    simpa using σ.compatible s.grade⁻¹ (σ.supportEquiv.symm i.1)
  have hgrade : σ.gradeEquiv (s.grade⁻¹ * σ.gradeEquiv.symm i.2) =
      (σ.gradeEquiv s.grade)⁻¹ * i.2 := by simp
  by_cases h : σ.supportEquiv.symm i.1 ≤ s.support
  · rw [if_pos h, if_pos (hsupp.mp h), hact, hgrade]
  · rw [if_neg h, if_neg (not_congr hsupp |>.mp h)]

/-- Full RFHM capstone: faithful partial-isometry representation, sharp separation, properness,
and information-neutral compatible symmetry transport. -/
theorem restrictionFormationHistory_capstone
    (σ : CompatibleSymmetry (E := E) (G := G)) :
    Function.Injective (packetOperator : RestrictionPacket E G →
      PacketHilbert (E := E) (G := G) →L[ℂ] PacketHilbert (E := E) (G := G)) ∧
    (∀ {s t : RestrictionPacket E G}, s ≠ t →
      1 ≤ ‖packetOperator s - packetOperator t‖ ∧
        ‖packetOperator s - packetOperator t‖ ≤ 2) ∧
    (∀ K, IsCompact K → {s : RestrictionPacket E G | packetOperator s ∈ K}.Finite) ∧
    (∀ s, σ.unitary ∘L packetOperator s ∘L σ.unitaryInv =
      packetOperator (σ.mapPacket s)) := by
  exact ⟨packetOperator_injective, fun h => packetOperator_uniform_separation h,
    fun _ hK => packetOperator_compact_preimage_finite hK,
    σ.unitary_conjugates_packetOperator⟩

end RestrictionPacket

end GaloisForLFunctions.HTGeometry
