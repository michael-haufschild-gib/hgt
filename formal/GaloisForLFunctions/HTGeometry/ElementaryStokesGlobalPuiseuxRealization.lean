import GaloisForLFunctions.HTGeometry.ElementaryStokesCoefficientRealization

namespace GaloisForLFunctions.IrregularStokes

noncomputable section

namespace ElementaryDecoratedGraph

/-- Any finite set admits an explicit injective coefficient assignment in any infinite type. -/
noncomputable def finiteDistinctCoefficients (α K : Type*) [Finite α] [Infinite K] : α → K :=
  letI : Fintype α := Fintype.ofFinite α
  fun a => Infinite.natEmbedding K ((Fintype.equivFin α a).val)

theorem finiteDistinctCoefficients_injective (α K : Type*) [Finite α] [Infinite K] :
    Function.Injective (finiteDistinctCoefficients α K) := by
  letI : Fintype α := Fintype.ofFinite α
  intro a b h
  apply (Fintype.equivFin α).injective
  apply Fin.ext
  exact (Infinite.natEmbedding K).injective h

def maxEdge {n : ℕ} (g : ElementaryDecoratedGraph n) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => g.edge i j

theorem edge_le_maxEdge {n : ℕ} (g : ElementaryDecoratedGraph n) (i j : Fin n) :
    g.edge i j ≤ g.maxEdge := by
  exact (Finset.le_sup (f := fun i => Finset.univ.sup fun j => g.edge i j)
    (Finset.mem_univ i)).trans' (Finset.le_sup (f := g.edge i) (Finset.mem_univ j))

def maxRamification {n : ℕ} (g : ElementaryDecoratedGraph n) : ℕ :=
  Finset.univ.sup g.ramification

theorem ramification_le_maxRamification {n : ℕ} (g : ElementaryDecoratedGraph n)
    (i : Fin n) : g.ramification i ≤ g.maxRamification :=
  Finset.le_sup (f := g.ramification) (Finset.mem_univ i)

/-- Finite global monomial stages used by the explicit elementary realization. -/
abbrev MonomialStage {n : ℕ} (g : ElementaryDecoratedGraph n) :=
  Fin g.maxEdge ⊕
    (Fin (g.maxRamification + 1) ⊕
      (Σ r : Fin (g.maxRamification + 1), Fin r.val))

namespace MonomialStage

def exponent {n : ℕ} {g : ElementaryDecoratedGraph n} : g.MonomialStage → ℚ
  | .inl high => (high.val + 2 : ℕ)
  | .inr (.inl ramification) =>
      1 + 1 / (ramification.val : ℚ)
  | .inr (.inr ⟨ramification, lower⟩) =>
      (lower.val + 1 : ℕ) / (ramification.val : ℚ)

theorem mandatory_exponent_le_two {n : ℕ} {g : ElementaryDecoratedGraph n}
    (r : Fin (g.maxRamification + 1)) :
    exponent (g := g) (.inr (.inl r)) ≤ 2 := by
  simp only [exponent]
  by_cases hr : r.val = 0
  · simp [hr]
  · have hrNat : 0 < r.val := Nat.pos_of_ne_zero hr
    have hrQ : (0 : ℚ) < r.val := by exact_mod_cast hrNat
    have hone : (1 : ℚ) ≤ r.val := by exact_mod_cast hrNat
    have hdiv : (1 : ℚ) / r.val ≤ 1 := (div_le_one hrQ).mpr hone
    linarith

theorem lower_exponent_le_one {n : ℕ} {g : ElementaryDecoratedGraph n}
    (r : Fin (g.maxRamification + 1)) (b : Fin r.val) :
    exponent (g := g) (.inr (.inr ⟨r, b⟩)) ≤ 1 := by
  simp only [exponent]
  have hrNat : 0 < r.val := Nat.zero_lt_of_lt b.isLt
  have hrQ : (0 : ℚ) < r.val := by exact_mod_cast hrNat
  apply (div_le_one hrQ).mpr
  exact_mod_cast Nat.succ_le_of_lt b.isLt

end MonomialStage

def highStage {n : ℕ} (g : ElementaryDecoratedGraph n) (k : ℕ)
    (hk : 0 < k) (hkmax : k ≤ g.maxEdge) : g.MonomialStage :=
  .inl ⟨k - 1, by omega⟩

@[simp] theorem highStage_exponent {n : ℕ} (g : ElementaryDecoratedGraph n) (k : ℕ)
    (hk : 0 < k) (hkmax : k ≤ g.maxEdge) :
    (g.highStage k hk hkmax).exponent = (k + 1 : ℕ) := by
  simp [highStage, MonomialStage.exponent]
  norm_cast
  omega

def mandatoryStage {n : ℕ} (g : ElementaryDecoratedGraph n) (r : ℕ)
    (hr : r ≤ g.maxRamification) : g.MonomialStage :=
  .inr (.inl ⟨r, Nat.lt_succ_of_le hr⟩)

@[simp] theorem mandatoryStage_exponent {n : ℕ} (g : ElementaryDecoratedGraph n) (r : ℕ)
    (hr : r ≤ g.maxRamification) :
    (g.mandatoryStage r hr).exponent = 1 + 1 / (r : ℚ) := rfl

def lowerStage {n : ℕ} (g : ElementaryDecoratedGraph n) (r b : ℕ)
    (hr : r ≤ g.maxRamification) (hb : b < r) : g.MonomialStage :=
  .inr (.inr ⟨⟨r, Nat.lt_succ_of_le hr⟩, ⟨b, hb⟩⟩)

@[simp] theorem lowerStage_exponent {n : ℕ} (g : ElementaryDecoratedGraph n) (r b : ℕ)
    (hr : r ≤ g.maxRamification) (hb : b < r) :
    (g.lowerStage r b hr hb).exponent = (b + 1 : ℕ) / (r : ℚ) := rfl

/-- The arithmetic edge encoded by a separating monomial stage.  High stages record an integral
rescaled edge, mandatory Airy stages record the reciprocal ramification contact, and lower stages
record the residual numerator at equal ramification. -/
def StageRealizesEdge {n : ℕ} (g : ElementaryDecoratedGraph n) (i j : Fin n) :
    g.MonomialStage → Prop
  | .inl high =>
      g.edge i j = g.ramification i * g.ramification j * (high.val + 1)
  | .inr (.inl ramification) =>
      g.edge i j * ramification.val = g.ramification i * g.ramification j
  | .inr (.inr ⟨ramification, lower⟩) =>
      g.ramification i = ramification.val ∧
        g.ramification j = ramification.val ∧ g.edge i j = lower.val

theorem highStage_realizesEdge_iff {n k : ℕ} (g : ElementaryDecoratedGraph n)
    (i j : Fin n) (hk : 0 < k) (hkmax : k ≤ g.maxEdge) :
    g.StageRealizesEdge i j (g.highStage k hk hkmax) ↔
      g.edge i j = g.ramification i * g.ramification j * k := by
  simp [StageRealizesEdge, highStage]
  rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hk)]

theorem mandatoryStage_realizesEdge_iff {n r : ℕ} (g : ElementaryDecoratedGraph n)
    (i j : Fin n) (hrmax : r ≤ g.maxRamification) :
    g.StageRealizesEdge i j (g.mandatoryStage r hrmax) ↔
      g.edge i j * r = g.ramification i * g.ramification j := by
  rfl

theorem lowerStage_realizesEdge_iff {n r b : ℕ} (g : ElementaryDecoratedGraph n)
    (i j : Fin n) (hrmax : r ≤ g.maxRamification) (hb : b < r) :
    g.StageRealizesEdge i j (g.lowerStage r b hrmax hb) ↔
      g.ramification i = r ∧ g.ramification j = r ∧ g.edge i j = b := by
  rfl

def stageCoefficient {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i : Fin n) :
    g.MonomialStage → ℂ
  | .inl high =>
      g.thresholdCoefficient hacute (high.val + 1 : ℕ) i
  | .inr (.inl ramification) =>
      if ramification.val = g.ramification i ∧ 1 < ramification.val then
        g.thresholdCoefficient hacute (1 / (ramification.val : ℚ)) i
      else 0
  | .inr (.inr ⟨ramification, lower⟩) =>
      if ramification.val = g.ramification i then
        g.thresholdCoefficient hacute
          ((lower.val : ℚ) / (ramification.val : ℚ) ^ 2) i
      else 0

/-- Finite coefficient packet before equal-exponent terms are collected. -/
def coefficientPacket {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i : Fin n) :
    g.MonomialStage →₀ ℂ :=
  Finsupp.equivFunOnFinite.symm (g.stageCoefficient hacute i)

/-- Actual finite Puiseux polynomial obtained by collecting the explicit stage coefficients at
their rational exponents. -/
def realizedPuiseuxPolynomial {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i : Fin n) : ℚ →₀ ℂ :=
  (g.coefficientPacket hacute i).sum fun stage coefficient =>
    Finsupp.single stage.exponent coefficient

def IsHighestDifferenceStage {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i j : Fin n)
    (stage : g.MonomialStage) : Prop :=
  g.stageCoefficient hacute i stage ≠ g.stageCoefficient hacute j stage ∧
    ∀ other : g.MonomialStage,
      g.stageCoefficient hacute i other ≠ g.stageCoefficient hacute j other →
        other.exponent ≤ stage.exponent

theorem highCoefficient_eq_iff {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i j : Fin n) (high : Fin g.maxEdge) :
    g.stageCoefficient hacute i (.inl high) =
        g.stageCoefficient hacute j (.inl high) ↔
      i = j ∨ g.rescaledEdge i j < (high.val + 1 : ℕ) := by
  exact g.thresholdCoefficient_eq_iff hacute _ i j

theorem mandatoryCoefficient_eq_iff_of_ramification_eq
    {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hijRam : g.ramification i = g.ramification j)
    (hr : 1 < g.ramification i)
    (r : Fin (g.maxRamification + 1)) (hri : r.val = g.ramification i) :
    g.stageCoefficient hacute i (.inr (.inl r)) =
        g.stageCoefficient hacute j (.inr (.inl r)) ↔
      i = j ∨ g.rescaledEdge i j < 1 / (g.ramification i : ℚ) := by
  have hrj : 1 < g.ramification j := by rwa [← hijRam]
  simp only [stageCoefficient, hri, hijRam, hrj, and_self, if_pos]
  exact g.thresholdCoefficient_eq_iff hacute _ i j

theorem lowerCoefficient_eq_iff_of_ramification_eq
    {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hijRam : g.ramification i = g.ramification j)
    (r : Fin (g.maxRamification + 1)) (hri : r.val = g.ramification i)
    (b : Fin r.val) :
    g.stageCoefficient hacute i (.inr (.inr ⟨r, b⟩)) =
        g.stageCoefficient hacute j (.inr (.inr ⟨r, b⟩)) ↔
      i = j ∨ g.rescaledEdge i j <
        (b.val : ℚ) / (g.ramification i : ℚ) ^ 2 := by
  simp only [stageCoefficient, hri, hijRam, if_pos]
  exact g.thresholdCoefficient_eq_iff hacute _ i j

theorem highStage_isHighestDifference
    {n k : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hij : i ≠ j) (hk : 0 < k) (hkmax : k ≤ g.maxEdge)
    (hweight : g.rescaledEdge i j = k) :
    g.IsHighestDifferenceStage hacute i j (g.highStage k hk hkmax) := by
  constructor
  · intro heq
    have hiff := (g.highCoefficient_eq_iff hacute i j
      ⟨k - 1, by omega⟩).mp heq
    rcases hiff with h | h
    · exact hij h
    · rw [hweight] at h
      have hkEq : k - 1 + 1 = k := by omega
      norm_num [hkEq] at h
  · intro other hother
    rcases other with high | (mandatory | lower)
    · have hnot : ¬(i = j ∨
          g.rescaledEdge i j < (high.val + 1 : ℕ)) := by
        exact fun h => hother ((g.highCoefficient_eq_iff hacute i j high).mpr h)
      have hle : high.val + 1 ≤ k := by
        rw [hweight] at hnot
        push Not at hnot
        exact_mod_cast hnot.2
      change ((high.val + 2 : ℕ) : ℚ) ≤
        (g.highStage k hk hkmax).exponent
      rw [highStage_exponent]
      exact_mod_cast Nat.add_le_add_right hle 1
    · calc
        MonomialStage.exponent (.inr (.inl mandatory)) ≤ 2 :=
          MonomialStage.mandatory_exponent_le_two mandatory
        _ ≤ (g.highStage k hk hkmax).exponent := by
          rw [highStage_exponent]
          exact_mod_cast (Nat.succ_le_succ hk)
    · rcases lower with ⟨r, b⟩
      calc
        MonomialStage.exponent (.inr (.inr ⟨r, b⟩)) ≤ 1 :=
          MonomialStage.lower_exponent_le_one r b
        _ ≤ (g.highStage k hk hkmax).exponent := by
          rw [highStage_exponent]
          norm_num

theorem mandatoryStage_isHighestDifference_sameRamification
    {n r : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hij : i ≠ j) (hir : g.ramification i = r)
    (hjr : g.ramification j = r) (hr : 1 < r)
    (hrmax : r ≤ g.maxRamification)
    (hweight : g.rescaledEdge i j = 1 / (r : ℚ)) :
    g.IsHighestDifferenceStage hacute i j (g.mandatoryStage r hrmax) := by
  have hijRam : g.ramification i = g.ramification j := hir.trans hjr.symm
  constructor
  · intro heq
    have hriPos : 1 < g.ramification i := by simpa [hir] using hr
    have hiff := (g.mandatoryCoefficient_eq_iff_of_ramification_eq
      hacute hijRam hriPos
      ⟨r, Nat.lt_succ_of_le hrmax⟩ hir.symm).mp heq
    rcases hiff with h | h
    · exact hij h
    · rw [hir, hweight] at h
      exact (lt_irrefl _ h)
  · intro other hother
    rcases other with high | (mandatory | lower)
    · exfalso
      apply hother
      apply (g.highCoefficient_eq_iff hacute i j high).mpr
      right
      rw [hweight]
      have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
      have hrOneQ : (1 : ℚ) < r := by exact_mod_cast hr
      have hdiv : (1 : ℚ) / r < 1 := (div_lt_one hrQ).mpr hrOneQ
      exact hdiv.trans_le (by norm_num)
    · by_cases hm : mandatory.val = r
      · rw [mandatoryStage_exponent]
        simp only [MonomialStage.exponent, hm]
        exact le_rfl
      · exfalso
        apply hother
        simp [stageCoefficient, hir, hjr, hm]
    · rcases lower with ⟨otherR, b⟩
      calc
        MonomialStage.exponent (.inr (.inr ⟨otherR, b⟩)) ≤ 1 :=
          MonomialStage.lower_exponent_le_one otherR b
        _ ≤ (g.mandatoryStage r hrmax).exponent := by
          rw [mandatoryStage_exponent]
          have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
          have hnonneg : (0 : ℚ) ≤ 1 / r := (div_nonneg zero_le_one hrQ.le)
          linarith

theorem lowerStage_isHighestDifference_sameRamification
    {n r b : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hij : i ≠ j) (hir : g.ramification i = r)
    (hjr : g.ramification j = r) (hb : b < r)
    (hrmax : r ≤ g.maxRamification)
    (hweight : g.rescaledEdge i j = (b : ℚ) / (r : ℚ) ^ 2) :
    g.IsHighestDifferenceStage hacute i j (g.lowerStage r b hrmax hb) := by
  have hijRam : g.ramification i = g.ramification j := hir.trans hjr.symm
  have hrNat : 0 < r := Nat.zero_lt_of_lt hb
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hrNat
  have hrSqQ : (0 : ℚ) < (r : ℚ) ^ 2 := sq_pos_of_pos hrQ
  have hbelowMandatory : (b : ℚ) / (r : ℚ) ^ 2 < 1 / (r : ℚ) := by
    calc
      (b : ℚ) / (r : ℚ) ^ 2 < (r : ℚ) / (r : ℚ) ^ 2 :=
        div_lt_div_of_pos_right (by exact_mod_cast hb) hrSqQ
      _ = 1 / (r : ℚ) := by field_simp
  have hbelowOne : (b : ℚ) / (r : ℚ) ^ 2 < 1 := by
    exact hbelowMandatory.trans_le <| (div_le_one hrQ).mpr (by exact_mod_cast hrNat)
  constructor
  · intro heq
    have hiff := (g.lowerCoefficient_eq_iff_of_ramification_eq
      hacute hijRam ⟨r, Nat.lt_succ_of_le hrmax⟩ hir.symm ⟨b, hb⟩).mp heq
    rcases hiff with h | h
    · exact hij h
    · rw [hir, hweight] at h
      exact (lt_irrefl _ h)
  · intro other hother
    rcases other with high | (mandatory | lower)
    · exfalso
      apply hother
      apply (g.highCoefficient_eq_iff hacute i j high).mpr
      right
      rw [hweight]
      exact hbelowOne.trans_le (by norm_num)
    · by_cases hm : mandatory.val = r
      · exfalso
        apply hother
        have hriPosCases : r = 1 ∨ 1 < r := by omega
        rcases hriPosCases with rfl | hr
        · simp only [stageCoefficient, hir, hjr, hm, lt_self_iff_false,
            and_false, if_false]
        · have hriPos : 1 < g.ramification i := by simpa [hir] using hr
          apply (g.mandatoryCoefficient_eq_iff_of_ramification_eq
            hacute hijRam hriPos mandatory (hm.trans hir.symm)).mpr
          exact Or.inr (by rw [hir, hweight]; exact hbelowMandatory)
      · exfalso
        apply hother
        simp [stageCoefficient, hir, hjr, hm]
    · rcases lower with ⟨otherR, otherB⟩
      by_cases hm : otherR.val = r
      · have heqRam := g.lowerCoefficient_eq_iff_of_ramification_eq
          hacute hijRam otherR (hm.trans hir.symm) otherB
        have hnot : ¬(i = j ∨ g.rescaledEdge i j <
            (otherB.val : ℚ) / (g.ramification i : ℚ) ^ 2) :=
          fun h => hother (heqRam.mpr h)
        have hleB : otherB.val ≤ b := by
          rw [hir, hweight] at hnot
          push Not at hnot
          have hdiv : (otherB.val : ℚ) / (r : ℚ) ^ 2 ≤
              (b : ℚ) / (r : ℚ) ^ 2 := hnot.2
          have hcast : (otherB.val : ℚ) ≤ b :=
            (div_le_div_iff_of_pos_right hrSqQ).mp hdiv
          exact_mod_cast hcast
        rw [lowerStage_exponent]
        simp only [MonomialStage.exponent, hm]
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.add_le_add_right hleB 1) hrQ.le
      · exfalso
        apply hother
        simp [stageCoefficient, hir, hjr, hm]

theorem mandatoryStage_isHighestDifference_oriented
    {n r s : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hir : g.ramification i = r) (hjs : g.ramification j = s)
    (hr : 1 < r) (hrs : s = 1 ∨ r < s)
    (hrmax : r ≤ g.maxRamification)
    (hweight : g.rescaledEdge i j = 1 / (r : ℚ)) :
    g.IsHighestDifferenceStage hacute i j (g.mandatoryStage r hrmax) := by
  have hrsNe : r ≠ s := by omega
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hrOneQ : (1 : ℚ) < r := by exact_mod_cast hr
  have hweightLtOne : (1 : ℚ) / r < 1 := (div_lt_one hrQ).mpr hrOneQ
  constructor
  · unfold mandatoryStage
    simp only [stageCoefficient, hir, hjs, hr, true_and, if_pos]
    rw [if_neg]
    · exact g.thresholdCoefficient_ne_zero hacute _ i
    · exact fun hsr => hrsNe hsr.1
  · intro other hother
    rcases other with high | (mandatory | lower)
    · exfalso
      apply hother
      apply (g.highCoefficient_eq_iff hacute i j high).mpr
      right
      rw [hweight]
      exact hweightLtOne.trans_le (by norm_num)
    · by_cases hmr : mandatory.val = r
      · rw [mandatoryStage_exponent]
        simp only [MonomialStage.exponent, hmr]
        exact le_rfl
      · by_cases hms : mandatory.val = s
        · rcases hrs with rfl | hrs
          · exfalso
            apply hother
            simp [stageCoefficient, hir, hjs, hms]
          · rw [mandatoryStage_exponent]
            simp only [MonomialStage.exponent, hms]
            have hsQ : (0 : ℚ) < s := by
              exact_mod_cast (Nat.zero_lt_of_lt (lt_trans hr hrs))
            have hrsQ : (r : ℚ) < s := by exact_mod_cast hrs
            have hinv : (1 : ℚ) / s ≤ 1 / r :=
              (one_div_le_one_div_of_le hrQ hrsQ.le)
            linarith
        · exfalso
          apply hother
          simp [stageCoefficient, hir, hjs, hmr, hms]
    · rcases lower with ⟨otherR, otherB⟩
      calc
        MonomialStage.exponent (.inr (.inr ⟨otherR, otherB⟩)) ≤ 1 :=
          MonomialStage.lower_exponent_le_one otherR otherB
        _ ≤ (g.mandatoryStage r hrmax).exponent := by
          rw [mandatoryStage_exponent]
          have hnonneg : (0 : ℚ) ≤ 1 / r := div_nonneg zero_le_one hrQ.le
          linarith

theorem isHighestDifferenceStage_symm {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n} {stage : g.MonomialStage} :
    g.IsHighestDifferenceStage hacute i j stage ↔
      g.IsHighestDifferenceStage hacute j i stage := by
  simp only [IsHighestDifferenceStage, ne_eq]
  constructor <;> rintro ⟨hdiff, hmax⟩ <;>
    exact ⟨Ne.symm hdiff, fun other hother => hmax other (Ne.symm hother)⟩

/-- Every exact elementary pair presentation selects a highest separating stage in the single
global coefficient packet. -/
theorem pairPresentation_hasHighestDifferenceStage
    {n r₀ s₀ edge₀ : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n} (hij : i ≠ j)
    (hir₀ : g.ramification i = r₀) (hjs₀ : g.ramification j = s₀)
    (hijEdge : g.edge i j = edge₀)
    (p : ElementaryPairPresentation r₀ s₀ edge₀) :
    ∃ stage : g.MonomialStage, g.IsHighestDifferenceStage hacute i j stage := by
  classical
  cases p with
  | unramified _ =>
      by_cases hedge : edge₀ = 0
      · subst edge₀
        have hrmax : 1 ≤ g.maxRamification :=
          hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.lowerStage 1 0 hrmax (by omega), ?_⟩
        apply g.lowerStage_isHighestDifference_sameRamification hacute hij hir₀ hjs₀
        simp [rescaledEdge, hir₀, hjs₀, hedge]
      · have hk : 0 < edge₀ := Nat.pos_of_ne_zero hedge
        have hkmax : edge₀ ≤ g.maxEdge := hijEdge ▸ g.edge_le_maxEdge i j
        refine ⟨g.highStage edge₀ hk hkmax, ?_⟩
        apply g.highStage_isHighestDifference hacute hij hk hkmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
  | unramifiedAiryBase hr =>
      have hrmax : s₀ ≤ g.maxRamification := hjs₀ ▸ g.ramification_le_maxRamification j
      refine ⟨g.mandatoryStage s₀ hrmax, ?_⟩
      apply (g.isHighestDifferenceStage_symm hacute).mpr
      apply g.mandatoryStage_isHighestDifference_oriented hacute hjs₀ hir₀ hr (Or.inl rfl)
        hrmax
      rw [rescaledEdge, g.edge_symm, hijEdge, hir₀, hjs₀]
      norm_num
  | unramifiedAiryHigh hr hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        exact (show k ≤ s₀ * k from by
          calc
            k = 1 * k := by simp
            _ ≤ s₀ * k := Nat.mul_le_mul_right k (by omega)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_⟩
      apply g.highStage_isHighestDifference hacute hij hk hkmax
      simp [rescaledEdge, hir₀, hjs₀, hijEdge]
      field_simp
  | airyUnramifiedBase hr =>
      have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
      refine ⟨g.mandatoryStage r₀ hrmax, ?_⟩
      apply g.mandatoryStage_isHighestDifference_oriented hacute hir₀ hjs₀ hr (Or.inl rfl)
        hrmax
      simp [rescaledEdge, hir₀, hjs₀, hijEdge]
  | airyUnramifiedHigh hr hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        exact (show k ≤ r₀ * k from by
          calc
            k = 1 * k := by simp
            _ ≤ r₀ * k := Nat.mul_le_mul_right k (by omega)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_⟩
      apply g.highStage_isHighestDifference hacute hij hk hkmax
      simp [rescaledEdge, hir₀, hjs₀, hijEdge]
      field_simp
  | unequalAiryBase hr hs hne =>
      rcases lt_or_gt_of_ne hne with hrs | hsr
      · have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.mandatoryStage r₀ hrmax, ?_⟩
        apply g.mandatoryStage_isHighestDifference_oriented hacute hir₀ hjs₀ hr
          (Or.inr hrs) hrmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge, Nat.max_eq_right hrs.le]
        field_simp
      · have hsmax : s₀ ≤ g.maxRamification := hjs₀ ▸ g.ramification_le_maxRamification j
        refine ⟨g.mandatoryStage s₀ hsmax, ?_⟩
        apply (g.isHighestDifferenceStage_symm hacute).mpr
        apply g.mandatoryStage_isHighestDifference_oriented hacute hjs₀ hir₀ hs
          (Or.inr hsr) hsmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge, Nat.max_eq_left hsr.le,
          g.edge_symm]
        field_simp
  | unequalAiryHigh hr hs hne hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        have hrsPos : 0 < r₀ * s₀ := Nat.mul_pos (Nat.zero_lt_of_lt hr) (Nat.zero_lt_of_lt hs)
        exact (show k ≤ r₀ * s₀ * k from by
          calc
            k = 1 * k := by simp
            _ ≤ (r₀ * s₀) * k := Nat.mul_le_mul_right k (by omega)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_⟩
      apply g.highStage_isHighestDifference hacute hij hk hkmax
      simp [rescaledEdge, hir₀, hjs₀, hijEdge]
      field_simp
  | equalAiryLow hr hedge =>
      by_cases heq : edge₀ = r₀
      · subst edge₀
        have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.mandatoryStage r₀ hrmax, ?_⟩
        apply g.mandatoryStage_isHighestDifference_sameRamification hacute hij hir₀ hjs₀ hr
          hrmax
        simp [rescaledEdge, hir₀, hjs₀, heq]
      · have hlt : edge₀ < r₀ := lt_of_le_of_ne hedge heq
        have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.lowerStage r₀ edge₀ hrmax hlt, ?_⟩
        apply g.lowerStage_isHighestDifference_sameRamification hacute hij hir₀ hjs₀ hlt
          hrmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
        ring
  | equalAiryHigh hr hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        have hrPos : 0 < r₀ := Nat.zero_lt_of_lt hr
        exact (show k ≤ r₀ ^ 2 * k from by
          calc
            k = 1 * k := by simp
            _ ≤ (r₀ ^ 2) * k := Nat.mul_le_mul_right k (by nlinarith)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_⟩
      apply g.highStage_isHighestDifference hacute hij hk hkmax
      simp [rescaledEdge, hir₀, hjs₀, hijEdge]
      field_simp

theorem pairPresentation_hasHighestDifferenceStage_indexed
    {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n} (hij : i ≠ j)
    (p : ElementaryPairPresentation
      (g.ramification i) (g.ramification j) (g.edge i j)) :
    ∃ stage : g.MonomialStage, g.IsHighestDifferenceStage hacute i j stage :=
  g.pairPresentation_hasHighestDifferenceStage hacute hij rfl rfl rfl p

/-- A highest stage whose exponent cannot receive a second unequal contribution.  This is the
precise no-cancellation condition needed after collecting stages into a Puiseux polynomial. -/
def IsUncancelledHighestDifferenceStage {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i j : Fin n)
    (stage : g.MonomialStage) : Prop :=
  g.IsHighestDifferenceStage hacute i j stage ∧
    ∀ other : g.MonomialStage, other.exponent = stage.exponent →
      g.stageCoefficient hacute i other ≠ g.stageCoefficient hacute j other →
        other = stage

theorem highStage_isUncancelledHighestDifference
    {n k : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hij : i ≠ j) (hk : 0 < k) (hkmax : k ≤ g.maxEdge)
    (hweight : g.rescaledEdge i j = k) :
    g.IsUncancelledHighestDifferenceStage hacute i j (g.highStage k hk hkmax) := by
  refine ⟨g.highStage_isHighestDifference hacute hij hk hkmax hweight, ?_⟩
  intro other hexponent hdiff
  rcases other with high | (mandatory | lower)
  · apply congrArg Sum.inl
    apply Fin.ext
    rw [highStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    norm_cast at hexponent
    change high.val = k - 1
    omega
  · exfalso
    have hcandidate : (g.highStage k hk hkmax).exponent = (k + 1 : ℕ) :=
      g.highStage_exponent k hk hkmax
    by_cases hsmall : mandatory.val ≤ 1
    · have hz : mandatory.val = 0 ∨ mandatory.val = 1 := by omega
      rcases hz with hz | hz
      · apply hdiff
        simp [stageCoefficient, hz]
      · apply hdiff
        simp [stageCoefficient, hz]
    · have hqQ : (1 : ℚ) < mandatory.val := by exact_mod_cast (lt_of_not_ge hsmall)
      have hqPos : (0 : ℚ) < mandatory.val := lt_trans zero_lt_one hqQ
      have hlt : MonomialStage.exponent (.inr (.inl mandatory)) < 2 := by
        simp only [MonomialStage.exponent]
        have : (1 : ℚ) / mandatory.val < 1 := (div_lt_one hqPos).mpr hqQ
        linarith
      rw [hcandidate] at hexponent
      have hkLower : (2 : ℚ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ hk)
      linarith
  · exfalso
    have hle := MonomialStage.lower_exponent_le_one lower.fst lower.snd
    rw [g.highStage_exponent k hk hkmax] at hexponent
    have hkLower : (2 : ℚ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ hk)
    linarith

theorem mandatoryStage_isUncancelledHighestDifference_sameRamification
    {n r : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hij : i ≠ j) (hir : g.ramification i = r)
    (hjr : g.ramification j = r) (hr : 1 < r)
    (hrmax : r ≤ g.maxRamification)
    (hweight : g.rescaledEdge i j = 1 / (r : ℚ)) :
    g.IsUncancelledHighestDifferenceStage hacute i j (g.mandatoryStage r hrmax) := by
  refine ⟨g.mandatoryStage_isHighestDifference_sameRamification hacute hij hir hjr hr
    hrmax hweight, ?_⟩
  intro other hexponent hdiff
  rcases other with high | (mandatory | lower)
  · exfalso
    rw [mandatoryStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hhigh : (2 : ℚ) ≤ (high.val + 2 : ℕ) := by norm_num
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hrOneQ : (1 : ℚ) < r := by exact_mod_cast hr
    have hcand : 1 + 1 / (r : ℚ) < 2 := by
      have := (div_lt_one hrQ).mpr hrOneQ
      linarith
    linarith
  · apply congrArg Sum.inr
    apply congrArg Sum.inl
    apply Fin.ext
    rw [mandatoryStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hinv : ((mandatory.val : ℚ)⁻¹) = ((r : ℚ)⁻¹) := by
      simpa [one_div] using (add_left_cancel hexponent)
    have hcast : (mandatory.val : ℚ) = (r : ℚ) := inv_injective hinv
    exact_mod_cast hcast
  · exfalso
    have hle := MonomialStage.lower_exponent_le_one lower.fst lower.snd
    rw [mandatoryStage_exponent] at hexponent
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hpos : (0 : ℚ) < 1 / r := div_pos zero_lt_one hrQ
    linarith

theorem mandatoryStage_isUncancelledHighestDifference_oriented
    {n r s : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hir : g.ramification i = r) (hjs : g.ramification j = s)
    (hr : 1 < r) (hrs : s = 1 ∨ r < s)
    (hrmax : r ≤ g.maxRamification)
    (hweight : g.rescaledEdge i j = 1 / (r : ℚ)) :
    g.IsUncancelledHighestDifferenceStage hacute i j (g.mandatoryStage r hrmax) := by
  refine ⟨g.mandatoryStage_isHighestDifference_oriented hacute hir hjs hr hrs hrmax
    hweight, ?_⟩
  intro other hexponent hdiff
  rcases other with high | (mandatory | lower)
  · exfalso
    rw [mandatoryStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hhigh : (2 : ℚ) ≤ (high.val + 2 : ℕ) := by norm_num
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hrOneQ : (1 : ℚ) < r := by exact_mod_cast hr
    have hcand : 1 + 1 / (r : ℚ) < 2 := by
      have := (div_lt_one hrQ).mpr hrOneQ
      linarith
    linarith
  · apply congrArg Sum.inr
    apply congrArg Sum.inl
    apply Fin.ext
    rw [mandatoryStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hinv : ((mandatory.val : ℚ)⁻¹) = ((r : ℚ)⁻¹) := by
      simpa [one_div] using (add_left_cancel hexponent)
    have hcast : (mandatory.val : ℚ) = (r : ℚ) := inv_injective hinv
    exact_mod_cast hcast
  · exfalso
    have hle := MonomialStage.lower_exponent_le_one lower.fst lower.snd
    rw [mandatoryStage_exponent] at hexponent
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hpos : (0 : ℚ) < 1 / r := div_pos zero_lt_one hrQ
    linarith

theorem lowerStage_isUncancelledHighestDifference_sameRamification
    {n r b : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    (hij : i ≠ j) (hir : g.ramification i = r)
    (hjr : g.ramification j = r) (hb : b < r)
    (hrmax : r ≤ g.maxRamification)
    (hweight : g.rescaledEdge i j = (b : ℚ) / (r : ℚ) ^ 2) :
    g.IsUncancelledHighestDifferenceStage hacute i j (g.lowerStage r b hrmax hb) := by
  refine ⟨g.lowerStage_isHighestDifference_sameRamification hacute hij hir hjr hb hrmax
    hweight, ?_⟩
  intro other hexponent hdiff
  rcases other with high | (mandatory | lower)
  · exfalso
    rw [lowerStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hhigh : (2 : ℚ) ≤ (high.val + 2 : ℕ) := by norm_num
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hb)
    have hbQ : (((b + 1 : ℕ) : ℚ) / r) ≤ 1 := by
      apply (div_le_one hrQ).mpr
      exact_mod_cast Nat.succ_le_of_lt hb
    linarith
  · exfalso
    by_cases hsmall : mandatory.val ≤ 1
    · have hz : mandatory.val = 0 ∨ mandatory.val = 1 := by omega
      rcases hz with hz | hz
      · apply hdiff
        simp [stageCoefficient, hz]
      · apply hdiff
        simp [stageCoefficient, hz]
    · have hqQ : (1 : ℚ) < mandatory.val := by exact_mod_cast (lt_of_not_ge hsmall)
      have hqPos : (0 : ℚ) < mandatory.val := lt_trans zero_lt_one hqQ
      have hmandatory : (1 : ℚ) < MonomialStage.exponent (.inr (.inl mandatory)) := by
        simp only [MonomialStage.exponent]
        have : (0 : ℚ) < 1 / mandatory.val := div_pos zero_lt_one hqPos
        linarith
      rw [lowerStage_exponent] at hexponent
      have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hb)
      have hcand : (((b + 1 : ℕ) : ℚ) / r) ≤ 1 := by
        apply (div_le_one hrQ).mpr
        exact_mod_cast Nat.succ_le_of_lt hb
      linarith
  · rcases lower with ⟨otherR, otherB⟩
    have hotherR : otherR.val = r := by
      by_contra hne
      apply hdiff
      simp [stageCoefficient, hir, hjr, hne]
    have hotherRFin : otherR = ⟨r, Nat.lt_succ_of_le hrmax⟩ := Fin.ext hotherR
    subst otherR
    have hnum : ((otherB.val + 1 : ℕ) : ℚ) = (b + 1 : ℕ) := by
      rw [lowerStage_exponent] at hexponent
      simp only [MonomialStage.exponent] at hexponent
      have hrNe : (r : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hb))
      exact (div_left_inj' hrNe).mp hexponent
    have hotherB : otherB.val = b := by
      have : otherB.val + 1 = b + 1 := by exact_mod_cast hnum
      omega
    have hotherBFin : otherB = ⟨b, hb⟩ := Fin.ext hotherB
    subst otherB
    rfl

theorem isUncancelledHighestDifferenceStage_symm {n : ℕ}
    (g : ElementaryDecoratedGraph n) (hacute : g.HasAcuteIsoscelesRescaling)
    {i j : Fin n} {stage : g.MonomialStage} :
    g.IsUncancelledHighestDifferenceStage hacute i j stage ↔
      g.IsUncancelledHighestDifferenceStage hacute j i stage := by
  constructor <;> rintro ⟨hhighest, hisolated⟩
  · refine ⟨(g.isHighestDifferenceStage_symm hacute).mp hhighest, ?_⟩
    exact fun other hexponent hdiff => hisolated other hexponent (Ne.symm hdiff)
  · refine ⟨(g.isHighestDifferenceStage_symm hacute).mpr hhighest, ?_⟩
    exact fun other hexponent hdiff => hisolated other hexponent (Ne.symm hdiff)

/-- The exhaustive elementary spectrum admits one global, exponent-isolated coefficient packet. -/
theorem pairPresentation_hasUncancelledHighestDifferenceStage
    {n r₀ s₀ edge₀ : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n} (hij : i ≠ j)
    (hir₀ : g.ramification i = r₀) (hjs₀ : g.ramification j = s₀)
    (hijEdge : g.edge i j = edge₀)
    (p : ElementaryPairPresentation r₀ s₀ edge₀) :
    ∃ stage : g.MonomialStage,
      g.IsUncancelledHighestDifferenceStage hacute i j stage ∧
        g.StageRealizesEdge i j stage := by
  classical
  cases p with
  | unramified _ =>
      by_cases hedge : edge₀ = 0
      · subst edge₀
        have hrmax : 1 ≤ g.maxRamification :=
          hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.lowerStage 1 0 hrmax (by omega), ?_, ?_⟩
        · apply g.lowerStage_isUncancelledHighestDifference_sameRamification
            hacute hij hir₀ hjs₀
          simp [rescaledEdge, hir₀, hjs₀, hedge]
        · exact (g.lowerStage_realizesEdge_iff i j hrmax (by omega)).2
            ⟨hir₀, hjs₀, hedge⟩
      · have hk : 0 < edge₀ := Nat.pos_of_ne_zero hedge
        have hkmax : edge₀ ≤ g.maxEdge := hijEdge ▸ g.edge_le_maxEdge i j
        refine ⟨g.highStage edge₀ hk hkmax, ?_, ?_⟩
        · apply g.highStage_isUncancelledHighestDifference hacute hij hk hkmax
          simp [rescaledEdge, hir₀, hjs₀, hijEdge]
        · apply (g.highStage_realizesEdge_iff i j hk hkmax).2
          simp [hir₀, hjs₀, hijEdge]
  | unramifiedAiryBase hr =>
      have hrmax : s₀ ≤ g.maxRamification := hjs₀ ▸ g.ramification_le_maxRamification j
      refine ⟨g.mandatoryStage s₀ hrmax, ?_, ?_⟩
      · apply (g.isUncancelledHighestDifferenceStage_symm hacute).mpr
        apply g.mandatoryStage_isUncancelledHighestDifference_oriented
          hacute hjs₀ hir₀ hr (Or.inl rfl) hrmax
        rw [rescaledEdge, g.edge_symm, hijEdge, hir₀, hjs₀]
        norm_num
      · apply (g.mandatoryStage_realizesEdge_iff i j hrmax).2
        simp [hir₀, hjs₀, hijEdge]
  | unramifiedAiryHigh hr hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        exact (show k ≤ s₀ * k from by
          calc
            k = 1 * k := by simp
            _ ≤ s₀ * k := Nat.mul_le_mul_right k (by omega)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_, ?_⟩
      · apply g.highStage_isUncancelledHighestDifference hacute hij hk hkmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
        field_simp
      · apply (g.highStage_realizesEdge_iff i j hk hkmax).2
        simp [hir₀, hjs₀, hijEdge]
  | airyUnramifiedBase hr =>
      have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
      refine ⟨g.mandatoryStage r₀ hrmax, ?_, ?_⟩
      · apply g.mandatoryStage_isUncancelledHighestDifference_oriented
          hacute hir₀ hjs₀ hr (Or.inl rfl) hrmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
      · apply (g.mandatoryStage_realizesEdge_iff i j hrmax).2
        simp [hir₀, hjs₀, hijEdge]
  | airyUnramifiedHigh hr hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        exact (show k ≤ r₀ * k from by
          calc
            k = 1 * k := by simp
            _ ≤ r₀ * k := Nat.mul_le_mul_right k (by omega)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_, ?_⟩
      · apply g.highStage_isUncancelledHighestDifference hacute hij hk hkmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
        field_simp
      · apply (g.highStage_realizesEdge_iff i j hk hkmax).2
        simp [hir₀, hjs₀, hijEdge]
  | unequalAiryBase hr hs hne =>
      rcases lt_or_gt_of_ne hne with hrs | hsr
      · have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.mandatoryStage r₀ hrmax, ?_, ?_⟩
        · apply g.mandatoryStage_isUncancelledHighestDifference_oriented
            hacute hir₀ hjs₀ hr (Or.inr hrs) hrmax
          simp [rescaledEdge, hir₀, hjs₀, hijEdge, Nat.max_eq_right hrs.le]
          field_simp
        · apply (g.mandatoryStage_realizesEdge_iff i j hrmax).2
          simp [hir₀, hjs₀, hijEdge, Nat.max_eq_right hrs.le, Nat.mul_comm]
      · have hsmax : s₀ ≤ g.maxRamification := hjs₀ ▸ g.ramification_le_maxRamification j
        refine ⟨g.mandatoryStage s₀ hsmax, ?_, ?_⟩
        · apply (g.isUncancelledHighestDifferenceStage_symm hacute).mpr
          apply g.mandatoryStage_isUncancelledHighestDifference_oriented
            hacute hjs₀ hir₀ hs (Or.inr hsr) hsmax
          simp [rescaledEdge, hir₀, hjs₀, hijEdge, Nat.max_eq_left hsr.le,
            g.edge_symm]
          field_simp
        · apply (g.mandatoryStage_realizesEdge_iff i j hsmax).2
          simp [hir₀, hjs₀, hijEdge, Nat.max_eq_left hsr.le]
  | unequalAiryHigh hr hs hne hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        have hproduct : 0 < r₀ * s₀ :=
          Nat.mul_pos (Nat.zero_lt_of_lt hr) (Nat.zero_lt_of_lt hs)
        exact (show k ≤ r₀ * s₀ * k from by
          calc
            k = 1 * k := by simp
            _ ≤ (r₀ * s₀) * k :=
              Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr hproduct)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_, ?_⟩
      · apply g.highStage_isUncancelledHighestDifference hacute hij hk hkmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
        field_simp
      · apply (g.highStage_realizesEdge_iff i j hk hkmax).2
        simp [hir₀, hjs₀, hijEdge]
  | equalAiryLow hr hedge =>
      by_cases heq : edge₀ = r₀
      · subst edge₀
        have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.mandatoryStage r₀ hrmax, ?_, ?_⟩
        · apply g.mandatoryStage_isUncancelledHighestDifference_sameRamification
            hacute hij hir₀ hjs₀ hr hrmax
          simp [rescaledEdge, hir₀, hjs₀, heq]
        · apply (g.mandatoryStage_realizesEdge_iff i j hrmax).2
          simp [hir₀, hjs₀, heq]
      · have hlt : edge₀ < r₀ := lt_of_le_of_ne hedge heq
        have hrmax : r₀ ≤ g.maxRamification := hir₀ ▸ g.ramification_le_maxRamification i
        refine ⟨g.lowerStage r₀ edge₀ hrmax hlt, ?_, ?_⟩
        · apply g.lowerStage_isUncancelledHighestDifference_sameRamification
            hacute hij hir₀ hjs₀ hlt hrmax
          simp [rescaledEdge, hir₀, hjs₀, hijEdge]
          ring
        · exact (g.lowerStage_realizesEdge_iff i j hrmax hlt).2
            ⟨hir₀, hjs₀, hijEdge⟩
  | equalAiryHigh hr hk =>
      rename_i k
      have hkmax : k ≤ g.maxEdge := by
        have hedgeMax := g.edge_le_maxEdge i j
        rw [hijEdge] at hedgeMax
        exact (show k ≤ r₀ ^ 2 * k from by
          calc
            k = 1 * k := by simp
            _ ≤ (r₀ ^ 2) * k := Nat.mul_le_mul_right k (by nlinarith)).trans hedgeMax
      refine ⟨g.highStage k hk hkmax, ?_, ?_⟩
      · apply g.highStage_isUncancelledHighestDifference hacute hij hk hkmax
        simp [rescaledEdge, hir₀, hjs₀, hijEdge]
        field_simp
      · apply (g.highStage_realizesEdge_iff i j hk hkmax).2
        simp [hir₀, hjs₀, hijEdge, pow_two]

theorem pairPresentation_hasUncancelledHighestDifferenceStage_indexed
    {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n} (hij : i ≠ j)
    (p : ElementaryPairPresentation
      (g.ramification i) (g.ramification j) (g.edge i j)) :
    ∃ stage : g.MonomialStage,
      g.IsUncancelledHighestDifferenceStage hacute i j stage ∧
        g.StageRealizesEdge i j stage :=
  g.pairPresentation_hasUncancelledHighestDifferenceStage
    hacute hij rfl rfl rfl p

/-- Actual finite Puiseux polynomial obtained by collecting every global stage with the same
rational exponent.  The `Finset.univ` presentation makes collisions explicit. -/
def globalPuiseuxPolynomial {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i : Fin n) : ℚ →₀ ℂ :=
  ∑ stage : g.MonomialStage,
    Finsupp.single stage.exponent (g.stageCoefficient hacute i stage)

theorem globalPuiseuxPolynomial_apply {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) (i : Fin n) (q : ℚ) :
    g.globalPuiseuxPolynomial hacute i q =
      ∑ stage : g.MonomialStage,
        if stage.exponent = q then g.stageCoefficient hacute i stage else 0 := by
  classical
  simp [globalPuiseuxPolynomial, Finsupp.single_apply]

/-- A mandatory Airy exponent is represented by one unique global monomial stage. -/
theorem eq_mandatoryStage_of_exponent_eq {n r : ℕ} (g : ElementaryDecoratedGraph n)
    (hr : 1 < r) (hrmax : r ≤ g.maxRamification) (other : g.MonomialStage)
    (hexponent : other.exponent = (g.mandatoryStage r hrmax).exponent) :
    other = g.mandatoryStage r hrmax := by
  rcases other with high | (mandatory | lower)
  · exfalso
    rw [mandatoryStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hhigh : (2 : ℚ) ≤ (high.val + 2 : ℕ) := by norm_num
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hrOneQ : (1 : ℚ) < r := by exact_mod_cast hr
    have hcand : 1 + 1 / (r : ℚ) < 2 := by
      have := (div_lt_one hrQ).mpr hrOneQ
      linarith
    linarith
  · apply congrArg Sum.inr
    apply congrArg Sum.inl
    apply Fin.ext
    rw [mandatoryStage_exponent] at hexponent
    simp only [MonomialStage.exponent] at hexponent
    have hinv : ((mandatory.val : ℚ)⁻¹) = ((r : ℚ)⁻¹) := by
      simpa [one_div] using (add_left_cancel hexponent)
    have hcast : (mandatory.val : ℚ) = (r : ℚ) := inv_injective hinv
    exact_mod_cast hcast
  · exfalso
    have hle := MonomialStage.lower_exponent_le_one lower.fst lower.snd
    rw [mandatoryStage_exponent] at hexponent
    have hrQ : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hpos : (0 : ℚ) < 1 / r := div_pos zero_lt_one hrQ
    linarith

theorem stageCoefficient_mandatoryStage_ne_zero {n : ℕ}
    (g : ElementaryDecoratedGraph n) (hacute : g.HasAcuteIsoscelesRescaling)
    (i : Fin n) (hr : 1 < g.ramification i)
    (hrmax : g.ramification i ≤ g.maxRamification) :
    g.stageCoefficient hacute i (g.mandatoryStage (g.ramification i) hrmax) ≠ 0 := by
  simp [stageCoefficient, mandatoryStage, hr, g.thresholdCoefficient_ne_zero]

/-- Collection of equal rational exponents cannot erase the mandatory Airy monomial. -/
theorem globalPuiseuxPolynomial_mandatory_ne_zero {n : ℕ}
    (g : ElementaryDecoratedGraph n) (hacute : g.HasAcuteIsoscelesRescaling)
    (i : Fin n) (hr : 1 < g.ramification i) :
    g.globalPuiseuxPolynomial hacute i
        (1 + 1 / (g.ramification i : ℚ)) ≠ 0 := by
  classical
  let hrmax : g.ramification i ≤ g.maxRamification :=
    g.ramification_le_maxRamification i
  let target := g.mandatoryStage (g.ramification i) hrmax
  have htargetExponent : target.exponent = 1 + 1 / (g.ramification i : ℚ) := by
    simp [target]
  have hcoeff : g.stageCoefficient hacute i target ≠ 0 := by
    exact g.stageCoefficient_mandatoryStage_ne_zero hacute i hr hrmax
  rw [g.globalPuiseuxPolynomial_apply]
  have hsum :
      (∑ other : g.MonomialStage,
        if other.exponent = 1 + 1 / (g.ramification i : ℚ) then
          g.stageCoefficient hacute i other else 0) =
        g.stageCoefficient hacute i target := by
    calc
      _ = if target.exponent = 1 + 1 / (g.ramification i : ℚ) then
          g.stageCoefficient hacute i target else 0 := by
        apply Finset.sum_eq_single target
        · intro other _ hne
          by_cases hexponent : other.exponent = 1 + 1 / (g.ramification i : ℚ)
          · have heq : other = target :=
              g.eq_mandatoryStage_of_exponent_eq hr hrmax other
                (hexponent.trans htargetExponent.symm)
            exact (hne heq).elim
          · rw [if_neg]
            exact fun h => hexponent (by simpa [one_div] using h)
        · simp
      _ = g.stageCoefficient hacute i target := by simp [htargetExponent]
  rw [hsum]
  exact hcoeff

/-- Every nonzero exponent of an elementary realization is either an integral high stage, the
mandatory Airy stage, or a lower fractional stage with the prescribed ramification. -/
def HasElementaryPuiseuxSupport (r : ℕ) (p : ℚ →₀ ℂ) : Prop :=
  ∀ q : ℚ, p q ≠ 0 →
    (∃ k : ℕ, 0 < k ∧ q = k) ∨
      (1 < r ∧ q = 1 + 1 / (r : ℚ)) ∨
      ∃ b : ℕ, b < r ∧ q = (b + 1 : ℕ) / (r : ℚ)

/-- Intrinsic certificate that a collected finite Puiseux polynomial is unramified at `r=1`, or
has exactly the one mandatory simple-Airy gcd drop when `r>1`. -/
def IsElementaryPuiseuxPolynomialOfRamification (r : ℕ) (p : ℚ →₀ ℂ) : Prop :=
  HasElementaryPuiseuxSupport r p ∧
    (r = 1 ∨ (1 < r ∧ p (1 + 1 / (r : ℚ)) ≠ 0))

theorem globalPuiseuxPolynomial_hasElementarySupport {n : ℕ}
    (g : ElementaryDecoratedGraph n) (hacute : g.HasAcuteIsoscelesRescaling)
    (i : Fin n) :
    HasElementaryPuiseuxSupport (g.ramification i)
      (g.globalPuiseuxPolynomial hacute i) := by
  classical
  intro q hq
  rw [g.globalPuiseuxPolynomial_apply] at hq
  obtain ⟨stage, _, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have hexponent : stage.exponent = q := by
    by_contra hne
    exact hterm (by simp [hne])
  have hcoeff : g.stageCoefficient hacute i stage ≠ 0 := by
    simpa [hexponent] using hterm
  rcases stage with high | (mandatory | lower)
  · left
    refine ⟨high.val + 2, by omega, ?_⟩
    simpa [MonomialStage.exponent] using hexponent.symm
  · have hactive : mandatory.val = g.ramification i ∧ 1 < mandatory.val := by
      by_contra h
      apply hcoeff
      simp [stageCoefficient, h]
    right
    left
    constructor
    · simpa [hactive.1] using hactive.2
    · simpa [MonomialStage.exponent, hactive.1] using hexponent.symm
  · have hactive : lower.fst.val = g.ramification i := by
      by_contra h
      apply hcoeff
      simp [stageCoefficient, h]
    right
    right
    refine ⟨lower.snd.val, ?_, ?_⟩
    · simpa [hactive] using lower.snd.isLt
    · simpa [MonomialStage.exponent, hactive] using hexponent.symm

theorem globalPuiseuxPolynomial_isElementary {n : ℕ}
    (g : ElementaryDecoratedGraph n) (hacute : g.HasAcuteIsoscelesRescaling)
    (i : Fin n) :
    IsElementaryPuiseuxPolynomialOfRamification (g.ramification i)
      (g.globalPuiseuxPolynomial hacute i) := by
  refine ⟨g.globalPuiseuxPolynomial_hasElementarySupport hacute i, ?_⟩
  by_cases hr : g.ramification i = 1
  · exact Or.inl hr
  · right
    have hri : 1 < g.ramification i := by
      have := g.ramification_pos i
      omega
    exact ⟨hri, g.globalPuiseuxPolynomial_mandatory_ne_zero hacute i hri⟩

/-- `e` is the largest exponent where two finite Puiseux polynomials differ. -/
def HasHighestDifferenceExponent (left right : ℚ →₀ ℂ) (e : ℚ) : Prop :=
  left e ≠ right e ∧ ∀ q : ℚ, e < q → left q = right q

/-- Coordinate-free arithmetic meaning of a highest Puiseux difference: its exponent and the two
ramifications recover the edge by exactly one of the high, mandatory, or lower formulas. -/
def HighestDifferenceRealizesEdge (r s edge : ℕ) (e : ℚ) : Prop :=
  (∃ k : ℕ, 0 < k ∧ e = (k + 1 : ℕ) ∧ edge = r * s * k) ∨
    (∃ q : ℕ, 0 < q ∧ e = 1 + 1 / (q : ℚ) ∧ edge * q = r * s) ∨
    ∃ q b : ℕ, 0 < q ∧ b < q ∧ r = q ∧ s = q ∧
      e = (b + 1 : ℕ) / (q : ℚ) ∧ edge = b

theorem stageRealizesEdge_gives_highestDifferenceRelation {n : ℕ}
    (g : ElementaryDecoratedGraph n) (i j : Fin n) (stage : g.MonomialStage)
    (hstage : g.StageRealizesEdge i j stage) :
    HighestDifferenceRealizesEdge (g.ramification i) (g.ramification j)
      (g.edge i j) stage.exponent := by
  rcases stage with high | (mandatory | lower)
  · left
    refine ⟨high.val + 1, by omega, ?_, ?_⟩
    · simp only [MonomialStage.exponent]
    · exact hstage
  · right
    left
    have hq : 0 < mandatory.val := by
      have hi := g.ramification_pos i
      have hj := g.ramification_pos j
      by_contra h
      have hzero : mandatory.val = 0 := Nat.eq_zero_of_not_pos h
      have hprod : g.ramification i * g.ramification j ≠ 0 :=
        Nat.mul_ne_zero (Nat.ne_of_gt hi) (Nat.ne_of_gt hj)
      apply hprod
      simpa [hzero] using hstage.symm
    exact ⟨mandatory.val, hq, rfl, hstage⟩
  · right
    right
    exact ⟨lower.fst.val, lower.snd.val, Nat.zero_lt_of_lt lower.snd.isLt,
      lower.snd.isLt, hstage.1, hstage.2.1, rfl, hstage.2.2⟩

theorem uncancelledStage_gives_highestDifferenceExponent
    {n : ℕ} (g : ElementaryDecoratedGraph n)
    (hacute : g.HasAcuteIsoscelesRescaling) {i j : Fin n}
    {stage : g.MonomialStage}
    (hstage : g.IsUncancelledHighestDifferenceStage hacute i j stage) :
    HasHighestDifferenceExponent (g.globalPuiseuxPolynomial hacute i)
      (g.globalPuiseuxPolynomial hacute j) stage.exponent := by
  classical
  rcases hstage with ⟨⟨hdiff, hhighest⟩, hisolated⟩
  constructor
  · have hsum :
        g.globalPuiseuxPolynomial hacute i stage.exponent -
            g.globalPuiseuxPolynomial hacute j stage.exponent =
          g.stageCoefficient hacute i stage - g.stageCoefficient hacute j stage := by
      rw [g.globalPuiseuxPolynomial_apply, g.globalPuiseuxPolynomial_apply,
        ← Finset.sum_sub_distrib]
      calc
        ∑ other,
            ((if other.exponent = stage.exponent then
                g.stageCoefficient hacute i other else 0) -
              if other.exponent = stage.exponent then
                g.stageCoefficient hacute j other else 0) =
            ((if stage.exponent = stage.exponent then
                g.stageCoefficient hacute i stage else 0) -
              if stage.exponent = stage.exponent then
                g.stageCoefficient hacute j stage else 0) := by
          apply Finset.sum_eq_single stage
          · intro other _ hne
            by_cases hexponent : other.exponent = stage.exponent
            · have hequal : g.stageCoefficient hacute i other =
                  g.stageCoefficient hacute j other := by
                by_contra hother
                exact hne (hisolated other hexponent hother)
              simp [hexponent, hequal]
            · simp [hexponent]
          · simp
        _ = g.stageCoefficient hacute i stage -
            g.stageCoefficient hacute j stage := by simp
    intro hequal
    have hzero : g.globalPuiseuxPolynomial hacute i stage.exponent -
        g.globalPuiseuxPolynomial hacute j stage.exponent = 0 := sub_eq_zero.mpr hequal
    rw [hsum] at hzero
    exact hdiff (sub_eq_zero.mp hzero)
  · intro q hq
    rw [g.globalPuiseuxPolynomial_apply, g.globalPuiseuxPolynomial_apply]
    apply Finset.sum_congr rfl
    intro other _
    by_cases hexponent : other.exponent = q
    · have hequal : g.stageCoefficient hacute i other =
          g.stageCoefficient hacute j other := by
        by_contra hother
        have hle := hhighest other hother
        rw [hexponent] at hle
        exact (not_lt_of_ge hle) hq
      simp [hexponent, hequal]
    · simp [hexponent]

/-- **Global coefficient-realization theorem.**  One explicit family of finite complex Puiseux
polynomials simultaneously realizes every pair in an elementary fission encoding, including after
all coincident rational exponents are collected. -/
theorem fissionEncoding_globalPuiseux_realizes_all_pairs
    {n : ℕ} {g : ElementaryDecoratedGraph n}
    (encoding : ElementaryFissionEncoding g) {i j : Fin n} (hij : i ≠ j) :
    ∃ e : ℚ,
      HasHighestDifferenceExponent
          (g.globalPuiseuxPolynomial encoding.acuteIsosceles i)
          (g.globalPuiseuxPolynomial encoding.acuteIsosceles j) e ∧
        HighestDifferenceRealizesEdge (g.ramification i) (g.ramification j)
          (g.edge i j) e := by
  obtain ⟨stage, hstage, hedge⟩ :=
    g.pairPresentation_hasUncancelledHighestDifferenceStage_indexed
      encoding.acuteIsosceles hij (encoding.pairPresentation i j hij)
  exact ⟨stage.exponent,
    g.uncancelledStage_gives_highestDifferenceExponent encoding.acuteIsosceles hstage,
    g.stageRealizesEdge_gives_highestDifferenceRelation i j stage hedge⟩

/-- Certificate form: every recognized graph has a simultaneous coefficient-level realization. -/
theorem globalPuiseux_realization_of_certificate
    {n : ℕ} (g : ElementaryDecoratedGraph n)
    (certificate : g.HasElementaryRecognitionCertificate) :
    ∃ polynomials : Fin n → (ℚ →₀ ℂ),
      (∀ i, IsElementaryPuiseuxPolynomialOfRamification
          (g.ramification i) (polynomials i)) ∧
        ∀ i j, i ≠ j → ∃ e : ℚ,
          HasHighestDifferenceExponent
              (polynomials i) (polynomials j) e ∧
            HighestDifferenceRealizesEdge (g.ramification i) (g.ramification j)
              (g.edge i j) e := by
  let encoding := g.fissionEncodingOfCertificate certificate
  exact ⟨g.globalPuiseuxPolynomial encoding.acuteIsosceles,
    fun i => g.globalPuiseuxPolynomial_isElementary encoding.acuteIsosceles i,
    fun i j hij => fissionEncoding_globalPuiseux_realizes_all_pairs encoding hij⟩

end ElementaryDecoratedGraph
end
end GaloisForLFunctions.IrregularStokes
