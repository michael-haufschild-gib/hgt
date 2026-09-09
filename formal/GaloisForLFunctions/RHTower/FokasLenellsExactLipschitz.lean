import GaloisForLFunctions.RHTower.FokasLenellsOperatorPhaseGenerators
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Optimal global Lipschitz constants for actual scattering operators

Strong vector derivatives suffice for the exact global operator Lipschitz
constant whenever the derivative's operator norm is conserved. This applies
to the scalar multipliers, full jump, Cauchy compression, mixed generators,
and the time generators of the actual odd initial part.
-/

open MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem strong_operator_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    (T D : ℝ → E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K)
    (hd : ∀ t u, HasDerivAt (fun s => T s u) (D t u) t)
    (hn : ∀ t, ‖D t‖ = K) (s t : ℝ) :
    ‖T s - T t‖ ≤ K * ‖s-t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg _))
  intro u
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun s => T s u) (f' := fun s => D s u)
    (C := K * ‖u‖)
    (fun s _ => (hd s u).hasDerivWithinAt)
    (fun s _ => by rw [← hn s]; exact (D s).le_opNorm u)
    convex_univ (Set.mem_univ t) (Set.mem_univ s)
  change ‖T s u - T t u‖ ≤ _
  calc
    _ ≤ (K * ‖u‖) * ‖s-t‖ := h
    _ = _ := by ring

private theorem strong_operator_lipschitz_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    (T D : ℝ → E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K)
    (hd : ∀ t u, HasDerivAt (fun s => T s u) (D t u) t)
    (hn : ∀ t, ‖D t‖ = K) (L : ℝ) :
    (∀ s t, ‖T s - T t‖ ≤ L * ‖s-t‖) ↔ K ≤ L := by
  constructor
  · intro h
    have hL : 0 ≤ L := by
      have h10 := (norm_nonneg (T 1 - T 0)).trans (h 1 0)
      simpa using h10
    rw [← hn 0]
    apply ContinuousLinearMap.opNorm_le_bound _ hL
    intro u
    have hv : ∀ᶠ s in 𝓝 (0 : ℝ),
        ‖T s u - T 0 u‖ ≤ (L * ‖u‖) * ‖s-0‖ := by
      apply Eventually.of_forall
      intro s
      calc
        _ ≤ ‖T s - T 0‖ * ‖u‖ := (T s - T 0).le_opNorm u
        _ ≤ (L * ‖s-0‖) * ‖u‖ := mul_le_mul_of_nonneg_right (h s 0) (norm_nonneg _)
        _ = _ := by ring
    have hb := norm_deriv_le_of_lip' (mul_nonneg hL (norm_nonneg u)) hv
    rw [(hd 0 u).deriv] at hb
    exact hb
  · intro h s t
    exact (strong_operator_norm_sub_le T D K hK hd hn s t).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))

/-- The least global time Lipschitz constant for the actual directMultiplier is the initial generator norm. -/
theorem directMultiplier_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) (L : ℝ) :
    (∀ s v, ‖directMultiplier q s x reverse - directMultiplier q v x reverse‖ ≤ L * ‖s-v‖) ↔
      ‖directTimeMultiplier q 0 0 reverse‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directMultiplier q s x reverse) (fun s => directTimeMultiplier q s x reverse)
    ‖directTimeMultiplier q 0 0 reverse‖ (norm_nonneg _)
    (fun s u => directMultiplier_time_hasDerivAt q s x reverse u)
    (fun s => norm_directTimeMultiplier_time_space_invariant q s x reverse) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directMultiplier_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) (s v : ℝ) :
    ‖directMultiplier q s x reverse - directMultiplier q v x reverse‖ ≤ ‖directTimeMultiplier q 0 0 reverse‖ * ‖s-v‖ :=
  (directMultiplier_time_lipschitz_iff q x reverse ‖directTimeMultiplier q 0 0 reverse‖).2 le_rfl s v

/-- The least global space Lipschitz constant for the actual directMultiplier is the initial generator norm. -/
theorem directMultiplier_space_lipschitz_iff (q : SchwartzMap ℝ ℂ) (t : ℝ) (reverse : Bool) (L : ℝ) :
    (∀ s v, ‖directMultiplier q t s reverse - directMultiplier q t v reverse‖ ≤ L * ‖s-v‖) ↔
      ‖directSpaceMultiplier q 0 0 reverse‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directMultiplier q t s reverse) (fun s => directSpaceMultiplier q t s reverse)
    ‖directSpaceMultiplier q 0 0 reverse‖ (norm_nonneg _)
    (fun s u => directMultiplier_space_hasDerivAt q t s reverse u)
    (fun s => norm_directSpaceMultiplier_time_space_invariant q t s reverse) L

/-- The corresponding optimal global space estimate holds for every pair of parameters. -/
theorem norm_directMultiplier_space_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (t : ℝ) (reverse : Bool) (s v : ℝ) :
    ‖directMultiplier q t s reverse - directMultiplier q t v reverse‖ ≤ ‖directSpaceMultiplier q 0 0 reverse‖ * ‖s-v‖ :=
  (directMultiplier_space_lipschitz_iff q t reverse ‖directSpaceMultiplier q 0 0 reverse‖).2 le_rfl s v

/-- The least global space Lipschitz constant for the actual directTimeMultiplier is the initial generator norm. -/
theorem directTimeMultiplier_space_lipschitz_iff (q : SchwartzMap ℝ ℂ) (t : ℝ) (reverse : Bool) (L : ℝ) :
    (∀ s v, ‖directTimeMultiplier q t s reverse - directTimeMultiplier q t v reverse‖ ≤ L * ‖s-v‖) ↔
      ‖directMultiplier q 0 0 reverse‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directTimeMultiplier q t s reverse) (fun s => directMultiplier q t s reverse)
    ‖directMultiplier q 0 0 reverse‖ (norm_nonneg _)
    (fun s u => directTimeMultiplier_space_hasDerivAt q t s reverse u)
    (fun s => norm_directMultiplier_time_space_invariant q t s reverse) L

/-- The corresponding optimal global space estimate holds for every pair of parameters. -/
theorem norm_directTimeMultiplier_space_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (t : ℝ) (reverse : Bool) (s v : ℝ) :
    ‖directTimeMultiplier q t s reverse - directTimeMultiplier q t v reverse‖ ≤ ‖directMultiplier q 0 0 reverse‖ * ‖s-v‖ :=
  (directTimeMultiplier_space_lipschitz_iff q t reverse ‖directMultiplier q 0 0 reverse‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directSpaceMultiplier is the initial generator norm. -/
theorem directSpaceMultiplier_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) (L : ℝ) :
    (∀ s v, ‖directSpaceMultiplier q s x reverse - directSpaceMultiplier q v x reverse‖ ≤ L * ‖s-v‖) ↔
      ‖directMultiplier q 0 0 reverse‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directSpaceMultiplier q s x reverse) (fun s => directMultiplier q s x reverse)
    ‖directMultiplier q 0 0 reverse‖ (norm_nonneg _)
    (fun s u => directSpaceMultiplier_time_hasDerivAt q s x reverse u)
    (fun s => norm_directMultiplier_time_space_invariant q s x reverse) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directSpaceMultiplier_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) (s v : ℝ) :
    ‖directSpaceMultiplier q s x reverse - directSpaceMultiplier q v x reverse‖ ≤ ‖directMultiplier q 0 0 reverse‖ * ‖s-v‖ :=
  (directSpaceMultiplier_time_lipschitz_iff q x reverse ‖directMultiplier q 0 0 reverse‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directTimeMultiplier of the odd initial part is the initial generator norm. -/
theorem directTimeMultiplier_oddInitialPart_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) (L : ℝ) :
    (∀ s v, ‖directTimeMultiplier (oddInitialPart q) s x reverse - directTimeMultiplier (oddInitialPart q) v x reverse‖ ≤ L * ‖s-v‖) ↔
      ‖compatibleSecondTimeMultiplier q 0 0 reverse‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directTimeMultiplier (oddInitialPart q) s x reverse) (fun s => compatibleSecondTimeMultiplier q s x reverse)
    ‖compatibleSecondTimeMultiplier q 0 0 reverse‖ (norm_nonneg _)
    (fun s u => directTimeMultiplier_oddInitialPart_hasDerivAt q s x reverse u)
    (fun s => norm_compatibleSecondTimeMultiplier_time_space_invariant q s x reverse) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directTimeMultiplier_oddInitialPart_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) (s v : ℝ) :
    ‖directTimeMultiplier (oddInitialPart q) s x reverse - directTimeMultiplier (oddInitialPart q) v x reverse‖ ≤ ‖compatibleSecondTimeMultiplier q 0 0 reverse‖ * ‖s-v‖ :=
  (directTimeMultiplier_oddInitialPart_time_lipschitz_iff q x reverse ‖compatibleSecondTimeMultiplier q 0 0 reverse‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directJumpPerturbation is the initial generator norm. -/
theorem directJumpPerturbation_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (L : ℝ) :
    (∀ s v, ‖directJumpPerturbation q s x - directJumpPerturbation q v x‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpTimeOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directJumpPerturbation q s x) (fun s => directJumpTimeOperator q s x)
    ‖directJumpTimeOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directJumpPerturbation_time_hasDerivAt q s x u)
    (fun s => norm_directJumpTimeOperator_time_space_invariant q s x) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directJumpPerturbation_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (s v : ℝ) :
    ‖directJumpPerturbation q s x - directJumpPerturbation q v x‖ ≤ ‖directJumpTimeOperator q 0 0‖ * ‖s-v‖ :=
  (directJumpPerturbation_time_lipschitz_iff q x ‖directJumpTimeOperator q 0 0‖).2 le_rfl s v

/-- The least global space Lipschitz constant for the actual directJumpPerturbation is the initial generator norm. -/
theorem directJumpPerturbation_space_lipschitz_iff (q : SchwartzMap ℝ ℂ) (t : ℝ) (L : ℝ) :
    (∀ s v, ‖directJumpPerturbation q t s - directJumpPerturbation q t v‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpSpaceOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directJumpPerturbation q t s) (fun s => directJumpSpaceOperator q t s)
    ‖directJumpSpaceOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directJumpPerturbation_space_hasDerivAt q t s u)
    (fun s => norm_directJumpSpaceOperator_time_space_invariant q t s) L

/-- The corresponding optimal global space estimate holds for every pair of parameters. -/
theorem norm_directJumpPerturbation_space_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (t : ℝ) (s v : ℝ) :
    ‖directJumpPerturbation q t s - directJumpPerturbation q t v‖ ≤ ‖directJumpSpaceOperator q 0 0‖ * ‖s-v‖ :=
  (directJumpPerturbation_space_lipschitz_iff q t ‖directJumpSpaceOperator q 0 0‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directCauchyOperator is the initial generator norm. -/
theorem directCauchyOperator_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (L : ℝ) :
    (∀ s v, ‖directCauchyOperator q s x - directCauchyOperator q v x‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpTimeOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directCauchyOperator q s x) (fun s => directCauchyTimeOperator q s x)
    ‖directJumpTimeOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directCauchyOperator_time_hasDerivAt q s x u)
    (fun s => norm_directCauchyTimeOperator_time_space_invariant q s x) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directCauchyOperator_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (s v : ℝ) :
    ‖directCauchyOperator q s x - directCauchyOperator q v x‖ ≤ ‖directJumpTimeOperator q 0 0‖ * ‖s-v‖ :=
  (directCauchyOperator_time_lipschitz_iff q x ‖directJumpTimeOperator q 0 0‖).2 le_rfl s v

/-- The least global space Lipschitz constant for the actual directCauchyOperator is the initial generator norm. -/
theorem directCauchyOperator_space_lipschitz_iff (q : SchwartzMap ℝ ℂ) (t : ℝ) (L : ℝ) :
    (∀ s v, ‖directCauchyOperator q t s - directCauchyOperator q t v‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpSpaceOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directCauchyOperator q t s) (fun s => directCauchySpaceOperator q t s)
    ‖directJumpSpaceOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directCauchyOperator_space_hasDerivAt q t s u)
    (fun s => norm_directCauchySpaceOperator_time_space_invariant q t s) L

/-- The corresponding optimal global space estimate holds for every pair of parameters. -/
theorem norm_directCauchyOperator_space_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (t : ℝ) (s v : ℝ) :
    ‖directCauchyOperator q t s - directCauchyOperator q t v‖ ≤ ‖directJumpSpaceOperator q 0 0‖ * ‖s-v‖ :=
  (directCauchyOperator_space_lipschitz_iff q t ‖directJumpSpaceOperator q 0 0‖).2 le_rfl s v

/-- The least global space Lipschitz constant for the actual directJumpTimeOperator is the initial generator norm. -/
theorem directJumpTimeOperator_space_lipschitz_iff (q : SchwartzMap ℝ ℂ) (t : ℝ) (L : ℝ) :
    (∀ s v, ‖directJumpTimeOperator q t s - directJumpTimeOperator q t v‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpMixedOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directJumpTimeOperator q t s) (fun s => directJumpMixedOperator q t s)
    ‖directJumpMixedOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directJumpTimeOperator_space_hasDerivAt q t s u)
    (fun s => norm_directJumpMixedOperator_time_space_invariant q t s) L

/-- The corresponding optimal global space estimate holds for every pair of parameters. -/
theorem norm_directJumpTimeOperator_space_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (t : ℝ) (s v : ℝ) :
    ‖directJumpTimeOperator q t s - directJumpTimeOperator q t v‖ ≤ ‖directJumpMixedOperator q 0 0‖ * ‖s-v‖ :=
  (directJumpTimeOperator_space_lipschitz_iff q t ‖directJumpMixedOperator q 0 0‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directJumpSpaceOperator is the initial generator norm. -/
theorem directJumpSpaceOperator_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (L : ℝ) :
    (∀ s v, ‖directJumpSpaceOperator q s x - directJumpSpaceOperator q v x‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpMixedOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directJumpSpaceOperator q s x) (fun s => directJumpMixedOperator q s x)
    ‖directJumpMixedOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directJumpSpaceOperator_time_hasDerivAt q s x u)
    (fun s => norm_directJumpMixedOperator_time_space_invariant q s x) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directJumpSpaceOperator_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (s v : ℝ) :
    ‖directJumpSpaceOperator q s x - directJumpSpaceOperator q v x‖ ≤ ‖directJumpMixedOperator q 0 0‖ * ‖s-v‖ :=
  (directJumpSpaceOperator_time_lipschitz_iff q x ‖directJumpMixedOperator q 0 0‖).2 le_rfl s v

/-- The least global space Lipschitz constant for the actual directCauchyTimeOperator is the initial generator norm. -/
theorem directCauchyTimeOperator_space_lipschitz_iff (q : SchwartzMap ℝ ℂ) (t : ℝ) (L : ℝ) :
    (∀ s v, ‖directCauchyTimeOperator q t s - directCauchyTimeOperator q t v‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpMixedOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directCauchyTimeOperator q t s) (fun s => directCauchyMixedOperator q t s)
    ‖directJumpMixedOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directCauchyTimeOperator_space_hasDerivAt q t s u)
    (fun s => norm_directCauchyMixedOperator_time_space_invariant q t s) L

/-- The corresponding optimal global space estimate holds for every pair of parameters. -/
theorem norm_directCauchyTimeOperator_space_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (t : ℝ) (s v : ℝ) :
    ‖directCauchyTimeOperator q t s - directCauchyTimeOperator q t v‖ ≤ ‖directJumpMixedOperator q 0 0‖ * ‖s-v‖ :=
  (directCauchyTimeOperator_space_lipschitz_iff q t ‖directJumpMixedOperator q 0 0‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directCauchySpaceOperator is the initial generator norm. -/
theorem directCauchySpaceOperator_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (L : ℝ) :
    (∀ s v, ‖directCauchySpaceOperator q s x - directCauchySpaceOperator q v x‖ ≤ L * ‖s-v‖) ↔
      ‖directJumpMixedOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directCauchySpaceOperator q s x) (fun s => directCauchyMixedOperator q s x)
    ‖directJumpMixedOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directCauchySpaceOperator_time_hasDerivAt q s x u)
    (fun s => norm_directCauchyMixedOperator_time_space_invariant q s x) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directCauchySpaceOperator_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (s v : ℝ) :
    ‖directCauchySpaceOperator q s x - directCauchySpaceOperator q v x‖ ≤ ‖directJumpMixedOperator q 0 0‖ * ‖s-v‖ :=
  (directCauchySpaceOperator_time_lipschitz_iff q x ‖directJumpMixedOperator q 0 0‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directJumpTimeOperator of the odd initial part is the initial generator norm. -/
theorem directJumpTimeOperator_oddInitialPart_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (L : ℝ) :
    (∀ s v, ‖directJumpTimeOperator (oddInitialPart q) s x - directJumpTimeOperator (oddInitialPart q) v x‖ ≤ L * ‖s-v‖) ↔
      ‖compatibleJumpSecondTimeOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directJumpTimeOperator (oddInitialPart q) s x) (fun s => compatibleJumpSecondTimeOperator q s x)
    ‖compatibleJumpSecondTimeOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directJumpTimeOperator_oddInitialPart_hasDerivAt q s x u)
    (fun s => norm_compatibleJumpSecondTimeOperator_time_space_invariant q s x) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directJumpTimeOperator_oddInitialPart_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (s v : ℝ) :
    ‖directJumpTimeOperator (oddInitialPart q) s x - directJumpTimeOperator (oddInitialPart q) v x‖ ≤ ‖compatibleJumpSecondTimeOperator q 0 0‖ * ‖s-v‖ :=
  (directJumpTimeOperator_oddInitialPart_time_lipschitz_iff q x ‖compatibleJumpSecondTimeOperator q 0 0‖).2 le_rfl s v

/-- The least global time Lipschitz constant for the actual directCauchyTimeOperator of the odd initial part is the initial generator norm. -/
theorem directCauchyTimeOperator_oddInitialPart_time_lipschitz_iff (q : SchwartzMap ℝ ℂ) (x : ℝ) (L : ℝ) :
    (∀ s v, ‖directCauchyTimeOperator (oddInitialPart q) s x - directCauchyTimeOperator (oddInitialPart q) v x‖ ≤ L * ‖s-v‖) ↔
      ‖compatibleJumpSecondTimeOperator q 0 0‖ ≤ L :=
  strong_operator_lipschitz_iff (fun s => directCauchyTimeOperator (oddInitialPart q) s x) (fun s => compatibleCauchySecondTimeOperator q s x)
    ‖compatibleJumpSecondTimeOperator q 0 0‖ (norm_nonneg _)
    (fun s u => directCauchyTimeOperator_oddInitialPart_hasDerivAt q s x u)
    (fun s => norm_compatibleCauchySecondTimeOperator_time_space_invariant q s x) L

/-- The corresponding optimal global time estimate holds for every pair of parameters. -/
theorem norm_directCauchyTimeOperator_oddInitialPart_time_sub_le_initial_generator (q : SchwartzMap ℝ ℂ) (x : ℝ) (s v : ℝ) :
    ‖directCauchyTimeOperator (oddInitialPart q) s x - directCauchyTimeOperator (oddInitialPart q) v x‖ ≤ ‖compatibleJumpSecondTimeOperator q 0 0‖ * ‖s-v‖ :=
  (directCauchyTimeOperator_oddInitialPart_time_lipschitz_iff q x ‖compatibleJumpSecondTimeOperator q 0 0‖).2 le_rfl s v

end
end RHTower.FokasLenells
