/-
# Diagonal form of the local `A₆` recurrence

This file removes the modulo-three bookkeeping from the diagonal term and
identifies a `K`-block family with one consecutive block of length `K*M`.
The resulting theorem is the literal scale recurrence needed for iteration.
-/
import GaloisForLFunctions.RHTower.BourgainA6LocalRecurrence

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The modulo-three color fibers partition an `ENNReal`-valued sum. -/
theorem sum_bourgainColorBlockFinset_ennreal
    {K : ℕ} (z : Fin K → ENNReal) :
    (∑ c : Fin 3, ∑ i ∈ bourgainColorBlockFinset K c, z i) =
      ∑ i : Fin K, z i := by
  exact Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin K)))
    (t := (Finset.univ : Finset (Fin 3)))
    (g := bourgainBlockColor)
    (fun i hi => Finset.mem_univ _)
    z

/-- Exact diagonal simplification: every block occurs in exactly one color
class. -/
theorem bourgainA6ThreeColorDiagonalLocalMoment_eq
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) :
    bourgainA6ThreeColorDiagonalLocalMoment Λ N K M q₀ y =
      (2 : ENNReal) ^ (12 : ℕ) *
        ∑ i : Fin K,
          bourgainA6SingleBlockLocalMoment Λ N K M q₀ i y := by
  unfold bourgainA6ThreeColorDiagonalLocalMoment
  rw [← Finset.mul_sum]
  rw [sum_bourgainColorBlockFinset_ennreal]

/-- A consecutive block of length `K*M` is exactly its `K` consecutive
subblocks of length `M`, at arbitrary denominator and start. -/
theorem bourgainA6PhysicalBlockSum_mul_eq_blockFamilySum
    (N K M q₀ : ℕ) (x : BourgainPhaseSpace) :
    bourgainA6PhysicalBlockSum N (K * M) q₀ (fun _ => 1) x =
      bourgainA6BlockFamilySum N K M q₀ x := by
  unfold bourgainA6PhysicalBlockSum bourgainA6BlockFamilySum
  rw [← (finProdFinEquiv : Fin K × Fin M ≃ Fin (K * M)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro i
  apply Fintype.sum_congr
  intro m
  rw [one_mul, one_mul]
  congr 2
  congr 1
  unfold bourgainIndex
  norm_cast
  rw [finProdFinEquiv_apply_val]
  simp only
  omega

/-- Local translated twelfth moment of one arbitrary consecutive physical
block. -/
def bourgainA6PhysicalBlockLocalMoment
    (Λ N L q : ℕ) (y : BourgainPhaseSpace) : ENNReal :=
  ∫⁻ x in
    {x : BourgainPhaseSpace |
      ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) L},
    ENNReal.ofReal
      (‖bourgainA6PhysicalBlockSum N L q (fun _ => 1) (x + y)‖ ^
        (12 : ℕ))

/-- A single family member is its literal length-`M` physical block
moment. -/
theorem bourgainA6SingleBlockLocalMoment_eq
    (Λ N K M q₀ : ℕ) (i : Fin K) (y : BourgainPhaseSpace) :
    bourgainA6SingleBlockLocalMoment Λ N K M q₀ i y =
      bourgainA6PhysicalBlockLocalMoment
        Λ N M (q₀ + M * i.1) y := by
  rfl

/-- A `K`-block family moment uses radius determined by the subblock scale
`M`; its integrand is exactly one length-`K*M` physical block. -/
theorem bourgainA6BlockFamilyLocalMoment_eq_setLIntegral_physicalBlock
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) :
    bourgainA6BlockFamilyLocalMoment Λ N K M q₀ y =
      ∫⁻ x in
        {x : BourgainPhaseSpace |
          ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
        ENNReal.ofReal
          (‖bourgainA6PhysicalBlockSum N (K * M) q₀
              (fun _ => 1) (x + y)‖ ^ (12 : ℕ)) := by
  unfold bourgainA6BlockFamilyLocalMoment
  apply setLIntegral_congr_fun measurableSet_le
  intro x hx
  rw [bourgainA6PhysicalBlockSum_mul_eq_blockFamilySum]

/-- Literal scale-recursion interface after removing all color
bookkeeping. -/
theorem bourgainA6BlockFamilyLocalMoment_le_block_diagonal_add_power
    {ε : ℝ} (hε : 0 < ε) :
    ∀ Λ : ℕ, 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K M q₀ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₀ : 0 < q₀) → (hinside : q₀ + M * K ≤ N) →
        (hstart : N ≤ Λ * q₀) →
      ∀ y : BourgainPhaseSpace,
      bourgainA6BlockFamilyLocalMoment Λ N K M q₀ y ≤
        (3 : ENNReal) ^ (11 : ℕ) *
          ((2 : ENNReal) ^ (12 : ℕ) *
              ∑ i : Fin K,
                bourgainA6PhysicalBlockLocalMoment
                  Λ N M (q₀ + M * i.1) y +
            (3 : ENNReal) * (K : ENNReal) ^ (20 : ℕ) *
              ENNReal.ofReal
                (C * (N : ℝ) ^ (10 : ℕ) *
                  (M : ℝ) ^ (4 + ε))) := by
  intro Λ hΛ
  obtain ⟨C, hC, hrec⟩ :=
    bourgainA6BlockFamilyLocalMoment_le_diagonal_add_power hε Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y
  simpa only [bourgainA6ThreeColorDiagonalLocalMoment_eq,
    bourgainA6SingleBlockLocalMoment_eq] using
    hrec N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y

end

end RHTower
