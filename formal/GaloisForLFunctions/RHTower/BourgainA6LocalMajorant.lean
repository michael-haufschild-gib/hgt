/-
# Local off-diagonal majorant for an `A₆` block family

This file sums the uniform separated-pair estimate over every off-diagonal
term produced by the three-color pointwise decomposition.  It is the
off-diagonal half of the one-step linear-to-bilinear recurrence.
-/
import GaloisForLFunctions.RHTower.BourgainA6PairLocalMoment

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Local translated moment of one ordered block pair. -/
def bourgainA6OrderedPairLocalMoment
    (Λ N K M q₀ : ℕ) (i j : Fin K)
    (y : BourgainPhaseSpace) : ENNReal :=
  ∫⁻ x in
    {x : BourgainPhaseSpace |
      ‖x‖ ≤ bourgainA6LocalRadius (1 / Real.sqrt (Λ : ℝ)) M},
    ENNReal.ofReal
      (‖bourgainA6PhysicalBlockSum N M (q₀ + M * i.1)
            (fun _ => 1) (x + y)‖ ^ (6 : ℕ) *
        ‖bourgainA6PhysicalBlockSum N M (q₀ + M * j.1)
            (fun _ => 1) (x + y)‖ ^ (6 : ℕ))

/-- Sum of all weighted off-diagonal local moments appearing in the
three-color majorant. -/
def bourgainA6ThreeColorPairLocalMoment
    (Λ N K M q₀ : ℕ) (y : BourgainPhaseSpace) : ENNReal :=
  ∑ c : Fin 3,
    (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^ (18 : ℕ) *
      ∑ i ∈ bourgainColorBlockFinset K c,
        ∑ j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
          bourgainA6OrderedPairLocalMoment Λ N K M q₀ i j y

/-- Exact finite multiplicity bound for all weighted ordered pairs in the
three color classes. -/
theorem bourgainThreeColorWeightedPairCount_le
    (K : ℕ) (B : ENNReal) :
    (∑ c : Fin 3,
      (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^ (18 : ℕ) *
        ∑ i ∈ bourgainColorBlockFinset K c,
          ∑ _j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
            B) ≤
      (3 : ENNReal) * (K : ENNReal) ^ (20 : ℕ) * B := by
  have hcolor (c : Fin 3) :
      (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ≤
        (K : ENNReal) := by
    have hcard :
        (bourgainColorBlockFinset K c).card ≤ K := by
      simpa using Finset.card_le_univ (bourgainColorBlockFinset K c)
    exact_mod_cast hcard
  have hinner (c : Fin 3) :
      (∑ i ∈ bourgainColorBlockFinset K c,
        ∑ _j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
          B) ≤
        (K : ENNReal) ^ (2 : ℕ) * B := by
    calc
      (∑ i ∈ bourgainColorBlockFinset K c,
        ∑ _j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
          B) ≤
        ∑ _i ∈ bourgainColorBlockFinset K c,
          (K : ENNReal) * B := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.sum_const, nsmul_eq_mul]
            have hcard :
                ((bourgainColorBlockFinset K c).filter
                  (fun j => j ≠ i)).card ≤ K := by
              simpa using Finset.card_le_univ
                ((bourgainColorBlockFinset K c).filter (fun j => j ≠ i))
            gcongr
      _ =
        (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) *
          ((K : ENNReal) * B) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ENNReal) * ((K : ENNReal) * B) := by
        simpa only [mul_comm] using
          (mul_le_mul_right (hcolor c) ((K : ENNReal) * B))
      _ = (K : ENNReal) ^ (2 : ℕ) * B := by ring
  calc
    (∑ c : Fin 3,
      (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^ (18 : ℕ) *
        ∑ i ∈ bourgainColorBlockFinset K c,
          ∑ _j ∈ (bourgainColorBlockFinset K c).filter (fun j => j ≠ i),
            B) ≤
        ∑ _c : Fin 3, (K : ENNReal) ^ (20 : ℕ) * B := by
      apply Finset.sum_le_sum
      intro c hc
      calc
        (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^
              (18 : ℕ) *
            (∑ i ∈ bourgainColorBlockFinset K c,
              ∑ _j ∈ (bourgainColorBlockFinset K c).filter
                  (fun j => j ≠ i), B) ≤
            (K : ENNReal) ^ (18 : ℕ) *
              ((K : ENNReal) ^ (2 : ℕ) * B) := by
          calc
            (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^
                  (18 : ℕ) *
                (∑ i ∈ bourgainColorBlockFinset K c,
                  ∑ _j ∈ (bourgainColorBlockFinset K c).filter
                      (fun j => j ≠ i), B) ≤
              (K : ENNReal) ^ (18 : ℕ) *
                (∑ i ∈ bourgainColorBlockFinset K c,
                  ∑ _j ∈ (bourgainColorBlockFinset K c).filter
                      (fun j => j ≠ i), B) := by
                simpa only [mul_comm] using
                  (mul_le_mul_right
                    (pow_le_pow_left' (hcolor c) 18)
                    (∑ i ∈ bourgainColorBlockFinset K c,
                      ∑ _j ∈ (bourgainColorBlockFinset K c).filter
                        (fun j => j ≠ i), B))
            _ ≤ (K : ENNReal) ^ (18 : ℕ) *
                ((K : ENNReal) ^ (2 : ℕ) * B) :=
              mul_le_mul_right (hinner c) _
        _ = (K : ENNReal) ^ (20 : ℕ) * B := by ring
    _ = (3 : ENNReal) * (K : ENNReal) ^ (20 : ℕ) * B := by
      simp [nsmul_eq_mul]
      ring

/-- Every term of the complete off-diagonal majorant is controlled by the
same clean local power bound. -/
theorem bourgainA6ThreeColorPairLocalMoment_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ Λ : ℕ, 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K M q₀ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₀ : 0 < q₀) → (hinside : q₀ + M * K ≤ N) →
        (hstart : N ≤ Λ * q₀) →
      ∀ y : BourgainPhaseSpace,
      bourgainA6ThreeColorPairLocalMoment Λ N K M q₀ y ≤
        ∑ c : Fin 3,
          (((bourgainColorBlockFinset K c).card : ℕ) : ENNReal) ^
              (18 : ℕ) *
            ∑ i ∈ bourgainColorBlockFinset K c,
              ∑ _j ∈ (bourgainColorBlockFinset K c).filter
                  (fun j => j ≠ i),
                ENNReal.ofReal
                  (C * (N : ℝ) ^ (10 : ℕ) *
                    (M : ℝ) ^ (4 + ε)) := by
  intro Λ hΛ
  obtain ⟨C, hC, hpair⟩ :=
    setLIntegral_bourgainA6ColorPair_localBall_power hε Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y
  unfold bourgainA6ThreeColorPairLocalMoment
  apply Finset.sum_le_sum
  intro c hc
  apply mul_le_mul_right
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact hpair N K M q₀ hN hM hMN hM2N hq₀ hinside hstart hi hj y

/-- Simplified fixed-`K` multiplicity form of the complete local
off-diagonal estimate. -/
theorem bourgainA6ThreeColorPairLocalMoment_power
    {ε : ℝ} (hε : 0 < ε) :
    ∀ Λ : ℕ, 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K M q₀ : ℕ), (hN : 0 < N) → (hM : 0 < M) →
        (hMN : M ≤ N) → (hM2N : M ^ (2 : ℕ) ≤ N) →
        (hq₀ : 0 < q₀) → (hinside : q₀ + M * K ≤ N) →
        (hstart : N ≤ Λ * q₀) →
      ∀ y : BourgainPhaseSpace,
      bourgainA6ThreeColorPairLocalMoment Λ N K M q₀ y ≤
        (3 : ENNReal) * (K : ENNReal) ^ (20 : ℕ) *
          ENNReal.ofReal
            (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε)) := by
  intro Λ hΛ
  obtain ⟨C, hC, hsum⟩ :=
    bourgainA6ThreeColorPairLocalMoment_le hε Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y
  exact (hsum N K M q₀ hN hM hMN hM2N hq₀ hinside hstart y).trans
    (bourgainThreeColorWeightedPairCount_le K
      (ENNReal.ofReal
        (C * (N : ℝ) ^ (10 : ℕ) * (M : ℝ) ^ (4 + ε))))

end

end RHTower
