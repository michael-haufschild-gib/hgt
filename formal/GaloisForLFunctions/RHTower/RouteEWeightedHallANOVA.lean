import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport

/-!
# Route E weighted-Hall ANOVA algebra

This module formalizes the finite algebraic faces of the weighted-Hall ANOVA law: physical
normalization, collision expansion, sharp one- and two-sided capacity rates, and exact partition
seam decomposition.  The relation-polytope projection and weighted-Hall duality live in the
companion module.
-/

namespace RHTower

open scoped BigOperators

/-- Positive source and target probability laws. -/
structure RouteEHallANOVAData (S T : Type*) [Fintype S] [Fintype T] where
  sourceLaw : S → ℝ
  targetLaw : T → ℝ
  source_pos : ∀ s, 0 < sourceLaw s
  target_pos : ∀ t, 0 < targetLaw t
  source_sum : ∑ s, sourceLaw s = 1
  target_sum : ∑ t, targetLaw t = 1

/-- A row-stochastic kernel.  Relation support is imposed in the projection companion. -/
structure RouteERowKernel (S T : Type*) [Fintype S] [Fintype T] where
  transition : S → T → ℝ
  transition_nonneg : ∀ s t, 0 ≤ transition s t
  row_sum : ∀ s, ∑ t, transition s t = 1

namespace RouteEHallANOVAData

variable {S T : Type*} [Fintype S] [Fintype T]

/-- Output target marginal of a source law passed through a row kernel. -/
def output (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (t : T) : ℝ :=
  ∑ s, D.sourceLaw s * K.transition s t

/-- Relative target-column density. -/
noncomputable def density (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (t : T) : ℝ :=
  D.output K t / D.targetLaw t

/-- Normalized physical column chi-square. -/
noncomputable def chiSquare (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) : ℝ :=
  ∑ t, D.targetLaw t * (D.density K t - 1) ^ 2

/-- Physical centered column energy for source mass `A` and target mass `B`. -/
noncomputable def physicalCenteredEnergy
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (A B : ℝ) : ℝ :=
  ∑ t,
    (A * D.output K t - (A / B) * (B * D.targetLaw t)) ^ 2 /
      (B * D.targetLaw t)

/-- Normalized two-row collision kernel. -/
noncomputable def collision
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (s s' : S) : ℝ :=
  ∑ t, K.transition s t * K.transition s' t / D.targetLaw t

theorem output_nonneg (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (t : T) :
    0 ≤ D.output K t :=
  Finset.sum_nonneg fun s _hs =>
    mul_nonneg (D.source_pos s).le (K.transition_nonneg s t)

theorem output_sum (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) :
    ∑ t, D.output K t = 1 := by
  classical
  simp_rw [output]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, K.row_sum, mul_one]
  exact D.source_sum

theorem density_nonneg (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (t : T) :
    0 ≤ D.density K t :=
  div_nonneg (D.output_nonneg K t) (D.target_pos t).le

theorem target_mul_density
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) (t : T) :
    D.targetLaw t * D.density K t = D.output K t := by
  rw [density, mul_div_cancel₀ _ (ne_of_gt (D.target_pos t))]

theorem mean_density (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) :
    ∑ t, D.targetLaw t * D.density K t = 1 := by
  simpa only [D.target_mul_density K] using D.output_sum K

/-- Exact finite physical normalization, equation (4) of the paper. -/
theorem physicalCenteredEnergy_eq
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (A B : ℝ) (hB : B ≠ 0) :
    D.physicalCenteredEnergy K A B = (A ^ 2 / B) * D.chiSquare K := by
  classical
  unfold physicalCenteredEnergy chiSquare density
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  have hβ : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
  field_simp

theorem chiSquare_eq_secondMoment_sub_one
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) :
    D.chiSquare K = ∑ t, D.targetLaw t * (D.density K t) ^ 2 - 1 := by
  classical
  unfold chiSquare
  calc
    (∑ t, D.targetLaw t * (D.density K t - 1) ^ 2) =
        ∑ t, (D.targetLaw t * (D.density K t) ^ 2 -
          2 * (D.targetLaw t * D.density K t) + D.targetLaw t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ = (∑ t, D.targetLaw t * (D.density K t) ^ 2) -
        2 * (∑ t, D.targetLaw t * D.density K t) + ∑ t, D.targetLaw t := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by rw [D.mean_density K, D.target_sum]; ring

private theorem output_square_expansion
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) :
    (∑ t, (D.output K t) ^ 2 / D.targetLaw t) =
      ∑ s, ∑ s', D.sourceLaw s * D.sourceLaw s' * D.collision K s s' := by
  classical
  calc
    (∑ t, (D.output K t) ^ 2 / D.targetLaw t) =
        ∑ t, ∑ s, ∑ s',
          (D.sourceLaw s * K.transition s t) *
            (D.sourceLaw s' * K.transition s' t) / D.targetLaw t := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [output, sq, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum, Finset.sum_div]
    _ = ∑ s, ∑ t, ∑ s',
          (D.sourceLaw s * K.transition s t) *
            (D.sourceLaw s' * K.transition s' t) / D.targetLaw t := Finset.sum_comm
    _ = ∑ s, ∑ s', ∑ t,
          (D.sourceLaw s * K.transition s t) *
            (D.sourceLaw s' * K.transition s' t) / D.targetLaw t := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.sum_comm]
    _ = _ := by
      unfold collision
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro s' _hs'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring

/-- Exact collision defect, equation (26) of the paper. -/
theorem chiSquare_eq_collisionDefect
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T) :
    D.chiSquare K =
      (∑ s, ∑ s', D.sourceLaw s * D.sourceLaw s' * D.collision K s s') - 1 := by
  rw [D.chiSquare_eq_secondMoment_sub_one]
  congr 1
  calc
    (∑ t, D.targetLaw t * (D.density K t) ^ 2) =
        ∑ t, (D.output K t) ^ 2 / D.targetLaw t := by
      apply Finset.sum_congr rfl
      intro t _ht
      have hβ : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
      rw [density]
      field_simp
    _ = _ := output_square_expansion D K

/-- Sharp one-sided capacity rate: `0 ≤ r ≤ 1+ε` gives chi-square at most `ε`. -/
theorem chiSquare_le_oneSided
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (ε : ℝ) (_hε : 0 ≤ ε) (hcap : ∀ t, D.density K t ≤ 1 + ε) :
    D.chiSquare K ≤ ε := by
  rw [D.chiSquare_eq_secondMoment_sub_one]
  have hsecond :
      (∑ t, D.targetLaw t * (D.density K t) ^ 2) ≤ 1 + ε := by
    calc
      (∑ t, D.targetLaw t * (D.density K t) ^ 2) ≤
          ∑ t, D.targetLaw t * ((1 + ε) * D.density K t) := by
        apply Finset.sum_le_sum
        intro t _ht
        apply mul_le_mul_of_nonneg_left _ (D.target_pos t).le
        have hr := D.density_nonneg K t
        nlinarith [mul_nonneg hr (sub_nonneg.mpr (hcap t))]
      _ = (1 + ε) * ∑ t, D.targetLaw t * D.density K t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      _ = 1 + ε := by rw [D.mean_density K]; ring
  linarith

/-- Two-sided relative load error `ε` gives the square rate `ε²`. -/
theorem chiSquare_le_twoSided
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (ε : ℝ) (herror : ∀ t, |D.density K t - 1| ≤ ε) :
    D.chiSquare K ≤ ε ^ 2 := by
  unfold chiSquare
  calc
    (∑ t, D.targetLaw t * (D.density K t - 1) ^ 2) ≤
        ∑ t, D.targetLaw t * ε ^ 2 := by
      apply Finset.sum_le_sum
      intro t _ht
      apply mul_le_mul_of_nonneg_left _ (D.target_pos t).le
      have hε : 0 ≤ ε := le_trans (abs_nonneg _) (herror t)
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (D.density K t - 1)) hε).2 (herror t)
    _ = ε ^ 2 := by simp [← Finset.sum_mul, D.target_sum]

/-- Symbolic two-atom witness proving the one-sided rate is exactly sharp. -/
theorem oneSided_rate_sharp (ε : ℝ) (hε : 0 < ε) :
    let β : Fin 2 → ℝ := fun i => if i = 0 then 1 / (1 + ε) else ε / (1 + ε)
    let r : Fin 2 → ℝ := fun i => if i = 0 then 1 + ε else 0
    (∀ i, 0 < β i) ∧
      (∀ i, 0 ≤ r i ∧ r i ≤ 1 + ε) ∧
      (∑ i, β i = 1) ∧
      (∑ i, β i * r i = 1) ∧
      (∑ i, β i * (r i - 1) ^ 2 = ε) := by
  dsimp
  have hden : 0 < 1 + ε := by linarith
  constructor
  · intro i
    fin_cases i <;> simp [hε, hden]
  constructor
  · intro i
    fin_cases i <;> simp [hden.le]
  constructor
  · simp
    field_simp
  constructor
  · simp
    field_simp
  · simp
    field_simp
    ring

/-- Target partition used by the exact marker/seam ANOVA. -/
structure Partition (D : RouteEHallANOVAData S T) (J : Type*) [Fintype J] [DecidableEq J] where
  sector : T → J
  sectorWeight_pos : ∀ j, 0 < ∑ t with sector t = j, D.targetLaw t

namespace Partition

variable {J : Type*} [Fintype J] [DecidableEq J]

def targetSectorWeight
    (D : RouteEHallANOVAData S T) (P : D.Partition J) (j : J) : ℝ :=
  ∑ t with P.sector t = j, D.targetLaw t

def outputSectorWeight
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (P : D.Partition J) (j : J) : ℝ :=
  ∑ t with P.sector t = j, D.output K t

noncomputable def sectorDensity
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (P : D.Partition J) (j : J) : ℝ :=
  P.outputSectorWeight D K j / P.targetSectorWeight D j

theorem sector_centered_sum_eq_zero
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (P : D.Partition J) (j : J) :
    ∑ t with P.sector t = j,
        D.targetLaw t * (D.density K t - P.sectorDensity D K j) = 0 := by
  classical
  have hβj : P.targetSectorWeight D j ≠ 0 :=
    ne_of_gt (P.sectorWeight_pos j)
  simp_rw [mul_sub, Finset.sum_sub_distrib, D.target_mul_density K]
  unfold sectorDensity outputSectorWeight targetSectorWeight
  rw [← Finset.sum_mul]
  simp [hβj]

/-- Exact total-variance partition law, retaining every marker or moving-seam mean. -/
theorem chiSquare_eq_within_add_between
    (D : RouteEHallANOVAData S T) (K : RouteERowKernel S T)
    (P : D.Partition J) :
    D.chiSquare K =
      (∑ j, ∑ t with P.sector t = j,
        D.targetLaw t * (D.density K t - P.sectorDensity D K j) ^ 2) +
      ∑ j, P.targetSectorWeight D j * (P.sectorDensity D K j - 1) ^ 2 := by
  classical
  unfold chiSquare
  rw [← Finset.sum_fiberwise (Finset.univ : Finset T) P.sector
    (fun t => D.targetLaw t * (D.density K t - 1) ^ 2)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  have hcenter := P.sector_centered_sum_eq_zero D K j
  rw [← Finset.sum_add_distrib]
  calc
    (∑ t ∈ Finset.univ with P.sector t = j,
        D.targetLaw t * (D.density K t - 1) ^ 2) =
        ∑ t with P.sector t = j,
          D.targetLaw t * (D.density K t - 1) ^ 2 := by simp
    _ = (∑ t with P.sector t = j,
          D.targetLaw t * (D.density K t - P.sectorDensity D K j) ^ 2) +
        P.targetSectorWeight D j * (P.sectorDensity D K j - 1) ^ 2 := by
      unfold targetSectorWeight
      rw [← Finset.sum_mul]
      calc
        (∑ t with P.sector t = j,
            D.targetLaw t * (D.density K t - 1) ^ 2) =
            (∑ t with P.sector t = j,
              D.targetLaw t * (D.density K t - P.sectorDensity D K j) ^ 2) +
            2 * (P.sectorDensity D K j - 1) *
              (∑ t with P.sector t = j,
                D.targetLaw t * (D.density K t - P.sectorDensity D K j)) +
            (∑ t with P.sector t = j, D.targetLaw t) *
              (P.sectorDensity D K j - 1) ^ 2 := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        _ = _ := by rw [hcenter]; ring

end Partition

/-- Exact between-sector term for a two-sector seam. -/
theorem twoSector_between_eq
    (b g : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    b * (g / b - 1) ^ 2 +
        (1 - b) * ((1 - g) / (1 - b) - 1) ^ 2 =
      (g - b) ^ 2 / (b * (1 - b)) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h1b0 : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb1)
  field_simp
  ring

end RouteEHallANOVAData

end RHTower
