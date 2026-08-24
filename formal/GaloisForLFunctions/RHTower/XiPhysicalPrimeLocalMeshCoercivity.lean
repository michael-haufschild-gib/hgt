import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointNoncancellation
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureDispersion
import GaloisForLFunctions.HTGeometry.TwoCellHilbertCoercivity

open scoped BigOperators RealInnerProductSpace
open MeasureTheory Set

namespace RHTower

noncomputable section

def xiPhysicalEndpointCellSet (c d : ℝ) : Set ℝ := Ioc c d

theorem measure_xiPhysicalEndpointCellSet_ne_top (c d : ℝ) :
    volume (xiPhysicalEndpointCellSet c d) ≠ ⊤ := by
  rw [xiPhysicalEndpointCellSet]
  exact ne_of_lt measure_Ioc_lt_top

def xiPhysicalEndpointCellIndicator (c d : ℝ) : XiPhysicalApertureL2 :=
  indicatorConstLp (μ := (volume : Measure ℝ)) 2
    (s := xiPhysicalEndpointCellSet c d) measurableSet_Ioc
    (measure_xiPhysicalEndpointCellSet_ne_top c d) (1 : ℝ)

theorem xiPhysicalEndpointCellSet_inter (a b c d : ℝ) :
    xiPhysicalEndpointCellSet a b ∩ xiPhysicalEndpointCellSet c d =
      Ioc (max a c) (min b d) := by
  ext u
  simp only [xiPhysicalEndpointCellSet, mem_inter_iff, mem_Ioc]
  constructor
  · rintro ⟨⟨hau, hub⟩, hcu, hud⟩
    exact ⟨max_lt hau hcu, le_min hub hud⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨⟨(max_lt_iff.mp hlo).1, (le_min_iff.mp hhi).1⟩,
      (max_lt_iff.mp hlo).2, (le_min_iff.mp hhi).2⟩

theorem volume_real_xiPhysicalEndpointCellSet_inter (a b c d : ℝ) :
    volume.real (xiPhysicalEndpointCellSet a b ∩
        xiPhysicalEndpointCellSet c d) =
      GaloisForLFunctions.HTGeometry.realIntervalOverlapLength a b c d := by
  rw [xiPhysicalEndpointCellSet_inter,
    GaloisForLFunctions.HTGeometry.realIntervalOverlapLength,
    Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal', max_comm]

theorem real_inner_xiPhysicalEndpointCellIndicator
    (a b c d : ℝ) :
    inner ℝ (xiPhysicalEndpointCellIndicator a b)
        (xiPhysicalEndpointCellIndicator c d) =
      GaloisForLFunctions.HTGeometry.realIntervalOverlapLength a b c d := by
  simpa only [xiPhysicalEndpointCellIndicator,
      volume_real_xiPhysicalEndpointCellSet_inter] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := (volume : Measure ℝ))
      (s := xiPhysicalEndpointCellSet a b)
      (t := xiPhysicalEndpointCellSet c d)
      measurableSet_Ioc measurableSet_Ioc
      (measure_xiPhysicalEndpointCellSet_ne_top a b)
      (measure_xiPhysicalEndpointCellSet_ne_top c d))

theorem real_inner_xiPhysicalEndpointCellIndicator_self
    {c d : ℝ} (hcd : c < d) :
    inner ℝ (xiPhysicalEndpointCellIndicator c d)
        (xiPhysicalEndpointCellIndicator c d) = d - c := by
  rw [real_inner_xiPhysicalEndpointCellIndicator,
    GaloisForLFunctions.HTGeometry.realIntervalOverlapLength]
  simp only [min_self, max_self, max_eq_left (sub_nonneg.mpr hcd.le)]

theorem real_inner_xiPhysicalEndpointCellIndicator_adjacent
    {t L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
    inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
        (xiPhysicalEndpointCellIndicator t (t + R)) = 0 := by
  rw [real_inner_xiPhysicalEndpointCellIndicator,
    GaloisForLFunctions.HTGeometry.realIntervalOverlapLength]
  simp [hL.le, hR.le]

theorem real_inner_xiPhysicalEndpointCellIndicator_prime
    (c d A m k : ℝ) (p : Nat.Primes) :
    inner ℝ (xiPhysicalEndpointCellIndicator c d)
        (xiPhysicalPrimeLogApertureIndicator A m k p) =
      GaloisForLFunctions.HTGeometry.realIntervalOverlapLength
        c d (xiPhysicalPrimeLogApertureStart m p)
          (xiPhysicalPrimeLogApertureEnd A k p) := by
  have hvolume : volume.real (xiPhysicalEndpointCellSet c d ∩
      xiPhysicalPrimeLogApertureSet A m k p) =
      GaloisForLFunctions.HTGeometry.realIntervalOverlapLength
        c d (xiPhysicalPrimeLogApertureStart m p)
          (xiPhysicalPrimeLogApertureEnd A k p) := by
    exact volume_real_xiPhysicalEndpointCellSet_inter c d
      (xiPhysicalPrimeLogApertureStart m p)
      (xiPhysicalPrimeLogApertureEnd A k p)
  simpa only [xiPhysicalEndpointCellIndicator,
      xiPhysicalPrimeLogApertureIndicator,
      hvolume] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := (volume : Measure ℝ))
      (s := xiPhysicalEndpointCellSet c d)
      (t := xiPhysicalPrimeLogApertureSet A m k p)
      measurableSet_Ioc measurableSet_Ioc
      (measure_xiPhysicalEndpointCellSet_ne_top c d)
      (measure_xiPhysicalPrimeLogApertureSet_ne_top A m k p))

theorem realIntervalOverlapLength_comm (a b c d : ℝ) :
    GaloisForLFunctions.HTGeometry.realIntervalOverlapLength a b c d =
      GaloisForLFunctions.HTGeometry.realIntervalOverlapLength c d a b := by
  simp only [GaloisForLFunctions.HTGeometry.realIntervalOverlapLength,
    min_comm b d, max_comm a c]

theorem real_inner_xiPhysicalEndpointCellIndicator_prime'
    (c d A m k : ℝ) (p : Nat.Primes) :
    inner ℝ (xiPhysicalEndpointCellIndicator c d)
        (xiPhysicalPrimeLogApertureIndicator A m k p) =
      GaloisForLFunctions.HTGeometry.realIntervalOverlapLength
        (xiPhysicalPrimeLogApertureStart m p)
          (xiPhysicalPrimeLogApertureEnd A k p) c d := by
  rw [real_inner_xiPhysicalEndpointCellIndicator_prime,
    realIntervalOverlapLength_comm]

theorem real_inner_xiPhysicalEndpointCellIndicator_aperture
    {A c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ A) (hcd : c < d) :
    inner ℝ (xiPhysicalEndpointCellIndicator c d)
        (xiPhysicalLogApertureIndicator A) = d - c := by
  have hsubset : xiPhysicalEndpointCellSet c d ⊆
      xiPhysicalLogApertureSet A := by
    intro u hu
    rw [xiPhysicalEndpointCellSet, mem_Ioc] at hu
    rw [xiPhysicalLogApertureSet, mem_Ioc]
    exact ⟨lt_of_le_of_lt hc hu.1, hu.2.trans hd⟩
  have hinter : xiPhysicalEndpointCellSet c d ∩
      xiPhysicalLogApertureSet A = xiPhysicalEndpointCellSet c d :=
    inter_eq_left.mpr hsubset
  have hvolume : volume.real (xiPhysicalEndpointCellSet c d) = d - c := by
    rw [xiPhysicalEndpointCellSet, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hcd.le)]
  simpa only [xiPhysicalEndpointCellIndicator,
      xiPhysicalLogApertureIndicator, hinter, hvolume] using
    (MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (μ := (volume : Measure ℝ))
      (s := xiPhysicalEndpointCellSet c d)
      (t := xiPhysicalLogApertureSet A)
      measurableSet_Ioc measurableSet_Ioc
      (measure_xiPhysicalEndpointCellSet_ne_top c d)
      (measure_xiPhysicalLogApertureSet_ne_top A))

/-- Exact formal meaning of positive adjacent aperture-mesh cells around `t`: both cells lie in
`(0,A]`, and no packet start or end lies in either open cell. -/
structure XiPhysicalPrimeLogAdjacentCells
    (P : Finset Nat.Primes) (A m k t L R : ℝ) : Prop where
  left_pos : 0 < L
  right_pos : 0 < R
  left_mem : 0 ≤ t - L
  right_mem : t + R ≤ A
  start_left_separated : ∀ p ∈ P,
    xiPhysicalPrimeLogApertureStart m p ≤ t - L ∨
      t ≤ xiPhysicalPrimeLogApertureStart m p
  end_left_separated : ∀ p ∈ P,
    xiPhysicalPrimeLogApertureEnd A k p ≤ t - L ∨
      t ≤ xiPhysicalPrimeLogApertureEnd A k p
  start_right_separated : ∀ p ∈ P,
    xiPhysicalPrimeLogApertureStart m p ≤ t ∨
      t + R ≤ xiPhysicalPrimeLogApertureStart m p
  end_right_separated : ∀ p ∈ P,
    xiPhysicalPrimeLogApertureEnd A k p ≤ t ∨
      t + R ≤ xiPhysicalPrimeLogApertureEnd A k p

theorem normalized_adjacentCell_inner_centeredCarrier_eq_endpointTraceJump
    {P : Finset Nat.Primes} {A m k t L R : ℝ}
    (hmesh : XiPhysicalPrimeLogAdjacentCells P A m k t L R)
    {p : Nat.Primes} (hp : p ∈ P)
    (hactive : 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    inner ℝ (xiPhysicalEndpointCellIndicator t (t + R))
          (xiPhysicalPrimeLogCenteredApertureCarrier A m k p) / R -
        inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
          (xiPhysicalPrimeLogCenteredApertureCarrier A m k p) / L =
      (if xiPhysicalPrimeLogApertureStart m p = t then 1 else 0) -
        (if xiPhysicalPrimeLogApertureEnd A k p = t then 1 else 0) := by
  have hab : xiPhysicalPrimeLogApertureStart m p <
      xiPhysicalPrimeLogApertureEnd A k p := by
    have hdiff : 0 < xiPhysicalPrimeLogApertureEnd A k p -
        xiPhysicalPrimeLogApertureStart m p := by
      simpa [xiPhysicalPrimeLogApertureLength] using hactive
    linarith
  have hgap :=
    GaloisForLFunctions.HTGeometry.normalized_realIntervalOverlap_gap_eq_endpointJump
      hmesh.left_pos hmesh.right_pos hab
      (hmesh.start_left_separated p hp) (hmesh.end_left_separated p hp)
      (hmesh.start_right_separated p hp) (hmesh.end_right_separated p hp)
  have ht0 : 0 ≤ t := by linarith [hmesh.left_mem, hmesh.left_pos]
  have htA : t ≤ A := by linarith [hmesh.right_mem, hmesh.right_pos]
  simp only [xiPhysicalPrimeLogCenteredApertureCarrier,
    inner_sub_right, real_inner_smul_right]
  rw [
    real_inner_xiPhysicalEndpointCellIndicator_prime',
    real_inner_xiPhysicalEndpointCellIndicator_prime',
    real_inner_xiPhysicalEndpointCellIndicator_aperture
      ht0
      hmesh.right_mem (by linarith [hmesh.right_pos]),
    real_inner_xiPhysicalEndpointCellIndicator_aperture
      hmesh.left_mem htA (by linarith [hmesh.left_pos])]
  convert hgap using 1 <;>
    field_simp [hmesh.left_pos.ne', hmesh.right_pos.ne'] <;> ring

theorem normalized_adjacentCell_inner_aggregateCarrier_eq_neg_endpointJump
    {P : Finset Nat.Primes} {A m k t L R : ℝ}
    (hmesh : XiPhysicalPrimeLogAdjacentCells P A m k t L R)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    inner ℝ (xiPhysicalEndpointCellIndicator t (t + R))
          (xiPhysicalPrimeLogAggregateApertureCarrier P A m k) / R -
        inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
          (xiPhysicalPrimeLogAggregateApertureCarrier P A m k) / L =
      -xiPhysicalPrimeLogEndpointJump P A m k t := by
  classical
  have hright :
      inner ℝ (xiPhysicalEndpointCellIndicator t (t + R))
          (xiPhysicalPrimeLogAggregateApertureCarrier P A m k) =
        ∑ p ∈ P, physicalPrimeEndpointWeight p *
          inner ℝ (xiPhysicalEndpointCellIndicator t (t + R))
            (xiPhysicalPrimeLogCenteredApertureCarrier A m k p) := by
    rw [xiPhysicalPrimeLogAggregateApertureCarrier, inner_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [real_inner_smul_right]
  have hleft :
      inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
          (xiPhysicalPrimeLogAggregateApertureCarrier P A m k) =
        ∑ p ∈ P, physicalPrimeEndpointWeight p *
          inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
            (xiPhysicalPrimeLogCenteredApertureCarrier A m k p) := by
    rw [xiPhysicalPrimeLogAggregateApertureCarrier, inner_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [real_inner_smul_right]
  rw [hright, hleft]
  calc
    (∑ p ∈ P, physicalPrimeEndpointWeight p *
          inner ℝ (xiPhysicalEndpointCellIndicator t (t + R))
            (xiPhysicalPrimeLogCenteredApertureCarrier A m k p)) / R -
        (∑ p ∈ P, physicalPrimeEndpointWeight p *
          inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
            (xiPhysicalPrimeLogCenteredApertureCarrier A m k p)) / L =
      ∑ p ∈ P, physicalPrimeEndpointWeight p *
        (inner ℝ (xiPhysicalEndpointCellIndicator t (t + R))
              (xiPhysicalPrimeLogCenteredApertureCarrier A m k p) / R -
          inner ℝ (xiPhysicalEndpointCellIndicator (t - L) t)
              (xiPhysicalPrimeLogCenteredApertureCarrier A m k p) / L) := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ = ∑ p ∈ P, physicalPrimeEndpointWeight p *
        ((if xiPhysicalPrimeLogApertureStart m p = t then 1 else 0) -
          (if xiPhysicalPrimeLogApertureEnd A k p = t then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [normalized_adjacentCell_inner_centeredCarrier_eq_endpointTraceJump
        hmesh hp (hactive p hp)]
    _ = -xiPhysicalPrimeLogEndpointJump P A m k t := by
      rw [xiPhysicalPrimeLogEndpointJump,
        xiPhysicalPrimeLogEndpointEndWeight,
        xiPhysicalPrimeLogEndpointStartWeight]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
      ring

/-- `(AH17)`, unnormalized form: every genuine adjacent endpoint cell pair forces the sharp
harmonic jump energy inside the coherent physical carrier. -/
theorem harmonicEndpointJump_le_xiPhysicalPrimeLogApertureFusionEnergy
    {P : Finset Nat.Primes} {A m k t L R : ℝ}
    (hA : 0 < A)
    (hmesh : XiPhysicalPrimeLogAdjacentCells P A m k t L R)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    L * R / (L + R) * xiPhysicalPrimeLogEndpointJump P A m k t ^ 2 ≤
      xiPhysicalPrimeLogApertureFusionEnergy P A m k := by
  have hleft : inner ℝ
      (xiPhysicalEndpointCellIndicator (t - L) t)
      (xiPhysicalEndpointCellIndicator (t - L) t) = L := by
    rw [real_inner_xiPhysicalEndpointCellIndicator_self (by linarith [hmesh.left_pos])]
    ring
  have hright : inner ℝ
      (xiPhysicalEndpointCellIndicator t (t + R))
      (xiPhysicalEndpointCellIndicator t (t + R)) = R := by
    rw [real_inner_xiPhysicalEndpointCellIndicator_self (by linarith [hmesh.right_pos])]
    ring
  have hcoerc := GaloisForLFunctions.HTGeometry.harmonicAverageGap_le_norm_sq
    hmesh.left_pos hmesh.right_pos
    (u := xiPhysicalEndpointCellIndicator (t - L) t)
    (v := xiPhysicalEndpointCellIndicator t (t + R))
    (f := xiPhysicalPrimeLogAggregateApertureCarrier P A m k)
    hleft hright
    (real_inner_xiPhysicalEndpointCellIndicator_adjacent
      hmesh.left_pos hmesh.right_pos)
  rw [normalized_adjacentCell_inner_aggregateCarrier_eq_neg_endpointJump
      hmesh hactive, neg_sq,
    ← xiPhysicalPrimeLogApertureFusionEnergy_eq_norm_sq P hA m k] at hcoerc
  exact hcoerc

/-- `(AH17)`: sharp local endpoint-mesh lower bound for normalized physical aperture
dispersion. -/
theorem harmonicEndpointJump_div_totalWeight_sq_le_normalizedApertureDispersion
    {P : Finset Nat.Primes} (hP : P.Nonempty)
    {A m k t L R : ℝ} (hA : 0 < A)
    (hmesh : XiPhysicalPrimeLogAdjacentCells P A m k t L R)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p) :
    (L * R / (L + R) * |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2) /
        xiPhysicalPrimeLogTotalWeight P ^ 2 ≤
      xiPhysicalPrimeLogNormalizedApertureDispersion P A m k := by
  rw [sq_abs,
    xiPhysicalPrimeLogNormalizedApertureDispersion_eq_fusionEnergy_div hP hA]
  exact div_le_div_of_nonneg_right
    (harmonicEndpointJump_le_xiPhysicalPrimeLogApertureFusionEnergy
      hA hmesh hactive)
    (sq_nonneg _)

/-- `(AH18)`: if both adjacent cells have length at least `sigma`, the normalized dispersion
dominates `sigma/2` times the squared endpoint jump. -/
theorem halfSigmaEndpointJump_div_totalWeight_sq_le_normalizedApertureDispersion
    {P : Finset Nat.Primes} (hP : P.Nonempty)
    {A m k t L R sigma : ℝ} (hA : 0 < A)
    (hmesh : XiPhysicalPrimeLogAdjacentCells P A m k t L R)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (hsigmaL : sigma ≤ L) (hsigmaR : sigma ≤ R) :
    (sigma * |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2 / 2) /
        xiPhysicalPrimeLogTotalWeight P ^ 2 ≤
      xiPhysicalPrimeLogNormalizedApertureDispersion P A m k := by
  have hcoeff : sigma / 2 ≤ L * R / (L + R) := by
    calc
      sigma / 2 ≤ min L R / 2 :=
        div_le_div_of_nonneg_right (le_min hsigmaL hsigmaR) (by norm_num)
      _ ≤ L * R / (L + R) :=
        RHTower.half_min_le_harmonicCellCoefficient
          hmesh.left_pos.le hmesh.right_pos.le
          (add_pos hmesh.left_pos hmesh.right_pos)
  have hjump_nonneg : 0 ≤ |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2 :=
    sq_nonneg _
  calc
    (sigma * |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2 / 2) /
        xiPhysicalPrimeLogTotalWeight P ^ 2 =
      (sigma / 2 * |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2) /
        xiPhysicalPrimeLogTotalWeight P ^ 2 := by ring
    _ ≤ (L * R / (L + R) *
          |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2) /
        xiPhysicalPrimeLogTotalWeight P ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff hjump_nonneg) (sq_nonneg _)
    _ ≤ xiPhysicalPrimeLogNormalizedApertureDispersion P A m k :=
      harmonicEndpointJump_div_totalWeight_sq_le_normalizedApertureDispersion
        hP hA hmesh hactive

/-- `(PE15)`: an upper bound for the physical carrier energy forces the sharp pointwise
square-root stability bound on every genuine endpoint jump. -/
theorem abs_xiPhysicalPrimeLogEndpointJump_le_sqrt_energy_scale
    {P : Finset Nat.Primes} {A m k t L R epsilon : ℝ}
    (hA : 0 < A)
    (hmesh : XiPhysicalPrimeLogAdjacentCells P A m k t L R)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (henergy : xiPhysicalPrimeLogApertureFusionEnergy P A m k ≤ epsilon) :
    |xiPhysicalPrimeLogEndpointJump P A m k t| ≤
      Real.sqrt ((L + R) * epsilon / (L * R)) := by
  have hlower := harmonicEndpointJump_le_xiPhysicalPrimeLogApertureFusionEnergy
    hA hmesh hactive
  have hLR : 0 < L * R := mul_pos hmesh.left_pos hmesh.right_pos
  have hsum : 0 < L + R := add_pos hmesh.left_pos hmesh.right_pos
  have hsq : |xiPhysicalPrimeLogEndpointJump P A m k t| ^ 2 ≤
      (L + R) * epsilon / (L * R) := by
    have hfrac : (L * R *
          xiPhysicalPrimeLogEndpointJump P A m k t ^ 2) / (L + R) ≤ epsilon := by
      calc
        (L * R * xiPhysicalPrimeLogEndpointJump P A m k t ^ 2) / (L + R) =
            L * R / (L + R) * xiPhysicalPrimeLogEndpointJump P A m k t ^ 2 := by
              ring
        _ ≤ xiPhysicalPrimeLogApertureFusionEnergy P A m k := hlower
        _ ≤ epsilon := henergy
    have hmul := (div_le_iff₀ hsum).mp hfrac
    apply (le_div_iff₀ hLR).2
    simpa [sq_abs, mul_comm, mul_left_comm, mul_assoc] using hmul
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by simpa [sq_abs] using hsq)

end
end RHTower
