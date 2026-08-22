import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Extremal
import GaloisForLFunctions.HTGeometry.WindingReturnEquivalence

/-!
# Extremality gives the continuous first-return exponent

Kleinbock--Margulis extremality controls integer simultaneous approximations, whereas a static
Hamiltonian evolves in continuous time.  This file closes that interface.  First, failure of VWA
is converted into an eventual lower bound for every integer lattice hit.  Second, anchoring one
nonzero spectral gap converts every sufficiently late continuous return into an integer winding.
The resulting continuous-time lower exponent is `1 / d` for `d` projective gap ratios, up to the
fixed radius distortion already forced by the anchor conversion.
-/

open Set

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

/-- Failure of very-well simultaneous approximation gives the sharp eventual lower first-hit
exponent.  Every sufficiently large winding that enters a radius `r` must exceed the displayed
power of `r`. -/
theorem eventually_rpow_lt_cast_of_hit_of_not_vwa
    {n : ℕ} (hn : 0 < n) {y : Fin n → ℝ} (hy : ¬ VWA y)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : ℕ, ∀ {q : ℕ}, Q < q → ∀ {r : ℝ},
      (∀ i, latticeClose ((q : ℝ) * y i) r) →
        r ^ (-(1 / (((n : ℝ))⁻¹ + η))) < (q : ℝ) := by
  let c : ℝ := ((n : ℝ))⁻¹ + η
  have hc : 0 < c := by
    dsimp [c]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  let A : Set ℕ := {q : ℕ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
    |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - η)}
  have hA : A.Finite := by
    simpa only [A] using finite_of_not_vwa hy hη
  obtain ⟨Q, hQ⟩ := hA.bddAbove
  refine ⟨Q, ?_⟩
  intro q hq r hhit
  have hqpos : 0 < q := by omega
  have hqnot : q ∉ A := by
    intro hmem
    have := hQ hmem
    omega
  have hfail : ∃ i, ∀ p : ℤ,
      (q : ℝ) ^ (-c) ≤ |(q : ℝ) * y i - p| := by
    have hpow : (q : ℝ) ^ (-c) = (q : ℝ) ^ (-((n : ℝ))⁻¹ - η) := by
      congr 1
      dsimp [c]
      ring
    by_contra h
    push Not at h
    apply hqnot
    refine ⟨by omega, ?_⟩
    choose p hp using h
    exact ⟨p, fun i => by rw [← hpow]; exact (hp i).le⟩
  simpa only [c] using rpow_lt_cast_of_hit hc hqpos hfail hhit

/-- A non-VWA projective gap packet forces the sharp continuous-time recurrence lower exponent,
up to the fixed anchor-ratio distortion.  Time itself supplies the removed winding direction, so
`d + 1` anchored gaps pay exponent `1 / d`, not `1 / (d + 1)`. -/
theorem eventually_continuousReturn_lower_of_not_vwa
    {d : ℕ} (hd : 0 < d) (g : Fin (d + 1) → ℝ) (hg0 : g 0 ≠ 0)
    {A : ℝ} (hA : ∀ j, |gapRatio g j| ≤ A)
    (hy : ¬ VWA fun i : Fin d => gapRatio g i.succ)
    {η : ℝ} (hη : 0 < η) :
    ∃ Q : ℕ, ∀ {r t : ℝ},
      (Q : ℝ) + r ≤ |gapTurn g t 0| →
      ContinuousReturn g r t →
      (r * (1 + A)) ^ (-(1 / (((d : ℝ))⁻¹ + η))) <
        |t| * |g 0| / (2 * Real.pi) + r := by
  obtain ⟨Q, hQ⟩ := eventually_rpow_lt_cast_of_hit_of_not_vwa hd hy hη
  refine ⟨Q, ?_⟩
  intro r t hlarge hreturn
  obtain ⟨q, hanchor, hwind⟩ :=
    exists_windingReturn_of_continuousReturn g hg0 hA hreturn
  have hqabsLower : (Q : ℝ) < |(q : ℝ)| := by
    have hrev := abs_sub_abs_le_abs_sub (gapTurn g t 0) (q : ℝ)
    linarith
  have hnatAbsCast : (q.natAbs : ℝ) = |(q : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hQnat : Q < q.natAbs := by
    have hreal : (Q : ℝ) < (q.natAbs : ℝ) := by
      rw [hnatAbsCast]
      exact hqabsLower
    exact_mod_cast hreal
  have hhit : ∀ i : Fin d,
      latticeClose ((q.natAbs : ℝ) * gapRatio g i.succ) (r * (1 + A)) := by
    intro i
    obtain ⟨p, hp⟩ := hwind i.succ
    by_cases hqnonneg : 0 ≤ q
    · have hcast : (q.natAbs : ℝ) = (q : ℝ) := by
        rw [hnatAbsCast, abs_of_nonneg]
        exact_mod_cast hqnonneg
      rw [hcast]
      exact ⟨p, hp⟩
    · have hqneg : (q : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hqnonneg)
      refine ⟨-p, ?_⟩
      rw [hnatAbsCast, abs_of_neg hqneg]
      push_cast
      rw [show -(q : ℝ) * gapRatio g i.succ - -(p : ℝ) =
          -((q : ℝ) * gapRatio g i.succ - (p : ℝ)) by ring, abs_neg]
      exact hp
  have hlower := hQ hQnat hhit
  have hupper := abs_winding_le_of_continuousReturn g hanchor
  rw [hnatAbsCast] at hlower
  exact hlower.trans_le hupper

/-! ## Unconditional generic-spectrum law -/

open MeasureTheory

/-- Identity parameter charts are nondegenerate at first order. -/
theorem nondegAt_id {n : ℕ} (x : Fin n → ℝ) :
    NondegAt 1 (fun y : Fin n → ℝ => y) x := by
  intro w h
  funext i
  have hz := h 1 (by omega) (by omega) (fun _ : Fin 1 => Pi.single i 1)
  simpa [Pi.single_apply] using hz

/-- Lebesgue-almost every vector has the optimal simultaneous Diophantine exponent. -/
theorem volume_vwa_eq_zero {n : ℕ} (hn : 0 < n) :
    volume {y : Fin n → ℝ | VWA y} = 0 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hdeg : volume {x ∈ (Set.univ : Set (Fin n → ℝ)) |
      ¬ NondegAt 1 (fun y : Fin n → ℝ => y) x} = 0 := by
    have hset : {x ∈ (Set.univ : Set (Fin n → ℝ)) |
        ¬ NondegAt 1 (fun y : Fin n → ℝ => y) x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, Set.mem_empty_iff_false,
        iff_false]
      exact fun h => h (nondegAt_id x)
    rw [hset, measure_empty]
  simpa only [Set.mem_univ, true_and] using
    (theoremA_simultaneous hn (l := 1) (by omega)
      (U := Set.univ) isOpen_univ
      (F := fun y : Fin n → ℝ => y)
      (fun _ _ => contDiffAt_id) hdeg)

/-- A gap packet with unit anchor and prescribed projective ratios. -/
def unitAnchoredGapPacket {d : ℕ} (y : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases 1 y

@[simp] theorem unitAnchoredGapPacket_zero {d : ℕ} (y : Fin d → ℝ) :
    unitAnchoredGapPacket y 0 = 1 := rfl

@[simp] theorem unitAnchoredGapPacket_succ {d : ℕ} (y : Fin d → ℝ) (i : Fin d) :
    unitAnchoredGapPacket y i.succ = y i := rfl

@[simp] theorem gapRatio_unitAnchoredGapPacket_succ {d : ℕ} (y : Fin d → ℝ) (i : Fin d) :
    gapRatio (unitAnchoredGapPacket y) i.succ = y i := by
  simp [gapRatio]

/-- Canonical finite distortion bound for the unit-anchored packet. -/
def unitAnchoredRatioBound {d : ℕ} (y : Fin d → ℝ) : ℝ :=
  1 + ∑ i, |y i|

theorem abs_gapRatio_unitAnchoredGapPacket_le {d : ℕ} (y : Fin d → ℝ)
    (j : Fin (d + 1)) :
    |gapRatio (unitAnchoredGapPacket y) j| ≤ unitAnchoredRatioBound y := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [gapRatio, unitAnchoredGapPacket_zero, div_one, abs_one,
      unitAnchoredRatioBound]
    have hsum : 0 ≤ ∑ i, |y i| := Finset.sum_nonneg fun i _ => abs_nonneg (y i)
    linarith
  · simp only [gapRatio_unitAnchoredGapPacket_succ, unitAnchoredRatioBound]
    have hi : |y i| ≤ ∑ k, |y k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (y k)) (Finset.mem_univ i)
    linarith

/-- The optimal continuous recurrence lower law for a unit-anchored ratio packet. -/
def HasOptimalContinuousReturnLower {d : ℕ} (y : Fin d → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ Q : ℕ, ∀ {r t : ℝ},
    (Q : ℝ) + r ≤ |gapTurn (unitAnchoredGapPacket y) t 0| →
    ContinuousReturn (unitAnchoredGapPacket y) r t →
    (r * (1 + unitAnchoredRatioBound y)) ^
        (-(1 / (((d : ℝ))⁻¹ + η))) <
      |t| / (2 * Real.pi) + r

/-- Every non-VWA ratio packet has the optimal continuous first-return lower exponent. -/
theorem hasOptimalContinuousReturnLower_of_not_vwa
    {d : ℕ} (hd : 0 < d) {y : Fin d → ℝ} (hy : ¬ VWA y) :
    HasOptimalContinuousReturnLower y := by
  intro η hη
  have hy' : ¬ VWA fun i : Fin d => gapRatio (unitAnchoredGapPacket y) i.succ := by
    simpa only [gapRatio_unitAnchoredGapPacket_succ] using hy
  simpa [unitAnchoredGapPacket_zero, gapRatio_unitAnchoredGapPacket_succ] using
    (eventually_continuousReturn_lower_of_not_vwa hd
      (unitAnchoredGapPacket y) (by simp)
      (abs_gapRatio_unitAnchoredGapPacket_le y) hy' hη)

/-- **Generic continuous first-return exponent.** Lebesgue-almost every finite projective
frequency packet obeys the optimal `1 / d` continuous-time recurrence lower law. -/
theorem volume_not_hasOptimalContinuousReturnLower_eq_zero
    {d : ℕ} (hd : 0 < d) :
    volume {y : Fin d → ℝ | ¬ HasOptimalContinuousReturnLower y} = 0 := by
  refine measure_mono_null (fun y hy => ?_) (volume_vwa_eq_zero hd)
  by_contra hyvwa
  exact hy (hasOptimalContinuousReturnLower_of_not_vwa hd hyvwa)

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
