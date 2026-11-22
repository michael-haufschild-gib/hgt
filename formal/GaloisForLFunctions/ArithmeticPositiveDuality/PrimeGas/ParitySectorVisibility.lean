import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ParityGradingRigidity

/-!
# Critical visibility of the square-shell gas

The normalized kernel trace is the coherent overlap of the doubled phase with
the identity. Its limiting magnitude is positive exactly in the sectors that
contain a sign character. Primewise rounding constructs such a character.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology ContinuousLinearMap
open scoped Classical

/-- Thermal phase insertion on the surviving square shells at physical inverse temperature β/2. -/
def squarePhaseHeat (χ : ℕ+ →* Circle) (β : TraceTemperature) :=
  squareKernelTransport (thermalPhaseOperator β (χ^2 : ℕ+ →* Circle))

theorem squarePhaseHeat_apply (χ : ℕ+ →* Circle) (β : TraceTemperature) (f : parityPairing.ker) (n : ℕ+) :
    (squarePhaseHeat χ β f : PairGas) (squareState n) =
      (thermalWeight β n : ℂ) * twoCopyPhase χ (χ*primeParity) f (squareState n) := by
  change (squareKernelEquiv (thermalPhaseOperator β (χ^2 : ℕ+ →* Circle) (squareKernelEquiv.symm f)) : PairGas) _ = _
  rw [squareKernelEquiv_coordinate, thermalPhaseOperator_apply, squareKernelEquiv_symm_coordinate, twoCopyPhase_square,
    MonoidHom.pow_apply, Circle.coe_pow]
  ring

/-- Trace measured against the ordinary doubled-energy partition. -/
def squarePhaseSignal (χ : ℕ+ →* Circle) (β : TraceTemperature) :=
  opTrace (squarePhaseHeat χ β) / riemannZeta β.val

theorem squarePhaseSignal_eq_overlap (χ : ℕ+ →* Circle) (β : TraceTemperature) :
    squarePhaseSignal χ β = phaseOverlap 1 (χ^2) β := by
  have hT : (thermalPhaseOperator β (χ^2 : ℕ+ →* Circle)).IsTraceClass := by
    unfold thermalPhaseOperator
    exact (HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)
  rw [squarePhaseSignal, squarePhaseHeat, squareKernelTransport_trace _ hT, thermalPhaseOperator_trace,
    phaseOverlap_eq_trace, div_one]
  rfl

/-- The sign character negative on precisely the primes in S. -/
def primeSign (S : Set Nat.Primes) : ℕ+ →* Circle :=
  (prime_phase_coordinates.surjective (fun p => if p ∈ S then -1 else 1)).choose

theorem primeSign_at (S : Set Nat.Primes) (p : Nat.Primes) :
    primeSign S (p : ℕ+) = if p ∈ S then -1 else 1 :=
  congrFun (prime_phase_coordinates.surjective (fun p => if p ∈ S then -1 else 1)).choose_spec p

theorem primeSign_square (S : Set Nat.Primes) : primeSign S ^ 2 = 1 := by
  apply prime_phase_coordinates.injective
  funext p
  change (primeSign S (p : ℕ+))^2 = 1
  rw [primeSign_at]
  split <;> simp

/-- Every character of order dividing two is specified by its negative primes. -/
theorem square_eq_one_iff_primeSign (ε : ℕ+ →* Circle) :
    ε^2 = 1 ↔ ∃ S : Set Nat.Primes, ε = primeSign S := by
  constructor
  · intro he
    let S : Set Nat.Primes := {p | ε (p : ℕ+) = -1}
    refine ⟨S,prime_phase_coordinates.injective ?_⟩
    funext p
    rw [primeSign_at]
    have h := congrArg (fun κ : ℕ+ →* Circle => (κ (p : ℕ+) : ℂ)) he
    simp only [MonoidHom.pow_apply, Circle.coe_pow, MonoidHom.one_apply, Circle.coe_one] at h
    rcases sq_eq_one_iff.mp h with h₁ | h₁
    · have hpos : ε (p : ℕ+) = 1 := Circle.coe_injective h₁
      have hn : p ∉ S := fun hp => by
        have hp' : ε (p : ℕ+) = -1 := hp
        rw [hpos] at hp'
        have hc := congrArg (fun z : Circle => (z : ℂ)) hp'
        norm_num at hc
      rw [if_neg hn,hpos]
    · have hneg : p ∈ S := Circle.coe_injective h₁
      rw [if_pos hneg]
      exact hneg
  · rintro ⟨S,rfl⟩
    exact primeSign_square S

private def negativePrimes (χ : ℕ+ →* Circle) : Set Nat.Primes :=
  {p | ‖(χ (p : ℕ+) : ℂ) + 1‖ < ‖(χ (p : ℕ+) : ℂ) - 1‖}

private theorem round_bound (χ : ℕ+ →* Circle) (p : Nat.Primes) :
    ‖(χ (p : ℕ+) : ℂ) - (primeSign (negativePrimes χ) (p : ℕ+) : ℂ)‖ ≤
      ‖(χ (p : ℕ+) : ℂ)^2 - 1‖ := by
  let z : ℂ := χ (p : ℕ+)
  have ht := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) z (-1)
  rw [norm_sub_rev (1 : ℂ) z, sub_neg_eq_add, sub_neg_eq_add] at ht
  have htwo : ‖(1:ℂ)+1‖ = 2 := by norm_num
  rw [htwo] at ht
  have hfac : z^2-1 = (z-1)*(z+1) := by ring
  change ‖z - (primeSign (negativePrimes χ) (p : ℕ+) : ℂ)‖ ≤ ‖z^2-1‖
  rw [hfac, norm_mul, primeSign_at]
  by_cases h : p ∈ negativePrimes χ
  · change ‖z+1‖ < ‖z-1‖ at h
    have hm : p ∈ negativePrimes χ := h
    rw [if_pos hm, Circle.coe_neg, Circle.coe_one, sub_neg_eq_add]
    exact le_mul_of_one_le_left (norm_nonneg _) (by linarith only [h,ht])
  · have hr : ‖z-1‖ ≤ ‖z+1‖ := le_of_not_gt h
    rw [if_neg h, Circle.coe_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith only [hr,ht])

private theorem square_sector_series (χ : ℕ+ →* Circle) :
    samePhaseSector 1 (χ^2) ↔ Summable (fun p : Nat.Primes => ‖(χ (p : ℕ+) : ℂ)^2 - 1‖^2 / (p : ℕ)) := by
  simp only [samePhaseSector, MonoidHom.pow_apply, Circle.coe_pow, MonoidHom.one_apply, Circle.coe_one]

/-- Squaring sends a sector to the identity precisely when it has a representative of order dividing two. -/
theorem square_sector_iff_sign (χ : ℕ+ →* Circle) :
    samePhaseSector 1 (χ^2) ↔ ∃ ε : ℕ+ →* Circle, ε^2 = 1 ∧ samePhaseSector ε χ := by
  rw [square_sector_series]
  constructor
  · intro hs
    refine ⟨primeSign (negativePrimes χ),primeSign_square _,?_⟩
    exact Summable.of_nonneg_of_le (fun _ => by positivity) (fun p =>
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (round_bound χ p) 2) (Nat.cast_nonneg _)) hs
  · rintro ⟨ε,he,hs⟩
    unfold samePhaseSector at hs
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_left 4)
    intro p
    let z : ℂ := χ (p : ℕ+)
    let e : ℂ := ε (p : ℕ+)
    have he2 : e^2 = 1 := by
      have h := congrArg (fun κ : ℕ+ →* Circle => (κ (p : ℕ+) : ℂ)) he
      simpa only [MonoidHom.pow_apply, Circle.coe_pow, MonoidHom.one_apply, Circle.coe_one] using h
    have hf : z^2 - 1 = (z-e)*(z+e) := by rw [← he2]; ring
    have hu : ‖z+e‖ ≤ 2 := (norm_add_le z e).trans (by norm_num [z,e])
    change ‖z^2-1‖^2 / (p : ℕ) ≤ 4*(‖z-e‖^2 / (p : ℕ))
    rw [hf, norm_mul, mul_pow, ← mul_div_assoc, mul_comm (4:ℝ)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hu₂ := pow_le_pow_left₀ (norm_nonneg _) hu 2
    norm_num at hu₂
    exact mul_le_mul_of_nonneg_left hu₂ (sq_nonneg _)

/-- Positive limiting visibility occurs exactly in the sign sectors. -/
theorem squarePhase_visibility_iff (χ : ℕ+ →* Circle) :
    (∃ r : ℝ, 0 < r ∧ Tendsto (fun β => ‖squarePhaseSignal χ β‖) atPartitionPole (𝓝 r)) ↔
      ∃ ε : ℕ+ →* Circle, ε^2 = 1 ∧ samePhaseSector ε χ := by
  rw [← square_sector_iff_sign, ← sectorAmplitude_ne_zero_iff]
  have hlim : Tendsto (fun β => ‖squarePhaseSignal χ β‖) atPartitionPole (𝓝 ‖sectorAmplitude 1 (χ^2)‖) := by
    simpa only [squarePhaseSignal_eq_overlap] using phaseOverlap_norm_limit 1 (χ^2)
  constructor
  · rintro ⟨r,hr,h⟩
    exact norm_pos_iff.mp ((tendsto_nhds_unique h hlim) ▸ hr)
  · exact fun h => ⟨_,norm_pos_iff.mpr h,hlim⟩

/-- Sign characters differing on a set of primes of infinite reciprocal mass belong to distinct sectors. -/
theorem primeSign_sector_iff (S T : Set Nat.Primes) :
    samePhaseSector (primeSign S) (primeSign T) ↔
      Summable (fun p : Nat.Primes => if p ∈ (S \ T) ∪ (T \ S) then ((p : ℕ) : ℝ)⁻¹ else 0) := by
  let a (p : Nat.Primes) : ℝ := if p ∈ (S \ T) ∪ (T \ S) then ((p : ℕ) : ℝ)⁻¹ else 0
  have hd : ‖(-1:ℂ) - 1‖^2 = 4 := by rw [show (-1:ℂ)-1 = -2 by ring, norm_neg]; norm_num
  have hd' : ‖(1:ℂ) + 1‖^2 = 4 := by norm_num
  have hp (p : Nat.Primes) :
      ‖(primeSign T (p : ℕ+) : ℂ)-(primeSign S (p : ℕ+) : ℂ)‖^2 / (p : ℕ) = 4*a p := by
    rw [primeSign_at,primeSign_at]
    by_cases hS : p ∈ S <;> by_cases hT : p ∈ T <;>
      simp [a,hS,hT,hd,hd',div_eq_mul_inv]
  unfold samePhaseSector
  constructor
  · intro hs
    exact (hs.mul_left (4:ℝ)⁻¹).congr fun p => by rw [hp, inv_mul_cancel_left₀ (by norm_num : (4:ℝ) ≠ 0)]
  · intro hs
    exact (hs.mul_left 4).congr fun p => (hp p).symm

#print axioms squarePhaseHeat_apply
#print axioms squarePhaseSignal_eq_overlap
#print axioms square_eq_one_iff_primeSign
#print axioms square_sector_iff_sign
#print axioms squarePhase_visibility_iff
#print axioms primeSign_sector_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
