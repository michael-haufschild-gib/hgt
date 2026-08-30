import GaloisForLFunctions.HTGeometry.FixedSourceFormationCapital

/-!
# Capital neutrality of common recovery and of functional-equation relabelling

Section 5 of the formation-resource card `ULF-FRM-2`.

A split common recovery attaches to every outcome an extra coordinate drawn from one law that
does not depend on which of the two source marks is active.  It changes neither the Rényi
overlap nor the Hellinger affinity, and the retained coordinate recovers the original packet, so
every data-processing divergence is unchanged.  A bijective relabelling of the outcome alphabet
commutes with independent powers and preserves all of these quantities as well.
-/

open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X H : Type*}

/-! ## Split common recovery -/

/-- `(FCAP.23)`  A split common recovery attaches an `H`-coordinate drawn from a mark-independent
kernel while retaining the original outcome. -/
def splitRecovery (p : X → ℝ) (κ : X → H → ℝ) : X × H → ℝ := fun q => p q.1 * κ q.1 q.2

theorem splitRecovery_nonneg {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) {κ : X → H → ℝ}
    (hκ : ∀ x h, 0 ≤ κ x h) (q : X × H) : 0 ≤ splitRecovery p κ q :=
  mul_nonneg (hp q.1) (hκ q.1 q.2)

/-- Retaining the original coordinate recovers the packet. -/
theorem sum_splitRecovery_fibre [Fintype H] (p : X → ℝ) {κ : X → H → ℝ}
    (hκ : ∀ x, ∑ h, κ x h = 1) (x : X) : ∑ h, splitRecovery p κ (x, h) = p x := by
  simp only [splitRecovery, ← Finset.mul_sum, hκ x, mul_one]

theorem sum_splitRecovery [Fintype X] [Fintype H] (p : X → ℝ) {κ : X → H → ℝ}
    (hκ : ∀ x, ∑ h, κ x h = 1) : ∑ q, splitRecovery p κ q = ∑ x, p x := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ => sum_splitRecovery_fibre p hκ x

/-- `(FCAP.24)`  A split common recovery is Rényi-neutral. -/
theorem renyiOverlap_splitRecovery [Fintype X] [Fintype H] {α : ℝ} (h0 : 0 < α) (u v : X → ℝ)
    {κ : X → H → ℝ} (hκ0 : ∀ x h, 0 ≤ κ x h) (hκ1 : ∀ x, ∑ h, κ x h = 1)
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    renyiOverlap α (splitRecovery u κ) (splitRecovery v κ) = renyiOverlap α u v := by
  have hpow : ∀ x h, κ x h ^ α * κ x h ^ (1 - α) = κ x h := by
    intro x h
    rcases eq_or_lt_of_le (hκ0 x h) with hz | hpos
    · rw [← hz, Real.zero_rpow h0.ne', zero_mul]
    · rw [← Real.rpow_add hpos]
      norm_num
  rw [renyiOverlap, renyiOverlap, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hterm : ∀ h : H, splitRecovery u κ (x, h) ^ α * splitRecovery v κ (x, h) ^ (1 - α)
      = u x ^ α * v x ^ (1 - α) * κ x h := by
    intro h
    simp only [splitRecovery]
    rw [Real.mul_rpow (hu x) (hκ0 x h), Real.mul_rpow (hv x) (hκ0 x h),
      show u x ^ α * κ x h ^ α * (v x ^ (1 - α) * κ x h ^ (1 - α))
        = u x ^ α * v x ^ (1 - α) * (κ x h ^ α * κ x h ^ (1 - α)) by ring, hpow x h]
  rw [Finset.sum_congr rfl fun h _ => hterm h, ← Finset.mul_sum, hκ1 x, mul_one]

/-- `(FCAP.24)`  A split common recovery is Hellinger-neutral. -/
theorem finitePacketAffinity_splitRecovery [Fintype X] [DecidableEq X] [Fintype H]
    [DecidableEq H] (u v : X → ℝ) {κ : X → H → ℝ} (hκ0 : ∀ x h, 0 ≤ κ x h)
    (hκ1 : ∀ x, ∑ h, κ x h = 1) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    finitePacketAffinity (splitRecovery u κ) (splitRecovery v κ) = finitePacketAffinity u v :=
  renyiOverlap_splitRecovery (by norm_num) u v hκ0 hκ1 hu hv

/-- The split common recovery of a binary experiment. -/
def FiniteExperiment.splitRecovery [Fintype X] [Fintype H] (E : FiniteExperiment X)
    {κ : X → H → ℝ} (hκ0 : ∀ x h, 0 ≤ κ x h) (hκ1 : ∀ x, ∑ h, κ x h = 1) :
    FiniteExperiment (X × H) where
  law₀ := GaloisForLFunctions.HTGeometry.splitRecovery E.law₀ κ
  law₁ := GaloisForLFunctions.HTGeometry.splitRecovery E.law₁ κ
  nonneg₀ := splitRecovery_nonneg E.nonneg₀ hκ0
  nonneg₁ := splitRecovery_nonneg E.nonneg₁ hκ0
  sum₀ := by rw [sum_splitRecovery _ hκ1, E.sum₀]
  sum₁ := by rw [sum_splitRecovery _ hκ1, E.sum₁]

/-- `(FCAP.24)`  Capital is unchanged by a split common recovery. -/
theorem FiniteExperiment.capital_splitRecovery [Fintype X] [Fintype H] {α : ℝ} (h0 : 0 < α)
    (E : FiniteExperiment X) {κ : X → H → ℝ} (hκ0 : ∀ x h, 0 ≤ κ x h)
    (hκ1 : ∀ x, ∑ h, κ x h = 1) :
    (E.splitRecovery hκ0 hκ1).capital α = E.capital α := by
  have h : renyiOverlap α (E.splitRecovery hκ0 hκ1).law₀ (E.splitRecovery hκ0 hκ1).law₁
      = renyiOverlap α E.law₀ E.law₁ :=
    renyiOverlap_splitRecovery h0 _ _ hκ0 hκ1 E.nonneg₀ E.nonneg₁
  rw [FiniteExperiment.capital, FiniteExperiment.capital, renyiCapital, renyiCapital, h]

/-! ## Functional-equation relabelling -/

/-- `(FCAP.25)`  A bijective relabelling of the outcome alphabet. -/
def reflectPacket (R : X ≃ X) (p : X → ℝ) : X → ℝ := fun x => p (R x)

/-- `(FCAP.25)`  Coordinatewise relabelling of an independent power is the independent power of
the relabelled packet. -/
theorem tensorPower_reflect (R : X ≃ X) (p : X → ℝ) (d : ℕ) (f : Fin d → X) :
    tensorPower d p (fun j => R (f j)) = tensorPower d (reflectPacket R p) f := rfl

theorem sum_reflectPacket [Fintype X] (R : X ≃ X) (p : X → ℝ) :
    ∑ x, reflectPacket R p x = ∑ x, p x :=
  Equiv.sum_comp R p

/-- Relabelling preserves the Rényi overlap. -/
theorem renyiOverlap_reflect [Fintype X] (α : ℝ) (R : X ≃ X) (u v : X → ℝ) :
    renyiOverlap α (reflectPacket R u) (reflectPacket R v) = renyiOverlap α u v :=
  Equiv.sum_comp R fun x => u x ^ α * v x ^ (1 - α)

/-- Relabelling preserves the Hellinger affinity. -/
theorem finitePacketAffinity_reflect [Fintype X] [DecidableEq X] (R : X ≃ X) (u v : X → ℝ) :
    finitePacketAffinity (reflectPacket R u) (reflectPacket R v) = finitePacketAffinity u v :=
  renyiOverlap_reflect _ R u v

/-- Relabelling preserves the Hellinger distance. -/
theorem finitePacketHellinger_reflect [Fintype X] [DecidableEq X] (R : X ≃ X) (u v : X → ℝ) :
    finitePacketHellinger (reflectPacket R u) (reflectPacket R v)
      = finitePacketHellinger u v := by
  simp only [finitePacketHellinger, EuclideanSpace.norm_eq, reflectPacket]
  simp only [show ∀ f g : X → ℝ, ∀ x : X,
    ((WithLp.toLp 2 f : EuclideanSpace ℝ X) - WithLp.toLp 2 g) x = f x - g x from
      fun f g x => by simp]
  congr 1
  exact Equiv.sum_comp R fun x => ‖Real.sqrt (u x) - Real.sqrt (v x)‖ ^ 2

/-- The relabelled binary experiment. -/
def FiniteExperiment.reflect [Fintype X] (R : X ≃ X) (E : FiniteExperiment X) :
    FiniteExperiment X where
  law₀ := reflectPacket R E.law₀
  law₁ := reflectPacket R E.law₁
  nonneg₀ := fun x => E.nonneg₀ _
  nonneg₁ := fun x => E.nonneg₁ _
  sum₀ := by rw [sum_reflectPacket, E.sum₀]
  sum₁ := by rw [sum_reflectPacket, E.sum₁]

/-- `(FCAP.25)`  Capital is a relabelling invariant. -/
theorem FiniteExperiment.capital_reflect [Fintype X] (α : ℝ) (R : X ≃ X)
    (E : FiniteExperiment X) : (E.reflect R).capital α = E.capital α := by
  have h : renyiOverlap α (E.reflect R).law₀ (E.reflect R).law₁ = renyiOverlap α E.law₀ E.law₁ :=
    renyiOverlap_reflect α R E.law₀ E.law₁
  rw [FiniteExperiment.capital, FiniteExperiment.capital, renyiCapital, renyiCapital, h]

end

end GaloisForLFunctions.HTGeometry
