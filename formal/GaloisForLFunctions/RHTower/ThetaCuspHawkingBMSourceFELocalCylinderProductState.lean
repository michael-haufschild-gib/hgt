import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEFiniteModeFockVacuumOrthogonality
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs

/-!
# Source-FE local-cylinder product-state sector law

HC83 proves that every nonzero repeated pair ratio drives normalized finite-cutoff vacua out of
reference Fock: fixed coefficients vanish and the unit vectors are not Cauchy. This module resolves
the surviving local-state question. It derives the actual cutoff Born weights from those Fock
coefficients, proves their exact Bernoulli product form, and proves every arbitrary finite-cylinder
reporter stabilizes exactly once its support lies below the cutoff.

Therefore local thermodynamic-state existence is unconditional—even off the critical wall where
the representing vectors escape. It is a dead RH producer. The local state is not blind to the
defect, however: its one-mode pair density is `‖r‖² / (1 + ‖r‖²)` and vanishes exactly for `r = 0`.
For the literal Xi source-FE ratio, universal local vacuum is exactly RH and transfers to HB,
Deninger/FZZ-P, PW-B, and canonical-copy RBH receivers.

This constructs the diagonal cylinder state only; it makes no unsupported full-CCR or
quasi-equivalence claim.

`[NEW] [EXTENDED SECTOR] [PRODUCT STATE] [LOCAL CONVERGENCE NO-GO] [LOCAL VACUUM IFF RH]`
-/

open Complex Real Filter Topology
open scoped ENNReal BigOperators

namespace RHTower

noncomputable section

/-- Squared Born weight of one Boolean pair occupation in the cutoff vacuum. -/
def finitePairFockBornWeight (r : ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ‖finitePairFockVacuum r N (pairOccupation S)‖ ^ 2

/-- Exact product form of every admitted Born coefficient. -/
theorem finitePairFockBornWeight_eq
    (r : ℂ) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    finitePairFockBornWeight r N S =
      (finitePairFockFactor r ^ 2) ^ N * (‖r‖ ^ 2) ^ S.card := by
  rw [finitePairFockBornWeight,
    finitePairFockVacuum_apply_pairOccupation r N S hS,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (finitePairFockFactor_nonneg r), norm_pow]
  rw [mul_pow]
  congr 1
  · rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  · rw [← pow_mul, ← pow_mul]
    congr 1
    omega

/-- Adding an unoccupied cutoff mode multiplies an old configuration weight by the local vacuum
factor. -/
theorem finitePairFockBornWeight_succ_old
    (r : ℂ) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    finitePairFockBornWeight r (N + 1) S =
      finitePairFockFactor r ^ 2 * finitePairFockBornWeight r N S := by
  have hS' : S ⊆ Finset.range (N + 1) :=
    hS.trans (Finset.range_mono (Nat.le_succ N))
  rw [finitePairFockBornWeight_eq r (N + 1) S hS',
    finitePairFockBornWeight_eq r N S hS, pow_succ]
  ring

/-- Adding an occupied cutoff mode supplies one further squared pair ratio. -/
theorem finitePairFockBornWeight_succ_insert
    (r : ℂ) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    finitePairFockBornWeight r (N + 1) (insert N S) =
      (finitePairFockFactor r ^ 2 * ‖r‖ ^ 2) *
        finitePairFockBornWeight r N S := by
  have hN : N ∉ S := fun hNS => (by simpa using hS hNS)
  have hS' : insert N S ⊆ Finset.range (N + 1) := by
    rw [Finset.range_add_one]
    intro n hn
    rw [Finset.mem_insert] at hn ⊢
    rcases hn with rfl | hn
    · exact Or.inl rfl
    · exact Or.inr (hS hn)
  rw [finitePairFockBornWeight_eq r (N + 1) (insert N S) hS',
    finitePairFockBornWeight_eq r N S hS,
    Finset.card_insert_of_notMem hN, pow_succ, pow_succ]
  ring

/-- Diagonal vector-state expectation of an arbitrary reporter on the first `K` pair modes. -/
def finitePairFockCylinderExpectation
    (r : ℂ) (N K : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ (Finset.range N).powerset,
    finitePairFockBornWeight r N S * f (S ∩ Finset.range K)

theorem finitePairFockCylinderExpectation_succ
    (r : ℂ) (N K : ℕ) (hKN : K ≤ N) (f : Finset ℕ → ℝ) :
    finitePairFockCylinderExpectation r (N + 1) K f =
      finitePairFockCylinderExpectation r N K f := by
  rw [finitePairFockCylinderExpectation, finitePairFockCylinderExpectation,
    Finset.range_add_one,
    Finset.sum_powerset_insert (by simp)]
  have hNK : N ∉ Finset.range K := by simp [not_lt.mpr hKN]
  have hsub : ∀ S ∈ (Finset.range N).powerset, S ⊆ Finset.range N := by
    intro S hS
    exact Finset.mem_powerset.mp hS
  calc
    (∑ S ∈ (Finset.range N).powerset,
          finitePairFockBornWeight r (N + 1) S * f (S ∩ Finset.range K)) +
        ∑ S ∈ (Finset.range N).powerset,
          finitePairFockBornWeight r (N + 1) (insert N S) *
            f (insert N S ∩ Finset.range K) =
      (∑ S ∈ (Finset.range N).powerset,
          finitePairFockFactor r ^ 2 *
            (finitePairFockBornWeight r N S * f (S ∩ Finset.range K))) +
        ∑ S ∈ (Finset.range N).powerset,
          (finitePairFockFactor r ^ 2 * ‖r‖ ^ 2) *
            (finitePairFockBornWeight r N S * f (S ∩ Finset.range K)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro S hS
        rw [finitePairFockBornWeight_succ_old r N S (hsub S hS)]
        ring
      · apply Finset.sum_congr rfl
        intro S hS
        rw [finitePairFockBornWeight_succ_insert r N S (hsub S hS)]
        have hinter : insert N S ∩ Finset.range K = S ∩ Finset.range K := by
          ext n
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hnS, hnK⟩
            · exact (hNK hnK).elim
            · exact ⟨hnS, hnK⟩
          · rintro ⟨hnS, hnK⟩
            exact ⟨Or.inr hnS, hnK⟩
        rw [hinter]
        ring
    _ = finitePairFockFactor r ^ 2 *
          (∑ S ∈ (Finset.range N).powerset,
            finitePairFockBornWeight r N S * f (S ∩ Finset.range K)) +
        (finitePairFockFactor r ^ 2 * ‖r‖ ^ 2) *
          (∑ S ∈ (Finset.range N).powerset,
            finitePairFockBornWeight r N S * f (S ∩ Finset.range K)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ S ∈ (Finset.range N).powerset,
          finitePairFockBornWeight r N S * f (S ∩ Finset.range K) := by
      calc
        finitePairFockFactor r ^ 2 *
              (∑ S ∈ (Finset.range N).powerset,
                finitePairFockBornWeight r N S * f (S ∩ Finset.range K)) +
            (finitePairFockFactor r ^ 2 * ‖r‖ ^ 2) *
              (∑ S ∈ (Finset.range N).powerset,
                finitePairFockBornWeight r N S * f (S ∩ Finset.range K)) =
          (finitePairFockFactor r ^ 2 * (1 + ‖r‖ ^ 2)) *
              (∑ S ∈ (Finset.range N).powerset,
                finitePairFockBornWeight r N S * f (S ∩ Finset.range K)) := by ring
        _ = _ := by rw [finitePairFockFactor_sq_mul, one_mul]

/-- Every reporter on the first `K` modes is exactly independent of all later cutoffs. -/
theorem finitePairFockCylinderExpectation_eq_cutoff
    (r : ℂ) (K N : ℕ) (hKN : K ≤ N) (f : Finset ℕ → ℝ) :
    finitePairFockCylinderExpectation r N K f =
      finitePairFockCylinderExpectation r K K f := by
  induction N, hKN using Nat.le_induction with
  | base => rfl
  | succ N hKN ih =>
      exact (finitePairFockCylinderExpectation_succ r N K hKN f).trans ih

/-- Every finite-cylinder vector state has an eventually constant thermodynamic limit, even when
the vectors themselves leave reference Fock. -/
theorem tendsto_finitePairFockCylinderExpectation
    (r : ℂ) (K : ℕ) (f : Finset ℕ → ℝ) :
    Tendsto (fun N : ℕ => finitePairFockCylinderExpectation r N K f)
      atTop (𝓝 (finitePairFockCylinderExpectation r K K f)) := by
  exact tendsto_atTop_of_eventually_const (i₀ := K) fun N hKN =>
    finitePairFockCylinderExpectation_eq_cutoff r K N hKN f

/-- One-mode occupation density of the limiting diagonal product state. -/
def finitePairFockOccupationDensity (r : ℂ) : ℝ :=
  finitePairFockFactor r ^ 2 * ‖r‖ ^ 2

/-- Local vacancy probability is the squared one-site vacuum factor. -/
theorem one_sub_finitePairFockOccupationDensity (r : ℂ) :
    1 - finitePairFockOccupationDensity r = finitePairFockFactor r ^ 2 := by
  rw [finitePairFockOccupationDensity]
  nlinarith [finitePairFockFactor_sq_mul r]

theorem finitePairFockOccupationDensity_nonneg (r : ℂ) :
    0 ≤ finitePairFockOccupationDensity r := by
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem finitePairFockOccupationDensity_le_one (r : ℂ) :
    finitePairFockOccupationDensity r ≤ 1 := by
  rw [← sub_nonneg]
  exact one_sub_finitePairFockOccupationDensity r ▸ sq_nonneg _

/-- Exact Bernoulli product form of every admitted cutoff Born weight. -/
theorem finitePairFockBornWeight_eq_bernoulli
    (r : ℂ) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    finitePairFockBornWeight r N S =
      finitePairFockOccupationDensity r ^ S.card *
        (1 - finitePairFockOccupationDensity r) ^ (N - S.card) := by
  have hcard : S.card ≤ N := by
    calc
      S.card ≤ (Finset.range N).card := Finset.card_le_card hS
      _ = N := Finset.card_range N
  rw [finitePairFockBornWeight_eq r N S hS,
    one_sub_finitePairFockOccupationDensity, finitePairFockOccupationDensity,
    mul_pow]
  calc
    (finitePairFockFactor r ^ 2) ^ N * (‖r‖ ^ 2) ^ S.card =
        (finitePairFockFactor r ^ 2) ^ (S.card + (N - S.card)) *
          (‖r‖ ^ 2) ^ S.card := by
      nth_rewrite 1 [show N = S.card + (N - S.card) by omega]
      rfl
    _ = (finitePairFockFactor r ^ 2) ^ S.card * (‖r‖ ^ 2) ^ S.card *
          (finitePairFockFactor r ^ 2) ^ (N - S.card) := by
      rw [pow_add]
      ring

/-- The first-mode occupation reporter has exactly the product-state density. -/
theorem finitePairFockCylinderExpectation_first_mem
    (r : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    finitePairFockCylinderExpectation r N 1
      (fun S => if 0 ∈ S then 1 else 0) = finitePairFockOccupationDensity r := by
  rw [finitePairFockCylinderExpectation_eq_cutoff r 1 N hN]
  have hempty := finitePairFockBornWeight_eq r 1 (∅ : Finset ℕ) (by simp)
  have hsingle := finitePairFockBornWeight_eq r 1 ({0} : Finset ℕ) (by simp)
  rw [finitePairFockCylinderExpectation,
    show Finset.range 1 = insert 0 ∅ by simp,
    Finset.sum_powerset_insert (by simp)]
  simp [hsingle, finitePairFockOccupationDensity]

/-- The actual cutoff Born weights have total mass one. -/
theorem finitePairFockCylinderExpectation_one (r : ℂ) (N : ℕ) :
    finitePairFockCylinderExpectation r N N (fun _S => 1) = 1 := by
  have hzero : finitePairFockBornWeight r 0 (∅ : Finset ℕ) = 1 := by
    rw [finitePairFockBornWeight_eq r 0 ∅ (by simp)]
    simp
  have h := finitePairFockCylinderExpectation_eq_cutoff
    r 0 N (Nat.zero_le N) (fun _S => 1)
  simpa [finitePairFockCylinderExpectation, hzero] using h

/-- First-mode occupation converges to the nontrivial local density even when vectors escape. -/
theorem tendsto_finitePairFockCylinderExpectation_first_mem (r : ℂ) :
    Tendsto
      (fun N : ℕ => finitePairFockCylinderExpectation r N 1
        (fun S => if 0 ∈ S then 1 else 0))
      atTop (𝓝 (finitePairFockOccupationDensity r)) := by
  simpa only [finitePairFockCylinderExpectation_first_mem r 1 le_rfl] using
    tendsto_finitePairFockCylinderExpectation r 1
      (fun S => if 0 ∈ S then 1 else 0)

/-- The occupation density is the usual Bernoulli parameter `‖r‖² / (1 + ‖r‖²)`. -/
theorem finitePairFockOccupationDensity_eq_div (r : ℂ) :
    finitePairFockOccupationDensity r = ‖r‖ ^ 2 / (1 + ‖r‖ ^ 2) := by
  have hden : (1 + ‖r‖ ^ 2 : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hden).2
  rw [finitePairFockOccupationDensity]
  calc
    (finitePairFockFactor r ^ 2 * ‖r‖ ^ 2) * (1 + ‖r‖ ^ 2) =
        (finitePairFockFactor r ^ 2 * (1 + ‖r‖ ^ 2)) * ‖r‖ ^ 2 := by ring
    _ = ‖r‖ ^ 2 := by rw [finitePairFockFactor_sq_mul, one_mul]

/-- Local occupation vanishes exactly for the trivial pair ratio. -/
theorem finitePairFockOccupationDensity_eq_zero_iff (r : ℂ) :
    finitePairFockOccupationDensity r = 0 ↔ r = 0 := by
  rw [finitePairFockOccupationDensity, mul_eq_zero]
  simp [(finitePairFockFactor_pos r).ne', norm_eq_zero]

/-- For every nonzero ratio, all finite-cylinder states converge although the representing cutoff
vectors are not Cauchy in reference Fock. -/
theorem finitePairFockCylinder_tendsto_and_not_cauchy_of_ne
    (r : ℂ) (hr : r ≠ 0) (K : ℕ) (f : Finset ℕ → ℝ) :
    Tendsto (fun N : ℕ => finitePairFockCylinderExpectation r N K f)
        atTop (𝓝 (finitePairFockCylinderExpectation r K K f)) ∧
      ¬ CauchySeq (finitePairFockVacuum r) := by
  exact ⟨tendsto_finitePairFockCylinderExpectation r K f,
    (cauchySeq_finitePairFockVacuum_iff r).not.mpr hr⟩

/-! ## Literal source-FE local product state -/

/-- Diagonal cylinder expectation induced by the literal source-FE cutoff vacuum. -/
def hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation
    (q : XiZeroCopy) (N K : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  finitePairFockCylinderExpectation
    (hbXiPeierlsUnitSourceFEFockVacuumPairRatio q) N K f

/-- Local pair density of the source-FE extended product state. -/
def hbXiPeierlsUnitSourceFELocalPairDensity (q : XiZeroCopy) : ℝ :=
  finitePairFockOccupationDensity
    (hbXiPeierlsUnitSourceFEFockVacuumPairRatio q)

/-- Every source-FE finite-cylinder state converges, without a wall or RH condition. -/
theorem tendsto_hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation
    (q : XiZeroCopy) (K : ℕ) (f : Finset ℕ → ℝ) :
    Tendsto
      (fun N : ℕ => hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q N K f)
      atTop
      (𝓝 (hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q K K f)) :=
  tendsto_finitePairFockCylinderExpectation _ K f

/-- Merely demanding existence of every diagonal local thermodynamic limit is unconditional. -/
def HBXiPeierlsUnitSourceFEGlobalLocalCylinderConvergence : Prop :=
  ∀ q : XiZeroCopy, ∀ K : ℕ, ∀ f : Finset ℕ → ℝ,
    Tendsto
      (fun N : ℕ => hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q N K f)
      atTop
      (𝓝 (hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q K K f))

theorem hbXiPeierlsUnitSourceFEGlobalLocalCylinderConvergence :
    HBXiPeierlsUnitSourceFEGlobalLocalCylinderConvergence := by
  intro q K f
  exact tendsto_hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q K f

/-- Off wall, the local state still converges while its representing vectors fail to converge. -/
theorem hbXiPeierlsUnitSourceFE_offWall_cylinder_tendsto_and_not_cauchy
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2)
    (K : ℕ) (f : Finset ℕ → ℝ) :
    Tendsto
        (fun N : ℕ => hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q N K f)
        atTop
        (𝓝 (hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q K K f)) ∧
      ¬ CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) :=
  ⟨tendsto_hbXiPeierlsUnitSourceFEFiniteModeFockCylinderExpectation q K f,
    not_cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_of_offWall q hq⟩

/-- Source-FE local vacuum is exactly vanishing pair amplitude. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_pair_eq_zero
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q = 0 :=
  (finitePairFockOccupationDensity_eq_zero_iff _).trans
    (hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero q)

/-- Source-FE local vacuum is exactly partner vacuum. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_pair_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero q)

/-- Source-FE extended local state is vacuum exactly on the critical wall. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_re_eq_half
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q)

/-- Universal local vacuum of the extended source-FE product state. -/
def HBXiPeierlsUnitSourceFEGlobalLocalPairVacuum : Prop :=
  ∀ q : XiZeroCopy, hbXiPeierlsUnitSourceFELocalPairDensity q = 0

/-- Universal local vacuum, unlike mere local convergence, is exactly RH. -/
theorem hbXiPeierlsUnitSourceFEGlobalLocalPairVacuum_iff_rh :
    HBXiPeierlsUnitSourceFEGlobalLocalPairVacuum ↔ RiemannHypothesis := by
  rw [HBXiPeierlsUnitSourceFEGlobalLocalPairVacuum,
    ← forall_hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_rh]
  exact forall_congr' fun q =>
    hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero q

/-- Extended local vacuum is HB optical darkness. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_opticalPower_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_opticalPower_zero n q)

/-- Extended local vacuum is Deninger Ward cancellation. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_sharedWardCharge_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_sharedWardCharge_zero n q)

/-- Extended local vacuum is FZZ-P information equilibrium. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_informationForce_zero
    (n : ℕ) (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_informationForce_zero n q)

/-- Extended local vacuum is every-grade PW-B balance. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_pwBalance_zero
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    hbXiPeierlsUnitSourceFELocalPairDensity q = 0 ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_pwBalance_zero n q k)

/-- On the canonical divisor copy, extended local vacuum is RBH balance. -/
theorem hbXiPeierlsUnitSourceFELocalPairDensity_firstCopy_eq_zero_iff_rbhBalance_zero
    (n : ℕ) (rho : XiDivisorSupport) :
    hbXiPeierlsUnitSourceFELocalPairDensity
        (reflectedBiHeatFirstDivisorCopy rho) = 0 ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 :=
  (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_partnerNumber_eq_zero
    (reflectedBiHeatFirstDivisorCopy rho)).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_firstCopy_eq_zero_iff_rbhBalance_zero n rho)

end

end RHTower
