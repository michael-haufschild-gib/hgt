import GaloisForLFunctions.HTGeometry.TripticGammaProductRealization
import GaloisForLFunctions.HTGeometry.TripticMultiplicativeKernelConverse
import GaloisForLFunctions.HTGeometry.MinimalHTCompletionArchitecture

/-!
# The exact Kummer-content root classification of the multiplicative triptic class

A member `Y` of the multiplicative triptic class has an `m`-th source root modulo differentially
algebraic factors — a class member `Z` with `Y/Z^m` differentially algebraic — exactly when `m`
divides its orbital charge on every orbit, equivalently every coefficient of its integral orbit
divisor, equivalently the divisor's Kummer content.  The root class is unique modulo differentially
algebraic factors, and the content itself is the maximum root order.

The backward direction realizes the quotient divisor by an explicit product of translated elliptic
gamma functions and identifies the remaining factor as differentially algebraic through the kernel
theorem for the orbital charge; the forward direction is the kernel theorem's converse together
with additivity of the charge.

* `differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source`;
* `HasTripticSourceRoot`, `hasTripticSourceRoot_iff_dvd_charge`;
* `hasTripticSourceRoot_iff_content_dvd`, `tripticSourceRoot_unique`;
* `hasTripticSourceRoot_content`, `tripticSource_maximal_root_order`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {τ σ : ℂ} {Y : ℂ → ℂ} {Cst : ℂ}

/-! ### The kernel theorem for class members -/

set_option maxHeartbeats 1000000 in
/-- **The kernel of the orbital charge, for class members.**  A member of the multiplicative
triptic class whose orbital charge vanishes on every orbit has vanishing mixed constant and a
differentially algebraic logarithmic derivative. -/
theorem differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hcharge : ∀ p : ℂ, tripticOrbitCharge Y σ p = 0) :
    Cst = 0 ∧ DifferentiallyAlgebraic (toMeromorphicNFOn (logDeriv Y) (Set.univ : Set ℂ)) := by
  have hFmero : MeromorphicOn (logDeriv Y) (Set.univ : Set ℂ) := fun z _ ↦
    ((hY.mero z (Set.mem_univ z)).deriv).div (hY.mero z (Set.mem_univ z))
  have hFper : ∀ z : ℂ, logDeriv Y (z + 1) = logDeriv Y z := fun z ↦
    logDeriv_of_periodic hY.periodic z
  refine differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor hFmero
    (periodicOneGerm_of_forall hFper) hY.mixed hτ hσ (indepTriple_of_indepPeriods hindep)
    hindepτ hindepσ ?_
  intro p ℓ hℓ
  rcases lt_or_eq_of_le (by omega : ℓ ≤ -1) with hlt | heq
  · have hzero : ∀ m : ℤ,
        laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) ℓ = 0 := by
      intro m
      rw [laurentCoeff_shiftDiff hFmero σ _ ℓ]
      obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp (hY.finOrd (p + (m : ℂ) * σ + σ))
      obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp (hY.finOrd (p + (m : ℂ) * σ))
      rw [laurentCoeff_logDeriv_eq_zero_of_le (hY.mero _ (Set.mem_univ _)) hn₁.symm (by omega),
        laurentCoeff_logDeriv_eq_zero_of_le (hY.mero _ (Set.mem_univ _)) hn₂.symm (by omega),
        sub_zero]
    rw [finsum_congr hzero, finsum_zero]
  · subst heq
    have hterm : ∀ m : ℤ,
        laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) (-1)
          = ((shiftOrder Y σ (p + (m : ℂ) * σ) : ℤ) : ℂ) := fun m ↦
      laurentCoeff_shiftDiff_logDeriv hY.mero hY.finOrd σ _
    rw [finsum_congr hterm, ← intCast_finsum]
    have hval : (∑ᶠ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ)) = tripticOrbitCharge Y σ p := rfl
    rw [hval, hcharge p]
    norm_num

/-- **The converse kernel statement, for class members**: differential algebraicity of the
logarithmic derivative forces the orbital charge to vanish on every orbit. -/
theorem tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (hDA : DifferentiallyAlgebraic (toMeromorphicNFOn (logDeriv Y) (Set.univ : Set ℂ)))
    (p : ℂ) : tripticOrbitCharge Y σ p = 0 :=
  tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic hY.mero hY.finOrd hY.periodic
    hY.mixed hτ hσ hindep hindepτ hindepσ hperiods hDA p

/-! ### The root classification -/

/-- **An `m`-th source root modulo differentially algebraic factors**: a class member `Z` such
that `Y/Z^m` has differentially algebraic logarithmic derivative. -/
def HasTripticSourceRoot (τ σ : ℂ) (Y : ℂ → ℂ) (m : ℕ) : Prop :=
  ∃ (Z : ℂ → ℂ) (CstZ : ℂ), TripticMultiplicativeSource τ σ Z CstZ ∧
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (logDeriv fun z ↦ Y z / Z z ^ m) (Set.univ : Set ℂ))

/-- The charge of the root defect `Y/Z^m` is the charge of `Y` minus `m` times the charge of
`Z`. -/
theorem tripticOrbitCharge_root_defect {Z : ℂ → ℂ} {CstZ : ℂ}
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hZ : TripticMultiplicativeSource τ σ Z CstZ)
    (hτ : 0 < τ.im) (hindep : IndepPeriods τ σ) (m : ℕ) (p : ℂ) :
    tripticOrbitCharge (fun z ↦ Y z / Z z ^ m) σ p
      = tripticOrbitCharge Y σ p - m * tripticOrbitCharge Z σ p := by
  have hpow := hZ.pow m
  rw [tripticOrbitCharge_div hY.mero hpow.mero hY.finOrd hpow.finOrd
    (finiteShiftSupport_of_source hY hτ hindep p)
    (finiteShiftSupport_of_source hpow hτ hindep p),
    tripticOrbitCharge_pow hZ.mero hZ.finOrd m]

/-- **The triptic Kummer root criterion, charge form.**  A class member has an `m`-th source root
modulo differentially algebraic factors exactly when `m` divides its orbital charge on every
orbit. -/
theorem hasTripticSourceRoot_iff_dvd_charge
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ)) (m : ℕ) :
    HasTripticSourceRoot τ σ Y m ↔ ∀ p : ℂ, (m : ℤ) ∣ tripticOrbitCharge Y σ p := by
  constructor
  · rintro ⟨Z, CstZ, hZ, hDA⟩
    intro p
    have hA : TripticMultiplicativeSource τ σ (fun z ↦ Y z / Z z ^ m)
        (Cst - (m : ℂ) * CstZ) := hY.div (hZ.pow m)
    have hzero := tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source hA
      hτ hσ hindep hindepτ hindepσ hperiods hDA p
    rw [tripticOrbitCharge_root_defect hY hZ hτ hindep m p] at hzero
    exact ⟨tripticOrbitCharge Z σ p, by linarith [hzero]⟩
  · intro hdvd
    have hfin := finite_support_tripticChargeClass hY hτ
    set E : (ℂ ⧸ tripticPeriodGroup τ σ) →₀ ℤ :=
      integralOrbitDivisorQuotient m (tripticDivisor Y τ σ hfin) with hE
    set Z : ℂ → ℂ := gammaDivisorSource τ σ E with hZdef
    have hZ := tripticMultiplicativeSource_gammaDivisorSource (τ := τ) (σ := σ) hτ hσ E
    have hZcharge : ∀ p : ℂ, tripticOrbitCharge Z σ p = tripticOrbitCharge Y σ p / m := by
      intro p
      rw [hZdef, tripticOrbitCharge_gammaDivisorSource hτ hσ hindep E p, hE]
      have happ : integralOrbitDivisorQuotient m (tripticDivisor Y τ σ hfin)
          (QuotientAddGroup.mk p)
          = tripticDivisor Y τ σ hfin (QuotientAddGroup.mk p) / (m : ℤ) := rfl
      rw [happ, tripticDivisor_mk hY hfin p]
    have hA : TripticMultiplicativeSource τ σ (fun z ↦ Y z / Z z ^ m)
        (Cst - (m : ℂ) * _) := hY.div (hZ.pow m)
    have hAcharge : ∀ p : ℂ, tripticOrbitCharge (fun z ↦ Y z / Z z ^ m) σ p = 0 := by
      intro p
      rw [tripticOrbitCharge_root_defect hY hZ hτ hindep m p, hZcharge p,
        Int.mul_ediv_cancel' (hdvd p), sub_self]
    obtain ⟨-, hDA⟩ := differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source hA
      hτ hσ hindep hindepτ hindepσ hAcharge
    exact ⟨Z, _, hZ, hDA⟩

/-- **Uniqueness of the root class modulo differentially algebraic factors.** -/
theorem tripticSourceRoot_unique
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ)) {m : ℕ} (hm : m ≠ 0)
    {Z₁ Z₂ : ℂ → ℂ} {CstZ₁ CstZ₂ : ℂ}
    (hZ₁ : TripticMultiplicativeSource τ σ Z₁ CstZ₁)
    (hZ₂ : TripticMultiplicativeSource τ σ Z₂ CstZ₂)
    (h₁ : DifferentiallyAlgebraic
      (toMeromorphicNFOn (logDeriv fun z ↦ Y z / Z₁ z ^ m) (Set.univ : Set ℂ)))
    (h₂ : DifferentiallyAlgebraic
      (toMeromorphicNFOn (logDeriv fun z ↦ Y z / Z₂ z ^ m) (Set.univ : Set ℂ))) :
    DifferentiallyAlgebraic
      (toMeromorphicNFOn (logDeriv fun z ↦ Z₁ z / Z₂ z) (Set.univ : Set ℂ)) := by
  have hcharge : ∀ p : ℂ, tripticOrbitCharge Z₁ σ p = tripticOrbitCharge Z₂ σ p := by
    intro p
    have hzero₁ := tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source
      (hY.div (hZ₁.pow m)) hτ hσ hindep hindepτ hindepσ hperiods h₁ p
    have hzero₂ := tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source
      (hY.div (hZ₂.pow m)) hτ hσ hindep hindepτ hindepσ hperiods h₂ p
    rw [tripticOrbitCharge_root_defect hY hZ₁ hτ hindep m p] at hzero₁
    rw [tripticOrbitCharge_root_defect hY hZ₂ hτ hindep m p] at hzero₂
    have hmul : (m : ℤ) * tripticOrbitCharge Z₁ σ p = (m : ℤ) * tripticOrbitCharge Z₂ σ p := by
      linarith [hzero₁, hzero₂]
    exact mul_left_cancel₀ (by exact_mod_cast hm) hmul
  have hquot : TripticMultiplicativeSource τ σ (fun z ↦ Z₁ z / Z₂ z) (CstZ₁ - CstZ₂) :=
    hZ₁.div hZ₂
  have hqcharge : ∀ p : ℂ, tripticOrbitCharge (fun z ↦ Z₁ z / Z₂ z) σ p = 0 := by
    intro p
    rw [tripticOrbitCharge_div hZ₁.mero hZ₂.mero hZ₁.finOrd hZ₂.finOrd
      (finiteShiftSupport_of_source hZ₁ hτ hindep p)
      (finiteShiftSupport_of_source hZ₂ hτ hindep p), hcharge p, sub_self]
  exact (differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source hquot
    hτ hσ hindep hindepτ hindepσ hqcharge).2

/-! ### The content spectrum -/

/-- Divisibility of the orbital charge at every base point is coefficientwise divisibility of the
integral orbit divisor. -/
theorem forall_dvd_charge_iff_coefficientwise
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hfin : (Function.support (tripticChargeClass Y τ σ)).Finite) (m : ℕ) :
    (∀ p : ℂ, (m : ℤ) ∣ tripticOrbitCharge Y σ p)
      ↔ IntegralOrbitDivisorCoefficientwiseDivisible m (tripticDivisor Y τ σ hfin) := by
  constructor
  · intro h g
    exact h (Quotient.out g)
  · intro h p
    have happ := tripticDivisor_mk hY hfin p
    have := h (QuotientAddGroup.mk p)
    rwa [happ] at this

/-- **The triptic Kummer root criterion, content form.**  A class member has an `m`-th source root
modulo differentially algebraic factors exactly when `m` divides the Kummer content of its
integral orbit divisor. -/
theorem hasTripticSourceRoot_iff_content_dvd
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (hfin : (Function.support (tripticChargeClass Y τ σ)).Finite) (m : ℕ) :
    HasTripticSourceRoot τ σ Y m
      ↔ m ∣ integralOrbitDivisorContent (tripticDivisor Y τ σ hfin) := by
  rw [hasTripticSourceRoot_iff_dvd_charge hY hτ hσ hindep hindepτ hindepσ hperiods m,
    forall_dvd_charge_iff_coefficientwise hY hfin m,
    integralOrbitDivisor_coefficientwiseDivisible_iff_content_dvd]

/-- **The content is a root order.**  For a class member with nonzero integral orbit divisor, the
Kummer content of the divisor is realized as a source-root order. -/
theorem hasTripticSourceRoot_content
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (hfin : (Function.support (tripticChargeClass Y τ σ)).Finite) :
    HasTripticSourceRoot τ σ Y (integralOrbitDivisorContent (tripticDivisor Y τ σ hfin)) :=
  (hasTripticSourceRoot_iff_content_dvd hY hτ hσ hindep hindepτ hindepσ hperiods hfin _).mpr
    dvd_rfl

/-- **The exact maximum root order.**  The Kummer content of the integral orbit divisor is a
source-root order, and every source-root order divides it: the content is the maximum root order
of the class member. -/
theorem tripticSource_maximal_root_order
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (hfin : (Function.support (tripticChargeClass Y τ σ)).Finite) :
    HasTripticSourceRoot τ σ Y (integralOrbitDivisorContent (tripticDivisor Y τ σ hfin)) ∧
      ∀ m : ℕ, HasTripticSourceRoot τ σ Y m
        → m ∣ integralOrbitDivisorContent (tripticDivisor Y τ σ hfin) :=
  ⟨hasTripticSourceRoot_content hY hτ hσ hindep hindepτ hindepσ hperiods hfin,
    fun m hm ↦
      (hasTripticSourceRoot_iff_content_dvd hY hτ hσ hindep hindepτ hindepσ hperiods hfin m).mp
        hm⟩

end

end GaloisForLFunctions.HTGeometry
