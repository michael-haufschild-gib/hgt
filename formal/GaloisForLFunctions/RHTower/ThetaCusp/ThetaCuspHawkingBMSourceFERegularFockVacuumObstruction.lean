import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEQNMRieszShaleRigidity
import GaloisForLFunctions.HTGeometry.BosonicFockOperatorRealization

/-!
# Source-FE regular-Fock vacuum obstruction

HC80 proves that the source-FE beta block repeated along the Birmingham--Mokhtari overtone ladder
is Hilbert--Schmidt exactly on the critical wall, but leaves its regular-Fock interpretation to the
external Shale--Stinespring theorem. HC81 shows that neither damped self-adjoint eigenmodes nor a
bounded Riesz change of basis can evade that obstruction.

This module internalizes the necessity direction directly in the corpus occupation Hilbert space.
For an arbitrary diagonal family `r n`, any nonzero square-summable occupation vector satisfying
the empty-mode two-particle recurrence

`psi (mu + 2 e_n) = r n * psi mu`

must have square-summable `r`. The proof begins at an arbitrary nonzero occupation coefficient, not
at a presumed nonzero vacuum overlap: finitely supported occupations leave an infinite tail of
empty modes, and their two-particle extensions form an injective coefficient slice.

The literal source-FE ratio is constant in overtone. Consequently a nonzero normalizable recurrence
vacuum exists exactly when the pair coefficient and partner occupation vanish, hence exactly on the
critical wall; universal existence is equivalent to RH and to the HB, Deninger/FZZ-P, PW-B, and
canonical-copy RBH receivers.

The recurrence is a necessary coefficient slice of the transformed annihilation equation. This
module does not define its full unbounded operators or exclude extended/nonregular Fock spaces.

`[NEW] [DIAGONAL SHALE NECESSITY] [FOCK-VACUUM NO-GO] [RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex Real
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Square summability of the coefficients of a concrete occupation-Hilbert vector. -/
theorem summable_sq_bosonicFock (ψ : HTGeometry.BosonicFock ℕ) :
    Summable (fun μ : ℕ →₀ ℕ => ‖ψ μ‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp (lp.memℓp ψ)
  refine h.congr ?_
  intro μ
  rw [show ((2 : ENNReal).toReal) = (2 : ℕ) by norm_num, Real.rpow_natCast]

/-- Any nonzero normalizable occupation vector satisfying diagonal empty-mode pair recurrences
forces square summability of the full ratio family. -/
theorem summable_sq_ratio_of_bosonicFock_emptyModePairRecurrence
    (r : ℕ → ℂ) (ψ : HTGeometry.BosonicFock ℕ) (hψ : ψ ≠ 0)
    (hrec : ∀ (μ : ℕ →₀ ℕ) (n : ℕ), μ n = 0 →
      ψ (μ + Finsupp.single n 2) = r n * ψ μ) :
    Summable (fun n : ℕ => ‖r n‖ ^ 2) := by
  have hex : ∃ μ : ℕ →₀ ℕ, ψ μ ≠ 0 := by
    by_contra h
    have hall : ∀ μ : ℕ →₀ ℕ, ψ μ = 0 := by
      intro μ
      by_contra hμ
      exact h ⟨μ, hμ⟩
    apply hψ
    apply lp.ext
    funext μ
    simpa using hall μ
  obtain ⟨μ, hμ⟩ := hex
  let M : ℕ := μ.support.sup (fun n : ℕ => n)
  let j : ℕ → ℕ := fun k => M + 1 + k
  have hj_zero (k : ℕ) : μ (j k) = 0 := by
    by_contra hne
    have hmem : j k ∈ μ.support := Finsupp.mem_support_iff.mpr hne
    have hle : j k ≤ μ.support.sup (fun n : ℕ => n) :=
      Finset.le_sup (f := fun n : ℕ => n) hmem
    dsimp [j, M] at hle
    omega
  have hj_inj : Function.Injective j := by
    intro k l hkl
    dsimp [j] at hkl
    omega
  let f : ℕ → (ℕ →₀ ℕ) := fun k => μ + Finsupp.single (j k) 2
  have hf_inj : Function.Injective f := by
    intro k l hkl
    by_contra hne
    have hjne : j k ≠ j l := fun h => hne (hj_inj h)
    have hev := congrArg (fun ν : ℕ →₀ ℕ => ν (j k)) hkl
    simp [f, hj_zero k, hjne] at hev
  have hsf : Summable (fun k : ℕ => ‖ψ (f k)‖ ^ 2) := by
    simpa [Function.comp_def] using
      (summable_sq_bosonicFock ψ).comp_injective hf_inj
  have hcoeff (k : ℕ) : ψ (f k) = r (j k) * ψ μ := by
    simpa [f] using hrec μ (j k) (hj_zero k)
  have hprod : Summable (fun k : ℕ => ‖r (j k) * ψ μ‖ ^ 2) :=
    hsf.congr (fun k => by rw [hcoeff k])
  have hμnorm : ‖ψ μ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hμ)
  have htail : Summable (fun k : ℕ => ‖r (j k)‖ ^ 2) := by
    have hscaled := hprod.mul_left (‖ψ μ‖ ^ 2)⁻¹
    refine hscaled.congr (fun k => ?_)
    rw [norm_mul, mul_pow]
    field_simp
  rw [← summable_nat_add_iff (M + 1)]
  simpa [j, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail

/-- A nonzero constant empty-mode pair recurrence has no normalizable occupation vector. -/
theorem bosonicFock_eq_zero_of_emptyModePairRecurrence
    (r : ℂ) (hr : r ≠ 0) (ψ : HTGeometry.BosonicFock ℕ)
    (hrec : ∀ (μ : ℕ →₀ ℕ) (n : ℕ), μ n = 0 →
      ψ (μ + Finsupp.single n 2) = r * ψ μ) :
    ψ = 0 := by
  by_contra hψ
  have hs : Summable (fun _n : ℕ => ‖r‖ ^ 2) :=
    summable_sq_ratio_of_bosonicFock_emptyModePairRecurrence
      (fun _n : ℕ => r) ψ hψ (by simpa using hrec)
  have hzsq : ‖r‖ ^ 2 = 0 := (summable_const_iff _).mp hs
  exact hr (norm_eq_zero.mp (sq_eq_zero_iff.mp hzsq))

/-- Existence of a nonzero normalizable empty-mode recurrence vector is exactly zero ratio. -/
theorem exists_bosonicFock_emptyModePairRecurrence_iff (r : ℂ) :
    (∃ ψ : HTGeometry.BosonicFock ℕ,
      ψ ≠ 0 ∧
        ∀ (μ : ℕ →₀ ℕ) (n : ℕ), μ n = 0 →
          ψ (μ + Finsupp.single n 2) = r * ψ μ) ↔
      r = 0 := by
  constructor
  · rintro ⟨ψ, hψ, hrec⟩
    by_contra hr
    exact hψ (bosonicFock_eq_zero_of_emptyModePairRecurrence r hr ψ hrec)
  · intro hr
    let vacuum : HTGeometry.BosonicFock ℕ :=
      lp.single 2 (0 : ℕ →₀ ℕ) (1 : ℂ)
    refine ⟨vacuum, ?_, ?_⟩
    · intro hvac
      have hev := congrArg (fun ψ : HTGeometry.BosonicFock ℕ => ψ (0 : ℕ →₀ ℕ)) hvac
      simp [vacuum, lp.single_apply] at hev
    · intro μ n hμ
      have hocc : μ + Finsupp.single n 2 ≠ 0 := by
        intro hzero
        have hev := congrArg (fun ν : ℕ →₀ ℕ => ν n) hzero
        simp [hμ] at hev
      simp [vacuum, lp.single_apply, hocc, hr]

/-- Positive Bogoliubov sheet coefficient never vanishes. -/
theorem hbXiPeierlsUnitSourceFEOrbitBogoliubovGain_pos (q : XiZeroCopy) :
    0 < hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q := by
  rw [hbXiPeierlsUnitSourceFEOrbitBogoliubovGain]
  exact Real.sqrt_pos.2
    (lt_of_lt_of_le zero_lt_one
      (hbXiPeierlsUnitSourceFEOrbitExpandingGain_ge_one q))

/-- Normalized two-particle coefficient forced by the transformed annihilation equation on an
empty mode. -/
def hbXiPeierlsUnitSourceFEFockVacuumPairRatio (q : XiZeroCopy) : ℂ :=
  -hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q /
    ((Real.sqrt 2 : ℂ) * (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q : ℂ))

theorem hbXiPeierlsUnitSourceFEFockVacuumPairRatio_denominator_ne_zero
    (q : XiZeroCopy) :
    (Real.sqrt 2 : ℂ) * (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain q : ℂ) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  · exact_mod_cast (ne_of_gt (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain_pos q))

/-- Normalized recurrence ratio vanishes exactly when the source pair coefficient vanishes. -/
theorem hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEFockVacuumPairRatio q = 0 ↔
      hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q = 0 := by
  simp [hbXiPeierlsUnitSourceFEFockVacuumPairRatio,
    hbXiPeierlsUnitSourceFEFockVacuumPairRatio_denominator_ne_zero q]

/-- A regular source-FE transformed vacuum is a nonzero occupation-Hilbert vector satisfying the
necessary empty-mode two-particle slice of the transformed annihilation equation. -/
def HBXiPeierlsUnitSourceFEHasRegularFockVacuum (q : XiZeroCopy) : Prop :=
  ∃ ψ : HTGeometry.BosonicFock ℕ,
    ψ ≠ 0 ∧
      ∀ (μ : ℕ →₀ ℕ) (n : ℕ), μ n = 0 →
        ψ (μ + Finsupp.single n 2) =
          hbXiPeierlsUnitSourceFEFockVacuumPairRatio q * ψ μ

/-- Existence of a regular recurrence vacuum is exactly vanishing pair amplitude. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_pair_eq_zero
    (q : XiZeroCopy) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q = 0 := by
  exact (exists_bosonicFock_emptyModePairRecurrence_iff
    (hbXiPeierlsUnitSourceFEFockVacuumPairRatio q)).trans
      (hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero q)

/-- Existence of a regular recurrence vacuum is exactly partner vacuum. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero
    (q : XiZeroCopy) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_pair_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero q)

/-- A nonzero normalizable source-FE recurrence vacuum exists exactly on the critical wall. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_re_eq_half
    (q : XiZeroCopy) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      (q.1 : ℂ).re = 1 / 2 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q)

/-- An off-wall source orbit has no nonzero normalizable vector satisfying even the empty-mode
pair slice of the transformed vacuum equation. -/
theorem not_hbXiPeierlsUnitSourceFEHasRegularFockVacuum_of_offWall
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ HBXiPeierlsUnitSourceFEHasRegularFockVacuum q :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_re_eq_half q).not.mpr hq

/-- Universal existence of regular source-FE recurrence vacua. -/
def HBXiPeierlsUnitSourceFEGlobalRegularFockVacuum : Prop :=
  ∀ q : XiZeroCopy, HBXiPeierlsUnitSourceFEHasRegularFockVacuum q

/-- Universal regular-Fock vacuum existence is exactly RH. -/
theorem hbXiPeierlsUnitSourceFEGlobalRegularFockVacuum_iff_rh :
    HBXiPeierlsUnitSourceFEGlobalRegularFockVacuum ↔ RiemannHypothesis := by
  rw [HBXiPeierlsUnitSourceFEGlobalRegularFockVacuum,
    ← forall_hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_rh]
  exact forall_congr' fun q =>
    hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero q

/-- Regular source-FE Fock-vacuum existence is HB optical darkness. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_opticalPower_zero
    (n : ℕ) (q : XiZeroCopy) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_opticalPower_zero n q)

/-- Regular source-FE Fock-vacuum existence is Deninger Ward cancellation. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_sharedWardCharge_zero
    (n : ℕ) (q : XiZeroCopy) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_sharedWardCharge_zero n q)

/-- Regular source-FE Fock-vacuum existence is FZZ-P information equilibrium. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_informationForce_zero
    (n : ℕ) (q : XiZeroCopy) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_informationForce_zero n q)

/-- Regular source-FE Fock-vacuum existence is every-grade PW-B balance. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_pwBalance_zero
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum q ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_pwBalance_zero n q k)

/-- On the canonical divisor copy, regular source-FE Fock-vacuum existence is RBH balance. -/
theorem hbXiPeierlsUnitSourceFEHasRegularFockVacuum_firstCopy_iff_rbhBalance_zero
    (n : ℕ) (rho : XiDivisorSupport) :
    HBXiPeierlsUnitSourceFEHasRegularFockVacuum
        (reflectedBiHeatFirstDivisorCopy rho) ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 :=
  (hbXiPeierlsUnitSourceFEHasRegularFockVacuum_iff_partnerNumber_eq_zero
    (reflectedBiHeatFirstDivisorCopy rho)).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_firstCopy_eq_zero_iff_rbhBalance_zero n rho)

end

end RHTower
