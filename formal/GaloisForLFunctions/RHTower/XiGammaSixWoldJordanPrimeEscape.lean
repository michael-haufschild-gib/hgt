import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanParametricVacuity

/-!
# Source-only prime escape and the finite-prime retention bound

Choose the least prefix of the literal Big-Witt row with left prime `p_n`
whose trace is at least `(n+1)(C+1)`, where `C` is the raw horizon norm.
This choice precedes every Xi copy and every scalar energy coefficient.
The normalized positive packets have trace one, ambient norm at most
`1/(n+1)`, and converge to the nonzero vertical one-leg graph class.
Their energy `A/p_n` tends to zero for every `A`, while every bounded range
of left-prime labels eventually leaves the support.

The accompanying retention estimate applies to every nonnegative packet:
`(A/B) * mass(left prime <= B) <= Re E_A` for `A >= 0`. Thus, for `A > 0`,
any zero-energy sequence of nonnegative packets loses its mass from each
bounded prime range. Existence of a source-only zero-output exhaustion
therefore does not force the original defect coefficient to vanish.

These are source constructions and quantitative bounds, not a proof of RH
or of source-to-fixed-physical reader agreement.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

private theorem escape_cutoff_exists (n : ℕ) :
    ∃ k : ℕ, ((n : ℝ) + 1) * (‖deningerBigWittCrossPrimePacketRawHorizon‖ + 1) ≤
      deningerBigWittWoldFixedLeftRightEdgeMass n (k + 1) := by
  have h := (tendsto_deningerBigWittWoldFixedLeftRightEdgeMass_atTop n).comp
    (tendsto_add_atTop_nat 1)
  exact (h.eventually (eventually_ge_atTop _)).exists

/-- Least source prefix meeting the prescribed trace threshold. -/
def deningerBigWittPrimeEscapeCutoff (n : ℕ) : ℕ :=
  Nat.find (escape_cutoff_exists n)

/-- A source-only row schedule, independent of every energy coefficient and Xi copy. -/
def deningerBigWittPrimeEscapePacket (n : ℕ) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket n
    (deningerBigWittPrimeEscapeCutoff n)

/-- Normalization retains exactly unit source trace. -/
theorem deningerBigWittPrimeEscapePacket_trace (n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittPrimeEscapePacket n) = 1 := by
  exact deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeNormalizedPacket _ _


/-- Every packet coefficient is a nonnegative real scalar. -/
theorem deningerBigWittPrimeEscapePacket_nonneg (n : ℕ)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    ∃ w : ℝ, 0 ≤ w ∧ deningerBigWittPrimeEscapePacket n i = (w : ℂ) := by
  classical
  rw [deningerBigWittPrimeEscapePacket,
    deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, Finsupp.smul_apply,
    smul_eq_mul, deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply]
  split_ifs with h
  · rw [deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    rw [deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge]
    refine ⟨(deningerBigWittWoldFixedLeftRightEdgeMass n
        (deningerBigWittPrimeEscapeCutoff n + 1))⁻¹ *
      deningerBigWittWoldFixedLeftRightEdgeWeight n k, ?_, ?_⟩
    · exact mul_nonneg
        (inv_nonneg.mpr (deningerBigWittWoldFixedLeftRightEdgeMass_pos _ _).le)
        (deningerBigWittWoldFixedLeftRightEdgeWeight_pos _ _).le
    · push_cast
      rfl
  · exact ⟨0, le_rfl, by simp⟩

/-- Every supported atom retains the prescribed left prime. -/
theorem deningerBigWittPrimeEscapePacket_support_left (n : ℕ)
    (i : DeningerCalderonWittCrossPrimePacketIndex)
    (hi : deningerBigWittPrimeEscapePacket n i ≠ 0) :
    i.1.1 = nthPrimeSubtype n := by
  classical
  apply deningerBigWittWoldFixedLeftRightEdgePrefix_left
    (a := n) (n := deningerBigWittPrimeEscapeCutoff n + 1)
  by_contra h
  apply hi
  simp [deningerBigWittPrimeEscapePacket,
    deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket,
    deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply, h]

/-- Each bounded range of left-prime labels eventually disappears entirely. -/
theorem deningerBigWittPrimeEscapePacket_finite_left_escape (B : ℕ) :
    ∀ᶠ n in atTop, ∀ i : DeningerCalderonWittCrossPrimePacketIndex,
      (i.1.1 : ℕ) ≤ B → deningerBigWittPrimeEscapePacket n i = 0 := by
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℕ)) atTop atTop :=
    nthPrimeSubtype_strictMono.tendsto_atTop
  filter_upwards [hp.eventually (eventually_gt_atTop B)] with n hn i hi
  by_contra h
  have hleft := deningerBigWittPrimeEscapePacket_support_left n i h
  rw [hleft] at hi
  omega

/-- Quantitative ambient decay from the source trace threshold. -/
theorem deningerBigWittPrimeEscapePacket_norm_le (n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittPrimeEscapePacket n)‖ ≤
      ((n : ℝ) + 1)⁻¹ := by
  let C := ‖deningerBigWittCrossPrimePacketRawHorizon‖
  let M := deningerBigWittWoldFixedLeftRightEdgeMass n (deningerBigWittPrimeEscapeCutoff n + 1)
  have hM : 0 < M := deningerBigWittWoldFixedLeftRightEdgeMass_pos _ _
  have hcut : ((n : ℝ) + 1) * (C + 1) ≤ M :=
    Nat.find_spec (escape_cutoff_exists n)
  have hN : 0 < (n : ℝ) + 1 := by positivity
  calc
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittPrimeEscapePacket n)‖ ≤
      M⁻¹ * C :=
        norm_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeNormalizedPacket_le _ _
    _ = C / M := by ring
    _ ≤ ((n : ℝ) + 1)⁻¹ := by
      apply (div_le_iff₀ hM).2
      apply (le_inv_mul_iff₀ hN).2
      nlinarith

/-- The ambient Hilbert observation tends to zero. -/
theorem tendsto_deningerBigWittPrimeEscapePacket_ambient :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
      (deningerBigWittPrimeEscapePacket n)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    deningerBigWittPrimeEscapePacket_norm_le
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- The singular graph retains the nonzero vertical class. -/
theorem tendsto_deningerBigWittPrimeEscapePacket_graph :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
      (deningerBigWittPrimeEscapePacket n)) atTop
      (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have hpair : Tendsto (fun n =>
      (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittPrimeEscapePacket n),
        deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittPrimeEscapePacket n)))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))) := by
    simpa only [nhds_prod_eq] using tendsto_deningerBigWittPrimeEscapePacket_ambient.prodMk
      (by simpa only [deningerBigWittPrimeEscapePacket_trace]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

/-- Exact energy on the selected source row. -/
theorem deningerBigWittPrimeEscapePacket_energy (A : ℝ) (n : ℕ) :
    primeLabelledEnergyReporter (fun p => A / (p : ℕ)) (deningerBigWittPrimeEscapePacket n) =
      ((A / (nthPrimeSubtype n : ℝ) : ℝ) : ℂ) := by
  exact primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket _ _ _

/-- The same source schedule has zero limiting energy for every scalar coefficient. -/
theorem tendsto_deningerBigWittPrimeEscapePacket_energy (A : ℝ) :
    Tendsto (fun n => primeLabelledEnergyReporter (fun p => A / (p : ℕ))
      (deningerBigWittPrimeEscapePacket n)) atTop (nhds 0) := by
  simp_rw [deningerBigWittPrimeEscapePacket_energy]
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  have h := (tendsto_inv_atTop_zero.comp hp).const_mul A
  have hreal : Tendsto (fun n => A / (nthPrimeSubtype n : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using h
  exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hreal


/-- Real packet mass carried by a bounded range of left-prime labels. -/
def deningerBigWittFiniteLeftHeadMass (B : ℕ)
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) : ℝ :=
  ∑ i ∈ f.support, if (i.1.1 : ℕ) ≤ B then (f i).re else 0

/-- Exact real marginal of the complex energy reporter. -/
theorem primeLabelledEnergyReporter_re_sum (c : Nat.Primes → ℝ)
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    (primeLabelledEnergyReporter c f).re =
      ∑ i ∈ f.support, c i.1.1 * (f i).re := by
  classical
  simp [primeLabelledEnergyReporter, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.toSpanSingleton, Complex.mul_re, mul_comm]

/-- Reciprocal energy bounds every finite-prime mass from below. -/
theorem deningerBigWittFiniteLeftHeadMass_energy_bound
    (A : ℝ) (hA : 0 ≤ A) (B : ℕ)
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (hf : ∀ i, 0 ≤ (f i).re) :
    (A / B) * deningerBigWittFiniteLeftHeadMass B f ≤
      (primeLabelledEnergyReporter (fun p => A / (p : ℕ)) f).re := by
  classical
  rw [deningerBigWittFiniteLeftHeadMass, Finset.mul_sum,
    primeLabelledEnergyReporter_re_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hp : (0 : ℝ) < (i.1.1 : ℕ) := by exact_mod_cast i.1.1.2.pos
  split_ifs with hb
  · apply mul_le_mul_of_nonneg_right _ (hf i)
    exact div_le_div_of_nonneg_left hA hp (by exact_mod_cast hb)
  · simpa using mul_nonneg (div_nonneg hA hp.le) (hf i)

/-- At positive coefficient, zero energy forces escape from every bounded prime range. -/
theorem tendsto_deningerBigWittFiniteLeftHeadMass_of_energy_zero
    (A : ℝ) (hA : 0 < A) (B : ℕ) (hB : 0 < B)
    (u : ℕ → DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (hu : ∀ n i, 0 ≤ (u n i).re)
    (hE : Tendsto (fun n => primeLabelledEnergyReporter (fun p => A / (p : ℕ))
      (u n)) atTop (nhds 0)) :
    Tendsto (fun n => deningerBigWittFiniteLeftHeadMass B (u n)) atTop (nhds 0) := by
  have hcoef : 0 < A / (B : ℝ) := div_pos hA (by exact_mod_cast hB)
  have hreal : Tendsto (fun n =>
      (primeLabelledEnergyReporter (fun p => A / (p : ℕ)) (u n)).re)
      atTop (nhds 0) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp hE
  have hweighted : Tendsto (fun n => (A / B) * deningerBigWittFiniteLeftHeadMass B (u n))
      atTop (nhds 0) := by
    apply squeeze_zero _ _ hreal
    · intro n
      apply mul_nonneg hcoef.le
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact hu n i
      · exact le_rfl
    · intro n
      exact deningerBigWittFiniteLeftHeadMass_energy_bound A hA.le B (u n) (hu n)
  have h := hweighted.const_mul (A / (B : ℝ))⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hcoef.ne', one_mul, mul_zero] using h

end
end RHTower.HedenmalmThetaSource
