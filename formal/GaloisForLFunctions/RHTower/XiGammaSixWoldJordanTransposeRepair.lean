import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanPositiveCoherentRepair

/-!
# Positive transposition and additive coherent repair

Reversing every edge of the genuine fixed-left normalized Big-Witt row preserves
positivity, unit trace and the singular one-leg graph limit. It removes the
anchor marginal exactly, and its reciprocal energy tends to zero for every
real coefficient. The raw reversed energy is exactly `A * p` times the squared
norm of the original raw row, giving a fixed numerator bound before division
by its divergent trace mass. Every bounded left-prime range loses its mass.

For every finite packet, its difference from its transpose is explicitly a
finite sum of complete two-point coherent packets. For the actual normalized
row this repair is eventually not any single complete coherent packet, by the
positive retention theorem. Local coherence of the summands does not give the
joint coherence required there. This does not prove fixed-reader agreement
or RH; it exhibits an actual positive source escape under additive assembly.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

def deningerBigWittCrossPairSwap :
    DeningerCalderonWittCrossPrimePacketIndex ≃ DeningerCalderonWittCrossPrimePacketIndex where
  toFun i := ⟨(i.1.2,i.1.1), Ne.symm i.2⟩
  invFun i := ⟨(i.1.2,i.1.1), Ne.symm i.2⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

def deningerBigWittCrossPairTranspose :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ]
      (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ deningerBigWittCrossPairSwap

theorem deningerBigWittCrossPairTranspose_apply
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairTranspose f i = f (deningerBigWittCrossPairSwap i) := by
  rw [deningerBigWittCrossPairTranspose, Finsupp.lmapDomain_apply, Finsupp.mapDomain_equiv_apply]
  rfl

theorem deningerBigWittCrossPairTranspose_single
    (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    deningerBigWittCrossPairTranspose (Finsupp.single i z) =
      Finsupp.single (deningerBigWittCrossPairSwap i) z := by
  simp [deningerBigWittCrossPairTranspose, Finsupp.lmapDomain_apply]

theorem deningerBigWittCrossPairTranspose_trace
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCrossPairTranspose f) =
      deningerBigWittCrossPairAlgebraicOneLegTrace f := by
  have h : deningerBigWittCrossPairAlgebraicOneLegTrace.comp deningerBigWittCrossPairTranspose =
      deningerBigWittCrossPairAlgebraicOneLegTrace := by
    apply Finsupp.lhom_ext
    intro i z
    simp [LinearMap.comp_apply, deningerBigWittCrossPairTranspose_single]
  exact congrArg (fun T => T f) h

theorem deningerBigWittCrossPairTranspose_norm
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairTranspose f)‖ =
      ‖deningerBigWittCrossPairFinitePacketAdmission f‖ := by
  have heq : ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairTranspose f)‖ ^ (2 : ℕ) =
      ‖deningerBigWittCrossPairFinitePacketAdmission f‖ ^ (2 : ℕ) := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    have hfun : (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
        ‖(deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairTranspose f)) i‖ ^ (2 : ℕ)) =
        fun i => ‖(deningerBigWittCrossPairFinitePacketAdmission f) (deningerBigWittCrossPairSwap i)‖ ^ (2 : ℕ) := by
      funext i
      rw [show (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairTranspose f)) i =
          deningerBigWittCrossPairTranspose f i from deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _,
        deningerBigWittCrossPairTranspose_apply,
        show (deningerBigWittCrossPairFinitePacketAdmission f) (deningerBigWittCrossPairSwap i) =
          f (deningerBigWittCrossPairSwap i) from deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _]
    rw [hfun]
    exact deningerBigWittCrossPairSwap.tsum_eq (fun i => ‖(deningerBigWittCrossPairFinitePacketAdmission f) i‖ ^ (2 : ℕ))
  nlinarith [norm_nonneg (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCrossPairTranspose f)),
    norm_nonneg (deningerBigWittCrossPairFinitePacketAdmission f)]

theorem deningerBigWittCoherentTwoPoint_eq
    (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    deningerBigWittCrossPairFiniteRightLegPacket
      (fun p => if p = i.1.1 then (starRingEnd ℂ) z else 0) {i.1.1,i.1.2} =
      Finsupp.single i z - Finsupp.single (deningerBigWittCrossPairSwap i) z := by
  classical
  rcases i with ⟨⟨p,q⟩,hpq⟩
  change p ≠ q at hpq
  simp [deningerBigWittCrossPairFiniteRightLegPacket, deningerBigWittCrossPairRightLeg,
    deningerBigWittCrossPairSwap, hpq, Ne.symm hpq, sub_eq_add_neg]

theorem deningerBigWittTransposeDifference_eq_sum_coherent
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    f - deningerBigWittCrossPairTranspose f =
      ∑ i ∈ f.support, deningerBigWittCrossPairFiniteRightLegPacket
        (fun p => if p = i.1.1 then (starRingEnd ℂ) (f i) else 0) {i.1.1,i.1.2} := by
  classical
  simp_rw [deningerBigWittCoherentTwoPoint_eq,
    ← deningerBigWittCrossPairTranspose_single]
  have hsum : (∑ i ∈ f.support, Finsupp.single i (f i)) = f := Finsupp.sum_single f
  rw [Finset.sum_sub_distrib, ← map_sum, hsum]


def deningerBigWittWoldTransposedRow (a n : ℕ) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  deningerBigWittCrossPairTranspose (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)

theorem deningerBigWittWoldTransposedRow_nonneg (a n : ℕ)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    ∃ w : ℝ, 0 ≤ w ∧ deningerBigWittWoldTransposedRow a n i = (w : ℂ) := by
  classical
  rw [deningerBigWittWoldTransposedRow, deningerBigWittCrossPairTranspose_apply,
    deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, Finsupp.smul_apply,
    smul_eq_mul, deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply]
  split_ifs with h
  · rw [deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.mem_map] at h
    obtain ⟨k,hk,heq⟩ := h
    rw [← heq, deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge]
    refine ⟨(deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1))⁻¹ *
      deningerBigWittWoldFixedLeftRightEdgeWeight a k, ?_, ?_⟩
    · exact mul_nonneg
        (inv_nonneg.mpr (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n).le)
        (deningerBigWittWoldFixedLeftRightEdgeWeight_pos a k).le
    · push_cast
      rfl
  · exact ⟨0, le_rfl, by simp⟩

theorem deningerBigWittWoldTransposedRow_trace (a n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittWoldTransposedRow a n) = 1 := by
  rw [deningerBigWittWoldTransposedRow, deningerBigWittCrossPairTranspose_trace,
    deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeNormalizedPacket]

theorem tendsto_deningerBigWittWoldTransposedRow_ambient (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittWoldTransposedRow a n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [deningerBigWittWoldTransposedRow, deningerBigWittCrossPairTranspose_norm]
  exact tendsto_zero_iff_norm_tendsto_zero.mp
    (tendsto_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeNormalizedPacket a)

theorem tendsto_deningerBigWittWoldTransposedRow_graph (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission (deningerBigWittWoldTransposedRow a n))
      atTop (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have hpair : Tendsto (fun n =>
      (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittWoldTransposedRow a n),
        deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittWoldTransposedRow a n)))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))) := by
    simpa only [nhds_prod_eq] using (tendsto_deningerBigWittWoldTransposedRow_ambient a).prodMk
      (by simpa only [deningerBigWittWoldTransposedRow_trace]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

theorem deningerBigWittWoldNormalizedPacket_zero_off_left (a n : ℕ)
    (i : DeningerCalderonWittCrossPrimePacketIndex) (hi : i.1.1 ≠ nthPrimeSubtype a) :
    deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i = 0 := by
  classical
  have hnot : i ∉ deningerBigWittWoldFixedLeftRightEdgePrefix a (n + 1) :=
    fun h => hi (deningerBigWittWoldFixedLeftRightEdgePrefix_left h)
  simp [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, Finsupp.smul_apply,
    deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply, hnot]

theorem deningerBigWittWoldTransposedRow_zero_on_anchor (a n : ℕ)
    (i : DeningerCalderonWittCrossPrimePacketIndex) (hi : i.1.1 = nthPrimeSubtype a) :
    deningerBigWittWoldTransposedRow a n i = 0 := by
  rw [deningerBigWittWoldTransposedRow, deningerBigWittCrossPairTranspose_apply]
  apply deningerBigWittWoldNormalizedPacket_zero_off_left
  change i.1.2 ≠ nthPrimeSubtype a
  intro h
  exact i.2 (hi.trans h.symm)

set_option backward.isDefEq.respectTransparency false in
theorem deningerBigWittWoldTransposedRow_anchor_marginal (a n : ℕ) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittWoldTransposedRow a n) (nthPrimeSubtype a) = 0 := by
  classical
  rw [deningerBigWittLeftPrimeMarginal, Finsupp.mapDomain, Finsupp.sum_apply]
  change (∑ i ∈ (deningerBigWittWoldTransposedRow a n).support,
    (Finsupp.single i.1.1 (deningerBigWittWoldTransposedRow a n i)) (nthPrimeSubtype a)) = 0
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finsupp.single_apply]
  split_ifs with h
  · exact deningerBigWittWoldTransposedRow_zero_on_anchor a n i h
  · rfl



theorem norm_sq_deningerBigWittFinitePacketAdmission_sum
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission f‖ ^ (2 : ℕ) = ∑ i ∈ f.support, ‖f i‖ ^ (2 : ℕ) := by
  classical
  have hfun : (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖(deningerBigWittCrossPairFinitePacketAdmission f) i‖ ^ (2 : ℕ)) = fun i => ‖f i‖ ^ (2 : ℕ) := by
    funext i
    rw [show (deningerBigWittCrossPairFinitePacketAdmission f) i = f i from
      deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _]
  rw [HilbertSchmidt.lp_norm_sq_eq, hfun]
  exact tsum_eq_sum (fun i hi => by simp [Finsupp.notMem_support_iff.mp hi])

theorem norm_sq_deningerBigWittWoldRawPacket_sum (a n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n)‖ ^ (2 : ℕ) =
      ∑ k ∈ Finset.range n, deningerBigWittWoldFixedLeftRightEdgeWeight a k ^ (2 : ℕ) := by
  classical
  rw [norm_sq_deningerBigWittFinitePacketAdmission_sum]
  have hsupport : (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n).support ⊆
      deningerBigWittWoldFixedLeftRightEdgePrefix a n := by
    intro i hi
    by_contra hn
    apply Finsupp.mem_support_iff.mp hi
    simp [deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply, hn]
  rw [show (∑ i ∈ (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n).support,
        ‖deningerBigWittWoldFixedLeftRightEdgeRawPacket a n i‖ ^ (2 : ℕ)) =
      ∑ i ∈ deningerBigWittWoldFixedLeftRightEdgePrefix a n,
        ‖deningerBigWittWoldFixedLeftRightEdgeRawPacket a n i‖ ^ (2 : ℕ) from
    Finsupp.sum_of_support_subset _ hsupport (fun _ z => ‖z‖ ^ (2 : ℕ)) (by intros; simp)]
  have heq : (∑ i ∈ deningerBigWittWoldFixedLeftRightEdgePrefix a n,
      ‖deningerBigWittWoldFixedLeftRightEdgeRawPacket a n i‖ ^ (2 : ℕ)) =
      ∑ i ∈ deningerBigWittWoldFixedLeftRightEdgePrefix a n,
        ‖deningerBigWittCrossPrimePacketRawCoefficient i‖ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply, if_pos hi]
  rw [heq, deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.sum_map]
  simp [deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge, sq_abs]

theorem deningerBigWittWoldTransposedRaw_energy (A : ℝ) (a n : ℕ) :
    primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittCrossPairTranspose (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n)) =
        ((A * (nthPrimeSubtype a : ℝ) *
          ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  rw [norm_sq_deningerBigWittWoldRawPacket_sum,
    deningerBigWittWoldFixedLeftRightEdgeRawPacket, map_sum, map_sum]
  simp_rw [deningerBigWittCrossPairTranspose_single, primeLabelledEnergyReporter_single]
  rw [deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.sum_map]
  have hterm (k : ℕ) :
      (((A / (nthPrimeSubtype (a + k + 1) : ℝ)) : ℝ) : ℂ) *
          (deningerBigWittWoldFixedLeftRightEdgeWeight a k : ℂ) =
        ((A * (nthPrimeSubtype a : ℝ) * deningerBigWittWoldFixedLeftRightEdgeWeight a k ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hp : (nthPrimeSubtype a : ℝ) ≠ 0 := (nthPrimeSubtype_pos a).ne'
    have hq : (nthPrimeSubtype (a + k + 1) : ℝ) ≠ 0 := (nthPrimeSubtype_pos _).ne'
    have hreal : A / (nthPrimeSubtype (a + k + 1) : ℝ) *
        deningerBigWittWoldFixedLeftRightEdgeWeight a k =
        A * (nthPrimeSubtype a : ℝ) * deningerBigWittWoldFixedLeftRightEdgeWeight a k ^ (2 : ℕ) := by
      rw [deningerBigWittWoldFixedLeftRightEdgeWeight]
      field_simp
    exact_mod_cast hreal
  change (∑ k ∈ Finset.range n,
    (((A / (nthPrimeSubtype (a + k + 1) : ℝ)) : ℝ) : ℂ) *
      deningerBigWittCrossPrimePacketRawCoefficient (deningerBigWittWoldFixedLeftRightEdgeEmbedding a k)) = _
  simp_rw [deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge, hterm]
  rw [Finset.mul_sum]
  push_cast
  rfl

theorem deningerBigWittWoldTransposedRow_energy (A : ℝ) (a n : ℕ) :
    primeLabelledEnergyReporter (fun q => A / (q : ℕ)) (deningerBigWittWoldTransposedRow a n) =
      ((A * (nthPrimeSubtype a : ℝ) *
          ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittWoldFixedLeftRightEdgeRawPacket a (n + 1))‖ ^ (2 : ℕ) /
        deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1) : ℝ) : ℂ) := by
  rw [deningerBigWittWoldTransposedRow, deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket,
    map_smul, map_smul, smul_eq_mul, deningerBigWittWoldTransposedRaw_energy]
  push_cast
  ring

theorem deningerBigWittWoldTransposedRow_energy_norm_le (A : ℝ) (a n : ℕ) :
    ‖primeLabelledEnergyReporter (fun q => A / (q : ℕ)) (deningerBigWittWoldTransposedRow a n)‖ ≤
      (|A| * (nthPrimeSubtype a : ℝ) * ‖deningerBigWittCrossPrimePacketRawHorizon‖ ^ (2 : ℕ)) /
        deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1) := by
  rw [deningerBigWittWoldTransposedRow_energy, Complex.norm_real, Real.norm_eq_abs, abs_div]
  simp only [abs_mul, abs_pow, abs_norm, abs_of_pos (nthPrimeSubtype_pos a),
    abs_of_pos (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n)]
  apply div_le_div_of_nonneg_right _ (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n).le
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg A) (nthPrimeSubtype_pos a).le)
  have hbound := norm_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeRawPacket_le a (n + 1)
  nlinarith [norm_nonneg (deningerBigWittCrossPairFinitePacketAdmission
    (deningerBigWittWoldFixedLeftRightEdgeRawPacket a (n + 1))),
    norm_nonneg deningerBigWittCrossPrimePacketRawHorizon]

theorem tendsto_deningerBigWittWoldTransposedRow_energy (A : ℝ) (a : ℕ) :
    Tendsto (fun n => primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittWoldTransposedRow a n)) atTop (nhds 0) := by
  apply squeeze_zero_norm (deningerBigWittWoldTransposedRow_energy_norm_le A a)
  have hmass : Tendsto
      (fun n => deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1)) atTop atTop :=
    (tendsto_deningerBigWittWoldFixedLeftRightEdgeMass_atTop a).comp
      (Filter.tendsto_add_atTop_nat 1)
  simpa [div_eq_mul_inv] using hmass.inv_tendsto_atTop.const_mul
    (|A| * (nthPrimeSubtype a : ℝ) * ‖deningerBigWittCrossPrimePacketRawHorizon‖ ^ (2 : ℕ))



/-- Although the repair is a finite sum of complete two-point packets, it is eventually
not any one complete coherent packet. The distinction is forced by the actual retained mass. -/
theorem deningerBigWittWoldTransposedRepair_eventually_not_complete (a : ℕ) :
    ∀ᶠ n in atTop, ¬ ∃ (b : Nat.Primes → ℂ) (s : Finset Nat.Primes),
      deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittWoldTransposedRow a n = deningerBigWittCrossPairFiniteRightLegPacket b s := by
  have hbudget := (tendsto_deningerBigWittWoldCoherentRemovalBudget a).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by exact zero_lt_one))
  filter_upwards [hbudget] with n hn
  rintro ⟨b,s,h⟩
  have hrepair : deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
      deningerBigWittCrossPairFiniteRightLegPacket b s = deningerBigWittWoldTransposedRow a n := by
    rw [← h]
    abel
  have hpos : ∀ i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket b s i).re := by
    intro i
    change 0 ≤ ((deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
      deningerBigWittCrossPairFiniteRightLegPacket b s) i).re
    rw [hrepair]
    obtain ⟨w,hw,heq⟩ := deningerBigWittWoldTransposedRow_nonneg a n i
    simpa only [heq, Complex.ofReal_re] using hw
  have hmass := (deningerBigWittWoldPositiveRepair_retained_mass_bound a n b s hpos).1
  rw [hrepair, deningerBigWittWoldTransposedRow_anchor_marginal, Complex.zero_re] at hmass
  linarith



theorem tendsto_deningerBigWittWoldTransposedRow_finite_head
    (a B : ℕ) (hB : 0 < B) :
    Tendsto (fun n => deningerBigWittFiniteLeftHeadMass B (deningerBigWittWoldTransposedRow a n))
      atTop (nhds 0) := by
  have hpos : ∀ n i, 0 ≤ (deningerBigWittWoldTransposedRow a n i).re := by
    intro n i
    obtain ⟨w,hw,heq⟩ := deningerBigWittWoldTransposedRow_nonneg a n i
    simpa only [heq, Complex.ofReal_re] using hw
  exact tendsto_deningerBigWittFiniteLeftHeadMass_of_energy_zero 1 zero_lt_one B hB
    (deningerBigWittWoldTransposedRow a) hpos (tendsto_deningerBigWittWoldTransposedRow_energy 1 a)


end
end RHTower.HedenmalmThetaSource
