import GaloisForLFunctions.RHTower.FermiNymanWeightedSignature
import GaloisForLFunctions.RHTower.FermiNymanCorrelationJets

/-!
# Weighted correlation cancellation and the multiplicity upper bound

For `0 ≤ a < 1`, weighted square integrability supplies the Mellin boundary rate.
Vanishing correlation jets at all actual zeros in `1-a < Re ρ < 1` clears every
possible defect pole and forces dyadic self-similarity. Such witnesses are neutral
for the matched weighted form. Negative witness families therefore inject into
those multiplicity coordinates, with no finite-zero assumption.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- The actual zeta zeros admitted at a weighted Mellin threshold. -/
def weightedStripZeros (a : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 1 - a < ρ.re ∧ ρ.re < 1}

def weightedStripMultiplicity {a : ℝ} (ρ : weightedStripZeros a) : ℕ :=
  (analyticOrderAt riemannZeta (ρ : ℂ)).toNat

theorem weightedStripMultiplicity_coe {a : ℝ} (ρ : weightedStripZeros a) :
    (weightedStripMultiplicity ρ : ℕ∞) = analyticOrderAt riemannZeta (ρ : ℂ) := by
  apply ENat.coe_toNat
  have hρ : (ρ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith [ρ.2.2.2]
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (x := 2) (by simp) (by simpa using hρ)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num : 1 < (2 : ℂ).re)))]
  exact ENat.zero_ne_top

def weightedStripMultiplicityCount (a : ℝ) : ℕ∞ :=
  ⨆ s : Finset (weightedStripZeros a), ((∑ ρ ∈ s, weightedStripMultiplicity ρ : ℕ) : ℕ∞)

theorem IsWeightedFermiWitness.conjugateMellinWitness {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {w : ℝ → ℂ} (hw : IsWeightedFermiWitness a w) :
    IsMellinFermiWitness (fun t => (starRingEnd ℂ) (w t)) a := by
  refine ⟨Complex.continuous_conj.comp_continuousOn hw.1, ha0, ha1, ?_, hw.2.2⟩
  intro x hx
  simpa only [Complex.norm_conj] using hw.integrableOn_mellinMajorant hx

theorem IsWeightedFermiWitness.majorant_rate {a : ℝ} {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) {x : ℝ} (hx : a < x) :
    witnessMajorant w x ≤
      ((1 + ∫ t in Ioc (0 : ℝ) 1, ‖fermiWeightTwist a w t‖ ^ 2) / 2) /
        Real.sqrt (x - a) := by
  have h := witnessMajorant_le_of_sq (continuousOn_fermiWeightTwist a hw.1)
    hw.integrableOn_normSq_twist (x := x - a + 1 / 2) (by linarith)
  have heq : witnessMajorant w x = witnessMajorant (fermiWeightTwist a w) (x - a + 1 / 2) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => weightedMellinIntegrand_eq_twist a x w ht.1)
  rw [← heq] at h
  have hS : 0 ≤ 1 + ∫ t in Ioc (0 : ℝ) 1, ‖fermiWeightTwist a w t‖ ^ 2 := by
    have hnonneg : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, ‖fermiWeightTwist a w t‖ ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc (fun t (_ : t ∈ Ioc (0 : ℝ) 1) =>
      sq_nonneg ‖fermiWeightTwist a w t‖)
    linarith
  have hsqrt : Real.sqrt (x - a) ≤ Real.sqrt (2 * (x - a + 1 / 2) - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < Real.sqrt (x - a) := Real.sqrt_pos.2 (by linarith)
  refine h.trans ?_
  rw [div_div]
  exact div_le_div_of_nonneg_left hS (by positivity)
    (mul_le_mul_of_nonneg_left hsqrt (by norm_num))

theorem IsWeightedFermiWitness.selfSimilar_of_removable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {w : ℝ → ℂ} (hw : IsWeightedFermiWitness a w)
    (hRem : ∀ z : ℂ, z.re < a → zetaEntire (1 - z) = 0 →
      0 ≤ meromorphicOrderAt (dyadicDefectLeft (fun t => (starRingEnd ℂ) (w t))) z)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  have hv := hw.conjugateMellinWitness ha0 ha1
  have h := hv.selfSimilar_of_removable (B :=
    (1 + ∫ t in Ioc (0 : ℝ) 1, ‖fermiWeightTwist a w t‖ ^ 2) / 2)
    (fun x hx _ => by simpa only [witnessMajorant, Complex.norm_conj] using hw.majorant_rate hx)
    hRem ht
  simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) h

theorem IsWeightedFermiWitness.analyticAt_fermiCorrelation {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {w : ℝ → ℂ} (hw : IsWeightedFermiWitness a w) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fermiCorrelation w) s := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
    (fun z hz => (hw.conjugateMellinWitness ha0 ha1).differentiableAt_correlationMellin hz
      |>.differentiableWithinAt)
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs

theorem IsWeightedFermiWitness.selfSimilar_of_correlation_order {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {w : ℝ → ℂ} (hw : IsWeightedFermiWitness a w)
    (hord : ∀ ρ : weightedStripZeros a,
      analyticOrderAt riemannZeta (ρ : ℂ) ≤ analyticOrderAt (fermiCorrelation w) (ρ : ℂ))
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  apply hw.selfSimilar_of_removable ha0 ha1 ?_ ht
  intro z hz hzero
  have hthreshold : 1 - a < (1 - z).re := by simp; linarith
  have hone : (1 - z).re < 1 := by
    by_contra hn
    exact Sieve.zetaEntire_ne_zero_of_one_le_re (le_of_not_gt hn) hzero
  have hne : (1 : ℂ) - z ≠ 1 := by
    intro h
    rw [h] at hone
    norm_num at hone
  have hζ : riemannZeta (1 - z) = 0 := by
    rw [zetaEntire_eq hne] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  let ρ : weightedStripZeros a := ⟨1 - z, hζ, hthreshold, hone⟩
  let N : ℂ → ℂ := fun u =>
    -((2 : ℂ) ^ (-u)) * u * (1 - u) * fermiCorrelation w (1 - u)
  let D : ℂ → ℂ := fun u => zetaEntire (1 - u)
  have hN : AnalyticAt ℂ N z := analyticAt_leftNumerator
    (hw.conjugateMellinWitness ha0 ha1) (by linarith : z.re < 1)
  have hD : AnalyticAt ℂ D z :=
    (differentiable_zetaEntire.analyticAt (1 - z)).comp (analyticAt_const.sub analyticAt_id)
  have hDO : analyticOrderAt D z = analyticOrderAt riemannZeta (1 - z) := by
    rw [analyticOrderAt_one_sub_local, analyticOrderAt_zetaEntire_of_ne_one hne]
  have hDf : analyticOrderAt D z ≠ ⊤ := by
    rw [hDO, ← weightedStripMultiplicity_coe ρ]
    exact WithTop.coe_ne_top
  have hP : AnalyticAt ℂ (fun u : ℂ => -((2 : ℂ) ^ (-u)) * u * (1 - u)) z := by
    have hpow : Differentiable ℂ (fun u : ℂ => (2 : ℂ) ^ (-u)) := fun _ =>
      (differentiableAt_id.neg).const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    exact (((hpow.analyticAt z).neg.mul analyticAt_id).mul
      (analyticAt_const.sub analyticAt_id))
  have hF : AnalyticAt ℂ (fun u => fermiCorrelation w (1 - u)) z :=
    (hw.analyticAt_fermiCorrelation ha0 ha1 (by linarith [hthreshold])).comp
      (analyticAt_const.sub analyticAt_id)
  have hNF : analyticOrderAt (fermiCorrelation w) (1 - z) ≤ analyticOrderAt N z := by
    change _ ≤ analyticOrderAt
      ((fun u : ℂ => -((2 : ℂ) ^ (-u)) * u * (1 - u)) *
        (fun u => fermiCorrelation w (1 - u))) z
    rw [analyticOrderAt_mul hP hF, analyticOrderAt_one_sub_local]
    exact le_add_of_nonneg_left zero_le
  change 0 ≤ meromorphicOrderAt (fun u => N u / D u) z
  exact meromorphicOrderAt_div_nonneg_of_order_le hN hD hDf
    (by rw [hDO]; exact le_trans (hord ρ) hNF)


/-- Self-similar pairs are neutral for the matched weighted subtraction. -/
theorem weightedDyadicForm_eq_zero_of_selfSimilar (a : ℝ) (u v : ℝ → ℂ)
    (hu : ∀ t ∈ Ioc (0 : ℝ) 1, u (t / 2) = u t)
    (hv : ∀ t ∈ Ioc (0 : ℝ) 1, v (t / 2) = v t) :
    weightedDyadicForm a u v = 0 := by
  let F : ℝ → ℂ := fun t => (t ^ (2 * a - 1) : ℝ) * u t * (starRingEnd ℂ) (v t)
  have hscale : ∀ t ∈ Ioc (0 : ℝ) 1,
      F (t / 2) = ((2 * (2 : ℝ) ^ (-2 * a) : ℝ) : ℂ) * F t := by
    intro t ht
    have hp : (t / 2) ^ (2 * a - 1) =
        (2 * (2 : ℝ) ^ (-2 * a)) * t ^ (2 * a - 1) := by
      rw [Real.div_rpow ht.1.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show -(2 * a - 1) = 1 + (-2 * a) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring
    simp only [F, hu t ht, hv t ht, hp, Complex.ofReal_mul]
    ring
  have heq := integral_Ioc_comp_half F
  have hi : (∫ t in Ioc (0 : ℝ) 1, F (t / 2)) =
      ((2 * (2 : ℝ) ^ (-2 * a) : ℝ) : ℂ) * ∫ t in Ioc (0 : ℝ) 1, F t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc hscale
  rw [hi] at heq
  unfold weightedDyadicForm
  change (∫ t in Ioc (0 : ℝ) (1 / 2), F t) -
    ((2 : ℝ) ^ (-2 * a) : ℝ) * ∫ t in Ioc (0 : ℝ) 1, F t = 0
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.real_smul] at heq
  linear_combination -(1 / 2 : ℂ) * heq

theorem IsWeightedFermiWitness.mellinRapid_correlationDensity {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) :
    MellinRapid (witnessCorrelation (fun t => (starRingEnd ℂ) (w t))) := by
  let v : ℝ → ℂ := fun t => (starRingEnd ℂ) (w t)
  have hv := hw.conjugateMellinWitness ha0 ha1
  let M : ℝ := 3 * witnessMajorant v 1
  have hbound : ∀ t, ‖witnessCorrelation v t‖ ≤ M := hv.norm_witnessCorrelation_le
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbound 0)
  have hi : IntegrableOn (witnessCorrelation v) (Ioi (0 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    refine IntegrableOn.union ?_ ?_
    · exact Measure.integrableOn_of_bounded (M := M)
        measure_Ioc_lt_top.ne hv.aestronglyMeasurable_witnessCorrelation
        (Eventually.of_forall hbound)
    · refine integrableOn_zero.congr_fun (fun t ht => ?_) measurableSet_Ioi
      exact (hv.witnessCorrelation_eq_zero ht.le).symm
  refine ⟨hi.locallyIntegrableOn, fun a => ?_, fun b hb => ?_⟩
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [hv.witnessCorrelation_eq_zero ht, norm_zero, zero_mul]
  · refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)]
    exact (hbound t).trans (le_mul_of_one_le_right hM
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (by linarith)))

theorem weightedFermiWitnessCorrelation_sum {a : ℝ} (ha1 : a < 1) {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (c : ι → ℂ) (hw : ∀ i, IsWeightedFermiWitness a (w i)) (b : ℝ) :
    witnessCorrelation (fun t => (starRingEnd ℂ) (∑ i, c i * w i t)) b =
      ∑ i, (starRingEnd ℂ) (c i) *
        witnessCorrelation (fun t => (starRingEnd ℂ) (w i t)) b := by
  classical
  simp_rw [witnessCorrelation_eq, map_sum, map_mul]
  have hexp : ∀ t, fermiNymanGen b t *
      (∑ i, (starRingEnd ℂ) (c i) * (starRingEnd ℂ) (w i t)) =
      ∑ i, (starRingEnd ℂ) (c i) *
        (fermiNymanGen b t * (starRingEnd ℂ) (w i t)) := by
    intro t
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ =>
    ((hw i).integrableOn_mul_conj ha1 (measurable_fermiNymanGen b)
      (norm_fermiNymanGen_le b)).const_mul _)]
  exact Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)

theorem weightedFermiCorrelation_sum {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (c : ι → ℂ) (hw : ∀ i, IsWeightedFermiWitness a (w i))
    {s : ℂ} (hs : 0 < s.re) :
    fermiCorrelation (fun t => ∑ i, c i * w i t) s =
      ∑ i, (starRingEnd ℂ) (c i) * fermiCorrelation (w i) s := by
  have hI : ∀ i, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
      witnessCorrelation (fun u => (starRingEnd ℂ) (w i u)) t) (Ioi 0) :=
    fun i => ((hw i).mellinRapid_correlationDensity ha0 ha1).mellinConvergent hs
  unfold fermiCorrelation correlationMellin mellin
  have hexp : ∀ t : ℝ, (t : ℂ) ^ (s - 1) •
      witnessCorrelation (fun u => (starRingEnd ℂ) (∑ i, c i * w i u)) t =
      ∑ i, (starRingEnd ℂ) (c i) * ((t : ℂ) ^ (s - 1) •
        witnessCorrelation (fun u => (starRingEnd ℂ) (w i u)) t) := by
    intro t
    rw [weightedFermiWitnessCorrelation_sum ha1 w c hw]
    simp only [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => (hI i).const_mul _)]
  exact Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)

theorem weightedFermiCorrelationJet_sum {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (c : ι → ℂ) (hw : ∀ i, IsWeightedFermiWitness a (w i))
    {ρ : ℂ} (hρ : 0 < ρ.re) (j : ℕ) :
    fermiCorrelationJet (fun t => ∑ i, c i * w i t) ρ j =
      ∑ i, c i * fermiCorrelationJet (w i) ρ j := by
  have hev : fermiCorrelation (fun t => ∑ i, c i * w i t) =ᶠ[𝓝 ρ]
      (fun s => ∑ i, (starRingEnd ℂ) (c i) * fermiCorrelation (w i) s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ] with s hs
    exact weightedFermiCorrelation_sum ha0 ha1 w c hw hs
  unfold fermiCorrelationJet
  rw [hev.iteratedDeriv_eq j, iteratedDeriv_fun_sum
    (f := fun i s => (starRingEnd ℂ) (c i) * fermiCorrelation (w i) s)
    (I := Finset.univ)
    (fun i _ => (analyticAt_const.mul ((hw i).analyticAt_fermiCorrelation ha0 ha1 hρ)).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field, map_sum, map_mul, Complex.conj_conj]

def weightedFermiMultiplicityJetPacket (a : ℝ) (w : ℝ → ℂ) :
    (Σ ρ : weightedStripZeros a, Fin (weightedStripMultiplicity ρ)) → ℂ :=
  fun p => fermiCorrelationJet w p.1 p.2

theorem IsWeightedFermiWitness.selfSimilar_of_jetPacket_eq_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) (hJ : weightedFermiMultiplicityJetPacket a w = 0)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  apply hw.selfSimilar_of_correlation_order ha0 ha1 ?_ ht
  intro ρ
  rw [← weightedStripMultiplicity_coe ρ]
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hw.analyticAt_fermiCorrelation ha0 ha1 (by linarith [ρ.2.2.1]))).mpr
  intro j hj
  have h := congrFun hJ ⟨ρ, ⟨j, hj⟩⟩
  have h' := congrArg (starRingEnd ℂ) h
  simpa [weightedFermiMultiplicityJetPacket, fermiCorrelationJet] using h'

theorem weightedDyadicForm_self_eq_zero_of_jetPacket_eq_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) (hJ : weightedFermiMultiplicityJetPacket a w = 0) :
    weightedDyadicForm a w w = 0 := by
  exact weightedDyadicForm_eq_zero_of_selfSimilar a w w
    (fun t ht => hw.selfSimilar_of_jetPacket_eq_zero ha0 ha1 hJ ht)
    (fun t ht => hw.selfSimilar_of_jetPacket_eq_zero ha0 ha1 hJ ht)

theorem weightedDyadicForm_negative_family_sum {a : ℝ} {n : ℕ} (v : Fin n → ℝ → ℂ)
    (hv : ∀ i, IsWeightedFermiWitness a (v i))
    (hq : ∀ i j, weightedDyadicForm a (v i) (v j) = if i = j then -1 else 0) (c : Fin n → ℂ) :
    weightedDyadicForm a (fun t => ∑ i, c i * v i t) (fun t => ∑ i, c i * v i t) =
      -((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
  rw [weightedDyadicForm_sum_sum v c c (fun i j => (hv i).integrableOn_weighted_mul_conj (hv j))]
  simp only [hq, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_neg_distrib]
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_sum]

theorem weightedCoefficients_eq_zero_of_negative_family_jetPacket_eq_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {n : ℕ}
    (v : Fin n → ℝ → ℂ) (hv : ∀ i, IsWeightedFermiWitness a (v i))
    (hq : ∀ i j, weightedDyadicForm a (v i) (v j) = if i = j then -1 else 0) (c : Fin n → ℂ)
    (hc : weightedFermiMultiplicityJetPacket a (fun t => ∑ i, c i * v i t) = 0) : c = 0 := by
  have hW : IsWeightedFermiWitness a (fun t => ∑ i, c i * v i t) :=
    isWeightedFermiWitness_finsetSum ha1 Finset.univ v c (fun i _ => hv i)
  have h0 := weightedDyadicForm_self_eq_zero_of_jetPacket_eq_zero ha0 ha1 hW hc
  rw [weightedDyadicForm_negative_family_sum v hv hq c] at h0
  have hsum : ∑ i, ‖c i‖ ^ 2 = 0 := by
    have h := congrArg Complex.re h0
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.zero_re] at h
    linarith
  funext i
  have hle : ‖c i‖ ^ 2 ≤ ∑ j, ‖c j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖c j‖) (Finset.mem_univ i)
  rw [hsum] at hle
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (c i)])

theorem weightedNegOrthonormalFamily_card_le_multiplicity {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) [Fintype (weightedStripZeros a)] {n : ℕ}
    (hfamily : IsWeightedNegOrthonormalWitnessFamily a n) :
    n ≤ ∑ ρ : weightedStripZeros a, weightedStripMultiplicity ρ := by
  classical
  obtain ⟨v, hv, hq⟩ := hfamily
  let J := Σ ρ : weightedStripZeros a, Fin (weightedStripMultiplicity ρ)
  let L : (Fin n → ℂ) →ₗ[ℂ] (J → ℂ) :=
    { toFun := fun c p => ∑ i, c i * weightedFermiMultiplicityJetPacket a (v i) p
      map_add' := by
        intro c d
        funext p
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
          RingHom.id_apply] }
  have hker : LinearMap.ker L = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply weightedCoefficients_eq_zero_of_negative_family_jetPacket_eq_zero ha0 ha1 v hv hq c
    have hJ : weightedFermiMultiplicityJetPacket a (fun t => ∑ i, c i * v i t) = L c := by
      funext p
      exact weightedFermiCorrelationJet_sum ha0 ha1 v c hv (by linarith [p.1.2.2.1]) p.2
    exact hJ.trans hc
  have hdim := L.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  simpa only [J, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_sigma,
    Fintype.card_fin] using hdim

theorem weightedStripMultiplicity_pos {a : ℝ} (ρ : weightedStripZeros a) : 0 < weightedStripMultiplicity ρ := by
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith [ρ.2.2.2]
  have horder : analyticOrderAt riemannZeta (ρ : ℂ) ≠ 0 :=
    (analyticOn_riemannZeta (ρ : ℂ) hne).analyticOrderAt_ne_zero.mpr ρ.2.1
  apply Nat.pos_of_ne_zero
  intro hm
  apply horder
  rw [← weightedStripMultiplicity_coe ρ, hm]
  rfl

theorem weightedStripMultiplicityCount_eq_sum (a : ℝ) [Fintype (weightedStripZeros a)] :
    weightedStripMultiplicityCount a = ((∑ ρ : weightedStripZeros a, weightedStripMultiplicity ρ : ℕ) : ℕ∞) := by
  classical
  apply le_antisymm
  · refine iSup_le fun s => ?_
    exact_mod_cast (Finset.sum_le_sum_of_subset (Finset.subset_univ s) :
      ∑ ρ ∈ s, weightedStripMultiplicity ρ ≤ ∑ ρ : weightedStripZeros a, weightedStripMultiplicity ρ)
  · exact le_iSup_of_le (Finset.univ : Finset (weightedStripZeros a)) le_rfl

theorem weightedStripMultiplicityCount_eq_top {a : ℝ} [Infinite (weightedStripZeros a)] :
    weightedStripMultiplicityCount a = ⊤ := by
  classical
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  obtain ⟨s, hcard⟩ := Finset.exists_card_eq (α := weightedStripZeros a) n
  have hs : s.card ≤ ∑ ρ ∈ s, weightedStripMultiplicity ρ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun ρ _ => Nat.succ_le_of_lt (weightedStripMultiplicity_pos ρ))
  calc
    (n : ℕ∞) = (s.card : ℕ∞) := by rw [hcard]
    _ ≤ ((∑ ρ ∈ s, weightedStripMultiplicity ρ : ℕ) : ℕ∞) := by exact_mod_cast hs
    _ ≤ weightedStripMultiplicityCount a := le_iSup_of_le s le_rfl

theorem weightedWitnessNegIndex_le_weightedStripMultiplicityCount {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    weightedWitnessNegIndex a ≤ weightedStripMultiplicityCount a := by
  classical
  cases fintypeOrInfinite (weightedStripZeros a) with
  | inl h =>
    letI := h
    rw [weightedStripMultiplicityCount_eq_sum]
    refine iSup₂_le fun n hn => ?_
    exact_mod_cast weightedNegOrthonormalFamily_card_le_multiplicity ha0 ha1 hn
  | inr h =>
    letI := h
    rw [weightedStripMultiplicityCount_eq_top]
    exact le_top


end RHTower
