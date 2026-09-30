import GaloisForLFunctions.RHTower.FermiNymanMultiplicitySignature

/-!
# Correlation-Mellin coordinates for the dyadic witness obstruction

The conjugate correlation transform of a Fermi witness is analytic in the right half-plane.
Its conjugated parameter jets are complex-linear on finite witness sums. If the correlation
vanishes to at least the zeta multiplicity at every right-strip zero, the left dyadic defect has
no pole. Unconditional removability then forces dyadic self-similarity.

Boundedness and compact support of the correlation density justify its Mellin transform and
all finite-sum identities. Analytic order comparison handles cancellation without a simple-zero
assumption or a choice of Laurent coefficients.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- The correlation transform of the conjugate literal witness. -/
def fermiCorrelation (w : ℝ → ℂ) : ℂ → ℂ :=
  correlationMellin (fun t => (starRingEnd ℂ) (w t))

theorem IsFermiNymanWitness.conjugateMellinWitness {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) :
    IsMellinFermiWitness (fun t => (starRingEnd ℂ) (w t)) (1 / 2) := by
  apply isMellinFermiWitness_half_of_sq
  · exact Complex.continuous_conj.comp_continuousOn hw.1
  · simpa only [Complex.norm_conj] using hw.2.1
  · exact hw.2.2

theorem IsFermiNymanWitness.analyticAt_fermiCorrelation {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fermiCorrelation w) s := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
    (fun z hz => hw.conjugateMellinWitness.differentiableAt_correlationMellin hz
      |>.differentiableWithinAt)
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs

theorem analyticOrderAt_zetaEntire_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt zetaEntire ρ = analyticOrderAt riemannZeta ρ := by
  have hev : zetaEntire =ᶠ[𝓝 ρ] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hρ] with z hz
    exact zetaEntire_eq hz
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) ρ = _
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ := analyticAt_id.sub analyticAt_const
  have hlin0 : analyticOrderAt (fun z : ℂ => z - 1) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (show (fun z : ℂ => z - 1) ρ ≠ 0 from sub_ne_zero.mpr hρ))
  rw [analyticOrderAt_mul hlin (analyticOn_riemannZeta ρ hρ), hlin0, zero_add]

theorem analyticOrderAt_one_sub_local (f : ℂ → ℂ) (z : ℂ) :
    analyticOrderAt (fun u => f (1 - u)) z = analyticOrderAt f (1 - z) := by
  have hd : HasDerivAt (fun u : ℂ => 1 - u) (-1) z := by
    convert (hasDerivAt_id z).const_sub (1 : ℂ) using 1 <;> rfl
  exact analyticOrderAt_comp_of_deriv_ne_zero
    (analyticAt_const.sub analyticAt_id) (by rw [hd.deriv]; norm_num)

theorem meromorphicOrderAt_div_nonneg_of_order_le {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hgfin : analyticOrderAt g z ≠ ⊤)
    (hord : analyticOrderAt g z ≤ analyticOrderAt f z) :
    0 ≤ meromorphicOrderAt (fun u => f u / g u) z := by
  change 0 ≤ meromorphicOrderAt (f / g) z
  rw [meromorphicOrderAt_div hf.meromorphicAt hg.meromorphicAt,
    hf.meromorphicOrderAt_eq, hg.meromorphicOrderAt_eq]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hgfin
  rw [← hm] at hord ⊢
  cases hn : analyticOrderAt f z with
  | top => simp
  | coe k =>
    have hmk : m ≤ k := by rw [hn] at hord; exact_mod_cast hord
    simp only [ENat.map_coe]
    exact_mod_cast (sub_nonneg.mpr (by exact_mod_cast hmk) : 0 ≤ (k : ℤ) - m)

/-- Cancellation of every right-strip multiplicity removes the entire dyadic obstruction. -/
theorem IsFermiNymanWitness.selfSimilar_of_correlation_order {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w)
    (hord : ∀ ρ : rightStripZeros,
      analyticOrderAt riemannZeta (ρ : ℂ) ≤ analyticOrderAt (fermiCorrelation w) (ρ : ℂ))
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : w (t / 2) = w t := by
  apply hw.selfSimilar_of_removable ?_ ht
  intro z hz hzero
  have hhalf : 1 / 2 < (1 - z).re := by simp; linarith
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
  let ρ : rightStripZeros := ⟨1 - z, hζ, hhalf, hone⟩
  let N : ℂ → ℂ := fun u =>
    -((2 : ℂ) ^ (-u)) * u * (1 - u) * fermiCorrelation w (1 - u)
  let D : ℂ → ℂ := fun u => zetaEntire (1 - u)
  have hN : AnalyticAt ℂ N z := analyticAt_leftNumerator hw.conjugateMellinWitness
    (by linarith : z.re < 1)
  have hD : AnalyticAt ℂ D z :=
    (differentiable_zetaEntire.analyticAt (1 - z)).comp (analyticAt_const.sub analyticAt_id)
  have hDO : analyticOrderAt D z = analyticOrderAt riemannZeta (1 - z) := by
    rw [analyticOrderAt_one_sub_local, analyticOrderAt_zetaEntire_of_ne_one hne]
  have hDf : analyticOrderAt D z ≠ ⊤ := by
    rw [hDO, ← rightStripMultiplicity_coe ρ]
    exact WithTop.coe_ne_top
  have hP : AnalyticAt ℂ (fun u : ℂ => -((2 : ℂ) ^ (-u)) * u * (1 - u)) z := by
    have hpow : Differentiable ℂ (fun u : ℂ => (2 : ℂ) ^ (-u)) := fun _ =>
      (differentiableAt_id.neg).const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    exact (((hpow.analyticAt z).neg.mul analyticAt_id).mul
      (analyticAt_const.sub analyticAt_id))
  have hF : AnalyticAt ℂ (fun u => fermiCorrelation w (1 - u)) z :=
    (hw.analyticAt_fermiCorrelation (by linarith [hhalf])).comp
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

theorem IsFermiNymanWitness.mellinRapid_correlationDensity {w : ℝ → ℂ}
    (hw : IsFermiNymanWitness w) :
    MellinRapid (witnessCorrelation (fun t => (starRingEnd ℂ) (w t))) := by
  let v : ℝ → ℂ := fun t => (starRingEnd ℂ) (w t)
  have hv := hw.conjugateMellinWitness
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

theorem fermiWitnessCorrelation_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (c : ι → ℂ) (hw : ∀ i, IsFermiNymanWitness (w i)) (b : ℝ) :
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
    ((hw i).integrableOn_mul_conj (measurable_fermiNymanGen b)
      (norm_fermiNymanGen_le b)).const_mul _)]
  exact Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)

theorem fermiCorrelation_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (c : ι → ℂ) (hw : ∀ i, IsFermiNymanWitness (w i))
    {s : ℂ} (hs : 0 < s.re) :
    fermiCorrelation (fun t => ∑ i, c i * w i t) s =
      ∑ i, (starRingEnd ℂ) (c i) * fermiCorrelation (w i) s := by
  have hI : ∀ i, IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) •
      witnessCorrelation (fun u => (starRingEnd ℂ) (w i u)) t) (Ioi 0) :=
    fun i => (hw i).mellinRapid_correlationDensity.mellinConvergent hs
  unfold fermiCorrelation correlationMellin mellin
  have hexp : ∀ t : ℝ, (t : ℂ) ^ (s - 1) •
      witnessCorrelation (fun u => (starRingEnd ℂ) (∑ i, c i * w i u)) t =
      ∑ i, (starRingEnd ℂ) (c i) * ((t : ℂ) ^ (s - 1) •
        witnessCorrelation (fun u => (starRingEnd ℂ) (w i u)) t) := by
    intro t
    rw [fermiWitnessCorrelation_sum w c hw]
    simp only [smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun i _ => (hI i).const_mul _)]
  exact Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)

/-- Conjugation converts the correlation jet's witness dependence into complex-linearity. -/
def fermiCorrelationJet (w : ℝ → ℂ) (ρ : ℂ) (j : ℕ) : ℂ :=
  (starRingEnd ℂ) (iteratedDeriv j (fermiCorrelation w) ρ)

theorem fermiCorrelationJet_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ → ℂ) (c : ι → ℂ) (hw : ∀ i, IsFermiNymanWitness (w i))
    {ρ : ℂ} (hρ : 0 < ρ.re) (j : ℕ) :
    fermiCorrelationJet (fun t => ∑ i, c i * w i t) ρ j =
      ∑ i, c i * fermiCorrelationJet (w i) ρ j := by
  have hev : fermiCorrelation (fun t => ∑ i, c i * w i t) =ᶠ[𝓝 ρ]
      (fun s => ∑ i, (starRingEnd ℂ) (c i) * fermiCorrelation (w i) s) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ] with s hs
    exact fermiCorrelation_sum w c hw hs
  unfold fermiCorrelationJet
  rw [hev.iteratedDeriv_eq j, iteratedDeriv_fun_sum
    (f := fun i s => (starRingEnd ℂ) (c i) * fermiCorrelation (w i) s)
    (I := Finset.univ)
    (fun i _ => (analyticAt_const.mul ((hw i).analyticAt_fermiCorrelation hρ)).contDiffAt)]
  simp only [iteratedDeriv_const_mul_field, map_sum, map_mul, Complex.conj_conj]

end RHTower
