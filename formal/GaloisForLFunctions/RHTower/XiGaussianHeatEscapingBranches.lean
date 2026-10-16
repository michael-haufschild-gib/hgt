import GaloisForLFunctions.RHTower.XiGaussianHeatAdmissionEscape
import GaloisForLFunctions.HTGeometry.HeatEscapeSimpleRoots
import GaloisForLFunctions.HTGeometry.AnalyticMonicRootGerm

/-!
# Unramified branches of the actual HCF admissions at infinity

Every universal escaping residue is nonzero and simple. The weighted analytic
extension therefore resolves the escaping packet into individual analytic
branches. After undoing the scale, every branch is a genuine simple pole.
The construction works at every positive time and every rank, including
multiple contacts, and is unique among continuous scaled root germs.
-/

open Filter Topology Polynomial HTGeometry GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- A resolved actual admission root with prescribed residue at the contact. -/
structure HeatAdmissionEscapingBranch (a : {t : ℝ // 0 < t}) (N : ℕ) (z : ℂ) where
  scaledRoot : ℝ → ℂ
  analytic : AnalyticAt ℝ scaledRoot (a : ℝ)
  at_contact : scaledRoot a = z
  residue_ne_zero : z ≠ 0
  admission_root : ∀ᶠ t in 𝓝[≠] (a : ℝ),
    aeval (scaledRoot t / ((t - a : ℝ) : ℂ))
      (monicMomentAdmissionPolynomial (heatRealMoments t) N) = 0
  meromorphic : MeromorphicAt (fun t => scaledRoot t / ((t - a : ℝ) : ℂ)) a
  pole_order : meromorphicOrderAt (fun t => scaledRoot t / ((t - a : ℝ) : ℂ)) a = -1
  unique : ∀ s : ℝ → ℂ, ContinuousAt s (a : ℝ) → s a = z →
    (∀ᶠ t in 𝓝[≠] (a : ℝ),
      aeval (s t / ((t - a : ℝ) : ℂ))
        (monicMomentAdmissionPolynomial (heatRealMoments t) N) = 0) →
    scaledRoot =ᶠ[𝓝[≠] (a : ℝ)] s

/-- Distinct residues separate the actual pole branches on a punctured neighborhood. -/
theorem HeatAdmissionEscapingBranch.eventually_ne
    {a : {t : ℝ // 0 < t}} {N : ℕ} {z w : ℂ}
    (b : HeatAdmissionEscapingBranch a N z) (c : HeatAdmissionEscapingBranch a N w)
    (hzw : z ≠ w) :
    ∀ᶠ t in 𝓝[≠] (a : ℝ),
      b.scaledRoot t / ((t - a : ℝ) : ℂ) ≠ c.scaledRoot t / ((t - a : ℝ) : ℂ) := by
  have he : ∀ᶠ t in 𝓝 (a : ℝ), b.scaledRoot t ≠ c.scaledRoot t :=
    (b.analytic.continuousAt.ne_iff_eventually_ne c.analytic.continuousAt).mp
      (by simpa only [b.at_contact, c.at_contact] using hzw)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hta
  exact ht ∘ (div_left_inj' (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hta))).mp

private theorem monicCoeffPolynomial_real_coeff {p : ℝ[X]} {N : ℕ}
    (hp : p.Monic) (hN : p.natDegree = N) :
    monicCoeffPolynomial N (fun i : Fin N => (p.coeff i : ℂ)) =
      p.map (algebraMap ℝ ℂ) := by
  have hn : (p.map (algebraMap ℝ ℂ)).natDegree = N := (hp.natDegree_map _).trans hN
  cases hn
  simpa only [coeff_map, Complex.coe_algebraMap] using
    monicCoeffPolynomial_coeff_of_monic (p.map (algebraMap ℝ ℂ)) (hp.map _)

/-- At every actual time/rank, the escaping packet consists of exactly its
offset many distinct residues, each with a unique unramified simple-pole
branch. No contact simplicity, regularity, or source-sign premise is used. -/
theorem hcf_heat_admission_unramified_branches (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      Fintype.card ((heatEscapePolynomial (heatRegularGap a j)
        (N - heatRegularHead a j)).rootSet ℂ) = N - heatRegularHead a j ∧
      ∀ z : (heatEscapePolynomial (heatRegularGap a j)
        (N - heatRegularHead a j)).rootSet ℂ,
        Nonempty (HeatAdmissionEscapingBranch a N z) := by
  classical
  obtain ⟨j, g, hj, hj1, hg, hga, hge⟩ := hcf_heat_admission_escape_profile a N
  have hgap := heatRegularHead_add_gap a j
  have hk : N - heatRegularHead a j < heatRegularGap a j := by omega
  let q : ℝ[X] := X ^ heatRegularHead a j *
    heatEscapePolynomial (heatRegularGap a j) (N - heatRegularHead a j)
  have hqm : q.Monic := (monic_X_pow _).mul (heatEscapePolynomial_monic _ _)
  have hqN : q.natDegree = N := by
    simp only [q, natDegree_X_pow_mul _ (heatEscapePolynomial_ne_zero _ _),
      heatEscapePolynomial_natDegree]
    omega
  let c : ℝ → Fin N → ℂ := fun t i => (g t i.castSucc : ℂ)
  have hc : AnalyticAt ℝ c (a : ℝ) := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (Complex.ofRealCLM.analyticAt _).comp ((analyticAt_pi_iff.mp hg) i.castSucc)
  have hca : monicCoeffPolynomial N (c a) = q.map (algebraMap ℝ ℂ) := by
    have he : c a = fun i : Fin N => (q.coeff i : ℂ) := by
      funext i
      simp only [c, hga]
      rfl
    rw [he]
    exact monicCoeffPolynomial_real_coeff hqm hqN
  have he : ∀ᶠ t in 𝓝[≠] (a : ℝ), monicCoeffPolynomial N (c t) =
      (weightedPolynomial (monicMomentAdmissionPolynomial (heatRealMoments t) N)
        N (t - a)).map (algebraMap ℝ ℂ) := by
    filter_upwards [hge] with t ht
    have hcs : c t = fun i : Fin N =>
        ((weightedPolynomial (monicMomentAdmissionPolynomial (heatRealMoments t) N)
          N (t - a)).coeff i : ℂ) := by
      funext i
      apply congrArg (fun x : ℝ => (x : ℂ))
      rw [weightedPolynomial, ofFn_coeff_eq_val_of_lt _ (by omega)]
      exact (congrFun ht i.castSucc).symm
    rw [hcs]
    obtain ⟨hm, hn⟩ := weightedPolynomial_monic_natDegree
      (monicMomentAdmissionPolynomial_monic _ _) (monicMomentAdmissionPolynomial_natDegree _ _)
      (t - a)
    exact monicCoeffPolynomial_real_coeff hm hn
  have htransport : ∀ᶠ t in 𝓝[≠] (a : ℝ), ∀ w : ℂ,
      (monicCoeffPolynomial N (c t)).eval w = 0 ↔
        aeval (w / ((t - a : ℝ) : ℂ))
          (monicMomentAdmissionPolynomial (heatRealMoments t) N) = 0 := by
    filter_upwards [he, self_mem_nhdsWithin] with t ht hta w
    rw [ht, eval_map_algebraMap]
    exact weightedPolynomial_aeval_eq_zero_iff
      (le_of_eq (monicMomentAdmissionPolynomial_natDegree _ _)) (sub_ne_zero.mpr hta) w
  refine ⟨j, hj, hj1, heatEscapePolynomial_card_rootSet hk, ?_⟩
  intro z
  have hz := aeval_eq_zero_of_mem_rootSet z.property
  have hz0 := heatEscapePolynomial_root_ne_zero hk hz
  have hroot : (monicCoeffPolynomial N (c a)).eval (z : ℂ) = 0 := by
    rw [hca, eval_map_algebraMap]
    simp only [q, map_mul, hz, mul_zero]
  have hder : (derivative (monicCoeffPolynomial N (c a))).eval (z : ℂ) ≠ 0 := by
    rw [hca, derivative_map, eval_map_algebraMap]
    exact heatEscapePolynomial_shift_root_simple hk _ hz
  obtain ⟨r, hr, hra, hre, hru⟩ := analytic_monic_root_germ hc hroot hder
  have hpole := analytic_residue_simple_pole hr (by simpa only [hra] using hz0)
  refine ⟨{
    scaledRoot := r
    analytic := hr
    at_contact := hra
    residue_ne_zero := hz0
    admission_root := ?_
    meromorphic := hpole.1
    pole_order := hpole.2
    unique := ?_ }⟩
  · filter_upwards [hre.filter_mono nhdsWithin_le_nhds, htransport] with t ht heq
    exact (heq (r t)).mp ht
  · intro s hs hsa hseq
    apply hru s hs hsa
    filter_upwards [hseq, htransport] with t ht heq
    exact (heq (s t)).mpr ht

/-- The entire escaping packet is simultaneously resolved on one punctured
neighborhood into distinct simple-pole admission roots. -/
theorem hcf_heat_admission_escape_packet (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      Fintype.card ((heatEscapePolynomial (heatRegularGap a j)
        (N - heatRegularHead a j)).rootSet ℂ) = N - heatRegularHead a j ∧
      ∃ b : ∀ z : (heatEscapePolynomial (heatRegularGap a j)
          (N - heatRegularHead a j)).rootSet ℂ, HeatAdmissionEscapingBranch a N z,
        ∀ᶠ t in 𝓝[≠] (a : ℝ),
          (∀ z, aeval ((b z).scaledRoot t / ((t - a : ℝ) : ℂ))
            (monicMomentAdmissionPolynomial (heatRealMoments t) N) = 0) ∧
          Function.Injective (fun z => (b z).scaledRoot t / ((t - a : ℝ) : ℂ)) := by
  classical
  obtain ⟨j, hj, hj1, hc, hb⟩ := hcf_heat_admission_unramified_branches a N
  let b := fun z => Classical.choice (hb z)
  have hsep : ∀ z w, ∀ᶠ t in 𝓝[≠] (a : ℝ), z ≠ w →
      (b z).scaledRoot t / ((t - a : ℝ) : ℂ) ≠
        (b w).scaledRoot t / ((t - a : ℝ) : ℂ) := by
    intro z w
    by_cases he : z = w
    · exact Filter.Eventually.of_forall (fun _ h => (h he).elim)
    · exact ((b z).eventually_ne (b w) (fun h => he (Subtype.ext h))).mono (fun _ ht _ => ht)
  refine ⟨j, hj, hj1, hc, b, ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun z => (b z).admission_root),
    Filter.eventually_all.mpr (fun z => Filter.eventually_all.mpr (hsep z))] with t ht hs
  refine ⟨ht, ?_⟩
  intro z w he
  by_contra hzw
  exact hs z w hzw he

end
end RHTower
