import GaloisForLFunctions.RHTower.CHMDThetaTranslateGraph

/-!
# Exact primitive critical modes of the complete CHMD jump form

Pole-annihilated small theta translates belong to the actual completed domain
and annihilate its entire signed polarization. Their jump eigenvalue is exactly
one in the weak form sense. Nonzero signed energy tests and approximate escape
are not used as substitutes for this exact identity.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDThetaTranslate
open CHMDDoobGraph CHMDTranslation

theorem neg_admissible {a : ℝ} (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    1 < 2 * Real.exp (-2 * |-a|) := by simpa only [abs_neg] using ha

def critical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) : SourceGraph :=
  lift a ha + lift (-a) (neg_admissible ha) - (2 * Real.cosh (a/2)) • constantLift 1

def criticalFunction (a x : ℝ) : ℝ := ratio a x + ratio (-a) x - 2 * Real.cosh (a/2)

theorem critical_source_ae (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    (critical a ha).val.fst =ᵐ[massMeasure] criticalFunction a := by
  let A := (lift a ha).val.fst
  let B := (lift (-a) (neg_admissible ha)).val.fst
  let G := (constantLift 1).val.fst
  let c := 2 * Real.cosh (a/2)
  have hg : G =ᵐ[massMeasure] (fun _ => (1 : ℝ)) :=
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
  filter_upwards [lift_source_ae a ha, lift_source_ae (-a) (neg_admissible ha), hg,
    Lp.coeFn_add A B, Lp.coeFn_smul c G, Lp.coeFn_sub (A+B) (c • G)] with x hA hB hG hadd hsm hsub
  change ((A+B)-c • G) x = criticalFunction a x
  rw [hsub, Pi.sub_apply, hadd, Pi.add_apply, hsm, Pi.smul_apply]
  change A x + B x - c * G x = _
  rw [hG]
  change (lift a ha).val.fst x + (lift (-a) (neg_admissible ha)).val.fst x - c * 1 = _
  rw [hA, hB, mul_one]
  rfl

theorem critical_pair_test (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourcePair (critical a ha) (testLift f hf hc) = 0 := by
  have h0 : 1 < 2 * Real.exp (-2 * |(0 : ℝ)|) := by norm_num
  have hg := pair_lift_test 0 h0 f hf hc
  rw [lift_zero] at hg
  have ht : CHMDTranslation.translate f 0 = f := by
    funext x; simp only [CHMDTranslation.translate, sub_zero]
  rw [neg_zero, ht] at hg
  rw [critical, sourcePair_sub_left, sourcePair_add_left, sourcePair_smul_left,
    pair_lift_test, pair_lift_test, hg,
    coshHalfMoment_translate hf.continuous hc, coshHalfMoment_translate hf.continuous hc]
  simp only [neg_neg, neg_div, Real.cosh_neg, Real.sinh_neg]
  ring

/-- Exact radical identity on the entire complete graph, including every prime power. -/
theorem critical_radical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (q : SourceGraph) :
    sourcePair (critical a ha) q = 0 := by
  have hc : Continuous (fun q => sourcePair (critical a ha) q) :=
    continuous_sourcePair.comp (continuous_const.prodMk continuous_id)
  have he : (fun q => sourcePair (critical a ha) q) = (fun _ => (0 : ℝ)) := by
    apply Continuous.ext_on dense_compactTests hc continuous_const
    rintro q ⟨v, hv, hvc, rfl⟩
    rw [← testLift_phi v hv hvc]
    exact critical_pair_test a ha (phiDoobTest v) (contDiff_phiDoobTest hv)
      (hasCompactSupport_phiDoobTest hvc)
  exact congrFun he q

theorem critical_primitive (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    ⟪(critical a ha).val.fst, (constantLift 1).val.fst⟫_ℝ = 0 := by
  have hh := critical_radical a ha (constantLift 1)
  rw [sourcePair_symm, sourcePair_ground, neg_eq_zero] at hh
  rwa [real_inner_comm] at hh

theorem critical_jump_identity (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (q : SourceGraph) :
    ⟪(critical a ha).val.snd, q.val.snd⟫_ℝ = ⟪(critical a ha).val.fst, q.val.fst⟫_ℝ :=
  sub_eq_zero.mp (critical_radical a ha q)

theorem critical_energy (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    sourceEnergy (critical a ha) = 0 := by
  rw [← sourcePair_self]
  exact critical_radical a ha _

/-- The polar filter is nonzero for every nonzero admitted shift. -/
theorem critical_ne_zero (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) (hane : a ≠ 0) :
    critical a ha ≠ 0 := by
  intro hz
  have hsource : (critical a ha).val.fst = 0 := by rw [hz]; rfl
  have hae := (critical_source_ae a ha).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hsource)
  have hcont : Continuous (criticalFunction a) :=
    ((continuous_ratio a).add (continuous_ratio (-a))).sub continuous_const
  have he := (hcont.ae_eq_iff_eq (μ := (volume : Measure ℝ)) continuous_const).mp
    (volume_absolutelyContinuous_mass.ae_eq hae)
  have hfun : (fun x => riemannKernelReal (x-a) + riemannKernelReal (x-(-a)) -
      (2 * Real.cosh (a/2)) * riemannKernelReal x) = (fun _ => (0 : ℝ)) := by
    funext x
    have hh := congrFun he x
    change ratio a x + ratio (-a) x - 2 * Real.cosh (a/2) = 0 at hh
    unfold ratio at hh
    field_simp [(riemannKernelReal_pos x).ne'] at hh
    linarith
  have hi := congrArg (fun f : ℝ → ℝ => ∫ x, f x) hfun
  have hInt := WeilExcess.integrable_riemannKernelReal
  have hsum : Integrable (fun x => riemannKernelReal (x-a) + riemannKernelReal (x-(-a))) :=
    (hInt.comp_sub_right a).add (hInt.comp_sub_right (-a))
  have hscale : Integrable (fun x => (2 * Real.cosh (a/2)) * riemannKernelReal x) := hInt.const_mul _
  rw [integral_sub hsum hscale,
    integral_add (hInt.comp_sub_right a) (hInt.comp_sub_right (-a)), integral_const_mul,
    integral_sub_right_eq_self, integral_sub_right_eq_self, integral_zero] at hi
  have hp := integral_riemannKernelReal_pos
  have hc : 1 < Real.cosh (a/2) := Real.one_lt_cosh.mpr (div_ne_zero hane (by norm_num))
  nlinarith

/-- Unconditional, actual nonzero primitive weak eigenvector of the full jump form at one. -/
theorem exists_exact_primitive_critical :
    ∃ p : SourceGraph, p ≠ 0 ∧ p ∈ compactCore ∧
      ⟪p.val.fst, (constantLift 1).val.fst⟫_ℝ = 0 ∧
      ∀ q : SourceGraph, ⟪p.val.snd, q.val.snd⟫_ℝ = ⟪p.val.fst, q.val.fst⟫_ℝ := by
  have ha := small_shift (a := radius) (by rw [abs_of_pos radius_pos])
  exact ⟨critical radius ha, critical_ne_zero radius ha radius_pos.ne',
    by rw [compactCore_eq_top]; trivial, critical_primitive radius ha,
    critical_jump_identity radius ha⟩

end RHTower.CHMDThetaTranslate
