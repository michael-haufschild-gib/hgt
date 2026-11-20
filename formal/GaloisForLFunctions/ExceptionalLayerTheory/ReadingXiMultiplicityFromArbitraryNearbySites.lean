import GaloisForLFunctions.ExceptionalLayerTheory.RecoveringAPoleByBarycentricInterpolation
import GaloisForLFunctions.ExceptionalLayerTheory.RecoveringZeroMultiplicityFromParabolicHadamardReadings

/-!
# Recovering the ξ divisor from arbitrarily placed sites

In a fixed small disk, N distinct readings of the logarithmic derivative
determine the zero order up to an error at most C·3⁻ᴺ. Sites can stay a
positive distance from the marked point or cluster among themselves.
The estimate works unchanged for any added polynomial calibration of
degree below N−1, even if its coefficients vary with the experiment.
-/

noncomputable section
open Complex Filter Metric Set Topology
open RHTower RHTower.BacklundConverse
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Error as a function of both the cloud radius and cardinality. The
same pole-free outer circle and regular-part bound work for all clouds. -/
theorem xi_residue_error_by_radius (p : ℂ) :
    ∃ R C : ℝ, 0<R ∧ 0≤C ∧ ∀ d : ℝ, 0≤d → d<R → ∀ t : Finset ℂ,
      t.Nonempty → p∉t → (∀ x ∈ t, dist x p≤d) →
      ‖barycentricResidue t p (logDeriv xi)-(hadamardOrder p:ℂ)‖ ≤ C*(d/(R-d))^t.card := by
  obtain ⟨r,hr,g,ha,hn,hf⟩ := xi_peel_ball p
  let R := r/2
  have hR : 0<R := half_pos hr
  have incl : closedBall p R ⊆ ball p r := closedBall_subset_ball (half_lt_self hr)
  have hg : DifferentiableOn ℂ (logDeriv g) (closedBall p R) := by
    intro z hz
    have h := ha z (incl hz)
    exact ((h.deriv.div h (hn z (incl hz))).differentiableAt).differentiableWithinAt
  obtain ⟨B,hB⟩ := (isCompact_closedBall p R).exists_bound_of_continuousOn hg.continuousOn
  let M := max 0 B
  have hm : 0≤M := le_max_left ..
  refine ⟨R,R*M,hR,mul_nonneg hR.le hm,?_⟩
  intro d hd hdr t ht hp hs
  have hs₀ (x : ℂ) (hx : x∈t) : x∈ball p r :=
    incl (mem_closedBall.mpr ((hs x hx).trans hdr.le))
  have he : barycentricResidue t p (logDeriv xi) =
      barycentricResidue t p (fun z => (hadamardOrder p:ℂ)/(z-p)+logDeriv g z) := by
    unfold barycentricResidue
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [logDeriv_xi_eq_pole_add ha hn hf (hs₀ x hx) (fun h => hp (h ▸ hx))]
  rw [he]
  exact barycentric_pole_error (hadamardOrder p:ℂ) p hd hdr hm hg
    (fun z hz => (hB z (sphere_subset_closedBall hz)).trans (le_max_right ..)) ht hp hs

/-- One fixed disk and one constant work for every finite choice of
sample locations. The marked point itself is excluded from the samples. -/
theorem xi_barycentric_residue_error (p : ℂ) :
    ∃ d C : ℝ, 0<d ∧ 0≤C ∧ ∀ t : Finset ℂ, t.Nonempty → p∉t →
      (∀ x ∈ t, dist x p≤d) →
      ‖barycentricResidue t p (logDeriv xi)-(hadamardOrder p:ℂ)‖ ≤ C*(1/3:ℝ)^t.card := by
  obtain ⟨R,C,hR,hC,h⟩ := xi_residue_error_by_radius p
  refine ⟨R/4,C,by positivity,hC,?_⟩
  have hh := h (R/4) (by positivity) (by linarith only [hR])
  have he : (R/4)/(R-R/4)=(1/3:ℝ) := by
    rw [show R-R/4=3*(R/4) by ring]
    field_simp [hR.ne'] <;> ring
  simpa only [he] using hh

/-- Any sequence of finite clouds with growing cardinality recovers the
same integer in a fixed disk. A separate polynomial drift at each cloud
may grow without bound as long as its degree leaves one residue reading. -/
theorem xi_multiplicity_from_calibrated_clouds (p : ℂ) :
    ∃ d : ℝ, 0<d ∧ ∀ {ι : Type*} {l : Filter ι} (t : ι → Finset ℂ) (P : ι → ℂ[X]),
      Tendsto (fun i => (t i).card) l atTop →
      (∀ᶠ i in l, p∉t i ∧ (∀ x ∈ t i, dist x p≤d) ∧ (P i).natDegree+1<(t i).card) →
      Tendsto (fun i => barycentricResidue (t i) p (fun z => logDeriv xi z+(P i).eval z))
        l (𝓝 (hadamardOrder p:ℂ)) := by
  obtain ⟨d,C,hd,_,hb⟩ := xi_barycentric_residue_error p
  refine ⟨d,hd,?_⟩
  intro ι l t P hn hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/3:ℝ))
    (by norm_num)).comp hn).const_mul C
  rw [mul_zero] at hh
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hh
  filter_upwards [hs,hn.eventually_gt_atTop 0] with i hi hpos
  rw [barycentric_polynomial_drift (t i) p (logDeriv xi) (P i) hi.2.2]
  exact hb _ (Finset.card_pos.mp hpos) hi.1 hi.2.1

/-- Eventually rounding the real reading to the nearest integer recovers
the exact order uniformly over all site choices and polynomial drifts. -/
theorem uniquely_decoded_xi_multiplicity (p : ℂ) :
    ∃ d : ℝ, 0<d ∧ ∃ N : ℕ, ∀ t : Finset ℂ, N≤t.card → p∉t →
      (∀ x ∈ t, dist x p≤d) → ∀ P : ℂ[X], P.natDegree+1<t.card →
      ∀ k : ℤ, |(barycentricResidue t p (fun z => logDeriv xi z+P.eval z)).re-k|<1/2 ↔
        k=(hadamardOrder p:ℤ) := by
  obtain ⟨d,C,hd,_,hb⟩ := xi_barycentric_residue_error p
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/3:ℝ)) (by norm_num)).const_mul C
  rw [mul_zero] at ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0:ℝ)<1/2))
  refine ⟨d,hd,N,fun t hnum hp hs P hP k => ?_⟩
  rw [barycentric_polynomial_drift t p (logDeriv xi) P hP]
  let z := barycentricResidue t p (logDeriv xi)
  have hh := (Complex.abs_re_le_norm (z-(hadamardOrder p:ℂ))).trans_lt
    ((hb t (Finset.card_pos.mp (by omega)) hp hs).trans_lt (hN t.card hnum))
  rw [Complex.sub_re,Complex.natCast_re] at hh
  constructor
  · intro hk
    have h₁ := (abs_lt.mp hh)
    have h₂ := (abs_lt.mp hk)
    change -(1/2:ℝ)<z.re-(k:ℝ) ∧ z.re-(k:ℝ)<1/2 at h₂
    have hab : (k:ℝ)<(hadamardOrder p:ℝ)+1 ∧ (hadamardOrder p:ℝ)<(k:ℝ)+1 := by
      constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]
    have hab' : k<(hadamardOrder p:ℤ)+1 ∧ (hadamardOrder p:ℤ)<k+1 := by exact_mod_cast hab
    omega
  · rintro rfl
    simpa only [Int.cast_natCast] using hh

#print axioms xi_residue_error_by_radius
#print axioms xi_barycentric_residue_error
#print axioms xi_multiplicity_from_calibrated_clouds
#print axioms uniquely_decoded_xi_multiplicity
end GaloisForLFunctions.ExceptionalLayerTheory
