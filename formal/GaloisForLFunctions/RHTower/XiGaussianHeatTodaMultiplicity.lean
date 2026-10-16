import GaloisForLFunctions.HTGeometry.HankelHeatToda
import GaloisForLFunctions.HTGeometry.AnalyticTodaMultiplicity
import GaloisForLFunctions.RHTower.XiGaussianHeatBlockJacobiCensus

/-!
# Exact singular heat dynamics of the actual Hankel ladder

The actual heat moments satisfy the Toda determinant identity at every
positive time, including simultaneous singularities of adjacent sections.

Between consecutive regular heads `n` and `n+d`, the determinant at rank
`n+k` has exact heat-time order `k(d-k)`. Dividing by this power of `t-a`
leaves an analytic nonvanishing germ. Its crossing parity is therefore
fixed by the two block distances. Every actual-source capstone is
unconditional; only positive time and intrinsic rank indices are inputs.

This resolves local singular evolution. It does not exclude contacts or
determine the complete prime–Gamma source sign.
-/

open Filter Topology Matrix HTGeometry

namespace RHTower
noncomputable section

theorem hasDerivAt_heatMomentDet_succ {a : ℝ} (ha : 0 < a) (n : ℕ) :
    HasDerivAt (heatMomentDet (n + 1))
      (-(hankelBorderMatrix (heatRealMoments a) n 1 0).det) a := by
  change HasDerivAt (fun t => (momentHankelMatrix (heatRealMoments t) (n + 1)).det) _ a
  simpa only [hankelBorderMatrix_zero_zero] using
    hasDerivAt_hankelBorderMatrix_zero (fun k => hasDerivAt_heatRealMoments k ha) n 0

theorem hasDerivAt_deriv_heatMomentDet_succ {a : ℝ} (ha : 0 < a) (n : ℕ) :
    HasDerivAt (deriv (heatMomentDet (n + 1)))
      (hankelBorderMatrix (heatRealMoments a) n 1 1).det a := by
  have h := (hasDerivAt_hankelBorderMatrix_one_zero
    (fun k => hasDerivAt_heatRealMoments k ha) n).neg
  simp only [neg_neg] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ha] with t ht
  exact (hasDerivAt_heatMomentDet_succ ht n).deriv

/-- The actual heat Toda law holds at all positive times, with no pivot hypothesis. -/
theorem hcf_heat_toda (a : {t : ℝ // 0 < t}) (n : ℕ) :
    heatMomentDet (n + 1) a * deriv (deriv (heatMomentDet (n + 1))) a -
        deriv (heatMomentDet (n + 1)) a ^ 2 =
      heatMomentDet n a * heatMomentDet (n + 2) a := by
  have hf := analyticAt_heatMomentDet a.property (n + 1)
  have hleft : ContinuousAt (fun t => heatMomentDet (n + 1) t *
      deriv (deriv (heatMomentDet (n + 1))) t -
        deriv (heatMomentDet (n + 1)) t ^ 2) (a : ℝ) :=
    (hf.mul hf.deriv.deriv |>.sub (hf.deriv.pow 2)).continuousAt
  have hright : ContinuousAt (fun t => heatMomentDet n t * heatMomentDet (n + 2) t)
      (a : ℝ) :=
    ((analyticAt_heatMomentDet a.property n).mul
      (analyticAt_heatMomentDet a.property (n + 2))).continuousAt
  have he : (fun t => heatMomentDet (n + 1) t *
      deriv (deriv (heatMomentDet (n + 1))) t -
        deriv (heatMomentDet (n + 1)) t ^ 2) =ᶠ[𝓝[≠] (a : ℝ)]
      (fun t => heatMomentDet n t * heatMomentDet (n + 2) t) := by
    filter_upwards [eventually_heatMomentDet_ne_zero a.property n,
      (eventually_gt_nhds a.property).filter_mono nhdsWithin_le_nhds] with t ht hpos
    rw [(hasDerivAt_heatMomentDet_succ hpos n).deriv,
      (hasDerivAt_deriv_heatMomentDet_succ hpos n).deriv, neg_sq]
    exact hankelBorder_condensation (heatRealMoments t) n ht
  exact tendsto_nhds_unique_of_eventuallyEq
    (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    (hright.tendsto.mono_left nhdsWithin_le_nhds) he

/-- The order is finite at every positive heat time, including singular times. -/
theorem analyticOrderAt_heatMomentDet_ne_top (a : {t : ℝ // 0 < t}) (N : ℕ) :
    analyticOrderAt (heatMomentDet N) (a : ℝ) ≠ ⊤ := by
  intro h
  have hz : ∀ᶠ t in 𝓝[≠] (a : ℝ), heatMomentDet N t = 0 :=
    (analyticOrderAt_eq_top.mp h).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, hnt⟩ := (hz.and (eventually_heatMomentDet_ne_zero a.property N)).exists
  exact hnt ht

/-- Heat-time order of the actual determinant germ. -/
def heatMomentMultiplicity (a : {t : ℝ // 0 < t}) (N : ℕ) : ℕ :=
  analyticOrderNatAt (heatMomentDet N) (a : ℝ)

theorem analyticOrderAt_heatMomentDet_eq (a : {t : ℝ // 0 < t}) (N : ℕ) :
    analyticOrderAt (heatMomentDet N) (a : ℝ) = (heatMomentMultiplicity a N : ℕ∞) :=
  (Nat.cast_analyticOrderNatAt (analyticOrderAt_heatMomentDet_ne_top a N)).symm

theorem meromorphicOrderAt_heatMomentDet_eq (a : {t : ℝ // 0 < t}) (N : ℕ) :
    meromorphicOrderAt (heatMomentDet N) (a : ℝ) =
      ((heatMomentMultiplicity a N : ℤ) : WithTop ℤ) := by
  rw [(analyticAt_heatMomentDet a.property N).meromorphicOrderAt_eq,
    analyticOrderAt_heatMomentDet_eq, ENat.map_coe]

theorem heatMomentMultiplicity_eq_zero_iff (a : {t : ℝ // 0 < t}) (N : ℕ) :
    heatMomentMultiplicity a N = 0 ↔ heatMomentDet N a ≠ 0 := by
  rw [← (analyticAt_heatMomentDet a.property N).analyticOrderAt_eq_zero,
    analyticOrderAt_heatMomentDet_eq]
  exact_mod_cast (Iff.rfl : heatMomentMultiplicity a N = 0 ↔ heatMomentMultiplicity a N = 0)

/-- Each interior zero obeys a forced, exact second-difference equation. -/
theorem heatMomentMultiplicity_recurrence (a : {t : ℝ // 0 < t}) (n : ℕ)
    (hz : heatMomentDet (n + 1) a = 0) :
    (heatMomentMultiplicity a n : ℤ) + heatMomentMultiplicity a (n + 2) =
      2 * heatMomentMultiplicity a (n + 1) - 2 := by
  have hm : 0 < heatMomentMultiplicity a (n + 1) := by
    apply Nat.pos_of_ne_zero
    intro h
    exact (heatMomentMultiplicity_eq_zero_iff a (n + 1)).mp h hz
  have horder := meromorphicOrderAt_curvature
    (analyticAt_heatMomentDet a.property (n + 1)) hm
    (analyticOrderAt_heatMomentDet_eq a (n + 1))
  have he : (fun t => heatMomentDet (n + 1) t *
      deriv (deriv (heatMomentDet (n + 1))) t - deriv (heatMomentDet (n + 1)) t ^ 2)
      =ᶠ[𝓝 (a : ℝ)] (fun t => heatMomentDet n t * heatMomentDet (n + 2) t) := by
    filter_upwards [eventually_gt_nhds a.property] with t ht
    exact hcf_heat_toda ⟨t, ht⟩ n
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)] at horder
  change meromorphicOrderAt (heatMomentDet n * heatMomentDet (n + 2)) (a : ℝ) = _ at horder
  rw [meromorphicOrderAt_mul (analyticAt_heatMomentDet a.property n).meromorphicAt
      (analyticAt_heatMomentDet a.property (n + 2)).meromorphicAt,
    meromorphicOrderAt_heatMomentDet_eq, meromorphicOrderAt_heatMomentDet_eq] at horder
  exact_mod_cast horder

theorem heat_normal_block_multiplicity (a : {t : ℝ // 0 < t}) {n d : ℕ}
    (h : MomentNormalBlock (heatRealMoments a) n d) :
    ∀ k ≤ d, heatMomentMultiplicity a (n + k) = k * (d - k) := by
  apply toda_multiplicity_block (fun k => heatMomentMultiplicity a (n + k)) h.length_pos
  · simpa only [Nat.add_zero] using (heatMomentMultiplicity_eq_zero_iff a n).mpr h.head_regular
  · exact (heatMomentMultiplicity_eq_zero_iff a (n + d)).mpr h.next_regular
  · intro k hk
    have hz : heatMomentDet (n + (k + 1)) a = 0 :=
      h.intermediate_singular (by omega) (by omega)
    simpa only [Nat.add_assoc] using heatMomentMultiplicity_recurrence a (n + k) hz

/-- The complete multiplicity profile of every canonical actual heat block.
Only positive time, block number, and an intrinsic within-block index are inputs. -/
theorem hcf_heat_block_multiplicity (a : {t : ℝ // 0 < t}) (j : ℕ)
    (k : Fin (heatRegularGap a j + 1)) :
    heatMomentMultiplicity a (heatRegularHead a j + k) =
      (k : ℕ) * (heatRegularGap a j - k) :=
  heat_normal_block_multiplicity a (heatRegularGap_normalBlock a j) k (by omega)

/-- Every actual determinant has order equal to the product of its distances
from its two neighboring regular heads. -/
theorem hcf_all_time_heat_multiplicity (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      analyticOrderAt (heatMomentDet N) (a : ℝ) =
        (((N - heatRegularHead a j) * (heatRegularHead a (j + 1) - N) : ℕ) : ℕ∞) := by
  obtain ⟨j, hj, hj1⟩ := exists_heatRegularHead_cover a N
  have hg := heatRegularHead_add_gap a j
  have h := heat_normal_block_multiplicity a (heatRegularGap_normalBlock a j)
    (N - heatRegularHead a j) (by omega)
  have hN : heatRegularHead a j + (N - heatRegularHead a j) = N := by omega
  have hd : heatRegularGap a j - (N - heatRegularHead a j) =
      heatRegularHead a (j + 1) - N := by omega
  rw [hN, hd] at h
  refine ⟨j, hj, hj1, ?_⟩
  rw [analyticOrderAt_heatMomentDet_eq, h]

/-- Unconditional local desingularization: remove the explicitly determined
power of heat time and the remaining germ is analytic and nonvanishing. -/
theorem hcf_heat_singular_normal_form (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ (j : ℕ) (g : ℝ → ℝ), heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      AnalyticAt ℝ g (a : ℝ) ∧ g a ≠ 0 ∧
      ∀ᶠ t in 𝓝 (a : ℝ), heatMomentDet N t =
        (t - a) ^ ((N - heatRegularHead a j) * (heatRegularHead a (j + 1) - N)) * g t := by
  obtain ⟨j, hj, hj1, ho⟩ := hcf_all_time_heat_multiplicity a N
  obtain ⟨g, hg, hgne, he⟩ :=
    (analyticAt_heatMomentDet a.property N).analyticOrderAt_eq_natCast.mp ho
  exact ⟨j, g, hj, hj1, hg, hgne, by simpa only [smul_eq_mul] using he⟩

/-- Exact crossing parity at every actual heat time. A determinant crosses
zero precisely when the product of its two block distances is odd. -/
theorem hcf_heat_crossing_parity (a : {t : ℝ // 0 < t}) (N : ℕ) :
    ∃ j, heatRegularHead a j ≤ N ∧ N < heatRegularHead a (j + 1) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        SignType.sign (heatMomentDet N (a - t) * heatMomentDet N (a + t)) =
          (-1 : SignType) ^ ((N - heatRegularHead a j) * (heatRegularHead a (j + 1) - N)) := by
  obtain ⟨j, hj, hj1, ho⟩ := hcf_all_time_heat_multiplicity a N
  exact ⟨j, hj, hj1,
    eventually_reflection_sign_of_analyticOrderAt (analyticAt_heatMomentDet a.property N) ho⟩

end
end RHTower
