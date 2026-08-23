import GaloisForLFunctions.RHTower.DivPowRepresentative
import GaloisForLFunctions.RHTower.DivShiftRepresentative
import GaloisForLFunctions.RHTower.ZetaHardyQuotientPow
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness

/-!
# The zeta Hardy core as a globally meromorphic function

`zetaHardyCore` is built from a Laplace transform and is therefore only holomorphic on the right
half-plane.  Its values there are those of `(s − 1)ζ(s)/s²` with `s = w + 1/2`, an expression that
is meromorphic on the whole plane; the meromorphic normal form of that expression is analytic
everywhere except at `w = −1/2`, and coincides with `zetaHardyCore` on the half-plane.

Replacing `zetaHardyCore` by this representative is what makes repeated division by the zeros of
`ζ` possible: after each division the quotient must again be *analytic* at the next zero, and the
zeros of `ζ` left of the critical line sit outside the half-plane.

## Main results

* `zetaShiftCoreNF`, `analyticAt_zetaShiftCoreNF`
* `isHalfPlaneHardy_zetaShiftCoreNF`
* `natCast_le_analyticOrderAt_zetaShiftCoreNF`
-/

open Complex Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- `(s − 1)ζ(s)/s²` in the half-plane variable `s = w + 1/2`. -/
def zetaShiftCore : ℂ → ℂ := fun w => (w - 1 / 2) * riemannZeta (w + 1 / 2) / (w + 1 / 2) ^ 2

/-- The analytic representative of the zeta Hardy core. -/
def zetaShiftCoreNF : ℂ → ℂ := toMeromorphicNFOn zetaShiftCore Set.univ

theorem meromorphicAt_zetaComp (w : ℂ) :
    MeromorphicAt (fun z : ℂ => riemannZeta (z + 1 / 2)) w :=
  meromorphicAt_comp_add.mpr (meromorphicAt_riemannZeta_everywhere (w + 1 / 2))

theorem analyticAt_zetaComp {w : ℂ} (hw : w ≠ 1 / 2) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + 1 / 2)) w := by
  have hne : w + 1 / 2 ≠ 1 := by
    intro h
    exact hw (by linear_combination h)
  have hζ : AnalyticAt ℂ riemannZeta (w + 1 / 2) := analyticOn_riemannZeta _ (by simpa using hne)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) w := analyticAt_id.add analyticAt_const
  exact AnalyticAt.comp (g := riemannZeta) (f := fun z : ℂ => z + 1 / 2) (x := w) hζ hshift

theorem meromorphicAt_zetaShiftCore (w : ℂ) : MeromorphicAt zetaShiftCore w := by
  have hfun : zetaShiftCore
      = (fun z : ℂ => (z - 1 / 2) * riemannZeta (z + 1 / 2)) / fun z : ℂ => (z + 1 / 2) ^ 2 := by
    funext z
    rw [zetaShiftCore, Pi.div_apply]
  rw [hfun]
  refine MeromorphicAt.div ?_ ?_
  · exact ((analyticAt_id.sub analyticAt_const).meromorphicAt).mul (meromorphicAt_zetaComp w)
  · exact ((analyticAt_id.add analyticAt_const).pow 2).meromorphicAt

theorem halfShift_pow_ne_zero {w : ℂ} (hw : w ≠ -(1 / 2)) : ((w : ℂ) + 1 / 2) ^ 2 ≠ 0 := by
  refine pow_ne_zero _ ?_
  intro h
  exact hw (by linear_combination h)

theorem analyticAt_zetaShiftCore {w : ℂ} (h1 : w ≠ 1 / 2) (h2 : w ≠ -(1 / 2)) :
    AnalyticAt ℂ zetaShiftCore w := by
  have hfun : zetaShiftCore
      = fun z : ℂ => (z - 1 / 2) * riemannZeta (z + 1 / 2) / (z + 1 / 2) ^ 2 := rfl
  rw [hfun]
  exact (((analyticAt_id.sub analyticAt_const).mul (analyticAt_zetaComp h1)).div
    ((analyticAt_id.add analyticAt_const).pow 2) (halfShift_pow_ne_zero h2))

theorem meromorphicOn_zetaShiftCore : MeromorphicOn zetaShiftCore Set.univ :=
  fun z _ => meromorphicAt_zetaShiftCore z

theorem meromorphicOrderAt_zetaShiftCoreNF (z : ℂ) :
    meromorphicOrderAt zetaShiftCoreNF z = meromorphicOrderAt zetaShiftCore z :=
  meromorphicOrderAt_congr
    (meromorphicOn_zetaShiftCore.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z))

theorem zetaShiftCoreNF_eq_of_analyticAt {z : ℂ} (h : AnalyticAt ℂ zetaShiftCore z) :
    zetaShiftCoreNF z = zetaShiftCore z := by
  have hmero : MeromorphicOn zetaShiftCore Set.univ := meromorphicOn_zetaShiftCore
  simp [zetaShiftCoreNF, toMeromorphicNFOn, hmero,
    ← (toMeromorphicNFAt_eq_self.2 h.meromorphicNFAt).symm]

theorem zetaShiftCoreNF_eq {z : ℂ} (h1 : z ≠ 1 / 2) (h2 : z ≠ -(1 / 2)) :
    zetaShiftCoreNF z = (z - 1 / 2) * riemannZeta (z + 1 / 2) / (z + 1 / 2) ^ 2 :=
  zetaShiftCoreNF_eq_of_analyticAt (analyticAt_zetaShiftCore h1 h2)

/-- At `w = 1/2` the simple zero of `w − 1/2` cancels the pole of `ζ`. -/
theorem meromorphicOrderAt_zetaShiftCore_half :
    meromorphicOrderAt zetaShiftCore (1 / 2) = (0 : WithTop ℤ) := by
  have hmsub : MeromorphicAt (fun z : ℂ => z - 1 / 2) (1 / 2 : ℂ) :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hmzeta : MeromorphicAt (fun z : ℂ => riemannZeta (z + 1 / 2)) (1 / 2 : ℂ) :=
    meromorphicAt_zetaComp _
  have hmden : MeromorphicAt (fun z : ℂ => (z + 1 / 2) ^ 2) (1 / 2 : ℂ) :=
    ((analyticAt_id.add analyticAt_const).pow 2).meromorphicAt
  have hnumfun : (fun z : ℂ => (z - 1 / 2) * riemannZeta (z + 1 / 2))
      = (fun z : ℂ => z - 1 / 2) * fun z : ℂ => riemannZeta (z + 1 / 2) := by
    funext z
    rw [Pi.mul_apply]
  have h1 : meromorphicOrderAt (fun z : ℂ => z - 1 / 2) (1 / 2 : ℂ) = ((1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_sub_const_self _
  have h2 : meromorphicOrderAt (fun z : ℂ => riemannZeta (z + 1 / 2)) (1 / 2 : ℂ)
      = ((-1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_comp_add riemannZeta (1 / 2) (1 / 2),
      show ((1 : ℂ) / 2 + 1 / 2) = 1 from by norm_num]
    exact GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one
  have hnum : meromorphicOrderAt (fun z : ℂ => (z - 1 / 2) * riemannZeta (z + 1 / 2))
      (1 / 2 : ℂ) = (0 : WithTop ℤ) := by
    rw [hnumfun, meromorphicOrderAt_mul (f := fun z : ℂ => z - 1 / 2)
      (g := fun z : ℂ => riemannZeta (z + 1 / 2)) hmsub hmzeta, h1, h2]
    norm_num
  have hdenord : meromorphicOrderAt (fun z : ℂ => (z + 1 / 2) ^ 2) (1 / 2 : ℂ)
      = (0 : WithTop ℤ) := by
    have hana : AnalyticAt ℂ (fun z : ℂ => (z + 1 / 2) ^ 2) (1 / 2 : ℂ) :=
      (analyticAt_id.add analyticAt_const).pow 2
    have hne : (((1 : ℂ) / 2) + 1 / 2) ^ 2 ≠ 0 := by norm_num
    rw [hana.meromorphicOrderAt_eq, hana.analyticOrderAt_eq_zero.2 hne]
    simp
  have hfun : zetaShiftCore
      = (fun z : ℂ => (z - 1 / 2) * riemannZeta (z + 1 / 2))
        / fun z : ℂ => (z + 1 / 2) ^ 2 := by
    funext z
    rw [zetaShiftCore, Pi.div_apply]
  rw [hfun, meromorphicOrderAt_div (f := fun z : ℂ => (z - 1 / 2) * riemannZeta (z + 1 / 2))
    (g := fun z : ℂ => (z + 1 / 2) ^ 2) (hmsub.mul hmzeta) hmden, hnum, hdenord]
  simp

/-- **The representative is analytic away from `w = −1/2`.** -/
theorem analyticAt_zetaShiftCoreNF {w : ℂ} (hw : w ≠ -(1 / 2)) :
    AnalyticAt ℂ zetaShiftCoreNF w := by
  have hNF : MeromorphicNFAt zetaShiftCoreNF w :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ w)
  refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  rw [meromorphicOrderAt_zetaShiftCoreNF]
  by_cases h1 : w = 1 / 2
  · rw [h1, meromorphicOrderAt_zetaShiftCore_half]
  · exact meromorphicOrderAt_nonneg_of_analyticAt (analyticAt_zetaShiftCore h1 hw)

theorem ne_neg_half_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ≠ -(1 / 2) := by
  intro h
  rw [h] at hw
  norm_num at hw

theorem analyticAt_zetaShiftCoreNF_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ zetaShiftCoreNF w :=
  analyticAt_zetaShiftCoreNF (ne_neg_half_of_re_pos hw)

/-- **The representative is a Hardy function**: it agrees with `zetaHardyCore` on the half-plane. -/
theorem isHalfPlaneHardy_zetaShiftCoreNF : ∃ M : ℝ, IsHalfPlaneHardy zetaShiftCoreNF M := by
  obtain ⟨M, hM⟩ := isHalfPlaneHardy_zetaHardyCore
  refine ⟨M, hM.congr_right ?_⟩
  have hoff : ∀ w : ℂ, 0 < w.re → w ≠ 1 / 2 → zetaHardyCore w = zetaShiftCoreNF w := by
    intro w hw hw1
    rw [zetaHardyCore_eq hw hw1, zetaShiftCoreNF_eq hw1 (ne_neg_half_of_re_pos hw)]
    congr 1
    ring
  intro w hw
  by_cases hw1 : w = 1 / 2
  · have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hcont1 : ContinuousAt zetaHardyCore w :=
      (hM.holo.analyticAt (hopen.mem_nhds hw)).continuousAt
    have hcont2 : ContinuousAt zetaShiftCoreNF w :=
      (analyticAt_zetaShiftCoreNF_of_re_pos hw).continuousAt
    refine eq_of_eventuallyEq_punctured hcont1 hcont2 ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (hopen.eventually_mem hw)] with z hz hz'
    refine hoff z hz' ?_
    rw [← hw1]
    simpa using hz
  · exact hoff w hw hw1

/-- **The representative vanishes at a zeta zero to the order of the zero.** -/
theorem natCast_le_analyticOrderAt_zetaShiftCoreNF {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) {k : ℕ}
    (hord : (k : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    (k : ℕ∞) ≤ analyticOrderAt zetaShiftCoreNF (ρ - 1 / 2) := by
  have hw1 : (ρ : ℂ) - 1 / 2 ≠ 1 / 2 := by
    intro h
    exact hρ1 (by linear_combination h)
  have hw2 : (ρ : ℂ) - 1 / 2 ≠ -(1 / 2) := by
    intro h
    exact hρ0 (by linear_combination h)
  have hζan : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ1)
  obtain ⟨g, hgan, hgfac⟩ := (natCast_le_analyticOrderAt hζan).1 hord
  have hana : AnalyticAt ℂ zetaShiftCoreNF (ρ - 1 / 2) := analyticAt_zetaShiftCoreNF hw2
  refine (natCast_le_analyticOrderAt hana).2 ?_
  have hval : ((ρ : ℂ) - 1 / 2) + 1 / 2 = ρ := by ring
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) (ρ - 1 / 2) :=
    analyticAt_id.add analyticAt_const
  have hg' : AnalyticAt ℂ g (((ρ : ℂ) - 1 / 2) + 1 / 2) := by rw [hval]; exact hgan
  have hgcomp : AnalyticAt ℂ (fun z : ℂ => g (z + 1 / 2)) (ρ - 1 / 2) :=
    AnalyticAt.comp (g := g) (f := fun z : ℂ => z + 1 / 2) (x := (ρ : ℂ) - 1 / 2) hg' hshift
  refine ⟨fun z : ℂ => (z - 1 / 2) * g (z + 1 / 2) / (z + 1 / 2) ^ 2, ?_, ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const).mul hgcomp).div
      ((analyticAt_id.add analyticAt_const).pow 2) (by rw [hval]; exact pow_ne_zero _ hρ0)
  · have hgshift : ∀ᶠ z : ℂ in 𝓝 ((ρ : ℂ) - 1 / 2), riemannZeta (z + 1 / 2)
        = ((z + 1 / 2) - ρ) ^ k • g (z + 1 / 2) := by
      have hc : Filter.Tendsto (fun z : ℂ => z + 1 / 2) (𝓝 ((ρ : ℂ) - 1 / 2)) (𝓝 ρ) := by
        have hcont : Continuous (fun z : ℂ => z + 1 / 2) := by fun_prop
        have hct : Filter.Tendsto (fun z : ℂ => z + 1 / 2) (𝓝 ((ρ : ℂ) - 1 / 2))
            (𝓝 (((ρ : ℂ) - 1 / 2) + 1 / 2)) := (hcont.continuousAt).tendsto
        rw [hval] at hct
        exact hct
      exact hc.eventually hgfac
    have hne1 : ∀ᶠ z : ℂ in 𝓝 ((ρ : ℂ) - 1 / 2), z ≠ 1 / 2 := eventually_ne_nhds hw1
    have hne2 : ∀ᶠ z : ℂ in 𝓝 ((ρ : ℂ) - 1 / 2), z ≠ -(1 / 2) := eventually_ne_nhds hw2
    filter_upwards [hgshift, hne1, hne2] with z hz hz1 hz2
    rw [zetaShiftCoreNF_eq hz1 hz2, hz, smul_eq_mul]
    have hden : ((z : ℂ) + 1 / 2) ^ 2 ≠ 0 := halfShift_pow_ne_zero hz2
    have hsub : ((z : ℂ) + 1 / 2) - ρ = z - (ρ - 1 / 2) := by ring
    rw [hsub, smul_eq_mul]
    field_simp

end

end RHTower
