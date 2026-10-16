import GaloisForLFunctions.RHTower.CHMDBulkCutoffGraph
import GaloisForLFunctions.RHTower.CHMDFiniteDivisorGraph

/-!
# The literal CHMD graph and the complete Xi zero pairing

The compact explicit formula extends to theta-dominated exponentially decaying
sources by strong graph convergence and the unconditional full zero-sum limit.
Both pole products and all zero multiplicities remain in the identity.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower
open WeilSpectral

theorem WeilSpectral.ExpDecayTest.add {f g : ℝ → ℝ}
    (hf : ExpDecayTest f) (hg : ExpDecayTest g) : ExpDecayTest (f + g) := by
  obtain ⟨hs, δ, C, hδ, hC, hb⟩ := hf
  obtain ⟨ht, ε, D, hε, hD, hc⟩ := hg
  refine ⟨hs.add ht, min δ ε, C + D, lt_min hδ hε, by positivity, fun x => ?_⟩
  have hδx : Real.exp (-((1/2 + δ) * |x|)) ≤
      Real.exp (-((1/2 + min δ ε) * |x|)) := by gcongr; exact min_le_left _ _
  have hεx : Real.exp (-((1/2 + ε) * |x|)) ≤
      Real.exp (-((1/2 + min δ ε) * |x|)) := by gcongr; exact min_le_right _ _
  have hfb := mul_le_mul_of_nonneg_left hδx hC
  have hgb := mul_le_mul_of_nonneg_left hεx hD
  have hd := ((hs.differentiable (by norm_num) x).hasDerivAt.add
    (ht.differentiable (by norm_num) x).hasDerivAt).deriv
  change deriv (f + g) x = deriv f x + deriv g x at hd
  rw [hd, Pi.add_apply]
  constructor
  · exact (abs_add_le _ _).trans (by nlinarith [(hb x).1, (hc x).1])
  · exact (abs_add_le _ _).trans (by nlinarith [(hb x).2, (hc x).2])

namespace CHMDDoobGraph

/-- The full zero sum minus the original two polar products. -/
def signedZeroEnergy (f : ℝ → ℝ) : ℝ :=
  (zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re -
    (paperFT (fun x => (f x : ℂ)) (I / 2) *
        (starRingEnd ℂ) (paperFT (fun x => (f x : ℂ)) (-I / 2)) +
      paperFT (fun x => (f x : ℂ)) (-I / 2) *
        (starRingEnd ℂ) (paperFT (fun x => (f x : ℂ)) (I / 2))).re

/-- Real polarization of the full signed zero pairing. -/
def signedZeroPair (f g : ℝ → ℝ) : ℝ :=
  (signedZeroEnergy (f + g) - signedZeroEnergy f - signedZeroEnergy g) / 2

theorem tendsto_signedZeroEnergy_truncTest {f : ℝ → ℝ} (hf : ExpDecayTest f) :
    Tendsto (fun L : ℝ => signedZeroEnergy (truncTest f L)) atTop
      (𝓝 (signedZeroEnergy f)) := by
  have hp := tendsto_paperFT_truncTest hf (z := I/2) (by simp)
  have hm := tendsto_paperFT_truncTest hf (z := -I/2) (by simp [abs_div])
  have hcp := (Complex.continuous_conj.tendsto _).comp hp
  have hcm := (Complex.continuous_conj.tendsto _).comp hm
  exact ((Complex.continuous_re.tendsto _).comp (tendsto_W_truncTest hf)).sub
    ((Complex.continuous_re.tendsto _).comp ((hp.mul hcm).add (hm.mul hcp)))

theorem relativeLift_energy_eq_signedZeroEnergy {f : ℝ → ℝ}
    (hfd : ExpDecayTest f) {A : NNReal} (hf : LipschitzWith A f) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    sourceEnergy (relativeLift f hf hM hb) = signedZeroEnergy f := by
  have hl := (continuous_sourceEnergy.tendsto _).comp
    (bulkTestLift_tendsto hfd.1 hf hM hb)
  have hr := (tendsto_signedZeroEnergy_truncTest hfd).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [] with n
  change signedZeroEnergy (truncTest f n) =
    sourceEnergy (testLift (truncTest f n) (contDiff_truncTest hfd.1 n)
      (hasCompactSupport_truncTest f n))
  rw [testLift_energy, markovEnergy_eq_W_sub
    (contDiff_ofReal_truncTest hfd.1 n)
    ((hasCompactSupport_truncTest f n).comp_left Complex.ofReal_zero)]
  rw [weilPoleTerm_weilTest_eq (contDiff_ofReal_truncTest hfd.1 n).continuous
    ((hasCompactSupport_truncTest f n).comp_left Complex.ofReal_zero)]
  rfl

/-- The identity depends only on the literal source representative, not its construction. -/
theorem sourceEnergy_eq_signedZeroEnergy {f : ℝ → ℝ} {p : SourceGraph}
    (hf : ExpDecayTest f) (hl : ∃ A, LipschitzWith A f)
    (hb : ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) :
    sourceEnergy p = signedZeroEnergy f := by
  obtain ⟨A, hA⟩ := hl
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left
    ((abs_nonneg (f 0)).trans (hM 0)) (riemannKernelReal_pos 0)
  have heq : p = relativeLift f hA hM0 hM := by
    apply source_projection_injective
    exact Lp.ext (hp.trans (relativeLift_source_ae f hA hM0 hM).symm)
  rw [heq]
  exact relativeLift_energy_eq_signedZeroEnergy hf hA hM0 hM

/-- Mixed signed pairings agree on the actual graph, including the polar contribution. -/
theorem sourcePair_eq_signedZeroPair {f g : ℝ → ℝ} {p q : SourceGraph}
    (hf : ExpDecayTest f) (hg : ExpDecayTest g)
    (hfl : ∃ A, LipschitzWith A f) (hgl : ∃ B, LipschitzWith B g)
    (hfb : ∃ M, ∀ x, |f x| ≤ M * riemannKernelReal x)
    (hgb : ∃ N, ∀ x, |g x| ≤ N * riemannKernelReal x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f)
    (hq : q.val.fst =ᵐ[massMeasure] phiDoobInv g) :
    sourcePair p q = signedZeroPair f g := by
  have hsum : (p+q).val.fst =ᵐ[massMeasure] phiDoobInv (f+g) := by
    filter_upwards [hp, hq, Lp.coeFn_add p.val.fst q.val.fst] with x hx hy hz
    change (p.val.fst + q.val.fst) x = _
    rw [hz, Pi.add_apply, hx, hy]
    simp only [phiDoobInv, Pi.add_apply, add_div]
  have hsl : ∃ A, LipschitzWith A (f+g) := by
    obtain ⟨A, hA⟩ := hfl
    obtain ⟨B, hB⟩ := hgl
    exact ⟨A+B, hA.add hB⟩
  have hsb : ∃ M, ∀ x, |(f+g) x| ≤ M * riemannKernelReal x := by
    obtain ⟨M, hM⟩ := hfb
    obtain ⟨N, hN⟩ := hgb
    exact ⟨M+N, fun x => (abs_add_le _ _).trans (by nlinarith [hM x, hN x])⟩
  rw [sourcePair_polarization, sourceEnergy_eq_signedZeroEnergy (hf.add hg) hsl hsb hsum,
    sourceEnergy_eq_signedZeroEnergy hf hfl hfb hp,
    sourceEnergy_eq_signedZeroEnergy hg hgl hgb hq]
  rfl

end CHMDDoobGraph
end RHTower
