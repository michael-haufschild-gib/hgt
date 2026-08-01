import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventJetCompletion
import GaloisForLFunctions.HTGeometry.CfcNormBound
import GaloisForLFunctions.HTGeometry.CompactOperatorDiscreteSpectrum

/-!
# The strong resolvent limit in resolvent coordinates

For an injective self-adjoint operator `B` with spectrum in `[0, M]`, the family with symbol
`(s - rho) x / (1 + s x)` converges strongly to the identity as `s → ∞`.

Read at `B = (A - rho)⁻¹` and `s = rho - lambda`, this is `(-lambda)(A - lambda)⁻¹ → I` strongly
for a self-adjoint `A` bounded below.  Nothing unbounded is constructed: the whole statement lives
in the coordinate of the bounded resolvent.

The limit is strong and not uniform for one reason only — the symbols do not converge at the
spectral accumulation point `0` — and the factor `B` in the composition is what removes that point.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology GaloisForLFunctions.HTGeometry

/-- **Strong resolvent limit.**  A uniformly bounded resolvent family converges strongly to the
identity: the symbols are uniformly bounded on the spectrum, their difference from one vanishes
uniformly after multiplication by the coordinate, and the range of `B` is dense. -/
theorem tendsto_resolventFamily_id {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) (hinj : Function.Injective B)
    {M rho : ℝ} (hspec : spectrum ℝ B ⊆ Set.Icc 0 M) (v : H) :
    Tendsto (fun s : ℝ => cfc (fun x : ℝ => (s - rho) * x / (1 + s * x)) B v) atTop (𝓝 v) := by
  have hden : ∀ s : ℝ, 1 ≤ s → ∀ x ∈ spectrum ℝ B, (0 : ℝ) < 1 + s * x := by
    intro s hs x hx
    have hx0 : 0 ≤ x := (hspec hx).1
    nlinarith
  have hcont : ∀ s : ℝ, 1 ≤ s →
      ContinuousOn (fun x : ℝ => (s - rho) * x / (1 + s * x)) (spectrum ℝ B) := by
    intro s hs
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hden s hs x hx).ne'
  have hbound : ∀ᶠ s : ℝ in atTop,
      ‖cfc (fun x : ℝ => (s - rho) * x / (1 + s * x)) B‖ ≤ 1 + |rho| := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    refine norm_cfc_le_of_forall_le _ B (hcont s hs) hsa fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact abs_resolventFamilySymbol_le hs (hspec hx).1
  have hnorm : Tendsto
      (fun s : ℝ => ‖(cfc (fun x : ℝ => (s - rho) * x / (1 + s * x)) B
        - ContinuousLinearMap.id ℂ H) ∘L B‖) atTop (𝓝 0) := by
    have hrw : ∀ᶠ s : ℝ in atTop,
        ‖cfc (fun x : ℝ => -(x * (1 + rho * x) / (1 + s * x))) B‖
          = ‖(cfc (fun x : ℝ => (s - rho) * x / (1 + s * x)) B
              - ContinuousLinearMap.id ℂ H) ∘L B‖ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      have hcongr : cfc (fun x : ℝ => -(x * (1 + rho * x) / (1 + s * x))) B
          = cfc (fun x : ℝ => ((s - rho) * x / (1 + s * x) - 1) * x) B :=
        cfc_congr fun x hx => (resolventSymbol_sub_one_mul (hden s hs x hx).ne').symm
      rw [hcongr, cfc_sub_one_mul_self _ B hsa (hcont s hs)]
      rfl
    refine Tendsto.congr' hrw ?_
    refine tendsto_norm_cfc_zero _ B hsa ?_ fun ε hε => ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      exact (ContinuousOn.div (by fun_prop) (by fun_prop)
        fun x hx => (hden s hs x hx).ne').neg
    · filter_upwards [eventually_forall_abs_resolventSymbol_le rho M hε] with s hsm x hx
      rw [Real.norm_eq_abs, abs_neg]
      exact hsm x (hspec hx)
  exact tendsto_id_of_norm_comp_tendsto_zero hsa hinj
    (by nlinarith [abs_nonneg rho] : (1 : ℝ) ≤ 1 + |rho|) hbound hnorm v

end GaloisForLFunctions.RHTower
