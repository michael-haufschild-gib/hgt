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

/-- **Neumann-shift strong limit.**  `(I + eps A)⁻¹ → I` strongly as `eps → 0+`, in the coordinate
of the bounded resolvent `B` with `A = rho + B⁻¹`.  Same chain as `tendsto_resolventFamily_id`,
with the Neumann-shift symbol in place of the resolvent-family symbol. -/
theorem tendsto_neumannShiftFamily_id {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {B : H →L[ℂ] H}
    (hsa : IsSelfAdjoint B) (hinj : Function.Injective B)
    {M rho : ℝ} (hspec : spectrum ℝ B ⊆ Set.Icc 0 M) (v : H) :
    Tendsto (fun eps : ℝ => cfc (fun x : ℝ => x / (eps + (1 + eps * rho) * x)) B v)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 v) := by
  have hgood : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < eps ∧ (1 : ℝ) / 2 ≤ 1 + eps * rho := by
    have hc : ContinuousAt (fun eps : ℝ => 1 + eps * rho) 0 := by fun_prop
    have hlim := hc.tendsto
    simp only [zero_mul, add_zero] at hlim
    filter_upwards [self_mem_nhdsWithin,
      (hlim.mono_left nhdsWithin_le_nhds).eventually
        (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))] with eps he hd
    exact ⟨he, hd.le⟩
  have hden : ∀ eps : ℝ, 0 < eps → (1 : ℝ) / 2 ≤ 1 + eps * rho →
      ∀ x ∈ spectrum ℝ B, (0 : ℝ) < eps + (1 + eps * rho) * x := by
    intro eps he hd x hx
    have hx0 : 0 ≤ x := (hspec hx).1
    nlinarith
  have hcont : ∀ eps : ℝ, 0 < eps → (1 : ℝ) / 2 ≤ 1 + eps * rho →
      ContinuousOn (fun x : ℝ => x / (eps + (1 + eps * rho) * x)) (spectrum ℝ B) := by
    intro eps he hd
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hden eps he hd x hx).ne'
  have hbound : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖cfc (fun x : ℝ => x / (eps + (1 + eps * rho) * x)) B‖ ≤ 2 := by
    filter_upwards [hgood] with eps hg
    refine norm_cfc_le_of_forall_le _ B (hcont eps hg.1 hg.2) hsa fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact abs_neumannFamilySymbol_le hg.1 hg.2 (hspec hx).1
  have hnorm : Tendsto
      (fun eps : ℝ => ‖(cfc (fun x : ℝ => x / (eps + (1 + eps * rho) * x)) B
        - ContinuousLinearMap.id ℂ H) ∘L B‖) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have hrw : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖cfc (fun x : ℝ =>
            -(eps * (x * (1 + rho * x)) / (eps + (1 + eps * rho) * x))) B‖
          = ‖(cfc (fun x : ℝ => x / (eps + (1 + eps * rho) * x)) B
              - ContinuousLinearMap.id ℂ H) ∘L B‖ := by
      filter_upwards [hgood] with eps hg
      have hcongr : cfc (fun x : ℝ =>
            -(eps * (x * (1 + rho * x)) / (eps + (1 + eps * rho) * x))) B
          = cfc (fun x : ℝ => (x / (eps + (1 + eps * rho) * x) - 1) * x) B :=
        cfc_congr fun x hx => (neumannSymbol_sub_one_mul (hden eps hg.1 hg.2 x hx).ne').symm
      rw [hcongr, cfc_sub_one_mul_self _ B hsa (hcont eps hg.1 hg.2)]
      rfl
    refine Tendsto.congr' hrw ?_
    refine tendsto_norm_cfc_zero _ B hsa ?_ fun delta hdelta => ?_
    · filter_upwards [hgood] with eps hg
      exact (ContinuousOn.div (by fun_prop) (by fun_prop)
        fun x hx => (hden eps hg.1 hg.2 x hx).ne').neg
    · filter_upwards [eventually_forall_abs_neumannSymbol_le rho M hdelta] with eps hsm x hx
      rw [Real.norm_eq_abs, abs_neg]
      exact hsm x (hspec hx)
  exact tendsto_id_of_norm_comp_tendsto_zero hsa hinj (by norm_num) hbound hnorm v

end GaloisForLFunctions.RHTower
