/-
# Lifting disk maps through `λ` (entry to the three-value Montel lift, `#30`)

With `λ : ℍ → ℂ∖{0,1}` now a covering map (`isCoveringMap_lambdaPunct`), the homotopy-lifting property
of covering spaces lets every continuous map from a (simply connected, locally path connected) **disk**
into `ℂ∖{0,1}` lift to an `ℍ`-valued map. This is the topological core of `normal_of_omitting_lift`'s
hypothesis: an omitting family `f_n : 𝔻 → ℂ∖{0,1}` lifts to `ℍ`-valued (hence, after the Cayley
identification `ℍ ≅ 𝔻`, bounded) maps `g_n` with `λ ∘ g_n = f_n`.

`exists_continuous_lift_disk`: the lift exists. (`ℍ`-valued continuous lift; its holomorphy — `λ` is a
local biholomorphism — and the bound via Cayley are the remaining analytic steps of `#30`.) Built on the
disk being contractible (`Convex.contractibleSpace`, hence simply connected) and open (locally path
connected), plus `λ` surjective (`lambdaPunct_surjective`) for the basepoint, fed to mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`.
-/
import Mathlib
import GaloisForLFunctions.Bottcher.ModularLambdaProperness
import GaloisForLFunctions.Bottcher.ModularLambdaCovering

open Metric UpperHalfPlane Filter Topology
open scoped UpperHalfPlane

namespace Bottcher

/-- **A continuous local section of a holomorphic local biholomorphism is holomorphic.** If `h` is
holomorphic with `h'(G z₀) ≠ 0`, `G` is continuous at `z₀`, and `h ∘ G` is holomorphic at `z₀`, then `G`
is holomorphic at `z₀`. Proof: `h` has a holomorphic local inverse `ψ` at `G z₀` (inverse function
theorem), and by continuity `G = ψ ∘ (h ∘ G)` near `z₀`, a composition of holomorphic maps. This is the
holomorphy step for the modular `λ`-lift (`#30`): `λ' ≠ 0` makes `λ` a local biholomorphism, so the
continuous lift `G` of a holomorphic `f` (with `λ ∘ G = f`) is automatically holomorphic. -/
theorem differentiableAt_lift {h G : ℂ → ℂ} {z₀ : ℂ}
    (hG : ContinuousAt G z₀)
    (hstr : HasStrictDerivAt h (deriv h (G z₀)) (G z₀))
    (hd0 : deriv h (G z₀) ≠ 0)
    (hanh : AnalyticAt ℂ h (G z₀))
    (hf : DifferentiableAt ℂ (fun z => h (G z)) z₀) :
    DifferentiableAt ℂ G z₀ := by
  set ψ := HasStrictDerivAt.localInverse h (deriv h (G z₀)) (G z₀) hstr hd0 with hψ
  have hψ_an : AnalyticAt ℂ ψ (h (G z₀)) := hanh.analyticAt_localInverse hd0
  have hlinv : ∀ᶠ x in 𝓝 (G z₀), ψ (h x) = x := hstr.eventually_left_inverse hd0
  have heq : (fun z => ψ (h (G z))) =ᶠ[𝓝 z₀] G := hG.eventually hlinv
  have hcomp : DifferentiableAt ℂ (fun z => ψ (h (G z))) z₀ :=
    (hψ_an.differentiableAt).comp z₀ hf
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- **Continuous lift of a disk map through `λ`.** Any continuous `F : 𝔻 → ℂ∖{0,1}` from a ball lifts to a
continuous `G : 𝔻 → ℍ` with `λ ∘ G = F`, by the covering-space lifting property
(`isCoveringMap_lambdaPunct` + the disk simply connected & locally path connected + `λ` surjective for the
basepoint). The topological heart of `#30`. -/
theorem exists_continuous_lift_disk {c : ℂ} {R : ℝ} (hR : 0 < R)
    (F : C(↥(ball c R), Punctured)) :
    ∃ G : C(↥(ball c R), ℍ), lambdaPunct ∘ G = F := by
  haveI : ContractibleSpace ↥(ball c R) :=
    (convex_ball c R).contractibleSpace (nonempty_ball.mpr hR)
  haveI : SimplyConnectedSpace ↥(ball c R) := inferInstance
  haveI : LocPathConnectedSpace ↥(ball c R) := isOpen_ball.locPathConnectedSpace
  haveI : Nonempty ↥(ball c R) := (nonempty_ball.mpr hR).to_subtype
  obtain ⟨a₀⟩ := (inferInstance : Nonempty ↥(ball c R))
  obtain ⟨e₀, he₀⟩ := lambdaPunct_surjective (F a₀)
  obtain ⟨G, ⟨_, hG⟩, _⟩ :=
    isCoveringMap_lambdaPunct.existsUnique_continuousMap_lifts F a₀ e₀ he₀
  exact ⟨G, hG⟩

/-- **Based continuous lift of a disk map through `λ`.** This is the sheet-selection form of
`exists_continuous_lift_disk`: if a basepoint preimage `e₀` is prescribed, the lifted disk map starts
at `e₀`.  The deck-normalized Montel assembly uses this to choose the lift sheet whose Cayley
coordinate lies in a strict subdisk. -/
theorem exists_continuous_lift_disk_based {c : ℂ} {R : ℝ} (hR : 0 < R)
    (F : C(↥(ball c R), Punctured)) (a₀ : ↥(ball c R)) (e₀ : ℍ)
    (he₀ : lambdaPunct e₀ = F a₀) :
    ∃ G : C(↥(ball c R), ℍ), G a₀ = e₀ ∧ lambdaPunct ∘ G = F := by
  haveI : ContractibleSpace ↥(ball c R) :=
    (convex_ball c R).contractibleSpace (nonempty_ball.mpr hR)
  haveI : SimplyConnectedSpace ↥(ball c R) := inferInstance
  haveI : LocPathConnectedSpace ↥(ball c R) := isOpen_ball.locPathConnectedSpace
  obtain ⟨G, hG, _⟩ :=
    isCoveringMap_lambdaPunct.existsUnique_continuousMap_lifts F a₀ e₀ he₀
  exact ⟨G, hG⟩

/-- The **Cayley transform** `w ↦ (w-i)/(w+i)`, mapping `ℍ` into the open unit disc. The bounded model of
`ℍ` used to turn an `ℍ`-valued lift into a `‖·‖ ≤ 1`-bounded one for `normal_of_omitting_lift` (`#30`). -/
noncomputable def cayley (w : ℂ) : ℂ := (w - Complex.I) / (w + Complex.I)

/-- **The Cayley transform maps `ℍ` strictly inside the unit disc**: `‖cayley w‖ < 1` for `Im w > 0`
(since `i` is strictly closer to `w` than `-i` is, `‖w-i‖ < ‖w+i‖`). Gives the `‖g‖ ≤ 1` bound of `#30`. -/
theorem cayley_norm_lt_one {w : ℂ} (hw : 0 < w.im) : ‖cayley w‖ < 1 := by
  have hden : w + Complex.I ≠ 0 := by
    intro h
    apply absurd hw
    rw [show w = -Complex.I by linear_combination h]
    simp
  rw [cayley, norm_div, div_lt_one (norm_pos_iff.mpr hden),
    Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im]
  nlinarith [hw]

/-- **The Cayley transform is holomorphic** away from `w = -i` (`w + i ≠ 0`). With `cayley_norm_lt_one`
this makes `g := cayley ∘ G` a bounded holomorphic disk map for the lift `G : 𝔻 → ℍ` (`#30`). -/
theorem cayley_differentiableAt {w : ℂ} (h : w + Complex.I ≠ 0) : DifferentiableAt ℂ cayley w := by
  unfold cayley
  exact (differentiableAt_id.sub_const _).div (differentiableAt_id.add_const _) h

/-- The **inverse Cayley transform** `ζ ↦ i(1+ζ)/(1-ζ)`, mapping `𝔻` back to `ℍ`. -/
noncomputable def cayleyInv (z : ℂ) : ℂ := Complex.I * ((1 + z) / (1 - z))

/-- **`cayleyInv ∘ cayley = id` on `ℍ`** (`w + i ≠ 0`). Combined with `μ := λ ∘ cayleyInv`, this gives
`μ ∘ (cayley ∘ G) = λ ∘ G = f` — the `EqOn` condition of `normal_of_omitting_lift` (`#30`). -/
theorem cayleyInv_cayley {w : ℂ} (h : w + Complex.I ≠ 0) : cayleyInv (cayley w) = w := by
  have h1 : (1 : ℂ) - cayley w ≠ 0 := by
    simp only [cayley, sub_ne_zero]
    intro hc
    rw [eq_div_iff h] at hc
    apply Complex.I_ne_zero
    linear_combination hc / 2
  have h2 : (w + Complex.I) - (w - Complex.I) ≠ 0 := by
    intro hc; apply Complex.I_ne_zero; linear_combination hc / 2
  rw [cayleyInv, cayley]
  field_simp
  ring

end Bottcher
