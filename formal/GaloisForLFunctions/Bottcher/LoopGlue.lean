/-
# Abstract loop-glue: cyclic cocycle → global single-valued lift (hDisc, cover assembly)

Combines the two atoms — `Cocycle.exists_cocycle_primitive` (trivialize the closed cocycle) and
`SheafGlue.analyticOnNhd_glue_finite` (glue pairwise-agreeing branches) — into the abstract cover-assembly
of the dyadic lift: a finite **cyclic** family of analytic branches `β i` on opens `U i` (only consecutive
patches overlap), related on consecutive overlaps by unit constants `u i` (`β i = u i · β (i+1)`) that
close up (`∏ u = 1`), glues to a single global analytic `F` on `⋃ U i` with `F = c i · β i` on each patch.

This is `hliftF`'s assembly with the analysis abstracted away; instantiating `U/β/u` from the actual basin
cover (with `∏ u = exp(2πi) = 1` from `CoverConstruction.no_singlevalued_branch_of_dyadic_period`) produces
the global single-valued `φ̃c`. The remaining hDisc work is exactly that geometric instantiation, plus the
deck map and figure-eight invariance.
-/
import GaloisForLFunctions.Bottcher.SheafGlue
import GaloisForLFunctions.Bottcher.Cocycle

open Set

namespace Bottcher

/-- **Global single-valued lift from a closed cyclic branch-cocycle.** A cyclic family of analytic branches
`β i` on opens `U i` (`i : Fin (n+1)`), with consecutive-overlap cocycle `β i = u i · β (i+1)` on
`U i ∩ U (i+1)`, only consecutive patches overlapping (`hdisj`), `u i ≠ 0`, and the cocycle closed
(`∏ u = 1`), assembles into a single global analytic `F` on `⋃ U i` with `F = c i · β i` on each `U i`
(`c` the cocycle primitive, nonzero). Proof: `exists_cocycle_primitive` gives `c` with `c(i+1)=c(i)u(i)`,
making the adjusted branches `c i · β i` agree pairwise on overlaps (consecutive by the cocycle, others
vacuous by disjointness); `analyticOnNhd_glue_finite` then glues them. -/
theorem exists_global_lift_of_cyclic_cocycle {n : ℕ} (U : Fin (n + 1) → Set ℂ) (β : Fin (n + 1) → ℂ → ℂ)
    (u : Fin (n + 1) → ℂ)
    (hUo : ∀ i, IsOpen (U i)) (hβ : ∀ i, AnalyticOnNhd ℂ (β i) (U i))
    (hu : ∀ i, u i ≠ 0) (hprod : ∏ i, u i = 1)
    (hcoc : ∀ i, Set.EqOn (β i) (fun z => u i * β (i + 1) z) (U i ∩ U (i + 1)))
    (hdisj : ∀ i j, (U i ∩ U j).Nonempty → (j = i ∨ j = i + 1 ∨ i = j + 1)) :
    ∃ (F : ℂ → ℂ) (c : Fin (n + 1) → ℂ), AnalyticOnNhd ℂ F (⋃ i, U i) ∧
      (∀ i, c i ≠ 0) ∧ (∀ i, Set.EqOn F (fun z => c i * β i z) (U i)) ∧
      (∀ i, ‖c i‖ = ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val < i.val), ‖u j‖) := by
  classical
  obtain ⟨c, hc0, hcp, hcnorm⟩ := exists_cocycle_primitive u hu hprod
  have hagree : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      Set.EqOn (fun z => c i * β i z) (fun z => c j * β j z) (U i ∩ U j) := by
    intro i _ j _ z hz
    rcases hdisj i j ⟨z, hz⟩ with rfl | rfl | rfl
    · rfl
    · show c i * β i z = c (i + 1) * β (i + 1) z
      have hb := hcoc i hz
      rw [hb, hcp i]; ring
    · show c (j + 1) * β (j + 1) z = c j * β j z
      have hz' : z ∈ U j ∩ U (j + 1) := ⟨hz.2, hz.1⟩
      have hb := hcoc j hz'
      rw [hb, hcp j]; ring
  have hfan : ∀ i ∈ Finset.univ, AnalyticOnNhd ℂ (fun z => c i * β i z) (U i) :=
    fun i _ => analyticOnNhd_const.mul (hβ i)
  obtain ⟨F, hFan, hFeq⟩ :=
    analyticOnNhd_glue_finite Finset.univ U (fun i z => c i * β i z) (fun i _ => hUo i) hfan hagree
  have hunion : (⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))), U i) = ⋃ i, U i := by simp
  rw [hunion] at hFan
  exact ⟨F, c, hFan, hc0, fun i => hFeq i (Finset.mem_univ i), hcnorm⟩

/-- **Single-valued Böttcher lift from a cyclic green-conjugate cover.** Specializes the loop-glue to the
disconnected case: a cyclic family of green-conjugate branches `F i` (`Re (F i) = G_c` on `U i`, the
modulus condition), with the multiplicative overlap cocycle `exp(F i) = u i · exp(F (i+1))` of UNIT
constants (`‖u i‖ = 1`, since the `F`-cocycle is imaginary, `greenConjugate_sub_imaginary_const`) closing
up (`∏ u = 1`, the absorbed period), assembles to a global single-valued `φ̃` on `⋃ U i`, nowhere zero,
with `‖φ̃ w‖ = exp(G_c w)` — exactly the lift `scaling_from_modulus_preserved` / `hscale_germ_of_greenConjugate`
consume. The modulus is exact because the cocycle primitive `c i` has `‖c i‖ = ∏ ‖u j‖ = 1`. -/
theorem exists_bottcherLift_of_cyclic_greenConjugate {c : ℂ} {n : ℕ} (U : Fin (n + 1) → Set ℂ)
    (F : Fin (n + 1) → ℂ → ℂ) (u : Fin (n + 1) → ℂ)
    (hUo : ∀ i, IsOpen (U i)) (hFan : ∀ i, AnalyticOnNhd ℂ (F i) (U i))
    (hFre : ∀ i, Set.EqOn (fun w => (F i w).re) (greenLimit c) (U i))
    (hu1 : ∀ i, ‖u i‖ = 1) (hprod : ∏ i, u i = 1)
    (hcoc : ∀ i, Set.EqOn (fun z => Complex.exp (F i z))
        (fun z => u i * Complex.exp (F (i + 1) z)) (U i ∩ U (i + 1)))
    (hdisj : ∀ i j, (U i ∩ U j).Nonempty → (j = i ∨ j = i + 1 ∨ i = j + 1)) :
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ (⋃ i, U i) ∧
      (∀ w ∈ ⋃ i, U i, φ w ≠ 0) ∧
      (∀ w ∈ ⋃ i, U i, ‖φ w‖ = Real.exp (greenLimit c w)) := by
  have hune : ∀ i, u i ≠ 0 := by
    intro i h; have := hu1 i; rw [h, norm_zero] at this; exact zero_ne_one this
  obtain ⟨φ, cc, hφan, hcc0, hφeq, hccnorm⟩ :=
    exists_global_lift_of_cyclic_cocycle U (fun i z => Complex.exp (F i z)) u hUo
      (fun i => (hFan i).cexp) hune hprod hcoc hdisj
  have hccnorm1 : ∀ i, ‖cc i‖ = 1 := by
    intro i; rw [hccnorm i]; exact Finset.prod_eq_one (fun j _ => hu1 j)
  refine ⟨φ, hφan, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    rw [hφeq i hi]
    exact mul_ne_zero (hcc0 i) (Complex.exp_ne_zero _)
  · intro w hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    rw [hφeq i hi, norm_mul, hccnorm1 i, one_mul, Complex.norm_exp]
    exact congrArg Real.exp (hFre i hi)

/-- **Single-valued lift from the ADDITIVE green-conjugate cocycle** — the form the existing machinery
produces. `greenConjugate_sub_imaginary_const` gives, on each consecutive overlap, the imaginary jump
`a i` with `F i = F (i+1) + a i`, `Re (a i) = 0`; the period machinery gives `∑ a i = k·2πi` (integer
multiple, from the dyadic monodromy over the cover loop). Then the green-conjugate branches assemble to the
global single-valued `φ̃` on `⋃ U i`, nowhere zero, with `‖φ̃ w‖ = exp(G_c w)`. Converts to the
multiplicative form via `u i = exp(a i)` (`‖u i‖ = exp(Re a i) = 1`, `∏ u = exp(∑ a) = exp(k·2πi) = 1` by
`prod_exp_eq_one_of_sum_eq_int_two_pi_I`). The cleanest hDisc-lift interface: it consumes exactly the
green-conjugate cocycle + the integer period, leaving only the basin sector-cover and the period value
`∑ a i = k·2πi` to instantiate. -/
theorem exists_bottcherLift_of_cyclic_greenConjugate_additive {c : ℂ} {n : ℕ} (k : ℤ)
    (U : Fin (n + 1) → Set ℂ) (F : Fin (n + 1) → ℂ → ℂ) (a : Fin (n + 1) → ℂ)
    (hUo : ∀ i, IsOpen (U i)) (hFan : ∀ i, AnalyticOnNhd ℂ (F i) (U i))
    (hFre : ∀ i, Set.EqOn (fun w => (F i w).re) (greenLimit c) (U i))
    (haim : ∀ i, (a i).re = 0)
    (hper : ∑ i, a i = (k : ℂ) * (2 * Real.pi * Complex.I))
    (hcoc : ∀ i, Set.EqOn (F i) (fun z => F (i + 1) z + a i) (U i ∩ U (i + 1)))
    (hdisj : ∀ i j, (U i ∩ U j).Nonempty → (j = i ∨ j = i + 1 ∨ i = j + 1)) :
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ (⋃ i, U i) ∧
      (∀ w ∈ ⋃ i, U i, φ w ≠ 0) ∧
      (∀ w ∈ ⋃ i, U i, ‖φ w‖ = Real.exp (greenLimit c w)) := by
  refine exists_bottcherLift_of_cyclic_greenConjugate U F (fun i => Complex.exp (a i))
    hUo hFan hFre (fun i => by rw [Complex.norm_exp, haim]; exact Real.exp_zero) ?_ ?_ hdisj
  · exact prod_exp_eq_one_of_sum_eq_int_two_pi_I Finset.univ a k hper
  · intro i z hz
    show Complex.exp (F i z) = Complex.exp (a i) * Complex.exp (F (i + 1) z)
    rw [hcoc i hz, Complex.exp_add]; ring

end Bottcher
