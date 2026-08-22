import GaloisForLFunctions.RHTower.SoninCarrierApertureChain

/-!
# The two ends of the Sonine chain

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), §2, records that the Sonine spaces form

> a strictly decreasing chain of non-trivial infinite dimensional subspaces of `K` with
> `K = ∪_{a>0} K_a`, `{0} = ∩_{a>0} K_a`

(the first equality being, as with `L_a = ∪_{b>a} L_b`, an equality of closures).

This file proves both ends for the corpus's concrete Sonine carrier.  The dense-union statement is
the `a ↓ 0` instance of the same lattice mechanism that gives Prop. 4.6: the intersection of the
strictly larger time bands is the time band at `0`, which is trivial because a single point is
Lebesgue-null.

## Main results

* `centralPhysicalForbidden_zero`, `centralFourierForbidden_zero`
* `topologicalClosure_iSup_pos_centralSoninCarrier` — `K = ∪_{a>0} K_a`.
* `iInf_pos_centralSoninCarrier` — `{0} = ∩_{a>0} K_a`.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The time band of zero aperture is trivial. -/
theorem centralPhysicalForbidden_zero : centralPhysicalForbidden (0 : ℝ) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [centralPhysicalForbidden, mem_physicalForbidden_iff] at hf
  rw [Submodule.mem_bot]
  refine Lp.ext ?_
  have hnull : (volume : Measure ℝ) (Set.Icc (-(0 : ℝ)) 0) = 0 := by
    simp
  filter_upwards [hf, compl_mem_ae_iff.2 hnull] with x hx hout
  simpa using hx hout

/-- The frequency band of zero aperture is trivial. -/
theorem centralFourierForbidden_zero : centralFourierForbidden (0 : ℝ) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [centralFourierForbidden, mem_fourierForbidden_iff] at hf
  have : fourierUnitary f ∈ centralPhysicalForbidden (0 : ℝ) := hf
  rw [centralPhysicalForbidden_zero, Submodule.mem_bot] at this
  rw [Submodule.mem_bot]
  have := congrArg (fun g => fourierUnitary.symm g) this
  simpa using this

/-- **`K = ∪_{a>0} K_a`.**  The Sonine carriers of positive aperture have dense union. -/
theorem topologicalClosure_iSup_pos_centralSoninCarrier :
    (⨆ a : {a : ℝ // 0 < a}, centralSoninCarrier a.1).topologicalClosure = ⊤ := by
  haveI : Nonempty {a : ℝ // (0 : ℝ) < a} := ⟨⟨1, by norm_num⟩⟩
  have hkey := topologicalClosure_iSup_orthogonal_sup_eq
    (A := fun b : {b : ℝ // (0 : ℝ) < b} => centralPhysicalForbidden b.1)
    (B := fun b : {b : ℝ // (0 : ℝ) < b} => centralFourierForbidden b.1)
    (fun i j hij => centralPhysicalForbidden_mono hij)
    (fun i j hij => centralFourierForbidden_mono hij)
    (fun i => by
      simpa [centralPhysicalForbidden, centralFourierForbidden] using
        physicalForbidden_inf_fourierForbidden_eq_bot i.1)
    (fun i => isClosed_centralPhysicalForbidden_sup_centralFourierForbidden i.1 i.2)
  rw [iInf_centralPhysicalForbidden, iInf_centralFourierForbidden,
    centralPhysicalForbidden_zero, centralFourierForbidden_zero, bot_sup_eq,
    Submodule.bot_orthogonal_eq_top] at hkey
  rw [show (fun b : {b : ℝ // (0 : ℝ) < b} => centralSoninCarrier b.1) =
      fun b : {b : ℝ // (0 : ℝ) < b} =>
        (centralPhysicalForbidden b.1 ⊔ centralFourierForbidden b.1 : Submodule ℂ SoninL2)ᗮ from
    funext fun b => centralSoninCarrier_eq_orthogonal_sup b.1]
  exact hkey

/-- **`{0} = ∩_{a>0} K_a`.**  A vector in every Sonine carrier vanishes. -/
theorem iInf_pos_centralSoninCarrier :
    (⨅ a : {a : ℝ // (0 : ℝ) < a}, centralSoninCarrier a.1) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  rw [Submodule.mem_iInf] at hf
  rw [Submodule.mem_bot]
  have hcut : ∀ n : ℕ, indicatorCutoff (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))
      measurableSet_Icc f = 0 := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmem := (hf ⟨(n : ℝ) + 1, hpos⟩).1
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff
      (K := physicalForbidden (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc)).mpr hmem
  have hae : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) → (f : ℝ → ℂ) x = 0 := by
    intro n
    filter_upwards [indicatorCutoff_ae (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))
      measurableSet_Icc f, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx hz
    intro hmem
    rw [hcut n, hz, Set.indicator_of_mem hmem] at hx
    simpa using hx.symm
  rw [← ae_all_iff] at hae
  refine Lp.ext ?_
  filter_upwards [hae, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx _hz
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  have hmem : x ∈ Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    have h1 : |x| ≤ (n : ℝ) + 1 := by linarith
    exact ⟨(abs_le.1 h1).1, (abs_le.1 h1).2⟩
  simp [hx n hmem]

end RHTower
