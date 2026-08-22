import GaloisForLFunctions.RHTower.SoninForbiddenClosedSum
import GaloisForLFunctions.RHTower.SoninL2ShellNull
import GaloisForLFunctions.HTGeometry.MonotoneDisjointInfiSup

/-!
# The Sonine carrier chain and Burnol's Proposition 4.6

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), Prop. 4.6:

> The union `⋃_{b>a} K_b` is dense in `K_a`.

with the proof:

> Generally speaking `⋂_{b>a}(A_b + B_b) = (⋂_{b>a}A_b) + (⋂_{b>a}B_b)` when we have vector spaces
> indexed by `b > a` with `A_{b₁} ⊂ A_{b₂}`, `B_{b₁} ⊂ B_{b₂}` for `b₁ < b₂` and `A_b ∩ B_b = {0}`
> for `b > a`.  We apply this to `A_b = L²(0,b;dt)` and `B_b = F₊(L²(0,b;dt))`, as
> `K_a = (A_a + B_a)^⊥`, `A_a = ∩_{b>a} A_b`, `B_a = ∩_{b>a} B_b`, and `A_a + B_a` is closed as a
> subspace of `L²(0,∞;dt)`.

This file carries out that proof for the corpus's concrete Sonine carrier
`centralSoninCarrier a = (centralPhysicalForbidden a)ᗮ ⊓ (centralFourierForbidden a)ᗮ`, the
full-line model of `K_a`.  The lattice identity is
`GaloisForLFunctions.HTGeometry.iInf_sup_eq_of_monotone_of_disjoint`, the closedness of `A_a + B_a`
is `isClosed_centralPhysicalForbidden_sup_centralFourierForbidden`, and the transversality is the
corpus's `physicalForbidden_inf_fourierForbidden_eq_bot`.

## Main results

* `mem_physicalForbidden_iff` — support characterisation of a time band.
* `centralPhysicalForbidden_mono`, `centralFourierForbidden_mono` — the two bands increase.
* `iInf_centralPhysicalForbidden`, `iInf_centralFourierForbidden` — the bands are the intersection
  of the strictly larger ones.
* `topologicalClosure_iSup_centralSoninCarrier` — **Burnol's Prop. 4.6**.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- A vector lies in a time band exactly when it vanishes almost everywhere outside it. -/
theorem mem_physicalForbidden_iff (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    f ∈ physicalForbidden s hs ↔ ∀ᵐ x ∂(volume : Measure ℝ), x ∉ s → (f : ℝ → ℂ) x = 0 := by
  constructor
  · intro hf
    have hcut : indicatorCutoff s hs f = f := by
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (physicalForbidden s hs).starProjection_eq_self_iff.mpr hf
    filter_upwards [indicatorCutoff_ae s hs f] with x hx
    intro hout
    rw [hcut] at hx
    simpa [hout] using hx
  · intro hf
    have hcut : indicatorCutoff s hs f = f := by
      apply Lp.ext
      filter_upwards [indicatorCutoff_ae s hs f, hf] with x hx hzero
      rw [hx]
      by_cases hmem : x ∈ s
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        exact (hzero hmem).symm
    exact ⟨f, hcut⟩

/-- A vector lies in a frequency band exactly when its Fourier transform lies in the time band. -/
theorem mem_fourierForbidden_iff (s : Set ℝ) (hs : MeasurableSet s) (f : SoninL2) :
    f ∈ fourierForbidden s hs ↔ fourierUnitary f ∈ physicalForbidden s hs := by
  have hcutF : f ∈ fourierForbidden s hs ↔ fourierCutoff s hs f = f :=
    ⟨fun hf => by
      rw [fourierCutoff_eq_fourierForbidden_starProjection]
      exact (fourierForbidden s hs).starProjection_eq_self_iff.mpr hf,
     fun hf => ⟨f, hf⟩⟩
  have hcutP : fourierUnitary f ∈ physicalForbidden s hs ↔
      indicatorCutoff s hs (fourierUnitary f) = fourierUnitary f :=
    ⟨fun hf => by
      rw [indicatorCutoff_eq_physicalForbidden_starProjection]
      exact (physicalForbidden s hs).starProjection_eq_self_iff.mpr hf,
     fun hf => ⟨fourierUnitary f, hf⟩⟩
  rw [hcutF, hcutP]
  constructor
  · intro h
    have := congrArg (fun g => fourierUnitary g) h
    simpa using this
  · intro h
    have : fourierUnitary.symm (indicatorCutoff s hs (fourierUnitary f)) =
        fourierUnitary.symm (fourierUnitary f) := by rw [h]
    simpa using this

/-- Time bands increase with the aperture. -/
theorem physicalForbidden_mono {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) : physicalForbidden s hs ≤ physicalForbidden t ht := by
  intro f hf
  rw [mem_physicalForbidden_iff] at hf ⊢
  filter_upwards [hf] with x hx hout
  exact hx fun hmem => hout (hst hmem)

theorem centralPhysicalForbidden_mono {a b : ℝ} (hab : a ≤ b) :
    centralPhysicalForbidden a ≤ centralPhysicalForbidden b :=
  physicalForbidden_mono _ _ (Set.Icc_subset_Icc (by linarith) hab)

theorem centralFourierForbidden_mono {a b : ℝ} (hab : a ≤ b) :
    centralFourierForbidden a ≤ centralFourierForbidden b := by
  intro f hf
  rw [centralFourierForbidden, mem_fourierForbidden_iff] at hf ⊢
  exact centralPhysicalForbidden_mono hab hf

/-- A vector in every strictly larger time band already lies in the given one. -/
theorem mem_centralPhysicalForbidden_of_forall_gt {a : ℝ} {f : SoninL2}
    (h : ∀ b : ℝ, a < b → f ∈ centralPhysicalForbidden b) : f ∈ centralPhysicalForbidden a := by
  rw [centralPhysicalForbidden, mem_physicalForbidden_iff]
  have hstep : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ Set.Icc (-(a + 1 / (n + 1))) (a + 1 / (n + 1)) → (f : ℝ → ℂ) x = 0 := by
    intro n
    have hlt : a < a + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have := h _ hlt
    rw [centralPhysicalForbidden, mem_physicalForbidden_iff] at this
    exact this
  rw [← ae_all_iff] at hstep
  filter_upwards [hstep] with x hx hout
  have habs : a < |x| := by
    by_contra hcon
    have hle : |x| ≤ a := not_lt.1 hcon
    exact hout ⟨(abs_le.1 hle).1, (abs_le.1 hle).2⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < |x| - a by linarith)
  refine hx n ?_
  intro hmem
  have h1 : a + 1 / ((n : ℝ) + 1) < |x| := by
    have : 1 / ((n : ℝ) + 1) < |x| - a := hn
    linarith
  have h2 : |x| ≤ a + 1 / ((n : ℝ) + 1) := abs_le.2 ⟨hmem.1, hmem.2⟩
  linarith

theorem iInf_centralPhysicalForbidden (a : ℝ) :
    (⨅ b : {b : ℝ // a < b}, centralPhysicalForbidden b.1) = centralPhysicalForbidden a := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [Submodule.mem_iInf] at hf
    exact mem_centralPhysicalForbidden_of_forall_gt fun b hb => hf ⟨b, hb⟩
  · exact le_iInf fun b => centralPhysicalForbidden_mono (le_of_lt b.2)

theorem iInf_centralFourierForbidden (a : ℝ) :
    (⨅ b : {b : ℝ // a < b}, centralFourierForbidden b.1) = centralFourierForbidden a := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rw [Submodule.mem_iInf] at hf
    rw [centralFourierForbidden, mem_fourierForbidden_iff]
    refine mem_centralPhysicalForbidden_of_forall_gt fun b hb => ?_
    have := hf ⟨b, hb⟩
    rwa [centralFourierForbidden, mem_fourierForbidden_iff] at this
  · exact le_iInf fun b => centralFourierForbidden_mono (le_of_lt b.2)

theorem centralSoninCarrier_eq_orthogonal_sup (a : ℝ) :
    centralSoninCarrier a =
      (centralPhysicalForbidden a ⊔ centralFourierForbidden a : Submodule ℂ SoninL2)ᗮ := by
  rw [centralSoninCarrier, Submodule.inf_orthogonal]

/-- **Burnol's Proposition 4.6.**  The union of the strictly smaller Sonine carriers is dense in
the Sonine carrier. -/
theorem topologicalClosure_iSup_centralSoninCarrier (a : ℝ) (ha : 0 < a) :
    (⨆ b : {b : ℝ // a < b}, centralSoninCarrier b.1).topologicalClosure =
      centralSoninCarrier a := by
  haveI : Nonempty {b : ℝ // a < b} := ⟨⟨a + 1, by linarith⟩⟩
  have hkey := topologicalClosure_iSup_orthogonal_sup_eq
    (A := fun b : {b : ℝ // a < b} => centralPhysicalForbidden b.1)
    (B := fun b : {b : ℝ // a < b} => centralFourierForbidden b.1)
    (fun i j hij => centralPhysicalForbidden_mono hij)
    (fun i j hij => centralFourierForbidden_mono hij)
    (fun i => by
      simpa [centralPhysicalForbidden, centralFourierForbidden] using
        physicalForbidden_inf_fourierForbidden_eq_bot i.1)
    (fun i => isClosed_centralPhysicalForbidden_sup_centralFourierForbidden i.1
      (lt_trans ha i.2))
  rw [iInf_centralPhysicalForbidden, iInf_centralFourierForbidden] at hkey
  rw [show (fun b : {b : ℝ // a < b} => centralSoninCarrier b.1) =
      fun b : {b : ℝ // a < b} =>
        (centralPhysicalForbidden b.1 ⊔ centralFourierForbidden b.1 : Submodule ℂ SoninL2)ᗮ from
    funext fun b => centralSoninCarrier_eq_orthogonal_sup b.1]
  rw [hkey, ← centralSoninCarrier_eq_orthogonal_sup]

end RHTower
