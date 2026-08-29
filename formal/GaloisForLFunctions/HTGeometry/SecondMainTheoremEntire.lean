import GaloisForLFunctions.HTGeometry.SecondMainTheoremChain

/-!
# The second main theorem for an entire function

Every meromorphy side condition of `mul_characteristic_le_of_separated` is automatic when `f` is
entire: sums, differences, quotients and inverses of meromorphic germs are meromorphic, and the
derivative of an entire function is entire.  What is left is the analytic content — the
first-main-theorem defect `hfmt` and the requirement that `f'` not vanish identically near the
circle.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric ValueDistribution MeromorphicOn Filter

/-- **The second main theorem for an entire function.** -/
theorem mul_characteristic_le_of_separated_entire
    {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {δ r K : ℝ} (hδ : 0 < δ) (hr : r ≠ 0)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hf : Differentiable ℂ f)
    (hfmt : ∀ j : Fin q, characteristic f ⊤ r ≤ characteristic f (A j : WithTop ℂ) r + K)
    (hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0) :
    (q : ℝ) * characteristic f ⊤ r
      ≤ (∑ j, logCounting f (A j : WithTop ℂ) r)
        + (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
        + proximity (fun z => (deriv f z)⁻¹) ⊤ r
        + ((q : ℝ) * K + (q : ℝ) * Real.posLog (2 / δ)
            + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 + Real.log (q : ℝ)) := by
  classical
  have hmf : ∀ z : ℂ, MeromorphicAt f z := fun z => (hf.analyticAt z).meromorphicAt
  have hmd : ∀ z : ℂ, MeromorphicAt (deriv f) z := fun z => ((hf.deriv).analyticAt z).meromorphicAt
  have hsubj : ∀ (j : Fin q) (z : ℂ), MeromorphicAt (fun w => f w - A j) z := by
    intro j z
    exact (hmf z).sub (analyticAt_const.meromorphicAt)
  have hquot : ∀ (j : Fin q) (z : ℂ), MeromorphicAt (fun w => deriv f w / (f w - A j)) z := by
    intro j z
    exact (hmd z).div (hsubj j z)
  refine mul_characteristic_le_of_separated A hδ hr hsep ?_ hfmt hcod ?_ ?_ ?_
  · intro j z _
    exact (hsubj j z).inv
  · intro z
    have hfam : ∀ j ∈ (Finset.univ : Finset (Fin q)),
        MeromorphicAt (fun w => deriv f w / (f w - A j)) z := fun j _ => hquot j z
    have hsum := MeromorphicAt.sum hfam
    have heq : (fun w : ℂ => ∑ j, deriv f w / (f w - A j))
        = ∑ j ∈ (Finset.univ : Finset (Fin q)), fun w : ℂ => deriv f w / (f w - A j) := by
      funext w
      simp [Finset.sum_apply]
    rw [heq]
    exact hsum
  · intro z
    exact (hmd z).inv
  · intro j z
    exact hquot j z


/-- **The second main theorem for an entire function, with the first-main-theorem defect
discharged.**  The only remaining hypothesis is that `f'` does not vanish identically near the
circle. -/
theorem exists_mul_characteristic_le_of_separated_entire
    {f : ℂ → ℂ} {q : ℕ} (A : Fin q → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hf : Differentiable ℂ f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, r ≠ 0 →
      (∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0) →
      (q : ℝ) * characteristic f ⊤ r
        ≤ (∑ j, logCounting f (A j : WithTop ℂ) r)
          + (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
          + proximity (fun z => (deriv f z)⁻¹) ⊤ r
          + ((q : ℝ) * K + (q : ℝ) * Real.posLog (2 / δ)
              + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 + Real.log (q : ℝ)) := by
  classical
  have hmf : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  set Kj : Fin q → ℝ := fun j =>
    (Real.posLog ‖A j‖ + Real.log 2)
      + max |Real.log ‖((f - fun _ : ℂ => A j) : ℂ → ℂ) 0‖|
        |Real.log ‖meromorphicTrailingCoeffAt ((f - fun _ : ℂ => A j) : ℂ → ℂ) 0‖| with hKj
  set K : ℝ := ∑ j, |Kj j| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hKle : ∀ j, Kj j ≤ K :=
    fun j => le_trans (le_abs_self _)
      (Finset.single_le_sum (fun i _ => abs_nonneg (Kj i)) (Finset.mem_univ j))
  refine ⟨K, hK0, fun r hr hcod => ?_⟩
  refine mul_characteristic_le_of_separated_entire A hδ hr hsep hf ?_ hcod
  intro j
  have hg : Meromorphic ((f - fun _ : ℂ => A j) : ℂ → ℂ) := by
    intro z
    exact (hmf z).sub (analyticAt_const.meromorphicAt)
  have hbase := characteristic_top_le_characteristic_coe (f := f) (a₀ := A j) (r := r) hmf hg
  have := hKle j
  rw [hKj] at this
  linarith [hbase, this]

end GaloisForLFunctions.HTGeometry
