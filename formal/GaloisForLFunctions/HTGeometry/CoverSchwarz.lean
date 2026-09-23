import GaloisForLFunctions.HTGeometry.OrderNSchwarz

/-!
# The Schwarz estimate on a finite cover

Composing the polydisc Schwarz lemma with a cover: if a function has vanishing jets of order below
`N` at every centre of a cover of a set `K` by balls of radius `r`, and is bounded by `M` on the
concentric balls of radius `R > r`, then it is smaller than `M` by the factor `(r/R)^N` everywhere
on `K`.

* **`norm_le_of_cover_schwarz`**.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **The Schwarz estimate transported along a cover.** -/
theorem norm_le_of_cover_schwarz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F)
    {ι : Type*} (c : ι → E) {r R M : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 0 < R)
    {N : ℕ}
    (hbd : ∀ i, ∀ w : E, ‖w‖ ≤ R → ‖F (c i + w)‖ ≤ M)
    (hvan : ∀ i, ∀ k, k < N → iteratedFDeriv ℂ k F (c i) = 0)
    {K : Set E} (hcov : ∀ z ∈ K, ∃ i, ‖z - c i‖ ≤ r) :
    ∀ z ∈ K, ‖F z‖ ≤ M * (r / R) ^ N / (1 - r / R) := by
  have hq0 : 0 ≤ r / R := by positivity
  have hq1 : r / R < 1 := by rw [div_lt_one hR]; exact hrR
  have hden : 0 < 1 - r / R := by linarith
  intro z hz
  obtain ⟨i, hi⟩ := hcov z hz
  have hM : 0 ≤ M := le_trans (norm_nonneg (F (c i + 0)))
    (hbd i 0 (by simpa using hR.le))
  set y : E := z - c i with hy
  have hzy : z = c i + y := by rw [hy]; abel
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hzy, hy0, add_zero]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h1 : ‖F (c i)‖ ≤ M := by
        have := hbd i 0 (by simpa using hR.le)
        simpa using this
      have h2 : M ≤ M * (r / R) ^ (0 : ℕ) / (1 - r / R) := by
        rw [pow_zero, mul_one, le_div_iff₀ hden]
        nlinarith
      exact h1.trans h2
    · have hz0 : iteratedFDeriv ℂ 0 F (c i) = 0 := hvan i 0 hN
      have hFz : F (c i) = 0 := by
        have := congrArg (fun T => T (fun _ : Fin 0 => (0 : E))) hz0
        simpa using this
      rw [hFz]
      simp only [norm_zero]
      positivity
  · have hyr : ‖y‖ < R := lt_of_le_of_lt hi hrR
    have hmain := norm_le_of_iteratedFDeriv_vanish hF hR (hbd i) (hvan i) hy0 hyr
    rw [hzy]
    refine hmain.trans ?_
    have hyq : ‖y‖ / R ≤ r / R := by gcongr
    have hyq0 : (0 : ℝ) ≤ ‖y‖ / R := by positivity
    have hden' : 0 < 1 - ‖y‖ / R := by linarith
    calc M * (‖y‖ / R) ^ N / (1 - ‖y‖ / R)
        ≤ M * (r / R) ^ N / (1 - ‖y‖ / R) := by gcongr
      _ ≤ M * (r / R) ^ N / (1 - r / R) := by gcongr

end GaloisForLFunctions.HTGeometry
