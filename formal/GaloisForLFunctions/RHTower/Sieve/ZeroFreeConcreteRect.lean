import GaloisForLFunctions.RHTower.Sieve.InvZetaEdgeBounds

/-!
# The concrete rectangle is zero-free

The rectangle the assembly uses is

    [ 1 - c₀/(16 log⁹N) ,  1 + c₀/(2 log⁹N) ] × [ -T , T ],     3 + 2T ≤ N.

`exists_zero_free_rect` cannot be used for it: the `δ` it produces comes from thickening a segment
of half-length `T`, so it shrinks with the truncation height in an uncontrolled way and can never be
compared with `c₀/(16 log⁹N)`.  What is needed instead is the *quantitative* region, and again the
split at height `1`: above it `riemannZeta_ne_zero_of_re_gt`, below it the compactness box, whose
`δ₀` is a fixed number and so does need to be compared — once — with `c₀/(16 log⁹N)`.
-/

namespace RHTower.Sieve

open Complex

/-- **Zero-freeness of the concrete rectangle.**  Every hypothesis is arithmetic in `N` and `T`
except the single compatibility condition `c₀/(16 log⁹N) ≤ δ₀`, which holds for all large `N`. -/
theorem zero_free_concrete_rect {N : ℕ} {δ₀ T : ℝ} (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N)
    (hbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → s ≠ 1 → riemannZeta s ≠ 0)
    (hfit : zeroFreeConst / (16 * (Real.log N) ^ 9) ≤ δ₀)
    (hT0 : 0 ≤ T) (hTN : 3 + 2 * T ≤ (N : ℝ)) :
    ∀ s ∈ Set.uIcc (1 - zeroFreeConst / (16 * (Real.log N) ^ 9))
        (1 + zeroFreeConst / (2 * (Real.log N) ^ 9)) ×ℂ Set.uIcc (-T) T,
      s ≠ 1 → riemannZeta s ≠ 0 := by
  have hA0 := zeroFreeConst_pos
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hL9 : (0 : ℝ) < (Real.log N) ^ 9 := by positivity
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log N) ^ 9) := by positivity
  have h2 : (0 : ℝ) < zeroFreeConst / (2 * (Real.log N) ^ 9) := by positivity
  have hcd : 1 - zeroFreeConst / (16 * (Real.log N) ^ 9)
      ≤ 1 + zeroFreeConst / (2 * (Real.log N) ^ 9) := by linarith
  have hcmp : zeroFreeConst / (2 * (Real.log N) ^ 9)
      < zeroFreeConst / (16 * (Real.log N) ^ 9) * 8 + zeroFreeConst / (16 * (Real.log N) ^ 9) := by
    have heq : zeroFreeConst / (2 * (Real.log N) ^ 9)
        = zeroFreeConst / (16 * (Real.log N) ^ 9) * 8 := by
      field_simp
      ring
    rw [heq]
    linarith
  intro s hs hs1
  rw [Complex.mem_reProdIm, Set.uIcc_of_le hcd, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at hs
  obtain ⟨⟨hrelo, -⟩, himlo, himhi⟩ := hs
  rcases le_or_gt 1 s.re with hge | hlt
  · exact riemannZeta_ne_zero_of_one_le_re hge
  rcases le_or_gt (|s.im|) 1 with hsmall | hbig
  · exact hbox s (by linarith) hlt.le hsmall hs1
  · have hNbig : 3 + 2 * |s.im| ≤ (N : ℝ) := by
      have : |s.im| ≤ T := abs_le.2 ⟨himlo, himhi⟩
      linarith
    have hgt : 1 - zeroFreeConst / (2 * (Real.log N) ^ 9) < s.re := by
      have heq : zeroFreeConst / (2 * (Real.log N) ^ 9)
          = zeroFreeConst / (16 * (Real.log N) ^ 9) * 8 := by
        field_simp
        ring
      rw [heq]
      linarith
    have hmain := riemannZeta_ne_zero_of_re_gt (β := s.re) (γ := s.im) (N := N)
      hlogN hN hbig.le hNbig hlt.le hgt
    rwa [Complex.re_add_im] at hmain

end RHTower.Sieve
