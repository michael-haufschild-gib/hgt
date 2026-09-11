import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSpacedToMeasure
import GaloisForLFunctions.RHTower.Sieve.HalaszMontgomeryLogPolyBlock

/-!
# Large values of a DENSE dyadic block, as a measure

Huxley's count (`Sieve/PrimeBlockLevelSetCount`) carries the sparse normalisation `#B ≤ E/N`, which
no dense prime block satisfies.  `Sieve/HalaszMontgomeryLogPolyBlock.halaszMontgomery_logPoly_finset`
has no such restriction: it bounds `∑_{w ∈ P} ‖logPoly a s w‖²` for any `s ⊆ [N, 2N)` over a
one-spaced family.  Turning that into a level-set count and then, through
`MenonHarmonicSpacedToMeasure`, into a measure gives the dense-block large-values estimate the
harmonic ladder actually needs.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- A one-spaced family inside a window has at most `2G + 2` points. -/
theorem card_le_of_spaced_in_Icc {P : Finset ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hmem : ∀ x ∈ P, x ∈ Set.Icc (-G) G) :
    (P.card : ℝ) ≤ 2 * G + 2 := by
  classical
  have hinj : Set.InjOn (fun x : ℝ => ⌊x⌋) P := by
    intro x hx y hy hxy
    by_contra hne
    have hsp := hsep x hx y hy hne
    have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    have h3 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h4 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [show (⌊y⌋ : ℤ) = ⌊x⌋ from hxy.symm] at h3 h4
    rcases abs_cases (x - y) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hsp <;> linarith
  have hsub : P.image (fun x : ℝ => ⌊x⌋) ⊆ Finset.Icc ⌊(-G : ℝ)⌋ ⌊(G : ℝ)⌋ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have hx' := hmem x hx
    rw [Set.mem_Icc] at hx'
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_le_floor hx'.1, Int.floor_le_floor hx'.2⟩
  have hfloorle : ⌊(-G : ℝ)⌋ ≤ ⌊(G : ℝ)⌋ := Int.floor_le_floor (by linarith)
  have hcard : (P.card : ℤ) ≤ (⌊(G : ℝ)⌋ - ⌊(-G : ℝ)⌋ + 1) := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Int.card_Icc] at h
    omega
  have hcardR : (P.card : ℝ) ≤ ((⌊(G : ℝ)⌋ : ℝ) - (⌊(-G : ℝ)⌋ : ℝ) + 1) := by
    exact_mod_cast hcard
  have hGf : (⌊(G : ℝ)⌋ : ℝ) ≤ G := Int.floor_le G
  have hnGf : -G - 1 < (⌊(-G : ℝ)⌋ : ℝ) := by
    have := Int.lt_floor_add_one (-G : ℝ)
    linarith
  linarith

/-- **A dense-block large-values count from Halász--Montgomery.** -/
theorem card_le_of_halaszMontgomery_level
    {N : ℕ} (hN : 1 ≤ N) {s : Finset ℕ} (hs : s ⊆ Finset.Ico N (2 * N)) (a : ℕ → ℂ)
    {P : Finset ℝ} {G U V : ℝ} (hG : 0 ≤ G) (hU : 0 < U)
    (hsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → (1 : ℝ) ≤ |x - y|)
    (hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G)
    (hmem : ∀ x ∈ P, x ∈ Set.Icc (-G) G)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N (4 * Real.pi * G) ≤ 1)
    (hV0 : 0 ≤ V) (hV : ∀ w ∈ P, V ≤ ‖logPoly a s w‖)
    (hgap : 0 < V ^ 2
      - (1 + 214 * Real.sqrt (4 * Real.pi * G) + 1536 * ((N : ℝ) / Real.sqrt U))
        * ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2) :
    (P.card : ℝ)
      ≤ ((N : ℝ) + 6 * (N : ℝ) * (1 + Real.log (2 * G + 2)))
          * ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2
        / (V ^ 2
          - (1 + 214 * Real.sqrt (4 * Real.pi * G) + 1536 * ((N : ℝ) / Real.sqrt U))
            * ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2) := by
  classical
  set Eng : ℝ := ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2 with hEng
  set CG : ℝ := 1 + 214 * Real.sqrt (4 * Real.pi * G) + 1536 * ((N : ℝ) / Real.sqrt U) with hCG
  have hHM := halaszMontgomery_logPoly_finset hN hs a hG hU hsep hspread hnear hlamT
  have hlow : (P.card : ℝ) * V ^ 2 ≤ ∑ w ∈ P, ‖logPoly a s w‖ ^ 2 := by
    have : ∀ w ∈ P, V ^ 2 ≤ ‖logPoly a s w‖ ^ 2 := by
      intro w hw
      exact pow_le_pow_left₀ hV0 (hV w hw) 2
    calc (P.card : ℝ) * V ^ 2 = ∑ _w ∈ P, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ P, ‖logPoly a s w‖ ^ 2 := Finset.sum_le_sum this
  have hcardG : (P.card : ℝ) ≤ 2 * G + 2 := card_le_of_spaced_in_Icc hG hsep hmem
  have hcard0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hEng0 : (0 : ℝ) ≤ Eng := by positivity
  have hlogmono : Real.log (P.card : ℝ) ≤ Real.log (2 * G + 2) := by
    rcases eq_or_lt_of_le hcard0 with h | h
    · rw [← h, Real.log_zero]
      have : (0 : ℝ) ≤ 2 * G + 2 := by linarith
      have h1 : (1 : ℝ) ≤ 2 * G + 2 := by linarith
      exact Real.log_nonneg h1
    · exact Real.log_le_log h hcardG
  have hchain : (P.card : ℝ) * V ^ 2
      ≤ ((N : ℝ) + 6 * (N : ℝ) * (1 + Real.log (2 * G + 2)) + (P.card : ℝ) * CG) * Eng := by
    refine hlow.trans (hHM.trans ?_)
    have hstep : (N : ℝ) + (12 * Real.pi * (N : ℝ) / (2 * Real.pi)) * (1 + Real.log P.card)
          + (P.card : ℝ) * CG
        ≤ (N : ℝ) + 6 * (N : ℝ) * (1 + Real.log (2 * G + 2)) + (P.card : ℝ) * CG := by
      have hcoef : (12 * Real.pi * (N : ℝ) / (2 * Real.pi)) = 6 * (N : ℝ) := by
        field_simp
        ring
      rw [hcoef]
      have hN0 : (0 : ℝ) ≤ 6 * (N : ℝ) := by positivity
      nlinarith [hlogmono, hN0]
    exact mul_le_mul_of_nonneg_right hstep hEng0
  rw [le_div_iff₀ hgap]
  nlinarith [hchain, hcard0]

/-- The level set of a `logPoly` inside a window. -/
def logPolyLevelSet (a : ℕ → ℂ) (s : Finset ℕ) (G V : ℝ) : Set ℝ :=
  Set.Icc (-G) G ∩ {w | V ≤ ‖logPoly a s w‖}

theorem logPolyLevelSet_subset (a : ℕ → ℂ) (s : Finset ℕ) (G V : ℝ) :
    logPolyLevelSet a s G V ⊆ Set.Icc (-G) G := Set.inter_subset_left

/-- **The dense-block large-values estimate, as a measure.**  No sparsity hypothesis: the block
`s` is an arbitrary subset of a dyadic range. -/
theorem volume_real_logPolyLevelSet_le_halaszMontgomery
    {N : ℕ} (hN : 1 ≤ N) {s : Finset ℕ} (hs : s ⊆ Finset.Ico N (2 * N)) (a : ℕ → ℂ)
    {G U V : ℝ} (hG : 0 ≤ G) (hU : 0 < U) (hV0 : 0 ≤ V)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N (4 * Real.pi * G) ≤ 1)
    (hgap : 0 < V ^ 2
      - (1 + 214 * Real.sqrt (4 * Real.pi * G) + 1536 * ((N : ℝ) / Real.sqrt U))
        * ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2) :
    volume.real (logPolyLevelSet a s G V)
      ≤ 2 * (((N : ℝ) + 6 * (N : ℝ) * (1 + Real.log (2 * G + 2)))
            * ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2
          / (V ^ 2
            - (1 + 214 * Real.sqrt (4 * Real.pi * G) + 1536 * ((N : ℝ) / Real.sqrt U))
              * ‖blockCoeff N (blockRestrictCoeff a s) 0‖ ^ 2)) * 1 := by
  refine measureReal_le_of_spaced_card_le hG one_pos (logPolyLevelSet_subset a s G V) ?_
  intro P hsep hPmem
  have hmem : ∀ x ∈ P, x ∈ Set.Icc (-G) G := fun x hx => (hPmem x hx).1
  have hspread : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ 2 * G := by
    intro x hx y hy
    have hx' := Set.mem_Icc.1 (hmem x hx)
    have hy' := Set.mem_Icc.1 (hmem y hy)
    rw [abs_le]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  exact card_le_of_halaszMontgomery_level hN hs a hG hU hsep hspread hmem hnear hlamT
    hV0 (fun x hx => (hPmem x hx).2) hgap

end

end RHTower.Sieve
