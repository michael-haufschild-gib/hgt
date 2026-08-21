import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIISparseHalaszMontgomery
import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteSeparatedExtension

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

noncomputable section

/-! # Halász--Montgomery on a literal real finite set

The existing receiver used a finite subset of an ambient Nat-indexed sequence. Proposition 4.2
supplies the ordinates themselves. We reuse the corpus's certified sorted finite-ordinate timeline
to close that representation seam without adding an ordering premise. -/

/-- Certified sorted-timeline input built from a separated finite set of real ordinates. -/
noncomputable def matomakiTeravainenFiniteSeparatedOrdinates
    (S : Finset ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|) :
    RHTower.CGLFiniteSeparatedOrdinates S.card where
  ordinate := S.orderEmbOfFin rfl
  spacing := delta
  spacing_pos := hdelta
  separated := by
    intro r s hrs
    exact hsep _ (Finset.orderEmbOfFin_mem S rfl r)
      _ (Finset.orderEmbOfFin_mem S rfl s)
      (fun h => hrs ((S.orderEmbOfFin rfl).injective h))

theorem matomakiTeravainenFiniteSeparatedOrdinates_image
    (S : Finset ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|) :
    RHTower.cglFiniteSeparatedOrdinatesImage
      (matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep) = S := by
  dsimp only [RHTower.cglFiniteSeparatedOrdinatesImage,
    matomakiTeravainenFiniteSeparatedOrdinates]
  exact Finset.image_orderEmbOfFin_univ S rfl

theorem matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
    (S : Finset ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    {i : ℕ} (hi : i < S.card) :
    RHTower.cglFiniteSeparatedOrdinatesTimeline
      (matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep) i ∈ S := by
  let P := matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep
  have hR : S.card ≠ 0 := by omega
  have hmem := Finset.orderEmbOfFin_mem
    (RHTower.cglFiniteSeparatedOrdinatesImage P)
    (RHTower.cglFiniteSeparatedOrdinatesImage_card P) ⟨i, hi⟩
  have hmemS : RHTower.cglFiniteSeparatedOrdinatesOrdered P ⟨i, hi⟩ ∈ S := by
    change RHTower.cglFiniteSeparatedOrdinatesOrdered P ⟨i, hi⟩ ∈
      Finset.univ.image P.ordinate at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨r, _hr, hrEq⟩ := hmem
    rw [← hrEq]
    change S.orderEmbOfFin rfl r ∈ S
    exact Finset.orderEmbOfFin_mem S rfl r
  simpa only [P, RHTower.cglFiniteSeparatedOrdinatesTimeline, dif_neg hR, dif_pos hi] using hmemS

theorem sum_finset_eq_sum_matomakiTeravainenFiniteSeparatedOrdinates_timeline
    (S : Finset ℝ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (f : ℝ → ℝ) :
    ∑ t ∈ S, f t = ∑ i ∈ Finset.range S.card,
      f (RHTower.cglFiniteSeparatedOrdinatesTimeline
        (matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep) i) := by
  let P := matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep
  let I := RHTower.cglFiniteSeparatedOrdinatesImage P
  let e := I.orderEmbOfFin (RHTower.cglFiniteSeparatedOrdinatesImage_card P)
  have hI : I = S := by
    dsimp only [I]
    simpa only [P] using
      matomakiTeravainenFiniteSeparatedOrdinates_image S delta hdelta hsep
  calc
    ∑ t ∈ S, f t = ∑ t ∈ I, f t := by
      rw [hI]
    _ = ∑ t ∈ Finset.image e Finset.univ, f t := by
      rw [Finset.image_orderEmbOfFin_univ]
    _ = ∑ i : Fin S.card, f (e i) := by
      rw [Finset.sum_image (Set.injOn_of_injective e.injective)]
    _ = ∑ i : Fin S.card,
        f (RHTower.cglFiniteSeparatedOrdinatesTimeline P (i : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hR : S.card ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
      simp only [P, e, I, RHTower.cglFiniteSeparatedOrdinatesTimeline,
        dif_neg hR, dif_pos i.isLt, RHTower.cglFiniteSeparatedOrdinatesOrdered]
    _ = ∑ i ∈ Finset.range S.card,
        f (RHTower.cglFiniteSeparatedOrdinatesTimeline P i) :=
      Fin.sum_univ_eq_sum_range
        (fun i => f (RHTower.cglFiniteSeparatedOrdinatesTimeline P i)) S.card

/-- Halász--Montgomery mean square for a dyadic block on the literal separated real finite set. -/
theorem halaszMontgomery_blockPoly_real_finset_explicit
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ)
    {S : Finset ℝ} {delta U T : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1) :
    ∑ t ∈ S, ‖blockPoly N c 1 t‖ ^ 2 ≤
      ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
          + (S.card : ℝ) *
            (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
        ‖blockCoeff N c 1‖ ^ 2 := by
  let P := matomakiTeravainenFiniteSeparatedOrdinates S delta hdelta hsep
  have hdiam : ∀ r ∈ Finset.range S.card, ∀ s ∈ Finset.range S.card,
      |RHTower.cglFiniteSeparatedOrdinatesTimeline P s -
        RHTower.cglFiniteSeparatedOrdinatesTimeline P r| ≤ T := by
    intro r hr s hs
    have hrmem := matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      S delta hdelta hsep (Finset.mem_range.1 hr)
    have hsmem := matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      S delta hdelta hsep (Finset.mem_range.1 hs)
    exact hspread _ hsmem _ hrmem
  have hbase := halaszMontgomery_dyadic_explicit (K := S.card) hN (blockCoeff N c 1)
    hdelta hU hT (RHTower.cglFiniteSeparatedOrdinatesTimeline_step P) hdiam
    hnear hlamT
  rw [sum_finset_eq_sum_matomakiTeravainenFiniteSeparatedOrdinates_timeline
    S delta hdelta hsep
    (fun t => ‖blockPoly N c 1 t‖ ^ 2)]
  simpa only [inner_dyadicDirRow_blockCoeff] using hbase

/-- The `T₁` receiver on literal real ordinates, stated with intrinsic coefficient mass. This is
the divisor-bounded form: an average energy bound replaces the false requirement that every
divisor-bounded coefficient be uniformly bounded by one fixed constant. -/
theorem matomakiTeravainen_typeII_T1_real_finset_energy_of_mass
    (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℂ)
    {S : Finset ℝ} {delta U T A G : ℝ}
    (hdelta : 0 < delta) (hU : 0 < U) (hT : 0 ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ T)
    (hnear : 3 * U ≤ 4 * Real.pi * (N : ℝ))
    (hlamT : logDyadicLambda N T ≤ 1)
    (F₁ : ℝ → ℝ) (hF₁0 : ∀ t ∈ S, 0 ≤ F₁ t) (hF₁ : ∀ t ∈ S, F₁ t ≤ A)
    (hmass : ‖blockCoeff N c 1‖ ^ 2 ≤ G) :
    ∑ t ∈ S, F₁ t ^ 2 * ‖blockPoly N c 1 t‖ ^ 2 ≤
      A ^ 2 *
        (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
            + (S.card : ℝ) *
              (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) * G) := by
  have hpoint : ∀ t ∈ S,
      F₁ t ^ 2 * ‖blockPoly N c 1 t‖ ^ 2 ≤
        A ^ 2 * ‖blockPoly N c 1 t‖ ^ 2 := by
    intro t ht
    have hsquare : F₁ t ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (hF₁0 t ht) (hF₁ t ht) 2
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  calc
    ∑ t ∈ S, F₁ t ^ 2 * ‖blockPoly N c 1 t‖ ^ 2
        ≤ ∑ t ∈ S, A ^ 2 * ‖blockPoly N c 1 t‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = A ^ 2 * ∑ t ∈ S, ‖blockPoly N c 1 t‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ A ^ 2 *
        (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
            + (S.card : ℝ) *
              (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) *
          ‖blockCoeff N c 1‖ ^ 2) := by
      gcongr
      exact halaszMontgomery_blockPoly_real_finset_explicit N hN c hdelta hU hT
        hsep hspread hnear hlamT
    _ ≤ A ^ 2 *
        (((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * (1 + Real.log S.card)
            + (S.card : ℝ) *
              (1 + 214 * Real.sqrt T + 1536 * ((N : ℝ) / Real.sqrt U))) * G) := by
      gcongr

end

end RHTower.Sieve
