import GaloisForLFunctions.RHTower.XiHeatShellMinimum

/-!
# The Turán rung detects an off-critical bottom shell

The variance expansion `2 * xiHeatTuranDefect t = sum_(q,q') (w q - w q')^(2 : ℕ) E t q E t q'` is
governed for large `t` by the pairs of least combined shell coordinate.  When the bottom shell is a
single conjugate pair `{w0, conj w0}` off the critical line, every bottom pair term is a nonpositive
**real** number — the phases `exp (-i t (Im w1 + Im w2))` cancel because the two heights are
opposite — while every other pair is damped by `exp (-t (2A + delta))` with `delta > 0` supplied by
the isolation of the bottom shell.  Hence the defect is eventually negative.

This is the converse half of the Turán rung: the rung is not merely nonnegative under RH, it
actually sees an off-critical bottom shell, with no Diophantine or almost-periodicity input.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A pair of copies at conjugate squared points contributes an explicit nonpositive real. -/
theorem xiHeatPairTerm_of_conj (t : ℝ) {z : XiZeroCopy × XiZeroCopy}
    (h : xiSpectralPoint z.2 ^ (2 : ℕ) = (starRingEnd ℂ) (xiSpectralPoint z.1 ^ (2 : ℕ))) :
    xiHeatPairTerm t z =
      (((-4 * (xiSpectralPoint z.1 ^ (2 : ℕ)).im ^ (2 : ℕ) *
        Real.exp (-(2 * t * (xiSpectralPoint z.1 ^ (2 : ℕ)).re))) : ℝ) : ℂ) := by
  have hsq : (xiSpectralPoint z.1 ^ (2 : ℕ) - xiSpectralPoint z.2 ^ (2 : ℕ)) ^ (2 : ℕ) =
      (((-4 * (xiSpectralPoint z.1 ^ (2 : ℕ)).im ^ (2 : ℕ)) : ℝ) : ℂ) := by
    rw [h, Complex.sub_conj, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hheat : xiGaussianHeatTerm t z.1 * xiGaussianHeatTerm t z.2 =
      ((Real.exp (-(2 * t * (xiSpectralPoint z.1 ^ (2 : ℕ)).re)) : ℝ) : ℂ) := by
    rw [xiGaussianHeatTerm, xiGaussianHeatTerm, ← Complex.exp_add, h, ← mul_add,
      Complex.add_conj]
    have hsum : -(t : ℂ) * ((2 * (xiSpectralPoint z.1 ^ (2 : ℕ)).re : ℝ) : ℂ) =
        ((-(2 * t * (xiSpectralPoint z.1 ^ (2 : ℕ)).re) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsum, ← Complex.ofReal_exp]
  rw [xiHeatPairTerm, hsq, hheat, ← Complex.ofReal_mul]

/-- **The Turán rung eventually detects an off-critical bottom shell.**  If the copies of least
shell coordinate form a single conjugate pair off the critical line, then the Turán minor is
strictly negative for all large heat times. -/
theorem exists_neg_xiHeatTuranDefect_of_bottom_conjugate_pair
    {q₀ : XiZeroCopy}
    (hmin : ∀ q : XiZeroCopy,
      (xiSpectralPoint q₀ ^ (2 : ℕ)).re ≤ (xiSpectralPoint q ^ (2 : ℕ)).re)
    (him : (xiSpectralPoint q₀ ^ (2 : ℕ)).im ≠ 0)
    (hbottom : ∀ q : XiZeroCopy,
      (xiSpectralPoint q ^ (2 : ℕ)).re = (xiSpectralPoint q₀ ^ (2 : ℕ)).re →
      xiSpectralPoint q ^ (2 : ℕ) = xiSpectralPoint q₀ ^ (2 : ℕ) ∨
        xiSpectralPoint q ^ (2 : ℕ) = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ (2 : ℕ))) :
    ∃ T : ℝ, ∀ t : ℝ, T < t → xiHeatTuranDefect t < 0 := by
  classical
  set A : ℝ := (xiSpectralPoint q₀ ^ (2 : ℕ)).re with hA
  -- the isolation gap, transported to this minimiser
  obtain ⟨A', δ, hδ, ⟨q₀', hq₀'⟩, hmin', hgap'⟩ := exists_bottom_shell_gap
  have hAA : A' = A := le_antisymm (hmin' q₀) (by rw [← hq₀']; exact hmin q₀')
  have hgap : ∀ q : XiZeroCopy,
      (xiSpectralPoint q ^ (2 : ℕ)).re = A ∨ A + δ ≤ (xiSpectralPoint q ^ (2 : ℕ)).re := by
    intro q
    have := hgap' q
    rwa [hAA] at this
  -- the bottom block
  set B : Finset XiZeroCopy := xiHeatShell A with hB
  have hmemB : ∀ q : XiZeroCopy, q ∈ B ↔ (xiSpectralPoint q ^ (2 : ℕ)).re = A := by
    intro q; rw [hB]; exact mem_xiHeatShell
  have hq₀B : q₀ ∈ B := (hmemB q₀).mpr rfl
  set q₁ : XiZeroCopy := xiZeroCopyLineConjEquiv q₀ with hq₁
  have hw₁ : xiSpectralPoint q₁ ^ (2 : ℕ) = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ (2 : ℕ)) := by
    rw [hq₁, xiSpectralSq_lineConj]
  have hq₁B : q₁ ∈ B := by
    rw [hmemB, hw₁, Complex.conj_re]
  set P : Finset (XiZeroCopy × XiZeroCopy) := B ×ˢ B with hP
  have hz₀P : (q₀, q₁) ∈ P := Finset.mk_mem_product hq₀B hq₁B
  -- the reference constant for the tail
  have hnorm1 : Summable (fun z : XiZeroCopy × XiZeroCopy =>
      ‖xiHeatPairTerm 1 z‖) := summable_norm_iff.mpr (summable_xiHeatPairTerm one_pos)
  set C : ℝ := ∑' z : XiZeroCopy × XiZeroCopy, ‖xiHeatPairTerm 1 z‖ with hC
  have hCnn : 0 ≤ C := tsum_nonneg fun z => norm_nonneg _
  set μ : ℝ := 4 * (xiSpectralPoint q₀ ^ (2 : ℕ)).im ^ (2 : ℕ) with hμ
  have hμpos : 0 < μ := by
    have : 0 < (xiSpectralPoint q₀ ^ (2 : ℕ)).im ^ (2 : ℕ) := by positivity
    rw [hμ]; linarith
  set K : ℝ := C * Real.exp (2 * A + δ) / μ with hK
  refine ⟨max 1 (K / δ), fun t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht)
  have htK : K / δ < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
  have hsum := summable_xiHeatPairTerm htpos
  -- bottom block: every term is a nonpositive real, and one is explicitly negative
  have hbotterm : ∀ z ∈ P, (xiHeatPairTerm t z).re ≤ 0 := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp (by rwa [hP] at hz)
    have h1 := hbottom z.1 ((hmemB z.1).mp hz1)
    have h2 := hbottom z.2 ((hmemB z.2).mp hz2)
    have hcase : xiSpectralPoint z.1 ^ (2 : ℕ) = xiSpectralPoint z.2 ^ (2 : ℕ) ∨
        xiSpectralPoint z.2 ^ (2 : ℕ) = (starRingEnd ℂ) (xiSpectralPoint z.1 ^ (2 : ℕ)) := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact Or.inl (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2])
      · exact Or.inr (by rw [h1, h2, Complex.conj_conj])
      · exact Or.inl (by rw [h1, h2])
    rcases hcase with heq | hconj
    · rw [xiHeatPairTerm, heq]
      simp
    · rw [xiHeatPairTerm_of_conj t hconj, Complex.ofReal_re]
      have h4 : 0 ≤ (xiSpectralPoint z.1 ^ (2 : ℕ)).im ^ (2 : ℕ) := sq_nonneg _
      have hexp : 0 < Real.exp (-(2 * t * (xiSpectralPoint z.1 ^ (2 : ℕ)).re)) :=
        Real.exp_pos _
      nlinarith
  have hz₀val : (xiHeatPairTerm t (q₀, q₁)).re = -(μ * Real.exp (-(2 * t * A))) := by
    rw [xiHeatPairTerm_of_conj t (z := (q₀, q₁)) (by simpa using hw₁),
      Complex.ofReal_re, hμ, hA]
    ring
  have hbotsum : ∑ z ∈ P, (xiHeatPairTerm t z).re ≤ -(μ * Real.exp (-(2 * t * A))) := by
    have hrest : ∑ z ∈ P.erase (q₀, q₁), (xiHeatPairTerm t z).re ≤ 0 :=
      Finset.sum_nonpos fun z hz => hbotterm z (Finset.mem_of_mem_erase hz)
    calc
      ∑ z ∈ P, (xiHeatPairTerm t z).re
          = (xiHeatPairTerm t (q₀, q₁)).re +
              ∑ z ∈ P.erase (q₀, q₁), (xiHeatPairTerm t z).re :=
            (Finset.add_sum_erase P (fun z => (xiHeatPairTerm t z).re) hz₀P).symm
      _ ≤ -(μ * Real.exp (-(2 * t * A))) + 0 := by
            rw [hz₀val]
            linarith
      _ = -(μ * Real.exp (-(2 * t * A))) := by ring
  -- tail
  have htail : ‖∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ, xiHeatPairTerm t z‖ ≤
      C * Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) := by
    have hsub : Summable (fun z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ =>
        ‖xiHeatPairTerm t z‖) :=
      (summable_norm_iff.mpr hsum).subtype _
    have hsub1 : Summable (fun z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ =>
        ‖xiHeatPairTerm 1 z‖) := hnorm1.subtype _
    have hbound : ∀ z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ,
        ‖xiHeatPairTerm t (z : XiZeroCopy × XiZeroCopy)‖ ≤
          Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) *
            ‖xiHeatPairTerm 1 (z : XiZeroCopy × XiZeroCopy)‖ := by
      rintro ⟨z, hz⟩
      have hzP : z ∉ P := by simpa using hz
      have hcomb : 2 * A + δ ≤
          (xiSpectralPoint z.1 ^ (2 : ℕ)).re + (xiSpectralPoint z.2 ^ (2 : ℕ)).re := by
        by_cases h1 : z.1 ∈ B
        · have h2 : z.2 ∉ B := fun hb => hzP (by rw [hP]; exact Finset.mk_mem_product h1 hb)
          have hne : (xiSpectralPoint z.2 ^ (2 : ℕ)).re ≠ A := fun hc => h2 ((hmemB z.2).mpr hc)
          have := (hgap z.2).resolve_left hne
          have h1' := (hmemB z.1).mp h1
          linarith
        · have hne : (xiSpectralPoint z.1 ^ (2 : ℕ)).re ≠ A := fun hc => h1 ((hmemB z.1).mpr hc)
          have := (hgap z.1).resolve_left hne
          have := hmin z.2
          linarith
      have hstep := norm_xiHeatPairTerm_le_of_le (t₁ := 1) (m := 2 * A + δ) ht1 hcomb
      have hrw : Real.exp (-((t - 1) * (2 * A + δ))) =
          Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hrw] at hstep
      linarith [hstep]
    calc
      ‖∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ, xiHeatPairTerm t z‖
          ≤ ∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ,
              ‖xiHeatPairTerm t (z : XiZeroCopy × XiZeroCopy)‖ :=
            norm_tsum_le_tsum_norm hsub
      _ ≤ ∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ,
              Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) *
                ‖xiHeatPairTerm 1 (z : XiZeroCopy × XiZeroCopy)‖ :=
            hsub.tsum_le_tsum hbound (hsub1.mul_left _)
      _ = Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) *
              ∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ,
                ‖xiHeatPairTerm 1 (z : XiZeroCopy × XiZeroCopy)‖ :=
            hsub1.tsum_mul_left _
      _ ≤ Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) * C := by
            have hle : ∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ,
                ‖xiHeatPairTerm 1 (z : XiZeroCopy × XiZeroCopy)‖ ≤ C := by
              have hsplit := hnorm1.sum_add_tsum_compl (s := P)
              have hnn : 0 ≤ ∑ z ∈ P, ‖xiHeatPairTerm 1 z‖ :=
                Finset.sum_nonneg fun z _ => norm_nonneg _
              rw [hC, ← hsplit]
              linarith
            exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = C * Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) := by ring
  -- assemble
  have hdefect : 2 * xiHeatTuranDefect t =
      ∑ z ∈ P, (xiHeatPairTerm t z).re +
        (∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ, xiHeatPairTerm t z).re := by
    rw [two_mul_xiHeatTuranDefect_eq_re_tsum_pair htpos, ← hsum.sum_add_tsum_compl (s := P),
      Complex.add_re, Complex.re_sum]
  have htailre : (∑' z : ↑((P : Set (XiZeroCopy × XiZeroCopy)))ᶜ,
      xiHeatPairTerm t z).re ≤ C * Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) :=
    le_trans (Complex.re_le_norm _) htail
  have hkey : C * Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ))) <
      μ * Real.exp (-(2 * t * A)) := by
    have hKt : K < t * δ := by
      rw [div_lt_iff₀ hδ] at htK
      linarith
    have hexpt : t * δ < Real.exp (t * δ) :=
      lt_of_lt_of_le (by linarith [Real.add_one_le_exp (t * δ)]) (le_refl _)
    have hK2 : K < Real.exp (t * δ) := lt_trans hKt hexpt
    have hprod : C * Real.exp (2 * A + δ) < Real.exp (t * δ) * μ := by
      rw [hK, div_lt_iff₀ hμpos] at hK2
      linarith
    have hfac : Real.exp (t * δ) * Real.exp (-(t * (2 * A + δ))) =
        Real.exp (-(2 * t * A)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      C * Real.exp (2 * A + δ) * Real.exp (-(t * (2 * A + δ)))
          < (Real.exp (t * δ) * μ) * Real.exp (-(t * (2 * A + δ))) :=
            mul_lt_mul_of_pos_right hprod (Real.exp_pos _)
      _ = μ * (Real.exp (t * δ) * Real.exp (-(t * (2 * A + δ)))) := by ring
      _ = μ * Real.exp (-(2 * t * A)) := by rw [hfac]
  linarith [hdefect, hbotsum, htailre, hkey]


/-- **Turán positivity forces the bottom shell onto the critical line.**  If the second Hankel
minor of the Gaussian heat trace is nonnegative at every positive time, then a bottom shell of the
simplest shape — one conjugate class — consists of real squared points. -/
theorem xiSpectralSq_bottom_im_eq_zero_of_forall_xiHeatTuranDefect_nonneg
    {q₀ : XiZeroCopy}
    (hmin : ∀ q : XiZeroCopy,
      (xiSpectralPoint q₀ ^ (2 : ℕ)).re ≤ (xiSpectralPoint q ^ (2 : ℕ)).re)
    (hbottom : ∀ q : XiZeroCopy,
      (xiSpectralPoint q ^ (2 : ℕ)).re = (xiSpectralPoint q₀ ^ (2 : ℕ)).re →
      xiSpectralPoint q ^ (2 : ℕ) = xiSpectralPoint q₀ ^ (2 : ℕ) ∨
        xiSpectralPoint q ^ (2 : ℕ) = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ (2 : ℕ)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ xiHeatTuranDefect t) :
    (xiSpectralPoint q₀ ^ (2 : ℕ)).im = 0 := by
  by_contra him
  obtain ⟨T, hT⟩ :=
    exists_neg_xiHeatTuranDefect_of_bottom_conjugate_pair hmin him hbottom
  set t : ℝ := max T 1 + 1 with ht
  have htT : T < t := by
    rw [ht]
    have := le_max_left T 1
    linarith
  have htpos : 0 < t := by
    rw [ht]
    have := le_max_right T 1
    linarith
  exact absurd (hpos t htpos) (not_le.mpr (hT t htT))

/-- **The lowest zero lies on the critical line under Turán positivity.**  Squaring detects the
critical line, so the previous theorem is a statement about the zero itself. -/
theorem xiSpectralPoint_bottom_im_eq_zero_of_forall_xiHeatTuranDefect_nonneg
    {q₀ : XiZeroCopy}
    (hmin : ∀ q : XiZeroCopy,
      (xiSpectralPoint q₀ ^ (2 : ℕ)).re ≤ (xiSpectralPoint q ^ (2 : ℕ)).re)
    (hbottom : ∀ q : XiZeroCopy,
      (xiSpectralPoint q ^ (2 : ℕ)).re = (xiSpectralPoint q₀ ^ (2 : ℕ)).re →
      xiSpectralPoint q ^ (2 : ℕ) = xiSpectralPoint q₀ ^ (2 : ℕ) ∨
        xiSpectralPoint q ^ (2 : ℕ) = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ (2 : ℕ)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ xiHeatTuranDefect t) :
    (xiSpectralPoint q₀).im = 0 := by
  by_contra him
  exact xiSpectralSq_im_ne_zero_of_im_ne_zero him
    (xiSpectralSq_bottom_im_eq_zero_of_forall_xiHeatTuranDefect_nonneg hmin hbottom hpos)

end

end RHTower
