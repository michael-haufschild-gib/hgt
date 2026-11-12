import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheFunctionalEquationDefectOfAFakeEdit
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwinsContinuePastTheLine
import GaloisForLFunctions.EulerFETransportTheory.PolynomialStripContinuationsLieInTheHamburgerClass

/-!
# The functional-equation defect of a twin on the critical line

A system `B` is a twin of `ζ` with factor `L` on `Re s > c` (`IsFactorTwinOn`) when
`(s - 1) ζ_B(s) = (s - 1) ζ(s) · M(s)`, `M = C L e^{H}`.  For `c < 1/2` the critical line lies in
the half-plane and the continuation is `ζ^ext = ζ M`.

* **Real symmetry** (`IsFactorTwinOn.cofactor_conj`).  `ζ_B` has real coefficients, so
  `M(s̄) = conj M(s)` on `Re s > c`.
* **The defect** (`IsFactorTwinOn.stripDefect_eq`).  The critical-line FE defect
  `g(t) = ζ^ext(s) - χ(s) ζ^ext(1 - s)`, `s = 1/2 + 2it`, is `2i ζ(s) Im M(s)` (Lemma 1.2(2)).
* **The pair twin** (`pairTwin_stripDefect_eq`, Corollary III.1(1)).  For `1/2 < Re ρ < 14/15`
  the greedy edit of the pair is a twin on a half-plane containing the line, and
  `g_pair(t) = 2i ζ(s) Im(C (s - ρ)(s - ρ̄) e^{H(s)})`, where on the line
  `(s - ρ)(s - ρ̄) = -4t² + (1/2 - β₀)² + γ₀² + 4i(1/2 - β₀)t` (`pairFactor_criticalLine`).
* **The quartet** (`quartetTwin_defect`, Corollary III.1(2)).  On the line the quartet factor is
  `|s - ρ|² |s - ρ̄|² ≥ 0`, so `g = 2i ζ(s) L₄(s) Im(C e^{H(s)})`; the quartet edit is nevertheless
  an integer-norm fake, so any Hamburger-strip defect it has is unbounded with
  `∫ ‖g‖² e^{-|t|/T} ≥ A²/(256πp₀) T log T`.
-/

open Complex Filter Topology Set
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm GaloisForLFunctions.EulerFETransportTheory

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect

open TwoSidedEdits

/-- `ζ_B(s̄) = conj ζ_B(s)`: the norms are real. -/
theorem zetaSeriesC_conj (B : BeurlingSystem) (s : ℂ) :
    B.zetaSeriesC ((starRingEnd ℂ) s) = (starRingEnd ℂ) (B.zetaSeriesC s) := by
  unfold BeurlingSystem.zetaSeriesC
  rw [Complex.conj_tsum]
  refine tsum_congr fun g => ?_
  have harg : ((B.intNorm g : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (B.intNorm_pos g).le]; exact Real.pi_ne_zero.symm
  rw [show -(starRingEnd ℂ) s = (starRingEnd ℂ) (-s) by simp, Complex.cpow_conj _ _ harg,
    Complex.conj_ofReal]

/-- `(s̄ - 1) ζ(s̄) = conj((s - 1) ζ(s))`. -/
theorem zetaResidueUnit_conj (s : ℂ) :
    zetaResidueUnit ((starRingEnd ℂ) s) = (starRingEnd ℂ) (zetaResidueUnit s) := by
  by_cases hs : s = 1
  · subst hs; simp
  · have hs' : (starRingEnd ℂ) s ≠ 1 := fun h => hs (by simpa using congrArg (starRingEnd ℂ) h)
    rw [zetaResidueUnit_of_ne hs, zetaResidueUnit_of_ne hs', riemannZeta_conj]
    simp

/-- **Real symmetry of the twin cofactor.**  If `B` is a twin of `ζ` with factor `L` on
`Re s > c` (`c < 1`), its cofactor `M = C L e^{H}` satisfies `M(s̄) = conj M(s)` there. -/
theorem IsFactorTwinOn.cofactor_conj {c : ℝ} (hc : c < 1) {B : BeurlingSystem} {L : ℂ → ℂ}
    {C : ℂ} {H : ℂ → ℂ} (hL : DifferentiableOn ℂ L {s : ℂ | c < s.re})
    (hH : DifferentiableOn ℂ H {s : ℂ | c < s.re})
    (hfac : ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * L s * Complex.exp (H s))) :
    ∀ s : ℂ, c < s.re → C * L ((starRingEnd ℂ) s) * Complex.exp (H ((starRingEnd ℂ) s)) =
      (starRingEnd ℂ) (C * L s * Complex.exp (H s)) := by
  set M : ℂ → ℂ := fun s => C * L s * Complex.exp (H s) with hM
  set U : Set ℂ := {s : ℂ | c < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hMd : DifferentiableOn ℂ M U := ((differentiableOn_const C).mul hL).mul hH.cexp
  set N : ℂ → ℂ := (starRingEnd ℂ) ∘ M ∘ (starRingEnd ℂ) with hN
  have hNd : DifferentiableOn ℂ N U := by
    intro s hs
    have hs' : (starRingEnd ℂ) s ∈ U := by simpa [hU] using hs
    have h := (hMd.differentiableAt (hUo.mem_nhds hs')).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have heq : ∀ s : ℂ, 1 < s.re → N s = M s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
    have hz : zetaResidueUnit s ≠ 0 := by
      rw [zetaResidueUnit_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
    have hsc : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
    have h1 := hfac ((starRingEnd ℂ) s) hsc
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [map_mul, map_mul, zetaSeriesC_conj, Complex.conj_conj, ← zetaResidueUnit_conj,
      Complex.conj_conj, map_sub, Complex.conj_conj, map_one, hfac s hs] at h2
    have h3 : zetaResidueUnit s * M s = zetaResidueUnit s * N s := by
      simpa [hM, hN] using h2
    exact (mul_left_cancel₀ hz h3).symm
  have hid := eqOn_re_gt_of_eq_on_re_gt_one hc hNd hMd heq
  intro s hs
  have h := hid hs
  have h' := congrArg (starRingEnd ℂ) h
  simp only [hN, hM, Function.comp_apply, Complex.conj_conj] at h'
  exact h'

/-- **The defect of a twin.**  For a twin on `Re s > c`, `c < 1/2`, with cofactor `M = C L e^{H}`,
the critical-line FE defect of the continuation `(s - 1) ζ(s) M(s)` is `2i ζ(s) Im M(s)`. -/
theorem IsFactorTwinOn.stripDefect_eq {c : ℝ} (hc : c < 1 / 2) {B : BeurlingSystem}
    {L : ℂ → ℂ} {C : ℂ} {H : ℂ → ℂ} (hL : DifferentiableOn ℂ L {s : ℂ | c < s.re})
    (hH : DifferentiableOn ℂ H {s : ℂ | c < s.re})
    (hfac : ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * L s * Complex.exp (H s))) (t : ℝ) :
    stripDefect (fun s => zetaResidueUnit s * (C * L s * Complex.exp (H s))) t =
      2 * I * riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
        ((C * L ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
          Complex.exp (H ((1 / 2 : ℂ) + (2 * t : ℝ) * I))).im : ℂ) := by
  have hsym := IsFactorTwinOn.cofactor_conj (by linarith) hL hH hfac
  refine stripDefect_eq_of_factor (M := fun s => C * L s * Complex.exp (H s)) (fun s hs => ?_)
    (fun s hs => ?_) t
  · have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    rw [zetaResidueUnit_of_ne hs1]
    field_simp [sub_ne_zero.mpr hs1]
  · have hc1 : 1 - s = (starRingEnd ℂ) s := by
      apply Complex.ext <;> simp [hs] <;> norm_num
    rw [hc1]
    exact hsym s (by rw [hs]; linarith)

/-! ## The pair twin and the quartet -/

/-- On the line, `(s - ρ)(s - ρ̄) = -4t² + (1/2 - β₀)² + γ₀² + 4i(1/2 - β₀)t`. -/
theorem pairFactor_criticalLine (ρ : ℂ) (t : ℝ) :
    ((1 / 2 : ℂ) + (2 * t : ℝ) * I - ρ) * ((1 / 2 : ℂ) + (2 * t : ℝ) * I - (starRingEnd ℂ) ρ) =
      ((-4 * t ^ 2 + (1 / 2 - ρ.re) ^ 2 + ρ.im ^ 2 : ℝ) : ℂ) +
        ((4 * (1 / 2 - ρ.re) * t : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    norm_num; ring
  · simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.mul_im, Complex.add_im,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    norm_num; ring

/-- **Corollary III.1(1): the defect of the pair twin.**  For `1/2 < Re ρ < 14/15` the greedy edit
of the pair `ρ, ρ̄` is a twin on a half-plane containing the critical line, and its critical-line
FE defect is `2i ζ(s) Im(C (s - ρ)(s - ρ̄) e^{H(s)})`. -/
theorem pairTwin_stripDefect_eq {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15) :
    ∃ c : ℝ, c < 1 / 2 ∧ ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ H {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → (s - 1) * (editSystem (PrimeEdits.edit ρ)).zetaSeriesC s =
        zetaResidueUnit s * (C * ((s - ρ) * (s - (starRingEnd ℂ) ρ)) * Complex.exp (H s))) ∧
      ∀ t : ℝ, stripDefect (fun s => zetaResidueUnit s *
          (C * ((s - ρ) * (s - (starRingEnd ℂ) ρ)) * Complex.exp (H s))) t =
        2 * I * riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
          ((C * (((1 / 2 : ℂ) + (2 * t : ℝ) * I - ρ) *
              ((1 / 2 : ℂ) + (2 * t : ℝ) * I - (starRingEnd ℂ) ρ)) *
            Complex.exp (H ((1 / 2 : ℂ) + (2 * t : ℝ) * I))).im : ℂ) := by
  set c : ℝ := (max (ρ.re - 13 / 30) (ρ.re / 2) + 1 / 2) / 2 with hcdef
  have hm1 : ρ.re - 13 / 30 < 1 / 2 := by linarith
  have hm2 : ρ.re / 2 < 1 / 2 := by linarith
  have hmax : max (ρ.re - 13 / 30) (ρ.re / 2) < 1 / 2 := max_lt hm1 hm2
  have hc : c < 1 / 2 := by rw [hcdef]; linarith
  have hc1 : ρ.re - 13 / 30 < c := by rw [hcdef]; linarith [le_max_left (ρ.re - 13 / 30) (ρ.re / 2)]
  have hc2 : ρ.re / 2 < c := by rw [hcdef]; linarith [le_max_right (ρ.re - 13 / 30) (ρ.re / 2)]
  obtain ⟨C, H, hC, hH, hfac⟩ := isFactorTwinOn_edit (by linarith) (by linarith) hc1 hc2
    (by linarith)
  have hL : DifferentiableOn ℂ (fun s : ℂ => (s - ρ) * (s - (starRingEnd ℂ) ρ))
      {s : ℂ | c < s.re} := by fun_prop
  exact ⟨c, hc, C, H, hC, hH, hfac, fun t => IsFactorTwinOn.stripDefect_eq hc hL hH hfac t⟩

/-- On the line the quartet factor is `|s - ρ|² |s - ρ̄|²`. -/
theorem quartetFactor_criticalLine (ρ : ℂ) (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (2 * t : ℝ) * I
    (s - ρ) * (s - (starRingEnd ℂ) ρ) * ((s - (1 - (starRingEnd ℂ) ρ)) * (s - (1 - ρ))) =
      ((‖s - ρ‖ ^ 2 * ‖s - (starRingEnd ℂ) ρ‖ ^ 2 : ℝ) : ℂ) := by
  intro s
  have h1 : s - (1 - (starRingEnd ℂ) ρ) = -(starRingEnd ℂ) (s - ρ) := by
    apply Complex.ext <;> simp [s] <;> ring
  have h2 : s - (1 - ρ) = -(starRingEnd ℂ) (s - (starRingEnd ℂ) ρ) := by
    apply Complex.ext <;> simp [s] <;> ring
  rw [h1, h2]
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  ring

/-- **Corollary III.1(2): the quartet.**  For `ρ = 1/2 + δ + iγ` with `0 < δ < 13/30` and
`ζ(ρ) ≠ 0` there is a two-sided edit with a count rate that is a twin of `ζ` with the quartet
factor `L₄ = (s - ρ)(s - ρ̄)(s - (1 - ρ̄))(s - (1 - ρ))` on a half-plane containing the line.  Its
critical-line FE defect is `2i ζ(s) Im(C L₄(s) e^{H(s)})` with `L₄(s) = |s - ρ|²|s - ρ̄|² ≥ 0`; the
edit is an integer-norm fake, so in the Hamburger strip class its defect is unbounded and has
logarithmic energy. -/
theorem quartetTwin_defect {ρ : ℂ} (hδ0 : 1 / 2 < ρ.re) (hδ1 : ρ.re < 1 / 2 + 13 / 30)
    (hζ : riemannZeta ρ ≠ 0) :
    ∃ (e : ℕ → ℤ) (β_c A C₀ c : ℝ) (C : ℂ) (H : ℂ → ℂ), IsEdit e ∧ β_c < 1 ∧
      (∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C₀ * x ^ β_c) ∧
      IsIntegerNormFakeAt (editSystem e) β_c ∧ c < 1 / 2 ∧
      DifferentiableOn ℂ H {s : ℂ | c < s.re} ∧
      (∀ s : ℂ, 1 < s.re → (s - 1) * (editSystem e).zetaSeriesC s =
        zetaResidueUnit s * (C * layerFactor (Finset.univ : Finset (Fin 2))
          ![ρ, 1 - (starRingEnd ℂ) ρ] s * Complex.exp (H s))) ∧
      (∀ t : ℝ, stripDefect (fun s => zetaResidueUnit s * (C * layerFactor
          (Finset.univ : Finset (Fin 2)) ![ρ, 1 - (starRingEnd ℂ) ρ] s * Complex.exp (H s))) t =
        2 * I * riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
          ((C * layerFactor (Finset.univ : Finset (Fin 2)) ![ρ, 1 - (starRingEnd ℂ) ρ]
            ((1 / 2 : ℂ) + (2 * t : ℝ) * I) *
            Complex.exp (H ((1 / 2 : ℂ) + (2 * t : ℝ) * I))).im : ℂ)) ∧
      ∀ (β : ℂ) (g : ℝ → ℂ), HamburgerStripDefect (editSystem e).zetaSeriesC β g →
        (∀ M : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ M) ∧
        ∃ p₀ : ℕ, p₀.Prime ∧ e p₀ = -1 ∧ 0 < A ∧ β = A / 2 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
          A ^ 2 / (256 * Real.pi * p₀) * (T * Real.log T) ≤
            ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) := by
  set b : ℝ := ρ.re with hb
  set ρs : Fin 2 → ℂ := ![ρ, 1 - (starRingEnd ℂ) ρ] with hρs
  have hρle : ∀ j ∈ (Finset.univ : Finset (Fin 2)), (ρs j).re ≤ b := by
    intro j _
    fin_cases j
    · simp [hρs, hb]
    · simp [hρs, hb]; linarith
  set c : ℝ := (max (b - 13 / 30) (b / 2) + 1 / 2) / 2 with hcdef
  have hmax : max (b - 13 / 30) (b / 2) < 1 / 2 := max_lt (by linarith) (by linarith)
  have hc : c < 1 / 2 := by rw [hcdef]; linarith
  have hc1 : b - 13 / 30 < c := by rw [hcdef]; linarith [le_max_left (b - 13 / 30) (b / 2)]
  have hc2 : b / 2 < c := by rw [hcdef]; linarith [le_max_right (b - 13 / 30) (b / 2)]
  set β_c : ℝ := (b + 1) / 2 with hβc
  obtain ⟨e, he, ⟨A, C₀, hA, hcount⟩, htwin⟩ := exists_isEdit_layerTwinOn
    (Finset.univ : Finset (Fin 2)) ρs (b := b) (c := c) (β := β_c) (by linarith) (by linarith)
    hρle hc1 hc2 (by linarith) (by rw [hβc]; linarith) (by rw [hβc]; linarith)
  have hβc1 : β_c < 1 := by rw [hβc]; linarith
  obtain ⟨C, H, hC, hH, hfac⟩ := id htwin
  have hLd : DifferentiableOn ℂ (layerFactor (Finset.univ : Finset (Fin 2)) ρs)
      {s : ℂ | c < s.re} := (differentiable_layerFactor _ _).differentiableOn
  -- the continuation vanishes at `ρ`
  obtain ⟨G, hGd, hGeq, hGzero⟩ := htwin.exists_continuation hLd
  have hρc : c < ρ.re := by rw [← hb]; linarith
  have hρ1 : ρ ≠ 1 := fun h => by
    have : b = 1 := by rw [hb, h, Complex.one_re]
    linarith
  have hG0 : G ρ = 0 := (hGzero ρ hρc hρ1 hζ).mpr
    ((layerFactor_eq_zero_iff _ _ ρ).mpr ⟨0, Finset.mem_univ _, Or.inl (by simp [hρs])⟩)
  -- an edited prime exists: otherwise `ζ_B = ζ` and `G = (s - 1) ζ(s)`
  have hedit : ∃ p : ℕ, e p ≠ 0 := by
    by_contra hall
    push Not at hall
    have hZ : ∀ s : ℂ, 1 < s.re → (editSystem e).zetaSeriesC s = riemannZeta s := by
      intro s hs
      rw [editSystem_zetaSeriesC he hs]
      have hE : LSeries (fun k => (e k : ℂ)) s = 0 := by
        rw [show (fun k => (e k : ℂ)) = 0 by funext k; simp [hall]]
        exact congrFun LSeries_zero s
      have hQ : editRem e s = 0 := by simp [editRem, hall]
      rw [hE, hQ, add_zero, Complex.exp_zero, mul_one]
    have hZd : DifferentiableOn ℂ zetaResidueUnit {s : ℂ | c < s.re} := fun s _ =>
      (analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt
    have heq : ∀ s : ℂ, 1 < s.re → G s = zetaResidueUnit s := by
      intro s hs
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      rw [hGeq s hs, hZ s hs, zetaResidueUnit_of_ne hs1]
    have hid := eqOn_re_gt_of_eq_on_re_gt_one (by linarith) hGd hZd heq hρc
    rw [hG0, zetaResidueUnit_of_ne hρ1] at hid
    exact mul_ne_zero (sub_ne_zero.mpr hρ1) hζ hid.symm
  obtain ⟨p, hp⟩ := hedit
  -- the edit is an integer-norm fake
  have hfake : IsIntegerNormFakeAt (editSystem e) β_c :=
    ⟨hasIntegerNorms_editSystem e, isDiscrete_editSystem e, notNormEquivPrimes_editSystem he hp,
      ⟨A, C₀, hA, hcount⟩, G, hGd.mono fun s hs => by simp only [Set.mem_setOf_eq] at hs ⊢; linarith,
      hGeq, ρ, hδ0, hρ1, hG0, hζ⟩
  refine ⟨e, β_c, A, C₀, c, C, H, he, hβc1, hcount, hfake, hc, hH, hfac,
    fun t => IsFactorTwinOn.stripDefect_eq hc hLd hH hfac t, fun β g hHam => ?_⟩
  obtain ⟨p₀, hp₀, hep₀, -⟩ := exists_least_deleted_prime hβc1.le hfake
  refine ⟨(editSystem_fake_defect_not_le_sqrt_log hβc1 hfake hcount hHam hp₀ hep₀).2,
    p₀, hp₀, hep₀, editSystem_fake_defect_energy hβc1 hfake hcount hHam hp₀ hep₀⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.FEDefect
