import GaloisForLFunctions.SquareRootThreshold.LargeDyadicPrimeWindowsDecideTheCriticalLine

/-!
# Pole-free dyadic windows decide the critical line

The polar-free bump `κ₂ = κ'' − κ/4` has `h_{κ₂}(±i/2) = 0`, so the two-bump tests built from it
lie in the Hodge class and their Weil kernels `k` have no pole terms. The window criterion then
compares the primes of one dyadic window with the archimedean term alone.

* **Tail Hodge criterion** (`onLine_or_poles_iff_polarFree_twoBump_nonneg_of_ge`). For every `V`,
  a tempered configuration is Weil nonnegative on the polar-free unimodular two-bump tests with
  lag `v ≥ V` iff each zero lies on the critical line or at `s = 0, 1`.
* **For `ζ`** (`onLine_iff_polarFree_primeWindow_le_arch`). Let `0 < w`, `2w < log 2`, `V ≥ 0`.
  RH holds iff for every height `γ`, lag `v ≥ V` and `|τ| = 1`,
  `Re Σ_{|log n − v| ≤ 2w} Λ(n)/√n (k(log n) + k(−log n)) ≤ Re (1/2π) ∫ h_k Γ`.
  Here `k` is the kernel of `κ₂,γ(t + v/2) + τκ₂,γ(t − v/2)` (`polarFreeKernel`). Each inequality
  weighs the primes of one window `(X/2, 2X)`, `X = e^v`, against the archimedean term at
  height `γ`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Tail visibility in the Hodge class.** An off-line zero other than `0, 1` breaks a polar-free
minor at a lag beyond any `V`. -/
theorem exists_minor_fails_polarFree_of_ge (Z : ZeroConfig) (hZ : TemperedConfig Z) {w : ℝ}
    (hw : 0 < w) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hre : ρ.re ≠ 1 / 2) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1)
    (V : ℝ) :
    ∃ γ v : ℝ, 0 ≤ v ∧ V ≤ v ∧ 2 * (lagStructure Z (scaledBumpPolarFree w γ) 0).re <
      ‖lagStructure Z (scaledBumpPolarFree w γ) v +
        conj (lagStructure Z (scaledBumpPolarFree w γ) (-v))‖ := by
  obtain ⟨t, ht, ht1⟩ := exists_rightZero_of_offLine Z hρ hre
  have ht1 := ht1 h0 h1
  have hqt : offLineWeight (scaledBumpPolarFree w t.im) (Z.mult t) t ≠ 0 := by
    have hm := Z.one_le_mult t ht.1
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (by omega))
      (pairWeight_polarFree_ne_zero hw (by linarith [ht.2]) ?_)
    rintro ⟨hi, hd⟩
    exact ht1 (Complex.ext (by simp; linarith) (by simpa using hi))
  obtain ⟨t₀, ht₀, him₀, hq₀, htop⟩ := exists_top_at_height Z ht
    (fun z => offLineWeight (scaledBumpPolarFree w t.im) (Z.mult z) z ≠ 0) hqt
  obtain ⟨v, hv, hV, hgt⟩ := exists_minor_gt_of_top_of_ge Z hZ (contDiff_scaledBumpPolarFree w t.im)
    (scaledBumpPolarFree_support hw t.im) ht₀ hq₀
    (fun t' ht' him' hq' => htop t' ht' (him'.trans him₀) hq') le_rfl
    (by linarith [ht₀.2]) 0 V
  exact ⟨t.im, v, hv, hV, by simpa using hgt⟩

/-- **Tail Hodge criterion.** For every `V`, a tempered configuration is Weil nonnegative on the
polar-free unimodular two-bump tests with lag `v ≥ V` iff each of its zeros lies on the critical
line or at `s = 0, 1`. -/
theorem onLine_or_poles_iff_polarFree_twoBump_nonneg_of_ge (Z : ZeroConfig)
    (hZ : TemperedConfig Z) {w : ℝ} (hw : 0 < w) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1) ↔ ∀ (γ v : ℝ) (τ : ℂ), V ≤ v → ‖τ‖ = 1 →
      0 ≤ (Z.W (twoBump (scaledBumpPolarFree w γ) v τ)
        (twoBump (scaledBumpPolarFree w γ) v τ)).re := by
  refine ⟨fun hon γ v τ _ _ => ?_, fun h ρ hρ => ?_⟩
  · obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half hw γ
    have hbc := hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw γ)
    have hc := (contDiff_scaledBumpPolarFree w γ).continuous
    refine re_W_nonneg_of_summand_nonneg Z fun ρ hρ => ?_
    rcases hon ρ hρ with h | h
    · exact re_Wsummand_nonneg_of_onLine Z _ h
    · rw [Wsummand_eq_zero_of_pole Z (paperFT_twoBump_eq_zero hc hbc v τ hp)
        (paperFT_twoBump_eq_zero hc hbc v τ hn) h, Complex.zero_re]
  · by_contra hcon
    push Not at hcon
    obtain ⟨γ, v, -, hV, hgt⟩ :=
      exists_minor_fails_polarFree_of_ge Z hZ hw hρ hcon.1 hcon.2.1 hcon.2.2 V
    obtain ⟨τ, hτ, heq⟩ := exists_unit_re_W_eq_minorDeficit Z hZ
      (contDiff_scaledBumpPolarFree w γ) (scaledBumpPolarFree_support hw γ) v
    have := h γ v τ hV hτ
    rw [heq, minorDeficit] at this
    linarith

/-- The Weil kernel of the polar-free unimodular two-bump test `κ₂,γ(t + v/2) + τκ₂,γ(t − v/2)`. -/
def polarFreeKernel (w γ v : ℝ) (τ : ℂ) : ℝ → ℂ :=
  EF.weilTest (twoBump (scaledBumpPolarFree w γ) v τ) (twoBump (scaledBumpPolarFree w γ) v τ)

/-- **RH as archimedean dominance of pole-free dyadic prime windows.** Let `0 < w`,
`2w < log 2` and `V ≥ 0`. Every nontrivial zero of `ζ` lies on the critical line iff, for every
height `γ`, lag `v ≥ V` and `|τ| = 1`, the window prime sum of `k = polarFreeKernel w γ v τ` is at
most its archimedean term. -/
theorem onLine_iff_polarFree_primeWindow_le_arch {w : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) {V : ℝ} (hV : 0 ≤ V) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), V ≤ v → ‖τ‖ = 1 →
        (∑ n ∈ lagPrimeWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (polarFreeKernel w γ v τ (Real.log n) + polarFreeKernel w γ v τ (-Real.log n))).re ≤
        ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (polarFreeKernel w γ v τ) r *
          (EF.gammaBracket r : ℂ)).re := by
  have hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, (ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1) ↔ ρ.re = 1 / 2 := by
    intro ρ hρ
    have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
    refine ⟨fun h' => ?_, Or.inl⟩
    rcases h' with h' | rfl | rfl
    · exact h'
    · simp at h
    · simp at h
  refine (forall₂_congr fun ρ hρ => hstrip ρ hρ).symm.trans
    ((onLine_or_poles_iff_polarFree_twoBump_nonneg_of_ge _ temperedConfig_zetaZeroConfig hw
      V).trans ?_)
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ =>
    imp_congr_right fun hv => imp_congr_right fun _ => ?_
  have hc := (contDiff_scaledBumpPolarFree w γ).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support hw γ)
  have hfc := hasCompactSupport_twoBump hbc v τ
  have hfcont : Continuous (twoBump (scaledBumpPolarFree w γ) v τ) :=
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree w γ) v ![1, τ]).continuous
  obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half hw γ
  have hpole : ∀ z : ℂ, paperFT (twoBump (scaledBumpPolarFree w γ) v τ) z = 0 →
      paperFT (polarFreeKernel w γ v τ) z = 0 := fun z hz => by
    rw [polarFreeKernel, EF.paperFT_weilTest hfcont hfcont hfc hfc, hz, zero_mul]
  rw [zeta_W_eq_literatureRHS (f := twoBump (scaledBumpPolarFree w γ) v τ)
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree w γ) v ![1, τ]) hfc,
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (scaledBumpPolarFree_support hw γ) hw2
      (hV.trans hv), lagPrimeWindowRHS, ← polarFreeKernel,
    hpole _ (paperFT_twoBump_eq_zero hc hbc v τ hp),
    hpole _ (by rw [neg_div]; exact paperFT_twoBump_eq_zero hc hbc v τ hn)]
  simp only [add_zero, zero_sub, Complex.add_re, Complex.neg_re]
  constructor <;> intro h <;> linarith
