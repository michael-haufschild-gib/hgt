import GaloisForLFunctions.SquareRootThreshold.DilutedOffLineLatticeHidingLaw

/-!
# Rigidity of periodic depth profiles at the square-root threshold

A periodic depth profile puts depth `d_r ≥ 0` at the ordinates `2π(r + jP)/L`; residues with
`d_r = 0` carry double on-line points (`profileConfig`). Its Nyquist aperture is `L/2`, and the
uniform depth reaches it (`uniformProfile_weil_nonneg_of_le_nyquist`).

**Profile rigidity** (`profile_hides_frequently_iff_uniform`,
`profile_hodge_frequently_iff_uniform`). Fix a profile `d` of period `P` with at least one
off-line residue. It hides, equivalently satisfies the Hodge index, at some aperture
`a > (P − 1)L/(2P)` for unboundedly many `L` iff its depth is constant. The modes
`D(m) = Σ_r 2cosh(d_r mL/P) e^{2πirm/P}` with `1 ≤ m < P` must stay below `2P`; as `L` grows the
deepest residues dominate them, and the vanishing of their power sums forces every residue to be
deepest (`uniform_crystal_of_frequently_bounded_modes`).

Consequently on-line and off-line zeros cannot share a fixed periodic shape that hides up to the
square-root threshold at growing density: any on-line residue, and any variation of depth, makes
the profile visible at every aperture above `(P − 1)L/(2P)` for all large `L`
(`exists_visible_profile_of_not_uniform`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The modes of a profile are the cosh-weighted power sums of the `P`-th roots of unity. -/
theorem depthSymbol_nat_eq (L : ℝ) {P : ℕ} (d : Fin P → ℝ) (m : ℕ) :
    depthSymbol L d m = ∑ r, ((2 * Real.cosh (d r * (m * (L / P))) : ℝ) : ℂ) *
      cexp (2 * π * I * (r : ℕ) / P) ^ m := by
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **Profile rigidity.** A periodic depth profile with an off-line residue that hides at some
aperture `a > (P − 1)L/(2P)` for unboundedly many `L` has constant depth. -/
theorem uniform_of_profile_hiding {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r)
    (hd1 : ∀ r, d r ≤ 1 / 2) (hpos : ∃ r, 0 < d r)
    (h : ∀ L₀ : ℝ, ∃ L : ℝ, ∃ hL : 0 < L, L₀ ≤ L ∧ ∃ a : ℝ, ((P : ℝ) - 1) * (L / P) / 2 < a ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) :
    ∀ r r', d r = d r' := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hfreq : ∃ᶠ ℓ in atTop, ∀ m : ℕ, 1 ≤ m → m < P →
      ‖∑ r, ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) *
        cexp (2 * π * I * (r : ℕ) / P) ^ m‖ ≤ 2 * P := by
    rw [frequently_atTop]
    intro ℓ₀
    obtain ⟨L, hL, hL₀, a, ha, hhide⟩ := h (ℓ₀ * P)
    refine ⟨L / P, by rw [le_div_iff₀ hPr]; exact hL₀, fun m hm1 hmP => ?_⟩
    have ha0 : 0 < a := lt_of_le_of_lt (by
      have : (1 : ℝ) ≤ P := by exact_mod_cast hP
      have : 0 ≤ ((P : ℝ) - 1) * (L / P) := by
        apply mul_nonneg (by linarith) (by positivity)
      linarith) ha
    have hn : m < ⌈2 * a * P / L⌉₊ := by
      refine lt_of_lt_of_le hmP (Nat.le_of_pred_lt ?_)
      rw [Nat.lt_ceil, lt_div_iff₀ hL]
      have h1 : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ P), Nat.cast_one]
      rw [Nat.pred_eq_sub_one, h1]
      have h2 : ((P : ℝ) - 1) * (L / P) / 2 * (2 * P) = ((P : ℝ) - 1) * L := by
        field_simp
      nlinarith
    have := norm_depthSymbol_le_of_weil_nonneg hL hP d hd0 hd1 ha0 hhide hm1 hn
    rwa [depthSymbol_nat_eq] at this
  exact (uniform_crystal_of_frequently_bounded_modes d hd0 hpos _
    (fun r => Complex.exp_ne_zero _) hfreq).1

/-- **Profile rigidity, both directions.** A periodic depth profile with an off-line residue hides
at some aperture `a > (P − 1)L/(2P)` for unboundedly many `L` iff its depth is constant; then it
hides up to `L/2` at every `L`. -/
theorem profile_hides_frequently_iff_uniform {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) (hpos : ∃ r, 0 < d r) :
    (∀ L₀ : ℝ, ∃ L : ℝ, ∃ hL : 0 < L, L₀ ≤ L ∧ ∃ a : ℝ, ((P : ℝ) - 1) * (L / P) / 2 < a ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) ↔
      ∀ r r', d r = d r' := by
  constructor
  · exact uniform_of_profile_hiding hP d hd0 hd1 hpos
  · intro hu L₀
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP
    have hL : 0 < max L₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨max L₀ 1, hL, le_max_left _ _, max L₀ 1 / 2, ?_, fun f hf hfs => ?_⟩
    · have : ((P : ℝ) - 1) * (max L₀ 1 / P) < P * (max L₀ 1 / P) :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)
      rw [show (P : ℝ) * (max L₀ 1 / P) = max L₀ 1 by field_simp] at this
      linarith
    · -- the profile is the uniform one
      set r₀ : Fin P := ⟨0, hP⟩
      have hd : d = fun _ => d r₀ := funext fun r => hu r r₀
      have key : ∀ (e : Fin P → ℝ) (he : e = fun _ => d r₀) (he0 : ∀ r, 0 ≤ e r)
          (he1 : ∀ r, e r ≤ 1 / 2),
          0 ≤ ((profileConfig hL hP e he0 he1).W f f).re := by
        intro e he he0 he1
        subst he
        exact uniformProfile_weil_nonneg_of_le_nyquist hL hP (hd0 r₀) (hd1 r₀)
          (by positivity) le_rfl hf hfs
      exact key d hd hd0 hd1

/-- **Profile rigidity for the Hodge index.** -/
theorem profile_hodge_frequently_iff_uniform {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) (hpos : ∃ r, 0 < d r) :
    (∀ L₀ : ℝ, ∃ L : ℝ, ∃ hL : 0 < L, L₀ ≤ L ∧ ∃ a : ℝ, ((P : ℝ) - 1) * (L / P) / 2 < a ∧
      HodgeIndexAtLevel (profileConfig hL hP d hd0 hd1) a) ↔
      ∀ r r', d r = d r' := by
  rw [← profile_hides_frequently_iff_uniform hP d hd0 hd1 hpos]
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  refine forall_congr' fun L₀ => exists_congr fun L => exists_congr fun hL =>
    and_congr_right fun _ => exists_congr fun a => and_congr_right fun ha => ?_
  have ha0 : 0 < a := lt_of_le_of_lt (by
    have : 0 ≤ ((P : ℝ) - 1) * (L / P) := mul_nonneg (by linarith) (by positivity)
    linarith) ha
  exact profileConfig_hodgeIndex_iff hL hP d hd0 hd1 ha0

/-- **Visibility below the threshold.** A periodic depth profile with an off-line residue and
non-constant depth (in particular, any profile mixing on-line and off-line residues) is visible,
for all large `L`, at every aperture `a > (P − 1)L/(2P)`. -/
theorem exists_visible_profile_of_not_uniform {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) (hpos : ∃ r, 0 < d r)
    (hnot : ¬ ∀ r r', d r = d r') :
    ∃ L₀ : ℝ, ∀ L : ℝ, ∀ hL : 0 < L, L₀ ≤ L → ∀ a : ℝ, ((P : ℝ) - 1) * (L / P) / 2 < a →
      ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((profileConfig hL hP d hd0 hd1).W f f).re < 0 := by
  by_contra hcon
  push Not at hcon
  exact hnot (uniform_of_profile_hiding hP d hd0 hd1 hpos hcon)

end GaloisForLFunctions.SquareRootThreshold
