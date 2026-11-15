import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRulerCarriesTheSeedAndEveryLever
import GaloisForLFunctions.ArithmeticPositiveDuality.ATwoScaleIntegerNormOneOff
import GaloisForLFunctions.InfiniteRankWeilTheory.TheFunctionalEquationAdmitsEveryFiniteLayer
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.EverySparseConfigurationIsRealized

/-!
# Levers that bite fail in the worlds

A lever valid for every member of a family bites at no abscissa the family realizes
(`disjoint_excluded_range_of_isLever`). Three families of the corpus realize intervals of abscissas,
so every lever that bites there, and every seed below them, uses a property the family lacks.

* **Euler products without a functional equation.** Integer-norm Euler products with natural
  coefficients, linear count, continuation to `Re s > 1/3` and no zero on the critical line realize
  every abscissa in `(½, 2/3)` (`exists_eulerWorld_zeroAbscissa_eq`), with any asymptotic abscissa
  below it (`exists_eulerWorld_abscissas_eq`). No lever of this family bites in `(½, 2/3)`
  (`le_apply_of_isLever_eulerWorlds`), and no bound of the abscissa by a function of the asymptotic
  abscissa holds below `2/3` (`two_thirds_le_of_forall_eulerWorld_le`).
* **Functional equations without a Dirichlet series.** The cosh models, entire of order one with
  the functional equation and reality, realize every abscissa `b ≥ ½`
  (`exists_coshModel_zeroSupRe_eq`); no lever of this family bites anywhere
  (`le_apply_of_isLever_coshModels`).
* **Edits of the primes.** For `7/8 < σ < 14/15` a two-sided edit of the rational primes, with
  count `A x + O(x^{14/15})`, has a zeta function whose zeros right of `7/8` lie exactly on
  `Re s = σ` (`exists_isEdit_zeros_on_line_right_of_seed`): the seed `7/8` is false for it.

Consequently a frame `b ↦ (c + b)/k` with centre below `2/3` is a lever in neither of the first
two families (`exists_world_not_isLever_frame`): a proof of such a lever for `ζ` uses both the
Dirichlet series and the functional equation, and a proof of the seed uses a property of the
rational primes that an edit with a power saving in its count lacks.
-/

open Complex Filter Topology Set

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open Zeta23 (ZeroConfig)
open GaloisForLFunctions.FamilyContinuationTheory (pairingStep)
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa (zeroAbscissa asymptoticAbscissa)
open GaloisForLFunctions.InfiniteRankWeilTheory (coshModel coshModel_eq_zero_iff
  re_eq_half_of_cosh_eq_zero)
open GaloisForLFunctions.WorldsOfTheZeroConfiguration (HasFakeZeroSet linePoints
  exists_isEdit_zeros_on_a_vertical_line)
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits (IsEdit editSystem)

/-! ### 1. Euler products without a functional equation -/

/-- `Z` is the configuration of an **integer-norm Euler product**: natural norms `q k ≥ 2`, natural
coefficients with linear count, continuation to `Re s > 1/3` off `s = 1`, no zero on the critical
line, and zeros right of the line equal to the right half of `Z`. -/
def IsEulerWorld (Z : ZeroConfig) : Prop :=
  ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧
    (∀ s : ℂ, 1 < s.re →
      HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
      LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
    DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
    (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
    {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re}

/-- Every pair `½ < θ < b < 2/3` is the pair (asymptotic abscissa, abscissa) of an Euler world. -/
theorem exists_eulerWorld_abscissas_eq {θ b : ℝ} (hθ : 1 / 2 < θ) (hθb : θ < b) (hb : b < 2 / 3) :
    ∃ Z : ZeroConfig, IsEulerWorld Z ∧ zeroAbscissa Z = b ∧ asymptoticAbscissa Z = θ := by
  obtain ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, -, -, -, hΘ, hΘ', -⟩ :=
    ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff.exists_two_scale_integer_norm_euler_product
      (θ := θ) (θ₂ := θ) (β := b) (γ := 1) hθ le_rfl hθb hb one_pos
  exact ⟨Z, ⟨q, a, hq, F, A, hA, hEuler, hcount, hdiff, hcrit, hright⟩, hΘ, hΘ'⟩

/-- Every abscissa in `(½, 2/3)` is the abscissa of an Euler world. -/
theorem exists_eulerWorld_zeroAbscissa_eq {b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) (2 / 3)) :
    ∃ Z : ZeroConfig, IsEulerWorld Z ∧ zeroAbscissa Z = b := by
  obtain ⟨Z, hZ, hΘ, -⟩ := exists_eulerWorld_abscissas_eq (θ := (1 / 2 + b) / 2)
    (by linarith only [hb.1]) (by linarith only [hb.1]) hb.2
  exact ⟨Z, hZ, hΘ⟩

/-- **No lever of the Euler worlds bites below `2/3`.** -/
theorem le_apply_of_isLever_eulerWorlds {T : ℝ → ℝ}
    (h : ∀ Z : ZeroConfig, IsEulerWorld Z → IsLever (zeroAbscissa Z) T) {b : ℝ}
    (hb : b ∈ Ioo (1 / 2 : ℝ) (2 / 3)) : b ≤ T b := by
  obtain ⟨Z, hZ, rfl⟩ := exists_eulerWorld_zeroAbscissa_eq hb
  exact (h Z hZ).le_apply_self

/-- A map that bites at a point of `(½, 2/3)` is not a lever for some Euler world. -/
theorem exists_eulerWorld_not_isLever {T : ℝ → ℝ} {b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) (2 / 3))
    (hT : T b < b) : ∃ Z : ZeroConfig, IsEulerWorld Z ∧ ¬ IsLever (zeroAbscissa Z) T := by
  by_contra hcon
  push Not at hcon
  exact absurd (le_apply_of_isLever_eulerWorlds hcon hb) (not_le.mpr hT)

/-- **The asymptotic abscissa bounds nothing on Euler worlds.** A bound `Θ ≤ G(Θ_∞)` valid for
every Euler world has `G ≥ 2/3` on `(½, 2/3)`. -/
theorem two_thirds_le_of_forall_eulerWorld_le {G : ℝ → ℝ}
    (h : ∀ Z : ZeroConfig, IsEulerWorld Z → zeroAbscissa Z ≤ G (asymptoticAbscissa Z)) {θ : ℝ}
    (hθ : θ ∈ Ioo (1 / 2 : ℝ) (2 / 3)) : 2 / 3 ≤ G θ := by
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨b', hb', hb'2⟩ : ∃ b', max b θ < b' ∧ b' < 2 / 3 := exists_between (max_lt hb hθ.2)
  obtain ⟨Z, hZ, hΘ, hΘ'⟩ := exists_eulerWorld_abscissas_eq hθ.1
    ((le_max_right b θ).trans_lt hb') hb'2
  have := h Z hZ
  rw [hΘ, hΘ'] at this
  exact ((le_max_left b θ).trans_lt hb').trans_le this

/-! ### 2. Functional equations without a Dirichlet series -/

/-- The supremum of the real parts of the zeros of a function. -/
noncomputable def zeroSupRe (G : ℂ → ℂ) : ℝ := sSup (re '' {s | G s = 0})

/-- The cosh model of one quartet right of the line has abscissa the real part of its point. -/
theorem zeroSupRe_coshModel_singleton {q : ℂ} (hq : 1 / 2 ≤ q.re) :
    zeroSupRe (coshModel {q}) = q.re := by
  have hmem : q.re ∈ re '' {s | coshModel {q} s = 0} :=
    ⟨q, (coshModel_eq_zero_iff {q} q).2 (Or.inr ⟨q, Finset.mem_singleton_self q, Or.inl rfl⟩), rfl⟩
  have hub : ∀ x ∈ re '' {s | coshModel {q} s = 0}, x ≤ q.re := by
    rintro _ ⟨s, hs, rfl⟩
    rcases (coshModel_eq_zero_iff {q} s).1 hs with hc | ⟨q', hq', hsq⟩
    · rw [re_eq_half_of_cosh_eq_zero hc]
      exact hq
    · rw [Finset.mem_singleton] at hq'
      subst hq'
      rcases hsq with rfl | rfl | rfl | rfl
      · exact le_rfl
      · rw [conj_re]
      · rw [sub_re, one_re]
        linarith only [hq]
      · rw [sub_re, one_re, conj_re]
        linarith only [hq]
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨q.re, hub⟩ hmem)

/-- Every `b ≥ ½` is the abscissa of an entire function of order one with the functional equation
and reality. -/
theorem exists_coshModel_zeroSupRe_eq {b : ℝ} (hb : 1 / 2 ≤ b) :
    ∃ Q : Finset ℂ, zeroSupRe (coshModel Q) = b := by
  refine ⟨{(b : ℂ) + I}, ?_⟩
  rw [zeroSupRe_coshModel_singleton (by simpa using hb)]
  simp

/-- **No lever of the cosh models bites.** -/
theorem le_apply_of_isLever_coshModels {T : ℝ → ℝ}
    (h : ∀ Q : Finset ℂ, IsLever (zeroSupRe (coshModel Q)) T) {b : ℝ} (hb : 1 / 2 ≤ b) :
    b ≤ T b := by
  obtain ⟨Q, rfl⟩ := exists_coshModel_zeroSupRe_eq hb
  exact (h Q).le_apply_self

/-- A map that bites at a point `b ≥ ½` is not a lever for some cosh model. -/
theorem exists_coshModel_not_isLever {T : ℝ → ℝ} {b : ℝ} (hb : 1 / 2 ≤ b) (hT : T b < b) :
    ∃ Q : Finset ℂ, ¬ IsLever (zeroSupRe (coshModel Q)) T := by
  by_contra hcon
  push Not at hcon
  exact absurd (le_apply_of_isLever_coshModels hcon hb) (not_le.mpr hT)

/-! ### 3. Frames and the seed -/

/-- **A frame with centre below `2/3` is a lever in neither family.** It fails for an integer-norm
Euler product and for an entire function with the functional equation. -/
theorem exists_world_not_isLever_frame {c k : ℝ} (hk : 1 < k) (hcen : c / (k - 1) < 2 / 3) :
    (∃ Z : ZeroConfig, IsEulerWorld Z ∧ ¬ IsLever (zeroAbscissa Z) (pairingStep c k)) ∧
      ∃ Q : Finset ℂ, ¬ IsLever (zeroSupRe (coshModel Q)) (pairingStep c k) := by
  obtain ⟨b, hb1, hb2⟩ : ∃ b, max (1 / 2) (c / (k - 1)) < b ∧ b < 2 / 3 :=
    exists_between (max_lt (by norm_num) hcen)
  have hhalf : 1 / 2 < b := (le_max_left _ _).trans_lt hb1
  have hcb : c < (k - 1) * b := by
    have := (le_max_right (1 / 2) (c / (k - 1))).trans_lt hb1
    rw [div_lt_iff₀ (by linarith only [hk])] at this
    linarith only [this]
  have hT : pairingStep c k b < b := by
    unfold pairingStep
    rw [div_lt_iff₀ (by linarith only [hk])]
    linarith only [hcb]
  exact ⟨exists_eulerWorld_not_isLever ⟨hhalf, hb2⟩ hT, exists_coshModel_not_isLever hhalf.le hT⟩

/-- **The seed is false for an edit of the primes.** For `7/8 < σ < 14/15` there is a two-sided
edit of the rational primes with count `A x + O(x^{14/15})` whose zeta function, continued to
`Re s > ½`, has a zero on `Re s = σ`, and all its zeros right of `7/8` other than `s = 1` lie on
that line. -/
theorem exists_isEdit_zeros_on_line_right_of_seed {σ : ℝ} (hσ : 7 / 8 < σ) (hσ1 : σ < 14 / 15) :
    ∃ e : ℕ → ℤ, IsEdit e ∧
      (∃ A' C : ℝ, 0 ≤ A' ∧ ∀ x : ℝ, 1 ≤ x →
        |((editSystem e).countBall x : ℝ) - A' * x| ≤ C * x ^ (14 / 15 : ℝ)) ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
        (∃ z : ℂ, z.re = σ ∧ G z = 0) ∧
        ∀ z : ℂ, 7 / 8 < z.re → z ≠ 1 → G z = 0 → z.re = σ := by
  have hd : 0 < 14 / 15 - σ := by linarith only [hσ1]
  have hA : 0 < 1 / (14 / 15 - σ) := one_div_pos.mpr hd
  have hroom : σ + 1 / (2 * (1 / (14 / 15 - σ))) < 14 / 15 := by
    have : 1 / (2 * (1 / (14 / 15 - σ))) = (14 / 15 - σ) / 2 := by
      field_simp
    rw [this]
    linarith only [hd]
  obtain ⟨e, he, hcount, G, hG, hGF, hzero⟩ :=
    exists_isEdit_zeros_on_a_vertical_line (σ := σ) (A := 1 / (14 / 15 - σ))
      (by linarith only [hσ]) hA hroom (β := 14 / 15) hroom (by norm_num)
  have hζ : ∀ z : ℂ, 7 / 8 < z.re → riemannZeta z ≠ 0 := fun z hz =>
    MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_seven_eighths_lt_re hz
  have hline : ∀ z : ℂ, (∃ j, z = linePoints σ (1 / (14 / 15 - σ)) j ∨
      z = (starRingEnd ℂ) (linePoints σ (1 / (14 / 15 - σ)) j)) → z.re = σ := by
    rintro z ⟨j, rfl | rfl⟩
    · rfl
    · rw [conj_re]
      rfl
  refine ⟨e, he, hcount, G, hG, hGF, ⟨linePoints σ (1 / (14 / 15 - σ)) 0, rfl, ?_⟩, ?_⟩
  · have hre : (linePoints σ (1 / (14 / 15 - σ)) 0).re = σ := rfl
    have hne : linePoints σ (1 / (14 / 15 - σ)) 0 ≠ 1 := fun h1 => by
      have := congrArg Complex.re h1
      rw [hre, one_re] at this
      linarith only [this, hσ1]
    exact (hzero _ (by rw [hre]; linarith only [hσ]) hne (hζ _ (by rw [hre]; exact hσ))).2
      ⟨0, Or.inl rfl⟩
  · intro z hz hz1 hGz
    exact hline z ((hzero z (by linarith only [hz]) hz1 (hζ z hz)).1 hGz)

#print axioms two_thirds_le_of_forall_eulerWorld_le
#print axioms exists_world_not_isLever_frame
#print axioms exists_isEdit_zeros_on_line_right_of_seed

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
