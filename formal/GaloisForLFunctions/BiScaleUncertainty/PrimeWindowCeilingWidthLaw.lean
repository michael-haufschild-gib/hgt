import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingRHCriterion
import GaloisForLFunctions.BiScaleUncertainty.DeficitPrimitiveOneSidedWidth
import GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer

/-!
# The window ceiling reads the zero width

The prime-side ceiling on windows of length `L = log X` is `c(L) = e^{L/2}(1 + o(1))`
(`tendsto_windowCeiling_div_exp`). This file measures its excess over the polar ceiling `e^{L/2}`
against the width of the zero set.

**Theorem.** Let `0 ≤ θ, β < ½`.
* (`xiZeroHalfPlaneBound_of_windowDeviations_le`) If `c(L) ≤ e^{L/2} + B(1+L)e^{θL}` for all large
  `L`, then every zero of `ξ` has `Re ρ ≤ ½ + θ`.
* (`windowDeviations_le_of_xiZeroHalfPlaneBound`) If every zero has `Re ρ ≤ ½ + β`, then for every
  `ε > 0`, `c(L) ≤ e^{L/2} + C e^{(1/4 + β/2 + ε)L}`.

So the excess exponent `θ* = limsup log(c(L) − e^{L/2})/L` satisfies
`width ≤ θ* ≤ width/2 + 1/4`: the zero width is read, with a loss, from a finite prime quantity
(only `n ≤ X` enter `c(log X)`). Under RH the excess is `O(X^{1/4+ε})`; an excess `O(X^ε)` for every
`ε` forces all zeros onto the line up to every width.

**Mechanism.** Lower direction: the polar test with cutoff `δ = e^{−L/2}` turns a ceiling bound into
`D(L) ≥ −(L + 2G(L) + 3 + 2C) e^{L/2}` for the integrated deficit (`deficit_ge_of_windowDeviations_le`,
`G` the allowed excess), and the width-`θ` Landau criterion
(`xiZeroHalfPlaneBound_of_deficitPrimitive_ge`) applies. Upper direction: the polar Schur weight
with the generalized von Koch bound `ψ(x) ≤ x + K x^γ + 1`, `γ = ½ + β + ε`; the error `K x^γ` at
distance `log n` costs `K e^{γL/2}` against the polar weight, the loss coming from the window
midpoint where the weight is `≍ e^{−L/4}`.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. From a ceiling bound to a lower bound on the integrated deficit -/

/-- **The polar test reads the deficit.** If every window deviation at length `L ≥ 4` is at most
`e^{L/2} + G` with `G ≥ 0`, then `D(L) ≥ −(L + 2G + 3 + 2C) e^{L/2}`, `C = log 4 + 5`. -/
theorem deficit_ge_of_windowDeviations_le {L G : ℝ} (hL4 : 4 ≤ L) (hG : 0 ≤ G)
    (h : ∀ x ∈ windowDeviations L, x ≤ Real.exp (L / 2) + G) :
    -((L + 2 * G + 3 + 2 * chebyshevDeficitConst) * Real.exp (L / 2)) ≤
      ccmLogChebyshevDeficitPrimitive L := by
  classical
  set C := chebyshevDeficitConst
  have hC := chebyshevDeficitConst_pos
  set E := Real.exp (L / 2) with hEdef
  have hEL : 0 < E := Real.exp_pos _
  set δ := Real.exp (-(L / 2)) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hLδ : 2 * δ < L := by linarith
  have hEδ : δ * E = 1 := by
    rw [hδdef, hEdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hδneg : Real.exp (-L / 2) = δ := by rw [hδdef]; congr 1; ring
  have hLδ1 : L * δ ≤ 1 := by
    have h1 : 1 + L / 2 + (L / 2) ^ 2 / 2 ≤ E := Real.quadratic_le_exp_of_nonneg (by linarith)
    have : L ≤ E := by nlinarith
    calc L * δ ≤ E * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = 1 := by rw [mul_comm]; exact hEδ
  set T := L - 2 * δ with hTdef
  have hT : 0 ≤ T := by linarith
  set f := polarTestFn hδ hLδ
  set c : WeilTestFn →₀ ℝ := Finsupp.single f 1
  have hc : ∀ g, 0 ≤ c g := fun g => by
    simp only [c]; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hsupp : ∀ g ∈ c.support, ∃ a, ∀ u, g.1 u ≠ 0 → u ∈ Ioo a (a + L) := fun g hg => by
    have : g = f := by
      by_contra hne; exact (Finsupp.mem_support_iff.mp hg) (by simp [c, Ne.symm hne])
    exact ⟨0, this ▸ polarTestFn_supp hδ hLδ⟩
  have hm := massOf_polarTest_pos hδ hLδ
  have hM := massOf_polarTest_le hδ hLδ
  rw [hδneg] at hM
  have hdev : nodeArchEnergy c - weilEnergy c =
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) := by
    rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_single_test]
  have hP := primeSide_polarTest_ge hδ hLδ
  rw [riesz_eq_deficit hT, hδneg, ← hdev] at hP
  have hx := h _ ⟨c, hc, hsupp, hm, rfl⟩
  rw [div_le_iff₀ hm] at hx
  have hpos : 0 ≤ E + G := by positivity
  have hx' : nodeArchEnergy c - weilEnergy c ≤ (E + G) * (2 + 2 * L * δ) :=
    hx.trans (mul_le_mul_of_nonneg_left hM hpos)
  have heT : 2 * E - 4 ≤ 2 * δ * Real.exp T := by
    have h1 : Real.exp T = E * E * Real.exp (-(2 * δ)) := by
      rw [hTdef, hEdef, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h2 : 1 - 2 * δ ≤ Real.exp (-(2 * δ)) := Real.one_sub_le_exp_neg _
    rw [h1]
    have : 2 * δ * (E * E * Real.exp (-(2 * δ))) = 2 * E * Real.exp (-(2 * δ)) := by
      rw [show 2 * δ * (E * E * Real.exp (-(2 * δ))) = 2 * (δ * E) * E * Real.exp (-(2 * δ)) by
        ring, hEδ]; ring
    rw [this]
    nlinarith
  -- `−2δ D(T) ≤ 2L + 4G + 6`
  have hD : -(2 * δ) * ccmLogChebyshevDeficitPrimitive T ≤ 2 * L + 4 * G + 6 := by
    have hexp : (E + G) * (2 + 2 * L * δ) = 2 * E + 2 * L * (δ * E) + 2 * G + 2 * G * (L * δ) := by
      ring
    rw [hexp, hEδ] at hx'
    have hGLδ : 2 * G * (L * δ) ≤ 2 * G := mul_le_of_le_one_right (by positivity) hLδ1
    nlinarith
  have hDT : -((L + 2 * G + 3) * E) ≤ ccmLogChebyshevDeficitPrimitive T := by
    have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ E / 2)
    have e1 : E / 2 * (-(2 * δ) * ccmLogChebyshevDeficitPrimitive T) =
        -(δ * E) * ccmLogChebyshevDeficitPrimitive T := by ring
    rw [e1, hEδ] at this
    nlinarith
  have hshift := deficit_sub_le (show T ≤ L by linarith)
  have hshift' : C * Real.exp L * (L - T) = 2 * C * E := by
    rw [hTdef, show L - (L - 2 * δ) = 2 * δ by ring]
    have : Real.exp L = E * E := by rw [hEdef, ← Real.exp_add]; congr 1; ring
    rw [this, show C * (E * E) * (2 * δ) = 2 * C * E * (δ * E) by ring, hEδ, mul_one]
  rw [hshift'] at hshift
  have habs := neg_abs_le (ccmLogChebyshevDeficitPrimitive L - ccmLogChebyshevDeficitPrimitive T)
  nlinarith

/-! ### 2. Excess exponent bounds the zero width -/

/-- **A ceiling excess `O((1+L)e^{θL})` bounds the zero width by `θ`.** -/
theorem xiZeroHalfPlaneBound_of_windowDeviations_le {θ B : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1 / 2)
    (h : ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L,
      x ≤ Real.exp (L / 2) + B * (1 + L) * Real.exp (θ * L)) :
    XiZeroHalfPlaneBound θ := by
  obtain ⟨L₁, hL₁⟩ := h.exists_forall_of_atTop
  set C := chebyshevDeficitConst
  have hC := chebyshevDeficitConst_pos
  set L₀ := max L₁ 4
  set K₀ := 2 * |B| + 4 + 2 * C
  have hlarge : ∀ L : ℝ, L₀ ≤ L →
      -(K₀ * (1 + L) * Real.exp ((1 / 2 + θ) * L)) ≤ ccmLogChebyshevDeficitPrimitive L := by
    intro L hL
    have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
    have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
    have hθL : 1 ≤ Real.exp (θ * L) := Real.one_le_exp (by nlinarith)
    set G := |B| * (1 + L) * Real.exp (θ * L) with hGdef
    have hG : 0 ≤ G := by positivity
    have hle : ∀ x ∈ windowDeviations L, x ≤ Real.exp (L / 2) + G := fun x hx => by
      have := hL₁ L hL1 x hx
      have : B * (1 + L) * Real.exp (θ * L) ≤ G :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith))
          (Real.exp_pos _).le
      linarith
    have hD := deficit_ge_of_windowDeviations_le hL4 hG hle
    have hsplit : Real.exp ((1 / 2 + θ) * L) = Real.exp (L / 2) * Real.exp (θ * L) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    have hE := Real.exp_pos (L / 2)
    have hbound : L + 2 * G + 3 + 2 * C ≤ K₀ * (1 + L) * Real.exp (θ * L) := by
      have h1 : L + 3 + 2 * C ≤ (4 + 2 * C) * (1 + L) * Real.exp (θ * L) := by
        have : L + 3 + 2 * C ≤ (4 + 2 * C) * (1 + L) := by nlinarith
        calc L + 3 + 2 * C ≤ (4 + 2 * C) * (1 + L) := this
          _ ≤ (4 + 2 * C) * (1 + L) * Real.exp (θ * L) :=
            le_mul_of_one_le_right (by positivity) hθL
      have h2 : 2 * G = 2 * |B| * (1 + L) * Real.exp (θ * L) := by rw [hGdef]; ring
      simp only [K₀]
      nlinarith
    have := mul_le_mul_of_nonneg_right hbound hE.le
    nlinarith
  set B₁ := max K₀ (C * Real.exp L₀)
  refine xiZeroHalfPlaneBound_of_deficitPrimitive_ge (B := B₁) hθ hθ' fun T hT => ?_
  by_cases hTL : L₀ ≤ T
  · have := hlarge T hTL
    have hK : K₀ ≤ B₁ := le_max_left _ _
    have : K₀ * (1 + T) * Real.exp ((1 / 2 + θ) * T) ≤ B₁ * (1 + T) * Real.exp ((1 / 2 + θ) * T) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by linarith)) (Real.exp_pos _).le
    linarith
  · push Not at hTL
    have hab := abs_deficitPrimitive_le hT
    have h1 : C * Real.exp T ≤ C * Real.exp L₀ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hTL.le) hC.le
    have h2 : C * Real.exp L₀ ≤ B₁ := le_max_right _ _
    have h3 : 1 ≤ (1 + T) * Real.exp ((1 / 2 + θ) * T) := by
      have := Real.one_le_exp (by nlinarith : 0 ≤ (1 / 2 + θ) * T)
      nlinarith
    have hB₁ : 0 ≤ B₁ := (by positivity : (0 : ℝ) ≤ C * Real.exp L₀).trans h2
    have : B₁ ≤ B₁ * (1 + T) * Real.exp ((1 / 2 + θ) * T) := by
      rw [mul_assoc]; exact le_mul_of_one_le_right hB₁ h3
    linarith [neg_abs_le (ccmLogChebyshevDeficitPrimitive T)]

/-! ### 3. Zero width bounds the ceiling excess -/

/-- **The polar Schur sum for a general Chebyshev majorant.** If `ψ(e^y) ≤ F(y)` on `[0, L]`, the
neighbour sum at `t = a + τ` is at most `e^{−τ/2}F(τ) + e^{−(L−τ)/2}F(L−τ) + (1+L)²φ(t)`. -/
theorem polar_schur_le_of_psi_le {a L t : ℝ} (ht : t ∈ Ioo a (a + L)) (N : ℕ) {F : ℝ → ℝ}
    (hψ : ∀ y : ℝ, 0 ≤ y → y ≤ L → Chebyshev.psi (Real.exp y) ≤ F y) :
    ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        ((Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) +
          (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n)) ≤
      Real.exp (-(t - a) / 2) * F (t - a) + Real.exp (-(L - (t - a)) / 2) * F (L - (t - a)) +
        (1 + L) ^ 2 * polarWeight a L t := by
  classical
  set τ := t - a with hτdef
  have hτ0 : 0 < τ := by rw [hτdef]; linarith [ht.1]
  have hτL : τ < L := by rw [hτdef]; linarith [ht.2]
  set e₁ := Real.exp (-τ / 2)
  set e₂ := Real.exp (-(L - τ) / 2)
  have he₁ : 0 < e₁ := Real.exp_pos _
  have he₂ : 0 < e₂ := Real.exp_pos _
  have hφ : polarWeight a L t = e₁ + e₂ := by
    rw [polarWeight, clampWindow_of_mem (Ioo_subset_Icc_self ht)]
    simp only [e₁, e₂, hτdef]
    congr 2; ring
  set Λ : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)
  set S := Finset.Ico 2 N
  have hsplit : ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
      ((Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) +
        (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n)) =
      (e₁ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n +
        e₂ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n / n) +
      (e₁ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n / n +
        e₂ * ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 := (Finset.mem_Ico.mp hn).1
    rw [mul_add, atom_mul_indicator_sub ht hn2, atom_mul_indicator_add ht hn2]
  have hexp : ∀ {n : ℕ} {y : ℝ}, 2 ≤ n → Real.log n < y → (n : ℝ) < Real.exp y := by
    intro n y hn h
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hpos).symm
      _ < Real.exp y := Real.exp_lt_exp.mpr h
  have hP1 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n ≤ F τ :=
    (sum_vonMangoldt_le_psi fun n hn => by
      rw [Finset.mem_filter] at hn
      exact (hexp (Finset.mem_Ico.mp hn.1).1 hn.2).le).trans (hψ _ hτ0.le hτL.le)
  have hP2 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n ≤ F (L - τ) :=
    (sum_vonMangoldt_le_psi fun n hn => by
      rw [Finset.mem_filter] at hn
      exact (hexp (Finset.mem_Ico.mp hn.1).1 hn.2).le).trans (hψ _ (by linarith) (by linarith))
  have hM1 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < τ), Λ n / n ≤ (1 + L) ^ 2 :=
    (sum_vonMangoldt_div_le_of_lt_exp hτ0.le fun n hn => by
      rw [Finset.mem_filter] at hn
      exact ⟨by have := (Finset.mem_Ico.mp hn.1).1; omega,
        hexp (Finset.mem_Ico.mp hn.1).1 hn.2⟩).trans
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hτL.le) (by linarith : (0 : ℝ) ≤ 2 + L + τ)])
  have hM2 : ∑ n ∈ S.filter (fun n : ℕ => Real.log n < L - τ), Λ n / n ≤ (1 + L) ^ 2 :=
    (sum_vonMangoldt_div_le_of_lt_exp (τ := L - τ) (by linarith) fun n hn => by
      rw [Finset.mem_filter] at hn
      exact ⟨by have := (Finset.mem_Ico.mp hn.1).1; omega,
        hexp (Finset.mem_Ico.mp hn.1).1 hn.2⟩).trans
      (by nlinarith [mul_pos hτ0 (by linarith : (0 : ℝ) < 2 + 2 * L - τ)])
  rw [hsplit, hφ]
  have h1 := mul_le_mul_of_nonneg_left hP1 he₁.le
  have h2 := mul_le_mul_of_nonneg_left hP2 he₂.le
  have h3 := mul_le_mul_of_nonneg_left hM1 he₂.le
  have h4 := mul_le_mul_of_nonneg_left hM2 he₁.le
  nlinarith

/-- The far-end loss of a power term: `e^{−s/2} e^{γs} ≤ e^{γL/2}(e^{−s/2} + e^{−(L−s)/2})` for
`0 ≤ γ ≤ 1`, `0 ≤ s ≤ L`. -/
theorem exp_half_mul_exp_le {γ L s : ℝ} (hγ1 : γ ≤ 1) (hγ0 : 0 ≤ γ) :
    Real.exp (-s / 2) * Real.exp (γ * s) ≤
      Real.exp (γ * L / 2) * (Real.exp (-s / 2) + Real.exp (-(L - s) / 2)) := by
  rcases le_or_gt s (L / 2) with hs | hs
  · have h1 : Real.exp (γ * s) ≤ Real.exp (γ * L / 2) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.exp_pos (-s / 2)
    have h3 := Real.exp_pos (-(L - s) / 2)
    have h4 := Real.exp_pos (γ * L / 2)
    nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]
  · have h1 : Real.exp (-s / 2) * Real.exp (γ * s) ≤ Real.exp (γ * L / 2) * Real.exp (-(L - s) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h2 := Real.exp_pos (-s / 2)
    have h4 := Real.exp_pos (γ * L / 2)
    nlinarith

/-- **The power-error polar ceiling.** If `ψ(x) ≤ x + K x^γ` for `x ≥ 0` (`K ≥ 0`, `0 ≤ γ ≤ 1`),
then `|A − W| ≤ (e^{L/2} + (1 + L)² + 2K e^{γL/2}) ‖c‖²` on windows of length `L ≥ 0`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_power {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L))
    {K γ : ℝ} (hK : 0 ≤ K) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ x + K * x ^ γ) :
    |nodeArchEnergy c - weilEnergy c| ≤
      (Real.exp (L / 2) + (1 + L) ^ 2 + 2 * K * Real.exp (γ * L / 2)) * massOf c := by
  set C := Real.exp (L / 2) + (1 + L) ^ 2 + 2 * K * Real.exp (γ * L / 2)
  have hN : L ≤ Real.log ⌈Real.exp L⌉₊ :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log ⌈Real.exp L⌉₊ := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  -- the Chebyshev majorant in the logarithmic variable
  have hψe : ∀ y : ℝ, 0 ≤ y → y ≤ L →
      Chebyshev.psi (Real.exp y) ≤ Real.exp y + K * Real.exp (γ * y) := fun y _ _ => by
    have := hψ _ (Real.exp_pos y).le
    rwa [← Real.exp_mul, mul_comm y γ] at this
  have hS : ∀ a t, t ∈ Ioo a (a + L) → ∑ n ∈ Finset.Ico 2 ⌈Real.exp L⌉₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        ((Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) +
          (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n)) ≤ C * polarWeight a L t := by
    intro a t ht
    refine (polar_schur_le_of_psi_le ht _ hψe).trans ?_
    set τ := t - a with hτdef
    have hφ : polarWeight a L t = Real.exp (-τ / 2) + Real.exp (-(L - τ) / 2) := by
      rw [polarWeight, clampWindow_of_mem (Ioo_subset_Icc_self ht)]
      congr 2; ring
    have hc1 : Real.exp (-τ / 2) * Real.exp τ = Real.exp (L / 2) * Real.exp (-(L - τ) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hc2 : Real.exp (-(L - τ) / 2) * Real.exp (L - τ) =
        Real.exp (L / 2) * Real.exp (-τ / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hp1 := exp_half_mul_exp_le (s := τ) (L := L) hγ1 hγ0
    have hp2 := exp_half_mul_exp_le (s := L - τ) (L := L) hγ1 hγ0
    rw [show -(L - (L - τ)) / 2 = -τ / 2 by ring] at hp2
    rw [hφ]
    have e1 : Real.exp (-τ / 2) * (Real.exp τ + K * Real.exp (γ * τ)) =
        Real.exp (L / 2) * Real.exp (-(L - τ) / 2) + K * (Real.exp (-τ / 2) * Real.exp (γ * τ)) := by
      rw [← hc1]; ring
    have e2 : Real.exp (-(L - τ) / 2) * (Real.exp (L - τ) + K * Real.exp (γ * (L - τ))) =
        Real.exp (L / 2) * Real.exp (-τ / 2) +
          K * (Real.exp (-(L - τ) / 2) * Real.exp (γ * (L - τ))) := by
      rw [← hc2]; ring
    rw [e1, e2]
    have k1 := mul_le_mul_of_nonneg_left hp1 hK
    have k2 := mul_le_mul_of_nonneg_left hp2 hK
    simp only [C]
    nlinarith
  rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_eq,
    linearCombination_apply ℝ (v := logVector), map_finsuppSum]
  have hX : ∀ f ∈ c.support,
      |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (c f • logVector f)| ≤ c f * (C * ∫ u, ‖f.1 u‖ ^ 2) := by
    intro f hf
    obtain ⟨a, ha⟩ := hsupp f hf
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hc f)]
    exact mul_le_mul_of_nonneg_left (abs_primeSide_le_of_window_schur ha hN
      (continuous_polarWeight a L).measurable (Real.exp_pos (-L / 2))
      (polarWeight_pos_lower hL) (polarWeight_le hL) fun t ht => hS a t ht) (hc f)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [WeilOneSided.massOf, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  have := hX f hf
  linarith

/-- `(1 + L)² ≤ 66 e^{L/4}` for `L ≥ 0`. -/
theorem one_add_sq_le_exp_quarter {L : ℝ} (hL : 0 ≤ L) : (1 + L) ^ 2 ≤ 66 * Real.exp (L / 4) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ L / 4)
  nlinarith [sq_nonneg (L - 1)]

/-- **Zero width bounds the ceiling excess.** If every zero has `Re ρ ≤ ½ + β` (`0 ≤ β`), then for
every `ε > 0` with `β + ε ≤ ½` there is `C` with `|x| ≤ e^{L/2} + C e^{(1/4 + β/2 + ε)L}` for every
window deviation at every length `L ≥ 0`. -/
theorem windowDeviations_le_of_xiZeroHalfPlaneBound {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1 / 2)
    (hXi : XiZeroHalfPlaneBound β) {ε : ℝ} (hε : 0 < ε) (hβε : β + ε ≤ 1 / 2) :
    ∃ C : ℝ, ∀ L : ℝ, 0 ≤ L → ∀ x ∈ windowDeviations L,
      |x| ≤ Real.exp (L / 2) + C * Real.exp ((1 / 4 + β / 2 + ε) * L) := by
  obtain ⟨K, hK, hvk⟩ :=
    RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound hβ hβ' hXi hε
  set γ := 1 / 2 + β + ε with hγdef
  have hγ0 : 0 ≤ γ := by rw [hγdef]; linarith
  have hγ1 : γ ≤ 1 := by rw [hγdef]; linarith
  have hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ x + K * x ^ γ := by
    intro x hx
    rcases lt_or_ge x 1 with hx1 | hx1
    · have h0 : Chebyshev.psi x = 0 := by
        have h1 : Chebyshev.psi x ≤ Chebyshev.psi 1 := Chebyshev.psi_mono hx1.le
        have h2 : Chebyshev.psi 1 = 0 := by
          rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_one, Finset.sum_Icc_succ_top (by norm_num),
            Finset.Icc_self, Finset.sum_singleton]
          simp [ArithmeticFunction.vonMangoldt_apply_one]
        linarith [Chebyshev.psi_nonneg x]
      rw [h0]
      have := Real.rpow_nonneg hx γ
      positivity
    · have := hvk x hx1
      rw [RHTower.FreeLagTrace.chebyshevPsiReal_eq_psi] at this
      linarith [le_abs_self (Chebyshev.psi x - x)]
  refine ⟨66 + 2 * K, fun L hL x hx => ?_⟩
  obtain ⟨c, hc, hs, hm, rfl⟩ := hx
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_power hc hL hs hK.le hγ0 hγ1 hψ
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  have hq : (1 + L) ^ 2 ≤ 66 * Real.exp ((1 / 4 + β / 2 + ε) * L) :=
    (one_add_sq_le_exp_quarter hL).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num))
  have hk : 2 * K * Real.exp (γ * L / 2) ≤ 2 * K * Real.exp ((1 / 4 + β / 2 + ε) * L) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [hγdef]; nlinarith)) (by positivity)
  have hmass : 0 ≤ massOf c := hm.le
  nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty
