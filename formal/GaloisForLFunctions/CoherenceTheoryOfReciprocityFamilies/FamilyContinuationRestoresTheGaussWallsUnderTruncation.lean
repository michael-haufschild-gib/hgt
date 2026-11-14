import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.IncompleteReciprocityRetainsPhasesWithSubcubicSaving
import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheWallIsThePriceOfCompletion
import GaloisForLFunctions.FamilyContinuationTheory.TheCubicProbeIsACoupledTowerReachingThreeFifths

/-!
# Family Continuation Restores the Gauss Walls Under Truncation

Row-by-row in `O = ℤ[ω]`, an incompletely completed reciprocity transform with sub-cubic cutoff
`Y₀ = X^η` (`1/6 < η < 1/3`) retains the `J = (1)` Möbius target and all unit-modulus local Gauss
root-number phases while achieving a uniform power saving below square-root cancellation on its
boundary reflection defect (`IncompleteReciprocityRetainsPhasesWithSubcubicSaving`). Passing to the
detector's row-family Poisson continuation at the signal residue `z = 1/6` alters the local prime
exponent by a `Q^2` sextic congruence amplification:

1. **Single-row convergence vs. `Q^2` row-Poisson amplification (`singleRow_vs_rowPoisson_amplification_dichotomy`):**
   At `l = 2` (`I = v^6`, `J = v^2`), the single-row prime weight `N(v)^{1 - 6σ}` is summable across
   all primes of `O` for every `σ > 1/2`. Summing over the row family modulo `v^6` and extracting
   the `z = 1/6` double residue multiplies by `N(v)^2`, producing the sextic resonance
   `R_v = κ_v^6 N(v)^{3 - 6s}`, whose prime-norm series diverges throughout `Re s ≤ 2/3`.
2. **Exact local series for every finite cube-exponent cutoff `l < L` (`L ≥ 1`):**
   At residue mode `j = 0`, every odd cube layer `l = 2r + 1` vanishes identically
   (`localTerm_odd_cube_eq_zero`), so truncating to `l < L` coincides pointwise with `l < 2M` for
   `M = (L + 1) / 2 ≥ 1`. Without assuming `‖R‖ < 1`, the local series restricted to `l < L` sums
   for `‖V‖ < 1` and `‖ρY‖ < 1` (`hasSum_localTerm_lt_cutoff`), and normalizes at the residue point
   `ρ = 1, Y = V = Q⁻¹, X = Q^{-s}` to `truncatedPrincipalLocalFactor ((L + 1) / 2) Q A ηp s`, which
   satisfies the exact telescoping identity (`truncatedPrincipalLocalFactor_eq_geom_mul_regular_add`)
   `truncatedPrincipalLocalFactor M Q A ηp s = (∑_{r < M} R^r) · regularLocalFactor Q A ηp s + (1 - Q⁻²)(Q⁻¹ R^M / (1 - D))`.
3. **Sharp all-depths continuation and zero-obstruction dichotomy (`L ∈ {1, 2}` vs. `L ≥ 3`):**
   - For `L ∈ {1, 2}` (`M = 1`), `l = 2` is omitted and `truncatedPrincipalCorrection 1 A η S`
     equals `principalCorrection 0 η S`, holomorphic and within `1/2` of `1` on `Re s > σ > 1/2`.
   - For every `L ≥ 3` (`M = (L + 1) / 2 ≥ 2`), there is an `M`-independent prime cutoff `N_cut`
     (`160 ≤ N_cut`) such that whenever `{v | N(v) ≤ N_cut} ⊆ S`,
     `truncatedFullPrincipalCorrection M 𝔪 η S` continues holomorphically to `Re s > 7/12`
     (`continuedTruncatedCorrection`), is nonvanishing on `Re s ≥ 2/3`, and for every `σ₀ < 2/3`,
     every holomorphic continuation `G` on `Re s > σ₀` agreeing with
     `truncatedFullPrincipalCorrection M 𝔪 η S` on `Re s ≥ 2` has the exact zero locus
     `G s = 0 ↔ continuedProbeCorrection 𝔪 η S s = 0` on `Re s > max σ₀ (41/72)` with
     `Re s ≥ 7/12`, hence infinitely many zeros with unbounded ordinates in `7/12 ≤ Re s < 2/3`
     whenever `σ₀ < 7/12` and no nonvanishing holomorphic continuation below `7/12`.
4. **Sub-cubic global defect lower bound (`η < 1/3`) and persistence of `7/8`, `2/3`, `3/5`:**
   For every global cutoff `N(J) < Z^η` with `η < 1/3` (including the entire `1/6 < η < 1/3`
   power-saving window), the `l = 2` squarefree shell `N(T)^6 ≤ Z` has `N(J) = N(T)^2 ≥ Z^η` and
   carries row-continued sixth-power Möbius norm at least `c · Z^{2/3}` (`c > 0`). Coupling the
   Grossencharacter tower contracts any base abscissa `σ_base > 3/5` (including `7/8` and `2/3`) via
   `b ↦ (3 + b) / 6` to `3/5`, leaving the uncoupled wall `2/3` and coupled wall `3/5` intact.
-/

noncomputable section

open Complex Filter Topology Set NumberField IsDedekindDomain
open scoped BigOperators Classical ComplexConjugate ContDiff

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory HeckeLFunctions MetaplecticMobiusDescent
open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### 1. Single-row convergence vs. `Q^2` row-Poisson congruence amplification -/

/-- **Single-row `l = 2` prime-series convergence vs. `Q^2` row-Poisson divergence:**
1. On every half-plane `σ > 1/2`, the single-row `l = 2` prime weight `N(v)^{1 - 6σ}` (and hence
   `N(v)^{-6σ}`) is absolutely summable over all primes `v` of `O = ℤ[ω]`.
2. At the signal double residue `z = 1/6`, summing over the row family amplifies `l = 2` by
   `N(v)^2` to `sexticResonance N(v) κ_v s (1/6)` of norm `N(v)^{3 - 6 Re s}`, which diverges for
   every `(𝔪, η)`, every finite prime set `S`, and every `s` with `Re s ≤ 2/3`. -/
theorem singleRow_vs_rowPoisson_amplification_dichotomy :
    (∀ σ : ℝ, 1 / 2 < σ →
      Summable fun v : HeightOneSpectrum O => (v.asIdeal.absNorm : ℝ) ^ (1 - 6 * σ)) ∧
    (∀ (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O)) (s : ℂ),
      s.re ≤ 2 / 3 →
      ¬ Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        ‖sexticResonance v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1) s ((1 / 6 : ℝ) : ℂ)‖) := by
  refine ⟨fun σ hσ => ?_, fun 𝔪 η S s hs => ?_⟩
  · have hexp : (1 : ℝ) < 6 * σ - 1 := by linarith
    refine (numberField_summable_finitePlace_absNorm_rpow (K := K) hexp).congr fun v => ?_
    show primeNorm v ^ (-(6 * σ - 1)) = (v.asIdeal.absNorm : ℝ) ^ (1 - 6 * σ)
    unfold primeNorm
    congr 1
    ring
  · refine not_summable_sexticResonance_of_re_le 𝔪 η S (x := s) (z := ((1 / 6 : ℝ) : ℂ)) ?_
    simp only [add_re, ofReal_re]
    linarith

/-! ### 2. Exact local row-Poisson series under every cube-exponent cutoff `l < L` (`L ≥ 1`) -/

section PrimeTruncation

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

include h2 hprim in
/-- **Odd cube exponents vanish identically at `j = 0`.** At residue mode `j = 0`, every term of the
local row-Poisson series with odd cube exponent `l = 2r + 1` vanishes, because the base layers
`(e, 1, k, i)` are supported on nonzero sextic residue modes `j ∈ {2, 3, 4}`. -/
theorem localTerm_odd_cube_eq_zero (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (e : Fin 2) (r k m : ℕ) :
    localTerm π ηp X Y V u 0 (e, 2 * r + 1, k, m) = 0 := by
  rw [show 2 * r + 1 = 1 + 2 * r by ring,
    localTerm_family π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) e 1 k (by omega) r m]
  split_ifs with hrm
  · suffices h0 : localTerm π ηp X Y V u 0 (e, 1, k, m - r) = 0 by rw [h0, mul_zero]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · rcases (show e = 0 ∨ e = 1 by fin_cases e <;> simp) with rfl | rfl <;> interval_cases k
      · rw [localTerm_C0 π hlam h2 hprim ηp X Y V hu 0 (m - r)]; simp
      · rw [localTerm_C1 π hlam h2 hprim ηp X Y V hu 0 (m - r)]; simp
      · rw [localTerm_D0 π hlam h2 hprim ηp X Y V hu 0 (m - r)]; simp
      · rw [localTerm_D1 π hlam h2 hprim ηp X Y V hu 0 (m - r)]; simp
    · exact localTerm_eq_zero_of_two_le π hlam h2 hprim ηp X Y V hu 0 e 1 k (m - r) (by omega) hk
  · rfl

include h2 hprim in
/-- For every cutoff `L ≥ 1`, truncating `localTerm` at `j = 0` to `l < L` coincides pointwise with
truncating to the even cutoff `l < 2 * ((L + 1) / 2)`. -/
theorem localTerm_lt_eq_lt_even (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    {L : ℕ} (hL : 1 ≤ L) (v : Fin 2 × ℕ × ℕ × ℕ) :
    (if v.2.1 < L then localTerm π ηp X Y V u 0 v else 0) =
      (if v.2.1 < 2 * ((L + 1) / 2) then localTerm π ηp X Y V u 0 v else 0) := by
  obtain ⟨e, l, k, m⟩ := v
  dsimp only
  by_cases hl : l < L
  · rw [if_pos hl, if_pos (by omega)]
  · rw [if_neg hl]
    by_cases hl2 : l < 2 * ((L + 1) / 2)
    · have hl_odd : l = 2 * (L / 2) + 1 := by omega
      rw [if_pos hl2, hl_odd, localTerm_odd_cube_eq_zero π hlam h2 hprim ηp X Y V hu]
    · rw [if_neg hl2]

include h2 hprim in
/-- **Exact sum of a single positive even cube layer `l = 2r` (`r ≥ 1`) without `‖R‖ < 1`.**
Assuming only `‖V‖ < 1` and `π ∤ u`, the layer `v.2.1 = 2r` at `j = 0` sums to
`R^r · ((1 - Q⁻¹)(1 - V)⁻¹ + ρY - ηp ρ⁻¹ X - ηp (Q - 1) X Y V (1 - V)⁻¹)`. -/
theorem hasSum_localTerm_even_layer (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (hV : ‖V‖ < 1) {r : ℕ} (hr : 1 ≤ r) :
    HasSum (fun v : Fin 2 × ℕ × ℕ × ℕ => if v.2.1 = 2 * r then localTerm π ηp X Y V u 0 v else 0)
      (primeR π ηp X V ^ r *
        ((1 - (primeQ π)⁻¹) * (1 - V)⁻¹ +
          complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y -
          ηp * (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))⁻¹ * X -
          ηp * (primeQ π - 1) * X * Y * V * (1 - V)⁻¹)) := by
  set ρ := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u)
  set Q := primeQ π
  set R := primeR π ηp X V
  let f₁ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v =>
    if v.1 = 0 ∧ v.2.1 = 2 * r ∧ v.2.2.1 = 0 ∧ r ≤ v.2.2.2 then
      R ^ r * (1 - Q⁻¹) * V ^ (v.2.2.2 - r) else 0
  let f₂ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v =>
    if v = (0, 2 * r, 1, r) then R ^ r * (ρ * Y) else 0
  let f₃ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v =>
    if v = (1, 2 * r, 0, r) then -(R ^ r * ηp * ρ⁻¹ * X) else 0
  let f₄ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v =>
    if v.1 = 1 ∧ v.2.1 = 2 * r ∧ v.2.2.1 = 1 ∧ r + 1 ≤ v.2.2.2 then
      -(R ^ r * ηp * (Q - 1) * X * Y * V ^ (v.2.2.2 - r)) else 0
  have hsplit : (fun v : Fin 2 × ℕ × ℕ × ℕ =>
      if v.2.1 = 2 * r then localTerm π ηp X Y V u 0 v else 0) =
      fun v => f₁ v + f₂ v + f₃ v + f₄ v := by
    funext ⟨e, l, k, m⟩
    simp only [f₁, f₂, f₃, f₄, Prod.mk.injEq]
    by_cases hl : l = 2 * r
    · subst hl
      rw [if_pos rfl]
      rcases Nat.lt_or_ge k 2 with hk | hk
      · rcases (show e = 0 ∨ e = 1 by fin_cases e <;> simp) with rfl | rfl <;> interval_cases k
        · -- `e = 0, k = 0`
          rw [show 2 * r = 2 + 2 * (r - 1) by omega,
            localTerm_family π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) 0 2 0
              (by norm_num) (r - 1) m,
            show 2 + 2 * (r - 1) = 2 * r by omega]
          rcases lt_trichotomy m (r - 1) with hlt | rfl | hgt
          · rw [if_neg (by omega)]
            simp [show ¬ (r ≤ m) by omega]
          · rw [if_pos le_rfl, Nat.sub_self,
              localTerm_A0 π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) 0]
            simp [show ¬ (r ≤ r - 1) by omega]
          · have hrm : r ≤ m := by omega
            have hsub0 : m - (r - 1) ≠ 0 := by omega
            rw [if_pos (by omega),
              localTerm_A0 π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) (m - (r - 1)),
              if_neg hsub0, show m - (r - 1) - 1 = m - r by omega]
            simp only [true_and, hrm, ite_true, show (0 : ℕ) = 1 ↔ False by decide, false_and,
              ite_false, show (0 : Fin 2) = 1 ↔ False by decide, add_zero]
            have hr_pow : R ^ (r - 1) * R = R ^ r := by
              rw [← pow_succ, show r - 1 + 1 = r by omega]
            dsimp only [R, Q]
            linear_combination (1 - Q⁻¹) * V ^ (m - r) * hr_pow
        · -- `e = 0, k = 1`
          rw [show 2 * r = 2 + 2 * (r - 1) by omega,
            localTerm_family π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) 0 2 1
              (by norm_num) (r - 1) m,
            show 2 + 2 * (r - 1) = 2 * r by omega]
          by_cases hmr : m = r
          · subst hmr
            rw [if_pos (by omega), show r - (r - 1) = 1 by omega,
              localTerm_A1 π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) 1,
              if_pos ⟨rfl, rfl⟩]
            simp only [show (1 : ℕ) = 0 ↔ False by decide, and_false, false_and, ite_false,
              and_self, ite_true, show (0 : Fin 2) = 1 ↔ False by decide, zero_add, add_zero]
            have hr_pow : R ^ (r - 1) * R = R ^ r := by
              rw [← pow_succ, show r - 1 + 1 = r by omega]
            dsimp only [R, ρ]
            linear_combination ρ * Y * hr_pow
          · by_cases hle : r - 1 ≤ m
            · rw [if_pos hle,
                localTerm_A1 π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) (m - (r - 1)),
                if_neg (by omega), mul_zero]
              simp [hmr]
            · rw [if_neg hle]
              simp [hmr]
        · -- `e = 1, k = 0`
          rw [show 2 * r = 0 + 2 * r by ring,
            localTerm_family π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) 1 0 0
              (by norm_num) r m,
            show 0 + 2 * r = 2 * r by ring]
          by_cases hmr : m = r
          · subst hmr
            rw [if_pos le_rfl, Nat.sub_self,
              localTerm_B0 π hlam h2 hprim ηp X Y V hu 0 0, if_pos ⟨rfl, rfl⟩]
            simp only [show (1 : Fin 2) = 0 ↔ False by decide, false_and, ite_false,
              and_self, ite_true, show (0 : ℕ) = 1 ↔ False by decide, and_false, zero_add, add_zero]
            dsimp only [R, ρ]
            ring
          · by_cases hle : r ≤ m
            · rw [if_pos hle, localTerm_B0 π hlam h2 hprim ηp X Y V hu 0 (m - r),
                if_neg (by omega), mul_zero]
              simp [hmr]
            · rw [if_neg hle]
              simp [hmr]
        · -- `e = 1, k = 1`
          rw [show 2 * r = 0 + 2 * r by ring,
            localTerm_family π hlam h2 hprim ηp X Y V hu (by norm_num : 0 < 6) 1 0 1
              (by norm_num) r m,
            show 0 + 2 * r = 2 * r by ring]
          rcases lt_trichotomy m r with hlt | rfl | hgt
          · rw [if_neg (by omega)]
            simp [show ¬ (r + 1 ≤ m) by omega]
          · rw [if_pos le_rfl, Nat.sub_self, localTerm_B1 π hlam h2 hprim ηp X Y V hu 0 0]
            simp [show ¬ (r + 1 ≤ r) by omega]
          · have hrm1 : r + 1 ≤ m := by omega
            rw [if_pos (by omega), localTerm_B1 π hlam h2 hprim ηp X Y V hu 0 (m - r),
              if_pos (Or.inl (by omega))]
            simp only [show (1 : Fin 2) = 0 ↔ False by decide, false_and, ite_false,
              show (1 : ℕ) = 0 ↔ False by decide, and_false, true_and, hrm1, ite_true, zero_add]
            dsimp only [R, Q]
            ring
      · rw [localTerm_eq_zero_of_two_le π hlam h2 hprim ηp X Y V hu 0 e (2 * r) k m (by omega) hk]
        simp [show k ≠ 0 by omega, show k ≠ 1 by omega]
    · rw [if_neg hl]
      simp [hl]
  rw [hsplit]
  have h₁ : HasSum f₁ (R ^ r * (1 - Q⁻¹) * (1 - V)⁻¹) := by
    have hinj : Function.Injective fun n : ℕ => ((0 : Fin 2), 2 * r, 0, r + n) :=
      fun a b h => by simpa using h
    refine (hinj.hasSum_iff (fun v hv => ?_)).mp ?_
    · simp only [f₁]
      rw [if_neg]
      rintro ⟨he, hl, hk, hm⟩
      exact hv ⟨v.2.2.2 - r, by ext <;> simp [he, hl, hk]; omega⟩
    · have hcomp : f₁ ∘ (fun n : ℕ => ((0 : Fin 2), 2 * r, 0, r + n)) =
          fun n => (R ^ r * (1 - Q⁻¹)) * V ^ n := by
        funext n
        simp [f₁]
      rw [hcomp]
      exact (hasSum_geometric_of_norm_lt_one hV).mul_left _
  have h₂ : HasSum f₂ (R ^ r * (ρ * Y)) := hasSum_ite_eq _ _
  have h₃ : HasSum f₃ (-(R ^ r * ηp * ρ⁻¹ * X)) := hasSum_ite_eq _ _
  have h₄ : HasSum f₄ (-(R ^ r * ηp * (Q - 1) * X * Y * V) * (1 - V)⁻¹) := by
    have hinj : Function.Injective fun n : ℕ => ((1 : Fin 2), 2 * r, 1, r + 1 + n) :=
      fun a b h => by simpa using h
    refine (hinj.hasSum_iff (fun v hv => ?_)).mp ?_
    · simp only [f₄]
      rw [if_neg]
      rintro ⟨he, hl, hk, hm⟩
      exact hv ⟨v.2.2.2 - (r + 1), by ext <;> simp [he, hl, hk]; omega⟩
    · have hcomp : f₄ ∘ (fun n : ℕ => ((1 : Fin 2), 2 * r, 1, r + 1 + n)) =
          fun n => -(R ^ r * ηp * (Q - 1) * X * Y * V) * V ^ n := by
        funext n
        simp only [f₄, Function.comp, true_and, le_add_iff_nonneg_right, zero_le, ite_true,
          show r + 1 + n - r = n + 1 by omega]
        rw [pow_succ']
        ring
      rw [hcomp]
      exact (hasSum_geometric_of_norm_lt_one hV).mul_left _
  have hval : R ^ r * ((1 - Q⁻¹) * (1 - V)⁻¹ + ρ * Y - ηp * ρ⁻¹ * X -
      ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹) =
      R ^ r * (1 - Q⁻¹) * (1 - V)⁻¹ + R ^ r * (ρ * Y) +
        -(R ^ r * ηp * ρ⁻¹ * X) + -(R ^ r * ηp * (Q - 1) * X * Y * V) * (1 - V)⁻¹ := by
    ring
  rw [hval]
  exact ((h₁.add h₂).add h₃).add h₄

include h2 hprim in
/-- **The truncated local series for every cutoff `L ≥ 1` (without `‖R‖ < 1`).** For `π ∤ u` and
`‖V‖, ‖ρY‖ < 1`, restricting `localTerm` at `j = 0` to `v.2.1 < L` replaces the geometric factor
`R(1 - R)⁻¹` in `rowLocalSum` by the finite polynomial `∑_{1 ≤ r < (L + 1) / 2} R^r`. -/
theorem hasSum_localTerm_lt_cutoff (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (hV : ‖V‖ < 1)
    (hW : ‖complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y‖ < 1)
    {L : ℕ} (hL : 1 ≤ L) :
    HasSum (fun v : Fin 2 × ℕ × ℕ × ℕ => if v.2.1 < L then localTerm π ηp X Y V u 0 v else 0)
      (rowLocalSum (primeQ π) 0 ηp X Y V
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u)) +
        (∑ r ∈ Finset.Ico 1 ((L + 1) / 2), primeR π ηp X V ^ r) *
          ((1 - (primeQ π)⁻¹) * (1 - V)⁻¹ +
            complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y -
            ηp * (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))⁻¹ * X -
            ηp * (primeQ π - 1) * X * Y * V * (1 - V)⁻¹)) := by
  have heven : ∀ d : ℕ,
      HasSum (fun v : Fin 2 × ℕ × ℕ × ℕ =>
        if v.2.1 < 2 * (d + 1) then localTerm π ηp X Y V u 0 v else 0)
        (rowLocalSum (primeQ π) 0 ηp X Y V
          (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u)) +
          (∑ r ∈ Finset.Ico 1 (d + 1), primeR π ηp X V ^ r) *
            ((1 - (primeQ π)⁻¹) * (1 - V)⁻¹ +
              complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y -
              ηp * (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))⁻¹ * X -
              ηp * (primeQ π - 1) * X * Y * V * (1 - V)⁻¹)) := by
    intro d
    induction d with
    | zero =>
      simp only [zero_add, mul_one, Finset.Ico_self, Finset.sum_empty, zero_mul, add_zero]
      refine (hasSum_localTerm_uncompleted π hlam h2 hprim ηp X Y V hu hV hW).congr_fun fun v => ?_
      have hiff : v.2.1 < 2 ↔ v.2.1 ≤ 1 := by omega
      by_cases hv : v.2.1 ≤ 1
      · rw [if_pos (hiff.mpr hv), if_pos hv]
      · rw [if_neg (mt hiff.mp hv), if_neg hv]
    | succ d ih =>
      have hlayer := hasSum_localTerm_even_layer π hlam h2 hprim ηp X Y V hu hV
        (r := d + 1) (by omega)
      have hsum := ih.add hlayer
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ d + 1)]
      refine (hsum.congr_fun fun v => ?_).trans_eq ?_
      · obtain ⟨e, l, k, m⟩ := v
        dsimp only
        by_cases hl : l < 2 * (d + 1)
        · rw [if_pos hl, if_neg (by omega), if_pos (by omega), add_zero]
        · rw [if_neg hl, zero_add]
          by_cases heq : l = 2 * (d + 1)
          · rw [if_pos heq, if_pos (by omega)]
          · rw [if_neg heq]
            by_cases hlt2 : l < 2 * (d + 2)
            · have hodd : l = 2 * (d + 1) + 1 := by omega
              rw [if_pos hlt2, hodd, localTerm_odd_cube_eq_zero π hlam h2 hprim ηp X Y V hu]
            · rw [if_neg hlt2]
      · ring
  have hM1 : 1 ≤ (L + 1) / 2 := by omega
  have hMd : (L + 1) / 2 - 1 + 1 = (L + 1) / 2 := by omega
  have h := heven ((L + 1) / 2 - 1)
  rw [hMd] at h
  exact h.congr_fun fun v => (localTerm_lt_eq_lt_even π hlam h2 hprim ηp X Y V hu hL v).symm

end PrimeTruncation

/-! ### 3. Residue-point normalization and exact telescoping decomposition -/

/-- **Truncated principal local factor** of depth `M = (L + 1) / 2 ≥ 1` at the signal residue
`ρ = 1, Y = V = Q⁻¹, X = Q^{-s}`. -/
def truncatedPrincipalLocalFactor (M : ℕ) (Q : ℝ) (A ηp s : ℂ) : ℂ :=
  (1 - ((Q : ℂ)⁻¹) ^ 2) *
    (1 + (Q : ℂ)⁻¹ * (ηp * (Q : ℂ) ^ (-s)) / (1 - ηp * (Q : ℂ) ^ (-s)) +
      (1 - (Q : ℂ)⁻¹) * ∑ r ∈ Finset.Ico 1 M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r)

/-- At `ρ = 1, Y = V = Q⁻¹, X = Q^{-s}`, multiplying the `l < L` local sum by the double-residue
prefactor `(1 - Q⁻¹)² / (1 - ηp Q^{-s})` yields `truncatedPrincipalLocalFactor ((L + 1) / 2)`. -/
theorem truncated_principal_factor_eq {Q : ℝ} (hQ : 1 < Q) (M : ℕ) (A ηp s : ℂ)
    (hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0) :
    (rowLocalSum (Q : ℂ) 0 ηp ((Q : ℂ) ^ (-s)) (Q : ℂ)⁻¹ (Q : ℂ)⁻¹ 1 +
      (∑ r ∈ Finset.Ico 1 M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r) *
        ((1 - (Q : ℂ)⁻¹) * (1 - (Q : ℂ)⁻¹)⁻¹ + 1 * (Q : ℂ)⁻¹ -
          ηp * (1 : ℂ)⁻¹ * (Q : ℂ) ^ (-s) -
          ηp * ((Q : ℂ) - 1) * (Q : ℂ) ^ (-s) * (Q : ℂ)⁻¹ * (Q : ℂ)⁻¹ *
            (1 - (Q : ℂ)⁻¹)⁻¹)) *
      ((1 - (Q : ℂ)⁻¹) * (1 - (Q : ℂ)⁻¹)) / (1 - ηp * (Q : ℂ) ^ (-s)) =
      truncatedPrincipalLocalFactor M Q A ηp s := by
  have hQ0 : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hQ1 : (Q : ℂ) - 1 ≠ 0 := by
    intro h
    have : ((Q - 1 : ℝ) : ℂ) = 0 := by push_cast; exact h
    linarith [ofReal_eq_zero.mp this]
  have hq : 1 - (Q : ℂ)⁻¹ ≠ 0 := by
    rw [show 1 - (Q : ℂ)⁻¹ = ((Q : ℂ) - 1) / Q by field_simp]
    exact div_ne_zero hQ1 hQ0
  rw [add_mul, add_div, uncompleted_principal_factor hQ ηp s hD]
  unfold principalLocalFactor truncatedPrincipalLocalFactor
  simp only [zero_mul, sub_zero, div_one]
  set S_geom := ∑ r ∈ Finset.Ico 1 M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r
  set D := ηp * (Q : ℂ) ^ (-s)
  have hD' : 1 - D ≠ 0 := hD
  field_simp [hQ0, hq, hD']
  ring

/-- At `M = 1` (`L ∈ {1, 2}`), `truncatedPrincipalLocalFactor` reduces to `principalLocalFactor`
with zero phase (`R = 0`). -/
theorem truncatedPrincipalLocalFactor_one (Q : ℝ) (A ηp s : ℂ) :
    truncatedPrincipalLocalFactor 1 Q A ηp s = principalLocalFactor Q 0 ηp s := by
  unfold truncatedPrincipalLocalFactor principalLocalFactor
  simp only [Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero, zero_mul, sub_zero, div_one]
  ring

/-- **Exact telescoping decomposition of `truncatedPrincipalLocalFactor` for all `M ≥ 1`.**
Factoring out the finite geometric polynomial `∑_{r < M} R^r` (`(1 - R^M)/(1 - R)`) leaves
`regularLocalFactor` plus the single remainder term `(1 - Q⁻²)(Q⁻¹ R^M / (1 - D))`. -/
theorem truncatedPrincipalLocalFactor_eq_geom_mul_regular_add {M : ℕ} (hM : 1 ≤ M)
    (Q : ℝ) (A ηp s : ℂ) (hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0) :
    truncatedPrincipalLocalFactor M Q A ηp s =
      (∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r) * regularLocalFactor Q A ηp s +
        (1 - ((Q : ℂ)⁻¹) ^ 2) *
          ((Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s)) ^ M / (1 - ηp * (Q : ℂ) ^ (-s))) := by
  have hd : ∀ d : ℕ,
      truncatedPrincipalLocalFactor (d + 1) Q A ηp s =
        (∑ r ∈ Finset.range (d + 1), (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r) *
          regularLocalFactor Q A ηp s +
        (1 - ((Q : ℂ)⁻¹) ^ 2) *
          ((Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s)) ^ (d + 1) /
            (1 - ηp * (Q : ℂ) ^ (-s))) := by
    intro d
    induction d with
    | zero =>
      unfold truncatedPrincipalLocalFactor regularLocalFactor
      simp only [zero_add, Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero,
        Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one]
      set D := ηp * (Q : ℂ) ^ (-s)
      have hD' : 1 - D ≠ 0 := hD
      field_simp [hD']
      ring
    | succ d ih =>
      have hlhs : truncatedPrincipalLocalFactor (d + 2) Q A ηp s =
          truncatedPrincipalLocalFactor (d + 1) Q A ηp s +
            (1 - ((Q : ℂ)⁻¹) ^ 2) * (1 - (Q : ℂ)⁻¹) *
              (A * (Q : ℂ) ^ (3 - 6 * s)) ^ (d + 1) := by
        unfold truncatedPrincipalLocalFactor
        rw [show d + 2 = (d + 1) + 1 from rfl, Finset.sum_Ico_succ_top (by omega : 1 ≤ d + 1)]
        ring
      rw [hlhs, ih, show d + 2 = (d + 1) + 1 from rfl, Finset.sum_range_succ]
      unfold regularLocalFactor
      set R := A * (Q : ℂ) ^ (3 - 6 * s)
      set D := ηp * (Q : ℂ) ^ (-s)
      have hD' : 1 - D ≠ 0 := hD
      rw [pow_succ R (d + 1)]
      field_simp [hD']
      ring
  have hMd : M - 1 + 1 = M := by omega
  simpa only [hMd] using hd (M - 1)

/-! ### 4. Sharp all-depths continuation and zero-obstruction dichotomy (`L ∈ {1, 2}` vs. `L ≥ 3`) -/

/-- The `S`-deleted Euler product of `truncatedPrincipalLocalFactor M`. -/
def truncatedPrincipalCorrection {L_nf : Type*} [Field L_nf] [NumberField L_nf] (M : ℕ)
    (A η : HeightOneSpectrum (𝓞 L_nf) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 L_nf))) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 L_nf) // v ∉ S},
    truncatedPrincipalLocalFactor M (primeNorm v.1) (A v.1) (η v.1) s

/-- **Uncompleted branch (`L ∈ {1, 2}`, i.e., `M = 1`):** omitting `l = 2` removes the Gauss wall
entirely; `truncatedPrincipalCorrection 1 A η S` is holomorphic and within `1/2` of `1` on every
half-plane `Re s > σ > 1/2` once small primes are placed in `S`. -/
theorem exists_truncatedPrincipalCorrection_one_cutoff {L_nf : Type*} [Field L_nf]
    [NumberField L_nf] {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 L_nf))),
      (∀ v : HeightOneSpectrum (𝓞 L_nf), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ A η : HeightOneSpectrum (𝓞 L_nf) → ℂ, (∀ v, ‖η v‖ ≤ 1) →
        DifferentiableOn ℂ (truncatedPrincipalCorrection 1 A η S) {s : ℂ | σ < s.re} ∧
          ∀ s : ℂ, σ < s.re → ‖truncatedPrincipalCorrection 1 A η S s - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_uncompletedCorrection_cutoff (K := L_nf) hσ
  refine ⟨N₀, hN₀, fun S hS A η hη => ?_⟩
  have heq : truncatedPrincipalCorrection 1 A η S = principalCorrection (fun _ => 0) η S := by
    funext s
    unfold truncatedPrincipalCorrection principalCorrection
    exact tprod_congr fun v => truncatedPrincipalLocalFactor_one _ _ _ _
  rw [heq]
  exact hcut S hS η hη

/-- Modified regular local factor remaining after dividing `truncatedPrincipalLocalFactor M` by
`∑_{r < M} R^r`. -/
def truncatedModifiedRegularFactor (M : ℕ) (Q : ℝ) (A ηp s : ℂ) : ℂ :=
  regularLocalFactor Q A ηp s +
    (1 - ((Q : ℂ)⁻¹) ^ 2) *
      ((Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s)) ^ M / (1 - ηp * (Q : ℂ) ^ (-s))) /
      (∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r)

/-- Exact local factorization `truncatedPrincipalLocalFactor M = (∑_{r < M} R^r) · truncatedModifiedRegularFactor M`. -/
theorem truncatedPrincipalLocalFactor_eq_geom_mul_modified {M : ℕ} (hM : 1 ≤ M)
    (Q : ℝ) (A ηp s : ℂ) (hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0)
    (hgeom : ∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r ≠ 0) :
    truncatedPrincipalLocalFactor M Q A ηp s =
      (∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r) *
        truncatedModifiedRegularFactor M Q A ηp s := by
  rw [truncatedPrincipalLocalFactor_eq_geom_mul_regular_add hM Q A ηp s hD]
  unfold truncatedModifiedRegularFactor
  rw [mul_add, mul_div_cancel₀ _ hgeom]

private theorem norm_R_le_quarter_of_sixty_four_le {Q : ℝ} (hQ : 64 ≤ Q) {A s : ℂ}
    (hA : ‖A‖ ≤ 1) (hs : 41 / 72 ≤ s.re) :
    ‖A * (Q : ℂ) ^ (3 - 6 * s)‖ ≤ 1 / 4 := by
  have hQ1 : 1 ≤ Q := by linarith
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans ?_
  calc ‖(Q : ℂ) ^ (3 - 6 * s)‖
      ≤ Q ^ (-(1 / 3 : ℝ)) := by
        refine norm_ofReal_cpow_le hQ1 ?_
        simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
        linarith
    _ ≤ (64 : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hQ (by norm_num)
    _ = 1 / 4 := by
        rw [show (64 : ℝ) = (4 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num

private theorem half_le_norm_geom_sum {M : ℕ} (hM : 1 ≤ M) {R : ℂ} (hR : ‖R‖ ≤ 1 / 4) :
    1 / 2 ≤ ‖∑ r ∈ Finset.range M, R ^ r‖ := by
  have hRM : ‖R ^ M‖ ≤ 1 / 4 := by
    rw [norm_pow]
    calc ‖R‖ ^ M ≤ (1 / 4 : ℝ) ^ M := pow_le_pow_left₀ (norm_nonneg R) hR M
      _ ≤ (1 / 4 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hM
      _ = 1 / 4 := pow_one _
  have h1RM : 3 / 4 ≤ ‖1 - R ^ M‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (R ^ M)
    rw [norm_one] at h
    linarith
  have h1R : ‖1 - R‖ ≤ 5 / 4 := by
    have h := norm_sub_le (1 : ℂ) R
    rw [norm_one] at h
    linarith
  have hprod : ‖(∑ r ∈ Finset.range M, R ^ r) * (1 - R)‖ = ‖1 - R ^ M‖ := by
    rw [geom_sum_mul_neg]
  rw [norm_mul] at hprod
  have hge : 3 / 5 ≤ ‖∑ r ∈ Finset.range M, R ^ r‖ := by
    nlinarith [norm_nonneg (∑ r ∈ Finset.range M, R ^ r)]
  linarith

/-- Uniform `M`-independent local defect bound on `Re s ≥ 41/72` (`< 7/12`) for every `M ≥ 2` and
every prime norm `Q ≥ 64`: `‖truncatedModifiedRegularFactor M Q A ηp s - 1‖ ≤ 17 Q^{-17/12}`. -/
theorem norm_truncatedModifiedRegularFactor_sub_one_le {M : ℕ} (hM : 2 ≤ M) {Q : ℝ}
    (hQ : 64 ≤ Q) {A ηp s : ℂ} (hA : ‖A‖ ≤ 1) (hη : ‖ηp‖ ≤ 1) (hs : 41 / 72 ≤ s.re) :
    ‖truncatedModifiedRegularFactor M Q A ηp s - 1‖ ≤ 17 * Q ^ (-(17 / 12 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hreg := norm_regularLocalFactor_sub_one_le hQ4 hA hη
    (σ := 41 / 72) (e := 17 / 12) (by norm_num) hs (by norm_num) (by norm_num) (by norm_num)
  set R := A * (Q : ℂ) ^ (3 - 6 * s)
  set D := ηp * (Q : ℂ) ^ (-s)
  set q : ℂ := (Q : ℂ)⁻¹
  have hR_qtr : ‖R‖ ≤ 1 / 4 := norm_R_le_quarter_of_sixty_four_le hQ hA hs
  have hgeom : 1 / 2 ≤ ‖∑ r ∈ Finset.range M, R ^ r‖ :=
    half_le_norm_geom_sum (by omega) hR_qtr
  have hD_half : ‖D‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
      ((norm_ofReal_cpow_le hQ1 (a := -(1 / 2 : ℝ)) (by rw [neg_re]; linarith)).trans
        (rpow_le_half_of_four_le hQ4 le_rfl))
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have h := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one] at h
    linarith
  have hq_norm : ‖q‖ = Q ^ (-1 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le, Real.rpow_neg_one]
  have h1q2 : ‖1 - q ^ 2‖ ≤ 2 := by
    have hq1 : ‖q‖ ≤ 1 := by
      rw [hq_norm]
      exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by norm_num)
    have h := norm_sub_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at h
    nlinarith [norm_nonneg q]
  have hR_pow : ‖R‖ ≤ Q ^ (-(5 / 12 : ℝ)) := by
    dsimp [R]
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans (norm_ofReal_cpow_le hQ1 ?_)
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hqRM : ‖q * R ^ M‖ ≤ Q ^ (-(17 / 12 : ℝ)) := by
    rw [norm_mul, norm_pow, hq_norm]
    have hRM : ‖R‖ ^ M ≤ Q ^ (-(10 / 12 : ℝ)) := by
      calc ‖R‖ ^ M ≤ (Q ^ (-(5 / 12 : ℝ))) ^ M := pow_le_pow_left₀ (norm_nonneg R) hR_pow M
        _ = (Q ^ (-(5 / 12 : ℝ))) ^ (M : ℝ) := (Real.rpow_natCast _ M).symm
        _ = Q ^ (-(5 / 12 : ℝ) * (M : ℝ)) := (Real.rpow_mul hQ0.le _ _).symm
        _ ≤ Q ^ (-(10 / 12 : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
            have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
            linarith
    calc Q ^ (-1 : ℝ) * ‖R‖ ^ M
        ≤ Q ^ (-1 : ℝ) * Q ^ (-(10 / 12 : ℝ)) := mul_le_mul_of_nonneg_left hRM (by positivity)
      _ = Q ^ ((-1 : ℝ) + -(10 / 12 : ℝ)) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ Q ^ (-(17 / 12 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hrem : ‖(1 - q ^ 2) * (q * R ^ M / (1 - D)) / (∑ r ∈ Finset.range M, R ^ r)‖ ≤
      8 * Q ^ (-(17 / 12 : ℝ)) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    rw [norm_mul, norm_div]
    have hd1 : ‖q * R ^ M‖ / ‖1 - D‖ ≤ 2 * Q ^ (-(17 / 12 : ℝ)) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.rpow_nonneg hQ0.le (-(17 / 12 : ℝ))]
    calc ‖1 - q ^ 2‖ * (‖q * R ^ M‖ / ‖1 - D‖)
        ≤ 2 * (2 * Q ^ (-(17 / 12 : ℝ))) :=
          mul_le_mul h1q2 hd1 (by positivity) (by norm_num)
      _ = 8 * Q ^ (-(17 / 12 : ℝ)) * (1 / 2) := by ring
      _ ≤ 8 * Q ^ (-(17 / 12 : ℝ)) * ‖∑ r ∈ Finset.range M, R ^ r‖ :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hsplit : truncatedModifiedRegularFactor M Q A ηp s - 1 =
      (regularLocalFactor Q A ηp s - 1) +
        (1 - q ^ 2) * (q * R ^ M / (1 - D)) / (∑ r ∈ Finset.range M, R ^ r) := by
    unfold truncatedModifiedRegularFactor
    ring
  rw [hsplit]
  calc ‖(regularLocalFactor Q A ηp s - 1) +
        (1 - q ^ 2) * (q * R ^ M / (1 - D)) / (∑ r ∈ Finset.range M, R ^ r)‖
      ≤ ‖regularLocalFactor Q A ηp s - 1‖ +
          ‖(1 - q ^ 2) * (q * R ^ M / (1 - D)) / (∑ r ∈ Finset.range M, R ^ r)‖ :=
        norm_add_le _ _
    _ ≤ 9 * Q ^ (-(17 / 12 : ℝ)) + 8 * Q ^ (-(17 / 12 : ℝ)) := add_le_add hreg hrem
    _ = 17 * Q ^ (-(17 / 12 : ℝ)) := by ring

theorem differentiableAt_truncatedModifiedRegularFactor {M : ℕ} (hM : 1 ≤ M) {Q : ℝ}
    (hQ : 64 ≤ Q) {A ηp s : ℂ} (hA : ‖A‖ ≤ 1) (hη : ‖ηp‖ ≤ 1) (hs : 41 / 72 ≤ s.re) :
    DifferentiableAt ℂ (truncatedModifiedRegularFactor M Q A ηp) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQ' : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ0.ne'
  have hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0 :=
    regular_denominator_ne_zero hQ4 hη (by linarith)
  have hgeom_ge : 1 / 2 ≤ ‖∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r‖ :=
    half_le_norm_geom_sum hM (norm_R_le_quarter_of_sixty_four_le hQ hA hs)
  have hgeom_ne : ∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * s)) ^ r ≠ 0 :=
    norm_pos_iff.mp (by linarith)
  have hR_diff : DifferentiableAt ℂ (fun z : ℂ => A * (Q : ℂ) ^ (3 - 6 * z)) s :=
    (((differentiableAt_const 3).sub
      ((differentiableAt_const 6).mul differentiableAt_id)).const_cpow (Or.inl hQ')).const_mul A
  have hD_diff : DifferentiableAt ℂ (fun z : ℂ => 1 - ηp * (Q : ℂ) ^ (-z)) s :=
    (differentiableAt_const 1).sub
      ((differentiableAt_id.neg.const_cpow (Or.inl hQ')).const_mul ηp)
  have hsum_diff : DifferentiableAt ℂ
      (fun z : ℂ => ∑ r ∈ Finset.range M, (A * (Q : ℂ) ^ (3 - 6 * z)) ^ r) s :=
    DifferentiableAt.sum fun r _ => hR_diff.pow r
  unfold truncatedModifiedRegularFactor
  exact (differentiableAt_regularLocalFactor hQ0 A ηp hD).add
    ((((differentiableAt_const _).mul (((hR_diff.pow M).const_mul _).div hD_diff hD))).div
      hsum_diff hgeom_ne)

/-- The `S`-deleted Euler product of `truncatedModifiedRegularFactor M`. -/
def truncatedModifiedRegularCorrection (M : ℕ) (A η : HeightOneSpectrum O → ℂ)
    (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S},
    truncatedModifiedRegularFactor M (primeNorm v.1) (A v.1) (η v.1) s

/-- **Uniform `M`-independent prime cutoff for `truncatedModifiedRegularCorrection` on
`Re s > 41/72`.** One fixed norm `N_cut ≥ 160` works simultaneously for all depths `M ≥ 2`, all
finite sets `S` containing `{v | N(v) ≤ N_cut}`, and all coefficients `‖A_v‖, ‖η_v‖ ≤ 1`. -/
theorem exists_truncatedModifiedRegularCorrection_cutoff :
    ∃ N_cut : ℕ, 160 ≤ N_cut ∧
      ∀ {M : ℕ}, 2 ≤ M → ∀ (S : Finset (HeightOneSpectrum O)),
        (∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ N_cut → v ∈ S) →
        ∀ A η : HeightOneSpectrum O → ℂ, (∀ v, ‖A v‖ ≤ 1) → (∀ v, ‖η v‖ ≤ 1) →
          DifferentiableOn ℂ (truncatedModifiedRegularCorrection M A η S)
            {s : ℂ | 41 / 72 < s.re} ∧
          (∀ s : ℂ, 41 / 72 < s.re →
            ‖truncatedModifiedRegularCorrection M A η S s - 1‖ ≤ 1 / 2) ∧
          (∀ s : ℂ, 41 / 72 < s.re →
            Multipliable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
              truncatedModifiedRegularFactor M (primeNorm v.1) (A v.1) (η v.1) s) := by
  obtain ⟨N₀, _, hcut⟩ := exists_cutoff_product (K := K)
    (by norm_num : (1 : ℝ) < 17 / 12) (by norm_num : (0 : ℝ) ≤ 17)
  set N_cut : ℕ := max 160 (max 64 N₀)
  refine ⟨N_cut, le_max_left _ _, fun {M} hM S hS A η hA hη => ?_⟩
  have hS_N₀ : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ N₀ → v ∈ S :=
    fun v hv => hS v (hv.trans ((le_max_right 64 N₀).trans (le_max_right 160 _)))
  have hbig64 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, 64 ≤ primeNorm v.1 := by
    intro v
    have hv : 64 < v.1.asIdeal.absNorm := lt_of_not_ge fun h =>
      v.2 (hS v.1 (h.trans ((le_max_left 64 N₀).trans (le_max_right 160 _))))
    unfold primeNorm
    exact_mod_cast hv.le
  set U : Set ℂ := {s : ℂ | 41 / 72 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  let f : HeightOneSpectrum O → ℂ → ℂ := fun v s =>
    if 64 ≤ primeNorm v then truncatedModifiedRegularFactor M (primeNorm v) (A v) (η v) s else 1
  obtain ⟨hdiff_f, hclose_f⟩ := hcut S hS_N₀ U hU f
    (fun v _ => by
      dsimp only [f]
      by_cases hv64 : 64 ≤ primeNorm v
      · simp only [if_pos hv64]
        exact fun s hs => (differentiableAt_truncatedModifiedRegularFactor (by omega) hv64
          (hA v) (hη v) (le_of_lt hs)).differentiableWithinAt
      · simp only [if_neg hv64]
        exact differentiableOn_const 1)
    (fun v _ s hs => by
      dsimp only [f]
      by_cases hv64 : 64 ≤ primeNorm v
      · rw [if_pos hv64]
        exact norm_truncatedModifiedRegularFactor_sub_one_le hM hv64 (hA v) (hη v) (le_of_lt hs)
      · rw [if_neg hv64, sub_self, norm_zero]
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [two_le_primeNorm v]) _))
  have heq : (fun s => ∏' v : {v : HeightOneSpectrum O // v ∉ S}, f v.1 s) =
      truncatedModifiedRegularCorrection M A η S := by
    funext s
    unfold truncatedModifiedRegularCorrection
    exact tprod_congr fun v => if_pos (hbig64 v)
  rw [heq] at hdiff_f hclose_f
  refine ⟨hdiff_f, hclose_f, fun s hs => ?_⟩
  have hsum : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      truncatedModifiedRegularFactor M (primeNorm v.1) (A v.1) (η v.1) s - 1 := by
    have hmaj : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        17 * primeNorm v.1 ^ (-(17 / 12 : ℝ)) :=
      ((numberField_summable_finitePlace_absNorm_rpow (K := K)
        (by norm_num : (1 : ℝ) < 17 / 12)).mul_left 17).comp_injective Subtype.val_injective
    exact (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) fun v =>
      norm_truncatedModifiedRegularFactor_sub_one_le hM (hbig64 v) (hA v.1) (hη v.1)
        (le_of_lt hs)).of_norm
  exact (Complex.multipliable_one_add_of_summable hsum).congr fun _ => by ring

private theorem cpow_pow_nat {x : ℂ} (hx : x ≠ 0) (z : ℂ) (M : ℕ) :
    (x ^ z) ^ M = x ^ ((M : ℂ) * z) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hexp : ((M + 1 : ℕ) : ℂ) * z = (M : ℂ) * z + z := by push_cast; ring
    rw [pow_succ, ih, ← Complex.cpow_add _ _ hx, hexp]

/-- The full truncated principal correction `truncatedPrincipalCorrection M · deletedEulerFactors`
for the Eisenstein probe with local phases `κ_v^6`. -/
def truncatedFullPrincipalCorrection (M : ℕ) (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  truncatedPrincipalCorrection M (fun v => primeKappaAt 𝔪 η v ^ 6)
    (fun v => heckeValue 𝔪 η v.asIdeal) S s *
    deletedEulerFactors 𝔪 η S s

/-- **Exact Euler-product functional identity on `Re s > 2/3` (`M ≥ 2`).** Multiplying
`truncatedFullPrincipalCorrection M 𝔪 η S s` by `L(6Ms - 3M, ψ₆^M χ_{𝔣(η^{6M})})` and its finite
deleted/residual factors recovers `continuedProbeCorrection 𝔪 η S s · truncatedModifiedRegularCorrection M`. -/
theorem truncatedFullPrincipalCorrection_mul_grossen_eq {M : ℕ} (hM : 2 ≤ M)
    (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS_lam : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S)
    (hS_64 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, 64 ≤ primeNorm v.1)
    {s : ℂ} (hs : 2 / 3 < s.re) :
    truncatedFullPrincipalCorrection M 𝔪 η S s *
      (grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
        grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
        residualCorrection (fun v => primeKappaAt 𝔪 η v ^ 6)
          (fun v => heckeValue 𝔪 η v.asIdeal) S s) =
      continuedProbeCorrection 𝔪 η S s *
        truncatedModifiedRegularCorrection M (fun v => primeKappaAt 𝔪 η v ^ 6)
          (fun v => heckeValue 𝔪 η v.asIdeal) S s := by
  set A : HeightOneSpectrum O → ℂ := fun v => primeKappaAt 𝔪 η v ^ 6
  set ηv : HeightOneSpectrum O → ℂ := fun v => heckeValue 𝔪 η v.asIdeal
  set wM : ℂ := 6 * (M : ℂ) * s - 3 * (M : ℂ)
  have hA : ∀ v, ‖A v‖ ≤ 1 := fun v => by
    dsimp [A]; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  have hη : ∀ v, ‖ηv v‖ ≤ 1 := fun v => norm_heckeValue_le_one 𝔪 η _
  have hw1 : 1 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  have hwM1 : 1 < wM.re := by
    have hre : wM.re = (M : ℝ) * (6 * s.re - 3) := by
      dsimp [wM]
      have h1 : (6 * (M : ℂ) * s - 3 * (M : ℂ)) = ((M : ℝ) : ℂ) * (6 * s - 3) := by
        push_cast; ring
      rw [h1, Complex.re_ofReal_mul]
      simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    rw [hre]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  -- Multipliability of `∑_{r < M} R_v^r` on `Re s > 2/3`
  have hmul_geom : Multipliable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      ∑ r ∈ Finset.range M, (A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)) ^ r := by
    have hmaj : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        2 * primeNorm v.1 ^ (-(6 * s.re - 3)) :=
      ((numberField_summable_finitePlace_absNorm_rpow (K := K) hw1).mul_left 2).comp_injective
        Subtype.val_injective
    have hsum : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        (∑ r ∈ Finset.range M, (A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)) ^ r) - 1 := by
      refine (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) fun v => ?_).of_norm
      set Rv := A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)
      have hv1 : 1 ≤ primeNorm v.1 := by linarith [two_le_primeNorm v.1]
      have hRv : ‖Rv‖ ≤ primeNorm v.1 ^ (-(6 * s.re - 3)) := by
        dsimp [Rv]; rw [norm_mul]
        refine (mul_le_of_le_one_left (norm_nonneg _) (hA v.1)).trans (norm_ofReal_cpow_le hv1 ?_)
        simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
      have hRv_qtr : ‖Rv‖ ≤ 1 / 4 :=
        norm_R_le_quarter_of_sixty_four_le (hS_64 v) (hA v.1) (by linarith)
      have h1Rv : 1 / 2 ≤ ‖1 - Rv‖ := by
        have h := norm_sub_norm_le (1 : ℂ) Rv; rw [norm_one] at h; linarith
      have hne : 1 - Rv ≠ 0 := norm_pos_iff.mp (by linarith)
      have hident : (∑ r ∈ Finset.range M, Rv ^ r) - 1 = Rv * (1 - Rv ^ (M - 1)) / (1 - Rv) := by
        rw [eq_div_iff hne]
        have hg := geom_sum_mul_neg Rv M
        have hpow : Rv * Rv ^ (M - 1) = Rv ^ M := by
          rw [← pow_succ', show M - 1 + 1 = M by omega]
        linear_combination hg - Rv * hpow
      have hnum : ‖1 - Rv ^ (M - 1)‖ ≤ 5 / 4 := by
        have hp : ‖Rv ^ (M - 1)‖ ≤ 1 / 4 := by
          rw [norm_pow]
          calc ‖Rv‖ ^ (M - 1) ≤ (1 / 4 : ℝ) ^ (M - 1) :=
                pow_le_pow_left₀ (norm_nonneg Rv) hRv_qtr (M - 1)
            _ ≤ (1 / 4 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = 1 / 4 := pow_one _
        have h := norm_sub_le (1 : ℂ) (Rv ^ (M - 1)); rw [norm_one] at h; linarith
      rw [hident, norm_div, norm_mul, div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg Rv]
    exact (Complex.multipliable_one_add_of_summable hsum).congr fun _ => by ring
  -- Multipliability of `truncatedModifiedRegularFactor M` on `Re s > 2/3`
  have hmul_mod : Multipliable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      truncatedModifiedRegularFactor M (primeNorm v.1) (A v.1) (ηv v.1) s := by
    have hmaj : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        17 * primeNorm v.1 ^ (-(17 / 12 : ℝ)) :=
      ((numberField_summable_finitePlace_absNorm_rpow (K := K)
        (by norm_num : (1 : ℝ) < 17 / 12)).mul_left 17).comp_injective Subtype.val_injective
    have hsum : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        truncatedModifiedRegularFactor M (primeNorm v.1) (A v.1) (ηv v.1) s - 1 :=
      (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) fun v =>
        norm_truncatedModifiedRegularFactor_sub_one_le hM (hS_64 v) (hA v.1) (hη v.1)
          (by linarith)).of_norm
    exact (Complex.multipliable_one_add_of_summable hsum).congr fun _ => by ring
  -- Factor `truncatedPrincipalCorrection M = (∏' geom) * truncatedModifiedRegularCorrection M`
  have hsplit_trunc : truncatedPrincipalCorrection M A ηv S s =
      (∏' v : {v : HeightOneSpectrum O // v ∉ S},
        ∑ r ∈ Finset.range M, (A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)) ^ r) *
      truncatedModifiedRegularCorrection M A ηv S s := by
    unfold truncatedPrincipalCorrection truncatedModifiedRegularCorrection
    rw [← hmul_geom.tprod_mul hmul_mod]
    refine tprod_congr fun v => ?_
    have hv4 : 4 ≤ primeNorm v.1 := by linarith [hS_64 v]
    have hD : 1 - ηv v.1 * (primeNorm v.1 : ℂ) ^ (-s) ≠ 0 :=
      regular_denominator_ne_zero hv4 (hη v.1) (by linarith)
    have hgeom_ge : 1 / 2 ≤
        ‖∑ r ∈ Finset.range M, (A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)) ^ r‖ :=
      half_le_norm_geom_sum (by omega)
        (norm_R_le_quarter_of_sixty_four_le (hS_64 v) (hA v.1) (by linarith))
    exact truncatedPrincipalLocalFactor_eq_geom_mul_modified (by omega) _ _ _ _ hD
      (norm_pos_iff.mp (by linarith))
  -- Multipliability of the `M`-th Grossencharacter Euler factors over `v ∉ S`
  have hmul_gM : Multipliable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      (1 - idealPsiSix v.1.asIdeal ^ M * heckeValue 𝔪 (η ^ (6 * M)) v.1.asIdeal *
        (primeNorm v.1 : ℂ) ^ (-wM))⁻¹ := by
    have hmaj : Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        primeNorm v.1 ^ (-wM.re) :=
      (numberField_summable_finitePlace_absNorm_rpow (K := K) hwM1).subtype _
    have hbd : ∀ v : {v : HeightOneSpectrum O // v ∉ S},
        ‖idealPsiSix v.1.asIdeal ^ M * heckeValue 𝔪 (η ^ (6 * M)) v.1.asIdeal *
          (primeNorm v.1 : ℂ) ^ (-wM)‖ ≤ primeNorm v.1 ^ (-wM.re) := by
      intro v
      have hv1 : 1 ≤ primeNorm v.1 := by linarith [two_le_primeNorm v.1]
      have hc : ‖idealPsiSix v.1.asIdeal ^ M * heckeValue 𝔪 (η ^ (6 * M)) v.1.asIdeal‖ ≤ 1 := by
        rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
          (norm_nonneg _) (norm_heckeValue_le_one 𝔪 (η ^ (6 * M)) _)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans
        (norm_ofReal_cpow_le hv1 (by rw [neg_re]))
    refine multipliable_one_sub_inv (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hbd) fun v =>
      (hbd v).trans ?_
    have hv2 := two_le_primeNorm v.1
    calc primeNorm v.1 ^ (-wM.re) ≤ primeNorm v.1 ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (primeNorm v.1)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  -- Multiply `(∏' geom)` by `grossenEulerProductModS 𝔪 (η^(6M)) M S wM` to get `grossenEulerProductModS 𝔪 (η^6) 1 S (6s-3)`
  have hprod_id :
      (∏' v : {v : HeightOneSpectrum O // v ∉ S},
        ∑ r ∈ Finset.range M, (A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)) ^ r) *
      grossenEulerProductModS 𝔪 (η ^ (6 * M)) M S wM =
      grossenEulerProductModS 𝔪 (η ^ 6) 1 S (6 * s - 3) := by
    unfold grossenEulerProductModS
    rw [← hmul_geom.tprod_mul hmul_gM]
    refine tprod_congr fun v => ?_
    have hlam : lambda ∉ v.1.asIdeal := fun h => v.2 (hS_lam v.1 h)
    have hQ_ne : (primeNorm v.1 : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (by linarith [two_le_primeNorm v.1])
    set Rv := A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)
    have hRv_eq : Rv = idealPsiSix v.1.asIdeal * heckeValue 𝔪 (η ^ 6) v.1.asIdeal *
        (primeNorm v.1 : ℂ) ^ (-(6 * s - 3)) := by
      dsimp [Rv, A]
      rw [primeKappaAt_pow_six 𝔪 η hlam, pow_one, show (3 - 6 * s : ℂ) = -(6 * s - 3) by ring]
    have hRvM_eq : Rv ^ M = idealPsiSix v.1.asIdeal ^ M * heckeValue 𝔪 (η ^ (6 * M)) v.1.asIdeal *
        (primeNorm v.1 : ℂ) ^ (-wM) := by
      dsimp [Rv, A]
      rw [mul_pow, primeKappaAt_pow_six 𝔪 η hlam, mul_pow,
        ← heckeValue_pow_ne_zero 𝔪 (η ^ 6) (by omega : M ≠ 0), ← pow_mul,
        cpow_pow_nat hQ_ne (3 - 6 * s) M]
      have hexp : (M : ℂ) * (3 - 6 * s) = -wM := by dsimp [wM]; ring
      rw [hexp]
    have hRv_qtr : ‖Rv‖ ≤ 1 / 4 :=
      norm_R_le_quarter_of_sixty_four_le (hS_64 v) (hA v.1) (by linarith)
    have h1Rv : 1 - Rv ≠ 0 := by
      have h := norm_sub_norm_le (1 : ℂ) Rv; rw [norm_one] at h
      exact norm_pos_iff.mp (by linarith)
    have h1RvM : 1 - Rv ^ M ≠ 0 := by
      have hM_le : ‖Rv ^ M‖ ≤ 1 / 4 := by
        rw [norm_pow]
        calc ‖Rv‖ ^ M ≤ (1 / 4 : ℝ) ^ M := pow_le_pow_left₀ (norm_nonneg Rv) hRv_qtr M
          _ ≤ (1 / 4 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 4 := pow_one _
      have h := norm_sub_norm_le (1 : ℂ) (Rv ^ M); rw [norm_one] at h
      exact norm_pos_iff.mp (by linarith)
    rw [← hRvM_eq, ← hRv_eq, pow_one]
    have hg := geom_sum_mul_neg Rv M
    field_simp [h1Rv, h1RvM]
    linear_combination hg
  have hgM_split := grossenEulerProductModS_eq_mul_deletedFactors 𝔪 (η ^ (6 * M))
    (by omega : 1 ≤ M) S hwM1
  have hg1_split := grossenEulerProductModS_eq_mul_deletedFactors 𝔪 (η ^ 6) le_rfl S hw1
  unfold truncatedFullPrincipalCorrection continuedProbeCorrection fullResidualCorrection
  change (truncatedPrincipalCorrection M A ηv S s * deletedEulerFactors 𝔪 η S s) *
    (grossenLFunction 𝔪 (η ^ (6 * M)) M wM * grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S wM *
      residualCorrection A ηv S s) =
    (grossenLFunction 𝔪 (η ^ 6) 1 (6 * s - 3) * grossenDeletedFactors 𝔪 (η ^ 6) 1 S (6 * s - 3) *
      (residualCorrection A ηv S s * deletedEulerFactors 𝔪 η S s)) *
      truncatedModifiedRegularCorrection M A ηv S s
  rw [hsplit_trunc, ← hgM_split, ← hg1_split]
  linear_combination (deletedEulerFactors 𝔪 η S s * residualCorrection A ηv S s *
    truncatedModifiedRegularCorrection M A ηv S s) * hprod_id

/-- **Explicit holomorphic continuation of `truncatedFullPrincipalCorrection M 𝔪 η S` (`M ≥ 2`) to
`Re s > 7/12`.** On `Re s ≥ 7/12`, `Re(6Ms - 3M) ≥ M / 2 ≥ 1`, so `grossenLFunction 𝔪 (η^{6M}) M`
is unconditionally nonvanishing and divides cleanly into `continuedProbeCorrection 𝔪 η S`. -/
def continuedTruncatedCorrection (M : ℕ) (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  (continuedProbeCorrection 𝔪 η S s *
    truncatedModifiedRegularCorrection M (fun v => primeKappaAt 𝔪 η v ^ 6)
      (fun v => heckeValue 𝔪 η v.asIdeal) S s) /
  (grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
    grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
    residualCorrection (fun v => primeKappaAt 𝔪 η v ^ 6)
      (fun v => heckeValue 𝔪 η v.asIdeal) S s)

private theorem truncated_denominator_ne_zero_of_seven_twelfths_le {M : ℕ} (hM : 2 ≤ M)
    (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    {s : ℂ} (hs : 7 / 12 ≤ s.re) :
    grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
      grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
      residualCorrection (fun v => primeKappaAt 𝔪 η v ^ 6)
        (fun v => heckeValue 𝔪 η v.asIdeal) S s ≠ 0 := by
  have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  have hη : ∀ v, ‖heckeValue 𝔪 η v.asIdeal‖ ≤ 1 := fun _ => norm_heckeValue_le_one 𝔪 η _
  have hwM_re : 1 ≤ (6 * (M : ℂ) * s - 3 * (M : ℂ)).re := by
    have h1 : (6 * (M : ℂ) * s - 3 * (M : ℂ)) = ((M : ℝ) : ℂ) * (6 * s - 3) := by
      push_cast; ring
    rw [h1, Complex.re_ofReal_mul]
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  exact mul_ne_zero
    (mul_ne_zero (grossenLFunction_ne_zero_of_one_le_re 𝔪 (η ^ (6 * M)) (by omega) hwM_re)
      (grossenDeletedFactors_ne_zero 𝔪 (η ^ (6 * M)) M S (by linarith)))
    (residualCorrection_ne_zero _ _ hA hη S (by linarith))

/-- **Holomorphy and exact zero-locus preservation for `continuedTruncatedCorrection M` (`M ≥ 2`) on
`Re s > 7/12`.** Whenever `S` contains `{v | N(v) ≤ N_cut}`, `continuedTruncatedCorrection M 𝔪 η S`
is holomorphic on `Re s > 7/12`, agrees with `truncatedFullPrincipalCorrection M 𝔪 η S` on
`Re s > 2/3`, is nonvanishing on `Re s ≥ 2/3`, and vanishes at `s` (`Re s > 7/12`) if and only if
`continuedProbeCorrection 𝔪 η S s = 0`. -/
theorem exists_continuedTruncatedCorrection_properties :
    ∃ N_cut : ℕ, 160 ≤ N_cut ∧
      ∀ {M : ℕ}, 2 ≤ M → ∀ (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
        (S : Finset (HeightOneSpectrum O)),
        (∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ N_cut → v ∈ S) →
        DifferentiableOn ℂ (continuedTruncatedCorrection M 𝔪 η S) {s : ℂ | 7 / 12 < s.re} ∧
        (∀ s : ℂ, 2 / 3 < s.re →
          continuedTruncatedCorrection M 𝔪 η S s =
            truncatedFullPrincipalCorrection M 𝔪 η S s) ∧
        (∀ s : ℂ, 2 / 3 ≤ s.re → continuedTruncatedCorrection M 𝔪 η S s ≠ 0) ∧
        (∀ s : ℂ, 7 / 12 < s.re →
          (continuedTruncatedCorrection M 𝔪 η S s = 0 ↔
            continuedProbeCorrection 𝔪 η S s = 0)) := by
  obtain ⟨N_cut, h160, hmod_cut⟩ := exists_truncatedModifiedRegularCorrection_cutoff
  refine ⟨N_cut, h160, fun {M} hM 𝔪 η S hS => ?_⟩
  have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  have hη : ∀ v, ‖heckeValue 𝔪 η v.asIdeal‖ ≤ 1 := fun _ => norm_heckeValue_le_one 𝔪 η _
  obtain ⟨hmod_diff, hmod_close, _⟩ := hmod_cut hM S hS _ _ hA hη
  have hmod_ne : ∀ s : ℂ, 41 / 72 < s.re →
      truncatedModifiedRegularCorrection M (fun v => primeKappaAt 𝔪 η v ^ 6)
        (fun v => heckeValue 𝔪 η v.asIdeal) S s ≠ 0 := by
    intro s hs h0
    have hc := hmod_close s hs
    rw [h0, zero_sub, norm_neg, norm_one] at hc
    linarith
  have hsub12 : {s : ℂ | 7 / 12 < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    have hs' : 7 / 12 < s.re := hs; show 1 / 2 < s.re; linarith
  have hsub41 : {s : ℂ | 7 / 12 < s.re} ⊆ {s : ℂ | 41 / 72 < s.re} := fun s hs => by
    have hs' : 7 / 12 < s.re := hs; show 41 / 72 < s.re; linarith
  have haff : Differentiable ℂ (fun s : ℂ => 6 * (M : ℂ) * s - 3 * (M : ℂ)) :=
    ((differentiable_id.const_mul (6 * (M : ℂ))).sub (differentiable_const (3 * (M : ℂ))))
  have hmap : MapsTo (fun s : ℂ => 6 * (M : ℂ) * s - 3 * (M : ℂ)) {s : ℂ | 7 / 12 < s.re}
      {w : ℂ | -(3 * (M : ℝ)) < w.re} := by
    intro s hs
    have hs' : 7 / 12 < s.re := hs
    have h1 : (6 * (M : ℂ) * s - 3 * (M : ℂ)) = ((M : ℝ) : ℂ) * (6 * s - 3) := by
      push_cast; ring
    show -(3 * (M : ℝ)) < (6 * (M : ℂ) * s - 3 * (M : ℂ)).re
    rw [h1, Complex.re_ofReal_mul]
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hLM_diff : DifferentiableOn ℂ
      (fun s : ℂ => grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ)))
      {s : ℂ | 7 / 12 < s.re} :=
    (differentiableOn_grossenLFunction 𝔪 (η ^ (6 * M)) (by omega)).comp haff.differentiableOn hmap
  have hdelM_diff : DifferentiableOn ℂ
      (fun s : ℂ => grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S (6 * (M : ℂ) * s - 3 * (M : ℂ)))
      {s : ℂ | 7 / 12 < s.re} :=
    ((differentiable_grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S).comp haff).differentiableOn
  have hnum_diff : DifferentiableOn ℂ
      (fun s => continuedProbeCorrection 𝔪 η S s *
        truncatedModifiedRegularCorrection M (fun v => primeKappaAt 𝔪 η v ^ 6)
          (fun v => heckeValue 𝔪 η v.asIdeal) S s)
      {s : ℂ | 7 / 12 < s.re} :=
    ((differentiableOn_continuedProbeCorrection 𝔪 η S).mono hsub12).mul (hmod_diff.mono hsub41)
  have hden_diff : DifferentiableOn ℂ
      (fun s => grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
        grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
        residualCorrection (fun v => primeKappaAt 𝔪 η v ^ 6)
          (fun v => heckeValue 𝔪 η v.asIdeal) S s)
      {s : ℂ | 7 / 12 < s.re} :=
    (hLM_diff.mul hdelM_diff).mul ((differentiableOn_residualCorrection _ _ hA hη S).mono hsub12)
  have hS_lam : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S :=
    fun v hv => hS v ((absNorm_le_nine_of_lambda_mem hv).trans (by omega))
  have hS_64 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, 64 ≤ primeNorm v.1 := by
    intro v
    have hv : 64 < v.1.asIdeal.absNorm := lt_of_not_ge fun h => v.2 (hS v.1 (by omega))
    unfold primeNorm
    exact_mod_cast hv.le
  refine ⟨hnum_diff.div hden_diff (fun s hs =>
      truncated_denominator_ne_zero_of_seven_twelfths_le hM 𝔪 η S (le_of_lt hs)),
    fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hden_ne := truncated_denominator_ne_zero_of_seven_twelfths_le hM 𝔪 η S (by linarith)
    unfold continuedTruncatedCorrection
    rw [div_eq_iff hden_ne]
    exact (truncatedFullPrincipalCorrection_mul_grossen_eq hM 𝔪 η S hS_lam hS_64 hs).symm
  · have hden_ne := truncated_denominator_ne_zero_of_seven_twelfths_le hM 𝔪 η S (by linarith)
    unfold continuedTruncatedCorrection
    exact div_ne_zero
      (mul_ne_zero (continuedProbeCorrection_ne_zero_of_two_thirds_le 𝔪 η S hs)
        (hmod_ne s (by linarith)))
      hden_ne
  · have hden_ne := truncated_denominator_ne_zero_of_seven_twelfths_le hM 𝔪 η S (le_of_lt hs)
    unfold continuedTruncatedCorrection
    rw [div_eq_zero_iff, or_iff_left hden_ne, mul_eq_zero]
    exact or_iff_left (hmod_ne s (by linarith))

/-- **Universal zero-obstruction theorem across all finite cube-exponent truncations `L ≥ 3`
(`M = (L + 1) / 2 ≥ 2`).** For the fixed prime cutoff `N_cut` (`160 ≤ N_cut`), whenever `S`
contains `{v | N(v) ≤ N_cut}` and `σ₀ < 7/12`, every function `G` holomorphic on `Re s > σ₀` that
agrees with `truncatedFullPrincipalCorrection ((L + 1) / 2) 𝔪 η S` on `Re s ≥ 2` has zeros in
`7/12 ≤ Re s < 2/3` with arbitrarily large imaginary parts (`|Im s| > T`), and in particular no
nonvanishing holomorphic continuation exists on `Re s > σ₀`. -/
theorem exists_unbounded_zeros_and_no_nonvanishing_continuation_of_truncatedProbeCorrection :
    ∃ N_cut : ℕ, 160 ≤ N_cut ∧
      ∀ {L : ℕ}, 3 ≤ L → ∀ (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
        (S : Finset (HeightOneSpectrum O)),
        (∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ N_cut → v ∈ S) →
        ∀ {σ₀ : ℝ}, σ₀ < 7 / 12 →
        (∀ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ < s.re} →
          (∀ s : ℂ, 2 ≤ s.re →
            G s = truncatedFullPrincipalCorrection ((L + 1) / 2) 𝔪 η S s) →
          ∀ T : ℝ, ∃ s₀ : ℂ, 7 / 12 ≤ s₀.re ∧ s₀.re < 2 / 3 ∧ T < |s₀.im| ∧ G s₀ = 0) ∧
        (¬ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ < s.re} ∧
          (∀ s : ℂ, 2 ≤ s.re →
            G s = truncatedFullPrincipalCorrection ((L + 1) / 2) 𝔪 η S s) ∧
          (∀ s : ℂ, σ₀ < s.re → G s ≠ 0)) := by
  obtain ⟨N_cut, h160, hmod_cut⟩ := exists_truncatedModifiedRegularCorrection_cutoff
  refine ⟨N_cut, h160, fun {L} hL 𝔪 η S hS {σ₀} hσ₀ => ?_⟩
  set M : ℕ := (L + 1) / 2
  have hM : 2 ≤ M := by omega
  have hzeros : ∀ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ < s.re} →
      (∀ s : ℂ, 2 ≤ s.re → G s = truncatedFullPrincipalCorrection M 𝔪 η S s) →
      ∀ T : ℝ, ∃ s₀ : ℂ, 7 / 12 ≤ s₀.re ∧ s₀.re < 2 / 3 ∧ T < |s₀.im| ∧ G s₀ = 0 := by
    intro G hG_diff hG_eq T
    have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
    have hη : ∀ v, ‖heckeValue 𝔪 η v.asIdeal‖ ≤ 1 := fun _ => norm_heckeValue_le_one 𝔪 η _
    obtain ⟨hmod_diff, _, _⟩ := hmod_cut hM S hS _ _ hA hη
    set U : Set ℂ := {s : ℂ | max σ₀ (41 / 72) < s.re}
    have hU_open : IsOpen U := isOpen_lt continuous_const continuous_re
    have hU_pre : IsPreconnected U := by
      have hU_eq : U = Complex.reCLM ⁻¹' Set.Ioi (max σ₀ (41 / 72)) := rfl
      rw [hU_eq]
      exact ((convex_Ioi _).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
    have hsubG : U ⊆ {s : ℂ | σ₀ < s.re} := fun s hs =>
      lt_of_le_of_lt (le_max_left _ _) hs
    have hsub41 : U ⊆ {s : ℂ | 41 / 72 < s.re} := fun s hs =>
      lt_of_le_of_lt (le_max_right _ _) hs
    have hsub12 : U ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => by
      have h41 : 41 / 72 < s.re := hsub41 hs; show 1 / 2 < s.re; linarith
    have haff : Differentiable ℂ (fun s : ℂ => 6 * (M : ℂ) * s - 3 * (M : ℂ)) :=
      ((differentiable_id.const_mul (6 * (M : ℂ))).sub (differentiable_const (3 * (M : ℂ))))
    have hmap : MapsTo (fun s : ℂ => 6 * (M : ℂ) * s - 3 * (M : ℂ)) U
        {w : ℂ | -(3 * (M : ℝ)) < w.re} := by
      intro s hs
      have h41 : 41 / 72 < s.re := hsub41 hs
      have h1 : (6 * (M : ℂ) * s - 3 * (M : ℂ)) = ((M : ℝ) : ℂ) * (6 * s - 3) := by
        push_cast; ring
      show -(3 * (M : ℝ)) < (6 * (M : ℂ) * s - 3 * (M : ℂ)).re
      rw [h1, Complex.re_ofReal_mul]
      simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    let D_diff : ℂ → ℂ := fun s =>
      G s * (grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
        grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S (6 * (M : ℂ) * s - 3 * (M : ℂ)) *
        residualCorrection (fun v => primeKappaAt 𝔪 η v ^ 6)
          (fun v => heckeValue 𝔪 η v.asIdeal) S s) -
      continuedProbeCorrection 𝔪 η S s *
        truncatedModifiedRegularCorrection M (fun v => primeKappaAt 𝔪 η v ^ 6)
          (fun v => heckeValue 𝔪 η v.asIdeal) S s
    have hD_diff : DifferentiableOn ℂ D_diff U := by
      have hLM : DifferentiableOn ℂ
          (fun s : ℂ => grossenLFunction 𝔪 (η ^ (6 * M)) M (6 * (M : ℂ) * s - 3 * (M : ℂ))) U :=
        (differentiableOn_grossenLFunction 𝔪 (η ^ (6 * M)) (by omega)).comp
          haff.differentiableOn hmap
      have hdelM : DifferentiableOn ℂ
          (fun s : ℂ => grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S
            (6 * (M : ℂ) * s - 3 * (M : ℂ))) U :=
        ((differentiable_grossenDeletedFactors 𝔪 (η ^ (6 * M)) M S).comp haff).differentiableOn
      exact ((hG_diff.mono hsubG).mul ((hLM.mul hdelM).mul
        ((differentiableOn_residualCorrection _ _ hA hη S).mono hsub12))).sub
        (((differentiableOn_continuedProbeCorrection 𝔪 η S).mono hsub12).mul
          (hmod_diff.mono hsub41))
    have hana : AnalyticOnNhd ℂ D_diff U := hD_diff.analyticOnNhd hU_open
    have h3_mem : (3 : ℂ) ∈ U := by
      change max σ₀ (41 / 72) < (3 : ℂ).re
      simp only [re_ofNat]
      exact max_lt (by linarith) (by norm_num)
    have hS_lam : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S :=
      fun v hv => hS v ((absNorm_le_nine_of_lambda_mem hv).trans (by omega))
    have hS_64 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, 64 ≤ primeNorm v.1 := by
      intro v
      have hv : 64 < v.1.asIdeal.absNorm := lt_of_not_ge fun h => v.2 (hS v.1 (by omega))
      unfold primeNorm
      exact_mod_cast hv.le
    have hev : D_diff =ᶠ[𝓝 (3 : ℂ)] 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by norm_num : (2 : ℝ) < (3 : ℂ).re)] with s hs
      have hs2 : 2 ≤ s.re := le_of_lt hs
      dsimp only [D_diff]
      rw [hG_eq s hs2, truncatedFullPrincipalCorrection_mul_grossen_eq hM 𝔪 η S hS_lam hS_64
        (by linarith), sub_self]
    obtain ⟨s₀, hs₀_lo, hs₀_hi, hs₀_im, hs₀_zero⟩ :=
      exists_zero_continuedProbeCorrection_in_strip_im_gt 𝔪 η S T
    have hs₀_mem : s₀ ∈ U := by
      change max σ₀ (41 / 72) < s₀.re
      exact max_lt (lt_of_lt_of_le hσ₀ hs₀_lo) (by linarith)
    have hD0 : D_diff s₀ = 0 :=
      hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_pre h3_mem hev hs₀_mem
    dsimp only [D_diff] at hD0
    rw [hs₀_zero, zero_mul, sub_zero] at hD0
    have hden_ne := truncated_denominator_ne_zero_of_seven_twelfths_le hM 𝔪 η S hs₀_lo
    exact ⟨s₀, hs₀_lo, hs₀_hi, hs₀_im, (mul_eq_zero.mp hD0).resolve_right hden_ne⟩
  refine ⟨hzeros, ?_⟩
  rintro ⟨G, hG_diff, hG_eq, hG_ne⟩
  obtain ⟨s₀, hs₀_lo, _, _, hG0⟩ := hzeros G hG_diff hG_eq 0
  exact hG_ne s₀ (lt_of_lt_of_le hσ₀ hs₀_lo) hG0

/-! ### 5. Sub-cubic global cutoff (`N(J) < Z^η`, `η < 1/3`) and persistence of `7/8`, `2/3`, `3/5` -/

private theorem mul_le_prime_iff {I J P : Ideal O} (hP : P.IsPrime) (hIJ : I * J ≤ P) :
    I ≤ P ∨ J ≤ P := by
  by_contra hnot
  obtain ⟨hI, hJ⟩ : ¬ (I ≤ P) ∧ ¬ (J ≤ P) := not_or.mp hnot
  obtain ⟨x, hxI, hxP⟩ := Set.not_subset.mp hI
  obtain ⟨y, hyJ, hyP⟩ := Set.not_subset.mp hJ
  exact (hP.mem_or_mem (hIJ (Ideal.mul_mem_mul hxI hyJ))).elim hxP hyP

private theorem mem_of_prod_asIdeal_le {S : Finset (HeightOneSpectrum O)}
    {T : Finset {v : HeightOneSpectrum O // v ∉ S}} {u₀ : {v : HeightOneSpectrum O // v ∉ S}}
    (hle : (∏ u ∈ T, u.1.asIdeal) ≤ u₀.1.asIdeal) : u₀ ∈ T := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.one_eq_top, top_le_iff] at hle
    exact absurd hle u₀.1.isPrime.ne_top
  | insert w T' hw ih =>
    rw [Finset.prod_insert hw] at hle
    rcases mul_le_prime_iff u₀.1.isPrime hle with hw_le | hT_le
    · have heq : w.1.asIdeal = u₀.1.asIdeal := w.1.isMaximal.eq_of_le u₀.1.isPrime.ne_top hw_le
      have hwu : w = u₀ := Subtype.ext (HeightOneSpectrum.ext heq)
      exact Finset.mem_insert.mpr (Or.inl hwu.symm)
    · exact Finset.mem_insert_of_mem (ih hT_le)

private theorem prod_asIdeal_injective (S : Finset (HeightOneSpectrum O)) :
    Function.Injective (fun T : Finset {v : HeightOneSpectrum O // v ∉ S} =>
      ∏ u ∈ T, u.1.asIdeal) := by
  intro T₁ T₂ h
  refine Finset.Subset.antisymm (fun u₀ hu₀ => ?_) (fun u₀ hu₀ => ?_)
  · refine mem_of_prod_asIdeal_le ?_
    rw [← h]
    exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun u => u.1.asIdeal) hu₀)
  · refine mem_of_prod_asIdeal_le ?_
    rw [h]
    exact Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun u => u.1.asIdeal) hu₀)

/-- **Unconditional `Z^{2/3}` squarefree sixth-power Möbius norm lower bound inside every sub-cubic
omitted tail `N(J) ≥ Z^η` (`η < 1/3`).** For every `η < 1/3` (in particular across the entire
Milestone 1 power-saving window `1/6 < η < 1/3`), every `(𝔪, η_char, S)`, and every `a : ℝ`, there
exist `c > 0` and `Z₁ ≥ 1` such that for all `Z ≥ Z₁`, some finite squarefree prime-subset family
`ℱ` outside `S` satisfies:
1. every `T ∈ ℱ` has cube-index norm `N(J) = N(T)² ≥ Z^η` (lying strictly inside the omitted
   sub-cubic tail `N(J) ≥ Z^η`),
2. every `T ∈ ℱ` has total sixth-power norm `N(T)⁶ ≤ Z`, and
3. the row-continued sixth-power Möbius norm sum over `ℱ` is at least `c · Z^{2/3}`. -/
theorem exists_subcubic_sixthPower_defect_lower_bound {η : ℝ} (hη : η < 1 / 3)
    (𝔪 : Modulus K) (η_char : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O)) (a : ℝ) :
    ∃ c Z₁ : ℝ, 0 < c ∧ 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
      ∃ ℱ : Finset (Finset {v : HeightOneSpectrum O // v ∉ S}),
        (∀ T ∈ ℱ, Z ^ η ≤ ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ)) ∧
        (∀ T ∈ ℱ, ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) ≤ Z) ∧
        c * Z ^ (2 / 3 : ℝ) ≤
          ∑ T ∈ ℱ, ‖deletedSquarefreeCoeff 𝔪 (η_char ^ 6) 1 T *
            (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
              (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a := by
  rcases le_or_gt η 0 with hη0 | hη0
  · obtain ⟨c₀, Z₀, hc₀, hZ₀, hbase⟩ :=
      exists_lower_bound_squarefree_sixthPower_mobius_norm 𝔪 η_char S a
    refine ⟨c₀, Z₀, hc₀, hZ₀, fun Z hZ => ?_⟩
    obtain ⟨ℱ, hℱ_hi, hℱ_sum⟩ := hbase Z hZ
    refine ⟨ℱ, fun T _ => ?_, hℱ_hi, hℱ_sum⟩
    have hZ_eta_le1 : Z ^ η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hZ₀.trans hZ) hη0
    have hNT1 : (1 : ℝ) ≤ ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (deletedSquarefreeNorm_pos T) 2
    exact hZ_eta_le1.trans hNT1
  · set b : ℝ := min a 0
    have hb_nonpos : b ≤ 0 := min_le_right a 0
    have hb_le_a : b ≤ a := min_le_left a 0
    obtain ⟨c_b, Z₀, hc_b, hZ₀, hbase⟩ :=
      exists_lower_bound_squarefree_sixthPower_mobius_norm 𝔪 η_char S b
    have hgap : 0 < 2 / 3 - 2 * η := by linarith
    set Z_cut : ℝ := max Z₀ ((256 / c_b + 1) ^ (1 / (2 / 3 - 2 * η)))
    refine ⟨c_b / 2, Z_cut, by positivity, hZ₀.trans (le_max_left _ _), fun Z hZ => ?_⟩
    have hZ1 : 1 ≤ Z := hZ₀.trans ((le_max_left _ _).trans hZ)
    have hZ_pos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
    obtain ⟨ℱ, hℱ_hi, hℱ_sum⟩ := hbase Z ((le_max_left _ _).trans hZ)
    set ℱ_high := ℱ.filter fun T => Z ^ η ≤ ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ)
    set ℱ_low := ℱ.filter fun T => ¬ (Z ^ η ≤ ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ))
    let term_b : Finset {v : HeightOneSpectrum O // v ∉ S} → ℝ := fun T =>
      ‖deletedSquarefreeCoeff 𝔪 (η_char ^ 6) 1 T * (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
        (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ b
    -- Bound `#ℱ_low ≤ 128 * Z^(η / 2)` by embedding into ideals of norm `≤ Z^(η / 2)`.
    have hlow_card : (ℱ_low.card : ℝ) ≤ 128 * Z ^ (η / 2) := by
      set S_id : Finset (Ideal O) :=
        ((Ideal.finite_setOf_absNorm_le (S := O) ⌊Z ^ (η / 2)⌋₊).toFinset).filter
          fun I => I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ Z ^ (η / 2)
      have hsub : (ℱ_low.image fun T => ∏ u ∈ T, u.1.asIdeal) ⊆ S_id := by
        intro I hI
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hI
        have hT_lt : ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ) < Z ^ η :=
          not_le.mp (Finset.mem_filter.mp hT).2
        have hsq_lt : (deletedSquarefreeNorm T : ℝ) ^ 2 < (Z ^ (η / 2)) ^ 2 := by
          have h1 : ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ) =
              (deletedSquarefreeNorm T : ℝ) ^ 2 := by push_cast; rfl
          have h2 : (Z ^ (η / 2)) ^ 2 = Z ^ η := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hZ_pos.le]; ring_nf
          linarith
        have hNT_lt : (deletedSquarefreeNorm T : ℝ) < Z ^ (η / 2) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) (deletedSquarefreeNorm T),
            Real.rpow_nonneg hZ_pos.le (η / 2)]
        have hnorm_eq : (∏ u ∈ T, u.1.asIdeal).absNorm = deletedSquarefreeNorm T := by
          rw [map_prod]; rfl
        simp only [S_id, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        refine ⟨(Nat.le_floor_iff (by positivity)).mpr (by rw [hnorm_eq]; linarith),
          fun h0 => ?_, by rw [hnorm_eq]; linarith⟩
        have hn0 : (∏ u ∈ T, u.1.asIdeal).absNorm = 0 := by rw [h0, map_zero]
        exact (deletedSquarefreeNorm_pos T).ne' (hnorm_eq.symm.trans hn0)
      have hcard_eq : (ℱ_low.image fun T => ∏ u ∈ T, u.1.asIdeal).card = ℱ_low.card :=
        Finset.card_image_of_injective _ (prod_asIdeal_injective S)
      have h1 : ℱ_low.card ≤ S_id.card := by
        rw [← hcard_eq]; exact Finset.card_le_card hsub
      have h1r : (ℱ_low.card : ℝ) ≤ (S_id.card : ℝ) := by exact_mod_cast h1
      exact h1r.trans (EisensteinLatticeCount.finite_ideal_count_real S_id (Z ^ (η / 2))
        (Real.one_le_rpow hZ1 (by linarith))
        (fun I hI => (Finset.mem_filter.mp hI).2.1)
        (fun I hI => (Finset.mem_filter.mp hI).2.2))
    -- Bound each `term_b T` on `ℱ_low` by `Z^((3 / 2) * η)`.
    have hlow_term : ∀ T ∈ ℱ_low, term_b T ≤ Z ^ ((3 / 2 : ℝ) * η) := by
      intro T hT
      have hT_lt : ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ) < Z ^ η :=
        not_le.mp (Finset.mem_filter.mp hT).2
      have hsq_lt : (deletedSquarefreeNorm T : ℝ) ^ 2 < (Z ^ (η / 2)) ^ 2 := by
        have h1 : ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ) =
            (deletedSquarefreeNorm T : ℝ) ^ 2 := by push_cast; rfl
        have h2 : (Z ^ (η / 2)) ^ 2 = Z ^ η := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZ_pos.le]; ring_nf
        linarith
      have hNT_le : (deletedSquarefreeNorm T : ℝ) ≤ Z ^ (η / 2) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (deletedSquarefreeNorm T),
          Real.rpow_nonneg hZ_pos.le (η / 2)]
      have hNT_pos : (0 : ℝ) < deletedSquarefreeNorm T :=
        Nat.cast_pos.mpr (deletedSquarefreeNorm_pos T)
      dsimp only [term_b]
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      have hc_le : ‖deletedSquarefreeCoeff 𝔪 (η_char ^ 6) 1 T‖ ≤ 1 :=
        norm_deletedSquarefreeCoeff_le 𝔪 (η_char ^ 6) 1 T
      calc ‖deletedSquarefreeCoeff 𝔪 (η_char ^ 6) 1 T‖ * (deletedSquarefreeNorm T : ℝ) ^ 3 *
            (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ b
          ≤ 1 * (deletedSquarefreeNorm T : ℝ) ^ 3 *
              (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ b :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hc_le (by positivity)) (by positivity)
        _ = Z ^ b * (deletedSquarefreeNorm T : ℝ) ^ (3 - 6 * b) := by
            rw [one_mul, Real.div_rpow hZ_pos.le (Nat.cast_nonneg _), Nat.cast_pow,
              ← Real.rpow_natCast (deletedSquarefreeNorm T : ℝ) 6,
              ← Real.rpow_mul hNT_pos.le, ← Real.rpow_natCast (deletedSquarefreeNorm T : ℝ) 3,
              div_eq_mul_inv, ← Real.rpow_neg hNT_pos.le,
              mul_left_comm ((deletedSquarefreeNorm T : ℝ) ^ _) (Z ^ b),
              ← Real.rpow_add hNT_pos]
            congr 2
            ring
        _ ≤ Z ^ b * (Z ^ (η / 2)) ^ (3 - 6 * b) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hNT_pos.le hNT_le (by linarith)) (by positivity)
        _ = Z ^ ((3 / 2 : ℝ) * η + b * (1 - 3 * η)) := by
            rw [← Real.rpow_mul hZ_pos.le, ← Real.rpow_add hZ_pos]
            congr 1
            ring
        _ ≤ Z ^ ((3 / 2 : ℝ) * η) := by
            refine Real.rpow_le_rpow_of_exponent_le hZ1 ?_
            have h13 : 0 < 1 - 3 * η := by linarith
            nlinarith
    have hlow_sum : ∑ T ∈ ℱ_low, term_b T ≤ (c_b / 2) * Z ^ (2 / 3 : ℝ) := by
      have h1 : ∑ T ∈ ℱ_low, term_b T ≤ 128 * Z ^ (2 * η) := by
        calc ∑ T ∈ ℱ_low, term_b T
            ≤ ∑ _T ∈ ℱ_low, Z ^ ((3 / 2 : ℝ) * η) := Finset.sum_le_sum hlow_term
          _ = (ℱ_low.card : ℝ) * Z ^ ((3 / 2 : ℝ) * η) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (128 * Z ^ (η / 2)) * Z ^ ((3 / 2 : ℝ) * η) :=
              mul_le_mul_of_nonneg_right hlow_card (by positivity)
          _ = 128 * (Z ^ (η / 2) * Z ^ ((3 / 2 : ℝ) * η)) := by ring
          _ = 128 * Z ^ (2 * η) := by
              rw [← Real.rpow_add hZ_pos]
              congr 2
              ring
      have hZ_pow : 256 / c_b ≤ Z ^ (2 / 3 - 2 * η) := by
        have hZ_ge : (256 / c_b + 1) ^ (1 / (2 / 3 - 2 * η)) ≤ Z :=
          (le_max_right _ _).trans hZ
        have hbase_ge1 : 1 ≤ 256 / c_b + 1 := by linarith [div_pos (by norm_num : (0 : ℝ) < 256) hc_b]
        calc 256 / c_b ≤ 256 / c_b + 1 := by linarith
          _ = ((256 / c_b + 1) ^ (1 / (2 / 3 - 2 * η))) ^ (2 / 3 - 2 * η) := by
              rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hgap.ne', Real.rpow_one]
          _ ≤ Z ^ (2 / 3 - 2 * η) := Real.rpow_le_rpow (by positivity) hZ_ge hgap.le
      have h2 : 128 * Z ^ (2 * η) ≤ (c_b / 2) * Z ^ (2 / 3 : ℝ) := by
        have hmul : (256 / c_b) * (c_b / 2) = 128 := by field_simp [hc_b.ne']; ring
        calc 128 * Z ^ (2 * η)
            = (c_b / 2) * ((256 / c_b) * Z ^ (2 * η)) := by linear_combination -Z ^ (2 * η) * hmul
          _ ≤ (c_b / 2) * (Z ^ (2 / 3 - 2 * η) * Z ^ (2 * η)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hZ_pow (by positivity)) (by positivity)
          _ = (c_b / 2) * Z ^ (2 / 3 : ℝ) := by
              rw [← Real.rpow_add hZ_pos]
              congr 2
              ring
      exact h1.trans h2
    have hsplit_sum : ∑ T ∈ ℱ_high, term_b T + ∑ T ∈ ℱ_low, term_b T = ∑ T ∈ ℱ, term_b T :=
      Finset.sum_filter_add_sum_filter_not ℱ
        (fun T => Z ^ η ≤ ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ)) term_b
    have hhigh_b : (c_b / 2) * Z ^ (2 / 3 : ℝ) ≤ ∑ T ∈ ℱ_high, term_b T := by
      linarith [hℱ_sum, hsplit_sum, hlow_sum]
    refine ⟨ℱ_high, fun T hT => (Finset.mem_filter.mp hT).2,
      fun T hT => hℱ_hi T (Finset.mem_filter.mp hT).1, hhigh_b.trans ?_⟩
    refine Finset.sum_le_sum fun T hT => ?_
    have hT_Z : ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) ≤ Z :=
      hℱ_hi T (Finset.mem_filter.mp hT).1
    have hNT6_pos : (0 : ℝ) < ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (pow_pos (deletedSquarefreeNorm_pos T) 6)
    have hquot_ge1 : 1 ≤ Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) :=
      (one_le_div hNT6_pos).mpr hT_Z
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hquot_ge1 hb_le_a) (norm_nonneg _)

/-- **Exact contraction of the coupled Grossencharacter threshold map `b ↦ (3 + b) / 6` from any
starting abscissa `σ_base` (including `7/8`, `2/3`, and `1`).** -/
theorem coupled_tower_iterates_eq_and_tendsto (σ_base : ℝ) :
    (∀ K : ℕ, ((fun b : ℝ => (3 + b) / 6)^[K] σ_base) =
      3 / 5 + (σ_base - 3 / 5) / (6 : ℝ) ^ K) ∧
    Tendsto (fun K : ℕ => ((fun b : ℝ => (3 + b) / 6)^[K] σ_base)) atTop (𝓝 (3 / 5 : ℝ)) := by
  have hiter : ∀ K : ℕ, ((fun b : ℝ => (3 + b) / 6)^[K] σ_base) =
      3 / 5 + (σ_base - 3 / 5) / (6 : ℝ) ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      field_simp
      ring
  refine ⟨hiter, ?_⟩
  have h0 : Tendsto (fun K : ℕ => (σ_base - 3 / 5) * ((1 / 6 : ℝ) ^ K)) atTop
      (𝓝 ((σ_base - 3 / 5) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
  have h1 : Tendsto (fun K : ℕ => (3 / 5 : ℝ) + (σ_base - 3 / 5) * ((1 / 6 : ℝ) ^ K)) atTop
      (𝓝 ((3 / 5 : ℝ) + (σ_base - 3 / 5) * 0)) :=
    tendsto_const_nhds.add h0
  simp only [mul_zero, add_zero] at h1
  refine h1.congr fun K => ?_
  rw [hiter K, one_div_pow, div_eq_mul_inv]

/-! ### 6. Complete synthesis of the incomplete-reciprocity producer classification -/

/-- **Complete unconditional classification of incompletely completed reciprocity transforms over
`O = ℤ[ω]` across Milestones 1, 2, and 3:**
1. *(Milestone 1 — Row-level sub-cubic power saving retaining target and root-number phases):*
   For every strictly sub-cubic cutoff `1/6 < η < 1/3`, conductor gap `0 < δ < 1`, compact smooth
   profile `W₀`, and bounded complex box `[σ₁, σ₂] × [-T, T]`, `incompleteIdealT (X^η)` retains the
   exact `J = (1)` Möbius target and all unit-modulus local Gauss root-number phases, is strictly
   non-reducible to `completedIdealT` on nontrivial profiles, and achieves a uniform power saving
   `‖reciprocityBoundaryDefect‖ ≤ C · X^{1/2 - min(3η - 1/2, 1)}` (`> 0` below `X^{1/2}`) across
   `X ≥ 1` and `N(c) ≤ X^{1 - δ}`, whereas in the sub-conductor regime `N(c) ≥ X^{1 + κ}` (`κ > 0`)
   the primitive cusp `1 / c` has reflection scale `≤ C₀ · X^{-2κ}` for all `η' ≤ 1/3`.
2. *(Milestone 2 — Restoration of the Gauss walls under row-family Poisson continuation):*
   Under the detector's row-family Poisson continuation (`z = 1/6`), `L ∈ {1, 2}` (`M = 1`) omits
   `l = 2` and converges without wall on `Re s > σ > 1/2`, whereas for **every** finite cube-exponent
   cutoff `L ≥ 3` (`M = (L + 1) / 2 ≥ 2`) and the fixed `L`-independent prime cutoff `N_cut ≥ 160`,
   every holomorphic continuation of `truncatedFullPrincipalCorrection ((L + 1) / 2) 𝔪 η S` below
   `7/12` has infinitely many zeros with unbounded ordinates in `7/12 ≤ Re s < 2/3` and admits no
   nonvanishing holomorphic continuation below `7/12`.
3. *(Milestone 3 — Sub-cubic global defect floor and invariance of `7/8`, `2/3`, `3/5`):*
   For every sub-cubic global cutoff `N(J) < Z^η` with `η < 1/3` (including `1/6 < η < 1/3`), the
   omitted tail `N(J) = N(T)² ≥ Z^η` (`N(T)⁶ ≤ Z`) carries sixth-power Möbius norm at least
   `c · Z^{2/3}` (`c > 0`), and iterating the coupled tower map `b ↦ (3 + b) / 6` from `7/8`, `2/3`,
   or `1` converges strictly from above to the stationary barrier `3/5`. -/
theorem incomplete_reciprocity_producer_classification :
    -- (1) Milestone 1: target retention and uniform sub-cubic power saving across the reflection box
    (∀ {Y₀ : ℝ}, 1 < Y₀ → ∀ (Ψ : O →* ℂ) (W : ℝ → ℂ) {X : ℝ}, 0 < X → ∀ I : Ideal O,
      incompleteIdealSummand Y₀ Ψ W X I 1 =
        (Real.sqrt X : ℂ)⁻¹ * CompletedGauss.columnWeight Ψ I * W ((Ideal.absNorm I : ℝ) / X)) ∧
    (∀ (W₀ : ℝ → ℂ) {a b : ℝ}, 0 < a → a ≤ b →
      Function.support W₀ ⊆ Icc a b → ContDiff ℝ ∞ W₀ →
      ∀ (σ₁ σ₂ T : ℝ) {δ η : ℝ}, 0 < δ → δ < 1 → 1 / 6 < η → η < 1 / 3 →
      ∃ C : ℝ, 0 < C ∧
        ∀ (X : ℝ), 1 ≤ X →
        ∀ (c : O) (hc : c ≠ 0) [Fintype (O ⧸ Ideal.span {9 * c})],
          (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ X ^ (1 - δ) →
        ∀ (Ψ : (O ⧸ Ideal.span {c}) →* ℂ), (∀ x, ‖Ψ x‖ ≤ 1) →
        ∀ s ∈ complexParameterBox σ₁ σ₂ T,
          ‖reciprocityBoundaryDefect (X ^ η) (X ^ max (δ / 3) ((1 - δ) / 3))
              c hc Ψ (CompletedHeight.finiteTwistCusp (9 * c) (mul_ne_zero (by norm_num) hc))
              (complexTwistedWindow W₀ s) X‖ ≤
            C * X ^ ((1 / 2 : ℝ) - min (3 * η - 1 / 2) 1)) ∧
    -- (2) Milestone 2: `L ≥ 3` truncation restores the exact strip zeros and blocks `σ₀ < 7/12`
    (∃ N_cut : ℕ, 160 ≤ N_cut ∧
      ∀ {L : ℕ}, 3 ≤ L → ∀ (𝔪 : Modulus K) (η_char : HeckeCharacter 𝔪)
        (S : Finset (HeightOneSpectrum O)),
        (∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ N_cut → v ∈ S) →
        ∀ {σ₀ : ℝ}, σ₀ < 7 / 12 →
          ¬ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ < s.re} ∧
            (∀ s : ℂ, 2 ≤ s.re →
              G s = truncatedFullPrincipalCorrection ((L + 1) / 2) 𝔪 η_char S s) ∧
            (∀ s : ℂ, σ₀ < s.re → G s ≠ 0)) ∧
    -- (3) Milestone 3: `Z^{2/3}` defect inside every `η < 1/3` tail + coupled limit `3/5` from `7/8` and `2/3`
    (∀ {η : ℝ}, η < 1 / 3 → ∀ (𝔪 : Modulus K) (η_char : HeckeCharacter 𝔪)
      (S : Finset (HeightOneSpectrum O)) (a : ℝ),
      ∃ c Z₁ : ℝ, 0 < c ∧ 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
        ∃ ℱ : Finset (Finset {v : HeightOneSpectrum O // v ∉ S}),
          (∀ T ∈ ℱ, Z ^ η ≤ ((deletedSquarefreeNorm T ^ 2 : ℕ) : ℝ)) ∧
          (∀ T ∈ ℱ, ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) ≤ Z) ∧
          c * Z ^ (2 / 3 : ℝ) ≤
            ∑ T ∈ ℱ, ‖deletedSquarefreeCoeff 𝔪 (η_char ^ 6) 1 T *
              (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
                (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a) ∧
    (∀ σ_base : ℝ, 3 / 5 < σ_base →
      (∀ K : ℕ, 3 / 5 < ((fun b : ℝ => (3 + b) / 6)^[K] σ_base)) ∧
      Tendsto (fun K : ℕ => ((fun b : ℝ => (3 + b) / 6)^[K] σ_base)) atTop (𝓝 (3 / 5 : ℝ))) := by
  refine ⟨fun hY₀ Ψ W hX I => incompleteIdealSummand_retains_target hY₀ Ψ W hX I,
    fun W₀ ha hab hs hW σ₁ σ₂ T hδ0 hδ1 hη_lo hη_hi =>
      (milestone_one_subcubic_power_saving W₀ ha hab hs hW σ₁ σ₂ T hδ0 hδ1 hη_lo hη_hi).2.2.2,
    ?_, fun hη 𝔪 η_char S a => exists_subcubic_sixthPower_defect_lower_bound hη 𝔪 η_char S a,
    fun σ_base hσ => ?_⟩
  · obtain ⟨N_cut, h160, hno⟩ :=
      exists_unbounded_zeros_and_no_nonvanishing_continuation_of_truncatedProbeCorrection
    exact ⟨N_cut, h160, fun hL 𝔪 η_char S hS hσ₀ => (hno hL 𝔪 η_char S hS hσ₀).2⟩
  · obtain ⟨hiter, htend⟩ := coupled_tower_iterates_eq_and_tendsto σ_base
    refine ⟨fun K => ?_, htend⟩
    rw [hiter K]
    have hpos : 0 < (σ_base - 3 / 5) / (6 : ℝ) ^ K := div_pos (by linarith) (by positivity)
    linarith

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.singleRow_vs_rowPoisson_amplification_dichotomy
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.localTerm_odd_cube_eq_zero
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.hasSum_localTerm_lt_cutoff
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.truncatedPrincipalLocalFactor_eq_geom_mul_regular_add
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.exists_truncatedPrincipalCorrection_one_cutoff
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.exists_continuedTruncatedCorrection_properties
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.exists_unbounded_zeros_and_no_nonvanishing_continuation_of_truncatedProbeCorrection
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.exists_subcubic_sixthPower_defect_lower_bound
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.coupled_tower_iterates_eq_and_tendsto
#print axioms GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.incomplete_reciprocity_producer_classification
