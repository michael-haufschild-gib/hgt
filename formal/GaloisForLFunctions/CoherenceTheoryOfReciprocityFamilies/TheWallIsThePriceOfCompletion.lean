import GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies.TheAverageRowIsBlindToTheTarget

/-!
# The wall is the price of completion

The cubic-theta probe sums the theta coefficients at completed indices `A = c n³`: at a prime `π`
the index has exponent `t = e + 3l` with `e ∈ {0, 1}` (squarefree part) and every `l ≥ 0` (cube
part). The reflection of the probe, which gives the direct estimate, is a property of the completed
theta row. On the Poisson side the completion produces the wall.

* `hasSum_localTerm_uncompleted`: for a row `u` with `π ∤ u`, the local series restricted to the
  cube-free indices `l ≤ 1` sums to `rowLocalSum` with `R = 0`:
  `(1 − V)⁻¹ + ρY(1 − ρY)⁻¹ − ηρ⁻¹X − η(Q − 1)XYV(1 − V)⁻¹`.
* `rowLocalSum_sub_uncompleted`: the completed part (`l ≥ 2`) is
  `R(1 − R)⁻¹ ((1 − Q⁻¹)(1 − V)⁻¹ + ρY − ηρ⁻¹X − η(Q − 1)XYV(1 − V)⁻¹)`: every occurrence of
  `R = κ⁶Q⁴X⁶V`, hence of the phase `L`-function `L(6x + 6z − 4, ψ₆η⁶)`, is a joint sixth power of
  the completed index and of the frequency.
* `uncompleted_principal_factor`: at the residue point `Y = V = Q⁻¹`, `ρ = 1`, the uncompleted
  principal correction is `principalLocalFactor Q 0 η s = (1 − Q⁻²)(1 + Q⁻¹D/(1 − D))`,
  `D = ηQ^{−s}`;
* `exists_uncompletedCorrection_cutoff`: its Euler product is holomorphic and within `½` of one on
  every half-plane `Re s > σ > ½`: without completion there is no wall.

So within the cubic probe the four conditions of a source that reads the line — the Möbius sign
(odd order), the target among the twists, a reflection, and a correction convergent on
`Re s > ½` — cannot all hold: the completion of the theta index is what the reflection needs, and
it is exactly what puts the phase `L`-function into the correction.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### The local series without completion -/

section Prime

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

include h2 hprim in
/-- **The uncompleted local series.** For `π ∤ u` and `‖V‖, ‖ρY‖ < 1`, the local series of the
row `u` at `π` restricted to the cube-free indices `l ≤ 1` sums to `rowLocalSum` with `R = 0`. -/
theorem hasSum_localTerm_uncompleted (ηp X Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (hV : ‖V‖ < 1)
    (hW : ‖complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y‖ < 1) :
    HasSum (fun v : Fin 2 × ℕ × ℕ × ℕ => if v.2.1 ≤ 1 then localTerm π ηp X Y V u 0 v else 0)
      (rowLocalSum (primeQ π) 0 ηp X Y V
        (complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u))) := by
  set ρ := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u)
  set Q := primeQ π
  -- the four nonzero pieces
  let g₁ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v => if v.1 = 0 ∧ v.2.1 = 0 ∧ v.2.2.1 = 0 then
    V ^ v.2.2.2 else 0
  let g₂ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v => if v.1 = 0 ∧ v.2.1 = 0 ∧ 1 ≤ v.2.2.1 ∧ v.2.2.2 = 0
    then (ρ * Y) ^ v.2.2.1 else 0
  let g₃ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v => if v = (1, 0, 0, 0) then -(ηp * ρ⁻¹ * X) else 0
  let g₄ : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun v => if v.1 = 1 ∧ v.2.1 = 0 ∧ v.2.2.1 = 1 ∧
    1 ≤ v.2.2.2 then -(ηp * (Q - 1) * X * Y * V ^ v.2.2.2) else 0
  have hsplit : (fun v : Fin 2 × ℕ × ℕ × ℕ =>
      if v.2.1 ≤ 1 then localTerm π ηp X Y V u 0 v else 0) = fun v => g₁ v + g₂ v + g₃ v + g₄ v := by
    funext v
    obtain ⟨e, l, k, m⟩ := v
    simp only [g₁, g₂, g₃, g₄, ρ, Q, Prod.mk.injEq]
    rcases (show e = 0 ∨ e = 1 by fin_cases e <;> simp) with rfl | rfl
    · -- `e = 0`
      rcases Nat.lt_or_ge l 2 with hl | hl
      · interval_cases l
        · rw [if_pos (by norm_num), localTerm_T0 π hlam h2 hprim ηp X Y V hu 0 k m]
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp
          · rcases Nat.eq_zero_or_pos m with rfl | hm
            · simp [Nat.pos_iff_ne_zero.mp hk, Nat.one_le_iff_ne_zero.mpr
                (Nat.pos_iff_ne_zero.mp hk)]
            · simp [Nat.pos_iff_ne_zero.mp hk, Nat.pos_iff_ne_zero.mp hm]
        · rw [if_pos le_rfl]
          rcases Nat.lt_or_ge k 2 with hk | hk
          · interval_cases k
            · rw [localTerm_C0 π hlam h2 hprim ηp X Y V hu 0 m]; simp
            · rw [localTerm_C1 π hlam h2 hprim ηp X Y V hu 0 m]; simp
          · rw [localTerm_eq_zero_of_two_le π hlam h2 hprim ηp X Y V hu 0 0 1 k m (by norm_num) hk]
            simp
      · rw [if_neg (by omega)]
        simp [show l ≠ 0 by omega]
    · -- `e = 1`
      rcases Nat.lt_or_ge l 2 with hl | hl
      · interval_cases l
        · rw [if_pos (by norm_num)]
          rcases Nat.lt_or_ge k 2 with hk | hk
          · interval_cases k
            · rw [localTerm_B0 π hlam h2 hprim ηp X Y V hu 0 m]
              rcases Nat.eq_zero_or_pos m with rfl | hm
              · simp
              · simp [Nat.pos_iff_ne_zero.mp hm]
            · rw [localTerm_B1 π hlam h2 hprim ηp X Y V hu 0 m]
              rcases Nat.eq_zero_or_pos m with rfl | hm
              · simp
              · simp [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)]
          · rw [localTerm_eq_zero_of_two_le π hlam h2 hprim ηp X Y V hu 0 1 0 k m (by norm_num) hk]
            simp [show k ≠ 0 by omega, show k ≠ 1 by omega]
        · rw [if_pos le_rfl]
          rcases Nat.lt_or_ge k 2 with hk | hk
          · interval_cases k
            · rw [localTerm_D0 π hlam h2 hprim ηp X Y V hu 0 m]; simp
            · rw [localTerm_D1 π hlam h2 hprim ηp X Y V hu 0 m]; simp
          · rw [localTerm_eq_zero_of_two_le π hlam h2 hprim ηp X Y V hu 0 1 1 k m (by norm_num) hk]
            simp
      · rw [if_neg (by omega)]
        simp [show l ≠ 0 by omega]
  rw [hsplit]
  -- the four sums
  have h₁ : HasSum g₁ ((1 - V)⁻¹) := by
    have hinj : Function.Injective fun m : ℕ => ((0 : Fin 2), 0, 0, m) := fun a b h => by
      simpa using h
    refine (hinj.hasSum_iff (fun v hv => ?_)).mp ?_
    · simp only [g₁]
      rw [if_neg]
      rintro ⟨h1, h2', h3⟩
      exact hv ⟨v.2.2.2, by ext <;> simp [h1, h2', h3]⟩
    · have hcomp : g₁ ∘ (fun m : ℕ => ((0 : Fin 2), 0, 0, m)) = fun m => V ^ m := by
        funext m
        simp [g₁]
      rw [hcomp]
      exact hasSum_geometric_of_norm_lt_one hV
  have h₂ : HasSum g₂ (ρ * Y * (1 - ρ * Y)⁻¹) := by
    have hinj : Function.Injective fun k : ℕ => ((0 : Fin 2), 0, k + 1, 0) := fun a b h => by
      simpa using h
    refine (hinj.hasSum_iff (fun v hv => ?_)).mp ?_
    · simp only [g₂]
      rw [if_neg]
      rintro ⟨h1, h2', h3, h4⟩
      exact hv ⟨v.2.2.1 - 1, by ext <;> simp [h1, h2', h4]; omega⟩
    · have hcomp : g₂ ∘ (fun k : ℕ => ((0 : Fin 2), 0, k + 1, 0)) =
          fun k => ρ * Y * (ρ * Y) ^ k := by
        funext k
        simp [g₂, pow_succ']
      rw [hcomp]
      exact (hasSum_geometric_of_norm_lt_one hW).mul_left (ρ * Y)
  have h₃ : HasSum g₃ (-(ηp * ρ⁻¹ * X)) := hasSum_ite_eq _ _
  have h₄ : HasSum g₄ (-(ηp * (Q - 1) * X * Y * V) * (1 - V)⁻¹) := by
    have hinj : Function.Injective fun m : ℕ => ((1 : Fin 2), 0, 1, m + 1) := fun a b h => by
      simpa using h
    refine (hinj.hasSum_iff (fun v hv => ?_)).mp ?_
    · simp only [g₄]
      rw [if_neg]
      rintro ⟨h1, h2', h3, h4⟩
      exact hv ⟨v.2.2.2 - 1, by ext <;> simp [h1, h2', h3]; omega⟩
    · have hcomp : g₄ ∘ (fun m : ℕ => ((1 : Fin 2), 0, 1, m + 1)) =
          fun m => -(ηp * (Q - 1) * X * Y * V) * V ^ m := by
        funext m
        simp only [g₄, Function.comp, true_and, le_add_iff_nonneg_left, zero_le, if_true]
        rw [pow_succ]
        ring
      rw [hcomp]
      exact (hasSum_geometric_of_norm_lt_one hV).mul_left _
  have hval : rowLocalSum Q 0 ηp X Y V ρ = (1 - V)⁻¹ + ρ * Y * (1 - ρ * Y)⁻¹ +
      -(ηp * ρ⁻¹ * X) + -(ηp * (Q - 1) * X * Y * V) * (1 - V)⁻¹ := by
    unfold rowLocalSum
    simp only [sub_zero, inv_one, one_mul, zero_mul, mul_zero, zero_add]
    ring
  rw [hval]
  exact ((h₁.add h₂).add h₃).add h₄

end Prime

/-- **The completed part is proportional to `R`.** -/
theorem rowLocalSum_sub_uncompleted (Q R ηp X Y V ρ : ℂ) (hR : 1 - R ≠ 0) :
    rowLocalSum Q R ηp X Y V ρ - rowLocalSum Q 0 ηp X Y V ρ =
      R * (1 - R)⁻¹ * ((1 - Q⁻¹) * (1 - V)⁻¹ + ρ * Y - ηp * ρ⁻¹ * X -
        ηp * (Q - 1) * X * Y * V * (1 - V)⁻¹) := by
  unfold rowLocalSum
  field_simp
  ring

/-- **The uncompleted principal correction.** At `ρ = 1`, `Y = V = Q⁻¹`, `X = Q^{−s}`, the
uncompleted local series times `(1 − V)(1 − Y)/(1 − ηX)` is the principal local factor with
phase `0`. -/
theorem uncompleted_principal_factor {Q : ℝ} (hQ : 1 < Q) (ηp s : ℂ)
    (hD : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0) :
    rowLocalSum (Q : ℂ) 0 ηp ((Q : ℂ) ^ (-s)) (Q : ℂ)⁻¹ (Q : ℂ)⁻¹ 1 *
        ((1 - (Q : ℂ)⁻¹) * (1 - (Q : ℂ)⁻¹)) / (1 - ηp * (Q : ℂ) ^ (-s)) =
      principalLocalFactor Q 0 ηp s := by
  have hQ0 : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hQ1 : (Q : ℂ) - 1 ≠ 0 := by
    intro h
    have : ((Q - 1 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have := ofReal_eq_zero.mp this
    linarith
  have hq : 1 - (Q : ℂ)⁻¹ ≠ 0 := by
    have h : 1 - (Q : ℂ)⁻¹ = ((Q : ℂ) - 1) / Q := by field_simp
    rw [h]
    exact div_ne_zero hQ1 hQ0
  unfold rowLocalSum principalLocalFactor
  simp only [zero_mul, sub_zero, inv_one, one_mul, mul_one, zero_add]
  have hD' : 1 - ηp * (Q : ℂ) ^ (-s) ≠ 0 := hD
  field_simp
  ring

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **No wall without completion.** For `σ > ½` there is `N₀` such that, whenever `S` contains
every prime of norm `≤ N₀`, the principal correction with phase `0` (the uncompleted probe) is
holomorphic and within `½` of one on `Re s > σ`, for all character values in the unit disc. -/
theorem exists_uncompletedCorrection_cutoff {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ η : HeightOneSpectrum (𝓞 K) → ℂ, (∀ v, ‖η v‖ ≤ 1) →
        DifferentiableOn ℂ (principalCorrection (fun _ => 0) η S) {s : ℂ | σ < s.re} ∧
          ∀ s : ℂ, σ < s.re → ‖principalCorrection (fun _ => 0) η S s - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_regularCorrection_cutoff (K := K) hσ
  refine ⟨N₀, hN₀, fun S hS η hη => ?_⟩
  have heq : principalCorrection (fun _ => 0) η S = regularCorrection (fun _ => 0) η S := by
    funext s
    have hloc : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
        principalLocalFactor (primeNorm v.1) 0 (η v.1) s =
          regularLocalFactor (primeNorm v.1) 0 (η v.1) s := fun v => by
      rw [principalLocalFactor_eq_phase_mul]
      simp [phaseLocalFactor]
    unfold principalCorrection regularCorrection
    exact tprod_congr hloc
  rw [heq]
  exact hcut S hS (fun _ => 0) η (fun _ => by simp) hη

end NumberField

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
