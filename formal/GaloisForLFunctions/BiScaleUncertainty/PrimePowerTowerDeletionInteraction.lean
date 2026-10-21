import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPriceAdditivity
import GaloisForLFunctions.BiScaleUncertainty.SignedPowerBathtub

/-!
# Deletion prices interact inside a tower: `log 2` and `log 4`

Across towers the deletion prices add (`PrimePowerDeletionPriceAdditivity`). Inside one tower they
do not. Delete a prime power `m` together with its square `m²` from the prime-power blind cone, and
put `s = √(1 + 8m)`.

**Theorem** (`isLeast_deletionDeviations₂_sq`, `isGreatest_deletionDeviations₂_sq`). On the
combinations blind at every prime power except `m` and `m²`, the exact range of `(A − W)/‖c‖²` is

`[−Λ(m)(s − 1)/(2m), Λ(m)(s + 1)/(2m)]`.

For `m = 2` this is `[−(√17 − 1)/4 · log 2, (√17 + 1)/4 · log 2]`. The single prices are `log 2/√2`
for `log 2` and `log 2/2` for `log 4`. The joint loss `(√17 − 1)/4 · log 2` is strictly less than
their sum and strictly more than the price of `log 2` alone
(`deletion_two_four_lt_sum`, `deletion_two_lt_deletion_two_four`): once `log 2` is deleted,
deleting `log 4` costs only `((√17 − 1)/4 − 1/√2) log 2 > 0`. The gain side is super-additive.

**Mechanism.**
* (`trigPoly_nonneg_of_cos_finite`, finite-band phase positivity) If the cosine moments of a
  nonnegative density vanish beyond frequency `J₀`, the trigonometric polynomial
  `∫G + 2Σ_{n ≤ J₀} c_n cos(nz)` built from its free moments is nonnegative. With `m^k`, `k ≥ 3`,
  blind this reads `‖c‖² + √m L_m cos θ + m L_{m²} cos 2θ ≥ 0` for every `θ`
  (`massOf_add_tower_nonneg`).
* Evaluating at the single angle `cos θ = ∓1/(λ√m)` gives both bounds; `λ` solves
  `λ²m ∓ λ − 2 = 0`.
* The bounds are attained by the narrow triples `h(u) + βh(u − log m) + h(u − 2 log m)` with
  `β = (±s − 1)/(2√m)`, the symmetric eigenvector of the degree-two Fejér–Riesz problem.

Both `L_m` and `L_{m²}` cannot be made extreme together: `cos θ ≈ −1` forces `cos 2θ ≈ 1`. In the
phase of one tower the square of a node is its second harmonic, so the two prices share one circle.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Finite-band phase positivity -/

/-- **Finite-band phase positivity.** If the cosine moments of a nonnegative density `G` vanish at
every `nℓ` with `n > J₀`, the trigonometric polynomial of its free moments is nonnegative. -/
theorem trigPoly_nonneg_of_cos_finite {G : ℝ → ℝ} (hGc : Continuous G) (hG0 : ∀ r, 0 ≤ G r)
    (hGi : Integrable G) {ℓ : ℝ} (J₀ : ℕ)
    (hcos : ∀ n : ℕ, J₀ < n → ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = 0)
    (z : AddCircle (2 * π)) :
    0 ≤ (∫ r, G r) + 2 * ∑ n ∈ Finset.Icc 1 J₀,
      (∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ))) * circleCos n z := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∫ r, G r := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n : ℕ => ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) :=
    ⟨_, rfl⟩
  have hcn : ∀ n : ℕ, ∫ r, G r * Real.cos (r * ((n : ℝ) * ℓ)) = c n := fun n => by rw [hc]
  simp_rw [hcn, ← hA] at hcos ⊢
  obtain ⟨D, hD⟩ : ∃ D : AddCircle (2 * π) → ℝ,
      D = fun z => A + 2 * ∑ n ∈ Finset.Icc 1 J₀, c n * circleCos n z := ⟨_, rfl⟩
  have hDc : Continuous D := by
    rw [hD]
    exact continuous_const.add (continuous_const.mul
      (continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_circleCos n)))
  obtain ⟨P, hPdef⟩ : ∃ P : AddCircle (2 * π) → ℝ, P = fun z => max 0 (-D z) := ⟨_, rfl⟩
  have hPc : Continuous P := hPdef ▸ continuous_const.max hDc.neg
  have hPeven : ∀ z, P (-z) = P z := fun z => by simp only [hPdef, hD, circleCos_neg]
  have hid := integral_mul_periodic_eq_of_cos_finite hGc hG0 hGi J₀
    (fun n hn => by rw [hcn]; exact hcos n hn) hPc hPeven
  simp_rw [hcn, ← hA] at hid
  have hL : 0 ≤ ∫ r, G r * P (phase ℓ r) :=
    integral_nonneg fun r => mul_nonneg (hG0 r) (by rw [hPdef]; exact le_max_left _ _)
  have hint : ∀ f : AddCircle (2 * π) → ℝ, Continuous f →
      Integrable f (AddCircle.haarAddCircle (T := 2 * π)) := fun f hf =>
    (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).integrable _
  have hR : A * (∫ z, P z ∂AddCircle.haarAddCircle) +
      2 * ∑ n ∈ Finset.Icc 1 J₀, c n * ∫ z, P z * circleCos n z ∂AddCircle.haarAddCircle =
      -∫ z, P z ^ 2 ∂AddCircle.haarAddCircle := by
    have e : ∀ z, A * P z + 2 * ∑ n ∈ Finset.Icc 1 J₀, c n * (P z * circleCos n z) = -P z ^ 2 := by
      intro z
      have hPD : P z * D z = -P z ^ 2 := by
        simp only [hPdef]
        rcases le_total 0 (D z) with h | h
        · rw [max_eq_left (by linarith)]; ring
        · rw [max_eq_right (by linarith)]; ring
      rw [← hPD, hD]
      simp only [Finset.mul_sum]
      ring_nf
      rw [Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => by ring
    have i1 : Integrable (fun z => A * P z) (AddCircle.haarAddCircle (T := 2 * π)) :=
      (hint _ hPc).const_mul A
    have i3 : ∀ n : ℕ, Integrable (fun z => c n * (P z * circleCos n z))
        (AddCircle.haarAddCircle (T := 2 * π)) := fun n =>
      (hint _ (hPc.mul (continuous_circleCos n))).const_mul (c n)
    have i2 : Integrable (fun z => 2 * ∑ n ∈ Finset.Icc 1 J₀, c n * (P z * circleCos n z))
        (AddCircle.haarAddCircle (T := 2 * π)) :=
      (integrable_finsetSum _ fun n _ => i3 n).const_mul 2
    have hsplit : ∫ z, (A * P z + 2 * ∑ n ∈ Finset.Icc 1 J₀, c n * (P z * circleCos n z))
          ∂AddCircle.haarAddCircle =
        A * (∫ z, P z ∂AddCircle.haarAddCircle) +
          2 * ∑ n ∈ Finset.Icc 1 J₀, c n * ∫ z, P z * circleCos n z ∂AddCircle.haarAddCircle := by
      rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun n _ => i3 n]
      simp only [integral_const_mul]
    rw [← hsplit, integral_congr_ae (Filter.Eventually.of_forall e), integral_neg]
  rw [hid] at hL
  have hsq : ∫ z, P z ^ 2 ∂AddCircle.haarAddCircle = 0 :=
    le_antisymm (by linarith) (integral_nonneg fun z => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (P z))
    (hint _ ((continuous_pow 2).comp hPc))).mp hsq
  have hall := (Continuous.ae_eq_iff_eq (AddCircle.haarAddCircle (T := 2 * π))
    ((continuous_pow 2).comp hPc) continuous_const).mp hae
  have h : P z ^ 2 = 0 := congrFun hall z
  have hP0 : P z = 0 := (pow_eq_zero_iff two_ne_zero).mp h
  have : -D z ≤ P z := by rw [hPdef]; exact le_max_right _ _
  have hDz : D z = A + 2 * ∑ n ∈ Finset.Icc 1 J₀, c n * circleCos n z := by rw [hD]
  linarith

/-! ### 2. The tower inequality for a node and its square -/

/-- The powers `m^k`, `k ≥ 3`, of a prime power avoid `m` and `m²`. -/
theorem pow_mem_primePowerNodes_diff_sq {m : ℕ} (hm : IsPrimePow m) {k : ℕ} (hk : 3 ≤ k) :
    m ^ k ∈ primePowerNodes \ {m, m ^ 2} := by
  have h2 := hm.two_le
  refine ⟨hm.pow (by omega), ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · intro h
    have : m ^ 2 ≤ m ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  · intro h
    have := Nat.pow_right_injective h2 h
    omega

/-- **The tower inequality.** On the cone blind at every prime power except `m`, `m²`:
`‖c‖² + √m L_m cos θ + m L_{m²} cos 2θ ≥ 0` for every `θ`. -/
theorem massOf_add_tower_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m : ℕ}
    (hm : IsPrimePow m) (hb : BlindOn (primePowerNodes \ {m, m ^ 2}) c) (θ : ℝ) :
    0 ≤ massOf c + Real.sqrt m * nodeVector c ⟨m, hm.two_le⟩ * Real.cos θ +
      (m : ℝ) * nodeVector c ⟨m ^ 2, by nlinarith [hm.two_le]⟩ * Real.cos (2 * θ) := by
  have h2 := hm.two_le
  have hcos : ∀ n : ℕ, 2 < n →
      ∫ r, combinationSpectralDensity c r * Real.cos (r * ((n : ℝ) * Real.log m)) = 0 := by
    intro n hn
    rw [integral_combinationSpectralDensity_mul_cos_pow c h2 (by omega)]
    rw [hb _ (pow_mem_primePowerNodes_diff_sq hm hn), mul_zero]
  have h := trigPoly_nonneg_of_cos_finite (continuous_combinationSpectralDensity c)
    (combinationSpectralDensity_nonneg hc) (integrable_combinationSpectralDensity c) 2 hcos
    (θ : AddCircle (2 * π))
  have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hIcc, Finset.sum_pair (by norm_num), circleCos_coe, circleCos_coe,
    integral_combinationSpectralDensity] at h
  have e1 : (fun r => combinationSpectralDensity c r * Real.cos (r * (((1 : ℕ) : ℝ) * Real.log m))) =
      fun r => combinationSpectralDensity c r * Real.cos (r * Real.log m) := by
    funext r; rw [Nat.cast_one, one_mul]
  have e2 : (fun r => combinationSpectralDensity c r * Real.cos (r * (((2 : ℕ) : ℝ) * Real.log m))) =
      fun r => combinationSpectralDensity c r * Real.cos (r * Real.log ((m ^ 2 : ℕ) : ℝ)) := by
    funext r; rw [Nat.cast_pow, Real.log_pow]
  rw [e1, e2, integral_combinationSpectralDensity_mul_cos_log c h2,
    integral_combinationSpectralDensity_mul_cos_log c (by nlinarith : 2 ≤ m ^ 2)] at h
  have hs : Real.sqrt ((m ^ 2 : ℕ) : ℝ) = m := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
  rw [hs] at h
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h
  have hπ := Real.pi_pos
  nlinarith

/-! ### 3. The two bounds from one angle each -/

/-- **The tower bounds.** If `M + √m A cos θ + m B cos 2θ ≥ 0` for every `θ`, then with
`s = √(1 + 8m)`: `A + B ≤ (s + 1)/(2m) · M` and `−(A + B) ≤ (s − 1)/(2m) · M`. The angles are
`cos θ = −2√m/(s + 1)` and `cos θ = 2√m/(s − 1)`, where `m(2cos²θ − 1) = √m cos θ`. -/
theorem tower_bounds {M A B m : ℝ} (hm : 2 ≤ m)
    (h : ∀ θ : ℝ, 0 ≤ M + Real.sqrt m * A * Real.cos θ + m * B * Real.cos (2 * θ)) :
    A + B ≤ (Real.sqrt (1 + 8 * m) + 1) / (2 * m) * M ∧
      -(A + B) ≤ (Real.sqrt (1 + 8 * m) - 1) / (2 * m) * M := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 + 8 * m) := ⟨_, rfl⟩
  rw [← hs]
  have hs2 : s ^ 2 = 1 + 8 * m := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt m := ⟨_, rfl⟩
  rw [← hq] at h
  have hq2 : q ^ 2 = m := by rw [hq]; exact Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hq1 : 1 < q := by nlinarith
  have hsq : 1 + 2 * q < s := by nlinarith
  constructor
  · have hx1 : -1 ≤ -(2 * q) / (s + 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hx2 : -(2 * q) / (s + 1) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hθ := h (Real.arccos (-(2 * q) / (s + 1)))
    rw [Real.cos_two_mul, Real.cos_arccos hx1 hx2] at hθ
    have key : 0 ≤ (s + 1) * M - 2 * m * (A + B) := by
      have e : (s + 1) * (M + q * A * (-(2 * q) / (s + 1)) +
          m * B * (2 * (-(2 * q) / (s + 1)) ^ 2 - 1)) = (s + 1) * M - 2 * m * (A + B) := by
        field_simp
        linear_combination (-2 * (s + 1) * A + 8 * m * B) * hq2 - m * B * hs2
      rw [← e]
      exact mul_nonneg (by linarith) hθ
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  · have hx1 : -1 ≤ 2 * q / (s - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hx2 : 2 * q / (s - 1) ≤ 1 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hθ := h (Real.arccos (2 * q / (s - 1)))
    rw [Real.cos_two_mul, Real.cos_arccos hx1 hx2] at hθ
    have key : 0 ≤ (s - 1) * M + 2 * m * (A + B) := by
      have e : (s - 1) * (M + q * A * (2 * q / (s - 1)) +
          m * B * (2 * (2 * q / (s - 1)) ^ 2 - 1)) = (s - 1) * M + 2 * m * (A + B) := by
        have hne : s - 1 ≠ 0 := by linarith
        field_simp
        linear_combination (2 * (s - 1) * A + 8 * m * B) * hq2 - m * B * hs2
      rw [← e]
      exact mul_nonneg (by linarith) hθ
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith

/-! ### 4. The narrow triple -/

/-- The narrow triple `b(u) + β b(u − log m) + b(u − 2 log m)` with the bump of index `m·m`. -/
def tripleTest (m : ℕ) (β : ℝ) (u : ℝ) : ℂ :=
  narrowBumpC (m * m) u + (β : ℂ) * narrowBumpC (m * m) (u - Real.log m) +
    narrowBumpC (m * m) (u - 2 * Real.log m)

theorem tripleTest_eq_sum (m : ℕ) (β : ℝ) : tripleTest m β = fun u => ∑ a ∈ Finset.range 3,
    (if a = 1 then (β : ℂ) else 1) * narrowBumpC (m * m) (u - (a : ℝ) * Real.log m) := by
  funext u
  simp [tripleTest, Finset.sum_range_succ]

theorem contDiff_tripleTest (m : ℕ) (β : ℝ) : ContDiff ℝ 2 (tripleTest m β) := by
  have hb : ContDiff ℝ 2 (narrowBumpC (m * m)) := (contDiff_narrowBumpC _).of_le (by norm_cast)
  exact (hb.add (contDiff_const.mul (hb.comp (contDiff_id.sub contDiff_const)))).add
    (hb.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_tripleTest (m : ℕ) (β : ℝ) : HasCompactSupport (tripleTest m β) := by
  have hb := hasCompactSupport_narrowBumpC (m * m)
  exact (hb.add ((hb.comp_homeomorph (Homeomorph.subRight (Real.log m))).mul_left)).add
    (hb.comp_homeomorph (Homeomorph.subRight (2 * Real.log m)))

/-- The narrow triple as a Weil test. -/
def tripleTestFn (m : ℕ) (β : ℝ) : WeilTestFn :=
  ⟨tripleTest m β, contDiff_tripleTest m β, hasCompactSupport_tripleTest m β⟩

/-- The autocorrelation of the triple. -/
theorem weilTest_tripleTest (m : ℕ) (β y : ℝ) :
    EF.weilTest (tripleTest m β) (tripleTest m β) y =
      ((2 + β ^ 2 : ℝ) : ℂ) * EF.weilTest (narrowBumpC (m * m)) (narrowBumpC (m * m)) y +
        (2 * β : ℝ) * (EF.weilTest (narrowBumpC (m * m)) (narrowBumpC (m * m)) (y + Real.log m) +
          EF.weilTest (narrowBumpC (m * m)) (narrowBumpC (m * m)) (y - Real.log m)) +
        EF.weilTest (narrowBumpC (m * m)) (narrowBumpC (m * m)) (y + 2 * Real.log m) +
        EF.weilTest (narrowBumpC (m * m)) (narrowBumpC (m * m)) (y - 2 * Real.log m) := by
  rw [tripleTest_eq_sum, weilTest_sum_translates (contDiff_narrowBumpC _).continuous
    (hasCompactSupport_narrowBumpC _)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, sub_zero, add_zero, Complex.conj_ofReal, map_one, mul_one, one_mul,
    show (0 : ℕ) ≠ 1 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true, if_false]
  have e1 : y - Real.log m + ((2 : ℕ) : ℝ) * Real.log m = y + Real.log m := by push_cast; ring
  have e2 : y - ((2 : ℕ) : ℝ) * Real.log m + Real.log m = y - Real.log m := by push_cast; ring
  have e3 : y - Real.log m + Real.log m = y := by ring
  have e4 : y - ((2 : ℕ) : ℝ) * Real.log m + ((2 : ℕ) : ℝ) * Real.log m = y := by ring
  have e5 : y + ((2 : ℕ) : ℝ) * Real.log m = y + 2 * Real.log m := by push_cast; ring
  have e6 : y - ((2 : ℕ) : ℝ) * Real.log m = y - 2 * Real.log m := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  push_cast
  ring

section TripleNodes

variable {m : ℕ} (hm : 2 ≤ m) {β : ℝ}

omit hm in
theorem log_two_le_abs_of (m : ℕ) {t : ℝ} (ht : Real.log 2 ≤ t ∨ t ≤ -Real.log 2) :
    pairRadius m m < |t| := by
  rcases ht with ht | ht
  · exact pairRadius_lt_of_le m m ht
  · exact pairRadius_lt_of_le_neg m m ht

include hm in
/-- At the origin the triple is `(2 + β²) ∫ h²`. -/
theorem weilTest_tripleTest_zero :
    EF.weilTest (tripleTest m β) (tripleTest m β) 0 =
      (((2 + β ^ 2) * ∫ t, (narrowBump (m * m) t) ^ 2 : ℝ) : ℂ) := by
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  rw [weilTest_tripleTest, zero_add, zero_sub, zero_add, zero_sub, weilTest_narrowBumpC_zero,
    narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl ha)),
    narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
    narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
    narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith)))]
  push_cast; ring

include hm in
/-- At `±log m` the triple is `2β ∫ h²`. -/
theorem weilTest_tripleTest_log (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (tripleTest m β) (tripleTest m β) (s * Real.log m) =
      ((2 * β * ∫ t, (narrowBump (m * m) t) ^ 2 : ℝ) : ℂ) := by
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  rw [weilTest_tripleTest]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl ha)),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith)))]
    push_cast; ring
  · rw [neg_one_mul, neg_add_cancel, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith)))]
    push_cast; ring

include hm in
/-- At `±2 log m` the triple is `∫ h²`. -/
theorem weilTest_tripleTest_two_log (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (tripleTest m β) (tripleTest m β) (s * (2 * Real.log m)) =
      ((∫ t, (narrowBump (m * m) t) ^ 2 : ℝ) : ℂ) := by
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  rw [weilTest_tripleTest]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith)))]
    push_cast; ring
  · rw [neg_one_mul, neg_add_cancel, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith)))]
    push_cast; ring

include hm in
/-- The triple vanishes at `±log n` for every `n ≥ 2` other than `m`, `m²`. -/
theorem weilTest_tripleTest_log_eq_zero {n : ℕ} (hn : 2 ≤ n) (hn₁ : n ≠ m) (hn₂ : n ≠ m ^ 2)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (tripleTest m β) (tripleTest m β) (s * Real.log n) = 0 := by
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  have g1 : pairRadius m m < |Real.log n - Real.log m| :=
    pairRadius_lt_abs_log_sub (by omega) (by omega) (Nat.le_mul_of_pos_left _ (by omega)) hn₁
  have g2 : pairRadius m m < |Real.log n - 2 * Real.log m| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m) (m₂ := m) (a := n) (b := m * m) (by omega)
      (by nlinarith) le_rfl (by rwa [← sq])
    rwa [log_natCast_mul (by omega) (by omega), ← two_mul] at this
  rw [weilTest_tripleTest]
  rcases hs with rfl | rfl
  · rw [one_mul, narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl hL)),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))), narrowCorr_eq_zero g1,
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inl (by linarith))), narrowCorr_eq_zero g2]
    ring
  · rw [neg_one_mul, narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (lt_abs_of_eq_or_eq_neg g1 (Or.inr (by ring))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith))),
      narrowCorr_eq_zero (lt_abs_of_eq_or_eq_neg g2 (Or.inr (by ring))),
      narrowCorr_eq_zero (log_two_le_abs_of m (Or.inr (by linarith)))]
    ring

end TripleNodes

/-! ### 5. The exact range for a node and its square -/

section TripleRange

variable {m : ℕ} (hm : 2 ≤ m) {β : ℝ}

include hm in
theorem massOf_single_tripleTestFn :
    massOf (Finsupp.single (tripleTestFn m β) 1) = (2 + β ^ 2) * ∫ t, (narrowBump (m * m) t) ^ 2 := by
  have hk := weilTest_tripleTest_zero (β := β) hm
  rw [RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact_mod_cast hk

include hm in
theorem nodeVector_single_tripleTestFn_log :
    nodeVector (Finsupp.single (tripleTestFn m β) 1) ⟨m, hm⟩ =
      4 * β * (∫ t, (narrowBump (m * m) t) ^ 2) / Real.sqrt m := by
  have e1 := weilTest_tripleTest_log (β := β) hm 1 (Or.inl rfl)
  have e2 := weilTest_tripleTest_log (β := β) hm (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [nodeVector_single_test, logVector_apply]
  change logValue (tripleTest m β) m = _
  rw [logValue, e1, e2, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

include hm in
theorem nodeVector_single_tripleTestFn_sq :
    nodeVector (Finsupp.single (tripleTestFn m β) 1) ⟨m ^ 2, by nlinarith⟩ =
      2 * (∫ t, (narrowBump (m * m) t) ^ 2) / m := by
  have e1 := weilTest_tripleTest_two_log (β := β) hm 1 (Or.inl rfl)
  have e2 := weilTest_tripleTest_two_log (β := β) hm (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [nodeVector_single_test, logVector_apply]
  change logValue (tripleTest m β) (m ^ 2) = _
  have hl : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log m := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hs : Real.sqrt ((m ^ 2 : ℕ) : ℝ) = m := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
  rw [logValue, hl, hs, e1, e2, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

include hm in
theorem blindOn_single_tripleTestFn :
    BlindOn (primePowerNodes \ {m, m ^ 2}) (Finsupp.single (tripleTestFn m β) 1) := by
  intro j hj
  obtain ⟨-, hne⟩ := hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  rw [nodeVector_single_test, logVector_apply]
  change logValue (tripleTest m β) j = 0
  have e1 := weilTest_tripleTest_log_eq_zero (β := β) hm j.2 hne.1 hne.2 1 (Or.inl rfl)
  have e2 := weilTest_tripleTest_log_eq_zero (β := β) hm j.2 hne.1 hne.2 (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [logValue, e1, e2]
  simp

end TripleRange

theorem vonMangoldt_sq (m : ℕ) :
    (ArithmeticFunction.vonMangoldt (m ^ 2) : ℝ) = ArithmeticFunction.vonMangoldt m := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]

/-- The deviation of the narrow triple: `Λ(m)(4β/√m + 2/m)/(2 + β²)`. -/
theorem deviation_single_tripleTestFn {m : ℕ} (hm : 2 ≤ m) (β : ℝ) :
    ArithmeticFunction.vonMangoldt m * ((4 * β / Real.sqrt m + 2 / m) / (2 + β ^ 2)) ∈
      deletionDeviations₂ m (m ^ 2) := by
  classical
  have hm2 : m ≠ m ^ 2 := by intro h; nlinarith
  have hI := integral_narrowBump_sq_pos (m * m)
  have hpos : 0 < massOf (Finsupp.single (tripleTestFn m β) 1) := by
    rw [massOf_single_tripleTestFn hm]; positivity
  refine ⟨_, fun f => ?_, blindOn_single_tripleTestFn hm, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [nodeArchEnergy_eq_weilEnergy_add_two hm (by nlinarith) hm2 (blindOn_single_tripleTestFn hm),
      add_sub_cancel_left, vonMangoldt_sq, nodeVector_single_tripleTestFn_log hm,
      nodeVector_single_tripleTestFn_sq hm, massOf_single_tripleTestFn hm]
    have hq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
    have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    field_simp

/-- The two extremal values of the triple deviation, from the eigenvector `β = (±s − 1)/(2√m)`. -/
theorem triple_deviation_values {m : ℝ} (hm : 2 ≤ m) :
    (4 * ((Real.sqrt (1 + 8 * m) - 1) / (2 * Real.sqrt m)) / Real.sqrt m + 2 / m) /
        (2 + ((Real.sqrt (1 + 8 * m) - 1) / (2 * Real.sqrt m)) ^ 2) =
      (Real.sqrt (1 + 8 * m) + 1) / (2 * m) ∧
    (4 * (-(Real.sqrt (1 + 8 * m) + 1) / (2 * Real.sqrt m)) / Real.sqrt m + 2 / m) /
        (2 + (-(Real.sqrt (1 + 8 * m) + 1) / (2 * Real.sqrt m)) ^ 2) =
      -((Real.sqrt (1 + 8 * m) - 1) / (2 * m)) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 + 8 * m) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt m := ⟨_, rfl⟩
  rw [← hs, ← hq]
  have hs2 : s ^ 2 = 1 + 8 * m := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hq2 : q ^ 2 = m := by rw [hq]; exact Real.sq_sqrt (by linarith)
  have hq0 : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr (by linarith)
  have hs1 : 1 < s := by nlinarith
  constructor
  · rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    linear_combination (1 - s) * hs2 + (8 - 8 * s) * hq2
  · rw [div_eq_iff (by positivity)]
    field_simp
    linear_combination (1 + s) * hs2 + (8 + 8 * s) * hq2

/-- **The loss side of `{m, m²}`.** The least normalized deviation on the cone blind at every prime
power except `m` and `m²` is `−Λ(m)(√(1 + 8m) − 1)/(2m)`. -/
theorem isLeast_deletionDeviations₂_sq {m : ℕ} (hm : IsPrimePow m) :
    IsLeast (deletionDeviations₂ m (m ^ 2))
      (-(ArithmeticFunction.vonMangoldt m * ((Real.sqrt (1 + 8 * (m : ℝ)) - 1) / (2 * m)))) := by
  have h2 := hm.two_le
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h2
  constructor
  · have h := deviation_single_tripleTestFn h2 (-(Real.sqrt (1 + 8 * (m : ℝ)) + 1) / (2 * Real.sqrt m))
    rwa [(triple_deviation_values hm').2, mul_neg] at h
  · rintro x ⟨c, hc, hb, hpos, rfl⟩
    have hm2 : m ≠ m ^ 2 := by intro h; nlinarith
    rw [nodeArchEnergy_eq_weilEnergy_add_two h2 (by nlinarith) hm2 hb, add_sub_cancel_left,
      vonMangoldt_sq]
    have hT := (tower_bounds hm' (massOf_add_tower_nonneg hc hm hb)).2
    have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    rw [le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hT hΛ]

/-- **The gain side of `{m, m²}`.** The greatest normalized deviation is `Λ(m)(√(1 + 8m) + 1)/(2m)`. -/
theorem isGreatest_deletionDeviations₂_sq {m : ℕ} (hm : IsPrimePow m) :
    IsGreatest (deletionDeviations₂ m (m ^ 2))
      (ArithmeticFunction.vonMangoldt m * ((Real.sqrt (1 + 8 * (m : ℝ)) + 1) / (2 * m))) := by
  have h2 := hm.two_le
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h2
  constructor
  · have h := deviation_single_tripleTestFn h2 ((Real.sqrt (1 + 8 * (m : ℝ)) - 1) / (2 * Real.sqrt m))
    rwa [(triple_deviation_values hm').1] at h
  · rintro x ⟨c, hc, hb, hpos, rfl⟩
    have hm2 : m ≠ m ^ 2 := by intro h; nlinarith
    rw [nodeArchEnergy_eq_weilEnergy_add_two h2 (by nlinarith) hm2 hb, add_sub_cancel_left,
      vonMangoldt_sq]
    have hT := (tower_bounds hm' (massOf_add_tower_nonneg hc hm hb)).1
    have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    rw [div_le_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left hT hΛ]

/-- Deleting `log 2` and `log 4` together costs `(√17 − 1)/4 · log 2`. -/
theorem isLeast_deletionDeviations₂_two_four :
    IsLeast (deletionDeviations₂ 2 4) (-((Real.sqrt 17 - 1) / 4 * Real.log 2)) := by
  have h := isLeast_deletionDeviations₂_sq (m := 2) Nat.prime_two.isPrimePow
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h
  have e : (2 : ℕ) ^ 2 = 4 := by norm_num
  rw [e] at h
  convert h using 2
  push_cast
  ring_nf

/-- **Sub-additivity in one tower.** The joint loss of `{log 2, log 4}` is strictly less than the sum
of the single losses `log 2/√2` and `log 2/2`. -/
theorem deletion_two_four_lt_sum :
    (Real.sqrt 17 - 1) / 4 * Real.log 2 < Real.log 2 / Real.sqrt 2 + Real.log 2 / 2 := by
  have hL := Real.log_pos one_lt_two
  have h17 : Real.sqrt 17 < 21 / 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : 7 / 10 < 1 / Real.sqrt 2 := by
    rw [lt_one_div (by norm_num) (Real.sqrt_pos.mpr (by norm_num)), Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [div_eq_mul_one_div (Real.log 2) (Real.sqrt 2)]
  nlinarith

/-- **`log 4` keeps a positive marginal price.** Once `log 2` is deleted, deleting `log 4` as well
still costs `((√17 − 1)/4 − 1/√2) log 2 > 0`. -/
theorem deletion_two_lt_deletion_two_four :
    Real.log 2 / Real.sqrt 2 < (Real.sqrt 17 - 1) / 4 * Real.log 2 := by
  have hL := Real.log_pos one_lt_two
  have h17 : 103 / 25 < Real.sqrt 17 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : 1 / Real.sqrt 2 < 71 / 100 := by
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    have : 141 / 100 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
    nlinarith
  rw [div_eq_mul_one_div (Real.log 2) (Real.sqrt 2)]
  nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty
