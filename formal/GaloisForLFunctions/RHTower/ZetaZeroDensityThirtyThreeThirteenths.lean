import GaloisForLFunctions.RHTower.ZetaZeroDensityEdgeRanges
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitGlobalZeroCount
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The zero-density estimate with exponent `33/13`

For all large `T` and every `σ ∈ [1/2, 1]`,

`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^B T^{(33/13)(1 - σ)}`,

counting zeros with multiplicity.  Two estimates are combined.

* On `σ ≤ 7/10` and `σ ≥ 26/33` the large-value class count with window `[T^{33/52}, T^{33/26}]`
  (`exists_zeroHeightBox_ncard_le_edge`).
* On `[7/10, 26/33]` the Gabriel interpolation count of the residue unit `(s - 1)ζ(s)`
  (`exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformPolylog`), whose exponent
  `E(σ) = (1-σ)(3183/1000 + (9009/50000)(1-σ))/(1 + (1271/1000)(1-σ))` is at most
  `(33/13)(1 - σ)` exactly when `1 - σ ≥ 0.2116…`, and `1 - 26/33 = 7/33 = 0.2121…`.

The bridge between the two counts is the fibre bound: the zero copies over one zero number its
multiplicity, which in the open strip is the analytic order of the residue unit.
-/

namespace RHTower

noncomputable section

open Complex Finset Filter RHTower.Sieve

/-- The number of copies of a Xi zero is its analytic order. -/
theorem toNat_divisor_xi_eq_analyticOrderAt (ρ : XiDivisorSupport) :
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) =
      (analyticOrderAt xi (ρ : ℂ)).toNat := by
  rw [MeromorphicOn.divisor_apply xi_analyticOnNhd_univ.meromorphicOn (Set.mem_univ (ρ : ℂ)),
    (xi_analyticOnNhd_univ (ρ : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq]
  have hcoe : ((((analyticOrderAt xi (ρ : ℂ)).toNat : ℕ) : ℕ∞)) =
      analyticOrderAt xi (ρ : ℂ) :=
    ENat.coe_toNat (xi_orderAt_ne_top (ρ : ℂ))
  rw [← hcoe]
  simp

/-- A zero copy is a zero of the residue unit. -/
theorem zetaResidueUnit_eq_zero_of_xiZeroCopy (q : XiZeroCopy) : zetaResidueUnit (q.1 : ℂ) = 0 := by
  have hne : (q.1 : ℂ) ≠ 1 := by
    intro h
    have := xiZeroCopy_re_lt_one q
    rw [h, one_re] at this
    exact lt_irrefl _ this
  simp [zetaResidueUnit, Function.update_of_ne hne, riemannZeta_eq_zero_of_xiZeroCopy q]

/-- **The fibre bound.**  If `0 < c ≤ σ` and `2T ≤ H`, the box `σ ≤ Re ρ`, `T ≤ Im ρ ≤ 2T` has at
most as many zero copies as the multiplicity-weighted count of residue-unit zeros with `σ ≤ Re w` in the
rectangle `[c, 4] × [-H, H]`. -/
theorem ncard_zeroHeightBox_le_zetaLittlewoodZeroCountAbove {σ T c H : ℝ} (hc0 : 0 < c)
    (hcσ : c ≤ σ) (hT : 0 ≤ T) (hH : 2 * T ≤ H) :
    ((zeroHeightBox σ T).ncard : ℝ) ≤ zetaLittlewoodZeroCountAbove c 4 H σ := by
  classical
  unfold zetaLittlewoodZeroCountAbove
  set R := (zetaResidueUnitClosedRectangleZeros ((c : ℂ) + (-H : ℝ) * I)
    (((4 : ℝ) : ℂ) + H * I)).filter (fun w => σ ≤ w.re) with hR
  set Z := (zeroHeightBox_finite σ T).toFinset with hZ
  have hmaps : ∀ q ∈ Z, (q.1 : ℂ) ∈ R := by
    intro q hq
    rw [hZ, Set.Finite.mem_toFinset] at hq
    obtain ⟨hre, him1, him2⟩ := hq
    have hlt := xiZeroCopy_re_lt_one q
    rw [hR, Finset.mem_filter, mem_zetaResidueUnitClosedRectangleZeros]
    refine ⟨⟨?_, zetaResidueUnit_eq_zero_of_xiZeroCopy q⟩, hre⟩
    rw [Complex.mem_reProdIm]
    constructor
    · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero]
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · simp only [add_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one, zero_add]
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
  rw [Set.ncard_eq_toFinset_card _ (zeroHeightBox_finite σ T), ← hZ,
    Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  refine Finset.sum_le_sum fun w hw => ?_
  rcases (Z.filter (fun q => (q.1 : ℂ) = w)).eq_empty_or_nonempty with he | ⟨q₀, hq₀⟩
  · rw [he, card_empty, Nat.cast_zero]
    exact Nat.cast_nonneg _
  obtain ⟨ρ, k₀⟩ := q₀
  have hρw : (ρ : ℂ) = w := (Finset.mem_filter.mp hq₀).2
  have hsub : Z.filter (fun q => (q.1 : ℂ) = w) ⊆
      (Finset.univ : Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))))).map
        ⟨Sigma.mk ρ, sigma_mk_injective⟩ := by
    intro q hq
    obtain ⟨ρ', k'⟩ := q
    have hρ' : ρ' = ρ := Subtype.ext (by rw [(Finset.mem_filter.mp hq).2, hρw])
    subst hρ'
    simp
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin,
    toNat_divisor_xi_eq_analyticOrderAt] at hcard
  have hstrip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    ⟨xiZeroCopy_re_pos ⟨ρ, k₀⟩, xiZeroCopy_re_lt_one ⟨ρ, k₀⟩⟩
  rw [← analyticOrderAt_zetaResidueUnit_eq_xi_of_mem_strip hstrip, hρw] at hcard
  exact_mod_cast hcard

/-- The Gabriel exponent is at most `(33/13)(1 - σ)` for `σ ≤ 26/33`. -/
theorem inghamUniformGabrielConservativeExponent_le_thirtyThree_thirteenths {σ : ℝ}
    (hσ2 : σ ≤ 26 / 33) :
    inghamUniformGabrielConservativeExponent σ ≤ (33 / 13) * (1 - σ) := by
  have hd : 0 ≤ 1 - σ := by linarith
  have hdenpos : 0 < 1 + (1271 / 1000 : ℝ) * (1 - σ) := by positivity
  rw [inghamUniformGabrielConservativeExponent_eq (by linarith), div_le_iff₀ hdenpos]
  have hbr : 0 ≤ (33 / 13 : ℝ) * (1 + (1271 / 1000) * (1 - σ)) - 3183 / 1000
      - (9009 / 50000) * (1 - σ) := by linarith
  nlinarith [mul_nonneg hd hbr]

/-- The Gabriel exponent is nonnegative below `1`. -/
theorem inghamUniformGabrielConservativeExponent_nonneg {σ : ℝ} (hσ : σ ≤ 1) :
    0 ≤ inghamUniformGabrielConservativeExponent σ := by
  have hd : 0 ≤ 1 - σ := by linarith
  rw [inghamUniformGabrielConservativeExponent_eq hσ]
  positivity

/-- **The middle range.**  For all large `T` and every `σ ∈ [7/10, 26/33]`,
`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^{16} T^{(33/13)(1 - σ)}`. -/
theorem exists_zeroHeightBox_ncard_le_gabriel_middle :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 26 / 33 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ 16 * T ^ ((33 / 13) * (1 - σ)) := by
  obtain ⟨K, hK, hev⟩ := exists_eventually_zetaLittlewoodZeroCountAbove_le_uniformPolylog
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨3 ^ 18 * K, by positivity, max (X₀ : ℝ) 3, fun T hT σ hσ1 hσ2 => ?_⟩
  have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = ⌈2 * T⌉₊ + 2 := ⟨_, rfl⟩
  have hceil1 : 2 * T ≤ (⌈2 * T⌉₊ : ℝ) := Nat.le_ceil _
  have hceil2 : (⌈2 * T⌉₊ : ℝ) < 2 * T + 1 := Nat.ceil_lt_add_one (by linarith)
  have hXcast : (X : ℝ) = (⌈2 * T⌉₊ : ℝ) + 2 := by rw [hXdef]; push_cast; ring
  have hXX₀ : X₀ ≤ X := by
    have h1 : (X₀ : ℝ) ≤ X := by
      have := le_trans (le_max_left _ _) hT
      rw [hXcast]
      linarith
    exact_mod_cast h1
  have hcount := hX₀ X hXX₀ (sigma := σ) hσ1 (by linarith)
  have hc0 : 0 < inghamUniformGabrielCenter σ := by
    unfold inghamUniformGabrielCenter
    linarith
  have hcσ : inghamUniformGabrielCenter σ ≤ σ := by
    unfold inghamUniformGabrielCenter
    linarith
  have hbox := ncard_zeroHeightBox_le_zetaLittlewoodZeroCountAbove (σ := σ) (T := T)
    hc0 hcσ hT0.le (show 2 * T ≤ (X : ℝ) - 2 by rw [hXcast]; linarith)
  refine le_trans hbox (le_trans hcount ?_)
  -- the numerical comparison
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = inghamUniformGabrielConservativeExponent σ := ⟨_, rfl⟩
  rw [← hEdef]
  have hE0 : 0 ≤ E := hEdef ▸ inghamUniformGabrielConservativeExponent_nonneg (by linarith)
  have hEA : E ≤ (33 / 13) * (1 - σ) :=
    hEdef ▸ inghamUniformGabrielConservativeExponent_le_thirtyThree_thirteenths hσ2
  have hE1 : E ≤ 1 := by linarith
  have hX1 : (1 : ℝ) ≤ X := by rw [hXcast]; linarith
  have hX3T : (X : ℝ) ≤ 3 * T := by rw [hXcast]; linarith
  have hX0 : (0 : ℝ) < X := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + Real.log (X : ℝ) := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith [Real.log_nonneg hX1]
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hL3 : L ≤ 3 * (1 + Real.log T) := by
    have h1 : Real.log (X : ℝ) ≤ Real.log 3 + Real.log T := by
      rw [← Real.log_mul (by norm_num) hT0.ne']
      exact Real.log_le_log hX0 hX3T
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    rw [hLdef]
    linarith
  have hXE1 : 1 ≤ (X : ℝ) ^ E := Real.one_le_rpow hX1 hE0
  have hXE : (X : ℝ) ^ E ≤ 3 * T ^ ((33 / 13) * (1 - σ)) := by
    calc (X : ℝ) ^ E ≤ (3 * T) ^ E := Real.rpow_le_rpow hX0.le hX3T hE0
      _ = 3 ^ E * T ^ E := Real.mul_rpow (by norm_num) hT0.le
      _ ≤ 3 ^ (1 : ℝ) * T ^ ((33 / 13) * (1 - σ)) :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) hE1)
            (Real.rpow_le_rpow_of_exponent_le hT1 hEA) (Real.rpow_nonneg hT0.le _)
            (by positivity)
      _ = 3 * T ^ ((33 / 13) * (1 - σ)) := by rw [Real.rpow_one]
  have hL2 : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL1
  have hinner : 1 + (X : ℝ) ^ E * L ^ (2 : ℕ) + L ^ (2 : ℕ) ≤ 3 * ((X : ℝ) ^ E * L ^ (2 : ℕ)) := by
    have h1 : 1 ≤ (X : ℝ) ^ E * L ^ (2 : ℕ) := one_le_mul_of_one_le_of_one_le hXE1 hL2
    have h2 : L ^ (2 : ℕ) ≤ (X : ℝ) ^ E * L ^ (2 : ℕ) := le_mul_of_one_le_left (by positivity) hXE1
    linarith
  have hL16 : L ^ (16 : ℕ) ≤ 3 ^ 16 * (1 + Real.log T) ^ 16 := by
    calc L ^ (16 : ℕ) ≤ (3 * (1 + Real.log T)) ^ 16 := pow_le_pow_left₀ (by linarith) hL3 _
      _ = 3 ^ 16 * (1 + Real.log T) ^ 16 := by ring
  have hTA0 : 0 ≤ T ^ ((33 / 13) * (1 - σ)) := Real.rpow_nonneg hT0.le _
  calc K * L ^ (14 : ℕ) * (1 + (X : ℝ) ^ E * L ^ (2 : ℕ) + L ^ (2 : ℕ))
      ≤ K * L ^ (14 : ℕ) * (3 * ((X : ℝ) ^ E * L ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 3 * K * L ^ (16 : ℕ) * (X : ℝ) ^ E := by ring
    _ ≤ 3 * K * (3 ^ 16 * (1 + Real.log T) ^ 16) * (3 * T ^ ((33 / 13) * (1 - σ))) := by
        gcongr
    _ = 3 ^ 18 * K * (1 + Real.log T) ^ 16 * T ^ ((33 / 13) * (1 - σ)) := by ring

/-- **The zero-density estimate with exponent `33/13`.**  There are `D ≥ 0` and `T₀ ≥ 1` such that
for all `T ≥ T₀` and `σ ∈ [1/2, 1]`,
`#{ρ : σ ≤ Re ρ, T ≤ Im ρ ≤ 2T} ≤ D (1 + log T)^{E+4} T^{(33/13)(1 - σ)}`, with
`E = classCountLogExponent`. -/
theorem exists_zeroHeightBox_ncard_le_thirtyThree_thirteenths :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ (classCountLogExponent + 4) * T ^ ((33 / 13) * (1 - σ)) := by
  obtain ⟨T₁, hT₁⟩ := exists_zeroHeightBox_ncard_le_edge
  obtain ⟨Dm, hDm, T₂, hT₂⟩ := exists_zeroHeightBox_ncard_le_gabriel_middle
  have hD0 : 0 ≤ zeroDensityConstant := by
    unfold zeroDensityConstant classCountConstant
    positivity
  refine ⟨zeroDensityConstant + Dm, by positivity, max (max T₁ T₂) 1, le_max_right _ _,
    fun T hT σ hσ1 hσ2 => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hl : 1 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hTA0 : 0 ≤ T ^ ((33 / 13) * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  have hLB0 : 0 ≤ (1 + Real.log T) ^ (classCountLogExponent + 4) := by positivity
  by_cases hrange : σ ≤ 7 / 10 ∨ 26 / 33 ≤ σ
  · refine le_trans (hT₁ T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT) σ hσ1
      hσ2 hrange) ?_
    gcongr
    linarith
  · push Not at hrange
    refine le_trans (hT₂ T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT) σ
      hrange.1.le hrange.2.le) ?_
    have hpow : (1 + Real.log T) ^ 16 ≤ (1 + Real.log T) ^ (classCountLogExponent + 4) :=
      pow_le_pow_right₀ hl (by unfold classCountLogExponent; omega)
    calc Dm * (1 + Real.log T) ^ 16 * T ^ ((33 / 13) * (1 - σ))
        ≤ Dm * (1 + Real.log T) ^ (classCountLogExponent + 4) * T ^ ((33 / 13) * (1 - σ)) := by
          gcongr
      _ ≤ (zeroDensityConstant + Dm) * (1 + Real.log T) ^ (classCountLogExponent + 4)
            * T ^ ((33 / 13) * (1 - σ)) := by
          gcongr
          linarith

end

end RHTower
