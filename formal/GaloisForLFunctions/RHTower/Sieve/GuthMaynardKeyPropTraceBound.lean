import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropFrequencySplit
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOneKeyPropPieces
import GaloisForLFunctions.RHTower.ChenGuptaLiProposition46
import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51S1Reassembly
import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteSeparatedExtension

/-!
# Propositions 4.6 and 5.1 of Guth–Maynard for `ζ`: the cubic inequality before the `S₂`, `S₃` bounds

For a smooth bump `w` with `0 ≤ w ≤ 1`, `ε > 0`, `X ≥ 5`, `N ≤ X`, `|b_n| ≤ 1` and an
`X^ε`-separated set `W ⊂ [0, X]` on which `|Σ_{N<n≤2N} w(n/N) b_n n^{it}| ≥ N^σ`:

`|W|³ N^{6σ−3} ≤ C_ε (N³ + |S₂(W)| + |S₃(W)| + |W|)`   (`card_cube_mul_le_of_trace`).

This is Guth–Maynard's Proposition 4.6 combined with (5.5) and Proposition 5.1
(`|W|³ ≪ N^{6−6σ} + N^{3−6σ} Σ_{m≠0} I_m`, `Σ_{m≠0} I_m = S₁ + S₂ + S₃`, `S₁ = O(1)`).

Mechanism: `W` is enumerated as the `q = 1` Chen–Gupta–Li fibre packet
(`CGLFiniteSeparatedOrdinates.toCGLFibreSeparatedPacket`); its source packet has time and base `X`,
spacing `X^ε`; the corpus Proposition 4.6 (`cglProposition46_realAsymptotic_bound`) bounds `|W|` by
`N^{2−2σ}` and the cube root of the nonzero-frequency sum, which at `q = 1` is
`S₁' + S₂ + S₃ − |W|(S₂ + S₃)({0})` (`norm_nonzeroFrequencySum_modulusOne_le`); the corpus
Proposition 5.1 (`cglProposition51S1_norm_le_literalEpsilonSourcePower`) bounds `S₁'`.  The
constants depend only on `w` and `ε`.
-/

set_option autoImplicit false

open Finset Complex
open scoped InnerProductSpace

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The weighted CGL polynomial at `q = 1` -/

/-- At modulus one every Dirichlet character value is `1`. -/
theorem dirichletCharacter_one_apply_modulusOne (n : ZMod (0 + 1)) :
    (1 : DirichletCharacter ℂ (0 + 1)) n = 1 := by
  haveI : Subsingleton (ZMod (0 + 1)) := (inferInstance : Subsingleton (ZMod 1))
  exact MulChar.one_apply (isUnit_of_subsingleton n)

/-- The CGL weighted polynomial of a `q = 1` row is the smoothed polynomial `D_N(t)`. -/
theorem cglWeightedPolynomial_modulusOne (w : CGLSmoothBump) (N : CGLPositiveLength) (b : ℕ → ℂ)
    (t : ℝ) :
    cglCharacterDyadicWeightedPolynomial N.value (0 + 1) (cglSmoothBumpDyadicWeight w N)
        ⟨t, 1⟩ (WithLp.toLp 2 fun j : Fin N.value => b (cglCharacterDyadicIndex N.value j)) =
      smoothedDyadicPoly w N.value b t := by
  unfold cglCharacterDyadicWeightedPolynomial smoothedDyadicPoly
  rw [show Ioc N.value (2 * N.value) = cglCharacterDyadicBlock N from rfl,
    cglCharacterDyadicBlock_sum_eq_sum_fin]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [cglSmoothBumpDyadicWeight, cglCharacterDyadicPhase, dirichletCharacter_one_apply_modulusOne,
    mul_one]
  change b _ * w.value _ * Complex.exp _ = _
  rw [mul_comm (b _) (w.value _)]
  congr 2
  push_cast
  ring

/-! ### The source packet -/

/-- `X ≤ (X^ε)^d` for `X ≥ 1`, `d = ⌊1/ε⌋ + 1`-type denominators with `1/d < ε`. -/
theorem le_rpow_pow_of_inv_lt {X ε : ℝ} (hX : 1 ≤ X) {d : ℕ} (hd : 0 < d)
    (hdε : (1 : ℝ) / d < ε) : X ^ 1 ≤ (X ^ ε) ^ d := by
  rw [← Real.rpow_natCast (X ^ ε) d, ← Real.rpow_mul (by linarith), pow_one]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : 1 ≤ ε * d := by rw [div_lt_iff₀ hd'] at hdε; linarith
  calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
    _ ≤ X ^ (ε * d) := Real.rpow_le_rpow_of_exponent_le hX this

/-- `(a + b)³ ≤ 4 (a³ + b³)` for `a, b ≥ 0`. -/
theorem add_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

/-- **Propositions 4.6 + 5.1 for `ζ`**, in the cubic form
`|W|³ N^{6σ−3} ≤ C (N³ + |S₂(W)| + |S₃(W)| + |W|)`. -/
theorem card_cube_mul_le_of_trace (w : CGLUnitRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (σ X : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N → 5 ≤ X → (N : ℝ) ≤ X → (∀ n, ‖b n‖ ≤ 1) → (∀ t ∈ W, t ∈ Set.Icc 0 X) →
      IsSeparated (X ^ ε) W →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖smoothedDyadicPoly w.toCGLSmoothBump N b t‖) →
      (W.card : ℝ) ^ 3 * (N : ℝ) ^ (6 * σ - 3) ≤
        C * ((N : ℝ) ^ 3 + ‖gmS2 w.toCGLRealSmoothBump N W‖ +
          ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ + W.card) := by
  classical
  obtain ⟨c, hc0, hc⟩ := norm_nonzeroFrequencySum_modulusOne_le w.toCGLRealSmoothBump
  -- the `ε`-denominator and the constants of Propositions 4.6 and 5.1
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (exists_nat_one_div_lt hε).choose + 1 := ⟨_, rfl⟩
  have hdε : (1 : ℝ) / d < ε := by
    have := (exists_nat_one_div_lt hε).choose_spec
    rw [hd]; push_cast; exact this
  have hd0 : 0 < d := by omega
  set wR := w.toCGLRealSmoothBump with hwR
  set w0 := w.toCGLSmoothBump with hw0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = cglLogFourierAmplitudeAllOrderBudget w0 (d * 115) *
      cglLogFourierAmplitudeAllOrderBudget w0 0 * cglLogFourierAmplitudeAllOrderBudget w0 0 :=
    ⟨_, rfl⟩
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : ℝ, S₁ = 3 * (9 * (cglLogFourierAmplitudeAllOrderBudget w0 (d * 25) *
      cglLogFourierAmplitudeAllOrderBudget w0 0 *
      (cglSmoothBumpHtAllOrderBudget w0 2 / (2 * Real.pi) ^ (2 : ℕ)) *
      cglProposition51PuncturedInverseSquareMass)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (cglLogFourierAmplitudeAllOrderBudget_nonneg _ _)
      (cglLogFourierAmplitudeAllOrderBudget_nonneg _ _)) (cglLogFourierAmplitudeAllOrderBudget_nonneg _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 288 * (K ^ (1 / 3 : ℝ) + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨4 * A ^ 3 + 4 * 288 ^ 3 * (|S₁| + 1 + c), by positivity, ?_⟩
  intro N σ X b W hN hX hNX hb hW hsep hbig
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hRHS0 : 0 ≤ (N : ℝ) ^ 3 + ‖gmS2 wR N W‖ + ‖allNonzeroCubicSum w0 W N‖ + W.card := by
    positivity
  rcases W.eq_empty_or_nonempty with hemp | hne
  · rw [show (W.card : ℝ) = 0 by rw [hemp]; simp, zero_pow (by norm_num), zero_mul]
    exact mul_nonneg (by positivity) (by positivity)
  obtain ⟨R, hR⟩ : ∃ R, W.card = R + 1 := ⟨W.card - 1, by have := hne.card_pos; omega⟩
  -- the enumeration of `W` as a `q = 1` fibre packet
  obtain ⟨ord, hord⟩ : ∃ ord : Fin (R + 1) → ℝ,
      ord = fun r => ((W.equivFin.symm (Fin.cast hR.symm r) : W) : ℝ) := ⟨_, rfl⟩
  have hord_mem : ∀ r, ord r ∈ W := fun r => by rw [hord]; exact Subtype.mem _
  have hord_inj : Function.Injective ord := by
    intro r s h
    rw [hord] at h
    have := Subtype.ext h
    exact Fin.cast_injective _ (W.equivFin.symm.injective this)
  have hord_image : (Finset.univ.image ord) = W := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hx; exact hord_mem r
    · rw [Finset.card_image_of_injective _ hord_inj, Finset.card_univ, Fintype.card_fin, hR]
  have hXε : 0 < X ^ ε := Real.rpow_pos_of_pos (by linarith) _
  let FS : CGLFiniteSeparatedOrdinates (R + 1) :=
    { ordinate := ord
      spacing := X ^ ε
      spacing_pos := hXε
      separated := fun r s hrs => hsep _ (hord_mem r) _ (hord_mem s) (fun h => hrs (hord_inj h)) }
  let P : CGLFibreSeparatedPacket 0 (R + 1) := FS.toCGLFibreSeparatedPacket 1
  have hPord : ∀ r, P.ordinate r = ord r := fun r =>
    cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_ordinate FS 1 r
  let NL : CGLPositiveLength := ⟨N, hN⟩
  let src : CGLLemma45LiteralEpsilonSourcePacket P NL :=
    { time := X
      time_one := by linarith
      base := X
      base_eq_modulus_mul_time := by simp
      base_five := hX
      length_le := hNX
      numerator := 1
      numerator_pos := one_pos
      denominator := d
      denominator_pos := hd0
      spacing_power := le_rpow_pow_of_inv_lt (by linarith) hd0 hdε
      ordinate_bound := fun r => by
        rw [hPord, Real.norm_eq_abs, abs_le]
        have := hW _ (hord_mem r)
        exact ⟨by linarith [this.1], this.2⟩
      epsilon := ε
      epsilon_pos := hε
      spacing_epsilon := le_rfl }
  let coeff : CGLCharacterDyadicBoundedCoefficients N :=
    ⟨WithLp.toLp 2 fun j : Fin N => b (cglCharacterDyadicIndex N j), fun j => hb _⟩
  let S46 : CGLProposition46Packet P NL :=
    { source := src
      cutoff := w
      sigma := σ
      coefficients := coeff
      large := fun r => by
        have hrow : cglLemma45FibreRows P r = ⟨ord r, 1⟩ := by
          simp only [cglLemma45FibreRows, hPord]
          rfl
        rw [hrow]
        have := cglWeightedPolynomial_modulusOne w0 NL b (ord r)
        change (N : ℝ) ^ σ / 6 ≤ ‖cglCharacterDyadicWeightedPolynomial N (0 + 1)
          (cglSmoothBumpDyadicWeight w0 NL) ⟨ord r, 1⟩ coeff.value‖
        rw [show coeff.value = WithLp.toLp 2 fun j : Fin N => b (cglCharacterDyadicIndex N j) from rfl,
          this]
        have h := hbig _ (hord_mem r)
        have : 0 ≤ (N : ℝ) ^ σ := Real.rpow_nonneg hN0.le _
        linarith }
  -- Proposition 4.6
  have h46 := cglProposition46_realAsymptotic_bound S46
  have hK' : cglProposition46ZeroFrequencyNumerator S46 = K := by rw [hK, hd]; rfl
  rw [hK'] at h46
  -- the nonzero-frequency sum through `S₁', S₂, S₃`
  have hinj : Function.Injective fun r => (cglLemma45FibreRows P r).time := by
    intro r s h
    simp only [cglLemma45FibreRows, hPord] at h
    exact hord_inj h
  have hNFS := hc NL (R + 1) (cglLemma45FibreRows P) hinj
  have himage : (Finset.univ.image fun r => (cglLemma45FibreRows P r).time) = W := by
    rw [← hord_image]; congr 1
  rw [himage] at hNFS
  have h51 := cglProposition51S1_norm_le_literalEpsilonSourcePower src wR
  have hbase : (1 : ℝ) ≤ src.base ^ (10 : ℕ) := one_le_pow₀ (by change (1 : ℝ) ≤ X; linarith)
  have hS1 : ‖cglProposition51S1 wR NL modulusOne (R + 1) (cglLemma45FibreRows P)‖ ≤ |S₁| := by
    refine h51.trans ?_
    have hden : src.epsilonDenominator = d := by rw [hd]; rfl
    rw [hden, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    have : 3 * (9 * (cglLogFourierAmplitudeAllOrderBudget w0 (d * 25) *
        cglLogFourierAmplitudeAllOrderBudget w0 0 *
        (cglSmoothBumpHtAllOrderBudget w0 2 / (2 * Real.pi) ^ (2 : ℕ)) *
        cglProposition51PuncturedInverseSquareMass)) = S₁ := hS₁.symm
    rw [this]
    nlinarith [le_abs_self S₁, abs_nonneg S₁]
  -- `Y = max 0 (Re Σ_{m≠0} I'_m) ≤ |S₁| + |S₂| + |S₃| + c |W|`
  obtain ⟨Y, hY⟩ : ∃ Y, Y = max 0 (cglProposition46NonzeroFrequencySum S46).re := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := hY ▸ le_max_left _ _
  have hYle : Y ≤ |S₁| + ‖gmS2 wR N W‖ + ‖allNonzeroCubicSum w0 W N‖ + c * (R + 1) := by
    rw [hY]
    refine max_le (by positivity) ((Complex.re_le_norm _).trans ?_)
    have e : cglProposition46NonzeroFrequencySum S46 =
        ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm wR NL modulusOne (R + 1)
            (cglLemma45FibreRows P) m := rfl
    rw [e]
    refine hNFS.trans ?_
    push_cast
    linarith
  -- cube the bound of Proposition 4.6
  rw [← hA, ← hY] at h46
  have hcard : (W.card : ℝ) = (R : ℝ) + 1 := by rw [hR]; push_cast; ring
  have ha : 0 ≤ A * (N : ℝ) ^ (2 - 2 * σ) := by positivity
  have hb' : 0 ≤ 288 * (N : ℝ) ^ (1 - 2 * σ) * Y ^ (1 / 3 : ℝ) := by positivity
  have hcube := add_cube_le ha hb'
  have h46' : (W.card : ℝ) ^ 3 ≤ (A * (N : ℝ) ^ (2 - 2 * σ) +
      288 * (N : ℝ) ^ (1 - 2 * σ) * Y ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [hcard]; exact pow_le_pow_left₀ (by positivity) h46 3
  have e1 : (A * (N : ℝ) ^ (2 - 2 * σ)) ^ 3 * (N : ℝ) ^ (6 * σ - 3) = A ^ 3 * (N : ℝ) ^ 3 := by
    rw [mul_pow, mul_assoc, ← Real.rpow_natCast ((N : ℝ) ^ (2 - 2 * σ)), ← Real.rpow_mul hN0.le,
      ← Real.rpow_add hN0, ← Real.rpow_natCast (N : ℝ) 3]
    congr 2; push_cast; ring
  have e2 : (288 * (N : ℝ) ^ (1 - 2 * σ) * Y ^ (1 / 3 : ℝ)) ^ 3 * (N : ℝ) ^ (6 * σ - 3) =
      288 ^ 3 * Y := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 - 2 * σ)), ← Real.rpow_mul hN0.le,
      ← Real.rpow_natCast (Y ^ (1 / 3 : ℝ)), ← Real.rpow_mul hY0]
    have h1 : (N : ℝ) ^ ((1 - 2 * σ) * ((3 : ℕ) : ℝ)) * (N : ℝ) ^ (6 * σ - 3) = 1 := by
      rw [← Real.rpow_add hN0]; norm_num; ring_nf; exact Real.rpow_zero _
    have h2 : Y ^ ((1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = Y := by norm_num
    rw [h2]
    calc 288 ^ 3 * (N : ℝ) ^ ((1 - 2 * σ) * ((3 : ℕ) : ℝ)) * Y * (N : ℝ) ^ (6 * σ - 3)
        = 288 ^ 3 * Y * ((N : ℝ) ^ ((1 - 2 * σ) * ((3 : ℕ) : ℝ)) * (N : ℝ) ^ (6 * σ - 3)) := by ring
      _ = 288 ^ 3 * Y := by rw [h1, mul_one]
  have hNp : 0 < (N : ℝ) ^ (6 * σ - 3) := Real.rpow_pos_of_pos hN0 _
  have hmain : (W.card : ℝ) ^ 3 * (N : ℝ) ^ (6 * σ - 3) ≤ 4 * (A ^ 3 * (N : ℝ) ^ 3 + 288 ^ 3 * Y) := by
    calc (W.card : ℝ) ^ 3 * (N : ℝ) ^ (6 * σ - 3)
        ≤ (4 * ((A * (N : ℝ) ^ (2 - 2 * σ)) ^ 3 +
            (288 * (N : ℝ) ^ (1 - 2 * σ) * Y ^ (1 / 3 : ℝ)) ^ 3)) * (N : ℝ) ^ (6 * σ - 3) :=
          mul_le_mul_of_nonneg_right (h46'.trans hcube) hNp.le
      _ = 4 * (A ^ 3 * (N : ℝ) ^ 3 + 288 ^ 3 * Y) := by rw [mul_assoc, add_mul, e1, e2]
  -- collect: `|S₁| ≤ |S₁| N³`, `c (R+1) = c |W|`
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hNr
  have hS1N : |S₁| ≤ |S₁| * (N : ℝ) ^ 3 := le_mul_of_one_le_right (abs_nonneg _) hN3
  rw [← hcard] at hYle
  have hS2 := norm_nonneg (gmS2 wR N W)
  have hS3 := norm_nonneg (allNonzeroCubicSum w0 W N)
  have hW0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (N : ℝ) ^ 3 + ‖gmS2 wR N W‖ + ‖allNonzeroCubicSum w0 W N‖ + W.card :=
    ⟨_, rfl⟩
  rw [← hZ]
  have hZ1 : 1 ≤ Z := by rw [hZ]; linarith
  have hYZ : Y ≤ (|S₁| + 1 + c) * Z := by
    have h1 : |S₁| ≤ |S₁| * Z := le_mul_of_one_le_right (abs_nonneg _) hZ1
    have h2 : ‖gmS2 wR N W‖ + ‖allNonzeroCubicSum w0 W N‖ ≤ Z := by rw [hZ]; linarith
    have h3 : c * W.card ≤ c * Z := mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) hc0
    nlinarith
  have hAZ : A ^ 3 * (N : ℝ) ^ 3 ≤ A ^ 3 * Z :=
    mul_le_mul_of_nonneg_left (by rw [hZ]; linarith) (by positivity)
  refine hmain.trans ?_
  calc 4 * (A ^ 3 * (N : ℝ) ^ 3 + 288 ^ 3 * Y)
      ≤ 4 * (A ^ 3 * Z + 288 ^ 3 * ((|S₁| + 1 + c) * Z)) := by gcongr
    _ = (4 * A ^ 3 + 4 * 288 ^ 3 * (|S₁| + 1 + c)) * Z := by ring

end

end RHTower.GuthMaynard
