import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCompensatedProducer

/-!
# The one-quarter rate under the Riemann hypothesis

The compensated producer with `T = y²` has alphabet `y³/Y` and rate `Y`, up to logarithms, where `Y` is the larger of the Mertens level at `T` and `1/y`. So a bound
`|M(n)| ≤ C n^{1−σ}`, `σ ≤ ½`, gives `Y ≈ y^{-2σ}` and an alphabet `y^{3+2σ}`:

* `|M(n)| ≤ C n^{1−σ}` gives every rate `K^{-a}`, `a < 2σ/(3 + 2σ)`;
* a zero-free strip `Re s > Θ`, `Θ ≥ ½`, gives every rate `K^{-a}`, `a < 2(1 − Θ)/(5 − 2Θ)`;
* the Riemann hypothesis gives every rate `K^{-a}`, `a < 1/4`.

Under the Riemann hypothesis the exponent of the rate therefore lies in `[1/4, 1/2]`.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The real arithmetic of the excess at a level. -/
private lemma compensated_excess {Y₀ Yn Lx lT lG lK Z FW Mg s4 : ℝ} (hY₀ : 0 ≤ Y₀) (hLx : 0 ≤ Lx)
    (hYn : 5 * Y₀ ≤ Yn) (hlT : lT ≤ Lx) (hlG : lG ≤ Lx) (hlK : lK ≤ Lx) (hlK0 : 0 ≤ lK) (hlG0 : 0 ≤ lG)
    (hZ : Z ≤ Yn + 2 * Y₀) (hZ0 : 0 ≤ Z) (hFW : FW ≤ 2 * Y₀) (hFW0 : 0 ≤ FW) (hMg : Mg ≤ Y₀)
    (hs4 : s4 ≤ Y₀ * (1 + lT)) :
    s4 + Yn * (1 + lG) + Mg + Z * lK + FW * lK ≤ 4 * (Yn * (1 + Lx)) := by
  have hYn0 : 0 ≤ Yn := by linarith
  have h1 : Y₀ * (1 + lT) ≤ Y₀ * (1 + Lx) := by gcongr
  have h2 : Yn * (1 + lG) ≤ Yn * (1 + Lx) := by gcongr
  have h3 : Z * lK ≤ (Yn + 2 * Y₀) * Lx := mul_le_mul hZ hlK hlK0 (by linarith)
  have h4 : FW * lK ≤ 2 * Y₀ * Lx := mul_le_mul hFW hlK hlK0 (by linarith)
  have h5 : 5 * (Y₀ * (1 + Lx)) ≤ Yn * (1 + Lx) := by
    calc 5 * (Y₀ * (1 + Lx)) = 5 * Y₀ * (1 + Lx) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hYn (by linarith)
  nlinarith

/-- **The compensated producer at a level.** With `|M(x)| ≤ η x` on `x ≥ y²` and `η + 5 (1 + log X)/y ≤ Y₀ ≤ 1`, there is an integer producer on an alphabet in
`[1, 6 (1 + B)/Y₀]`, `B = compBound y`, of rate at most `8 Y₀ (5 + 2 log X)(1 + log X)`, provided the alphabet lies below `X`. -/
theorem exists_compensated_producer_of_level {y : ℕ} (hy : 4 ≤ y) {η Y₀ : ℝ} {X : ℕ}
    (hM : ∀ x, y * y ≤ x → |mertens x| ≤ η * x)
    (hY₀ : η + 5 * (1 + Real.log X) / y ≤ Y₀) (hY₀1 : Y₀ ≤ 1)
    (hX : 6 * (1 + compBound y) / Y₀ ≤ X) :
    ∃ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B ∧ AlphabetLE c ⌊6 * (1 + compBound y) / Y₀⌋₊ ∧
      rate c m B ≤ 8 * (Y₀ * (5 + 2 * Real.log X)) * (1 + Real.log X) := by
  obtain ⟨d, hc⟩ := exists_isCompensation (by omega : 1 ≤ y)
  have hy1 : 1 ≤ y := by omega
  have hyR : (4 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hT : 16 ≤ y * y := by nlinarith
  have hTR : (16 : ℝ) ≤ ((y * y : ℕ) : ℝ) := by exact_mod_cast hT
  have hlT0 : 0 ≤ Real.log ((y * y : ℕ) : ℝ) := Real.log_natCast_nonneg _
  -- The bound is large.
  have hlog0 : (0 : ℝ) ≤ (Nat.log 2 (y * y) : ℝ) := Nat.cast_nonneg _
  have hb : (10 : ℝ) ≤ ((2 * y + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ 2 * y + 2)
  have hB2 : 2 * ((y * y : ℕ) : ℝ) ≤ compBound y := by
    rw [compBound]
    have h1 : (1 : ℝ) ≤ (Nat.log 2 (y * y) : ℝ) + 1 := by linarith
    have h2 : (1 : ℝ) ≤ (Nat.log 2 (y * y) : ℝ) + 3 := by linarith
    have h3 : (2 : ℝ) ≤ 2 + Real.log ((y * y : ℕ) : ℝ) := by linarith
    have h4 : (1 : ℝ) ≤ ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3) := by nlinarith
    have h5 : (2 : ℝ) ≤ ((2 * y + 2 : ℕ) : ℝ) * (((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3)) *
        (2 + Real.log ((y * y : ℕ) : ℝ)) := by nlinarith
    calc 2 * ((y * y : ℕ) : ℝ) = ((y * y : ℕ) : ℝ) * 2 := by ring
      _ ≤ ((y * y : ℕ) : ℝ) * (((2 * y + 2 : ℕ) : ℝ) * (((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3)) *
          (2 + Real.log ((y * y : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h5 (by linarith)
      _ = _ := by ring
  obtain ⟨B, hBdef⟩ : ∃ B, B = compBound y := ⟨_, rfl⟩
  rw [← hBdef] at hB2 hX ⊢
  have hB0 : 0 < B := by linarith
  -- `η ≥ 0` and `Y₀ > 0`.
  have hη : 0 ≤ η := by
    have h1 := hM (y * y) le_rfl
    have h2 := abs_nonneg (mertens (y * y))
    have h3 : (0 : ℝ) < ((y * y : ℕ) : ℝ) := by linarith
    by_contra hneg
    push Not at hneg
    nlinarith
  have hXpos : (6 : ℝ) ≤ X := by
    have hY₀pos0 : 0 < Y₀ ∨ Y₀ ≤ 0 := lt_or_ge 0 Y₀
    rcases hY₀pos0 with h | h
    · refine le_trans ?_ hX
      rw [le_div_iff₀ h]
      nlinarith
    · exfalso
      have h1 : 0 ≤ 5 * (1 + Real.log X) / y ∨ True := Or.inr trivial
      rcases Nat.eq_zero_or_pos X with h0 | h0
      · subst h0
        have h2 : (5 : ℝ) / y > 0 := by positivity
        simp only [Nat.cast_zero, Real.log_zero, add_zero, mul_one] at hY₀
        linarith
      · have h3 : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
        have h2 : 0 < 5 * (1 + Real.log X) / y := by positivity
        linarith
  have hXone : 1 ≤ X := by
    have : (1 : ℝ) ≤ X := by linarith
    exact_mod_cast this
  have hLx : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hgap : 5 / (y : ℝ) ≤ 5 * (1 + Real.log X) / y := by
    gcongr
    linarith
  have hY₀0 : 0 < Y₀ := by
    have : 0 < 5 / (y : ℝ) := by positivity
    linarith
  -- The power of two.
  obtain ⟨A, hAdef⟩ : ∃ A, A = (1 + B) / Y₀ := ⟨_, rfl⟩
  have hAB : 1 + B ≤ A := by
    rw [hAdef, le_div_iff₀ hY₀0]
    nlinarith
  have hA1 : 1 ≤ A := by linarith
  have hfl : 1 ≤ ⌊A⌋₊ := Nat.le_floor (by simpa using hA1)
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.log 2 ⌊A⌋₊ + 1 := ⟨_, rfl⟩
  have hG1 : A ≤ ((2 ^ g : ℕ) : ℝ) := by
    have h1 : ⌊A⌋₊ < 2 ^ g := by
      rw [hg]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 := Nat.lt_floor_add_one A
    have h3 : ((⌊A⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ g : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hG2 : ((2 ^ g : ℕ) : ℝ) ≤ 2 * A := by
    have h1 : 2 ^ Nat.log 2 ⌊A⌋₊ ≤ ⌊A⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((⌊A⌋₊ : ℕ) : ℝ) ≤ A := Nat.floor_le (by linarith)
    have h3 : ((2 ^ Nat.log 2 ⌊A⌋₊ : ℕ) : ℝ) ≤ ((⌊A⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hg, pow_succ]
    push_cast at h3 ⊢
    linarith
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ, G = 2 ^ g := ⟨_, rfl⟩
  have hG1' : A ≤ (G : ℝ) := by rw [hGdef]; exact hG1
  have hG2' : (G : ℝ) ≤ 2 * A := by rw [hGdef]; exact hG2
  have hGR0 : (0 : ℝ) < G := by linarith
  have hTG' : (((y * y : ℕ) : ℝ)) < G := by linarith
  have hTG : y * y < G := by exact_mod_cast hTG'
  have hG2n : 2 ≤ G := by omega
  have hK : ((G * 3 : ℕ) : ℝ) ≤ 6 * A := by
    push_cast
    linarith
  have hAX : 6 * A ≤ X := by
    have e : 6 * A = 6 * (1 + B) / Y₀ := by
      rw [hAdef]
      ring
    rw [e]
    exact hX
  have hGX : G ≤ X := by
    have : (G : ℝ) ≤ X := by linarith
    exact_mod_cast this
  -- The near law.
  have hmass := compMass_le hc hy
  have hweight := compWeighted_le hc hy
  rw [← hBdef] at hmass hweight
  have hY₀G : (1 + B) / (G : ℝ) ≤ Y₀ := by
    rw [div_le_iff₀ hGR0]
    have h1 : 1 + B = A * Y₀ := by
      rw [hAdef]
      field_simp
    rw [h1]
    calc A * Y₀ ≤ (G : ℝ) * Y₀ := mul_le_mul_of_nonneg_right hG1' hY₀0.le
      _ = _ := mul_comm _ _
  have hn : ∀ P ∈ largePrimes y, d P ≤ G := by
    intro P hP
    have h1 := hc.le_two_mul hy hP
    have h2 := (mem_largePrimes.mp hP).1.2
    have h3 : (((2 * (y * y) : ℕ) : ℝ)) < G := by
      push_cast
      push_cast at hB2
      linarith
    have h4 : 2 * (y * y) < G := by exact_mod_cast h3
    omega
  obtain ⟨Yn, hYndef⟩ : ∃ Yn, Yn = Y₀ * (5 + 2 * Real.log X) := ⟨_, rfl⟩
  have hYn5 : 5 * Y₀ ≤ Yn := by
    rw [hYndef]
    nlinarith
  have hYn0 : 0 ≤ Yn := by linarith
  have hnear : ∀ s, 1 ≤ s → s < G → |compNear y d s - compCount y d s| ≤ (s : ℝ) * Yn := by
    intro s hs hsG
    have h := abs_compNear_sub_le hc hy1 hY₀0.le hM hGX (by omega : 1 ≤ G) hXone hn hY₀ hs (by omega : s ≤ X)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg s))
    have h1 : (1 + compMass y d) / (G : ℝ) ≤ Y₀ := by
      refine le_trans ?_ hY₀G
      gcongr
    rw [hYndef]
    nlinarith
  -- The linear weight.
  obtain ⟨Z, hZ1, hZ2⟩ := exists_rat_btwn (by linarith : Yn + Y₀ < Yn + 2 * Y₀)
  have hZ0 : (0 : ℝ) ≤ (Z : ℝ) := by linarith
  have hWG : compWeighted y d / (G : ℝ) ≤ Y₀ := by
    refine le_trans ?_ hY₀G
    gcongr
    linarith
  have hK3 : 2 * compWeighted y d / ((G * 3 : ℕ) : ℝ) ≤ Y₀ := by
    push_cast
    have e : 2 * compWeighted y d / ((G : ℝ) * 3) = (2 / 3) * (compWeighted y d / G) := by
      field_simp
    rw [e]
    have hW0 : 0 ≤ compWeighted y d := by
      refine sum_nonneg fun x _ => by positivity
    have : 0 ≤ compWeighted y d / (G : ℝ) := by positivity
    linarith
  have hZY : Yn + 2 * compWeighted y d / ((G * 3 : ℕ) : ℝ) ≤ (Z : ℝ) := by linarith
  subst hGdef
  obtain ⟨c, m, hP, hal, hslope⟩ := exists_compensated_producer hc hy hTG hZ0 hnear hZY
  have hG2R : (2 : ℝ) ≤ ((2 ^ g : ℕ) : ℝ) := by exact_mod_cast hG2n
  refine ⟨c, m, 2 ^ g, hP, fun k hk => (hal k hk).trans (Nat.le_floor ?_), ?_⟩
  · have e : 6 * (1 + B) / Y₀ = 6 * A := by
      rw [hAdef]
      ring
    rw [e]
    exact hK
  -- The rate.
  have hslope2 := compSlope_le hc hy hG2n hYn0 hnear
  have hfar := sum_far_weight_le (d := d) hy hTG
  have hFW : ∑ x ∈ compPairs y, (compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g (2 ^ g * 3) (x.1 ^ x.2) ≤ 2 * Y₀ := by
    linarith
  have hFW0 : 0 ≤ ∑ x ∈ compPairs y, (compDefect y d (x.1 ^ x.2) : ℝ) / farModulus g (2 ^ g * 3) (x.1 ^ x.2) :=
    sum_nonneg fun x _ => by positivity
  have hm := hP.m_pos
  have hd := hP.one_sub_pos
  have hd2 : 1 / 2 ≤ 1 - 1 / ((2 ^ g : ℕ) : ℝ) := by
    have : 1 / ((2 ^ g : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hG2R
    linarith
  have hlogT : Real.log ((y * y : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by linarith) (by exact_mod_cast hTG.le.trans hGX)
  have hlogG : Real.log ((2 ^ g : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log hGR0 (by exact_mod_cast hGX)
  have hlogK : Real.log ((2 ^ g * 3 : ℕ) : ℝ) ≤ Real.log X :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogK0 : 0 ≤ Real.log ((2 ^ g * 3 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogG0 : 0 ≤ Real.log ((2 ^ g : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hMg : compMass y d / ((2 ^ g : ℕ) : ℝ) ≤ Y₀ := by
    refine le_trans ?_ hY₀G
    gcongr
    linarith
  have h4y : 4 / (y : ℝ) * (1 + Real.log ((y * y : ℕ) : ℝ)) ≤ Y₀ * (1 + Real.log ((y * y : ℕ) : ℝ)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have h1 : 4 / (y : ℝ) ≤ 5 / y := by gcongr; norm_num
    linarith
  have hexc := compensated_excess hY₀0.le hLx hYn5 hlogT hlogG hlogK hlogK0 hlogG0 hZ2.le hZ0 hFW hFW0 hMg h4y
  have hratio : stencilSlope c ≤ (m : ℝ) * (1 - 1 / ((2 ^ g : ℕ) : ℝ) + 4 * (Yn * (1 + Real.log X))) := by
    refine hslope.trans (mul_le_mul_of_nonneg_left ?_ hm.le)
    linarith
  rw [rate, normSlope, sub_le_iff_le_add, div_le_iff₀ (mul_pos hm hd)]
  refine hratio.trans ?_
  rw [hYndef] at hexc ⊢
  have hE0 : 0 ≤ Y₀ * (5 + 2 * Real.log X) * (1 + Real.log X) := by positivity
  have hkey : 4 * (Y₀ * (5 + 2 * Real.log X) * (1 + Real.log X)) ≤
      8 * (Y₀ * (5 + 2 * Real.log X)) * (1 + Real.log X) * (1 - 1 / ((2 ^ g : ℕ) : ℝ)) := by
    have e : 8 * (Y₀ * (5 + 2 * Real.log X)) * (1 + Real.log X) =
        8 * (Y₀ * (5 + 2 * Real.log X) * (1 + Real.log X)) := by ring
    rw [e]
    nlinarith
  calc (m : ℝ) * (1 - 1 / ((2 ^ g : ℕ) : ℝ) + 4 * (Y₀ * (5 + 2 * Real.log X) * (1 + Real.log X)))
      ≤ (m : ℝ) * (1 - 1 / ((2 ^ g : ℕ) : ℝ) +
          8 * (Y₀ * (5 + 2 * Real.log X)) * (1 + Real.log X) * (1 - 1 / ((2 ^ g : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hm.le
    _ = _ := by ring

/-- A cube of a logarithm against a power. -/
private lemma eventually_cube_log_le {A γ : ℝ} (hA : 0 ≤ A) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, A * (1 + Real.log x) ^ 3 ≤ x ^ γ := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = γ / 3 := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hδ : (0 : ℝ) < 1 / (2 * (A + 1)) := by positivity
  have h1 := (isLittleO_log_rpow_atTop hκ0).bound hδ
  have h2 := (tendsto_rpow_atTop hκ0).eventually_ge_atTop (2 * (A + 1))
  filter_upwards [h1, h2, Real.tendsto_log_atTop.eventually_ge_atTop 0, eventually_gt_atTop 0] with x h3 h4 h5 h6
  have hxp : 0 ≤ x ^ κ := by positivity
  rw [Real.norm_of_nonneg h5, Real.norm_of_nonneg hxp] at h3
  have h7 : 1 ≤ 1 / (2 * (A + 1)) * x ^ κ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith
  have h8 : 1 + Real.log x ≤ 1 / (A + 1) * x ^ κ := by
    have e : 1 / (A + 1) * x ^ κ = 1 / (2 * (A + 1)) * x ^ κ + 1 / (2 * (A + 1)) * x ^ κ := by
      field_simp
      ring
    rw [e]
    linarith
  have h9 : (1 + Real.log x) ^ 3 ≤ (1 / (A + 1) * x ^ κ) ^ 3 := pow_le_pow_left₀ (by linarith) h8 3
  have hpow : (x ^ κ) ^ 3 = x ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h6.le, hκ]
    congr 1
    push_cast
    ring
  have h10 : A * (1 / (A + 1)) ^ 3 ≤ 1 := by
    have hA1 : (1 : ℝ) ≤ A + 1 := by linarith
    have h11 : (1 / (A + 1)) ^ 3 ≤ 1 / (A + 1) := by
      have h12 : 1 / (A + 1) ≤ 1 := (div_le_one (by linarith)).mpr hA1
      have h13 : 0 ≤ 1 / (A + 1) := by positivity
      calc (1 / (A + 1)) ^ 3 ≤ (1 / (A + 1)) ^ 1 := pow_le_pow_of_le_one h13 h12 (by norm_num)
        _ = _ := pow_one _
    calc A * (1 / (A + 1)) ^ 3 ≤ A * (1 / (A + 1)) := mul_le_mul_of_nonneg_left h11 hA
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by linarith)]
        linarith
  have hxg : 0 ≤ x ^ γ := by positivity
  calc A * (1 + Real.log x) ^ 3 ≤ A * (1 / (A + 1) * x ^ κ) ^ 3 := mul_le_mul_of_nonneg_left h9 hA
    _ = A * (1 / (A + 1)) ^ 3 * (x ^ κ) ^ 3 := by ring
    _ = A * (1 / (A + 1)) ^ 3 * x ^ γ := by rw [hpow]
    _ ≤ 1 * x ^ γ := mul_le_mul_of_nonneg_right h10 hxg
    _ = _ := one_mul _

/-- `compBound y ≤ 72 y³ (1 + log y)³` for `y ≥ 4`. -/
private lemma compBound_le {y : ℕ} (hy : 4 ≤ y) :
    compBound y ≤ 72 * (y : ℝ) ^ 3 * (1 + Real.log y) ^ 3 := by
  have hyR : (4 : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (y : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact Real.log_nonneg (by linarith)
  have hT : ((y * y : ℕ) : ℝ) = (y : ℝ) ^ 2 := by
    push_cast
    ring
  have hlogT : Real.log ((y * y : ℕ) : ℝ) = 2 * u := by
    rw [hT, Real.log_pow, hu]
    norm_num
  have hb : ((2 * y + 2 : ℕ) : ℝ) ≤ 3 * (y : ℝ) := by
    push_cast
    linarith
  -- The binary logarithm.
  have hl : (Nat.log 2 (y * y) : ℝ) ≤ 3 * u := by
    have h1 : 2 ^ Nat.log 2 (y * y) ≤ y * y := Nat.pow_log_le_self 2 (by nlinarith)
    have h2 : ((2 : ℝ)) ^ Nat.log 2 (y * y) ≤ ((y * y : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, hlogT] at h3
    have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hl0 : (0 : ℝ) ≤ (Nat.log 2 (y * y) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hl0 : (0 : ℝ) ≤ (Nat.log 2 (y * y) : ℝ) := Nat.cast_nonneg _
  rw [compBound, hlogT, hT, ← hu]
  have h1 : (Nat.log 2 (y * y) : ℝ) + 1 ≤ 3 * (1 + u) := by linarith
  have h2 : (Nat.log 2 (y * y) : ℝ) + 3 ≤ 3 * (1 + u) := by linarith
  have h3 : 2 + 2 * u = 2 * (1 + u) := by ring
  rw [h3]
  have hy2 : 0 ≤ (y : ℝ) ^ 2 := by positivity
  have h1u : 0 ≤ 1 + u := by linarith
  calc (y : ℝ) ^ 2 * ((2 * y + 2 : ℕ) : ℝ) * ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3) * (2 * (1 + u))
      ≤ (y : ℝ) ^ 2 * (3 * (y : ℝ)) * (3 * (1 + u)) * (3 * (1 + u)) * (2 * (1 + u)) := by
        gcongr
    _ ≤ _ := by
        have e : (y : ℝ) ^ 2 * (3 * (y : ℝ)) * (3 * (1 + u)) * (3 * (1 + u)) * (2 * (1 + u)) =
            54 * (y : ℝ) ^ 3 * (1 + u) ^ 3 := by ring
        rw [e]
        have : 0 ≤ (y : ℝ) ^ 3 * (1 + u) ^ 3 := by positivity
        nlinarith

/-- **A power bound on the Mertens function gives a rate at the compensated exponent.** With `|M(n)| ≤ C n^{1−σ}`, `0 < σ ≤ ½`, there are integer producers of rate
`K^{-a}` for every `a < 2σ/(3 + 2σ)`. -/
theorem hasRate_of_power_quarter {C σ a : ℝ} (hC : 0 ≤ C) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2)
    (hM : ∀ n : ℕ, 1 ≤ n → |mertens n| ≤ C * (n : ℝ) ^ (1 - σ)) (ha0 : 0 < a) (ha : a < 2 * σ / (3 + 2 * σ)) :
    HasRate fun K => (K : ℝ) ^ (-a) := by
  have hd₀ : 0 < 3 + 2 * σ := by linarith
  have ha' : a * (3 + 2 * σ) < 2 * σ := by rwa [lt_div_iff₀ hd₀] at ha
  -- The exponent of the alphabet.
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = min 1 ((2 * σ - a * (3 + 2 * σ)) / (2 * a)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκdef]
    exact lt_min one_pos (div_pos (by linarith) (by positivity))
  have hκ1 : κ ≤ 1 := hκdef ▸ min_le_left _ _
  have hκa : a * κ ≤ (2 * σ - a * (3 + 2 * σ)) / 2 := by
    have h1 : κ ≤ (2 * σ - a * (3 + 2 * σ)) / (2 * a) := hκdef ▸ min_le_right _ _
    calc a * κ ≤ a * ((2 * σ - a * (3 + 2 * σ)) / (2 * a)) := mul_le_mul_of_nonneg_left h1 ha0.le
      _ = _ := by field_simp
  obtain ⟨D, hDdef⟩ : ∃ D, D = 3 + 2 * σ + κ := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hDdef]; linarith
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith
  have hD5 : D ≤ 5 := by rw [hDdef]; linarith
  have haD : a * D < 2 * σ := by
    rw [hDdef]
    nlinarith
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 1 / D := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [hedef]; positivity
  have he1 : e ≤ 1 := by
    rw [hedef, div_le_one hD0]
    exact hD1
  obtain ⟨b, hbdef⟩ : ∃ b, b = e * (2 * σ) := ⟨_, rfl⟩
  have hab : a < b := by
    rw [hbdef, hedef]
    have : 1 / D * (2 * σ) = 2 * σ / D := by ring
    rw [this, lt_div_iff₀ hD0]
    exact haD
  obtain ⟨gap, hgapdef⟩ : ∃ gap, gap = b - a := ⟨_, rfl⟩
  have hgap : 0 < gap := by rw [hgapdef]; linarith
  obtain ⟨A, hAdef⟩ : ∃ A, A = C + 45 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hAdef]; linarith
  have hcut : Tendsto (fun K : ℕ => ⌊(K : ℝ) ^ e⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop he0).comp tendsto_natCast_atTop_atTop)
  have hN := tendsto_natCast_atTop_atTop (R := ℝ)
  have h1 := hcut.eventually (hN.eventually (eventually_cube_log_le (A := 1000) (γ := κ) (by norm_num) hκ0))
  have h2 := hcut.eventually (hN.eventually (eventually_cube_log_le (A := A) (γ := 2 * σ) hA0.le (by positivity)))
  have h3 := hN.eventually (eventually_cube_log_le (A := 2100 * A) (γ := gap) (by positivity) hgap)
  filter_upwards [h1, h2, h3, hcut.eventually_ge_atTop 4, eventually_ge_atTop 1] with K hK1 hK2 hK3 hy4 hK0
  obtain ⟨y, hydef⟩ : ∃ y, y = ⌊(K : ℝ) ^ e⌋₊ := ⟨_, rfl⟩
  rw [← hydef] at hK1 hK2 hy4
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  have hK0R : (0 : ℝ) < K := by linarith
  have hyR : (4 : ℝ) ≤ y := by exact_mod_cast hy4
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (y : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact Real.log_nonneg hy1
  rw [← hu] at hK1 hK2
  have h1u : 1 ≤ 1 + u := by linarith
  have hcube : 1 ≤ (1 + u) ^ 3 := one_le_pow₀ h1u
  have hypow : 0 < (y : ℝ) ^ (-(2 * σ)) := Real.rpow_pos_of_pos hy0 _
  -- The level.
  obtain ⟨η, hηdef⟩ : ∃ η, η = C * (y : ℝ) ^ (-(2 * σ)) := ⟨_, rfl⟩
  have hM' : ∀ x, y * y ≤ x → |mertens x| ≤ η * x := by
    intro x hx
    have hx1 : 1 ≤ x := le_trans (Nat.mul_pos (by omega) (by omega)) hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx1
    refine (hM x hx1).trans ?_
    have hsplit : (x : ℝ) ^ (1 - σ) = (x : ℝ) * (x : ℝ) ^ (-σ) := by
      rw [sub_eq_add_neg, Real.rpow_add hxR, Real.rpow_one]
    have hmono : (x : ℝ) ^ (-σ) ≤ (y : ℝ) ^ (-(2 * σ)) := by
      have hle : (y : ℝ) ^ (2 : ℝ) ≤ x := by
        rw [Real.rpow_two]
        have : ((y * y : ℕ) : ℝ) ≤ x := by exact_mod_cast hx
        push_cast at this
        nlinarith
      calc (x : ℝ) ^ (-σ) ≤ ((y : ℝ) ^ (2 : ℝ)) ^ (-σ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
        _ = _ := by
            rw [← Real.rpow_mul hy0.le]
            congr 1
            ring
    rw [hsplit, hηdef]
    calc C * ((x : ℝ) * (x : ℝ) ^ (-σ)) ≤ C * ((x : ℝ) * (y : ℝ) ^ (-(2 * σ))) := by gcongr
      _ = _ := by ring
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = y ^ 8 := ⟨_, rfl⟩
  have hlogX : Real.log (X : ℝ) = 8 * u := by
    rw [hXdef]
    push_cast
    rw [Real.log_pow, hu]
    norm_num
  obtain ⟨Y₀, hY₀def⟩ : ∃ Y₀, Y₀ = (y : ℝ) ^ (-(2 * σ)) * (C + 5 * (1 + 8 * u)) := ⟨_, rfl⟩
  have hY₀0 : 0 < Y₀ := by
    rw [hY₀def]
    positivity
  have hinvy : 1 / (y : ℝ) ≤ (y : ℝ) ^ (-(2 * σ)) := by
    have h4 : (y : ℝ) ^ (-1 : ℝ) ≤ (y : ℝ) ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at h4
  have hY₀ge : η + 5 * (1 + Real.log X) / y ≤ Y₀ := by
    rw [hlogX, hηdef, hY₀def]
    have e : 5 * (1 + 8 * u) / (y : ℝ) = 5 * (1 + 8 * u) * (1 / (y : ℝ)) := by ring
    rw [e]
    have h5 := mul_le_mul_of_nonneg_left hinvy (by positivity : 0 ≤ 5 * (1 + 8 * u))
    nlinarith
  -- `C + 5 (1 + 8 u) ≤ A (1 + u)`.
  have hAu : C + 5 * (1 + 8 * u) ≤ A * (1 + u) := by
    rw [hAdef]
    nlinarith
  have hAu3 : C + 5 * (1 + 8 * u) ≤ A * (1 + u) ^ 3 := by
    refine hAu.trans (mul_le_mul_of_nonneg_left ?_ hA0.le)
    calc 1 + u = (1 + u) ^ 1 := (pow_one _).symm
      _ ≤ (1 + u) ^ 3 := pow_le_pow_right₀ h1u (by norm_num)
  have hinvpow : (y : ℝ) ^ (-(2 * σ)) * (y : ℝ) ^ (2 * σ) = 1 := by
    rw [← Real.rpow_add hy0]
    simp
  have hY₀1 : Y₀ ≤ 1 := by
    rw [hY₀def]
    have h6 : C + 5 * (1 + 8 * u) ≤ (y : ℝ) ^ (2 * σ) := hAu3.trans hK2
    calc (y : ℝ) ^ (-(2 * σ)) * (C + 5 * (1 + 8 * u)) ≤ (y : ℝ) ^ (-(2 * σ)) * (y : ℝ) ^ (2 * σ) :=
          mul_le_mul_of_nonneg_left h6 hypow.le
      _ = 1 := hinvpow
  -- The alphabet.
  have hB := compBound_le hy4
  rw [← hu] at hB
  have hBpow : 6 * (1 + compBound y) / Y₀ ≤ (y : ℝ) ^ D := by
    have hpow3 : (1 : ℝ) ≤ (y : ℝ) ^ 3 := one_le_pow₀ hy1
    have h1B : 1 + compBound y ≤ 73 * (y : ℝ) ^ 3 * (1 + u) ^ 3 := by
      have : 1 ≤ (y : ℝ) ^ 3 * (1 + u) ^ 3 := one_le_mul_of_one_le_of_one_le hpow3 hcube
      nlinarith
    have hY₀low : (y : ℝ) ^ (-(2 * σ)) ≤ Y₀ := by
      rw [hY₀def]
      refine le_mul_of_one_le_right hypow.le ?_
      nlinarith
    have hsplitD : (y : ℝ) ^ D = (y : ℝ) ^ 3 * (y : ℝ) ^ (2 * σ) * (y : ℝ) ^ κ := by
      rw [hDdef, Real.rpow_add hy0, Real.rpow_add hy0, Real.rpow_natCast_three hy0]
    rw [div_le_iff₀ hY₀0]
    have h7 : 6 * (1 + compBound y) ≤ 438 * (1 + u) ^ 3 * (y : ℝ) ^ 3 := by nlinarith
    have h8 : 438 * (1 + u) ^ 3 ≤ (y : ℝ) ^ κ := by
      have : 438 * (1 + u) ^ 3 ≤ 1000 * (1 + u) ^ 3 := by nlinarith
      linarith
    have hp : 0 ≤ (y : ℝ) ^ 3 * (y : ℝ) ^ (2 * σ) := by positivity
    calc 6 * (1 + compBound y) ≤ (y : ℝ) ^ κ * (y : ℝ) ^ 3 := by
          refine h7.trans (mul_le_mul_of_nonneg_right h8 (by positivity))
      _ = (y : ℝ) ^ 3 * (y : ℝ) ^ (2 * σ) * (y : ℝ) ^ κ * ((y : ℝ) ^ (-(2 * σ))) := by
          have e2 : (y : ℝ) ^ 3 * (y : ℝ) ^ (2 * σ) * (y : ℝ) ^ κ * ((y : ℝ) ^ (-(2 * σ))) =
              (y : ℝ) ^ κ * (y : ℝ) ^ 3 * ((y : ℝ) ^ (-(2 * σ)) * (y : ℝ) ^ (2 * σ)) := by ring
          rw [e2, hinvpow, mul_one]
      _ ≤ (y : ℝ) ^ D * Y₀ := by
          rw [hsplitD]
          exact mul_le_mul_of_nonneg_left hY₀low (by positivity)
  have hKe : 0 ≤ (K : ℝ) ^ e := by positivity
  have hyle : (y : ℝ) ≤ (K : ℝ) ^ e := hydef ▸ Nat.floor_le hKe
  have hylt : (K : ℝ) ^ e < (y : ℝ) + 1 := hydef ▸ Nat.lt_floor_add_one _
  have hyD : (y : ℝ) ^ D ≤ K := by
    calc (y : ℝ) ^ D ≤ ((K : ℝ) ^ e) ^ D := Real.rpow_le_rpow hy0.le hyle hD0.le
      _ = K := by
          rw [← Real.rpow_mul hK0R.le, hedef, one_div, inv_mul_cancel₀ hD0.ne', Real.rpow_one]
  have hXle : (y : ℝ) ^ D ≤ X := by
    rw [hXdef]
    push_cast
    calc (y : ℝ) ^ D ≤ (y : ℝ) ^ (8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      _ = _ := by
          rw [← Real.rpow_natCast]
          norm_num
  obtain ⟨c, m, B, hP, hal, hr⟩ := exists_compensated_producer_of_level hy4 hM' hY₀ge hY₀1 (hBpow.trans hXle)
  refine ⟨c, m, B, hP, fun k hk => (hal k hk).trans (Nat.floor_le_of_le (hBpow.trans hyD)), hr.trans ?_⟩
  -- The rate.
  rw [hlogX]
  obtain ⟨w, hw⟩ : ∃ w, w = Real.log (K : ℝ) := ⟨_, rfl⟩
  rw [← hw] at hK3
  have hw0 : 0 ≤ w := by
    rw [hw]
    exact Real.log_nonneg hKR
  have hTK : (y : ℝ) ≤ K := by
    refine hyle.trans ?_
    calc (K : ℝ) ^ e ≤ (K : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hKR he1
      _ = K := Real.rpow_one _
  have huw : u ≤ w := by
    rw [hu, hw]
    exact Real.log_le_log hy0 hTK
  have hy2 : (K : ℝ) ^ e / 2 ≤ y := by linarith
  have hpow : (y : ℝ) ^ (-(2 * σ)) ≤ 2 * (K : ℝ) ^ (-b) := by
    calc (y : ℝ) ^ (-(2 * σ)) ≤ ((K : ℝ) ^ e / 2) ^ (-(2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hy2 (by linarith)
      _ = (2 : ℝ) ^ (2 * σ) * (K : ℝ) ^ (-b) := by
          rw [Real.div_rpow hKe (by norm_num), ← Real.rpow_mul hK0R.le, Real.rpow_neg (by norm_num)]
          have hexp : e * -(2 * σ) = -b := by rw [mul_neg, hbdef]
          rw [hexp]
          field_simp
      _ ≤ 2 * (K : ℝ) ^ (-b) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc (2 : ℝ) ^ (2 * σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hsplitK : (K : ℝ) ^ (-b) = (K : ℝ) ^ (-gap) * (K : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hK0R, hgapdef]
    congr 1
    ring
  have hKa : 0 < (K : ℝ) ^ (-a) := Real.rpow_pos_of_pos hK0R _
  have hKg : (K : ℝ) ^ (-gap) * (K : ℝ) ^ gap = 1 := by
    rw [← Real.rpow_add hK0R]
    simp
  have hKgpos : 0 < (K : ℝ) ^ (-gap) := Real.rpow_pos_of_pos hK0R _
  -- The polylogarithm.
  have hpoly : 8 * (C + 5 * (1 + 8 * u)) * (5 + 2 * (8 * u)) * (1 + 8 * u) ≤ 1024 * A * (1 + w) ^ 3 := by
    have h4 : (C + 5 * (1 + 8 * u)) ≤ A * (1 + w) := hAu.trans (mul_le_mul_of_nonneg_left (by linarith) hA0.le)
    have h5 : 5 + 2 * (8 * u) ≤ 16 * (1 + w) := by linarith
    have h6 : 1 + 8 * u ≤ 8 * (1 + w) := by linarith
    have h7 : 0 ≤ C + 5 * (1 + 8 * u) := by positivity
    calc 8 * (C + 5 * (1 + 8 * u)) * (5 + 2 * (8 * u)) * (1 + 8 * u)
        ≤ 8 * (A * (1 + w)) * (16 * (1 + w)) * (8 * (1 + w)) := by gcongr
      _ = _ := by ring
  rw [hY₀def]
  have e1 : 8 * ((y : ℝ) ^ (-(2 * σ)) * (C + 5 * (1 + 8 * u)) * (5 + 2 * (8 * u))) * (1 + 8 * u) =
      (y : ℝ) ^ (-(2 * σ)) * (8 * (C + 5 * (1 + 8 * u)) * (5 + 2 * (8 * u)) * (1 + 8 * u)) := by ring
  rw [e1]
  have hK3' : 2100 * A * (1 + w) ^ 3 * (K : ℝ) ^ (-gap) ≤ 1 := by
    have h8 := mul_le_mul_of_nonneg_right hK3 hKgpos.le
    rw [mul_comm ((K : ℝ) ^ gap), hKg] at h8
    exact h8
  have hw3 : 0 ≤ (1 + w) ^ 3 := by positivity
  calc (y : ℝ) ^ (-(2 * σ)) * (8 * (C + 5 * (1 + 8 * u)) * (5 + 2 * (8 * u)) * (1 + 8 * u))
      ≤ (2 * (K : ℝ) ^ (-b)) * (1024 * A * (1 + w) ^ 3) :=
        mul_le_mul hpow hpoly (by positivity) (by positivity)
    _ = (2048 * A * (1 + w) ^ 3 * (K : ℝ) ^ (-gap)) * (K : ℝ) ^ (-a) := by
        rw [hsplitK]
        ring
    _ ≤ (2100 * A * (1 + w) ^ 3 * (K : ℝ) ^ (-gap)) * (K : ℝ) ^ (-a) := by
        refine mul_le_mul_of_nonneg_right ?_ hKa.le
        refine mul_le_mul_of_nonneg_right ?_ hKgpos.le
        nlinarith
    _ ≤ 1 * (K : ℝ) ^ (-a) := mul_le_mul_of_nonneg_right hK3' hKa.le
    _ = _ := one_mul _

/-- **The rate from a zero-free strip.** If `ζ ≠ 0` on `Re s > Θ`, `½ ≤ Θ < 1`, there are integer producers of rate `K^{-a}` for every `a < 2(1 − Θ)/(5 − 2Θ)`. -/
theorem hasRate_of_zeroFree_quarter {Θ a : ℝ} (hΘh : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) (ha0 : 0 < a) (ha : a < 2 * (1 - Θ) / (5 - 2 * Θ)) :
    HasRate fun K => (K : ℝ) ^ (-a) := by
  have hd : 0 < 5 - 2 * Θ := by linarith
  have ha' : a * (5 - 2 * Θ) < 2 * (1 - Θ) := by rwa [lt_div_iff₀ hd] at ha
  have ha1 : a < 1 := by
    by_contra h
    push Not at h
    nlinarith
  have h1a : 0 < 2 - 2 * a := by linarith
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁, σ₁ = 3 * a / (2 - 2 * a) := ⟨_, rfl⟩
  have hσ₁lt : σ₁ < 1 - Θ := by
    rw [hσ₁, div_lt_iff₀ h1a]
    nlinarith
  have hσ₁0 : 0 < σ₁ := by rw [hσ₁]; positivity
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (σ₁ + (1 - Θ)) / 2 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hσ12 : σ ≤ 1 / 2 := by rw [hσ]; linarith
  have hσgt : σ₁ < σ := by rw [hσ]; linarith
  obtain ⟨C, hC, hM⟩ := exists_mertens_power_of_zeroFree hΘh hΘ1 hzf hσ0 (by rw [hσ]; linarith)
  refine hasRate_of_power_quarter hC hσ0 hσ12 (fun n hn => ?_) ha0 ?_
  · rw [mertens_eq_mertensM]
    exact hM n hn
  · rw [lt_div_iff₀ (by linarith : 0 < 3 + 2 * σ)]
    have h3 : 3 * a < σ * (2 - 2 * a) := by
      have : σ₁ * (2 - 2 * a) = 3 * a := by
        rw [hσ₁]
        field_simp
      nlinarith
    linarith

/-- **The Riemann hypothesis gives every rate below `K^{-1/4}`.** -/
theorem hasRate_of_riemannHypothesis_quarter (h : RiemannHypothesis) {a : ℝ} (ha0 : 0 < a)
    (ha : a < 1 / 4) : HasRate fun K => (K : ℝ) ^ (-a) := by
  have hzf : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → riemannZeta s ≠ 0 := by
    intro s hs
    by_cases h1 : s.re < 1
    · exact (RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp h) s hs h1
    · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1)
  refine hasRate_of_zeroFree_quarter (Θ := 1 / 2) le_rfl (by norm_num) hzf ha0 ?_
  norm_num
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
