import GaloisForLFunctions.BezoutValuationIncidence.ReciprocityFormOfTheBernoulliKernel
import GaloisForLFunctions.RHTower.Sieve.KuzminLandau
import GaloisForLFunctions.RHTower.DiscreteVanDerCorput

/-!
# The Kuzmin–Landau gain for flat small-scale rows

The coherent obstruction concerns arbitrary small-scale coefficients. For the flat row
`c(d) = d` on `[D₁, D₂)` (all moduli of the interval, `a_d = 1` in `Σ a_d b_n 𝒢(d, n)`) the kernel is
summed over the small modulus first:

`Col(n) = Σ_{D₁ ≤ d < D₂} 𝔅(d, n)`,  `𝔅(d, n) + π²/72 = (d²/2) Σ_j B₂({jn/d})/j²`.

With `B₂({y}) = π⁻² Σ_h cos(2πhy)/h²` the column becomes a combination of the reciprocal-phase sums
`T(x) = Σ_d d² cos(2πx/d)`, `x = hjn`. Their phase increments `x/(d(d+1))` are monotone. While
`x ≤ X₀ = D₁(D₁+1)/2` they lie in `[x/D₂², 1/2]`, and the Kuzmin–Landau inequality with Abel summation
against `d²` gives `|T(x)| ≤ 3D₂⁴/x + 2D₂²`. Beyond `X₀` the trivial bound `W₂ = Σ_d d²` is summed over
the tail `hj > X₀/n`. For every `J ≥ 1`

`|Col(n) + (π²/72)(D₂ - D₁)| ≤ (12 D₂⁴/n + 8 D₂² + 2 W₂ h_J n/X₀)/(2π²) + W₂/(6J)`.

For `c'` above `Q` and `[D₁, D₂) = [P, 2P)`, the rank-two remainder bound `≍ S₀ P³` improves to
`≍ S₀(P⁴/Q + PQ log P)`, a gain `P/Q + (Q/P²) log P`. For flat small-scale rows and arbitrary
large-scale coefficients, the cross-scale form has diagonal quality for `Q ≥ P^{3/2} log P`
(exponent `θ` up to `4/3`), beyond the Type-II barrier `Q ≥ P^{5/3}`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Kuzmin–Landau for the reciprocal phase -/

/-- **Reciprocal phases.** If `0 < x`, `2x ≤ D₁(D₁+1)`, `1 ≤ D₁ ≤ D' ≤ D₂`, then
`|Σ_{D₁ ≤ d < D'} e(x/d)| ≤ 3D₂²/(2x) + 1`. -/
theorem norm_sum_Ico_exp_div_le {x : ℝ} {D₁ D₂ D' : ℕ} (hD₁ : 1 ≤ D₁) (hx : 0 < x)
    (hxD : 2 * x ≤ (D₁ : ℝ) * ((D₁ : ℝ) + 1)) (h1 : D₁ ≤ D') (h2 : D' ≤ D₂) :
    ‖∑ d ∈ Ico D₁ D', Complex.exp (((2 * Real.pi * (x / d) : ℝ) : ℂ) * Complex.I)‖ ≤
      3 * (D₂ : ℝ) ^ 2 / (2 * x) + 1 := by
  rcases Nat.eq_or_lt_of_le h1 with heq | hlt
  · subst heq
    simp only [Ico_self, sum_empty, norm_zero]
    positivity
  set M := D' - D₁ - 1
  have hM : D' - D₁ = M + 1 := by omega
  set ψ : ℕ → ℝ := fun m => x / ((D' - 1 - m : ℕ) : ℝ)
  have hD₂R : (1 : ℝ) ≤ D₂ := by exact_mod_cast (le_trans hD₁ (le_trans h1 h2))
  set δ : ℝ := x / (D₂ : ℝ) ^ 2
  have hδ0 : 0 < δ := by positivity
  -- the increments
  have hinc : ∀ m < M, ψ (m + 1) - ψ m =
      x / (((D' - 2 - m : ℕ) : ℝ) * ((D' - 1 - m : ℕ) : ℝ)) := by
    intro m hm
    have hd1 : D' - 1 - (m + 1) = D' - 2 - m := by omega
    have hpos1 : (0 : ℝ) < ((D' - 2 - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < D' - 2 - m)
    have hcast : ((D' - 1 - m : ℕ) : ℝ) = ((D' - 2 - m : ℕ) : ℝ) + 1 := by
      rw [show D' - 1 - m = (D' - 2 - m) + 1 by omega]; push_cast; ring
    simp only [ψ, hd1]
    rw [hcast]
    field_simp
    ring
  have hlo : ∀ m < M, δ ≤ ψ (m + 1) - ψ m := by
    intro m hm
    rw [hinc m hm]
    have ha : (0 : ℝ) < ((D' - 2 - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < D' - 2 - m)
    have hb : ((D' - 2 - m : ℕ) : ℝ) * ((D' - 1 - m : ℕ) : ℝ) ≤ (D₂ : ℝ) ^ 2 := by
      have h3 : ((D' - 2 - m : ℕ) : ℝ) ≤ D₂ := by exact_mod_cast (by omega : D' - 2 - m ≤ D₂)
      have h4 : ((D' - 1 - m : ℕ) : ℝ) ≤ D₂ := by exact_mod_cast (by omega : D' - 1 - m ≤ D₂)
      nlinarith [Nat.cast_nonneg (α := ℝ) (D' - 1 - m)]
    have hc : (0 : ℝ) < ((D' - 1 - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < D' - 1 - m)
    exact div_le_div_of_nonneg_left hx.le (mul_pos ha hc) hb
  have hhi : ∀ m < M, ψ (m + 1) - ψ m ≤ 1 - δ := by
    intro m hm
    rw [hinc m hm]
    have ha : (D₁ : ℝ) ≤ ((D' - 2 - m : ℕ) : ℝ) := by exact_mod_cast (by omega : D₁ ≤ D' - 2 - m)
    have hb : (D₁ : ℝ) + 1 ≤ ((D' - 1 - m : ℕ) : ℝ) := by
      have := (by omega : D₁ + 1 ≤ D' - 1 - m); exact_mod_cast this
    have hD₁R : (1 : ℝ) ≤ D₁ := by exact_mod_cast hD₁
    have hden : (D₁ : ℝ) * ((D₁ : ℝ) + 1) ≤ ((D' - 2 - m : ℕ) : ℝ) * ((D' - 1 - m : ℕ) : ℝ) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    have hpos : (0 : ℝ) < ((D' - 2 - m : ℕ) : ℝ) * ((D' - 1 - m : ℕ) : ℝ) :=
      mul_pos (by linarith) (by linarith)
    have hhalf : x / (((D' - 2 - m : ℕ) : ℝ) * ((D' - 1 - m : ℕ) : ℝ)) ≤ 1 / 2 := by
      rw [div_le_iff₀ hpos]
      linarith
    have hδhalf : δ ≤ 1 / 2 := by
      simp only [δ]
      rw [div_le_iff₀ (by positivity)]
      have : (D₁ : ℝ) + 1 ≤ D₂ := by exact_mod_cast (by omega : D₁ + 1 ≤ D₂)
      nlinarith
    linarith
  have hmono : ∀ m, m + 1 < M → ψ (m + 1) - ψ m ≤ ψ (m + 2) - ψ (m + 1) := by
    intro m hm
    rw [hinc m (by omega), show ψ (m + 2) - ψ (m + 1) = ψ (m + 1 + 1) - ψ (m + 1) by rfl,
      hinc (m + 1) hm]
    refine div_le_div_of_nonneg_left hx.le ?_ ?_
    · have : (0 : ℝ) < ((D' - 2 - (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < D' - 2 - (m + 1))
      have : (0 : ℝ) < ((D' - 1 - (m + 1) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < D' - 1 - (m + 1))
      positivity
    · have e1 : ((D' - 2 - (m + 1) : ℕ) : ℝ) ≤ ((D' - 2 - m : ℕ) : ℝ) := by
        exact_mod_cast (by omega : D' - 2 - (m + 1) ≤ D' - 2 - m)
      have e2 : ((D' - 1 - (m + 1) : ℕ) : ℝ) ≤ ((D' - 1 - m : ℕ) : ℝ) := by
        exact_mod_cast (by omega : D' - 1 - (m + 1) ≤ D' - 1 - m)
      exact mul_le_mul e1 e2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hKL := kuzminLandau_band ψ M hδ0 hlo hhi hmono
  have hre : ∑ d ∈ Ico D₁ D', Complex.exp (((2 * Real.pi * (x / d) : ℝ) : ℂ) * Complex.I) =
      ∑ m ∈ range (M + 1), Complex.exp (((2 * Real.pi * ψ m : ℝ) : ℂ) * Complex.I) := by
    rw [← hM, sum_Ico_eq_sum_range]
    rw [← Finset.sum_range_reflect]
    refine sum_congr rfl fun m hm => ?_
    have hm' := mem_range.mp hm
    simp only [ψ]
    congr 4
    rw [show D₁ + (D' - D₁ - 1 - m) = D' - 1 - m by omega]
  rw [hre]
  refine hKL.trans (le_of_eq ?_)
  simp only [δ]
  field_simp

/-! ## §2. Abel summation against an increasing weight -/

/-- `|Σ_{D₁ ≤ d < D₂} g(d) z_d| ≤ 2 g(D₂ - 1) B` for a nonnegative monotone `g` when all initial sums
`Σ_{D₁ ≤ d < D'} z_d` have norm at most `B`. -/
theorem norm_sum_Ico_mono_mul_le {g : ℕ → ℝ} {z : ℕ → ℂ} {D₁ D₂ : ℕ} {B : ℝ} (hD : D₁ < D₂)
    (hg0 : ∀ d, 0 ≤ g d) (hmono : Monotone g)
    (hB : ∀ D', D₁ ≤ D' → D' ≤ D₂ → ‖∑ d ∈ Ico D₁ D', z d‖ ≤ B) :
    ‖∑ d ∈ Ico D₁ D₂, (g d : ℂ) * z d‖ ≤ 2 * g (D₂ - 1) * B := by
  set L := D₂ - D₁
  -- reverse the order so that the weight decreases
  have hrev : ∑ d ∈ Ico D₁ D₂, (g d : ℂ) * z d =
      ∑ m ∈ range L, ((g (D₂ - 1 - m) : ℝ) : ℂ) * z (D₂ - 1 - m) := by
    rw [sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
    refine sum_congr rfl fun m hm => ?_
    have := mem_range.mp hm
    rw [show D₁ + (L - 1 - m) = D₂ - 1 - m by omega]
  rw [hrev]
  have hB0 : 0 ≤ B := le_trans (by simp) (hB D₁ le_rfl hD.le)
  have hanti : Antitone fun m => g (D₂ - 1 - m) := fun a b hab => hmono (by omega)
  set b : ℕ → ℂ := fun m => if m < L then z (D₂ - 1 - m) else 0
  have hpartL : ∀ k, k ≤ L → ‖∑ j ∈ range k, z (D₂ - 1 - j)‖ ≤ 2 * B := by
    intro k hk
    have hsplit : ∑ j ∈ range k, z (D₂ - 1 - j) =
        ∑ d ∈ Ico D₁ D₂, z d - ∑ d ∈ Ico D₁ (D₂ - k), z d := by
      rw [← sum_Ico_consecutive _ (by omega : D₁ ≤ D₂ - k) (by omega : D₂ - k ≤ D₂),
        add_sub_cancel_left, sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
      rw [show D₂ - (D₂ - k) = k by omega]
      refine sum_congr rfl fun j hj => ?_
      have := mem_range.mp hj
      congr 1
      omega
    rw [hsplit]
    calc ‖∑ d ∈ Ico D₁ D₂, z d - ∑ d ∈ Ico D₁ (D₂ - k), z d‖
        ≤ ‖∑ d ∈ Ico D₁ D₂, z d‖ + ‖∑ d ∈ Ico D₁ (D₂ - k), z d‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB D₂ hD.le le_rfl) (hB _ (by omega) (by omega))
      _ = 2 * B := by ring
  have hpart : ∀ k, ‖∑ j ∈ range k, b j‖ ≤ 2 * B := by
    intro k
    have hb : ∑ j ∈ range k, b j = ∑ j ∈ range (min k L), z (D₂ - 1 - j) := by
      rw [← sum_range_add_sum_Ico b (min_le_left k L)]
      have h0 : ∑ j ∈ Ico (min k L) k, b j = 0 := sum_eq_zero fun j hj => by
        have := mem_Ico.mp hj
        simp only [b]; rw [if_neg (by omega)]
      rw [h0, add_zero]
      exact sum_congr rfl fun j hj => by
        have := mem_range.mp hj
        simp only [b]; rw [if_pos (by omega)]
    rw [hb]
    exact hpartL _ (min_le_right k L)
  have h := norm_sum_amplitude_phase_le hanti (fun m => hg0 _) hpart L
  have hsum : ∑ m ∈ range L, ((g (D₂ - 1 - m) : ℝ) : ℂ) * b m =
      ∑ m ∈ range L, ((g (D₂ - 1 - m) : ℝ) : ℂ) * z (D₂ - 1 - m) :=
    sum_congr rfl fun m hm => by simp only [b]; rw [if_pos (mem_range.mp hm)]
  rw [hsum] at h
  calc ‖∑ m ∈ range L, ((g (D₂ - 1 - m) : ℝ) : ℂ) * z (D₂ - 1 - m)‖
      ≤ g (D₂ - 1 - 0) * (2 * B) := h
    _ = 2 * g (D₂ - 1) * B := by rw [Nat.sub_zero]; ring

/-! ## §3. The reciprocal-phase sum `T(x) = Σ_d d² cos(2πx/d)` -/

/-- `|Σ_{D₁ ≤ d < D₂} d² cos(2πx/d)| ≤ 3D₂⁴/x + 2D₂²` when `0 < x ≤ D₁(D₁+1)/2`. -/
theorem abs_sum_Ico_sq_mul_cos_div_le {x : ℝ} {D₁ D₂ : ℕ} (hD₁ : 1 ≤ D₁) (hD : D₁ < D₂) (hx : 0 < x)
    (hxD : 2 * x ≤ (D₁ : ℝ) * ((D₁ : ℝ) + 1)) :
    |∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * x / d)| ≤
      3 * (D₂ : ℝ) ^ 4 / x + 2 * (D₂ : ℝ) ^ 2 := by
  set z : ℕ → ℂ := fun d => Complex.exp (((2 * Real.pi * (x / d) : ℝ) : ℂ) * Complex.I)
  have hre : ∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * x / d) =
      (∑ d ∈ Ico D₁ D₂, (((d : ℝ) ^ 2 : ℝ) : ℂ) * z d).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [Complex.re_ofReal_mul]
    simp only [z]
    rw [Complex.exp_ofReal_mul_I_re]
    congr 2
    ring
  have hmono : Monotone fun d : ℕ => (d : ℝ) ^ 2 := fun a b hab => by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hab := norm_sum_Ico_mono_mul_le (g := fun d : ℕ => (d : ℝ) ^ 2) (z := z) hD
    (fun d => sq_nonneg _) hmono
    (fun D' h1 h2 => norm_sum_Ico_exp_div_le hD₁ hx hxD h1 h2)
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hab.trans ?_)
  have hD₂ : ((D₂ - 1 : ℕ) : ℝ) ≤ D₂ := by exact_mod_cast Nat.sub_le D₂ 1
  have hD₂0 : (0 : ℝ) ≤ ((D₂ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : ((D₂ - 1 : ℕ) : ℝ) ^ 2 ≤ (D₂ : ℝ) ^ 2 := pow_le_pow_left₀ hD₂0 hD₂ 2
  have hpos : 0 ≤ 3 * (D₂ : ℝ) ^ 2 / (2 * x) + 1 := by positivity
  calc 2 * ((D₂ - 1 : ℕ) : ℝ) ^ 2 * (3 * (D₂ : ℝ) ^ 2 / (2 * x) + 1)
      ≤ 2 * (D₂ : ℝ) ^ 2 * (3 * (D₂ : ℝ) ^ 2 / (2 * x) + 1) := by gcongr
    _ = 3 * (D₂ : ℝ) ^ 4 / x + 2 * (D₂ : ℝ) ^ 2 := by field_simp

/-! ## §4. Truncated Fourier series -/

/-- The tail of a series with terms `|f h| ≤ C/(h+1)²` after `H₁` terms is at most `C/H₁`. -/
theorem abs_hasSum_sub_partial_le {f : ℕ → ℝ} {s C : ℝ} (hf : HasSum f s) (hC : 0 ≤ C)
    (hb : ∀ h, |f h| ≤ C / ((h : ℝ) + 1) ^ 2) {H₁ : ℕ} (hH : 1 ≤ H₁) :
    |s - ∑ h ∈ range H₁, f h| ≤ C / H₁ := by
  have hlim : Tendsto (fun K => |∑ h ∈ range K, f h - ∑ h ∈ range H₁, f h|) atTop
      (𝓝 |s - ∑ h ∈ range H₁, f h|) := (hf.tendsto_sum_nat.sub_const _).abs
  refine le_of_tendsto hlim (eventually_atTop.mpr ⟨H₁, fun K hK => ?_⟩)
  rw [← sum_range_add_sum_Ico f hK, add_sub_cancel_left]
  calc |∑ h ∈ Ico H₁ K, f h| ≤ ∑ h ∈ Ico H₁ K, |f h| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ range K, C * (if H₁ ≤ h then 1 / ((h : ℝ) + 1) ^ 2 else 0) := by
        rw [← sum_range_add_sum_Ico _ hK]
        have h0 : 0 ≤ ∑ h ∈ range H₁, C * (if H₁ ≤ h then 1 / ((h : ℝ) + 1) ^ 2 else 0) :=
          sum_nonneg fun h _ => by split_ifs <;> positivity
        refine le_trans ?_ (le_add_of_nonneg_left h0)
        refine sum_le_sum fun h hh => ?_
        rw [if_pos (mem_Ico.mp hh).1, mul_one_div]
        exact hb h
    _ = C * ∑ h ∈ range K, (if H₁ ≤ h then 1 / ((h : ℝ) + 1) ^ 2 else 0) := by rw [mul_sum]
    _ ≤ C * (1 / (H₁ : ℝ)) := mul_le_mul_of_nonneg_left (sum_range_ite_ge_div_sq_le hH K) hC
    _ = C / H₁ := by ring

theorem abs_bernoulliTwo_le {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliTwo x| ≤ 1 / 6 := by
  obtain ⟨h0, h1⟩ := hx
  unfold bernoulliTwo
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - 1 / 2)]

/-- `Φ_d(m) + 1/12 = (d²/(2π²)) Σ_{h ≥ 1} cos(2πhm/d)/h²`. -/
theorem hasSum_residuePotential_add {d : ℕ} (hd : 0 < d) (m : ℕ) :
    HasSum (fun h : ℕ => (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) *
      (Real.cos (2 * Real.pi * ((h + 1) * m : ℕ) / d) / ((h : ℝ) + 1) ^ 2))
      (residuePotential d m + 1 / 12) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set x : ℝ := ((m % d : ℕ) : ℝ) / d
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
    have hlt : ((m % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt _ hd
    exact ⟨by positivity, by rw [div_le_one hdR]; exact hlt.le⟩
  have hs := (hasSum_cos_div_sq hx).mul_left ((d : ℝ) ^ 2 / (2 * Real.pi ^ 2))
  have hval : (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) * (Real.pi ^ 2 * bernoulliTwo x) =
      residuePotential d m + 1 / 12 := by
    rw [residuePotential_eq_bernoulli hd]
    simp only [bernoulliTwo, x]
    field_simp
    ring
  rw [hval] at hs
  refine hs.congr_fun fun h => ?_
  congr 2
  -- reduce the phase modulo one
  have hdiv := Nat.div_add_mod m d
  have hm : ((h + 1) * m : ℕ) = ((h + 1) * (m / d) * d : ℕ) + (h + 1) * (m % d) := by
    calc (h + 1) * m = (h + 1) * (d * (m / d) + m % d) := by rw [hdiv]
      _ = _ := by ring
  have hphase : 2 * Real.pi * (((h + 1) * m : ℕ) : ℝ) / d =
      2 * Real.pi * ((h : ℝ) + 1) * x + (((h + 1) * (m / d) : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hm]
    simp only [x]
    push_cast
    field_simp
    ring
  rw [hphase, Real.cos_add_nat_mul_two_pi]

/-! ## §5. The column of a flat interval of small moduli -/

theorem sum_range_inv_sq_le (J : ℕ) : ∑ j ∈ range J, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have h := sum_le_hasSum (range J) (fun j _ => by positivity) hz
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

theorem sum_range_inv_cube_le (J : ℕ) : ∑ j ∈ range J, 1 / ((j : ℝ) + 1) ^ 3 ≤ 2 := by
  refine le_trans (sum_le_sum fun j _ => ?_) (sum_range_inv_sq_le J)
  have h1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem sum_range_inv_eq (J : ℕ) : ∑ j ∈ range J, 1 / ((j : ℝ) + 1) = ∑ k ∈ Icc 1 J, 1 / (k : ℝ) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]; push_cast; ring

/-- The count of the trivial range: `Σ_{h, (h+1)a > X} 1/(h+1)² ≤ 2a/X`. -/
theorem sum_range_ite_tail_le {a X : ℝ} (ha : 0 < a) (hX : 0 < X) (H : ℕ) :
    ∑ h ∈ range H, (if X < ((h : ℝ) + 1) * a then 1 / ((h : ℝ) + 1) ^ 2 else 0) ≤ 2 * a / X := by
  set h₀ := ⌊X / a⌋₊
  rcases Nat.eq_zero_or_pos h₀ with h0 | h0
  · have hXa : X / a < 1 := by
      have h' : X / a < (h₀ : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [h0] at h'; simpa using h'
    have hlt : X < a := by rwa [div_lt_one ha] at hXa
    calc ∑ h ∈ range H, (if X < ((h : ℝ) + 1) * a then 1 / ((h : ℝ) + 1) ^ 2 else 0)
        ≤ ∑ h ∈ range H, 1 / ((h : ℝ) + 1) ^ 2 :=
          sum_le_sum fun h _ => by split_ifs <;> [exact le_rfl; positivity]
      _ ≤ 2 := sum_range_inv_sq_le H
      _ ≤ 2 * a / X := by rw [le_div_iff₀ hX]; linarith
  · have hfl : (h₀ : ℝ) ≤ X / a := Nat.floor_le (by positivity)
    have hfl' : X / a < (h₀ : ℝ) + 1 := Nat.lt_floor_add_one _
    calc ∑ h ∈ range H, (if X < ((h : ℝ) + 1) * a then 1 / ((h : ℝ) + 1) ^ 2 else 0)
        ≤ ∑ h ∈ range H, (if h₀ ≤ h then 1 / ((h : ℝ) + 1) ^ 2 else 0) := by
          refine sum_le_sum fun h _ => ?_
          by_cases hc : X < ((h : ℝ) + 1) * a
          · rw [if_pos hc, if_pos]
            have h2 : X / a < (h : ℝ) + 1 := by rw [div_lt_iff₀ ha]; linarith
            have h3 : (h₀ : ℝ) < ((h + 1 : ℕ) : ℝ) := by push_cast; linarith
            have h4 : h₀ < h + 1 := by exact_mod_cast h3
            omega
          · rw [if_neg hc]; split_ifs <;> positivity
      _ ≤ 1 / (h₀ : ℝ) := sum_range_ite_ge_div_sq_le h0 H
      _ ≤ 2 * a / X := by
          have hh0 : (1 : ℝ) ≤ h₀ := by exact_mod_cast h0
          rw [div_le_div_iff₀ (by positivity) hX]
          have : X < a * ((h₀ : ℝ) + 1) := by rw [div_lt_iff₀ ha] at hfl'; linarith
          nlinarith

/-- **The flat column.** For `1 ≤ D₁ < D₂`, `n ≥ 1`, `J ≥ 1`, with `W₂ = Σ_{D₁ ≤ d < D₂} d²`,
`X₀ = D₁(D₁+1)/2`, `h_J = Σ_{k ≤ J} 1/k`:
`|Σ_d 𝔅(d, n) + (π²/72)(D₂ - D₁)| ≤ (12 D₂⁴/n + 8 D₂² + 2 W₂ h_J n/X₀)/(2π²) + W₂/(5J)`. -/
theorem abs_sum_Ico_bernoulliKernel_add_le {D₁ D₂ n J : ℕ} (hD₁ : 1 ≤ D₁) (hD : D₁ < D₂)
    (hn : 1 ≤ n) (hJ : 1 ≤ J) :
    |∑ d ∈ Ico D₁ D₂, bernoulliKernel d n + Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁)| ≤
      (12 * (D₂ : ℝ) ^ 4 / n + 8 * (D₂ : ℝ) ^ 2 +
          2 * (∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2) * (∑ k ∈ Icc 1 J, 1 / (k : ℝ)) * n /
            ((D₁ : ℝ) * ((D₁ : ℝ) + 1) / 2)) / (2 * Real.pi ^ 2) +
        (∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2) / (5 * J) := by
  set W₂ := ∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2
  set hJs := ∑ k ∈ Icc 1 J, 1 / (k : ℝ)
  set X₀ : ℝ := (D₁ : ℝ) * ((D₁ : ℝ) + 1) / 2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hD₁R : (1 : ℝ) ≤ D₁ := by exact_mod_cast hD₁
  have hX₀ : 0 < X₀ := by positivity
  have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  -- per modulus: the shifted kernel as a series and its truncations
  set g : ℕ → ℕ → ℝ := fun d j => (residuePotential d ((j + 1) * n) + 1 / 12) / ((j : ℝ) + 1) ^ 2
  set c : ℕ → ℕ → ℕ → ℝ := fun d j h => (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) *
    (Real.cos (2 * Real.pi * ((h + 1) * ((j + 1) * n) : ℕ) / d) / ((h : ℝ) + 1) ^ 2)
  have hgsum : ∀ d ∈ Ico D₁ D₂, HasSum (g d) (bernoulliKernel d n + Real.pi ^ 2 / 72) := by
    intro d hd
    have hd0 : 0 < d := by have := (mem_Ico.mp hd).1; omega
    have h := (hasSum_bernoulliKernel hd0 n).add (hz.mul_left (1 / 12))
    convert h using 1
    · ext j; simp only [g]; ring
    · ring
  have hgbound : ∀ d ∈ Ico D₁ D₂, ∀ j, |g d j| ≤ (d : ℝ) ^ 2 / 12 / ((j : ℝ) + 1) ^ 2 := by
    intro d hd j
    have hd0 : 0 < d := by have := (mem_Ico.mp hd).1; omega
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    simp only [g]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hB := residuePotential_eq_bernoulli hd0 ((j + 1) * n)
    set x : ℝ := (((j + 1) * n % d : ℕ) : ℝ) / d
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
      have hlt : (((j + 1) * n % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt _ hd0
      exact ⟨by positivity, by rw [div_le_one hdR]; exact hlt.le⟩
    have hb := abs_bernoulliTwo_le hx
    have hrw : residuePotential d ((j + 1) * n) + 1 / 12 = (d : ℝ) ^ 2 / 2 * bernoulliTwo x := by
      rw [hB]; simp only [bernoulliTwo, x]; ring
    rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2 / 2)]
    nlinarith [sq_nonneg (d : ℝ)]
  have htrunc_j : ∀ d ∈ Ico D₁ D₂, |bernoulliKernel d n + Real.pi ^ 2 / 72 -
      ∑ j ∈ range J, g d j| ≤ (d : ℝ) ^ 2 / 12 / J := fun d hd =>
    abs_hasSum_sub_partial_le (hgsum d hd) (by positivity) (hgbound d hd) hJ
  have hcsum : ∀ d ∈ Ico D₁ D₂, ∀ j, HasSum (c d j) (residuePotential d ((j + 1) * n) + 1 / 12) :=
    fun d hd j => hasSum_residuePotential_add (by have := (mem_Ico.mp hd).1; omega) _
  have hcbound : ∀ d ∈ Ico D₁ D₂, ∀ j h, |c d j h| ≤ (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) / ((h : ℝ) + 1) ^ 2 := by
    intro d _ j h
    simp only [c]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2 / (2 * Real.pi ^ 2)), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < ((h : ℝ) + 1) ^ 2), mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have htrunc_h : ∀ d ∈ Ico D₁ D₂, ∀ j, |residuePotential d ((j + 1) * n) + 1 / 12 -
      ∑ h ∈ range J, c d j h| ≤ (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) / J := fun d hd j =>
    abs_hasSum_sub_partial_le (hcsum d hd j) (by positivity) (hcbound d hd j) hJ
  -- three-part decomposition
  set A₁ := ∑ d ∈ Ico D₁ D₂, (bernoulliKernel d n + Real.pi ^ 2 / 72 - ∑ j ∈ range J, g d j)
  set A₂ := ∑ d ∈ Ico D₁ D₂, ∑ j ∈ range J,
    (residuePotential d ((j + 1) * n) + 1 / 12 - ∑ h ∈ range J, c d j h) / ((j : ℝ) + 1) ^ 2
  set A₃ := ∑ d ∈ Ico D₁ D₂, ∑ j ∈ range J, ∑ h ∈ range J, c d j h / ((j : ℝ) + 1) ^ 2
  have hdecomp : ∑ d ∈ Ico D₁ D₂, bernoulliKernel d n + Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) =
      A₁ + A₂ + A₃ := by
    have hL : Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) = ∑ _d ∈ Ico D₁ D₂, Real.pi ^ 2 / 72 := by
      rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hD.le]; ring
    rw [hL, ← sum_add_distrib]
    simp only [A₁, A₂, A₃, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    have hg : ∑ j ∈ range J, g d j = ∑ j ∈ range J,
        ((residuePotential d ((j + 1) * n) + 1 / 12 - ∑ h ∈ range J, c d j h) / ((j : ℝ) + 1) ^ 2 +
          ∑ h ∈ range J, c d j h / ((j : ℝ) + 1) ^ 2) := by
      refine sum_congr rfl fun j _ => ?_
      simp only [g]
      rw [← sum_div]
      ring
    rw [hg, sum_add_distrib]
    ring
  have hA₁ : |A₁| ≤ W₂ / (12 * J) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [show W₂ / (12 * J) = ∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 / 12 / J by
      simp only [W₂]; rw [sum_div]; exact sum_congr rfl fun d _ => by ring]
    exact sum_le_sum htrunc_j
  have hA₂ : |A₂| ≤ W₂ / (Real.pi ^ 2 * J) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [show W₂ / (Real.pi ^ 2 * J) = ∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) / J * 2 by
      simp only [W₂]; rw [sum_div]; exact sum_congr rfl fun d _ => by field_simp]
    refine sum_le_sum fun d hd => ?_
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range J, |(residuePotential d ((j + 1) * n) + 1 / 12 - ∑ h ∈ range J, c d j h) /
          ((j : ℝ) + 1) ^ 2|
        ≤ ∑ j ∈ range J, (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) / J * (1 / ((j : ℝ) + 1) ^ 2) := by
          refine sum_le_sum fun j _ => ?_
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2), ← mul_one_div]
          exact mul_le_mul_of_nonneg_right (htrunc_h d hd j) (by positivity)
      _ = (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) / J * ∑ j ∈ range J, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [mul_sum]
      _ ≤ (d : ℝ) ^ 2 / (2 * Real.pi ^ 2) / J * 2 :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_le J) (by positivity)
  -- the main part through the reciprocal-phase sums
  set x : ℕ → ℕ → ℝ := fun j h => (((h + 1) * ((j + 1) * n) : ℕ) : ℝ)
  have hx : ∀ j h, x j h = ((h : ℝ) + 1) * (((j : ℝ) + 1) * n) := fun j h => by
    simp only [x]; push_cast; ring
  have hxpos : ∀ j h, 0 < x j h := fun j h => by rw [hx]; positivity
  have hA₃eq : A₃ = 1 / (2 * Real.pi ^ 2) * ∑ j ∈ range J, ∑ h ∈ range J,
      1 / (((j : ℝ) + 1) ^ 2 * ((h : ℝ) + 1) ^ 2) *
        ∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * x j h / d) := by
    simp only [A₃, c, x]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun d _ => ?_
    field_simp
  have hT : ∀ j h, |∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * x j h / d)| ≤
      3 * (D₂ : ℝ) ^ 4 / x j h + 2 * (D₂ : ℝ) ^ 2 + (if X₀ < x j h then W₂ else 0) := by
    intro j h
    by_cases hc : X₀ < x j h
    · rw [if_pos hc]
      have htriv : |∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * x j h / d)| ≤ W₂ := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)
      have : 0 ≤ 3 * (D₂ : ℝ) ^ 4 / x j h + 2 * (D₂ : ℝ) ^ 2 := by
        have := hxpos j h; positivity
      linarith
    · rw [if_neg hc, add_zero]
      exact abs_sum_Ico_sq_mul_cos_div_le hD₁ hD (hxpos j h) (by simp only [X₀] at hc; linarith)
  have hA₃ : |A₃| ≤ (12 * (D₂ : ℝ) ^ 4 / n + 8 * (D₂ : ℝ) ^ 2 + 2 * W₂ * hJs * n / X₀) /
      (2 * Real.pi ^ 2) := by
    rw [hA₃eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi ^ 2)),
      one_div_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    set w : ℕ → ℕ → ℝ := fun j h => 1 / (((j : ℝ) + 1) ^ 2 * ((h : ℝ) + 1) ^ 2)
    have hw0 : ∀ j h, 0 ≤ w j h := fun j h => by positivity
    set u : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) ^ 3
    set v : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) ^ 2
    set t : ℕ → ℕ → ℝ := fun j h =>
      if X₀ < ((h : ℝ) + 1) * (((j : ℝ) + 1) * n) then 1 / ((h : ℝ) + 1) ^ 2 else 0
    have hterm : ∀ j h, w j h *
        (3 * (D₂ : ℝ) ^ 4 / x j h + 2 * (D₂ : ℝ) ^ 2 + (if X₀ < x j h then W₂ else 0)) =
        3 * (D₂ : ℝ) ^ 4 / n * (u j * u h) + 2 * (D₂ : ℝ) ^ 2 * (v j * v h) + W₂ * (v j * t j h) := by
      intro j h
      simp only [w, u, v, t]
      rw [hx]
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hh : (0 : ℝ) < (h : ℝ) + 1 := by positivity
      have hn0 : (0 : ℝ) < n := by linarith
      split_ifs
      all_goals field_simp
      all_goals ring
    have hu := sum_range_inv_cube_le J
    have hv := sum_range_inv_sq_le J
    have hu0 : 0 ≤ ∑ j ∈ range J, u j := sum_nonneg fun j _ => by positivity
    have hv0 : 0 ≤ ∑ j ∈ range J, v j := sum_nonneg fun j _ => by positivity
    have hW₂0 : 0 ≤ W₂ := sum_nonneg fun d _ => sq_nonneg _
    have htail : ∀ j, ∑ h ∈ range J, t j h ≤ 2 * (((j : ℝ) + 1) * n) / X₀ := fun j =>
      sum_range_ite_tail_le (by positivity) hX₀ J
    calc |∑ j ∈ range J, ∑ h ∈ range J, w j h *
          ∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2 * Real.cos (2 * Real.pi * x j h / d)|
        ≤ ∑ j ∈ range J, ∑ h ∈ range J, w j h *
            (3 * (D₂ : ℝ) ^ 4 / x j h + 2 * (D₂ : ℝ) ^ 2 + (if X₀ < x j h then W₂ else 0)) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h _ => ?_)
          rw [abs_mul, abs_of_nonneg (hw0 j h)]
          exact mul_le_mul_of_nonneg_left (hT j h) (hw0 j h)
      _ = 3 * (D₂ : ℝ) ^ 4 / n * ((∑ j ∈ range J, u j) * ∑ h ∈ range J, u h) +
            2 * (D₂ : ℝ) ^ 2 * ((∑ j ∈ range J, v j) * ∑ h ∈ range J, v h) +
            W₂ * ∑ j ∈ range J, v j * ∑ h ∈ range J, t j h := by
          rw [sum_congr rfl fun j _ => sum_congr rfl fun h _ => hterm j h, sum_mul_sum, sum_mul_sum,
            mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
          refine sum_congr rfl fun j _ => ?_
          simp only [sum_add_distrib, mul_sum]
      _ ≤ 3 * (D₂ : ℝ) ^ 4 / n * (2 * 2) + 2 * (D₂ : ℝ) ^ 2 * (2 * 2) +
            W₂ * ∑ j ∈ range J, v j * (2 * (((j : ℝ) + 1) * n) / X₀) := by
          have h1 : (∑ j ∈ range J, u j) * ∑ h ∈ range J, u h ≤ 2 * 2 :=
            mul_le_mul hu hu hu0 (by norm_num)
          have h2 : (∑ j ∈ range J, v j) * ∑ h ∈ range J, v h ≤ 2 * 2 :=
            mul_le_mul hv hv hv0 (by norm_num)
          have h3 : ∑ j ∈ range J, v j * ∑ h ∈ range J, t j h ≤
              ∑ j ∈ range J, v j * (2 * (((j : ℝ) + 1) * n) / X₀) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (htail j) (by positivity)
          have hA : 0 ≤ 3 * (D₂ : ℝ) ^ 4 / n := by positivity
          have hB : 0 ≤ 2 * (D₂ : ℝ) ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB,
            mul_le_mul_of_nonneg_left h3 hW₂0]
      _ = 12 * (D₂ : ℝ) ^ 4 / n + 8 * (D₂ : ℝ) ^ 2 + 2 * W₂ * hJs * n / X₀ := by
          have hsum : ∑ j ∈ range J, v j * (2 * (((j : ℝ) + 1) * n) / X₀) =
              2 * n / X₀ * ∑ j ∈ range J, 1 / ((j : ℝ) + 1) := by
            rw [mul_sum]
            refine sum_congr rfl fun j _ => ?_
            simp only [v]
            have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
            field_simp
          rw [hsum, sum_range_inv_eq J]
          simp only [hJs]
          ring
  rw [hdecomp]
  have hW₂ : 0 ≤ W₂ := sum_nonneg fun d _ => sq_nonneg _
  have hlast : W₂ / (12 * J) + W₂ / (Real.pi ^ 2 * J) ≤ W₂ / (5 * J) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    have hJ0 : (0 : ℝ) < J := by linarith
    nlinarith [mul_nonneg hW₂ hJ0.le, mul_nonneg (mul_nonneg hW₂ hJ0.le) hJ0.le]
  calc |A₁ + A₂ + A₃| ≤ |A₁| + |A₂| + |A₃| := abs_add_three _ _ _
    _ ≤ W₂ / (12 * J) + W₂ / (Real.pi ^ 2 * J) +
          (12 * (D₂ : ℝ) ^ 4 / n + 8 * (D₂ : ℝ) ^ 2 + 2 * W₂ * hJs * n / X₀) / (2 * Real.pi ^ 2) :=
        add_le_add (add_le_add hA₁ hA₂) hA₃
    _ ≤ _ := by linarith

/-! ## §6. Flat small-scale rows -/

/-- The flat row `c(d) = d` on `[D₁, D₂)` (`a_d = 1` in `Σ a_d b_n 𝒢(d, n)`). -/
def flatRow (D₁ D₂ : ℕ) (d : ℕ) : ℝ := if d ∈ Ico D₁ D₂ then (d : ℝ) else 0

/-- **The Kuzmin–Landau gain.** For the flat row on `[D₁, D₂) ⊆ [1, N]` and every large-scale row
`c'`, with `W₂ = Σ_{D₁ ≤ d < D₂} d²`, `X₀ = D₁(D₁+1)/2` and `J ≥ 1`,
`|B + m R' + β H' + (π²/72)(D₂ - D₁) Σ_n c'(n)/n²|
  ≤ Σ_n (|c'(n)|/n²) ((12 D₂⁴/n + 8 D₂² + 2 W₂ h_J n/X₀)/(2π²) + W₂/(5J))
    + ¾ (Σ_d |c(d)| d²) Σ_n |c'(n)|/n³`. -/
theorem abs_rowBilinear_flatRow_add_le {N D₁ D₂ J : ℕ} (hD₁ : 1 ≤ D₁) (hD : D₁ < D₂)
    (hD₂N : D₂ ≤ N + 1) (hJ : 1 ≤ J) (c' : ℕ → ℝ) :
    |rowBilinear N (flatRow D₁ D₂) c' + rowMean N (flatRow D₁ D₂) * vonMangoldtReadout N c' +
        rowBeta N (flatRow D₁ D₂) * finiteHarmonicSum N c' +
        Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2| ≤
      ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 *
          ((12 * (D₂ : ℝ) ^ 4 / n + 8 * (D₂ : ℝ) ^ 2 +
              2 * (∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2) * (∑ k ∈ Icc 1 J, 1 / (k : ℝ)) * n /
                ((D₁ : ℝ) * ((D₁ : ℝ) + 1) / 2)) / (2 * Real.pi ^ 2) +
            (∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2) / (5 * J)) +
        3 / 4 * (∑ d ∈ Icc 1 N, |flatRow D₁ D₂ d| * (d : ℝ) ^ 2) *
          ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  set c := flatRow D₁ D₂
  have hsub : Ico D₁ D₂ ⊆ Icc 1 N := fun d hd => by
    have := mem_Ico.mp hd; exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set M := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  have hM : M = ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * ∑ d ∈ Ico D₁ D₂, bernoulliKernel d n := by
    simp only [M]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_subset hsub fun d _ hd => by simp [c, flatRow, hd], mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by have := (mem_Ico.mp hd).1; omega : 0 < d)
    simp only [c, flatRow, if_pos hd]
    field_simp
  set colB : ℕ → ℝ := fun n => (12 * (D₂ : ℝ) ^ 4 / n + 8 * (D₂ : ℝ) ^ 2 +
    2 * (∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2) * (∑ k ∈ Icc 1 J, 1 / (k : ℝ)) * n /
      ((D₁ : ℝ) * ((D₁ : ℝ) + 1) / 2)) / (2 * Real.pi ^ 2) + (∑ d ∈ Ico D₁ D₂, (d : ℝ) ^ 2) / (5 * J)
  have hMb : |M + Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2| ≤
      ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 * colB n := by
    rw [hM, mul_sum, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hcol := abs_sum_Ico_bernoulliKernel_add_le hD₁ hD hn1 hJ
    rw [show c' n / (n : ℝ) ^ 2 * ∑ d ∈ Ico D₁ D₂, bernoulliKernel d n +
        Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) * (c' n / (n : ℝ) ^ 2) =
        c' n / (n : ℝ) ^ 2 * (∑ d ∈ Ico D₁ D₂, bernoulliKernel d n +
          Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁)) by ring, abs_mul, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_left hcol (by positivity)
  have htri := abs_add_le (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - M)
    (M + Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2)
  have heq : rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c' - M +
      (M + Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) =
      rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
      rowBeta N c * finiteHarmonicSum N c' +
      Real.pi ^ 2 / 72 * ((D₂ : ℝ) - D₁) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 := by ring
  rw [heq] at htri
  simp only [colB] at hMb
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
