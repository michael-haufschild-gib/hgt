import GaloisForLFunctions.SquareRootThreshold.ZetaUniformTwinRadiusOfNearTopZeros

/-!
# Hiding needs near-top twins at every lag

Lag grids see attained tops (`LagGridsSeeAttainedTops`), and chains with no top zero hide from them
(`ChainsHideFromLagGrids`). For `ζ` the attained top is replaced by a near-top zero at large height,
which always exists when the top is not attained, together with the modulation of the bump to its
height.

* **Near-top zeros at every height** (`exists_high_near_top_zero`). If some zero lies right of the
  line and no zero has the largest real part, then for every `V > 0` and every `T` there is a zero
  above height `T` within `1/V` of the supremum `Θ` of the real parts: the finitely many zeros
  below `T` stay below `Θ` by a fixed amount.
* **An explicit height** (`nearTopHeight`, `nearTopHeight_conditions`). Beyond
  `T_w = 1 + 700000(e^{w/2}B_w)²/a_w²` the reflected zero is negligible at the centre of the
  modulated family and loud records sit at height `≥ γ₀/2`.
* **Trichotomy** (`zeta_hiding_needs_near_top_twins`). For every `V > 0` and `T` there is a
  `1/V`-near-top zero `½ + z₀` above `max(T, T_w)` such that, for the bump modulated to its height
  `γ₀`, either a difference test is Weil negative at a lag `v ≤ V`, or `V < V_w(z₀)`
  (`hidingLag`), or the Legendre record has a twin within `R_w(γ₀)/V`, `R_w(γ₀) =
  73(κ_w + π log log(180(Γ + 6)) + 4π)`, `Γ ≤ 2γ₀` for large `γ₀`.

The escape `V < V_w(z₀)` reads `log log γ₀ ≳ V Re z₀`: hiding without twins needs every near-top zero
above `T_w` at doubly exponential height `γ₀ ≥ exp exp(c_w Θ V)`, against `exp(cV³)` for the
one-parameter family. What replaces the attainment premise of the grids is a near-top zero below
that height together with the modulation to its height; what remains is the twin, a pair of zeros
closer than `(log log γ₀)/V`, which is the pair-correlation barrier at the square-root threshold.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### High near-top zeros replace the attained top -/

/-- **Near-top zeros at every height.** If some zero of `ζ` lies right of the line and no zero has the
largest real part, then for every `V > 0` and every height `T` there is a zero `ρ` right of the
line, above `T`, with `Re ρ' ≤ Re ρ + 1/V` for every zero `ρ'`. -/
theorem exists_high_near_top_zero (hoff : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re)
    (hna : ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re)
    {V : ℝ} (hV : 0 < V) (T : ℝ) :
    ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re ∧ T < ρ.im ∧
      ∀ ρ' ∈ zetaZeroConfig.carrier, ρ'.re ≤ ρ.re + 1 / V := by
  classical
  obtain ⟨ρ₁, hρ₁, hre₁⟩ := hoff
  set S : Set ℝ := Complex.re '' zetaZeroConfig.carrier with hS
  have hSb : BddAbove S := ⟨1, by
    rintro x ⟨ρ, hρ, rfl⟩; exact (zetaZeroConfig.strip ρ hρ).2⟩
  have hSne : S.Nonempty := ⟨ρ₁.re, ρ₁, hρ₁, rfl⟩
  set β := sSup S with hβ
  have hle : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ β := fun ρ hρ => le_csSup hSb ⟨ρ, hρ, rfl⟩
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < β := fun ρ hρ => by
    obtain ⟨ρ', hρ', h⟩ := hna ρ hρ; exact lt_of_lt_of_le h (hle ρ' hρ')
  -- the low zeros stay below `β`
  set F := zetaZeroConfig.carrier ∩ {ρ : ℂ | -|T| - 1 < ρ.im ∧ ρ.im ≤ |T|} with hF
  have hFfin : F.Finite := zetaZeroConfig.finite_window _ _
  obtain ⟨m, hmβ, hm⟩ : ∃ m < β, ∀ ρ ∈ F, ρ.re ≤ m := by
    rcases F.eq_empty_or_nonempty with hFe | hFne
    · exact ⟨ρ₁.re, hlt ρ₁ hρ₁, fun ρ hρ => by rw [hFe] at hρ; exact absurd hρ (Set.notMem_empty _)⟩
    · obtain ⟨ρ₀, hρ₀F, hmax⟩ := hFfin.exists_maximalFor Complex.re F hFne
      refine ⟨ρ₀.re, hlt ρ₀ hρ₀F.1, fun ρ hρ => ?_⟩
      by_contra h; push Not at h
      exact absurd (hmax hρ h.le) (not_le.mpr h)
  set t := max (max m (β - 1 / V)) (1 / 2) with ht
  have htβ : t < β := by
    have h1 : β - 1 / V < β := by linarith [one_div_pos.mpr hV]
    have h2 : 1 / 2 < β := lt_of_lt_of_le hre₁ (hle ρ₁ hρ₁)
    exact max_lt (max_lt hmβ h1) h2
  obtain ⟨x, ⟨ρ, hρ, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hSne htβ
  have hρm : m < ρ.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hx
  have hρV : β - 1 / V < ρ.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hx
  have hρh : 1 / 2 < ρ.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hρF : ρ ∉ F := fun h => absurd (hm ρ h) (not_le.mpr hρm)
  have hnear : ∀ ρ' ∈ zetaZeroConfig.carrier, ρ'.re ≤ ρ.re + 1 / V := fun ρ' hρ' => by
    linarith [hle ρ' hρ']
  by_cases him : |T| < ρ.im
  · exact ⟨ρ, hρ, hρh, lt_of_le_of_lt (le_abs_self T) him, hnear⟩
  · have hlow : ρ.im ≤ -|T| - 1 := by
      by_contra h; push Not at h
      exact hρF ⟨hρ, h, not_lt.mp him⟩
    refine ⟨conj ρ, conj_mem_zetaZeroConfig hρ, by simpa using hρh, ?_, fun ρ' hρ' => ?_⟩
    · rw [Complex.conj_im]; linarith [le_abs_self T]
    · rw [Complex.conj_re]; exact hnear ρ' hρ'

/-! ### An explicit height beyond which the modulated family is centred -/

/-- The height `T_w = 1 + 700000 (e^{w/2}B_w)²/a_w²` beyond which the modulated family is centred. -/
def nearTopHeight (w : ℝ) : ℝ :=
  1 + 700000 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2

/-- Beyond `T_w` the reflected zero is negligible at the centre and loud records sit near `±γ`. -/
theorem nearTopHeight_conditions {w γ : ℝ} (hw : 0 < w) (hγ : nearTopHeight w ≤ γ) :
    40 * Real.log (180 * γ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + 2 * γ) ^ 4 ≤
        centerAmplitude w ^ 2 / 2 ∧
      80 * Real.log (90 * γ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ / 2) ^ 4 <
        centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hK0 : 0 ≤ K₀ := by positivity
  have hT : 1 + 700000 * K₀ / a ^ 2 ≤ γ := by
    have := hγ; unfold nearTopHeight at this; rw [← hK₀, ← ha] at this; exact this
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ 700000 * K₀ / a ^ 2 := by positivity
    linarith
  have hγ0 : 0 < γ := by linarith
  have hγ3 : γ ≤ γ ^ 3 := by
    have h2 : 1 ≤ γ ^ 2 := one_le_pow₀ hγ1
    calc γ = γ * 1 := by ring
      _ ≤ γ * γ ^ 2 := mul_le_mul_of_nonneg_left h2 hγ0.le
      _ = γ ^ 3 := by ring
  have hKa : 700000 * K₀ ≤ a ^ 2 * γ ^ 3 := by
    have h1 : 700000 * K₀ / a ^ 2 ≤ γ := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have : a ^ 2 * γ ≤ a ^ 2 * γ ^ 3 := mul_le_mul_of_nonneg_left hγ3 (by positivity)
    linarith
  have hE : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  constructor
  · have hlog : Real.log (180 * γ) ≤ 180 * γ := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 180 * γ by positivity); linarith
    have hden : 16 * γ ^ 4 ≤ (1 + 2 * γ) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * γ) (by linarith : 2 * γ ≤ 1 + 2 * γ) 4
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc 40 * Real.log (180 * γ) * K₀ ≤ 40 * (180 * γ) * K₀ := by gcongr
      _ ≤ a ^ 2 / 2 * (16 * γ ^ 4) := by nlinarith
      _ ≤ a ^ 2 / 2 * (1 + 2 * γ) ^ 4 := mul_le_mul_of_nonneg_left hden (by positivity)
  · have hlog : Real.log (90 * γ) ≤ 90 * γ := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 90 * γ by positivity); linarith
    have hden : γ ^ 4 / 16 ≤ (1 + γ / 2) ^ 4 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ γ / 2) (by linarith : γ / 2 ≤ 1 + γ / 2) 4
      calc γ ^ 4 / 16 = (γ / 2) ^ 4 := by ring
        _ ≤ _ := this
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hEpos := Real.exp_pos 1
    calc 80 * Real.log (90 * γ) * K₀ * (2 * Real.exp 1) ≤ 80 * (90 * γ) * K₀ * (2 * Real.exp 1) := by
          gcongr
      _ ≤ 80 * (90 * γ) * K₀ * 6 := by gcongr; linarith
      _ < a ^ 2 * (γ ^ 4 / 16) := by
          have : 0 < a ^ 2 * γ := by positivity
          nlinarith
      _ ≤ a ^ 2 * (1 + γ / 2) ^ 4 := mul_le_mul_of_nonneg_left hden (by positivity)

/-! ### The trichotomy -/

/-- The twin radius numerator `R_w(γ₀) = 73(κ_w + π log log(180(Γ + 6)) + 4π)`. -/
def twinRadiusNumerator (w γ₀ : ℝ) : ℝ :=
  73 * (uniformTwinDepth w +
    π * Real.log (Real.log (180 * (recordHeightEnvelope w γ₀ + 6))) + 4 * π)

/-- The hiding lag `V_w(z₀) = max(R_w(γ₀) max(1, 4/δ₀), 2 log(160 log(180Γ)(e^{w/2}B_w)²/a_w²)/δ₀)`,
`δ₀ = Re z₀`, `γ₀ = Im z₀`: below it a near-top zero may hide without a twin. -/
def hidingLag (w : ℝ) (z₀ : ℂ) : ℝ :=
  max (twinRadiusNumerator w z₀.im * max 1 (4 / z₀.re))
    (2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) / z₀.re)

/-- **Hiding needs near-top twins at every lag.** Suppose some zero of `ζ` lies right of the line and
no zero has the largest real part. Fix `w > 0`, `V > 0` and a height `T`. Then there is a zero
`½ + z₀` right of the line, above `max(T, T_w)`, that is `1/V`-near the top, such that one of the
following holds for the family modulated to `γ₀ = Im z₀`:

1. a difference test `κ(t + v/2) − κ(t − v/2)` of the modulated bump is Weil negative at some lag
   `v ∈ [0, V]`;
2. `V < V_w(z₀)` (`hidingLag`): the zero sits so high that `log log γ₀ ≳ V Re z₀`;
3. the Legendre record `z*` at lag `V` has a twin, another zero within `R_w(γ₀)/V` of
   `(Re z* − κ_w/V) + i Im z*`. -/
theorem zeta_hiding_needs_near_top_twins {w : ℝ} (hw : 0 < w)
    (hoff : ∃ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re)
    (hna : ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∃ ρ ∈ zetaZeroConfig.carrier, ρ₀.re < ρ.re)
    {V : ℝ} (hV : 0 < V) (T : ℝ) :
    ∃ z₀ : ℂ, (1 / 2 + z₀) ∈ zetaZeroConfig.carrier ∧ 0 < z₀.re ∧ max T (nearTopHeight w) < z₀.im ∧
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) ∧
      ((∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
          (twoBump (modScaledBump w z₀.im) v (-1))).re < 0) ∨
        V < hidingLag w z₀ ∨
        ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ 0 < z₁.re ∧
          (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
            ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
              ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
          ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
            ‖z - ((z₁.re - uniformTwinDepth w / V : ℝ) + z₁.im * I)‖ <
              twinRadiusNumerator w z₀.im / V) := by
  obtain ⟨ρ, hρ, hreρ, himρ, hnear⟩ := exists_high_near_top_zero hoff hna hV (max T (nearTopHeight w))
  set z₀ : ℂ := ρ - 1 / 2 with hz₀def
  have hρz : 1 / 2 + z₀ = ρ := by rw [hz₀def]; ring
  have hre_eq : z₀.re = ρ.re - 1 / 2 := by simp [hz₀def]
  have hre₀ : 0 < z₀.re := by rw [hre_eq]; linarith
  have him₀ : z₀.im = ρ.im := by simp [hz₀def]
  have hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier := by rw [hρz]; exact hρ
  have hnear₀ : ∀ ρ' ∈ zetaZeroConfig.carrier, ρ'.re - 1 / 2 ≤ z₀.re + 1 / V := fun ρ' hρ' => by
    have := hnear ρ' hρ'
    rw [hre_eq]; linarith
  refine ⟨z₀, hz₀, hre₀, by rw [him₀]; exact himρ, hnear₀, ?_⟩
  have hTw : nearTopHeight w ≤ z₀.im := by rw [him₀]; exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) himρ)
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  obtain ⟨hΓ, hsmall⟩ := nearTopHeight_conditions hw hTw
  -- the modulated exponents are zeros, hence below the top
  have htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 →
      z.re ≤ z₀.re + 1 / V := fun z hz => by
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have := hnear₀ _ h
      have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      linarith
    · have := hnear₀ _ h
      have e : (1 / 2 + conj z).re = 1 / 2 + z.re := by simp
      linarith
  by_cases hneg : ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0
  · exact Or.inl hneg
  push Not at hneg
  by_cases hlag : V < hidingLag w z₀
  · exact Or.inr (Or.inl hlag)
  push Not at hlag
  refine Or.inr (Or.inr ?_)
  have hV1 : twinRadiusNumerator w z₀.im * max 1 (4 / z₀.re) ≤ V :=
    (le_max_left _ _).trans hlag
  have hV2 : 2 * Real.log (160 * Real.log (180 * recordHeightEnvelope w z₀.im) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V := by
    have := (le_max_right _ _).trans hlag
    rw [div_le_iff₀ hre₀] at this; linarith
  obtain ⟨z₁, hz₁, hre₁, -, -, -, hrec, z, hz, hDz, hdist⟩ :=
    zeta_uniform_twin_radius hw hV hz₀ hre₀ hpos₀ hΓ hsmall htop hneg hV1 hV2
  exact ⟨z₁, hz₁, lt_of_lt_of_le (by linarith) hre₁, hrec, z, hz, hDz, hdist⟩

end GaloisForLFunctions.SquareRootThreshold
