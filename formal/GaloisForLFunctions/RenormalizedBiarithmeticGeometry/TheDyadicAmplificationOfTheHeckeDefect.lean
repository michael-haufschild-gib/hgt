import GaloisForLFunctions.ConjugateDiagonalGeometry.TwoScaleDepthRigidity

/-!
# The dyadic amplification of the Hecke defect

For a compact `C²` test `f`, let `D = D(f)` be the collided mass of the zeta divisor and
`E(L) = D(T_L f) + D(T_{−L} f) − 2D(f) = Σ_ρ w_ρ (2cosh(2δ_ρ L) − 2)` the symmetric Hecke defect.
Two-scale rigidity `E(L)² ≤ D(E(2L) − 4E(L))` says `E(2L) ≥ a_D(E(L))` for the amplification map
`a_D(e) = 4e + e²/D`, and `a_D` conjugates to doubling of the angle:
`a_D(D(2cosh θ − 2)) = D(2cosh 2θ − 2)` (`amplify_cosh`).

* **Dyadic amplification with fixed loss** (`heckeDefect_dyadic_ge`). If
  `E(L) ≥ D(2cosh θ − 2)` then `E(2^k L) ≥ D(2cosh(2^k θ) − 2)` for every `k`. The loss `D(f)` does
  not depend on `k`: the collided mass is a non-scaling invariant, the arithmetic stand-in for the
  genus in Weil's tensor-power argument. With the strip bound this is a sandwich
  `D(2cosh(2^k θ) − 2) ≤ E(2^k L) ≤ D(2cosh(2^k L) − 2)` (`heckeDefect_dyadic_sandwich`).
* **Lossless transfer to small scales** (`heckeDefect_le_of_dyadic_le`). An upper bound
  `E(2^k L) ≤ D(2cosh(2^k φ) − 2)` at one dyadic scale gives `E(L) ≤ D(2cosh φ − 2)`.
* **Growth decides blindness** (`heckeDefect_eq_zero_of_dyadic_subexp`). If `E(2^k L)` grows slower
  than every `exp(ε 2^k)`, then `E(L) = 0`: the test sees no off-line zero.
* **RH as a growth rate** (`riemannHypothesis_iff_dyadic_subexp`). RH holds iff for every compact
  `C²` test the dyadic Hecke defects `E(2^k)` are `O(exp(ε 2^k))` for every `ε > 0`.

A source-side bound on the Hecke defect is needed at one large dyadic scale only.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open Zeta23 GaloisForLFunctions.ConjugateDiagonalGeometry GaloisForLFunctions.ArithmeticPolarization

/-! ### The amplification map -/

/-- The dyadic amplification map `e ↦ 4e + e²/D`. -/
def amplify (D e : ℝ) : ℝ := 4 * e + e ^ 2 / D

theorem amplify_nonneg {D e : ℝ} (hD : 0 < D) (he : 0 ≤ e) : 0 ≤ amplify D e := by
  unfold amplify; positivity

theorem amplify_lt_amplify {D a b : ℝ} (hD : 0 < D) (ha : 0 ≤ a) (hab : a < b) :
    amplify D a < amplify D b := by
  unfold amplify
  have : a ^ 2 / D ≤ b ^ 2 / D :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab.le 2) hD.le
  linarith

theorem amplify_le_amplify {D a b : ℝ} (hD : 0 < D) (ha : 0 ≤ a) (hab : a ≤ b) :
    amplify D a ≤ amplify D b := by
  rcases hab.lt_or_eq with h | rfl
  · exact (amplify_lt_amplify hD ha h).le
  · exact le_rfl

/-- **The amplification map doubles the angle**: `a_D(D(2cosh θ − 2)) = D(2cosh 2θ − 2)`. -/
theorem amplify_cosh {D : ℝ} (hD : 0 < D) (θ : ℝ) :
    amplify D (D * (2 * Real.cosh θ - 2)) = D * (2 * Real.cosh (2 * θ) - 2) := by
  have h2 : Real.cosh (2 * θ) = 2 * Real.cosh θ ^ 2 - 1 := by
    rw [Real.cosh_two_mul, Real.sinh_sq]; ring
  rw [amplify, h2]
  field_simp
  ring

theorem iterate_amplify_nonneg {D : ℝ} (hD : 0 < D) :
    ∀ (k : ℕ) {e : ℝ}, 0 ≤ e → 0 ≤ (amplify D)^[k] e
  | 0, _, he => he
  | k + 1, _, he => by
    rw [Function.iterate_succ_apply']
    exact amplify_nonneg hD (iterate_amplify_nonneg hD k he)

theorem iterate_amplify_lt {D : ℝ} (hD : 0 < D) :
    ∀ (k : ℕ) {a b : ℝ}, 0 ≤ a → a < b → (amplify D)^[k] a < (amplify D)^[k] b
  | 0, _, _, _, hab => hab
  | k + 1, _, _, ha, hab => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact amplify_lt_amplify hD (iterate_amplify_nonneg hD k ha) (iterate_amplify_lt hD k ha hab)

theorem iterate_amplify_le {D : ℝ} (hD : 0 < D) (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (amplify D)^[k] a ≤ (amplify D)^[k] b := by
  rcases hab.lt_or_eq with h | rfl
  · exact (iterate_amplify_lt hD k ha h).le
  · exact le_rfl

/-- Iterating the amplification map multiplies the angle by `2^k`. -/
theorem iterate_amplify_cosh {D : ℝ} (hD : 0 < D) :
    ∀ (k : ℕ) (θ : ℝ), (amplify D)^[k] (D * (2 * Real.cosh θ - 2)) =
      D * (2 * Real.cosh (2 ^ k * θ) - 2)
  | 0, θ => by simp
  | k + 1, θ => by
    rw [Function.iterate_succ_apply', iterate_amplify_cosh hD k θ, amplify_cosh hD, pow_succ,
      mul_comm (2 ^ k : ℝ) 2, mul_assoc]

theorem two_mul_cosh_sub_two_nonneg (θ : ℝ) : 0 ≤ 2 * Real.cosh θ - 2 := by
  linarith [Real.one_le_cosh θ]

/-! ### Dyadic amplification of the Hecke defect -/

/-- The collided mass of a compact test. -/
abbrev mass (f : CompactTest) : ℝ := collidedForm zetaZeroConfig f.1

theorem mass_nonneg (f : CompactTest) : 0 ≤ mass f :=
  tsum_nonneg fun ρ => zetaWeight_nonneg f ρ

/-- The strip bound: `E(L) ≤ D(2cosh L − 2)`. -/
theorem heckeDefect_le_mass_cosh (f : CompactTest) (L : ℝ) :
    heckeDefect f L ≤ mass f * (2 * Real.cosh L - 2) := by
  have h := heckeDefect_le_strip f L
  rw [depthKernel, show 2 * (1 / 2 : ℝ) * L = L by ring, mul_comm] at h
  exact h

theorem mass_pos_of_heckeDefect_pos {f : CompactTest} {L : ℝ} (h : 0 < heckeDefect f L) :
    0 < mass f := by
  rcases (mass_nonneg f).lt_or_eq with hD | hD
  · exact hD
  · have := heckeDefect_le_mass_cosh f L
    rw [← hD, zero_mul] at this
    linarith

/-- One doubling step: `E(2L) ≥ a_D(E(L))`. -/
theorem amplify_heckeDefect_le (f : CompactTest) (L : ℝ) (hD : 0 < mass f) :
    amplify (mass f) (heckeDefect f L) ≤ heckeDefect f (2 * L) := by
  have h : heckeDefect f L ^ 2 ≤ mass f * (heckeDefect f (2 * L) - 4 * heckeDefect f L) :=
    heckeDefect_sq_le_two_scale f L
  rw [amplify]
  have : heckeDefect f L ^ 2 / mass f ≤ heckeDefect f (2 * L) - 4 * heckeDefect f L := by
    rw [div_le_iff₀ hD]; linarith
  linarith

/-- Iterated doubling: `E(2^k L) ≥ a_D^k(E(L))`. -/
theorem iterate_amplify_heckeDefect_le (f : CompactTest) (L : ℝ) (hD : 0 < mass f) :
    ∀ k : ℕ, (amplify (mass f))^[k] (heckeDefect f L) ≤ heckeDefect f (2 ^ k * L)
  | 0 => by simp
  | k + 1 => by
    rw [Function.iterate_succ_apply', pow_succ, mul_comm (2 ^ k : ℝ) 2, mul_assoc]
    exact (amplify_le_amplify hD (iterate_amplify_nonneg hD k (heckeDefect_nonneg f L))
      (iterate_amplify_heckeDefect_le f L hD k)).trans (amplify_heckeDefect_le f _ hD)

/-- **Dyadic amplification with fixed loss.** If `E(L) ≥ D(2cosh θ − 2)`, then
`E(2^k L) ≥ D(2cosh(2^k θ) − 2)` for all `k`. -/
theorem heckeDefect_dyadic_ge (f : CompactTest) (L θ : ℝ)
    (h : mass f * (2 * Real.cosh θ - 2) ≤ heckeDefect f L) (k : ℕ) :
    mass f * (2 * Real.cosh (2 ^ k * θ) - 2) ≤ heckeDefect f (2 ^ k * L) := by
  rcases (mass_nonneg f).lt_or_eq with hD | hD
  · rw [← iterate_amplify_cosh hD]
    exact (iterate_amplify_le hD k (mul_nonneg hD.le (two_mul_cosh_sub_two_nonneg θ)) h).trans
      (iterate_amplify_heckeDefect_le f L hD k)
  · rw [← hD, zero_mul]
    exact heckeDefect_nonneg f _

/-- **The dyadic sandwich**: between the effective angle `θ` read at scale `L` and the strip
angle. -/
theorem heckeDefect_dyadic_sandwich (f : CompactTest) (L θ : ℝ)
    (h : mass f * (2 * Real.cosh θ - 2) ≤ heckeDefect f L) (k : ℕ) :
    mass f * (2 * Real.cosh (2 ^ k * θ) - 2) ≤ heckeDefect f (2 ^ k * L) ∧
      heckeDefect f (2 ^ k * L) ≤ mass f * (2 * Real.cosh (2 ^ k * L) - 2) :=
  ⟨heckeDefect_dyadic_ge f L θ h k, heckeDefect_le_mass_cosh f _⟩

/-- **Lossless transfer to small scales.** An upper bound at the dyadic scale `2^k L` with angle
`2^k φ` bounds the defect at scale `L` with angle `φ`. -/
theorem heckeDefect_le_of_dyadic_le (f : CompactTest) (L φ : ℝ) (k : ℕ)
    (h : heckeDefect f (2 ^ k * L) ≤ mass f * (2 * Real.cosh (2 ^ k * φ) - 2)) :
    heckeDefect f L ≤ mass f * (2 * Real.cosh φ - 2) := by
  rcases (mass_nonneg f).lt_or_eq with hD | hD
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := iterate_amplify_lt hD k (mul_nonneg hD.le (two_mul_cosh_sub_two_nonneg φ)) hlt
    rw [iterate_amplify_cosh hD] at h1
    linarith [iterate_amplify_heckeDefect_le f L hD k]
  · have := heckeDefect_le_mass_cosh f L
    rw [← hD, zero_mul] at this ⊢
    exact this

/-! ### Growth decides blindness -/

/-- A positive defect admits a positive effective angle. -/
theorem exists_angle_of_heckeDefect_pos {f : CompactTest} {L : ℝ} (h : 0 < heckeDefect f L) :
    ∃ θ : ℝ, 0 < θ ∧ mass f * (2 * Real.cosh θ - 2) ≤ heckeDefect f L := by
  have hc : Tendsto (fun θ : ℝ => mass f * (2 * Real.cosh θ - 2)) (𝓝[>] 0)
      (𝓝 (mass f * (2 * Real.cosh 0 - 2))) :=
    ((continuous_const.mul ((continuous_const.mul Real.continuous_cosh).sub
      continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [Real.cosh_zero, show (2 : ℝ) * 1 - 2 = 0 by norm_num, mul_zero] at hc
  obtain ⟨θ, hθ, hθpos⟩ := ((hc.eventually (gt_mem_nhds h)).and self_mem_nhdsWithin).exists
  exact ⟨θ, hθpos, hθ.le⟩

/-- **Growth decides blindness.** If the dyadic defects `E(2^k L)` grow slower than every
`exp(ε 2^k)`, the test sees no off-line zero at scale `L`. -/
theorem heckeDefect_eq_zero_of_dyadic_subexp (f : CompactTest) (L : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
      heckeDefect f (2 ^ k * L) ≤ C * Real.exp (ε * 2 ^ k)) :
    heckeDefect f L = 0 := by
  by_contra hne
  have hpos : 0 < heckeDefect f L := lt_of_le_of_ne (heckeDefect_nonneg f L) (Ne.symm hne)
  have hD := mass_pos_of_heckeDefect_pos hpos
  obtain ⟨θ, hθ, hθE⟩ := exists_angle_of_heckeDefect_pos hpos
  obtain ⟨C, hC⟩ := h (θ / 2) (by positivity)
  set M : ℝ := (|C| + 2 * mass f) / mass f + 1
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M / θ)
  set y : ℝ := Real.exp (θ / 2 * 2 ^ k)
  have hy1 : 1 ≤ y := Real.one_le_exp (by positivity)
  have hyM : M < y := by
    have hk2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h1 : M < θ / 2 * 2 ^ k := by
      rw [div_lt_iff₀ hθ] at hk
      nlinarith
    linarith [Real.add_one_le_exp (θ / 2 * 2 ^ k)]
  -- `D(y² − 2) ≤ E(2^k L) ≤ C y`, impossible for `y > M`.
  have hlow := heckeDefect_dyadic_ge f L θ hθE k
  have hcosh : Real.exp (2 ^ k * θ) ≤ 2 * Real.cosh (2 ^ k * θ) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(2 ^ k * θ))]
  have hy2 : Real.exp (2 ^ k * θ) = y ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hup := hC k
  have hDy : mass f * (y ^ 2 - 2) ≤ C * y := by
    calc mass f * (y ^ 2 - 2) ≤ mass f * (2 * Real.cosh (2 ^ k * θ) - 2) := by
          rw [← hy2]; exact mul_le_mul_of_nonneg_left (by linarith) hD.le
      _ ≤ C * y := hlow.trans hup
  have hMy : (|C| + 2 * mass f) / mass f < y := by linarith
  rw [div_lt_iff₀ hD] at hMy
  nlinarith [le_abs_self C, abs_nonneg C]

/-! ### RH as a growth rate -/

/-- Under RH every zero has depth `0`, so every Hecke defect vanishes. -/
theorem heckeDefect_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) (f : CompactTest)
    (L : ℝ) : heckeDefect f L = 0 := by
  rw [heckeDefect]
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hre : (ρ : ℂ).re = 1 / 2 := hRH ρ hρ.1 (fun ⟨n, hn⟩ => by
      have := hρ.2.1; rw [hn] at this; simp at this; linarith [(by positivity : (0 : ℝ) ≤ n)])
    (fun h1 => by rw [h1] at hρ; exact absurd hρ.2.2 (by norm_num))
  rw [zetaDepth, hre, sub_self, depthKernel, mul_zero, zero_mul, Real.cosh_zero]
  ring

/-- A vanishing defect at one nonzero scale makes the collided form Hecke invariant. -/
theorem collidedForm_translate_eq_of_heckeDefect_eq_zero (f : CompactTest)
    (h : heckeDefect f 1 = 0) (L : ℝ) :
    collidedForm zetaZeroConfig (ArithmeticPolarization.translate L f.1) =
      collidedForm zetaZeroConfig f.1 := by
  have hterm : ∀ ρ, zetaWeight f ρ * depthKernel 1 (zetaDepth ρ) = 0 := by
    have hs := (summable_heckeDefect f 1).hasSum
    rw [← heckeDefect, h] at hs
    have hz := (hasSum_zero_iff_of_nonneg fun ρ =>
      mul_nonneg (zetaWeight_nonneg f ρ) (depthKernel_nonneg _ _)).mp hs
    exact fun ρ => congrFun hz ρ
  rw [collidedForm_translate, collidedForm]
  refine tsum_congr fun ρ => ?_
  rcases mul_eq_zero.mp (hterm ρ) with hw | hk
  · have hw' : (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f.1 ρ) = 0 := hw
    rw [mul_right_comm, hw', zero_mul]
  · rcases (depthKernel_eq_zero_iff 1 (zetaDepth ρ)).mp hk with hd | h10
    · rw [zetaDepth] at hd
      rw [hd, mul_zero, zero_mul, Real.exp_zero, mul_one]
    · exact absurd h10 one_ne_zero

/-- **RH as a growth rate.** RH holds iff for every compact `C²` test the dyadic Hecke defects
`E(2^k)` grow slower than every `exp(ε 2^k)`. -/
theorem riemannHypothesis_iff_dyadic_subexp :
    RiemannHypothesis ↔ ∀ f : CompactTest, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ k : ℕ,
      heckeDefect f (2 ^ k) ≤ C * Real.exp (ε * 2 ^ k) := by
  constructor
  · intro hRH f ε _
    exact ⟨0, fun k => by rw [heckeDefect_eq_zero_of_riemannHypothesis hRH, zero_mul]⟩
  · intro h
    rw [riemannHypothesis_iff_collided_hecke_invariant]
    intro g hg hgc L
    set f : CompactTest := ⟨fun u => (g u : ℂ),
      Complex.ofRealCLM.contDiff.comp hg, hgc.comp_left Complex.ofReal_zero⟩
    have h0 : heckeDefect f 1 = 0 := heckeDefect_eq_zero_of_dyadic_subexp f 1 (by
      intro ε hε
      obtain ⟨C, hC⟩ := h f ε hε
      exact ⟨C, fun k => by rw [mul_one]; exact hC k⟩)
    exact collidedForm_translate_eq_of_heckeDefect_eq_zero f h0 L

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
