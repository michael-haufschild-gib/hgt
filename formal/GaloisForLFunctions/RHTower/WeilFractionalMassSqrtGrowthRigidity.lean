import GaloisForLFunctions.RHTower.WeilAbelianTwistRigidity

/-!
# Real spectral mass of order `o(√T)` forces `Λ` and RH

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1`

`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)
  + Σ_k c_k · 2(s−½)/((s−½)² + u_k²)`,

with integer masses `m_j` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) and real masses `c_k ≥ 0` at
ordinates `u_k ≥ 1`, `u_k → ∞`.

**Theorem** (`fractional_mass_sqrt_growth_rigidity`).  If the real mass below height `y`,
`C(y) = Σ_{u_k < y} c_k`, is `o(√y)`, then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann
hypothesis holds.

The total real mass may be infinite.  `MonotoneTwistLock.fractional_mass_summable_rigidity` is
the case `Σ_k c_k < ∞`.

**Proof.**
* `C(y) ≤ √y + K` gives `Σ_k c_k/u_k² = ∫_1^∞ 2y^{−3} C(y) dy < ∞`
  (`summable_div_sq_of_phaseSum_le`).  This is all the product of the real-mass factors needs, so
  `G = K·Q·R` is a Herglotz producer.
* On the lower half-line `G(1 − s) = e^{2πiC(y)} G(s)`, `s = ½ − iy`.  Each atom below `y`
  contributes its phase `e^{2πic_k}`.
* `C` is monotone and `o(√y)`, so Abelian twist rigidity (`AbelianTwist.abelian_twist_rigidity`)
  applies with `κ₀ = 1`, `β₀ = 2π`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity FractionalMassTailRigidity

noncomputable section

/-- **A linear mass bound `C(y) ≤ Ky + K'` makes `Σ_k c_k/u_k²` finite.**  Each term is
`c_k/u_k² = ∫_{y > u_k} 2c_k y^{−3} dy`, so every finite partial sum is at most
`∫_1^∞ 2y^{−3}(|K|y + |K'|) dy`. -/
theorem summable_div_sq_of_phaseSum_le {c u : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) {K K' : ℝ}
    (hK : ∀ y : ℝ, 1 ≤ y → phaseSum c u y ≤ K * y + K') :
    Summable fun k => c k / u k ^ 2 := by
  set w : ℝ → ℝ := fun y => 2 * y ^ (-3 : ℝ) with hw
  have hwint : IntegrableOn w (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2
  have hw0 : ∀ y ∈ Ioi (1 : ℝ), 0 ≤ w y := fun y hy => by
    have : (0 : ℝ) < y := lt_trans one_pos hy
    simp only [hw]; positivity
  set f : ℕ → ℝ → ℝ := fun k => (Ioi (u k)).indicator fun y => c k * w y with hf
  have hfint : ∀ k, IntegrableOn (f k) (Ioi 1) := fun k =>
    (hwint.const_mul (c k)).indicator measurableSet_Ioi
  have hfk : ∀ k, ∫ y in Ioi (1 : ℝ), f k y = c k / u k ^ 2 := by
    intro k
    have hu0 : 0 < u k := lt_of_lt_of_le one_pos (hu1 k)
    simp only [hf]
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Ioi_subset_Ioi (hu1 k)), integral_const_mul]
    simp only [hw]
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hu0]
    have e : u k ^ ((-3 : ℝ) + 1) = (u k ^ 2)⁻¹ := by
      rw [show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le, Real.rpow_natCast]
    rw [e]
    field_simp
    norm_num
  have hBint : IntegrableOn (fun y => w y * (|K| * y + |K'|)) (Ioi 1) := by
    have h1 : IntegrableOn (fun y : ℝ => 2 * |K| * y ^ (-2 : ℝ) + 2 * |K'| * y ^ (-3 : ℝ))
        (Ioi 1) :=
      ((integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos).const_mul (2 * |K|)).add
        ((integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) one_pos).const_mul (2 * |K'|))
    refine IntegrableOn.congr_fun h1 (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := lt_trans one_pos hy
    simp only [hw]
    have e : y ^ (-3 : ℝ) * y = y ^ (-2 : ℝ) := by
      conv_lhs => rw [show y ^ (-3 : ℝ) * y = y ^ (-3 : ℝ) * y ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hy0]; norm_num
    linear_combination (-2 * |K| : ℝ) * e
  refine summable_of_sum_le (fun k => div_nonneg (hc k) (by positivity))
    (c := ∫ y in Ioi (1 : ℝ), w y * (|K| * y + |K'|)) fun S => ?_
  calc ∑ k ∈ S, c k / u k ^ 2 = ∑ k ∈ S, ∫ y in Ioi (1 : ℝ), f k y :=
        Finset.sum_congr rfl fun k _ => (hfk k).symm
    _ = ∫ y in Ioi (1 : ℝ), ∑ k ∈ S, f k y := (integral_finsetSum S fun k _ => hfint k).symm
    _ ≤ ∫ y in Ioi (1 : ℝ), w y * (|K| * y + |K'|) := by
        refine setIntegral_mono_on (integrable_finsetSum S fun k _ => hfint k) hBint
          measurableSet_Ioi fun y hy => ?_
        have hpt : ∀ k, f k y = w y * (if u k < y then c k else 0) := by
          intro k
          simp only [hf, Set.indicator_apply, mem_Ioi]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl fun k _ => hpt k, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 y hy)
        have hS : ∑ k ∈ S, (if u k < y then c k else 0) ≤ phaseSum c u y :=
          (summable_phaseTerm hut y).sum_le_tsum S fun k _ => by
            split_ifs; exacts [hc k, le_rfl]
        have hy1 : (1 : ℝ) < y := hy
        have := mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith : (0 : ℝ) ≤ y)
        linarith [hK y (le_of_lt hy), le_abs_self K']

/-- **Real spectral mass of order `o(√T)` forces `Λ` and RH.**  The hypotheses of
`FractionalMassTailRigidity.fractional_mass_tail_rigidity`, with the tail condition replaced by
`C(y) = Σ_{u_k < y} c_k = o(√y)`. -/
theorem fractional_mass_sqrt_growth_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ}
    {c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k) (hut : Tendsto u atTop atTop)
    (hgrowth : ∀ γ : ℝ, 0 < γ → ∃ K : ℝ, ∀ y : ℝ, 1 ≤ y → phaseSum c u y ≤ γ * Real.sqrt y + K)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨K₁, hK₁⟩ := hgrowth 1 one_pos
  have hcs2 : Summable fun k => c k / u k ^ 2 :=
    summable_div_sq_of_phaseSum_le hc hu1 hut (K := 1) (K' := K₁) fun y hy => by
      have h := hK₁ y hy
      have hs : Real.sqrt y ≤ y := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      linarith
  set G := gInf lam m t c u with hGdef
  set Φ := phiInf m t c u with hΦdef
  have hid' : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s := fun s hs => (hid s hs).symm
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_phiInf lam hone hsum hc hu1 hut hcs2
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs =>
    re_phiInf_nonneg hc hu1 hut hcs2 hs
  have hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s := fun s hs =>
    continuousAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s := fun s hs =>
    hasDerivAt_gInf hone hsum hc hu1 hut hcs2 hs
  have hG2 : G 2 = bigG lam 2 := gInf_two hone hsum hc hu1 hut hcs2
  set C : ℝ → ℝ := fun x => phaseSum c u (2 * x) with hCdef
  have hCm : Monotone C := fun a b h => phaseSum_mono hc hut (by linarith)
  have hCg : ∀ γ : ℝ, 0 < γ → ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → C x ≤ γ * Real.sqrt x + K := by
    intro γ hγ
    obtain ⟨K, hK⟩ := hgrowth (γ / Real.sqrt 2) (by positivity)
    refine ⟨K, fun x hx => ?_⟩
    have h := hK (2 * x) (by linarith)
    have e : γ / Real.sqrt 2 * Real.sqrt (2 * x) = γ * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num)]
      field_simp
    rw [e] at h
    exact h
  have hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      1 * cexp ((((2 * Real.pi) * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ0
    have hy : 0 < -(2 * τ) := by linarith
    have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
      rw [lineS_eq]; push_cast; ring
    have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
    have hC : C (-τ) = phaseSum c u (-(2 * τ)) := by
      simp only [hCdef]; congr 1; ring
    rw [hC]
    simp only [hGdef, gInf]
    rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracInfProd_conj hc hu1 hut hcs2 hre,
      hline, conj_fracInfProd_lower hc hu1 hut hcs2 hy]
    ring
  exact abelian_twist_rigidity hsl hΦd hΦre hid' hGc hGd hG2 hCm hCg hlock

end

end AbelianTwist

end RHTower
