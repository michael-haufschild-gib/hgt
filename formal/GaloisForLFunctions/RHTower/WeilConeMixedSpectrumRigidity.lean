import GaloisForLFunctions.RHTower.WeilConeNearIntegerAtomicRigidity

/-!
# Mixed spectra of Weil-positive systems

Let `lam` be full-cone Weil-positive.  Suppose its boundary measure splits as

`μ_lam = Σ_j m_j(δ_{t_j} + δ_{−t_j}) + Σ_k c_k(δ_{u_k} + δ_{−u_k}) + ν`

(in the sense of Poisson integrals): integer masses `m_j` at `t_j ≥ 1`, real masses `c_k ≥ 0` at
`u_k ≥ 1`, `u_k → ∞`, and a positive measure `ν`.  Suppose the diffuse part of the Weil
continuation, `Φ_d = Φ_lam − (atomic series)`, extends continuously to the critical line.

**Theorem** (`vonMangoldt_and_riemannHypothesis_of_mixed_spectrum`).  If the non-integer spectral
mass below height `y`,

`Σ_{u_k < y} c_k + (1/π) ∫_{−y}^{0} Re Φ_d(½ + iv) dv`,

is `O(y^α)` for some `α < 1`, then `lam(n) = Λ(n)` for every `n ≥ 2`, and RH holds.

This is the Weil-cone form of mixed-spectrum rigidity (`AbelianTwist.mixed_spectrum_power_rigidity`).
The only regularity premise is the continuity of `Φ_d` up to the line.  Positivity of `Re Φ_d`
and absolute convergence of the Dirichlet series are consequences of Weil positivity.

**Proof.**
* `Re Φ_lam(½ + w) = Re w · ∫ P_w dμ_lam` (Poisson representation), and the atomic series has
  real part `Re w · Σ (masses) P_w(atoms)` (`re_massSeries_eq`).  So `Re Φ_d = Re w · ∫ P_w dν ≥ 0`.
* `Φ_d` is holomorphic on `Re s > ½` as a difference of holomorphic functions, and on `Re s > 1`
  the Weil continuation is the Weil function.
* Mixed-spectrum rigidity applies.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz IntegerMassRigidity AbelianTwist FractionalMassRigidity FractionalMassTailRigidity

/-- **Real part of a positive mass series.**  For masses `c_j ≥ 0` at ordinates `t_j ≥ 1` with
`Σ c_j/t_j² < ∞` and `Re w > 0`, `Re Σ_j c_j 2w/(w² + t_j²) = Re w · Σ_j c_j (P_w(t_j) + P_w(−t_j))`. -/
theorem re_massSeries_eq {c t : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => c j / t j ^ 2) {w : ℂ} (hw0 : 0 < w.re) :
    (∑' j, (c j : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2))).re =
      w.re * (∑' j, ENNReal.ofReal (c j) * (poissonDensity w (t j) +
        poissonDensity w (-(t j)))).toReal := by
  have hfin : ∀ j, ENNReal.ofReal (c j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))
      ≠ ⊤ := fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨poissonDensity_ne_top _ _, poissonDensity_ne_top _ _⟩)
  have hterm : ∀ j, (ENNReal.ofReal (c j) * (poissonDensity w (t j) +
      poissonDensity w (-(t j)))).toReal =
      c j * (‖1 / (w - I * (t j : ℂ))‖ ^ 2 + ‖1 / (w - I * ((-(t j) : ℝ) : ℂ))‖ ^ 2) := by
    intro j
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc j),
      ENNReal.toReal_add (poissonDensity_ne_top _ _) (poissonDensity_ne_top _ _)]
    congr 1
  have hsumC : Summable fun j => ((c j : ℝ) : ℂ) * (2 * w / (w ^ 2 + (t j : ℂ) ^ 2)) := by
    refine Summable.of_norm_bounded
      ((hsum.mul_left (2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2)))) fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
    have := norm_two_mul_div_le hw0 (hone j)
    calc c j * ‖2 * w / (w ^ 2 + (t j : ℂ) ^ 2)‖
        ≤ c j * (2 * ‖w‖ * ((4 + 4 * w.im ^ 2 / w.re ^ 2) / t j ^ 2)) :=
          mul_le_mul_of_nonneg_left this (hc j)
      _ = 2 * ‖w‖ * (4 + 4 * w.im ^ 2 / w.re ^ 2) * (c j / t j ^ 2) := by ring
  rw [ENNReal.tsum_toReal_eq hfin, Complex.re_tsum hsumC]
  simp_rw [hterm]
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [Complex.re_ofReal_mul, re_two_mul_div hw0]
  ring

/-- The Herglotz data of a mixed spectrum: the diffuse part is holomorphic with nonnegative real
part, and the Weil identity holds on `Re s > 1`. -/
theorem mixed_spectrum_data {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ → ℕ} {t c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hcs2 : Summable fun k => c k / u k ^ 2) {ν : Measure ℝ}
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      (∑' j, ENNReal.ofReal (m j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))) +
      (∑' k, ENNReal.ofReal (c k) * (poissonDensity w (u k) + poissonDensity w (-(u k)))) +
      ∫⁻ r, poissonDensity w r ∂ν)
    {Φd : ℂ → ℂ}
    (hΦdeq : ∀ s : ℂ, 1 / 2 < s.re → weilContinuation hW s =
      atomicPairSeries (fun j => Real.pi * m j) t s +
        (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s) :
    DifferentiableOn ℂ Φd {s : ℂ | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φd s).re) ∧
      ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
        LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
          atomicPairSeries (fun j => Real.pi * m j) t s +
            (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s := by
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hm0 : ∀ j, (0 : ℝ) ≤ m j := fun j => Nat.cast_nonneg _
  -- the atomic series as functions
  set A : ℂ → ℂ := atomicPairSeries (fun j => Real.pi * m j) t with hA
  set B : ℂ → ℂ := fun s => ∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))
    with hB
  have hAd : DifferentiableOn ℂ A U := differentiableOn_atomicPairSeries hone
    ((hsum.mul_left Real.pi).congr fun j => by
      rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le (hm0 j))]; ring)
  have hBeq : ∀ s, B s = atomicPairSeries (fun k => Real.pi * c k) u s := fun s =>
    (atomicPairSeries_pi_mul_eq c u s).symm
  have hBd : DifferentiableOn ℂ B U := by
    have h := differentiableOn_atomicPairSeries hu1 (c := fun k => Real.pi * c k)
      ((hcs2.mul_left Real.pi).congr fun k => by
        rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le (hc k))]; ring)
    exact h.congr fun s _ => hBeq s
  -- holomorphy of the diffuse part
  have hΦdd : DifferentiableOn ℂ Φd U := by
    have h := ((differentiableOn_weilContinuation hW).sub hAd).sub hBd
    refine h.congr fun s hs => ?_
    have := hΦdeq s hs
    simp only [Pi.sub_apply]
    rw [this]; ring
  -- positivity of the diffuse part
  have hΦdre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φd s).re := by
    intro s hs
    set w : ℂ := s - 1 / 2 with hwdef
    have hw0 : 0 < w.re := by rw [hwdef]; simp; linarith
    have hre := re_weilContinuation_eq hW hs
    rw [← hwdef, hrep w hw0] at hre
    have hfin := lintegral_poissonDensity_lt_top hW hw0
    rw [hrep w hw0] at hfin
    have hS1 : (∑' j, ENNReal.ofReal (m j) * (poissonDensity w (t j) + poissonDensity w (-(t j))))
        ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (le_trans le_self_add le_self_add)
    have hS2 : (∑' k, ENNReal.ofReal (c k) * (poissonDensity w (u k) + poissonDensity w (-(u k))))
        ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (le_trans le_add_self le_self_add)
    have hS3 : (∫⁻ r, poissonDensity w r ∂ν) ≠ ⊤ := ne_top_of_le_ne_top hfin.ne le_add_self
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hS1, hS2⟩) hS3,
      ENNReal.toReal_add hS1 hS2] at hre
    have hAre : (A s).re = w.re * (∑' j, ENNReal.ofReal (m j) *
        (poissonDensity w (t j) + poissonDensity w (-(t j)))).toReal := by
      rw [hA, atomicPairSeries_pi_mul_eq, ← hwdef]
      exact re_massSeries_eq hm0 hone hsum hw0
    have hBre : (B s).re = w.re * (∑' k, ENNReal.ofReal (c k) *
        (poissonDensity w (u k) + poissonDensity w (-(u k)))).toReal := by
      simp only [hB]
      rw [← hwdef]
      exact re_massSeries_eq hc hu1 hcs2 hw0
    have hdecomp := congrArg Complex.re (hΦdeq s hs)
    simp only [Complex.add_re] at hdecomp
    have : (Φd s).re = w.re * (∫⁻ r, poissonDensity w r ∂ν).toReal := by
      have hA' : (atomicPairSeries (fun j => Real.pi * m j) t s).re = (A s).re := rfl
      have hB' : (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))).re =
          (B s).re := rfl
      rw [hA', hB', hAre, hBre] at hdecomp
      have hwre : w.re = s.re - 1 / 2 := by simp [hwdef]
      rw [← hwre, mul_add, mul_add] at hre
      linarith
    rw [this]
    exact mul_nonneg hw0.le ENNReal.toReal_nonneg
  -- the identity on `Re s > 1`
  have hfun : (fun n => if 2 ≤ n then (lam n : ℂ) else 0) = lamC lam := by
    funext n
    rw [lamC]
    split_ifs <;> simp
  have hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s := by
    intro s hs
    have h1 := weilContinuation_eq hW hs
    have h2 := hΦdeq s (by linarith)
    rw [← h2, h1, weilFunction, zetaArchimedeanDatum, hfun]
  exact ⟨hΦdd, hΦdre, hid⟩

/-- **Mixed spectra of Weil-positive systems.**  Integer atoms, real atoms and a positive rest
`ν`, with the diffuse part `Φ_d` of the Weil continuation continuous up to the critical line: if
the non-integer spectral mass below `y` is `O(y^α)`, `α < 1`, then `lam = Λ` and RH holds. -/
theorem vonMangoldt_and_riemannHypothesis_of_mixed_spectrum {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ → ℕ} {t c u : ℕ → ℝ} (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hut : Tendsto u atTop atTop) (hcs2 : Summable fun k => c k / u k ^ 2) {ν : Measure ℝ}
    (hrep : ∀ w : ℂ, 0 < w.re → ∫⁻ r, poissonDensity w r ∂boundaryMeasure hW =
      (∑' j, ENNReal.ofReal (m j) * (poissonDensity w (t j) + poissonDensity w (-(t j)))) +
      (∑' k, ENNReal.ofReal (c k) * (poissonDensity w (u k) + poissonDensity w (-(u k)))) +
      ∫⁻ r, poissonDensity w r ∂ν)
    {Φd : ℂ → ℂ} (hΦdc : ContinuousOn Φd {s : ℂ | 1 / 2 ≤ s.re})
    (hΦdeq : ∀ s : ℂ, 1 / 2 < s.re → weilContinuation hW s =
      atomicPairSeries (fun j => Real.pi * m j) t s +
        (∑' k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) + Φd s)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ y : ℝ, 1 ≤ y →
      phaseSum c u y + (∫ v in -y..0, (Φd ((1 / 2 : ℂ) + (v : ℂ) * I)).re) / Real.pi ≤
        K * y ^ α) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨hΦdd, hΦdre, hid⟩ := mixed_spectrum_data hW hone hsum hc hu1 hcs2 hrep hΦdeq
  exact mixed_spectrum_power_rigidity hone hsum hc hu1 hut hΦdd hΦdc hΦdre hgrowth
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hid

end RHTower.WeilSpectral
