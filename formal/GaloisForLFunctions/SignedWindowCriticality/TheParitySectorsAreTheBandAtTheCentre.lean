import GaloisForLFunctions.SignedWindowCriticality.OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The parity sectors of a window are the band at its centre

On the symmetric window `[−a, a]` the parity `x ↦ −x` is the reflection `R₀` through the centre
`0`. A half-window test `f`, supported in `[−a, 0]`, and its mirror image `f∘R₀` form a reflection
pair, `W(f ± f∘R₀) = 2W(f) ± 2𝒞₀(f)`, with the **centre coupling**
`𝒞₀(f) = 𝓗₀(f) − Σ_n Λ(n)n^{−1/2}(f⋆f)(−log n)`: the collar Hankel form at the centre minus the
smoothed prime count of the test with itself (`OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount`).

* **Each parity sector is the band at the centre** (`odd_nonneg_iff_centreCoupling_le`,
  `even_nonneg_iff_neg_centreCoupling_le`). Weil's form is nonnegative on the odd (even) `C²` tests
  of `[−a, a]` iff `𝒞₀(f) ≤ W(f)` (`−𝒞₀(f) ≤ W(f)`) for every `C²` half-window test `f`. A parity
  sector test vanishing near `0` splits as `f ± f∘R₀`; a general one is a limit of such tests by a
  cut-off at the centre whose height is bounded and whose width shrinks
  (`le_weilQuad_of_centreCutoff`), along which Weil's form is lower semicontinuous because the
  perturbation's `L¹`, `L²` and Lévy norms vanish (SSHA's perturbation bound).
* **The odd unit window in half-window form** (`centreCoupling_eq_of_half`,
  `odd_unit_nonneg_iff`). For `a = ½` only the prime `2` meets the centre: the odd unit window is
  nonnegative iff
  `W(f) ≥ 𝓗₀(f) − (log 2/√2)·(f⋆f)(−log 2)` for every `C²` test `f` supported in `[−½, 0]`.
* **It reads one arithmetic number** (`odd_unit_nonneg_iff_mem_unitBandWeights`,
  `convex_unitBandWeights`). The condition is linear in the prime-two weight: the odd unit window
  is nonnegative iff `w₂ = log 2/√2` lies in the set of admissible weights, and that set is an
  interval. Any divisor with the archimedean place and pole of `ζ` and the same weight at `2` has
  the same odd unit window.
* **Markov–Hankel form** (`odd_unit_nonneg_iff_markov_hankel`). Since `ω(t) = Σ_j e^{−(2j+½)t}`, the
  archimedean coupling of `f` with its mirror is the positive Hankel form `Σ_j m_j(f)²`,
  `m_j(f) = ∫f(u)e^{(2j+½)u}du`, and the odd unit window is nonnegative iff
  `4S(f)² ≤ M(f) + Σ_{j≥0} m_j(f)² + w₂(f⋆f)(−log 2)`: the pole debt of the pair is paid by the
  Markov part of the half, which alone dies at width `e^{−3/4} < ½`, the reflection squares and the
  prime value. On every symmetric window (`odd_nonneg_iff_markov_hankel`,
  `even_nonneg_iff_markov_hankel`) the odd sector is `4S² ≤ M + Σ_j m_j² + P` and the even sector
  `Σ_j m_j² + P ≤ M + 4C²`, `P(f) = Σ_n w_n(f⋆f)(−log n)`: in the odd sector the reflection squares
  and the primes pay the sinh debt, in the even sector they are paid by the cosh credit.

`W(f)` is Weil's form on a window of length `½`, where it is archimedean; `𝓗₀(f)` is one pole square
against the trivial-zero squares; `(f⋆f)(−log 2) = ∫f(u)f(−log 2 − u)du` is the single prime value.
This is the exact content of the one question (review-0311 §2.8) in the language of reflection
pairs: one half-window, one Hankel form, one prime value.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower _root_.RHTower
open SpacingScaleHarmonicAnalysis Zeta23

/-- The coupling of a half-window test with its mirror image through the centre `0`. -/
def centreCoupling (f : ℝ → ℝ) : ℝ :=
  collarHankel 0 f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * 0 - Real.log n)

/-! ### A cut-off at the centre -/

/-- A smooth even bump, `1` on `[−½, ½]` and `0` off `(−1, 1)`. -/
def centreBump (x : ℝ) : ℝ := Real.smoothTransition (4 / 3 * (1 - x ^ 2))

theorem contDiff_centreBump : ContDiff ℝ 2 centreBump :=
  (Real.smoothTransition.contDiff (n := 2)).comp (by fun_prop)

theorem centreBump_neg (x : ℝ) : centreBump (-x) = centreBump x := by
  simp only [centreBump, neg_sq]

theorem centreBump_nonneg (x : ℝ) : 0 ≤ centreBump x := Real.smoothTransition.nonneg _

theorem centreBump_le_one (x : ℝ) : centreBump x ≤ 1 := Real.smoothTransition.le_one _

theorem centreBump_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : centreBump x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : x ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at h; linarith
  linarith

theorem centreBump_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : centreBump x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 1 ≤ x ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num) hx 2
    rw [sq_abs] at h; linarith
  linarith

theorem lt_abs_of_notMem_Icc {a x : ℝ} (hx : x ∉ Icc (-a) a) : a < |x| := by
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
  · exact lt_of_lt_of_le hx (le_abs_self x)

theorem hasCompactSupport_centreBump : HasCompactSupport centreBump :=
  HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun _ hx =>
    centreBump_eq_zero (lt_abs_of_notMem_Icc hx).le

/-- The cut-off of width `1/(n + 1)`. -/
def centreCutoff (n : ℕ) (u : ℝ) : ℝ := centreBump (((n : ℝ) + 1) * u)

/-- The test `F` cut off at the centre. -/
def cutAtCentre (F : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ := F u + -(F u * centreCutoff n u)

theorem contDiff_centreCutoff (n : ℕ) : ContDiff ℝ 2 (centreCutoff n) :=
  contDiff_centreBump.comp (contDiff_const.mul contDiff_id)

theorem centreCutoff_eq_one {n : ℕ} {u : ℝ} (hu : |u| ≤ 1 / (2 * ((n : ℝ) + 1))) :
    centreCutoff n u = 1 := by
  apply centreBump_eq_one
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_pos hn]
  rw [le_div_iff₀ (by positivity)] at hu
  nlinarith

theorem centreCutoff_eq_zero {n : ℕ} {u : ℝ} (hu : 1 / ((n : ℝ) + 1) ≤ |u|) :
    centreCutoff n u = 0 := by
  apply centreBump_eq_zero
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_of_pos hn]
  rw [div_le_iff₀ hn] at hu
  linarith

/-! ### Lower semicontinuity along the cut-off -/

/-- `L²` bound of the cut-off perturbation. -/
def cutA (M : ℝ) (n : ℕ) : ℝ := 2 * M ^ 2 * (1 / ((n : ℝ) + 1))

/-- `L¹` bound of the cut-off perturbation. -/
def cutB (M : ℝ) (n : ℕ) : ℝ := 2 * M * (1 / ((n : ℝ) + 1))

/-- Lévy bound of the cut-off perturbation. -/
def cutV (M K L : ℝ) (n : ℕ) : ℝ :=
  Real.exp (1 / 2) * (K + M * L * ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) ^ 2 * cutB M n +
    (4 * Real.log ((n : ℝ) + 1) + levyLipConstant) * cutA M n

/-- The resulting bound on the motion of Weil's form. -/
def cutErr (θ nF lF P m₀ m₁ M K L : ℝ) (n : ℕ) : ℝ :=
  θ * (2 * (nF * Real.sqrt (cutA M n)) + cutA M n) +
    (2 * (lF * Real.sqrt (cutV M K L n)) + cutV M K L n) +
    P * (2 * (nF * Real.sqrt (cutA M n)) + cutA M n) + m₀ * cutB M n + m₁ * cutB M n ^ 2

theorem levyLipConstant_nonneg : 0 ≤ levyLipConstant := by
  unfold levyLipConstant
  have h : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact add_nonneg (Real.exp_pos _).le (div_nonneg (by positivity) (sub_pos.mpr h).le)

theorem tendsto_log_succ_mul_inv :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hs
  refine h.congr fun n => ?_
  simp only [Function.comp, pow_one, one_mul, add_zero]
  ring

theorem tendsto_cutA (M : ℝ) : Tendsto (cutA M) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * M ^ 2)
  rw [mul_zero] at h
  exact h

theorem tendsto_cutB (M : ℝ) : Tendsto (cutB M) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * M)
  rw [mul_zero] at h
  exact h

theorem tendsto_cutV (M K L : ℝ) : Tendsto (cutV M K L) atTop (𝓝 0) := by
  have hx := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have e : ∀ n : ℕ, cutV M K L n =
      Real.exp (1 / 2) * (2 * M) * (K * (1 / ((n : ℝ) + 1)) ^ 3 +
        M * L * (1 / ((n : ℝ) + 1)) ^ 2) +
      2 * M ^ 2 * (4 * (Real.log ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))) +
        levyLipConstant * (1 / ((n : ℝ) + 1))) := fun n => by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [cutV, cutA, cutB]
    field_simp
  have h1 := (((hx.pow 3).const_mul K).add ((hx.pow 2).const_mul (M * L))).const_mul
    (Real.exp (1 / 2) * (2 * M))
  have h2 := ((tendsto_log_succ_mul_inv.const_mul 4).add (hx.const_mul levyLipConstant)).const_mul
    (2 * M ^ 2)
  have h := h1.add h2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  exact h.congr fun n => (e n).symm

theorem tendsto_cutErr (θ nF lF P m₀ m₁ M K L : ℝ) :
    Tendsto (cutErr θ nF lF P m₀ m₁ M K L) atTop (𝓝 0) := by
  have hA := tendsto_cutA M
  have hB := tendsto_cutB M
  have hV := tendsto_cutV M K L
  have hsA : Tendsto (fun n => Real.sqrt (cutA M n)) atTop (𝓝 0) := by simpa using hA.sqrt
  have hsV : Tendsto (fun n => Real.sqrt (cutV M K L n)) atTop (𝓝 0) := by simpa using hV.sqrt
  have t1 := (((hsA.const_mul nF).const_mul 2).add hA).const_mul θ
  have t2 := ((hsV.const_mul lF).const_mul 2).add hV
  have t3 := (((hsA.const_mul nF).const_mul 2).add hA).const_mul P
  have t := (((t1.add t2).add t3).add (hB.const_mul m₀)).add ((hB.pow 2).const_mul m₁)
  simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at t
  exact t

theorem abs_centreCutoff_le (n : ℕ) (u : ℝ) : |centreCutoff n u| ≤ 1 := by
  unfold centreCutoff
  rw [abs_of_nonneg (centreBump_nonneg _)]
  exact centreBump_le_one _

/-- **Weil's form is lower semicontinuous along the cut-off at the centre.** If every cut test
`F(1 − χ_n)` has `W ≥ c`, then `W(F) ≥ c`. -/
theorem le_weilQuad_of_centreCutoff {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {a : ℝ}
    (hFa : SupportedIn a F) {c : ℝ} (hc : ∀ n : ℕ, c ≤ weilQuad (cutAtCentre F n)) :
    c ≤ weilQuad F := by
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx =>
      hFa x (lt_abs_of_notMem_Icc hx)
  obtain ⟨M, hM⟩ := hFc.exists_bound_of_continuous hF.continuous
  obtain ⟨KF, hKF⟩ := hF.lipschitzWith_of_hasCompactSupport hFc (by norm_num)
  obtain ⟨Lb, hLb⟩ := contDiff_centreBump.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_centreBump (by norm_num)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hFb : ∀ u, |F u| ≤ M := fun u => by simpa [Real.norm_eq_abs] using hM u
  have hFL : ∀ u v, |F u - F v| ≤ KF * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hKF.dist_le_mul u v
  have hbL : ∀ x y, |centreBump x - centreBump y| ≤ Lb * |x - y| := fun x y => by
    simpa [Real.dist_eq] using hLb.dist_le_mul x y
  have hbound : ∀ n : ℕ, c - cutErr (2 * |gammaHardyPhaseRate 0|)
      (Real.sqrt (∫ u, F u ^ 2)) (Real.sqrt (levyEnergy F)) (2 * primeMass a)
      (4 * Real.cosh (a / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|))
      (4 * Real.cosh (a / 2) ^ 2) M KF Lb n ≤ weilQuad F := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hx0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set D : ℝ → ℝ := fun u => -(F u * centreCutoff n u) with hD
    have hDc : ContDiff ℝ 2 D := (hF.mul (contDiff_centreCutoff n)).neg
    have hDcs : HasCompactSupport D := (hFc.mul_right).neg
    have hDa : SupportedIn a D := fun u hu => by simp [D, hFa u hu]
    have hDz : ∀ u, u ∉ Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)) → D u = 0 :=
      fun u hu => by simp [D, centreCutoff_eq_zero (lt_abs_of_notMem_Icc hu).le]
    have hDb : ∀ u, |D u| ≤ M := fun u => by
      simp only [D, abs_neg, abs_mul]
      nlinarith [hFb u, abs_nonneg (F u), abs_nonneg (centreCutoff n u), abs_centreCutoff_le n u]
    have hvol : volume.real (Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) =
        2 * (1 / ((n : ℝ) + 1)) := by
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    have hA : (∫ u, D u ^ 2) ≤ cutA M n := by
      have e : (∫ u, D u ^ 2) = ∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), D u ^ 2 :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hDz u hu]).symm
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) (f := fun u => D u ^ 2)
        measure_Icc_lt_top (C := M ^ 2) fun u _ => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hDb u) 2
      rw [hvol, Real.norm_eq_abs] at h
      have h2 := le_abs_self (∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), D u ^ 2)
      rw [e]; unfold cutA; nlinarith
    have hB : (∫ u, |D u|) ≤ cutB M n := by
      have e : (∫ u, |D u|) = ∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), |D u| :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hDz u hu]).symm
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) (f := fun u => |D u|)
        measure_Icc_lt_top (C := M) fun u _ => by
          rw [Real.norm_eq_abs, abs_abs]; exact hDb u
      rw [hvol, Real.norm_eq_abs] at h
      have h2 := le_abs_self (∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), |D u|)
      rw [e]; unfold cutB; nlinarith
    -- Lipschitz bound of `D`
    have hKD : 0 ≤ (KF : ℝ) + M * Lb * ((n : ℝ) + 1) :=
      add_nonneg KF.coe_nonneg (mul_nonneg (mul_nonneg hM0 Lb.coe_nonneg) hn.le)
    have hDL : ∀ u v, |D u - D v| ≤ ((KF : ℝ) + M * Lb * ((n : ℝ) + 1)) * |u - v| := by
      intro u v
      have hcL : |centreCutoff n u - centreCutoff n v| ≤ Lb * ((n : ℝ) + 1) * |u - v| := by
        have h := hbL (((n : ℝ) + 1) * u) (((n : ℝ) + 1) * v)
        rw [show ((n : ℝ) + 1) * u - ((n : ℝ) + 1) * v = ((n : ℝ) + 1) * (u - v) by ring,
          abs_mul, abs_of_pos hn] at h
        simp only [centreCutoff]; linarith
      have e : D u - D v = -((F u - F v) * centreCutoff n u + F v *
          (centreCutoff n u - centreCutoff n v)) := by simp only [D]; ring
      rw [e, abs_neg]
      calc |(F u - F v) * centreCutoff n u + F v * (centreCutoff n u - centreCutoff n v)|
          ≤ |F u - F v| * |centreCutoff n u| +
              |F v| * |centreCutoff n u - centreCutoff n v| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ KF * |u - v| * 1 + M * (Lb * ((n : ℝ) + 1) * |u - v|) :=
            add_le_add (mul_le_mul (hFL u v) (abs_centreCutoff_le n u) (abs_nonneg _)
              (mul_nonneg KF.coe_nonneg (abs_nonneg _)))
              (mul_le_mul (hFb v) hcL (abs_nonneg _) hM0)
        _ = ((KF : ℝ) + M * Lb * ((n : ℝ) + 1)) * |u - v| := by ring
    -- the Lévy energy of `D`
    have hx2 : 0 < (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
    have hx21 : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      nlinarith
    have hlev := levyEnergy_le_lipschitz hDc hDcs hDL hx2 hx21
    have hlog : Real.log (1 / (1 / ((n : ℝ) + 1)) ^ 2) = 2 * Real.log ((n : ℝ) + 1) := by
      rw [div_pow, one_pow, one_div_one_div, Real.log_pow]; push_cast; ring
    rw [hlog] at hlev
    have hI0 : 0 ≤ ∫ u, |D u| := integral_nonneg fun u => abs_nonneg _
    have hJ0 : 0 ≤ ∫ u, D u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hL0 : 0 ≤ levyEnergy D := levyEnergy_nonneg' D
    have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have hC0 : 0 ≤ 2 * (2 * Real.log ((n : ℝ) + 1)) + levyLipConstant := by
      linarith [levyLipConstant_nonneg]
    have hV : levyEnergy D ≤ cutV M KF Lb n := by
      have hcoef : 0 ≤ Real.exp (1 / 2) * ((KF : ℝ) + M * Lb * ((n : ℝ) + 1)) *
          (1 / ((n : ℝ) + 1)) ^ 2 := mul_nonneg (mul_nonneg (Real.exp_pos _).le hKD) hx2.le
      have := add_le_add (mul_le_mul_of_nonneg_left hB hcoef) (mul_le_mul_of_nonneg_left hA hC0)
      unfold cutV
      linarith
    -- the perturbation bound
    have hpert := weilQuad_add_le hF hFc hDc hDcs hFa hDa
    have hcut : (fun u => F u + D u) = cutAtCentre F n := by
      funext u; simp only [D, cutAtCentre]
    rw [hcut] at hpert
    have hP0 : 0 ≤ 2 * primeMass a := mul_nonneg (by norm_num) (primeMass_nonneg a)
    have hθ0 : 0 ≤ 2 * |gammaHardyPhaseRate 0| := by positivity
    have hnF : 0 ≤ Real.sqrt (∫ u, F u ^ 2) := Real.sqrt_nonneg _
    have hlF : 0 ≤ Real.sqrt (levyEnergy F) := Real.sqrt_nonneg _
    have hm₀ : 0 ≤ 4 * Real.cosh (a / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|) := by
      positivity
    have hm₁ : 0 ≤ 4 * Real.cosh (a / 2) ^ 2 := by positivity
    have s1 := Real.sqrt_le_sqrt hA
    have s2 := Real.sqrt_le_sqrt hV
    have s3 := pow_le_pow_left₀ hI0 hB 2
    have c1 := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s1 hnF) (by norm_num :
        (0 : ℝ) ≤ 2)) hA) hθ0
    have c2 := add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s2 hlF)
      (by norm_num : (0 : ℝ) ≤ 2)) hV
    have c3 := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s1 hnF) (by norm_num :
        (0 : ℝ) ≤ 2)) hA) hP0
    have c4 := mul_le_mul_of_nonneg_left hB hm₀
    have c5 := mul_le_mul_of_nonneg_left s3 hm₁
    have := hc n
    unfold cutErr
    linarith
  have hlim := (tendsto_cutErr (2 * |gammaHardyPhaseRate 0|)
      (Real.sqrt (∫ u, F u ^ 2)) (Real.sqrt (levyEnergy F)) (2 * primeMass a)
      (4 * Real.cosh (a / 2) * (|coshHalfMoment F| + |sinhHalfMoment F|))
      (4 * Real.cosh (a / 2) ^ 2) M KF Lb).const_sub c
  rw [sub_zero] at hlim
  exact le_of_tendsto' hlim hbound

/-! ### Parity sector tests split at the centre -/

/-- The left half of a test that vanishes near the centre. -/
def leftHalf (n : ℕ) (G : ℝ → ℝ) (u : ℝ) : ℝ :=
  G u * Real.smoothTransition (-(2 * ((n : ℝ) + 1)) * u)

theorem contDiff_leftHalf {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (n : ℕ) :
    ContDiff ℝ 2 (leftHalf n G) :=
  hG.mul ((Real.smoothTransition.contDiff (n := 2)).comp (by fun_prop))

theorem leftHalf_eq_zero_of_pos {G : ℝ → ℝ} (n : ℕ) {u : ℝ} (hu : 0 < u) : leftHalf n G u = 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [leftHalf]
  rw [Real.smoothTransition.zero_of_nonpos (x := -(2 * ((n : ℝ) + 1)) * u) (by nlinarith),
    mul_zero]

theorem cutAtCentre_eq_zero {F : ℝ → ℝ} {n : ℕ} {u : ℝ} (hu : |u| ≤ 1 / (2 * ((n : ℝ) + 1))) :
    cutAtCentre F n u = 0 := by
  simp [cutAtCentre, centreCutoff_eq_one hu]

theorem cutAtCentre_neg_of_odd {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) (n : ℕ) (u : ℝ) :
    cutAtCentre F n (-u) = -cutAtCentre F n u := by
  simp only [cutAtCentre, centreCutoff, hodd, mul_neg, centreBump_neg]; ring

theorem cutAtCentre_neg_of_even {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) (n : ℕ) (u : ℝ) :
    cutAtCentre F n (-u) = cutAtCentre F n u := by
  simp only [cutAtCentre, centreCutoff, heven, mul_neg, centreBump_neg]

/-- The step `σ(u) + σ(−u) = 1` away from the centre. -/
theorem step_add_step_neg (n : ℕ) {u : ℝ} (hu : 1 / (2 * ((n : ℝ) + 1)) < |u|) :
    Real.smoothTransition (-(2 * ((n : ℝ) + 1)) * u) +
      Real.smoothTransition (-(2 * ((n : ℝ) + 1)) * -u) = 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hu' : 1 < 2 * ((n : ℝ) + 1) * |u| := by
    rw [div_lt_iff₀ (by positivity)] at hu; linarith
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0] at hu'
    rw [Real.smoothTransition.zero_of_nonpos (x := -(2 * ((n : ℝ) + 1)) * u) (by nlinarith),
      Real.smoothTransition.one_of_one_le (x := -(2 * ((n : ℝ) + 1)) * -u) (by nlinarith)]
    norm_num
  · rw [abs_of_neg h0] at hu'
    rw [Real.smoothTransition.one_of_one_le (x := -(2 * ((n : ℝ) + 1)) * u) (by nlinarith),
      Real.smoothTransition.zero_of_nonpos (x := -(2 * ((n : ℝ) + 1)) * -u) (by nlinarith)]
    norm_num

theorem cutAtCentre_eq_sub_reflect {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) (n : ℕ) :
    cutAtCentre F n = fun u => leftHalf n (cutAtCentre F n) u +
      -collarReflect 0 (leftHalf n (cutAtCentre F n)) u := by
  funext u
  simp only [leftHalf, collarReflect, mul_zero, zero_sub]
  rw [cutAtCentre_neg_of_odd hodd]
  by_cases hu : |u| ≤ 1 / (2 * ((n : ℝ) + 1))
  · rw [cutAtCentre_eq_zero hu]; ring
  · have h := step_add_step_neg n (not_le.mp hu)
    linear_combination (-cutAtCentre F n u) * h

theorem cutAtCentre_eq_add_reflect {F : ℝ → ℝ} (heven : ∀ x, F (-x) = F x) (n : ℕ) :
    cutAtCentre F n = fun u => leftHalf n (cutAtCentre F n) u +
      collarReflect 0 (leftHalf n (cutAtCentre F n)) u := by
  funext u
  simp only [leftHalf, collarReflect, mul_zero, zero_sub]
  rw [cutAtCentre_neg_of_even heven]
  by_cases hu : |u| ≤ 1 / (2 * ((n : ℝ) + 1))
  · rw [cutAtCentre_eq_zero hu]; ring
  · have h := step_add_step_neg n (not_le.mp hu)
    linear_combination (-cutAtCentre F n u) * h

/-! ### The equivalences -/

theorem hasCompactSupport_of_half {f : ℝ → ℝ} {a : ℝ} (h0 : ∀ u, 0 < u → f u = 0)
    (ha : ∀ u, u < -a → f u = 0) : HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc fun u hu => by
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · exact ha u hu
    · exact h0 u hu

theorem supportedIn_reflect_pair {f : ℝ → ℝ} {a : ℝ} (ha0 : 0 < a) (h0 : ∀ u, 0 < u → f u = 0)
    (ha : ∀ u, u < -a → f u = 0) (ε : ℝ) :
    SupportedIn a (fun u => f u + ε * collarReflect 0 f u) := fun u hu => by
  simp only [collarReflect, mul_zero, zero_sub]
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    rw [h0 u (by linarith), ha (-u) (by linarith)]; ring
  · rw [abs_of_neg h] at hu
    rw [ha u (by linarith), h0 (-u) (by linarith)]; ring

theorem leftHalf_cut_props {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {a : ℝ} (hFa : SupportedIn a F)
    (n : ℕ) :
    ContDiff ℝ 2 (leftHalf n (cutAtCentre F n)) ∧
      (∀ u, 0 < u → leftHalf n (cutAtCentre F n) u = 0) ∧
      (∀ u, u < -a → leftHalf n (cutAtCentre F n) u = 0) := by
  refine ⟨contDiff_leftHalf ((hF.add (hF.mul (contDiff_centreCutoff n)).neg)) n,
    fun u hu => leftHalf_eq_zero_of_pos n hu, fun u hu => ?_⟩
  have hu' : a < |u| := lt_of_lt_of_le (by linarith) (neg_le_abs u)
  simp [leftHalf, cutAtCentre, hFa u hu']

/-- **The odd sector is the band at the centre.** -/
theorem odd_nonneg_iff_centreCoupling_le {a : ℝ} (ha : 0 < a) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn a F → 0 ≤ weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -a → f u = 0) →
        centreCoupling f ≤ weilQuad f := by
  constructor
  · intro hW f hf h0 hfa
    have hfc := hasCompactSupport_of_half h0 hfa
    have hodd : ∀ x, (fun u => f u + -collarReflect 0 f u) (-x) =
        -(fun u => f u + -collarReflect 0 f u) x := fun x => by
      simp only [collarReflect, mul_zero, zero_sub, neg_neg]; ring
    have hsupp : SupportedIn a (fun u => f u + -collarReflect 0 f u) := by
      have := supportedIn_reflect_pair ha h0 hfa (-1)
      intro u hu; have h := this u hu; simp only [neg_one_mul] at h; exact h
    have h := hW (fun u => f u + -collarReflect 0 f u)
      (hf.add (contDiff_collarReflect (m := 0) hf).neg) hodd hsupp
    rw [weilQuad_sub_collarReflect hf hfc h0] at h
    unfold centreCoupling
    linarith
  · intro hband F hF hodd hFa
    refine le_weilQuad_of_centreCutoff hF hFa fun n => ?_
    obtain ⟨hl, hl0, hla⟩ := leftHalf_cut_props hF hFa n
    rw [cutAtCentre_eq_sub_reflect hodd n,
      weilQuad_sub_collarReflect hl (hasCompactSupport_of_half hl0 hla) hl0]
    have := hband _ hl hl0 hla
    unfold centreCoupling at this
    linarith

/-- **The even sector is the band at the centre.** -/
theorem even_nonneg_iff_neg_centreCoupling_le {a : ℝ} (ha : 0 < a) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn a F → 0 ≤ weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -a → f u = 0) →
        -centreCoupling f ≤ weilQuad f := by
  constructor
  · intro hW f hf h0 hfa
    have hfc := hasCompactSupport_of_half h0 hfa
    have heven : ∀ x, (fun u => f u + collarReflect 0 f u) (-x) =
        (fun u => f u + collarReflect 0 f u) x := fun x => by
      simp only [collarReflect, mul_zero, zero_sub, neg_neg]; ring
    have hsupp : SupportedIn a (fun u => f u + collarReflect 0 f u) := by
      have := supportedIn_reflect_pair ha h0 hfa 1
      intro u hu; have h := this u hu; simp only [one_mul] at h; exact h
    have h := hW (fun u => f u + collarReflect 0 f u)
      (hf.add (contDiff_collarReflect (m := 0) hf)) heven hsupp
    rw [weilQuad_add_collarReflect hf hfc h0] at h
    unfold centreCoupling
    linarith
  · intro hband F hF heven hFa
    refine le_weilQuad_of_centreCutoff hF hFa fun n => ?_
    obtain ⟨hl, hl0, hla⟩ := leftHalf_cut_props hF hFa n
    rw [cutAtCentre_eq_add_reflect heven n,
      weilQuad_add_collarReflect hl (hasCompactSupport_of_half hl0 hla) hl0]
    have := hband _ hl hl0 hla
    unfold centreCoupling at this
    linarith

/-! ### The odd unit window -/

/-- On the unit window only the prime `2` meets the centre. -/
theorem centreCoupling_eq_of_half {f : ℝ → ℝ} (hfa : ∀ u, u < -(1 / 2) → f u = 0) :
    centreCoupling f = collarHankel 0 f - vonMangoldtAtom 2 * selfConv f (-Real.log 2) := by
  unfold centreCoupling
  congr 1
  rw [tsum_eq_single 2]
  · simp
  · intro n hn
    rcases lt_or_ge n 2 with h | h
    · simp [vonMangoldtAtom, not_le.mpr h]
    · have h3 : 3 ≤ n := by omega
      have hlog : 1 < Real.log n := by
        have h1 : 1 < Real.log 3 :=
          (Real.lt_log_iff_exp_lt (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
        have h2 : Real.log 3 ≤ Real.log n :=
          Real.log_le_log (by norm_num) (by exact_mod_cast h3)
        linarith
      have hz : selfConv f (2 * 0 - Real.log n) = 0 := by
        unfold selfConv
        refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
        simp only [Pi.zero_apply]
        rcases lt_or_ge u (-(1 / 2)) with hu | hu
        · rw [hfa u hu, zero_mul]
        · rw [hfa (2 * 0 - Real.log n - u) (by linarith), mul_zero]
      rw [hz, mul_zero]

/-- **The odd unit window in half-window form.** Weil's form is nonnegative on odd `C²` tests of
`[−½, ½]` iff `W(f) ≥ 𝓗₀(f) − (log 2/√2)(f⋆f)(−log 2)` for every `C²` test `f` supported in
`[−½, 0]`. -/
theorem odd_unit_nonneg_iff :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn (1 / 2) F →
        0 ≤ weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -(1 / 2) → f u = 0) →
        collarHankel 0 f - vonMangoldtAtom 2 * selfConv f (-Real.log 2) ≤ weilQuad f := by
  rw [odd_nonneg_iff_centreCoupling_le (by norm_num : (0 : ℝ) < 1 / 2)]
  constructor
  · intro h f hf h0 hfa
    rw [← centreCoupling_eq_of_half hfa]; exact h f hf h0 hfa
  · intro h f hf h0 hfa
    rw [centreCoupling_eq_of_half hfa]; exact h f hf h0 hfa

/-- The prime-two weights `w` for which the half-window band of the unit window holds:
`𝓗₀(f) − w(f⋆f)(−log 2) ≤ W(f)` for every `C²` test `f` supported in `[−½, 0]`. -/
def unitBandWeights : Set ℝ :=
  {w | ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -(1 / 2) → f u = 0) →
    collarHankel 0 f - w * selfConv f (-Real.log 2) ≤ weilQuad f}

/-- **The odd unit window reads one arithmetic number.** It is nonnegative iff the prime-two weight
`w₂ = log 2/√2` lies in `unitBandWeights`. -/
theorem odd_unit_nonneg_iff_mem_unitBandWeights :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn (1 / 2) F →
        0 ≤ weilQuad F) ↔ vonMangoldtAtom 2 ∈ unitBandWeights :=
  odd_unit_nonneg_iff

/-- **The admissible prime-two weights form an interval.** -/
theorem convex_unitBandWeights : Convex ℝ unitBandWeights := by
  intro w₁ h₁ w₂ h₂ s t hs ht hst f hf h0 hfa
  have e₁ := h₁ f hf h0 hfa
  have e₂ := h₂ f hf h0 hfa
  have : collarHankel 0 f - (s • w₁ + t • w₂) * selfConv f (-Real.log 2) =
      s * (collarHankel 0 f - w₁ * selfConv f (-Real.log 2)) +
        t * (collarHankel 0 f - w₂ * selfConv f (-Real.log 2)) := by
    simp only [smul_eq_mul]
    have : collarHankel 0 f = (s + t) * collarHankel 0 f := by rw [hst, one_mul]
    linear_combination this
  rw [this]
  have hW : s * weilQuad f + t * weilQuad f = weilQuad f := by rw [← add_mul, hst, one_mul]
  linarith [mul_le_mul_of_nonneg_left e₁ hs, mul_le_mul_of_nonneg_left e₂ ht]

/-! ### The odd unit window as a Markov–Hankel inequality -/

theorem leftMoment_half_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    leftMoment f (1 / 2) = coshHalfMoment f - sinhHalfMoment f := by
  unfold leftMoment coshHalfMoment sinhHalfMoment
  have h1 : Integrable (fun x => f x * Real.cosh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have h2 : Integrable (fun x => f x * Real.sinh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [← mul_sub, Real.cosh_sub_sinh, show -(1 / 2 * u) = -(u / 2) by ring]

theorem leftMoment_neg_half_eq {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    leftMoment f (-(1 / 2)) = coshHalfMoment f + sinhHalfMoment f := by
  unfold leftMoment coshHalfMoment sinhHalfMoment
  have h1 : Integrable (fun x => f x * Real.cosh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have h2 : Integrable (fun x => f x * Real.sinh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [← mul_add, Real.cosh_add_sinh, show -(-(1 / 2) * u) = u / 2 by ring]

/-- **The odd unit window as a Markov–Hankel inequality.** With `C, S` the cosh and sinh moments
of a half-window test `f` on `[−½, 0]`, `M(f) = W(f) − 2C² + 2S²` its Markov part and
`m_j(f) = ∫f(u)e^{(2j+½)u}du` (`m_0 = C + S`, `m_{k+1} = μ_{σ_k}(f)`), the odd unit window is
nonnegative iff `4S² ≤ M(f) + Σ_{j≥0} m_j(f)² + w₂(f⋆f)(−log 2)` for every such `f`: the pole debt
of `f − f∘R₀` is paid by the Markov energy of the half, the archimedean reflection squares and the
prime value. -/
theorem odd_unit_nonneg_iff_markov_hankel :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn (1 / 2) F →
        0 ≤ weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -(1 / 2) → f u = 0) →
        4 * sinhHalfMoment f ^ 2 ≤
          (weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2) +
            leftMoment f (-(1 / 2)) ^ 2 + (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
            vonMangoldtAtom 2 * selfConv f (-Real.log 2) := by
  rw [odd_unit_nonneg_iff]
  have key : ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) →
      (∀ u, u < -(1 / 2) → f u = 0) →
      ((weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2) +
          leftMoment f (-(1 / 2)) ^ 2 + (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
          vonMangoldtAtom 2 * selfConv f (-Real.log 2)) - 4 * sinhHalfMoment f ^ 2 =
        weilQuad f - (collarHankel 0 f - vonMangoldtAtom 2 * selfConv f (-Real.log 2)) := by
    intro f hf h0 hfa
    have hfc := hasCompactSupport_of_half h0 hfa
    have hH : collarHankel 0 f =
        leftMoment f (1 / 2) ^ 2 - ∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2 := by
      simp [collarHankel]
    rw [hH, leftMoment_half_eq hf.continuous hfc, leftMoment_neg_half_eq hf.continuous hfc]
    ring
  constructor
  · intro h f hf h0 hfa
    have := h f hf h0 hfa
    have e := key f hf h0 hfa
    linarith
  · intro h f hf h0 hfa
    have := h f hf h0 hfa
    have e := key f hf h0 hfa
    linarith

/-- The centre coupling in moment form. -/
theorem centreCoupling_eq_moments {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    centreCoupling f = (coshHalfMoment f - sinhHalfMoment f) ^ 2 -
      (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) -
      ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * 0 - Real.log n) := by
  unfold centreCoupling
  rw [← leftMoment_half_eq hf hfc]
  simp [collarHankel]

/-- **Every symmetric window in Markov–Hankel form.** With `M(f) = W(f) − 2C² + 2S²`,
`m_j(f) = ∫f(u)e^{(2j+½)u}du` and the prime values `P(f) = Σ_n w_n(f⋆f)(−log n)`, the odd sector of
`[−a, a]` is nonnegative iff `4S(f)² ≤ M(f) + Σ_j m_j(f)² + P(f)`, and the even sector iff
`Σ_j m_j(f)² + P(f) ≤ M(f) + 4C(f)²`, for every `C²` half-window test `f` on `[−a, 0]`. -/
theorem odd_nonneg_iff_markov_hankel {a : ℝ} (ha : 0 < a) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn a F → 0 ≤ weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -a → f u = 0) →
        4 * sinhHalfMoment f ^ 2 ≤
          (weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2) +
            leftMoment f (-(1 / 2)) ^ 2 + (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
            ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * 0 - Real.log n) := by
  rw [odd_nonneg_iff_centreCoupling_le ha]
  refine forall_congr' fun f => imp_congr_right fun hf => imp_congr_right fun h0 =>
    imp_congr_right fun hfa => ?_
  have hfc := hasCompactSupport_of_half h0 hfa
  rw [centreCoupling_eq_moments hf.continuous hfc, leftMoment_neg_half_eq hf.continuous hfc]
  constructor <;> intro h <;> nlinarith [h]

theorem even_nonneg_iff_markov_hankel {a : ℝ} (ha : 0 < a) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn a F → 0 ≤ weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -a → f u = 0) →
        leftMoment f (-(1 / 2)) ^ 2 + (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
            (∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * 0 - Real.log n)) ≤
          (weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2) +
            4 * coshHalfMoment f ^ 2 := by
  rw [even_nonneg_iff_neg_centreCoupling_le ha]
  refine forall_congr' fun f => imp_congr_right fun hf => imp_congr_right fun h0 =>
    imp_congr_right fun hfa => ?_
  have hfc := hasCompactSupport_of_half h0 hfa
  rw [centreCoupling_eq_moments hf.continuous hfc, leftMoment_neg_half_eq hf.continuous hfc]
  constructor <;> intro h <;> nlinarith [h]

end GaloisForLFunctions.SignedWindowCriticality

end
