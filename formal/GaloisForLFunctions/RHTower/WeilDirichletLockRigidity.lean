import GaloisForLFunctions.RHTower.WeilDirichletLockSpectrum
import GaloisForLFunctions.RHTower.WeilLinearTwistPositivity

/-!
# Dirichlet locks force the true producer

**Theorem** (`dirichlet_lock_rigidity`).  Let `G` be a Herglotz producer for the weights `lam`.
Suppose that on the lower critical line

`G(1 − s) = V(s) G(s)`,  `V(s) = Σ_k P(k) k^{−(s−½)}`,  `Σ_k |P(k)| < ∞`.

Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.

On the line `s = ½ − 2ix` the factor is `V = Σ_k P(k) e^{2ix log k}`.  It is almost periodic with
frequencies `λ_k = 2 log k`, i.e. `e^{−λ_k/2} = 1/k ∈ ℚ`.  These are exactly the frequencies that
`ap_lock_rigidity` excludes.  The proof needs no growth condition on `P` beyond absolute
summability.

**Proof.**
1. The divisor system gives `F(w) V(w) = G(1) ζ(w)` on `Re w > 1` (`dirLock_factorization`),
   i.e. `G V = 2G(1) ξ`.  Analytic continuation extends this to `Re w > ½`, and continuity extends
   it to the critical line.
2. `G(s̄) = conj G(s)` (`G_conj`).
3. On the lower line the lock gives `G(1 − s) = V(s) G(s) = 2G(1) ξ(s)`.  Conjugation and
   `ξ(s) ∈ ℝ` give `G(s) = 2 conj(G(1)) ξ(s)`.  Hence `G(½ − iy) = κ G(½ + iy)` with the
   constant `κ = conj G(1)/G(1)`, and `phase_lock_rigidity` applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- A function continuous at `s` that vanishes on `s + (0, ∞)` vanishes at `s`. -/
theorem eq_zero_of_vanish_right {h : ℂ → ℂ} {s : ℂ} (hc : ContinuousAt h s)
    (hz : ∀ δ : ℝ, 0 < δ → h (s + δ) = 0) : h s = 0 := by
  have ht : Tendsto (fun δ : ℝ => s + (δ : ℂ)) (𝓝[>] 0) (𝓝 s) := by
    have : Tendsto (fun δ : ℝ => s + (δ : ℂ)) (𝓝 0) (𝓝 (s + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  have h2 : Tendsto (fun δ : ℝ => h (s + δ)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hz δ hδ).symm
  exact tendsto_nhds_unique (hc.tendsto.comp ht) h2

/-! ### `G V = 2 G(1) ξ` up to the critical line -/

theorem G_mul_dirLock_eq_xi {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hsys : ∀ m : ℕ, 1 ≤ m → ((Real.sqrt m : ℝ) : ℂ) *
      LSeries.convolution (halfCoeff (dirichletExp (lamLog lam))) P m = G 1)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    G s * dirLock P s = 2 * G 1 * xi s := by
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (fun z => G z * dirLock P z) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((hGd z hz).differentiableAt.mul (differentiableAt_dirLock hP hz)).differentiableWithinAt)
      hUo
  have hg : AnalyticOnNhd ℂ (fun z => 2 * G 1 * xi z) U :=
    DifferentiableOn.analyticOnNhd (fun z _ =>
      ((xi_differentiable z).const_mul (2 * G 1)).differentiableWithinAt) hUo
  have h2 : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have heq : (fun z => G z * dirLock P z) =ᶠ[𝓝 2] (fun z => 2 * G 1 * xi z) := by
    have ho : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [ho] with z hz
    exact G_mul_dirLock_eq_xi_of_one_lt hsl hid hGd hG2 hP hsys hz
  have hEq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2 heq
  rcases lt_or_eq_of_le hs with hlt | heq'
  · exact hEq hlt
  · have hc : ContinuousAt (fun z => G z * dirLock P z - 2 * G 1 * xi z) s :=
      ((hGc s hs).mul (continuous_dirLock hP).continuousAt).sub
        (continuous_const.mul xi_differentiable.continuous).continuousAt
    have h0 := eq_zero_of_vanish_right hc fun δ hδ => by
      have : (s + δ) ∈ U := by
        show 1 / 2 < (s + (δ : ℂ)).re
        rw [Complex.add_re, Complex.ofReal_re]; linarith
      exact sub_eq_zero.mpr (hEq this)
    exact sub_eq_zero.mp h0

/-- `ξ` is real on the critical line. -/
theorem conj_xi_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) : conj (xi s) = xi s := by
  have h : conj s = 1 - s := by
    apply Complex.ext
    · simp [Complex.conj_re, hs]; norm_num
    · simp [Complex.conj_im]
  rw [← xi_conj, h, xi_one_sub]

/-! ### The rigidity theorem -/

/-- **Dirichlet locks force the true producer.**  If a Herglotz producer satisfies
`G(1 − s) = (Σ_k P(k) k^{−(s−½)}) G(s)` on the lower critical line with `Σ |P(k)| < ∞`, then
`lam = Λ` and the Riemann hypothesis holds. -/
theorem dirichlet_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = LSeries P (lineS τ - 1 / 2) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hlock' : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = dirLock P (lineS τ) * G (lineS τ) :=
    fun τ hτ => by rw [dirLock_of_le P (le_of_eq (lineS_re τ).symm)]; exact hlock τ hτ
  have hG1 : G 1 ≠ 0 := G_ne_zero hΦd hGd hG2 (ρ := 1) (by norm_num)
  have hκ : conj (G 1) / G 1 ≠ 0 :=
    div_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hG1) hG1
  refine phase_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 (Y := 0) le_rfl hκ ?_
  intro y hy
  set s : ℂ := 1 / 2 - (y : ℂ) * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hline : lineS (-y / 2) = s := by rw [lineS_eq, hs]; push_cast; ring
  have hup : 1 - s = 1 / 2 + (y : ℂ) * I := by rw [hs]; ring
  have hL := hlock' (-y / 2) (by linarith)
  rw [hline, hup] at hL
  have hsys := fun m hm => dirLock_divisor_system hsl hΦd hΦre hid hGc hGd hG2 hP hlock' (m := m) hm
  have hF := G_mul_dirLock_eq_xi hsl hid hGc hGd hG2 hP hsys (le_of_eq hsre.symm)
  have hupper : G (1 / 2 + (y : ℂ) * I) = 2 * G 1 * xi s := by
    rw [hL, mul_comm, hF]
  have hconj : conj (1 / 2 + (y : ℂ) * I) = s := by
    rw [hs, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
      Complex.conj_ofNat]
    ring
  have hlower : G s = 2 * conj (G 1) * xi s := by
    have hc := G_conj hsl hid hGc hGd hG2 (s := 1 / 2 + (y : ℂ) * I) (by simp)
    rw [hconj, hupper, map_mul, map_mul, conj_xi_of_re_eq_half hsre, Complex.conj_ofNat] at hc
    exact hc
  rw [hlower, hupper]
  field_simp

end

end AbelianTwist

end RHTower
