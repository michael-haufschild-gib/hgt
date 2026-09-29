import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.HTGeometry.HamburgerFunctionalEquation
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The Riemann-kernel transform of a weight system is injective

For real weights `w` on `n ≥ 1` with `Σ |w(n)| n^{−σ} < ∞` for every `σ > 1`, put
`G_w(y) = Σ_n w(n) n^{−1/2} (Φ(y − log n) + Φ(y + log n))`, with `Φ` Riemann's kernel.

**Theorem** (`eq_zero_of_riemannKernelTransform_eq_zero`). If `G_w ≡ 0`, then `w = 0`.

The kernel is `Φ = Ψ'' − Ψ/4` with `Ψ(u) = Σ_m e^{u/2} e^{−πm²e^{2u}}`. With
`a = 1 ⋆ w` (`oneConvWeight`) and `S(y) = Σ_k a(k) e^{y/2} e^{−πk²e^{2y}} = e^{y/2} θ_a(e^{2y})`, the
scaling `cuspTerm_add_log` rearranges `Σ_n w(n) n^{−1/2} Φ(y + log n)` into `S''(y) − S(y)/4`
(`tsum_shift_cuspSeries_eq`). By evenness of `Φ`, `G_w(y) = F''(y) − F(y)/4` with
`F(y) = S(y) + S(−y)`. So `F = A(e^{y/2} + e^{−y/2})`, which is the odd theta relation
`θ_a(x) = −x^{−1/2} θ_a(1/x) + A + A x^{−1/2}`. Hamburger's theorem in its odd form
(`coeff_eq_zero_of_odd_coeffTheta_relation`) forces `a = 0`, and Möbius inversion gives `w = 0`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace RHTower

noncomputable section

/-! ## Scaling of cusp terms -/

theorem exp_half_log_eq_sqrt {N : ℝ} (hN : 0 < N) : Real.exp (Real.log N / 2) = Real.sqrt N := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hN]; ring_nf

/-- `cuspTerm R m (y + log N) = √N · cuspTerm R (N m) y`. -/
theorem cuspTerm_add_log (R : ℝ[X]) (m : ℕ) {N : ℕ} (hN : 0 < N) (y : ℝ) :
    cuspTerm R m (y + Real.log N) = Real.sqrt N * cuspTerm R (N * m) y := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cuspTerm
  have h1 : Real.exp ((y + Real.log N) / 2) = Real.sqrt N * Real.exp (y / 2) := by
    rw [show (y + Real.log N) / 2 = Real.log N / 2 + y / 2 by ring, Real.exp_add,
      exp_half_log_eq_sqrt hNpos]
  have h2 : (m : ℝ) ^ 2 * Real.exp (2 * (y + Real.log N)) =
      ((N * m : ℕ) : ℝ) ^ 2 * Real.exp (2 * y) := by
    rw [show 2 * (y + Real.log N) = 2 * y + (Real.log N + Real.log N) by ring, Real.exp_add,
      Real.exp_add, Real.exp_log hNpos]
    push_cast; ring
  rw [h1, h2]; ring

/-! ## Weighted cusp series -/

/-- `Σ_{k ≥ 1} a(k) e^{y/2} R(k²e^{2y}) e^{−πk²e^{2y}}`. -/
def weightedCuspSeries (a : ℕ → ℝ) (R : ℝ[X]) (y : ℝ) : ℝ :=
  ∑' k : ℕ, a (k + 1) * cuspTerm R (k + 1) y

theorem abs_weightedCuspTerm_le {a : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (ha : ∀ k : ℕ, |a (k + 1)| ≤ K * ((k + 1 : ℕ) : ℝ) ^ p) (R : ℝ[X]) (k : ℕ) {y Y₁ Y₂ H : ℝ}
    (hY₁ : 0 < Y₁) (h1 : Y₁ ≤ Real.exp (2 * y)) (h2 : Real.exp (2 * y) ≤ Y₂)
    (hH : Real.exp (y / 2) ≤ H) :
    |a (k + 1) * cuspTerm R (k + 1) y| ≤
      K * (H * polyAbsBound R * (1 + Y₂) ^ R.natDegree) *
        (((k + 1 : ℕ) : ℝ) ^ (p + 2 * R.natDegree) * Real.exp (-(π * Y₁) * ((k + 1 : ℕ) : ℝ))) := by
  have hc := abs_cuspTerm_le R k hY₁ h1 h2 hH
  have hK : 0 ≤ K := by
    have := (abs_nonneg _).trans (ha 0); simp at this; nlinarith [this]
  rw [abs_mul]
  calc |a (k + 1)| * |cuspTerm R (k + 1) y|
      ≤ (K * ((k + 1 : ℕ) : ℝ) ^ p) * (H * polyAbsBound R * (1 + Y₂) ^ R.natDegree *
          ((k + 1 : ℕ) : ℝ) ^ (2 * R.natDegree) * Real.exp (-(π * Y₁) * ((k + 1 : ℕ) : ℝ))) :=
        mul_le_mul (ha k) hc (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem summable_weightedCuspTerm {a : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (ha : ∀ k : ℕ, |a (k + 1)| ≤ K * ((k + 1 : ℕ) : ℝ) ^ p) (R : ℝ[X]) (y : ℝ) :
    Summable fun k : ℕ => a (k + 1) * cuspTerm R (k + 1) y := by
  have hY := Real.exp_pos (2 * y)
  refine Summable.of_norm_bounded ((summable_cuspTerm_bound (p + 2 * R.natDegree)
    (mul_pos Real.pi_pos hY)).mul_left
      (K * (Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree)))
    fun k => ?_
  rw [Real.norm_eq_abs]
  exact abs_weightedCuspTerm_le ha R k hY le_rfl le_rfl le_rfl

theorem hasDerivAt_weightedCuspSeries {a : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (ha : ∀ k : ℕ, |a (k + 1)| ≤ K * ((k + 1 : ℕ) : ℝ) ^ p) (R : ℝ[X]) (y₀ : ℝ) :
    HasDerivAt (weightedCuspSeries a R) (weightedCuspSeries a (cuspDeriv R) y₀) y₀ := by
  set Y₁ := Real.exp (2 * (y₀ - 1)) with hY₁
  set Y₂ := Real.exp (2 * (y₀ + 1)) with hY₂
  set H := Real.exp ((y₀ + 1) / 2) with hH
  have hY₁0 : 0 < Y₁ := Real.exp_pos _
  set d := (cuspDeriv R).natDegree with hd
  have hbound : ∀ k : ℕ, ∀ y ∈ Ioo (y₀ - 1) (y₀ + 1),
      ‖a (k + 1) * cuspTerm (cuspDeriv R) (k + 1) y‖ ≤
        K * (H * polyAbsBound (cuspDeriv R) * (1 + Y₂) ^ d) *
          (((k + 1 : ℕ) : ℝ) ^ (p + 2 * d) * Real.exp (-(π * Y₁) * ((k + 1 : ℕ) : ℝ))) := by
    intro k y hy
    have hy' : y₀ - 1 < y ∧ y < y₀ + 1 := hy
    rw [Real.norm_eq_abs]
    exact abs_weightedCuspTerm_le ha (cuspDeriv R) k hY₁0
      (Real.exp_le_exp.mpr (by linarith [hy'.1])) (Real.exp_le_exp.mpr (by linarith [hy'.2]))
      (Real.exp_le_exp.mpr (by linarith [hy'.2]))
  have hsum := (summable_cuspTerm_bound (p + 2 * d) (mul_pos Real.pi_pos hY₁0)).mul_left
    (K * (H * polyAbsBound (cuspDeriv R) * (1 + Y₂) ^ d))
  exact hasDerivAt_tsum_of_isPreconnected (g := fun k : ℕ => fun y => a (k + 1) * cuspTerm R (k + 1) y)
    (g' := fun k : ℕ => fun y => a (k + 1) * cuspTerm (cuspDeriv R) (k + 1) y) hsum isOpen_Ioo
    isPreconnected_Ioo (fun k y _ => (hasDerivAt_cuspTerm R (k + 1) y).const_mul _) hbound
    (y₀ := y₀) (show y₀ ∈ Ioo (y₀ - 1) (y₀ + 1) from ⟨by linarith, by linarith⟩)
    (summable_weightedCuspTerm ha R y₀) (show y₀ ∈ Ioo (y₀ - 1) (y₀ + 1) from ⟨by linarith, by linarith⟩)

theorem weightedCuspSeries_riemannCuspPoly {a : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (ha : ∀ k : ℕ, |a (k + 1)| ≤ K * ((k + 1 : ℕ) : ℝ) ^ p) (y : ℝ) :
    weightedCuspSeries a riemannCuspPoly y =
      weightedCuspSeries a (cuspDeriv (cuspDeriv 1)) y - weightedCuspSeries a 1 y / 4 := by
  unfold weightedCuspSeries
  have hterm : ∀ k : ℕ, a (k + 1) * cuspTerm riemannCuspPoly (k + 1) y =
      a (k + 1) * cuspTerm (cuspDeriv (cuspDeriv 1)) (k + 1) y -
        (1 / 4) * (a (k + 1) * cuspTerm 1 (k + 1) y) := by
    intro k
    unfold riemannCuspPoly cuspTerm
    simp only [eval_sub, eval_mul, eval_C, eval_one]
    ring
  simp_rw [hterm]
  rw [(summable_weightedCuspTerm ha _ y).tsum_sub ((summable_weightedCuspTerm ha 1 y).mul_left _),
    tsum_mul_left]
  ring

/-! ## Divisor rearrangement -/

/-- The divisor sum `(1 ⋆ w)(k) = Σ_{d ∣ k} w(d)`. -/
def oneConvWeight (w : ℕ → ℝ) (k : ℕ) : ℝ := ∑ d ∈ k.divisors, w d

/-- **Rearrangement over factorizations.** `Σ_{n,m ≥ 1} w(n) F(nm) = Σ_{k ≥ 1} (1 ⋆ w)(k) F(k)`. -/
theorem hasSum_divisorWeight_mul {w F : ℕ → ℝ}
    (hs : Summable fun q : ℕ × ℕ => w (q.1 + 1) * F ((q.1 + 1) * (q.2 + 1))) :
    HasSum (fun k : ℕ => oneConvWeight w (k + 1) * F (k + 1))
      (∑' q : ℕ × ℕ, w (q.1 + 1) * F ((q.1 + 1) * (q.2 + 1))) := by
  set f₁ : ℕ+ × ℕ+ → ℝ := fun q => w q.1 * F (q.1 * q.2) with hf₁
  set e : ℕ × ℕ ≃ ℕ+ × ℕ+ := (Equiv.pnatEquivNat.prodCongr Equiv.pnatEquivNat).symm with he
  have hcomp : (fun q : ℕ × ℕ => w (q.1 + 1) * F ((q.1 + 1) * (q.2 + 1))) = f₁ ∘ e := by
    funext q
    simp [hf₁, he, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe]
  have h1 : HasSum f₁ (∑' q : ℕ × ℕ, w (q.1 + 1) * F ((q.1 + 1) * (q.2 + 1))) := by
    rw [← e.hasSum_iff, ← hcomp]; exact hs.hasSum
  have h2 := (sigmaAntidiagonalEquivProd.hasSum_iff (f := f₁)).mpr h1
  have h3 : ∀ k : ℕ+, HasSum (fun c : Nat.divisorsAntidiagonal (k : ℕ) =>
      (f₁ ∘ sigmaAntidiagonalEquivProd) ⟨k, c⟩) (oneConvWeight w k * F k) := by
    intro k
    have hfin := hasSum_fintype (fun c : Nat.divisorsAntidiagonal (k : ℕ) =>
      (f₁ ∘ sigmaAntidiagonalEquivProd) ⟨k, c⟩)
    convert hfin using 1
    rw [Finset.univ_eq_attach]
    simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
      divisorsAntidiagonalFactors, hf₁, PNat.mk_coe]
    rw [(Nat.divisorsAntidiagonal (k : ℕ)).sum_attach (fun x : ℕ × ℕ => w x.1 * F (x.1 * x.2)),
      Nat.sum_divisorsAntidiagonal (fun a b => w a * F (a * b)), oneConvWeight, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  have h4 := h2.sigma h3
  have h5 := (Equiv.pnatEquivNat.symm.hasSum_iff (f := fun k : ℕ+ => oneConvWeight w k * F k)).mpr h4
  convert h5 using 1
  funext k
  simp [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe]

/-- The double family `w(n) cuspTerm R (nm) y` is dominated by a product of summable sequences. -/
theorem abs_mul_cuspTerm_prod_le {w : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (hw : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ p) (R : ℝ[X]) (y : ℝ) (n m : ℕ) :
    |w (n + 1) * cuspTerm R ((n + 1) * (m + 1)) y| ≤
      (K * (Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree)) *
        ((((n + 1 : ℕ) : ℝ) ^ (p + 2 * R.natDegree) *
          Real.exp (-(π * Real.exp (2 * y) / 2) * ((n + 1 : ℕ) : ℝ))) *
        (((m + 1 : ℕ) : ℝ) ^ (2 * R.natDegree) *
          Real.exp (-(π * Real.exp (2 * y) / 2) * ((m + 1 : ℕ) : ℝ)))) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg _).trans (hw 0); simp at this; nlinarith [this]
  have hY : 0 < Real.exp (2 * y) := Real.exp_pos _
  have hidx : (n + 1) * (m + 1) = ((n + 1) * (m + 1) - 1) + 1 := by
    have : 1 ≤ (n + 1) * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hc := abs_cuspTerm_le R ((n + 1) * (m + 1) - 1) hY le_rfl le_rfl le_rfl
  rw [← hidx] at hc
  have hcast : (((n + 1) * (m + 1) : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast] at hc
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hexp : Real.exp (-(π * Real.exp (2 * y)) * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ))) ≤
      Real.exp (-(π * Real.exp (2 * y) / 2) * ((n + 1 : ℕ) : ℝ)) *
        Real.exp (-(π * Real.exp (2 * y) / 2) * ((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have h1 : ((n + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) ≤
        2 * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) := by nlinarith
    have hpY : 0 < π * Real.exp (2 * y) := mul_pos Real.pi_pos hY
    nlinarith
  have hB0 : 0 ≤ Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree := by
    have := polyAbsBound_nonneg R; positivity
  rw [abs_mul]
  calc |w (n + 1)| * |cuspTerm R ((n + 1) * (m + 1)) y|
      ≤ (K * ((n + 1 : ℕ) : ℝ) ^ p) *
          (Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree *
            (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) ^ (2 * R.natDegree) *
            Real.exp (-(π * Real.exp (2 * y)) * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)))) :=
        mul_le_mul (hw n) hc (abs_nonneg _) (by positivity)
    _ ≤ (K * ((n + 1 : ℕ) : ℝ) ^ p) *
          (Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree *
            (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) ^ (2 * R.natDegree) *
            (Real.exp (-(π * Real.exp (2 * y) / 2) * ((n + 1 : ℕ) : ℝ)) *
              Real.exp (-(π * Real.exp (2 * y) / 2) * ((m + 1 : ℕ) : ℝ)))) := by gcongr
    _ = _ := by rw [mul_pow, pow_add]; ring

/-- `Σ_n w(n) n^{−1/2} S_R(y + log n) = Σ_k (1 ⋆ w)(k) · cuspTerm R k y`. -/
theorem tsum_shift_cuspSeries_eq {w : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (hw : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ p) (R : ℝ[X]) (y : ℝ) :
    ∑' n : ℕ, w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) * cuspSeries R (y + Real.log ((n + 1 : ℕ) : ℝ)) =
      weightedCuspSeries (oneConvWeight w) R y := by
  have hY : 0 < Real.exp (2 * y) := Real.exp_pos _
  have hsumN := summable_cuspTerm_bound (p + 2 * R.natDegree)
    (by positivity : 0 < π * Real.exp (2 * y) / 2)
  have hsumM := summable_cuspTerm_bound (2 * R.natDegree)
    (by positivity : 0 < π * Real.exp (2 * y) / 2)
  have hprod := (hsumN.mul_of_nonneg hsumM (fun _ => by positivity) (fun _ => by positivity)).mul_left
    (K * (Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree))
  have hs : Summable fun q : ℕ × ℕ => w (q.1 + 1) * cuspTerm R ((q.1 + 1) * (q.2 + 1)) y :=
    Summable.of_norm_bounded hprod fun q => by
      rw [Real.norm_eq_abs]; exact abs_mul_cuspTerm_prod_le hw R y q.1 q.2
  -- rewrite the left side as the double sum
  have hleft : ∀ n : ℕ, w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      cuspSeries R (y + Real.log ((n + 1 : ℕ) : ℝ)) =
      ∑' m : ℕ, w (n + 1) * cuspTerm R ((n + 1) * (m + 1)) y := by
    intro n
    have hN : 0 < n + 1 := Nat.succ_pos n
    have hsq : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    unfold cuspSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [cuspTerm_add_log R (m + 1) hN y, ← mul_assoc, div_mul_cancel₀ _ hsq.ne']
  rw [tsum_congr hleft, ← hs.tsum_prod]
  have h := (hasSum_divisorWeight_mul (w := w) (F := fun k => cuspTerm R k y) hs).tsum_eq
  exact h.symm

/-- The shifted sum `Σ_n w(n) n^{−1/2} S_R(y + log n)` converges. -/
theorem summable_shift_cuspSeries {w : ℕ → ℝ} {K : ℝ} {p : ℕ}
    (hw : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ p) (R : ℝ[X]) (y : ℝ) :
    Summable fun n : ℕ =>
      w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) * cuspSeries R (y + Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hY : 0 < Real.exp (2 * y) := Real.exp_pos _
  have hsumN := summable_cuspTerm_bound (p + 2 * R.natDegree)
    (by positivity : 0 < π * Real.exp (2 * y) / 2)
  have hsumM := summable_cuspTerm_bound (2 * R.natDegree)
    (by positivity : 0 < π * Real.exp (2 * y) / 2)
  have hprod := (hsumN.mul_of_nonneg hsumM (fun _ => by positivity) (fun _ => by positivity)).mul_left
    (K * (Real.exp (y / 2) * polyAbsBound R * (1 + Real.exp (2 * y)) ^ R.natDegree))
  have hs : Summable fun q : ℕ × ℕ => w (q.1 + 1) * cuspTerm R ((q.1 + 1) * (q.2 + 1)) y :=
    Summable.of_norm_bounded hprod fun q => by
      rw [Real.norm_eq_abs]; exact abs_mul_cuspTerm_prod_le hw R y q.1 q.2
  refine hs.prod.congr fun n => ?_
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hsq : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  unfold cuspSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [cuspTerm_add_log R (m + 1) hN y, ← mul_assoc, div_mul_cancel₀ _ hsq.ne']

/-! ## A second-order linear equation -/

/-- Solutions of `f'' = f/4` on the line are `A e^{y/2} + B e^{−y/2}`. -/
theorem exists_eq_exp_of_second_deriv {f f₁ f₂ : ℝ → ℝ} (h1 : ∀ y, HasDerivAt f (f₁ y) y)
    (h2 : ∀ y, HasDerivAt f₁ (f₂ y) y) (h : ∀ y, f₂ y = f y / 4) :
    ∃ A B : ℝ, ∀ y, f y = A * Real.exp (y / 2) + B * Real.exp (-(y / 2)) := by
  set g : ℝ → ℝ := fun y => f₁ y - f y / 2 with hg
  have hgd : ∀ y, HasDerivAt g (-(g y) / 2) y := by
    intro y
    have := (h2 y).sub ((h1 y).div_const 2)
    refine this.congr_deriv ?_
    rw [h y]; simp only [hg]; ring
  have hE : ∀ y, HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (y / 2) * (1 / 2)) y := by
    intro y
    have := (Real.hasDerivAt_exp (y / 2)).comp y ((hasDerivAt_id y).div_const 2)
    exact this.congr_deriv (by simp)
  have hEn : ∀ y, HasDerivAt (fun y : ℝ => Real.exp (-(y / 2)))
      (Real.exp (-(y / 2)) * (-(1 / 2))) y := by
    intro y
    have := (Real.hasDerivAt_exp (-(y / 2))).comp y ((hasDerivAt_id y).div_const 2).neg
    exact this.congr_deriv (by simp)
  have hEn1 : ∀ y, HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-y) * (-1)) y := by
    intro y
    have := (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_id y).neg
    exact this.congr_deriv (by simp)
  -- `e^{y/2} g` is constant
  have hc1 : ∀ y, HasDerivAt (fun y => Real.exp (y / 2) * g y) 0 y := by
    intro y
    have := (hE y).mul (hgd y)
    refine this.congr_deriv ?_
    ring
  have hconst1 : ∀ y, Real.exp (y / 2) * g y = Real.exp (0 / 2) * g 0 :=
    fun y => is_const_of_deriv_eq_zero (fun y => (hc1 y).differentiableAt)
      (fun y => (hc1 y).deriv) y 0
  set C := Real.exp (0 / 2) * g 0 with hC
  have hgval : ∀ y, g y = C * Real.exp (-(y / 2)) := by
    intro y
    have h := hconst1 y
    have hE' : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by rw [← Real.exp_add]; simp
    calc g y = (Real.exp (y / 2) * Real.exp (-(y / 2))) * g y := by rw [hE', one_mul]
      _ = (Real.exp (y / 2) * g y) * Real.exp (-(y / 2)) := by ring
      _ = C * Real.exp (-(y / 2)) := by rw [h]
  -- `e^{−y/2} f + C e^{−y}` is constant
  have hc2 : ∀ y, HasDerivAt (fun y => Real.exp (-(y / 2)) * f y + C * Real.exp (-y)) 0 y := by
    intro y
    have := ((hEn y).mul (h1 y)).add ((hEn1 y).const_mul C)
    refine this.congr_deriv ?_
    have hgy := hgval y
    simp only [hg] at hgy
    have hEE : Real.exp (-(y / 2)) * Real.exp (-(y / 2)) = Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have : f₁ y = C * Real.exp (-(y / 2)) + f y / 2 := by linarith
    rw [this]
    linear_combination C * hEE
  have hconst2 : ∀ y, Real.exp (-(y / 2)) * f y + C * Real.exp (-y) =
      Real.exp (-(0 / 2)) * f 0 + C * Real.exp (-0) :=
    fun y => is_const_of_deriv_eq_zero (fun y => (hc2 y).differentiableAt)
      (fun y => (hc2 y).deriv) y 0
  refine ⟨Real.exp (-(0 / 2)) * f 0 + C * Real.exp (-0), -C, fun y => ?_⟩
  have h := hconst2 y
  have hE' : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by rw [← Real.exp_add]; simp
  have hE'' : Real.exp (y / 2) * Real.exp (-y) = Real.exp (-(y / 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc f y = Real.exp (y / 2) * (Real.exp (-(y / 2)) * f y + C * Real.exp (-y)) -
        C * (Real.exp (y / 2) * Real.exp (-y)) := by
        rw [mul_add, ← mul_assoc, hE']; ring
    _ = _ := by rw [h, hE'']; ring

/-! ## The theorem -/

theorem cuspSeries_riemannCuspPoly_eq (u : ℝ) : cuspSeries riemannCuspPoly u = riemannKernelReal u := by
  have h := riemannPhiKernel_eq_cuspSeries u
  rw [riemannPhiKernel_eq_ofReal] at h
  exact_mod_cast h.symm

theorem weightedCuspSeries_one_eq (a : ℕ → ℝ) (y : ℝ) :
    weightedCuspSeries a 1 y = Real.exp (y / 2) *
      ∑' k : ℕ, a (k + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * Real.exp (2 * y)) := by
  unfold weightedCuspSeries cuspTerm
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [eval_one, mul_one]
  push_cast
  ring_nf

/-- **Injectivity of the Riemann-kernel transform.** If
`Σ_n w(n) n^{−1/2} (Φ(y − log n) + Φ(y + log n)) = 0` for every `y`, then `w = 0`. -/
theorem eq_zero_of_riemannKernelTransform_eq_zero {w : ℕ → ℝ}
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |w (n + 1)| / ((n : ℝ) + 1) ^ σ)
    (hG : ∀ y : ℝ, ∑' n : ℕ, w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) +
        riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ))) = 0) :
    ∀ n : ℕ, w (n + 1) = 0 := by
  -- polynomial growth
  have hs2 := hsum 2 (by norm_num)
  set K := ∑' n : ℕ, |w (n + 1)| / ((n : ℝ) + 1) ^ (2 : ℝ) with hKdef
  have hw : ∀ n : ℕ, |w (n + 1)| ≤ K * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    have hle := hs2.le_tsum n (fun j _ => by positivity)
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ (2 : ℝ) := by positivity
    rw [div_le_iff₀ hpos] at hle
    have : ((n : ℝ) + 1) ^ (2 : ℝ) = ((n + 1 : ℕ) : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; ring
    rw [this] at hle; exact hle
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => by positivity
  set a := oneConvWeight w with hadef
  have ha : ∀ k : ℕ, |a (k + 1)| ≤ (|w 0| + K) * ((k + 1 : ℕ) : ℝ) ^ 3 := by
    intro k
    unfold a oneConvWeight
    have hmem : ∀ d ∈ (k + 1).divisors, |w d| ≤ (|w 0| + K) * ((k + 1 : ℕ) : ℝ) ^ 2 := by
      intro d hd
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
      have hdk : d ≤ k + 1 := Nat.divisor_le hd
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have h1 := hw e
      have h2 : ((e + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr
      nlinarith [abs_nonneg (w 0)]
    calc |∑ d ∈ (k + 1).divisors, w d| ≤ ∑ d ∈ (k + 1).divisors, |w d| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ (k + 1).divisors, (|w 0| + K) * ((k + 1 : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum hmem
      _ = ((k + 1).divisors.card : ℝ) * ((|w 0| + K) * ((k + 1 : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((k + 1 : ℕ) : ℝ) * ((|w 0| + K) * ((k + 1 : ℕ) : ℝ) ^ 2) := by
          gcongr; exact_mod_cast Nat.card_divisors_le_self _
      _ = _ := by ring
  -- the kernel sum as a weighted cusp series
  set S := weightedCuspSeries a 1 with hS
  set S₁ := weightedCuspSeries a (cuspDeriv 1) with hS₁
  set S₂ := weightedCuspSeries a (cuspDeriv (cuspDeriv 1)) with hS₂
  have hshift : ∀ y, ∑' n : ℕ, w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ)) = S₂ y - S y / 4 := by
    intro y
    have h := tsum_shift_cuspSeries_eq hw riemannCuspPoly y
    simp_rw [cuspSeries_riemannCuspPoly_eq] at h
    rw [h, weightedCuspSeries_riemannCuspPoly ha y]
  have hsummG : ∀ y, Summable fun n : ℕ => w (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ)) := by
    intro y
    have h := summable_shift_cuspSeries hw riemannCuspPoly y
    simpa only [cuspSeries_riemannCuspPoly_eq] using h
  have hF : ∀ y, (S₂ y - S y / 4) + (S₂ (-y) - S (-y) / 4) = 0 := by
    intro y
    rw [← hshift y, ← hshift (-y)]
    have h := hG y
    have hev : ∀ n : ℕ, riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) =
        riemannKernelReal (-y + Real.log ((n + 1 : ℕ) : ℝ)) := by
      intro n
      unfold riemannKernelReal
      rw [show -y + Real.log ((n + 1 : ℕ) : ℝ) = -(y - Real.log ((n + 1 : ℕ) : ℝ)) by ring, abs_neg]
    simp_rw [hev, mul_add] at h
    rw [(hsummG (-y)).tsum_add (hsummG y)] at h
    linarith
  -- `F = S + S(−·)` solves `F'' = F/4`
  have hd0 : ∀ y, HasDerivAt S (S₁ y) y := fun y => hasDerivAt_weightedCuspSeries ha 1 y
  have hd1 : ∀ y, HasDerivAt S₁ (S₂ y) y := fun y => hasDerivAt_weightedCuspSeries ha (cuspDeriv 1) y
  have hF1 : ∀ y, HasDerivAt (fun y => S y + S (-y)) (S₁ y - S₁ (-y)) y := by
    intro y
    have := (hd0 y).add ((hd0 (-y)).comp y (hasDerivAt_neg y))
    exact this.congr_deriv (by ring)
  have hF2 : ∀ y, HasDerivAt (fun y => S₁ y - S₁ (-y)) (S₂ y + S₂ (-y)) y := by
    intro y
    have := (hd1 y).sub ((hd1 (-y)).comp y (hasDerivAt_neg y))
    exact this.congr_deriv (by ring)
  obtain ⟨A, B, hAB⟩ := exists_eq_exp_of_second_deriv hF1 hF2 (fun y => by
    have := hF y; linarith)
  have hAB' : A = B := by
    have h1 := hAB 2
    have h2 := hAB (-2)
    have hsym : S 2 + S (-2) = S (-2) + S (-(-2)) := by rw [neg_neg]; ring
    rw [h1, h2] at hsym
    have hne : Real.exp (2 / 2) ≠ Real.exp (-(2 / 2)) := by
      intro h; have := Real.exp_injective h; linarith
    have hsub : (A - B) * (Real.exp (2 / 2) - Real.exp (-(2 / 2))) = 0 := by
      rw [show -(-2 / 2 : ℝ) = 2 / 2 by ring, show (-2 / 2 : ℝ) = -(2 / 2) by ring] at hsym
      linarith
    rcases mul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) hne
  -- the odd theta relation
  set a' : ℕ → ℂ := fun k => (a k : ℂ) with ha'
  have htheta : ∀ x : ℝ, 0 < x → GaloisForLFunctions.HTGeometry.coeffTheta a' x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * GaloisForLFunctions.HTGeometry.coeffTheta a' x⁻¹) +
        (A : ℂ) + (A : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    set T : ℝ → ℝ := fun x => ∑' k : ℕ, a (k + 1) * Real.exp (-π * ((k : ℝ) + 1) ^ 2 * x) with hT
    have hθ : ∀ x : ℝ, GaloisForLFunctions.HTGeometry.coeffTheta a' x = (T x : ℂ) := by
      intro x
      rw [GaloisForLFunctions.HTGeometry.coeffTheta, hT, Complex.ofReal_tsum]
      refine tsum_congr fun k => ?_
      simp only [ha']; push_cast; ring_nf
    set y := Real.log x / 2 with hy
    have hx2 : Real.exp (2 * y) = x := by rw [hy, show 2 * (Real.log x / 2) = Real.log x by ring,
      Real.exp_log hx]
    have hx2' : Real.exp (2 * (-y)) = x⁻¹ := by
      rw [show 2 * (-y) = -(2 * y) by ring, Real.exp_neg, hx2]
    have hS : ∀ u, S u = Real.exp (u / 2) * T (Real.exp (2 * u)) := fun u => by
      rw [hS, weightedCuspSeries_one_eq]
    have hrel := hAB y
    rw [hAB', hS y, hS (-y), hx2, hx2'] at hrel
    -- hrel : e^{y/2} T x + e^{-y/2} T x⁻¹ = B e^{y/2} + B e^{-y/2}
    have hpow : ((x : ℂ) ^ (-(1 / 2 : ℂ))) = ((Real.exp (-y) : ℝ) : ℂ) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hx.le, Real.rpow_def_of_pos hx, hy]
      congr 1; ring_nf
    have hE1 : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
    have hE2 : Real.exp (-(y / 2)) * Real.exp (-(y / 2)) = Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have hreal : T x = -(Real.exp (-y) * T x⁻¹) + B + B * Real.exp (-y) := by
      have h := congrArg (fun t => Real.exp (-(y / 2)) * t) hrel
      beta_reduce at h
      have e1 : Real.exp (-(y / 2)) * (Real.exp (y / 2) * T x + Real.exp (-y / 2) * T x⁻¹) =
          T x + Real.exp (-y) * T x⁻¹ := by
        rw [show -y / 2 = -(y / 2) by ring, mul_add, ← mul_assoc, hE1, ← mul_assoc, hE2, one_mul]
      have e2 : Real.exp (-(y / 2)) * (B * Real.exp (y / 2) + B * Real.exp (-(y / 2))) =
          B + B * Real.exp (-y) := by
        rw [mul_add, show Real.exp (-(y / 2)) * (B * Real.exp (y / 2)) =
          B * (Real.exp (-(y / 2)) * Real.exp (y / 2)) by ring, hE1,
          show Real.exp (-(y / 2)) * (B * Real.exp (-(y / 2))) =
          B * (Real.exp (-(y / 2)) * Real.exp (-(y / 2))) by ring, hE2, mul_one]
      rw [e1, e2] at h
      linarith
    rw [hθ x, hθ x⁻¹, hpow, hreal, hAB']
    push_cast
    ring
  have ha'sum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a' (n + 1)‖ / ((n : ℝ) + 1) ^ σ := by
    intro σ hσ
    have hone : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ σ := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hσ)
      simpa using this
    have hpair : Summable fun q : ℕ × ℕ =>
        |w (q.1 + 1)| * (1 / (((q.1 + 1) * (q.2 + 1) : ℕ) : ℝ) ^ σ) := by
      have h := (hsum σ hσ).mul_of_nonneg hone (fun _ => by positivity) (fun _ => by positivity)
      refine h.congr fun q => ?_
      rw [show (((q.1 + 1) * (q.2 + 1) : ℕ) : ℝ) = ((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1) by push_cast; ring,
        Real.mul_rpow (by positivity) (by positivity)]
      field_simp
    have hdiv := (hasSum_divisorWeight_mul (w := fun n => |w n|)
      (F := fun k => 1 / ((k : ℕ) : ℝ) ^ σ) hpair).summable
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hdiv
    simp only [ha', Complex.norm_real, Real.norm_eq_abs, oneConvWeight]
    have habs : |∑ d ∈ (n + 1).divisors, w d| ≤ ∑ d ∈ (n + 1).divisors, |w d| :=
      Finset.abs_sum_le_sum_abs _ _
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := by positivity
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right habs (by positivity)
  have hzero : ∀ k : ℕ, a (k + 1) = 0 := fun k => by
    have h : (a (k + 1) : ℂ) = 0 :=
      GaloisForLFunctions.HTGeometry.coeff_eq_zero_of_odd_coeffTheta_relation ha'sum htheta k
    exact_mod_cast h
  -- Möbius inversion
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := hzero n
    unfold a oneConvWeight at h
    rw [← Nat.cons_self_properDivisors (Nat.succ_ne_zero n), Finset.sum_cons] at h
    have hprop : ∑ d ∈ (n + 1).properDivisors, w d = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos n)
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      exact ih e (by omega)
    linarith

end

end RHTower
