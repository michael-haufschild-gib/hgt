import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau
import GaloisForLFunctions.RHTower.LandauRelativeRigidity
import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# A polarized base whose Adams squares continue is pure

The positive counterpart of the ruler theorems for flow data and abelian bases. A **polarized
datum** of rank `2g` over a base has at each point `x` (frequency `ℓ(x) = log N(x)`, weight
`λ(x) ≥ 0`) the parameters `α_{x,i}^{±1}`, `i < g`: the functional equation pairs `α` with `α⁻¹`
(weight normalized to `0`). The `m`-th Adams power has level-`n` trace
`p_m(x, n) = Σ_i (α_{x,i}^{mn} + α_{x,i}^{−mn})`, assumed real (`adamsTrace`). It moves a parameter of
modulus `N^δ` to `N^{mδ}`: it is the tensor-power amplification without the combinatorics of
`V^{⊗k}`.

* **The Rankin–Landau step** (`norm_eq_one_of_adamsPoleLaw`). If for every `m ≥ 1` the
  Rankin–Selberg square `Σ_{x,n} λ(x) p_m(x,n)² N(x)^{−ns}` of the `m`-th Adams power converges
  somewhere and continues analytically to `Re s > 1` (`AdamsPoleLaw`), then every parameter at a
  point of positive weight is unitary. Landau's theorem turns the continuation into convergence on
  `Re s > 1` (the coefficients are squares); one point of the base then gives
  `|α_{x,i}|^m ≤ N(x)` for every `m` through power-sum rigidity.
* **Rank two: the Adams package** (`norm_eq_one_of_adams_continue`). For `g = 1`,
  `p_m² = p_{2m} + 2`: the square of an Adams power is the next Adams power plus the
  polarization pairs `α^m ⊗ α^{−m}`, of weight `det = 1` whatever `α` is. So it suffices that the
  base series converges on `Re s > 1` and that every Adams series `Σ λ(x) p_j(x,n) N(x)^{−ns}`,
  `j ≥ 1`, converges somewhere and continues to `Re s > 1`.

For an automorphic representation of `GL₂` the Adams series are differences of logarithmic
derivatives of symmetric-power `L`-functions, and the package is the classical observation that
symmetric-power functoriality gives the Ramanujan bound. For a flow datum or an abelian base the
corresponding constituents are the shifted modes themselves, whose series have their poles at
`1 + Z`: there the package is the conclusion. A pencil through `ζ` has to provide the package
with constituents that are `L`-functions of other objects.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {ι : Type*} {g : ℕ}

/-- The level-`n` trace of the `m`-th Adams power at `x`: `Σ_i (α_{x,i}^{mn} + α_{x,i}^{−mn})`. -/
def adamsTrace (α : ι → Fin g → ℂ) (m n : ℕ) (x : ι) : ℂ :=
  ∑ i, ((α x i) ^ (m * n) + (α x i)⁻¹ ^ (m * n))

/-- Frequency `(n + 1) ℓ(x)` of the level `n + 1` at `x`. -/
def levelFreq (ℓ : ι → ℝ) (p : ι × ℕ) : ℝ := (p.2 + 1) * ℓ p.1

/-- Coefficients `λ(x) p_m(x, n+1)²` of the Rankin–Selberg square of the `m`-th Adams power. -/
def adamsSquareCoeff (lam : ι → ℝ) (α : ι → Fin g → ℂ) (m : ℕ) (p : ι × ℕ) : ℝ :=
  lam p.1 * (adamsTrace α m (p.2 + 1) p.1).re ^ 2

/-- **The pole law of the Adams squares**: for every `m ≥ 1` the Rankin–Selberg square of the
`m`-th Adams power converges at some `σ₁` and continues analytically to `Re s > 1`. -/
def AdamsPoleLaw (ℓ lam : ι → ℝ) (α : ι → Fin g → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ σ₁ : ℝ, Summable (gdTwistTerm (adamsSquareCoeff lam α m) (levelFreq ℓ) σ₁ 0) ∧
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 1 < s.re} ∧
      ∀ s : ℂ, σ₁ < s.re → G s = gdSeries (adamsSquareCoeff lam α m) (levelFreq ℓ) s

theorem adamsSquareCoeff_nonneg {lam : ι → ℝ} (hlam : ∀ x, 0 ≤ lam x) (α : ι → Fin g → ℂ) (m : ℕ)
    (p : ι × ℕ) : 0 ≤ adamsSquareCoeff lam α m p :=
  mul_nonneg (hlam _) (sq_nonneg _)

theorem levelFreq_nonneg {ℓ : ι → ℝ} (hℓ : ∀ x, 0 ≤ ℓ x) (p : ι × ℕ) : 0 ≤ levelFreq ℓ p :=
  mul_nonneg (by positivity) (hℓ _)

/-- A parameter whose powers are bounded by `(e^ℓ)` for every exponent `m` has modulus at most one. -/
theorem norm_le_one_of_forall_pow_le {z : ℂ} {B : ℝ} (h : ∀ m : ℕ, 1 ≤ m → ‖z‖ ^ m ≤ B) :
    ‖z‖ ≤ 1 := by
  by_contra hz
  push Not at hz
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B hz
  have h1 := h (m + 1) (by omega)
  have h2 : ‖z‖ ^ m ≤ ‖z‖ ^ (m + 1) := pow_le_pow_right₀ hz.le (by omega)
  linarith

/-- `e^{−2(n+1)ℓ} · (e^ℓ)^{2(n+1)} = 1`. -/
theorem exp_levelFreq (ℓ : ι → ℝ) (x : ι) (n : ℕ) :
    Real.exp (-(2 * levelFreq ℓ (x, n))) * (Real.exp (ℓ x) ^ (n + 1)) ^ 2 = 1 := by
  have h1 : (Real.exp (ℓ x) ^ (n + 1)) ^ 2 = Real.exp (2 * levelFreq ℓ (x, n)) := by
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    simp only [levelFreq]
    push_cast
    ring
  rw [h1, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **The Rankin–Landau step.** Under the pole law of the Adams squares, every parameter at a
point of positive weight is unitary. -/
theorem norm_eq_one_of_adamsPoleLaw {ℓ lam : ι → ℝ} {α : ι → Fin g → ℂ}
    (hℓ : ∀ x, 0 ≤ ℓ x) (hlam : ∀ x, 0 ≤ lam x) (hα : ∀ x i, α x i ≠ 0)
    (hreal : ∀ m n x, (adamsTrace α m n x).im = 0) (hpole : AdamsPoleLaw ℓ lam α)
    {x : ι} (hx : 0 < lam x) (i : Fin g) : ‖α x i‖ = 1 := by
  -- for every m, both α and α⁻¹ have m-th power at most e^{ℓ(x)}
  have hbound : ∀ m : ℕ, 1 ≤ m → ‖α x i‖ ^ m ≤ Real.exp (ℓ x) ∧
      ‖(α x i)⁻¹‖ ^ m ≤ Real.exp (ℓ x) := by
    intro m hm
    obtain ⟨σ₁, hsum, G, hG, hagree⟩ := hpole m hm
    have ha := adamsSquareCoeff_nonneg hlam α m
    have hf := levelFreq_nonneg hℓ
    -- convergence at σ = 2, by Landau if needed
    have h2 : Summable (gdTwistTerm (adamsSquareCoeff lam α m) (levelFreq ℓ) 2 0) := by
      rcases le_or_gt σ₁ 2 with hle | hlt
      · exact summable_gdTwistTerm_of_le ha hf hsum hle
      · exact general_landau_summable_of_halfPlane_analytic ha hf hsum (by linarith : (1 : ℝ) < σ₁)
          hG hagree (by norm_num : (1 : ℝ) < 2)
    -- restrict to the levels of the point x
    have hx2 : Summable fun n : ℕ => gdTwistTerm (adamsSquareCoeff lam α m) (levelFreq ℓ) 2 0 (x, n) :=
      h2.comp_injective (fun a b h => (Prod.mk.inj h).2)
    set C := ∑' n : ℕ, gdTwistTerm (adamsSquareCoeff lam α m) (levelFreq ℓ) 2 0 (x, n)
    have hterm : ∀ n : ℕ, gdTwistTerm (adamsSquareCoeff lam α m) (levelFreq ℓ) 2 0 (x, n) ≤ C :=
      fun n => hx2.le_tsum n fun j _ => gdTwistTerm_nonneg ha hf 2 0 (x, j)
    -- the Adams traces at x grow at most like e^{ℓ(x) n}
    have hpow : ∀ n : ℕ, 1 ≤ n → ‖∑ j : Fin g ⊕ Fin g,
        (Sum.elim (fun i => (α x i) ^ m) (fun i => (α x i)⁻¹ ^ m) j) ^ n‖ ≤
          Real.sqrt (C / lam x) * Real.exp (ℓ x) ^ n := by
      intro n hn
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hsumeq : ∑ j : Fin g ⊕ Fin g,
          (Sum.elim (fun i => (α x i) ^ m) (fun i => (α x i)⁻¹ ^ m) j) ^ (n' + 1) =
          adamsTrace α m (n' + 1) x := by
        rw [Fintype.sum_sum_type, adamsTrace, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Sum.elim_inl, Sum.elim_inr, ← pow_mul]
      rw [hsumeq]
      have hre : adamsTrace α m (n' + 1) x = ((adamsTrace α m (n' + 1) x).re : ℂ) :=
        Complex.ext rfl (by simp [hreal])
      rw [hre, Complex.norm_real, Real.norm_eq_abs]
      have ht := hterm n'
      simp only [gdTwistTerm, pow_zero, mul_one, adamsSquareCoeff] at ht
      set t := (adamsTrace α m (n' + 1) x).re
      have hC0 : 0 ≤ C := tsum_nonneg fun j => gdTwistTerm_nonneg ha hf 2 0 (x, j)
      have hsq : t ^ 2 ≤ (C / lam x) * (Real.exp (ℓ x) ^ (n' + 1)) ^ 2 := by
        have h3 := mul_le_mul_of_nonneg_right ht (sq_nonneg (Real.exp (ℓ x) ^ (n' + 1)))
        have h4 := exp_levelFreq ℓ x n'
        have h5 : lam x * t ^ 2 * Real.exp (-(2 * levelFreq ℓ (x, n'))) *
            (Real.exp (ℓ x) ^ (n' + 1)) ^ 2 = lam x * t ^ 2 := by
          rw [mul_assoc (lam x * t ^ 2), h4, mul_one]
        rw [div_mul_eq_mul_div, le_div_iff₀ hx]
        linarith
      have hCl : 0 ≤ C / lam x := div_nonneg hC0 hx.le
      calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
        _ ≤ Real.sqrt ((C / lam x) * (Real.exp (ℓ x) ^ (n' + 1)) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (C / lam x) * Real.exp (ℓ x) ^ (n' + 1) := by
            rw [Real.sqrt_mul hCl, Real.sqrt_sq (by positivity)]
    have hrig := GaloisForLFunctions.RHTower.WeilKloosterman.norm_le_of_power_sums_bound
      Finset.univ (Sum.elim (fun i => (α x i) ^ m) (fun i => (α x i)⁻¹ ^ m)) (m0 := 1)
      (Real.exp_pos _).le (fun n hn => by simpa using hpow n hn)
    refine ⟨?_, ?_⟩
    · simpa [norm_pow] using hrig (Sum.inl i) (Finset.mem_univ _)
    · simpa [norm_pow] using hrig (Sum.inr i) (Finset.mem_univ _)
  have h1 : ‖α x i‖ ≤ 1 := norm_le_one_of_forall_pow_le fun m hm => (hbound m hm).1
  have h2 : ‖(α x i)⁻¹‖ ≤ 1 := norm_le_one_of_forall_pow_le fun m hm => (hbound m hm).2
  rw [norm_inv] at h2
  have hpos : 0 < ‖α x i‖ := norm_pos_iff.mpr (hα x i)
  have : 1 ≤ ‖α x i‖ := by
    rwa [inv_le_one₀ hpos] at h2
  linarith

/-! ### Rank two: the Adams package -/

/-- Coefficients `λ(x) p_j(x, n+1)` of the `j`-th Adams series of the rank-two datum `β(x)^{±1}`. -/
def adamsCoeff (lam : ι → ℝ) (β : ι → ℂ) (j : ℕ) (p : ι × ℕ) : ℝ :=
  lam p.1 * ((β p.1) ^ (j * (p.2 + 1)) + (β p.1)⁻¹ ^ (j * (p.2 + 1))).re

/-- The rank-two datum with parameters `β(x)^{±1}`. -/
def rankTwo (β : ι → ℂ) : ι → Fin 1 → ℂ := fun x _ => β x

theorem adamsTrace_rankTwo (β : ι → ℂ) (m n : ℕ) (x : ι) :
    adamsTrace (rankTwo β) m n x = β x ^ (m * n) + (β x)⁻¹ ^ (m * n) := by
  simp [adamsTrace, rankTwo]

/-- `(b^k + b^{−k})² = b^{2k} + b^{−2k} + 2`: the square of an Adams power is the next Adams power
plus the two polarization pairs. -/
theorem sq_add_inv_pow (b : ℂ) (hb : b ≠ 0) (k : ℕ) :
    (b ^ k + b⁻¹ ^ k) ^ 2 = b ^ (2 * k) + b⁻¹ ^ (2 * k) + 2 := by
  have h : b ^ k * b⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hb, one_pow]
  rw [pow_mul', pow_mul' b⁻¹]
  linear_combination 2 * h

/-- **Squares of Adams powers**: `λ p_m² = λ p_{2m} + 2λ` for a rank-two datum with real traces. -/
theorem adamsSquareCoeff_rankTwo {lam : ι → ℝ} {β : ι → ℂ} (hβ : ∀ x, β x ≠ 0)
    (hreal : ∀ m n x, (β x ^ (m * n) + (β x)⁻¹ ^ (m * n)).im = 0) (m : ℕ) (p : ι × ℕ) :
    adamsSquareCoeff lam (rankTwo β) m p = adamsCoeff lam β (2 * m) p + 2 * lam p.1 := by
  simp only [adamsSquareCoeff, adamsCoeff, adamsTrace_rankTwo]
  rw [show 2 * m * (p.2 + 1) = 2 * (m * (p.2 + 1)) by ring]
  have hw := hreal m (p.2 + 1) p.1
  have hsq : ((β p.1 ^ (m * (p.2 + 1)) + (β p.1)⁻¹ ^ (m * (p.2 + 1))).re) ^ 2 =
      ((β p.1 ^ (m * (p.2 + 1)) + (β p.1)⁻¹ ^ (m * (p.2 + 1))) ^ 2).re := by
    rw [sq, sq, Complex.mul_re, hw]
    ring
  have hre2 : ((2 : ℂ)).re = 2 := by norm_num
  rw [hsq, sq_add_inv_pow _ (hβ _), Complex.add_re, hre2]
  ring

theorem summable_ofReal_mul_cexp {κ : Type*} {a f : κ → ℝ} (hf : ∀ p, 0 ≤ f p) {σ : ℝ}
    (h : Summable fun p => |a p| * Real.exp (-(σ * f p))) {s : ℂ} (hs : σ ≤ s.re) :
    Summable fun p => (a p : ℂ) * Complex.exp (-(s * (f p : ℂ))) := by
  refine Summable.of_norm (h.of_nonneg_of_le (fun p => norm_nonneg _) fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hre : (-(s * (f p : ℂ))).re = -(s.re * f p) := by simp [Complex.mul_re]
  rw [hre]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hf p])) (abs_nonneg _)

/-- **Rank two: the Adams package proves purity.** If the base series converges on `Re s > 1` and
every Adams series `Σ λ(x) p_j(x,n) N(x)^{−ns}`, `j ≥ 1`, converges absolutely somewhere and
continues analytically to `Re s > 1`, then `|β(x)| = 1` at every point of positive weight. -/
theorem norm_eq_one_of_adams_continue {ℓ lam : ι → ℝ} {β : ι → ℂ} (hℓ : ∀ x, 0 ≤ ℓ x)
    (hlam : ∀ x, 0 ≤ lam x) (hβ : ∀ x, β x ≠ 0)
    (hreal : ∀ m n x, (β x ^ (m * n) + (β x)⁻¹ ^ (m * n)).im = 0)
    (hbase : ∀ σ : ℝ, 1 < σ →
      Summable (gdTwistTerm (fun p : ι × ℕ => lam p.1) (levelFreq ℓ) σ 0))
    (hadams : ∀ j : ℕ, 1 ≤ j → ∃ σ₁ : ℝ,
      Summable (fun p => |adamsCoeff lam β j p| * Real.exp (-(σ₁ * levelFreq ℓ p))) ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | 1 < s.re} ∧
        ∀ s : ℂ, σ₁ < s.re → G s = gdSeries (adamsCoeff lam β j) (levelFreq ℓ) s)
    {x : ι} (hx : 0 < lam x) : ‖β x‖ = 1 := by
  have hf := levelFreq_nonneg hℓ
  have hlam' : ∀ p : ι × ℕ, 0 ≤ lam p.1 := fun p => hlam p.1
  refine norm_eq_one_of_adamsPoleLaw (α := rankTwo β) hℓ hlam (fun x _ => hβ x)
    (fun m n x => by rw [adamsTrace_rankTwo]; exact hreal m n x) (fun m hm => ?_) hx 0
  obtain ⟨σ₁, hs1, G, hG, hagree⟩ := hadams (2 * m) (by omega)
  set σ₂ := max σ₁ 2
  have hσ₁ : σ₁ ≤ σ₂ := le_max_left _ _
  have hσ₂ : 1 < σ₂ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hsA : Summable fun p => |adamsCoeff lam β (2 * m) p| * Real.exp (-(σ₂ * levelFreq ℓ p)) :=
    hs1.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) fun p =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hf p])) (abs_nonneg _)
  have hsB := hbase σ₂ hσ₂
  refine ⟨σ₂, ?_, fun s => G s + 2 * gdSeries (fun p : ι × ℕ => lam p.1) (levelFreq ℓ) s, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (gdTwistTerm_nonneg (adamsSquareCoeff_nonneg hlam _ m) hf σ₂ 0)
      (fun p => ?_) (hsA.add (hsB.mul_left 2))
    simp only [gdTwistTerm, pow_zero, mul_one, adamsSquareCoeff_rankTwo hβ hreal]
    have he := Real.exp_pos (-(σ₂ * levelFreq ℓ p))
    nlinarith [le_abs_self (adamsCoeff lam β (2 * m) p), hlam p.1]
  · refine hG.add (DifferentiableOn.const_mul (fun s hs => ?_) 2)
    have hs' : 1 < s.re := hs
    have hσ : 1 < (1 + s.re) / 2 := by linarith
    exact (RHTower.differentiableAt_gdSeries hlam' hf (hbase _ hσ)
      (by linarith)).differentiableWithinAt
  · intro s hs
    have hs2 : σ₂ ≤ s.re := hs.le
    beta_reduce
    rw [hagree s (lt_of_le_of_lt hσ₁ hs)]
    have hA := summable_ofReal_mul_cexp hf hsA hs2
    have hB : Summable fun p : ι × ℕ => ((lam p.1 : ℝ) : ℂ) * Complex.exp (-(s * (levelFreq ℓ p : ℂ))) :=
      summable_ofReal_mul_cexp hf (a := fun p : ι × ℕ => lam p.1) (hsB.congr fun p => by
        simp only [gdTwistTerm, pow_zero, mul_one, abs_of_nonneg (hlam p.1)]) hs2
    simp only [gdSeries]
    rw [← tsum_mul_left, ← hA.tsum_add (hB.mul_left 2)]
    refine tsum_congr fun p => ?_
    rw [adamsSquareCoeff_rankTwo hβ hreal]
    push_cast
    ring

end GaloisForLFunctions.TensorPowerProgramme
