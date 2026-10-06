import GaloisForLFunctions.RHTower.VerticalProgressionRatioForm

/-!
# The mollified second moment along a vertical progression: quadruple expansion

With `t_ℓ = αℓ + β`, `s_ℓ = ½ + it_ℓ` and a real weight `ψ` supported in `[1, 2]`,

`S₂(T) = Σ_{ℓ ∈ ℤ} ψ(ℓ/T) |ζ(s_ℓ) M_N(s_ℓ)|²`.

**Theorem** (`norm_secondMoment_sub_expansion_le`). For `αT ≥ 32` and `2|β| ≤ αT`,

`S₂(T) = 2 Σ_{P, h, k} c_q e^{iβλ_q} Σ_ℓ ψ(ℓ/T) V(2πmn/t_ℓ) e(ℓ αλ_q/2π) + E`,
`|E| ≤ (T + 1) Ψ₀ · C(1 + log 3αT)/√(αT/2) · 4N`,

where `q = (P, h, k)`, `m = P₁ + 1`, `n = P₂ + 1`, `h, k ∈ [1, N]`,
`c_q = (mn)^{−1/2} b(h)h^{−1/2} b(k)k^{−1/2}` and `λ_q = log(nk/(mh))`.

**Proof.** The symmetric approximate functional equation gives
`|ζ(½+it)|² = Σ_P (mn)^{−1/2} V(2πmn/t)(e^{it log(n/m)} + e^{−it log(n/m)}) + O(log t/√t)`; the two
halves agree under `m ↔ n`. Multiply by `|M_N|² = Σ_{h,k} b(h)b(k)(hk)^{−1/2}(k/h)^{it}` and exchange
the finite `ℓ`-sum with the absolutely convergent `P`-series;
`e^{it_ℓλ} = e^{iβλ} e(ℓ αλ/2π)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)

/-- `S₂(T) = Σ_ℓ ψ(ℓ/T) |ζ M_N(½ + i(αℓ + β))|²`. -/
def secondMoment (ψ : ℝ → ℝ) (α β : ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  ∑' ℓ : ℤ, ψ (ℓ / T) * ‖apMollZeta N α β ℓ‖ ^ 2

/-- `b(h)/√h`. -/
def mollAmp (N h : ℕ) : ℝ := Sieve.linearMollifierCoeff N h / Real.sqrt h

/-- The quadruple coefficient `c_q = (mn)^{−1/2} b(h)h^{−1/2} b(k)k^{−1/2}`. -/
def quadCoeff (N : ℕ) (P : ℕ × ℕ) (h k : ℕ) : ℝ := pairAmp P * mollAmp N h * mollAmp N k

/-- The quadruple frequency `λ_q = log(n/m) + log(k/h)`. -/
def quadFreq (P : ℕ × ℕ) (h k : ℕ) : ℝ := pairFreq P + (Real.log k - Real.log h)

/-- The quadruple lattice sum `c_q e^{iβλ} Σ_ℓ ψ(ℓ/T) V(2πmn/t_ℓ) e(ℓ αλ/2π)`. -/
def quadTerm (ψ : ℝ → ℝ) (α β : ℝ) (N : ℕ) (T : ℝ) (P : ℕ × ℕ) (h k : ℕ) : ℂ :=
  (quadCoeff N P h k : ℂ) * Complex.exp ((β * quadFreq P h k : ℝ) * I) *
    latticeSum (fun x => (ψ (x / T) : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / (α * x + β)))
      (α * quadFreq P h k / (2 * Real.pi))

/-! ## `|M_N|²` -/

theorem natCast_cpow_neg_critPt {h : ℕ} (hh : 1 ≤ h) (t : ℝ) :
    (h : ℂ) ^ (-critPt t) =
      ((Real.sqrt h)⁻¹ : ℝ) * Complex.exp ((-(t * Real.log h)) * I) := by
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  rw [show (h : ℂ) = ((h : ℝ) : ℂ) by push_cast; rfl, ZetaNotch.ofReal_cpow_eq_exp hpos]
  have hs : (Real.sqrt h)⁻¹ = Real.exp (-(Real.log h / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos, ← Real.exp_neg]
    congr 1; ring
  rw [hs, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold critPt
  push_cast
  ring

theorem linMoll_critPt_eq (N : ℕ) (t : ℝ) :
    linMoll N (critPt t) = ∑ h ∈ Finset.Icc 1 N,
      (mollAmp N h : ℂ) * Complex.exp ((-(t * Real.log h)) * I) := by
  unfold linMoll
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [natCast_cpow_neg_critPt (Finset.mem_Icc.mp hh).1, mollAmp]
  push_cast
  ring

/-- `|M_N(½ + it)|² = Σ_{h,k} b(h)b(k)(hk)^{−1/2} e^{it log(k/h)}`. -/
theorem normSq_linMoll_eq (N : ℕ) (t : ℝ) :
    ((‖linMoll N (critPt t)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ((mollAmp N h * mollAmp N k : ℝ) : ℂ) *
        Complex.exp ((t * (Real.log k - Real.log h) : ℝ) * I) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, linMoll_critPt_eq, map_sum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (-(↑t * ↑(Real.log k)) * I) = (t * Real.log k : ℝ) * I := by
    rw [map_mul, Complex.conj_I, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    ring
  rw [this, mul_mul_mul_comm, ← Complex.exp_add]
  push_cast
  ring_nf

/-! ## The symmetric AFE main term -/

theorem pairAmp_swap (P : ℕ × ℕ) : pairAmp P.swap = pairAmp P := by
  unfold pairAmp; simp only [Prod.fst_swap, Prod.snd_swap]; ring_nf

theorem pairProd_swap (P : ℕ × ℕ) : pairProd P.swap = pairProd P := by
  unfold pairProd; simp only [Prod.fst_swap, Prod.snd_swap]; ring

theorem pairFreq_swap (P : ℕ × ℕ) : pairFreq P.swap = -pairFreq P := by
  unfold pairFreq; simp only [Prod.fst_swap, Prod.snd_swap]; ring

theorem summable_afeHalf {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    Summable (fun P : ℕ × ℕ => (pairAmp P : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
      Complex.exp ((t * (ξ * pairFreq P) : ℝ) * I)) := by
  have hL : 0 < t / (2 * Real.pi) := by positivity
  refine (ZetaNotch.summable_direct_envelope hL).of_norm_bounded fun P => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ZetaNotch.pairAmp_pos P),
    Complex.norm_exp_ofReal_mul_I, mul_one,
    show 2 * Real.pi * pairProd P / t = pairProd P / (t / (2 * Real.pi)) by field_simp]

/-- `A(t) = 2 Σ_P (mn)^{−1/2} V(2πmn/t) e^{it log(n/m)}`. -/
theorem afeMain_eq_two_mul {t : ℝ} (ht : 0 < t) :
    ∑' P : ℕ × ℕ, (pairAmp P : ℂ) * smoothAFECutoff (pairProd P / (t / (2 * Real.pi))) *
        (Complex.exp ((t * pairFreq P : ℝ) * I) + Complex.exp ((t * (-pairFreq P) : ℝ) * I)) =
      2 * ∑' P : ℕ × ℕ, (pairAmp P : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
        Complex.exp ((t * pairFreq P : ℝ) * I) := by
  have hV : ∀ P : ℕ × ℕ, pairProd P / (t / (2 * Real.pi)) = 2 * Real.pi * pairProd P / t :=
    fun P => by field_simp
  have h1 := summable_afeHalf ht 1
  have h2 := summable_afeHalf ht (-1)
  simp only [one_mul, neg_one_mul] at h1 h2
  simp only [hV, mul_add]
  rw [h1.tsum_add h2]
  have hswap : ∑' P : ℕ × ℕ, (pairAmp P : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
      Complex.exp ((t * -pairFreq P : ℝ) * I) =
      ∑' P : ℕ × ℕ, (pairAmp P : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
        Complex.exp ((t * pairFreq P : ℝ) * I) := by
    rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) (fun P : ℕ × ℕ => (pairAmp P : ℂ) *
      smoothAFECutoff (2 * Real.pi * pairProd P / t) * Complex.exp ((t * pairFreq P : ℝ) * I))]
    refine tsum_congr fun P => ?_
    simp only [Equiv.prodComm_apply, pairAmp_swap, pairProd_swap, pairFreq_swap, mul_neg]
  rw [hswap]
  ring

/-- `A(t)|M_N|² = 2 Σ_P Σ_{h,k} c_q V(2πmn/t) e^{itλ_q}`. -/
theorem afeMain_mul_normSq {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑' P : ℕ × ℕ, (pairAmp P : ℂ) * smoothAFECutoff (pairProd P / (t / (2 * Real.pi))) *
        (Complex.exp ((t * pairFreq P : ℝ) * I) + Complex.exp ((t * (-pairFreq P) : ℝ) * I))) *
        ((‖linMoll N (critPt t)‖ ^ 2 : ℝ) : ℂ) =
      2 * ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (quadCoeff N P h k : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
          Complex.exp ((t * quadFreq P h k : ℝ) * I) := by
  rw [afeMain_eq_two_mul ht, normSq_linMoll_eq, mul_assoc, ← tsum_mul_right]
  congr 1
  refine tsum_congr fun P => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold quadCoeff quadFreq
  rw [show (t * (pairFreq P + (Real.log k - Real.log h)) : ℝ) =
      t * pairFreq P + t * (Real.log k - Real.log h) by ring, Complex.ofReal_add, add_mul,
    Complex.exp_add]
  simp only [Complex.ofReal_mul]
  ring

/-! ## Summation over the progression -/

/-- `e^{i(αx+β)λ} = e^{iβλ} e(x αλ/2π)`. -/
theorem cexp_progression (α β lam x : ℝ) :
    Complex.exp (((α * x + β) * lam : ℝ) * I) =
      Complex.exp ((β * lam : ℝ) * I) * unitExp (x * (α * lam / (2 * Real.pi))) := by
  unfold unitExp
  rw [← Complex.exp_add]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

theorem summable_quadPoint {t : ℝ} (ht : 0 < t) (N : ℕ) :
    Summable (fun P : ℕ × ℕ => ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      (quadCoeff N P h k : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / t) *
        Complex.exp ((t * quadFreq P h k : ℝ) * I)) := by
  have hL : 0 < t / (2 * Real.pi) := by positivity
  refine summable_sum fun h _ => summable_sum fun k _ => ?_
  refine ((ZetaNotch.summable_direct_envelope hL).mul_left |mollAmp N h * mollAmp N k|).of_norm_bounded
    fun P => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one, show 2 * Real.pi * pairProd P / t = pairProd P / (t / (2 * Real.pi)) by field_simp]
  unfold quadCoeff
  rw [abs_mul, abs_mul, abs_of_pos (ZetaNotch.pairAmp_pos P), abs_mul (mollAmp N h)]
  apply le_of_eq
  ring

/-- **Summation over the progression.** -/
theorem tsum_ell_quadPoint {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β : ℝ}
    (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β) :
    latticeSum (fun x => (ψ (x / T) : ℂ) * (2 * ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N,
        ∑ k ∈ Finset.Icc 1 N, (quadCoeff N P h k : ℂ) *
          smoothAFECutoff (2 * Real.pi * pairProd P / (α * x + β)) *
          Complex.exp (((α * x + β) * quadFreq P h k : ℝ) * I))) 0 =
      2 * ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        quadTerm ψ α β N T P h k := by
  have hsuppC : Function.support (fun x : ℝ => (ψ x : ℂ)) ⊆ Icc 1 2 := by
    intro x hx; apply hsupp; intro h0; apply hx; simp [h0]
  rw [latticeSum_eq_sum (support_cutoff_subset hsuppC hT _)]
  simp only [mul_zero, unitExp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have hterm : ∀ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, (ψ ((ℓ : ℝ) / T) : ℂ) * (2 * ∑' P : ℕ × ℕ,
      ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, (quadCoeff N P h k : ℂ) *
        smoothAFECutoff (2 * Real.pi * pairProd P / (α * ℓ + β)) *
        Complex.exp (((α * ℓ + β) * quadFreq P h k : ℝ) * I)) =
      2 * ∑' P : ℕ × ℕ, (ψ ((ℓ : ℝ) / T) : ℂ) * ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (quadCoeff N P h k : ℂ) * smoothAFECutoff (2 * Real.pi * pairProd P / (α * ℓ + β)) *
        Complex.exp (((α * ℓ + β) * quadFreq P h k : ℝ) * I) := by
    intro ℓ _
    rw [tsum_mul_left]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Summable.tsum_finsetSum]
  · congr 1
    refine tsum_congr fun P => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold quadTerm
    rw [latticeSum_eq_sum (support_cutoff_subset hsuppC hT _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [cexp_progression]
    ring
  · intro ℓ _
    by_cases h0 : ψ ((ℓ : ℝ) / T) = 0
    · simp only [h0, Complex.ofReal_zero, zero_mul]; exact summable_zero
    · exact (summable_quadPoint (hpos ℓ h0) N).mul_left _

/-! ## The expansion -/

theorem latticeSum_sub {f g : ℝ → ℂ} {A B : ℝ} (hf : Function.support f ⊆ Icc A B)
    (hg : Function.support g ⊆ Icc A B) (u : ℝ) :
    latticeSum f u - latticeSum g u = latticeSum (fun x => f x - g x) u := by
  unfold latticeSum
  rw [← (summable_lattice hf u).tsum_sub (summable_lattice hg u)]
  refine tsum_congr fun ℓ => ?_
  ring

/-- **The quadruple expansion of the second moment.** -/
theorem norm_secondMoment_sub_expansion_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ψ : ℝ → ℝ}, Function.support ψ ⊆ Icc 1 2 → ∀ {Ψ₀ : ℝ},
      (∀ y, |ψ y| ≤ Ψ₀) → ∀ {α β : ℝ} (N : ℕ) {T : ℝ}, 0 < α → 2 * |β| ≤ α * T →
      32 ≤ α * T →
      ‖(secondMoment ψ α β N T : ℂ) - 2 * ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 N, quadTerm ψ α β N T P h k‖ ≤
        (T + 1) * (Ψ₀ * (C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) * (4 * N))) := by
  obtain ⟨C, hC0, hAFE⟩ := ZetaNotch.exists_norm_zetaSq_sub_symmetricAFE_le
  refine ⟨C, hC0, fun {ψ} hsupp {Ψ₀} hΨ {α β} N {T} hα hβ hαT => ?_⟩
  have hT : 0 < T := by
    by_contra h; push Not at h; nlinarith
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  set A : ℝ → ℂ := fun t => ∑' P : ℕ × ℕ, (pairAmp P : ℂ) *
    smoothAFECutoff (pairProd P / (t / (2 * Real.pi))) *
      (Complex.exp ((t * pairFreq P : ℝ) * I) + Complex.exp ((t * (-pairFreq P) : ℝ) * I))
    with hA
  have hsuppC : Function.support (fun x : ℝ => (ψ x : ℂ)) ⊆ Icc 1 2 := by
    intro x hx; apply hsupp; intro h0; apply hx; simp [h0]
  have hrange : ∀ x : ℝ, ψ (x / T) ≠ 0 → α * T / 2 ≤ α * x + β ∧ α * x + β ≤ 3 * α * T := by
    intro x hx
    obtain ⟨h1, h2⟩ := hsupp hx
    rw [le_div_iff₀ hT] at h1
    rw [div_le_iff₀ hT] at h2
    constructor
    · have := neg_abs_le β; nlinarith
    · have := le_abs_self β; nlinarith
  have hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β := fun x hx => by
    have := (hrange x hx).1; nlinarith
  have hS : (secondMoment ψ α β N T : ℂ) = latticeSum (fun x => (ψ (x / T) : ℂ) *
      (ZetaNotch.zetaSq (α * x + β) * ((‖linMoll N (critPt (α * x + β))‖ ^ 2 : ℝ) : ℂ))) 0 := by
    unfold secondMoment latticeSum
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun ℓ => ?_
    simp only [mul_zero, unitExp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [ZetaNotch.zetaSq_eq_normSq]
    unfold apMollZeta
    rw [norm_mul, mul_pow]
    push_cast
    rfl
  have hM : 2 * ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
      quadTerm ψ α β N T P h k = latticeSum (fun x => (ψ (x / T) : ℂ) *
        (A (α * x + β) * ((‖linMoll N (critPt (α * x + β))‖ ^ 2 : ℝ) : ℂ))) 0 := by
    rw [← tsum_ell_quadPoint hsupp N hT hpos]
    congr 1
    funext x
    by_cases h0 : ψ (x / T) = 0
    · simp [h0]
    · rw [hA, afeMain_mul_normSq (hpos x h0) N]
  rw [hS, hM, latticeSum_sub (support_cutoff_subset hsuppC hT _) (support_cutoff_subset hsuppC hT _)]
  have hbd := norm_latticeSum_le_of_bound (A := T) (B := 2 * T)
    (M := Ψ₀ * (C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) * (4 * N))) (by linarith)
    (support_cutoff_subset hsuppC hT (fun x => ZetaNotch.zetaSq (α * x + β) *
        ((‖linMoll N (critPt (α * x + β))‖ ^ 2 : ℝ) : ℂ) -
      A (α * x + β) * ((‖linMoll N (critPt (α * x + β))‖ ^ 2 : ℝ) : ℂ))) (fun x => ?_) 0
  · refine (le_of_eq_of_le ?_ hbd).trans (le_of_eq (by ring))
    congr 2
    funext x
    ring
  have hlog3 : 0 ≤ 1 + Real.log (3 * α * T) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * α * T by linarith); linarith
  by_cases h0 : ψ (x / T) = 0
  · simp only [h0, Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg hΨ0 (mul_nonneg (div_nonneg (mul_nonneg hC0 hlog3) (Real.sqrt_nonneg _))
      (by positivity))
  obtain ⟨ht1, ht2⟩ := hrange x h0
  set t := α * x + β with ht
  have ht16 : 16 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hz := hAFE t ht16
  have hMb := norm_linMoll_critPt_le N t
  have hM2 : ‖linMoll N (critPt t)‖ ^ 2 ≤ 4 * N := by
    calc ‖linMoll N (critPt t)‖ ^ 2 ≤ (2 * Real.sqrt N) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hMb 2
      _ = 4 * N := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; ring
  have herr : C * (1 + Real.log t) / Real.sqrt t ≤
      C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) := by
    have hlog : Real.log t ≤ Real.log (3 * α * T) := Real.log_le_log ht0 ht2
    have hsq : Real.sqrt (α * T / 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt ht1
    have hsq0 : 0 < Real.sqrt (α * T / 2) := Real.sqrt_pos.mpr (by positivity)
    have hlog0 : 0 ≤ 1 + Real.log t := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t); linarith
    calc C * (1 + Real.log t) / Real.sqrt t ≤ C * (1 + Real.log t) / Real.sqrt (α * T / 2) :=
          div_le_div_of_nonneg_left (by positivity) hsq0 hsq
      _ ≤ C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) := by gcongr
  rw [← sub_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg (linMoll N (critPt t))) 2)]
  have hzt : ‖ZetaNotch.zetaSq t - A t‖ ≤
      C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) := hz.trans herr
  calc |ψ (x / T)| * (‖ZetaNotch.zetaSq t - A t‖ * ‖linMoll N (critPt t)‖ ^ 2)
      ≤ Ψ₀ * (C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) * (4 * N)) := by
        gcongr
        exact hΨ _

end

end RHTower.VerticalAP
