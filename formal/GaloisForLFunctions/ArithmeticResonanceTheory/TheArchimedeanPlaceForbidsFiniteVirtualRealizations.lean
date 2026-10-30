import GaloisForLFunctions.ArithmeticResonanceTheory.EvenRealizationsHaveNoZeros
import GaloisForLFunctions.ArithmeticResonanceTheory.TheAmplifierLaw

/-!
# The archimedean place forbids finite virtual realizations

Zeros of a dynamical zeta function come from an *odd* part: a **virtual realization** is a pair of
finite weighted graphs with `Z(s) = det(1 − M⁻(s)) / det(1 − M⁺(s))`. Over `𝔽_q` every curve zeta
is one, with odd part `H¹` and lengths `k log q`; its zeros sit on vertical lines.

Both determinants are **exponential polynomials** `Σ_j c_j e^{−λ_j s}` with real frequencies
(`IsExpPoly`, closed under sums and products; `isExpPoly_det_one_sub_graphMatrix`). Along a real
arithmetic progression `s₀ + h k` such a function is a finite exponential sum in `k` with distinct
positive bases `e^{−λh}`, so by rate = depth it vanishes on the progression only if it vanishes
identically (`eq_zero_of_vanish_on_progression`).

**Theorem** (`riemannZeta_ne_virtualRealization`). `ζ` is not a finite virtual realization:
`(s − 1)ζ(s) det(1 − M⁺(s)) = (s − 1) det(1 − M⁻(s))` would hold on `ℂ`, the trivial zeros
`ζ(−2(k + 1)) = 0` would force the odd determinant to vanish on a progression, hence identically,
and then the even determinant would vanish on `Re s > 1`, against `Z⁺ · det(1 − M⁺) = 1`.

The obstruction is the archimedean place: the Gamma factor puts zeros on a real progression, which
no finite-dimensional odd part can carry. A realization of `ζ` needs an infinite-rank odd part.
-/

open Matrix Finset Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-! ## Exponential polynomials -/

/-- An **exponential polynomial** `s ↦ Σ_{j < N} c_j e^{−λ_j s}` with real frequencies. -/
def IsExpPoly (f : ℂ → ℂ) : Prop :=
  ∃ (N : ℕ) (c : Fin N → ℂ) (lf : Fin N → ℝ),
    ∀ s, f s = ∑ j, c j * Complex.exp (-((lf j : ℂ) * s))

theorem isExpPoly_const (a : ℂ) : IsExpPoly fun _ => a :=
  ⟨1, fun _ => a, fun _ => 0, fun s => by simp⟩

theorem isExpPoly_exp (c : ℂ) (l0 : ℝ) : IsExpPoly fun s => c * Complex.exp (-((l0 : ℂ) * s)) :=
  ⟨1, fun _ => c, fun _ => l0, fun s => by simp⟩

theorem IsExpPoly.add {f g : ℂ → ℂ} (hf : IsExpPoly f) (hg : IsExpPoly g) :
    IsExpPoly fun s => f s + g s := by
  obtain ⟨N, c, l, hf⟩ := hf
  obtain ⟨M, d, m, hg⟩ := hg
  refine ⟨N + M, Fin.append c d, Fin.append l m, fun s => ?_⟩
  show f s + g s = _
  rw [hf, hg, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem IsExpPoly.mul {f g : ℂ → ℂ} (hf : IsExpPoly f) (hg : IsExpPoly g) :
    IsExpPoly fun s => f s * g s := by
  obtain ⟨N, c, l, hf⟩ := hf
  obtain ⟨M, d, m, hg⟩ := hg
  refine ⟨N * M, fun j => c (finProdFinEquiv.symm j).1 * d (finProdFinEquiv.symm j).2,
    fun j => l (finProdFinEquiv.symm j).1 + m (finProdFinEquiv.symm j).2, fun s => ?_⟩
  show f s * g s = _
  dsimp only
  rw [hf, hg, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ,
    ← (finProdFinEquiv.symm.sum_comp (fun q : Fin N × Fin M =>
      c q.1 * Complex.exp (-((l q.1 : ℂ) * s)) * (d q.2 * Complex.exp (-((m q.2 : ℂ) * s)))))]
  · refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [show -(((l (finProdFinEquiv.symm j).1 : ℂ) + (m (finProdFinEquiv.symm j).2 : ℂ)) * s) =
      -((l (finProdFinEquiv.symm j).1 : ℂ) * s) + -((m (finProdFinEquiv.symm j).2 : ℂ) * s) by ring,
      Complex.exp_add]
    ring

theorem IsExpPoly.neg {f : ℂ → ℂ} (hf : IsExpPoly f) : IsExpPoly fun s => -f s := by
  simpa using (isExpPoly_const (-1)).mul hf

theorem IsExpPoly.sub {f g : ℂ → ℂ} (hf : IsExpPoly f) (hg : IsExpPoly g) :
    IsExpPoly fun s => f s - g s := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem isExpPoly_sum {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, IsExpPoly (f i)) :
    IsExpPoly fun s => ∑ i ∈ t, f i s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isExpPoly_const 0
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isExpPoly_prod {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ t, IsExpPoly (f i)) :
    IsExpPoly fun s => ∏ i ∈ t, f i s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isExpPoly_const 1
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The determinant `det(1 − M(s))` of a finite weighted graph is an exponential polynomial. -/
theorem isExpPoly_det_one_sub_graphMatrix {n : ℕ} {E : Type*} [Fintype E] (src tgt : E → Fin n)
    (r : E → ℝ) (c : E → ℂ) : IsExpPoly fun s => (1 - graphMatrix src tgt r c s).det := by
  have hentry : ∀ i j : Fin n, IsExpPoly fun s => (1 - graphMatrix src tgt r c s) i j := by
    intro i j
    simp only [Matrix.sub_apply, graphMatrix]
    refine (isExpPoly_const _).sub (isExpPoly_sum _ fun e _ => ?_)
    split_ifs
    · simpa [mul_comm] using isExpPoly_exp (c e) (r e)
    · exact isExpPoly_const 0
  simp_rw [Matrix.det_apply']
  refine isExpPoly_sum _ fun σ _ => (isExpPoly_const _).mul (isExpPoly_prod _ fun i _ => hentry _ _)

/-- **No exponential polynomial vanishes on a real progression unless it vanishes.** If
`f(s₀ + h(k + 1)) = 0` for every `k`, with `h ≠ 0` real, then `f = 0`. -/
theorem eq_zero_of_vanish_on_progression {f : ℂ → ℂ} (hf : IsExpPoly f) (s₀ : ℂ) {h : ℝ}
    (hh : h ≠ 0) (hv : ∀ k : ℕ, f (s₀ + h * (k + 1)) = 0) : ∀ s, f s = 0 := by
  classical
  obtain ⟨N, c, l, hf⟩ := hf
  -- group the terms by frequency
  set S : Finset ℝ := Finset.univ.image l with hS
  set C : ℝ → ℂ := fun μ => ∑ j with l j = μ, c j with hC
  have hgroup : ∀ s, f s = ∑ μ ∈ S, C μ * Complex.exp (-((μ : ℂ) * s)) := by
    intro s
    rw [hf, hS, Finset.sum_image']
    intro j _
    simp only [hC, Finset.sum_mul]
    refine Finset.sum_congr ?_ fun i hi => ?_
    · ext i; simp
    · rw [(Finset.mem_filter.mp hi).2]
  -- along the progression the grouped sum is an exponential sum with distinct bases `e^{−μh}`
  set α : ℝ → ℂ := fun μ => ((Real.exp (-(μ * h)) : ℝ) : ℂ) with hα
  set d : ℝ → ℂ := fun μ => C μ * Complex.exp (-((μ : ℂ) * s₀)) with hd
  have hinj : Set.InjOn α S := fun μ _ ν _ hμν => by
    have h1 : Real.exp (-(μ * h)) = Real.exp (-(ν * h)) := Complex.ofReal_injective hμν
    have h2 := Real.exp_injective h1
    have : (μ - ν) * h = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hh)
  have hseq : ∀ k : ℕ, ∑ μ ∈ S, d μ * α μ ^ (k + 1) = 0 := by
    intro k
    rw [← hv k, hgroup]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [hd, hα, mul_assoc]
    congr 1
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hzero : ∀ μ ∈ S, d μ = 0 := by
    intro μ hμ
    by_contra hne
    have hle := norm_le_of_eventually_norm_le S d α hinj (K := 0) (R := 0) le_rfl
      ((eventually_ge_atTop 1).mono fun k hk => by
        obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        rw [hseq k]; simp) μ hμ hne
    have hpos : 0 < ‖α μ‖ := by simp [hα]
    linarith
  intro s
  rw [hgroup]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hCμ : C μ = 0 := by
    have := hzero μ hμ
    simp only [hd, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
    exact this
  rw [hCμ, zero_mul]

/-! ## No finite virtual realization of `ζ` -/

/-- **`ζ` is not a finite virtual realization.** There are no finite weighted graphs `G⁺` (positive
lengths) and `G⁻` (any real lengths) with `ζ(s) · det(1 − M⁺(s)) = det(1 − M⁻(s))` on a right
half-plane. -/
theorem riemannZeta_ne_virtualRealization {n m : ℕ} {E F : Type*} [Fintype E] [Fintype F]
    (src tgt : E → Fin n) {r : E → ℝ} (hr : ∀ e, 0 < r e) (c : E → ℂ)
    (src' tgt' : F → Fin m) (r' : F → ℝ) (c' : F → ℂ) :
    ¬ ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      riemannZeta s * (1 - graphMatrix src tgt r c s).det =
        (1 - graphMatrix src' tgt' r' c' s).det := by
  rintro ⟨σ₀, hσ₀⟩
  set Dp : ℂ → ℂ := fun s => (1 - graphMatrix src tgt r c s).det with hDp
  set Dm : ℂ → ℂ := fun s => (1 - graphMatrix src' tgt' r' c' s).det with hDm
  set σ₂ : ℝ := max σ₀ 1 with hσ₂
  -- `(s − 1)ζ(s) D⁺(s) = (s − 1) D⁻(s)` on `ℂ`
  have hright : ∀ s : ℂ, σ₂ < s.re → RHTower.zetaResidueFactor s * Dp s = (s - 1) * Dm s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; linarith [le_max_right σ₀ 1]
    rw [RHTower.zetaResidueFactor_of_ne hs1, mul_assoc, hσ₀ s (lt_of_le_of_lt (le_max_left _ _) hs)]
  have hL : Differentiable ℂ fun s => RHTower.zetaResidueFactor s * Dp s :=
    RHTower.differentiable_zetaResidueFactor.mul (differentiable_det_one_sub_graphMatrix src tgt r c)
  have hR : Differentiable ℂ fun s => (s - 1) * Dm s :=
    (by fun_prop : Differentiable ℂ fun s : ℂ => s - 1).mul
      (differentiable_det_one_sub_graphMatrix src' tgt' r' c')
  set z₀ : ℂ := ((σ₂ + 1 : ℝ) : ℂ) with hz₀
  have hev : (fun s => RHTower.zetaResidueFactor s * Dp s) =ᶠ[𝓝 z₀] fun s => (s - 1) * Dm s := by
    have hopen : IsOpen {s : ℂ | σ₂ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show σ₂ < z₀.re by simp [hz₀])] with s hs
    exact hright s hs
  have heq : ∀ s, RHTower.zetaResidueFactor s * Dp s = (s - 1) * Dm s := fun s =>
    (hL.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (hR.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ z₀) hev
      (Set.mem_univ s)
  -- the trivial zeros force `D⁻ = 0` on a progression, hence identically
  have hDm0 : ∀ s, Dm s = 0 := by
    refine eq_zero_of_vanish_on_progression (isExpPoly_det_one_sub_graphMatrix src' tgt' r' c') 0
      (h := -2) (by norm_num) fun k => ?_
    have hs : (0 : ℂ) + ((-2 : ℝ) : ℂ) * ((k : ℂ) + 1) = -2 * ((k : ℂ) + 1) := by push_cast; ring
    have hne : (-2 * ((k : ℂ) + 1)) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h := heq (-2 * ((k : ℂ) + 1))
    rw [RHTower.zetaResidueFactor_of_ne hne, riemannZeta_neg_two_mul_nat_add_one, mul_zero,
      zero_mul] at h
    rw [hs]
    have hne' : (-2 * ((k : ℂ) + 1)) - 1 ≠ 0 := sub_ne_zero.mpr hne
    exact (mul_eq_zero.mp h.symm).resolve_left hne'
  -- then `D⁺` vanishes on `Re s > max σ₀ 1`, against `Z⁺ · D⁺ = 1` far to the right
  obtain ⟨σ₁, hσ₁⟩ := graphZeta_mul_det_eq_one src tgt hr c
  set s : ℂ := ((max σ₂ σ₁ + 1 : ℝ) : ℂ) with hsdef
  have hsre : s.re = max σ₂ σ₁ + 1 := by simp [hsdef]
  have hs₂ : σ₂ < s.re := by rw [hsre]; linarith [le_max_left σ₂ σ₁]
  have hs₁ : σ₁ < s.re := by rw [hsre]; linarith [le_max_right σ₂ σ₁]
  have hζ : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (lt_of_le_of_lt (le_max_right σ₀ 1) hs₂)
  have hDp : Dp s = 0 := by
    have h := hσ₀ s (lt_of_le_of_lt (le_max_left σ₀ 1) hs₂)
    rw [show (1 - graphMatrix src' tgt' r' c' s).det = Dm s from rfl, hDm0 s] at h
    exact (mul_eq_zero.mp h).resolve_left hζ
  have h1 := hσ₁ s hs₁
  rw [show (1 - graphMatrix src tgt r c s).det = Dp s from rfl, hDp, mul_zero] at h1
  exact zero_ne_one h1

end GaloisForLFunctions.ArithmeticResonanceTheory
