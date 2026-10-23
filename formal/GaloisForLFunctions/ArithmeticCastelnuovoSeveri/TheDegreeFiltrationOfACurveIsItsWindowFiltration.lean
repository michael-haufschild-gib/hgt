import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair

/-!
# The degree filtration of a curve is its window filtration

Over `ℚ` no degree certifies the Hodge index for all configurations (`exists_hidden_at_degree`);
over `𝔽_q` the Frobenius window `2g` does. This file makes the second statement exact on the scaling
surface of the curve: the Hodge defect at degree `a` is decided by **one** Frobenius window,

    hodgeDefectAt (curveConfig) a = 0   if the window ⌈2a/log q⌉ is positive semidefinite,
                                   = ∞   otherwise                      (`hodgeDefectAt_curveConfig`).

* **Below the threshold** (`re_W_curveConfig_nonneg_of_window`). By the explicit formula
  (`W_curveConfig`), `W(f, f) = log q Σ_m t_{|m|} ∫ f(u) conj f(u − m log q) du`. Cutting the line into
  cells of length `log q` (`integral_eq_sum_cells`), this is `log q ∫_0^{log q} ⟨T F(s), F(s)⟩ ds`,
  where `F(s) = (f(s + j log q))_j` and `T` is the Toeplitz matrix of the traces. A test supported in
  `[−a, a]` has at most `⌈2a/log q⌉` consecutive nonzero coordinates in each cell
  (`window_of_support`), so the integrand is a value of the window Gram matrix.
* **Above the threshold** (`top_le_hodgeDefectAt_curveConfig`). A negative vector `v` of the window
  gives tests `Σ_j v_j g_b(· − j log q)` built on narrow bumps `g_b` with disjoint offsets; distinct
  offsets do not interact (`W_curveConfig_offsets_eq_zero`), each test has square
  `log q ‖g‖² v* T v < 0`, so the defect exceeds every integer.

So the scaling surface of a curve sees its outer eigenvalues from the degree
`(n₀ − 1) log q / 2` on, `n₀` the first window with a negative square, and then sees each of them
infinitely often (the defect jumps from `0` to `∞`, as Kronecker rank one predicts). For the golden
fake curve the jump is at `log 5 / 2` (`goldenDatum_hodgeDefectAt`).
-/

open Complex MeasureTheory Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Translation invariance and cells -/

/-- **Weil's form is invariant under the scaling flow.** -/
theorem ZeroConfig_W_translate (Z : ZeroConfig) (c : ℝ) (f g : ℝ → ℂ) :
    Z.W (translate c f) (translate c g) = Z.W f g := by
  simp only [ZeroConfig.W, ZeroConfig.Wsummand, paperFT_translate]
  refine tsum_congr fun τ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have h : cexp (I * gammaOf τ * c) * cexp (conj (I * conj (gammaOf τ) * c)) = 1 := by
    rw [← Complex.exp_add]
    simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    rw [show I * gammaOf τ * c + -I * gammaOf τ * c = 0 by ring, Complex.exp_zero]
  linear_combination ((Z.mult τ : ℂ) * paperFT f (gammaOf ↑τ) *
    conj (paperFT g (conj (gammaOf ↑τ)))) * h

theorem translate_translate (a b : ℝ) (g : ℝ → ℂ) :
    translate a (translate b g) = translate (a + b) g := by
  funext u
  simp only [translate]
  congr 1
  ring

/-- A continuous function with `tsupport ⊆ [−a, a]` vanishes off the open interval. -/
theorem mem_Ioo_of_ne_zero {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (hfs : tsupport f ⊆ Set.Icc (-a) a) {u : ℝ} (hu : f u ≠ 0) : -a < u ∧ u < a := by
  have hmem : ∀ v, f v ≠ 0 → v ∈ Set.Icc (-a) a := fun v hv => hfs (subset_tsupport _ hv)
  have hopen : IsOpen {v | f v ≠ 0} := isOpen_ne_fun hf continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen u hu
  have h1 := hmem (u + ε / 2) (hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos] <;> linarith))
  have h2 := hmem (u - ε / 2) (hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]; linarith))
  exact ⟨by linarith [h2.1], by linarith [h1.2]⟩

/-- **Cell decomposition.** If `h` is continuous and vanishes outside `[−N L, N L]`, then
`∫ h = Σ_{k < 2N} ∫_0^L h(s + (k − N) L) ds`. -/
theorem integral_eq_sum_cells {h : ℝ → ℂ} (hh : Continuous h) {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hsupp : ∀ u, h u ≠ 0 → -(N * L) ≤ u ∧ u ≤ N * L) :
    ∫ u, h u = ∑ k ∈ range (2 * N), ∫ s in (0 : ℝ)..L, h (s + ((k : ℝ) - N) * L) := by
  have hNL : -(N * L) ≤ N * L := by nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have h1 : ∫ u, h u = ∫ u in -(N * L)..(N * L), h u := by
    rw [intervalIntegral.integral_of_le hNL, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    by_contra hne
    exact hu ⟨(hsupp u hne).1, (hsupp u hne).2⟩
  rw [h1]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := h)
    (a := fun k : ℕ => ((k : ℝ) - N) * L) (n := 2 * N)
    (fun k _ => hh.intervalIntegrable _ _)
  simp only at hadj
  rw [show (((2 * N : ℕ) : ℝ) - N) * L = N * L by push_cast; ring,
    show (((0 : ℕ) : ℝ) - N) * L = -(N * L) by push_cast; ring] at hadj
  rw [← hadj]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_comp_add_right h (((k : ℝ) - N) * L)]
  congr 1
  · ring
  · push_cast; ring

/-! ### The window of a cell -/

/-- A test supported in `[−a, a]` has at most `⌈2a/L⌉` consecutive nonzero coordinates
`f(s + jL)` in each cell. -/
theorem window_of_support {f : ℝ → ℂ} (hf : Continuous f) {a L : ℝ} (hL : 0 < L)
    (hfs : tsupport f ⊆ Set.Icc (-a) a) (s : ℝ) {j j' : ℤ} (hj : f (s + j * L) ≠ 0)
    (hj' : f (s + j' * L) ≠ 0) : j' - j < ⌈2 * a / L⌉₊ := by
  have h1 := mem_Ioo_of_ne_zero hf hfs hj
  have h2 := mem_Ioo_of_ne_zero hf hfs hj'
  have hlt : ((j' - j : ℤ) : ℝ) < 2 * a / L := by
    rw [lt_div_iff₀ hL]; push_cast; nlinarith
  have hceil : 2 * a / L ≤ (⌈2 * a / L⌉₊ : ℝ) := Nat.le_ceil _
  exact_mod_cast hlt.trans_le hceil

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- The Toeplitz form of a finitely supported coordinate vector is a window value: if the nonzero
coordinates of `F` lie in a window of length `n` and the window Gram matrix is positive
semidefinite, the form is nonnegative. -/
theorem re_toeplitz_nonneg_of_window (S : Finset ℤ) (F : ℤ → ℂ) {n : ℕ}
    (hwin : ∀ j ∈ S, ∀ j' ∈ S, F j ≠ 0 → F j' ≠ 0 → j' - j < n)
    (hpsd : ∀ x : Fin n → ℂ, 0 ≤ hermQuad (D.spanGram n) x) :
    0 ≤ (∑ j ∈ S, ∑ k ∈ S, (D.trace (j - k).natAbs : ℂ) * F j * conj (F k)).re := by
  classical
  set J := S.filter fun j => F j ≠ 0
  rcases J.eq_empty_or_nonempty with hJ | hJ
  · have h0 : ∀ j ∈ S, F j = 0 := fun j hj => by
      by_contra h
      have : j ∈ J := Finset.mem_filter.mpr ⟨hj, h⟩
      rw [hJ] at this
      exact absurd this (Finset.notMem_empty _)
    rw [Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k _ => by rw [h0 j hj]; ring]
    simp
  set j₀ := J.min' hJ
  have hj₀ := J.min'_mem hJ
  -- the coordinates live on the window `j₀, …, j₀ + n − 1`
  set G : Fin n → ℂ := fun b => if (j₀ + b : ℤ) ∈ S then F (j₀ + b) else 0
  have hsupp : ∀ j ∈ S, F j ≠ 0 → ∃ b : Fin n, (j₀ + b : ℤ) = j := by
    intro j hj hFj
    have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨hj, hFj⟩
    have hge : j₀ ≤ j := J.min'_le j hjJ
    have hlt := hwin _ (Finset.mem_filter.mp hj₀).1 j hj (Finset.mem_filter.mp hj₀).2 hFj
    refine ⟨⟨(j - j₀).toNat, by omega⟩, ?_⟩
    simp only
    omega
  have hreindex : ∀ (T : ℤ → ℤ → ℂ), (∀ j k, F j = 0 → T j k = 0) → (∀ j k, F k = 0 → T j k = 0) →
      ∑ j ∈ S, ∑ k ∈ S, T j k = ∑ b : Fin n, ∑ c : Fin n,
        (if (j₀ + b : ℤ) ∈ S ∧ (j₀ + c : ℤ) ∈ S then T (j₀ + b) (j₀ + c) else 0) := by
    intro T hT1 hT2
    have hinj : Function.Injective (fun b : Fin n => (j₀ + b : ℤ)) := fun b c h => by
      simp only [add_right_inj, Nat.cast_inj] at h; exact Fin.ext h
    have hS : ∀ (U : ℤ → ℂ), (∀ j, F j = 0 → U j = 0) →
        ∑ j ∈ S, U j = ∑ b : Fin n, (if (j₀ + b : ℤ) ∈ S then U (j₀ + b) else 0) := by
      intro U hU
      rw [← Finset.sum_filter_add_sum_filter_not S fun j => F j ≠ 0,
        Finset.sum_eq_zero (s := S.filter fun j => ¬F j ≠ 0) fun j hj => hU j (by
          simpa using (Finset.mem_filter.mp hj).2), add_zero]
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
        fun b => (j₀ + b : ℤ) ∈ S ∧ F (j₀ + b) ≠ 0]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter fun b : Fin n =>
          ¬((j₀ + b : ℤ) ∈ S ∧ F (j₀ + b) ≠ 0)) fun b hb => by
        have hb' := (Finset.mem_filter.mp hb).2
        split_ifs with h1
        · exact hU _ (by by_contra h2; exact hb' ⟨h1, h2⟩)
        · rfl, add_zero]
      refine Finset.sum_bij_ne_zero (fun j hj _ => ⟨(j - j₀).toNat, ?_⟩) ?_ ?_ ?_ ?_
      · obtain ⟨b, hb⟩ := hsupp j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
        have := b.2; omega
      · intro j hj _
        obtain ⟨b, hb⟩ := hsupp j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hj' : (j₀ + ((j - j₀).toNat : ℕ) : ℤ) = j := by
          have := b.2; omega
        simp only [hj']
        exact ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
      · intro j hj _ j' hj' _ h
        have hb := hsupp j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
        have hb' := hsupp j' (Finset.mem_filter.mp hj').1 (Finset.mem_filter.mp hj').2
        obtain ⟨b, hb⟩ := hb; obtain ⟨b', hb'⟩ := hb'
        have h1 := congrArg Fin.val h
        simp only at h1
        omega
      · intro b hb hne
        have hb' := (Finset.mem_filter.mp hb).2
        refine ⟨(j₀ + b : ℤ), Finset.mem_filter.mpr hb', hne ?_, ?_⟩
        · rw [if_pos hb'.1] at hne ⊢; exact fun h => hne h
        · ext; simp
      · intro j hj _
        have hb := hsupp j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
        obtain ⟨b, hb⟩ := hb
        have hj' : (j₀ + ((j - j₀).toNat : ℕ) : ℤ) = j := by have := b.2; omega
        simp only [hj', if_pos (Finset.mem_filter.mp hj).1]
    rw [hS (fun j => ∑ k ∈ S, T j k) (fun j hj => Finset.sum_eq_zero fun k _ => hT1 j k hj)]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hb
    · rw [hS (fun k => T (j₀ + b) k) (fun k hk => hT2 _ k hk)]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : (j₀ + c : ℤ) ∈ S
      · rw [if_pos hc, if_pos ⟨hb, hc⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.2)]
    · exact (Finset.sum_eq_zero fun c _ => by rw [if_neg (fun h => hb h.1)]).symm
  rw [hreindex _ (fun j k h => by rw [h]; ring) (fun j k h => by rw [h]; simp)]
  have hq := hpsd (fun b => conj (G b))
  simp only [hermQuad, dotProduct, Matrix.mulVec, spanGram, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj] at hq
  convert hq using 2
  rw [Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  have hd : ((j₀ + b : ℤ) - (j₀ + c)).natAbs = Nat.dist b c := by
    rw [show ((j₀ + b : ℤ) - (j₀ + c)) = (b : ℤ) - c by ring]
    exact natAbs_sub_eq_dist _ _
  simp only [G]
  by_cases hb : (j₀ + b : ℤ) ∈ S <;> by_cases hc : (j₀ + c : ℤ) ∈ S <;>
    simp [hb, hc, hd] <;> ring

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
