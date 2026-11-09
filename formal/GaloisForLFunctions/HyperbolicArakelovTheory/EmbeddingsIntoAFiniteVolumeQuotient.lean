import GaloisForLFunctions.HyperbolicArakelovTheory.EmbeddingsIntoACompactQuotient

/-!
# Embeddings of the degrees into a finite-volume quotient

B118′.1 asks whether some lattice `Γ ⊂ SL₂(ℂ)` and some embedding `n ↦ w_n` of the degrees into
`Γ\ℍ³` reproduce the normalized Frobenius intersection through an automorphic Green function at
`s = ½`. For a lattice the Poincaré series of `G_{1/2}` diverges, so every candidate is a fundamental
solution of `Δ − 3/4` chosen by a growth condition in the cusps (the `L²` resolvent, the continued
Poincaré series of `SurfaceOfSpecZ`). Two classical properties of such a kernel are used:
* `IsNewtonian`: it is unbounded above as two distinct points merge;
* `CuspExpansion`: in a cusp `Λ\{t > T₀}` with height `t`, Fourier expansion in the horizontal
  variables leaves, up to `K`-Bessel modes that decay in the height, the zero mode, which solves
  `t²Z'' − tZ' + ¾Z = 0` in each variable (solutions `t^{½}`, `t^{3/2}`). For `x` at height `t` and `y`
  higher in the same cusp, `K(x, y) ≈ A(x)u^{½} + B(x)u^{3/2}` as `u = ht y → ∞`, with
  `A(x) ≈ a₁t^{½} + a₂t^{3/2}` and `B(x) ≈ b₁t^{½} + b₂t^{3/2}` as `t → ∞`. The jump of the Green
  function across `t = u` is the Wronskian `b₁ − a₂ = −1/|Λ|`; only `b₁ ≠ a₂` is used.

**Theorem** (`not_eq_frobenius_of_finiteVolume`). Let `Y` carry a proper height (compact sublevel sets)
and finitely many cusps, and let `K` be Newtonian with a cusp expansion in every cusp. No injective
embedding of the degrees reproduces `2πG_{1/2}(|log(n/m)|) + κΛ(n/m)(n/m)^{−1/2}`.

**Mechanism.** If infinitely many degrees stay at bounded height they cluster, and
`not_eq_frobenius_of_mapClusterPt` applies. Otherwise the heights tend to `∞` and infinitely many
degrees `y_j = w_{φ(j)}` lie in one cusp. For fixed `j`, the target is bounded on the pairs
`(φ(j), φ(k))`, `φ(k) ≥ 2φ(j)`, so `A(y_j)u^{½} + B(y_j)u^{3/2}` is bounded as `u → ∞`, which forces
`A(y_j) = B(y_j) = 0` (`eq_zero_of_bounded_zeroMode`). Letting `j → ∞` then forces
`a₁ = a₂ = b₁ = b₂ = 0`, against the Wronskian.
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-- `αu^{½} + βu^{3/2}` stays bounded along `u_n → ∞` only if `α = β = 0`. -/
theorem eq_zero_of_bounded_zeroMode {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {α β C : ℝ}
    (hb : ∀ᶠ n in atTop, |α * Real.sqrt (u n) + β * (u n * Real.sqrt (u n))| ≤ C) :
    α = 0 ∧ β = 0 := by
  have hβ : β = 0 := by
    by_contra hβ
    have hβ0 : 0 < |β| := abs_pos.mpr hβ
    obtain ⟨n, hn, hu1, hu2⟩ := (hb.and ((hu.eventually_ge_atTop 1).and
      (hu.eventually_ge_atTop ((|α| + |C| + 1) / |β|)))).exists
    have hs1 : 1 ≤ Real.sqrt (u n) := Real.one_le_sqrt.mpr hu1
    have h1 : |α| + |C| + 1 ≤ |β| * u n := by rwa [div_le_iff₀ hβ0, mul_comm] at hu2
    have h2 : |β| * u n - |α| ≤ (|β| * u n - |α|) * Real.sqrt (u n) :=
      le_mul_of_one_le_right (by linarith) hs1
    have h3 : |β| * (u n * Real.sqrt (u n)) - |α| * Real.sqrt (u n) ≤
        |α * Real.sqrt (u n) + β * (u n * Real.sqrt (u n))| := by
      have := abs_sub_abs_le_abs_sub (β * (u n * Real.sqrt (u n))) (-(α * Real.sqrt (u n)))
      rw [sub_neg_eq_add, abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ u n),
        abs_of_nonneg (Real.sqrt_nonneg _), add_comm] at this
      linarith
    nlinarith [le_abs_self C]
  refine ⟨?_, hβ⟩
  subst hβ
  by_contra hα
  have hα0 : 0 < |α| := abs_pos.mpr hα
  have hs : Tendsto (fun n => Real.sqrt (u n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hu
  obtain ⟨n, hn, hs1⟩ := (hb.and (hs.eventually_ge_atTop ((|C| + 1) / |α|))).exists
  rw [zero_mul, add_zero, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  rw [div_le_iff₀ hα0] at hs1
  nlinarith [le_abs_self C]

/-- **A cusp expansion** of `K` in the cusp labelled `κ` (see the module docstring): zero modes
`A(x)u^{½} + B(x)u^{3/2}` in the upper point and `a₁t^{½} + a₂t^{3/2}`, `b₁t^{½} + b₂t^{3/2}` in the
lower one, up to errors vanishing with the heights, and the Wronskian `b₁ ≠ a₂`. -/
structure CuspExpansion {Y ι : Type*} (K : Y → Y → ℝ) (ht : Y → ℝ) (lab : Y → ι) (κ : ι) where
  T₀ : ℝ
  A : Y → ℝ
  B : Y → ℝ
  a₁ : ℝ
  a₂ : ℝ
  b₁ : ℝ
  b₂ : ℝ
  wronskian : b₁ ≠ a₂
  zeroMode : ∀ x, lab x = κ → T₀ < ht x → ∀ y : ℕ → Y, (∀ n, lab (y n) = κ) →
    Tendsto (ht ∘ y) atTop atTop →
    Tendsto (fun n => K x (y n) - (A x * Real.sqrt (ht (y n)) +
      B x * (ht (y n) * Real.sqrt (ht (y n))))) atTop (𝓝 0)
  zeroModeA : ∀ x : ℕ → Y, (∀ n, lab (x n) = κ) → Tendsto (ht ∘ x) atTop atTop →
    Tendsto (fun n => A (x n) - (a₁ * Real.sqrt (ht (x n)) +
      a₂ * (ht (x n) * Real.sqrt (ht (x n))))) atTop (𝓝 0)
  zeroModeB : ∀ x : ℕ → Y, (∀ n, lab (x n) = κ) → Tendsto (ht ∘ x) atTop atTop →
    Tendsto (fun n => B (x n) - (b₁ * Real.sqrt (ht (x n)) +
      b₂ * (ht (x n) * Real.sqrt (ht (x n))))) atTop (𝓝 0)

/-- On pairs of ratio `≥ 2` the normalized Frobenius intersection is bounded in absolute value. -/
theorem abs_frobeniusTarget_le {m n : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ n) (κ : ℝ) :
    |archProfile |Real.log n - Real.log m| + κ * weilPrimeKernel m n| ≤
      archProfile (Real.log 2) + 2 * |κ| := by
  have hup := frobeniusTarget_le hm h2 κ
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (2 : ℝ) * m ≤ n := by exact_mod_cast h2
  have hlt : Real.log m < Real.log n := Real.log_lt_log hm' (by linarith)
  have ha : 0 ≤ archProfile |Real.log n - Real.log m| :=
    (archProfile_pos (abs_pos.mpr (sub_ne_zero.mpr hlt.ne'))).le
  have ha2 : 0 ≤ archProfile (Real.log 2) := (archProfile_pos (Real.log_pos (by norm_num))).le
  have hw : -(2 * |κ|) ≤ κ * weilPrimeKernel m n := by
    have h0 := weilPrimeKernel_nonneg m n
    have hle := weilPrimeKernel_le_two m n
    have : -(|κ| * weilPrimeKernel m n) ≤ κ * weilPrimeKernel m n := by
      have := neg_abs_le κ
      nlinarith
    nlinarith [abs_nonneg κ]
  rw [abs_le]
  constructor <;> linarith

/-- **No embedding into a finite-volume quotient carries the Frobenius intersection** (B118′.1).
`Y` has a height with compact sublevel sets and finitely many cusp labels; `K` is Newtonian and has
a cusp expansion in every cusp. -/
theorem not_eq_frobenius_of_finiteVolume {Y ι : Type*} [PseudoMetricSpace Y] [Finite ι]
    {K : Y → Y → ℝ} (hK : IsNewtonian K) {ht : Y → ℝ} (hcpt : ∀ T, IsCompact {y | ht y ≤ T})
    {lab : Y → ι} (E : ∀ κ, CuspExpansion K ht lab κ) {w : ℕ → Y} (hw : Function.Injective w)
    (κ₀ : ℝ) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      K (w m) (w n) = archProfile |Real.log n - Real.log m| + κ₀ * weilPrimeKernel m n := by
  intro h
  by_cases hb : ∃ T, ∃ᶠ n in atTop, ht (w n) ≤ T
  · obtain ⟨T, hT⟩ := hb
    obtain ⟨y, -, hy⟩ := (hcpt T).exists_mapClusterPt_of_frequently (f := w) hT
    exact not_eq_frobenius_of_mapClusterPt hK hw hy κ₀ h
  push Not at hb
  have htend : Tendsto (ht ∘ w) atTop atTop :=
    tendsto_atTop.2 fun T => (hb T).mono fun n hn => hn.le
  -- infinitely many degrees in one cusp
  obtain ⟨κ, hκ⟩ : ∃ κ, ∃ᶠ n in atTop, lab (w n) = κ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := (eventually_all.2 fun κ => (hcon κ).mono fun n hn => hn).exists
    exact hn (lab (w n)) rfl
  obtain ⟨φ, hφ, hφκ⟩ := extraction_of_frequently_atTop hκ
  set y := w ∘ φ with hy
  have hyt : Tendsto (ht ∘ y) atTop atTop := htend.comp hφ.tendsto_atTop
  set C₀ := archProfile (Real.log 2) + 2 * |κ₀| with hC₀
  -- both zero-mode coefficients vanish at every high degree of the cusp
  have hAB : ∀ j, 1 ≤ j → (E κ).T₀ < ht (y j) → (E κ).A (y j) = 0 ∧ (E κ).B (y j) = 0 := by
    intro j hj hjT
    have hlim := (E κ).zeroMode (y j) (hφκ j) hjT y hφκ hyt
    have hφj : 1 ≤ φ j := le_trans hj (hφ.id_le j)
    refine eq_zero_of_bounded_zeroMode hyt (C := C₀ + 1) ?_
    have hev1 := hlim.eventually (Metric.ball_mem_nhds 0 one_pos)
    have hev2 : ∀ᶠ k in atTop, 2 * φ j ≤ φ k := hφ.tendsto_atTop.eventually_ge_atTop _
    filter_upwards [hev1, hev2] with k hk1 hk2
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hk1
    have heq := h (φ j) (φ k) (by omega) (by omega) (by omega)
    have hbd := abs_frobeniusTarget_le (by omega : 0 < φ j) hk2 κ₀
    simp only [hy, Function.comp_apply] at hk1 ⊢
    rw [heq] at hk1
    have := abs_sub_abs_le_abs_sub
      (archProfile |Real.log (φ k) - Real.log (φ j)| + κ₀ * weilPrimeKernel (φ j) (φ k))
      ((E κ).A (w (φ j)) * Real.sqrt (ht (w (φ k))) +
        (E κ).B (w (φ j)) * (ht (w (φ k)) * Real.sqrt (ht (w (φ k)))))
    rw [abs_sub_comm] at this
    linarith [abs_sub_abs_le_abs_sub
      ((E κ).A (w (φ j)) * Real.sqrt (ht (w (φ k))) +
        (E κ).B (w (φ j)) * (ht (w (φ k)) * Real.sqrt (ht (w (φ k)))))
      (archProfile |Real.log (φ k) - Real.log (φ j)| + κ₀ * weilPrimeKernel (φ j) (φ k))]
  have hev : ∀ᶠ j in atTop, (E κ).A (y j) = 0 ∧ (E κ).B (y j) = 0 :=
    ((eventually_ge_atTop 1).and (hyt.eventually_gt_atTop (E κ).T₀)).mono
      fun j ⟨hj, hjT⟩ => hAB j hj hjT
  -- then the coefficients of `A` and `B` vanish
  have hcoef : ∀ (F : Y → ℝ) (c₁ c₂ : ℝ), (∀ᶠ j in atTop, F (y j) = 0) →
      Tendsto (fun n => F (y n) - (c₁ * Real.sqrt (ht (y n)) +
        c₂ * (ht (y n) * Real.sqrt (ht (y n))))) atTop (𝓝 0) → c₁ = 0 ∧ c₂ = 0 := by
    intro F c₁ c₂ hF hlim
    refine eq_zero_of_bounded_zeroMode hyt (C := 1) ?_
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds 0 one_pos), hF] with n hn hFn
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hFn, zero_sub, abs_neg] at hn
    exact hn.le
  have ha := hcoef (E κ).A (E κ).a₁ (E κ).a₂ (hev.mono fun j hj => hj.1)
    ((E κ).zeroModeA y hφκ hyt)
  have hb' := hcoef (E κ).B (E κ).b₁ (E κ).b₂ (hev.mono fun j hj => hj.2)
    ((E κ).zeroModeB y hφκ hyt)
  exact (E κ).wronskian (hb'.1.trans ha.2.symm)

end GaloisForLFunctions.HyperbolicArakelovTheory
