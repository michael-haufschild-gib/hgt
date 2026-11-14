import GaloisForLFunctions.CompactHyperbolicSurfaces.CyclicCovers
import GaloisForLFunctions.CompactHyperbolicSurfaces.SmallEigenvalueZeta
import GaloisForLFunctions.CompactHyperbolicSurfaces.AreaIntegrality

/-!
# The Selberg zeta function is entire

With `|F| = 2πN`, `N ∈ ℕ` (`exists_nat_volume_F_eq`), the factor `e^{(|F|/2π) G_a(s)}` of
`Z = κ E e^{A(s² − s)} e^{(|F|/2π) G_a}` is the product of the entire functions

  `e^{N g_k(s)} = (s + k)^{N(2k+1)} e^{N((s² − s)/(a + k) − 2s − g̃_k(a))}`   (`zFactor`),

`g_k` the `k`-th term of `G_a`.  On `|s| < R` and `k ≥ K_R`, `|g_k(s)| ≤ C_R/k²`
(`exists_norm_gTerm_le`: mean value theorem with `|g_k'| = |2s − 1| |s − a|/((a + k)|s + k|)`), so
`Π_k e^{N g_k}` converges locally uniformly on `ℂ` (`hasProdLocallyUniformlyOn_zFactor`).  Hence
`Ẑ = κ E e^{A(s² − s)} Π_k e^{N g_k}` (`entireZeta`) is entire and equals `Z` on `Re s > 0`
(`entireZeta_eq_selbergZeta`).

**Headline** (`exists_selbergZeta_small_eigenvalue`).  For some odd `n`, the cyclic cover
`X = Γ_n\ℍ` of the quaternion surface `Γ(5)\ℍ` has an entire function `Ẑ` which is the Euler
product `Π_{p, k} (1 − e^{−(s+k)ℓ_p})` on `Re s > 1`, satisfies
`Ẑ(1 − s) = Ẑ(s) exp(−|F| ∫_0^{s−½} v tan πv dv)` on `0 < Re s < 1`, and whose zeros in
`0 < Re s < 1` off `Re s = ½` are exactly the points `½ ± √(¼ − λ)` for the eigenvalues
`λ ∈ (0, ¼)`: a finite nonempty set.
-/

open MeasureTheory Set Filter Metric
open scoped MatrixGroups Topology Real

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-! ### The entire factors -/

/-- `g̃_k(a) = (a² − a)/(a + k) − 2a + (2k + 1) log(a + k)`. -/
def gConst (a : ℝ) (k : ℕ) : ℂ :=
  ((a : ℂ) * a - a) / ((a : ℂ) + k) - 2 * a + (2 * k + 1) * Complex.log ((a : ℂ) + k)

/-- The entire factor `(s + k)^{N(2k+1)} e^{N((s² − s)/(a + k) − 2s − g̃_k(a))}`. -/
def zFactor (N : ℕ) (a : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  (s + k) ^ (N * (2 * k + 1)) *
    Complex.exp (N * ((s * s - s) / ((a : ℂ) + k) - 2 * s - gConst a k))

/-- `e^{N g_k(s)} = (s + k)^{N(2k+1)} e^{N(…)}` away from `s = −k`. -/
theorem zFactor_eq_exp (N : ℕ) (a : ℝ) (k : ℕ) {s : ℂ} (hs : s + k ≠ 0) :
    zFactor N a k s = Complex.exp (N * gTerm a k s) := by
  rw [zFactor, gTerm, ← gConst]
  conv_lhs => rw [← Complex.exp_log hs, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_zFactor (N : ℕ) (a : ℝ) (k : ℕ) : Continuous (zFactor N a k) := by
  unfold zFactor; fun_prop

theorem differentiable_zFactor (N : ℕ) (a : ℝ) (k : ℕ) : Differentiable ℂ (zFactor N a k) := by
  have hk : ((a : ℂ) + k) = ((a + k : ℝ) : ℂ) := by push_cast; ring
  unfold zFactor; fun_prop

/-- `g_k' = (2s − 1)(1/(a + k) − 1/(s + k))` wherever `Re(s + k) > 0`. -/
theorem hasDerivAt_gTerm' {a : ℝ} (ha : 0 < a) (k : ℕ) {s : ℂ} (hs : 0 < s.re + k) :
    HasDerivAt (gTerm a k) ((2 * s - 1) * psiTerm a k s) s := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hslit : s + k ∈ Complex.slitPlane := Or.inl (by simpa using hs)
  have ht0 : s + k ≠ 0 := Complex.slitPlane_ne_zero hslit
  have ha0 : (a : ℂ) + k ≠ 0 := by exact_mod_cast (show (0 : ℝ) < a + k by linarith).ne'
  have h1 : HasDerivAt (fun s : ℂ => (s * s - s) / ((a : ℂ) + k)) ((2 * s - 1) / ((a : ℂ) + k)) s :=
    ((((hasDerivAt_id s).mul (hasDerivAt_id s)).sub (hasDerivAt_id s)).div_const
      ((a : ℂ) + k)).congr_deriv (by simp only [id]; ring)
  have h2 : HasDerivAt (fun s : ℂ => Complex.log (s + k)) (1 / (s + k)) s :=
    ((hasDerivAt_id s).add_const (k : ℂ)).clog hslit
  have h3 := ((h1.sub ((hasDerivAt_id s).const_mul 2)).add
    (h2.const_mul (2 * (k : ℂ) + 1))).sub_const
    (((a : ℂ) * a - a) / ((a : ℂ) + k) - 2 * a + (2 * k + 1) * Complex.log ((a : ℂ) + k))
  refine h3.congr_deriv ?_
  rw [psiTerm]
  field_simp
  ring

/-- **The terms of `G_a` are `O(k⁻²)` locally uniformly.**  For `|s| < R` and `k ≥ K`:
`s + k ≠ 0` and `|g_k(s)| ≤ C/k²`. -/
theorem exists_norm_gTerm_le {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 1 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ s ∈ ball (0 : ℂ) R,
      s + k ≠ 0 ∧ ‖gTerm a k s‖ ≤ C / (k : ℝ) ^ 2 := by
  set R' := max R a + 1
  have hR'a : a + 1 ≤ R' := by have := le_max_right R a; simp only [R']; linarith
  have hR'R : R + 1 ≤ R' := by have := le_max_left R a; simp only [R']; linarith
  have hR' : 0 < R' := by linarith
  refine ⟨2 * R' * (2 * (2 * R' + 1) * (R' + a)), 2 * R' + 1, by positivity, by linarith,
    fun k hk s hs => ?_⟩
  have hkpos : (0 : ℝ) < k := by linarith
  -- on `ball 0 R'`: `Re(t + k) > 0` and `|t + k| ≥ k/2`
  have hball : ∀ t ∈ ball (0 : ℂ) R', 0 < t.re + k ∧ (k : ℝ) / 2 ≤ ‖t + k‖ := by
    intro t ht
    have ht' : ‖t‖ < R' := by simpa using ht
    have h1 : -‖t‖ ≤ t.re := by have := Complex.abs_re_le_norm t; linarith [abs_le.mp this]
    have h2 : (k : ℝ) - ‖t‖ ≤ ‖t + k‖ := by
      have := norm_sub_norm_le ((k : ℂ)) (-t)
      rw [sub_neg_eq_add, norm_neg, Complex.norm_natCast, add_comm] at this
      linarith
    constructor <;> linarith
  have hsR : s ∈ ball (0 : ℂ) R' := ball_subset_ball (by linarith) hs
  have haR : (a : ℂ) ∈ ball (0 : ℂ) R' := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ha.le]; linarith
  refine ⟨fun h => ?_, ?_⟩
  · have := (hball s hsR).2
    rw [h, norm_zero] at this
    linarith
  -- the derivative bound
  have hbound : ∀ t ∈ ball (0 : ℂ) R', ‖deriv (gTerm a k) t‖ ≤
      2 * (2 * R' + 1) * (R' + a) / (k : ℝ) ^ 2 := by
    intro t ht
    obtain ⟨hre, hnorm⟩ := hball t ht
    have ht' : ‖t‖ < R' := by simpa using ht
    have htk : t + k ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
    have hak : (a : ℂ) + k ≠ 0 := by exact_mod_cast (show (0 : ℝ) < a + k by linarith).ne'
    rw [(hasDerivAt_gTerm' ha k hre).deriv, psiTerm,
      show 1 / ((a : ℂ) + k) - 1 / (t + k) = (t - a) / (((a : ℂ) + k) * (t + k)) by
        field_simp; ring,
      norm_mul, norm_div, norm_mul]
    have hakn : ‖(a : ℂ) + k‖ = a + k := by
      rw [show ((a : ℂ) + k) = ((a + k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [hakn]
    have h1 : ‖2 * t - 1‖ ≤ 2 * R' + 1 := by
      have := norm_sub_le (2 * t) 1
      rw [norm_mul, norm_one, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    have h2 : ‖t - a‖ ≤ R' + a := by
      have := norm_sub_le t (a : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg ha.le] at this
      linarith
    have h3 : (k : ℝ) * (k / 2) ≤ (a + k) * ‖t + k‖ :=
      mul_le_mul (by linarith) hnorm (by positivity) (by positivity)
    have hden : 0 < (a + k) * ‖t + k‖ := lt_of_lt_of_le (by positivity) h3
    calc ‖2 * t - 1‖ * (‖t - a‖ / ((a + k) * ‖t + k‖))
        ≤ (2 * R' + 1) * ((R' + a) / ((k : ℝ) * (k / 2))) := by
          gcongr
      _ = 2 * (2 * R' + 1) * (R' + a) / (k : ℝ) ^ 2 := by field_simp
  have hmv := (convex_ball (0 : ℂ) R').norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hasDerivAt_gTerm' ha k (hball t ht).1).differentiableAt) hbound haR hsR
  have hga : gTerm a k a = 0 := by rw [gTerm]; ring
  rw [hga, sub_zero] at hmv
  have hsa : ‖s - a‖ ≤ 2 * R' := by
    have := norm_sub_le s (a : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg ha.le] at this
    have : ‖s‖ < R' := by simpa using hsR
    linarith
  calc ‖gTerm a k s‖ ≤ 2 * (2 * R' + 1) * (R' + a) / (k : ℝ) ^ 2 * ‖s - a‖ := hmv
    _ ≤ 2 * (2 * R' + 1) * (R' + a) / (k : ℝ) ^ 2 * (2 * R') :=
        mul_le_mul_of_nonneg_left hsa (by positivity)
    _ = 2 * R' * (2 * (2 * R' + 1) * (R' + a)) / (k : ℝ) ^ 2 := by ring

/-- **Locally uniform convergence of `Π_k e^{N g_k}` on `ℂ`.** -/
theorem hasProdLocallyUniformlyOn_zFactor (N : ℕ) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun k => zFactor N a k) (fun s => ∏' k : ℕ, zFactor N a k s)
      (ball (0 : ℂ) R) := by
  obtain ⟨C, K, hC, hK1, hb⟩ := exists_norm_gTerm_le ha R
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun k s => zFactor N a k s - 1) (K := ball (0 : ℂ) R) isOpen_ball
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 * N * C)) ?_
    (fun k => ((continuous_zFactor N a k).sub continuous_const).continuousOn)
  · simpa only [add_sub_cancel] using h
  rw [eventually_atTop]
  refine ⟨max ⌈K⌉₊ (⌈(N : ℝ) * C⌉₊ + 1), fun k hk s hs => ?_⟩
  have hkK : K ≤ k := (Nat.ceil_le.mp (le_of_max_le_left hk))
  have hkNC : (N : ℝ) * C < k := by
    have h1 := le_of_max_le_right hk
    have h2 : (N : ℝ) * C ≤ ⌈(N : ℝ) * C⌉₊ := Nat.le_ceil _
    have h3 : ((⌈(N : ℝ) * C⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hk1 : (1 : ℝ) ≤ k := hK1.trans hkK
  obtain ⟨hsk, hg⟩ := hb k hkK s hs
  rw [zFactor_eq_exp N a k hsk]
  have hNg : ‖(N : ℂ) * gTerm a k s‖ ≤ (N : ℝ) * (C / (k : ℝ) ^ 2) := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)
  have hsmall : (N : ℝ) * (C / (k : ℝ) ^ 2) ≤ 1 := by
    have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    rw [← mul_div_assoc, div_le_one (by positivity)]
    linarith
  refine (Complex.norm_exp_sub_one_le (hNg.trans hsmall)).trans ?_
  calc 2 * ‖(N : ℂ) * gTerm a k s‖ ≤ 2 * ((N : ℝ) * (C / (k : ℝ) ^ 2)) := by linarith
    _ = 2 * N * C * (1 / (k : ℝ) ^ 2) := by ring

/-- **`Π_k e^{N g_k}` is entire.** -/
theorem differentiable_tprod_zFactor (N : ℕ) {a : ℝ} (ha : 0 < a) :
    Differentiable ℂ fun s => ∏' k : ℕ, zFactor N a k s := by
  intro s
  have hmem : s ∈ ball (0 : ℂ) (‖s‖ + 1) := by simp
  have hd : DifferentiableOn ℂ (fun s => ∏' k : ℕ, zFactor N a k s) (ball (0 : ℂ) (‖s‖ + 1)) :=
    (hasProdLocallyUniformlyOn_zFactor N ha _).differentiableOn
      (Eventually.of_forall fun _ => by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finsetProd (fun _ _ => (differentiable_zFactor N a _).differentiableOn))
      isOpen_ball
  exact (hd s hmem).differentiableAt (isOpen_ball.mem_nhds hmem)

/-- On `Re s > 0`, `Π_k e^{N g_k(s)} = e^{N G_a(s)}`. -/
theorem tprod_zFactor_eq (N : ℕ) {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ∏' k : ℕ, zFactor N a k s = Complex.exp (N * gSeries a s) := by
  obtain ⟨C, K, -, -, hb⟩ := exists_norm_gTerm_le ha (‖s‖ + 1)
  have hsum : Summable fun k => gTerm a k s := by
    refine Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left C) ?_
    rw [eventually_atTop]
    refine ⟨⌈K⌉₊, fun k hk => ?_⟩
    have h := (hb k (Nat.ceil_le.mp hk) s (by simp)).2
    rwa [mul_one_div]
  have h := (hsum.hasSum.mul_left (N : ℂ)).cexp
  rw [gSeries, ← h.tprod_eq]
  refine tprod_congr fun k => ?_
  have hsk : s + k ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [Function.comp_apply, zFactor_eq_exp N a k hsk]

/-! ### The entire zeta function -/

namespace CompactQuotient

variable (X : CompactQuotient)

/-- `N = |F|/2π`, a natural number. -/
def areaN : ℕ := X.exists_nat_volume_F_eq.choose

theorem area_eq_areaN : X.area = 2 * π * X.areaN := X.exists_nat_volume_F_eq.choose_spec

/-- **The entire Selberg zeta function** `Ẑ(s) = κ E(s) e^{A(s² − s)} Π_k e^{N g_k(s)}`. -/
def entireZeta {a : ℝ} (ha : 1 < a) (s : ℂ) : ℂ :=
  X.zetaConst ha * X.specProd ha s * Complex.exp (X.zConst a * (s * s - s)) *
    ∏' k : ℕ, zFactor X.areaN a k s

theorem differentiable_entireZeta {a : ℝ} (ha : 1 < a) : Differentiable ℂ (X.entireZeta ha) := by
  have hE := X.differentiable_specProd ha
  have hP := differentiable_tprod_zFactor X.areaN (a := a) (by linarith)
  unfold entireZeta
  fun_prop

/-- **`Ẑ = Z` on `Re s > 0`.** -/
theorem entireZeta_eq_selbergZeta {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : 0 < s.re) :
    X.entireZeta ha s = X.selbergZeta ha s := by
  have hN : ((X.area / (2 * π) : ℝ) : ℂ) = X.areaN := by
    rw [area_eq_areaN, mul_div_cancel_left₀ _ (by positivity)]
    push_cast
    ring
  rw [entireZeta, selbergZeta, zG, tprod_zFactor_eq _ (by linarith) hs, hN, mul_assoc _ (Complex.exp _),
    ← Complex.exp_add]

end CompactQuotient

open CompactQuotient

/-- **The Selberg zeta function of a surface with a small eigenvalue.**  For some odd `n`,
`X = Γ_n\ℍ` (a cyclic cover of the quaternion surface `Γ(5)\ℍ`, every `γ ≠ 1` hyperbolic) carries
an entire function `Ẑ` (`= Z` on `Re s > 0`) which is the Euler product
`Π_{p, k} (1 − e^{−(s+k)ℓ_p})` on `Re s > 1`, satisfies
`Ẑ(1 − s) = Ẑ(s) exp(−|F| ∫_0^{s−½} v tan πv dv)` on `0 < Re s < 1`, and whose zeros in
`0 < Re s < 1` off `Re s = ½` are exactly the points `½ ± √(¼ − λ)` for the eigenvalues
`λ ∈ (0, ¼)`, a finite nonempty set. -/
theorem exists_selbergZeta_small_eigenvalue :
    ∃ (n : ℕ) (X : CompactQuotient) (Z : ℂ → ℂ), X.Γ = coverGroup n ∧
      (∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) ∧
      Differentiable ℂ Z ∧
      (∀ s : ℂ, 0 < s.re → Z s = X.selbergZeta one_lt_two s) ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun x : X.PClass × ℕ =>
          1 - Complex.exp (-((s + x.2) * X.classLen x.1.1))) (Z s)) ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 → Z (1 - s) = Z s * Complex.exp (-(X.area *
          ∫ t in (0 : ℝ)..1, (s - 1 / 2) * (((t : ℂ) * (s - 1 / 2)) *
            Complex.tan (π * ((t : ℂ) * (s - 1 / 2))))))) ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ Z s = 0}.Finite ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ Z s = 0}.Nonempty ∧
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ Z s = 0} =
        {s | ∃ j : X.SpecIndex one_lt_two, 0 < X.spectralParam one_lt_two j ∧
          X.spectralParam one_lt_two j < 1 / 4 ∧
          (s = ((1 / 2 + √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ) ∨
            s = ((1 / 2 - √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ))} := by
  obtain ⟨n, hodd, -, hsmall⟩ := exists_coverGroup_small_eigenvalue (a := 2) one_lt_two
  obtain ⟨X, hX⟩ := exists_compactQuotient_coverGroup hodd
  have hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ| := by
    intro γ hγ
    have hmem : (γ : SL(2, ℝ)) ∈ congGroup 5 := (hX ▸ γ.2 : (γ : SL(2, ℝ)) ∈ coverGroup n).1
    exact two_lt_abs_trSL_congGroup (by norm_num) ⟨γ, hmem⟩ fun h =>
      hγ (Subtype.ext (congrArg (fun x : congGroup 5 => (x : SL(2, ℝ))) h))
  obtain ⟨j, hj0, hj1⟩ := hsmall X hX
  have hEq : ∀ s : ℂ, 0 < s.re → X.entireZeta one_lt_two s = X.selbergZeta one_lt_two s :=
    fun s hs => X.entireZeta_eq_selbergZeta one_lt_two hs
  have hset : {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.entireZeta one_lt_two s = 0} =
      {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta one_lt_two s = 0} := by
    ext s
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1, h2, h3⟩; exact ⟨h0, h1, h2, (hEq s h0) ▸ h3⟩
    · rintro ⟨h0, h1, h2, h3⟩; exact ⟨h0, h1, h2, (hEq s h0).symm ▸ h3⟩
  have hzeros := X.offLine_zeros_eq hhyp one_lt_two
  refine ⟨n, X, X.entireZeta one_lt_two, hX, hhyp, X.differentiable_entireZeta one_lt_two, hEq,
    fun s hs => ?_, fun s h0 h1 => ?_, ?_, ?_, hset.trans hzeros⟩
  · rw [hEq s (by linarith), ← eulerZeta_eq_selbergZeta hhyp one_lt_two hs]
    exact hasProd_eulerZeta hhyp hs
  · rw [hEq s h0, hEq (1 - s) (by simp; linarith)]
    exact selbergZeta_one_sub (X := X) one_lt_two h0 h1
  · have hS := X.finite_lam_lt one_lt_two (1 / 4)
    refine ((hS.image fun j => ((1 / 2 + √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ)).union
      (hS.image fun j => ((1 / 2 - √(1 / 4 - X.spectralParam one_lt_two j) : ℝ) : ℂ))).subset ?_
    rw [hset, hzeros]
    rintro s ⟨j, -, hj, hs | hs⟩
    · exact Or.inl ⟨j, hj, hs.symm⟩
    · exact Or.inr ⟨j, hj, hs.symm⟩
  · rw [hset, hzeros]
    exact ⟨_, j, hj0, hj1, Or.inl rfl⟩

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
