import GaloisForLFunctions.RHTower.WeilRationalMassAtomicProduct
import GaloisForLFunctions.RHTower.MaassZetaSquaredConverse

/-!
# Half-integer spectral masses force `Λ` and the Riemann hypothesis

Let `lam` be full-cone Weil-positive whose boundary measure `μ` has half-integer counting:
`2μ((a,b]) ∈ ℕ` for `a < b` in a set of full measure.  The atoms may lie anywhere.

**Theorem** (`vonMangoldt_and_riemannHypothesis_of_half_integer_counting`).  Then
`lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.

The atomic form with masses `m_j/2` (`half_integer_mass_rigidity`) and the form through the
square of the completed exponential (`vonMangoldt_and_riemannHypothesis_of_bigG_sq`) are proved
on the way.

**Proof.**
* `G = s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)` satisfies `G² = K P Q` on `Re s > 1`, with `P` the
  polynomial of the finitely many atoms in `(−1, 1)` and `Q` the symmetric genus-one product over
  the other atoms (`WeilSpectral.bigG_pow_eq_of_fractional_counting`).  So the Dirichlet series
  `F² = exp(Σ 2 lam(n) n^{−s}/log n)`, with coefficients `g = a ⋆ a`, `g_1 = 1`, has the completion
  `K P Q`: entire, with `(KPQ)(1 − s) = ε (KPQ)(s)`, `ε = ±1`.
* `|P(σ + iτ)|` and `|Q(σ + iτ)|` increase in `σ ≥ 1/2` and `|G(2 + iτ)|` is bounded (Stirling), so
  `K P Q` is bounded on `−1/2 ≤ Re s ≤ 3/2`.
* If `ε = −1`, the odd converse statement (`coeff_eq_zero_of_odd_functional_equation`) gives
  `g_1 = 0`, which is false.  So `ε = 1`, and the converse theorem for `ζ²`
  (`MaassZetaSquaredConverse`) gives `F² = ζ²`.  Comparing logarithmic derivatives,
  `Σ lam(n) n^{−s} = −ζ'/ζ(s)`, so `lam = Λ`.
* Then `K P Q = (2ξ)²` everywhere; a zero `ρ` of `ζ` with `Re ρ > 1/2` would be a zero of `P Q` off
  the critical line, which `P Q` does not have.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace RHTower.HalfIntegerMassRigidity

open IntegerMassRigidity MaassZetaSquaredConverse GaloisForLFunctions.HTGeometry

variable {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ}

/-! ## Bounds on the strip -/

/-- `G(2 + iτ)` is bounded. -/
theorem exists_bound_bigG_two (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, ‖bigG lam (2 + τ * I)‖ ≤ B := by
  obtain ⟨Cγ, Nγ, hCγ, hγ⟩ := exists_bound_Gammaℝ_two
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) 2 n‖ with hS
  set F : ℝ := (4 / Real.pi) ^ (Nγ + 2) * (Nγ + 2).factorial * Real.exp Real.pi with hF
  refine ⟨Cγ * Real.exp S * F, by positivity, fun τ => ?_⟩
  have hre : (1 : ℝ) < (2 + (τ : ℂ) * I).re := by simp
  unfold bigG zetaOf
  have hsumm : LSeriesSummable (lamLog lam) (2 + τ * I) :=
    lseriesSummable_of_le (norm_lamLog_le lam) hsl hre
  have hL : ‖LSeries (lamLog lam) (2 + τ * I)‖ ≤ S := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsumm.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hz : ‖Complex.exp (LSeries (lamLog lam) (2 + τ * I))‖ ≤ Real.exp S := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)
  have hτ := abs_nonneg τ
  have h1 : ‖(2 + (τ : ℂ) * I)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I)‖ ≤ ‖(2 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have h2 : ‖(2 + (τ : ℂ) * I - 1)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I - 1)‖ = ‖(1 : ℂ) + (τ : ℂ) * I‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have hpe : (|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4)) ≤ F := by
    have h := pow_mul_exp_le (by positivity : (0 : ℝ) ≤ |τ| + 4) (Nγ + 2)
    have he : Real.exp (-(Real.pi * |τ| / 4)) =
        Real.exp (-(Real.pi * (|τ| + 4) / 4)) * Real.exp Real.pi := by
      rw [← Real.exp_add]; ring_nf
    rw [he, hF, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(2 + (τ : ℂ) * I)‖ * ‖(2 + (τ : ℂ) * I - 1)‖ * ‖Complex.Gammaℝ (2 + τ * I)‖ *
        ‖Complex.exp (LSeries (lamLog lam) (2 + τ * I))‖
      ≤ (|τ| + 4) * (|τ| + 4) * (Cγ * ((|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)))) *
          Real.exp S := by
        gcongr
        exact hγ τ
    _ = Cγ * Real.exp S * ((|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4))) := by ring
    _ ≤ Cγ * Real.exp S * F := mul_le_mul_of_nonneg_left hpe (by positivity)

theorem atomQ_two_ne_zero (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) :
    atomQ m t 2 ≠ 0 :=
  atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne (by norm_num))

/-- `|Q(σ + iτ)| ≤ |Q(2 + iτ)|` for `1/2 ≤ σ ≤ 2`. -/
theorem norm_atomQ_le_two (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    {σ : ℝ} (τ : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 2) :
    ‖atomQ m t (σ + τ * I)‖ ≤ ‖atomQ m t (2 + τ * I)‖ := by
  have h := norm_ghat_le_two (lam := fun _ => (0 : ℝ)) hone hsum τ h1 h2
  unfold ghat at h
  rw [norm_mul, norm_mul] at h
  have hK : 0 < ‖bigK (fun _ => (0 : ℝ)) m t‖ :=
    norm_pos_iff.mpr (div_ne_zero (bigG_ne_zero _ (by norm_num)) (atomQ_two_ne_zero hone hsum))
  exact le_of_mul_le_mul_left h hK

/-- The completion `K P Q` is bounded on `−1/2 ≤ Re s ≤ 3/2`. -/
theorem exists_bound_completion (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {F : Finset ℝ}
    {n : ℝ → ℕ} (hF : ∀ x ∈ F, -x ∈ F) (hn : ∀ x, n (-x) = n x) {K : ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → bigG lam s ^ 2 = K * (WeilSpectral.atomPoly F n s * atomQ m t s)) :
    ∃ B : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖K * (WeilSpectral.atomPoly F n s * atomQ m t s)‖ ≤ B := by
  obtain ⟨B₀, hB₀, hB⟩ := exists_bound_bigG_two hsl
  have hright : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖K * (WeilSpectral.atomPoly F n s * atomQ m t s)‖ ≤ B₀ ^ 2 := by
    intro s h1 h2
    have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
    have hmonoQ := norm_atomQ_le_two hone hsum s.im h1 (by linarith)
    have hmonoP := WeilSpectral.norm_atomPoly_le_two F n s.im h1 (by linarith)
    rw [← hs] at hmonoQ hmonoP
    have h2re : (1 : ℝ) < (2 + (s.im : ℂ) * I).re := by simp
    calc ‖K * (WeilSpectral.atomPoly F n s * atomQ m t s)‖
        = ‖K‖ * (‖WeilSpectral.atomPoly F n s‖ * ‖atomQ m t s‖) := by rw [norm_mul, norm_mul]
      _ ≤ ‖K‖ * (‖WeilSpectral.atomPoly F n (2 + s.im * I)‖ * ‖atomQ m t (2 + s.im * I)‖) := by
          gcongr
      _ = ‖bigG lam (2 + s.im * I) ^ 2‖ := by rw [hG _ h2re, norm_mul, norm_mul]
      _ = ‖bigG lam (2 + s.im * I)‖ ^ 2 := norm_pow _ _
      _ ≤ B₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
  refine ⟨B₀ ^ 2, fun s h1 h2 => ?_⟩
  by_cases hr : 1 / 2 ≤ s.re
  · exact hright s hr h2
  · rw [not_le] at hr
    have h := hright (1 - s) (by simp; linarith) (by simp; linarith)
    rw [WeilSpectral.atomPoly_one_sub F n hF hn, atomQ_one_sub hone hsum] at h
    have hpm : ‖((-1 : ℂ) ^ (∑ x ∈ F, n x))‖ = 1 := by simp
    calc ‖K * (WeilSpectral.atomPoly F n s * atomQ m t s)‖
        = ‖K * ((-1) ^ (∑ x ∈ F, n x) * WeilSpectral.atomPoly F n s * atomQ m t s)‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hpm, one_mul]
      _ ≤ B₀ ^ 2 := h

/-! ## The main theorem -/

/-- **Half-integer masses, through the square of the completed exponential.**  If
`G(s)² = K P(s) Q(s)` on `Re s > 1` for the polynomial `P` of a finite symmetric configuration
and an integer-mass atomic product `Q`, then `lam = Λ` on `n ≥ 2` and the Riemann hypothesis
holds. -/
theorem vonMangoldt_and_riemannHypothesis_of_bigG_sq (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {F : Finset ℝ}
    {n : ℝ → ℕ} (hF : ∀ x ∈ F, -x ∈ F) (hn : ∀ x, n (-x) = n x)
    (hG : ∀ s : ℂ, 1 < s.re → bigG lam s ^ 2 =
      (bigG lam 2 ^ 2 / (WeilSpectral.atomPoly F n 2 * atomQ m t 2)) *
        (WeilSpectral.atomPoly F n s * atomQ m t s)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set K := bigG lam 2 ^ 2 / (WeilSpectral.atomPoly F n 2 * atomQ m t 2) with hKdef
  set R : ℂ → ℂ := fun s => WeilSpectral.atomPoly F n s * atomQ m t s with hR
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  set g := LSeries.convolution a a with hg_def
  have hLg : ∀ s : ℂ, 1 < s.re → LSeriesSummable g s ∧ LSeries g s = zetaOf lam s ^ 2 := by
    intro s hs
    refine ⟨(hLa s hs).1.convolution (hLa s hs).1, ?_⟩
    rw [hg_def, LSeries_convolution' (hLa s hs).1 (hLa s hs).1, (hLa s hs).2, sq]
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have hg1 : g 1 = 1 := by simp [hg_def, LSeries.convolution_def, ha1]
  have hgsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ) :=
    fun σ hσ => summable_of_LSeriesSummable hσ (hLg σ (by simpa using hσ)).1
  have hRd : Differentiable ℂ R :=
    (WeilSpectral.differentiable_atomPoly F n).mul (differentiable_atomQ hone hsum)
  have hΛ : Differentiable ℂ (fun s => K * R s) := hRd.const_mul K
  set ε : ℂ := (-1) ^ (∑ x ∈ F, n x) with hε_def
  have hsymε : ∀ s, K * R (1 - s) = ε * (K * R s) := fun s => by
    simp only [hR]
    rw [WeilSpectral.atomPoly_one_sub F n hF hn, atomQ_one_sub hone hsum]
    ring
  have heq : ∀ s : ℂ, 1 < s.re →
      K * R s = s ^ 2 * (s - 1) ^ 2 * Complex.Gammaℝ s ^ 2 * LSeries g s := by
    intro s hs
    rw [← hG s hs, (hLg s hs).2]
    unfold bigG
    ring
  have hbd := exists_bound_completion hone hsum hsl hF hn (K := K) hG
  -- the sign is `+1`
  have hε : ε = 1 := by
    rcases neg_one_pow_eq_or ℂ (∑ x ∈ F, n x) with h | h
    · exact h
    · exfalso
      have h0 := coeff_eq_zero_of_odd_functional_equation hgsum hΛ
        (fun s => by rw [hsymε, show ε = -1 from h, neg_one_mul]) heq hbd le_rfl
      rw [hg1] at h0
      exact one_ne_zero h0
  have hsym : ∀ s, K * R (1 - s) = K * R s := fun s => by rw [hsymε, hε, one_mul]
  have hcoef := fun {n : ℕ} (hn : 1 ≤ n) =>
    coeff_eq_divisorCount_of_functional_equation hgsum hg1 hΛ hsym heq hbd hn
  -- `F² = ζ²`
  have hsq : ∀ s : ℂ, 1 < s.re → zetaOf lam s ^ 2 = riemannZeta s ^ 2 := by
    intro s hs
    rw [← (hLg s hs).2, ← LSeries_divisorCount hs]
    exact LSeries_congr (fun {n} hn => hcoef (Nat.one_le_iff_ne_zero.mpr hn)) s
  -- comparing logarithmic derivatives: `Σ lam(n) n^{−s} = −ζ'/ζ`
  have hLam : ∀ s : ℂ, 1 < s.re →
      LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : (fun z => riemannZeta z ^ 2) =ᶠ[𝓝 s] (fun z => zetaOf lam z ^ 2) := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact (hsq z hz).symm
    have h1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
    have hdζ := (differentiableAt_riemannZeta h1).hasDerivAt.pow 2
    have hdf := ((hasDerivAt_zetaOf hsl hs).pow 2).congr_of_eventuallyEq hev
    have huniq := hdζ.unique hdf
    have hζne := riemannZeta_ne_zero_of_one_lt_re hs
    simp only [Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one] at huniq
    have hs2 := hsq s hs
    have hkey : riemannZeta s * (deriv riemannZeta s + riemannZeta s * LSeries (lamTwo lam) s) = 0 := by
      linear_combination (1 / 2 : ℂ) * huniq - LSeries (lamTwo lam) s * hs2
    have hkey' : deriv riemannZeta s + riemannZeta s * LSeries (lamTwo lam) s = 0 :=
      (mul_eq_zero.mp hkey).resolve_left hζne
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    field_simp
    linear_combination hkey'
  have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
      (EReal.coe_lt_top 1)
  have habs2 : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
      (EReal.coe_lt_top 1)
  have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hLam x (by simpa using hx)
  refine ⟨fun n hn => ?_, ?_⟩
  · have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
    simp only [lamTwo, if_pos hn] at h
    exact_mod_cast h
  -- the Riemann hypothesis
  · by_contra hRH
    obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : (fun s => K * R s) =ᶠ[𝓝 (2 : ℂ)] zetaSqCompleted := by
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hz' : 1 < z.re := hz
      have h1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
      rw [show K * R z = bigG lam z ^ 2 from (hG z hz').symm, zetaSqCompleted,
        two_xi_eq (by linarith) h1]
      unfold bigG
      rw [mul_pow, hsq z hz', ← mul_pow]
    have hA : AnalyticOnNhd ℂ (fun s => K * R s) Set.univ :=
      hΛ.differentiableOn.analyticOnNhd isOpen_univ
    have hB : AnalyticOnNhd ℂ zetaSqCompleted Set.univ :=
      differentiable_zetaSqCompleted.differentiableOn.analyticOnNhd isOpen_univ
    have hglob := hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ
      (Set.mem_univ _) hev (Set.mem_univ ρ)
    have hglob' : K * R ρ = zetaSqCompleted ρ := hglob
    have hρne1 : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
    have hzero : K * R ρ = 0 := by
      rw [hglob', zetaSqCompleted, two_xi_eq (by linarith) hρne1, hρ0, mul_zero,
        zero_pow two_ne_zero]
    have hre : ρ.re ≠ 1 / 2 := by intro h; linarith
    have hK : K ≠ 0 :=
      div_ne_zero (pow_ne_zero 2 (bigG_ne_zero lam (by norm_num)))
        (mul_ne_zero (WeilSpectral.atomPoly_ne_zero F n (by norm_num)) (atomQ_two_ne_zero hone hsum))
    have hRρ : R ρ ≠ 0 :=
      mul_ne_zero (WeilSpectral.atomPoly_ne_zero F n hre)
        (atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne hre))
    exact mul_ne_zero hK hRρ hzero

/-- **Half-integer spectral masses force `Λ` and RH** (atomic form, atoms at `|t| ≥ 1`).  If on
`Re s > 1`
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j (m_j/2)/((s−½)² + t_j²)`
with integers `m_j ≥ 0`, `t_j ≥ 1`, `Σ m_j/t_j² < ∞`, then `lam = Λ` on `n ≥ 2` and RH holds. -/
theorem half_integer_mass_rigidity (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j / 2) t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hP : ∀ s, WeilSpectral.atomPoly ∅ (fun _ => 0) s = 1 := fun s => by
    simp [WeilSpectral.atomPoly]
  refine vonMangoldt_and_riemannHypothesis_of_bigG_sq (F := ∅) (n := fun _ => 0) hone hsum hsl
    (by simp) (fun _ => rfl) fun s hs => ?_
  have hid' : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = atomicPairSeries (fun j => Real.pi * m j / ((2 : ℕ) : ℝ)) t s := by
    intro s hs; rw [hid s hs]; norm_num
  rw [hP, hP, one_mul, one_mul]
  exact WeilSpectral.bigG_pow_eq_mul_atomQ (k := 2) (by norm_num) hone hsum hsl hid' hs

/-- **Half-integer counting forces `Λ` and RH.**  A full-cone Weil-positive `lam` whose boundary
measure has half-integer counting, `2μ((a,b]) ∈ ℕ` for `a < b` in a set of full measure, is `Λ` on
`n ≥ 2`, and the Riemann hypothesis holds.  The atoms may lie anywhere. -/
theorem vonMangoldt_and_riemannHypothesis_of_half_integer_counting (hW : WeilPositiveFull lam)
    {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b →
      ∃ n : ℕ, (2 : ℝ≥0∞) * WeilSpectral.boundaryMeasure hW (Ioc a b) = n) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨F, n, m, t, hF, hn, hone, hsum, hG⟩ := WeilSpectral.bigG_pow_eq_of_fractional_counting hW
    (k := 2) (by norm_num) hY (by simpa using hcount)
  exact vonMangoldt_and_riemannHypothesis_of_bigG_sq hone hsum
    (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hF hn hG

end RHTower.HalfIntegerMassRigidity
