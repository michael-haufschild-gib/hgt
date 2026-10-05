import GaloisForLFunctions.RHTower.WeilZetaPowerConverse
import GaloisForLFunctions.RHTower.WeilHalfIntegerMassRigidity

/-!
# Rational-mass Weil producers are fake `ζᵏ` with the Riemann hypothesis

Let `lam` be full-cone Weil-positive with boundary measure `μ`, and `k ≥ 1` with
`k μ((a, b]) ∈ ℕ` for `a < b` in a set of full measure.

**Theorem** (`exists_zetaPowerDatum_of_fractional_counting`).  The Dirichlet series
`G = exp(k Σ_{n≥2} lam(n) n^{−s}/log n) = Σ g(n) n^{−s}` has `g(1) = 1` and is a degree-`k` datum
(`WeilZetaPower.ZetaPowerDatum`): its completion `E(s) = (s(s − 1)Γ_ℝ(s))^k G(s)` is entire of
finite order with `E(1 − s) = ±E(s)`.  Moreover `E(1) ≠ 0` (the pole of `G` at `s = 1` has order
exactly `k`, as `Γ_ℝ(1) = 1`), every zero of `E` lies on `Re s = ½`, and `−G'/G = k Σ lam(n) n^{−s}`,
i.e. `lam = (1/k)Λ_G`.

With the converse (`WeilZetaPower.weilPositiveFull_of_zetaPowerDatum`,
`WeilZetaPower.exists_natCast_eq_mul_boundaryMeasure`) this is an exact correspondence
(`weilPositiveFull_counting_iff_zetaPowerDatum`).

**Proof.**  `E = G̃^k = K P Q` with `G̃ = s(s − 1)Γ_ℝ(s) exp(Σ lam(n) n^{−s}/log n)`
(`WeilSpectral.bigG_pow_eq_of_fractional_counting`); `P` and `Q` vanish only on the critical
line and are symmetric, so `E` is entire with `E(1 − s) = (−1)^{deg P} E(s)` and zeros only on the
line.  `|P|` and `|Q|` increase in `σ ≥ ½`, so `|E(σ + it)| ≤ |G̃(2 + it)|^k` is bounded on
`½ ≤ σ ≤ 2`, by the functional equation on `−1 ≤ σ ≤ 2`, and the order-one envelope follows
(`CompletionGrowth.orderOneEnvelope_of_strip_bound`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace RHTower.WeilZetaPower

open IntegerMassRigidity HalfIntegerMassRigidity CompletionGrowth GaloisForLFunctions.HTGeometry

theorem lamC_eq_lamTwo (lam : ℕ → ℝ) : WeilHerglotz.lamC lam = lamTwo lam := by
  funext n
  simp only [WeilHerglotz.lamC, lamTwo]
  split_ifs <;> simp

/-- **Rational counting gives a fake `ζᵏ` with the Riemann hypothesis.** -/
theorem exists_zetaPowerDatum_of_fractional_counting {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {k : ℕ} (hk : 0 < k) {Y : Set ℝ} (hY : volume Yᶜ = 0)
    (hcount : ∀ a ∈ Y, ∀ b ∈ Y, a < b →
      ∃ n : ℕ, (k : ℝ≥0∞) * WeilSpectral.boundaryMeasure hW (Ioc a b) = n) :
    ∃ (g : ℕ → ℂ) (E : ℂ → ℂ), ZetaPowerDatum k g E ∧ g 1 = 1 ∧ E 1 ≠ 0 ∧
      (∀ s, E s = 0 → s.re = 1 / 2) ∧
      ∀ s : ℂ, 1 < s.re →
        deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s := by
  obtain ⟨F, n, m, t, hF, hn, hone, hsum, hG⟩ :=
    WeilSpectral.bigG_pow_eq_of_fractional_counting hW hk hY hcount
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
    fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  set K : ℂ := bigG lam 2 ^ k / (WeilSpectral.atomPoly F n 2 * atomQ m t 2) with hK
  set E : ℂ → ℂ := fun s => K * (WeilSpectral.atomPoly F n s * atomQ m t s) with hE
  set b : ℕ → ℂ := fun j => (k : ℂ) * lamLog lam j with hb
  have hb0 : b 0 = 0 := by simp [hb, lamLog_zero]
  have hb1 : b 1 = 0 := by simp [hb, lamLog_one]
  have hbsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable b s := fun s hs =>
    lseriesSummable_of_le (C := 2 * k) (fun j => by
      rw [hb, norm_mul, Complex.norm_natCast, mul_assoc]
      exact (mul_le_mul_of_nonneg_left (norm_lamLog_le lam j) (Nat.cast_nonneg k)).trans
        (le_of_eq (by ring))) hsl hs
  set g : ℕ → ℂ := dirichletExp b with hg
  have hLg : ∀ s : ℂ, 1 < s.re → LSeriesSummable g s ∧ LSeries g s = zetaOf lam s ^ k := by
    intro s hs
    obtain ⟨h1, h2⟩ := LSeries_dirichletExp hb0 hb1 (hbsum s hs)
    refine ⟨h1, ?_⟩
    rw [h2, zetaOf, ← Complex.exp_nat_mul]
    congr 1
    rw [show b = (k : ℂ) • lamLog lam from rfl, LSeries_smul]
  have hg1 : g 1 = 1 := dirichletExp_one hb0 hb1
  -- nonvanishing off the line
  have hP2 : WeilSpectral.atomPoly F n 2 ≠ 0 := WeilSpectral.atomPoly_ne_zero F n (by norm_num)
  have hK0 : K ≠ 0 := div_ne_zero (pow_ne_zero k (bigG_ne_zero lam (by norm_num)))
    (mul_ne_zero hP2 (atomQ_two_ne_zero hone hsum))
  have hnz : ∀ s : ℂ, s.re ≠ 1 / 2 → E s ≠ 0 := fun s hs =>
    mul_ne_zero hK0 (mul_ne_zero (WeilSpectral.atomPoly_ne_zero F n hs)
      (atomQ_ne_zero hone hsum (ne_atomAt_of_re_ne hs)))
  have hRH : ∀ s, E s = 0 → s.re = 1 / 2 := fun s h0 => by
    by_contra hs
    exact hnz s hs h0
  have hE1 : E 1 ≠ 0 := hnz 1 (by norm_num)
  -- the datum
  have hEd : Differentiable ℂ E :=
    ((WeilSpectral.differentiable_atomPoly F n).mul (differentiable_atomQ hone hsum)).const_mul K
  have hcomp : ∀ s : ℂ, 1 < s.re →
      E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s := by
    intro s hs
    rw [(hLg s hs).2, ← mul_pow]
    show K * (WeilSpectral.atomPoly F n s * atomQ m t s) = _
    rw [← hG s hs]
    rfl
  set ε : ℂ := (-1) ^ (∑ x ∈ F, n x) with hε
  have hsymε : ∀ s, E (1 - s) = ε * E s := fun s => by
    simp only [hE]
    rw [WeilSpectral.atomPoly_one_sub F n hF hn, atomQ_one_sub hone hsum]
    ring
  have hεn : ‖ε‖ = 1 := by simp [hε]
  -- the strip bound
  obtain ⟨B₀, hB₀, hB⟩ := exists_bound_bigG_two hsl
  have hright : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖E s‖ ≤ B₀ ^ k := by
    intro s h1 h2
    have hs : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
    have hmonoQ := norm_atomQ_le_two hone hsum s.im h1 h2
    have hmonoP := WeilSpectral.norm_atomPoly_le_two F n s.im h1 h2
    rw [← hs] at hmonoQ hmonoP
    have h2re : (1 : ℝ) < (2 + (s.im : ℂ) * I).re := by simp
    calc ‖E s‖ = ‖K‖ * (‖WeilSpectral.atomPoly F n s‖ * ‖atomQ m t s‖) := by
          simp only [hE]; rw [norm_mul, norm_mul]
      _ ≤ ‖K‖ * (‖WeilSpectral.atomPoly F n (2 + s.im * I)‖ * ‖atomQ m t (2 + s.im * I)‖) := by
          gcongr
      _ = ‖bigG lam (2 + s.im * I) ^ k‖ := by rw [hG _ h2re, norm_mul, norm_mul]
      _ = ‖bigG lam (2 + s.im * I)‖ ^ k := norm_pow _ _
      _ ≤ B₀ ^ k := pow_le_pow_left₀ (norm_nonneg _) (hB _) k
  have hstrip : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖E z‖ ≤ B₀ ^ k := by
    intro z h1 h2
    by_cases hz : 1 / 2 ≤ z.re
    · exact hright z hz h2
    · rw [not_le] at hz
      have h := hright (1 - z) (by simp; linarith) (by simp; linarith)
      rwa [hsymε, norm_mul, hεn, one_mul] at h
  obtain ⟨C, hC0, hC⟩ := orderOneEnvelope_of_strip_bound hεn hsymε ((hLg 2 (by norm_num)).1)
    (fun s hs => hcomp s (by linarith)) hstrip
  have hD : ZetaPowerDatum k g E :=
    { summable := fun s hs => (hLg s hs).1
      entire := hEd
      completion := hcomp
      functional_equation := by
        rcases neg_one_pow_eq_or ℂ (∑ x ∈ F, n x) with h | h
        · exact Or.inl fun s => by rw [hsymε, show ε = 1 from h, one_mul]
        · exact Or.inr fun s => by rw [hsymε, show ε = -1 from h, neg_one_mul]
      finite_order := finiteOrder_of_orderOne hC0 hC }
  refine ⟨g, E, hD, hg1, hE1, hRH, fun s hs => ?_⟩
  -- `−G'/G = k Σ lam(n) n^{−s}`
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : LSeries g =ᶠ[𝓝 s] fun z => zetaOf lam z ^ k := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact (hLg z hz).2
  have hd : HasDerivAt (fun z => zetaOf lam z ^ k)
      ((k : ℂ) * zetaOf lam s ^ (k - 1) * (zetaOf lam s * (-LSeries (lamTwo lam) s))) s :=
    (hasDerivAt_zetaOf hsl hs).pow k
  rw [hev.deriv_eq, hd.deriv, (hLg s hs).2, lamC_eq_lamTwo]
  rcases Nat.exists_eq_succ_of_ne_zero hk.ne' with ⟨j, rfl⟩
  push_cast
  rw [pow_succ]
  ring

/-- **The exact correspondence.**  For `k ≥ 1`, a real `lam` is full-cone Weil-positive with
`k μ_lam((a, b]) ∈ ℕ` for all `a < b` if and only if `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1` and
`lam = (1/k)Λ_G` for a degree-`k` datum `G` with `g(1) = 1`, `E(1) ≠ 0` and all zeros of `E` on
`Re s = ½`. -/
theorem weilPositiveFull_counting_iff_zetaPowerDatum {k : ℕ} (hk : 0 < k) (lam : ℕ → ℝ) :
    (∃ hW : WeilPositiveFull lam, ∀ a b : ℝ, a < b →
        ∃ n : ℕ, (k : ℝ≥0∞) * WeilSpectral.boundaryMeasure hW (Ioc a b) = n) ↔
      (∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) ∧
        ∃ (g : ℕ → ℂ) (E : ℂ → ℂ), ZetaPowerDatum k g E ∧ g 1 = 1 ∧ E 1 ≠ 0 ∧
          (∀ s, E s = 0 → s.re = 1 / 2) ∧
          ∀ s : ℂ, 1 < s.re →
            deriv (LSeries g) s = -(k : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s := by
  constructor
  · rintro ⟨hW, hcount⟩
    refine ⟨fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ, ?_⟩
    exact exists_zetaPowerDatum_of_fractional_counting hW hk (Y := univ) (by simp)
      fun a _ b _ hab => hcount a b hab
  · rintro ⟨hsl, g, E, hD, -, -, hRH, hΛ⟩
    exact ⟨weilPositiveFull_of_zetaPowerDatum hk hD hRH hsl hΛ, fun a b _ =>
      exists_natCast_eq_mul_boundaryMeasure hk hD hRH hsl hΛ a b⟩

end RHTower.WeilZetaPower
