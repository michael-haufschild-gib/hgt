import GaloisForLFunctions.ArithmeticPositiveDuality.IntegrableDefectsAtUnitDensityAreRigid

/-!
# Integrable functional-equation defects force additive saturation of the spectrum

Let `Σ_n a_n λ_n^{-s}` be a positive spectrum (`λ_0 = 1 < λ_1 < …`, masses `a_n ≥ 1`) whose theta
function satisfies the Riemann functional equation up to an integrable defect, with pole
coefficient `β` (residue `2β`). The Abel means `C_τ(ε) = ε Σ a_n e^{-2πλ_nε} cos(2πλ_nτ)` are then
the Bohr coefficients of a self-dual measure: `C_0 → β/π`, `C_{λ_m} → a_m/(2π)`, and `C_τ → 0` at every
`τ > 0` that is not a frequency (`IntegrableDefectsAtUnitDensityAreRigid`).

* **Gram inequality** (`abelCos_gram`). For every finite set `S` of indices and every `r`,
  `2r Σ_{m∈S} C_{λ_m} ≤ r² C_0 + Σ_{m,m'∈S} C_{λ_m − λ_{m'}}`: the squared modulus of
  `r − Σ_m e^{2πiλλ_m}` against the positive Abel measure.
* **Difference-free sets are small** (`sum_mass_le_of_differenceFree`, `card_le_of_differenceFree`).
  If no difference `λ_m − λ_{m'}` (`m, m' ∈ S`) is a frequency, then `Σ_{m∈S} a_m ≤ 2β √|S|`, hence
  `|S| ≤ 4β²`: among any `⌊4β²⌋ + 1` frequencies two differ by a frequency.
* **No defect without additive structure** (`not_integrable_defect_of_large_differenceFree`). A spectrum
  with difference-free subsets of every finite size has no integrable functional-equation defect,
  at any residue.

For the rational integers every difference is again a frequency, so the bound is empty there. For a
discrete Euler product the frequencies are the generalized integers, and the theorem says that an
integrable defect requires the generalized integers to be additively saturated: the independence
number of their difference graph is at most the squared residue. This is the first constraint on
integrable defects that holds at every residue, beyond the unit-density and integer-support cases.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### The Gram inequality -/

/-- `Σ_{m,m'} cos(θ_m − θ_{m'}) = (Σ cos θ_m)² + (Σ sin θ_m)²`. -/
theorem sum_sum_cos_sub (S : Finset ℕ) (θ : ℕ → ℝ) :
    ∑ m ∈ S, ∑ m' ∈ S, Real.cos (θ m - θ m') =
      (∑ m ∈ S, Real.cos (θ m)) ^ 2 + (∑ m ∈ S, Real.sin (θ m)) ^ 2 := by
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m' _ => Real.cos_sub _ _

/-- The pointwise Gram inequality `2r Σ cos θ_m ≤ r² + Σ_{m,m'} cos(θ_m − θ_{m'})`. -/
theorem two_mul_sum_cos_le (S : Finset ℕ) (θ : ℕ → ℝ) (r : ℝ) :
    2 * r * ∑ m ∈ S, Real.cos (θ m) ≤ r ^ 2 + ∑ m ∈ S, ∑ m' ∈ S, Real.cos (θ m - θ m') := by
  rw [sum_sum_cos_sub]
  nlinarith [sq_nonneg (r - ∑ m ∈ S, Real.cos (θ m)), sq_nonneg (∑ m ∈ S, Real.sin (θ m))]

/-- **The Gram inequality for the positive Abel measure.** -/
theorem abelCos_gram {a lam : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2) (S : Finset ℕ) (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * r * ∑ m ∈ S, abelCos a lam (lam m) ε ≤
      r ^ 2 * abelCos a lam 0 ε + ∑ m ∈ S, ∑ m' ∈ S, abelCos a lam (lam m - lam m') ε := by
  set F : ℕ → ℝ := fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε)) with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => mul_nonneg (ha0 n) (Real.exp_pos _).le
  set X : ℝ → ℝ := fun τ => ∑' n, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
    Real.cos (2 * Real.pi * lam n * τ) with hX
  have hXs : ∀ τ, HasSum (fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      Real.cos (2 * Real.pi * lam n * τ)) (X τ) := fun τ =>
    (summable_abelCos hlam ha0 ha τ hε).hasSum
  have h0 : HasSum (fun n => r ^ 2 * (a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      Real.cos (2 * Real.pi * lam n * 0))) (r ^ 2 * X 0) := (hXs 0).mul_left _
  have h1 : HasSum (fun n => ∑ m ∈ S, ∑ m' ∈ S, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      Real.cos (2 * Real.pi * lam n * (lam m - lam m')))
      (∑ m ∈ S, ∑ m' ∈ S, X (lam m - lam m')) :=
    hasSum_sum fun m _ => hasSum_sum fun m' _ => hXs (lam m - lam m')
  have h2 : HasSum (fun n => 2 * r * ∑ m ∈ S, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
      Real.cos (2 * Real.pi * lam n * lam m)) (2 * r * ∑ m ∈ S, X (lam m)) :=
    (hasSum_sum fun m _ => hXs (lam m)).mul_left _
  have hG0 : 0 ≤ r ^ 2 * X 0 + ∑ m ∈ S, ∑ m' ∈ S, X (lam m - lam m') -
      2 * r * ∑ m ∈ S, X (lam m) := by
    refine ((h0.add h1).sub h2).nonneg fun n => ?_
    have hp := two_mul_sum_cos_le S (fun m => 2 * Real.pi * lam n * lam m) r
    simp only [← mul_sub] at hp
    have hFn := hF0 n
    have hexp : ∑ m ∈ S, ∑ m' ∈ S, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
          Real.cos (2 * Real.pi * lam n * (lam m - lam m')) =
        F n * ∑ m ∈ S, ∑ m' ∈ S, Real.cos (2 * Real.pi * lam n * (lam m - lam m')) := by
      simp only [hF, Finset.mul_sum]
    have hexp2 : ∑ m ∈ S, a n * Real.exp (-(2 * Real.pi * lam n * ε)) *
          Real.cos (2 * Real.pi * lam n * lam m) =
        F n * ∑ m ∈ S, Real.cos (2 * Real.pi * lam n * lam m) := by
      simp only [hF, Finset.mul_sum]
    simp only [mul_zero, Real.cos_zero, mul_one]
    rw [hexp, hexp2]
    have := mul_le_mul_of_nonneg_left hp hFn
    have hF' : F n = a n * Real.exp (-(2 * Real.pi * lam n * ε)) := rfl
    rw [← hF']
    nlinarith
  have hab : ∀ τ, abelCos a lam τ ε = ε * X τ := fun τ => rfl
  simp only [hab]
  have e1 : ∑ x ∈ S, ∑ x_1 ∈ S, ε * X (lam x - lam x_1) =
      ε * ∑ m ∈ S, ∑ m' ∈ S, X (lam m - lam m') := by simp only [Finset.mul_sum]
  rw [e1, ← Finset.mul_sum]
  nlinarith [mul_nonneg hε.le hG0]

/-! ### Separation of a non-frequency -/

/-- The frequencies of a positive spectrum with finite `Σ a_n/λ_n²` and `a_n ≥ 1` tend to infinity. -/
theorem tendsto_lam_atTop {a lam : ℕ → ℝ} (hlam : ∀ n, 1 ≤ lam n) (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) : Tendsto lam atTop atTop := by
  have hs : Summable fun n => 1 / lam n ^ 2 :=
    ha.of_nonneg_of_le (fun n => by have := hlam n; positivity)
      fun n => div_le_div_of_nonneg_right (ha1 n) (by have := hlam n; positivity)
  have h0 := hs.tendsto_atTop_zero
  rw [tendsto_atTop]
  intro b
  have hb : 0 < 1 / (max b 1 + 1) ^ 2 := by positivity
  filter_upwards [h0.eventually (gt_mem_nhds hb)] with n hn
  have hl := hlam n
  by_contra hlt
  push Not at hlt
  have h1 : lam n ^ 2 < (max b 1 + 1) ^ 2 := by
    have : lam n < max b 1 + 1 := by linarith [le_max_left b 1]
    nlinarith
  have h2 : 1 / (max b 1 + 1) ^ 2 < 1 / lam n ^ 2 :=
    one_div_lt_one_div_of_lt (by positivity) h1
  linarith

/-- **A positive non-frequency is separated** from the spectrum in the relative sense of the gap
lemma: `c λ_n ≤ |λ_n − τ|` for all `n`. -/
theorem exists_sep_of_not_mem_range {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n)
    (htend : Tendsto lam atTop atTop) {τ : ℝ} (hτ : 0 < τ) (hnot : τ ∉ Set.range lam) :
    ∃ c > 0, ∀ n, c * lam n ≤ |lam n - τ| := by
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp htend (2 * τ)).exists_forall_of_atTop
  set f : ℕ → ℝ := fun n => |lam n - τ| / lam n with hf
  have hfpos : ∀ n, 0 < f n := fun n => by
    have hne : lam n - τ ≠ 0 := fun h => hnot ⟨n, by linarith⟩
    exact div_pos (abs_pos.mpr hne) (hpos n)
  set c₁ := (Finset.range (N + 1)).inf' ⟨0, by simp⟩ f with hc₁
  have hc₁pos : 0 < c₁ := (Finset.lt_inf'_iff _).mpr fun n _ => hfpos n
  refine ⟨min c₁ (1 / 2), lt_min hc₁pos (by norm_num), fun n => ?_⟩
  rcases le_or_gt n N with hn | hn
  · have hle : c₁ ≤ f n := Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
    have := hpos n
    calc min c₁ (1 / 2) * lam n ≤ f n * lam n :=
          mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hle) this.le
      _ = |lam n - τ| := by rw [hf]; field_simp
  · have h2 := hN n hn.le
    have := hpos n
    rw [abs_of_nonneg (by linarith)]
    calc min c₁ (1 / 2) * lam n ≤ 1 / 2 * lam n :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) this.le
      _ ≤ lam n - τ := by linarith

/-! ### Difference-free sets -/

theorem abelCos_neg (a lam : ℕ → ℝ) (τ ε : ℝ) : abelCos a lam (-τ) ε = abelCos a lam τ ε := by
  unfold abelCos
  congr 1
  refine tsum_congr fun n => ?_
  rw [mul_neg, Real.cos_neg]

/-- **Difference-free sets carry little mass.** Under an integrable functional-equation defect with
pole coefficient `β`, a set `S` of frequencies whose positive differences are not frequencies has
`Σ_{m∈S} a_m ≤ 2β √|S|`. -/
theorem sum_mass_le_of_differenceFree {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    (S : Finset ℕ) (hS : ∀ m ∈ S, ∀ m' ∈ S, lam m' < lam m → lam m - lam m' ∉ Set.range lam) :
    ∑ m ∈ S, a m ≤ 2 * β * Real.sqrt S.card := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_trans zero_le_one (ha1 n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have htend := tendsto_lam_atTop hlam ha1 ha
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  -- atoms
  have hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0) (𝓝 (a m / (2 * Real.pi))) := by
    intro m
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
    have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
      (hpos m) hc hsep
    have hh := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos m) hres
    have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
      rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    rwa [hre] at hh
  -- gaps
  have hgap : ∀ τ : ℝ, 0 < τ → τ ∉ Set.range lam →
      Tendsto (abelCos a lam τ) (𝓝[>] 0) (𝓝 0) := by
    intro τ hτ hnot
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_not_mem_range hpos htend hτ hnot
    have hres := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ)) hlam haC hτ.le hc hsep
    simpa using abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL hτ hres
  -- pairs
  have hpair : ∀ m ∈ S, ∀ m' ∈ S, Tendsto (abelCos a lam (lam m - lam m')) (𝓝[>] 0)
      (𝓝 (if m = m' then β / Real.pi else 0)) := by
    intro m hm m' hm'
    by_cases hmm : m = m'
    · subst hmm
      simpa using hC0
    · rw [if_neg hmm]
      rcases lt_or_gt_of_ne (hmono.injective.ne hmm) with hlt | hgt
      · rw [show lam m - lam m' = -(lam m' - lam m) by ring]
        have heq : abelCos a lam (-(lam m' - lam m)) = abelCos a lam (lam m' - lam m) :=
          funext fun ε => abelCos_neg a lam _ ε
        rw [heq]
        exact hgap _ (by linarith) (hS m' hm' m hm hlt)
      · exact hgap _ (by linarith) (hS m hm m' hm' hgt)
  have hsumpair : Tendsto (fun ε => ∑ m ∈ S, ∑ m' ∈ S, abelCos a lam (lam m - lam m') ε)
      (𝓝[>] 0) (𝓝 (∑ m ∈ S, ∑ m' ∈ S, if m = m' then β / Real.pi else 0)) :=
    tendsto_finsetSum _ fun m hm => tendsto_finsetSum _ fun m' hm' => hpair m hm m' hm'
  have hdiag : ∑ m ∈ S, ∑ m' ∈ S, (if m = m' then β / Real.pi else 0) = S.card * (β / Real.pi) := by
    simp [Finset.sum_ite_eq]
  rw [hdiag] at hsumpair
  have hsumatom : Tendsto (fun ε => ∑ m ∈ S, abelCos a lam (lam m) ε) (𝓝[>] 0)
      (𝓝 (∑ m ∈ S, a m / (2 * Real.pi))) := tendsto_finsetSum _ fun m _ => hatom m
  set K : ℝ := (S.card : ℝ) with hK
  set r : ℝ := Real.sqrt K with hr
  have hlim := le_of_tendsto_of_tendsto ((hsumatom.const_mul (2 * r)))
    ((hC0.const_mul (r ^ 2)).add hsumpair)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using abelCos_gram ha0 hlam ha S r hε)
  -- `2r Σ a_m/(2π) ≤ (r² + K) β/π`, with `r² = K`
  have hrK : r ^ 2 = K := Real.sq_sqrt (by positivity)
  rw [hrK, ← Finset.sum_div] at hlim
  have hπ := Real.pi_pos
  have h1 : r * ∑ m ∈ S, a m ≤ 2 * K * β := by
    have : 2 * r * ((∑ m ∈ S, a m) / (2 * Real.pi)) = r * (∑ m ∈ S, a m) / Real.pi := by
      field_simp
    rw [this] at hlim
    have h2 : K * (β / Real.pi) + K * (β / Real.pi) = 2 * K * β / Real.pi := by ring
    rw [h2, div_le_div_iff_of_pos_right hπ] at hlim
    exact hlim
  rcases (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card).lt_or_eq with hK0 | hK0
  · have hr0 : 0 < r := Real.sqrt_pos.mpr (by rw [hK]; exact hK0)
    have hKr : K = r * r := by rw [← sq, hrK]
    rw [hKr] at h1
    have : ∑ m ∈ S, a m ≤ 2 * r * β := by nlinarith
    linarith
  · have hS0 : S = ∅ := by
      rw [eq_comm, Nat.cast_eq_zero, Finset.card_eq_zero] at hK0; exact hK0
    have hr0 : r = 0 := by rw [hr, hK, ← hK0, Real.sqrt_zero]
    simp [hS0, hr0]

/-- **Difference-free sets are small.** `|S| ≤ 4β²` for every difference-free set of frequencies. -/
theorem card_le_of_differenceFree {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    (S : Finset ℕ) (hS : ∀ m ∈ S, ∀ m' ∈ S, lam m' < lam m → lam m - lam m' ∉ Set.range lam) :
    (S.card : ℝ) ≤ 4 * β ^ 2 := by
  have h := sum_mass_le_of_differenceFree hmono hlam0 ha1 ha hgm hgb hgi hθ S hS
  have hK : (S.card : ℝ) ≤ ∑ m ∈ S, a m := by
    have := Finset.sum_le_sum fun m (_ : m ∈ S) => ha1 m
    simpa using this
  have hs := Real.sqrt_nonneg (S.card : ℝ)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  -- `s² ≤ 2β s` with `s = √|S|`, hence `s ≤ 2β` or `s = 0`
  have h2 : Real.sqrt S.card * Real.sqrt S.card ≤ 2 * β * Real.sqrt S.card := by nlinarith
  rcases hs.lt_or_eq with hs0 | hs0
  · have h3 : Real.sqrt S.card ≤ 2 * β := le_of_mul_le_mul_right (by linarith) hs0
    nlinarith
  · rw [← hs0] at hsq
    nlinarith

/-- **No integrable defect without additive structure.** A positive spectrum that contains
difference-free sets of every finite size has no integrable functional-equation defect, at any
pole residue. -/
theorem not_integrable_defect_of_large_differenceFree {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha1 : ∀ n, 1 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2)
    (hfree : ∀ K : ℕ, ∃ S : Finset ℕ, K ≤ S.card ∧
      ∀ m ∈ S, ∀ m' ∈ S, lam m' < lam m → lam m - lam m' ∉ Set.range lam)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) : False := by
  obtain ⟨K, hK⟩ := exists_nat_gt (4 * β ^ 2)
  obtain ⟨S, hSK, hS⟩ := hfree K
  have h := card_le_of_differenceFree hmono hlam0 ha1 ha hgm hgb hgi hθ S hS
  have : (K : ℝ) ≤ S.card := by exact_mod_cast hSK
  linarith

end GaloisForLFunctions.ArithmeticPositiveDuality
