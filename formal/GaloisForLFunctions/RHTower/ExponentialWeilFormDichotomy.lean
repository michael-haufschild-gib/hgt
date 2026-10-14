import GaloisForLFunctions.RHTower.WeilLagFunction
import GaloisForLFunctions.RHTower.CesaroSignRecurrence
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Exponential Weil forms: a multiplier-agnostic positivity dichotomy

For values `A_ρ, B_ρ` attached to the Xi zeros put

`F(z) = Σ_ρ e^{z A_ρ + z̄ B_ρ}/(ρ(1−ρ))`   (`expWeilForm`).

With `ĝ_z(s) = e^{z A(s)}/s` and `B_ρ = conj A(1 − ρ̄)` this is the Weil form `Σ_ρ ĝ_z(ρ) ĝ_z^♯(ρ)`.

**Negativity** (`exists_re_expWeilForm_neg`).  If `min(|A_ρ|, |B_ρ|) ≤ 1` for every zero, only
finitely many zeros have `|A_ρ + conj B_ρ| > 1`, and one zero has `|A_ρ + conj B_ρ| > 2`, then
`Re F(z) < 0` for some `z`.
* `z A + z̄ B = Re(z a) + i Im(z b)` with `a = A + conj B`, `b = A − conj B`: the modulus of a term
  sees only `a`, its phase only `b`; and `b ≠ 0` once `|a| > 2`.
* Tilt the top direction `ā*/M` by a generic `1 + is` and scale it: every maximizer of the modulus
  then carries a nonzero phase of size below `1`.
* On `z = nω` the form is a dominant power sum; its real symmetrisation is a unit pencil with
  positive-real-part fibre coefficients, uniformly negative arbitrarily late
  (`exists_arbitrarily_late_re_tsum_normalizedExponentialPencil_lt_neg_of_dominantFinset`).

**Dichotomy** (`riemannHypothesis_iff_frequently_expWeilForm_nonneg`).  For a family `A_N, B_N`
with these bounds, `B_N = conj A_N` under RH, and some `|a_ρ(N)| > 2` on every large `N` off RH:

`RH ⟺ ∃ᶠ N, ∀ z, Re F_N(z) ≥ 0 ⟺ ∀ N, ∀ z, Re F_N(z) ≥ 0`.

**The pole shadow** (`riemannHypothesis_iff_frequently_poleShadowWeilForm_nonneg`).  The prime-free
multiplier `m_N(s) = N^{s−½}/(s+1)²` is such a family: for a zero right of the line
`|m_N(ρ)| = N^{Re ρ−½}/|ρ+1|² → ∞`.  So

`RH ⟺ ∃ᶠ N, ∀ z ∈ ℂ, Re Σ_ρ exp(z N^{ρ−½}/(ρ+1)² + z̄ N^{½−ρ}/(2−ρ)²)/(ρ(1−ρ)) ≥ 0`.

Each single `N` is a certificate: positivity at `N ≥ 2` forces
`Re ρ − ½ ≤ log(3|ρ+1|²)/log N` for every zero right of the line
(`re_sub_half_le_of_poleShadowWeilForm_nonneg`).

Arithmetic shell multipliers `U_s(N)/(s+1)²` detect off-line zeros through their prime number
theorem main term, which is this pole shadow; the dichotomy does not see the primes.
-/

open Complex Filter
open scoped ComplexConjugate Topology

namespace RHTower

noncomputable section

/-- The exponential Weil form `F(z) = Σ_ρ e^{z A_ρ + z̄ B_ρ}/(ρ(1−ρ))`. -/
def expWeilForm (A B : XiZeroCopy → ℂ) (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, cexp (z * A q + conj z * B q) * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))

/-- `ω A + ω̄ B = Re(ω (A + conj B)) + i Im(ω (A − conj B))`. -/
theorem mul_add_conj_mul_eq (ω A B : ℂ) :
    ω * A + conj ω * B = (((ω * (A + conj B)).re : ℝ) : ℂ) + (((ω * (A - conj B)).im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- `Re(1/(ρ(1−ρ))) > 0` for every zero in the strip. -/
theorem re_one_div_xiZeroCopy_pos (q : XiZeroCopy) :
    0 < (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hz : ((q.1 : ℂ) * (1 - (q.1 : ℂ))).re =
      (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) + (q.1 : ℂ).im ^ 2 := by
    simp [Complex.mul_re]; ring
  have hpos : 0 < ((q.1 : ℂ) * (1 - (q.1 : ℂ))).re := by
    rw [hz]; nlinarith [sq_nonneg (q.1 : ℂ).im]
  rw [one_div, Complex.inv_re]
  refine div_pos hpos (Complex.normSq_pos.mpr fun h => ?_)
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

theorem summable_expWeilForm_terms {A B : XiZeroCopy → ℂ} {C : ℝ}
    (hbd : ∀ q, ‖A q‖ ≤ C ∧ ‖B q‖ ≤ C) (z : ℂ) :
    Summable fun q : XiZeroCopy =>
      cexp (z * A q + conj z * B q) * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left
    (Real.exp (‖z‖ * (2 * C)))) fun q => ?_
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  obtain ⟨hA, hB⟩ := hbd q
  calc (z * A q + conj z * B q).re ≤ ‖z * A q + conj z * B q‖ := Complex.re_le_norm _
    _ ≤ ‖z‖ * ‖A q‖ + ‖z‖ * ‖B q‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
    _ ≤ ‖z‖ * (2 * C) := by nlinarith [norm_nonneg z]

/-- **Positivity under conjugate symmetry and RH.** -/
theorem re_expWeilForm_nonneg_of_riemannHypothesis {A B : XiZeroCopy → ℂ} {C : ℝ}
    (hbd : ∀ q, ‖A q‖ ≤ C ∧ ‖B q‖ ≤ C) (hRH : RiemannHypothesis)
    (hsym : ∀ q, B q = conj (A q)) (z : ℂ) : 0 ≤ (expWeilForm A B z).re := by
  rw [expWeilForm, Complex.re_tsum (summable_expWeilForm_terms hbd z)]
  refine tsum_nonneg fun q => ?_
  have hhalf := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hrefl : 1 - (q.1 : ℂ) = conj (q.1 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hhalf]; norm_num
    · simp
  rw [hsym q, hrefl, ← map_mul, Complex.add_conj, Complex.mul_conj,
    ← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  exact mul_nonneg (Real.exp_pos _).le (div_nonneg zero_le_one (Complex.normSq_nonneg _))

/-- A phase part vanishes only at modulus at most `2`. -/
theorem sub_conj_ne_zero_of_two_lt {A B : ℂ} (hmin : ‖A‖ ≤ 1 ∨ ‖B‖ ≤ 1)
    (h : 2 < ‖A + conj B‖) : A - conj B ≠ 0 := by
  intro hb
  rw [sub_eq_zero] at hb
  have hn : ‖A‖ = ‖B‖ := by rw [hb, Complex.norm_conj]
  rw [← hb, ← two_mul, norm_mul] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2] at h
  rcases hmin with h1 | h1 <;> linarith

/-- **A loud modulus part with a nonzero phase makes the exponential Weil form negative.**  If only
finitely many zeros have `|A_ρ + conj B_ρ| > L`, each of them has `A_ρ ≠ conj B_ρ`, and there is
one, then `Re F(z) < 0` for some `z`. -/
theorem exists_re_expWeilForm_neg_of_threshold {A B : XiZeroCopy → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hfin : {q : XiZeroCopy | L < ‖A q + conj (B q)‖}.Finite)
    (hbne : ∀ q, L < ‖A q + conj (B q)‖ → A q - conj (B q) ≠ 0)
    {q₁ : XiZeroCopy} (hq₁ : L < ‖A q₁ + conj (B q₁)‖) :
    ∃ z : ℂ, (expWeilForm A B z).re < 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : XiZeroCopy → ℂ, a = fun q => A q + conj (B q) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : XiZeroCopy → ℂ, b = fun q => A q - conj (B q) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have haq : ∀ q, a q = A q + conj (B q) := fun q => by rw [ha]
  have hbq : ∀ q, b q = A q - conj (B q) := fun q => by rw [hb]
  have hwq : ∀ q, w q = 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := fun q => by rw [hw]
  -- the loud set and the top modulus
  obtain ⟨F, hF⟩ : ∃ F : Finset XiZeroCopy, F = hfin.toFinset := ⟨_, rfl⟩
  have hmemF : ∀ q, q ∈ F ↔ L < ‖a q‖ := by
    intro q; rw [hF, Set.Finite.mem_toFinset, haq]; rfl
  have hq₁F : q₁ ∈ F := (hmemF q₁).mpr (by rw [haq]; exact hq₁)
  have hnotF : ∀ q, q ∉ F → ‖a q‖ ≤ L := fun q hq => by
    by_contra h; push Not at h; exact hq ((hmemF q).mpr h)
  obtain ⟨qs, hqsF, hqsmax⟩ := F.exists_max_image (fun q => ‖a q‖) ⟨q₁, hq₁F⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖a qs‖ := ⟨_, rfl⟩
  have hML : L < M := by
    have h1 : ‖a q₁‖ ≤ ‖a qs‖ := hqsmax q₁ hq₁F
    rw [haq q₁] at h1
    rw [hM]; linarith
  have hM0 : 0 < M := by linarith
  -- the top direction
  obtain ⟨ωs, hωs⟩ : ∃ ωs : ℂ, ωs = conj (a qs) / (M : ℂ) := ⟨_, rfl⟩
  have hωsa : ωs * a qs = (M : ℂ) := by
    have hsq : conj (a qs) * a qs = (M : ℂ) ^ 2 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hM]; push_cast; ring
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    rw [hωs, div_mul_eq_mul_div, hsq]
    field_simp
  have hωsn : ‖ωs‖ = 1 := by
    rw [hωs, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hM0.le, ← hM,
      div_self hM0.ne']
  -- the tilt `s`
  obtain ⟨β, hβ⟩ : ∃ β : XiZeroCopy → ℂ, β = fun q => ωs * b q := ⟨_, rfl⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = min 1 ((M ^ 2 - L ^ 2) / (L ^ 2 + 1)) := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀]; exact lt_min one_pos (div_pos (by nlinarith) (by positivity))
  obtain ⟨s, ⟨hs0, hs1⟩, hsB⟩ := (Set.Ioo_infinite hε₀0).exists_notMem_finset
    (F.image fun q => -(β q).im / (β q).re)
  have hs1' : s < 1 := hs1.trans_le (hε₀ ▸ min_le_left _ _)
  have hs2 : s < (M ^ 2 - L ^ 2) / (L ^ 2 + 1) := hs1.trans_le (hε₀ ▸ min_le_right _ _)
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : ℂ, ω₀ = ωs * (1 + (s : ℂ) * I) := ⟨_, rfl⟩
  have hω₀a : (ω₀ * a qs).re = M := by
    rw [hω₀, mul_right_comm, hωsa]; simp
  have hω₀n2 : ‖ω₀‖ ^ 2 = 1 + s ^ 2 := by
    rw [hω₀, norm_mul, hωsn, one_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  have hω₀L : ‖ω₀‖ * L < M := by
    have h1 : s * (L ^ 2 + 1) < M ^ 2 - L ^ 2 := by rwa [lt_div_iff₀ (by positivity)] at hs2
    have hss : s ^ 2 ≤ s := by nlinarith
    have h3 : s ^ 2 * L ^ 2 ≤ s * L ^ 2 := mul_le_mul_of_nonneg_right hss (sq_nonneg L)
    have h4 : s * L ^ 2 ≤ s * (L ^ 2 + 1) := by nlinarith
    have h2 : (‖ω₀‖ * L) ^ 2 < M ^ 2 := by
      rw [mul_pow, hω₀n2]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hM0.le h2
  -- the maximizers of `Re(ω₀ a_ρ)`
  obtain ⟨qm, hqmF, hqmmax⟩ := F.exists_max_image (fun q => (ω₀ * a q).re) ⟨q₁, hq₁F⟩
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = (ω₀ * a qm).re := ⟨_, rfl⟩
  have hMr₀ : M ≤ r₀ := by rw [hr₀, ← hω₀a]; exact hqmmax qs hqsF
  obtain ⟨D, hD⟩ : ∃ D : Finset XiZeroCopy, D = F.filter (fun q => (ω₀ * a q).re = r₀) :=
    ⟨_, rfl⟩
  have hmemD : ∀ q, q ∈ D ↔ q ∈ F ∧ (ω₀ * a q).re = r₀ := fun q => by
    rw [hD, Finset.mem_filter]
  have hqmD : qm ∈ D := (hmemD qm).mpr ⟨hqmF, hr₀.symm⟩
  have hreF : ∀ q, (ω₀ * a q).re ≤ ‖ω₀‖ * ‖a q‖ := fun q =>
    (Complex.re_le_norm _).trans (norm_mul _ _).le
  have hlt : ∀ q, q ∉ D → (ω₀ * a q).re < r₀ := by
    intro q hq
    by_cases hqF : q ∈ F
    · have h1 : (ω₀ * a q).re ≤ r₀ := hr₀ ▸ hqmmax q hqF
      have h2 : (ω₀ * a q).re ≠ r₀ := fun h => hq ((hmemD q).mpr ⟨hqF, h⟩)
      exact lt_of_le_of_ne h1 h2
    · have h2 : ‖ω₀‖ * ‖a q‖ ≤ ‖ω₀‖ * L := mul_le_mul_of_nonneg_left (hnotF q hqF) (norm_nonneg _)
      linarith [hreF q]
  have hDbig : ∀ q ∈ D, L < ‖a q‖ := by
    intro q hq
    by_contra h
    push Not at h
    have h1 : ‖ω₀‖ * ‖a q‖ ≤ ‖ω₀‖ * L := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    linarith [hreF q, ((hmemD q).mp hq).2]
  have hDphase : ∀ q ∈ D, (ω₀ * b q).im ≠ 0 := by
    intro q hq
    have hqF := ((hmemD q).mp hq).1
    have hb0 : b q ≠ 0 := by
      rw [hbq]; exact hbne q (by rw [← haq]; exact hDbig q hq)
    have hωs0 : ωs ≠ 0 := fun h => by rw [h, norm_zero] at hωsn; exact zero_ne_one hωsn
    have hβ0 : β q ≠ 0 := by rw [hβ]; exact mul_ne_zero hωs0 hb0
    intro him
    have e : (ω₀ * b q).im = (β q).im + s * (β q).re := by
      rw [show ω₀ * b q = β q * (1 + (s : ℂ) * I) by rw [hω₀, hβ]; ring]
      simp [Complex.mul_im]; ring
    rw [e] at him
    by_cases hre : (β q).re = 0
    · apply hβ0
      apply Complex.ext
      · simpa using hre
      · simp only [Complex.zero_im]; rw [hre, mul_zero, add_zero] at him; exact him
    · apply hsB
      rw [Finset.mem_image]
      exact ⟨q, hqF, by field_simp; linarith⟩
  -- the scale `ε`
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (1 + ∑ q ∈ D, |(ω₀ * b q).im|) := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ q ∈ D, |(ω₀ * b q).im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεph : ∀ q ∈ D, |ε * (ω₀ * b q).im| < 1 := by
    intro q hq
    have h1 : |(ω₀ * b q).im| ≤ ∑ q ∈ D, |(ω₀ * b q).im| :=
      Finset.single_le_sum (f := fun q => |(ω₀ * b q).im|) (fun _ _ => abs_nonneg _) hq
    rw [abs_mul, abs_of_pos hε0, hε, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  -- the power-sum bases
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = (ε : ℂ) * ω₀ := ⟨_, rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : XiZeroCopy → ℂ, ξ = fun q => cexp (ω * A q + conj ω * B q) := ⟨_, rfl⟩
  have hξeq : ∀ q, ξ q = cexp (((ε * (ω₀ * a q).re : ℝ) : ℂ) +
      ((ε * (ω₀ * b q).im : ℝ) : ℂ) * I) := by
    intro q
    rw [hξ]; dsimp only
    rw [mul_add_conj_mul_eq, hω, haq, hbq, mul_assoc, mul_assoc,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.exp (ε * r₀) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ Real.exp_pos _
  have hξn : ∀ q, ‖ξ q‖ = Real.exp (ε * (ω₀ * a q).re) := by
    intro q; rw [hξeq, Complex.norm_exp]; simp
  have hdom : ∀ q ∈ D, ‖ξ q‖ = r := fun q hq => by
    rw [hξn, hr, ((hmemD q).mp hq).2]
  have hsub : ∀ q ∉ D, ‖ξ q‖ < r := fun q hq => by
    rw [hξn, hr]; exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (hlt q hq) hε0)
  have hξr : ∀ q, ‖ξ q / (r : ℂ)‖ ≤ 1 := by
    intro q
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr0.le, div_le_one hr0]
    by_cases hq : q ∈ D
    · exact (hdom q hq).le
    · exact (hsub q hq).le
  have hnoOne : ∀ q ∈ D, ξ q / (r : ℂ) ≠ 1 := by
    intro q hq h
    have hunit : ξ q / (r : ℂ) = cexp (((ε * (ω₀ * b q).im : ℝ) : ℂ) * I) := by
      rw [hξeq, Complex.exp_add, hr, ((hmemD q).mp hq).2, Complex.ofReal_exp]
      field_simp
    rw [hunit, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hx : ε * (ω₀ * b q).im = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa using this
    have hph := hεph q hq
    rw [hx] at hph
    have hn0 : n = 0 := by
      by_contra hn0
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hph
      nlinarith [Real.pi_gt_three]
    rw [hn0, Int.cast_zero, zero_mul, mul_eq_zero] at hx
    exact hDphase q hq (hx.resolve_left hε0.ne')
  -- the real symmetrisation as a dominant pencil
  obtain ⟨c', hc'⟩ : ∃ c' : XiZeroCopy ⊕ XiZeroCopy → ℂ,
      c' = Sum.elim w (fun q => conj (w q)) := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : XiZeroCopy ⊕ XiZeroCopy → ℂ,
      b' = Sum.elim ξ (fun q => conj (ξ q)) := ⟨_, rfl⟩
  have hwsum : Summable w := hw ▸ summable_inv_mul_one_sub
  have hc'sum : Summable c' := by
    rw [hc']
    refine Summable.sum _ hwsum ?_
    refine Summable.of_norm_bounded hwsum.norm fun q => ?_
    simp
  have hrere : ∀ i, 0 < (c' i).re := by
    intro i
    rcases i with q | q
    · rw [hc']; simp only [Sum.elim_inl]; rw [hwq]; exact re_one_div_xiZeroCopy_pos q
    · rw [hc']; simp only [Sum.elim_inr, Complex.conj_re]; rw [hwq]
      exact re_one_div_xiZeroCopy_pos q
  have hconjr : ∀ q, conj (ξ q) / (r : ℂ) = conj (ξ q / (r : ℂ)) := fun q => by
    rw [map_div₀, Complex.conj_ofReal]
  obtain ⟨δ, hδ, hlate⟩ :=
    exists_arbitrarily_late_re_tsum_normalizedExponentialPencil_lt_neg_of_dominantFinset
    c' b' hc'sum (D.disjSum D) hr0
    (by
      intro i hi
      rcases i with q | q
      · rw [hb']; exact hdom q (Finset.inl_mem_disjSum.mp hi)
      · rw [hb']; simp only [Sum.elim_inr, Complex.norm_conj]
        exact hdom q (Finset.inr_mem_disjSum.mp hi))
    (by
      intro i hi
      rcases i with q | q
      · rw [hb']; exact hsub q fun h => hi (Finset.inl_mem_disjSum.mpr h)
      · rw [hb']; simp only [Sum.elim_inr, Complex.norm_conj]
        exact hsub q fun h => hi (Finset.inr_mem_disjSum.mpr h))
    (by
      intro i hi
      rcases i with q | q
      · rw [hb']; exact hnoOne q (Finset.inl_mem_disjSum.mp hi)
      · rw [hb']; simp only [Sum.elim_inr]
        rw [hconjr]
        intro h
        apply hnoOne q (Finset.inr_mem_disjSum.mp hi)
        rw [← Complex.conj_conj (ξ q / (r : ℂ)), h, map_one])
    (by
      refine ⟨b' (Sum.inl qm) / (r : ℂ), Finset.mem_image_of_mem _
        (Finset.inl_mem_disjSum.mpr hqmD), fun h0 => ?_⟩
      have hre := congrArg Complex.re h0
      rw [finiteExponentialFiberCoefficient, Complex.re_sum, Complex.zero_re] at hre
      refine (Finset.sum_pos (fun i _ => hrere i) ⟨Sum.inl qm, ?_⟩).ne' hre
      rw [Finset.mem_filter]
      exact ⟨Finset.inl_mem_disjSum.mpr hqmD, rfl⟩)
    (by
      intro n
      rw [finiteExponentialPencil, Finset.sum_disjSum, ← Finset.sum_add_distrib, Complex.im_sum]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hc', hb']
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hconjr, ← map_pow, ← map_mul, Complex.add_conj]
      simp)
  obtain ⟨n, -, hn⟩ := hlate 0
  -- back to the Weil form at `z = nω`
  have hsumX : Summable fun q => w q * (ξ q / (r : ℂ)) ^ n :=
    Summable.of_norm_bounded hwsum.norm fun q => by
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hξr q))
  have hsumY : Summable fun q => conj (w q) * (conj (ξ q) / (r : ℂ)) ^ n :=
    Summable.of_norm_bounded hwsum.norm fun q => by
      rw [norm_mul, norm_pow, Complex.norm_conj, hconjr, Complex.norm_conj]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hξr q))
  have hsplit : (∑' i, c' i * (b' i / (r : ℂ)) ^ n) =
      (∑' q, w q * (ξ q / (r : ℂ)) ^ n) + conj (∑' q, w q * (ξ q / (r : ℂ)) ^ n) := by
    rw [Summable.tsum_sum (f := fun i => c' i * (b' i / (r : ℂ)) ^ n)
      (by rw [hc', hb']; exact hsumX) (by rw [hc', hb']; exact hsumY), Complex.conj_tsum]
    rw [hc', hb']
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hconjr, ← map_pow, ← map_mul]
  rw [hsplit, Complex.add_re, Complex.conj_re] at hn
  have hX : (∑' q, w q * (ξ q / (r : ℂ)) ^ n).re < 0 := by linarith
  refine ⟨(n : ℂ) * ω, ?_⟩
  have hF : expWeilForm A B ((n : ℂ) * ω) =
      ((r ^ n : ℝ) : ℂ) * ∑' q, w q * (ξ q / (r : ℂ)) ^ n := by
    rw [expWeilForm, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have e1 : (n : ℂ) * ω * A q + conj ((n : ℂ) * ω) * B q =
        (n : ℂ) * (ω * A q + conj ω * B q) := by
      rw [map_mul, map_natCast]; ring
    rw [e1, Complex.exp_nat_mul, ← hwq]
    have e2 : ξ q = cexp (ω * A q + conj ω * B q) := by rw [hξ]
    rw [← e2, div_pow]
    push_cast
    field_simp
  rw [hF, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg (pow_pos hr0 n) hX

/-- **A loud modulus part makes the exponential Weil form negative somewhere.** -/
theorem exists_re_expWeilForm_neg {A B : XiZeroCopy → ℂ}
    (hmin : ∀ q, ‖A q‖ ≤ 1 ∨ ‖B q‖ ≤ 1)
    (hfin : {q : XiZeroCopy | 1 < ‖A q + conj (B q)‖}.Finite)
    {q₁ : XiZeroCopy} (hq₁ : 2 < ‖A q₁ + conj (B q₁)‖) :
    ∃ z : ℂ, (expWeilForm A B z).re < 0 :=
  exists_re_expWeilForm_neg_of_threshold (L := 2) (by norm_num)
    (hfin.subset fun q hq => by simp only [Set.mem_setOf_eq] at hq ⊢; linarith)
    (fun q hq => sub_conj_ne_zero_of_two_lt (hmin q) hq) hq₁

/-! ## The dichotomy for a family -/

/-- **RH ⟺ exponential Weil positivity on infinitely many members of a detecting family.** -/
theorem riemannHypothesis_iff_frequently_expWeilForm_nonneg (A B : ℕ → XiZeroCopy → ℂ)
    (hbd : ∀ N, ∃ C : ℝ, ∀ q, ‖A N q‖ ≤ C ∧ ‖B N q‖ ≤ C)
    (hmin : ∀ N q, ‖A N q‖ ≤ 1 ∨ ‖B N q‖ ≤ 1)
    (hfin : ∀ N, {q : XiZeroCopy | 1 < ‖A N q + conj (B N q)‖}.Finite)
    (hsym : RiemannHypothesis → ∀ N q, B N q = conj (A N q))
    (hdet : ¬ RiemannHypothesis → ∀ᶠ N : ℕ in atTop, ∃ q, 2 < ‖A N q + conj (B N q)‖) :
    RiemannHypothesis ↔ ∃ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 ≤ (expWeilForm (A N) (B N) z).re := by
  constructor
  · intro hRH
    refine (Eventually.of_forall fun N z => ?_).frequently
    obtain ⟨C, hC⟩ := hbd N
    exact re_expWeilForm_nonneg_of_riemannHypothesis hC hRH (hsym hRH N) z
  · intro hfr
    by_contra hRH
    obtain ⟨N, hpos, q₁, hq₁⟩ := (hfr.and_eventually (hdet hRH)).exists
    obtain ⟨z, hz⟩ := exists_re_expWeilForm_neg (hmin N) (hfin N) hq₁
    exact (not_le.mpr hz) (hpos z)

/-- **Dichotomy.**  Positivity on infinitely many members forces it on every member. -/
theorem riemannHypothesis_iff_forall_expWeilForm_nonneg (A B : ℕ → XiZeroCopy → ℂ)
    (hbd : ∀ N, ∃ C : ℝ, ∀ q, ‖A N q‖ ≤ C ∧ ‖B N q‖ ≤ C)
    (hmin : ∀ N q, ‖A N q‖ ≤ 1 ∨ ‖B N q‖ ≤ 1)
    (hfin : ∀ N, {q : XiZeroCopy | 1 < ‖A N q + conj (B N q)‖}.Finite)
    (hsym : RiemannHypothesis → ∀ N q, B N q = conj (A N q))
    (hdet : ¬ RiemannHypothesis → ∀ᶠ N : ℕ in atTop, ∃ q, 2 < ‖A N q + conj (B N q)‖) :
    RiemannHypothesis ↔ ∀ N : ℕ, ∀ z : ℂ, 0 ≤ (expWeilForm (A N) (B N) z).re := by
  refine ⟨fun hRH N z => ?_, fun h => (riemannHypothesis_iff_frequently_expWeilForm_nonneg A B
    hbd hmin hfin hsym hdet).mpr (Eventually.of_forall fun N z => h N z).frequently⟩
  obtain ⟨C, hC⟩ := hbd N
  exact re_expWeilForm_nonneg_of_riemannHypothesis hC hRH (hsym hRH N) z

/-! ## The pole shadow -/

/-- The pole shadow `m_N(s) = N^{s−½}/(s+1)²`. -/
def poleShadow (N : ℕ) (s : ℂ) : ℂ := cexp ((s - 1 / 2) * (Real.log N : ℂ)) / (s + 1) ^ 2

theorem norm_poleShadow (N : ℕ) (s : ℂ) :
    ‖poleShadow N s‖ = Real.exp ((s.re - 1 / 2) * Real.log N) / ‖s + 1‖ ^ 2 := by
  rw [poleShadow, norm_div, norm_pow, Complex.norm_exp, Complex.re_mul_ofReal]
  congr 3
  simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]

theorem one_add_im_sq_le_norm_add_one_sq {s : ℂ} (h0 : 0 ≤ s.re) :
    1 + s.im ^ 2 ≤ ‖s + 1‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
  nlinarith

theorem norm_poleShadow_le_one {N : ℕ} {s : ℂ} (h0 : 0 ≤ s.re) (h : s.re ≤ 1 / 2) :
    ‖poleShadow N s‖ ≤ 1 := by
  rw [norm_poleShadow]
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 : Real.exp ((s.re - 1 / 2) * Real.log N) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog)
  have h2 : 1 ≤ ‖s + 1‖ ^ 2 :=
    (by nlinarith [sq_nonneg s.im] : (1 : ℝ) ≤ 1 + s.im ^ 2).trans
      (one_add_im_sq_le_norm_add_one_sq h0)
  rw [div_le_one (by linarith)]
  linarith

theorem norm_poleShadow_le_band {N : ℕ} {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖poleShadow N s‖ ≤ Real.exp ((1 / 2) * Real.log N) / (1 + s.im ^ 2) := by
  rw [norm_poleShadow]
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  calc Real.exp ((s.re - 1 / 2) * Real.log N) / ‖s + 1‖ ^ 2
      ≤ Real.exp ((1 / 2) * Real.log N) / ‖s + 1‖ ^ 2 :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    _ ≤ Real.exp ((1 / 2) * Real.log N) / (1 + s.im ^ 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hpos (one_add_im_sq_le_norm_add_one_sq h0)

theorem poleShadow_conj (N : ℕ) (s : ℂ) : poleShadow N (conj s) = conj (poleShadow N s) := by
  rw [poleShadow, poleShadow, map_div₀, map_pow, ← Complex.exp_conj, map_mul, map_sub,
    Complex.conj_ofReal, map_add, map_one, map_div₀, map_one, map_ofNat]

theorem re_one_sub_xiZeroCopy_mem (q : XiZeroCopy) :
    0 ≤ (1 - (q.1 : ℂ)).re ∧ (1 - (q.1 : ℂ)).re ≤ 1 := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> linarith

/-- The pole-shadow Weil form `Σ_ρ exp(z N^{ρ−½}/(ρ+1)² + z̄ N^{½−ρ}/(2−ρ)²)/(ρ(1−ρ))`. -/
def poleShadowWeilForm (N : ℕ) (z : ℂ) : ℂ :=
  expWeilForm (fun q => poleShadow N (q.1 : ℂ)) (fun q => poleShadow N (1 - (q.1 : ℂ))) z

theorem poleShadow_bounds (N : ℕ) :
    (∃ C : ℝ, ∀ q : XiZeroCopy, ‖poleShadow N (q.1 : ℂ)‖ ≤ C ∧
      ‖poleShadow N (1 - (q.1 : ℂ))‖ ≤ C) ∧
    (∀ q : XiZeroCopy, ‖poleShadow N (q.1 : ℂ)‖ ≤ 1 ∨ ‖poleShadow N (1 - (q.1 : ℂ))‖ ≤ 1) ∧
    {q : XiZeroCopy | 1 < ‖poleShadow N (q.1 : ℂ) + conj (poleShadow N (1 - (q.1 : ℂ)))‖}.Finite := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp ((1 / 2) * Real.log N) := ⟨_, rfl⟩
  have hE0 : 0 < E := hE ▸ Real.exp_pos _
  have hband : ∀ q : XiZeroCopy, ‖poleShadow N (q.1 : ℂ)‖ ≤ E / (1 + (q.1 : ℂ).im ^ 2) ∧
      ‖poleShadow N (1 - (q.1 : ℂ))‖ ≤ E / (1 + (q.1 : ℂ).im ^ 2) := by
    intro q
    obtain ⟨h2, h3⟩ := re_one_sub_xiZeroCopy_mem q
    refine ⟨hE ▸ norm_poleShadow_le_band (xiZeroCopy_re_pos q).le (xiZeroCopy_re_lt_one q).le, ?_⟩
    have := hE ▸ norm_poleShadow_le_band (N := N) h2 h3
    have him : (1 - (q.1 : ℂ)).im ^ 2 = (q.1 : ℂ).im ^ 2 := by simp
    rwa [him] at this
  refine ⟨⟨E, fun q => ?_⟩, fun q => ?_, ?_⟩
  · have h : E / (1 + (q.1 : ℂ).im ^ 2) ≤ E :=
      div_le_self hE0.le (by nlinarith [sq_nonneg (q.1 : ℂ).im])
    exact ⟨(hband q).1.trans h, (hband q).2.trans h⟩
  · by_cases h : (q.1 : ℂ).re ≤ 1 / 2
    · exact Or.inl (norm_poleShadow_le_one (xiZeroCopy_re_pos q).le h)
    · push Not at h
      refine Or.inr (norm_poleShadow_le_one (re_one_sub_xiZeroCopy_mem q).1 ?_)
      simp only [Complex.sub_re, Complex.one_re]
      linarith
  · refine (finite_xiZeroCopy_band 0 (r := √(2 * E)) (Real.sqrt_nonneg _)).subset fun q hq => ?_
    simp only [Set.mem_setOf_eq] at hq ⊢
    rw [sub_zero]
    obtain ⟨hA, hB⟩ := hband q
    have htri := (norm_add_le (poleShadow N (q.1 : ℂ))
      (conj (poleShadow N (1 - (q.1 : ℂ))))).trans_eq (by rw [Complex.norm_conj])
    have hpos : 0 < 1 + (q.1 : ℂ).im ^ 2 := by positivity
    have h2 : 1 < 2 * E / (1 + (q.1 : ℂ).im ^ 2) := by
      have e : 2 * E / (1 + (q.1 : ℂ).im ^ 2) =
          E / (1 + (q.1 : ℂ).im ^ 2) + E / (1 + (q.1 : ℂ).im ^ 2) := by ring
      rw [e]; linarith
    rw [lt_div_iff₀ hpos] at h2
    have h3 : (q.1 : ℂ).im ^ 2 ≤ 2 * E := by nlinarith
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h3

/-- Off RH, a zero right of the line is loud for the pole shadow on every large `N`. -/
theorem eventually_exists_two_lt_norm_poleShadow_sym (hRH : ¬ RiemannHypothesis) :
    ∀ᶠ N : ℕ in atTop, ∃ q : XiZeroCopy,
      2 < ‖poleShadow N (q.1 : ℂ) + conj (poleShadow N (1 - (q.1 : ℂ)))‖ := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖(q₁.1 : ℂ) + 1‖ ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hc]
    have := one_add_im_sq_le_norm_add_one_sq (xiZeroCopy_re_pos q₁).le
    nlinarith [sq_nonneg (q₁.1 : ℂ).im]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (q₁.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hgrow : Tendsto (fun N : ℕ => Real.exp (δ * Real.log N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hδ0)
  filter_upwards [hgrow.eventually (eventually_gt_atTop (3 * c))] with N hN
  refine ⟨q₁, ?_⟩
  have hV : 3 < ‖poleShadow N (q₁.1 : ℂ)‖ := by
    rw [norm_poleShadow, ← hc, lt_div_iff₀ hc0, ← hδ]; linarith
  have hV' : ‖poleShadow N (1 - (q₁.1 : ℂ))‖ ≤ 1 :=
    norm_poleShadow_le_one (re_one_sub_xiZeroCopy_mem q₁).1
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have htri := norm_sub_le (poleShadow N (q₁.1 : ℂ) + conj (poleShadow N (1 - (q₁.1 : ℂ))))
    (conj (poleShadow N (1 - (q₁.1 : ℂ))))
  rw [add_sub_cancel_right, Complex.norm_conj] at htri
  linarith

/-- Under RH the reflected pole shadow is the conjugate one. -/
theorem poleShadow_one_sub_eq_conj_of_riemannHypothesis (hRH : RiemannHypothesis) (N : ℕ)
    (q : XiZeroCopy) : poleShadow N (1 - (q.1 : ℂ)) = conj (poleShadow N (q.1 : ℂ)) := by
  have hhalf := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  have hrefl : 1 - (q.1 : ℂ) = conj (q.1 : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hhalf]; norm_num
    · simp
  rw [hrefl, poleShadow_conj]

/-- **One shell certifies a zero-free region.**  If the pole-shadow form is nonnegative at `N ≥ 2`,
every zero right of the line satisfies `Re ρ − ½ ≤ log(3|ρ+1|²)/log N`. -/
theorem re_sub_half_le_of_poleShadowWeilForm_nonneg {N : ℕ} (hN : 2 ≤ N)
    (hpos : ∀ z : ℂ, 0 ≤ (poleShadowWeilForm N z).re) (q : XiZeroCopy)
    (hq : 1 / 2 ≤ (q.1 : ℂ).re) :
    (q.1 : ℂ).re - 1 / 2 ≤ Real.log (3 * ‖(q.1 : ℂ) + 1‖ ^ 2) / Real.log N := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hsym : ‖poleShadow N (q.1 : ℂ) + conj (poleShadow N (1 - (q.1 : ℂ)))‖ ≤ 2 := by
    by_contra h
    push Not at h
    obtain ⟨z, hz⟩ := exists_re_expWeilForm_neg (poleShadow_bounds N).2.1 (poleShadow_bounds N).2.2 h
    exact (not_le.mpr hz) (hpos z)
  have hB : ‖poleShadow N (1 - (q.1 : ℂ))‖ ≤ 1 :=
    norm_poleShadow_le_one (re_one_sub_xiZeroCopy_mem q).1
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have htri := norm_sub_le (poleShadow N (q.1 : ℂ) + conj (poleShadow N (1 - (q.1 : ℂ))))
    (conj (poleShadow N (1 - (q.1 : ℂ))))
  rw [add_sub_cancel_right, Complex.norm_conj] at htri
  have hA : ‖poleShadow N (q.1 : ℂ)‖ ≤ 3 := by linarith
  have hc0 : 0 < ‖(q.1 : ℂ) + 1‖ ^ 2 := by
    have := one_add_im_sq_le_norm_add_one_sq (xiZeroCopy_re_pos q).le
    nlinarith [sq_nonneg (q.1 : ℂ).im]
  rw [norm_poleShadow, div_le_iff₀ hc0] at hA
  rw [le_div_iff₀ hlogN, ← Real.exp_le_exp, Real.exp_log (by positivity)]
  linarith

/-- **RH ⟺ pole-shadow Weil positivity on infinitely many `N`**; no primes enter. -/
theorem riemannHypothesis_iff_frequently_poleShadowWeilForm_nonneg :
    RiemannHypothesis ↔ ∃ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 ≤ (poleShadowWeilForm N z).re :=
  riemannHypothesis_iff_frequently_expWeilForm_nonneg
    (fun N q => poleShadow N (q.1 : ℂ)) (fun N q => poleShadow N (1 - (q.1 : ℂ)))
    (fun N => (poleShadow_bounds N).1) (fun N => (poleShadow_bounds N).2.1)
    (fun N => (poleShadow_bounds N).2.2)
    (fun hRH N q => poleShadow_one_sub_eq_conj_of_riemannHypothesis hRH N q)
    eventually_exists_two_lt_norm_poleShadow_sym

/-- **Dichotomy for the pole shadow.** -/
theorem riemannHypothesis_iff_forall_poleShadowWeilForm_nonneg :
    RiemannHypothesis ↔ ∀ N : ℕ, ∀ z : ℂ, 0 ≤ (poleShadowWeilForm N z).re :=
  riemannHypothesis_iff_forall_expWeilForm_nonneg
    (fun N q => poleShadow N (q.1 : ℂ)) (fun N q => poleShadow N (1 - (q.1 : ℂ)))
    (fun N => (poleShadow_bounds N).1) (fun N => (poleShadow_bounds N).2.1)
    (fun N => (poleShadow_bounds N).2.2)
    (fun hRH N q => poleShadow_one_sub_eq_conj_of_riemannHypothesis hRH N q)
    eventually_exists_two_lt_norm_poleShadow_sym

end

end RHTower
