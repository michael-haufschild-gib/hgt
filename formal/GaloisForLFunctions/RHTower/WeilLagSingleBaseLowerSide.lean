import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase
import GaloisForLFunctions.HTGeometry.DiscreteKernelAverage

/-!
# Single-base lag sequences are unbounded below at an attained nonresonant top

Let `b ≥ 2` and suppose the maximal real part `β₀ > ½` of the Xi zeros is attained. Call the top
level *resonant* for `b` if some top ordinate `γ` has `γ log b ∈ 2πℤ`, i.e. `b^{iγ} = 1`.

**Theorem** (`exists_pow_integerLag_lt_of_attainedTop_nonresonant`). If the top level is
nonresonant for `b`, then `a_{b^m}` is unbounded below.

Together with `exists_pow_integerLag_gt_of_attainedTop` (unbounded above, no resonance condition)
this gives the two-sided single-base picture at an attained top: the upper side always detects it,
and the lower side detects it exactly when no top ordinate is resonant. A resonant top ordinate
contributes the constant `Re(w) > 0` at every sample, which is the obstruction.

**Proof.** Write `a_{b^m} = r^m g(m) + O(r^m · tail(m))` with `r = b^{β₀−½}`, `tail(m) → 0`, and
`g(m) = Σ_{top} Re(w_ρ b^{imγ_ρ})`.
* *Mean zero.* Each top term has ratio `b^{iγ} ≠ 1`, so its averages over `m < N` are `O(1/N)`;
  with a finite truncation the averages of `g` tend to zero.
* *Positive part.* `g(0) = Σ_{top} Re w_ρ = c > 0`. On the Bohr set where all phases of a finite
  part `F` of the top level are near `2πℤ`, `g ≥ c/2`; the cosine-power kernel `K` gives this set
  kernel mass `≥ aN` among `m < N` (`exists_kernel_return_mass`).
* If `a_{b^m}` were bounded below, `g(m) ≥ −ε` for large `m`. Then
  `Σ_{m<N}(g + ε) ≥ Σ_{m<N}(g + ε)K ≥ (c/2)aN − O(1)`, contradicting the mean for `ε = ca/16`.
-/

open Complex Filter Real Topology
open GaloisForLFunctions.HTGeometry.KroneckerFlow

namespace RHTower

noncomputable section

/-- No top ordinate is a multiple of `2π/log b`. -/
def NonresonantTop (β₀ : ℝ) (b : ℕ) : Prop :=
  ∀ q ∈ topLevel β₀, ∀ k : ℤ, zeroOrdinate q * Real.log b ≠ 2 * π * k

theorem norm_exp_I_mul_ofReal' (x : ℝ) : ‖Complex.exp (I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

theorem norm_exp_two_pi_I_mul_ofReal (x : ℝ) : ‖Complex.exp (2 * Real.pi * I * (x : ℂ))‖ = 1 := by
  rw [show 2 * Real.pi * I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The top function `g(m) = Σ_{top} Re(w_ρ e^{i m log b γ_ρ})`. -/
def topLagPart (β₀ : ℝ) (b : ℕ) (m : ℕ) : ℝ :=
  ∑' q : topLevel β₀, (lagWeight q *
    Complex.exp (I * ((((m : ℝ) * Real.log b) * zeroOrdinate q : ℝ) : ℂ))).re

theorem norm_topTerm (β₀ : ℝ) (b m : ℕ) (q : topLevel β₀) :
    ‖lagWeight q * Complex.exp (I * ((((m : ℝ) * Real.log b) * zeroOrdinate q : ℝ) : ℂ))‖ =
      ‖lagWeight q‖ := by
  rw [norm_mul, norm_exp_I_mul_ofReal', mul_one]

theorem summable_topLagPart_terms (β₀ : ℝ) (b m : ℕ) :
    Summable fun q : topLevel β₀ => (lagWeight q *
      Complex.exp (I * ((((m : ℝ) * Real.log b) * zeroOrdinate q : ℝ) : ℂ))).re := by
  refine (summable_norm_lagWeight.subtype _).of_norm_bounded fun q => ?_
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (le_of_eq (norm_topTerm β₀ b m q))

/-- **The single-base value splits into the top function and a lower part.** -/
theorem integerLag_pow_eq_top_add (β₀ : ℝ) (b m : ℕ) :
    ∃ low : ℝ,
      |low| ≤ Real.exp ((m : ℝ) * Real.log b * (β₀ - 1 / 2)) * lowerTail β₀ (Real.log b) m ∧
      integerLag (b ^ m) =
        Real.exp ((m : ℝ) * Real.log b * (β₀ - 1 / 2)) * topLagPart β₀ b m + low := by
  set L : ℝ := m * Real.log b with hLdef
  set T := topLevel β₀ with hTdef
  set f : XiZeroCopy → ℂ := fun q => lagWeight q * Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) with hfdef
  have hf : Summable f := summable_lagWeight_mul_exp L
  refine ⟨(∑' q : ↑Tᶜ, f q).re, abs_re_lowerPart_le β₀ (Real.log b) m, ?_⟩
  have hval : integerLag (b ^ m) = (∑' q : T, f q).re + (∑' q : ↑Tᶜ, f q).re := by
    rw [integerLag_pow, weilLagFunction_eq_tsum_lagWeight, ← hLdef,
      ← hf.tsum_subtype_add_tsum_subtype_compl T, Complex.add_re]
  set g : T → ℂ := fun q => lagWeight q * Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ))
    with hgdef
  have hg : Summable g := by
    refine (summable_norm_lagWeight.subtype T).of_norm_bounded fun q => ?_
    exact le_of_eq (norm_topTerm β₀ b m q)
  have htopval : (∑' q : T, f q).re = Real.exp (L * (β₀ - 1 / 2)) * ∑' q : T, (g q).re := by
    have e1 : ∀ q : T, f q = (Real.exp (L * (β₀ - 1 / 2)) : ℂ) * g q := by
      intro q
      have hq : ((q.1).1 : ℂ).re = β₀ := q.2
      simp only [hfdef, hgdef]
      rw [exp_lag_top hq]; ring
    rw [tsum_congr e1, tsum_mul_left, Complex.re_ofReal_mul, Complex.re_tsum hg]
  rw [hval, htopval]
  rfl

/-- The top function is bounded by the total weight. -/
theorem abs_topLagPart_le (β₀ : ℝ) (b m : ℕ) :
    |topLagPart β₀ b m| ≤ ∑' q : topLevel β₀, ‖lagWeight q‖ := by
  unfold topLagPart
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_topLagPart_terms β₀ b m).norm).trans ?_
  refine Summable.tsum_le_tsum (fun q => ?_) (summable_topLagPart_terms β₀ b m).norm
    (summable_norm_lagWeight.subtype _)
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (le_of_eq (norm_topTerm β₀ b m q))

/-- `e^{2πi x} ≠ 1` off the integers. -/
theorem exp_two_pi_I_ne_one_of_not_int {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) :
    Complex.exp (2 * Real.pi * I * x) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply hx n
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((x : ℝ) : ℂ) = n := by
    apply mul_left_cancel₀ hpi
    rw [show 2 * Real.pi * I * ((x : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * I) from hn]
    ring
  exact_mod_cast h2

/-- The unit ratio `b^{iγ} = e^{2πi γ log b/(2π)}`. -/
def lagPhaseRatio (b : ℕ) (γ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * ((γ * Real.log b / (2 * π) : ℝ) : ℂ))

theorem exp_topPhase_eq_pow (b : ℕ) (γ : ℝ) (m : ℕ) :
    Complex.exp (I * ((((m : ℝ) * Real.log b) * γ : ℝ) : ℂ)) = lagPhaseRatio b γ ^ m := by
  rw [lagPhaseRatio, ← Complex.exp_nat_mul]
  congr 1
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **Nonresonant averages vanish.** -/
theorem abs_sum_re_phase_le {b : ℕ} {γ : ℝ} (hres : ∀ k : ℤ, γ * Real.log b ≠ 2 * π * k)
    (w : ℂ) (N : ℕ) :
    |∑ m ∈ Finset.range N, (w * Complex.exp (I * ((((m : ℝ) * Real.log b) * γ : ℝ) : ℂ))).re| ≤
      ‖w‖ * (2 / ‖lagPhaseRatio b γ - 1‖) := by
  have hznorm : ‖lagPhaseRatio b γ‖ = 1 := norm_exp_two_pi_I_mul_ofReal _
  have hz1 : lagPhaseRatio b γ ≠ 1 := by
    apply exp_two_pi_I_ne_one_of_not_int
    intro k hk
    apply hres k
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    field_simp at hk
    linarith
  simp_rw [exp_topPhase_eq_pow]
  rw [← Complex.re_sum, ← Finset.mul_sum]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_unit_geom_sum_le hznorm hz1 N) (norm_nonneg _)

/-- **On a Bohr box the top function is at least half its value at `0`.** -/
theorem half_le_topLagPart_of_box {β₀ : ℝ} (b : ℕ) (F : Finset (topLevel β₀))
    (hFtail : ∑' q : {x : topLevel β₀ // x ∉ F}, ‖lagWeight q‖ < topWeight β₀ / 8)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρW : 2 * π * ρ * ∑' q : topLevel β₀, ‖lagWeight q‖ ≤ topWeight β₀ / 4) (n : ℕ)
    (hn : ∀ q ∈ F, ∃ z : ℤ, |(n : ℝ) * (zeroOrdinate q * Real.log b / (2 * π)) - z| < ρ) :
    topWeight β₀ / 2 ≤ topLagPart β₀ b n := by
  set c := topWeight β₀ with hc
  set W := ∑' q : (topLevel β₀), ‖lagWeight q‖ with hW
  have hsT : Summable fun q : (topLevel β₀) => ‖lagWeight q‖ := summable_norm_lagWeight.subtype (topLevel β₀)
  have hsTre := summable_lagWeight_re_subtype (topLevel β₀)
  set L : ℝ := n * Real.log b with hL
  set g : (topLevel β₀) → ℂ := fun q => lagWeight q * Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ))
    with hgdef
  have hgn : ∀ q : (topLevel β₀), ‖g q‖ = ‖lagWeight q‖ := fun q => norm_topTerm β₀ b n q
  have hg : Summable fun q : (topLevel β₀) => (g q).re := summable_topLagPart_terms β₀ b n
  have hgF : ∀ q ∈ F, (lagWeight q).re - ‖lagWeight q‖ * (2 * π * ρ) ≤ (g q).re := by
    intro q hq
    obtain ⟨z, hz⟩ := hn q hq
    have hphase : ‖Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1‖ ≤ 2 * π * ρ := by
      set x : ℝ := 2 * π * ((n : ℝ) * (zeroOrdinate q.1 * Real.log b / (2 * π)) - z) with hx
      have hθ : L * zeroOrdinate q.1 = x + z * (2 * π) := by
        rw [hx, hL]; field_simp; ring
      have hper : Complex.exp (I * ((z * (2 * π) : ℝ) : ℂ)) = 1 := by
        push_cast
        rw [show I * ((z : ℂ) * (2 * π)) = (z : ℂ) * (2 * π * I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I z
      rw [hθ, Complex.ofReal_add, mul_add, Complex.exp_add, hper, mul_one]
      refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
      rw [Real.norm_eq_abs, hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact mul_le_mul_of_nonneg_left hz.le (by positivity)
    have hsplit : g q = lagWeight q +
        lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1) := by
      simp only [hgdef]; ring
    rw [hsplit, Complex.add_re]
    have h1 := neg_le_of_abs_le (Complex.abs_re_le_norm
      (lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1)))
    rw [norm_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left hphase (norm_nonneg (lagWeight q))
    linarith
  have hsplitT := hg.sum_add_tsum_compl (s := F)
  have hsplitW := hsTre.sum_add_tsum_compl (s := F)
  have hFnorm : ∑ q ∈ F, ‖lagWeight q‖ ≤ W := hsT.sum_le_tsum F fun q _ => norm_nonneg _
  have hFre : c - c / 8 ≤ ∑ q ∈ F, (lagWeight q).re := by
    have hre_le : ∑' q : {x : (topLevel β₀) // x ∉ F}, (lagWeight q).re ≤
        ∑' q : {x : (topLevel β₀) // x ∉ F}, ‖lagWeight q‖ :=
      Summable.tsum_le_tsum (fun q => Complex.re_le_norm _) (hsTre.subtype _) (hsT.subtype _)
    have e' : ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, (lagWeight q).re =
        ∑' q : {x : (topLevel β₀) // x ∉ F}, (lagWeight q).re := rfl
    have hcval : c = ∑' q : (topLevel β₀), (lagWeight q).re := rfl
    linarith
  have hFg : ∑ q ∈ F, (lagWeight q).re - c / 4 ≤ ∑ q ∈ F, (g q).re := by
    have h1 : ∑ q ∈ F, ((lagWeight q).re - ‖lagWeight q‖ * (2 * π * ρ)) ≤ ∑ q ∈ F, (g q).re :=
      Finset.sum_le_sum hgF
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at h1
    have h2 : (∑ q ∈ F, ‖lagWeight q‖) * (2 * π * ρ) ≤ W * (2 * π * ρ) :=
      mul_le_mul_of_nonneg_right hFnorm (by positivity)
    linarith
  have hgtail : |∑' q : {x : (topLevel β₀) // x ∉ F}, (g q).re| ≤ c / 8 := by
    have h1 : |∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, (g q).re| ≤ ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, ‖(g q).re‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_tsum_le_tsum_norm (hg.norm.subtype _)
    have h2 : ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, ‖(g q).re‖ ≤ ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, ‖lagWeight q‖ := by
      refine Summable.tsum_le_tsum (fun q => ?_) (hg.norm.subtype _) (hsT.subtype _)
      rw [Real.norm_eq_abs, ← hgn q]
      exact Complex.abs_re_le_norm _
    have e' : ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, ‖lagWeight q‖ =
        ∑' q : {x : (topLevel β₀) // x ∉ F}, ‖lagWeight q‖ := rfl
    have e'' : ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, (g q).re = ∑' q : {x : (topLevel β₀) // x ∉ F}, (g q).re := rfl
    rw [← e'']
    linarith
  have e'' : ∑' q : ↑(↑F : Set (topLevel β₀))ᶜ, (g q).re = ∑' q : {x : (topLevel β₀) // x ∉ F}, (g q).re := rfl
  have := (abs_le.mp hgtail).1
  have hval : topLagPart β₀ b n = ∑' q : (topLevel β₀), (g q).re := rfl
  rw [hval]
  linarith

/-- **Averages of the top function are small at a nonresonant top.** -/
theorem sum_topLagPart_le {β₀ : ℝ} {b : ℕ} (hres : NonresonantTop β₀ b)
    (F : Finset (topLevel β₀)) {η : ℝ}
    (hFtail : ∑' q : {x : topLevel β₀ // x ∉ F}, ‖lagWeight q‖ < η) (N : ℕ) :
    ∑ m ∈ Finset.range N, topLagPart β₀ b m ≤
      ∑ q ∈ F, ‖lagWeight q‖ * (2 / ‖lagPhaseRatio b (zeroOrdinate q.1) - 1‖) + N * η := by
  have hsT : Summable fun q : (topLevel β₀) => ‖lagWeight q‖ := summable_norm_lagWeight.subtype (topLevel β₀)
  have hterm : ∀ m : ℕ, topLagPart β₀ b m =
      ∑ q ∈ F, (lagWeight q * Complex.exp (I * ((((m : ℝ) * Real.log b) * zeroOrdinate q.1 :
        ℝ) : ℂ))).re + ∑' q : {x : (topLevel β₀) // x ∉ F}, (lagWeight q * Complex.exp (I *
          ((((m : ℝ) * Real.log b) * zeroOrdinate q.1.1 : ℝ) : ℂ))).re := by
    intro m
    unfold topLagPart
    exact ((summable_topLagPart_terms β₀ b m).sum_add_tsum_compl (s := F)).symm
  have htailm : ∀ m : ℕ, ∑' q : {x : (topLevel β₀) // x ∉ F}, (lagWeight q * Complex.exp (I *
      ((((m : ℝ) * Real.log b) * zeroOrdinate q.1.1 : ℝ) : ℂ))).re ≤ η := by
    intro m
    have hs := (summable_topLagPart_terms β₀ b m).subtype (fun x : (topLevel β₀) => x ∉ F)
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
    refine le_trans (Summable.tsum_le_tsum (fun q => ?_) hs.norm (hsT.subtype _)) hFtail.le
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (le_of_eq (norm_topTerm β₀ b m q.1))
  calc ∑ m ∈ Finset.range N, topLagPart β₀ b m
      = ∑ q ∈ F, ∑ m ∈ Finset.range N, (lagWeight q * Complex.exp (I *
          ((((m : ℝ) * Real.log b) * zeroOrdinate q.1 : ℝ) : ℂ))).re +
        ∑ m ∈ Finset.range N, ∑' q : {x : (topLevel β₀) // x ∉ F}, (lagWeight q * Complex.exp (I *
          ((((m : ℝ) * Real.log b) * zeroOrdinate q.1.1 : ℝ) : ℂ))).re := by
        rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ q ∈ F, ‖lagWeight q‖ * (2 / ‖lagPhaseRatio b (zeroOrdinate q.1) - 1‖) + N * η := by
        refine add_le_add (Finset.sum_le_sum fun q _ =>
          (le_abs_self _).trans (abs_sum_re_phase_le (hres q.1 q.2) (lagWeight q) N)) ?_
        calc ∑ m ∈ Finset.range N, ∑' q : {x : (topLevel β₀) // x ∉ F}, (lagWeight q *
              Complex.exp (I * ((((m : ℝ) * Real.log b) * zeroOrdinate q.1.1 : ℝ) : ℂ))).re
            ≤ ∑ _m ∈ Finset.range N, η := Finset.sum_le_sum fun m _ => htailm m
          _ = N * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **A lag bound from below forces the top function to be eventually almost nonnegative.** -/
theorem eventually_neg_le_topLagPart {β₀ : ℝ} (hβ : 1 / 2 < β₀)
    (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, 1 ≤ m → M ≤ integerLag (b ^ m)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → -ε ≤ topLagPart β₀ b m := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set r := Real.exp (Real.log b * (β₀ - 1 / 2)) with hr
  have hr1 : 1 < r := Real.one_lt_exp_iff.mpr (by nlinarith)
  have hev1 := (tendsto_lowerTail hlogb hmax).eventually
    (eventually_le_nhds (show (0 : ℝ) < ε / 2 by positivity))
  have hrpow : Tendsto (fun m : ℕ => |M| / r ^ m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hr1)
  have hev2 := hrpow.eventually (eventually_le_nhds (show (0 : ℝ) < ε / 2 by positivity))
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp (hev1.and hev2)
  refine ⟨max m₁ 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hmm₁ : m₁ ≤ m := (le_max_left _ _).trans hm
  obtain ⟨low, hlow, hval⟩ := integerLag_pow_eq_top_add β₀ b m
  have hMm := hM m hm1
  rw [hval] at hMm
  have hexp : Real.exp ((m : ℝ) * Real.log b * (β₀ - 1 / 2)) = r ^ m := by
    rw [hr, ← Real.exp_nat_mul]; congr 1; ring
  rw [hexp] at hMm hlow
  have hrm : 0 < r ^ m := by positivity
  obtain ⟨h1, h2⟩ := hm₁ m hmm₁
  have hlow' := (abs_le.mp hlow).2
  have hg : r ^ m * (-(|M| / r ^ m) - lowerTail β₀ (Real.log b) m) ≤
      r ^ m * topLagPart β₀ b m := by
    have e : r ^ m * (-(|M| / r ^ m) - lowerTail β₀ (Real.log b) m) =
        -|M| - r ^ m * lowerTail β₀ (Real.log b) m := by
      field_simp
    rw [e]
    nlinarith [neg_abs_le M]
  have := le_of_mul_le_mul_left hg hrm
  linarith

/-- **The averaging contradiction.** A bounded sequence that is eventually almost nonnegative,
and at least `c/2` wherever a weight `0 ≤ H ≤ 1` of total mass `≥ aN` lives, cannot have averages
below `ca/16`. -/
theorem false_of_mean_and_mass {g H : ℕ → ℝ} {c a W E' : ℝ} {m₂ N₀ : ℕ} (hc : 0 < c)
    (ha : 0 < a) (hH0 : ∀ n, 0 ≤ H n) (hH1 : ∀ n, H n ≤ 1) (hW : ∀ n, |g n| ≤ W)
    (hbox : ∀ n, 0 < H n → c / 2 ≤ g n)
    (hlow : ∀ n, m₂ ≤ n → -(c * a / 16) ≤ g n)
    (hmass : ∀ N, N₀ ≤ N → 0 < N → a * N ≤ ∑ n ∈ Finset.range N, H n)
    (hmean : ∀ N : ℕ, ∑ n ∈ Finset.range N, g n ≤ E' + N * (c * a / 16)) : False := by
  set ε := c * a / 16 with hε
  have hε0 : 0 < ε := by positivity
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  set h : ℕ → ℝ := fun n => c / 2 * H n with hh
  have hhle : ∀ n, m₂ ≤ n → h n ≤ g n + ε := by
    intro n hn
    have hg := hlow n hn
    simp only [hh]
    rcases (hH0 n).lt_or_eq with hpos | hzero
    · have h1 := hbox n hpos
      have h2 := hH1 n
      nlinarith
    · rw [← hzero]; linarith
  have hhsmall : ∀ n, h n ≤ c / 2 := by
    intro n; simp only [hh]; have := hH1 n; nlinarith
  have hgsmall : ∀ n, -(W + ε) ≤ g n + ε := fun n => by
    linarith [(abs_le.mp (hW n)).1]
  have hE'0 : 0 ≤ E' := by
    have := hmean 0
    simpa using this
  obtain ⟨N, hN⟩ := exists_nat_gt ((E' + m₂ * (W + ε + c) + 1) * 8 / (c * a) + N₀ + 1)
  have hca : 0 < c * a := by positivity
  have hq0 : 0 ≤ (E' + m₂ * (W + ε + c) + 1) * 8 / (c * a) := by positivity
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    exact_mod_cast this
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hhsum : c / 2 * (a * N) ≤ ∑ n ∈ Finset.range N, h n := by
    have : ∑ n ∈ Finset.range N, h n = c / 2 * ∑ n ∈ Finset.range N, H n := by
      rw [Finset.mul_sum]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hmass N hNN₀ hNpos) (by positivity)
  have hsplit : ∀ f : ℕ → ℝ, ∑ n ∈ Finset.range N, f n =
      ∑ n ∈ (Finset.range N).filter (fun n => n < m₂), f n +
        ∑ n ∈ (Finset.range N).filter (fun n => ¬ n < m₂), f n := fun f =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hcard : (((Finset.range N).filter (fun n => n < m₂)).card : ℝ) ≤ m₂ := by
    have : ((Finset.range N).filter (fun n => n < m₂)).card ≤ m₂ := by
      calc ((Finset.range N).filter (fun n => n < m₂)).card ≤ (Finset.range m₂).card := by
            apply Finset.card_le_card
            intro n hn
            simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
            exact hn.2
        _ = m₂ := Finset.card_range _
    exact_mod_cast this
  have hA : ∑ n ∈ (Finset.range N).filter (fun n => ¬ n < m₂), h n ≤
      ∑ n ∈ (Finset.range N).filter (fun n => ¬ n < m₂), (g n + ε) :=
    Finset.sum_le_sum fun n hn => hhle n (not_lt.mp (Finset.mem_filter.mp hn).2)
  have hB : ∑ n ∈ (Finset.range N).filter (fun n => n < m₂), h n ≤ m₂ * (c / 2) := by
    calc _ ≤ ∑ _n ∈ (Finset.range N).filter (fun n => n < m₂), c / 2 :=
          Finset.sum_le_sum fun n _ => hhsmall n
      _ = ((Finset.range N).filter (fun n => n < m₂)).card * (c / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ m₂ * (c / 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hC : -(m₂ * (W + ε)) ≤ ∑ n ∈ (Finset.range N).filter (fun n => n < m₂), (g n + ε) := by
    calc -(m₂ * (W + ε)) ≤ -(((Finset.range N).filter (fun n => n < m₂)).card * (W + ε)) := by
          have : 0 ≤ W + ε := by linarith
          nlinarith
      _ = ∑ _n ∈ (Finset.range N).filter (fun n => n < m₂), -(W + ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun n _ => hgsmall n
  have hD : ∑ n ∈ Finset.range N, (g n + ε) ≤ E' + N * ε + N * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith [hmean N]
  rw [hsplit] at hhsum hD
  have hNr : (m₂ : ℝ) * (W + ε + c) + E' + 1 < c * a / 8 * N := by
    have h1 : (E' + m₂ * (W + ε + c) + 1) * 8 / (c * a) < N := by
      have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
      linarith
    rw [div_lt_iff₀ hca] at h1
    nlinarith
  nlinarith [hA, hB, hC, hhsum, hD]

/-- **An attained nonresonant top is detected from below.** -/
theorem exists_pow_integerLag_lt_of_attainedTop_nonresonant {β₀ : ℝ} (hβ : 1 / 2 < β₀)
    (h : AttainedTop β₀) {b : ℕ} (hb : 2 ≤ b) (hres : NonresonantTop β₀ b) (M : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ integerLag (b ^ m) < M := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨htop, hmax⟩ := h
  set T := topLevel β₀ with hTdef
  set c := topWeight β₀ with hcdef
  have hc : 0 < c := topWeight_pos htop
  set W := ∑' q : T, ‖lagWeight q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  have htail := tendsto_tsum_compl_atTop_zero (fun q : T => ‖lagWeight q‖)
  obtain ⟨F, hF⟩ :=
    Filter.eventually_atTop.mp (htail.eventually_lt_const (by linarith : (0 : ℝ) < c / 8))
  set ρ : ℝ := min (1 / 4) (c / (8 * π * (W + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ4 : ρ ≤ 1 / 4 := min_le_left _ _
  have hρW : 2 * π * ρ * W ≤ c / 4 := by
    have h1 : ρ ≤ c / (8 * π * (W + 1)) := min_le_right _ _
    have h2 : 2 * π * ρ * W ≤ 2 * π * (c / (8 * π * (W + 1))) * W := by gcongr
    have h3 : 2 * π * (c / (8 * π * (W + 1))) * W = c / 4 * (W / (W + 1)) := by
      field_simp; ring
    have h4 : W / (W + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  let e := F.equivFin
  let α : Fin F.card → ℝ := fun i => zeroOrdinate (e.symm i).1 * Real.log b / (2 * π)
  obtain ⟨Mk, a, ha, N₀, hmass⟩ := exists_kernel_return_mass α hρ0 hρ4
  obtain ⟨F', hF'⟩ := Filter.eventually_atTop.mp
    (htail.eventually_lt_const (by positivity : (0 : ℝ) < c * a / 16))
  obtain ⟨m₁, hm₁⟩ := eventually_neg_le_topLagPart hβ hmax hb hcon
    (show 0 < c * a / 16 by positivity)
  set Bx : ℕ → Prop := fun n => ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - 0 - z| < ρ with hBx
  set H : ℕ → ℝ := fun n => if Bx n then flowKernel Mk α 0 n else 0 with hHdef
  have hHB : ∀ n, 0 < H n → Bx n := by
    intro n hn
    by_contra hb
    simp only [hHdef, if_neg hb] at hn
    exact lt_irrefl _ hn
  refine false_of_mean_and_mass (g := topLagPart β₀ b) (H := H) (m₂ := m₁) (N₀ := N₀) hc ha
    (fun n => by simp only [hHdef]; split_ifs; exacts [flowKernel_nonneg Mk α 0 _, le_rfl])
    (fun n => by simp only [hHdef]; split_ifs; exacts [flowKernel_le_one Mk α 0 _, zero_le_one])
    (abs_topLagPart_le β₀ b) (fun n hn => ?_) hm₁ (fun (N : ℕ) (hN : N₀ ≤ N) (hN0 : 0 < N) => ?_)
    (sum_topLagPart_le hres F' (hF' F' le_rfl))
  · have hb := hHB n hn
    refine half_le_topLagPart_of_box b F (hF F le_rfl) hρ0.le hρW n fun q hq => ?_
    obtain ⟨z, hz⟩ := hb (e ⟨q, hq⟩)
    refine ⟨z, ?_⟩
    have hα : α (e ⟨q, hq⟩) = zeroOrdinate q.1 * Real.log b / (2 * π) := by
      simp only [α, Equiv.symm_apply_apply]
    rwa [hα, sub_zero] at hz
  · have := hmass N hN hN0
    rw [Finset.sum_filter] at this
    convert this using 3

/-- **Bounded-below single-base lags exclude attained nonresonant tops.** -/
theorem not_attainedTop_nonresonant_of_forall_ge {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, 1 ≤ m → M ≤ integerLag (b ^ m)) {β₀ : ℝ} (hβ : 1 / 2 < β₀)
    (hres : NonresonantTop β₀ b) : ¬ AttainedTop β₀ := by
  intro h
  obtain ⟨m, hm1, hm⟩ := exists_pow_integerLag_lt_of_attainedTop_nonresonant hβ h hb hres M
  exact absurd (hM m hm1) (not_le.mpr hm)

end

end RHTower
