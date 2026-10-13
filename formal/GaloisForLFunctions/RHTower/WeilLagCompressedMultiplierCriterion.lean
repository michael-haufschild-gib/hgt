import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Compressed lag multipliers

For a multiplier `h` on the zero copies of `ξ` put `R_h(n) = Σ_ρ e^{n h(ρ)} / (ρ(1 − ρ))`.
The lag progression `Φ(nℓ)` is the case `h(ρ) = ℓ(ρ − ½)`.

Call `h` *compressing* if for every `ε > 0` only finitely many zero copies have `Re h > ε`.
Then a positive value of `Re h` forces a largest value, attained by finitely many zeros, and
`Re R_h(n)` is unbounded above along the integers: simultaneous Dirichlet approximation aligns
the finitely many top phases, the top weight `Σ Re 1/(ρ(1−ρ))` is positive, and the remaining
zeros are suppressed by dominated convergence (`exists_compressedLag_gt`).

Consequently, if `Re h ≤ 0` on the critical line and `Re h > 0` to its right, RH holds if and
only if `h` is compressing and `Re R_h(n)` is bounded above
(`riemannHypothesis_iff_isCompressing_and_bddAbove`).  Since the growth is exponential at the
attained rate, subexponential slack `Re R_h(n) ≤ C_ε e^{εn}` already suffices
(`riemannHypothesis_iff_compressedLag_subexponential`).  For the lag multiplier, compression is
exactly the statement that the zeros approach the line
(`isCompressingMultiplier_lagMultiplier_iff`).

The multiplier `H(z) = z / log(2 − z²)`, `z = ρ − ½`, is compressing unconditionally: for
`z = x + iy` with `|x| ≤ ½`, `Re H` has the sign of `x`, and `Re H ≤ 3x / log(7/4 + y²)` once
`log(7/4 + y²) ≥ 1`.  The sign comes from `|arg(2 − z²)| ≤ 2|xy|/(2 − x² + y²)` and
`log u − 2y²/u ≥ log(7/2) − 1 > 0` for `u = 2 − x² + y²`.  Hence RH holds if and only if
`Re Σ_ρ e^{n H(ρ − ½)}/(ρ(1 − ρ))` is bounded above along the integers
(`riemannHypothesis_iff_bddAbove_logCompressedLag`), with no condition on the zeros at large
height.
-/

open Complex Filter Real Topology
open GaloisForLFunctions.HTGeometry (latticeClose exists_simultaneous_dirichlet)

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-! ## Compressed lags of a multiplier -/

/-- The compressed lag `Σ_ρ e^{n h(ρ)}/(ρ(1 − ρ))` of a multiplier `h` on the zero copies. -/
def compressedLag (h : XiZeroCopy → ℂ) (n : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, lagWeight q * Complex.exp ((n : ℂ) * h q)

/-- A multiplier is compressing if, for every `ε > 0`, only finitely many zero copies have
`Re h > ε`. -/
def IsCompressingMultiplier (h : XiZeroCopy → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → {q : XiZeroCopy | ε < (h q).re}.Finite

theorem re_natCast_mul_multiplier (n : ℕ) (z : ℂ) : ((n : ℂ) * z).re = n * z.re := by
  simp [Complex.mul_re]

/-- A compressing exponent has real part bounded above. -/
theorem exists_re_le_of_compressing {ι : Type*} {h : ι → ℂ}
    (hc : ∀ ε : ℝ, 0 < ε → {i | ε < (h i).re}.Finite) : ∃ B : ℝ, ∀ i, (h i).re ≤ B := by
  obtain ⟨B₀, hB₀⟩ := ((hc 1 one_pos).image fun i => (h i).re).bddAbove
  refine ⟨max 1 B₀, fun i => ?_⟩
  by_cases hi : 1 < (h i).re
  · exact (hB₀ ⟨i, hi, rfl⟩).trans (le_max_right _ _)
  · exact (not_lt.mp hi).trans (le_max_left _ _)

theorem summable_mul_exp_of_compressing {ι : Type*} {w h : ι → ℂ}
    (hws : Summable fun i => ‖w i‖) (hc : ∀ ε : ℝ, 0 < ε → {i | ε < (h i).re}.Finite) (n : ℕ) :
    Summable fun i => w i * Complex.exp ((n : ℂ) * h i) := by
  obtain ⟨B, hB⟩ := exists_re_le_of_compressing hc
  refine (hws.mul_right (Real.exp (n * B))).of_norm_bounded fun i => ?_
  rw [norm_mul, Complex.norm_exp, re_natCast_mul_multiplier]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB i) (Nat.cast_nonneg n))) (norm_nonneg _)

/-- **Weighted exponential sums with a compressing exponent grow at the attained rate.**  Let the
weights `w i` have positive real parts and absolutely summable norms, and let only finitely many
`i` have `Re h i > ε`, for every `ε > 0`.  If some `Re h i > 0`, the largest value `M₀` of `Re h` is
attained by finitely many indices, and beyond every index, along exponents produced by simultaneous
Dirichlet approximation of their phases, `Re Σ w_i e^{n h_i} ≥ (c/2) e^{n M₀}` with
`c = Σ_{Re h = M₀} Re w > 0`. -/
theorem exists_re_tsum_mul_exp_ge {ι : Type*} {w h : ι → ℂ} (hwre : ∀ i, 0 < (w i).re)
    (hws : Summable fun i => ‖w i‖) (hc : ∀ ε : ℝ, 0 < ε → {i | ε < (h i).re}.Finite)
    (hpos : ∃ i, 0 < (h i).re) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      c * Real.exp ((n : ℝ) * M₀) ≤ (∑' i, w i * Complex.exp ((n : ℂ) * h i)).re := by
  classical
  obtain ⟨q₀, hq₀⟩ := hpos
  -- (1) the attained top `M₀` and its finite level set `F`
  have hSfin := hc ((h q₀).re / 2) (by linarith)
  set S := hSfin.toFinset with hS
  have hq₀S : q₀ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]
    show (h q₀).re / 2 < (h q₀).re
    linarith
  obtain ⟨qm, -, hqm⟩ := S.exists_max_image (fun q => (h q).re) ⟨q₀, hq₀S⟩
  set M₀ := (h qm).re with hM₀def
  have hM₀q₀ : (h q₀).re ≤ M₀ := hqm q₀ hq₀S
  have hM₀ : 0 < M₀ := by linarith
  have hmax : ∀ q : ι, (h q).re ≤ M₀ := by
    intro q
    by_cases hq : (h q₀).re / 2 < (h q).re
    · exact hqm q (by rw [hS, Set.Finite.mem_toFinset]; exact hq)
    · push Not at hq
      linarith
  have hTfin : {q : ι | (h q).re = M₀}.Finite :=
    hSfin.subset fun q hq => by
      have hq' : (h q).re = M₀ := hq
      show (h q₀).re / 2 < (h q).re
      linarith
  set F := hTfin.toFinset with hF
  have hmemF : ∀ q, q ∈ F ↔ (h q).re = M₀ := fun q => by
    rw [hF, Set.Finite.mem_toFinset]; rfl
  have hqmF : qm ∈ F := (hmemF qm).mpr rfl
  set c := ∑ q ∈ F, (w q).re with hcdef
  have hc0 : 0 < c := Finset.sum_pos (fun q _ => hwre q) ⟨qm, hqmF⟩
  refine ⟨M₀, hM₀, c / 2, by positivity, fun N₀ => ?_⟩
  set W := ∑' q : ι, ‖w q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  have hFW : ∑ q ∈ F, ‖w q‖ ≤ W :=
    hws.sum_le_tsum F fun q _ => norm_nonneg _
  -- (2) the resolution of the simultaneous approximation
  set Q : ℕ := ⌈8 * π * W / c⌉₊ + 1 with hQdef
  have hQ0 : 0 < Q := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQW : W * (2 * π / Q) ≤ c / 4 := by
    have hQge : 8 * π * W / c ≤ Q := by
      have := Nat.le_ceil (8 * π * W / c)
      rw [hQdef]; push_cast; linarith
    rw [← mul_div_assoc, div_le_iff₀ hQpos]
    have := (div_le_iff₀ hc0).mp hQge
    nlinarith [Real.pi_pos]
  -- (3) the lower tail tends to zero
  set tail : ℕ → ℝ := fun n => ∑' q : ↑(↑F : Set ι)ᶜ,
      ‖w q‖ * Real.exp (-((n : ℝ) * (M₀ - (h q).re))) with htaildef
  have htail : Tendsto tail atTop (𝓝 0) := by
    have hd := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun (n : ℕ) (q : ↑(↑F : Set ι)ᶜ) =>
        ‖w q‖ * Real.exp (-((n : ℝ) * (M₀ - (h q).re))))
      (g := fun _ => 0) (bound := fun q : ↑(↑F : Set ι)ᶜ => ‖w q‖)
      (hws.subtype _) ?_ ?_
    · rw [tsum_zero] at hd
      exact hd
    · intro q
      have hlt : (h q).re < M₀ :=
        lt_of_le_of_ne (hmax q) fun he => q.2 (Finset.mem_coe.mpr ((hmemF q).mpr he))
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (M₀ - (h q).re)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul ‖w q‖
      simp only [mul_zero] at h2
      exact h2
    · filter_upwards with n q
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_pos (Real.exp_pos _)]
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      have := hmax q
      have : 0 ≤ (n : ℝ) * (M₀ - (h q).re) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
      linarith
  -- (4) the scale `N`
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (htail.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < c / 4)))
  set N := max N₁ N₀ + 1 with hNdef
  -- (5) Dirichlet on the top phases
  let e := F.equivFin
  let β : Fin F.card → ℝ := fun i => N * (h (e.symm i).1).im * 1 / (2 * π)
  obtain ⟨m', hm'1, -, hclose⟩ := exists_simultaneous_dirichlet β hQ0
  set n := N * m' with hndef
  have hnN : N ≤ n := Nat.le_mul_of_pos_right N hm'1
  refine ⟨n, by omega, ?_⟩
  have hphase : ∀ q ∈ F,
      ‖Complex.exp (I * ((((N * m' : ℕ) : ℝ) * 1 * (h q).im : ℝ) : ℂ)) - 1‖ ≤ 2 * π / Q := by
    intro q hq
    have hc' := hclose (e ⟨q, hq⟩)
    have hβ' : β (e ⟨q, hq⟩) = N * (h q).im * 1 / (2 * π) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ'] at hc'
    exact norm_exp_phase_sub_one_le hc'
  -- (6) the value as a top part plus a lower part
  set f : ι → ℂ := fun q => w q * Complex.exp ((n : ℂ) * h q) with hfdef
  have hf : Summable f := summable_mul_exp_of_compressing hws hc n
  have hval : (∑' i, w i * Complex.exp ((n : ℂ) * h i)).re
      = (∑ q ∈ F, f q).re + (∑' q : ↑(↑F : Set ι)ᶜ, f q).re := by
    rw [← hf.sum_add_tsum_compl (s := F), Complex.add_re]
  have hexpTop : ∀ q ∈ F, Complex.exp ((n : ℂ) * h q) = (Real.exp ((n : ℝ) * M₀) : ℂ) *
      Complex.exp (I * ((((N * m' : ℕ) : ℝ) * 1 * (h q).im : ℝ) : ℂ)) := by
    intro q hq
    have hre : (h q).re = M₀ := (hmemF q).mp hq
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext
    · simp [Complex.mul_re, hre, hndef]
    · simp [Complex.mul_im, hndef]
  have htopre : ∀ q ∈ F,
      Real.exp ((n : ℝ) * M₀) * ((w q).re - ‖w q‖ * (2 * π / Q)) ≤ (f q).re := by
    intro q hq
    set ph := Complex.exp (I * ((((N * m' : ℕ) : ℝ) * 1 * (h q).im : ℝ) : ℂ)) with hph
    have hsplit : f q = (Real.exp ((n : ℝ) * M₀) : ℂ) * (w q + w q * (ph - 1)) := by
      rw [hfdef]
      simp only
      rw [hexpTop q hq]
      ring
    rw [hsplit, Complex.re_ofReal_mul, Complex.add_re]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h1 := neg_le_of_abs_le (Complex.abs_re_le_norm (w q * (ph - 1)))
    rw [norm_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hphase q hq) (norm_nonneg (w q))
    linarith
  have htop : Real.exp ((n : ℝ) * M₀) * (3 * c / 4) ≤ (∑ q ∈ F, f q).re := by
    rw [Complex.re_sum]
    have h1 := Finset.sum_le_sum htopre
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul] at h1
    have h2 : (∑ q ∈ F, ‖w q‖) * (2 * π / Q) ≤ W * (2 * π / Q) :=
      mul_le_mul_of_nonneg_right hFW (by positivity)
    have h3 : 3 * c / 4 ≤ (∑ q ∈ F, (w q).re) - (∑ q ∈ F, ‖w q‖) * (2 * π / Q) := by
      rw [← hcdef]
      linarith
    exact (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le).trans h1
  have hlow : |(∑' q : ↑(↑F : Set ι)ᶜ, f q).re| ≤ Real.exp ((n : ℝ) * M₀) * tail n := by
    have hsum : Summable fun q : ↑(↑F : Set ι)ᶜ => f q := hf.subtype _
    have hterm : ∀ q : ↑(↑F : Set ι)ᶜ, ‖f q‖ = Real.exp ((n : ℝ) * M₀) *
        (‖w q‖ * Real.exp (-((n : ℝ) * (M₀ - (h q).re)))) := by
      intro q
      rw [hfdef]
      simp only
      rw [norm_mul, Complex.norm_exp, re_natCast_mul_multiplier,
        show (n : ℝ) * (h q).re = (n : ℝ) * M₀ + -((n : ℝ) * (M₀ - (h q).re)) by ring,
        Real.exp_add]
      ring
    have h1 := (Complex.abs_re_le_norm _).trans (norm_tsum_le_tsum_norm hsum.norm)
    rw [tsum_congr hterm, tsum_mul_left] at h1
    exact h1
  -- (7) the numerics
  have htailn : tail n ≤ c / 4 := hN₁ n (by omega)
  rw [hval]
  have hl := (abs_le.mp hlow).1
  have hE := Real.exp_pos ((n : ℝ) * M₀)
  nlinarith [mul_le_mul_of_nonneg_left htailn hE.le]

/-- **A positive value of a compressing multiplier is detected along the integers, at its
exponential rate.**  `Re R_h(n) ≥ (c/2) e^{n M₀}` beyond every index, where `M₀ = max Re h > 0` and
`c = Σ_{Re h = M₀} Re(1/(ρ(1−ρ))) > 0`. -/
theorem exists_compressedLag_ge_exp {h : XiZeroCopy → ℂ} (hc : IsCompressingMultiplier h)
    (hpos : ∃ q : XiZeroCopy, 0 < (h q).re) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      c * Real.exp ((n : ℝ) * M₀) ≤ (compressedLag h n).re :=
  exists_re_tsum_mul_exp_ge (fun q => lagWeight_re_pos q) summable_norm_lagWeight hc hpos

theorem summable_compressedLag_term {h : XiZeroCopy → ℂ} (hc : IsCompressingMultiplier h)
    (n : ℕ) : Summable fun q : XiZeroCopy => lagWeight q * Complex.exp ((n : ℂ) * h q) :=
  summable_mul_exp_of_compressing summable_norm_lagWeight hc n

/-- **A positive value of a compressing multiplier is detected along the integers.** -/
theorem exists_compressedLag_gt {h : XiZeroCopy → ℂ} (hc : IsCompressingMultiplier h)
    (hpos : ∃ q : XiZeroCopy, 0 < (h q).re) (M : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ M < (compressedLag h n).re := by
  obtain ⟨M₀, hM₀, c, hc0, hgrow⟩ := exists_compressedLag_ge_exp hc hpos
  have hexp_unb : Tendsto (fun n : ℕ => c * Real.exp ((n : ℝ) * M₀)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hM₀)).const_mul_atTop
      hc0
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hexp_unb.eventually_gt_atTop M)
  obtain ⟨n, hn, hle⟩ := hgrow (N₂ + 1)
  exact ⟨n, by omega, (hN₂ n (by omega)).trans_le hle⟩

/-- Under RH every compressed lag of a multiplier with `Re h ≤ 0` on the critical line is bounded
in absolute value by the total lag weight. -/
theorem abs_re_compressedLag_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    {h : XiZeroCopy → ℂ} (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re ≤ 0)
    (n : ℕ) : |(compressedLag h n).re| ≤ ∑' q : XiZeroCopy, ‖lagWeight q‖ := by
  have hle : ∀ q : XiZeroCopy, ‖lagWeight q * Complex.exp ((n : ℂ) * h q)‖ ≤ ‖lagWeight q‖ := by
    intro q
    rw [norm_mul, Complex.norm_exp, re_natCast_mul_multiplier]
    refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
    have := hline q (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) this
  have hs : Summable fun q : XiZeroCopy => lagWeight q * Complex.exp ((n : ℂ) * h q) :=
    summable_norm_lagWeight.of_norm_bounded hle
  exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hs.norm).trans
    (Summable.tsum_le_tsum hle hs.norm summable_norm_lagWeight))

/-- **Compressed-lag criterion.**  Let `Re h ≤ 0` on the critical line and `Re h > 0` to its right.
RH holds if and only if `h` is compressing and its compressed lag is bounded above along the
integers. -/
theorem riemannHypothesis_iff_isCompressing_and_bddAbove {h : XiZeroCopy → ℂ}
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re ≤ 0)
    (hright : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → 0 < (h q).re) :
    RiemannHypothesis ↔
      IsCompressingMultiplier h ∧ ∃ M : ℝ, ∀ n : ℕ, (compressedLag h n).re ≤ M := by
  constructor
  · intro hRH
    refine ⟨fun ε hε => Set.finite_empty.subset fun q hq => ?_, ⟨_, fun n =>
      (le_abs_self _).trans (abs_re_compressedLag_le_of_riemannHypothesis hRH hline n)⟩⟩
    have h1 := hline q (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
    have h2 : ε < (h q).re := hq
    exfalso
    linarith
  · rintro ⟨hc, M, hM⟩
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    obtain ⟨n, -, hn⟩ := exists_compressedLag_gt hc ⟨q, hright q hq⟩ M
    exact absurd (hM n) (not_le.mpr hn)

/-- For an unconditionally compressing multiplier the criterion needs no condition on the zeros. -/
theorem riemannHypothesis_iff_bddAbove_compressedLag {h : XiZeroCopy → ℂ}
    (hc : IsCompressingMultiplier h)
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re ≤ 0)
    (hright : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → 0 < (h q).re) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n : ℕ, (compressedLag h n).re ≤ M := by
  rw [riemannHypothesis_iff_isCompressing_and_bddAbove hline hright]
  exact ⟨fun h' => h'.2, fun h' => ⟨hc, h'⟩⟩

/-- **Subexponential slack suffices for compressing multipliers.**  Let `Re h ≤ 0` on the critical
line, `Re h > 0` to its right, and `h` compressing.  RH holds if and only if for every `ε > 0` the
compressed lag satisfies `Re R_h(n) ≤ C e^{εn}` along the integers. -/
theorem riemannHypothesis_iff_compressedLag_subexponential {h : XiZeroCopy → ℂ}
    (hc : IsCompressingMultiplier h)
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re ≤ 0)
    (hright : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → 0 < (h q).re) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
      (compressedLag h n).re ≤ C * Real.exp (ε * n) := by
  constructor
  · intro hRH ε hε
    refine ⟨∑' q : XiZeroCopy, ‖lagWeight q‖, fun n => ?_⟩
    have h1 := (le_abs_self _).trans (abs_re_compressedLag_le_of_riemannHypothesis hRH hline n)
    have h0 : 0 ≤ ∑' q : XiZeroCopy, ‖lagWeight q‖ := tsum_nonneg fun q => norm_nonneg _
    have h2 : 1 ≤ Real.exp (ε * n) := Real.one_le_exp (by positivity)
    nlinarith
  · intro hsub
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    obtain ⟨M₀, hM₀, c, hc0, hgrow⟩ := exists_compressedLag_ge_exp hc ⟨q, hright q hq⟩
    obtain ⟨C, hC⟩ := hsub (M₀ / 2) (by positivity)
    have hunb : Tendsto (fun n : ℕ => c * Real.exp ((n : ℝ) * (M₀ / 2))) atTop atTop :=
      (Real.tendsto_exp_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))).const_mul_atTop hc0
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hunb.eventually_gt_atTop C)
    obtain ⟨n, hn, hle⟩ := hgrow N₀
    have hupper := hC n
    have hsplit : Real.exp ((n : ℝ) * M₀)
        = Real.exp ((n : ℝ) * (M₀ / 2)) * Real.exp (M₀ / 2 * n) := by
      rw [← Real.exp_add]; ring_nf
    have hbig := hN₀ n hn
    have hpos := Real.exp_pos (M₀ / 2 * (n : ℝ))
    rw [hsplit] at hle
    nlinarith

/-! ## The lag multiplier: compression is the approach of the zeros to the line -/

/-- The lag multiplier `ℓ(ρ − ½)`; its compressed lag is the lag progression `Φ(nℓ)`. -/
def lagMultiplier (ℓ : ℝ) (q : XiZeroCopy) : ℂ := (ℓ : ℂ) * ((q.1 : ℂ) - 1 / 2)

theorem re_lagMultiplier (ℓ : ℝ) (q : XiZeroCopy) :
    (lagMultiplier ℓ q).re = ℓ * ((q.1 : ℂ).re - 1 / 2) := by
  simp [lagMultiplier, Complex.mul_re]

theorem compressedLag_lagMultiplier (ℓ : ℝ) (n : ℕ) :
    compressedLag (lagMultiplier ℓ) n = weilLagFunction ((n : ℝ) * ℓ) := by
  rw [weilLagFunction_eq_tsum_lagWeight, compressedLag]
  refine tsum_congr fun q => ?_
  rw [lagMultiplier]
  push_cast
  ring_nf

/-- **For the lag multiplier, compression is exactly the approach of the zeros to the line.** -/
theorem isCompressingMultiplier_lagMultiplier_iff {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsCompressingMultiplier (lagMultiplier ℓ) ↔ ZerosApproachLine := by
  constructor
  · intro hc η hη
    refine ((hc (ℓ * η) (by positivity)).preimage
      (xiZeroCopyReflectEquiv.injective.injOn)).subset fun q hq => ?_
    have hq' : η < (xiSpectralPoint q).im := hq
    rw [spectral_im_eq] at hq'
    show ℓ * η < (lagMultiplier ℓ (xiZeroCopyReflectEquiv q)).re
    rw [re_lagMultiplier, xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re]
    nlinarith
  · intro hZ ε hε
    refine (finite_abs_im_gt_of_zerosApproachLine hZ (div_pos hε hℓ)).subset fun q hq => ?_
    have hq' : ε < (lagMultiplier ℓ q).re := hq
    rw [re_lagMultiplier] at hq'
    show ε / ℓ < |(xiSpectralPoint q).im|
    rw [spectral_im_eq, abs_sub_comm, div_lt_iff₀ hℓ]
    calc ε < ℓ * ((q.1 : ℂ).re - 1 / 2) := hq'
      _ ≤ ℓ * |(q.1 : ℂ).re - 1 / 2| := mul_le_mul_of_nonneg_left (le_abs_self _) hℓ.le
      _ = |(q.1 : ℂ).re - 1 / 2| * ℓ := mul_comm _ _

/-- The general criterion specialised to the lag multiplier: RH holds if and only if the zeros
approach the line and one lag progression is bounded above. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_lagProgression_bddAbove {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    RiemannHypothesis ↔
      ZerosApproachLine ∧ ∃ M : ℝ, ∀ n : ℕ, (weilLagFunction ((n : ℝ) * ℓ)).re ≤ M := by
  rw [riemannHypothesis_iff_isCompressing_and_bddAbove (h := lagMultiplier ℓ)
    (fun q hq => by rw [re_lagMultiplier, hq]; simp)
    (fun q hq => by rw [re_lagMultiplier]; nlinarith),
    isCompressingMultiplier_lagMultiplier_iff hℓ]
  simp_rw [compressedLag_lagMultiplier]

/-! ## A logarithmically compressing multiplier -/

/-- `|arg w| ≤ |Im w| / Re w` on the right half-plane. -/
private theorem abs_arg_le_abs_im_div_re_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    |w.arg| ≤ |w.im| / w.re := by
  have hlt : |w.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have htan : Real.tan |w.arg| = |w.im| / w.re := by
    rcases le_or_gt 0 w.arg with h | h
    · rw [abs_of_nonneg h, Complex.tan_arg, abs_of_nonneg (Complex.arg_nonneg_iff.mp h)]
    · rw [abs_of_neg h, Real.tan_neg, Complex.tan_arg, abs_of_neg (Complex.arg_neg_iff.mp h),
        neg_div]
  rw [← htan]
  exact Real.le_tan (abs_nonneg _) hlt

/-- `log u − 2y²/u > 0` for `u = 2 − x² + y²` and `x² ≤ ¼`. -/
theorem log_sub_two_mul_sq_div_pos {x y : ℝ} (hx : x ^ 2 ≤ 1 / 4) :
    0 < Real.log (2 - x ^ 2 + y ^ 2) - 2 * y ^ 2 / (2 - x ^ 2 + y ^ 2) := by
  set b := 2 - x ^ 2 with hb
  have hb74 : 7 / 4 ≤ b := by rw [hb]; linarith
  set u := b + y ^ 2 with hu
  have hu0 : 0 < u := by rw [hu]; nlinarith [sq_nonneg y]
  have h2b : 0 < 2 * b := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hu0 h2b)
  rw [Real.log_div hu0.ne' h2b.ne', inv_div] at hlog
  have h72 : 1 < Real.log (7 / 2) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hlog2b : Real.log (7 / 2) ≤ Real.log (2 * b) := Real.log_le_log (by norm_num) (by linarith)
  have hfrac : 2 * y ^ 2 / u = 2 - 2 * b / u := by
    field_simp
    rw [hu]
    ring
  rw [hfrac]
  linarith

/-- The logarithmically compressing multiplier `H(z) = z / log(2 − z²)`. -/
def logCompressedMultiplier (z : ℂ) : ℂ := z / Complex.log (2 - z ^ 2)

theorem two_sub_sq_re (z : ℂ) : (2 - z ^ 2).re = 2 - z.re ^ 2 + z.im ^ 2 := by
  simp [sq, Complex.mul_re]
  ring

theorem two_sub_sq_im (z : ℂ) : (2 - z ^ 2).im = -(2 * z.re * z.im) := by
  simp [sq, Complex.mul_im]
  ring

theorem re_logCompressedMultiplier (z : ℂ) :
    (logCompressedMultiplier z).re = (z.re * Real.log ‖2 - z ^ 2‖ + z.im * (2 - z ^ 2).arg)
      / Complex.normSq (Complex.log (2 - z ^ 2)) := by
  rw [logCompressedMultiplier, Complex.div_re, Complex.log_re, Complex.log_im]
  ring

/-- The three estimates behind the sign and the decay of `Re H` on `|Re z| ≤ ½`. -/
theorem logCompressedMultiplier_estimates {z : ℂ} (hx : z.re ^ 2 ≤ 1 / 4) :
    Real.log (7 / 4 + z.im ^ 2) ≤ Real.log (2 - z.re ^ 2 + z.im ^ 2) ∧
      Real.log (2 - z.re ^ 2 + z.im ^ 2) ≤ Real.log ‖2 - z ^ 2‖ ∧
      |z.im * (2 - z ^ 2).arg| ≤ 2 * |z.re| * (z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2)) := by
  have hre := two_sub_sq_re z
  have him := two_sub_sq_im z
  have hu : 0 < 2 - z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  have hw : 0 < (2 - z ^ 2).re := by rw [hre]; exact hu
  refine ⟨Real.log_le_log (by positivity) (by linarith), ?_, ?_⟩
  · have h := Real.log_le_log hw (Complex.re_le_norm (2 - z ^ 2))
    rwa [hre] at h
  · have harg := abs_arg_le_abs_im_div_re_of_re_pos hw
    rw [abs_mul]
    calc |z.im| * |(2 - z ^ 2).arg| ≤ |z.im| * (|(2 - z ^ 2).im| / (2 - z ^ 2).re) :=
          mul_le_mul_of_nonneg_left harg (abs_nonneg _)
      _ = 2 * |z.re| * (z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2)) := by
          rw [him, hre, abs_neg, abs_mul, abs_mul, abs_two, ← sq_abs z.im]
          ring

/-- `log ‖2 − z²‖ > 0` and `normSq (log(2 − z²)) ≥ (log ‖2 − z²‖)²` on `|Re z| ≤ ½`. -/
theorem log_norm_two_sub_sq_pos {z : ℂ} (hx : z.re ^ 2 ≤ 1 / 4) :
    0 < Real.log ‖2 - z ^ 2‖ ∧
      Real.log ‖2 - z ^ 2‖ ^ 2 ≤ Complex.normSq (Complex.log (2 - z ^ 2)) := by
  obtain ⟨h1, h2, -⟩ := logCompressedMultiplier_estimates hx
  have h74 : 0 < Real.log (7 / 4 + z.im ^ 2) :=
    Real.log_pos (by nlinarith [sq_nonneg z.im])
  refine ⟨by linarith, ?_⟩
  rw [Complex.normSq_apply, Complex.log_re]
  nlinarith [sq_nonneg (Complex.log (2 - z ^ 2)).im]

/-- `Re H(z) > 0` for `0 < Re z ≤ ½`. -/
theorem re_logCompressedMultiplier_pos {z : ℂ} (hx0 : 0 < z.re) (hx : z.re ^ 2 ≤ 1 / 4) :
    0 < (logCompressedMultiplier z).re := by
  obtain ⟨-, h2, h3⟩ := logCompressedMultiplier_estimates hx
  obtain ⟨hl, hn⟩ := log_norm_two_sub_sq_pos hx
  have hkey := log_sub_two_mul_sq_div_pos (x := z.re) (y := z.im) hx
  rw [re_logCompressedMultiplier]
  apply div_pos _ (lt_of_lt_of_le (by positivity) hn)
  rw [abs_of_pos hx0] at h3
  have h4 := neg_le_of_abs_le h3
  have h5 : z.re * Real.log (2 - z.re ^ 2 + z.im ^ 2) ≤ z.re * Real.log ‖2 - z ^ 2‖ :=
    mul_le_mul_of_nonneg_left h2 hx0.le
  have h6 : 0 < z.re * (Real.log (2 - z.re ^ 2 + z.im ^ 2)
      - 2 * z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2)) := mul_pos hx0 hkey
  have e : 2 * z.re * (z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2))
      = z.re * (2 * z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2)) := by ring
  rw [e] at h4
  nlinarith

/-- `Re H(z) ≤ 0` for `−½ ≤ Re z ≤ 0`. -/
theorem re_logCompressedMultiplier_nonpos {z : ℂ} (hx0 : z.re ≤ 0) (hx : z.re ^ 2 ≤ 1 / 4) :
    (logCompressedMultiplier z).re ≤ 0 := by
  obtain ⟨-, h2, h3⟩ := logCompressedMultiplier_estimates hx
  obtain ⟨-, hn⟩ := log_norm_two_sub_sq_pos hx
  have hkey := log_sub_two_mul_sq_div_pos (x := z.re) (y := z.im) hx
  rw [re_logCompressedMultiplier]
  apply div_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
  rw [abs_of_nonpos hx0] at h3
  have h4 := le_of_abs_le h3
  have h5 : z.re * Real.log ‖2 - z ^ 2‖ ≤ z.re * Real.log (2 - z.re ^ 2 + z.im ^ 2) :=
    mul_le_mul_of_nonpos_left h2 hx0
  have h6 : z.re * (Real.log (2 - z.re ^ 2 + z.im ^ 2)
      - 2 * z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hx0 hkey.le
  have e : 2 * -z.re * (z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2))
      = -(z.re * (2 * z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2))) := by ring
  rw [e] at h4
  nlinarith

/-- **Logarithmic compression.**  `Re H(x + iy) ≤ 3x / log(7/4 + y²)` for `0 ≤ x ≤ ½` once
`log(7/4 + y²) ≥ 1`. -/
theorem re_logCompressedMultiplier_le {z : ℂ} (hx0 : 0 ≤ z.re) (hx : z.re ^ 2 ≤ 1 / 4)
    (hL : 1 ≤ Real.log (7 / 4 + z.im ^ 2)) :
    (logCompressedMultiplier z).re ≤ 3 * z.re / Real.log (7 / 4 + z.im ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := logCompressedMultiplier_estimates hx
  obtain ⟨hl, hn⟩ := log_norm_two_sub_sq_pos hx
  set ℓ := Real.log ‖2 - z ^ 2‖ with hℓ
  set L₀ := Real.log (7 / 4 + z.im ^ 2) with hL₀
  have hℓL : L₀ ≤ ℓ := h1.trans h2
  have hℓ1 : 1 ≤ ℓ := hL.trans hℓL
  have hu : 0 < 2 - z.re ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg z.im]
  have hfr : z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2) ≤ 1 := by
    rw [div_le_one hu]; linarith
  rw [abs_of_nonneg hx0] at h3
  have h4 := le_of_abs_le h3
  have hnum : z.re * ℓ + z.im * (2 - z ^ 2).arg ≤ 3 * z.re * ℓ := by
    have : 2 * z.re * (z.im ^ 2 / (2 - z.re ^ 2 + z.im ^ 2)) ≤ 2 * z.re :=
      by nlinarith
    nlinarith
  rw [re_logCompressedMultiplier, ← hℓ]
  have hden : 0 < ℓ ^ 2 := by positivity
  calc (z.re * ℓ + z.im * (2 - z ^ 2).arg) / Complex.normSq (Complex.log (2 - z ^ 2))
      ≤ 3 * z.re * ℓ / Complex.normSq (Complex.log (2 - z ^ 2)) :=
        div_le_div_of_nonneg_right hnum (Complex.normSq_nonneg _)
    _ ≤ 3 * z.re * ℓ / ℓ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) hden hn
    _ = 3 * z.re / ℓ := by field_simp
    _ ≤ 3 * z.re / L₀ :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hℓL

/-- The multiplier `H(ρ − ½)` on the zero copies. -/
def logCompressedZeroMultiplier (q : XiZeroCopy) : ℂ := logCompressedMultiplier ((q.1 : ℂ) - 1 / 2)

theorem re_sub_half_sq_le (q : XiZeroCopy) : (((q.1 : ℂ) - 1 / 2).re) ^ 2 ≤ 1 / 4 := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have e : ((q.1 : ℂ) - 1 / 2).re = (q.1 : ℂ).re - 1 / 2 := by simp
  rw [e]
  nlinarith

theorem re_logCompressedZeroMultiplier_nonpos {q : XiZeroCopy} (hq : (q.1 : ℂ).re ≤ 1 / 2) :
    (logCompressedZeroMultiplier q).re ≤ 0 :=
  re_logCompressedMultiplier_nonpos (by simp; linarith) (re_sub_half_sq_le q)

theorem re_logCompressedZeroMultiplier_pos {q : XiZeroCopy} (hq : 1 / 2 < (q.1 : ℂ).re) :
    0 < (logCompressedZeroMultiplier q).re :=
  re_logCompressedMultiplier_pos (by simp; linarith) (re_sub_half_sq_le q)

/-- **Compression in ordinate form.**  If `0 ≤ Re z ≤ ½` and `Re H(z) > ε > 0`, then
`|Im z| ≤ 1 + exp(max 1 (3/(2ε)))`. -/
theorem abs_im_le_of_lt_re_logCompressedMultiplier {z : ℂ} (hx0 : 0 ≤ z.re)
    (hx : z.re ^ 2 ≤ 1 / 4) {ε : ℝ} (hε : 0 < ε) (h : ε < (logCompressedMultiplier z).re) :
    |z.im| ≤ 1 + Real.exp (max 1 (3 / (2 * ε))) := by
  set K : ℝ := max 1 (3 / (2 * ε)) with hK
  have hx12 : z.re ≤ 1 / 2 := by nlinarith
  have hlogK : Real.log (7 / 4 + z.im ^ 2) < K := by
    by_contra hge
    push Not at hge
    have hL1 : 1 ≤ Real.log (7 / 4 + z.im ^ 2) := (le_max_left _ _).trans hge
    have hle := re_logCompressedMultiplier_le hx0 hx hL1
    have hLpos : 0 < Real.log (7 / 4 + z.im ^ 2) := by linarith
    have h32 : 3 / (2 * ε) ≤ Real.log (7 / 4 + z.im ^ 2) := (le_max_right _ _).trans hge
    have hbound : 3 * z.re / Real.log (7 / 4 + z.im ^ 2) ≤ ε := by
      rw [div_le_iff₀ hLpos]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε)).mp h32
      nlinarith
    linarith
  have hexp : 7 / 4 + z.im ^ 2 < Real.exp K :=
    (Real.log_lt_iff_lt_exp (by positivity)).mp hlogK
  nlinarith [sq_abs z.im, abs_nonneg z.im]

/-- **`H(ρ − ½)` is compressing, unconditionally.** -/
theorem isCompressingMultiplier_logCompressedZeroMultiplier :
    IsCompressingMultiplier logCompressedZeroMultiplier := by
  intro ε hε
  refine (finite_xiZeroCopy_band 0 (r := 1 + Real.exp (max 1 (3 / (2 * ε)))) (by positivity)).subset
    fun q hq => ?_
  have hq' : ε < (logCompressedZeroMultiplier q).re := hq
  have hright : 1 / 2 < (q.1 : ℂ).re := by
    by_contra hle
    push Not at hle
    linarith [re_logCompressedZeroMultiplier_nonpos hle]
  have hzre : ((q.1 : ℂ) - 1 / 2).re = (q.1 : ℂ).re - 1 / 2 := by simp
  have hzim : ((q.1 : ℂ) - 1 / 2).im = (q.1 : ℂ).im := by simp
  have h := abs_im_le_of_lt_re_logCompressedMultiplier (z := (q.1 : ℂ) - 1 / 2)
    (by rw [hzre]; linarith) (re_sub_half_sq_le q) hε hq'
  show |(q.1 : ℂ).im - 0| ≤ _
  rwa [sub_zero, ← hzim]

/-- **RH through a logarithmically compressed lag.**  With `H(z) = z / log(2 − z²)`, RH holds if
and only if `Re Σ_ρ e^{n H(ρ − ½)}/(ρ(1 − ρ))` is bounded above along the integers. -/
theorem riemannHypothesis_iff_bddAbove_logCompressedLag :
    RiemannHypothesis ↔
      ∃ M : ℝ, ∀ n : ℕ, (compressedLag logCompressedZeroMultiplier n).re ≤ M :=
  riemannHypothesis_iff_bddAbove_compressedLag isCompressingMultiplier_logCompressedZeroMultiplier
    (fun _ hq => re_logCompressedZeroMultiplier_nonpos hq.le)
    (fun _ hq => re_logCompressedZeroMultiplier_pos hq)

/-- **RH through a logarithmically compressed lag with subexponential slack.** -/
theorem riemannHypothesis_iff_logCompressedLag_subexponential :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
      (compressedLag logCompressedZeroMultiplier n).re ≤ C * Real.exp (ε * n) :=
  riemannHypothesis_iff_compressedLag_subexponential
    isCompressingMultiplier_logCompressedZeroMultiplier
    (fun _ hq => re_logCompressedZeroMultiplier_nonpos hq.le)
    (fun _ hq => re_logCompressedZeroMultiplier_pos hq)

end

end RHTower
