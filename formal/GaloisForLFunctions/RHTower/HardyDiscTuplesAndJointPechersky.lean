import GaloisForLFunctions.RHTower.PrimeSumDivergenceOfHorizontalExtent
import GaloisForLFunctions.RHTower.PecherskyDensityPrimeVectorsHardyDisc

/-!
# Tuples of Hardy-disc elements and the joint Pechersky approximation

Fix finitely many discs `|z − z i| < ρ i`, `i : ι`, each inside the strip
(`2ρ i − 2 Re (z i) < −1`, `Re (z i) + ρ i ≤ b < 1`).  The direct sum
`DiscTuple ι = PiLp 2 (fun _ : ι => HardyDisk)` carries the *prime tuples*
`u_p = (primeTerm (z i) (ρ i) p)_i`, square-summable over the primes, and the pairing of `u_p`
with a tuple `e` is `F_e(log p)`, where

  `F_e(ξ) = Σ_i exp(−conj(z i) ξ) · Φ_{e i}(ξ)`   (`tuplePairing`)

is entire, of exponential type, with `‖F_e(−x)‖ ≤ (Σ_i ‖e i‖) e^{bx}` on the negative ray.  The
horizontal-extent divergence lemma `exists_primeLogWeightedSum_gt_of_negRay` therefore makes
`Σ_{p<N} |⟪u_p, e⟫|` unbounded whenever `F_e ≢ 0`, whatever the vertical extent of the family.

Let `primeSpan` be the closed linear span of the prime tuples.  A tuple of `primeSpan` whose
pairings with the prime tuples are summable has `F_e ≡ 0`, hence is orthogonal to every prime
tuple, hence to `primeSpan`, hence vanishes.  So Pechersky's hypotheses hold in the Hilbert space
`primeSpan`, and the finite Pechersky lemma with prescribed initial phases gives: **every tuple of
`primeSpan` is within `ε` of a finite unimodular prime sum `Σ_{n<N} ω_n u_n`, with any finite initial
phase assignment** (`exists_unimodular_primeTuple_sum_approx_extend`).  This is the joint-phase
approximation on finitely many discs at once; which tuples lie in `primeSpan` is the subject of
the next module.
-/

open Complex Filter Topology Finset
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-! ## The direct sum and the prime tuples -/

/-- The direct sum of the Hardy spaces of the discs `i : ι`. -/
abbrev DiscTuple (ι : Type*) [Fintype ι] := PiLp 2 (fun _ : ι => HardyDisk)

/-- The tuple of prime vectors `(primeTerm (z i) (ρ i) n)_i`; zero for composite `n`. -/
def primeTuple (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (n : ℕ) : DiscTuple ι :=
  WithLp.toLp 2 fun i => primeTerm (z i) (hρ i) n

theorem primeTuple_apply (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (n : ℕ) (i : ι) :
    primeTuple z hρ n i = primeTerm (z i) (hρ i) n := rfl

theorem primeTuple_of_not_prime (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {n : ℕ}
    (hn : ¬ n.Prime) : primeTuple z hρ n = 0 := by
  ext i
  rw [primeTuple_apply, primeTerm_of_not_prime _ _ hn]
  rfl

theorem norm_primeTuple_sq (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (n : ℕ) :
    ‖primeTuple z hρ n‖ ^ 2 = ∑ i, ‖primeTerm (z i) (hρ i) n‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- **Square-summability of the prime tuples.** -/
theorem summable_norm_primeTuple_sq (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (hρσ : ∀ i, 2 * ρ i - 2 * (z i).re < -1) :
    Summable fun n => ‖primeTuple z hρ n‖ ^ 2 := by
  simp_rw [norm_primeTuple_sq]
  exact summable_sum fun i _ => summable_norm_primeTerm_sq (z i) (hρ i) (hρσ i)

/-! ## The pairing function -/

/-- `F_e(ξ) = Σ_i exp(−conj(z i) ξ) Φ_{e i}(ξ)`: the pairing of the prime tuples with `e`, read at
`ξ = log p`. -/
def tuplePairing (z : ι → ℂ) (ρ : ι → ℝ) (e : DiscTuple ι) (ξ : ℂ) : ℂ :=
  ∑ i, Complex.exp (-(conj (z i)) * ξ) * coefficientTransform (ρ i) (e i) ξ

theorem differentiable_tuplePairing (z : ι → ℂ) (ρ : ι → ℝ) (e : DiscTuple ι) :
    Differentiable ℂ (tuplePairing z ρ e) := by
  unfold tuplePairing
  refine Differentiable.fun_sum fun i _ => ?_
  exact (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id)).mul
    (differentiable_coefficientTransform (ρ i) (e i))

/-- `conj (n^{−z}) = exp(−conj z · log n)`. -/
theorem conj_natCast_cpow_neg {n : ℕ} (hn : 0 < n) (z : ℂ) :
    conj ((n : ℂ) ^ (-z)) = Complex.exp (-(conj z) * ((Real.log n : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.exp_conj, map_mul, map_neg]
  rw [show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast], Complex.conj_ofReal]
  ring_nf

/-- **The pairing with a prime tuple is `F_e(log p)`.** -/
theorem inner_primeTuple_of_prime (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {n : ℕ}
    (hn : n.Prime) (e : DiscTuple ι) :
    ⟪primeTuple z hρ n, e⟫_ℂ = tuplePairing z ρ e ((Real.log n : ℝ) : ℂ) := by
  rw [PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [primeTuple_apply, primeTerm_of_prime _ _ hn, inner_primeVector,
    conj_natCast_cpow_neg hn.pos]

/-- The partial absolute pairings are the prime sums of `F_e` with weight `σ = 0`. -/
theorem sum_norm_inner_primeTuple (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (e : DiscTuple ι)
    (N : ℕ) :
    ∑ n ∈ range N, ‖⟪primeTuple z hρ n, e⟫_ℂ‖ = primeLogWeightedSum (tuplePairing z ρ e) 0 N := by
  unfold primeLogWeightedSum
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · rw [if_pos hn, inner_primeTuple_of_prime z hρ hn, neg_zero, Real.rpow_zero, one_mul]
  · rw [if_neg hn, primeTuple_of_not_prime z hρ hn, inner_zero_left, norm_zero]

/-- Exponential type of the pairing function: `‖F_e ξ‖ ≤ (Σ‖e i‖) e^{τ‖ξ‖}` with
`τ = Σ_i (‖z i‖ + ρ i)`. -/
theorem norm_tuplePairing_le (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (e : DiscTuple ι)
    (ξ : ℂ) :
    ‖tuplePairing z ρ e ξ‖ ≤ (∑ i, ‖e i‖) * Real.exp ((∑ i, (‖z i‖ + ρ i)) * ‖ξ‖) := by
  unfold tuplePairing
  refine (norm_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  have hterm : ‖z i‖ + ρ i ≤ ∑ j, (‖z j‖ + ρ j) :=
    single_le_sum (f := fun j => ‖z j‖ + ρ j) (fun j _ => by have := hρ j; positivity)
      (mem_univ i)
  rw [norm_mul, Complex.norm_exp]
  have h1 : (-(conj (z i)) * ξ).re ≤ ‖z i‖ * ‖ξ‖ := by
    calc (-(conj (z i)) * ξ).re ≤ ‖-(conj (z i)) * ξ‖ := Complex.re_le_norm _
      _ = ‖z i‖ * ‖ξ‖ := by rw [norm_mul, norm_neg, Complex.norm_conj]
  calc Real.exp (-(conj (z i)) * ξ).re * ‖coefficientTransform (ρ i) (e i) ξ‖
      ≤ Real.exp (‖z i‖ * ‖ξ‖) * (‖e i‖ * Real.exp (ρ i * ‖ξ‖)) :=
        mul_le_mul (Real.exp_le_exp.mpr h1) (norm_coefficientTransform_le (hρ i) (e i) ξ)
          (norm_nonneg _) (Real.exp_pos _).le
    _ = ‖e i‖ * Real.exp ((‖z i‖ + ρ i) * ‖ξ‖) := by
        rw [add_mul, Real.exp_add]
        ring
    _ ≤ ‖e i‖ * Real.exp ((∑ j, (‖z j‖ + ρ j)) * ‖ξ‖) := by
        gcongr

/-- Negative-ray rate of the pairing function: `‖F_e(−x)‖ ≤ (Σ‖e i‖) e^{bx}` when
`Re (z i) + ρ i ≤ b` for all `i`. -/
theorem norm_tuplePairing_neg_le (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (e : DiscTuple ι)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) {x : ℝ} (hx : 0 ≤ x) :
    ‖tuplePairing z ρ e ((-x : ℝ) : ℂ)‖ ≤ (∑ i, ‖e i‖) * Real.exp (b * x) := by
  unfold tuplePairing
  refine (norm_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(conj (z i)) * ((-x : ℝ) : ℂ)).re = (z i).re * x := by
    simp [Complex.mul_re]
  have hnorm : ‖((-x : ℝ) : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hx]
  calc Real.exp (-(conj (z i)) * ((-x : ℝ) : ℂ)).re * ‖coefficientTransform (ρ i) (e i) ((-x : ℝ) : ℂ)‖
      ≤ Real.exp ((z i).re * x) * (‖e i‖ * Real.exp (ρ i * x)) := by
        rw [hre]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := norm_coefficientTransform_le (hρ i) (e i) ((-x : ℝ) : ℂ)
        rwa [hnorm] at this
    _ = ‖e i‖ * Real.exp (((z i).re + ρ i) * x) := by
        rw [add_mul, Real.exp_add]
        ring
    _ ≤ ‖e i‖ * Real.exp (b * x) := by
        gcongr
        exact hb i

/-- **Divergence of the absolute pairings** for every `e` with `F_e ≢ 0`, whatever the vertical
extent of the family: only `Re (z i) + ρ i ≤ b < 1` is used. -/
theorem exists_sum_norm_inner_primeTuple_gt (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {e : DiscTuple ι}
    (hne : tuplePairing z ρ e ≠ 0) (M : ℝ) :
    ∃ N : ℕ, M < ∑ n ∈ range N, ‖⟪primeTuple z hρ n, e⟫_ℂ‖ := by
  have hsum : 0 ≤ ∑ i, (‖z i‖ + ρ i) := sum_nonneg fun i _ => by
    have := hρ i
    positivity
  have hgrow : ∀ ξ : ℂ, ‖tuplePairing z ρ e ξ‖
      ≤ (∑ i, ‖e i‖ + 1) * Real.exp ((∑ i, (‖z i‖ + ρ i)) * ‖ξ‖) := fun ξ =>
    (norm_tuplePairing_le z hρ e ξ).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  have hneg : ∀ x : ℝ, 0 ≤ x → ‖tuplePairing z ρ e ((-x : ℝ) : ℂ)‖
      ≤ (∑ i, ‖e i‖ + 1) * Real.exp (b * x) := fun x hx =>
    (norm_tuplePairing_neg_le z hρ e hb hx).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  obtain ⟨N, hN⟩ := exists_primeLogWeightedSum_gt_of_negRay (differentiable_tuplePairing z ρ e)
    (σ := 0) hsum hgrow hne le_rfl hneg (by linarith) M
  exact ⟨N, by rwa [sum_norm_inner_primeTuple]⟩

/-! ## The closed span of the prime tuples -/

/-- The closed linear span of the prime tuples. -/
def primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) : Submodule ℂ (DiscTuple ι) :=
  (Submodule.span ℂ (Set.range (primeTuple z hρ))).topologicalClosure

instance instCompleteSpacePrimeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) :
    CompleteSpace (primeSpan z hρ) := by
  unfold primeSpan
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem primeTuple_mem_primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (n : ℕ) :
    primeTuple z hρ n ∈ primeSpan z hρ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

/-- A tuple is orthogonal to the closed span iff it is orthogonal to every prime tuple. -/
theorem mem_orthogonal_primeSpan_iff (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (e : DiscTuple ι) :
    e ∈ (primeSpan z hρ)ᗮ ↔ ∀ n, ⟪primeTuple z hρ n, e⟫_ℂ = 0 := by
  constructor
  · intro he n
    exact (Submodule.mem_orthogonal _ _).mp he _ (primeTuple_mem_primeSpan z hρ n)
  · intro h
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hle : primeSpan z hρ ≤ (ℂ ∙ e)ᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [← inner_conj_symm, h n, map_zero]
    have := hle hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
    exact this

/-- **Orthogonality to the prime tuples forces `F_e ≡ 0`**, by the divergence lemma. -/
theorem tuplePairing_eq_zero_of_mem_orthogonal (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {e : DiscTuple ι}
    (he : e ∈ (primeSpan z hρ)ᗮ) : tuplePairing z ρ e = 0 := by
  by_contra hne
  obtain ⟨N, hN⟩ := exists_sum_norm_inner_primeTuple_gt z hρ hb hb1 hne 0
  have h0 := (mem_orthogonal_primeSpan_iff z hρ e).mp he
  simp only [h0, norm_zero, sum_const_zero, lt_self_iff_false] at hN

/-- Conversely, `F_e ≡ 0` gives orthogonality to the closed span. -/
theorem mem_orthogonal_primeSpan_of_tuplePairing_eq_zero (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) {e : DiscTuple ι} (hF : tuplePairing z ρ e = 0) :
    e ∈ (primeSpan z hρ)ᗮ := by
  rw [mem_orthogonal_primeSpan_iff]
  intro n
  by_cases hn : n.Prime
  · rw [inner_primeTuple_of_prime z hρ hn, hF]
    rfl
  · rw [primeTuple_of_not_prime z hρ hn, inner_zero_left]

/-! ## The joint Pechersky approximation -/

/-- **Joint Pechersky approximation with prescribed initial phases.**  Every tuple `h` of the
closed span of the prime tuples is within `ε` of a finite unimodular prime sum
`Σ_{n<N} ω_n u_n`, `N ≥ N₁`, whose phases `ω_n` for `n < N₁` are any prescribed unimodular
values. -/
theorem exists_unimodular_primeTuple_sum_approx_extend (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) (hρσ : ∀ i, 2 * ρ i - 2 * (z i).re < -1) {b : ℝ}
    (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) {h : DiscTuple ι} (hh : h ∈ primeSpan z hρ)
    {ε : ℝ} (hε : 0 < ε) (N₁ : ℕ) (a₀ : ℕ → ℂ) (ha₀ : ∀ n, ‖a₀ n‖ = 1) :
    ∃ N : ℕ, N₁ ≤ N ∧ ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ = 1) ∧ (∀ n < N₁, a n = a₀ n) ∧
      ‖h - ∑ n ∈ range N, a n • primeTuple z hρ n‖ < ε := by
  let x : ℕ → primeSpan z hρ := fun n => ⟨primeTuple z hρ n, primeTuple_mem_primeSpan z hρ n⟩
  have hsum : Summable fun n => ‖x n‖ ^ 2 := by
    have := summable_norm_primeTuple_sq z hρ hρσ
    refine this.congr fun n => ?_
    rw [← Submodule.norm_coe]
  have hdiv : ∀ e : primeSpan z hρ, e ≠ 0 → ∀ M : ℝ,
      ∃ N : ℕ, M < ∑ n ∈ range N, ‖⟪x n, e⟫_ℂ‖ := by
    intro e he M
    have hFe : tuplePairing z ρ (e : DiscTuple ι) ≠ 0 := by
      intro hF
      apply he
      have h1 : (e : DiscTuple ι) ∈ (primeSpan z hρ)ᗮ :=
        mem_orthogonal_primeSpan_of_tuplePairing_eq_zero z hρ hF
      have h2 : (e : DiscTuple ι) ∈ primeSpan z hρ ⊓ (primeSpan z hρ)ᗮ := ⟨e.2, h1⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
      exact Subtype.ext h2
    obtain ⟨N, hN⟩ := exists_sum_norm_inner_primeTuple_gt z hρ hb hb1 hFe M
    exact ⟨N, by simpa only [Submodule.coe_inner] using hN⟩
  obtain ⟨N, hN, a, ha, ha₀', hclose⟩ :=
    exists_unimodular_finite_approx_extend x hsum hdiv ⟨h, hh⟩ hε N₁ a₀ ha₀
  refine ⟨N, hN, a, ha, ha₀', ?_⟩
  rw [← Submodule.norm_coe] at hclose
  simpa [x] using hclose

end RHTower
