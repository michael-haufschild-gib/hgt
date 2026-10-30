import Mathlib

/-!
# The two realizations of the primes

A realization of the primes is a dynamical system whose primitive periodic orbits have lengths
`log p`, one for each prime. Two exist for free, and they sit at opposite ends.

**The commutative realization**: one loop of length `log p` for each prime, disjoint. Its transfer
operator is diagonal with eigenvalues `p^{−s}` (`commEigen`), its `n`-th trace is
`Σ_p p^{−ns}` (`commTrace`), and its dynamical zeta function is the Euler product:
`exp Σ_n tr(L_sⁿ)/n = ζ(s)` on `Re s > 1` (`exp_tsum_commTrace_eq_riemannZeta`). The spectral
radius is `≤ 2^{−σ}`, below `1/2` on `σ ≥ 1`, and no eigenvalue equals `1` on `Re s > 0`
(`commEigen_ne_one`); the trace norm `P(σ) = Σ_p p^{−σ}` is finite exactly for `σ > 1`
(`summable_norm_commEigen_iff`) and tends to `+∞` as `σ ↓ 1` (`tendsto_primeZetaR_nhdsGT_one`).
The pole of `ζ` is a **nuclearity pole**, not an eigenvalue crossing (`commutative_pole_is_nuclear`).

**The free realization**: one vertex with a loop of length `log p` for each prime, i.e. the full
shift on the prime alphabet. Its periodic orbits of period `n` are the words of length `n`, so its
`n`-th trace is `P(σ)ⁿ` (`freeTrace_eq_pow`) and its zeta function is the renewal function
`exp Σ_n P(σ)ⁿ/n = (1 − P(σ))⁻¹` (`exp_tsum_freeTrace_eq`). `P` decreases strictly from `+∞` at
`1⁺` to `P(2) ≤ π²/6 − 1 < 1`, so the free realization has a **spectral pole** — the single
eigenvalue `P(σ)` crosses `1` — at a unique `σ* ∈ (1, 2)` (`free_pole_is_spectral`): free
dynamics overcounts and has the wrong entropy.

Every realization of `ζ` lies between these: commutativity gives the right zeta without dynamics,
freeness gives dynamics with the wrong zeta.
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-! ## The prime zeta function on the real axis -/

/-- `P(σ) = Σ_p p^{−σ}`: the trace norm of the commutative realization and the eigenvalue of the
free realization. -/
noncomputable def primeZetaR (σ : ℝ) : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ)

theorem one_lt_prime_cast (p : Nat.Primes) : (1 : ℝ) < ((p : ℕ) : ℝ) := by
  exact_mod_cast p.prop.one_lt

theorem summable_prime_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) :=
  Nat.Primes.summable_rpow.mpr (by linarith)

theorem primeZetaR_strictAntiOn : StrictAntiOn primeZetaR (Set.Ioi 1) := by
  intro σ hσ τ hτ hστ
  have h2 : (2 : ℕ).Prime := Nat.prime_two
  refine Summable.tsum_lt_tsum (i := ⟨2, h2⟩) (fun p => ?_) ?_ (summable_prime_rpow_neg hτ)
    (summable_prime_rpow_neg hσ)
  · exact Real.rpow_le_rpow_of_exponent_le (one_lt_prime_cast p).le (by linarith)
  · exact Real.rpow_lt_rpow_of_exponent_lt (one_lt_prime_cast _) (by linarith)

theorem continuousOn_primeZetaR {σ₀ : ℝ} (hσ₀ : 1 < σ₀) : ContinuousOn primeZetaR (Set.Ici σ₀) := by
  refine continuousOn_tsum (u := fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ₀))
    (fun p => ?_) (summable_prime_rpow_neg hσ₀) (fun p σ hσ => ?_)
  · exact (Continuous.rpow continuous_const continuous_neg
      fun _ => Or.inl (zero_lt_one.trans (one_lt_prime_cast p)).ne').continuousOn
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact Real.rpow_le_rpow_of_exponent_le (one_lt_prime_cast p).le (neg_le_neg hσ)

/-- **The prime zeta function blows up at `1`**: `P(σ) → +∞` as `σ ↓ 1`, because `Σ_p 1/p`
diverges. -/
theorem tendsto_primeZetaR_nhdsGT_one : Tendsto primeZetaR (𝓝[>] 1) atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  -- a finite set of primes whose reciprocals exceed `M + 1`
  have hns : ¬ Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
    fun h => (lt_irrefl (-1 : ℝ)) (Nat.Primes.summable_rpow.mp h)
  obtain ⟨S, hS⟩ : ∃ S : Finset Nat.Primes, M + 1 < ∑ p ∈ S, ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
    by_contra h
    push Not at h
    exact hns (summable_of_sum_le (fun p => Real.rpow_nonneg (by positivity) _) h)
  -- the finite sum is continuous in `σ`
  have hcont : Continuous fun σ : ℝ => ∑ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) :=
    continuous_finsetSum _ fun p _ => Continuous.rpow continuous_const continuous_neg
      fun _ => Or.inl (zero_lt_one.trans (one_lt_prime_cast p)).ne'
  have hev : ∀ᶠ σ in 𝓝 (1 : ℝ), M < ∑ p ∈ S, ((p : ℕ) : ℝ) ^ (-σ) :=
    hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with σ hσ hσ1
  exact hσ.le.trans (Summable.sum_le_tsum S (fun p _ => Real.rpow_nonneg (by positivity) _)
    (summable_prime_rpow_neg hσ1))

/-- `P(2) ≤ π²/6 − 1 < 1`. -/
theorem primeZetaR_two_lt_one : primeZetaR 2 < 1 := by
  -- compare with `Σ_{n ≥ 0} 1/(n + 2)² = π²/6 − 1` along the injection `p ↦ p − 2`
  have hsum : HasSum (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ)) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simpa [Finset.sum_range_succ] using h
  have hle : primeZetaR 2 ≤ Real.pi ^ 2 / 6 - 1 := by
    rw [← hsum.tsum_eq]
    refine Summable.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p : ℕ) - 2) ?_ ?_ (fun p => ?_)
      (summable_prime_rpow_neg one_lt_two) hsum.summable
    · intro p q hpq
      have := p.prop.two_le
      have := q.prop.two_le
      exact Subtype.ext (by simp only at hpq; omega)
    · intro n _; positivity
    · have h2 := p.prop.two_le
      rw [Nat.sub_add_cancel h2, Real.rpow_neg (by positivity), one_div]
      norm_cast
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-! ## The commutative realization -/

/-- The eigenvalue `p^{−s}` of the diagonal transfer operator of the commutative realization. -/
noncomputable def commEigen (s : ℂ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ (-s)

theorem norm_commEigen (s : ℂ) (p : Nat.Primes) :
    ‖commEigen s p‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [commEigen, Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]

/-- The spectral radius of the commutative transfer operator is at most `2^{−σ}`. -/
theorem norm_commEigen_le {s : ℂ} (hs : 0 ≤ s.re) (p : Nat.Primes) :
    ‖commEigen s p‖ ≤ 2 ^ (-s.re) := by
  rw [norm_commEigen]
  exact Real.rpow_le_rpow_of_nonpos two_pos (by exact_mod_cast p.prop.two_le) (by linarith)

theorem norm_commEigen_lt_one {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) : ‖commEigen s p‖ < 1 := by
  rw [norm_commEigen]
  exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_prime_cast p) (by linarith)

/-- No eigenvalue of the commutative transfer operator equals `1` on `Re s > 0`. -/
theorem commEigen_ne_one {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) : commEigen s p ≠ 1 := by
  intro h
  have := norm_commEigen_lt_one hs p
  rw [h, norm_one] at this
  exact lt_irrefl _ this

/-- The commutative transfer operator is trace class exactly on `Re s > 1`. -/
theorem summable_norm_commEigen_iff (s : ℂ) :
    Summable (fun p : Nat.Primes => ‖commEigen s p‖) ↔ 1 < s.re := by
  simp_rw [norm_commEigen]
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- The trace `tr(L_sⁿ) = Σ_p p^{−ns}` of the commutative transfer operator. -/
noncomputable def commTrace (s : ℂ) (n : ℕ) : ℂ := ∑' p : Nat.Primes, commEigen s p ^ n

/-- **The commutative realization realizes `ζ`.** On `Re s > 1`,
`exp Σ_{n ≥ 1} tr(L_sⁿ)/n = ζ(s)`. -/
theorem exp_tsum_commTrace_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' n : ℕ, commTrace s (n + 1) / ((n : ℂ) + 1)) = riemannZeta s := by
  have hs0 : 0 ≤ s.re := by linarith
  set f : Nat.Primes → ℕ → ℂ := fun p n => commEigen s p ^ (n + 1) / ((n : ℂ) + 1) with hf
  -- absolute summability of the double series
  have hhalf : ∀ p, ‖commEigen s p‖ ≤ 1 / 2 := fun p => by
    refine (norm_commEigen_le hs0 p).trans ?_
    calc (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one, one_div]
  have hbound : ∀ q : Nat.Primes × ℕ, ‖Function.uncurry f q‖ ≤
      ‖commEigen s q.1‖ * (1 / 2) ^ q.2 := by
    rintro ⟨p, n⟩
    simp only [Function.uncurry, hf, norm_div, norm_pow]
    have hn : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
      rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos n
    have h0 : 0 ≤ ‖commEigen s p‖ := norm_nonneg _
    calc ‖commEigen s p‖ ^ (n + 1) / ‖(n : ℂ) + 1‖ ≤ ‖commEigen s p‖ ^ (n + 1) :=
          div_le_self (pow_nonneg h0 _) hn
      _ = ‖commEigen s p‖ * ‖commEigen s p‖ ^ n := by ring
      _ ≤ ‖commEigen s p‖ * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hhalf p) n) h0
  have hsumm : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded (Summable.mul_of_nonneg ((summable_norm_commEigen_iff s).mpr hs)
      (summable_geometric_two) (fun _ => norm_nonneg _) (fun _ => by positivity)) hbound
  -- each prime contributes `−log(1 − p^{−s})`
  have hlog : ∀ p : Nat.Primes, ∑' n : ℕ, f p n = -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) := by
    intro p
    have h := Complex.hasSum_taylorSeries_neg_log (norm_commEigen_lt_one (by linarith) p)
    have h1 := (hasSum_nat_add_iff' 1).mpr h
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
      sub_zero] at h1
    refine (h1.congr_fun fun n => ?_).tsum_eq.trans ?_
    · simp [hf]
    · rfl
  have hswap : ∑' n : ℕ, commTrace s (n + 1) / ((n : ℂ) + 1) = ∑' p : Nat.Primes, ∑' n : ℕ, f p n := by
    rw [← hsumm.tsum_comm]
    refine tsum_congr fun n => ?_
    rw [commTrace, tsum_div_const]
  rw [hswap, tsum_congr hlog]
  exact riemannZeta_eulerProduct_exp_log hs

/-- **The pole of `ζ` is a nuclearity pole in the commutative realization.** On `σ ≥ 1` every
eigenvalue has modulus `≤ 1/2`, while the trace norm `P(σ)` tends to `+∞` as `σ ↓ 1`. -/
theorem commutative_pole_is_nuclear :
    (∀ s : ℂ, 1 ≤ s.re → ∀ p, ‖commEigen s p‖ ≤ 1 / 2) ∧
      Tendsto primeZetaR (𝓝[>] 1) atTop := by
  refine ⟨fun s hs p => (norm_commEigen_le (by linarith) p).trans ?_,
    tendsto_primeZetaR_nhdsGT_one⟩
  calc (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one, one_div]

/-! ## The free realization -/

/-- The `n`-th trace of the free realization: the sum over words `w` of length `n` in the prime
alphabet of `e^{−σ Σ_i log wᵢ}`. -/
noncomputable def freeTrace (σ : ℝ) (n : ℕ) : ℝ :=
  ∑' w : Fin n → Nat.Primes, ∏ i, ((w i : ℕ) : ℝ) ^ (-σ)

/-- Words in a summable nonnegative alphabet: `Σ_w Π_i g(wᵢ) = (Σ g)ⁿ`. -/
theorem hasSum_prod_words {β : Type*} {g : β → ℝ} (hg0 : ∀ b, 0 ≤ g b) {S : ℝ} (hg : HasSum g S)
    (n : ℕ) : HasSum (fun w : Fin n → β => ∏ i, g (w i)) (S ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsm : Summable fun x : β × (Fin n → β) => g x.1 * ∏ i, g (x.2 i) :=
      Summable.mul_of_nonneg (f := g) (g := fun w : Fin n → β => ∏ i, g (w i)) hg.summable
        ih.summable (fun b => hg0 b) (fun w => Finset.prod_nonneg fun i _ => hg0 (w i))
    have hmul : HasSum (fun x : β × (Fin n → β) => g x.1 * ∏ i, g (x.2 i)) (S * S ^ n) :=
      HasSum.mul (f := g) (g := fun w : Fin n → β => ∏ i, g (w i)) hg ih hsm
    -- a word of length `n + 1` is a letter followed by a word of length `n`
    have heq : (fun x : β × (Fin n → β) => g x.1 * ∏ i, g (x.2 i)) =
        (fun w : Fin (n + 1) → β => ∏ i, g (w i)) ∘ (Fin.consEquiv (n := n) fun _ => β) := by
      funext x; simp [Fin.prod_univ_succ]
    rw [heq] at hmul
    rw [pow_succ']
    exact (Fin.consEquiv (n := n) fun _ => β).hasSum_iff.mp hmul

theorem freeTrace_eq_pow {σ : ℝ} (hσ : 1 < σ) (n : ℕ) : freeTrace σ n = primeZetaR σ ^ n :=
  (hasSum_prod_words (fun p => Real.rpow_nonneg (by positivity) _)
    (summable_prime_rpow_neg hσ).hasSum n).tsum_eq

/-- **The free realization's zeta is the renewal function**: `exp Σ_n P(σ)ⁿ/n = (1 − P(σ))⁻¹`
where `P(σ) < 1`. -/
theorem exp_tsum_freeTrace_eq {σ : ℝ} (hσ : 1 < σ) (hP : primeZetaR σ < 1) :
    Real.exp (∑' n : ℕ, freeTrace σ (n + 1) / ((n : ℝ) + 1)) = (1 - primeZetaR σ)⁻¹ := by
  have hP0 : 0 ≤ primeZetaR σ :=
    tsum_nonneg fun p => Real.rpow_nonneg (by positivity) _
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (abs_lt.mpr ⟨by linarith, hP⟩)
  simp_rw [freeTrace_eq_pow hσ]
  rw [h.tsum_eq, Real.exp_neg, Real.exp_log (by linarith)]

/-- **The free realization has a spectral pole at an entropy `σ* ∈ (1, 2)`.** The eigenvalue
`P(σ)` of the one-vertex transfer operator crosses `1` at a unique `σ* > 1`, and the renewal zeta
`(1 − P(σ))⁻¹` tends to `+∞` as `σ ↓ σ*`. -/
theorem free_pole_is_spectral :
    ∃ σs : ℝ, 1 < σs ∧ σs < 2 ∧ primeZetaR σs = 1 ∧
      (∀ τ, 1 < τ → primeZetaR τ = 1 → τ = σs) ∧
      Tendsto (fun τ => (1 - primeZetaR τ)⁻¹) (𝓝[>] σs) atTop := by
  -- a point `σ₀ ∈ (1, 2)` with `P(σ₀) > 1`
  obtain ⟨σ₀, hσ₀P, hσ₀⟩ := ((tendsto_primeZetaR_nhdsGT_one.eventually (eventually_gt_atTop 1)).and
    (Ioo_mem_nhdsGT one_lt_two)).exists
  have h2 := primeZetaR_two_lt_one
  -- intermediate value on `[σ₀, 2]`
  obtain ⟨σs, ⟨hσs0, hσs2⟩, hσs⟩ := intermediate_value_Icc' hσ₀.2.le
    ((continuousOn_primeZetaR hσ₀.1).mono Set.Icc_subset_Ici_self) ⟨h2.le, hσ₀P.le⟩
  have hσs1 : 1 < σs := hσ₀.1.trans_le hσs0
  have hσslt2 : σs < 2 := lt_of_le_of_ne hσs2 (by rintro rfl; linarith)
  have hσ₀lt : σ₀ < σs := lt_of_le_of_ne hσs0 (by rintro rfl; linarith)
  refine ⟨σs, hσs1, hσslt2, hσs, fun τ hτ hPτ => ?_, ?_⟩
  · exact primeZetaR_strictAntiOn.injOn hτ hσs1 (hPτ.trans hσs.symm)
  · -- `1 − P(τ) → 0⁺` as `τ ↓ σs`
    have hcont : ContinuousAt primeZetaR σs :=
      (continuousOn_primeZetaR hσ₀.1).continuousAt (Ici_mem_nhds hσ₀lt)
    have hlim : Tendsto (fun τ => 1 - primeZetaR τ) (𝓝[>] σs) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := (tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝[>] σs)).sub
          (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        rwa [hσs, sub_self] at this
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        have := primeZetaR_strictAntiOn hσs1 (hσs1.trans hτ) hτ
        simp only [Set.mem_Ioi]; linarith
    exact tendsto_inv_nhdsGT_zero.comp hlim

end GaloisForLFunctions.ArithmeticResonanceTheory
