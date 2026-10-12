import GaloisForLFunctions.RHTower.JointAncestryRandomPhaseLargeDeviation
import GaloisForLFunctions.RHTower.WeilLagPrimeWindowMeanReceiver

/-!
# Parseval's identity for random-phase JAS aggregates

Test level-one JAS positivity on a finite set `P` of primes with the phase vectors
`z_p = r ω^{k_p}` (`ω = e^{2πi/N}`, `N ≥ 3`), and write `a = r/(1+r²)` and `Φ` for the lag function
`Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`.

**Theorem** (`sum_normSq_jasPhaseAggregate_sub_mean`).  The phase vectors have mean aggregate
`(1+r²)^{|P|} Φ(0)`, and the sum of squared deviations is exactly

`Σ_k |agg(k) − (1+r²)^{|P|}Φ(0)|² = (1+r²)^{2|P|} N^{|P|} Σ_{e ≠ 0} κ_e² Φ(L_e)²`.

The sum runs over the sign patterns `e : P → {0, +, −}`, with `κ_e = Π_{e_p ≠ 0} a/p` and the
signed lag `L_e = Σ_{e_p = −} log p − Σ_{e_p = +} log p`.  So random phases see the lag function
only through `Φ²`, at every signed prime-product lag.

**Variance law** (`abs_re_sub_half_le_of_phaseVariance`,
`exists_halfPlane_lt_half_iff_exists_phaseVariance`).  On the Huxley windows `(x, x + x^θ]`,
`7/12 < θ < 1`, the following are equivalent:
* the deviation sum is at most `C (1+r²)^{2|P|} N^{|P|} x^{2c−2} |P|` for some `c < ½`;
* there is a zero-free half-plane `Re s > 1 − ε`, `ε > 0`.
For every `c ≥ 0` the bound forces `|Re ρ − ½| ≤ c`, and RH holds iff the bound holds for every
`c > 0` (`riemannHypothesis_iff_forall_phaseVariance`).  So the phase average sees `Φ` only
through `Φ²`, yet a subpower phase variance is as strong as positivity at the constant vectors.

**Proof.**  Expand each factor `1 + a(ω^{k}A + ω^{−k}B)` as `Σ_{e ∈ {0,+,−}} χ_e(k) h_e`.  The
product over `P` is then a sum over sign patterns of the characters `χ_e(k) = Π_p χ_{e_p}(k_p)`
of `(ℤ/N)^P`.  These are orthonormal for `N ≥ 3`, so Parseval's identity applies.  The
coefficient of `χ_e` in the zero sum is `κ_e Φ(L_e)`, since `A_p = p^{−ρ−½}` and
`B_p = p^{ρ−3/2}` give `Π_+ A_p Π_− B_p = κ_e e^{L_e(ρ−½)}/a^{#e}`.  For the variance law, the
patterns of a single prime give `Σ_k |dev|² ≥ (1+r²)^{2|P|} N^{|P|} a² Σ_P Φ(log p)²/p²`.
Cauchy–Schwarz then bounds the signed window means, and the window-mean receiver
(`abs_re_sub_half_le_of_primeWindowMean`) applies.  The converse uses `|Φ(L)| ≤ M e^{α|L|}` and
`Σ_e κ_e² e^{2α|L_e|} = Π_p(1 + 2a²p^{2α−2}) − 1`.
-/

open Complex Filter
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Characters of the phase torus -/

/-- The phase characters `1, ω^j, ω^{−j}`, indexed by `e ∈ {0, 1, 2}`. -/
def jasPhaseChar (N : ℕ) (e : Fin 3) (j : Fin N) : ℂ :=
  ![1, unitRoot N ^ (j : ℕ), conj (unitRoot N ^ (j : ℕ))] e

/-- **Orthogonality on `ℤ/N`.**  For `N ≥ 3` the three phase characters are orthogonal. -/
theorem sum_jasPhaseChar_mul_conj {N : ℕ} (hN : 3 ≤ N) (e e' : Fin 3) :
    ∑ j : Fin N, jasPhaseChar N e j * conj (jasPhaseChar N e' j) = if e = e' then (N : ℂ) else 0 := by
  have h1 : ∑ j : Fin N, unitRoot N ^ (j : ℕ) = 0 := by
    have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 1) one_ne_zero (by omega)
    simpa using this
  have h2 : ∑ j : Fin N, (unitRoot N ^ (j : ℕ)) ^ 2 = 0 := by
    have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 2) two_ne_zero (by omega)
    simp_rw [← pow_mul, mul_comm (2 : ℕ)] at this ⊢
    exact this
  have h1c : ∑ j : Fin N, conj (unitRoot N ^ (j : ℕ)) = 0 := by
    rw [← map_sum, h1, map_zero]
  have h2c : ∑ j : Fin N, conj (unitRoot N ^ (j : ℕ)) ^ 2 = 0 := by
    simp_rw [← map_pow]; rw [← map_sum, h2, map_zero]
  have hw : ∀ j : Fin N, unitRoot N ^ (j : ℕ) * conj (unitRoot N ^ (j : ℕ)) = 1 :=
    fun j => unitRoot_pow_mul_conj N j
  have hw' : ∀ j : Fin N, conj (unitRoot N ^ (j : ℕ)) * unitRoot N ^ (j : ℕ) = 1 :=
    fun j => by rw [mul_comm]; exact hw j
  have hN' : ∑ _j : Fin N, (1 : ℂ) = N := by simp
  fin_cases e <;> fin_cases e' <;>
    simp only [jasPhaseChar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, map_one, mul_one, one_mul, Complex.conj_conj,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, if_true]
  all_goals first
    | exact h1
    | exact h1c
    | (simp_rw [← sq]; exact h2)
    | (simp_rw [← sq]; exact h2c)
    | (simp_rw [hw]; simp)
    | (simp_rw [hw']; simp)
    | simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The character `χ_e(k) = Π_i χ_{e_i}(k_i)` of the phase torus `(ℤ/N)^ι`. -/
def jasPhaseCharVec (N : ℕ) (e : ι → Fin 3) (k : ι → Fin N) : ℂ := ∏ i, jasPhaseChar N (e i) (k i)

/-- **Orthogonality on `(ℤ/N)^ι`.** -/
theorem sum_jasPhaseCharVec_mul_conj {N : ℕ} (hN : 3 ≤ N) (e e' : ι → Fin 3) :
    ∑ k : ι → Fin N, jasPhaseCharVec N e k * conj (jasPhaseCharVec N e' k) =
      if e = e' then (N : ℂ) ^ Fintype.card ι else 0 := by
  have hfac : ∀ k : ι → Fin N, jasPhaseCharVec N e k * conj (jasPhaseCharVec N e' k) =
      ∏ i, (jasPhaseChar N (e i) (k i) * conj (jasPhaseChar N (e' i) (k i))) := by
    intro k; unfold jasPhaseCharVec; rw [map_prod, ← Finset.prod_mul_distrib]
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun i j => jasPhaseChar N (e i) j * conj (jasPhaseChar N (e' i) j))]
  simp_rw [sum_jasPhaseChar_mul_conj hN]
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ e' i := by
      by_contra hc; push Not at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **Parseval's identity on the phase torus.** -/
theorem sum_normSq_sum_jasPhaseCharVec {N : ℕ} (hN : 3 ≤ N) (s : Finset (ι → Fin 3))
    (c : (ι → Fin 3) → ℂ) :
    ∑ k : ι → Fin N, ‖∑ e ∈ s, c e * jasPhaseCharVec N e k‖ ^ 2 =
      (N : ℝ) ^ Fintype.card ι * ∑ e ∈ s, ‖c e‖ ^ 2 := by
  have hre : ∀ z : ℂ, ‖z‖ ^ 2 = (z * conj z).re := fun z => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hre]
  rw [← Complex.re_sum]
  have h1 : ∀ k : ι → Fin N, (∑ e ∈ s, c e * jasPhaseCharVec N e k) *
      conj (∑ e ∈ s, c e * jasPhaseCharVec N e k) =
      ∑ e ∈ s, ∑ e' ∈ s, c e * conj (c e') *
        (jasPhaseCharVec N e k * conj (jasPhaseCharVec N e' k)) := by
    intro k
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
    rw [map_mul]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ e ∈ s, ∑ k : ι → Fin N, ∑ e' ∈ s, c e * conj (c e') *
      (jasPhaseCharVec N e k * conj (jasPhaseCharVec N e' k)) =
      c e * conj (c e) * (N : ℂ) ^ Fintype.card ι := by
    intro e he
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_jasPhaseCharVec_mul_conj hN, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq s e (fun e' => c e * conj (c e') * (N : ℂ) ^ Fintype.card ι),
      if_pos he]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  have h3 : ∑ e ∈ s, c e * conj (c e) = ((∑ e ∈ s, ‖c e‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [h3, show ((N : ℂ) ^ Fintype.card ι) = (((N : ℝ) ^ Fintype.card ι : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-! ## Expansion of the phase products -/

/-- `1 + a(ω^jX + ω^{−j}Y) = Σ_e χ_e(j) h_e` with `h = (1, aX, aY)`. -/
theorem phaseFactor_eq_sum_jasPhaseChar (N : ℕ) (a : ℝ) (X Y : ℂ) (j : Fin N) :
    phaseFactor N a X Y j =
      ∑ e : Fin 3, jasPhaseChar N e j * ![1, (a : ℂ) * X, (a : ℂ) * Y] e := by
  rw [Fin.sum_univ_three]
  simp only [jasPhaseChar, phaseFactor, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The coefficient `h_e = Π_i (1, aX_i, aY_i)_{e_i}` of the character `χ_e`. -/
def jasPhaseCoeff (a : ℝ) (X Y : ι → ℂ) (e : ι → Fin 3) : ℂ :=
  ∏ i, ![1, (a : ℂ) * X i, (a : ℂ) * Y i] (e i)

/-- `Π_i g_i(k_i) = Σ_e h_e χ_e(k)`. -/
theorem prod_phaseFactor_eq_sum (N : ℕ) (a : ℝ) (X Y : ι → ℂ) (k : ι → Fin N) :
    ∏ i, phaseFactor N a (X i) (Y i) (k i) =
      ∑ e : ι → Fin 3, jasPhaseCoeff a X Y e * jasPhaseCharVec N e k := by
  simp_rw [phaseFactor_eq_sum_jasPhaseChar]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold jasPhaseCoeff jasPhaseCharVec
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by ring

omit [DecidableEq ι] in
theorem jasPhaseCoeff_zero (a : ℝ) (X Y : ι → ℂ) : jasPhaseCoeff a X Y 0 = 1 := by
  simp [jasPhaseCoeff]

omit [DecidableEq ι] in
theorem jasPhaseCharVec_zero (N : ℕ) (k : ι → Fin N) : jasPhaseCharVec N 0 k = 1 := by
  simp [jasPhaseCharVec, jasPhaseChar]

/-- `Π_i g_i(k_i) − 1 = Σ_{e ≠ 0} h_e χ_e(k)`. -/
theorem prod_phaseFactor_sub_one_eq_sum (N : ℕ) (a : ℝ) (X Y : ι → ℂ) (k : ι → Fin N) :
    (∏ i, phaseFactor N a (X i) (Y i) (k i)) - 1 =
      ∑ e ∈ Finset.univ.erase 0, jasPhaseCoeff a X Y e * jasPhaseCharVec N e k := by
  rw [prod_phaseFactor_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0), jasPhaseCoeff_zero,
    jasPhaseCharVec_zero]
  ring

omit [DecidableEq ι] in
/-- `|h_e| ≤ 1` when `0 ≤ a ≤ 1` and `|X_i|, |Y_i| ≤ 1`. -/
theorem norm_jasPhaseCoeff_le_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) {X Y : ι → ℂ}
    (hX : ∀ i, ‖X i‖ ≤ 1) (hY : ∀ i, ‖Y i‖ ≤ 1) (e : ι → Fin 3) : ‖jasPhaseCoeff a X Y e‖ ≤ 1 := by
  unfold jasPhaseCoeff
  rw [norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ?_
  have h : ∀ f : Fin 3, ‖![1, (a : ℂ) * X i, (a : ℂ) * Y i] f‖ ≤ 1 := by
    intro f
    have hXa : ‖(a : ℂ) * X i‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      nlinarith [hX i, norm_nonneg (X i)]
    have hYa : ‖(a : ℂ) * Y i‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      nlinarith [hY i, norm_nonneg (Y i)]
    fin_cases f
    · simp
    · exact hXa
    · exact hYa
  exact h (e i)

/-! ## The signed lags -/

/-- The weight `(1, a/p, a/p)` of a sign at the prime `p`. -/
def jasSignWeight (a : ℝ) (f : Fin 3) (p : Nat.Primes) : ℝ := ![1, a / ((p : ℕ) : ℝ), a / ((p : ℕ) : ℝ)] f

/-- The lag `(0, −1, +1)` of a sign. -/
def jasSignLag (f : Fin 3) : ℝ := ![0, -1, 1] f

/-- Per prime: `(1, aA_p, aB_p)_f = κ_f(p) e^{ℓ_f log p (ρ − ½)}` at level one. -/
theorem jasHoloVec_eq_signWeight (a : ℝ) (q : XiZeroCopy) (p : Nat.Primes) (f : Fin 3) :
    ![1, (a : ℂ) * jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) p,
        (a : ℂ) * jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) p] f =
      (jasSignWeight a f p : ℂ) *
        cexp (((jasSignLag f * Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
  have hpinv : ((((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = cexp (-((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hp0]
  fin_cases f
  · show (1 : ℂ) = ((1 : ℝ) : ℂ) *
      cexp ((((0 : ℝ) * Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2))
    simp
  · show (a : ℂ) * jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) p =
      ((a / ((p : ℕ) : ℝ) : ℝ) : ℂ) *
        cexp ((((-1 : ℝ) * Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2))
    unfold jasHoloA
    rw [show ((a / ((p : ℕ) : ℝ) : ℝ) : ℂ) = (a : ℂ) * ((((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by
      push_cast; ring, hpinv, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · show (a : ℂ) * jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) p =
      ((a / ((p : ℕ) : ℝ) : ℝ) : ℂ) *
        cexp ((((1 : ℝ) * Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2))
    unfold jasHoloB
    rw [show ((a / ((p : ℕ) : ℝ) : ℝ) : ℂ) = (a : ℂ) * ((((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) by
      push_cast; ring, hpinv, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- The coefficient of `χ_e` at a zero: `h_e(ρ) = κ_e e^{L_e(ρ−½)}`. -/
theorem jasPhaseCoeff_jasHolo (a : ℝ) (P : Finset Nat.Primes) (q : XiZeroCopy) (e : ↥P → Fin 3) :
    jasPhaseCoeff a (fun p : ↥P => jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) (p : Nat.Primes))
        (fun p : ↥P => jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) (p : Nat.Primes)) e =
      ((∏ p : ↥P, jasSignWeight a (e p) p : ℝ) : ℂ) *
        cexp (((∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) : ℝ) : ℂ) *
          ((q.1 : ℂ) - 1 / 2)) := by
  unfold jasPhaseCoeff
  simp_rw [jasHoloVec_eq_signWeight]
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod, Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum]

/-! ## Parseval's identity for the JAS aggregate -/

theorem norm_jasHoloA_one_le_one (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) p‖ ≤ 1 := by
  refine (norm_jasHoloA_le_half 1 q p).trans (Real.exp_le_one_iff.mpr ?_)
  nlinarith [log_prime_pos p]

theorem norm_jasHoloB_one_le_one (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) p‖ ≤ 1 := by
  refine (norm_jasHoloB_le_half 1 q p).trans (Real.exp_le_one_iff.mpr ?_)
  nlinarith [log_prime_pos p]

/-- **Parseval's identity for random-phase JAS aggregates.**  Over the phase vectors
`k : P → ℤ/N` (`N ≥ 3`), the squared deviations of the level-one aggregate from its mean
`(1+r²)^{|P|}Φ(0)` sum to `(1+r²)^{2|P|} N^{|P|} Σ_{e ≠ 0} κ_e² Φ(L_e)²`, over the sign patterns
`e : P → {0, +, −}`. -/
theorem sum_normSq_jasPhaseAggregate_sub_mean {r : ℝ} (hr : 0 ≤ r) {N : ℕ} (hN : 3 ≤ N)
    (P : Finset Nat.Primes) :
    ∑ k : ↥P → Fin N, ‖jasPhaseAggregate 1 r N P k -
        (((1 + r ^ 2) ^ P.card * poleSharpConstant : ℝ) : ℂ)‖ ^ 2 =
      (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card *
        ∑ e ∈ Finset.univ.erase (0 : ↥P → Fin 3),
          (∏ p : ↥P, jasSignWeight (r / (1 + r ^ 2)) (e p) p) ^ 2 *
            weilLagFunctionReal
              (∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 := by
  classical
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  rw [← hadef]
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have ha1 : a ≤ 1 := by
    rw [hadef, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
  -- notation
  obtain ⟨A, hAdef⟩ : ∃ A : XiZeroCopy → ↥P → ℂ,
      A = fun (q : XiZeroCopy) (p : ↥P) => jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) (p : Nat.Primes) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : XiZeroCopy → ↥P → ℂ,
      B = fun (q : XiZeroCopy) (p : ↥P) => jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) (p : Nat.Primes) :=
    ⟨_, rfl⟩
  have hA1 : ∀ q p, ‖A q p‖ ≤ 1 := fun q p => by rw [hAdef]; exact norm_jasHoloA_one_le_one q p
  have hB1 : ∀ q p, ‖B q p‖ ≤ 1 := fun q p => by rw [hBdef]; exact norm_jasHoloB_one_le_one q p
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hws : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub
  have hwn : Summable fun q => ‖w q‖ := hws.norm
  obtain ⟨Pi, hPidef⟩ : ∃ Pi : XiZeroCopy → (↥P → Fin N) → ℂ,
      Pi = fun q k => ∏ p : ↥P, phaseFactor N a (A q p) (B q p) (k p) := ⟨_, rfl⟩
  have hPi : ∀ q k, ‖Pi q k - 1‖ ≤ 3 ^ P.card + 1 := by
    intro q k
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, hPidef, norm_prod]
    have : ∏ p : ↥P, ‖phaseFactor N a (A q p) (B q p) (k p)‖ ≤ ∏ _p : ↥P, (3 : ℝ) :=
      Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => by
        refine (norm_phaseFactor_le ha _ _ _).trans ?_
        nlinarith [hA1 q p, hB1 q p, norm_nonneg (A q p), norm_nonneg (B q p)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe] at this
    linarith
  -- the aggregate and its deviation
  have hagg : ∀ k, jasPhaseAggregate 1 r N P k =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) * ∑' q, w q * Pi q k := by
    intro k
    unfold jasPhaseAggregate
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_phase _ _ hr (k p),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPidef,
      hwdef, hAdef, hBdef, hadef]
    push_cast
    ring
  have hsumD : ∀ k, Summable fun q => w q * (Pi q k - 1) := fun k =>
    Summable.of_norm_bounded (hwn.mul_right _) fun q => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hPi q k) (norm_nonneg _)
  have hdev : ∀ k, jasPhaseAggregate 1 r N P k -
      (((1 + r ^ 2) ^ P.card * poleSharpConstant : ℝ) : ℂ) =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) * ∑' q, w q * (Pi q k - 1) := by
    intro k
    have e1 : ∀ q, w q * Pi q k = w q + w q * (Pi q k - 1) := fun q => by ring
    rw [hagg]
    simp_rw [e1]
    rw [hws.tsum_add (hsumD k), hwdef, tsum_inv_zero_mul_one_sub_zero]
    push_cast
    ring
  -- the character expansion of the deviation
  obtain ⟨G, hGdef⟩ : ∃ G : (↥P → Fin 3) → ℂ,
      G = fun e => ∑' q, w q * jasPhaseCoeff a (A q) (B q) e := ⟨_, rfl⟩
  have hexp : ∀ k, ∑' q, w q * (Pi q k - 1) =
      ∑ e ∈ Finset.univ.erase (0 : ↥P → Fin 3), G e * jasPhaseCharVec N e k := by
    intro k
    have h1 : ∀ q, w q * (Pi q k - 1) = ∑ e ∈ Finset.univ.erase (0 : ↥P → Fin 3),
        w q * jasPhaseCoeff a (A q) (B q) e * jasPhaseCharVec N e k := by
      intro q
      rw [hPidef]
      simp only
      rw [prod_phaseFactor_sub_one_eq_sum N a (A q) (B q) k, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    simp_rw [h1]
    rw [Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [hGdef, tsum_mul_right]
    · intro e _
      refine Summable.of_norm_bounded hwn fun q => ?_
      rw [norm_mul, norm_mul]
      have h2 := norm_jasPhaseCoeff_le_one ha ha1 (hA1 q) (hB1 q) e
      have h3 : ‖jasPhaseCharVec N e k‖ = 1 := by
        unfold jasPhaseCharVec
        rw [norm_prod]
        refine Finset.prod_eq_one fun i _ => ?_
        have h4 : ∀ (f : Fin 3) (j : Fin N), ‖jasPhaseChar N f j‖ = 1 := by
          intro f j
          fin_cases f
          · simp [jasPhaseChar]
          · exact norm_unitRoot_pow N j
          · show ‖conj (unitRoot N ^ (j : ℕ))‖ = 1
            rw [Complex.norm_conj]; exact norm_unitRoot_pow N j
        exact h4 _ _
      rw [h3, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) h2
  -- the coefficients
  have hG : ∀ e, G e = ((∏ p : ↥P, jasSignWeight a (e p) p : ℝ) : ℂ) *
      weilLagFunction (∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
    intro e
    rw [hGdef]
    simp only
    have h1 : ∀ q, w q * jasPhaseCoeff a (A q) (B q) e =
        ((∏ p : ↥P, jasSignWeight a (e p) p : ℝ) : ℂ) *
          (cexp (((∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) : ℝ) : ℂ) *
            ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
      intro q
      have := jasPhaseCoeff_jasHolo a P q e
      rw [hAdef, hBdef, hwdef]
      simp only
      rw [this]
      ring
    simp_rw [h1]
    rw [tsum_mul_left, weilLagFunction]
  -- Parseval
  have hpar := sum_normSq_sum_jasPhaseCharVec hN (Finset.univ.erase (0 : ↥P → Fin 3)) G (N := N)
  rw [Fintype.card_coe] at hpar
  simp_rw [hdev, norm_mul, mul_pow, hexp]
  rw [← Finset.mul_sum, hpar]
  have hnorm : ∀ e, ‖G e‖ ^ 2 = (∏ p : ↥P, jasSignWeight a (e p) p) ^ 2 *
      weilLagFunctionReal
        (∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 := by
    intro e
    rw [hG, weilLagFunction_eq_ofReal, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, mul_pow]
  simp_rw [hnorm]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← pow_mul]
  ring

/-! ## Bounds on the deviation sum -/

/-- **Single-prime patterns.**  The deviation sum is at least
`(1+r²)^{2|P|} N^{|P|} Σ_{p ∈ P} (a/p)² Φ(log p)²`. -/
theorem sum_sq_le_sum_normSq_jasPhaseAggregate_sub_mean {r : ℝ} (hr : 0 ≤ r) {N : ℕ}
    (hN : 3 ≤ N) (P : Finset Nat.Primes) :
    (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card *
        ∑ p ∈ P, (r / (1 + r ^ 2) / ((p : ℕ) : ℝ)) ^ 2 *
          weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2 ≤
      ∑ k : ↥P → Fin N, ‖jasPhaseAggregate 1 r N P k -
        (((1 + r ^ 2) ^ P.card * poleSharpConstant : ℝ) : ℂ)‖ ^ 2 := by
  classical
  rw [sum_normSq_jasPhaseAggregate_sub_mean hr hN P]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  rw [← hadef]
  obtain ⟨g, hgdef⟩ : ∃ g : ↥P → (↥P → Fin 3), g = fun p => Pi.single p 2 := ⟨_, rfl⟩
  have hg : Function.Injective g := by
    intro p₁ p₂ h
    by_contra hne
    have h1 := congrFun h p₁
    rw [hgdef] at h1
    simp only [Pi.single_eq_same] at h1
    rw [Pi.single_eq_of_ne hne] at h1
    exact absurd h1 (by decide)
  have hsub : Finset.univ.image g ⊆ Finset.univ.erase 0 := by
    intro e he
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    have h1 := congrFun h p
    rw [hgdef] at h1
    simp only [Pi.single_eq_same, Pi.zero_apply] at h1
    exact absurd h1 (by decide)
  have hval : ∀ p : ↥P, (∏ p' : ↥P, jasSignWeight a (g p p') p') ^ 2 *
      weilLagFunctionReal
        (∑ p' : ↥P, jasSignLag (g p p') * Real.log (((p' : Nat.Primes) : ℕ) : ℝ)) ^ 2 =
      (a / (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 *
        weilLagFunctionReal (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 := by
    intro p
    have h1 : ∏ p' : ↥P, jasSignWeight a (g p p') p' = a / (((p : Nat.Primes) : ℕ) : ℝ) := by
      rw [Finset.prod_eq_single p]
      · rw [hgdef]; simp [jasSignWeight]
      · intro b _ hb; rw [hgdef]; simp [Pi.single_eq_of_ne hb, jasSignWeight]
      · intro h; exact absurd (Finset.mem_univ p) h
    have h2 : ∑ p' : ↥P, jasSignLag (g p p') * Real.log (((p' : Nat.Primes) : ℕ) : ℝ) =
        Real.log (((p : Nat.Primes) : ℕ) : ℝ) := by
      rw [Finset.sum_eq_single p]
      · rw [hgdef]; simp [jasSignLag]
      · intro b _ hb; rw [hgdef]; simp [Pi.single_eq_of_ne hb, jasSignLag]
      · intro h; exact absurd (Finset.mem_univ p) h
    rw [h1, h2]
  calc ∑ p ∈ P, (a / ((p : ℕ) : ℝ)) ^ 2 * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2
      = ∑ p : ↥P, (a / (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 *
          weilLagFunctionReal (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 :=
        (Finset.sum_coe_sort P (fun p => (a / ((p : ℕ) : ℝ)) ^ 2 *
          weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2)).symm
    _ = ∑ e ∈ Finset.univ.image g, (∏ p' : ↥P, jasSignWeight a (e p') p') ^ 2 *
          weilLagFunctionReal
            (∑ p' : ↥P, jasSignLag (e p') * Real.log (((p' : Nat.Primes) : ℕ) : ℝ)) ^ 2 := by
        rw [Finset.sum_image (fun x _ y _ h => hg h)]
        exact Finset.sum_congr rfl fun p _ => (hval p).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => by positivity

/-- `|Φ(L)| ≤ e^{α|L|} M` for every `L` under a half-plane bound `α ≥ 0`. -/
theorem abs_weilLagFunctionReal_le_abs_of_xiZeroHalfPlaneBound {alpha : ℝ}
    (hXi : XiZeroHalfPlaneBound alpha) (L : ℝ) :
    |weilLagFunctionReal L| ≤ Real.exp (alpha * |L|) * jasLagAbsMass := by
  rcases le_total 0 L with hL | hL
  · rw [abs_of_nonneg hL]; exact abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi hL
  · have h := abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi (neg_nonneg.mpr hL)
    have he : weilLagFunctionReal (-L) = weilLagFunctionReal L := by
      unfold weilLagFunctionReal; rw [weilLagFunction_neg]
    rw [he] at h
    rwa [abs_of_nonpos hL]

/-- **Half-plane bound.**  Under `Re ρ ≤ ½ + α` (`α ≥ 0`),
`Σ_{e ≠ 0} κ_e² Φ(L_e)² ≤ M² (Π_P(1 + 2(a/p)² p^{2α}) − 1)`. -/
theorem sum_jasSign_le_of_xiZeroHalfPlaneBound {alpha : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (halpha : 0 ≤ alpha) {a : ℝ} (P : Finset Nat.Primes) :
    ∑ e ∈ Finset.univ.erase (0 : ↥P → Fin 3), (∏ p : ↥P, jasSignWeight a (e p) p) ^ 2 *
        weilLagFunctionReal
          (∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 ≤
      jasLagAbsMass ^ 2 * ((∏ p ∈ P, (1 + 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
        Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)))) - 1) := by
  classical
  have hM : 0 ≤ jasLagAbsMass := tsum_nonneg fun q => norm_nonneg _
  obtain ⟨F, hFdef⟩ : ∃ F : ↥P → Fin 3 → ℝ, F = fun (p : ↥P) (f : Fin 3) => jasSignWeight a f p ^ 2 *
      Real.exp (2 * alpha * (|jasSignLag f| * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hF0 : ∀ p, F p 0 = 1 := fun p => by rw [hFdef]; simp [jasSignWeight, jasSignLag]
  have hFsum : ∀ p : ↥P, ∑ f : Fin 3, F p f = 1 + 2 * (a / (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 *
      Real.exp (2 * alpha * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
    intro p
    rw [Fin.sum_univ_three, hFdef]
    simp [jasSignWeight, jasSignLag]
    ring
  have hterm : ∀ e : ↥P → Fin 3, (∏ p : ↥P, jasSignWeight a (e p) p) ^ 2 *
      weilLagFunctionReal
        (∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 ≤
      jasLagAbsMass ^ 2 * ∏ p : ↥P, F p (e p) := by
    intro e
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ,
        L = ∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) := ⟨_, rfl⟩
    rw [← hLdef]
    have hΦ := abs_weilLagFunctionReal_le_abs_of_xiZeroHalfPlaneBound hXi L
    have hL : |L| ≤ ∑ p : ↥P, |jasSignLag (e p)| * Real.log (((p : Nat.Primes) : ℕ) : ℝ) := by
      rw [hLdef]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast p.1.2.one_lt.le))]
    have hexp : Real.exp (alpha * |L|) ^ 2 ≤
        ∏ p : ↥P, Real.exp (2 * alpha * (|jasSignLag (e p)| * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) := by
      rw [← Real.exp_sum, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      rw [← Finset.mul_sum]
      push_cast
      nlinarith
    have hsq : weilLagFunctionReal L ^ 2 ≤ (Real.exp (alpha * |L|) * jasLagAbsMass) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hΦ 2
    calc (∏ p : ↥P, jasSignWeight a (e p) p) ^ 2 * weilLagFunctionReal L ^ 2
        ≤ (∏ p : ↥P, jasSignWeight a (e p) p) ^ 2 * (Real.exp (alpha * |L|) * jasLagAbsMass) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = jasLagAbsMass ^ 2 * ((∏ p : ↥P, jasSignWeight a (e p) p ^ 2) *
            Real.exp (alpha * |L|) ^ 2) := by rw [Finset.prod_pow]; ring
      _ ≤ jasLagAbsMass ^ 2 * ((∏ p : ↥P, jasSignWeight a (e p) p ^ 2) *
            ∏ p : ↥P, Real.exp (2 * alpha *
              (|jasSignLag (e p)| * Real.log (((p : Nat.Primes) : ℕ) : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp ?_) (by positivity)
          exact Finset.prod_nonneg fun p _ => sq_nonneg _
      _ = jasLagAbsMass ^ 2 * ∏ p : ↥P, F p (e p) := by
          rw [← Finset.prod_mul_distrib, hFdef]
  refine (Finset.sum_le_sum fun e _ => hterm e).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  have htot : ∑ e : ↥P → Fin 3, ∏ p : ↥P, F p (e p) =
      ∏ p ∈ P, (1 + 2 * (a / ((p : ℕ) : ℝ)) ^ 2 * Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ))) := by
    rw [← Fintype.prod_sum F]
    simp_rw [hFsum]
    exact Finset.prod_coe_sort P (fun p => 1 + 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
      Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)))
  rw [← htot, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ↥P → Fin 3))]
  simp only [Pi.zero_apply, hF0, Finset.prod_const_one]
  ring

/-! ## The variance law on Huxley windows -/

/-- The deviation sum `Σ_k |agg(k) − (1+r²)^{|P|}Φ(0)|²` over the phase vectors `k : P → ℤ/N`. -/
def jasPhaseDevSq (r : ℝ) (N : ℕ) (P : Finset Nat.Primes) : ℝ :=
  ∑ k : ↥P → Fin N, ‖jasPhaseAggregate 1 r N P k -
    (((1 + r ^ 2) ^ P.card * poleSharpConstant : ℝ) : ℂ)‖ ^ 2

/-- The variance budget `C (1+r²)^{2|P|} N^{|P|} x^{2c−2} |P|`. -/
def jasPhaseVarianceBudget (C c r : ℝ) (N : ℕ) (P : Finset Nat.Primes) (x : ℝ) : ℝ :=
  C * (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card * Real.exp ((2 * c - 2) * Real.log x) * P.card

theorem mem_jasIntervalPrimes_bounds {x L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) {p : Nat.Primes}
    (hp : p ∈ jasIntervalPrimes x L) : x < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ x + L := by
  have hp' : (p : ℕ) ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊).filter Nat.Prime := Finset.mem_subtype.mp hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp'
  exact ⟨(Nat.floor_lt hx).mp hp'.1.1,
    le_trans (by exact_mod_cast hp'.1.2) (Nat.floor_le (by positivity))⟩

theorem card_jasIntervalPrimes_le {x L : ℝ} (hx : 0 ≤ x) (hL : 0 ≤ L) :
    ((jasIntervalPrimes x L).card : ℝ) ≤ L + 1 := by
  have h1 : ((jasIntervalPrimes x L).card : ℝ) ≤ (Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊).card := by
    have : (jasIntervalPrimes x L).card ≤ (Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊).card := by
      refine Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ)) ?_ ?_
      · intro p hp
        have hp' : (p : ℕ) ∈ (Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊).filter Nat.Prime :=
          Finset.mem_subtype.mp hp
        exact (Finset.mem_filter.mp hp').1
      · intro p₁ _ p₂ _ h; exact Subtype.val_injective h
    exact_mod_cast this
  refine h1.trans ?_
  rw [Nat.card_Ioc]
  have hmono : ⌊x⌋₊ ≤ ⌊x + L⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub hmono]
  have h2 : (⌊x + L⌋₊ : ℝ) ≤ x + L := Nat.floor_le (by positivity)
  have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  linarith

/-- **A variance budget bounds the signed window mean.**  On a window `P ⊂ (x, 2x]`, a deviation
sum of at most `C (1+r²)^{2|P|} N^{|P|} x^{2c−2} |P|` gives
`|Σ_P Φ(log p)| ≤ (2√C/a) x^c |P|`. -/
theorem abs_sum_weilLag_le_of_phaseDevSq {r C c x : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hx : 1 ≤ x)
    {N : ℕ} (hN : 3 ≤ N) (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, x < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * x)
    (h : jasPhaseDevSq r N P ≤ jasPhaseVarianceBudget C c r N P x) :
    |∑ p ∈ P, weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))| ≤
      2 * Real.sqrt C / (r / (1 + r ^ 2)) * Real.exp (c * Real.log x) * P.card := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; positivity
  rw [← hadef]
  have hx0 : 0 < x := by linarith
  have hlow := sum_sq_le_sum_normSq_jasPhaseAggregate_sub_mean hr.le hN P
  rw [← hadef] at hlow
  have hcomb := hlow.trans (le_trans (le_of_eq rfl) h)
  unfold jasPhaseVarianceBudget at hcomb
  have hpos : 0 < (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hS : ∑ p ∈ P, (a / ((p : ℕ) : ℝ)) ^ 2 * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2 ≤
      C * Real.exp ((2 * c - 2) * Real.log x) * P.card := by
    have e : C * (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card *
        Real.exp ((2 * c - 2) * Real.log x) * P.card =
        ((1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card) *
          (C * Real.exp ((2 * c - 2) * Real.log x) * P.card) := by ring
    rw [e] at hcomb
    exact le_of_mul_le_mul_left hcomb hpos
  have hterm : ∀ p ∈ P, a ^ 2 / (4 * x ^ 2) * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2 ≤
      (a / ((p : ℕ) : ℝ)) ^ 2 * weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2 := by
    intro p hp
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    obtain ⟨h1, h2⟩ := hP p hp
    have hp0 : 0 < ((p : ℕ) : ℝ) := by linarith
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((p : ℕ) : ℝ) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    nlinarith [sq_nonneg a]
  have hS2 : ∑ p ∈ P, weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2 ≤
      4 * C / a ^ 2 * Real.exp (2 * c * Real.log x) * P.card := by
    have h1 := (Finset.sum_le_sum hterm).trans hS
    rw [← Finset.mul_sum] at h1
    have hx2 : x ^ 2 = Real.exp (2 * Real.log x) := by
      rw [← Real.exp_log hx0, ← Real.exp_nat_mul, Real.log_exp]; push_cast; ring
    have hE : Real.exp ((2 * c - 2) * Real.log x) * x ^ 2 = Real.exp (2 * c * Real.log x) := by
      rw [hx2, ← Real.exp_add]; ring_nf
    have hq : 0 < a ^ 2 / (4 * x ^ 2) := by positivity
    rw [← le_div_iff₀' hq] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← hE]
    field_simp
  have hCS := sq_sum_le_card_mul_sum_sq (s := P)
    (f := fun p => weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)))
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  have hsqrt : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC
  have hexp2 : Real.exp (c * Real.log x) ^ 2 = Real.exp (2 * c * Real.log x) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  calc (∑ p ∈ P, weilLagFunctionReal (Real.log ((p : ℕ) : ℝ))) ^ 2
      ≤ P.card * ∑ p ∈ P, weilLagFunctionReal (Real.log ((p : ℕ) : ℝ)) ^ 2 := hCS
    _ ≤ P.card * (4 * C / a ^ 2 * Real.exp (2 * c * Real.log x) * P.card) :=
        mul_le_mul_of_nonneg_left hS2 (Nat.cast_nonneg _)
    _ = (2 * Real.sqrt C / a * Real.exp (c * Real.log x) * P.card) ^ 2 := by
        rw [mul_pow, mul_pow, div_pow, mul_pow, hsqrt, hexp2]
        field_simp
        ring

/-- **The variance receiver.**  For `7/12 < θ < 1`, `r > 0` and `N ≥ 3`, suppose the deviation sum
on the Huxley windows `P_x = (x, x + x^θ]` is eventually at most
`C (1+r²)^{2|P_x|} N^{|P_x|} x^{2c−2} |P_x|`.  Then every zero satisfies
`|Re ρ − ½| ≤ max(0, c)`. -/
theorem abs_re_sub_half_le_of_phaseVariance {c θ C r : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1)
    (hC : 0 ≤ C) (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N)
    (h : ∀ᶠ x : ℝ in atTop, jasPhaseDevSq r N (jasIntervalPrimes x (Real.exp (θ * Real.log x))) ≤
      jasPhaseVarianceBudget C c r N (jasIntervalPrimes x (Real.exp (θ * Real.log x))) x)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c := by
  refine abs_re_sub_half_le_of_primeWindowMean hθ hθ1
    (C := 2 * Real.sqrt C / (r / (1 + r ^ 2))) (by positivity) ?_ q
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hwin : Real.exp (θ * Real.log x) ≤ x := by
    calc Real.exp (θ * Real.log x) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hx1])
      _ = x := Real.exp_log hx0
  refine abs_sum_weilLag_le_of_phaseDevSq hr hC hx1 hN _ (fun p hp => ?_) hx
  have := mem_jasIntervalPrimes_bounds hx0.le (Real.exp_pos _).le hp
  exact ⟨this.1, by linarith [this.2]⟩

/-- `Π_P(1 + t_p) − 1 ≤ (Σ t_p) e^{Σ t_p}` for `t ≥ 0`. -/
theorem prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (∏ i ∈ s, (1 + t i)) - 1 ≤ (∑ i ∈ s, t i) * Real.exp (∑ i ∈ s, t i) := by
  have h1 := GaloisForLFunctions.HTGeometry.prod_one_add_le_exp_sum s t ht
  have h2 := Real.add_one_le_exp (-(∑ i ∈ s, t i))
  have h3 : Real.exp (-(∑ i ∈ s, t i)) * Real.exp (∑ i ∈ s, t i) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (∑ i ∈ s, t i)
  nlinarith

/-- **Half-planes bound the variance.**  Under `Re ρ ≤ ½ + α` with `0 ≤ α ≤ ½`, the deviation sum
on any window `P ⊂ (x, 2x]` with `|P| ≤ 2x` is at most
`(e M²/2) (1+r²)^{2|P|} N^{|P|} x^{2α−2} |P|`. -/
theorem jasPhaseDevSq_le_of_xiZeroHalfPlaneBound {alpha r x : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (halpha : 0 ≤ alpha) (halpha2 : alpha ≤ 1 / 2) (hr : 0 ≤ r) (hx : 1 ≤ x) {N : ℕ} (hN : 3 ≤ N)
    (P : Finset Nat.Primes) (hP : ∀ p ∈ P, x < ((p : ℕ) : ℝ))
    (hcard : (P.card : ℝ) ≤ 2 * x) :
    jasPhaseDevSq r N P ≤
      jasPhaseVarianceBudget (Real.exp 1 * jasLagAbsMass ^ 2 / 2) alpha r N P x := by
  unfold jasPhaseDevSq jasPhaseVarianceBudget
  rw [sum_normSq_jasPhaseAggregate_sub_mean hr hN P]
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  rw [← hadef]
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [hadef, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
  have hx0 : 0 < x := by linarith
  have hM : 0 ≤ jasLagAbsMass := tsum_nonneg fun q => norm_nonneg _
  have hB := sum_jasSign_le_of_xiZeroHalfPlaneBound hXi halpha (a := a) P
  -- each factor `t_p = 2(a/p)² p^{2α} ≤ x^{2α−2}/2`
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp ((2 * alpha - 2) * Real.log x) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have ht : ∀ p ∈ P, 2 * (a / ((p : ℕ) : ℝ)) ^ 2 * Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)) ≤
      E / 2 := by
    intro p hp
    have hp1 : x < ((p : ℕ) : ℝ) := hP p hp
    have hp0 : 0 < ((p : ℕ) : ℝ) := by linarith
    have hlog : Real.log x ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log hx0 hp1.le
    have e1 : (a / ((p : ℕ) : ℝ)) ^ 2 * Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)) =
        a ^ 2 * Real.exp ((2 * alpha - 2) * Real.log ((p : ℕ) : ℝ)) := by
      rw [div_pow, show (2 * alpha - 2) * Real.log ((p : ℕ) : ℝ) =
        2 * alpha * Real.log ((p : ℕ) : ℝ) + -(2 * Real.log ((p : ℕ) : ℝ)) by ring, Real.exp_add,
        Real.exp_neg, show 2 * Real.log ((p : ℕ) : ℝ) = Real.log (((p : ℕ) : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
      field_simp
    have e2 : Real.exp ((2 * alpha - 2) * Real.log ((p : ℕ) : ℝ)) ≤ E := by
      rw [hEdef]; exact Real.exp_le_exp.mpr (by nlinarith)
    rw [mul_assoc, e1]
    have h4 : 2 * a ^ 2 ≤ 1 / 2 := by nlinarith
    have h5 := Real.exp_pos ((2 * alpha - 2) * Real.log ((p : ℕ) : ℝ))
    nlinarith
  have hsum : ∑ p ∈ P, 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
      Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)) ≤ P.card * (E / 2) := by
    have := Finset.sum_le_sum ht
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hsum1 : P.card * (E / 2) ≤ 1 := by
    have hE1 : E * x ≤ 1 := by
      rw [hEdef]
      have : Real.exp ((2 * alpha - 2) * Real.log x) * x =
          Real.exp ((2 * alpha - 1) * Real.log x) := by
        rw [show (2 * alpha - 1) * Real.log x = (2 * alpha - 2) * Real.log x + Real.log x by ring,
          Real.exp_add, Real.exp_log hx0]
      rw [this]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.log_nonneg hx])
    nlinarith
  have hprod := prod_one_add_sub_one_le P (fun p => 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
    Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ))) (fun p _ => by positivity)
  have hS0 : 0 ≤ ∑ p ∈ P, 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
      Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)) := Finset.sum_nonneg fun p _ => by positivity
  have hexpS : Real.exp (∑ p ∈ P, 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
      Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ))) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (hsum.trans hsum1)
  have hprod' : (∏ p ∈ P, (1 + 2 * (a / ((p : ℕ) : ℝ)) ^ 2 *
      Real.exp (2 * alpha * Real.log ((p : ℕ) : ℝ)))) - 1 ≤ P.card * (E / 2) * Real.exp 1 :=
    hprod.trans (mul_le_mul hsum hexpS (Real.exp_pos _).le (by positivity))
  have hpos : 0 ≤ (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card := by positivity
  calc (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card *
        ∑ e ∈ Finset.univ.erase (0 : ↥P → Fin 3), (∏ p : ↥P, jasSignWeight a (e p) p) ^ 2 *
          weilLagFunctionReal
            (∑ p : ↥P, jasSignLag (e p) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2
      ≤ (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card *
          (jasLagAbsMass ^ 2 * (P.card * (E / 2) * Real.exp 1)) :=
        mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left hprod' (sq_nonneg _))) hpos
    _ = Real.exp 1 * jasLagAbsMass ^ 2 / 2 * (1 + r ^ 2) ^ (2 * P.card) * (N : ℝ) ^ P.card *
          Real.exp ((2 * alpha - 2) * Real.log x) * P.card := by rw [hEdef]; ring

/-- On a Huxley window `(x, x + x^θ]` (`θ ≤ 1`, `x ≥ 1`) the primes lie in `(x, 2x]` and number at
most `2x`. -/
theorem jasHuxleyWindow_bounds {θ x : ℝ} (hθ1 : θ ≤ 1) (hx : 1 ≤ x) :
    (∀ p ∈ jasIntervalPrimes x (Real.exp (θ * Real.log x)),
      x < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * x) ∧
      ((jasIntervalPrimes x (Real.exp (θ * Real.log x))).card : ℝ) ≤ 2 * x := by
  have hx0 : 0 < x := by linarith
  have hwin : Real.exp (θ * Real.log x) ≤ x := by
    calc Real.exp (θ * Real.log x) ≤ Real.exp (Real.log x) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hx])
      _ = x := Real.exp_log hx0
  refine ⟨fun p hp => ?_, ?_⟩
  · have := mem_jasIntervalPrimes_bounds hx0.le (Real.exp_pos _).le hp
    exact ⟨this.1, by linarith [this.2]⟩
  · have := card_jasIntervalPrimes_le hx0.le (Real.exp_pos (θ * Real.log x)).le
    linarith

/-- **Quasi-RH ⟺ a power-saving phase variance.**  For `7/12 < θ < 1`, `r > 0` and `N ≥ 3`, a
zero-free half-plane `Re s > ½ + α`, `α < ½`, exists iff for some `c < ½` the deviation sum on
the Huxley windows is eventually at most `C (1+r²)^{2|P_x|} N^{|P_x|} x^{2c−2} |P_x|`. -/
theorem exists_halfPlane_lt_half_iff_exists_phaseVariance {θ r : ℝ} (hθ : 7 / 12 < θ)
    (hθ1 : θ < 1) (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    (∃ alpha : ℝ, alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha) ↔
      ∃ c : ℝ, c < 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
        jasPhaseDevSq r N (jasIntervalPrimes x (Real.exp (θ * Real.log x))) ≤
          jasPhaseVarianceBudget C c r N (jasIntervalPrimes x (Real.exp (θ * Real.log x))) x := by
  constructor
  · rintro ⟨alpha, halpha, hXi⟩
    obtain ⟨α', hα'def⟩ : ∃ a : ℝ, a = max alpha 0 := ⟨_, rfl⟩
    have hXi' : XiZeroHalfPlaneBound α' := fun ρ hρ => by
      have := hXi ρ hρ; rw [hα'def]; linarith [le_max_left alpha 0]
    have hα'0 : 0 ≤ α' := by rw [hα'def]; exact le_max_right _ _
    have hα'2 : α' < 1 / 2 := by rw [hα'def]; exact max_lt halpha (by norm_num)
    have hM : 0 ≤ jasLagAbsMass := tsum_nonneg fun q => norm_nonneg _
    refine ⟨α', hα'2, Real.exp 1 * jasLagAbsMass ^ 2 / 2, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    obtain ⟨hmem, hcard⟩ := jasHuxleyWindow_bounds hθ1.le hx
    exact jasPhaseDevSq_le_of_xiZeroHalfPlaneBound hXi' hα'0 hα'2.le hr.le hx hN _
      (fun p hp => (hmem p hp).1) hcard
  · rintro ⟨c, hc, C, hC, h⟩
    refine ⟨max 0 c, max_lt (by norm_num) hc, fun ρ hρ => ?_⟩
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := abs_re_sub_half_le_of_phaseVariance hθ hθ1 hC hr hN h q
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ subpower phase variance.**  For `7/12 < θ < 1`, `r > 0` and `N ≥ 3`, RH holds iff for
every `ε > 0` the deviation sum on the Huxley windows is eventually at most
`C_ε (1+r²)^{2|P_x|} N^{|P_x|} x^{2ε−2} |P_x|`. -/
theorem riemannHypothesis_iff_forall_phaseVariance {θ r : ℝ} (hθ : 7 / 12 < θ) (hθ1 : θ < 1)
    (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      jasPhaseDevSq r N (jasIntervalPrimes x (Real.exp (θ * Real.log x))) ≤
        jasPhaseVarianceBudget C ε r N (jasIntervalPrimes x (Real.exp (θ * Real.log x))) x := by
  constructor
  · intro hRH ε hε
    have hXi : XiZeroHalfPlaneBound 0 := riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH
    have hM : 0 ≤ jasLagAbsMass := tsum_nonneg fun q => norm_nonneg _
    refine ⟨Real.exp 1 * jasLagAbsMass ^ 2 / 2, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    obtain ⟨hmem, hcard⟩ := jasHuxleyWindow_bounds hθ1.le hx
    refine (jasPhaseDevSq_le_of_xiZeroHalfPlaneBound hXi le_rfl (by norm_num) hr.le hx hN _
      (fun p hp => (hmem p hp).1) hcard).trans ?_
    unfold jasPhaseVarianceBudget
    have hx0 : 0 < x := by linarith
    have : Real.exp ((2 * 0 - 2) * Real.log x) ≤ Real.exp ((2 * ε - 2) * Real.log x) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.log_nonneg hx])
    have hpos : 0 ≤ Real.exp 1 * jasLagAbsMass ^ 2 / 2 * (1 + r ^ 2) ^
        (2 * (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card) * (N : ℝ) ^
          (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card := by positivity
    have hcard0 : (0 : ℝ) ≤ (jasIntervalPrimes x (Real.exp (θ * Real.log x))).card :=
      Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hpos) hcard0
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have hle : ∀ ε : ℝ, 0 < ε → (q.1 : ℂ).re - 1 / 2 ≤ ε := by
      intro ε hε
      obtain ⟨C, hC, hε'⟩ := h ε hε
      have := abs_re_sub_half_le_of_phaseVariance hθ hθ1 hC hr hN hε' q
      rw [max_eq_right hε.le] at this
      linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]
    by_contra hcon
    push Not at hcon
    have := hle (((q.1 : ℂ).re - 1 / 2) / 2) (by linarith)
    linarith

end

end RHTower
