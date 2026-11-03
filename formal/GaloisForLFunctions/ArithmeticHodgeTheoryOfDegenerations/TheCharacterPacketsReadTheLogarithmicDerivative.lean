import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HyperbolaSumsOfAVonMangoldtTail
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkSecondOrderOfThePoleIsAStieltjesConstant
import GaloisForLFunctions.ArtinMertens.TheTwistedVonMangoldtSeriesConvergesAtOne

/-!
# The character packets read the logarithmic derivative of `L`

Character packets `X_χ(n) = χ(n)/√n`, `n ≤ N`, for nontrivial Dirichlet characters `χ` mod `q`, against
the prime matrix `P(n, j) = Λ(j/n)/√(j/n)` (`n ∣ j`, symmetric).

* **Hyperbola form** (`charPacketPairing_eq`): `⟨P X_χ, X_ψ⟩ = Σ_{n ≤ N} χ̄(n)ψ(n)/n · (S_ψ(⌊N/n⌋)
  + S̄_χ(⌊N/n⌋))`, `S_χ(k) = Σ_{m ≤ k} χ(m)Λ(m)/m`.
* **The derivative of `L'/L`** (`tendsto_integral_twistLogTail`): with `S_χ(∞) = −L'(1,χ)/L(1,χ)`
  (ArtinMertens) and the tail `δ_χ = S_χ − S_χ(∞)`, `∫_0^T δ_χ(⌊e^u⌋) du → I_χ = −(L'/L)'(1, χ)`:
  Newman's theorem, the transform being `(G(z) − G(0))/z` with `G(z) = −L'/L(1 + z, χ)`.
* **Second order** (`tendsto_charPacketPairing_sub`): for nontrivial `χ, ψ` mod `q`,
  `⟨P X_χ, X_ψ⟩ − (S_ψ(∞) + S̄_χ(∞)) ⟨X_χ, X_ψ⟩ → [χ = ψ] (φ(q)/q)(I_χ + Ī_χ)`.

So `L'(1, χ)/L(1, χ)` is the first-order energy of a character packet, `ρ_χ = −2 Re L'(1,χ)/L(1,χ)`
(bounded, not `log N` as for the Ramanujan packets), and the second order is
`−2(φ(q)/q) Re (L'/L)'(1, χ)`; distinct characters decouple to second order.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticFunction (vonMangoldt)
open ArithmeticEffectivityTheory

variable {q : ℕ} [NeZero q]

/-! ### Definitions -/

/-- The prime pairing of two character packets: `Σ_{n, j ≤ N} χ̄(n) ψ(j) P(n, j)/√(nj)`. -/
def charPacketPairing (χ ψ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, conj (χ n) * ψ j *
    ((weilPrimeKernel n j / (Real.sqrt n * Real.sqrt j) : ℝ) : ℂ)

/-- The Gram entry `⟨X_χ, X_ψ⟩ = Σ_{n ≤ N} χ̄(n) ψ(n)/n`. -/
def charPacketGram (χ ψ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, conj (χ n) * ψ n / n

/-- `S_χ(k) = Σ_{m ≤ k} χ(m)Λ(m)/m`. -/
def twistLogSum (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  ∑ m ∈ Icc 1 k, χ m * (vonMangoldt m : ℂ) / m

/-- `S_χ(∞) = −L'(1, χ)/L(1, χ)`. -/
def twistLogDeriv (χ : DirichletCharacter ℂ q) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

/-- The tail `δ_χ(k) = S_χ(k) − S_χ(∞)`. -/
def twistLogTail (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ := twistLogSum χ k - twistLogDeriv χ

/-- `I_χ = d/ds (−L'(s, χ)/L(s, χ))` at `s = 1`. -/
def twistLogDerivDeriv (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (fun s => -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) 1

/-! ### The prime kernel in packet gauge -/

/-- `P(n, j)/√(nj) = [n ∣ j] Λ(j/n)/j + [j ∣ n] Λ(n/j)/n`. -/
theorem weilPrimeKernel_div_sqrt_mul {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    weilPrimeKernel n j / (Real.sqrt n * Real.sqrt j) =
      (if n ∣ j then vonMangoldt (j / n) / j else 0) +
        (if j ∣ n then vonMangoldt (n / j) / n else 0) := by
  have hup : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → primeKernelUp a b / (Real.sqrt a * Real.sqrt b) =
      if a ∣ b then vonMangoldt (b / a) / b else 0 := fun a b ha hb => by
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
    unfold primeKernelUp
    by_cases h : a ∣ b ∧ a ≠ b
    · rw [if_pos h, if_pos h.1]
      have hq : ((b / a : ℕ) : ℝ) = (b : ℝ) / a := Nat.cast_div h.1 ha0.ne'
      rw [hq, Real.sqrt_div' _ ha0.le]
      obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt b = r := ⟨_, Real.sqrt_pos.mpr hb0, rfl⟩
      obtain ⟨s, hs0, hs⟩ : ∃ s, 0 < s ∧ Real.sqrt a = s := ⟨_, Real.sqrt_pos.mpr ha0, rfl⟩
      have hbr : (b : ℝ) = r ^ 2 := by rw [← hr, Real.sq_sqrt hb0.le]
      have hr0' := hr0.ne'
      have hs0' := hs0.ne'
      rw [hr, hs, hbr]
      field_simp
    · rw [if_neg h, zero_div]
      split_ifs with hab
      · have : a = b := by by_contra hne; exact h ⟨hab, hne⟩
        rw [this, Nat.div_self (by omega), ArithmeticFunction.vonMangoldt_apply_one, zero_div]
      · rfl
  rw [weilPrimeKernel_eq_up_add, add_div, hup n j hn hj, mul_comm (Real.sqrt n), hup j n hj hn]

/-! ### The hyperbola form of the pairing -/

/-- Multiples of `L` in `[1, N]`: `Σ_{n ≤ N, L ∣ n} F(n/L) = Σ_{i ≤ N/L} F(i)`. -/
theorem sum_Icc_ite_dvd_eq {M : Type*} [AddCommMonoid M] (N : ℕ) {L : ℕ} (hL : 0 < L)
    (F : ℕ → M) :
    ∑ n ∈ Icc 1 N, (if L ∣ n then F (n / L) else 0) = ∑ i ∈ Icc 1 (N / L), F i := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun i => L * i) (fun n => n / L) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hL.ne' (by have := hi.1; omega)), ?_⟩,
      dvd_mul_right L i⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hL).mp hi.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left k hL]
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hn1, ?_⟩
    rw [Nat.le_div_iff_mul_le hL, mul_comm]
    exact hnN
  · intro i _
    exact Nat.mul_div_cancel_left i hL
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro i _
    rw [Nat.mul_div_cancel_left i hL]

omit [NeZero q] in
theorem conj_twistLogSum (χ : DirichletCharacter ℂ q) (k : ℕ) :
    conj (twistLogSum χ k) = ∑ m ∈ Icc 1 k, conj (χ m) * (vonMangoldt m : ℂ) / m := by
  unfold twistLogSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_div₀, map_mul, Complex.conj_ofReal, map_natCast (starRingEnd ℂ) m]

omit [NeZero q] in
/-- **The hyperbola form**: `⟨P X_χ, X_ψ⟩ = Σ_{n ≤ N} χ̄(n)ψ(n)/n (S_ψ(⌊N/n⌋) + S̄_χ(⌊N/n⌋))`. -/
theorem charPacketPairing_eq (χ ψ : DirichletCharacter ℂ q) (N : ℕ) :
    charPacketPairing χ ψ N = ∑ n ∈ Icc 1 N, conj (χ n) * ψ n / n *
      (twistLogSum ψ (N / n) + conj (twistLogSum χ (N / n))) := by
  have hw : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, conj (χ n) * ψ j *
      ((weilPrimeKernel n j / (Real.sqrt n * Real.sqrt j) : ℝ) : ℂ) =
      (if n ∣ j then conj (χ n) * ψ j * ((vonMangoldt (j / n) / j : ℝ) : ℂ) else 0) +
        (if j ∣ n then conj (χ n) * ψ j * ((vonMangoldt (n / j) / n : ℝ) : ℂ) else 0) :=
    fun n hn j hj => by
      rw [weilPrimeKernel_div_sqrt_mul (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hj).1]
      split_ifs <;> simp only [Complex.ofReal_add, Complex.ofReal_zero, mul_add, mul_zero,
        add_zero, zero_add]
  unfold charPacketPairing
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl (hw n hn)]
  simp only [Finset.sum_add_distrib]
  -- the upper half
  have hA : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      (if n ∣ j then conj (χ n) * ψ j * ((vonMangoldt (j / n) / j : ℝ) : ℂ) else 0) =
      ∑ n ∈ Icc 1 N, conj (χ n) * ψ n / n * twistLogSum ψ (N / n) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hrw : ∀ j ∈ Icc 1 N,
        (if n ∣ j then conj (χ n) * ψ j * ((vonMangoldt (j / n) / j : ℝ) : ℂ) else 0) =
        if n ∣ j then (fun m => conj (χ n) * ψ ((n * m : ℕ) : ZMod q) *
          ((vonMangoldt m / ((n * m : ℕ) : ℝ) : ℝ) : ℂ)) (j / n) else 0 := fun j _ => by
      split_ifs with h
      · simp only [Nat.mul_div_cancel' h]
      · rfl
    rw [Finset.sum_congr rfl hrw, sum_Icc_ite_dvd_eq N hn1 (fun m => conj (χ n) *
      ψ ((n * m : ℕ) : ZMod q) * ((vonMangoldt m / ((n * m : ℕ) : ℝ) : ℝ) : ℂ)), twistLogSum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.cast_mul, map_mul]
    push_cast
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn1.ne'
    by_cases hm : (m : ℂ) = 0
    · rw [hm]; simp
    · field_simp
  -- the lower half
  have hB : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      (if j ∣ n then conj (χ n) * ψ j * ((vonMangoldt (n / j) / n : ℝ) : ℂ) else 0) =
      ∑ j ∈ Icc 1 N, conj (χ j) * ψ j / j * conj (twistLogSum χ (N / j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 0 < j := (Finset.mem_Icc.mp hj).1
    have hrw : ∀ n ∈ Icc 1 N,
        (if j ∣ n then conj (χ n) * ψ j * ((vonMangoldt (n / j) / n : ℝ) : ℂ) else 0) =
        if j ∣ n then (fun m => conj (χ ((j * m : ℕ) : ZMod q)) * ψ j *
          ((vonMangoldt m / ((j * m : ℕ) : ℝ) : ℝ) : ℂ)) (n / j) else 0 := fun n _ => by
      split_ifs with h
      · simp only [Nat.mul_div_cancel' h]
      · rfl
    rw [Finset.sum_congr rfl hrw, sum_Icc_ite_dvd_eq N hj1 (fun m => conj (χ ((j * m : ℕ) : ZMod q)) *
      ψ j * ((vonMangoldt m / ((j * m : ℕ) : ℝ) : ℝ) : ℂ)), conj_twistLogSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.cast_mul, map_mul, map_mul]
    push_cast
    have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast hj1.ne'
    by_cases hm : (m : ℂ) = 0
    · rw [hm]; simp
    · field_simp
  rw [hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-! ### The tail of the twisted series -/

theorem tendsto_twistLogTail (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (twistLogTail χ) atTop (𝓝 0) := by
  have h := (ArtinMertens.tendsto_sum_twist_vonMangoldt_div χ hχ).comp
    tendsto_natCast_atTop_atTop
  have h2 := h.sub_const (twistLogDeriv χ)
  rw [show -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 =
    twistLogDeriv χ from rfl, sub_self] at h2
  refine h2.congr fun k => ?_
  simp only [Function.comp_apply, Nat.floor_natCast, twistLogTail, twistLogSum, twistLogDeriv]

theorem hasVonMangoldtIncrements_twistLogTail (χ : DirichletCharacter ℂ q) :
    HasVonMangoldtIncrements (twistLogTail χ) 1 := fun k => by
  unfold twistLogTail twistLogSum
  rw [Finset.sum_Icc_succ_top (by omega), sub_sub_sub_cancel_right, add_sub_cancel_left, one_mul,
    norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  push_cast
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine div_le_div_of_nonneg_right ?_ hk.le
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)

theorem tendsto_conj_twistLogTail (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun k => conj (twistLogTail χ k)) atTop (𝓝 0) := by
  have := (Complex.continuous_conj.tendsto 0).comp (tendsto_twistLogTail χ hχ)
  rwa [map_zero] at this

theorem hasVonMangoldtIncrements_conj_twistLogTail (χ : DirichletCharacter ℂ q) :
    HasVonMangoldtIncrements (fun k => conj (twistLogTail χ k)) 1 := fun k => by
  rw [← map_sub, Complex.norm_conj]
  exact hasVonMangoldtIncrements_twistLogTail χ k

/-! ### Newman's theorem for the tail -/

/-- `G(z) = −L'(z + 1, χ)/L(z + 1, χ)`. -/
def twistLogDerivShift (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) (z + 1) / DirichletCharacter.LFunction χ (z + 1)

theorem analyticAt_twistLogDerivShift (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ}
    (hz : DirichletCharacter.LFunction χ (z + 1) ≠ 0) :
    AnalyticAt ℂ (twistLogDerivShift χ) z := by
  have hdiff := DirichletCharacter.differentiable_LFunction hχ
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    fun w _ => hdiff.analyticAt w
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z := analyticAt_id.add analyticAt_const
  have hL : AnalyticAt ℂ (fun w : ℂ => DirichletCharacter.LFunction χ (w + 1)) z :=
    (hA (z + 1) trivial).comp (f := fun w : ℂ => w + 1) hshift
  have hD : AnalyticAt ℂ (fun w : ℂ => deriv (DirichletCharacter.LFunction χ) (w + 1)) z :=
    ((hA.deriv) (z + 1) trivial).comp (f := fun w : ℂ => w + 1) hshift
  exact hD.neg.div hL hz

/-- The difference quotient `(G(z) − G(0))/z` is analytic on `Re z ≥ 0`. -/
theorem analyticAt_dslope_twistLogDerivShift (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ}
    (hz : 0 ≤ z.re) : AnalyticAt ℂ (dslope (twistLogDerivShift χ) 0) z := by
  set U : Set ℂ := {w | DirichletCharacter.LFunction χ (w + 1) ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun
    ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      (continuous_id.add continuous_const)) continuous_const
  have hmem : ∀ w : ℂ, 0 ≤ w.re → w ∈ U := fun w hw =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp; linarith)
  have hG : DifferentiableOn ℂ (twistLogDerivShift χ) U := fun w hw =>
    (analyticAt_twistLogDerivShift χ hχ hw).differentiableAt.differentiableWithinAt
  have h0 : U ∈ 𝓝 (0 : ℂ) := hU.mem_nhds (hmem 0 (by simp))
  have hd := (Complex.differentiableOn_dslope h0).mpr hG
  exact hd.analyticAt (hU.mem_nhds (hmem z hz))

/-- The Newman function `f(u) = δ_χ(⌊e^u⌋)`. -/
def twistTailNewmanF (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ := twistLogTail χ ⌊Real.exp u⌋₊

theorem measurable_twistTailNewmanF (χ : DirichletCharacter ℂ q) :
    Measurable (twistTailNewmanF χ) :=
  measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp)

omit [NeZero q] in
theorem LSeries_twist_div_eq (χ : DirichletCharacter ℂ q) (z : ℂ) :
    LSeries (fun n => χ n * (vonMangoldt n : ℂ) / n) z =
      LSeries (fun n => χ n * (vonMangoldt n : ℂ)) (z + 1) := by
  unfold LSeries
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [LSeries.term]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
      Complex.cpow_add _ _ hn0, Complex.cpow_one]
    field_simp

/-- **The Laplace transform of the tail**: `∫_0^∞ δ_χ(⌊e^u⌋) e^{−zu} du = (G(z) − G(0))/z`. -/
theorem integral_twistTailLaplace_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ}
    (hz : 0 < z.re) :
    ∫ u in Set.Ioi (0 : ℝ), twistTailNewmanF χ u * cexp (-(z * u)) =
      dslope (twistLogDerivShift χ) 0 z := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hs : (1 : ℝ) < (z + 1).re := by simp; linarith
  set a : ℕ → ℂ := fun n => χ n * (vonMangoldt n : ℂ) / n with ha
  -- the partial sums are bounded
  have htend : Tendsto (fun n : ℕ => ∑ k ∈ Icc 1 n, a k) atTop (𝓝 (twistLogDeriv χ)) := by
    have h := (tendsto_twistLogTail χ hχ).add_const (twistLogDeriv χ)
    rw [zero_add] at h
    refine h.congr fun n => ?_
    simp only [twistLogTail, twistLogSum, ha, sub_add_cancel]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    simpa only [Real.rpow_zero] using htend.isBigO_one ℝ
  have hsumm : LSeriesSummable a z := by
    have h := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    unfold LSeriesSummable at h ⊢
    refine h.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [LSeries.term]
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
        Complex.cpow_add _ _ hn0, Complex.cpow_one]
      simp only [ha, Pi.mul_apply]
      field_simp
  have h1 := LSeries_eq_mul_integral a le_rfl hz hsumm hO
  rw [LSeries_twist_div_eq, ArtinMertens.LSeries_twist_vonMangoldt_eq_LFunction χ hs] at h1
  -- the substitution `t = e^u`
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn
    (fun t : ℝ => (∑ k ∈ Icc 1 ⌊t⌋₊, a k) * (t : ℂ) ^ (-(z + 1)))
  rw [ArtinMertens.exp_image_Ioi_zero] at hsub
  have hF : ∫ u in Set.Ioi (0 : ℝ), (∑ k ∈ Icc 1 ⌊Real.exp u⌋₊, a k) * cexp (-(z * u)) =
      twistLogDerivShift χ z / z := by
    rw [twistLogDerivShift, h1, hsub, mul_div_cancel_left₀ _ hz0]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [abs_of_pos (Real.exp_pos u), ArtinMertens.ofReal_exp_cpow, Complex.real_smul,
      Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  -- integrability of both pieces
  obtain ⟨B, hB⟩ : ∃ B, ∀ n : ℕ, ‖∑ k ∈ Icc 1 n, a k‖ ≤ B := by
    obtain ⟨B, hB⟩ := htend.norm.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have hexp : IntegrableOn (fun u : ℝ => cexp (-(z * u))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_complex_Ioi (a := -z) (by simp; linarith) 0
    simpa only [neg_mul] using this
  have hmeasF : Measurable fun u : ℝ => ∑ k ∈ Icc 1 ⌊Real.exp u⌋₊, a k := by
    show Measurable ((fun n : ℕ => ∑ k ∈ Icc 1 n, a k) ∘ fun u : ℝ => ⌊Real.exp u⌋₊)
    exact measurable_from_nat.comp (Nat.measurable_floor.comp Real.measurable_exp)
  have hint1 : IntegrableOn (fun u : ℝ => (∑ k ∈ Icc 1 ⌊Real.exp u⌋₊, a k) * cexp (-(z * u)))
      (Set.Ioi 0) := by
    refine (hexp.norm.const_mul B).mono' ?_ (ae_of_all _ fun u => ?_)
    · exact (hmeasF.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal).neg).measurable).aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hconst : ∫ u in Set.Ioi (0 : ℝ), cexp (-(z * u)) = 1 / z := by
    have := integral_exp_mul_complex_Ioi (a := -z) (by simp; linarith) 0
    simp only [neg_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
    rw [this]
    field_simp
  have hsplit : ∀ u : ℝ, twistTailNewmanF χ u * cexp (-(z * u)) =
      (∑ k ∈ Icc 1 ⌊Real.exp u⌋₊, a k) * cexp (-(z * u)) - twistLogDeriv χ * cexp (-(z * u)) :=
    fun u => by simp only [twistTailNewmanF, twistLogTail, twistLogSum, ha]; ring
  simp_rw [hsplit]
  rw [integral_sub hint1 (hexp.const_mul _), MeasureTheory.integral_const_mul, hF, hconst,
    dslope_of_ne _ hz0, slope_def_field, sub_zero]
  have hG0 : twistLogDerivShift χ 0 = twistLogDeriv χ := by
    simp [twistLogDerivShift, twistLogDeriv]
  rw [hG0]
  field_simp

/-- **Newman's theorem for the tail**: `∫_0^T δ_χ(⌊e^u⌋) du → I_χ = −(L'/L)'(1, χ)`. -/
theorem tendsto_integral_twistLogTail (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun T : ℝ => ∫ u in (0 : ℝ)..T, twistLogTail χ ⌊Real.exp u⌋₊) atTop
      (𝓝 (twistLogDerivDeriv χ)) := by
  obtain ⟨B, hB⟩ := exists_norm_le_of_tendsto (tendsto_twistLogTail χ hχ)
  have h := ArtinMertens.newman_analytic_theorem (f := twistTailNewmanF χ) (B := B)
    (measurable_twistTailNewmanF χ).aestronglyMeasurable (fun t _ => hB _)
    (g := dslope (twistLogDerivShift χ) 0)
    (fun z hz => analyticAt_dslope_twistLogDerivShift χ hχ hz)
    (fun z hz => (integral_twistTailLaplace_eq χ hχ hz).symm)
  rw [dslope_same] at h
  have hd : deriv (twistLogDerivShift χ) 0 = twistLogDerivDeriv χ := by
    unfold twistLogDerivDeriv
    show deriv (fun z => (fun s => -deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) (z + 1)) 0 = _
    rw [deriv_comp_add_const (fun s => -deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s) 1 0, zero_add]
  rw [hd] at h
  exact h

/-! ### Means of the packet weights -/

theorem sum_range_eq_sum_zmod (f : ZMod q → ℂ) :
    ∑ r ∈ range q, f r = ∑ a : ZMod q, f a := by
  refine (Finset.sum_nbij (fun x : ZMod q => x.val)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun x _ y _ h => ZMod.val_injective q h) (fun r hr => ?_)
    (fun x _ => by rw [ZMod.natCast_zmod_val])).symm
  refine ⟨(r : ZMod q), Finset.mem_univ _, ?_⟩
  exact ZMod.val_cast_of_lt (Finset.mem_range.mp hr)

/-- Orthogonality: `Σ_{r < q} χ̄(r) ψ(r) = [χ = ψ] φ(q)`. -/
theorem sum_range_conj_mul (χ ψ : DirichletCharacter ℂ q) :
    ∑ r ∈ range q, conj (χ r) * ψ r = if χ = ψ then (q.totient : ℂ) else 0 := by
  have e : ∀ a : ZMod q, conj (χ a) * ψ a = (χ⁻¹ * ψ) a := fun a => by
    rw [MulChar.mul_apply, ← MulChar.star_apply']
    rfl
  rw [Finset.sum_congr rfl fun (r : ℕ) _ => e (r : ZMod q),
    sum_range_eq_sum_zmod (fun a => (χ⁻¹ * ψ) a)]
  split_ifs with h
  · subst h
    rw [inv_mul_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · refine MulChar.sum_eq_zero_of_ne_one fun h' => h ?_
    exact (inv_mul_eq_one.mp h')

/-! ### The second order -/

/-- **The second order of the character packets**: for nontrivial `χ, ψ` mod `q`,
`⟨P X_χ, X_ψ⟩ − (S_ψ(∞) + S̄_χ(∞))⟨X_χ, X_ψ⟩ → [χ = ψ](φ(q)/q)(I_χ + Ī_χ)`. -/
theorem tendsto_charPacketPairing_sub (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    Tendsto (fun N => charPacketPairing χ ψ N -
      (twistLogDeriv ψ + conj (twistLogDeriv χ)) * charPacketGram χ ψ N) atTop
      (𝓝 (if χ = ψ then (q.totient / q : ℂ) * (twistLogDerivDeriv χ + conj (twistLogDerivDeriv χ))
        else 0)) := by
  set v : ℕ → ℂ := fun n => conj (χ n) * ψ n with hv
  have hq : 0 < q := NeZero.pos q
  have hper : ∀ n, v (n + q) = v n := fun n => by
    simp only [hv]; push_cast; rw [ZMod.natCast_self, add_zero]
  have hmean : ∑ r ∈ range q, v r = if χ = ψ then (q.totient : ℂ) else 0 :=
    sum_range_conj_mul χ ψ
  have hid : ∀ N : ℕ, charPacketPairing χ ψ N -
      (twistLogDeriv ψ + conj (twistLogDeriv χ)) * charPacketGram χ ψ N =
      ∑ n ∈ Icc 1 N, v n / n * twistLogTail ψ (N / n) +
        ∑ n ∈ Icc 1 N, v n / n * (fun k => conj (twistLogTail χ k)) (N / n) := fun N => by
    rw [charPacketPairing_eq, charPacketGram, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hv, twistLogTail, map_sub]
    ring
  simp only [hid]
  have hincψ := hasVonMangoldtIncrements_twistLogTail ψ
  have hincχ := hasVonMangoldtIncrements_conj_twistLogTail χ
  have htψ := tendsto_twistLogTail ψ hψ
  have htχ := tendsto_conj_twistLogTail χ hχ
  split_ifs with hcs
  · subst hcs
    set μ : ℂ := (q.totient : ℂ) / q with hμ
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hmean0 : ∑ r ∈ range q, (v r - μ) = 0 := by
      rw [Finset.sum_sub_distrib, hmean, if_pos rfl, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, hμ]
      field_simp
      ring
    have hper0 : ∀ n, v (n + q) - μ = v n - μ := fun n => by rw [hper]
    have hsplit : ∀ (δ : ℕ → ℂ) (N : ℕ), ∑ n ∈ Icc 1 N, v n / n * δ (N / n) =
        μ * ∑ n ∈ Icc 1 N, δ (N / n) / n + ∑ n ∈ Icc 1 N, (v n - μ) / n * δ (N / n) :=
      fun δ N => by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    -- the constant-weight sums
    have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hL1 : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, twistLogTail χ (N / n) / n) atTop
        (𝓝 (twistLogDerivDeriv χ)) := by
      have h := (tendsto_sum_hyperbola_sub_integral zero_le_one
        (hasVonMangoldtIncrements_twistLogTail χ) (tendsto_twistLogTail χ hχ)).add
        ((tendsto_integral_twistLogTail χ hχ).comp hlog)
      rw [zero_add] at h
      refine h.congr fun N => ?_
      simp only [Function.comp_apply, sub_add_cancel]
    have hL3 : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, conj (twistLogTail χ (N / n)) / n) atTop
        (𝓝 (conj (twistLogDerivDeriv χ))) := by
      have h := (Complex.continuous_conj.tendsto _).comp hL1
      refine h.congr fun N => ?_
      simp only [Function.comp_apply, map_sum, map_div₀, map_natCast]
    have hL2 := tendsto_sum_periodic_mul_hyperbola hq hper0 hmean0 zero_le_one
      (hasVonMangoldtIncrements_twistLogTail χ) (tendsto_twistLogTail χ hχ)
    have hL4 := tendsto_sum_periodic_mul_hyperbola hq hper0 hmean0 zero_le_one hincχ htχ
    have htot := ((hL1.const_mul μ).add hL2).add ((hL3.const_mul μ).add hL4)
    simp only [add_zero] at htot
    rw [show μ * twistLogDerivDeriv χ + μ * conj (twistLogDerivDeriv χ) =
      μ * (twistLogDerivDeriv χ + conj (twistLogDerivDeriv χ)) by ring] at htot
    refine htot.congr fun N => ?_
    rw [hsplit (twistLogTail χ) N, hsplit (fun k => conj (twistLogTail χ k)) N]
  · have hmean0 : ∑ r ∈ range q, v r = 0 := by rw [hmean, if_neg hcs]
    have h1 := tendsto_sum_periodic_mul_hyperbola hq hper hmean0 zero_le_one hincψ htψ
    have h2 := tendsto_sum_periodic_mul_hyperbola hq hper hmean0 zero_le_one hincχ htχ
    simpa using h1.add h2

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
