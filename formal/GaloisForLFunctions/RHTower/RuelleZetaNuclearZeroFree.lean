import GaloisForLFunctions.HTGeometry.AnalyticMarkovTransferMatrix
import GaloisForLFunctions.RHTower.ZetaMultipleLandauZeroFree

/-!
# Nuclear Ruelle zeta functions are zero-free; `ζ` is not one of them

Let `S` be an analytic Markov system (`AnalyticMarkov.System`): the holomorphic inverse branches of a
real-analytic, orientation-preserving, expanding Markov map `T`, each mapping its Markov disc into a
compact subdisc of the next (so that the transfer operators are nuclear).  Its periodic points of
period `n` are the closed admissible words `P` of length `n`, with multiplier
`(T^n)′(x_P)⁻¹ = e^{Λ_P} ∈ (0, 1)`.  The Ruelle zeta function is
`ζ_R(s) = exp Σ_{n≥1} n⁻¹ Z_n(s)`, `Z_n(s) = Σ_P e^{sΛ_P} = Σ_{x ∈ Fix T^n} |(T^n)′(x)|^{−s}`
(`ruelleZeta`, `cycleSum`), where the series converges absolutely for `Re s > σ₀` (`AbscissaLE S σ₀`;
`σ₀ = h = 1` when the topological entropy is `1`).

**Theorem** (`ruelleZeta_continuation`).  The Fredholm determinant `D(s) = det(1 − L_s)`
(`fredholmD`) is entire, `ζ_R(s) D(s) = D(s + 1)` for `Re s > σ₀`, and `D(s + 1) ≠ 0` for
`Re s > σ₀ − 1`.  So `ζ_R` continues meromorphically as `D(s + 1)/D(s)` with no zero in
`Re s > σ₀ − 1`: for entropy `1` the Ruelle zeta function is zero-free on `Re s > 0`.

**Corollary** (`not_riemannZeta_eq_ruelleZeta`).  `ζ` is not the Ruelle zeta function of such a map
of entropy at most `1`: `ζ(ρ) = 0` at some `ρ` with `Re ρ = 1/2` (Hardy).

**Proof.**  By the trace formula `Tr L_s^n = Σ_P e^{sΛ_P}/(1 − e^{Λ_P}) = Σ_{k≥0} Z_n(s + k)`
(`AnalyticMarkov.System.itrace_mat`) and the identity `det(1 − L_s) = exp(−Σ_n Tr L_s^n/n)`
(`GeomFredholm.fdet_one_eq_exp`, valid since `Σ_n |Tr L_s^n| rⁿ < ∞` for some `r > 1` by the expansion
bound `e^{Λ_P} ≤ κⁿ`), `D(s) = exp(−Σ_{k≥0} log ζ_R(s + k))` for `Re s > σ₀`.  Shifting `s ↦ s + 1`
removes the term `k = 0`.
-/

open Complex Filter Topology Set Finset Metric
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.AnalyticMarkov
open GaloisForLFunctions.HTGeometry.GeomFredholm

noncomputable section

namespace RHTower.RuelleZeta

variable (S : System)

/-- `Z_n(s) = Σ_{closed words P of length n} e^{sΛ_P}`. -/
def cycleSum (s : ℂ) (n : ℕ) : ℂ :=
  ∑ a, ∑ P ∈ S.wordsTo a a n, Complex.exp (s * S.cycleΛ a n P)

/-- `Z_n(σ)` for real `σ`. -/
def realCycleSum (σ : ℝ) (n : ℕ) : ℝ :=
  ∑ a, ∑ P ∈ S.wordsTo a a n, Real.exp (σ * (S.cycleΛ a n P).re)

/-- `log ζ_R(s) = Σ_{n≥1} Z_n(s)/n`. -/
def logZeta (s : ℂ) : ℂ := ∑' n : ℕ, cycleSum S s (n + 1) / ((n + 1 : ℕ) : ℂ)

/-- The Ruelle zeta function. -/
def ruelleZeta (s : ℂ) : ℂ := Complex.exp (logZeta S s)

/-- The Fredholm determinant `D(s) = det(1 − L_s)`. -/
def fredholmD (s : ℂ) : ℂ := fdet (S.mat s) 1

/-- The dynamical series converges absolutely for `Re s > σ₀`. -/
def AbscissaLE (σ₀ : ℝ) : Prop :=
  ∀ σ : ℝ, σ₀ < σ → Summable fun n : ℕ => realCycleSum S σ (n + 1) / ((n + 1 : ℕ) : ℝ)

variable {S} {σ₀ : ℝ}

/-! ## Single closed words -/

/-- `κ₊ = max κ ½ ∈ [½, 1)`. -/
def κp (S : System) : ℝ := max S.κ (1 / 2)

theorem κp_pos : 0 < κp S := lt_max_of_lt_right (by norm_num)
theorem κp_lt_one : κp S < 1 := max_lt S.κ_lt_one (by norm_num)

theorem κ_pos_of_branch (e : Fin S.q) : 0 < S.κ := by
  have hc : ((S.c (S.src e) : ℝ) : ℂ) ∈ closedBall (S.c (S.src e) : ℂ) (S.θ * S.R (S.src e)) :=
    mem_closedBall_self (mul_nonneg S.θ_nonneg (S.R_pos _).le)
  exact (Real.exp_pos _).trans_le (S.expanding e _ hc)

theorem word_facts {a : Fin S.p} {n : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.wordsTo a a (n + 1)) :
    (S.cycleΛ a (n + 1) P).im = 0 ∧
      (S.cycleΛ a (n + 1) P).re ≤ (n + 1) * Real.log (κp S) ∧
      ‖Complex.exp (S.cycleΛ a (n + 1) P)‖ ≤ DiscFixedPoint.contractionFactor S.θ := by
  have hcl := System.isClosed_of_mem_wordsTo hP
  obtain ⟨him, hle, -⟩ := System.cycleΛ_spec hcl
  refine ⟨him, ?_, System.norm_exp_cycleΛ_le hcl⟩
  -- the word has a first branch, so `κ > 0`
  have hP1 := hcl.1
  rw [System.mem_paths_succ] at hP1
  obtain ⟨e, -, -, -, -⟩ := hP1
  have hκ := κ_pos_of_branch e
  have h1 : Real.exp (S.cycleΛ a (n + 1) P).re ≤ κp S ^ (n + 1) :=
    hle.trans (pow_le_pow_left₀ hκ.le (le_max_left _ _) _)
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp, Real.log_pow] at h2
  exact_mod_cast h2

theorem norm_exp_mul_cycleΛ {a : Fin S.p} {n : ℕ} {P : List (Fin S.q)}
    (hP : P ∈ S.wordsTo a a (n + 1)) (s : ℂ) :
    ‖Complex.exp (s * S.cycleΛ a (n + 1) P)‖ = Real.exp (s.re * (S.cycleΛ a (n + 1) P).re) := by
  rw [Complex.norm_exp, Complex.mul_re, (word_facts hP).1, mul_zero, sub_zero]

/-- `e^{σΛ} ≤ e^{σ'Λ} t^{n+1}` with `t = κ₊^{σ−σ'}`, for `σ' ≤ σ`. -/
theorem exp_mul_le {a : Fin S.p} {n : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.wordsTo a a (n + 1))
    {σ σ' : ℝ} (h : σ' ≤ σ) :
    Real.exp (σ * (S.cycleΛ a (n + 1) P).re) ≤
      Real.exp (σ' * (S.cycleΛ a (n + 1) P).re) *
        Real.exp ((σ - σ') * Real.log (κp S)) ^ (n + 1) := by
  have h2 := (word_facts hP).2.1
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have hδ : 0 ≤ σ - σ' := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hδ
  push_cast at h3 ⊢
  nlinarith

theorem norm_cycleSum_le (s : ℂ) (n : ℕ) :
    ‖cycleSum S s (n + 1)‖ ≤ realCycleSum S s.re (n + 1) := by
  unfold cycleSum realCycleSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_)
  exact (Finset.sum_le_sum fun P hP => (norm_exp_mul_cycleΛ hP s).le)

theorem realCycleSum_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ realCycleSum S σ n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

theorem realCycleSum_le {σ σ' : ℝ} (h : σ' ≤ σ) (n : ℕ) :
    realCycleSum S σ (n + 1) ≤
      Real.exp ((σ - σ') * Real.log (κp S)) ^ (n + 1) * realCycleSum S σ' (n + 1) := by
  unfold realCycleSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun P hP => (exp_mul_le hP h).trans (le_of_eq (by ring))

/-! ## The trace as a sum over shifts -/

theorem hasSum_cycleSum_shift (s : ℂ) (n : ℕ) :
    HasSum (fun k : ℕ => cycleSum S (s + k) (n + 1)) (S.cycleTraceSum s (n + 1)) := by
  unfold cycleSum System.cycleTraceSum
  refine hasSum_sum fun a _ => hasSum_sum fun P hP => ?_
  set Λ := S.cycleΛ a (n + 1) P
  have hκ := DiscFixedPoint.contractionFactor_lt_one S.θ_nonneg S.θ_lt_one
  have hq : ‖Complex.exp Λ‖ < 1 := lt_of_le_of_lt (word_facts hP).2.2 hκ
  have hgeo := (hasSum_geometric_of_norm_lt_one hq).mul_left (Complex.exp (s * Λ))
  have e : ∀ k : ℕ, Complex.exp ((s + k) * Λ) = Complex.exp (s * Λ) * Complex.exp Λ ^ k :=
    fun k => by rw [← Complex.exp_nat_mul, ← Complex.exp_add]; ring_nf
  simp_rw [e]
  rw [div_eq_mul_inv]
  exact hgeo

theorem norm_cycleTraceSum_le (s : ℂ) (n : ℕ) :
    ‖S.cycleTraceSum s (n + 1)‖ ≤
      realCycleSum S s.re (n + 1) / (1 - DiscFixedPoint.contractionFactor S.θ) := by
  have hκ := DiscFixedPoint.contractionFactor_lt_one S.θ_nonneg S.θ_lt_one
  have hpos : 0 < 1 - DiscFixedPoint.contractionFactor S.θ := by linarith
  unfold System.cycleTraceSum realCycleSum
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P hP => ?_)
  rw [norm_div, norm_exp_mul_cycleΛ hP s]
  refine div_le_div_of_nonneg_left (Real.exp_pos _).le hpos ?_
  have h1 := (word_facts hP).2.2
  have h2 : 1 - ‖Complex.exp (S.cycleΛ a (n + 1) P)‖ ≤ ‖1 - Complex.exp (S.cycleΛ a (n + 1) P)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (Complex.exp (S.cycleΛ a (n + 1) P))
    rwa [norm_one] at this
  linarith

/-! ## The determinant -/

theorem exists_bound_mul_pow_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ∃ B : ℝ, ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * u ^ (n + 1) ≤ B := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1 (r := u)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hu0]; exact hu1)
  refine ⟨∑' m : ℕ, (m : ℝ) ^ 1 * u ^ m, fun n => ?_⟩
  have h := hs.le_tsum (n + 1) (fun j _ => by positivity)
  simpa using h

/-- **The trace series of `L_s` converges on a disc of radius `> 1`.** -/
theorem exists_summable_itrace (hσ₀ : AbscissaLE S σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    ∃ r : ℝ, 1 < r ∧ Summable fun n => ‖itrace (S.mat s) (n + 1)‖ * r ^ (n + 1) := by
  set σ' : ℝ := (s.re + σ₀) / 2 with hσ'
  have hσ'1 : σ₀ < σ' := by rw [hσ']; linarith
  have hσ'2 : σ' ≤ s.re := by rw [hσ']; linarith
  set t : ℝ := Real.exp ((s.re - σ') * Real.log (κp S)) with ht
  have hlog : Real.log (κp S) < 0 := Real.log_neg (κp_pos (S := S)) (κp_lt_one (S := S))
  have hδ : 0 < s.re - σ' := by rw [hσ']; linarith
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by
    have hneg : (s.re - σ') * Real.log (κp S) < 0 := mul_neg_of_pos_of_neg hδ hlog
    rw [ht]
    calc Real.exp ((s.re - σ') * Real.log (κp S)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  set u : ℝ := Real.sqrt t with hu
  have hu0 : 0 < u := Real.sqrt_pos.mpr ht0
  have hu1 : u < 1 := by rw [hu, Real.sqrt_lt' one_pos]; simpa using ht1
  have hut : u ^ 2 = t := Real.sq_sqrt ht0.le
  obtain ⟨B, hB⟩ := exists_bound_mul_pow_le hu0.le hu1
  set κc := DiscFixedPoint.contractionFactor S.θ
  have hκ := DiscFixedPoint.contractionFactor_lt_one S.θ_nonneg S.θ_lt_one
  have hpos : 0 < 1 - κc := by linarith
  refine ⟨u⁻¹, (one_lt_inv₀ hu0).mpr hu1, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (((hσ₀ σ' hσ'1).mul_left (B / (1 - κc))))
  rw [System.itrace_mat]
  have h1 := norm_cycleTraceSum_le (S := S) s n
  have h2 := realCycleSum_le (S := S) hσ'2 n
  have hR0 := realCycleSum_nonneg (S := S) σ' (n + 1)
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hBn := hB n
  calc ‖S.cycleTraceSum s (n + 1)‖ * u⁻¹ ^ (n + 1)
      ≤ (t ^ (n + 1) * realCycleSum S σ' (n + 1) / (1 - κc)) * u⁻¹ ^ (n + 1) := by
        refine mul_le_mul_of_nonneg_right (h1.trans ?_) (by positivity)
        exact div_le_div_of_nonneg_right h2 hpos.le
    _ = (((n + 1 : ℕ) : ℝ) * u ^ (n + 1)) * (realCycleSum S σ' (n + 1) /
          ((n + 1 : ℕ) : ℝ)) / (1 - κc) := by
        rw [← hut, ← pow_mul, inv_pow]
        field_simp
        ring
    _ ≤ B * (realCycleSum S σ' (n + 1) / ((n + 1 : ℕ) : ℝ)) / (1 - κc) := by
        gcongr
    _ = B / (1 - κc) * (realCycleSum S σ' (n + 1) / ((n + 1 : ℕ) : ℝ)) := by ring

theorem geomDecay_mat_of_norm_le {r : ℝ} {s : ℂ} (hs : ‖s‖ ≤ r) :
    ∃ C : ℝ, GeomDecay (S.mat s) C S.η := by
  obtain ⟨L, -, hL⟩ := S.exists_bound_ℓ
  exact ⟨_, System.geomDecay_mat hL hs⟩

/-- **The determinant is entire.** -/
theorem differentiable_fredholmD : Differentiable ℂ (fredholmD S) := by
  intro s₀
  obtain ⟨L, -, hL⟩ := S.exists_bound_ℓ
  set r : ℝ := ‖s₀‖ + 1 with hr
  have hU : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hM : ∀ s ∈ Metric.ball (0 : ℂ) r,
      GeomDecay (S.mat s) (S.q * Real.exp (r * L) / (S.η ^ (S.p - 1)) ^ 2) S.η := fun s hs =>
    System.geomDecay_mat hL (mem_ball_zero_iff.mp hs).le
  have hd : ∀ i j, DifferentiableOn ℂ (fun s => S.mat s i j) (Metric.ball (0 : ℂ) r) :=
    fun i j => (System.differentiable_mat i j).differentiableOn
  have h := differentiableOn_fdet hU hM hd 1 System.η_pos.le System.η_lt_one
  exact h.differentiableAt (hU.mem_nhds (mem_ball_zero_iff.mpr (by rw [hr]; linarith)))

/-- `D(s) = exp(−Σ_{k≥0} log ζ_R(s + k))` for `Re s > σ₀`. -/
theorem fredholmD_eq (hσ₀ : AbscissaLE S σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    Summable (fun k : ℕ => logZeta S (s + k)) ∧
      fredholmD S s = Complex.exp (-∑' k : ℕ, logZeta S (s + k)) := by
  obtain ⟨C, hM⟩ := geomDecay_mat_of_norm_le (S := S) (r := ‖s‖) (s := s) le_rfl
  obtain ⟨r, hr, hsum⟩ := exists_summable_itrace hσ₀ hs
  have hD := fdet_one_eq_exp hM hr hsum
  -- the double series
  set f : ℕ → ℕ → ℂ := fun n k => cycleSum S (s + k) (n + 1) / ((n + 1 : ℕ) : ℂ) with hf
  have hκ := DiscFixedPoint.contractionFactor_lt_one S.θ_nonneg S.θ_lt_one
  set σ := s.re
  have hsummσ := hσ₀ σ hs
  -- `|Z_{n+1}(s + k)| ≤ κ₊^k Z_{n+1}(σ)`
  have hfb : ∀ n k, ‖f n k‖ ≤ (realCycleSum S σ (n + 1) / ((n + 1 : ℕ) : ℝ)) * κp S ^ k := by
    intro n k
    simp only [hf]
    rw [norm_div, Complex.norm_natCast]
    have h1 := norm_cycleSum_le (S := S) (s + k) n
    have hre : (s + k).re = σ + k := by simp [σ]
    rw [hre] at h1
    have h2 := realCycleSum_le (S := S) (σ := σ + k) (σ' := σ) (by linarith [Nat.cast_nonneg (α := ℝ) k]) n
    have h3 : Real.exp ((σ + k - σ) * Real.log (κp S)) ^ (n + 1) ≤ κp S ^ k := by
      have hl := Real.log_neg (κp_pos (S := S)) (κp_lt_one (S := S))
      have hk := Nat.cast_nonneg (α := ℝ) k
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      have hneg : (k : ℝ) * Real.log (κp S) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk hl.le
      rw [show σ + k - σ = (k : ℝ) by ring, ← Real.exp_nat_mul]
      calc Real.exp (((n + 1 : ℕ) : ℝ) * ((k : ℝ) * Real.log (κp S)))
          ≤ Real.exp ((k : ℝ) * Real.log (κp S)) := by
            rw [Real.exp_le_exp]; push_cast; nlinarith [mul_nonpos_of_nonneg_of_nonpos hn0 hneg]
        _ = κp S ^ k := by rw [Real.exp_nat_mul, Real.exp_log κp_pos]
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hR0 := realCycleSum_nonneg (S := S) σ (n + 1)
    calc ‖cycleSum S (s + ↑k) (n + 1)‖ / ((n + 1 : ℕ) : ℝ)
        ≤ (Real.exp ((σ + k - σ) * Real.log (κp S)) ^ (n + 1) * realCycleSum S σ (n + 1)) /
            ((n + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (h1.trans h2) hn.le
      _ ≤ (κp S ^ k * realCycleSum S σ (n + 1)) / ((n + 1 : ℕ) : ℝ) := by gcongr
      _ = realCycleSum S σ (n + 1) / ((n + 1 : ℕ) : ℝ) * κp S ^ k := by ring
  have hgeo : Summable fun k : ℕ => κp S ^ k :=
    summable_geometric_of_lt_one κp_pos.le κp_lt_one
  have hjoint : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded (hsummσ.mul_of_nonneg hgeo (fun n => by
      have := realCycleSum_nonneg (S := S) σ (n + 1); positivity) (fun k => by
        have := κp_pos (S := S); positivity)) fun x => ?_
    exact hfb x.1 x.2
  -- rows: `Σ_k f n k = Tr L_s^{n+1}/(n+1)`
  have hrow : ∀ n, HasSum (fun k => f n k) (itrace (S.mat s) (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
    intro n
    rw [System.itrace_mat]
    exact (hasSum_cycleSum_shift (S := S) s n).div_const _
  -- columns: `Σ_n f n k = log ζ_R(s + k)`
  have hcolb : ∀ k : ℕ, ‖logZeta S (s + k)‖ ≤
      (∑' n, realCycleSum S σ (n + 1) / ((n + 1 : ℕ) : ℝ)) * κp S ^ k := by
    intro k
    have hs1 : Summable fun n => ‖f n k‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hfb n k)
        (hsummσ.mul_right (κp S ^ k))
    calc ‖logZeta S (s + k)‖ = ‖∑' n, f n k‖ := rfl
      _ ≤ ∑' n, ‖f n k‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' n, realCycleSum S σ (n + 1) / ((n + 1 : ℕ) : ℝ) * κp S ^ k :=
          hs1.tsum_le_tsum (fun n => hfb n k) (hsummσ.mul_right _)
      _ = (∑' n, realCycleSum S σ (n + 1) / ((n + 1 : ℕ) : ℝ)) * κp S ^ k := tsum_mul_right
  have hlogsum : Summable fun k : ℕ => logZeta S (s + k) :=
    Summable.of_norm_bounded (hgeo.mul_left _) hcolb
  refine ⟨hlogsum, ?_⟩
  have htrace : traceSeries (itrace (S.mat s)) 1 = ∑' k : ℕ, logZeta S (s + k) := by
    unfold traceSeries
    have e1 : (fun n : ℕ => (1 : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ) * itrace (S.mat s) (n + 1)) =
        fun n => ∑' k, f n k := by
      funext n
      rw [(hrow n).tsum_eq, one_pow]
      ring
    rw [e1, ← hjoint.tsum_comm]
    rfl
  unfold fredholmD
  rw [hD, htrace]

/-! ## The functional equation and the zero-free region -/

/-- **`ζ_R(s) D(s) = D(s + 1)`** for `Re s > σ₀`. -/
theorem ruelleZeta_mul_fredholmD (hσ₀ : AbscissaLE S σ₀) {s : ℂ} (hs : σ₀ < s.re) :
    ruelleZeta S s * fredholmD S s = fredholmD S (s + 1) := by
  obtain ⟨hsum, hD⟩ := fredholmD_eq hσ₀ hs
  have hs1 : σ₀ < (s + 1).re := by simp; linarith
  obtain ⟨-, hD1⟩ := fredholmD_eq hσ₀ hs1
  have hsplit : ∑' k : ℕ, logZeta S (s + k) =
      logZeta S s + ∑' k : ℕ, logZeta S (s + 1 + k) := by
    rw [hsum.tsum_eq_zero_add]
    congr 1
    · simp
    · refine tsum_congr fun k => ?_
      congr 1
      push_cast
      ring
  rw [hD, hD1, hsplit, neg_add, Complex.exp_add, ruelleZeta, ← mul_assoc, ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero, one_mul]

/-- **`D(s + 1)` has no zero on `Re s > σ₀ − 1`.** -/
theorem fredholmD_add_one_ne_zero (hσ₀ : AbscissaLE S σ₀) {s : ℂ} (hs : σ₀ - 1 < s.re) :
    fredholmD S (s + 1) ≠ 0 := by
  have hs1 : σ₀ < (s + 1).re := by simp; linarith
  rw [(fredholmD_eq hσ₀ hs1).2]
  exact Complex.exp_ne_zero _

/-- **Nuclear Ruelle zeta functions are zero-free to the left of their abscissa.**  The determinant
`D(s) = det(1 − L_s)` is entire, `ζ_R(s) D(s) = D(s + 1)` on `Re s > σ₀`, and `D(s + 1) ≠ 0` on
`Re s > σ₀ − 1`; hence the meromorphic continuation `D(s + 1)/D(s)` of `ζ_R` has no zero on
`Re s > σ₀ − 1` (on `Re s > 0` for entropy `1`). -/
theorem ruelleZeta_continuation (hσ₀ : AbscissaLE S σ₀) :
    Differentiable ℂ (fredholmD S) ∧
      (∀ s : ℂ, σ₀ < s.re → ruelleZeta S s * fredholmD S s = fredholmD S (s + 1)) ∧
      (∀ s : ℂ, σ₀ - 1 < s.re → fredholmD S (s + 1) ≠ 0) :=
  ⟨differentiable_fredholmD, fun _ hs => ruelleZeta_mul_fredholmD hσ₀ hs,
    fun _ hs => fredholmD_add_one_ne_zero hσ₀ hs⟩

/-- **`ζ` is not a nuclear Ruelle zeta function of entropy at most one.** -/
theorem not_riemannZeta_eq_ruelleZeta (hσ₀ : AbscissaLE S 1) :
    ¬ ∀ s : ℂ, 1 < s.re → riemannZeta s = ruelleZeta S s := by
  intro h
  set U : Set ℂ := {1}ᶜ with hUdef
  have hU : IsOpen U := isOpen_compl_singleton
  have hUc : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      1).isPreconnected
  set F : ℂ → ℂ := fun s => riemannZeta s * fredholmD S s - fredholmD S (s + 1) with hFdef
  have hDd := differentiable_fredholmD (S := S)
  have hFd : DifferentiableOn ℂ F U := fun s hs => by
    have hadd : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := differentiableAt_id.add_const 1
    have h3' := DifferentiableAt.comp (g := fredholmD S) (f := fun z : ℂ => z + 1) s
      (hDd (s + 1)) hadd
    have h3 : DifferentiableAt ℂ (fun z => fredholmD S (z + 1)) s := h3'
    exact (((differentiableAt_riemannZeta hs).mul (hDd s)).sub h3).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hU
  have h2U : (2 : ℂ) ∈ U := by simp [hUdef]
  have hev : F =ᶠ[𝓝 2] 0 := by
    have hV : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hV] with s hs
    simp only [hFdef, Pi.zero_apply]
    rw [h s hs, ruelleZeta_mul_fredholmD hσ₀ hs, sub_self]
  have hzero := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc h2U hev
  obtain ⟨ρ, hρre, hρ⟩ := RHTower.ZetaMultiple.exists_riemannZeta_zero_re_half
  have hρU : ρ ∈ U := by
    simp only [hUdef, mem_compl_iff, mem_singleton_iff]
    intro h1; rw [h1] at hρre; norm_num at hρre
  have hFρ := hzero hρU
  simp only [hFdef, Pi.zero_apply, hρ, zero_mul, zero_sub, neg_eq_zero] at hFρ
  exact fredholmD_add_one_ne_zero hσ₀ (by rw [hρre]; norm_num) hFρ

end RHTower.RuelleZeta

end
