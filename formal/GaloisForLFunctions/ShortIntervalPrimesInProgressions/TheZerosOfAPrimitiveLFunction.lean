import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.HTGeometry.OrderOneConvergenceExponent

/-!
# The zeros of a primitive Dirichlet `L`-function

Let `χ` be a primitive nonprincipal character mod `N` and `Λ(s, χ)` its completed `L`-function,
an entire function of order one. Its zeros, counted with multiplicity, are indexed by the zero
copies of `z ↦ Λ(z + 2, χ)` (`LZero χ`, with value `LZero.point`).

* Every zero lies in the open critical strip: `Λ ≠ 0` on `Re s ≥ 1` because `L(s, χ) ≠ 0` there,
  and on `Re s ≤ 0` by the functional equation, whose root number is nonzero because applying
  the equation twice returns `Λ` (`zero_re_mem`).
* **Hadamard.** `Λ'/Λ(s) = A + Σ_ρ (1/(s − ρ) + 1/(ρ − 2))` wherever `Λ(s) ≠ 0`, the series over
  the zeros converging absolutely (`logDeriv_completedLFunction_eq`).
* The zeros have convergence exponent at most one: `Σ_ρ |ρ − 2|^{−α} < ∞` for every `α > 1`
  (`summable_norm_rpow_neg`).
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.CountableDivisor
open RHTower.OrderOneHadamard

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-! ### Convergence exponents of order-one divisors -/

/-- Every exponent above one is a convergence exponent of an order-one divisor. -/
theorem summable_rpow_neg_of_orderOneDensity {ι : Type*} {a : ι → ℂ}
    (hloc : LocallyFiniteDivisor a) (hden : OrderOneDensityIdx a) {α : ℝ} (hα : 1 < α) :
    Summable (fun i : ι => ‖a i‖ ^ (-α)) := by
  classical
  obtain ⟨K, hK, hcount⟩ := hden
  set S : Set ι := {i : ι | ‖a i‖ ≤ 1} with hS
  rw [← summable_subtype_and_compl (s := S)]
  constructor
  · haveI : Finite ↑S := Set.Finite.to_subtype (hloc 1)
    exact Summable.of_finite
  · have hgt : ∀ p : ↑(Sᶜ), 1 < ‖a p.1‖ := by
      intro p
      have hp := p.2
      simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
      exact hp
    have hle : ∀ n : ℕ, ({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard
        ≤ {i : ι | logBucket a i = n}.ncard := by
      intro n
      exact Set.ncard_le_ncard_of_injOn (fun p : ↑(Sᶜ) => (p : ι))
        (fun p hp => hp) (fun p _ q _ h => Subtype.ext h)
        (finite_logBucket_fiber hloc n)
    have hfib : ∀ n : ℕ, {p : ↑(Sᶜ) | logBucket a p.1 = n}.Finite := by
      intro n
      refine Set.Finite.ofFinset ((finite_logBucket_fiber hloc n).toFinset.preimage
        (fun p : ↑(Sᶜ) => (p : ι)) (fun p _ q _ h => Subtype.ext h)) ?_
      intro p
      simp [Set.Finite.mem_toFinset]
    refine summable_of_bucket _ (fun p => Real.rpow_nonneg (norm_nonneg _) _)
      (fun p => logBucket a p.1) hfib (fun n => Real.exp (-α * (n : ℝ)))
      (fun p => norm_rpow_le_expBucket (hgt p) (by linarith)) ?_
    -- the bucket counts `K (1 + e^{n+1}) log (2 + e^{n+1}) ≤ 2Ke (n + 2) e^n`
    have hmaj : Summable (fun n : ℕ =>
        (4 * K * Real.exp 1) * (((n : ℝ) + 1) * Real.exp (-(α - 1) * n))) :=
      (summable_linear_expNeg (by linarith)).mul_left _
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
    set E : ℝ := Real.exp ((n : ℝ) + 1) with hE
    have hE1 : (1 : ℝ) ≤ E := Real.one_le_exp (by positivity)
    have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have hE2 : (2 : ℝ) ≤ E := hexp1.trans (Real.exp_le_exp.mpr (by
      have := Nat.cast_nonneg (α := ℝ) n; linarith))
    have h3 : (({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard : ℝ)
        ≤ ({i : ι | logBucket a i = n}.ncard : ℝ) := by exact_mod_cast hle n
    have hcnt := le_trans (le_trans h3 (ncard_logBucket_fiber_le hloc n)) (hcount E hE1)
    have hlog : Real.log (2 + E) ≤ (n : ℝ) + 2 := by
      have hle2 : 2 + E ≤ Real.exp ((n : ℝ) + 2) := by
        rw [show (n : ℝ) + 2 = ((n : ℝ) + 1) + 1 by ring, Real.exp_add]
        nlinarith
      calc Real.log (2 + E) ≤ Real.log (Real.exp ((n : ℝ) + 2)) :=
            Real.log_le_log (by linarith) hle2
        _ = (n : ℝ) + 2 := Real.log_exp _
    have hlog0 : 0 ≤ Real.log (2 + E) := Real.log_nonneg (by linarith)
    have hsplit : E * Real.exp (-α * (n : ℝ)) = Real.exp 1 * Real.exp (-(α - 1) * n) := by
      rw [hE, ← Real.exp_add, ← Real.exp_add]; ring_nf
    calc (({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard : ℝ) * Real.exp (-α * (n : ℝ))
        ≤ (K * (1 + E) * Real.log (2 + E)) * Real.exp (-α * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hcnt (Real.exp_nonneg _)
      _ ≤ (K * (2 * E) * ((n : ℝ) + 2)) * Real.exp (-α * (n : ℝ)) := by
          gcongr
          linarith
      _ = 2 * K * ((n : ℝ) + 2) * (E * Real.exp (-α * (n : ℝ))) := by ring
      _ = 2 * K * ((n : ℝ) + 2) * (Real.exp 1 * Real.exp (-(α - 1) * n)) := by rw [hsplit]
      _ ≤ 4 * K * ((n : ℝ) + 1) * (Real.exp 1 * Real.exp (-(α - 1) * n)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
      _ = (4 * K * Real.exp 1) * (((n : ℝ) + 1) * Real.exp (-(α - 1) * n)) := by ring

variable {N : ℕ} [NeZero N]

/-! ### The completed `L`-function -/

/-- `Λ(z + 2, χ)`: the completed `L`-function centred at the anchor `2`. -/
def shiftedL (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  DirichletCharacter.completedLFunction χ (z + 2)

/-- The zeros of `Λ(s, χ)`, with multiplicity. -/
abbrev LZero (χ : DirichletCharacter ℂ N) : Type := ZeroCopy (shiftedL χ)

/-- The zero `ρ` of a zero copy. -/
def LZero.point {χ : DirichletCharacter ℂ N} (q : LZero χ) : ℂ :=
  zeroCopyPoint (shiftedL χ) q + 2

variable {χ : DirichletCharacter ℂ N}

theorem analyticOnNhd_shiftedL (hχ : χ ≠ 1) : AnalyticOnNhd ℂ (shiftedL χ) univ :=
  ((DirichletCharacter.differentiable_completedLFunction hχ).comp
    (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ

omit [NeZero N] in
theorem gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

theorem completedLFunction_eq_mul {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s = χ.gammaFactor s * DirichletCharacter.LFunction χ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0),
    mul_div_cancel₀ _ (gammaFactor_ne_zero hs)]

/-- `Λ(s, χ) ≠ 0` on `Re s ≥ 1`. -/
theorem completedLFunction_ne_zero_of_one_le_re (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  rw [completedLFunction_eq_mul (by linarith)]
  exact mul_ne_zero (gammaFactor_ne_zero (by linarith))
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs)

omit [NeZero N] in
theorem inv_ne_one (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)

omit [NeZero N] in
theorem isPrimitive_inv (hprim : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
  exact hprim

/-- The root number of a primitive character is nonzero: the functional equation applied twice
returns `Λ(2, χ⁻¹) ≠ 0`. -/
theorem rootNumber_ne_zero (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h0
  have h1 := hprim.completedLFunction_one_sub (2 : ℂ)
  have h2 := (isPrimitive_inv hprim).completedLFunction_one_sub (-1 : ℂ)
  rw [show (1 : ℂ) - 2 = -1 by ring, h0, mul_zero, zero_mul] at h1
  rw [inv_inv, show (1 : ℂ) - (-1) = 2 by ring, h1, mul_zero] at h2
  exact completedLFunction_ne_zero_of_one_le_re (inv_ne_one hχ) (by norm_num) h2

/-- `Λ(s, χ) ≠ 0` on `Re s ≤ 0`, by the functional equation. -/
theorem completedLFunction_ne_zero_of_re_nonpos (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) : DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have h := hprim.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero hχ hprim))
    (completedLFunction_ne_zero_of_one_le_re (inv_ne_one hχ) (by rw [sub_re, one_re]; linarith))
  exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast NeZero.ne N))

theorem shiftedL_zero_ne_zero (hχ : χ ≠ 1) : shiftedL χ 0 ≠ 0 := by
  rw [shiftedL, zero_add]
  exact completedLFunction_ne_zero_of_one_le_re hχ (by norm_num)

/-! ### The zeros -/

theorem completedLFunction_point (hχ : χ ≠ 1) (q : LZero χ) :
    DirichletCharacter.completedLFunction χ q.point = 0 :=
  eq_zero_at_zeroCopyPoint (analyticOnNhd_shiftedL hχ) q

/-- **The zeros lie in the open critical strip.** -/
theorem zero_re_mem (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) :
    0 < q.point.re ∧ q.point.re < 1 := by
  have h := completedLFunction_point hχ q
  constructor
  · by_contra hle
    exact completedLFunction_ne_zero_of_re_nonpos hχ hprim (not_lt.mp hle) h
  · by_contra hle
    exact completedLFunction_ne_zero_of_one_le_re hχ (not_lt.mp hle) h

theorem point_ne_zero (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) : q.point ≠ 0 := by
  intro h
  have := (zero_re_mem hχ hprim q).1
  rw [h, zero_re] at this
  exact lt_irrefl 0 this

theorem point_ne_one (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) : q.point ≠ 1 := by
  intro h
  have := (zero_re_mem hχ hprim q).2
  rw [h, one_re] at this
  exact lt_irrefl 1 this

/-! ### The Hadamard product -/

theorem orderOneBound (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖shiftedL χ z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨C, hC, hbound⟩ := RHTower.completedLFunction_orderOneEnvelope hχ
  refine ⟨6 * C, by positivity, fun z => (hbound (z + 2)).trans (Real.exp_le_exp.mpr ?_)⟩
  have hz := norm_nonneg z
  have hz2 : ‖z + 2‖ ≤ ‖z‖ + 2 := (norm_add_le _ _).trans (by norm_num)
  have hlog2 : Real.log 2 ≤ Real.log (2 + ‖z‖) := Real.log_le_log (by norm_num) (by linarith)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log (2 + ‖z + 2‖) ≤ 2 * Real.log (2 + ‖z‖) := by
    calc Real.log (2 + ‖z + 2‖) ≤ Real.log (2 * (2 + ‖z‖)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log (2 + ‖z‖) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 2 * Real.log (2 + ‖z‖) := by linarith
  have hlog0 : 0 ≤ Real.log (2 + ‖z + 2‖) := Real.log_nonneg (by linarith [norm_nonneg (z + 2)])
  unfold HTGeometry.orderOneWeight
  calc C * (1 + ‖z + 2‖) * Real.log (2 + ‖z + 2‖)
      ≤ C * (3 * (1 + ‖z‖)) * (2 * Real.log (2 + ‖z‖)) := by
        gcongr
        linarith
    _ = 6 * C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by ring

theorem summable_inv_sq (hχ : χ ≠ 1) :
    Summable (fun q : LZero χ => 1 / ‖zeroCopyPoint (shiftedL χ) q‖ ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ := orderOneBound hχ
  exact summable_inv_sq_zeroCopyPoint hC (analyticOnNhd_shiftedL hχ) (shiftedL_zero_ne_zero hχ)
    hbound

/-- **Convergence exponent one.** `Σ_ρ |ρ − 2|^{−α} < ∞` for every `α > 1`. -/
theorem summable_norm_rpow_neg (hχ : χ ≠ 1) {α : ℝ} (hα : 1 < α) :
    Summable (fun q : LZero χ => ‖zeroCopyPoint (shiftedL χ) q‖ ^ (-α)) := by
  obtain ⟨C, hC, hbound⟩ := orderOneBound hχ
  exact summable_rpow_neg_of_orderOneDensity
    (locallyFinite_zeroCopyPoint (analyticOnNhd_shiftedL hχ))
    (orderOneDensityIdx_zeroCopyPoint hC (analyticOnNhd_shiftedL hχ)
      (shiftedL_zero_ne_zero hχ) hbound) hα

theorem zeroCopyPoint_ne_zero' (hχ : χ ≠ 1) (q : LZero χ) : zeroCopyPoint (shiftedL χ) q ≠ 0 :=
  zeroCopyPoint_ne_zero (analyticOnNhd_shiftedL hχ) (shiftedL_zero_ne_zero hχ) q

/-- **The Hadamard partial fraction.** Wherever `Λ(s, χ) ≠ 0`,
`Λ'/Λ(s) = A + Σ_ρ ((s − ρ)⁻¹ + (ρ − 2)⁻¹)`. -/
theorem logDeriv_completedLFunction_eq (hχ : χ ≠ 1) :
    ∃ A : ℂ, ∀ s : ℂ, DirichletCharacter.completedLFunction χ s ≠ 0 →
      logDeriv (DirichletCharacter.completedLFunction χ) s =
        A + ∑' q : LZero χ, ((s - q.point)⁻¹ + (q.point - 2)⁻¹) := by
  obtain ⟨C, hC, hbound⟩ := orderOneBound hχ
  have han := analyticOnNhd_shiftedL hχ
  have hf0 := shiftedL_zero_ne_zero hχ
  have hford : ∀ z, analyticOrderAt (shiftedL χ) z ≠ ⊤ := fun z =>
    han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ z)
      (by rw [(han 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]; exact ENat.zero_ne_top)
  obtain ⟨a, b, hfac⟩ := exists_expAffine_mul_hadamardProduct hC han hf0 hford hbound
  have hsum := summable_inv_sq hχ
  have hane := zeroCopyPoint_ne_zero' hχ
  refine ⟨a, fun s hs => ?_⟩
  set z := s - 2
  have hz : shiftedL χ z ≠ 0 := by rw [shiftedL, sub_add_cancel]; exact hs
  have hzq : ∀ q : LZero χ, z ≠ zeroCopyPoint (shiftedL χ) q := by
    intro q hq
    apply hz
    rw [hq]
    exact eq_zero_at_zeroCopyPoint han q
  -- `Λ(s) = shiftedL (s − 2)`, a translate
  have hcomp : DirichletCharacter.completedLFunction χ = fun w => shiftedL χ (w - 2) := by
    funext w; rw [shiftedL, sub_add_cancel]
  have hP : hadamardProduct (shiftedL χ) z ≠ 0 := by
    intro h; apply hz; rw [hfac z, h, mul_zero]
  have hdiffP : DifferentiableAt ℂ (hadamardProduct (shiftedL χ)) z :=
    ((hadamardProduct_analytic han hf0 hsum) z (mem_univ z)).differentiableAt
  have hdiffE : DifferentiableAt ℂ (fun w => Complex.exp (a * w + b)) z := by fun_prop
  have hlogS : logDeriv (shiftedL χ) z = a + logDeriv (hadamardProduct (shiftedL χ)) z := by
    have hfeq : shiftedL χ = fun w => Complex.exp (a * w + b) * hadamardProduct (shiftedL χ) w :=
      funext hfac
    rw [hfeq, logDeriv_mul (f := fun w => Complex.exp (a * w + b)) z (Complex.exp_ne_zero _) hP
      hdiffE hdiffP]
    congr 1
    rw [logDeriv_apply]
    have hd : deriv (fun w => Complex.exp (a * w + b)) z = Complex.exp (a * z + b) * a := by
      have := ((hasDerivAt_id z).const_mul a |>.add_const b).cexp
      simpa using this.deriv
    rw [hd, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  have hlogP := RHTower.logDeriv_canonicalProductE1Indexed hane hsum hzq
  have hshift : logDeriv (DirichletCharacter.completedLFunction χ) s = logDeriv (shiftedL χ) z := by
    rw [hcomp, show (fun w => shiftedL χ (w - 2)) = (shiftedL χ) ∘ (fun w => w - 2) from rfl,
      logDeriv_comp (by
        have := (analyticOnNhd_shiftedL hχ) z (mem_univ z)
        simpa [z] using this.differentiableAt) (by fun_prop)]
    have hd : deriv (fun w : ℂ => w - 2) s = 1 := by
      simp
    rw [hd, mul_one]
  rw [hshift, hlogS, hadamardProduct, hlogP]
  congr 1
  refine tsum_congr fun q => ?_
  simp only [LZero.point, z]
  ring_nf

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
