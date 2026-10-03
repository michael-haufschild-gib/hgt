import GaloisForLFunctions.HTGeometry.PrimeHodgeCubicSylvesterLaw
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier

/-!
# One nilpotent lift makes the cubic law ordinary

On `Ĥ = ℓ²(Primes) ⊕ ℓ²(Primes)` put `L̂ = [[L, -I], [0, L]] = D - N` with `D = L ⊕ L` and the
nilpotent `N(x, y) = (y, 0)`, `N² = 0`.  Since `D` and `N` commute,
`exp(-rL̂) = e^{-rD} exp(rN) = [[e^{-rL}, r e^{-rL}], [0, e^{-rL}]]` (**(PCOB.17)**): this is a
semigroup whose prime coordinates solve `ẋ₁ = -λx₁ + x₂`, `ẋ₂ = -λx₂`, i.e. its generator is `-L̂`
on the prime basis.  With `b̂ = (0, 2b_d)`, `P exp(-rL̂) b̂ = 2r e^{-rL} b_d`.  The Gramian
`Ĝ = ∫₀^∞ |e^{-rL̂}b̂⟩⟨e^{-rL̂}b̂| dr` has blocks `8bb̄/(λ+λ')³, 4bb̄/(λ+λ')², 4bb̄/(λ+λ')²,
4bb̄/(λ+λ')`; its first corner is `A_d` (**(PCOB.18)**) and it solves the ordinary Lyapunov equation
`L̂Ĝ + ĜL̂* = |b̂⟩⟨b̂|` (**(PCOB.19)**).  Tensoring with `Φ` gives first corner `𝖳_d`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower GaloisForLFunctions

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

/-! ## The prime heat semigroup -/

theorem norm_primeHeatSymbol_le (r : ℝ≥0) (p : Nat.Primes) :
    ‖((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg r.2 (primeClock_pos p).le

/-- The prime heat semigroup `e^{-rL}`, `(e^{-rL}x)_p = p^{-r} x_p`. -/
def primeHeat (r : ℝ≥0) : ℓ²P →L[ℂ] ℓ²P :=
  lpDiagonalCLM (fun p => ((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ)) zero_le_one
    (norm_primeHeatSymbol_le r)

theorem primeHeat_apply (r : ℝ≥0) (x : ℓ²P) (p : Nat.Primes) :
    (primeHeat r x : Nat.Primes → ℂ) p = ((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ) * x p :=
  rfl

theorem primeHeat_zero : primeHeat 0 = 1 := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun p => ?_)
  rw [primeHeat_apply]
  simp

theorem primeHeat_add (r s : ℝ≥0) : primeHeat (r + s) = primeHeat r ∘L primeHeat s := by
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun p => ?_)
  rw [ContinuousLinearMap.comp_apply, primeHeat_apply, primeHeat_apply, primeHeat_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, NNReal.coe_add]
  congr 3
  ring

/-! ## The Jordan block -/

local notation "Ĥ" => ℓ²P × ℓ²P

/-- The nilpotent creation step `N(x, y) = (y, 0)`. -/
def jordanNilpotent : Ĥ →L[ℂ] Ĥ := (ContinuousLinearMap.snd ℂ ℓ²P ℓ²P).prod 0

theorem jordanNilpotent_apply (z : Ĥ) : jordanNilpotent z = (z.2, 0) := rfl

theorem jordanNilpotent_sq : jordanNilpotent * jordanNilpotent = 0 := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [mul_apply_eq_comp, jordanNilpotent_apply, jordanNilpotent_apply]
  rfl

/-- **The nilpotent exponential.**  `exp(rN) = I + rN`. -/
theorem exp_smul_jordanNilpotent (r : ℝ) :
    NormedSpace.exp ((r : ℂ) • jordanNilpotent) = 1 + (r : ℂ) • jordanNilpotent := by
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) _]
  have hpow : ∀ n, 2 ≤ n → ((r : ℂ) • jordanNilpotent) ^ n = 0 := fun n hn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [smul_pow, pow_add jordanNilpotent, sq, jordanNilpotent_sq, zero_mul, smul_zero]
  rw [tsum_eq_sum (s := Finset.range 2) fun n hn => by
    rw [hpow n (by simp only [Finset.mem_range, not_lt] at hn; exact hn), smul_zero]]
  simp [Finset.sum_range_succ]

/-- The diagonal heat `e^{-rD} = e^{-rL} ⊕ e^{-rL}`. -/
def jointHeat (r : ℝ≥0) : Ĥ →L[ℂ] Ĥ := (primeHeat r).prodMap (primeHeat r)

theorem jointHeat_apply (r : ℝ≥0) (z : Ĥ) : jointHeat r z = (primeHeat r z.1, primeHeat r z.2) := rfl

theorem jointHeat_comm_jordanNilpotent (r : ℝ≥0) :
    jointHeat r * jordanNilpotent = jordanNilpotent * jointHeat r := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, jordanNilpotent_apply, jointHeat_apply, jointHeat_apply,
    jordanNilpotent_apply, map_zero]

/-- **(PCOB.17)** `exp(-rL̂) = e^{-rD} exp(rN)`. -/
def jordanSemigroup (r : ℝ≥0) : Ĥ →L[ℂ] Ĥ :=
  jointHeat r * NormedSpace.exp ((r : ℂ) • jordanNilpotent)

/-- `exp(-rL̂) = [[e^{-rL}, r e^{-rL}], [0, e^{-rL}]]`. -/
theorem jordanSemigroup_apply (r : ℝ≥0) (z : Ĥ) :
    jordanSemigroup r z = (primeHeat r z.1 + (r : ℂ) • primeHeat r z.2, primeHeat r z.2) := by
  rw [jordanSemigroup, exp_smul_jordanNilpotent, mul_apply_eq_comp, add_apply, one_apply_eq_self,
    smul_apply, jordanNilpotent_apply, jointHeat_apply]
  refine Prod.ext ?_ ?_
  · show primeHeat r (z.1 + (r : ℂ) • z.2) = _
    rw [map_add, map_smul]
  · show primeHeat r (z.2 + (r : ℂ) • 0) = _
    rw [smul_zero, add_zero]

theorem jordanSemigroup_zero : jordanSemigroup 0 = 1 := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [jordanSemigroup_apply, primeHeat_zero]
  simp

/-- **Semigroup law.** -/
theorem jordanSemigroup_add (r s : ℝ≥0) :
    jordanSemigroup (r + s) = jordanSemigroup r * jordanSemigroup s := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [mul_apply_eq_comp, jordanSemigroup_apply, jordanSemigroup_apply, jordanSemigroup_apply,
    primeHeat_add]
  refine Prod.ext ?_ rfl
  simp only [ContinuousLinearMap.comp_apply, map_add, map_smul, NNReal.coe_add, Complex.ofReal_add,
    add_smul]
  abel

/-- `b̂ = (0, 2b_d)`. -/
def jordanSource {d : ℝ} (hd : 0 < d) : Ĥ := (0, (2 : ℂ) • primeCubicBirthLp hd)

/-- **(PCOB.17)** `P exp(-rL̂) b̂ = 2r e^{-rL} b_d`. -/
theorem fst_jordanSemigroup_jordanSource {d : ℝ} (hd : 0 < d) (r : ℝ≥0) :
    (jordanSemigroup r (jordanSource hd)).1 = (2 * r : ℂ) • primeHeat r (primeCubicBirthLp hd) := by
  rw [jordanSemigroup_apply, jordanSource]
  simp only [map_zero, zero_add, map_smul, smul_smul]
  ring_nf

/-- The prime coordinates of `e^{-rL̂} b̂`: `2r p^{-r} b_d(p)` and `2 p^{-r} b_d(p)`. -/
theorem jordanSemigroup_jordanSource_coord {d : ℝ} (hd : 0 < d) (r : ℝ≥0) (p : Nat.Primes) :
    ((jordanSemigroup r (jordanSource hd)).1 : Nat.Primes → ℂ) p =
        2 * r * ((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ) * primeHodgeCubicBirthVector d p ∧
      ((jordanSemigroup r (jordanSource hd)).2 : Nat.Primes → ℂ) p =
        2 * ((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ) * primeHodgeCubicBirthVector d p := by
  rw [jordanSemigroup_apply, jordanSource]
  simp only [map_zero, zero_add, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, primeHeat_apply,
    primeCubicBirthLp_apply]
  constructor <;> ring

/-! ## The generator on the prime basis -/

/-- On the prime basis `e^{-rL̂}(u e_p, v e_p) = (p^{-r}(u + rv) e_p, p^{-r} v e_p)`. -/
theorem jordanSemigroup_single (p : Nat.Primes) (u v : ℂ) (r : ℝ≥0) :
    jordanSemigroup r ((lp.single 2 p u : ℓ²P), (lp.single 2 p v : ℓ²P)) =
      ((lp.single 2 p (((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ) * (u + r * v)) : ℓ²P),
        (lp.single 2 p (((Real.exp (-((r : ℝ) * Real.log (p : ℝ))) : ℝ) : ℂ) * v) : ℓ²P)) := by
  rw [jordanSemigroup_apply]
  refine Prod.ext (lp.ext (funext fun q => ?_)) (lp.ext (funext fun q => ?_))
  · simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, primeHeat_apply,
      lp.single_apply, Pi.single_apply]
    split_ifs with hq
    · subst hq
      ring
    · ring
  · simp only [primeHeat_apply, lp.single_apply, Pi.single_apply]
    split_ifs with hq
    · subst hq
      rfl
    · ring

/-- **The generator is `-L̂`.**  The prime coordinates `x₁(r) = p^{-r}(u + rv)`, `x₂(r) = p^{-r}v`
solve `ẋ₁ = -λ_p x₁ + x₂`, `ẋ₂ = -λ_p x₂`. -/
theorem hasDerivAt_jordanCoordinates (p : Nat.Primes) (u v : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.exp (-(s * Real.log (p : ℝ))) : ℝ) : ℂ) * (u + s * v))
        (-(Real.log (p : ℝ) : ℂ) * (((Real.exp (-(r * Real.log (p : ℝ))) : ℝ) : ℂ) * (u + r * v)) +
          ((Real.exp (-(r * Real.log (p : ℝ))) : ℝ) : ℂ) * v) r ∧
      HasDerivAt (fun s : ℝ => ((Real.exp (-(s * Real.log (p : ℝ))) : ℝ) : ℂ) * v)
        (-(Real.log (p : ℝ) : ℂ) * (((Real.exp (-(r * Real.log (p : ℝ))) : ℝ) : ℂ) * v)) r := by
  have hreal : HasDerivAt (fun s : ℝ => Real.exp (-(s * Real.log (p : ℝ))))
      (Real.exp (-(r * Real.log (p : ℝ))) * -(Real.log (p : ℝ))) r := by
    have := ((hasDerivAt_id r).mul_const (Real.log (p : ℝ))).neg.exp
    simpa using this
  have hexp : HasDerivAt (fun s : ℝ => ((Real.exp (-(s * Real.log (p : ℝ))) : ℝ) : ℂ))
      (((Real.exp (-(r * Real.log (p : ℝ))) * -(Real.log (p : ℝ)) : ℝ) : ℂ)) r :=
    hreal.ofReal_comp
  have hlin : HasDerivAt (fun s : ℝ => u + (s : ℂ) * v) v r := by
    simpa using ((hasDerivAt_id r).ofReal_comp.mul_const v).const_add u
  refine ⟨(hexp.mul hlin).congr_deriv ?_, (hexp.mul_const v).congr_deriv ?_⟩ <;>
  · rw [Complex.ofReal_mul, Complex.ofReal_neg]
    ring

/-! ## The Gramian and the Lyapunov equation -/

/-- `∫₀^∞ e^{-ar} dr = 1/a`, `∫₀^∞ r e^{-ar} dr = 1/a²`, `∫₀^∞ r² e^{-ar} dr = 2/a³`. -/
theorem integral_exp_neg_moments {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), Real.exp (-(a * r)) = 1 / a ∧
      ∫ r in Ioi (0 : ℝ), r * Real.exp (-(a * r)) = 1 / a ^ 2 ∧
      ∫ r in Ioi (0 : ℝ), r ^ 2 * Real.exp (-(a * r)) = 2 / a ^ 3 := by
  have h1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1) ha
  have h2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) ha
  have h3 := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 3) ha
  have hG3 : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h2
  simp_rw [Real.rpow_one] at h2
  refine ⟨?_, ?_, ?_⟩
  · simpa [Real.Gamma_one] using h1
  · simpa [Real.Gamma_two, div_eq_mul_inv, Real.rpow_natCast] using h2
  · simpa [hG3, show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_natCast, div_eq_mul_inv, mul_comm] using h3

/-- Block kernels of the Gramian `Ĝ`. -/
def jordanGramKernel (d : ℝ) (i j : Fin 2) (p q : Nat.Primes) : ℂ :=
  if i = 0 ∧ j = 0 then
    8 * (primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)) /
      ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ 3
  else if i = 1 ∧ j = 1 then
    4 * (primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)) /
      ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ)
  else
    4 * (primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)) /
      ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ 2

/-- The time profile of the `i`-th coordinate of `e^{-rL̂}b̂`: `2r` or `2`. -/
def jordanTimeProfile (i : Fin 2) (r : ℝ) : ℝ := if i = 0 then 2 * r else 2

/-- **Gramian entries.**  `Ĝ_{ij}(p,q) = ∫₀^∞ (e^{-rL̂}b̂)_{i,p} conj (e^{-rL̂}b̂)_{j,q} dr`. -/
theorem jordanGramKernel_eq_integral (d : ℝ) (i j : Fin 2) (p q : Nat.Primes) :
    jordanGramKernel d i j p q =
      ∫ r in Ioi (0 : ℝ),
        (((jordanTimeProfile i r * Real.exp (-(r * Real.log (p : ℝ))) : ℝ) : ℂ) *
            primeHodgeCubicBirthVector d p) *
          star (((jordanTimeProfile j r * Real.exp (-(r * Real.log (q : ℝ))) : ℝ) : ℂ) *
            primeHodgeCubicBirthVector d q) := by
  set a := Real.log (p : ℝ) + Real.log (q : ℝ)
  have ha : 0 < a := add_pos (primeClock_pos p) (primeClock_pos q)
  obtain ⟨m0, m1, m2⟩ := integral_exp_neg_moments ha
  set bb := primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)
  have hpt : ∀ r : ℝ, (((jordanTimeProfile i r * Real.exp (-(r * Real.log (p : ℝ))) : ℝ) : ℂ) *
        primeHodgeCubicBirthVector d p) *
      star (((jordanTimeProfile j r * Real.exp (-(r * Real.log (q : ℝ))) : ℝ) : ℂ) *
        primeHodgeCubicBirthVector d q) =
      ((jordanTimeProfile i r * jordanTimeProfile j r * Real.exp (-(a * r)) : ℝ) : ℂ) * bb := fun r => by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    have he : Real.exp (-(r * Real.log (p : ℝ))) * Real.exp (-(r * Real.log (q : ℝ))) =
        Real.exp (-(a * r)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (((jordanTimeProfile i r * Real.exp (-(r * Real.log (p : ℝ))) : ℝ) : ℂ) *
            primeHodgeCubicBirthVector d p) *
          (((jordanTimeProfile j r * Real.exp (-(r * Real.log (q : ℝ))) : ℝ) : ℂ) *
            star (primeHodgeCubicBirthVector d q))
        = ((jordanTimeProfile i r * jordanTimeProfile j r *
            (Real.exp (-(r * Real.log (p : ℝ))) * Real.exp (-(r * Real.log (q : ℝ)))) : ℝ) : ℂ) *
            bb := by
          push_cast
          ring
      _ = _ := by rw [he]
  simp_rw [hpt]
  rw [integral_mul_const, integral_complex_ofReal]
  have hs : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have ha' : ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) = (a : ℂ) := rfl
  fin_cases i <;> fin_cases j <;>
    simp only [jordanTimeProfile, jordanGramKernel, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true,
      and_true, one_ne_zero, zero_ne_one, if_false, and_false, ha']
  · have : (fun r : ℝ => 2 * r * (2 * r) * Real.exp (-(a * r))) =
        fun r => 4 * (r ^ 2 * Real.exp (-(a * r))) := by
      funext r
      ring
    rw [this, integral_const_mul, m2]
    push_cast
    field_simp
    ring
  · have : (fun r : ℝ => 2 * r * 2 * Real.exp (-(a * r))) =
        fun r => 4 * (r * Real.exp (-(a * r))) := by
      funext r
      ring
    rw [this, integral_const_mul, m1]
    push_cast
    field_simp
    rfl
  · have : (fun r : ℝ => 2 * (2 * r) * Real.exp (-(a * r))) =
        fun r => 4 * (r * Real.exp (-(a * r))) := by
      funext r
      ring
    rw [this, integral_const_mul, m1]
    push_cast
    field_simp
    rfl
  · have : (fun r : ℝ => 2 * 2 * Real.exp (-(a * r))) = fun r => 4 * Real.exp (-(a * r)) := by
      funext r
      ring
    rw [this, integral_const_mul, m0]
    push_cast
    field_simp
    rfl

/-- **(PCOB.18)** The first corner of the Gramian is `A_d`. -/
theorem jordanGramKernel_zero_zero {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    jordanGramKernel d 0 0 p q = normalizedStokesPrimeKernel d (p, q) := by
  have h := primeHodgeCubicClock_normalizedStokesKernel hd p q
  have hs : ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.2 (add_pos (primeClock_pos p) (primeClock_pos q)).ne')
  rw [jordanGramKernel, if_pos ⟨rfl, rfl⟩, div_eq_iff hs, mul_comm (normalizedStokesPrimeKernel d (p, q)),
    h]
  ring

/-- The source covariance `b̂ b̂*`: zero except `(2b)(2b)*` in the lower corner. -/
def jordanSourceKernel (d : ℝ) (i j : Fin 2) (p q : Nat.Primes) : ℂ :=
  if i = 1 ∧ j = 1 then
    4 * (primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)) else 0

/-- **(PCOB.19) The ordinary Lyapunov equation.**  Entrywise on the prime basis,
`(L̂Ĝ + ĜL̂*)_{ij}(p,q) = (b̂b̂*)_{ij}(p,q)` with `L̂ = [[L, -I], [0, L]]`. -/
theorem jordanLyapunov (d : ℝ) (i j : Fin 2) (p q : Nat.Primes) :
    ((Real.log (p : ℝ) : ℝ) : ℂ) * jordanGramKernel d i j p q -
        (if i = 0 then jordanGramKernel d 1 j p q else 0) +
      (((Real.log (q : ℝ) : ℝ) : ℂ) * jordanGramKernel d i j p q -
        (if j = 0 then jordanGramKernel d i 1 p q else 0)) =
      jordanSourceKernel d i j p q := by
  set s : ℂ := ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) with hs_def
  have hs : s ≠ 0 :=
    Complex.ofReal_ne_zero.2 (add_pos (primeClock_pos p) (primeClock_pos q)).ne'
  have hsum : ((Real.log (p : ℝ) : ℝ) : ℂ) + ((Real.log (q : ℝ) : ℝ) : ℂ) = s := by
    rw [hs_def, Complex.ofReal_add]
  set bb := primeHodgeCubicBirthVector d p * star (primeHodgeCubicBirthVector d q)
  have key : ∀ c : ℂ, ((Real.log (p : ℝ) : ℝ) : ℂ) * c + ((Real.log (q : ℝ) : ℝ) : ℂ) * c = s * c :=
    fun c => by rw [← add_mul, hsum]
  fin_cases i <;> fin_cases j
  · simp only [jordanGramKernel, jordanSourceKernel, Fin.isValue, Fin.zero_eta, if_true,
      and_true, one_ne_zero, zero_ne_one, if_false, and_false, and_self, ← hs_def]
    rw [show ∀ x y z w : ℂ, x - y + (z - w) = (x + z) - (y + w) from fun _ _ _ _ => by ring, key]
    field_simp
    ring
  · simp only [jordanGramKernel, jordanSourceKernel, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true,
      and_true, one_ne_zero, zero_ne_one, if_false, and_false, and_self, ← hs_def, sub_zero]
    rw [show ∀ x y z : ℂ, x - y + z = (x + z) - y from fun _ _ _ => by ring, key]
    field_simp
    ring
  · simp only [jordanGramKernel, jordanSourceKernel, Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true,
      and_true, one_ne_zero, zero_ne_one, if_false, and_false, and_self, ← hs_def, sub_zero]
    rw [show ∀ x z w : ℂ, x + (z - w) = (x + z) - w from fun _ _ _ => by ring, key]
    field_simp
    ring
  · simp only [jordanGramKernel, jordanSourceKernel, Fin.isValue, Fin.mk_one, if_true,
      one_ne_zero, if_false, and_self, ← hs_def, sub_zero]
    rw [key]
    field_simp

/-- Tensoring with `Φ`: the first corner of the joint system is the prime–Hodge defect `𝖳_d`. -/
theorem primeHodgeHistoryDefectKernel_eq_jordanGram {d : ℝ} (hd : 0 < d)
    (a b : PrimeHodgeHistoryIndex) :
    primeHodgeHistoryDefectKernel d (a, b) =
      if a.1 = b.1 then (PrimeHodgeHistory.w a.1 : ℂ) * jordanGramKernel d 0 0 a.2 b.2 else 0 := by
  rw [primeHodgeHistoryDefectKernel]
  split_ifs
  · rw [jordanGramKernel_zero_zero hd]
  · rfl

end GaloisForLFunctions.HTGeometry
