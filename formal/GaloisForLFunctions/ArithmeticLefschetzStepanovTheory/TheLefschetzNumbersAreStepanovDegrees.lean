import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovCountOfTheClosedPoints
import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ
import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier

/-!
# The Lefschetz numbers are Stepanov degrees

Over `𝔽_q` the Lefschetz and Stepanov halves meet in one polynomial: the closed points of degree
dividing `n` are the zeros of `x^{qⁿ} − x`, whose degree `qⁿ` is the Lefschetz count of the fixed
points of `Fⁿ`. Over `Spec ℤ` the fixed points of the Frobenius graph `Γ_n` are the primes `p` with
`pᵏ = n`, each of index `log p` (`SurfaceOfSpecZ.pointCount_eq`:
`Γ_1·Γ_n = Λ(n) + 1 + 1/(n² − 1)`), and a fixed point `p` is the closed point `u_p = 1` of the
circle of `p`. The minimal integer auxiliary vanishing at the fixed points of all `Γ_n`, `n ≤ N`,
each counted once per degree, is

  `A_N = Π_{p ≤ N} (u_p − 1)^{⌊log_p N⌋}`   (`fixedPointAux`),

and on the orbit `A_N(s) = Π_{p ≤ N} (p^{-s} − 1)^{⌊log_p N⌋}` (`orbitFun_fixedPointAux`).

* **Lefschetz = Stepanov** (`log_length_fixedPointAux_eq_sum_lefschetz`). The degree of `A_N` is
  the sum of the prime Lefschetz numbers: `log N(A_N) = ψ(N) = Σ_{2≤n≤N} (Γ_1·Γ_n − 1 − 1/(n² − 1))`;
  its length is `lcm(1, …, N)` (`length_fixedPointAux`). Every nonzero integer auxiliary vanishing at
  the same fixed points to the same orders is at least as long (`lcmUpto_le_length_of_dvd`).
* **The arithmetic Stepanov bound in its exact form**
  (`riemannHypothesis_iff_log_length_fixedPointAux_le`). RH holds iff
  `log N(A_N) ≤ N + C √N (log N)²` for all large `N`: an upper bound on the degree of the
  fixed-point auxiliary, the main term `N` playing the role of `qⁿ`. The same holds for the
  squarefree auxiliary `Π_{p ≤ N} (u_p − 1)` of length `N#` (`riemannHypothesis_iff_log_length_primeAux_le`).

Length is multiplicative on circle factors (`length_circleProduct`), so every closed-point
auxiliary `Π_p (u_p − 1)^{κ(p)}` has exactly the length `Π_p p^{κ(p)}` of its top monomial and is the
shortest auxiliary with its vanishing (`prod_pow_le_length_of_dvd`).
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-! ### Length is multiplicative on circle factors -/

theorem length_one : length (1 : MvPolynomial P ℤ) = 1 := by
  rw [length, MvPolynomial.support_one, sup_singleton]
  simp [weight]

theorem weight_le_of_mem_support_circlePoly {h : Polynomial ℤ} {p : P} {α : P →₀ ℕ}
    (hα : α ∈ (circlePoly h p).support) : weight α ≤ ((p : Nat.Primes) : ℕ) ^ h.natDegree := by
  classical
  rw [circlePoly_eq_sum] at hα
  obtain ⟨k, hk, hαk⟩ := mem_biUnion.mp (MvPolynomial.support_sum hα)
  have hαs : α = Finsupp.single p k := by
    have := MvPolynomial.support_monomial_subset hαk
    simpa using this
  rw [hαs, weight_single]
  exact Nat.pow_le_pow_right (p : Nat.Primes).2.pos (Nat.lt_succ_iff.mp (mem_range.mp hk))

/-- `N(h(u_p) G) ≤ p^{deg h} N(G)`. -/
theorem length_circlePoly_mul_le (h : Polynomial ℤ) (p : P) (G : MvPolynomial P ℤ) :
    length (circlePoly h p * G) ≤ ((p : Nat.Primes) : ℕ) ^ h.natDegree * length G := by
  classical
  refine Finset.sup_le fun α hα => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hα)
  rw [weight_add]
  exact Nat.mul_le_mul (weight_le_of_mem_support_circlePoly ha) (le_sup (f := weight) hb)

/-- **Length is multiplicative on circle factors.** -/
theorem length_circleProduct (L : List (P × Polynomial ℤ)) (hL : ∀ x ∈ L, x.2 ≠ 0) :
    length (circleProduct L) = (L.map fun x => ((x.1 : Nat.Primes) : ℕ) ^ x.2.natDegree).prod := by
  apply le_antisymm
  · induction L with
    | nil => simp [circleProduct, length_one]
    | cons x L ih =>
      have hrw : circleProduct (x :: L) = circlePoly x.2 x.1 * circleProduct L := by
        simp [circleProduct]
      rw [hrw, List.map_cons, List.prod_cons]
      exact (length_circlePoly_mul_le _ _ _).trans
        (Nat.mul_le_mul_left _ (ih fun y hy => hL y (List.mem_cons_of_mem _ hy)))
  · have h := prod_pow_mul_length_le L hL (G := 1) one_ne_zero
    rwa [length_one, mul_one, mul_one] at h

/-! ### Closed-point auxiliaries on any prime torus -/

/-- The auxiliary `Π_{p ∈ P} (u_p − 1)^{κ(p)}`: vanishing to order `κ(p)` along the closed point
`u_p = 1` of every circle. -/
def closedPointAux (κ : P → ℕ) : MvPolynomial P ℤ :=
  circleProduct ((univ : Finset P).toList.map fun p =>
    (p, (Polynomial.X - Polynomial.C 1 : Polynomial ℤ) ^ κ p))

theorem closedPointAux_factor_ne_zero (κ : P → ℕ) :
    ∀ x ∈ (univ : Finset P).toList.map (fun p =>
      (p, (Polynomial.X - Polynomial.C 1 : Polynomial ℤ) ^ κ p)), x.2 ≠ 0 := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)

theorem degree_map_closedPointAux (κ : P → ℕ) :
    (((univ : Finset P).toList.map (fun p =>
      (p, (Polynomial.X - Polynomial.C 1 : Polynomial ℤ) ^ κ p))).map
        fun x => ((x.1 : Nat.Primes) : ℕ) ^ x.2.natDegree).prod =
      ∏ p : P, ((p : Nat.Primes) : ℕ) ^ κ p := by
  rw [List.map_map]
  have hfun : ((fun x : P × Polynomial ℤ => ((x.1 : Nat.Primes) : ℕ) ^ x.2.natDegree) ∘
      fun p : P => (p, (Polynomial.X - Polynomial.C 1 : Polynomial ℤ) ^ κ p)) =
      fun p : P => ((p : Nat.Primes) : ℕ) ^ κ p := by
    funext p
    simp only [Function.comp_apply, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      mul_one]
  rw [hfun]
  exact Finset.prod_map_toList _ _

/-- `Π_p (u_p − 1)^{κ(p)}` has length `Π_p p^{κ(p)}`. -/
theorem length_closedPointAux (κ : P → ℕ) :
    length (closedPointAux κ) = ∏ p : P, ((p : Nat.Primes) : ℕ) ^ κ p := by
  rw [closedPointAux, length_circleProduct _ (closedPointAux_factor_ne_zero κ),
    degree_map_closedPointAux]

/-- **Minimality.** A nonzero integer auxiliary divisible by `Π_p (u_p − 1)^{κ(p)}` has length at
least `Π_p p^{κ(p)}`. -/
theorem prod_pow_le_length_of_dvd {κ : P → ℕ} {F : MvPolynomial P ℤ} (hF : F ≠ 0)
    (h : closedPointAux κ ∣ F) : ∏ p : P, ((p : Nat.Primes) : ℕ) ^ κ p ≤ length F := by
  obtain ⟨G, rfl⟩ := h
  have hG : G ≠ 0 := right_ne_zero_of_mul hF
  have hc := prod_pow_mul_length_le _ (closedPointAux_factor_ne_zero κ) hG
  rw [degree_map_closedPointAux] at hc
  exact (Nat.le_mul_of_pos_right _ (one_le_length hG)).trans hc

/-- On the orbit a circle product is the product of its one-variable factors at `p^{-s}`. -/
theorem orbitFun_circleProduct (L : List (P × Polynomial ℤ)) (s : ℂ) :
    orbitFun (circleProduct L) s = (L.map fun x =>
      Polynomial.aeval (Complex.exp (-s * Real.log ((x.1 : Nat.Primes) : ℕ))) x.2).prod := by
  induction L with
  | nil => rw [circleProduct, List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, orbitFun,
      map_one]
  | cons x L ih =>
    have hrw : circleProduct (x :: L) = circlePoly x.2 x.1 * circleProduct L := by
      simp [circleProduct]
    rw [hrw, orbitFun_circlePoly_mul, ih, List.map_cons, List.prod_cons]

/-- On the orbit, `Π_p (u_p − 1)^{κ(p)}` is `Π_p (p^{-s} − 1)^{κ(p)}`. -/
theorem orbitFun_closedPointAux (κ : P → ℕ) (s : ℂ) :
    orbitFun (closedPointAux κ) s =
      ∏ p : P, (Complex.exp (-s * Real.log ((p : Nat.Primes) : ℕ)) - 1) ^ κ p := by
  rw [closedPointAux, orbitFun_circleProduct, List.map_map]
  have hfun : ((fun x : P × Polynomial ℤ =>
      Polynomial.aeval (Complex.exp (-s * Real.log ((x.1 : Nat.Primes) : ℕ))) x.2) ∘
      fun p : P => (p, (Polynomial.X - Polynomial.C 1 : Polynomial ℤ) ^ κ p)) =
      fun p : P => (Complex.exp (-s * Real.log ((p : Nat.Primes) : ℕ)) - 1) ^ κ p := by
    funext p
    simp [map_pow, map_sub]
  rw [hfun]
  exact Finset.prod_map_toList _ _

/-! ### The fixed-point auxiliary of the Frobenius graphs of degree `≤ N` -/

/-- The primes `p ≤ N` as the variables of the prime torus. -/
abbrev primesUpTo (N : ℕ) : Finset Nat.Primes := GaloisForLFunctions.primesLE N

/-- **The fixed-point auxiliary** `A_N = Π_{p ≤ N} (u_p − 1)^{⌊log_p N⌋}`: the fixed point `p` of
`Γ_{pᵏ}` is counted once for every `k ≥ 1` with `pᵏ ≤ N`. -/
def fixedPointAux (N : ℕ) : MvPolynomial (primesUpTo N) ℤ :=
  closedPointAux fun p => Nat.log ((p : Nat.Primes) : ℕ) N

/-- The squarefree auxiliary `Π_{p ≤ N} (u_p − 1)`: each fixed point counted once. -/
def primeAux (N : ℕ) : MvPolynomial (primesUpTo N) ℤ := closedPointAux fun _ => 1

theorem prod_primesUpTo {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∏ p : primesUpTo N, f ((p : Nat.Primes) : ℕ) = ∏ x ∈ Nat.primesLE N, f x := by
  rw [Finset.prod_coe_sort (primesUpTo N) (fun p : Nat.Primes => f (p : ℕ)), primesUpTo,
    GaloisForLFunctions.primesLE, prod_map]
  simp only [Function.Embedding.coeFn_mk]
  exact prod_attach (Nat.primesBelow (N + 1)) f

/-- `A_N` has length `lcm(1, …, N)`. -/
theorem length_fixedPointAux (N : ℕ) : length (fixedPointAux N) = Nat.lcmUpto N := by
  rw [fixedPointAux, length_closedPointAux, Nat.lcmUpto_eq_prod_pow_log]
  exact prod_primesUpTo N (fun x => x ^ Nat.log x N)

/-- The squarefree auxiliary has length the primorial `N#`. -/
theorem length_primeAux (N : ℕ) : length (primeAux N) = primorial N := by
  rw [primeAux, length_closedPointAux, prod_primesUpTo N (fun x => x ^ 1)]
  simp only [pow_one]
  rfl

/-- **The degree of the fixed-point auxiliary is `ψ(N)`.** -/
theorem log_length_fixedPointAux (N : ℕ) :
    Real.log (length (fixedPointAux N)) = Chebyshev.psi N := by
  rw [length_fixedPointAux, Chebyshev.psi_eq_log_lcmUpto]

/-- The degree of the squarefree auxiliary is `θ(N)`. -/
theorem log_length_primeAux (N : ℕ) : Real.log (length (primeAux N)) = Chebyshev.theta N := by
  rw [length_primeAux, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]

/-- **Lefschetz = Stepanov.** The degree of the fixed-point auxiliary is the sum of the prime parts
of the Lefschetz numbers `Γ_1·Γ_n = Λ(n) + 1 + 1/(n² − 1)` of the Frobenius graphs of degree
`2 ≤ n ≤ N`. -/
theorem log_length_fixedPointAux_eq_sum_lefschetz (N : ℕ) :
    Real.log (length (fixedPointAux N)) =
      ∑ n ∈ Icc 2 N, (SurfaceOfSpecZ.pointCount n - 1 - 1 / ((n : ℝ) ^ 2 - 1)) := by
  rw [log_length_fixedPointAux, Chebyshev.psi, Nat.floor_natCast]
  have hsplit : Ioc 0 N = (Icc 2 N) ∪ ({1} ∩ Ioc 0 N) := by
    ext n; simp only [mem_Ioc, mem_union, mem_Icc, mem_inter, mem_singleton]; omega
  rw [hsplit, sum_union (by
    rw [disjoint_left]; intro n hn hn'; simp only [mem_inter, mem_singleton] at hn'
    rw [hn'.1] at hn; simp at hn)]
  have h1 : ∑ n ∈ ({1} ∩ Ioc 0 N), ArithmeticFunction.vonMangoldt n = 0 :=
    sum_eq_zero fun n hn => by
      simp only [mem_inter, mem_singleton] at hn
      rw [hn.1, ArithmeticFunction.vonMangoldt_apply_one]
  rw [h1, add_zero]
  refine sum_congr rfl fun n hn => ?_
  rw [SurfaceOfSpecZ.pointCount_eq (mem_Icc.mp hn).1]
  ring

/-- **The Stepanov count of the fixed points.** A nonzero integer auxiliary vanishing at the fixed
points of the Frobenius graphs of degree `≤ N` to the orders of `A_N` has length at least
`lcm(1, …, N)`. -/
theorem lcmUpto_le_length_of_dvd {N : ℕ} {F : MvPolynomial (primesUpTo N) ℤ} (hF : F ≠ 0)
    (h : fixedPointAux N ∣ F) : Nat.lcmUpto N ≤ length F := by
  have hc := prod_pow_le_length_of_dvd hF h
  rwa [prod_primesUpTo N (fun x => x ^ Nat.log x N), ← Nat.lcmUpto_eq_prod_pow_log] at hc

/-- **The fixed-point auxiliary on the orbit**: `A_N(s) = Π_{p ≤ N} (p^{-s} − 1)^{⌊log_p N⌋}`. -/
theorem orbitFun_fixedPointAux (N : ℕ) (s : ℂ) :
    orbitFun (fixedPointAux N) s = ∏ p : primesUpTo N,
      (Complex.exp (-s * Real.log ((p : Nat.Primes) : ℕ)) - 1) ^
        Nat.log ((p : Nat.Primes) : ℕ) N :=
  orbitFun_closedPointAux _ s

/-! ### The arithmetic Stepanov bound in its exact form -/

/-- **RH is an upper bound on the degree of the fixed-point auxiliary.** -/
theorem riemannHypothesis_iff_log_length_fixedPointAux_le :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Real.log (length (fixedPointAux N)) ≤ N + C * Real.sqrt N * Real.log N ^ 2 := by
  simp only [log_length_fixedPointAux]
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := (RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO.mp hRH).bound
    refine ⟨C, (tendsto_natCast_atTop_atTop.eventually hC).mono fun N hN => ?_⟩
    have hnn : 0 ≤ Real.sqrt N * Real.log N ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn] at hN
    have := (le_abs_self _).trans hN
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hC
    refine RHTower.riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq (le_max_right C 0) ?_
    refine eventually_atTop.mpr ⟨N₀ + 1, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    set N := ⌊x⌋₊
    have hN : N₀ ≤ N := Nat.le_floor (by linarith)
    have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
    have hN1 : (1 : ℝ) ≤ N := by
      have : 1 ≤ N := Nat.le_floor (by push_cast; linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)])
      exact_mod_cast this
    have hbound := hN₀ N hN
    rw [Chebyshev.psi_eq_psi_coe_floor]
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hlogx : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) hNx
    have hsq : Real.sqrt N ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
    have hm : C * Real.sqrt N * Real.log N ^ 2 ≤ max C 0 * Real.sqrt x * Real.log x ^ 2 := by
      calc C * Real.sqrt N * Real.log N ^ 2 ≤ max C 0 * Real.sqrt N * Real.log N ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.sqrt_nonneg _)) (sq_nonneg _)
        _ ≤ max C 0 * Real.sqrt x * Real.log x ^ 2 := by
            gcongr
    linarith

/-- **The squarefree form.** RH is an upper bound on the degree `θ(N)` of `Π_{p ≤ N} (u_p − 1)`. -/
theorem riemannHypothesis_iff_log_length_primeAux_le :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Real.log (length (primeAux N)) ≤ N + C * Real.sqrt N * Real.log N ^ 2 := by
  rw [riemannHypothesis_iff_log_length_fixedPointAux_le]
  simp only [log_length_fixedPointAux, log_length_primeAux]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, hC.mono fun N hN => (Chebyshev.theta_le_psi N).trans hN⟩
  · rintro ⟨C, hC⟩
    refine ⟨C + 2, (hC.and (eventually_ge_atTop 3)).mono fun N ⟨hN, hN3⟩ => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hdiff := Chebyshev.psi_sub_theta_le hN1
    have hlog1 : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
      linarith
    have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    have : 2 * Real.sqrt N * Real.log N ≤ 2 * Real.sqrt N * Real.log N ^ 2 := by
      have := mul_le_mul_of_nonneg_left (show Real.log N ≤ Real.log N ^ 2 by nlinarith)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs)
      linarith
    nlinarith

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
