import GaloisForLFunctions.LSeriesPolynomialWeightUniqueness
import GaloisForLFunctions.ZetaJetExtraction
import GaloisForLFunctions.Hypertranscendence

/-!
# The Riemann zeta function is hypertranscendental

`ζ` satisfies no algebraic differential equation over `ℂ[s]`.  The proof is the elementary
resonance argument in coefficient space.  Suppose `P(s, ζ, ζ', …, ζ⁽ⁿ⁾) ≡ 0` with `P ≠ 0`.
Shifting the value slot by one replaces `ζ` by `u = ζ − 1 = L(𝟙_{n≥2})`, whose jets are L-series
of the jet atoms `(log n)^j · 𝟙_{n≥2}`.  Expanding `P` monomialwise turns the relation into a
polynomially weighted family of L-series vanishing on the real ray; the uniqueness theorem kills
every Dirichlet coefficient, and the jet-monomial extraction engine — prime peeling against
unique factorization — then kills every coefficient of `P`.

This machine-checks the classical Hilbert–Ostrowski statement that `ζ` is hypertranscendental,
by a proof using only unique factorization, the infinitude of primes, and polynomial algebra on
the Dirichlet-series side.
-/

namespace GaloisForLFunctions

open Filter Topology LSeries ArithmeticFunction MvPolynomial

noncomputable section

/-! ## The jet atoms as iterated log-multiples of the tail of ζ -/

theorem coe_zetaJetA_succ (k : ℕ) :
    ⇑(zetaJetA (k + 1)) = LSeries.logMul (⇑(zetaJetA k)) := by
  funext m
  have hlog : Complex.log ((m : ℕ) : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg m)]
  simp only [zetaJetA_apply, LSeries.logMul, hlog]
  by_cases hm : 2 ≤ m
  · rw [if_pos hm, if_pos hm, pow_succ]
    ring
  · rw [if_neg hm, if_neg hm, mul_zero]

theorem logMul_iterate_zetaJetA_zero (j : ℕ) :
    LSeries.logMul^[j] (⇑(zetaJetA 0)) = ⇑(zetaJetA j) := by
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, ← coe_zetaJetA_succ]

theorem zetaJetA_zero_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑(zetaJetA 0)) s := by
  have hone : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  refine Summable.of_norm_bounded hone.norm ?_
  intro m
  have heq : term (⇑(zetaJetA 0)) s m = (if 2 ≤ m then (1 : ℂ) else 0) * term 1 s m := by
    rw [LSeries.term_def, LSeries.term_def]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [if_neg (by omega : m ≠ 0), if_neg (by omega : m ≠ 0)]
      simp only [zetaJetA_apply, Pi.one_apply]
      by_cases h2 : 2 ≤ m
      · rw [if_pos h2, if_pos h2, one_mul, pow_zero]
      · rw [if_neg h2, if_neg h2, zero_div, zero_mul]
  rw [heq, norm_mul]
  calc ‖if 2 ≤ m then (1 : ℂ) else 0‖ * ‖term 1 s m‖
      ≤ 1 * ‖term 1 s m‖ := by
        gcongr
        split <;> simp
    _ = ‖term 1 s m‖ := one_mul _

theorem abscissaOfAbsConv_zetaJetA_le (j : ℕ) :
    abscissaOfAbsConv (⇑(zetaJetA j)) ≤ 1 := by
  induction j with
  | zero =>
      apply abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      intro y hy
      exact zetaJetA_zero_LSeriesSummable (by simpa using hy)
  | succ k ih =>
      rw [coe_zetaJetA_succ, LSeries.abscissaOfAbsConv_logMul]
      exact ih

theorem zetaJetA_LSeriesSummable (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑(zetaJetA j)) s := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  calc abscissaOfAbsConv (⇑(zetaJetA j)) ≤ 1 := abscissaOfAbsConv_zetaJetA_le j
    _ < (s.re : EReal) := by exact_mod_cast hs

/-! ## Jets of ζ on the half-plane of absolute convergence -/

theorem riemannZeta_eventuallyEq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta =ᶠ[𝓝 s] fun z => 1 + LSeries (⇑(zetaJetA 0)) z := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with z hz
  rw [← LSeries_one_eq_riemannZeta hz]
  have hsplit : (1 : ℕ → ℂ) = (fun m => if m ≤ 1 then 1 else 0) + ⇑(zetaJetA 0) := by
    funext m
    simp only [Pi.one_apply, Pi.add_apply, zetaJetA_apply, pow_zero]
    by_cases hm : m ≤ 1
    · rw [if_pos hm, if_neg (by omega), add_zero]
    · rw [if_neg hm, if_pos (by omega), zero_add]
  have hindsum : LSeriesSummable (fun m : ℕ => if m ≤ 1 then (1 : ℂ) else 0) z := by
    apply summable_of_ne_finset_zero (s := {1})
    intro m hm
    rw [Finset.mem_singleton] at hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_def, if_neg (by omega : m ≠ 0), if_neg (by omega : ¬ m ≤ 1), zero_div]
  have hind : LSeries (fun m : ℕ => if m ≤ 1 then (1 : ℂ) else 0) z = 1 := by
    rw [LSeries, tsum_eq_single 1 ?_]
    · rw [LSeries.term_def, if_neg one_ne_zero, if_pos le_rfl]
      simp
    · intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · exact LSeries.term_zero _ _
      · rw [LSeries.term_def, if_neg (by omega : m ≠ 0), if_neg (by omega : ¬ m ≤ 1), zero_div]
  rw [hsplit, LSeries_add hindsum (zetaJetA_zero_LSeriesSummable hz), hind]

theorem iteratedDeriv_riemannZeta_eq (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j riemannZeta s =
      (if j = 0 then 1 else 0) + (-1) ^ j * LSeries (⇑(zetaJetA j)) s := by
  rw [(riemannZeta_eventuallyEq hs).iteratedDeriv_eq j]
  have habs : abscissaOfAbsConv (⇑(zetaJetA 0)) < (s.re : EReal) :=
    lt_of_le_of_lt (abscissaOfAbsConv_zetaJetA_le 0) (by exact_mod_cast hs)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [iteratedDeriv_zero]
  · rw [iteratedDeriv_const_add hj, LSeries_iteratedDeriv j habs,
      logMul_iterate_zetaJetA_zero, if_neg (by omega), zero_add]

/-! ## L-series of jet-monomial products -/

theorem lseries_arith_one {s : ℂ} :
    LSeriesSummable (⇑(1 : ArithmeticFunction ℂ)) s ∧
      LSeries (⇑(1 : ArithmeticFunction ℂ)) s = 1 := by
  have hterm : ∀ m : ℕ, m ≠ 1 → term (⇑(1 : ArithmeticFunction ℂ)) s m = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_def, if_neg (by omega : m ≠ 0), ArithmeticFunction.one_apply,
        if_neg hm, zero_div]
  have hsum : LSeriesSummable (⇑(1 : ArithmeticFunction ℂ)) s := by
    apply summable_of_ne_finset_zero (s := {1})
    intro m hm
    rw [Finset.mem_singleton] at hm
    exact hterm m hm
  refine ⟨hsum, ?_⟩
  rw [LSeries, tsum_eq_single 1 hterm]
  rw [LSeries.term_def, if_neg one_ne_zero, ArithmeticFunction.one_apply, if_pos rfl]
  simp

theorem lseries_arith_mul {f g : ArithmeticFunction ℂ} {s : ℂ}
    (hf : LSeriesSummable (⇑f) s) (hg : LSeriesSummable (⇑g) s) :
    LSeriesSummable (⇑(f * g)) s ∧
      LSeries (⇑(f * g)) s = LSeries (⇑f) s * LSeries (⇑g) s := by
  constructor
  · rw [← ArithmeticFunction.coe_mul]
    exact hf.convolution hg
  · rw [← ArithmeticFunction.coe_mul]
    exact LSeries_convolution' hf hg

theorem lseries_jetProd (M : Multiset ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑(jetProd M)) s := by
  induction M using Multiset.induction_on with
  | empty =>
      rw [jetProd_zero]
      exact lseries_arith_one.1
  | cons j M ih =>
      rw [jetProd_cons]
      exact (lseries_arith_mul (zetaJetA_LSeriesSummable j hs) ih).1

theorem lseries_jetProd_eq (M : Multiset ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (⇑(jetProd M)) s = (M.map (fun j => LSeries (⇑(zetaJetA j)) s)).prod := by
  induction M using Multiset.induction_on with
  | empty =>
      rw [jetProd_zero]
      simpa using lseries_arith_one.2
  | cons j M ih =>
      rw [jetProd_cons,
        (lseries_arith_mul (zetaJetA_LSeriesSummable j hs) (lseries_jetProd M hs)).2,
        ih, Multiset.map_cons, Multiset.prod_cons]

/-! ## Jet multisets of monomial exponents -/

/-- The multiset of jet orders of a monomial exponent, with multiplicities. -/
def jetM (n : ℕ) (d : Fin (n + 2) →₀ ℕ) : Multiset ℕ :=
  (Finset.univ.val : Multiset (Fin (n + 1))).bind fun i => Multiset.replicate (d i.succ) (i : ℕ)

theorem jetM_entries {n : ℕ} (d : Fin (n + 2) →₀ ℕ) : ∀ j ∈ jetM n d, j ≤ n := by
  intro j hj
  rw [jetM, Multiset.mem_bind] at hj
  obtain ⟨i, -, hi⟩ := hj
  rw [Multiset.eq_of_mem_replicate hi]
  exact Nat.lt_succ_iff.mp i.isLt

theorem jetM_count {n : ℕ} (d : Fin (n + 2) →₀ ℕ) (i : Fin (n + 1)) :
    Multiset.count (i : ℕ) (jetM n d) = d i.succ := by
  classical
  rw [jetM, Multiset.count_bind]
  have hmap : Multiset.map
      (fun b : Fin (n + 1) => Multiset.count (i : ℕ) (Multiset.replicate (d b.succ) (b : ℕ)))
      (Finset.univ.val : Multiset (Fin (n + 1))) =
      Multiset.map (fun b : Fin (n + 1) => if b = i then d b.succ else 0)
        (Finset.univ.val : Multiset (Fin (n + 1))) := by
    apply Multiset.map_congr rfl
    intro b _
    rw [Multiset.count_replicate]
    by_cases hb : b = i
    · rw [if_pos (by exact_mod_cast congrArg (Fin.val) hb), if_pos hb]
    · rw [if_neg (fun h => hb (Fin.val_injective h)), if_neg hb]
  rw [hmap]
  show (∑ b : Fin (n + 1), if b = i then d b.succ else 0) = d i.succ
  rw [Finset.sum_ite_eq' Finset.univ i (fun b => d b.succ), if_pos (Finset.mem_univ i)]

theorem jetM_inj {n : ℕ} {d₁ d₂ : Fin (n + 2) →₀ ℕ} (h0 : d₁ 0 = d₂ 0)
    (hM : jetM n d₁ = jetM n d₂) : d₁ = d₂ := by
  ext i
  induction i using Fin.cases with
  | zero => exact h0
  | succ k =>
      have := congrArg (Multiset.count (k : ℕ)) hM
      rwa [jetM_count d₁ k, jetM_count d₂ k] at this

theorem lseries_jetM_eq {n : ℕ} (d : Fin (n + 2) →₀ ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (⇑(jetProd (jetM n d))) s =
      ∏ j : Fin (n + 1), (LSeries (⇑(zetaJetA (j : ℕ))) s) ^ (d j.succ) := by
  rw [lseries_jetProd_eq _ hs, jetM, Multiset.map_bind]
  simp only [Multiset.map_replicate]
  rw [Multiset.prod_bind]
  simp only [Multiset.prod_replicate]
  rw [← Finset.prod_eq_multiset_prod]

/-! ## Finite linear combinations of L-series -/

theorem term_const_mul (c : ℂ) (f : ℕ → ℂ) (s : ℂ) (m : ℕ) :
    term (fun k => c * f k) s m = c * term f s m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [LSeries.term_zero]
  · rw [LSeries.term_def, LSeries.term_def, if_neg (by omega : m ≠ 0),
      if_neg (by omega : m ≠ 0), mul_div_assoc]

theorem LSeriesSummable.const_mul {f : ℕ → ℂ} {s : ℂ} (c : ℂ)
    (hf : LSeriesSummable f s) : LSeriesSummable (fun k => c * f k) s := by
  have := hf.mul_left c
  apply this.congr
  intro m
  rw [term_const_mul]

theorem LSeries_const_mul {f : ℕ → ℂ} {s : ℂ} (c : ℂ) :
    LSeries (fun k => c * f k) s = c * LSeries f s := by
  rw [LSeries, LSeries, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [term_const_mul]

theorem LSeriesSummable_finsetSum {ι : Type*} (t : Finset ι) (F : ι → ℕ → ℂ) (s : ℂ)
    (h : ∀ i ∈ t, LSeriesSummable (F i) s) :
    LSeriesSummable (fun k => ∑ i ∈ t, F i k) s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact LSeriesSummable_zero
  | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LSeries_finsetSum {ι : Type*} (t : Finset ι) (F : ι → ℕ → ℂ) (s : ℂ)
    (h : ∀ i ∈ t, LSeriesSummable (F i) s) :
    LSeries (fun k => ∑ i ∈ t, F i k) s = ∑ i ∈ t, LSeries (F i) s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact congrFun LSeries_zero s
  | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      rw [show (fun k => F a k + ∑ i ∈ t, F i k) =
        (F a) + (fun k => ∑ i ∈ t, F i k) from rfl]
      rw [LSeries_add (h a (Finset.mem_insert_self a t))
        (LSeriesSummable_finsetSum t F s fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-! ## The main theorem -/

/-- **The Riemann zeta function is hypertranscendental** (Hilbert; Stadigh, Ostrowski): `ζ`
satisfies no algebraic differential equation over `ℂ[s]`.  Machine-checked by the
coefficient-space resonance argument: unique factorization isolates the linear layer of a
hypothetical relation at the primes and peels each higher layer at products of primes, so the
relation forces every coefficient to vanish. -/
theorem hypertranscendental_riemannZeta : Hypertranscendental riemannZeta := by
  classical
  rintro ⟨n, P, hP0, hPzero⟩
  have hzero_ne_one : (0 : Fin (n + 2)) ≠ 1 := by
    simp
  -- shift the value slot by one
  have hback : aeval (fun i : Fin (n + 2) =>
        if i = 1 then X 1 - 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ))
      (aeval (fun i : Fin (n + 2) =>
        if i = 1 then X 1 + 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ)) P) = P := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hgen : (fun i : Fin (n + 2) =>
        aeval (fun i : Fin (n + 2) =>
            if i = 1 then X 1 - 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ))
          (if i = 1 then X 1 + 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ))) =
        (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
      funext i
      by_cases hi : i = 1
      · subst hi
        rw [if_pos rfl, map_add, map_one, aeval_X, if_pos rfl]
        ring
      · rw [if_neg hi, aeval_X, if_neg hi]
    rw [hgen, aeval_X_left_apply]
  set Q : MvPolynomial (Fin (n + 2)) ℂ :=
    aeval (fun i : Fin (n + 2) =>
      if i = 1 then X 1 + 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ)) P with hQdef
  have hQ0 : Q ≠ 0 := by
    intro h0
    apply hP0
    rw [← hback, h0, _root_.map_zero]
  -- the L-series jet vector annihilates Q on the half-plane
  set v : ℂ → Fin (n + 2) → ℂ := fun z => Fin.cons z
    (fun j : Fin (n + 1) => (-1) ^ (j : ℕ) * LSeries (⇑(zetaJetA (j : ℕ))) z) with hv
  have hQvanish : ∀ z : ℂ, 1 < z.re → eval (v z) Q = 0 := by
    intro z hz
    have hvec : (fun i : Fin (n + 2) =>
        aeval (v z) (if i = 1 then X 1 + 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ))) =
        Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) riemannZeta z) := by
      funext i
      induction i using Fin.cases with
      | zero =>
          rw [if_neg hzero_ne_one, aeval_X]
          simp only [hv, Fin.cons_zero]
      | succ k =>
          by_cases hk : k = 0
          · subst hk
            rw [Fin.succ_zero_eq_one, if_pos rfl, map_add, map_one, aeval_X]
            simp only [hv]
            rw [show (1 : Fin (n + 2)) = Fin.succ 0 from Fin.succ_zero_eq_one.symm,
              Fin.cons_succ, Fin.cons_succ]
            simp only [Fin.val_zero, pow_zero, one_mul]
            rw [iteratedDeriv_zero, (riemannZeta_eventuallyEq hz).eq_of_nhds]
            ring
          · have hne : Fin.succ k ≠ 1 := fun h =>
              hk (Fin.succ_injective _ (h.trans Fin.succ_zero_eq_one.symm))
            rw [if_neg hne, aeval_X]
            simp only [hv, Fin.cons_succ]
            rw [iteratedDeriv_riemannZeta_eq (k : ℕ) hz,
              if_neg (fun h => hk (Fin.val_eq_zero_iff.mp h)), zero_add]
    rw [hQdef, ← MvPolynomial.aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have : (fun i : Fin (n + 2) => (aeval (v z))
        ((fun i : Fin (n + 2) =>
          if i = 1 then X 1 + 1 else (X i : MvPolynomial (Fin (n + 2)) ℂ)) i)) =
        Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) riemannZeta z) := hvec
    rw [this, MvPolynomial.aeval_eq_eval]
    exact hPzero z
  -- expand Q on the jet vector into a polynomially weighted L-series family
  set A : ℕ := Q.totalDegree with hA
  set sgn : (Fin (n + 2) →₀ ℕ) → ℂ :=
    fun d => (-1) ^ (∑ i : Fin (n + 1), (i : ℕ) * d i.succ) with hsgn
  set g : ℕ → ℕ → ℂ := fun a k =>
    ∑ d ∈ Q.support.filter (fun d => d 0 = a),
      Q.coeff d * sgn d * (jetProd (jetM n d)) k with hg
  have hsgn_ne : ∀ d, sgn d ≠ 0 := by
    intro d
    simp only [hsgn]
    exact pow_ne_zero _ (by norm_num)
  have hdeg : ∀ d ∈ Q.support, d 0 ≤ A := by
    intro d hd
    have h1 : d 0 ≤ d.sum fun _ e => e := by
      rcases Nat.eq_zero_or_pos (d 0) with h | h
      · omega
      · have hmem : (0 : Fin (n + 2)) ∈ d.support := Finsupp.mem_support_iff.mpr (by omega)
        exact Finset.single_le_sum (f := fun i => d i) (fun i _ => Nat.zero_le _) hmem
    have h2 := MvPolynomial.le_totalDegree hd
    omega
  have hgsum : ∀ a, a ≤ A → LSeriesSummable (g a) ((2 : ℝ) : ℂ) := by
    intro a _
    have h2 : (1 : ℝ) < (((2 : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]
      norm_num
    apply LSeriesSummable_finsetSum
    intro d _
    exact LSeriesSummable.const_mul _ (lseries_jetProd (jetM n d) h2)
  have hmono : ∀ (x : ℝ), 2 ≤ x → ∀ d ∈ Q.support,
      (∏ i, v (x : ℂ) i ^ d i) =
        (x : ℂ) ^ (d 0) * (sgn d * LSeries (⇑(jetProd (jetM n d))) ((x : ℝ) : ℂ)) := by
    intro x hx d _
    have hxre : (1 : ℝ) < (((x : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]
      linarith
    rw [Fin.prod_univ_succ]
    have h0 : v ((x : ℝ) : ℂ) 0 = ((x : ℝ) : ℂ) := by
      simp only [hv, Fin.cons_zero]
    rw [h0]
    congr 1
    calc ∏ j : Fin (n + 1), v ((x : ℝ) : ℂ) j.succ ^ d j.succ
        = ∏ j : Fin (n + 1),
            (((-1 : ℂ) ^ (j : ℕ)) ^ d j.succ *
              (LSeries (⇑(zetaJetA (j : ℕ))) ((x : ℝ) : ℂ)) ^ d j.succ) := by
          apply Finset.prod_congr rfl
          intro j _
          simp only [hv, Fin.cons_succ]
          rw [mul_pow]
      _ = sgn d * LSeries (⇑(jetProd (jetM n d))) ((x : ℝ) : ℂ) := by
          rw [Finset.prod_mul_distrib, lseries_jetM_eq d hxre]
          simp only [hsgn]
          congr 1
          rw [← Finset.prod_pow_eq_pow_sum]
          apply Finset.prod_congr rfl
          intro j _
          rw [← pow_mul]
  have hgzero : ∀ x : ℝ, (2 : ℝ) ≤ x →
      ∑ a ∈ Finset.range (A + 1), (x : ℂ) ^ a * LSeries (g a) ((x : ℝ) : ℂ) = 0 := by
    intro x hx
    have hxre : (1 : ℝ) < (((x : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]
      linarith
    have h0 := hQvanish ((x : ℝ) : ℂ) hxre
    rw [eval_eq'] at h0
    have hmaps : ∀ d ∈ Q.support, d 0 ∈ Finset.range (A + 1) := by
      intro d hd
      rw [Finset.mem_range]
      have := hdeg d hd
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun d => coeff d Q * ∏ i, v ((x : ℝ) : ℂ) i ^ d i)] at h0
    rw [← h0]
    apply Finset.sum_congr rfl
    intro a _
    calc (x : ℂ) ^ a * LSeries (g a) ((x : ℝ) : ℂ)
        = (x : ℂ) ^ a * ∑ d ∈ Q.support.filter (fun d => d 0 = a),
            (Q.coeff d * sgn d) * LSeries (⇑(jetProd (jetM n d))) ((x : ℝ) : ℂ) := by
          congr 1
          rw [hg]
          simp only []
          rw [LSeries_finsetSum _ _ _
            (fun d _ => LSeriesSummable.const_mul _ (lseries_jetProd (jetM n d) hxre))]
          exact Finset.sum_congr rfl fun d _ => LSeries_const_mul _
      _ = ∑ d ∈ Q.support.filter (fun d => d 0 = a),
            coeff d Q * ∏ i, v ((x : ℝ) : ℂ) i ^ d i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [hmono x hx d hd.1, ← hd.2]
          ring
  have hcoeff := lseries_polyWeightFamily_coeff_eq_zero g hgsum hgzero
  have hQcoeff : ∀ d ∈ Q.support, coeff d Q = 0 := by
    intro d hd
    have haA : d 0 ≤ A := hdeg d hd
    have hvanish : ∀ k : ℕ, k ≠ 0 →
        ∑ M ∈ (Q.support.filter (fun d' => d' 0 = d 0)).image (jetM n),
          (∑ d' ∈ (Q.support.filter (fun d' => d' 0 = d 0)).filter
              (fun d' => jetM n d' = M), Q.coeff d' * sgn d') * jetProd M k = 0 := by
      intro k hk
      rw [Finset.sum_image'
        (fun d' => (Q.coeff d' * sgn d') * jetProd (jetM n d') k) ?_]
      · have hgv := hcoeff k (by omega) (d 0) haA
        rw [hg] at hgv
        simp only [] at hgv
        rw [← hgv]
      · intro d' hd'
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d'' hd''
        rw [Finset.mem_filter] at hd''
        simp only []
        rw [hd''.2]
    have hTa : ∀ M ∈ (Q.support.filter (fun d' => d' 0 = d 0)).image (jetM n),
        ∀ j ∈ M, j ≤ n := by
      intro M hM
      rw [Finset.mem_image] at hM
      obtain ⟨d', -, rfl⟩ := hM
      exact jetM_entries d'
    have hext := jetProd_family_coeff_eq_zero (N := n) _ _ hTa hvanish
    have hsingleton : (Q.support.filter (fun d' => d' 0 = d 0)).filter
        (fun d' => jetM n d' = jetM n d) = {d} := by
      ext d'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hsupp, h0⟩, hMeq⟩
        exact jetM_inj h0 hMeq
      · rintro rfl
        exact ⟨⟨hd, rfl⟩, rfl⟩
    have hMmem : jetM n d ∈ (Q.support.filter (fun d' => d' 0 = d 0)).image (jetM n) :=
      Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, rfl⟩, rfl⟩
    have hzero := hext (jetM n d) hMmem
    rw [hsingleton, Finset.sum_singleton] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (hsgn_ne d)
  exact hQ0 (MvPolynomial.eq_zero_iff.mpr fun d => by
    by_cases hd : d ∈ Q.support
    · exact hQcoeff d hd
    · exact MvPolynomial.notMem_support_iff.mp hd)

end

end GaloisForLFunctions
