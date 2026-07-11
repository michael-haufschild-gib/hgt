/-
# Full algebraic independence of the Hurwitz shift ladder (`s ∉ ℚ`)

Capstone of the deformation method.  For `Re s > 1` and `s` not rational, the ladder
`ζ(s,a), ζ(s+1,a), …, ζ(s+N,a)` satisfies no polynomial relation of ANY degree with
coefficients in `ℂ[a]` on the upper half-plane: `hurwitz_ladder_independence`.

The endgame after the monodromy grid invariance:

1. `mv_grid_zero` — a multivariate polynomial over `ℂ` vanishing on a product of infinite
   sets is zero (peel one variable with the finite-root theorem, recurse).
2. `monoScalar_pow_injective` — for `s ∉ ℚ` the powers `q^m` (`q = e^{-2πi s}`) are pairwise
   distinct, so the deformation grid is infinite in every coordinate.
3. `ladder_matrix_surjective` — the deformation directions at the `N+1` branch points
   `a = 0, -1, …, -N` form, at any fixed `a` in the upper half-plane, the matrix
   `(n+a)^{-s-k} = (n+a)^{-s}·u_n^k` (`u_n = (n+a)^{-1}`): a column-scaled Vandermonde in the
   pairwise distinct nodes `u_n`, hence invertible — the affine `c`-orbit of the ladder values
   fills all of `ℂ^{N+1}`.

Hence the evaluated polynomial vanishes identically at every `a` in the upper half-plane, and
each `ℂ[a]`-coefficient has infinitely many roots.  Via the escape identity
`∂_a^k ζ(s,a) = (-1)^k (s)_k ζ(s+k,a)` this is precisely the hypertranscendence of
`a ↦ ζ(s,a)` over `ℂ(a)` for every non-rational `s` with `Re s > 1`.
-/
import GaloisForLFunctions.Hurwitz.LadderDeformationBridge
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Vandermonde

open Complex HurwitzZetaShift HurwitzOrbit

namespace HurwitzLadder

/-- **Grid vanishing.**  A multivariate polynomial over `ℂ` vanishing on a product
`S_0 × ⋯ × S_r` of infinite sets is zero. -/
theorem mv_grid_zero : ∀ (r : ℕ) (p : MvPolynomial (Fin r) ℂ) (S : Fin r → Set ℂ),
    (∀ i, (S i).Infinite) →
    (∀ v : Fin r → ℂ, (∀ i, v i ∈ S i) → MvPolynomial.eval v p = 0) → p = 0 := by
  intro r
  induction r with
  | zero =>
    intro p S _ h
    obtain ⟨cst, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
    have h0 := h (fun i => i.elim0) (fun i => i.elim0)
    rw [MvPolynomial.eval_C] at h0
    rw [h0, map_zero]
  | succ r ih =>
    intro p S hS h
    have hpoly : ∀ v : Fin r → ℂ, (∀ i, v i ∈ S i.succ) →
        Polynomial.map (MvPolynomial.eval v) (MvPolynomial.finSuccEquiv ℂ r p) = 0 := by
      intro v hv
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hsub : S 0 ⊆
          {y | Polynomial.IsRoot
            (Polynomial.map (MvPolynomial.eval v) (MvPolynomial.finSuccEquiv ℂ r p)) y} := by
        intro y hy
        show Polynomial.eval y
          (Polynomial.map (MvPolynomial.eval v) (MvPolynomial.finSuccEquiv ℂ r p)) = 0
        rw [← MvPolynomial.eval_eq_eval_mv_eval']
        apply h
        intro i
        refine Fin.cases ?_ ?_ i
        · rwa [Fin.cons_zero]
        · intro j
          rw [Fin.cons_succ]
          exact hv j
      exact Set.Infinite.mono hsub (hS 0)
    have hcoeff : ∀ j : ℕ, (MvPolynomial.finSuccEquiv ℂ r p).coeff j = 0 := by
      intro j
      apply ih _ (fun i => S i.succ) (fun i => hS i.succ)
      intro v hv
      have hc := congrArg (fun q => Polynomial.coeff q j) (hpoly v hv)
      simpa [Polynomial.coeff_map] using hc
    have hfz : MvPolynomial.finSuccEquiv ℂ r p = 0 :=
      Polynomial.ext (fun j => by rw [hcoeff j, Polynomial.coeff_zero])
    have hsymm := congrArg (MvPolynomial.finSuccEquiv ℂ r).symm hfz
    rwa [AlgEquiv.symm_apply_apply, map_zero] at hsymm

/-- For non-rational `s`, the powers of the monodromy scalar `q = e^{-2πi s}` are pairwise
distinct: `q^d = 1` would force `s·d ∈ ℤ`. -/
theorem monoScalar_pow_injective {s : ℂ} (hsQ : ∀ r : ℚ, (r : ℂ) ≠ s) :
    Function.Injective (fun m : ℕ => monoScalar s ^ m) := by
  have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi, Complex.I_ne_zero]
  have hpow : ∀ d : ℕ, monoScalar s ^ d = 1 → d = 0 := by
    intro d hd
    by_contra hdne
    rw [monoScalar, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hd
    obtain ⟨k, hk⟩ := hd
    have hdC : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdne
    apply hsQ (-(k : ℚ) / (d : ℚ))
    push_cast
    rw [div_eq_iff hdC]
    have hlin : (2 * (Real.pi : ℂ) * Complex.I) * (-((k : ℂ)))
        = (2 * (Real.pi : ℂ) * Complex.I) * (s * (d : ℂ)) := by
      linear_combination hk
    exact mul_left_cancel₀ h2πI hlin
  have key : ∀ m₁ m₂ : ℕ, m₁ < m₂ → monoScalar s ^ m₁ = monoScalar s ^ m₂ → False := by
    intro m₁ m₂ hlt h
    have hq0 : monoScalar s ^ m₁ ≠ 0 := pow_ne_zero _ (monoScalar_ne_zero s)
    have hsplit : monoScalar s ^ m₂ = monoScalar s ^ m₁ * monoScalar s ^ (m₂ - m₁) := by
      rw [← pow_add]
      congr 1
      omega
    have hone : monoScalar s ^ m₁ * monoScalar s ^ (m₂ - m₁)
        = monoScalar s ^ m₁ * 1 := by
      rw [mul_one, ← hsplit, h]
    have hcancel := mul_left_cancel₀ hq0 hone
    have := hpow _ hcancel
    omega
  intro m₁ m₂ h
  simp only at h
  rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · exact absurd h (fun hh => key m₁ m₂ hlt hh)
  · exact heq
  · exact absurd h.symm (fun hh => key m₂ m₁ hgt hh)

/-- **Vandermonde surjectivity of the deformation directions.**  At any `a` in the upper
half-plane, the matrix `W_{k,n} = (n+a)^{-(s+k)}` (`k,n ≤ N`) is invertible — it factors as a
transposed Vandermonde in the pairwise distinct nodes `(n+a)^{-1}` times a nonvanishing
diagonal — so every target vector is hit by some deformation. -/
theorem ladder_matrix_surjective {s a : ℂ} (ha : 0 < a.im) (N : ℕ) (y : Fin (N + 1) → ℂ) :
    ∃ lam : Fin (N + 1) → ℂ, ∀ k : Fin (N + 1),
      (∑ n : Fin (N + 1), (((n : ℕ) : ℂ) + a) ^ (-(s + ((k : ℕ) : ℂ))) * lam n) = y k := by
  have hbase_ne : ∀ n : Fin (N + 1), (((n : ℕ) : ℂ) + a) ≠ 0 := by
    intro n hh
    have him : ((((n : ℕ) : ℂ)) + a).im = a.im := by simp
    rw [hh] at him
    simp only [Complex.zero_im] at him
    rw [← him] at ha
    exact lt_irrefl 0 ha
  have huinj : Function.Injective (fun n : Fin (N + 1) => ((((n : ℕ) : ℂ)) + a)⁻¹) := by
    intro n₁ n₂ h
    have h2 : ((((n₁ : ℕ) : ℂ)) + a) = ((((n₂ : ℕ) : ℂ)) + a) := inv_injective h
    have h3 : (((n₁ : ℕ) : ℂ)) = (((n₂ : ℕ) : ℂ)) := by
      have := congrArg (fun w => w - a) h2
      simpa using this
    exact Fin.ext (Nat.cast_injective h3)
  set W : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
    Matrix.of fun k n => ((((n : ℕ) : ℂ)) + a) ^ (-(s + ((k : ℕ) : ℂ))) with hW
  have hWfact : W = (Matrix.vandermonde
        (fun n : Fin (N + 1) => ((((n : ℕ) : ℂ)) + a)⁻¹)).transpose
      * Matrix.diagonal (fun n : Fin (N + 1) => ((((n : ℕ) : ℂ)) + a) ^ (-s)) := by
    ext k n
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    simp only [Matrix.vandermonde_apply]
    show ((((n : ℕ) : ℂ)) + a) ^ (-(s + ((k : ℕ) : ℂ))) = _
    have hsplit : -(s + ((k : ℕ) : ℂ)) = (-s) + (-((k : ℕ) : ℂ)) := by ring
    have hk1 : ((((n : ℕ) : ℂ)) + a) ^ (-(((k : ℕ)) : ℂ))
        = (((((n : ℕ) : ℂ)) + a)⁻¹) ^ (k : ℕ) := by
      rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
    rw [hsplit, Complex.cpow_add _ _ (hbase_ne n), hk1]
    ring
  have hdet : W.det ≠ 0 := by
    rw [hWfact, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    apply mul_ne_zero
    · exact (Matrix.det_vandermonde_ne_zero_iff).mpr huinj
    · rw [Finset.prod_ne_zero_iff]
      intro n _
      rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h1, _⟩
      exact hbase_ne n h1
  have hunit : IsUnit W.det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨W⁻¹.mulVec y, ?_⟩
  intro k
  have hWy : W.mulVec (W⁻¹.mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hunit, Matrix.one_mulVec]
  have hk := congrFun hWy k
  rw [Matrix.mulVec, dotProduct] at hk
  exact hk

/-- Evaluation of a substituted multivariate polynomial: composing `aeval g` with a point
evaluation is the point evaluation of the substituted values. -/
theorem eval_aeval {m r : ℕ} (v : Fin m → ℂ) (g : Fin r → MvPolynomial (Fin m) ℂ)
    (p : MvPolynomial (Fin r) ℂ) :
    MvPolynomial.eval v (MvPolynomial.aeval g p)
      = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) p := by
  have h := MvPolynomial.comp_aeval (R := ℂ) g
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] ℂ)
  have h2 := congrFun (congrArg (fun φ : MvPolynomial (Fin r) ℂ →ₐ[ℂ] ℂ => (φ :
    MvPolynomial (Fin r) ℂ → ℂ)) h) p
  simpa [MvPolynomial.aeval_eq_eval] using h2

/-- **Full algebraic independence of the Hurwitz shift ladder.**  Let `Re s > 1` and `s ∉ ℚ`.
If a polynomial `P` in `N+1` variables with coefficients in `ℂ[a]` satisfies
`P(a; ζ(s,a), ζ(s+1,a), …, ζ(s+N,a)) = 0` throughout the upper half-plane, then `P = 0` —
no bound on the degree.  Monodromy at the branch points `a = 0, -1, …, -N` deforms the ladder
along the infinite grid `(q^{m_0}, …, q^{m_N})`; polynomials vanishing on an infinite grid
vanish on the whole deformation space; the deformation directions span by the Vandermonde
factorization; so the evaluated polynomial dies at every point of the upper half-plane. -/
theorem hurwitz_ladder_independence {s : ℂ} (hs1 : 1 < s.re)
    (hsQ : ∀ r : ℚ, (r : ℂ) ≠ s) (N : ℕ)
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) a) P = 0) :
    P = 0 := by
  -- the genuine relation is the undeformed member of the family
  have h1 : ∀ a : ℂ, 0 < a.im → relA s N P (fun _ => 1) a = 0 := by
    intro a ha
    have hg : (fun k : Fin (N + 1) => dzeta s N (fun _ => 1) (k : ℕ) a)
        = fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) a :=
      funext fun k => dzeta_one s N (k : ℕ) a
    rw [relA, hg]
    exact hrel a ha
  have hgrid := relA_grid hs1 P h1
  -- pointwise endgame at each a in the upper half-plane
  have hmap : ∀ a : ℂ, 0 < a.im → MvPolynomial.map (Polynomial.evalRingHom a) P = 0 := by
    intro a ha
    set w : Fin (N + 1) → Fin (N + 1) → ℂ :=
      fun k n => ((((n : ℕ)) : ℂ) + a) ^ (-(s + ((k : ℕ) : ℂ))) with hw
    set base : Fin (N + 1) → ℂ :=
      fun k => hzeta (s + ((k : ℕ) : ℂ)) a - ∑ n : Fin (N + 1), w k n with hbase
    have hdz : ∀ (c : Fin (N + 1) → ℂ) (k : Fin (N + 1)),
        dzeta s N c (k : ℕ) a = base k + ∑ n : Fin (N + 1), w k n * c n := by
      intro c k
      rw [dzeta, hbase]
      have hterm : ∀ n : Fin (N + 1),
          (c n - 1) * ((((n : ℕ) : ℂ) + a) ^ (-(s + ((k : ℕ) : ℂ))))
            = w k n * c n - w k n := by
        intro n
        rw [hw]
        ring
      rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_sub_distrib]
      ring
    set Pa : MvPolynomial (Fin (N + 1)) ℂ := MvPolynomial.map (Polynomial.evalRingHom a) P
      with hPa
    set sub : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ :=
      fun k => MvPolynomial.C (base k)
        + ∑ n : Fin (N + 1), MvPolynomial.C (w k n) * MvPolynomial.X n with hsub
    have heval : ∀ c : Fin (N + 1) → ℂ,
        MvPolynomial.eval c (MvPolynomial.aeval sub Pa) = relA s N P c a := by
      intro c
      rw [eval_aeval]
      have hsubeval : (fun k : Fin (N + 1) => MvPolynomial.eval c (sub k))
          = fun k : Fin (N + 1) => dzeta s N c (k : ℕ) a := by
        funext k
        rw [hsub]
        simp only [map_add, MvPolynomial.eval_C, map_sum, map_mul, MvPolynomial.eval_X]
        rw [hdz c k]
      rw [hsubeval, hPa, MvPolynomial.eval_map]
      rfl
    have hΨ0 : MvPolynomial.aeval sub Pa = 0 := by
      apply mv_grid_zero _ _ (fun _ => Set.range (fun m : ℕ => monoScalar s ^ m))
      · intro _
        exact Set.infinite_range_of_injective (monoScalar_pow_injective hsQ)
      · intro v hv
        choose m hm using hv
        have hveq : v = fun n => monoScalar s ^ m n := by
          funext n
          exact (hm n).symm
        rw [heval, hveq]
        exact hgrid m a ha
    have hall : ∀ lam : Fin (N + 1) → ℂ, relA s N P lam a = 0 := by
      intro lam
      rw [← heval lam, hΨ0, map_zero]
    have hy : ∀ y : Fin (N + 1) → ℂ, MvPolynomial.eval y Pa = 0 := by
      intro y
      obtain ⟨lam, hlam⟩ := ladder_matrix_surjective ha N (fun k => y k - base k)
      have hdzy : (fun k : Fin (N + 1) => dzeta s N lam (k : ℕ) a) = y := by
        funext k
        rw [hdz lam k]
        have hk := hlam k
        rw [hw]
        rw [show (∑ n : Fin (N + 1),
            ((((n : ℕ)) : ℂ) + a) ^ (-(s + ((k : ℕ) : ℂ))) * lam n) = y k - base k from hk]
        ring
      have hrel_lam := hall lam
      rw [relA, ← MvPolynomial.eval_map (Polynomial.evalRingHom a), hdzy] at hrel_lam
      exact hrel_lam
    refine MvPolynomial.funext (fun y => ?_)
    rw [hy y, map_zero]
  -- each ℂ[a]-coefficient has infinitely many roots
  have hcoeff : ∀ d : Fin (N + 1) →₀ ℕ, MvPolynomial.coeff d P = 0 := by
    intro d
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun t : ℕ => (((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I) := by
      intro t₁ t₂ h
      have him := congrArg Complex.im h
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_one, mul_zero, add_zero] at him
      have : (t₁ : ℝ) = (t₂ : ℝ) := by linarith
      exact_mod_cast this
    have hsub : Set.range (fun t : ℕ => (((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I)
        ⊆ {x | Polynomial.IsRoot (MvPolynomial.coeff d P) x} := by
      rintro x ⟨t, rfl⟩
      have him : 0 < ((((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im := by
        simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_one, mul_zero, add_zero]
        positivity
      have hm := hmap _ him
      have hc := congrArg (MvPolynomial.coeff d) hm
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hc
      exact hc
    exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)
  exact MvPolynomial.ext _ _ (fun d => by rw [hcoeff d, MvPolynomial.coeff_zero])

/-- **Near-ray form.**  The relation hypothesis is needed only on one punctured upper
half-disc at a single branch point `-n₀`: the genuine relation function is analytic on the
upper half-plane, so the identity theorem propagates it everywhere. -/
theorem hurwitz_ladder_independence_near_ray {s : ℂ} (hs1 : 1 < s.re)
    (hsQ : ∀ r : ℚ, (r : ℂ) ≠ s) (N : ℕ) (n₀ : ℕ)
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ x : ℂ, ‖x‖ < 1 / 2 → 0 < x.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom (-(n₀ : ℂ) + x))
        (fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) (-(n₀ : ℂ) + x)) P = 0) :
    P = 0 := by
  apply hurwitz_ladder_independence hs1 hsQ N P
  -- the genuine relation function, as the undeformed relA (any deformation width works)
  have hReq : ∀ a : ℂ, relA (N := N) s 0 P (fun _ => 1) a
      = MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) a) P := by
    intro a
    have hg : (fun k : Fin (N + 1) => dzeta s 0 (fun _ => 1) (k : ℕ) a)
        = fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) a :=
      funext fun k => dzeta_one s 0 (k : ℕ) a
    rw [relA, hg]
  have hAn : AnalyticOnNhd ℂ (relA (N := N) s 0 P (fun _ => 1)) UHP :=
    (relA_differentiableOn hs1 P _).analyticOnNhd isOpen_UHP
  set a₀ : ℂ := -(n₀ : ℂ) + ((1 / 4 : ℝ) : ℂ) * Complex.I with ha₀
  have ha₀x : a₀ + (n₀ : ℂ) = ((1 / 4 : ℝ) : ℂ) * Complex.I := by rw [ha₀]; ring
  have ha₀mem : a₀ ∈ UHP := by
    show 0 < a₀.im
    have him : a₀.im = (a₀ + (n₀ : ℂ)).im := by simp
    rw [him, ha₀x]
    simp
  have hOopen : IsOpen {a : ℂ | 0 < (a + (n₀ : ℂ)).im ∧ ‖a + (n₀ : ℂ)‖ < 1 / 2} := by
    apply IsOpen.inter
    · have hcont : Continuous fun a : ℂ => (a + (n₀ : ℂ)).im :=
        Complex.continuous_im.comp (continuous_id.add continuous_const)
      exact isOpen_lt continuous_const hcont
    · have hcont : Continuous fun a : ℂ => ‖a + (n₀ : ℂ)‖ :=
        (continuous_id.add continuous_const).norm
      exact isOpen_lt hcont continuous_const
  have ha₀O : a₀ ∈ {a : ℂ | 0 < (a + (n₀ : ℂ)).im ∧ ‖a + (n₀ : ℂ)‖ < 1 / 2} := by
    constructor
    · rw [ha₀x]
      simp
    · rw [ha₀x, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      norm_num
  have hev : relA (N := N) s 0 P (fun _ => 1) =ᶠ[nhds a₀] 0 := by
    refine Filter.eventuallyEq_of_mem (hOopen.mem_nhds ha₀O) ?_
    intro a ha
    have hx := hrel (a + (n₀ : ℂ)) ha.2 ha.1
    have ha_eq : -(n₀ : ℂ) + (a + (n₀ : ℂ)) = a := by ring
    rw [ha_eq] at hx
    rw [Pi.zero_apply, hReq a]
    exact hx
  have hzero := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_UHP
    ha₀mem hev
  intro a ha
  have := hzero (ha : a ∈ UHP)
  rw [Pi.zero_apply] at this
  rw [← hReq a]
  exact this

end HurwitzLadder
