import GaloisForLFunctions.HTGeometry.LeeYangAsanoContraction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The first-zero budget law for ferromagnetic characteristic functions

Let `σ` be an Ising model on a finite set `V` at zero field, with ferromagnetic couplings `J ≥ 0` on
bonds between distinct sites. Let `X = Σ_k c_k σ_k`, and let `t` satisfy `0 < t c_k < π/2`, with
`τ_k = tan(t c_k)`.

* **Lee–Yang for the moment generating polynomial** (`genFn_ne_zero`). The function
  `G(x) = Σ_D W(D) ∏_k (1 + x_kσ_k)` equals `e^{ΣJ} ∏(1 + x_k)·Z_{LY}(w)` with
  `w_k = (1 − x_k)/(1 + x_k)` and Lee–Yang couplings `e^{−2J}` (`genFn_eq_maEval`). So it has no
  zero when all `Re x_k > 0`, and by spin flip none when all `Re x_k < 0`.
* **The budget polynomial** (`budgetPoly`). With `M_A = Σ_D W(D)∏_{k∈A}σ_k` (odd moments vanish,
  `corrA_eq_zero_of_odd`), `q(u) = Σ_{|A| even} (−u)^{|A|/2} τ_A M_A / Z₀` satisfies
  `q(λ²) = G(iλτ)/Z₀`, `q(0) = 1` and `q'(0) = −S` with `S = Σ_{a<b} τ_aτ_b⟨σ_aσ_b⟩`
  (`coeff_one_budgetPoly`). Lee–Yang puts every root of `q` on `(0, ∞)` (`budgetPoly_roots`).
* **Positive roots** (`eval_one_ge_of_pos_roots`). A real polynomial with `q(0) = 1` and all roots
  real and positive is `∏(1 − u/u_j)`, so `q(1) ≥ 1 − S` when `S < 1`.
* **Griffiths' first inequality** (`corrA_nonneg`), via the high-temperature expansion.

**Theorem** (`charFn_ge`). `Z₀ E[e^{itX}] ≥ Z₀ ∏_k cos(t c_k)·(1 − S) > 0` whenever `S < 1`.

**Corollary** (`charFn_pos_of_variance_budget`). If `τ_aτ_b ≤ R c_ac_b` and
`R·Σ_{a<b} c_ac_b⟨σ_aσ_b⟩ < 1`, then `E[e^{itX}] > 0`. The sum is half the excess variance
`Var X − Σ c_k²`.

Newman's Gaussian inequality is not needed. The threshold `S < 1` improves the bound
`sinh S < 1` that comes from Gaussian domination.
-/

open Complex Finset Polynomial

namespace GaloisForLFunctions.HTGeometry.LeeYang

/-- **Positive-root polynomials.** Let `q` be a real polynomial with `q(0) = 1` whose complex roots
are all real and positive. Then `c := −q'(0) ≥ 0`, and `q(1) ≥ 1 − c` whenever `c < 1`. Indeed
`q = ∏(1 − X/u_j)` with `u_j > 0`, `c = Σ 1/u_j`, and `∏(1 − y_j) ≥ 1 − Σ y_j` on `[0, 1]`. -/
theorem eval_one_ge_of_pos_roots : ∀ (n : ℕ) (q : ℝ[X]), q.natDegree = n → q.eval 0 = 1 →
    (∀ z : ℂ, aeval z q = 0 → z.im = 0 ∧ 0 < z.re) →
    0 ≤ -q.coeff 1 ∧ (-q.coeff 1 < 1 → 1 - (-q.coeff 1) ≤ q.eval 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q hn h0 hroots
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hq := eq_C_of_natDegree_eq_zero (hn ▸ hn0)
    have hc0 : q.coeff 0 = 1 := by rw [hq] at h0; simpa using h0
    rw [hq, hc0]; simp [Polynomial.coeff_one]
  -- a positive real root
  have hdeg : 0 < (q.map (algebraMap ℝ ℂ)).degree := by
    rw [degree_map]; exact natDegree_pos_iff_degree_pos.mp (hn ▸ hnpos)
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hza : aeval z q = 0 := by rw [aeval_def, ← eval_map]; exact hz
  obtain ⟨hzim, hzre⟩ := hroots z hza
  set u := z.re with hu
  have hzu : z = (u : ℂ) := by apply Complex.ext <;> simp [hu, hzim]
  have hqu : q.eval u = 0 := by
    have := hza
    rw [hzu, show (u : ℂ) = algebraMap ℝ ℂ u from rfl,
      aeval_algebraMap_apply_eq_algebraMap_eval] at this
    exact (algebraMap ℝ ℂ).injective (by rw [this, map_zero])
  have hroot : q.IsRoot u := hqu
  set p := q /ₘ (X - C u) with hp
  have hqp : (X - C u) * p = q := mul_divByMonic_eq_iff_isRoot.mpr hroot
  set h := C (-u) * p with hh
  have hu0 : u ≠ 0 := hzre.ne'
  have hqh : q = (C 1 - C (1 / u) * X) * h := by
    rw [← hqp, hh]
    have : (C 1 - C (1 / u) * X) * (C (-u) * p) = (X - C u) * p := by
      rw [← mul_assoc]; congr 1
      rw [show (C 1 - C (1 / u) * X) * C (-u) = C (-u) + C (1 / u * u) * X by
        simp only [map_neg, map_one, map_mul]; ring]
      rw [div_mul_cancel₀ (1 : ℝ) hu0]; simp; ring
    exact this.symm
  clear_value h
  have hh0 : h.eval 0 = 1 := by
    have := congrArg (eval 0) hqh
    rw [h0] at this; simpa using this.symm
  have hhdeg : h.natDegree < n := by
    have h1 : h.natDegree = p.natDegree := by rw [hh]; exact natDegree_C_mul (neg_ne_zero.mpr hu0)
    have h2 : p.natDegree = q.natDegree - 1 := by
      rw [hp, natDegree_divByMonic _ (monic_X_sub_C u), natDegree_X_sub_C]
    omega
  have hhroots : ∀ w : ℂ, aeval w h = 0 → w.im = 0 ∧ 0 < w.re := by
    intro w hw
    refine hroots w ?_
    rw [hqh, map_mul, hw, mul_zero]
  obtain ⟨ihpos, ihbd⟩ := ih h.natDegree hhdeg h rfl hh0 hhroots
  have hcoeff : q.coeff 1 = h.coeff 1 - 1 / u := by
    have hc0 : h.coeff 0 = 1 := by rw [← hh0, coeff_zero_eq_eval_zero]
    have e : (C 1 - C (1 / u) * X) * h = h - C (1 / u) * (X * h) := by
      rw [sub_mul, map_one, one_mul, mul_assoc]
    have hX : (X * h).coeff 1 = h.coeff 0 := coeff_X_mul (p := h) (n := 0)
    rw [hqh, e, coeff_sub, coeff_C_mul, hX, hc0]; ring
  have hinv : 0 < 1 / u := by positivity
  refine ⟨by rw [hcoeff]; linarith, fun hlt => ?_⟩
  have hlt1 : 1 / u < 1 := by rw [hcoeff] at hlt; linarith
  have hlt2 : -h.coeff 1 < 1 := by rw [hcoeff] at hlt; linarith
  have hb := ihbd hlt2
  have heval : q.eval 1 = (1 - 1 / u) * h.eval 1 := by rw [hqh]; simp
  rw [heval, hcoeff]
  have hpos : 0 ≤ 1 - 1 / u := by linarith
  have := mul_le_mul_of_nonneg_left hb hpos
  nlinarith

/-! ## Ising spins -/

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin `σ_k = −1` on the down set `D` and `+1` off it. -/
def spin (D : Finset V) (k : V) : ℝ := if k ∈ D then -1 else 1

/-- The Boltzmann weight `exp(Σ_{(i,j)∈E} J_{ij} σ_i σ_j)` at zero field. -/
def isingWeight (J : V → V → ℝ) (E : Finset (V × V)) (D : Finset V) : ℝ :=
  Real.exp (∑ p ∈ E, J p.1 p.2 * spin D p.1 * spin D p.2)

/-- The generating function `Σ_D W(D) ∏_k (1 + x_k σ_k)`. -/
def genFn (J : V → V → ℝ) (E : Finset (V × V)) (x : V → ℂ) : ℂ :=
  ∑ D : Finset V, (isingWeight J E D : ℂ) * ∏ k, (1 + x k * spin D k)

omit [Fintype V] in
theorem spin_compl [Fintype V] (D : Finset V) (k : V) : spin Dᶜ k = -spin D k := by
  by_cases h : k ∈ D <;> simp [spin, h]

theorem isingWeight_compl (J : V → V → ℝ) (E : Finset (V × V)) (D : Finset V) :
    isingWeight J E Dᶜ = isingWeight J E D := by
  simp only [isingWeight, spin_compl, mul_neg, neg_mul, neg_neg]

omit [Fintype V] in
theorem isingWeight_pos (J : V → V → ℝ) (E : Finset (V × V)) (D : Finset V) : 0 < isingWeight J E D :=
  Real.exp_pos _

/-- **Spin-flip symmetry** at zero field. -/
theorem genFn_neg (J : V → V → ℝ) (E : Finset (V × V)) (x : V → ℂ) :
    genFn J E (fun k => -x k) = genFn J E x := by
  rw [genFn, genFn]
  refine Fintype.sum_equiv ⟨compl, compl, compl_compl, compl_compl⟩ _ _ (fun D => ?_)
  simp only [Equiv.coe_fn_mk, isingWeight_compl, spin_compl]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  push_cast; ring

omit [Fintype V] in
theorem exp_bond (Jv : ℝ) (D : Finset V) (i j : V) :
    Real.exp (Jv * spin D i * spin D j) =
      Real.exp Jv * (if (i ∈ D ↔ j ∈ D) then 1 else Real.exp (-2 * Jv)) := by
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp [spin, hi, hj, ← Real.exp_add] <;> ring_nf

/-- **Bridge to the Lee–Yang polynomial:** `genFn = e^{ΣJ} ∏(1 + x_k) · Z(w)` with
`w_k = (1 − x_k)/(1 + x_k)` and couplings `e^{−2J}`. -/
theorem genFn_eq_maEval (J : V → V → ℝ) (E : Finset (V × V)) {x : V → ℂ}
    (hx : ∀ k, 1 + x k ≠ 0) :
    genFn J E x = (Real.exp (∑ p ∈ E, J p.1 p.2) : ℂ) * (∏ k, (1 + x k)) *
      maEval (isingCoeff (fun i j => Real.exp (-2 * J i j)) E)
        (fun k => (1 - x k) / (1 + x k)) := by
  rw [genFn, maEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  have hbr : isingWeight J E D = Real.exp (∑ p ∈ E, J p.1 p.2) *
      ∏ p ∈ E, (if (p.1 ∈ D ↔ p.2 ∈ D) then 1 else Real.exp (-2 * J p.1 p.2)) := by
    rw [isingWeight, Real.exp_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => exp_bond _ D p.1 p.2
  have hic : isingCoeff (fun i j => Real.exp (-2 * J i j)) E D =
      ((∏ p ∈ E, (if (p.1 ∈ D ↔ p.2 ∈ D) then 1 else Real.exp (-2 * J p.1 p.2)) : ℝ) : ℂ) := by
    rw [isingCoeff, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [bondWeight]
    split_ifs <;> simp
  have hb : (isingWeight J E D : ℂ) = (Real.exp (∑ p ∈ E, J p.1 p.2) : ℂ) *
      isingCoeff (fun i j => Real.exp (-2 * J i j)) E D := by
    rw [hbr, hic, Complex.ofReal_mul]
  have hp : ∏ k, (1 + x k * spin D k) = (∏ k, (1 + x k)) * ∏ k ∈ D, (1 - x k) / (1 + x k) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ D)]
    have h1 : ∏ k ∈ Finset.univ.filter (· ∈ D), (1 + x k * spin D k) =
        ∏ k ∈ D, (1 - x k) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.prod_congr rfl fun k hk => by simp [spin, hk]; ring
    have h2 : ∏ k ∈ Finset.univ.filter (· ∉ D), (1 + x k * spin D k) =
        ∏ k ∈ Finset.univ.filter (· ∉ D), (1 + x k) :=
      Finset.prod_congr rfl fun k hk => by
        simp only [Finset.mem_filter] at hk; simp [spin, hk.2]
    rw [h1, h2]
    have h3 : ∏ k ∈ D, (1 - x k) = (∏ k ∈ D, (1 + x k)) * ∏ k ∈ D, (1 - x k) / (1 + x k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by field_simp [hx k]
    rw [h3, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ D) (fun k => 1 + x k),
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    ring
  rw [hb, hp]; ring

/-- **Lee–Yang for the generating function.** `genFn ≠ 0` whenever all `Re x_k > 0` or all
`Re x_k < 0`, for ferromagnetic couplings `J ≥ 0`. -/
theorem genFn_ne_zero (J : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) {x : V → ℂ}
    (hx : (∀ k, 0 < (x k).re) ∨ (∀ k, (x k).re < 0)) : genFn J E x ≠ 0 := by
  have hpos : ∀ y : V → ℂ, (∀ k, 0 < (y k).re) → genFn J E y ≠ 0 := by
    intro y hy
    have h1 : ∀ k, 1 + y k ≠ 0 := fun k h => by
      have := congrArg Complex.re h; simp at this; linarith [hy k]
    rw [genFn_eq_maEval J E h1]
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne')
      (Finset.prod_ne_zero_iff.mpr fun k _ => h1 k)) ?_
    refine leeYang_polydisc _ E hE (fun p hp => ?_) _ fun k => ?_
    · rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      linarith [hJ p hp]
    · rw [norm_div, div_lt_one (norm_pos_iff.mpr (h1 k))]
      have e1 : ‖1 - y k‖ ^ 2 = (1 - (y k).re) ^ 2 + (y k).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
      have e2 : ‖1 + y k‖ ^ 2 = (1 + (y k).re) ^ 2 + (y k).im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
      have : ‖1 - y k‖ ^ 2 < ‖1 + y k‖ ^ 2 := by rw [e1, e2]; nlinarith [hy k]
      nlinarith [norm_nonneg (1 - y k), norm_nonneg (1 + y k)]
  rcases hx with h | h
  · exact hpos x h
  · rw [← genFn_neg]
    exact hpos _ fun k => by simp [h k]

/-! ## Moments and the budget polynomial -/

/-- The unnormalized moment `M_A = Σ_D W(D) ∏_{k∈A} σ_k`. -/
def corrA (J : V → V → ℝ) (E : Finset (V × V)) (A : Finset V) : ℝ :=
  ∑ D : Finset V, isingWeight J E D * ∏ k ∈ A, spin D k

/-- The partition function `Z₀ = Σ_D W(D)`. -/
def Zpart (J : V → V → ℝ) (E : Finset (V × V)) : ℝ := ∑ D : Finset V, isingWeight J E D

theorem Zpart_pos (J : V → V → ℝ) (E : Finset (V × V)) : 0 < Zpart J E :=
  Finset.sum_pos (fun D _ => isingWeight_pos J E D) ⟨∅, Finset.mem_univ _⟩

theorem corrA_empty (J : V → V → ℝ) (E : Finset (V × V)) : corrA J E ∅ = Zpart J E := by
  simp [corrA, Zpart]

/-- **Odd moments vanish** at zero field. -/
theorem corrA_eq_zero_of_odd (J : V → V → ℝ) (E : Finset (V × V)) {A : Finset V}
    (hA : Odd A.card) : corrA J E A = 0 := by
  have h : corrA J E A = -corrA J E A := by
    conv_lhs => rw [corrA]
    rw [← Fintype.sum_equiv ⟨compl, compl, compl_compl, compl_compl⟩
      (fun D => isingWeight J E Dᶜ * ∏ k ∈ A, spin Dᶜ k) _ (fun D => by simp)]
    simp only [isingWeight_compl, spin_compl, Finset.prod_neg, hA.neg_one_pow, corrA]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  linarith

/-- **Moment expansion:** `genFn(sτ) = Σ_A s^{|A|} τ_A M_A`. -/
theorem genFn_smul_eq (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) (s : ℂ) :
    genFn J E (fun k => s * τ k) =
      ∑ A : Finset V, s ^ A.card * (((∏ k ∈ A, τ k) * corrA J E A : ℝ) : ℂ) := by
  have hexp : ∀ D : Finset V, ∏ k, (1 + s * τ k * spin D k) =
      ∑ A : Finset V, s ^ A.card * (((∏ k ∈ A, τ k) * ∏ k ∈ A, spin D k : ℝ) : ℂ) := by
    intro D
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    push_cast
    ring
  rw [genFn]
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [corrA]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun D _ => by ring

/-- The coefficient `(−1)^{|A|/2} τ_A M_A / Z₀`. -/
def budgetCoeff (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) (A : Finset V) : ℝ :=
  (-1) ^ (A.card / 2) * ((∏ k ∈ A, τ k) * corrA J E A) / Zpart J E

/-- **The budget polynomial** `q(u) = Σ_{|A| even} (−u)^{|A|/2} τ_A M_A / Z₀`, so that
`q(λ²) = genFn(iλτ)/Z₀`. -/
def budgetPoly (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) : ℝ[X] :=
  ∑ A : Finset V, if Even A.card then C (budgetCoeff J E τ A) * X ^ (A.card / 2) else 0

/-- The tangent-weighted pair mass `S = Σ_{a<b} τ_a τ_b ⟨σ_a σ_b⟩`. -/
def pairMass (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset V).powersetCard 2, (∏ k ∈ A, τ k) * corrA J E A / Zpart J E

theorem aeval_ofReal_eq_eval (q : ℝ[X]) (x : ℝ) : aeval (x : ℂ) q = ((q.eval x : ℝ) : ℂ) := by
  have := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) x q
  simpa [Complex.coe_algebraMap] using this

theorem aeval_budgetPoly (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) (l : ℂ) :
    aeval (l * l) (budgetPoly J E τ) = genFn J E (fun k => (I * l) * τ k) / Zpart J E := by
  rw [genFn_smul_eq, budgetPoly, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun A _ => ?_
  have hZ : (Zpart J E : ℂ) ≠ 0 := by exact_mod_cast (Zpart_pos J E).ne'
  split_ifs with hA
  · obtain ⟨n, hn⟩ := hA
    have hcard : A.card / 2 = n := by omega
    rw [map_mul, aeval_C, map_pow, aeval_X, budgetCoeff, hcard, hn, ← two_mul, pow_mul]
    simp only [Complex.coe_algebraMap]
    push_cast
    rw [show (I * l) ^ 2 = -(l * l) by ring_nf; rw [I_sq]; ring]
    field_simp
    ring
  · rw [Nat.not_even_iff_odd] at hA
    rw [corrA_eq_zero_of_odd J E hA]
    simp

theorem eval_zero_budgetPoly (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) :
    (budgetPoly J E τ).eval 0 = 1 := by
  have h := aeval_budgetPoly J E τ 0
  rw [show (0 : ℂ) * 0 = ((0 : ℝ) : ℂ) by simp, aeval_ofReal_eq_eval] at h
  have hg : genFn J E (fun k => (I * 0) * τ k) = Zpart J E := by
    simp [genFn, Zpart]
  rw [hg, div_self (by exact_mod_cast (Zpart_pos J E).ne')] at h
  exact_mod_cast h

theorem coeff_one_budgetPoly (J : V → V → ℝ) (E : Finset (V × V)) (τ : V → ℝ) :
    (budgetPoly J E τ).coeff 1 = -pairMass J E τ := by
  rw [budgetPoly, finsetSum_coeff, pairMass, Finset.powersetCard_eq_filter, Finset.powerset_univ,
    Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h2 : A.card = 2
  · have hev : Even A.card := by rw [h2]; exact even_two
    rw [if_pos hev, if_pos h2, coeff_C_mul_X_pow, if_pos (by rw [h2]), budgetCoeff, h2]
    ring
  · rw [if_neg h2, neg_zero]
    split_ifs with hev
    · rw [coeff_C_mul_X_pow, if_neg]
      obtain ⟨n, hn⟩ := hev
      omega
    · rfl

/-- **Lee–Yang places every root of the budget polynomial on `(0, ∞)`.** -/
theorem budgetPoly_roots (J : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) {τ : V → ℝ} (hτ : ∀ k, 0 < τ k) (u : ℂ)
    (hu : aeval u (budgetPoly J E τ) = 0) : u.im = 0 ∧ 0 < u.re := by
  obtain ⟨l, rfl⟩ := IsAlgClosed.exists_eq_mul_self u
  rw [aeval_budgetPoly, div_eq_zero_iff] at hu
  have hZ : (Zpart J E : ℂ) ≠ 0 := by exact_mod_cast (Zpart_pos J E).ne'
  have hg : genFn J E (fun k => (I * l) * τ k) = 0 := hu.resolve_right hZ
  have hre : ∀ k, ((I * l) * τ k).re = -(l.im * τ k) := fun k => by simp
  have him : l.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact genFn_ne_zero J E hE hJ (Or.inl fun k => by rw [hre]; nlinarith [hτ k]) hg
    · exact genFn_ne_zero J E hE hJ (Or.inr fun k => by rw [hre]; nlinarith [hτ k]) hg
  have hl : l = (l.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hre0 : l.re ≠ 0 := by
    intro h0
    have h1 : l = 0 := by rw [hl, h0]; simp
    rw [h1] at hg
    have h2 : genFn J E (fun k => (I * 0) * τ k) = Zpart J E := by simp [genFn, Zpart]
    rw [h2] at hg
    exact hZ hg
  refine ⟨by simp [him], ?_⟩
  simp only [Complex.mul_re, him, mul_zero, sub_zero]
  exact mul_self_pos.mpr hre0

/-- **The first-zero budget law (abstract form).** For a ferromagnet at zero field and positive
weights `τ`, `genFn(iτ) = Σ_D W(D) ∏_k(1 + iτ_kσ_k)` is real and at least `Z₀(1 − S)` whenever the
pair mass `S = Σ_{a<b} τ_aτ_b⟨σ_aσ_b⟩` is below `1`. -/
theorem genFn_I_ge (J : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) {τ : V → ℝ} (hτ : ∀ k, 0 < τ k)
    (hS : pairMass J E τ < 1) :
    ∃ r : ℝ, genFn J E (fun k => I * τ k) = r ∧ Zpart J E * (1 - pairMass J E τ) ≤ r := by
  obtain ⟨-, hbd⟩ := eval_one_ge_of_pos_roots _ (budgetPoly J E τ) rfl
    (eval_zero_budgetPoly J E τ) (budgetPoly_roots J E hE hJ hτ)
  rw [coeff_one_budgetPoly, neg_neg] at hbd
  have hq := hbd hS
  refine ⟨Zpart J E * (budgetPoly J E τ).eval 1, ?_, ?_⟩
  · have h := aeval_budgetPoly J E τ 1
    rw [show (1 : ℂ) * 1 = ((1 : ℝ) : ℂ) by simp, aeval_ofReal_eq_eval, mul_one] at h
    have hZ : (Zpart J E : ℂ) ≠ 0 := by exact_mod_cast (Zpart_pos J E).ne'
    rw [eq_div_iff hZ] at h
    push_cast
    rw [← h]; ring
  · exact mul_le_mul_of_nonneg_left hq (Zpart_pos J E).le

/-! ## Griffiths' first inequality -/

omit [Fintype V] in
theorem spin_mul_self (D : Finset V) (k : V) : spin D k * spin D k = 1 := by
  by_cases h : k ∈ D <;> simp [spin, h]

omit [Fintype V] in
/-- Spin monomials multiply by symmetric difference. -/
theorem prod_spin_mul (D B C : Finset V) :
    (∏ k ∈ B, spin D k) * ∏ k ∈ C, spin D k = ∏ k ∈ symmDiff B C, spin D k := by
  rw [← Finset.prod_sdiff (Finset.inter_subset_left : B ∩ C ⊆ B),
    ← Finset.prod_sdiff (Finset.inter_subset_right : B ∩ C ⊆ C),
    Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right, symmDiff_def,
    Finset.sup_eq_union, Finset.prod_union disjoint_sdiff_sdiff]
  have hsq : (∏ k ∈ B ∩ C, spin D k) * ∏ k ∈ B ∩ C, spin D k = 1 := by
    rw [← Finset.prod_mul_distrib]; simp [spin_mul_self]
  calc (∏ k ∈ B \ C, spin D k) * (∏ k ∈ B ∩ C, spin D k) *
        ((∏ k ∈ C \ B, spin D k) * ∏ k ∈ B ∩ C, spin D k)
      = (∏ k ∈ B \ C, spin D k) * (∏ k ∈ C \ B, spin D k) *
        ((∏ k ∈ B ∩ C, spin D k) * ∏ k ∈ B ∩ C, spin D k) := by ring
    _ = _ := by rw [hsq, mul_one]

omit [Fintype V] in
/-- A product of bond spins is a spin monomial. -/
theorem exists_prod_bond_eq (F : Finset (V × V)) :
    ∃ B : Finset V, ∀ D : Finset V,
      ∏ p ∈ F, (spin D p.1 * spin D p.2) = ∏ k ∈ B, spin D k := by
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, fun D => by simp⟩
  | insert p F hp ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨symmDiff (symmDiff {p.1} {p.2}) B, fun D => ?_⟩
    rw [Finset.prod_insert hp, hB, ← prod_spin_mul, ← prod_spin_mul]
    simp

/-- **The sum of a spin monomial is nonnegative.** -/
theorem sum_prod_spin_nonneg (B : Finset V) : 0 ≤ ∑ D : Finset V, ∏ k ∈ B, spin D k := by
  have e : ∀ D : Finset V, ∏ k ∈ B, spin D k = ∏ k ∈ D, (if k ∈ B then (-1 : ℝ) else 1) := by
    intro D
    have l1 : ∏ k ∈ B, spin D k = ∏ k, (if k ∈ B then spin D k else 1) := by
      rw [Finset.prod_ite_mem, Finset.univ_inter]
    have l2 : ∏ k ∈ D, (if k ∈ B then (-1 : ℝ) else 1) =
        ∏ k, (if k ∈ D then (if k ∈ B then (-1 : ℝ) else 1) else 1) := by
      rw [Finset.prod_ite_mem Finset.univ D (fun k => if k ∈ B then (-1 : ℝ) else 1),
        Finset.univ_inter]
    rw [l1, l2]
    exact Finset.prod_congr rfl fun k _ => by
      by_cases hk : k ∈ D <;> by_cases hb : k ∈ B <;> simp [spin, hk, hb]
  simp_rw [e]
  have h := Finset.prod_add (fun k : V => (if k ∈ B then (-1 : ℝ) else 1)) (fun _ => (1 : ℝ))
    Finset.univ
  simp only [Finset.prod_const_one, mul_one, Finset.powerset_univ] at h
  rw [← h]
  exact Finset.prod_nonneg fun k _ => by split_ifs <;> norm_num

omit [Fintype V] in
theorem exp_bond_cosh (Jv : ℝ) (D : Finset V) (i j : V) :
    Real.exp (Jv * spin D i * spin D j) = Real.sinh Jv * (spin D i * spin D j) + Real.cosh Jv := by
  rw [← Real.cosh_add_sinh]
  by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;>
    simp [spin, hi, hj, Real.cosh_neg, Real.sinh_neg] <;> ring

/-- **Griffiths' first inequality.** For ferromagnetic couplings, every moment `M_A` is
nonnegative. -/
theorem corrA_nonneg (J : V → V → ℝ) (E : Finset (V × V)) (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2)
    (A : Finset V) : 0 ≤ corrA J E A := by
  have hW : ∀ D : Finset V, isingWeight J E D =
      ∑ t ∈ E.powerset, (∏ p ∈ t, (Real.sinh (J p.1 p.2) * (spin D p.1 * spin D p.2))) *
        ∏ p ∈ E \ t, Real.cosh (J p.1 p.2) := by
    intro D
    rw [isingWeight, Real.exp_sum, ← Finset.prod_add]
    exact Finset.prod_congr rfl fun p _ => exp_bond_cosh _ D _ _
  rw [corrA]
  simp_rw [hW, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun t ht => ?_
  obtain ⟨B, hB⟩ := exists_prod_bond_eq t
  have ht' : t ⊆ E := Finset.mem_powerset.mp ht
  have e : ∀ D : Finset V, (∏ p ∈ t, (Real.sinh (J p.1 p.2) * (spin D p.1 * spin D p.2))) *
      (∏ p ∈ E \ t, Real.cosh (J p.1 p.2)) * ∏ k ∈ A, spin D k =
      ((∏ p ∈ t, Real.sinh (J p.1 p.2)) * ∏ p ∈ E \ t, Real.cosh (J p.1 p.2)) *
        ∏ k ∈ symmDiff B A, spin D k := by
    intro D
    rw [Finset.prod_mul_distrib, hB, ← prod_spin_mul]; ring
  simp_rw [e, ← Finset.mul_sum]
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p hp => ?_)
    (Finset.prod_nonneg fun p _ => (Real.cosh_pos _).le)) (sum_prod_spin_nonneg _)
  exact Real.sinh_nonneg_iff.mpr (hJ p (ht' hp))

/-! ## The characteristic function of a weighted magnetization -/

/-- The unnormalized characteristic function `Σ_D W(D) e^{it Σ_k c_k σ_k}`. -/
def charFn (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (t : ℝ) : ℂ :=
  ∑ D : Finset V, (isingWeight J E D : ℂ) * Complex.exp (I * t * ∑ k, (c k * spin D k : ℝ))

omit [Fintype V] in
theorem exp_I_spin (x : ℝ) (D : Finset V) (k : V) (hx : Real.cos x ≠ 0) :
    Complex.exp (I * ((x * spin D k : ℝ) : ℂ)) =
      (Real.cos x : ℂ) * (1 + I * (Real.tan x : ℂ) * (spin D k : ℂ)) := by
  have ht : (Real.tan x : ℂ) = (Real.sin x : ℂ) / (Real.cos x : ℂ) := by
    rw [Real.tan_eq_sin_div_cos]; push_cast; ring
  have hc : (Real.cos x : ℂ) ≠ 0 := by exact_mod_cast hx
  rw [ht]
  by_cases h : k ∈ D
  · simp only [spin, h, if_true]
    push_cast
    rw [show I * (x * -1 : ℂ) = (-x : ℂ) * I by ring, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp
  · simp only [spin, h, if_false]
    push_cast
    rw [show I * (x * 1 : ℂ) = (x : ℂ) * I by ring, Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    field_simp

theorem charFn_eq (J : V → V → ℝ) (E : Finset (V × V)) (c : V → ℝ) (t : ℝ)
    (hc : ∀ k, Real.cos (t * c k) ≠ 0) :
    charFn J E c t = (∏ k, (Real.cos (t * c k) : ℂ)) *
      genFn J E (fun k => I * (Real.tan (t * c k) : ℂ)) := by
  rw [charFn, genFn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  have h : Complex.exp (I * t * ∑ k, (c k * spin D k : ℝ)) =
      ∏ k, Complex.exp (I * (((t * c k) * spin D k : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  simp_rw [exp_I_spin _ D _ (hc _)]
  rw [Finset.prod_mul_distrib]
  ring

/-- **The first-zero budget law.** Let `σ` be a ferromagnetic Ising model at zero field
(`J ≥ 0` on bonds between distinct sites), `X = Σ_k c_k σ_k`, and `t` with `0 < t c_k < π/2`.
Put `τ_k = tan(t c_k)` and `S = Σ_{a<b} τ_a τ_b ⟨σ_aσ_b⟩`. If `S < 1`, then the characteristic
function satisfies `Z₀ E[e^{itX}] ≥ Z₀ (∏_k cos(t c_k))(1 − S) > 0`. No Gaussian (Newman)
inequality is used: Lee–Yang places every zero of `s ↦ ⟨∏(1 + sτ_kσ_k)⟩` on the imaginary axis. -/
theorem charFn_ge (J : V → V → ℝ) (E : Finset (V × V)) (hE : ∀ p ∈ E, p.1 ≠ p.2)
    (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (c : V → ℝ) (t : ℝ)
    (hc : ∀ k, 0 < t * c k ∧ t * c k < Real.pi / 2)
    (hS : pairMass J E (fun k => Real.tan (t * c k)) < 1) :
    ∃ r : ℝ, charFn J E c t = r ∧
      (∏ k, Real.cos (t * c k)) * Zpart J E * (1 - pairMass J E (fun k => Real.tan (t * c k))) ≤ r ∧
      0 < r := by
  have hcos : ∀ k, 0 < Real.cos (t * c k) := fun k =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hc k, Real.pi_pos], (hc k).2⟩
  have htan : ∀ k, 0 < Real.tan (t * c k) := fun k =>
    Real.tan_pos_of_pos_of_lt_pi_div_two (hc k).1 (hc k).2
  obtain ⟨r, hr, hrge⟩ := genFn_I_ge J E hE hJ htan hS
  have hP : 0 < ∏ k, Real.cos (t * c k) := Finset.prod_pos fun k _ => hcos k
  refine ⟨(∏ k, Real.cos (t * c k)) * r, ?_, ?_, ?_⟩
  · rw [charFn_eq J E c t fun k => (hcos k).ne', hr]; push_cast; ring
  · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hrge hP.le
  · have : 0 < Zpart J E * (1 - pairMass J E (fun k => Real.tan (t * c k))) :=
      mul_pos (Zpart_pos J E) (by linarith)
    exact mul_pos hP (lt_of_lt_of_le this hrge)

/-- **The variance budget.** If `τ_aτ_b ≤ R c_ac_b` on every pair and the excess pair variance
`ΔV/2 = Σ_{a<b} c_ac_b⟨σ_aσ_b⟩` satisfies `R·ΔV/2 < 1`, then `E[e^{itX}] > 0`. -/
theorem charFn_pos_of_variance_budget (J : V → V → ℝ) (E : Finset (V × V))
    (hE : ∀ p ∈ E, p.1 ≠ p.2) (hJ : ∀ p ∈ E, 0 ≤ J p.1 p.2) (c : V → ℝ) (t R : ℝ)
    (hc : ∀ k, 0 < t * c k ∧ t * c k < Real.pi / 2)
    (hR : ∀ A ∈ (Finset.univ : Finset V).powersetCard 2,
      ∏ k ∈ A, Real.tan (t * c k) ≤ R * ∏ k ∈ A, c k)
    (hbudget : R * pairMass J E c < 1) :
    ∃ r : ℝ, charFn J E c t = r ∧ 0 < r := by
  have hle : pairMass J E (fun k => Real.tan (t * c k)) ≤ R * pairMass J E c := by
    rw [pairMass, pairMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun A hA => ?_
    have hZ := Zpart_pos J E
    have hM := corrA_nonneg J E hJ A
    rw [div_le_iff₀ hZ, mul_div_assoc', div_mul_cancel₀ _ hZ.ne', ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hR A hA) hM
  obtain ⟨r, hr, -, hpos⟩ := charFn_ge J E hE hJ c t hc (lt_of_le_of_lt hle hbudget)
  exact ⟨r, hr, hpos⟩

end

end GaloisForLFunctions.HTGeometry.LeeYang
