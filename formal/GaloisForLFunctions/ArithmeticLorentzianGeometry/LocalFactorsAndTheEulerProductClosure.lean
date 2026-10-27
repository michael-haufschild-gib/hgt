import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexTricklesDown
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSuccessorConnectionIsTheArchimedeanGaugeField

/-!
# Local factors and the Euler product closure

Where can the Lorentzian signature of Weil's form come from, place by place?

* **A prime ladder is not Lorentzian** (`not_isHyperbolic_ladderGram`). The prime kernel on the
  `p`-ladder `1, p, …, p⁵` is `log p · p^{−|i−j|/2}`: Metzler, but the classes `δ_1 + δ_p` and
  `δ_{p⁴} + δ_{p⁵}` span a positive definite plane for every prime `p` (the reverse Cauchy–Schwarz
  inequality fails since `√2 p > √p + 1`). Each Euler factor alone has at least two positive squares;
  local positivity of the Lorentzian kind is absent.
* **The archimedean jump form is a Laplacian** (`qf_jumpForm_nonpos`). A nonnegative kernel minus
  its row sums on the diagonal is negative semidefinite: the archimedean place contributes no
  positive square, and its self-energy is what pays the row sums (the stability regime of
  `TheMetzlerDichotomy` with `π = 1`).
* **The Euler product closure is Lorentzian and blind** (`isLorentzian_esymm2Form`,
  `isLorentzian_eulerHessian`). The Hessian of a product `∏_p ⟨L_p, y⟩` of nonnegative local linear
  forms at a positive point is `Σ_{p≠q} (∏_{r≠p,q} ⟨L_r, y⟩) L_p L_qᵀ`, a positive multiple of the
  second elementary symmetric form `(Σ M_p)(Σ M_p)ᵀ − Σ M_p M_pᵀ`: rank one minus positive
  semidefinite, hence Lorentzian — for **every** nonnegative choice of local data. Products
  preserve the class where sums do not, but the closure is blind to which Euler product it is fed:
  Beurling systems and fake curves supply nonnegative local factors as well. The selection of the
  Euler point cannot come from the multiplicative closure; it comes from the archimedean
  gauge-fixing (`TheSignIsAGaugeFixing`) and the trickle-down defect (`TheHodgeIndexTricklesDown`).
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticEffectivityTheory ArithmeticElectrostatics

/-! ### A prime ladder is not Lorentzian -/

/-- The prime kernel on the `p`-ladder `p^0, …, p^M`. -/
def ladderGram (p M : ℕ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Matrix.of fun i j => weilPrimeKernel (p ^ (i : ℕ)) (p ^ (j : ℕ))

theorem weilPrimeKernel_pow_pow {p : ℕ} (hp : p.Prime) {i j : ℕ} (hij : i < j) :
    weilPrimeKernel (p ^ i) (p ^ j) = Real.log p / Real.sqrt ((p : ℝ) ^ (j - i)) := by
  unfold weilPrimeKernel
  have hdvd : p ^ i ∣ p ^ j := pow_dvd_pow p hij.le
  have hne : p ^ i ≠ p ^ j := fun h => by
    have := Nat.pow_right_injective hp.two_le h; omega
  rw [if_pos ⟨hdvd, hne⟩, Nat.pow_div hij.le hp.pos,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast; rfl

theorem bil_single_single {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (a b : ι) :
    bil Q (Pi.single a 1) (Pi.single b 1) = Q a b := by
  simp [bil, mulVec, dotProduct, Pi.single_apply]

theorem bil_pair_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ) (a b c d : ι) :
    bil Q (Pi.single a 1 + Pi.single b 1) (Pi.single c 1 + Pi.single d 1) =
      Q a c + Q a d + Q b c + Q b d := by
  rw [bil_add_left, bil_add_right, bil_add_right, bil_single_single, bil_single_single,
    bil_single_single, bil_single_single]
  ring

/-- The arithmetic core: with `t = p^{−1/2} ≤ 2^{−1/2}`, `4 ≤ t⁴(1 + t)⁴` is impossible. -/
theorem ladder_revCS_fails {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (ht2 : t ^ 2 ≤ 1 / 2)
    (h : 2 * (L * t) * (2 * (L * t)) ≤ (L * t ^ 4 + L * t ^ 5 + L * t ^ 3 + L * t ^ 4) ^ 2) :
    False := by
  have e : (L * t ^ 4 + L * t ^ 5 + L * t ^ 3 + L * t ^ 4) ^ 2 =
      (L ^ 2 * t ^ 2) * (t ^ 4 * (1 + t) ^ 4) := by ring
  have e' : 2 * (L * t) * (2 * (L * t)) = (L ^ 2 * t ^ 2) * 4 := by ring
  rw [e, e'] at h
  have h4 : 4 ≤ t ^ 4 * (1 + t) ^ 4 := le_of_mul_le_mul_left h (by positivity)
  have ht34 : t ≤ 3 / 4 := by nlinarith
  have hu : t ^ 2 * (1 + t) ^ 2 ≤ 1 / 2 * (49 / 16) := by
    have h1 : (1 + t) ^ 2 ≤ 49 / 16 := by nlinarith
    exact mul_le_mul ht2 h1 (by positivity) (by norm_num)
  have hu' : t ^ 4 * (1 + t) ^ 4 = (t ^ 2 * (1 + t) ^ 2) ^ 2 := by ring
  rw [hu'] at h4
  have hu0 : 0 ≤ t ^ 2 * (1 + t) ^ 2 := by positivity
  nlinarith

/-- **Every prime ladder has two positive squares**: `δ_1 + δ_p` and `δ_{p⁴} + δ_{p⁵}` violate the
reverse Cauchy–Schwarz inequality. -/
theorem not_isHyperbolic_ladderGram {p : ℕ} (hp : p.Prime) : ¬ IsHyperbolic (ladderGram p 5) := by
  intro h
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hsq : ∀ k : ℕ, Real.sqrt ((p : ℝ) ^ k) = Real.sqrt p ^ k := fun k => by
    rw [show (p : ℝ) ^ k = (Real.sqrt p ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, hs2]]
    exact Real.sqrt_sq (by positivity)
  -- the entries in terms of `t = p^{−1/2}`
  have k : ∀ i j : ℕ, (hij : i < j) → (hj : j < 6) →
      ladderGram p 5 ⟨i, by omega⟩ ⟨j, hj⟩ = Real.log p * (Real.sqrt p)⁻¹ ^ (j - i) := by
    intro i j hij hj
    simp only [ladderGram, Matrix.of_apply]
    rw [weilPrimeKernel_pow_pow hp hij, hsq, div_eq_mul_inv, inv_pow]
  have kc : ∀ i j : Fin 6, ladderGram p 5 i j = ladderGram p 5 j i := fun i j => by
    simp only [ladderGram, Matrix.of_apply]; exact weilPrimeKernel_comm _ _
  have k0 : ∀ i : Fin 6, ladderGram p 5 i i = 0 := fun i => by
    simp only [ladderGram, Matrix.of_apply]; exact weilPrimeKernel_self _
  have hx := bil_pair_pair (ladderGram p 5) 0 1 0 1
  have hy := bil_pair_pair (ladderGram p 5) 4 5 4 5
  have hb := bil_pair_pair (ladderGram p 5) 0 1 4 5
  rw [k0, k0, kc 1 0, k 0 1 (by norm_num) (by norm_num)] at hx
  rw [k0, k0, kc 5 4, k 4 5 (by norm_num) (by norm_num)] at hy
  rw [k 0 4 (by norm_num) (by norm_num), k 0 5 (by norm_num) (by norm_num),
    k 1 4 (by norm_num) (by norm_num), k 1 5 (by norm_num) (by norm_num)] at hb
  have hcs := h _ (Pi.single 4 1 + Pi.single 5 1) (show 0 < qf (ladderGram p 5) _ by
    rw [qf, hx]; positivity)
  rw [qf, qf, hx, hy, hb] at hcs
  have ht2 : (Real.sqrt p)⁻¹ ^ 2 ≤ 1 / 2 := by
    rw [inv_pow, hs2, one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hp.two_le)
  exact ladder_revCS_fails hL (inv_pos.mpr hs) ht2 (by
    simp only [Nat.sub_zero, show 5 - 4 = 1 from rfl, show 4 - 1 = 3 from rfl,
      show 5 - 1 = 4 from rfl, show 1 - 0 = 1 from rfl, pow_one] at hcs
    linarith)

/-! ### The archimedean jump form is a Laplacian -/

variable {ι : Type*} [Fintype ι]

/-- **A jump form is negative semidefinite**: `Q − diag(Q·1)` with `Q` Metzler. The archimedean
place contributes no positive square; its self-energy pays the row sums. -/
theorem qf_jumpForm_nonpos [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsSymm) (hM : IsMetzler A)
    (v : ι → ℝ) : qf (A - diagonal (rowSum A)) v ≤ 0 := by
  have h := qf_le_sum_rowSum_mul_sq hA hM v
  have e : qf (A - diagonal (rowSum A)) v = qf A v - ∑ j, rowSum A j * v j ^ 2 := by
    rw [qf, bil, sub_mulVec, dotProduct_sub]
    congr 1
    simp only [mulVec_diagonal, dotProduct]
    exact sum_congr rfl fun j _ => by ring
  rw [e]; linarith

/-! ### The Euler product closure -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The second elementary symmetric form `Σ_{p≠q} M_p M_qᵀ` of a family of linear forms. -/
def esymm2Form (M : κ → ι → ℝ) : Matrix ι ι ℝ :=
  ∑ p, ∑ q, if p = q then 0 else vecMulVec (M p) (M q)

theorem sum_ite_eq_zero_else {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ) (f : κ → ℝ) :
    ∑ q, (if p = q then 0 else f q) = ∑ q, f q - f p := by
  rw [← Finset.add_sum_erase _ _ (mem_univ p), ← Finset.add_sum_erase _ f (mem_univ p), if_pos rfl,
    zero_add, add_sub_cancel_left]
  exact sum_congr rfl fun q hq => if_neg (Ne.symm (ne_of_mem_erase hq))

theorem esymm2Form_apply (M : κ → ι → ℝ) (i j : ι) :
    esymm2Form M i j = (∑ p, M p i) * (∑ q, M q j) - ∑ p, M p i * M p j := by
  have e : ∀ p q, (if p = q then (0 : Matrix ι ι ℝ) else vecMulVec (M p) (M q)) i j =
      if p = q then 0 else M p i * M q j := fun p q => by
    split_ifs <;> simp [vecMulVec_apply]
  simp only [esymm2Form, Matrix.sum_apply, e, sum_ite_eq_zero_else, sum_sub_distrib, sum_mul,
    mul_sum]
  congr 1
  exact Finset.sum_comm

theorem esymm2Form_eq (M : κ → ι → ℝ) :
    esymm2Form M = vecMulVec (∑ p, M p) (∑ p, M p) - ∑ p, vecMulVec (M p) (M p) := by
  ext i j
  rw [esymm2Form_apply]
  simp [Matrix.sum_apply, vecMulVec_apply, Finset.sum_apply]

/-- **The second elementary symmetric form of nonnegative linear forms is Lorentzian**: rank one
minus positive semidefinite. -/
theorem isLorentzian_esymm2Form {M : κ → ι → ℝ} (hM : ∀ p i, 0 ≤ M p i) :
    IsLorentzian (esymm2Form M) := by
  have hsymm : (esymm2Form M).IsSymm := Matrix.IsSymm.ext fun i j => by
    simp only [esymm2Form, Matrix.sum_apply]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by
      by_cases h : q = p
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]; simp [vecMulVec_apply, mul_comm]
  refine ⟨hsymm, fun i j => ?_, ?_⟩
  · simp only [esymm2Form, Matrix.sum_apply]
    exact sum_nonneg fun p _ => sum_nonneg fun q _ => by
      split_ifs
      · simp
      · simp only [vecMulVec_apply]; exact mul_nonneg (hM p i) (hM q j)
  · have e := esymm2Form_eq M
    set S := ∑ p, M p
    set N : Matrix ι ι ℝ := -∑ p, vecMulVec (M p) (M p)
    have hN : N.IsSymm := by
      refine Matrix.IsSymm.ext fun i j => ?_
      simp [N, Matrix.sum_apply, vecMulVec_apply, mul_comm]
    have hneg : ∀ x, qf N x ≤ 0 := fun x => by
      have : qf N x = -∑ p, (M p ⬝ᵥ x) ^ 2 := by
        simp only [N, qf, bil, neg_mulVec, dotProduct_neg, sum_mulVec, dotProduct_sum,
          vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        congr 1
        exact sum_congr rfl fun p _ => by rw [dotProduct_comm x (M p)]; ring
      rw [this]
      exact neg_nonpos.mpr (sum_nonneg fun _ _ => sq_nonneg _)
    have := isHyperbolic_rankOne_add hN S hneg
    rwa [show vecMulVec S S + N = esymm2Form M by rw [e]; simp [N, sub_eq_add_neg]] at this

/-- The Hessian of `y ↦ ∏_p ⟨L_p, y⟩` (product rule): `Σ_{p≠q} (∏_{r≠p,q} ⟨L_r, y⟩) L_p L_qᵀ`. -/
def eulerHessian (L : κ → ι → ℝ) (y : ι → ℝ) : Matrix ι ι ℝ :=
  ∑ p, ∑ q, if p = q then 0 else
    (∏ r ∈ (univ.erase p).erase q, (L r ⬝ᵥ y)) • vecMulVec (L p) (L q)

/-- **The Euler product closure is Lorentzian for every nonnegative local datum.** At a point where
every local factor is positive, the Hessian of `∏_p ⟨L_p, y⟩` is
`(∏_r ⟨L_r, y⟩) · esymm2(L_p/⟨L_p, y⟩)`. -/
theorem isLorentzian_eulerHessian {L : κ → ι → ℝ} (hL : ∀ p i, 0 ≤ L p i) {y : ι → ℝ}
    (hy : ∀ p, 0 < L p ⬝ᵥ y) : IsLorentzian (eulerHessian L y) := by
  set c : κ → ℝ := fun r => L r ⬝ᵥ y
  set C := ∏ r, c r with hCdef
  have hC : 0 < C := prod_pos fun r _ => hy r
  have hprod : ∀ p q, p ≠ q → ∏ r ∈ (univ.erase p).erase q, c r = C / (c p * c q) := by
    intro p q hpq
    have hq : q ∈ univ.erase p := mem_erase.mpr ⟨Ne.symm hpq, mem_univ q⟩
    have e1 := Finset.mul_prod_erase (univ.erase p) c hq
    have e2 := Finset.mul_prod_erase univ c (mem_univ p)
    have hcp := (hy p).ne'
    have hcq := (hy q).ne'
    rw [eq_div_iff (mul_ne_zero hcp hcq), hCdef, ← e2, ← e1]
    ring
  have e : eulerHessian L y = C • esymm2Form (fun p => (c p)⁻¹ • L p) := by
    simp only [eulerHessian, esymm2Form, smul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    split_ifs with hpq
    · simp
    · rw [hprod p q hpq]
      ext i j
      simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      have hcp := (hy p).ne'
      have hcq := (hy q).ne'
      field_simp
  rw [e]
  obtain ⟨hs, hnn, hh⟩ := isLorentzian_esymm2Form (M := fun p => (c p)⁻¹ • L p)
    (fun p i => mul_nonneg (inv_nonneg.mpr (hy p).le) (hL p i))
  refine ⟨hs.smul _, fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul]; exact mul_nonneg hC.le (hnn i j), ?_⟩
  intro x z hx
  have hq : ∀ v w, bil (C • esymm2Form fun p => (c p)⁻¹ • L p) v w =
      C * bil (esymm2Form fun p => (c p)⁻¹ • L p) v w := fun v w => by
    simp only [bil, smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp only [qf, hq] at hx ⊢
  have hx' : 0 < bil (esymm2Form fun p => (c p)⁻¹ • L p) x x :=
    pos_of_mul_pos_right hx hC.le
  have := hh x z hx'
  simp only [qf] at this
  nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg C)]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
