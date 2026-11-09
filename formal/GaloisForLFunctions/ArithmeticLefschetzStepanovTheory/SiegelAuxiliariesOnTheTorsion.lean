import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFrobeniusOfTheTorsionIsGalois
import Mathlib.NumberTheory.SiegelsLemma

/-!
# Siegel auxiliaries on the torsion

The tool Stepanov's construction needs first: integer auxiliaries of controlled height that vanish
exactly where the Frobenius acts exactly. Here the exact points are closed torsion points of the
prime torus.

For exponent vectors `α` in a finite set `S` and a torsion point `μ^b` of order `m`,
`F(μ^b) = Σ_α c_α μ^{b·α} = Σ_{r < m} C_r μ^r` with **class sums** `C_r = Σ_{b·α ≡ r} c_α`
(`aeval_torsionPoint_auxOf`). If all class sums are equal, `F` vanishes at every primitive `μ`, i.e.
on the whole closed point (`aeval_torsionPoint_eq_zero_of_classSum`), since `Σ_{r<m} μ^r = 0`.
These are `m − 1` integer linear conditions with coefficients in `{−1, 0, 1}`.

**Siegel's lemma on smooth numbers** (`exists_siegel_auxiliary`). For closed points of orders
`m_1, …, m_L` and any `S` with `M = Σ (m_i − 1) < |S|` there is a nonzero integer auxiliary on `S`
with `|c_α| ≤ |S|^{M/(|S| − M)}` vanishing on all of them. On the prime torus it is a `P`-smooth
integer Dirichlet polynomial, and at every `δ`-return to one of its torsion points it is at most
`δ L(F)` (`norm_orbitValue_le_of_siegel`): exact vanishing on the torus is approximate vanishing at
every return, at a precision linear in `δ`.
-/

open Finset Matrix

attribute [local instance] Matrix.seminormedAddCommGroup

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ : Type*}

/-- The pairing `b·α = Σ_i b_i α_i`. -/
def pairing [Fintype σ] (b : σ → ℕ) (α : σ →₀ ℕ) : ℕ := ∑ i, b i * α i

/-- The auxiliary with coefficients `c` on the exponent vectors `S`. -/
def auxOf (S : Finset (σ →₀ ℕ)) (c : S → ℤ) : MvPolynomial σ ℤ :=
  ∑ α : S, MvPolynomial.monomial α.1 (c α)

theorem coeff_auxOf (S : Finset (σ →₀ ℕ)) (c : S → ℤ) (α : S) :
    (auxOf S c).coeff α.1 = c α := by
  classical
  rw [auxOf, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
  · simp
  · intro β _ hβ
    rw [MvPolynomial.coeff_monomial, if_neg (fun h => hβ (Subtype.ext h))]
  · intro h; exact absurd (mem_univ α) h

theorem auxOf_ne_zero {S : Finset (σ →₀ ℕ)} {c : S → ℤ} (hc : c ≠ 0) : auxOf S c ≠ 0 := by
  obtain ⟨α, hα⟩ := Function.ne_iff.mp hc
  intro h
  apply hα
  rw [← coeff_auxOf S c α, h, MvPolynomial.coeff_zero]
  rfl

theorem aeval_torsionPoint_auxOf [Fintype σ] (S : Finset (σ →₀ ℕ)) (c : S → ℤ) (μ : ℂ)
    (b : σ → ℕ) :
    MvPolynomial.aeval (torsionPoint μ b) (auxOf S c) = ∑ α : S, (c α : ℂ) * μ ^ pairing b α := by
  rw [auxOf, map_sum]
  refine sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial, algebraMap_int_eq, eq_intCast]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), pairing, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun i _ => ?_
  rw [torsionPoint, ← pow_mul]

/-- The class sum `C_r = Σ_{b·α ≡ r (mod m)} c_α`. -/
def classSum [Fintype σ] (S : Finset (σ →₀ ℕ)) (c : S → ℤ) (m : ℕ) (b : σ → ℕ) (r : ℕ) : ℤ :=
  ∑ α ∈ (univ : Finset S).filter (fun α => pairing b α.1 % m = r), c α

/-- **Equal class sums kill the closed point.** -/
theorem aeval_torsionPoint_eq_zero_of_classSum [Fintype σ] (S : Finset (σ →₀ ℕ)) (c : S → ℤ)
    {m : ℕ} (hm : 1 < m) (b : σ → ℕ) (hC : ∀ r < m, classSum S c m b r = classSum S c m b 0)
    {μ : ℂ} (hμ : μ ∈ primitiveRoots m ℂ) :
    MvPolynomial.aeval (torsionPoint μ b) (auxOf S c) = 0 := by
  classical
  have hμ' : IsPrimitiveRoot μ m := (mem_primitiveRoots (by omega)).mp hμ
  rw [aeval_torsionPoint_auxOf]
  have hmod : ∀ α : S, μ ^ pairing b α = μ ^ (pairing b α % m) := fun α => by
    conv_lhs => rw [← Nat.div_add_mod (pairing b α) m, pow_add, pow_mul, hμ'.pow_eq_one, one_pow,
      one_mul]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := (univ : Finset S)) (t := range m)
    (g := fun α : S => pairing b α % m) (fun α _ => mem_range.mpr (Nat.mod_lt _ (by omega)))
    (fun α : S => (c α : ℂ) * μ ^ pairing b α)
  rw [← hfib]
  have hrow : ∀ r ∈ range m, (∑ α ∈ (univ : Finset S).filter (fun α => pairing b α.1 % m = r),
      (c α : ℂ) * μ ^ pairing b α.1) = (classSum S c m b 0 : ℂ) * μ ^ r := by
    intro r hr
    rw [← hC r (mem_range.mp hr), classSum, Int.cast_sum, sum_mul]
    refine sum_congr rfl fun α hα => ?_
    rw [hmod α, (mem_filter.mp hα).2]
  rw [sum_congr rfl hrow, ← mul_sum, hμ'.geom_sum_eq_zero hm, mul_zero]

/-- The condition matrix: row `(i, r)` is `C_{r+1} − C_0` for the `i`-th closed point. -/
def classMatrix [Fintype σ] (S : Finset (σ →₀ ℕ)) {L : ℕ} (T : Fin L → ℕ × (σ → ℕ)) :
    Matrix (Σ i : Fin L, Fin ((T i).1 - 1)) S ℤ :=
  fun x α => (if pairing (T x.1).2 α % (T x.1).1 = x.2.1 + 1 then 1 else 0) -
    (if pairing (T x.1).2 α % (T x.1).1 = 0 then 1 else 0)

theorem norm_classMatrix_le [Fintype σ] (S : Finset (σ →₀ ℕ)) {L : ℕ}
    (T : Fin L → ℕ × (σ → ℕ)) : ‖classMatrix S T‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  intro x α
  simp only [classMatrix]
  split_ifs with h1 h2 <;> simp_all

theorem classMatrix_mulVec [Fintype σ] (S : Finset (σ →₀ ℕ)) {L : ℕ} (T : Fin L → ℕ × (σ → ℕ))
    (c : S → ℤ) (x : Σ i : Fin L, Fin ((T i).1 - 1)) :
    (classMatrix S T *ᵥ c) x = classSum S c (T x.1).1 (T x.1).2 (x.2.1 + 1) -
      classSum S c (T x.1).1 (T x.1).2 0 := by
  simp only [mulVec, dotProduct, classMatrix, classSum, sub_mul, sum_sub_distrib, ite_mul,
    one_mul, zero_mul, sum_ite, sum_const_zero, add_zero]

/-- **Siegel's lemma on smooth numbers.** For closed torsion points of orders `m_i > 1` and a set
`S` of exponent vectors with `M = Σ (m_i − 1) < |S|`, there is a nonzero integer auxiliary on `S`
with `|c_α| ≤ |S|^{M/(|S| − M)}` vanishing on every one of the closed points. -/
theorem exists_siegel_auxiliary [Fintype σ] (S : Finset (σ →₀ ℕ)) {L : ℕ}
    (T : Fin L → ℕ × (σ → ℕ)) (hT : ∀ i, 1 < (T i).1)
    (hM0 : 0 < ∑ i, ((T i).1 - 1)) (hMS : ∑ i, ((T i).1 - 1) < S.card) :
    ∃ c : S → ℤ, c ≠ 0 ∧
      (∀ α, (|c α| : ℝ) ≤ (S.card : ℝ) ^ ((∑ i, ((T i).1 - 1) : ℕ) /
        ((S.card : ℝ) - (∑ i, ((T i).1 - 1) : ℕ)))) ∧
      ∀ i, ∀ μ ∈ primitiveRoots (T i).1 ℂ,
        MvPolynomial.aeval (torsionPoint μ (T i).2) (auxOf S c) = 0 := by
  classical
  have hcardι : Fintype.card (Σ i : Fin L, Fin ((T i).1 - 1)) = ∑ i, ((T i).1 - 1) := by
    simp
  have hcardS : Fintype.card S = S.card := Fintype.card_coe S
  obtain ⟨c, hc0, hc, hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le (classMatrix S T)
    (by rw [hcardι, hcardS]; exact hMS) (by rw [hcardι]; exact hM0)
  refine ⟨c, hc0, fun α => ?_, fun i μ hμ => ?_⟩
  · have h1 : max 1 ‖classMatrix S T‖ = 1 := max_eq_left (norm_classMatrix_le S T)
    rw [h1, mul_one, hcardι, hcardS] at hnorm
    have := (norm_le_pi_norm c α).trans hnorm
    rwa [Int.norm_eq_abs] at this
  · refine aeval_torsionPoint_eq_zero_of_classSum S c (hT i) (T i).2 (fun r hr => ?_) hμ
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rfl
    have hrow := congrFun hc ⟨i, ⟨r - 1, by omega⟩⟩
    rw [classMatrix_mulVec, Pi.zero_apply, sub_eq_zero] at hrow
    simpa [Nat.sub_add_cancel hr0] using hrow

/-- **Exact on the torus, approximate at every return.** A Siegel auxiliary vanishing at `μ^b` is
at most `δ L(F)` at every `δ`-return to `μ^b`. -/
theorem norm_orbitValue_le_of_siegel {P : Finset Nat.Primes} (F : MvPolynomial P ℤ) {μ : ℂ}
    (hμ : ‖μ‖ = 1) (b : P → ℕ) (hF : MvPolynomial.aeval (torsionPoint μ b) F = 0) {t δ : ℝ}
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ) : ‖orbitValue F t‖ ≤ δ * lipWeight F := by
  have hv : ∀ p, ‖torsionPoint μ b p‖ ≤ 1 := fun p => by
    rw [torsionPoint, norm_pow, hμ, one_pow]
  have h := norm_aeval_sub_le F (u := orbitPoint P t) (fun p => (InfiniteRankWeilTheory.norm_phase _ _).le)
    hv hret
  rw [hF, sub_zero] at h
  rw [orbitValue, mul_comm]
  exact h

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
