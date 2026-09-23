import GaloisForLFunctions.HTGeometry.RankOneProjectionConjugation
import GaloisForLFunctions.HTGeometry.ProductStabilizerPhysicalScore

/-!
# The exact Haar value of the literal two-query score

For a pure state and a traceless Hermitian involution the normalized Haar mean square of the
expectation value is `1/(D+1)`, independently of the state and of the observable.  The corpus
computes that value on the index type `Fin 2 ⊕ Fin d` and for a prepared coordinate state; a
Hermitian idempotent of unit trace is such a preparation, and normalized Haar transfers across a
change of index type, so the value holds verbatim on a qubit register.

Averaging over the dictionary and over the product stabilizer samples changes nothing, so the
literal two-query score of a Haar unitary has expectation exactly `1/(2^n + 1)`.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-! ### Reindexing preserves the matrix structure used by the benchmark -/

theorem reindexAlgEquiv_entry (e : κ ≃ κ') (M : Matrix κ κ ℂ) (a b : κ) :
    Matrix.reindexAlgEquiv ℂ ℂ e M (e a) (e b) = M a b := by
  show M (e.symm (e a)) (e.symm (e b)) = M a b
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem reindexAlgEquiv_star (e : κ ≃ κ') (M : Matrix κ κ ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ e (star M) = star (Matrix.reindexAlgEquiv ℂ ℂ e M) := rfl

theorem reindexAlgEquiv_isHermitian (e : κ ≃ κ') {M : Matrix κ κ ℂ} (hM : M.IsHermitian) :
    (Matrix.reindexAlgEquiv ℂ ℂ e M).IsHermitian := by
  ext i j
  exact congrFun (congrFun hM (e.symm i)) (e.symm j)

theorem reindexAlgEquiv_trace (e : κ ≃ κ') (M : Matrix κ κ ℂ) :
    (Matrix.reindexAlgEquiv ℂ ℂ e M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  refine (Fintype.sum_equiv e _ _ fun a => ?_).symm
  simp only [Matrix.diag_apply]
  exact (reindexAlgEquiv_entry e M a a).symm

/-! ### The Haar mean square of a pure-state expectation -/

theorem continuous_preparedProbe (d : ℕ)
    (A : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
    (W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) (j : Fin 2 ⊕ Fin d) :
    Continuous fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
      (Complex.re ((star ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * A *
        ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) j j)) ^ (2 : ℕ) := by
  have hentry : ∀ a b : Fin 2 ⊕ Fin d,
      Continuous fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
        ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) a b := by
    intro a b
    have : ∀ U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ,
        ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) a b
          = ∑ c, (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) a c *
              (W : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) c b := by
      intro U; rfl
    simp only [this]
    exact continuous_finsetSum _ fun c _ =>
      (continuous_finiteUnitaryEntry a c).mul continuous_const
  have hprod : Continuous fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
      (star ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * A *
        ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) j j := by
    have hexp : ∀ U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ,
        (star ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
            Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * A *
          ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
            Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) j j
          = ∑ a, ∑ b, star
              (((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
                Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) b j) * A b a *
              ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
                Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) a j := by
      intro U
      simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
    simp only [hexp]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((continuous_star.comp (hentry b j)).mul continuous_const).mul (hentry a j)
  exact (Complex.continuous_re.comp hprod).pow 2

/-- **The exact Haar mean square on any finite register.**  For a pure state and a traceless
Hermitian involution the normalized Haar mean square of the expectation is `1/(D+1)`. -/
theorem haar_sq_trace_pure_state_conjugation
    (d : ℕ) (e : κ ≃ Fin 2 ⊕ Fin d)
    {ρ : Matrix κ κ ℂ} (hherm : ρ.IsHermitian) (hidem : ρ * ρ = ρ) (htr : ρ.trace = 1)
    {P : Matrix κ κ ℂ} (hP : P.IsHermitian) (hPtr : P.trace = 0) (hPinv : P * P = 1) :
    (∫ V : Matrix.unitaryGroup κ ℂ,
        (Matrix.trace (ρ * (star (V : Matrix κ κ ℂ) * P * (V : Matrix κ κ ℂ)))).re ^ (2 : ℕ)
        ∂finiteUnitaryHaar κ)
      = ((d : ℝ) + 3)⁻¹ := by
  classical
  obtain ⟨K, j, hK, hKeq⟩ := exists_unitary_trace_mul_eq_conj_entry hherm hidem htr
  set Ku : Matrix.unitaryGroup κ ℂ := ⟨K, hK⟩ with hKu
  set W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ := unitaryGroupReindex e Ku with hW
  set A : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ := Matrix.reindexAlgEquiv ℂ ℂ e P with hA
  have hfcont := continuous_preparedProbe d A W (e j)
  have htrans := integral_finiteUnitaryHaar_reindex e
    (fun U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ =>
      (Complex.re ((star ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * A *
        ((U * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) (e j) (e j))) ^ (2 : ℕ)) hfcont
  have hpoint : ∀ V : Matrix.unitaryGroup κ ℂ,
      (Complex.re ((star (((unitaryGroupReindex e V) * W :
            Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
            Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * A *
          (((unitaryGroupReindex e V) * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
            Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) (e j) (e j))) ^ (2 : ℕ)
        = (Matrix.trace (ρ * (star (V : Matrix κ κ ℂ) * P * (V : Matrix κ κ ℂ)))).re ^ (2 : ℕ) := by
    intro V
    have hVW : (((unitaryGroupReindex e V) * W : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
        Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
        = Matrix.reindexAlgEquiv ℂ ℂ e ((V : Matrix κ κ ℂ) * K) := by
      rw [hW, hKu]
      exact (map_mul (Matrix.reindexAlgEquiv ℂ ℂ e) (V : Matrix κ κ ℂ) K).symm
    rw [hVW, hA, ← reindexAlgEquiv_star, ← map_mul, ← map_mul, reindexAlgEquiv_entry]
    congr 2
    have hmat : star ((V : Matrix κ κ ℂ) * K) * P * ((V : Matrix κ κ ℂ) * K)
        = star K * (star (V : Matrix κ κ ℂ) * P * (V : Matrix κ κ ℂ)) * K := by
      rw [star_mul]
      simp only [Matrix.mul_assoc]
    rw [hmat, hKeq]
  simp only [hpoint] at htrans
  rw [htrans]
  have hbench := finiteUnitaryPreparedTracelessHermitianInvolutionHaarSignal_eq d A
    (reindexAlgEquiv_isHermitian e hP)
    (by rw [reindexAlgEquiv_trace]; exact hPtr)
    (by rw [hA, ← map_mul, hPinv, map_one])
    W (e j)
  exact hbench


/-! ### The Haar expectation of the literal two-query score -/

theorem continuous_sq_trace_conj (ρ P : Matrix κ κ ℂ) :
    Continuous fun V : Matrix.unitaryGroup κ ℂ =>
      (Matrix.trace (ρ * (star (V : Matrix κ κ ℂ) * P * (V : Matrix κ κ ℂ)))).re ^ (2 : ℕ) := by
  have htr : Continuous (Matrix.trace : Matrix κ κ ℂ → ℂ) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp (continuous_apply i)
  have hV : Continuous fun V : Matrix.unitaryGroup κ ℂ => (V : Matrix κ κ ℂ) :=
    continuous_subtype_val
  have hstar : Continuous fun V : Matrix.unitaryGroup κ ℂ => star (V : Matrix κ κ ℂ) :=
    continuous_star.comp hV
  have hmat : Continuous fun V : Matrix.unitaryGroup κ ℂ =>
      ρ * (star (V : Matrix κ κ ℂ) * P * (V : Matrix κ κ ℂ)) :=
    continuous_const.mul ((hstar.mul continuous_const).mul hV)
  exact (Complex.continuous_re.comp (htr.comp hmat)).pow 2

/-- **The exact Haar benchmark of the literal two-query score.**  A Haar unitary scores exactly
`1/(2^n + 1)` on the same randomized two-query experiment, for every nonidentity Pauli
dictionary. -/
theorem haar_literalTwoQueryScore_eq
    {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (label : ι → Fin n → Option (Fin 3))
    (hlabel : ∀ i, label i ≠ pauliIdentityLabel n) :
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        literalTwoQueryScore label
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n)))
      = 1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  classical
  have hcard : Fintype.card (FiniteQubitConfiguration (Fin n))
      = Fintype.card (Fin 2 ⊕ Fin (2 ^ n - 2)) := by
    have hpow : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simp only [FiniteQubitConfiguration, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_sum]
    omega
  set e : FiniteQubitConfiguration (Fin n) ≃ Fin 2 ⊕ Fin (2 ^ n - 2) :=
    Fintype.equivOfCardEq hcard with he
  have hterm : ∀ (i : ι) (smpl : Fin n → Fin 3 × Bool),
      (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        (Matrix.trace (productStabilizerDensity smpl *
          (star (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            finitePauliMatrix (label i) *
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))).re ^ (2 : ℕ)
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n)))
        = 1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
    intro i smpl
    have hpow : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ (1 : ℕ) := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [haar_sq_trace_pure_state_conjugation (2 ^ n - 2) e
      (productStabilizerDensity_isHermitian smpl)
      (productStabilizerDensity_mul_self smpl)
      (trace_productStabilizerDensity smpl)
      (finitePauliMatrix_isHermitian (label i))
      (finitePauliMatrix_trace_eq_zero_of_ne_identity (label i) (hlabel i))
      (finitePauliMatrix_mul_self (label i))]
    have hd3 : ((2 ^ n - 2 : ℕ) : ℝ) + 3 = ((2 ^ n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hpow]
      push_cast
      ring
    rw [hd3, one_div]
  have hcont : ∀ (i : ι) (smpl : Fin n → Fin 3 × Bool),
      Continuous fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
        (Matrix.trace (productStabilizerDensity smpl *
          (star (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            finitePauliMatrix (label i) *
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))).re ^ (2 : ℕ) :=
    fun i smpl => continuous_sq_trace_conj _ _
  simp only [literalTwoQueryScore]
  rw [integral_div, integral_finsetSum _ (fun i _ => by
    refine Integrable.div_const ?_ _
    exact integrable_finsetSum _ fun smpl _ =>
      integrable_finiteUnitaryHaar_of_continuous _ (hcont i smpl))]
  have hinner : ∀ i : ι,
      (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        (∑ smpl : Fin n → Fin 3 × Bool,
          (Matrix.trace (productStabilizerDensity smpl *
            (star (V : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) *
              finitePauliMatrix (label i) *
              (V : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)))).re ^ (2 : ℕ))
          / ((6 : ℝ) ^ Fintype.card (Fin n))
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n)))
        = 1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
    intro i
    rw [integral_div, integral_finsetSum _ (fun smpl _ =>
      integrable_finiteUnitaryHaar_of_continuous _ (hcont i smpl))]
    rw [Finset.sum_congr rfl fun smpl _ => hterm i smpl]
    rw [Finset.sum_const, Finset.card_univ]
    have hcardsmpl : (Fintype.card (Fin n → Fin 3 × Bool) : ℝ)
        = (6 : ℝ) ^ Fintype.card (Fin n) := by
      simp
    rw [nsmul_eq_mul, hcardsmpl]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hinner i]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hM : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast this
  field_simp

end

end GaloisForLFunctions.HTGeometry
