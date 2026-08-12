import Mathlib
import GaloisForLFunctions.RHTower.HighExponentShellZeroFree

/-!
# The marked Euler shell: pure-prime skeleton and moment object

The high-exponent shell mark `a_m = 1_{M_max = m}` is one on every pure `m`-th prime power.  The
diagonal prolongation `L = -δ` therefore reads off every prime logarithm from the marked skeleton,
and the prime Mass half-density coefficient, the reflection-odd Weil tangent coefficient and the
prime phase are all shell jets at `p^m`.

The associated moment object is the weighted prime-log Hankel block.  Its quadratic form is a
positive weighted sum of squares of polynomial values at the distinct nodes `log p`, so its rank is
`min(R+1, |F|)`, and a truncated moment face does not determine its successor among positive
atomic sources.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open RHTower
open scoped Matrix

section Skeleton

/-- **`(ESG.2)`.**  The shell mark is one on every pure `m`-th prime power. -/
theorem shellIndicator_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    shellIndicator m (p ^ m) = 1 := by
  rw [shellIndicator_eq_one_iff]
  refine ⟨fun q hq hdvd => ?_, fun h => h p hp dvd_rfl⟩
  have hqdvd : q ∣ p ^ m := (dvd_pow_self q (Nat.succ_ne_zero m)).trans hdvd
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)
  subst hqp
  have hle : m + 1 ≤ m := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvd
  omega

/-- **`(ESG.1)`, `(ESG.2)`.**  The diagonal prolongation `L = -δ` applied `k` times to the shell
mark. -/
noncomputable def shellJet (m k n : ℕ) : ℝ := (-(Real.log n)) ^ k * (shellIndicator m n : ℝ)

/-- **`(ESG.4)`.**  Pure-power recovery: the shell jets at `p^m` are the powers of `-m log p`. -/
theorem shellJet_prime_pow {p : ℕ} (hp : p.Prime) (m k : ℕ) :
    shellJet m k (p ^ m) = (-((m : ℝ) * Real.log p)) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [shellJet, shellIndicator_prime_pow hp m]
  push_cast
  rw [Real.log_pow]
  ring

/-- **`(ESG.5)`.**  Each prime logarithm is recovered from the marked skeleton. -/
theorem log_eq_shellJet {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    Real.log p = -(shellJet m 1 (p ^ m)) / m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [shellJet_prime_pow hp m 1, pow_one]
  field_simp

/-- **`(ESG.6)`.**  The prime Mass half-density coefficient. -/
noncomputable def massCoeff (p : ℕ) : ℝ := Real.log p / Real.sqrt p

/-- **`(ESG.6)`.**  The positive-location coefficient of the reflection-odd Weil tangent. -/
noncomputable def weilCoeff (p : ℕ) : ℝ := -(Real.log p) ^ 2 / Real.sqrt p

/-- **`(ESG.7)`.**  The Mass coefficient is a first shell jet. -/
theorem massCoeff_eq_shellJet {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    massCoeff p = -(shellJet m 1 (p ^ m)) / (m * Real.sqrt p) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [massCoeff, shellJet_prime_pow hp m 1, pow_one]
  field_simp

/-- **`(ESG.8)`.**  The Weil tangent coefficient is a second shell jet. -/
theorem weilCoeff_eq_shellJet {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    weilCoeff p = -(shellJet m 2 (p ^ m)) / ((m : ℝ) ^ 2 * Real.sqrt p) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [weilCoeff, shellJet_prime_pow hp m 2]
  field_simp

/-- **`(ESG.9)`.**  The prime phase is the exponential of a first shell jet. -/
theorem primePhase_eq_shellJet {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) (t : ℝ) :
    Complex.exp (-(Complex.I * (t * Real.log p)))
      = Complex.exp (Complex.I * (t / m) * (shellJet m 1 (p ^ m) : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmc : ((m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm0
  congr 1
  rw [shellJet_prime_pow hp m 1, pow_one]
  push_cast
  field_simp

end Skeleton

/-! ### The finite prime chart and restriction naturality -/

section FiniteChart

variable {E F : Finset ℕ}

/-- **`(ESG.6)`.**  The diagonal prime-log operator of a finite prime chart. -/
noncomputable def chartDiag (F : Finset ℕ) (v : ↥F → ℂ) : ↥F → ℂ :=
  fun p => (Real.log p : ℂ) * v p

/-- **`(ESG.6)`.**  The Mass vector of a finite prime chart. -/
noncomputable def chartMass (F : Finset ℕ) : ↥F → ℂ := fun p => (massCoeff p : ℂ)

/-- **`(ESG.6)`.**  The prime clock flow of a finite prime chart. -/
noncomputable def chartFlow (F : Finset ℕ) (t : ℝ) (v : ↥F → ℂ) : ↥F → ℂ :=
  fun p => Complex.exp (-(Complex.I * ((t * Real.log p : ℝ) : ℂ))) * v p

/-- **`(ESG.6)`.**  The logarithmic history of a finite prime chart. -/
noncomputable def chartHistory (F : Finset ℕ) (t : ℝ) : ↥F → ℂ :=
  fun p => ((-t * Real.log p : ℝ) : ℂ)

/-- Coordinate restriction between finite prime charts. -/
def chartRestrict (h : E ⊆ F) (v : ↥F → ℂ) : ↥E → ℂ := fun p => v ⟨p, h p.2⟩

theorem chartRestrict_diag (h : E ⊆ F) (v : ↥F → ℂ) :
    chartRestrict h (chartDiag F v) = chartDiag E (chartRestrict h v) := rfl

theorem chartRestrict_mass (h : E ⊆ F) : chartRestrict h (chartMass F) = chartMass E := rfl

theorem chartRestrict_flow (h : E ⊆ F) (t : ℝ) (v : ↥F → ℂ) :
    chartRestrict h (chartFlow F t v) = chartFlow E t (chartRestrict h v) := rfl

theorem chartRestrict_history (h : E ⊆ F) (t : ℝ) :
    chartRestrict h (chartHistory F t) = chartHistory E t := rfl

theorem chartRestrict_comp {D : Finset ℕ} (hDE : D ⊆ E) (hEF : E ⊆ F) (v : ↥F → ℂ) :
    chartRestrict hDE (chartRestrict hEF v) = chartRestrict (hDE.trans hEF) v := rfl

end FiniteChart

/-! ### The Mass/Weil moment object -/

section Moments

/-- **`(ESG.10)`.**  The prime-log moment of a finite prime chart. -/
noncomputable def shellMoment (F : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ p ∈ F, (Real.log p) ^ (r + 2) / p

/-- **`(ESG.11)`.**  The moment object is a shell-jet sum. -/
theorem shellMoment_eq_shellJet (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) {m : ℕ} (hm : m ≠ 0)
    (r : ℕ) :
    shellMoment F r
      = ((-1 : ℝ) ^ r / (m : ℝ) ^ (r + 2)) * ∑ p ∈ F, shellJet m (r + 2) (p ^ m) / p := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [shellMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [shellJet_prime_pow (hF p hp) m (r + 2)]
  have hexp : (-((m : ℝ) * Real.log p)) ^ (r + 2)
      = (-1 : ℝ) ^ (r + 2) * (m : ℝ) ^ (r + 2) * (Real.log p) ^ (r + 2) := by
    rw [neg_pow, mul_pow]
    ring
  rw [hexp]
  have hsign : (-1 : ℝ) ^ r * (-1 : ℝ) ^ (r + 2) = 1 := by
    rw [← pow_add]
    rw [show r + (r + 2) = 2 * r + 2 by ring, pow_add, pow_mul]
    norm_num
  field_simp
  rw [mul_assoc, hsign, mul_one]

/-- The positive prime weight `(log p)²/p`. -/
noncomputable def primeWeight (p : ℕ) : ℝ := (Real.log p) ^ 2 / p

theorem primeWeight_pos {p : ℕ} (hp : p.Prime) : 0 < primeWeight p := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2 : 0 < Real.log p := Real.log_pos h1
  have h3 : (0 : ℝ) < p := by linarith
  rw [primeWeight]
  positivity

/-- **`(ESG.13)`.**  The moment Hankel form is the weighted sum of squares of polynomial values at
the prime-log nodes. -/
theorem hankel_quadratic (F : Finset ℕ) (R : ℕ) (c : Fin (R + 1) → ℝ) :
    ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), c i * c j * shellMoment F ((i : ℕ) + (j : ℕ))
      = ∑ p ∈ F, primeWeight p * (∑ i : Fin (R + 1), c i * (Real.log p) ^ (i : ℕ)) ^ 2 := by
  have hterm : ∀ p ∈ F, ∀ i j : Fin (R + 1),
      c i * c j * ((Real.log p) ^ ((i : ℕ) + (j : ℕ) + 2) / p)
        = primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ))) := by
    intro p _ i j
    rw [primeWeight]
    rw [show (i : ℕ) + (j : ℕ) + 2 = ((i : ℕ) + (j : ℕ)) + 2 from rfl, pow_add, pow_add]
    ring
  have hexpand : ∀ i j : Fin (R + 1), c i * c j * shellMoment F ((i : ℕ) + (j : ℕ))
      = ∑ p ∈ F, primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ))) := by
    intro i j
    rw [shellMoment, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => hterm p hp i j
  have s1 : ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), ∑ p ∈ F,
        primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ)))
      = ∑ i : Fin (R + 1), ∑ p ∈ F, ∑ j : Fin (R + 1),
        primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have s2 : ∑ i : Fin (R + 1), ∑ p ∈ F, ∑ j : Fin (R + 1),
        primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ)))
      = ∑ p ∈ F, ∑ i : Fin (R + 1), ∑ j : Fin (R + 1),
        primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ))) :=
    Finset.sum_comm
  have s3 : ∀ p : ℕ, ∑ i : Fin (R + 1), ∑ j : Fin (R + 1),
        primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ)))
      = primeWeight p * (∑ i : Fin (R + 1), c i * (Real.log p) ^ (i : ℕ)) ^ 2 := by
    intro p
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hexpand i j)), s1, s2]
  exact Finset.sum_congr rfl fun p _ => s3 p

end Moments

/-! ### The Hankel block and its rank -/

section Hankel

/-- **`(ESG.12)`.**  The moment Hankel block through order `R`. -/
noncomputable def hankelBlock (F : Finset ℕ) (R : ℕ) : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ :=
  Matrix.of fun i j => shellMoment F ((i : ℕ) + (j : ℕ))

/-- The weighted Vandermonde factor of the Hankel block. -/
noncomputable def shellGram (F : Finset ℕ) (R : ℕ) : Matrix ↥F (Fin (R + 1)) ℝ :=
  Matrix.of fun p i => Real.sqrt (primeWeight (p : ℕ)) * (Real.log (p : ℕ)) ^ (i : ℕ)

theorem hankelBlock_eq_gram (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (R : ℕ) :
    hankelBlock F R = (shellGram F R)ᵀ * shellGram F R := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [hankelBlock, shellGram, Matrix.of_apply, Matrix.transpose_apply]
  rw [shellMoment, ← Finset.sum_coe_sort F]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsq : Real.sqrt (primeWeight (p : ℕ)) * Real.sqrt (primeWeight (p : ℕ))
      = primeWeight (p : ℕ) := Real.mul_self_sqrt (primeWeight_pos (hF _ p.2)).le
  calc (Real.log (p : ℕ)) ^ ((i : ℕ) + (j : ℕ) + 2) / (p : ℕ)
      = primeWeight (p : ℕ) * ((Real.log (p : ℕ)) ^ (i : ℕ) * (Real.log (p : ℕ)) ^ (j : ℕ)) := by
        rw [primeWeight, ← pow_add]
        rw [show (i : ℕ) + (j : ℕ) + 2 = ((i : ℕ) + (j : ℕ)) + 2 from rfl, pow_add]
        ring
    _ = (Real.sqrt (primeWeight (p : ℕ)) * (Real.log (p : ℕ)) ^ (i : ℕ))
          * (Real.sqrt (primeWeight (p : ℕ)) * (Real.log (p : ℕ)) ^ (j : ℕ)) := by
        rw [mul_mul_mul_comm, hsq]

/-- **`(ESG.12)`.**  The rank of the moment Hankel block is `min(R+1, |F|)`: the block is the Gram
matrix of a weighted Vandermonde system at the distinct prime-log nodes. -/
theorem rank_hankelBlock (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) (R : ℕ) :
    (hankelBlock F R).rank = min (R + 1) F.card := by
  classical
  rw [hankelBlock_eq_gram F hF R, Matrix.rank_transpose_mul_self]
  refine le_antisymm (le_min ?_ ?_) ?_
  · simpa using Matrix.rank_le_card_width (shellGram F R)
  · simpa [Fintype.card_coe] using Matrix.rank_le_card_height (shellGram F R)
  · have hk1 : min (R + 1) F.card ≤ R + 1 := min_le_left _ _
    have hk2 : min (R + 1) F.card ≤ Fintype.card ↥F := by
      rw [Fintype.card_coe]; exact min_le_right _ _
    set k := min (R + 1) F.card with hkdef
    set row : Fin k → ↥F := fun i => (Fintype.equivFin ↥F).symm (Fin.castLE hk2 i) with hrow
    have hrowinj : Function.Injective row := fun a b hab =>
      Fin.castLE_injective hk2 ((Fintype.equivFin ↥F).symm.injective hab)
    set S := (shellGram F R).submatrix row (Fin.castLE hk1) with hS
    have hSapply : ∀ i j : Fin k,
        S i j = Real.sqrt (primeWeight ((row i : ↥F) : ℕ))
          * (Real.log ((row i : ↥F) : ℕ)) ^ (j : ℕ) := fun i j => rfl
    have hST : Sᵀ = Matrix.of (fun j i => Real.sqrt (primeWeight ((row i : ↥F) : ℕ))
        * (Matrix.vandermonde (fun i => Real.log ((row i : ↥F) : ℕ)))ᵀ j i) := by
      ext j i
      rw [Matrix.transpose_apply, hSapply]
      simp [Matrix.vandermonde]
    have hdetS : S.det = (∏ i, Real.sqrt (primeWeight ((row i : ↥F) : ℕ)))
        * (Matrix.vandermonde (fun i => Real.log ((row i : ↥F) : ℕ))).det := by
      rw [← Matrix.det_transpose S, hST, Matrix.det_mul_row, Matrix.det_transpose]
    have hprod : (∏ i, Real.sqrt (primeWeight ((row i : ↥F) : ℕ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        (Real.sqrt_pos.mpr (primeWeight_pos (hF _ (row i).2))).ne'
    have hnodes : Function.Injective (fun i => Real.log ((row i : ↥F) : ℕ)) := by
      intro a b hab
      have hpos : ∀ i : Fin k, (0 : ℝ) < (((row i : ↥F) : ℕ) : ℝ) := fun i => by
        exact_mod_cast (hF _ (row i).2).pos
      have h1 := Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos a)) (Set.mem_Ioi.mpr (hpos b)) hab
      have h2 : ((row a : ↥F) : ℕ) = ((row b : ↥F) : ℕ) := by exact_mod_cast h1
      exact hrowinj (Subtype.ext h2)
    have hvdm : (Matrix.vandermonde (fun i => Real.log ((row i : ↥F) : ℕ))).det ≠ 0 := by
      rw [Matrix.det_vandermonde]
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
      exact sub_ne_zero.mpr fun h => hij (hnodes h).symm
    have hdet : S.det ≠ 0 := by rw [hdetS]; exact mul_ne_zero hprod hvdm
    have hrankS : S.rank = k := by
      rw [Matrix.rank_of_isUnit S ((Matrix.isUnit_iff_isUnit_det S).mpr
        (isUnit_iff_ne_zero.mpr hdet)), Fintype.card_fin]
    calc k = S.rank := hrankS.symm
      _ ≤ (shellGram F R).rank := Matrix.rank_submatrix_le _ _ _

end Hankel

/-! ### Successor nonuniqueness of a truncated moment face -/

section Successor

/-- **`(ESG.12)`.**  A truncated moment face through order `2R` does not determine the successor
moment among positive atomic sources: two positive weight systems on the same `2R+2` distinct nodes
share every moment through `2R` and differ at `2R+1`.  The perturbation is the preimage of the last
coordinate vector under the invertible full Vandermonde system. -/
theorem exists_positive_moment_ambiguity (R : ℕ) (x : Fin (2 * R + 2) → ℝ)
    (hx : Function.Injective x) :
    ∃ w₁ w₂ : Fin (2 * R + 2) → ℝ, (∀ j, 0 < w₁ j) ∧ (∀ j, 0 < w₂ j) ∧
      (∀ r : Fin (2 * R + 1), ∑ j, w₁ j * x j ^ (r : ℕ) = ∑ j, w₂ j * x j ^ (r : ℕ)) ∧
      ∑ j, w₁ j * x j ^ (2 * R + 1) ≠ ∑ j, w₂ j * x j ^ (2 * R + 1) := by
  classical
  set A : Matrix (Fin (2 * R + 2)) (Fin (2 * R + 2)) ℝ := (Matrix.vandermonde x)ᵀ with hA
  have hdet : IsUnit A.det := by
    refine isUnit_iff_ne_zero.mpr ?_
    rw [hA, Matrix.det_transpose, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun h => (Finset.mem_Ioi.mp hj).ne' (hx h)
  set e : Fin (2 * R + 2) → ℝ := Pi.single (Fin.last (2 * R + 1)) 1 with he
  set c : Fin (2 * R + 2) → ℝ := A⁻¹.mulVec e with hc
  have hAc : A.mulVec c = e := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hrow : ∀ r : Fin (2 * R + 2), ∑ j, c j * x j ^ (r : ℕ) = e r := by
    intro r
    have h : (∑ j, A r j * c j) = e r := congrFun hAc r
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hA, Matrix.transpose_apply, Matrix.vandermonde_apply, mul_comm]
  have hcvan : ∀ r : Fin (2 * R + 1), ∑ j, c j * x j ^ (r : ℕ) = 0 := by
    intro r
    have hne : (Fin.castSucc r) ≠ Fin.last (2 * R + 1) := Fin.castSucc_lt_last r |>.ne
    have := hrow (Fin.castSucc r)
    rw [he, Pi.single_apply, if_neg hne] at this
    simpa using this
  have hclast : ∑ j, c j * x j ^ (2 * R + 1) = 1 := by
    have := hrow (Fin.last (2 * R + 1))
    rw [he, Pi.single_apply, if_pos rfl] at this
    simpa using this
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ j, |c j| ≤ M :=
    ⟨Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ (fun j => |c j|),
      fun j => Finset.le_sup' (fun j => |c j|) (Finset.mem_univ j)⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (c 0)) (hM 0)
  set ε : ℝ := (2 * (M + 1))⁻¹ with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hsmall : ∀ j, |ε * c j| < 1 := by
    intro j
    rw [abs_mul, abs_of_pos hεpos, hε, inv_mul_eq_div, div_lt_one (by positivity)]
    linarith [hM j]
  refine ⟨fun j => 1 + ε * c j, fun j => 1 - ε * c j, fun j => ?_, fun j => ?_, fun r => ?_, ?_⟩
  · have h := abs_lt.mp (hsmall j); linarith [h.1]
  · have h := abs_lt.mp (hsmall j); linarith [h.2]
  · have hdiff : ∑ j, (1 + ε * c j) * x j ^ (r : ℕ) - ∑ j, (1 - ε * c j) * x j ^ (r : ℕ)
        = (2 * ε) * ∑ j, c j * x j ^ (r : ℕ) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hcvan r, mul_zero] at hdiff
    linarith [hdiff]
  · have hdiff : ∑ j, (1 + ε * c j) * x j ^ (2 * R + 1)
        - ∑ j, (1 - ε * c j) * x j ^ (2 * R + 1)
        = (2 * ε) * ∑ j, c j * x j ^ (2 * R + 1) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hclast, mul_one] at hdiff
    intro heq
    rw [heq, sub_self] at hdiff
    have h2 : (0 : ℝ) < 2 * ε := by positivity
    linarith [hdiff]

end Successor

end HTGeometry.ConstraintMotiveRelativity
