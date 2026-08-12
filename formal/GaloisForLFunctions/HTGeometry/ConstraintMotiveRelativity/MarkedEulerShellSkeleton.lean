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
  ring

/-- **`(ESG.8)`.**  The Weil tangent coefficient is a second shell jet. -/
theorem weilCoeff_eq_shellJet {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    weilCoeff p = -(shellJet m 2 (p ^ m)) / ((m : ℝ) ^ 2 * Real.sqrt p) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [weilCoeff, shellJet_prime_pow hp m 2]
  field_simp
  ring

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
  ring

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
  nlinarith [hsign, sq_nonneg ((Real.log p) ^ (r + 2))]

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
  calc ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), c i * c j * shellMoment F ((i : ℕ) + (j : ℕ))
      = ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), ∑ p ∈ F,
          primeWeight p * ((c i * (Real.log p) ^ (i : ℕ)) * (c j * (Real.log p) ^ (j : ℕ))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [shellMoment, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p hp => hterm p hp i j
    _ = ∑ p ∈ F, primeWeight p * (∑ i : Fin (R + 1), c i * (Real.log p) ^ (i : ℕ)) ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

end Moments

end HTGeometry.ConstraintMotiveRelativity
