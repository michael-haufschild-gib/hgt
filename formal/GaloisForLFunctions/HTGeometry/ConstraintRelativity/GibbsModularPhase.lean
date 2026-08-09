import Mathlib
import GaloisForLFunctions.Core
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity

/-!
# The finite-prime Gibbs modular phase clock

The modular flow of a faithful Gibbs state on a finite matrix algebra acts on the matrix unit
`E_{i0}` by the phase of the eigenvalue ratio.  With Gibbs weights `p_i^{-β}` the orbit of the
framed vector `∑ (log p_i) E_{i0}` is the arithmetic phase clock `(log p_i) p_i^{it}`, and the
framed two-copy quadratic reader on that orbit is the subdiscriminant of the phase vector.

Three points on concentric circles are a zero of the subdiscriminant exactly when they form an
equilateral triangle, which the triangle inequality on the radii makes possible; Kronecker density
of the prime phase flow then brings the reader arbitrarily close to zero.
-/

open scoped BigOperators

open GaloisForLFunctions

namespace HTGeometry.ConstraintRelativity

/-! ## Conjugating a matrix unit by diagonal matrices -/

section MatrixUnits

variable {n : Type*} [DecidableEq n] [Fintype n]

theorem diagonal_mul_single_mul_diagonal (d e : n → ℂ) (i j : n) (a : ℂ) :
    Matrix.diagonal d * Matrix.single i j a * Matrix.diagonal e
      = Matrix.single i j (d i * a * e j) := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hk : k = i
  · subst hk
    by_cases hl : l = j
    · subst hl; simp
    · simp [Ne.symm hl]
  · simp [Ne.symm hk]

end MatrixUnits

/-! ## The Gibbs state and its modular flow -/

section Gibbs

variable {N : ℕ}

/-- The unnormalized Gibbs weights: `1` at the reference index, `p_i^{-β}` elsewhere. -/
noncomputable def gibbsWeight (p : Fin N → ℝ) (β : ℝ) : Option (Fin N) → ℝ :=
  fun i => i.elim 1 fun j => (p j) ^ (-β)

@[simp] theorem gibbsWeight_none (p : Fin N → ℝ) (β : ℝ) : gibbsWeight p β none = 1 := rfl

@[simp] theorem gibbsWeight_some (p : Fin N → ℝ) (β : ℝ) (j : Fin N) :
    gibbsWeight p β (some j) = (p j) ^ (-β) := rfl

theorem gibbsWeight_pos {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) (β : ℝ) (i : Option (Fin N)) :
    0 < gibbsWeight p β i := by
  cases i with
  | none => simp
  | some j => simpa using Real.rpow_pos_of_pos (hp j) (-β)

/-- **Card `(1)`.**  The Gibbs partition function. -/
noncomputable def gibbsPartition (p : Fin N → ℝ) (β : ℝ) : ℝ := 1 + ∑ j, (p j) ^ (-β)

theorem gibbsPartition_pos {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) (β : ℝ) :
    0 < gibbsPartition p β := by
  have : (0:ℝ) ≤ ∑ j, (p j) ^ (-β) :=
    Finset.sum_nonneg fun j _ => (Real.rpow_pos_of_pos (hp j) (-β)).le
  simpa [gibbsPartition] using by linarith

/-- The eigenvalues of the Gibbs state. -/
noncomputable def gibbsEigen (p : Fin N → ℝ) (β : ℝ) (i : Option (Fin N)) : ℝ :=
  (gibbsPartition p β)⁻¹ * gibbsWeight p β i

theorem gibbsEigen_pos {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) (β : ℝ) (i : Option (Fin N)) :
    0 < gibbsEigen p β i :=
  mul_pos (inv_pos.2 (gibbsPartition_pos hp β)) (gibbsWeight_pos hp β i)

/-- **Card `(1)`.**  The faithful Gibbs state. -/
noncomputable def gibbsState (p : Fin N → ℝ) (β : ℝ) :
    Matrix (Option (Fin N)) (Option (Fin N)) ℂ :=
  Matrix.diagonal fun i => ((gibbsEigen p β i : ℝ) : ℂ)

/-- The complex power `ρ_β^z` of the Gibbs state. -/
noncomputable def gibbsPower (p : Fin N → ℝ) (β : ℝ) (z : ℂ) :
    Matrix (Option (Fin N)) (Option (Fin N)) ℂ :=
  Matrix.diagonal fun i => Complex.exp ((Real.log (gibbsEigen p β i) : ℂ) * z)

theorem gibbsPower_one {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) (β : ℝ) :
    gibbsPower p β 1 = gibbsState p β := by
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  rw [mul_one, ← Complex.ofReal_exp, Real.exp_log (gibbsEigen_pos hp β i)]

/-- **Card `(2)`.**  The modular flow of the Gibbs state. -/
noncomputable def modularFlow (p : Fin N → ℝ) (β : ℝ) (s : ℝ)
    (Y : Matrix (Option (Fin N)) (Option (Fin N)) ℂ) :
    Matrix (Option (Fin N)) (Option (Fin N)) ℂ :=
  gibbsPower p β (Complex.I * s) * Y * gibbsPower p β (-(Complex.I * s))

/-- The modular flow multiplies a matrix unit by the phase of its eigenvalue ratio. -/
theorem modularFlow_single {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) (β s : ℝ) (j : Fin N) (a : ℂ) :
    modularFlow p β s (Matrix.single (some j) none a)
      = Matrix.single (some j) none
          (Complex.exp ((Real.log ((p j) ^ (-β)) : ℂ) * (Complex.I * s)) * a) := by
  simp only [modularFlow, gibbsPower]
  rw [diagonal_mul_single_mul_diagonal]
  congr 1
  rw [mul_right_comm, ← Complex.exp_add]
  congr 1
  congr 1
  have hZ : (0:ℝ) < gibbsPartition p β := gibbsPartition_pos hp β
  have hw : (0:ℝ) < (p j) ^ (-β) := Real.rpow_pos_of_pos (hp j) (-β)
  have h1 : Real.log (gibbsEigen p β (some j))
      = Real.log ((gibbsPartition p β)⁻¹) + Real.log ((p j) ^ (-β)) := by
    rw [gibbsEigen, gibbsWeight_some, Real.log_mul (by positivity) hw.ne']
  have h2 : Real.log (gibbsEigen p β none) = Real.log ((gibbsPartition p β)⁻¹) := by
    rw [gibbsEigen, gibbsWeight_none, mul_one]
  rw [h1, h2]
  push_cast
  ring

/-- **Card `(3)`.**  The framed arithmetic vector. -/
noncomputable def primeFrame (p : Fin N → ℝ) : Matrix (Option (Fin N)) (Option (Fin N)) ℂ :=
  ∑ j, Matrix.single (some j) none ((Real.log (p j) : ℝ) : ℂ)

/-- **Card `(3)`.**  The modular orbit of the framed vector, at modular time `-t/β`. -/
noncomputable def primeClock (p : Fin N → ℝ) (β t : ℝ) :
    Matrix (Option (Fin N)) (Option (Fin N)) ℂ :=
  modularFlow p β (-t / β) (primeFrame p)

/-- **Card `(5)`.**  The framed coordinate functionals. -/
def frameCoord (Y : Matrix (Option (Fin N)) (Option (Fin N)) ℂ) (j : Fin N) : ℂ :=
  Y (some j) none

@[simp] theorem frameCoord_single (j k : Fin N) (a : ℂ) :
    frameCoord (Matrix.single (some k) none a) j = if k = j then a else 0 := by
  simp [frameCoord, Matrix.single_apply, eq_comm]

/-- **Card `(4)`.**  The modular orbit of the framed vector is the arithmetic phase clock. -/
theorem frameCoord_primeClock {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) {β : ℝ} (hβ : β ≠ 0) (t : ℝ)
    (j : Fin N) :
    frameCoord (primeClock p β t) j
      = ((Real.log (p j) : ℝ) : ℂ) * Complex.exp (((t * Real.log (p j) : ℝ) : ℂ) * Complex.I) := by
  classical
  have hsum : primeClock p β t
      = ∑ k, Matrix.single (some k) none
          (Complex.exp ((Real.log ((p k) ^ (-β)) : ℂ) * (Complex.I * ((-t / β : ℝ) : ℂ)))
            * ((Real.log (p k) : ℝ) : ℂ)) := by
    rw [primeClock, primeFrame, modularFlow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := modularFlow_single hp β (-t / β) k ((Real.log (p k) : ℝ) : ℂ)
    rwa [modularFlow] at this
  have hcoord : ∀ F : Fin N → ℂ,
      frameCoord (∑ k, Matrix.single (some k) none (F k)) j = F j := by
    intro F
    simp only [frameCoord, Matrix.sum_apply, Matrix.single_apply, Option.some.injEq, and_true]
    rw [Finset.sum_ite_eq' Finset.univ j F]
    simp
  rw [hsum, hcoord, mul_comm]
  congr 2
  have hlog : Real.log ((p j) ^ (-β)) = -β * Real.log (p j) :=
    Real.log_rpow (hp j) (-β)
  rw [hlog]
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ
  push_cast
  field_simp

end Gibbs

/-! ## The framed two-copy quadratic reader -/

section Reader

/-- **Card `(8)`.**  The subdiscriminant of a phase vector. -/
noncomputable def subdiscriminant {N : ℕ} (z : Fin N → ℂ) : ℂ :=
  (N : ℂ) * (∑ i, (z i) ^ 2) - (∑ i, z i) ^ 2

/-- **Card `(6)`.**  The framed two-copy quadratic reader. -/
noncomputable def framedReader {N : ℕ} (Y : Matrix (Option (Fin N)) (Option (Fin N)) ℂ) : ℂ :=
  subdiscriminant fun j => frameCoord Y j

/-- **Card `(7)`.**  The framed reader on the modular orbit is the subdiscriminant of the
arithmetic phase vector. -/
theorem framedReader_primeClock {N : ℕ} {p : Fin N → ℝ} (hp : ∀ j, 0 < p j) {β : ℝ} (hβ : β ≠ 0)
    (t : ℝ) :
    framedReader (primeClock p β t)
      = subdiscriminant fun j =>
          ((Real.log (p j) : ℝ) : ℂ) * Complex.exp (((t * Real.log (p j) : ℝ) : ℂ) * Complex.I) := by
  refine congrArg subdiscriminant (funext fun j => ?_)
  exact frameCoord_primeClock hp hβ t j

end Reader

/-! ## Zeros of the subdiscriminant on three concentric circles -/

section Equilateral

/-- A primitive cube root of unity. -/
noncomputable def cubeRoot : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2

theorem cubeRoot_sq_add : cubeRoot ^ 2 + cubeRoot + 1 = 0 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [cubeRoot]
  linear_combination (-1/4 : ℂ) * h3 + ((((Real.sqrt 3 : ℝ) : ℂ) ^ 2) / 4) * hI

theorem norm_cubeRoot : ‖cubeRoot‖ = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : ‖cubeRoot‖ ^ 2 = 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [cubeRoot, Complex.normSq_apply, Complex.div_re, Complex.div_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im, Complex.normSq_apply]
    norm_num
    nlinarith [h3]
  calc ‖cubeRoot‖ = Real.sqrt (‖cubeRoot‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (1 ^ 2) := by rw [hsq]
    _ = 1 := by norm_num

/-- The subdiscriminant of three points factors through the two equilateral conditions. -/
theorem subdiscriminant_three (z : Fin 3 → ℂ) :
    subdiscriminant z
      = 2 * ((z 0 + cubeRoot * z 1 + cubeRoot ^ 2 * z 2)
          * (z 0 + cubeRoot ^ 2 * z 1 + cubeRoot * z 2)) := by
  have h := cubeRoot_sq_add
  simp only [subdiscriminant, Fin.sum_univ_three]
  push_cast
  linear_combination (-2 * (z 1 ^ 2 + z 2 ^ 2) * (cubeRoot - 1) - 2 * (z 0 * z 1 + z 0 * z 2)
    - 2 * z 1 * z 2 * (1 + cubeRoot ^ 2 - cubeRoot)) * h

/-- Three points forming an equilateral triangle are a zero of the subdiscriminant. -/
theorem subdiscriminant_eq_zero_of_equilateral {z : Fin 3 → ℂ}
    (h : z 0 + cubeRoot * z 1 + cubeRoot ^ 2 * z 2 = 0) : subdiscriminant z = 0 := by
  rw [subdiscriminant_three, h, zero_mul, mul_zero]

/-- Three prescribed positive moduli satisfying the triangle inequalities are realized by three
complex numbers summing to zero. -/
theorem exists_sum_eq_zero_of_triangle {r : Fin 3 → ℝ} (hr : ∀ i, 0 < r i)
    (h2 : r 2 ≤ r 0 + r 1) (h0 : r 0 ≤ r 1 + r 2) (h1 : r 1 ≤ r 0 + r 2) :
    ∃ w : Fin 3 → ℂ, (∀ i, ‖w i‖ = r i) ∧ w 0 + w 1 + w 2 = 0 := by
  set c : ℝ := (r 2 ^ 2 - r 0 ^ 2 - r 1 ^ 2) / (2 * r 0 * r 1) with hc
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hden : 0 < 2 * r 0 * r 1 := by positivity
  have hcle : c ≤ 1 := by
    rw [hc, div_le_one hden]
    nlinarith [hr 0, hr 1, hr 2, h2, mul_le_mul_of_nonneg_left h2 (hr 2).le]
  have hcge : -1 ≤ c := by
    rw [hc, le_div_iff₀ hden]
    nlinarith [hr 0, hr 1, hr 2, h0, h1,
      mul_nonneg (by linarith : (0:ℝ) ≤ r 2 - (r 0 - r 1)) (by linarith : (0:ℝ) ≤ r 2 + (r 0 - r 1))]
  set φ : ℝ := Real.arccos c with hφ
  have hcos : Real.cos φ = c := Real.cos_arccos hcge hcle
  set X : ℂ := ((r 0 : ℝ) : ℂ) + ((r 1 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) with hX
  have hre : X.re = r 0 + r 1 * Real.cos φ := by
    simp [hX, Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  have him : X.im = r 1 * Real.sin φ := by
    simp [hX, Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
  have hnsq : Complex.normSq X = r 2 ^ 2 := by
    rw [Complex.normSq_apply, hre, him]
    have hpy : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
    have hcc : Real.cos φ = (r 2 ^ 2 - r 0 ^ 2 - r 1 ^ 2) / (2 * r 0 * r 1) := by rw [hcos, hc]
    have hsin : Real.sin φ * Real.sin φ = 1 - Real.cos φ * Real.cos φ := by nlinarith [hpy]
    have hexp : (r 0 + r 1 * Real.cos φ) * (r 0 + r 1 * Real.cos φ)
        + r 1 * Real.sin φ * (r 1 * Real.sin φ)
        = r 0 ^ 2 + r 1 ^ 2 + 2 * r 0 * r 1 * Real.cos φ := by nlinarith [hsin]
    rw [hexp, hcc]
    field_simp
    ring
  have hthird : ‖X‖ = r 2 := by
    have hsq : ‖X‖ ^ 2 = r 2 ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; exact hnsq
    calc ‖X‖ = Real.sqrt (‖X‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (r 2 ^ 2) := by rw [hsq]
      _ = r 2 := Real.sqrt_sq hr2.le
  refine ⟨![((r 0 : ℝ) : ℂ), ((r 1 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I), -X], ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [hthird, abs_of_pos hr0, abs_of_pos hr1, Complex.norm_exp_ofReal_mul_I]
  · simp [hX]

/-- **Card `(9)`, geometric step.**  Three concentric circles whose radii satisfy the triangle
inequalities carry a zero of the subdiscriminant. -/
theorem exists_phase_subdiscriminant_eq_zero {r : Fin 3 → ℝ} (hr : ∀ i, 0 < r i)
    (h2 : r 2 ≤ r 0 + r 1) (h0 : r 0 ≤ r 1 + r 2) (h1 : r 1 ≤ r 0 + r 2) :
    ∃ θ : Fin 3 → ℝ,
      subdiscriminant (fun i => ((r i : ℝ) : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)) = 0 := by
  obtain ⟨w, hw, hsum⟩ := exists_sum_eq_zero_of_triangle hr h2 h0 h1
  set z : Fin 3 → ℂ := ![w 0, cubeRoot ^ 2 * w 1, cubeRoot * w 2] with hz
  have hcube : cubeRoot ^ 3 = 1 := by
    have h := cubeRoot_sq_add
    linear_combination (cubeRoot - 1) * h
  have hnorm : ∀ i, ‖z i‖ = r i := by
    intro i
    fin_cases i <;> simp [hz, norm_cubeRoot, hw]
  have hequi : z 0 + cubeRoot * z 1 + cubeRoot ^ 2 * z 2 = 0 := by
    simp only [hz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    calc w 0 + cubeRoot * (cubeRoot ^ 2 * w 1) + cubeRoot ^ 2 * (cubeRoot * w 2)
        = w 0 + cubeRoot ^ 3 * w 1 + cubeRoot ^ 3 * w 2 := by ring
      _ = w 0 + w 1 + w 2 := by rw [hcube]; ring
      _ = 0 := hsum
  refine ⟨fun i => Complex.arg (z i), ?_⟩
  have hrepr : ∀ i, ((r i : ℝ) : ℂ) * Complex.exp ((Complex.arg (z i) : ℂ) * Complex.I) = z i := by
    intro i
    rw [← hnorm i]
    exact Complex.norm_mul_exp_arg_mul_I (z i)
  rw [show (fun i => ((r i : ℝ) : ℂ) * Complex.exp ((Complex.arg (z i) : ℂ) * Complex.I)) = z from
    funext hrepr]
  exact subdiscriminant_eq_zero_of_equilateral hequi

end Equilateral

/-! ## Kronecker density drives the reader to zero -/

section Density

/-- The framed reader as a function of the three phases. -/
noncomputable def phaseReader (r : Fin 3 → ℝ) (u : Fin 3 → ℂ) : ℂ :=
  subdiscriminant fun i => ((r i : ℝ) : ℂ) * u i

theorem continuous_phaseReader (r : Fin 3 → ℝ) : Continuous (phaseReader r) := by
  unfold phaseReader subdiscriminant
  fun_prop

/-- **Card `(9)`.**  For three rationally independent positive frequencies whose radii satisfy the
triangle inequalities, the framed reader on the Gibbs modular orbit comes arbitrarily close to
zero. -/
theorem exists_norm_framedReader_lt {p : Fin 3 → ℝ} (hp : ∀ j, 0 < p j) {β : ℝ} (hβ : β ≠ 0)
    (hind : LinearIndependent ℚ fun j => Real.log (p j))
    (hpos : ∀ j, 0 < Real.log (p j))
    (h2 : Real.log (p 2) ≤ Real.log (p 0) + Real.log (p 1))
    (h0 : Real.log (p 0) ≤ Real.log (p 1) + Real.log (p 2))
    (h1 : Real.log (p 1) ≤ Real.log (p 0) + Real.log (p 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ‖framedReader (primeClock p β t)‖ < ε := by
  set r : Fin 3 → ℝ := fun j => Real.log (p j) with hrdef
  obtain ⟨θ, hθ⟩ := exists_phase_subdiscriminant_eq_zero (r := r) hpos h2 h0 h1
  set v : Fin 3 → ℂ := fun i => Complex.exp ((θ i : ℂ) * Complex.I) with hv
  have hfv : phaseReader r v = 0 := hθ
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_phaseReader r) v ε hε
  obtain ⟨t, ht⟩ := kronecker_approx hind θ hδ
  refine ⟨t, ?_⟩
  set u : Fin 3 → ℂ := fun i => expChar (r i) t with hu
  have hdist : dist u v < δ := by
    rw [dist_pi_lt_iff hδ]
    intro i
    simpa [hu, hv, Complex.dist_eq] using ht i
  have hlt : ‖phaseReader r u‖ < ε := by
    have := hcont u hdist
    rwa [hfv, Complex.dist_eq, sub_zero] at this
  have heq : framedReader (primeClock p β t) = phaseReader r u := by
    rw [framedReader_primeClock hp hβ]
    refine congrArg subdiscriminant (funext fun j => ?_)
    simp only [hu, expChar, hrdef]
    rw [mul_comm t (Real.log (p j))]
  rwa [heq]

/-- **Card `(9)`.**  The infimum of the framed reader along the modular clock is zero. -/
theorem csInf_norm_framedReader_eq_zero {p : Fin 3 → ℝ} (hp : ∀ j, 0 < p j) {β : ℝ} (hβ : β ≠ 0)
    (hind : LinearIndependent ℚ fun j => Real.log (p j))
    (hpos : ∀ j, 0 < Real.log (p j))
    (h2 : Real.log (p 2) ≤ Real.log (p 0) + Real.log (p 1))
    (h0 : Real.log (p 0) ≤ Real.log (p 1) + Real.log (p 2))
    (h1 : Real.log (p 1) ≤ Real.log (p 0) + Real.log (p 2)) :
    sInf (Set.range fun t : ℝ => ‖framedReader (primeClock p β t)‖) = 0 := by
  have hne : (Set.range fun t : ℝ => ‖framedReader (primeClock p β t)‖).Nonempty :=
    ⟨_, Set.mem_range_self 0⟩
  have hbdd : BddBelow (Set.range fun t : ℝ => ‖framedReader (primeClock p β t)‖) :=
    ⟨0, by rintro x ⟨t, rfl⟩; exact norm_nonneg _⟩
  refine le_antisymm ?_ (le_csInf hne (by rintro x ⟨t, rfl⟩; exact norm_nonneg _))
  refine (Real.sInf_le_iff hbdd hne).2 fun ε hε => ?_
  obtain ⟨t, ht⟩ := exists_norm_framedReader_lt hp hβ hind hpos h2 h0 h1 hε
  exact ⟨_, Set.mem_range_self t, by simpa using ht⟩

end Density

/-! ## The explicit prime triple -/

section PrimeTriple

/-- The prime triple `(101, 103, 107)`. -/
def triplePrimeNat : Fin 3 → ℕ := fun j => 101 + 2 * (j : ℕ) + (if (j : ℕ) = 2 then 2 else 0)

theorem triplePrimeNat_injective : Function.Injective triplePrimeNat := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [triplePrimeNat] at hab
  apply Fin.ext
  split_ifs at hab <;> omega

theorem triplePrimeNat_prime (j : Fin 3) : Nat.Prime (triplePrimeNat j) := by
  fin_cases j <;> norm_num [triplePrimeNat]

/-- The prime triple as members of the primes. -/
def triplePrimes (j : Fin 3) : Nat.Primes := ⟨triplePrimeNat j, triplePrimeNat_prime j⟩

theorem triplePrimes_injective : Function.Injective triplePrimes := fun _ _ hab =>
  triplePrimeNat_injective (congrArg (fun q : Nat.Primes => (q : ℕ)) hab)

/-- The radii of the prime triple. -/
noncomputable def tripleRadii : Fin 3 → ℝ := fun j => ((triplePrimes j : Nat.Primes) : ℕ)

theorem tripleRadii_eq (j : Fin 3) : tripleRadii j = ((triplePrimeNat j : ℕ) : ℝ) := rfl

theorem tripleRadii_pos (j : Fin 3) : 0 < tripleRadii j := by
  rw [tripleRadii_eq]
  exact_mod_cast (triplePrimeNat_prime j).pos

theorem log_tripleRadii_pos (j : Fin 3) : 0 < Real.log (tripleRadii j) := by
  refine Real.log_pos ?_
  rw [tripleRadii_eq]
  exact_mod_cast (triplePrimeNat_prime j).one_lt

theorem tripleRadii_linearIndependent :
    LinearIndependent ℚ fun j => Real.log (tripleRadii j) :=
  linearIndependent_log_primes.comp triplePrimes triplePrimes_injective

/-- The three prime logarithms satisfy the triangle inequalities. -/
theorem log_triple_triangle :
    Real.log (tripleRadii 2) ≤ Real.log (tripleRadii 0) + Real.log (tripleRadii 1) ∧
    Real.log (tripleRadii 0) ≤ Real.log (tripleRadii 1) + Real.log (tripleRadii 2) ∧
    Real.log (tripleRadii 1) ≤ Real.log (tripleRadii 0) + Real.log (tripleRadii 2) := by
  have h101 : tripleRadii 0 = (101 : ℝ) := by rw [tripleRadii_eq]; norm_num [triplePrimeNat]
  have h103 : tripleRadii 1 = (103 : ℝ) := by rw [tripleRadii_eq]; norm_num [triplePrimeNat]
  have h107 : tripleRadii 2 = (107 : ℝ) := by rw [tripleRadii_eq]; norm_num [triplePrimeNat]
  rw [h101, h103, h107]
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [← Real.log_mul (by norm_num) (by norm_num)]
      exact Real.log_le_log (by norm_num) (by norm_num)

/-- **Card `(9)`, explicit form.**  For the prime triple `(101, 103, 107)` the framed two-copy
reader on the Gibbs modular clock has infimum zero. -/
theorem csInf_norm_framedReader_triple {β : ℝ} (hβ : β ≠ 0) :
    sInf (Set.range fun t : ℝ => ‖framedReader (primeClock tripleRadii β t)‖) = 0 := by
  obtain ⟨h2, h0, h1⟩ := log_triple_triangle
  exact csInf_norm_framedReader_eq_zero tripleRadii_pos hβ tripleRadii_linearIndependent
    log_tripleRadii_pos h2 h0 h1

end PrimeTriple

end HTGeometry.ConstraintRelativity
