import GaloisForLFunctions.GrowingWindowsOfSpecZ.ACurveDegeneratesAtItsNumberOfAngles
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeAnchorFlow
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheWindowReceiversOfACurve

/-!
# The canonical flow of a curve

Over `𝔽_q` the sign is known and the canonical flow of the window tower computes. Let `D` be a curve
datum with `R` distinct normalized eigenvalues and lattice data `κ(d) = Re Σ_i β_i^{|d|}`.

* **Purity certificates** (`unitary_iff_margins_pos`, `unitary_iff_reflCoeff_sq_lt`,
  `unitary_iff_flow_admitted`). The datum is unitary iff the first `R` margins are positive, iff the
  `R − 1` reflection coefficients `γ_0, …, γ_{R−2}` lie in `(−1,1)`, iff the anchor flow is admitted
  at each of these steps, for any one anchor `s` with `s² < 1`.
* **The flow on a unitary curve** (`curve_flow_inside`, `curve_flow_contact`). The reflection starts at
  `r_0 = 1`, stays in `(−1,1)` for `0 < n < R`, and at the number of angles returns to the boundary at
  the exact value `r_R = −γ_{R−1} = B(0)`, with `B` the reduced characteristic polynomial, for every
  anchor.
* **The kick is the point count** (`schurParam_curveLattice`). The Schur parameter at step `n` is the
  polar term minus `N_{n+1} q^{−(n+1)/2}` minus the frozen prediction: the function-field form of the
  reflectors of the prime echo train.
* **The ladder** (`liForm_eq_neg_two_toeplitz`). On primitive vectors the form of the Li couplings
  `2(2g − κ(|i−j|))` is exactly `−2` times the window form. So the Cayley ladder and the canonical
  chain read one quadratic form.
-/

noncomputable section

open Finset Polynomial Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The lattice data of a curve datum: `κ(d) = Re Σ_i β_i^{|d|}`. -/
def curveLattice (d : ℤ) : ℝ := D.trace d.natAbs

theorem curveLattice_isEven : IsEvenSeq (curveLattice D) := fun d => by
  simp only [curveLattice, Int.natAbs_neg]

theorem curveLattice_zero : curveLattice D 0 = Fintype.card ι := by
  simpa [curveLattice] using D.trace_zero

private theorem natAbs_sub_eq_dist (i j : ℕ) : ((i : ℤ) - j).natAbs = Nat.dist i j := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
    omega

/-- The lattice form of a curve is its Frobenius window form. -/
theorem toeplitzForm_curveLattice (n : ℕ) (e : ℕ → ℝ) :
    toeplitzForm (curveLattice D) n (fun k => e k) = D.toeplitz (range n) e := by
  simp only [toeplitzForm, curveLattice, natAbs_sub_eq_dist, CurveDatum.toeplitz]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range n, e k * e l * D.trace (Nat.dist k l))]
  refine sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => e i * e l * D.trace (Nat.dist i l))]
  exact sum_congr rfl fun j _ => by ring

/-- The multiplicity of a normalized eigenvalue. -/
def angleMultiplicity (z : ℂ) : ℝ :=
  open Classical in ((univ : Finset ι).filter (fun i => D.β i = z)).card

variable {D}

theorem spectrum_conj {z : ℂ} (hz : z ∈ D.spectrum) : conj z ∈ D.spectrum := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨D.conjPerm i, Finset.mem_univ _, D.β_conjPerm i⟩

theorem spectrum_norm (hU : ∀ i, ‖D.β i‖ = 1) {z : ℂ} (hz : z ∈ D.spectrum) : ‖z‖ = 1 := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  exact hU i

theorem angleMultiplicity_pos {z : ℂ} (hz : z ∈ D.spectrum) : 0 < angleMultiplicity D z := by
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  have h : 0 < ((univ : Finset ι).filter (fun j => D.β j = D.β i)).card :=
    Finset.card_pos.mpr ⟨i, by simp⟩
  have he : angleMultiplicity D (D.β i) =
      (((univ : Finset ι).filter (fun j => D.β j = D.β i)).card : ℝ) := by
    simp only [angleMultiplicity]
  rw [he]
  exact_mod_cast h

/-- A unitary curve datum has the lattice data of its angles, with their multiplicities. -/
theorem curveLattice_eq_curveData (hU : ∀ i, ‖D.β i‖ = 1) :
    curveLattice D = curveData D.spectrum (angleMultiplicity D) := by
  classical
  funext d
  have hsum : ∑ z ∈ D.spectrum, ((angleMultiplicity D z : ℝ) : ℂ) * z ^ d = ∑ i, D.β i ^ d := by
    have h := Finset.sum_comp (s := (univ : Finset ι)) (fun z : ℂ => z ^ d) D.β
    rw [h]
    refine sum_congr rfl fun z _ => ?_
    have he : angleMultiplicity D z = (((univ : Finset ι).filter (fun j => D.β j = z)).card : ℝ) := by
      simp only [angleMultiplicity]
    rw [he, nsmul_eq_mul]
    push_cast
    rfl
  rw [curveData, hsum, curveLattice]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · simp [CurveDatum.trace, CurveDatum.powerSum]
  · have hneg : ∑ i, D.β i ^ (-(m : ℤ)) = conj (∑ i, D.β i ^ m) := by
      rw [map_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [zpow_neg, zpow_natCast, map_pow, ← inv_pow, Complex.inv_eq_conj (hU i)]
    rw [hneg, Complex.conj_re]
    simp [CurveDatum.trace, CurveDatum.powerSum]

/-- **A unitary curve is positive up to its number of angles, and degenerates there.** -/
theorem curveLattice_first_critical (hU : ∀ i, ‖D.β i‖ = 1) :
    (∀ k < D.spectrum.card, 0 < levinsonErr (curveLattice D) k) ∧
      levinsonErr (curveLattice D) D.spectrum.card = 0 := by
  rw [curveLattice_eq_curveData hU]
  exact curve_first_critical (fun z hz => spectrum_norm hU hz)
    (fun z hz => angleMultiplicity_pos hz) (fun z hz => spectrum_conj hz)

/-! ### Purity certificates -/

/-- **The margin certificate.** A curve datum is unitary iff its first `R` margins are positive. -/
theorem unitary_iff_margins_pos :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ k < D.spectrum.card, 0 < levinsonErr (curveLattice D) k := by
  refine ⟨fun hU => (curveLattice_first_critical hU).1, fun h => ?_⟩
  refine D.unitary_of_toeplitz_nonneg_on_spectrum_window fun e => ?_
  rw [← toeplitzForm_curveLattice]
  exact (windowEval_sq_le_latticeKernel (curveLattice_isEven D) 0 _ h _).2

theorem levinsonErr_curveLattice_zero [Nonempty ι] : 0 < levinsonErr (curveLattice D) 0 := by
  rw [levinsonErr_zero, curveLattice_zero]
  exact_mod_cast Fintype.card_pos

theorem spectrum_card_pos [Nonempty ι] : 0 < D.spectrum.card :=
  Finset.card_pos.mpr ((Finset.univ_nonempty (α := ι)).image D.β)

private theorem margins_pos_of_step [Nonempty ι] {R : ℕ} {P : ℕ → Prop}
    (hstep : ∀ k, k + 1 < R → (∀ j ≤ k, 0 < levinsonErr (curveLattice D) j) → P k →
      0 < levinsonErr (curveLattice D) (k + 1))
    (hP : ∀ k, k + 1 < R → P k) :
    ∀ k < R, 0 < levinsonErr (curveLattice D) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero => exact levinsonErr_curveLattice_zero
    | succ m => exact hstep m hk (fun j hj => ih j (by omega) (by omega)) (hP m hk)

/-- **The Schur certificate.** A curve datum is unitary iff its first `R − 1` reflection coefficients
lie in `(−1,1)`. -/
theorem unitary_iff_reflCoeff_sq_lt [Nonempty ι] :
    (∀ i, ‖D.β i‖ = 1) ↔
      ∀ k, k + 1 < D.spectrum.card → reflCoeff (curveLattice D) k ^ 2 < 1 := by
  rw [unitary_iff_margins_pos]
  constructor
  · intro h k hk
    have h1 := h (k + 1) hk
    have h0 := h k (by omega)
    rw [levinsonErr_succ_eq_mul h0.ne'] at h1
    have := (pos_iff_pos_of_mul_pos h1).mp h0
    linarith only [this]
  · intro hγ
    refine margins_pos_of_step (P := fun k => reflCoeff (curveLattice D) k ^ 2 < 1)
      (fun k _ hj hP => ?_) hγ
    rw [levinsonErr_succ_eq_mul (hj k le_rfl).ne']
    exact mul_pos (hj k le_rfl) (by linarith only [hP])

/-- **The flow certificate.** For any one anchor `s` with `s² < 1`, a curve datum is unitary iff the
anchor flow is admitted at each of the first `R − 1` steps. -/
theorem unitary_iff_flow_admitted [Nonempty ι] {s : ℝ} (hs : s ^ 2 < 1) :
    (∀ i, ‖D.β i‖ = 1) ↔
      ∀ k, k + 1 < D.spectrum.card →
        (s * latticeReflection (curveLattice D) s k - reflCoeff (curveLattice D) k) ^ 2 <
          (1 - reflCoeff (curveLattice D) k * (s * latticeReflection (curveLattice D) s k)) ^ 2 := by
  rw [unitary_iff_margins_pos]
  constructor
  · intro h k hk
    have hlow : ∀ j ≤ k, 0 < levinsonErr (curveLattice D) j := fun j hj => h j (by omega)
    exact (levinsonErr_succ_pos_iff (latticeAnchor_sq_lt hs hlow).2 (hlow k le_rfl)).mp (h _ hk)
  · intro hadm
    refine margins_pos_of_step (P := fun k =>
        (s * latticeReflection (curveLattice D) s k - reflCoeff (curveLattice D) k) ^ 2 <
          (1 - reflCoeff (curveLattice D) k * (s * latticeReflection (curveLattice D) s k)) ^ 2)
      (fun k _ hj hP => ?_) hadm
    exact (levinsonErr_succ_pos_iff (latticeAnchor_sq_lt hs hj).2 (hj k le_rfl)).mpr hP

/-! ### The flow on a unitary curve -/

/-- **The flow stays inside the disc below the number of angles.** -/
theorem curve_flow_inside (hU : ∀ i, ‖D.β i‖ = 1) {s : ℝ} (hs : s ^ 2 < 1) {n : ℕ} (hn : 0 < n)
    (hnR : n < D.spectrum.card) : latticeReflection (curveLattice D) s n ^ 2 < 1 :=
  (latticeReflection_sq_lt hs hn fun k hk =>
    (curveLattice_first_critical hU).1 k (by omega)).2

/-- **The contact value of a curve.** At the number of angles the reflection is `−γ_{R−1}`, and this
value is `B(0)` for the reduced characteristic polynomial `B`, whatever the anchor. -/
theorem curve_flow_contact (hU : ∀ i, ‖D.β i‖ = 1) [Nonempty ι] {s : ℝ} (hs : s ^ 2 < 1) :
    ∃ m, D.spectrum.card = m + 1 ∧
      latticeReflection (curveLattice D) s (m + 1) = -reflCoeff (curveLattice D) m ∧
      reflCoeff (curveLattice D) m ^ 2 = 1 ∧
      ((latticeReflection (curveLattice D) s (m + 1) : ℝ) : ℂ) = D.reducedCharPoly.eval 0 := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, D.spectrum.card = m + 1 :=
    ⟨D.spectrum.card - 1, by have := spectrum_card_pos (D := D); omega⟩
  obtain ⟨hpos, hzero⟩ := curveLattice_first_critical hU
  rw [hm] at hpos hzero
  obtain ⟨hγ, hr⟩ := latticeReflection_contact hs (fun k hk => hpos k (by omega)) hzero
  refine ⟨m, hm, hr, hγ, ?_⟩
  rw [hr]
  set κ := curveLattice D with hκdef
  have hκ : IsEvenSeq κ := curveLattice_isEven D
  set γ := reflCoeff κ m with hγdef
  set S := D.spectrum with hSdef
  set ρ := angleMultiplicity D with hρdef
  have hcurve : κ = curveData S ρ := curveLattice_eq_curveData hU
  have hS : ∀ z ∈ S, ‖z‖ = 1 := fun z hz => spectrum_norm hU hz
  -- the Levinson vector is the zero mode of the window of size `R + 1`
  let v := levinsonVec κ (m + 1)
  have hT : toeplitzForm κ (m + 2) v = 0 := by
    rw [toeplitzForm_levinsonVec hκ fun k hk => (hpos k hk).ne', hzero]
  rw [hcurve, toeplitzForm_curveData hS] at hT
  have hnn : ∀ z ∈ S, 0 ≤ ρ z * ‖∑ k : Fin (m + 2), (v k : ℂ) * z ^ (k : ℕ)‖ ^ 2 :=
    fun z hz => mul_nonneg (angleMultiplicity_pos hz).le (sq_nonneg _)
  have hv0 := (sum_eq_zero_iff_of_nonneg hnn).mp hT
  have heval : ∀ z ∈ S, (vecPoly v).eval z = 0 := fun z hz => by
    have h1 := hv0 z hz
    rw [mul_eq_zero, or_iff_right (angleMultiplicity_pos hz).ne', sq_eq_zero_iff, norm_eq_zero]
      at h1
    simpa [vecPoly, eval_finsetSum] using h1
  -- its polynomial is `−γ` times the reduced characteristic polynomial
  have hlast : v (Fin.last (m + 1)) = -γ := by
    change levinsonVec κ (m + 1) (Fin.last m).succ = -γ
    rw [levinsonVec, Fin.cons_succ, levinsonPred_succ, Fin.snoc_last]
  have hfirst : v 0 = 1 := rfl
  have hBm : (D.reducedCharPoly).Monic := monic_prod_X_sub_C id S
  have hBd : (D.reducedCharPoly).natDegree = m + 1 := by
    rw [CurveDatum.natDegree_reducedCharPoly, ← hSdef, hm]
  have hBeval : ∀ z ∈ S, (D.reducedCharPoly).eval z = 0 := fun z hz => by
    rw [CurveDatum.reducedCharPoly, eval_prod]
    exact Finset.prod_eq_zero hz (by simp)
  have hPQ : vecPoly v = C ((-γ : ℝ) : ℂ) * D.reducedCharPoly := by
    by_contra hne
    have hne' : vecPoly v - C ((-γ : ℝ) : ℂ) * D.reducedCharPoly ≠ 0 := sub_ne_zero.mpr hne
    have hdeg : (vecPoly v - C ((-γ : ℝ) : ℂ) * D.reducedCharPoly).natDegree < S.card := by
      rw [hm, natDegree_lt_iff_degree_lt hne', degree_lt_iff_coeff_zero]
      intro j hj
      rw [coeff_sub, coeff_C_mul]
      rcases eq_or_lt_of_le hj with rfl | hj'
      · have h1 : (vecPoly v).coeff (m + 1) = ((-γ : ℝ) : ℂ) := by
          rw [coeff_vecPoly, dif_pos (by omega)]
          exact congrArg _ hlast
        have h2 : (D.reducedCharPoly).coeff (m + 1) = 1 := by
          rw [← hBd]
          exact hBm.coeff_natDegree
        rw [h1, h2]
        ring
      · have h1 : (vecPoly v).coeff j = 0 := by
          rw [coeff_vecPoly, dif_neg (by omega)]
        have h2 : (D.reducedCharPoly).coeff j = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        rw [h1, h2]
        ring
    apply hne'
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun z hz => ?_) hdeg
    rw [eval_sub, eval_mul, heval z hz, hBeval z hz]
    ring
  -- the constant coefficient is one
  have hconst : (vecPoly v).eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_vecPoly, dif_pos (by omega)]
    exact congrArg _ hfirst
  rw [hPQ, eval_mul, eval_C] at hconst
  have hγc : (((-γ : ℝ) : ℂ)) ^ 2 = 1 := by
    have : (-γ) ^ 2 = 1 := by rw [neg_sq]; exact hγ
    exact_mod_cast this
  calc ((-γ : ℝ) : ℂ) = ((-γ : ℝ) : ℂ) * (((-γ : ℝ) : ℂ) * (D.reducedCharPoly).eval 0) := by
        rw [hconst, mul_one]
    _ = ((-γ : ℝ) : ℂ) ^ 2 * (D.reducedCharPoly).eval 0 := by ring
    _ = _ := by rw [hγc, one_mul]

/-! ### The kick and the ladder -/

variable (D)

/-- **The kick is the point count.** The Schur parameter at step `n` is the polar term, minus
`N_{n+1} q^{−(n+1)/2}`, minus the frozen prediction from the earlier lags. -/
theorem schurParam_curveLattice (n : ℕ) :
    schurParam (curveLattice D) n =
      D.sqrtq ^ (n + 1) + (D.sqrtq⁻¹) ^ (n + 1) - D.pointCount (n + 1) * (D.sqrtq⁻¹) ^ (n + 1) -
        frozenPrediction (curveLattice D) n (levinsonPred (curveLattice D) n) := by
  rw [schurParam_eq, ← D.trace_eq_polar_sub_prime]
  congr 1

/-- The first reflection coefficient is the normalized first trace. -/
theorem reflCoeff_curveLattice_zero :
    reflCoeff (curveLattice D) 0 = D.trace 1 / Fintype.card ι := by
  simp [reflCoeff, schurParam, schurCoupling, levinsonErr_zero, curveLattice, D.trace_zero]

/-- The first step of the flow: `r_1 = (s − γ_0)/(1 − γ_0 s)`. -/
theorem latticeReflection_one (s : ℝ) :
    latticeReflection (curveLattice D) s 1 =
      (s - reflCoeff (curveLattice D) 0) / (1 - reflCoeff (curveLattice D) 0 * s) := by
  rw [latticeReflection, latticeRightTrace_succ, latticeLeftTrace_succ, latticeRightTrace_zero,
    latticeLeftTrace_zero]
  ring_nf

/-- **The ladder is the chain on primitive vectors**: the form of the Li couplings
`2(2g − κ(|i−j|))` is `−2` times the window form when `Σ c = 0`. -/
theorem liForm_eq_neg_two_toeplitz {n : ℕ} (c : Fin n → ℝ) (hc : ∑ i, c i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, c i * c j *
        (2 * ((Fintype.card ι : ℝ) - curveLattice D ((i : ℤ) - j))) =
      -2 * toeplitzForm (curveLattice D) n c := by
  have hzero : ∑ i : Fin n, ∑ j : Fin n, c i * c j * (2 * (Fintype.card ι : ℝ)) = 0 := by
    have h : ∑ i : Fin n, ∑ j : Fin n, c i * c j * (2 * (Fintype.card ι : ℝ)) =
        (∑ i, c i) * (∑ j, c j) * (2 * (Fintype.card ι : ℝ)) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [h, hc]
    ring
  have hexp : ∀ i j : Fin n, c i * c j * (2 * ((Fintype.card ι : ℝ) -
      curveLattice D ((i : ℤ) - j))) = c i * c j * (2 * (Fintype.card ι : ℝ)) -
        2 * (curveLattice D ((i : ℤ) - j) * c i * c j) := fun i j => by ring
  have h1 : ∑ i : Fin n, ∑ j : Fin n, c i * c j *
      (2 * ((Fintype.card ι : ℝ) - curveLattice D ((i : ℤ) - j))) =
      ∑ i : Fin n, ∑ j : Fin n, c i * c j * (2 * (Fintype.card ι : ℝ)) -
        2 * toeplitzForm (curveLattice D) n c := by
    simp only [hexp, toeplitzForm, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [h1, hzero]
  ring

end GaloisForLFunctions.GrowingWindowsOfSpecZ
