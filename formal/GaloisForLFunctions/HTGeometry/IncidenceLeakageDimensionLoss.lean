import GaloisForLFunctions.HTGeometry.EndpointProbeTransitionCriterion

/-!
# Dimension loss is quantitative leakage

For a bi-stochastic matrix tuple, `∑ Bₐ*Bₐ = ∑ BₐBₐ* = 1`, the total Hilbert--Schmidt energy that a
source projector emits is its dimension, and the total energy a target projector can capture is its
dimension.  Everything emitted and not captured is leakage, so

`Leak_B(U,V) ≥ dim U − dim V`.

The proof is two trace identities and one Pythagoras split; no spectral theory is used, and the
bound is attained, so a dimension-losing incidence cut leaks at least one full unit.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The real Hilbert--Schmidt energy of a matrix. -/
def hsSqRe (X : Matrix d d ℂ) : ℝ := ((Xᴴ * X).trace).re

omit [DecidableEq d] in
theorem trace_conjTranspose_mul_self (X : Matrix d d ℂ) :
    (Xᴴ * X).trace = ((∑ i, ∑ j, ‖X j i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _

omit [DecidableEq d] in
theorem hsSqRe_eq_sum (X : Matrix d d ℂ) : hsSqRe X = ∑ i, ∑ j, ‖X j i‖ ^ (2 : ℕ) := by
  rw [hsSqRe, trace_conjTranspose_mul_self, Complex.ofReal_re]

omit [DecidableEq d] in
theorem hsSqRe_nonneg (X : Matrix d d ℂ) : 0 ≤ hsSqRe X := by
  rw [hsSqRe_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/-! ## Splitting the energy along a projector -/

omit [DecidableEq d] in
theorem hsSqRe_eq_trace_right (Y Q : Matrix d d ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) :
    hsSqRe (Y * Q) = ((Yᴴ * Y * Q).trace).re := by
  unfold hsSqRe
  congr 1
  rw [Matrix.conjTranspose_mul, hQ]
  rw [show Q * Yᴴ * (Y * Q) = Q * (Yᴴ * Y) * Q from by simp [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_cycle Q (Yᴴ * Y) Q, hQQ]
  exact Matrix.trace_mul_comm Q (Yᴴ * Y)

omit [DecidableEq d] in
theorem hsSqRe_eq_trace_left (X R : Matrix d d ℂ) (hR : Rᴴ = R) (hRR : R * R = R) :
    hsSqRe (R * X) = ((Xᴴ * R * X).trace).re := by
  unfold hsSqRe
  congr 1
  rw [Matrix.conjTranspose_mul, hR]
  rw [show Xᴴ * R * (R * X) = Xᴴ * (R * R) * X from by simp [Matrix.mul_assoc], hRR]

omit [Fintype d] in
theorem conjTranspose_one_sub {P : Matrix d d ℂ} (hP : Pᴴ = P) : (1 - P)ᴴ = 1 - P := by
  rw [Matrix.conjTranspose_sub, hP, Matrix.conjTranspose_one]

theorem one_sub_idem {P : Matrix d d ℂ} (hPP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]
  simp

/-- Cutting the source by a projector splits the energy. -/
theorem hsSqRe_split_right (Y P : Matrix d d ℂ) (hP : Pᴴ = P) (hPP : P * P = P) :
    hsSqRe Y = hsSqRe (Y * P) + hsSqRe (Y * (1 - P)) := by
  rw [hsSqRe_eq_trace_right Y P hP hPP,
    hsSqRe_eq_trace_right Y (1 - P) (conjTranspose_one_sub hP) (one_sub_idem hPP),
    ← Complex.add_re]
  unfold hsSqRe
  congr 1
  rw [← Matrix.trace_add, ← Matrix.mul_add]
  simp

/-- Cutting the target by a projector splits the energy. -/
theorem hsSqRe_split_left (X Q : Matrix d d ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) :
    hsSqRe X = hsSqRe (Q * X) + hsSqRe ((1 - Q) * X) := by
  rw [hsSqRe_eq_trace_left X Q hQ hQQ,
    hsSqRe_eq_trace_left X (1 - Q) (conjTranspose_one_sub hQ) (one_sub_idem hQQ),
    ← Complex.add_re]
  unfold hsSqRe
  congr 1
  rw [← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.mul_add]
  simp

/-! ## The leakage bound -/

variable {A : Type*} [Fintype A]

/-- **Total emitted energy is the source dimension.** -/
theorem sum_hsSqRe_mul_source (B : A → Matrix d d ℂ) (hcol : ∑ a, (B a)ᴴ * B a = 1)
    {PU : Matrix d d ℂ} (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU) :
    ∑ a, hsSqRe (B a * PU) = (PU.trace).re := by
  have hterm : ∀ a : A, hsSqRe (B a * PU) = (((B a)ᴴ * B a * PU).trace).re :=
    fun a => hsSqRe_eq_trace_right (B a) PU hUherm hUidem
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Complex.re_sum, ← Matrix.trace_sum,
    ← Finset.sum_mul, hcol, Matrix.one_mul]

/-- **Total capturable energy is the target dimension.** -/
theorem sum_hsSqRe_target_mul (B : A → Matrix d d ℂ) (hrow : ∑ a, B a * (B a)ᴴ = 1)
    {PV : Matrix d d ℂ} (hVherm : PVᴴ = PV) (hVidem : PV * PV = PV) :
    ∑ a, hsSqRe (PV * B a) = (PV.trace).re := by
  have hterm : ∀ a : A, hsSqRe (PV * B a) = ((B a * (B a)ᴴ * PV).trace).re := by
    intro a
    rw [hsSqRe_eq_trace_left (B a) PV hVherm hVidem]
    congr 1
    exact Matrix.trace_mul_cycle _ _ _
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Complex.re_sum, ← Matrix.trace_sum,
    ← Finset.sum_mul, hrow, Matrix.one_mul]

/-- **Dimension loss is quantitative leakage.**  For a bi-stochastic tuple, the leakage of a
source projector past a target projector is at least the dimension drop. -/
theorem leak_ge_dim_sub (B : A → Matrix d d ℂ) (hcol : ∑ a, (B a)ᴴ * B a = 1)
    (hrow : ∑ a, B a * (B a)ᴴ = 1) {PU PV : Matrix d d ℂ}
    (hUherm : PUᴴ = PU) (hUidem : PU * PU = PU)
    (hVherm : PVᴴ = PV) (hVidem : PV * PV = PV) :
    (PU.trace).re - (PV.trace).re ≤ ∑ a, hsSqRe ((1 - PV) * (B a * PU)) := by
  have hsplit : ∀ a : A,
      hsSqRe (B a * PU) = hsSqRe (PV * (B a * PU)) + hsSqRe ((1 - PV) * (B a * PU)) :=
    fun a => hsSqRe_split_left (B a * PU) PV hVherm hVidem
  have hcap : ∀ a : A, hsSqRe (PV * (B a * PU)) ≤ hsSqRe (PV * B a) := by
    intro a
    have hassoc : PV * (B a * PU) = (PV * B a) * PU := by rw [Matrix.mul_assoc]
    rw [hassoc]
    have := hsSqRe_split_right (PV * B a) PU hUherm hUidem
    have hnn := hsSqRe_nonneg ((PV * B a) * (1 - PU))
    linarith
  have hsum : ∑ a, hsSqRe (B a * PU)
      = ∑ a, hsSqRe (PV * (B a * PU)) + ∑ a, hsSqRe ((1 - PV) * (B a * PU)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => hsplit a
  have hemit := sum_hsSqRe_mul_source B hcol hUherm hUidem
  have hcapture := sum_hsSqRe_target_mul B hrow hVherm hVidem
  have hle : ∑ a, hsSqRe (PV * (B a * PU)) ≤ (PV.trace).re := by
    rw [← hcapture]
    exact Finset.sum_le_sum fun a _ => hcap a
  rw [hemit] at hsum
  linarith

end GaloisForLFunctions.HTGeometry
