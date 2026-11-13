import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsTheSignOfWeilsFormOnStepPackets

/-!
# The binding energy of a window is at most its pole capacity

The neutral part of a window is Weil's form minus the poles: on a step packet `σ`,
`N(σ) = W(σ) − 2 (Σ σ_j d_j)(Σ σ_j)`, with `d_j = log((a + 1)/a)` the degree of the block `a`.
The pole term is a form of rank two, and its largest value on packets of unit mass is at most the
**pole capacity** of the window `(R, R + J]`, of ratio `ρ = (R + J)/R`:

  `cap = J/√(R(R + J)) + log ρ = 2 sinh(log ρ / 2) + log ρ = √ρ − 1/√ρ + log ρ`

(`poleCapacity_eq_sinh`, `two_mul_charges_le_poleCapacity`). The bound uses `d_a ≤ 1/√(a(a + 1))`,
which is `t ≤ sinh t` at `t = d_a / 2` (`blockDegree_le_inv_sqrt`), so the degrees have square sum
at most `1/R − 1/(R + J)` (`sum_sq_blockDegree_le`), and a weighted Cauchy–Schwarz inequality
(`two_mul_sum_mul_sum_le`). At infinite block size `cap` is the positive eigenvalue
`2(sinh ℓ + ℓ)`, `ℓ = log ρ / 2`, of the pole form of a window.

So for an eigenvector `φ` of the window, with eigenvalue `λ = −μ`, unconditionally
(`binding_add_packetForm_le`)

  `μ Σ φ² + W(φ) ≤ cap · Σ φ²`:

**the binding energy and Weil's form of the packet share the pole capacity.** Under RH Weil's
form is nonnegative on step packets, so `μ ≤ √ρ − 1/√ρ + log ρ` at every block size
(`neg_eigenvalue_le_poleCapacity_of_riemannHypothesis`); a window whose binding energy exceeds
its pole capacity carries a step packet of negative Weil form, hence an off-line zero
(`not_riemannHypothesis_of_poleCapacity_lt`). Without hypothesis the binding energy is at least a
fixed multiple of `√ρ` (`eigenvalue_le_twoEnds`): the floor trees reproduce the pole up to a
constant factor, and RH caps the factor at one.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### The degrees of the blocks -/

/-- **The degree of a block is at most `1/√(a(a + 1))`**: at `t = d_a/2`, `e^{2t} = (a + 1)/a`
and `t ≤ sinh t = 1/(2√(a(a + 1)))`. -/
theorem blockDegree_le_inv_sqrt {a : ℕ} (ha : 1 ≤ a) :
    blockDegree a ≤ 1 / Real.sqrt (a * (a + 1)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have ha0' : (a : ℝ) ≠ 0 := ha0.ne'
  obtain ⟨t, ht_def⟩ : ∃ t, t = blockDegree a / 2 := ⟨_, rfl⟩
  have ht : 0 ≤ t := by rw [ht_def]; exact (div_pos (blockDegree_pos ha) two_pos).le
  have hEF : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : Real.exp t * Real.exp t = ((a + 1 : ℕ) : ℝ) / a := by
    rw [← Real.exp_add, show t + t = blockDegree a by rw [ht_def]; ring, blockDegree,
      Real.exp_sub, Real.exp_log (show (0 : ℝ) < ((a + 1 : ℕ) : ℝ) by positivity),
      Real.exp_log ha0]
  have key : (a : ℝ) * (Real.exp t * Real.exp t) = a + 1 := by
    rw [h2, mul_div_cancel₀ _ ha0', Nat.cast_add_one]
  have hS : Real.sqrt (a * (a + 1)) = a * Real.exp t := by
    rw [show (a : ℝ) * (a + 1) = (a * Real.exp t) ^ 2 by
      rw [mul_pow, sq (a : ℝ), sq (Real.exp t), mul_assoc, key]]
    exact Real.sqrt_sq (by positivity)
  have hsinh : t ≤ (Real.exp t - Real.exp (-t)) / 2 := by
    have := Real.self_le_sinh_iff.mpr ht
    rwa [Real.sinh_eq] at this
  have hval : Real.exp t - Real.exp (-t) = 1 / (a * Real.exp t) := by
    rw [eq_div_iff (mul_pos ha0 (Real.exp_pos t)).ne']
    calc (Real.exp t - Real.exp (-t)) * (a * Real.exp t) =
          a * (Real.exp t * Real.exp t) - a * (Real.exp t * Real.exp (-t)) := by ring
      _ = 1 := by rw [key, hEF]; ring
  rw [hS]
  calc blockDegree a = 2 * t := by rw [ht_def]; ring
    _ ≤ Real.exp t - Real.exp (-t) := by linarith
    _ = 1 / (a * Real.exp t) := hval

/-- **The degrees of the blocks of a window have square sum at most `1/R − 1/(R + J)`.** -/
theorem sum_sq_blockDegree_le {R : ℕ} (hR : 1 ≤ R) (J : ℕ) :
    ∑ j ∈ range J, blockDegree (R + j) ^ 2 ≤ 1 / (R : ℝ) - 1 / ((R + J : ℕ) : ℝ) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have ha : 1 ≤ R + J := by omega
    have ha0 : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
    have hx0 : ((R + J : ℕ) : ℝ) ≠ 0 := ha0.ne'
    have hx1 : ((R + J : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    have hprod : (0 : ℝ) < ((R + J : ℕ) : ℝ) * (((R + J : ℕ) : ℝ) + 1) :=
      mul_pos ha0 (by positivity)
    have h1 : blockDegree (R + J) ^ 2 ≤ (1 / Real.sqrt (((R + J : ℕ) : ℝ) *
        (((R + J : ℕ) : ℝ) + 1))) ^ 2 :=
      pow_le_pow_left₀ (blockDegree_pos ha).le (blockDegree_le_inv_sqrt ha) 2
    rw [div_pow, one_pow, Real.sq_sqrt hprod.le] at h1
    have e : 1 / ((R + J : ℕ) : ℝ) - 1 / ((R + (J + 1) : ℕ) : ℝ) =
        1 / (((R + J : ℕ) : ℝ) * (((R + J : ℕ) : ℝ) + 1)) := by
      rw [show R + (J + 1) = (R + J) + 1 by omega, Nat.cast_add_one, div_sub_div _ _ hx0 hx1,
        one_mul, mul_one, add_sub_cancel_left]
    linarith

/-- The degrees of the blocks of a window add up to its logarithmic length. -/
theorem sum_blockDegree_window (R J : ℕ) :
    ∑ j ∈ range J, blockDegree (R + j) = Real.log ((R + J : ℕ) : ℝ) - Real.log R := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, blockDegree, show R + J + 1 = R + (J + 1) by omega]
    ring

/-- `4xy ≤ (qx + y/q)²` for `q > 0`. -/
theorem four_mul_le_sq_add_div {q : ℝ} (hq : 0 < q) (x y : ℝ) :
    4 * (x * y) ≤ (q * x + y / q) ^ 2 := by
  have hxy : q * x * (y / q) = x * y := by
    rw [mul_comm q x, mul_assoc, mul_div_cancel₀ y hq.ne']
  nlinarith [sq_nonneg (q * x - y / q), hxy]

/-- **Weighted Cauchy–Schwarz for the pole term.** For every `q > 0`,
`2 (Σ σ d)(Σ σ) ≤ ((q² D + 2L + J/q²)/2) Σ σ²` when `Σ d² ≤ D` and `Σ d = L`: apply
Cauchy–Schwarz to the weights `q d_j + 1/q` and `4xy ≤ (qx + y/q)²`. -/
theorem two_mul_sum_mul_sum_le {J : ℕ} (σ d : ℕ → ℝ) {D L q : ℝ} (hq : 0 < q)
    (hD : ∑ j ∈ range J, d j ^ 2 ≤ D) (hL : ∑ j ∈ range J, d j = L) :
    2 * ((∑ j ∈ range J, σ j * d j) * ∑ j ∈ range J, σ j) ≤
      (q ^ 2 * D + 2 * L + J / q ^ 2) / 2 * ∑ j ∈ range J, σ j ^ 2 := by
  have hq1 : q * (1 / q) = 1 := mul_one_div_cancel hq.ne'
  have hcs : (∑ j ∈ range J, σ j * (q * d j + 1 / q)) ^ 2 ≤
      (∑ j ∈ range J, σ j ^ 2) * ∑ j ∈ range J, (q * d j + 1 / q) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hlin : ∑ j ∈ range J, σ j * (q * d j + 1 / q) =
      q * ∑ j ∈ range J, σ j * d j + (∑ j ∈ range J, σ j) / q := by
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hw : ∑ j ∈ range J, (q * d j + 1 / q) ^ 2 =
      q ^ 2 * ∑ j ∈ range J, d j ^ 2 + 2 * L + J / q ^ 2 := by
    have e : ∀ j, (q * d j + 1 / q) ^ 2 = q ^ 2 * d j ^ 2 + 2 * d j + 1 / q ^ 2 := fun j => by
      calc (q * d j + 1 / q) ^ 2 = q ^ 2 * d j ^ 2 + 2 * d j * (q * (1 / q)) + (1 / q) ^ 2 := by
            ring
        _ = q ^ 2 * d j ^ 2 + 2 * d j + 1 / q ^ 2 := by rw [hq1, _root_.one_div_pow]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hL, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rw [hlin, hw] at hcs
  have h4 := (four_mul_le_sq_add_div hq (∑ j ∈ range J, σ j * d j)
    (∑ j ∈ range J, σ j)).trans hcs
  have hm : 0 ≤ ∑ j ∈ range J, σ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hDm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (sq_nonneg q)) hm
  linarith [h4, hDm]

/-! ### The pole capacity -/

/-- The pole capacity of the window `(R, R + J]`. -/
def poleCapacity (R J : ℕ) : ℝ :=
  J / Real.sqrt (R * (R + J)) + Real.log (((R + J : ℕ) : ℝ) / R)

/-- **The pole capacity is `2 sinh(L/2) + L`**, `L = log((R + J)/R)`, i.e. `√ρ − 1/√ρ + log ρ`. -/
theorem poleCapacity_eq_sinh {R : ℕ} (hR : 1 ≤ R) (J : ℕ) :
    poleCapacity R J = 2 * Real.sinh (Real.log (((R + J : ℕ) : ℝ) / R) / 2) +
      Real.log (((R + J : ℕ) : ℝ) / R) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hRJ : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  obtain ⟨t, ht_def⟩ : ∃ t, t = Real.log (((R + J : ℕ) : ℝ) / R) / 2 := ⟨_, rfl⟩
  have hEF : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2 : (R : ℝ) * (Real.exp t * Real.exp t) = R + J := by
    rw [← Real.exp_add, show t + t = Real.log (((R + J : ℕ) : ℝ) / R) by rw [ht_def]; ring,
      Real.exp_log (div_pos hRJ hR0), mul_div_cancel₀ _ hR0.ne', Nat.cast_add]
  have hS : Real.sqrt (R * (R + J)) = R * Real.exp t := by
    rw [show (R : ℝ) * (R + J) = (R * Real.exp t) ^ 2 by
      rw [mul_pow, sq (R : ℝ), sq (Real.exp t), mul_assoc, h2]]
    exact Real.sqrt_sq (by positivity)
  rw [← ht_def]
  unfold poleCapacity
  rw [Real.sinh_eq, hS]
  congr 1
  rw [div_eq_iff (mul_pos hR0 (Real.exp_pos t)).ne']
  calc (J : ℝ) = R * (Real.exp t * Real.exp t) - R * (Real.exp t * Real.exp (-t)) := by
        rw [h2, hEF]; ring
    _ = 2 * ((Real.exp t - Real.exp (-t)) / 2) * (R * Real.exp t) := by ring

/-- **The pole term of a step packet is at most the pole capacity times the mass.** -/
theorem two_mul_charges_le_poleCapacity {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    2 * ((∑ j ∈ range J, σ j * blockDegree (R + j)) * ∑ j ∈ range J, σ j) ≤
      poleCapacity R J * ∑ j ∈ range J, σ j ^ 2 := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hRJ : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have hRJ2 : (0 : ℝ) < R + J := by
    have := Nat.cast_nonneg (α := ℝ) J
    linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (R * (R + J)) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr (mul_pos hR0 hRJ2)
  have hss : s * s = R * (R + J) := by rw [hs_def]; exact Real.mul_self_sqrt (by positivity)
  have hq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hq2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hL : ∑ j ∈ range J, blockDegree (R + j) = Real.log (((R + J : ℕ) : ℝ) / R) := by
    rw [sum_blockDegree_window, Real.log_div hRJ.ne' hR0.ne']
  have h := two_mul_sum_mul_sum_le (J := J) σ (fun j => blockDegree (R + j)) hq
    (sum_sq_blockDegree_le hR J) hL
  rw [hq2] at h
  have hD : 1 / (R : ℝ) - 1 / ((R + J : ℕ) : ℝ) = J / (s * s) := by
    rw [hss, Nat.cast_add, div_sub_div _ _ hR0.ne' hRJ2.ne', one_mul, mul_one,
      add_sub_cancel_left]
  have hsD : s * (J / (s * s)) = J / s := by
    rw [← div_div, mul_div_cancel₀ _ hs.ne']
  have hcap : (s * (1 / (R : ℝ) - 1 / ((R + J : ℕ) : ℝ)) +
      2 * Real.log (((R + J : ℕ) : ℝ) / R) + J / s) / 2 = poleCapacity R J := by
    unfold poleCapacity
    rw [← hs_def, hD, hsD]
    ring
  rw [hcap] at h
  exact h

/-! ### The binding energy and Weil's form of the packet -/

theorem sum_range_sq_extendFin {J : ℕ} (φ : Fin J → ℝ) :
    ∑ j ∈ range J, extendFin φ j ^ 2 = ∑ k, φ k * φ k := by
  rw [show ∑ k, φ k * φ k = ∑ j ∈ range J, extendFin (fun k => φ k * φ k) j from
    sum_fin_eq_sum_range_extendFin _]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [extendFin, dif_pos (Finset.mem_range.mp hj), sq]

/-- **The binding energy and Weil's form of the packet share the pole capacity.** For an
eigenvector `φ` of the window with eigenvalue `λ`, `−λ Σ φ² + W(φ) ≤ cap · Σ φ²`. -/
theorem binding_add_packetForm_le {Q R J : ℕ} (hR : 1 ≤ R) {φ : Fin J → ℝ} {lam : ℝ}
    (heig : neutralWindow Q R J *ᵥ φ = lam • φ) :
    -lam * ∑ j ∈ range J, extendFin φ j ^ 2 + packetForm Q (stepPacket R J (extendFin φ)) ≤
      poleCapacity R J * ∑ j ∈ range J, extendFin φ j ^ 2 := by
  have hN := neutralForm_stepPacket hR Q J (extendFin φ)
  rw [neutralForm, integral_stepPacket_mul_exp_neg hR, integral_stepPacket_mul_exp hR] at hN
  have hb : bilin (neutralWindow Q R J) φ φ =
      ∑ j ∈ range J, ∑ l ∈ range J,
        extendFin φ j * extendFin φ l * neutralBlock Q (R + j) (R + l) :=
    sum_fin_windowMatrix_eq (neutralBlock Q) R φ
  have heigen : bilin (neutralWindow Q R J) φ φ = lam * ∑ j ∈ range J, extendFin φ j ^ 2 := by
    rw [bilin_eigen heig, sum_range_sq_extendFin]
  rw [hb] at heigen
  have hcap := two_mul_charges_le_poleCapacity hR J (extendFin φ)
  linarith

/-- **Under RH the binding energy of every window is at most its pole capacity**
`√ρ − 1/√ρ + log ρ`, at every block size. -/
theorem neg_eigenvalue_le_poleCapacity_of_riemannHypothesis (hRH : RiemannHypothesis)
    {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 1 ≤ J) (hQ : R + J ≤ Q * R) {φ : Fin J → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : neutralWindow Q R J *ᵥ φ = lam • φ) :
    -lam ≤ poleCapacity R J := by
  have h := binding_add_packetForm_le hR heig
  have hW := packetForm_stepPacket_nonneg_of_riemannHypothesis hRH hR hQ (extendFin φ)
  have hpos : 0 < ∑ j ∈ range J, extendFin φ j ^ 2 := by
    rw [sum_range_sq_extendFin]
    exact Finset.sum_pos (fun k _ => mul_pos (hφ k) (hφ k)) ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  nlinarith

/-- **A window that binds beyond its pole capacity carries an off-line zero.** -/
theorem not_riemannHypothesis_of_poleCapacity_lt {Q R J : ℕ} (hR : 1 ≤ R) (hJ : 1 ≤ J)
    (hQ : R + J ≤ Q * R) {φ : Fin J → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R J *ᵥ φ = lam • φ) (hlt : poleCapacity R J < -lam) :
    ¬ RiemannHypothesis := fun hRH =>
  absurd (neg_eigenvalue_le_poleCapacity_of_riemannHypothesis hRH hR hJ hQ hφ heig)
    (not_le.mpr hlt)

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
