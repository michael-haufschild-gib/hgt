import GaloisForLFunctions.ArithmeticLorentzianGeometry.AnIsometricLadderCarriesNoPositiveSquare
import GaloisForLFunctions.ArithmeticLorentzianGeometry.LocalFactorsAndTheEulerProductClosure
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheTrickleDownInequalityIsTheSquareRootCount
import GaloisForLFunctions.RHTower.LiCriterion
import GaloisForLFunctions.RHTower.LiSubexponentialCriterion
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing

/-!
# RH is reflection positivity of the Cayley ladder

The Cayley map `w = 1 − 1/s` sends the critical line to the unit circle and the functional equation
`s ↦ 1 − s` to `w ↦ w⁻¹`. With complex conjugation, the zeros are invariant under the
reflection `r(w) = 1/w̄`, which fixes exactly the unit circle. In these coordinates, multiplication
by `w` plays the role of Frobenius on a ladder: for a weighted configuration `(m_a, w_a)` the
**Cayley ladder** is the Toeplitz ladder of the Li couplings
`ℓ(n) = Re Σ_a m_a (2 − w_a^n − w_a^{−n})` (`cayleyLadder`, `liCoupling`).

* **The reflection formula** (`sum_liTerm_eq`, `qf_cayleyLadder_eq`): with `p_c(z) = Σ c_i z^i`,
  `Q_K[c] = Re Σ_a m_a (2(Σ c)² − 2 p_c(w_a) p_c(w_a⁻¹))`. On primitive vectors, `Σ c = 0`, the
  ladder is `−2 Re Σ_a m_a p_c(w_a) \overline{p_c(r w_a)}`: the regularized pairing of `p_c` with
  its reflection.
* **Unitary points are reflection positive** (`hasSum_evaluation_of_unitary`,
  `qf_cayleyLadder_nonpos_of_unitary`): if every `|w_a| = 1`, the reflection is conjugation and
  `−Q_K[c]/2 = Σ_a m_a |p_c(w_a)|²` on primitive vectors. The shift `c ↦ (0, c)` multiplies `p_c`
  by `z` (`cayleyPoly_shift`): it preserves the reflected pairing at every point
  (`cayleyPairing_shift`) and is conformal with factor `|w_a|²` for the evaluation at `w_a`
  (`norm_cayleyPoly_shift`).
* **Depth-one probes** (`qf_toeplitzLadder_last_sub_zero`, `nonneg_of_forall_primitive_nonpos`):
  `Q_{n+1}[e_n − e_0] = 2ℓ(0) − 2ℓ(n)`, so reflection positivity of every ladder forces `ℓ(n) ≥ 0`.
  A ladder that is negative semidefinite on primitive vectors is hyperbolic
  (`isHyperbolic_toeplitzLadder_of_primitive`).

For `ζ` (`xiMult`, `xiCayley`) the couplings are the paired Li coefficients `2λ_n`, and Li's
criterion closes the circle:

* **RH ⇔ reflection positivity** (`riemannHypothesis_iff_cayleyLadder_nonpos`): RH holds iff every
  Cayley ladder of `ζ` is negative semidefinite on primitive vectors.
* **The sign is the Hodge index** (`riemannHypothesis_iff_cayleyLadder_nonneg`,
  `isLorentzian_cayleyLadder_of_rh`): RH holds iff every Cayley ladder is entrywise nonnegative,
  and then every ladder is Lorentzian. In Cayley coordinates the Metzler sign implies the Hodge
  index. The trickle-down step is hidden in the sign: Li positivity is equivalent to RH.
* **The couplings never decay** (`not_tendsto_xiLiPaired_re_zero`): if `2λ_n → 0`, Li's criterion
  with exponential slack gives RH, every ladder is then hyperbolic, and a decaying isometric ladder
  must be negative semidefinite (`forall_isHyperbolic_toeplitzLadder_iff`), which fails at depth two.
  The Cayley ladder carries its positive square on growing couplings, as the ladder dichotomy
  requires.

Over `𝔽_q` the same ladder, built on the normalized Frobenius eigenvalues, is the square-root
count with the sharp constant: `ℓ(n) = 2(2g − Σ_i β_i^n)` (`liCoupling_curveDatum`), so
`ℓ(n) ≥ 0` is the lower Weil bound `N_n ≥ q^n + 1 − 2g q^{n/2}`
(`liCoupling_nonneg_iff_pointCount_ge`), and reflection positivity of every Cayley ladder is RH
for the curve (`unitary_iff_cayleyLadder_nonpos`); the golden datum fails it
(`golden_not_cayleyLadder_nonpos`).
-/

noncomputable section

open Matrix Finset Filter Complex Topology
open RHTower (liTerm xiRootW xiLiPaired XiDivisorSupport)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (CurveDatum goldenDatum)

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

/-! ### The Cayley pairing of one point -/

/-- The Cayley polynomial `p_c(z) = Σ_i c_i z^i` of a ladder vector. -/
def cayleyPoly {K : ℕ} (c : Fin K → ℝ) (z : ℂ) : ℂ := ∑ i, (c i : ℂ) * z ^ (i : ℕ)

/-- `w^{|i−j|} + w^{−|i−j|} = w^i w^{−j} + w^j w^{−i}`. -/
theorem pow_dist_add_inv_pow_dist {w : ℂ} (hw : w ≠ 0) (i j : ℕ) :
    w ^ Nat.dist i j + w⁻¹ ^ Nat.dist i j = w ^ i * w⁻¹ ^ j + w ^ j * w⁻¹ ^ i := by
  have h1 : ∀ a : ℕ, w ^ a * w⁻¹ ^ a = 1 := fun a => by
    rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  rcases le_total i j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd : Nat.dist i (i + d) = d := by unfold Nat.dist; omega
    rw [hd, pow_add, pow_add, ← mul_assoc, h1, mul_comm (w ^ i) (w ^ d), mul_assoc, h1]
    ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd : Nat.dist (j + d) j = d := by unfold Nat.dist; omega
    rw [hd, pow_add, pow_add, mul_comm (w ^ j) (w ^ d), mul_assoc, h1, ← mul_assoc, h1]
    ring

/-- **The Cayley pairing of one point.** For `w ≠ 0`,
`Σ_{i,j} c_i c_j (2 − w^{|i−j|} − w^{−|i−j|}) = 2(Σ c)² − 2 p_c(w) p_c(w⁻¹)`. -/
theorem sum_liTerm_eq {K : ℕ} {w : ℂ} (hw : w ≠ 0) (c : Fin K → ℝ) :
    ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * liTerm w (Nat.dist i j) =
      2 * ((∑ i, c i : ℝ) : ℂ) ^ 2 - 2 * (cayleyPoly c w * cayleyPoly c w⁻¹) := by
  have h : ∀ i j : Fin K, ((c i * c j : ℝ) : ℂ) * liTerm w (Nat.dist i j) =
      2 * ((c i : ℂ) * c j) - ((c i : ℂ) * w ^ (i : ℕ)) * ((c j : ℂ) * w⁻¹ ^ (j : ℕ)) -
        ((c j : ℂ) * w ^ (j : ℕ)) * ((c i : ℂ) * w⁻¹ ^ (i : ℕ)) := fun i j => by
    have := pow_dist_add_inv_pow_dist hw i j
    rw [RHTower.liTerm]
    push_cast
    linear_combination (-((c i : ℂ) * c j)) * this
  have e1 : ∑ i : Fin K, ∑ j : Fin K, 2 * ((c i : ℂ) * c j) = 2 * ((∑ i, c i : ℝ) : ℂ) ^ 2 := by
    push_cast
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have e2 : ∑ i : Fin K, ∑ j : Fin K, ((c i : ℂ) * w ^ (i : ℕ)) * ((c j : ℂ) * w⁻¹ ^ (j : ℕ)) =
      cayleyPoly c w * cayleyPoly c w⁻¹ := by
    rw [cayleyPoly, cayleyPoly, Finset.sum_mul_sum]
  have e3 : ∑ i : Fin K, ∑ j : Fin K, ((c j : ℂ) * w ^ (j : ℕ)) * ((c i : ℂ) * w⁻¹ ^ (i : ℕ)) =
      cayleyPoly c w * cayleyPoly c w⁻¹ := by
    rw [Finset.sum_comm]; exact e2
  simp only [h, Finset.sum_sub_distrib, e1, e2, e3]
  ring

/-- On the unit circle the reflected point is the conjugate, and the pairing is a norm:
`p_c(w) p_c(w⁻¹) = |p_c(w)|²`. -/
theorem cayleyPoly_mul_inv_of_norm_eq_one {K : ℕ} {w : ℂ} (hw : ‖w‖ = 1) (c : Fin K → ℝ) :
    cayleyPoly c w * cayleyPoly c w⁻¹ = ((‖cayleyPoly c w‖ ^ 2 : ℝ) : ℂ) := by
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]; simp
  have hconj : cayleyPoly c w⁻¹ = (starRingEnd ℂ) (cayleyPoly c w) := by
    rw [hinv, cayleyPoly, cayleyPoly, map_sum]
    simp only [map_mul, map_pow, Complex.conj_ofReal]
  rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ### Frobenius in Cayley coordinates -/

/-- The shift `c ↦ (0, c)` multiplies the Cayley polynomial by `z`. -/
theorem cayleyPoly_shift {K : ℕ} (c : Fin K → ℝ) (z : ℂ) :
    cayleyPoly (Fin.cons 0 c : Fin (K + 1) → ℝ) z = z * cayleyPoly c z := by
  rw [cayleyPoly, Fin.sum_univ_succ, cayleyPoly, Finset.mul_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Complex.ofReal_zero, zero_mul, zero_add,
    pow_succ]
  exact sum_congr rfl fun i _ => by ring

/-- The shift preserves the reflected pairing at every point `w ≠ 0`. -/
theorem cayleyPairing_shift {K : ℕ} (c : Fin K → ℝ) {w : ℂ} (hw : w ≠ 0) :
    cayleyPoly (Fin.cons 0 c : Fin (K + 1) → ℝ) w * cayleyPoly (Fin.cons 0 c : Fin (K + 1) → ℝ) w⁻¹ =
      cayleyPoly c w * cayleyPoly c w⁻¹ := by
  rw [cayleyPoly_shift, cayleyPoly_shift]
  have : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  linear_combination (cayleyPoly c w * cayleyPoly c w⁻¹) * this

/-- The shift is conformal with factor `|w|²` for the evaluation at `w`. -/
theorem norm_cayleyPoly_shift {K : ℕ} (c : Fin K → ℝ) (w : ℂ) :
    ‖cayleyPoly (Fin.cons 0 c : Fin (K + 1) → ℝ) w‖ ^ 2 = ‖w‖ ^ 2 * ‖cayleyPoly c w‖ ^ 2 := by
  rw [cayleyPoly_shift, norm_mul, mul_pow]

/-! ### The Cayley ladder of a configuration -/

variable {α : Type*}

/-- The **Li coupling** `ℓ(n) = Re Σ_a m_a (2 − w_a^n − w_a^{−n})` of a weighted configuration. -/
def liCoupling (m : α → ℝ) (w : α → ℂ) (n : ℕ) : ℝ := (∑' a, (m a : ℂ) * liTerm (w a) n).re

theorem liCoupling_zero (m : α → ℝ) (w : α → ℂ) : liCoupling m w 0 = 0 := by
  simp [liCoupling]

/-- The **Cayley ladder**: the Toeplitz ladder of the Li couplings. -/
def cayleyLadder (m : α → ℝ) (w : α → ℂ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  toeplitzLadder (liCoupling m w) K


/-- The `(i, j)` term of the ladder form at the point `a`. -/
def cayleyTerm (m : α → ℝ) (w : α → ℂ) {K : ℕ} (c : Fin K → ℝ) (i j : Fin K) (a : α) : ℂ :=
  ((c i * c j : ℝ) : ℂ) * ((m a : ℂ) * liTerm (w a) (Nat.dist i j))

theorem sum_cayleyTerm {m : α → ℝ} {w : α → ℂ} (hw : ∀ a, w a ≠ 0) {K : ℕ} (c : Fin K → ℝ)
    (a : α) : ∑ i, ∑ j, cayleyTerm m w c i j a = (m a : ℂ) *
      (2 * ((∑ i, c i : ℝ) : ℂ) ^ 2 - 2 * (cayleyPoly c (w a) * cayleyPoly c (w a)⁻¹)) := by
  rw [← sum_liTerm_eq (hw a), Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact sum_congr rfl fun j _ => by simp only [cayleyTerm]; ring

/-- The reflected pairing is summable whenever the Li sums are: it is a finite combination of
them. -/
theorem summable_cayleyPairing {m : α → ℝ} {w : α → ℂ} (hw : ∀ a, w a ≠ 0)
    (hs : ∀ n, Summable fun a => (m a : ℂ) * liTerm (w a) n) {K : ℕ} (c : Fin K → ℝ) :
    Summable fun a => (m a : ℂ) *
      (2 * ((∑ i, c i : ℝ) : ℂ) ^ 2 - 2 * (cayleyPoly c (w a) * cayleyPoly c (w a)⁻¹)) := by
  simp_rw [← sum_cayleyTerm hw c]
  exact summable_sum fun i _ => summable_sum fun j _ => (hs _).mul_left _

/-- **The Cayley reflection formula.** If the Li sums converge,
`Q_K[c] = Re Σ_a m_a (2(Σ c)² − 2 p_c(w_a) p_c(w_a⁻¹))`. -/
theorem qf_cayleyLadder_eq {m : α → ℝ} {w : α → ℂ} (hw : ∀ a, w a ≠ 0)
    (hs : ∀ n, Summable fun a => (m a : ℂ) * liTerm (w a) n) {K : ℕ} (c : Fin K → ℝ) :
    qf (cayleyLadder m w K) c = (∑' a, (m a : ℂ) *
      (2 * ((∑ i, c i : ℝ) : ℂ) ^ 2 - 2 * (cayleyPoly c (w a) * cayleyPoly c (w a)⁻¹))).re := by
  have hsum : ∀ i j, Summable (cayleyTerm m w c i j) := fun i j => (hs _).mul_left _
  have hterm : ∀ i j : Fin K,
      c i * cayleyLadder m w K i j * c j = (∑' a, cayleyTerm m w c i j a).re := fun i j => by
    simp only [cayleyTerm]
    rw [tsum_mul_left, Complex.re_ofReal_mul]
    simp only [cayleyLadder, toeplitzLadder, Matrix.of_apply, liCoupling]
    ring
  calc qf (cayleyLadder m w K) c = ∑ i, ∑ j, (∑' a, cayleyTerm m w c i j a).re := by
        rw [qf_eq_sum]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hterm i j
    _ = (∑ i, ∑ j, ∑' a, cayleyTerm m w c i j a).re := by simp only [Complex.re_sum]
    _ = (∑' a, ∑ i, ∑ j, cayleyTerm m w c i j a).re := by
        rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsum i j]
        exact congrArg Complex.re (sum_congr rfl fun i _ =>
          (Summable.tsum_finsetSum fun j _ => hsum i j).symm)
    _ = _ := by simp only [sum_cayleyTerm hw c]

/-- **Unitary points are reflection positive.** If every `|w_a| = 1`, then on primitive vectors
`−Q_K[c] = Σ_a 2 m_a |p_c(w_a)|²`: the ladder is minus twice the evaluation Gram. -/
theorem hasSum_evaluation_of_unitary {m : α → ℝ} {w : α → ℂ} (hU : ∀ a, ‖w a‖ = 1)
    (hs : ∀ n, Summable fun a => (m a : ℂ) * liTerm (w a) n) {K : ℕ} {c : Fin K → ℝ}
    (hc : ∑ i, c i = 0) :
    HasSum (fun a => 2 * m a * ‖cayleyPoly c (w a)‖ ^ 2) (-qf (cayleyLadder m w K) c) := by
  have hw : ∀ a, w a ≠ 0 := fun a h => by
    have := hU a
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hre := Complex.hasSum_re (summable_cayleyPairing hw hs c).hasSum
  rw [← qf_cayleyLadder_eq hw hs c] at hre
  have e : ∀ a, ((m a : ℂ) * (2 * ((∑ i, c i : ℝ) : ℂ) ^ 2 -
      2 * (cayleyPoly c (w a) * cayleyPoly c (w a)⁻¹))).re =
      -(2 * m a * ‖cayleyPoly c (w a)‖ ^ 2) := fun a => by
    rw [hc, cayleyPoly_mul_inv_of_norm_eq_one (hU a)]
    have : (m a : ℂ) * (2 * ((0 : ℝ) : ℂ) ^ 2 - 2 * ((‖cayleyPoly c (w a)‖ ^ 2 : ℝ) : ℂ)) =
        ((-(2 * m a * ‖cayleyPoly c (w a)‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  simp only [e] at hre
  simpa only [neg_neg] using hre.neg

theorem qf_cayleyLadder_nonpos_of_unitary {m : α → ℝ} {w : α → ℂ} (hm : ∀ a, 0 ≤ m a)
    (hU : ∀ a, ‖w a‖ = 1) (hs : ∀ n, Summable fun a => (m a : ℂ) * liTerm (w a) n) {K : ℕ}
    {c : Fin K → ℝ} (hc : ∑ i, c i = 0) : qf (cayleyLadder m w K) c ≤ 0 := by
  have := (hasSum_evaluation_of_unitary hU hs hc).nonneg fun a => by
    have := hm a; positivity
  linarith

/-! ### Depth-one probes -/

/-- **Depth-one probe**: `Q_{n+1}[e_n − e_0] = 2ℓ(0) − 2ℓ(n)` on a Toeplitz ladder. -/
theorem qf_toeplitzLadder_last_sub_zero (ℓ : ℕ → ℝ) (n : ℕ) :
    qf (toeplitzLadder ℓ (n + 1)) (Pi.single (Fin.last n) 1 - Pi.single 0 1) =
      2 * ℓ 0 - 2 * ℓ n := by
  have e : (Pi.single (Fin.last n) 1 - Pi.single 0 1 : Fin (n + 1) → ℝ) =
      (1 : ℝ) • Pi.single (Fin.last n) 1 + (-1 : ℝ) • Pi.single 0 1 := by
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  have hd : Nat.dist n 0 = n := by unfold Nat.dist; omega
  rw [e, qf_add_smul (toeplitzLadder_isSymm ℓ _)]
  simp only [qf, bil_single_single, toeplitzLadder, Matrix.of_apply, Nat.dist_self, Fin.val_last,
    Fin.val_zero, hd]
  ring

/-- If every depth of a Toeplitz ladder with `ℓ(0) = 0` is negative semidefinite on primitive
vectors, its couplings are nonnegative. -/
theorem nonneg_of_forall_primitive_nonpos {ℓ : ℕ → ℝ} (h0 : ℓ 0 = 0)
    (h : ∀ K (c : Fin K → ℝ), ∑ i, c i = 0 → qf (toeplitzLadder ℓ K) c ≤ 0) (n : ℕ) :
    0 ≤ ℓ n := by
  have hc : ∑ i, (Pi.single (Fin.last n) 1 - Pi.single 0 1 : Fin (n + 1) → ℝ) i = 0 := by
    simp [Finset.sum_sub_distrib]
  have := h (n + 1) _ hc
  rw [qf_toeplitzLadder_last_sub_zero, h0] at this
  linarith

/-- A ladder that is negative semidefinite on primitive vectors is hyperbolic. -/
theorem isHyperbolic_toeplitzLadder_of_primitive {ℓ : ℕ → ℝ} {K : ℕ}
    (h : ∀ c : Fin K → ℝ, ∑ i, c i = 0 → qf (toeplitzLadder ℓ K) c ≤ 0) :
    IsHyperbolic (toeplitzLadder ℓ K) :=
  isHyperbolic_of_nonpos_on_ker (toeplitzLadder_isSymm ℓ K) (dotLeft fun _ => 1) fun z hz =>
    h z (by simpa [dotLeft, dotProduct] using hz)

/-! ### The Cayley ladder of `ζ` -/

/-- The multiplicity of a zero of `ξ`. -/
def xiMult (ρ : XiDivisorSupport) : ℝ :=
  ((MeromorphicOn.divisor RHTower.xi Set.univ) (ρ : ℂ) : ℝ)

/-- The Cayley point `w_ρ = 1 − 1/ρ` of a zero of `ξ`. -/
def xiCayley (ρ : XiDivisorSupport) : ℂ := xiRootW (ρ : ℂ)

/-- The Li couplings of `ζ` are the paired Li coefficients `2λ_n`. -/
theorem liCoupling_xi (n : ℕ) : liCoupling xiMult xiCayley n = (xiLiPaired n).re := rfl

theorem xiMult_pos (ρ : XiDivisorSupport) : 0 < xiMult ρ := by
  have := RHTower.xi_divisor_pos_on_support ρ
  unfold xiMult
  exact_mod_cast this

theorem xiCayley_ne_zero (ρ : XiDivisorSupport) : xiCayley ρ ≠ 0 := by
  have him := RHTower.xi_divisor_support_im_ne_zero ρ
  exact RHTower.xiRootW_ne_zero (fun h => him (by simp [h])) (fun h => him (by simp [h]))

theorem xiCayley_ne_one (ρ : XiDivisorSupport) : xiCayley ρ ≠ 1 := by
  have him := RHTower.xi_divisor_support_im_ne_zero ρ
  have h0 : (ρ : ℂ) ≠ 0 := fun h => him (by simp [h])
  intro h
  rw [xiCayley, RHTower.xiRootW, sub_eq_self, one_div, inv_eq_zero] at h
  exact h0 h

theorem summable_xiCayley (n : ℕ) :
    Summable fun ρ => (xiMult ρ : ℂ) * liTerm (xiCayley ρ) n :=
  RHTower.summable_xiLiPairedTerm n

theorem norm_xiCayley_of_rh (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    ‖xiCayley ρ‖ = 1 := by
  have him := RHTower.xi_divisor_support_im_ne_zero ρ
  exact (RHTower.norm_xiRootW_eq_one_iff fun h => him (by simp [h])).mpr
    (RHTower.xi_divisor_support_re_eq_half_of_rh hRH ρ)

theorem nonempty_xiDivisorSupport : Nonempty XiDivisorSupport := by
  obtain ⟨ρ, hρ⟩ := RHTower.riemannXi_zeroSet_infinite.nonempty
  have hxi : RHTower.xi ρ = 0 := by rw [RHTower.xi_eq_riemannXi]; exact hρ
  exact ⟨⟨ρ, RHTower.mem_xi_divisor_support_of_eq_zero hxi⟩⟩

/-- **RH is reflection positivity of the Cayley ladder**: RH holds iff every Cayley ladder of `ζ`
is negative semidefinite on primitive vectors. -/
theorem riemannHypothesis_iff_cayleyLadder_nonpos :
    RiemannHypothesis ↔ ∀ K (c : Fin K → ℝ), ∑ i, c i = 0 →
      qf (cayleyLadder xiMult xiCayley K) c ≤ 0 :=
  ⟨fun hRH _ _ hc => qf_cayleyLadder_nonpos_of_unitary (fun ρ => (xiMult_pos ρ).le)
      (norm_xiCayley_of_rh hRH) summable_xiCayley hc,
    fun h => RHTower.riemannHypothesis_of_forall_re_xiLiPaired_nonneg
      (nonneg_of_forall_primitive_nonpos (liCoupling_zero _ _) h)⟩

/-- **The sign is the Hodge index**: RH holds iff every Cayley ladder of `ζ` is entrywise
nonnegative. -/
theorem riemannHypothesis_iff_cayleyLadder_nonneg :
    RiemannHypothesis ↔ ∀ K (i j : Fin K), 0 ≤ cayleyLadder xiMult xiCayley K i j := by
  constructor
  · intro hRH K i j
    simp only [cayleyLadder, toeplitzLadder, Matrix.of_apply, liCoupling_xi]
    exact RHTower.re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    refine RHTower.riemannHypothesis_of_forall_re_xiLiPaired_nonneg fun n => ?_
    have hd : Nat.dist n 0 = n := by unfold Nat.dist; omega
    have := h (n + 1) (Fin.last n) 0
    simpa only [cayleyLadder, toeplitzLadder, Matrix.of_apply, Fin.val_last, Fin.val_zero, hd,
      liCoupling_xi] using this

/-- Under RH every Cayley ladder of `ζ` is Lorentzian. -/
theorem isLorentzian_cayleyLadder_of_rh (hRH : RiemannHypothesis) (K : ℕ) :
    IsLorentzian (cayleyLadder xiMult xiCayley K) :=
  ⟨toeplitzLadder_isSymm _ K, riemannHypothesis_iff_cayleyLadder_nonneg.mp hRH K,
    isHyperbolic_toeplitzLadder_of_primitive fun c hc =>
      riemannHypothesis_iff_cayleyLadder_nonpos.mp hRH K c hc⟩

/-- Under RH the Cayley ladder of `ζ` is minus twice the evaluation Gram of the zeros:
`−Q_K[c] = Σ_ρ 2 m_ρ |p_c(w_ρ)|²` for `Σ c = 0`. -/
theorem hasSum_xi_evaluation_of_rh (hRH : RiemannHypothesis) {K : ℕ} {c : Fin K → ℝ}
    (hc : ∑ i, c i = 0) :
    HasSum (fun ρ => 2 * xiMult ρ * ‖cayleyPoly c (xiCayley ρ)‖ ^ 2)
      (-qf (cayleyLadder xiMult xiCayley K) c) :=
  hasSum_evaluation_of_unitary (norm_xiCayley_of_rh hRH) summable_xiCayley hc

theorem xiLiPaired_zero_re : (xiLiPaired 0).re = 0 := liCoupling_zero xiMult xiCayley

/-- Under RH the first coupling is positive: `2λ_1 = Σ_ρ m_ρ |w_ρ − 1|² > 0`. -/
theorem xiLiPaired_one_re_pos_of_rh (hRH : RiemannHypothesis) : 0 < (xiLiPaired 1).re := by
  set c : Fin 2 → ℝ := Pi.single (Fin.last 1) 1 - Pi.single 0 1
  have hc : ∑ i, c i = 0 := by simp [c, Finset.sum_sub_distrib]
  have hq : qf (cayleyLadder xiMult xiCayley 2) c = 2 * 0 - 2 * (xiLiPaired 1).re := by
    rw [cayleyLadder, qf_toeplitzLadder_last_sub_zero, liCoupling_zero, liCoupling_xi]
  have hp : ∀ z : ℂ, cayleyPoly c z = z - 1 := fun z => by
    simp [cayleyPoly, c, Fin.sum_univ_two, Pi.single_apply]
    ring
  obtain ⟨ρ⟩ := nonempty_xiDivisorSupport
  have hpos : 0 < 2 * xiMult ρ * ‖cayleyPoly c (xiCayley ρ)‖ ^ 2 := by
    rw [hp]
    have := xiMult_pos ρ
    have : 0 < ‖xiCayley ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (xiCayley_ne_one ρ))
    positivity
  have hlt := hasSum_lt (f := fun _ => (0 : ℝ)) (i := ρ)
    (fun σ => by have := (xiMult_pos σ).le; positivity) hpos hasSum_zero
    (hasSum_xi_evaluation_of_rh hRH hc)
  rw [hq] at hlt
  linarith

/-- **The Li couplings of `ζ` never decay.** If `2λ_n → 0`, Li's criterion with exponential slack
gives RH; then every Cayley ladder is hyperbolic, a decaying isometric ladder must be negative
semidefinite, and the depth-two ladder is not, since `2λ_1 > 0`. -/
theorem not_tendsto_xiLiPaired_re_zero :
    ¬ Tendsto (fun n => (xiLiPaired n).re) atTop (𝓝 0) := by
  intro hdec
  have hRH : RiemannHypothesis := by
    obtain ⟨B, hB⟩ := hdec.bddBelow_range
    rw [RHTower.riemannHypothesis_iff_xiLiPaired_subexp]
    intro r hr
    refine ⟨max (-B) 0, fun n => ?_⟩
    have h1 : B ≤ (xiLiPaired n).re := hB ⟨n, rfl⟩
    have h2 : 1 ≤ r ^ n := one_le_pow₀ hr.le
    have h3 : 0 ≤ max (-B) 0 := le_max_right _ _
    have h4 : -B ≤ max (-B) 0 := le_max_left _ _
    nlinarith
  have hhyp : ∀ K, IsHyperbolic (toeplitzLadder (liCoupling xiMult xiCayley) K) := fun K =>
    isHyperbolic_toeplitzLadder_of_primitive fun c hc =>
      riemannHypothesis_iff_cayleyLadder_nonpos.mp hRH K c hc
  have hnsd := (forall_isHyperbolic_toeplitzLadder_iff (c := liCoupling xiMult xiCayley) hdec).mp
    hhyp 2 fun _ => 1
  have h2 : qf (toeplitzLadder (liCoupling xiMult xiCayley) 2) (fun _ => 1) =
      2 * (xiLiPaired 1).re := by
    simp [qf_eq_sum, Fin.sum_univ_two, toeplitzLadder, Nat.dist, liCoupling_xi, xiLiPaired_zero_re]
    ring
  rw [h2] at hnsd
  linarith [xiLiPaired_one_re_pos_of_rh hRH]

/-! ### Calibration over finite fields -/

section FiniteField

variable {ι : Type*} [Fintype ι]

/-- Over `𝔽_q` the Li coupling of the normalized Frobenius eigenvalues is `2(2g − Σ_i β_i^n)`. -/
theorem liCoupling_curveDatum (D : CurveDatum ι) (n : ℕ) :
    liCoupling (fun _ => 1) D.β n = 2 * (Fintype.card ι - D.trace n) := by
  have hinv : ∀ i, (D.β i)⁻¹ = D.β (D.fePerm i) := fun i =>
    (eq_inv_of_mul_eq_one_left (D.β_fePerm i)).symm
  have hsum : ∑ i, (D.β i)⁻¹ ^ n = D.powerSum n := by
    simp_rw [hinv]
    exact Equiv.sum_comp D.fePerm (fun i => D.β i ^ n)
  have hps : ∑ i, D.β i ^ n = (D.trace n : ℂ) := D.powerSum_eq_trace n
  rw [liCoupling, tsum_fintype]
  simp only [Complex.ofReal_one, one_mul, RHTower.liTerm, Finset.sum_sub_distrib, hsum, hps,
    D.powerSum_eq_trace, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp
  ring

/-- The Li sign at depth `n` is Weil's lower bound with the sharp constant `2g = |ι|`:
`ℓ(n) ≥ 0 ⇔ N_n ≥ q^n + 1 − 2g q^{n/2}`. -/
theorem liCoupling_nonneg_iff_pointCount_ge (D : CurveDatum ι) (n : ℕ) :
    0 ≤ liCoupling (fun _ => 1) D.β n ↔
      D.q ^ n + 1 - (Fintype.card ι : ℝ) * D.sqrtq ^ n ≤ D.pointCount n := by
  rw [liCoupling_curveDatum, ← D.trace_le_iff_pointCount_ge]
  constructor <;> intro h <;> linarith

/-- **Over `𝔽_q` reflection positivity of the Cayley ladder is RH for the curve.** -/
theorem unitary_iff_cayleyLadder_nonpos (D : CurveDatum ι) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ K (c : Fin K → ℝ), ∑ i, c i = 0 →
      qf (cayleyLadder (fun _ => 1) D.β K) c ≤ 0 := by
  constructor
  · intro hU K c hc
    exact qf_cayleyLadder_nonpos_of_unitary (fun _ => zero_le_one) hU
      (fun n => (hasSum_fintype _).summable) hc
  · intro h
    refine D.unitary_of_trace_le (C := Fintype.card ι) fun k => ?_
    have := nonneg_of_forall_primitive_nonpos (liCoupling_zero _ _) h k
    rw [liCoupling_curveDatum] at this
    linarith

/-- The golden datum is not reflection positive. -/
theorem golden_not_cayleyLadder_nonpos :
    ¬ ∀ K (c : Fin K → ℝ), ∑ i, c i = 0 →
      qf (cayleyLadder (fun _ => 1) goldenDatum.β K) c ≤ 0 := fun h =>
  ArithmeticCastelnuovoSeveri.goldenDatum_not_unitary ((unitary_iff_cayleyLadder_nonpos _).mpr h)

end FiniteField

end GaloisForLFunctions.ArithmeticLorentzianGeometry
