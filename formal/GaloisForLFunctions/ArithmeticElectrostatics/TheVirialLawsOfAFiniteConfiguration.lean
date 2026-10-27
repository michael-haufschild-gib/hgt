import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheRankinSelbergSquareSeesTheFieldOfTheOtherZeros

/-!
# The virial laws of a finite configuration

A finite configuration of distinct charges `z_j ∈ ℂ` with multiplicities `m_j` has the field
`E_j = Σ_{k ≠ j} m_k/(z_j − z_k)` (`fieldAt`), the simple Laurent coefficient of the squared
logarithmic derivative divided by `2 m_j`. Pairing the field with a displacement and symmetrizing
over ordered pairs gives exact laws:

* **Newton's third law** (`sum_mul_fieldAt_eq_zero`): `Σ_j m_j E_j = 0`.
* **Stieltjes' virial** (`sum_mul_mul_fieldAt`): `Σ_j m_j z_j E_j = ½((Σ m)² − Σ m²)`, a pure count.
* **The transverse virial** (`sum_mul_re_fieldAt_eq_transverseEnergy`): for real multiplicities and
  every centre `c`, `Σ_j m_j (Re z_j − c) Re E_j` is the transverse energy
  `½ Σ_{j ≠ k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²`: the work of the field against the
  displacement is a Dirichlet energy on the complete graph with conductances `m_j m_k/|z_j − z_k|²`.
* **The vertical virial** and **the energy count** (`transverseEnergy_add_verticalEnergy`): the
  transverse and vertical energies add up to `½((Σ m)² − Σ m²)`.

So equilibrium (vanishing transverse field) is an identity-level statement about a positive
quadratic energy of the real parts: the field is its gradient, and a configuration is critical
exactly when all of its energy is vertical.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticElectrostatics

open GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Symmetrization over ordered pairs -/

/-- Sums over ordered pairs of distinct indices are invariant under swapping the pair. -/
theorem sum_sum_erase_swap {M : Type*} [AddCommGroup M] (F : ι → ι → M) :
    ∑ j, ∑ k ∈ univ.erase j, F j k = ∑ j, ∑ k ∈ univ.erase j, F k j := by
  have e : ∀ G : ι → ι → M, ∑ j, ∑ k ∈ univ.erase j, G j k = ∑ j, ∑ k, G j k - ∑ j, G j j := by
    intro G
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => sum_erase_eq_sub (mem_univ j)
  rw [e F, e (fun j k => F k j), sum_comm]

/-- Twice an ordered-pair sum is the ordered-pair sum of the symmetrized summand. -/
theorem two_mul_sum_sum_erase (F : ι → ι → ℂ) :
    2 * ∑ j, ∑ k ∈ univ.erase j, F j k = ∑ j, ∑ k ∈ univ.erase j, (F j k + F k j) := by
  rw [two_mul]
  conv_lhs => arg 2; rw [sum_sum_erase_swap]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => (sum_add_distrib).symm

theorem two_mul_sum_sum_erase_real (F : ι → ι → ℝ) :
    2 * ∑ j, ∑ k ∈ univ.erase j, F j k = ∑ j, ∑ k ∈ univ.erase j, (F j k + F k j) := by
  rw [two_mul]
  conv_lhs => arg 2; rw [sum_sum_erase_swap]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => (sum_add_distrib).symm

/-- The ordered-pair sum of `m_j m_k` is `(Σ m)² − Σ m²`. -/
theorem sum_sum_erase_mul {R : Type*} [CommRing R] (m : ι → R) :
    ∑ j, ∑ k ∈ univ.erase j, m j * m k = (∑ j, m j) ^ 2 - ∑ j, m j ^ 2 := by
  rw [sq, sum_mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_erase_eq_sub (mem_univ j), sq]

/-! ### Newton's law and Stieltjes' virial -/

/-- The field written as the ordered-pair summand `m_j m_k/(z_j − z_k)` after weighting by `m_j`. -/
theorem mul_fieldAt (m z : ι → ℂ) (g : ι → ℂ) (j : ι) :
    g j * m j * fieldAt m z j = ∑ k ∈ univ.erase j, g j * m j * m k / (z j - z k) := by
  rw [fieldAt, mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-- **Newton's third law**: the total weighted field vanishes. -/
theorem sum_mul_fieldAt_eq_zero (m z : ι → ℂ) (hz : Function.Injective z) :
    ∑ j, m j * fieldAt m z j = 0 := by
  have h2 : 2 * ∑ j, m j * fieldAt m z j = 0 := by
    have hrw : ∑ j, m j * fieldAt m z j =
        ∑ j, ∑ k ∈ univ.erase j, m j * m k / (z j - z k) := by
      refine sum_congr rfl fun j _ => ?_
      simpa using mul_fieldAt m z (fun _ => 1) j
    rw [hrw, two_mul_sum_sum_erase]
    refine sum_eq_zero fun j _ => sum_eq_zero fun k hk => ?_
    have hd : z j - z k ≠ 0 := sub_ne_zero.mpr fun h => (ne_of_mem_erase hk) (hz h).symm
    have hd' : z k - z j ≠ 0 := fun h => hd (by rw [← neg_sub, h, neg_zero])
    field_simp
    ring
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **Stieltjes' virial**: `Σ_j m_j z_j E_j = ½((Σ m)² − Σ m²)`, independent of the positions. -/
theorem sum_mul_mul_fieldAt (m z : ι → ℂ) (hz : Function.Injective z) :
    ∑ j, m j * z j * fieldAt m z j = ((∑ j, m j) ^ 2 - ∑ j, m j ^ 2) / 2 := by
  have hrw : ∑ j, m j * z j * fieldAt m z j =
      ∑ j, ∑ k ∈ univ.erase j, z j * m j * m k / (z j - z k) := by
    refine sum_congr rfl fun j _ => ?_
    rw [mul_comm (m j) (z j)]
    exact mul_fieldAt m z z j
  have h2 : 2 * ∑ j, m j * z j * fieldAt m z j = (∑ j, m j) ^ 2 - ∑ j, m j ^ 2 := by
    rw [hrw, two_mul_sum_sum_erase, ← sum_sum_erase_mul]
    refine sum_congr rfl fun j _ => sum_congr rfl fun k hk => ?_
    have hd : z j - z k ≠ 0 := sub_ne_zero.mpr fun h => (ne_of_mem_erase hk) (hz h).symm
    have hd' : z k - z j ≠ 0 := fun h => hd (by rw [← neg_sub, h, neg_zero])
    field_simp
    ring
  rw [← h2]
  ring

/-! ### The transverse and vertical virial -/

/-- The **transverse energy** `½ Σ_{j ≠ k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²`. -/
noncomputable def transverseEnergy (m : ι → ℝ) (z : ι → ℂ) : ℝ :=
  (∑ j, ∑ k ∈ univ.erase j,
    m j * m k * ((z j).re - (z k).re) ^ 2 / Complex.normSq (z j - z k)) / 2

/-- The **vertical energy** `½ Σ_{j ≠ k} m_j m_k (Im z_j − Im z_k)²/|z_j − z_k|²`. -/
noncomputable def verticalEnergy (m : ι → ℝ) (z : ι → ℂ) : ℝ :=
  (∑ j, ∑ k ∈ univ.erase j,
    m j * m k * ((z j).im - (z k).im) ^ 2 / Complex.normSq (z j - z k)) / 2

/-- The transverse field of real multiplicities: `Re E_j = Σ_{k ≠ j} m_k (Re z_j − Re z_k)/|z_j − z_k|²`. -/
theorem re_fieldAt (m : ι → ℝ) (z : ι → ℂ) (j : ι) :
    (fieldAt (fun k => (m k : ℂ)) z j).re =
      ∑ k ∈ univ.erase j, m k * ((z j).re - (z k).re) / Complex.normSq (z j - z k) := by
  rw [fieldAt, Complex.re_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero,
    Complex.sub_re]

/-- The vertical field of real multiplicities: `−Im E_j = Σ_{k ≠ j} m_k (Im z_j − Im z_k)/|z_j − z_k|²`. -/
theorem neg_im_fieldAt (m : ι → ℝ) (z : ι → ℂ) (j : ι) :
    -(fieldAt (fun k => (m k : ℂ)) z j).im =
      ∑ k ∈ univ.erase j, m k * ((z j).im - (z k).im) / Complex.normSq (z j - z k) := by
  rw [fieldAt, Complex.im_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub,
    Complex.sub_im]
  ring

/-- The symmetric part of a displacement–field summand is the squared difference. -/
private theorem pair_virial (a b c w : ℝ) (mj mk : ℝ) :
    (a - c) * mj * (mk * (a - b) / w) + (b - c) * mk * (mj * (b - a) / w) =
      mj * mk * (a - b) ^ 2 / w := by
  ring

/-- Displacement-weighted field sums are halves of symmetrized pair sums. -/
private theorem sum_virial (m : ι → ℝ) (z : ι → ℂ) (u : ι → ℝ) (c : ℝ) :
    ∑ j, (u j - c) * m j *
        (∑ k ∈ univ.erase j, m k * (u j - u k) / Complex.normSq (z j - z k)) =
      (∑ j, ∑ k ∈ univ.erase j,
        m j * m k * (u j - u k) ^ 2 / Complex.normSq (z j - z k)) / 2 := by
  have hrw : ∑ j, (u j - c) * m j *
      (∑ k ∈ univ.erase j, m k * (u j - u k) / Complex.normSq (z j - z k)) =
      ∑ j, ∑ k ∈ univ.erase j,
        (u j - c) * m j * (m k * (u j - u k) / Complex.normSq (z j - z k)) :=
    sum_congr rfl fun j _ => by rw [mul_sum]
  have h2 := two_mul_sum_sum_erase_real (fun j k =>
    (u j - c) * m j * (m k * (u j - u k) / Complex.normSq (z j - z k)))
  rw [hrw, eq_div_iff (two_ne_zero' ℝ), mul_comm, h2]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [show Complex.normSq (z k - z j) = Complex.normSq (z j - z k) by
    rw [← Complex.normSq_neg, neg_sub]]
  exact pair_virial _ _ _ _ _ _

/-- **The transverse virial**: the work of the transverse field against the displacement from any
centre `c` is the transverse energy. -/
theorem sum_mul_re_fieldAt_eq_transverseEnergy (m : ι → ℝ) (z : ι → ℂ) (c : ℝ) :
    ∑ j, ((z j).re - c) * m j * (fieldAt (fun k => (m k : ℂ)) z j).re =
      transverseEnergy m z := by
  simp_rw [re_fieldAt]
  exact sum_virial m z (fun j => (z j).re) c

/-- **The vertical virial**: the work of the vertical field against the height is the vertical
energy. -/
theorem sum_mul_neg_im_fieldAt_eq_verticalEnergy (m : ι → ℝ) (z : ι → ℂ) (c : ℝ) :
    ∑ j, ((z j).im - c) * m j * -(fieldAt (fun k => (m k : ℂ)) z j).im =
      verticalEnergy m z := by
  simp_rw [neg_im_fieldAt]
  exact sum_virial m z (fun j => (z j).im) c

/-- **The energy count**: transverse plus vertical energy is `½((Σ m)² − Σ m²)`. -/
theorem transverseEnergy_add_verticalEnergy (m : ι → ℝ) (z : ι → ℂ) (hz : Function.Injective z) :
    transverseEnergy m z + verticalEnergy m z = ((∑ j, m j) ^ 2 - ∑ j, m j ^ 2) / 2 := by
  rw [transverseEnergy, verticalEnergy, ← add_div, ← sum_add_distrib, ← sum_sum_erase_mul]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hd : z j - z k ≠ 0 := sub_ne_zero.mpr fun h => (ne_of_mem_erase hk) (hz h).symm
  have hn : Complex.normSq (z j - z k) ≠ 0 := Complex.normSq_eq_zero.not.mpr hd
  rw [← add_div, ← mul_add, div_eq_iff hn, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- The transverse energy of nonnegative multiplicities is nonnegative. -/
theorem transverseEnergy_nonneg {m : ι → ℝ} (hm : ∀ j, 0 ≤ m j) (z : ι → ℂ) :
    0 ≤ transverseEnergy m z :=
  div_nonneg (sum_nonneg fun j _ => sum_nonneg fun k _ =>
    div_nonneg (mul_nonneg (mul_nonneg (hm j) (hm k)) (sq_nonneg _))
      (Complex.normSq_nonneg _)) zero_le_two

end GaloisForLFunctions.ArithmeticElectrostatics
