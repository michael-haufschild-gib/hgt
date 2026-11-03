import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheAnglesOfADegenerateWindow
import Mathlib.LinearAlgebra.Lagrange

/-!
# A degenerate window is a curve

Let the lattice window of size `n + 1` be positive definite and the next margin vanish
(`levinsonErr κ (n + 1) = 0`). The zero mode `V` has `n + 1` distinct zeros on the unit circle
(`zeroMode_roots`). Then the window is literally the window of a curve with these Frobenius angles:

`κ(j − k) = Σ_z ρ_z z^j \overline{z}^k` for `j, k ≤ n`, with weights `ρ_z > 0`
(`degenerate_window_is_curve`).

*Proof.* Modulo the radical line `ℂV`, multiplication by `z` is an isometry of the Hermitian form
(`hform_X_mul`), and `P_w = V/(z − w)` is an eigenvector with eigenvalue `w`: `zP_w = wP_w + V`.
Eigenvectors of an isometry with distinct unimodular eigenvalues are orthogonal
(`hform_cofactor_orth`). Lagrange interpolation at the `n + 1` zeros writes every polynomial of
degree `≤ n` as `Σ_w (P(w)/P_w(w))P_w` (`eq_sum_cofactor`), so the form diagonalizes with weights
`ρ_w = ⟨P_w, P_w⟩/|P_w(w)|² > 0`. Taking `P = z^j`, `Q = z^k` gives the moments.

This is the Carathéodory–Fejér structure of a first failure: the frozen data of a degenerate window
are the power sums of finitely many points on the circle with positive multiplicities, exactly as the
window of a curve over `𝔽_q` is the Toeplitz form of the power sums of its `2g` Frobenius eigenvalues.
-/

noncomputable section

open Finset Polynomial Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

variable {κ : ℤ → ℝ}

/-! ### Sums and monomials -/

theorem hform_add_right (N : ℕ) (p q q' : ℂ[X]) :
    hform κ N p (q + q') = hform κ N p q + hform κ N p q' := by
  simp only [hform, coeff_add, map_add, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem hform_zero_left (N : ℕ) (q : ℂ[X]) : hform κ N 0 q = 0 := by simp [hform]

theorem hform_zero_right (N : ℕ) (p : ℂ[X]) : hform κ N p 0 = 0 := by simp [hform]

theorem hform_sum_left (N : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (q : ℂ[X]) :
    hform κ N (∑ i ∈ s, f i) q = ∑ i ∈ s, hform κ N (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, hform_zero_left]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hform_add_left, ih]

theorem hform_sum_right (N : ℕ) {ι : Type*} (s : Finset ι) (p : ℂ[X]) (f : ι → ℂ[X]) :
    hform κ N p (∑ i ∈ s, f i) = ∑ i ∈ s, hform κ N p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, sum_empty, hform_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hform_add_right, ih]

/-- The form on monomials is the Toeplitz sequence: `⟨z^j, z^k⟩_N = κ(j − k)`. -/
theorem hform_X_pow (N : ℕ) {j k : ℕ} (hj : j ≤ N) (hk : k ≤ N) :
    hform κ N (X ^ j) (X ^ k) = (κ ((j : ℤ) - k) : ℂ) := by
  simp only [hform, coeff_X_pow]
  rw [sum_eq_single j, sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (mem_range.mpr (by omega)) h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-! ### Eigenvectors of the shift modulo the radical -/

/-- **Distinct unimodular eigenvalues give orthogonal eigenvectors.** If `V` is in the radical and
`(z − w)P_w = V`, `(z − v)P_v = V` with `|v| = 1`, `w ≠ v`, and `P_w, P_v` fit below degree `N`,
then `⟨P_w, P_v⟩_N = 0`: multiplication by `z` is an isometry modulo `V` with eigenvectors `P_w`. -/
theorem hform_orth_of_eigen {N : ℕ} {V Pw Pv : ℂ[X]} {w v : ℂ}
    (hradL : ∀ G, hform κ N V G = 0) (hradR : ∀ G, hform κ N G V = 0)
    (hw : (X - C w) * Pw = V) (hv : (X - C v) * Pv = V) (hcw : Pw.coeff N = 0)
    (hcv : Pv.coeff N = 0) (hv1 : ‖v‖ = 1) (hvw : w ≠ v) : hform κ N Pw Pv = 0 := by
  have hPw : X * Pw = V + C w * Pw := by rw [← hw]; ring
  have hPv : X * Pv = V + C v * Pv := by rw [← hv]; ring
  have hiso := hform_X_mul (κ := κ) N hcw hcv
  rw [hPw, hPv, hform_add_left, hradL, zero_add, hform_smul_left, hform_add_right, hradR,
    zero_add, hform_smul_right] at hiso
  have hne : w * conj v - 1 ≠ 0 := by
    intro h
    apply hvw
    have hvv : conj v * v = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hv1]; norm_num
    calc w = w * (conj v * v) := by rw [hvv, mul_one]
      _ = (w * conj v) * v := by ring
      _ = v := by rw [sub_eq_zero.mp h, one_mul]
  have : (w * conj v - 1) * hform κ N Pw Pv = 0 := by linear_combination hiso
  exact (mul_eq_zero.mp this).resolve_left hne

/-- **Lagrange interpolation by cofactors.** If `P_z` (`z ∈ S`) vanish at the other points of `S`,
not at their own, and have degree `< |S|`, every `P` of degree `< |S|` is
`Σ_z (P(z)/P_z(z))P_z`. -/
theorem eq_sum_cofactor {S : Finset ℂ} {Pc : ℂ → ℂ[X]} {P : ℂ[X]}
    (hdeg : ∀ z ∈ S, (Pc z).degree < S.card) (hself : ∀ z ∈ S, (Pc z).eval z ≠ 0)
    (hother : ∀ z ∈ S, ∀ v ∈ S, v ≠ z → (Pc z).eval v = 0) (hP : P.degree < S.card) :
    P = ∑ z ∈ S, C (P.eval z / (Pc z).eval z) * Pc z := by
  have hsum : (∑ z ∈ S, C (P.eval z / (Pc z).eval z) * Pc z).degree < S.card := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro z hz
    refine lt_of_le_of_lt ?_ (hdeg z hz)
    rw [← smul_eq_C_mul]
    exact degree_smul_le _ _
  refine eq_of_degrees_lt_of_eval_finset_eq S hP hsum fun v hv => ?_
  rw [eval_finsetSum, sum_eq_single v]
  · rw [eval_mul, eval_C, div_mul_cancel₀ _ (hself v hv)]
  · intro z hz hzv
    rw [eval_mul, hother z hz v hv (Ne.symm hzv), mul_zero]
  · intro h; exact absurd hv h

/-- **The form diagonalizes on the cofactors**:
`⟨P, Q⟩ = Σ_z (P(z)/P_z(z))\overline{(Q(z)/P_z(z))}⟨P_z, P_z⟩` when the cofactors are orthogonal. -/
theorem hform_eq_sum_diag {N : ℕ} {S : Finset ℂ} {Pc : ℂ → ℂ[X]} {P Q : ℂ[X]}
    (hP : P = ∑ z ∈ S, C (P.eval z / (Pc z).eval z) * Pc z)
    (hQ : Q = ∑ z ∈ S, C (Q.eval z / (Pc z).eval z) * Pc z)
    (horth : ∀ z ∈ S, ∀ v ∈ S, z ≠ v → hform κ N (Pc z) (Pc v) = 0) :
    hform κ N P Q = ∑ z ∈ S, (P.eval z / (Pc z).eval z) *
      conj (Q.eval z / (Pc z).eval z) * hform κ N (Pc z) (Pc z) := by
  conv_lhs => rw [hP, hQ]
  rw [hform_sum_left]
  refine sum_congr rfl fun z hz => ?_
  rw [hform_smul_left, hform_sum_right, sum_eq_single z]
  · rw [hform_smul_right]; ring
  · intro v hv hvz
    rw [hform_smul_right, horth z hz v hv (Ne.symm hvz), mul_zero]
  · intro h; exact absurd hz h

/-! ### The degenerate window -/

/-- The cofactor `P_w = V/(z − w)` of a root `w` of the zero mode. -/
def cofactor (V : ℂ[X]) (w : ℂ) : ℂ[X] := V /ₘ (X - C w)

section degenerate

variable (hκ : IsEvenSeq κ) {n : ℕ} (hpd : ToeplitzPosDef κ (n + 1))
  (h0 : levinsonErr κ (n + 1) = 0)
include hκ hpd h0

theorem zeroMode_ne_zero : vecPoly (levinsonVec κ (n + 1)) ≠ 0 := fun h => by
  have hdegV := natDegree_zeroMode hκ hpd h0
  rw [h, natDegree_zero] at hdegV; omega

theorem cofactor_spec {w : ℂ} (hw : w ∈ (vecPoly (levinsonVec κ (n + 1))).roots) :
    (X - C w) * cofactor (vecPoly (levinsonVec κ (n + 1))) w =
      vecPoly (levinsonVec κ (n + 1)) :=
  mul_divByMonic_eq_iff_isRoot.mpr ((mem_roots (zeroMode_ne_zero hκ hpd h0)).mp hw)

theorem natDegree_cofactor {w : ℂ} (hw : w ∈ (vecPoly (levinsonVec κ (n + 1))).roots) :
    (cofactor (vecPoly (levinsonVec κ (n + 1))) w).natDegree = n := by
  have hdegV := natDegree_zeroMode hκ hpd h0
  have hspec := cofactor_spec hκ hpd h0 hw
  have hPne : cofactor (vecPoly (levinsonVec κ (n + 1))) w ≠ 0 := fun h =>
    zeroMode_ne_zero hκ hpd h0 (by rw [← hspec, h, mul_zero])
  have h1 := natDegree_mul (X_sub_C_ne_zero w) hPne
  rw [hspec, hdegV, natDegree_X_sub_C] at h1
  omega

theorem cofactor_ne_zero {w : ℂ} (hw : w ∈ (vecPoly (levinsonVec κ (n + 1))).roots) :
    cofactor (vecPoly (levinsonVec κ (n + 1))) w ≠ 0 := fun h =>
  zeroMode_ne_zero hκ hpd h0 (by rw [← cofactor_spec hκ hpd h0 hw, h, mul_zero])

/-- The cofactor does not vanish at its own root: the angles are simple. -/
theorem eval_cofactor_self_ne_zero {w : ℂ} (hw : w ∈ (vecPoly (levinsonVec κ (n + 1))).roots) :
    (cofactor (vecPoly (levinsonVec κ (n + 1))) w).eval w ≠ 0 := by
  intro h
  obtain ⟨R, hR⟩ := dvd_iff_isRoot.mpr h
  apply not_sq_dvd_zeroMode hκ hpd h0 w
  refine ⟨R, ?_⟩
  rw [← cofactor_spec hκ hpd h0 hw, hR]
  ring

/-- The cofactor of `w` vanishes at every other root. -/
theorem eval_cofactor_other {w v : ℂ} (hw : w ∈ (vecPoly (levinsonVec κ (n + 1))).roots)
    (hv : v ∈ (vecPoly (levinsonVec κ (n + 1))).roots) (hvw : v ≠ w) :
    (cofactor (vecPoly (levinsonVec κ (n + 1))) w).eval v = 0 := by
  have hroot := (mem_roots (zeroMode_ne_zero hκ hpd h0)).mp hv
  rw [← cofactor_spec hκ hpd h0 hw, IsRoot, eval_mul, eval_sub, eval_X, eval_C] at hroot
  exact (mul_eq_zero.mp hroot).resolve_left (sub_ne_zero.mpr hvw)

/-- **A degenerate window is a curve.** If the lattice window of size `n + 1` is positive definite and
the next margin vanishes, there are `n + 1` distinct points `z` on the unit circle and weights
`ρ_z > 0` with `κ(j − k) = Σ_z ρ_z z^j\overline{z}^k` for all `j, k ≤ n`. -/
theorem degenerate_window_is_curve :
    ∃ S : Finset ℂ, S.card = n + 1 ∧ (∀ z ∈ S, ‖z‖ = 1) ∧ ∃ ρ : ℂ → ℝ, (∀ z ∈ S, 0 < ρ z) ∧
      ∀ j k : ℕ, j ≤ n → k ≤ n →
        (κ ((j : ℤ) - k) : ℂ) = ∑ z ∈ S, (ρ z : ℂ) * z ^ j * conj z ^ k := by
  classical
  have hroots := zeroMode_roots hκ hpd h0
  set V := vecPoly (levinsonVec κ (n + 1))
  set S := V.roots.toFinset
  have hmem : ∀ z, z ∈ S ↔ z ∈ V.roots := fun z => Multiset.mem_toFinset
  have hcard : S.card = n + 1 := by
    rw [Multiset.toFinset_card_of_nodup hroots.1, hroots.2.1]
  set Pc : ℂ → ℂ[X] := fun z => cofactor V z
  have hradL : ∀ G, hform κ (n + 1) V G = 0 := hform_zeroMode_eq_zero hκ hpd h0
  have hradR : ∀ G, hform κ (n + 1) G V = 0 := fun G => by
    rw [← conj_hform hκ, hradL, map_zero]
  have hcoef : ∀ z ∈ S, (Pc z).coeff (n + 1) = 0 := fun z hz =>
    coeff_eq_zero_of_natDegree_lt (by
      rw [show Pc z = cofactor V z from rfl, natDegree_cofactor hκ hpd h0 ((hmem z).mp hz)]
      omega)
  have horth : ∀ z ∈ S, ∀ v ∈ S, z ≠ v → hform κ (n + 1) (Pc z) (Pc v) = 0 :=
    fun z hz v hv hzv => hform_orth_of_eigen hradL hradR (cofactor_spec hκ hpd h0 ((hmem z).mp hz))
      (cofactor_spec hκ hpd h0 ((hmem v).mp hv)) (hcoef z hz) (hcoef v hv)
      (hroots.2.2 v ((hmem v).mp hv)) hzv
  have hdegc : ∀ z ∈ S, (Pc z).degree < S.card := fun z hz => by
    rw [hcard, degree_eq_natDegree (cofactor_ne_zero hκ hpd h0 ((hmem z).mp hz)),
      natDegree_cofactor hκ hpd h0 ((hmem z).mp hz)]
    exact_mod_cast Nat.lt_succ_self n
  have hself : ∀ z ∈ S, (Pc z).eval z ≠ 0 := fun z hz =>
    eval_cofactor_self_ne_zero hκ hpd h0 ((hmem z).mp hz)
  have hother : ∀ z ∈ S, ∀ v ∈ S, v ≠ z → (Pc z).eval v = 0 := fun z hz v hv hvz =>
    eval_cofactor_other hκ hpd h0 ((hmem z).mp hz) ((hmem v).mp hv) hvz
  -- the diagonal entries are positive reals
  have hdiag : ∀ z ∈ S, hform κ (n + 1) (Pc z) (Pc z) =
      ((hform κ (n + 1) (Pc z) (Pc z)).re : ℂ) := fun z hz => by
    refine Complex.ext rfl ?_
    simp only [Complex.ofReal_im]
    have := congrArg Complex.im (conj_hform hκ (n + 1) (Pc z) (Pc z))
    simp only [Complex.conj_im] at this
    linarith
  have hdpos : ∀ z ∈ S, 0 < (hform κ (n + 1) (Pc z) (Pc z)).re := fun z hz => by
    rw [hform_succ_of_coeff n (hcoef z hz) (hcoef z hz)]
    exact re_hform_self_pos hpd (cofactor_ne_zero hκ hpd h0 ((hmem z).mp hz))
      (natDegree_cofactor hκ hpd h0 ((hmem z).mp hz)).le
  refine ⟨S, hcard, fun z hz => hroots.2.2 z ((hmem z).mp hz),
    fun z => (hform κ (n + 1) (Pc z) (Pc z)).re / Complex.normSq ((Pc z).eval z),
    fun z hz => div_pos (hdpos z hz) (Complex.normSq_pos.mpr (hself z hz)), fun j k hj hk => ?_⟩
  have hXj : (X ^ j : ℂ[X]).degree < S.card := by
    rw [degree_X_pow, hcard]; exact_mod_cast Nat.lt_succ_of_le hj
  have hXk : (X ^ k : ℂ[X]).degree < S.card := by
    rw [degree_X_pow, hcard]; exact_mod_cast Nat.lt_succ_of_le hk
  rw [← hform_X_pow (n + 1) (by omega : j ≤ n + 1) (by omega : k ≤ n + 1),
    hform_eq_sum_diag (eq_sum_cofactor hdegc hself hother hXj)
      (eq_sum_cofactor hdegc hself hother hXk) horth]
  refine sum_congr rfl fun z hz => ?_
  rw [hdiag z hz, eval_pow, eval_pow, eval_X, map_div₀, map_pow]
  dsimp only
  have hne := hself z hz
  have hcne : conj ((Pc z).eval z) ≠ 0 := (_root_.map_ne_zero _).mpr hne
  have hns : ((Complex.normSq ((Pc z).eval z) : ℝ) : ℂ) = (Pc z).eval z * conj ((Pc z).eval z) := by
    rw [Complex.mul_conj]
  push_cast
  rw [hns]
  field_simp

end degenerate

end GaloisForLFunctions.GrowingWindowsOfSpecZ
