import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeCanonicalSystem
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Basic

/-!
# The angles of a degenerate window

Read the amplitudes of a lattice window as the coefficients of a polynomial: `x ↦ Σ_k x_kz^k`. The
Toeplitz form becomes the Hermitian form
`⟨p, q⟩_N = Σ_{j,k≤N} κ(j − k)p_j\overline{q_k}` (`hform`) on polynomials of degree `≤ N`, and the
lattice translation becomes multiplication by `z`, an isometry (`hform_X_mul`). Two classical facts
of the Schur–Szegő theory then read as statements about the growth of windows.

* **Positive windows have outer ground states** (`norm_gt_one_of_predictor_root`). If the lattice
  window of size `n + 1` is positive definite, the predictor polynomial
  `F(z) = 1 + Σ_k a_kz^{k+1}` has no zero in the closed unit disc. The predictor is the ground state of
  the corner problem; positivity of the window is that this ground state is outer
  (minimum phase), the lattice form of a positive ground state (Mechanism A).
* **A degenerate window has all its angles on the circle** (`norm_eq_one_of_critical_root`). If the
  window of size `n + 1` is positive definite and the next margin vanishes, every zero of the zero-mode
  polynomial `V(z) = Σ_k v_kz^k` of the Levinson vector lies on the unit circle: at a first critical
  lattice length the window is the window of finitely many Frobenius angles, exactly as the window
  of a curve over a finite field. Under RH no lattice of Spec ℤ degenerates
  (`not_riemannHypothesis_of_first_critical`); off RH a first failure looks like a curve.

The proofs use only the orthogonality relations of the predictor and of the zero mode, the
isometry `z·`, and the factorization `F = (z − z₀)Q` at a root.
-/

noncomputable section

open Finset Polynomial Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

variable {κ : ℤ → ℝ}

/-- The **Hermitian Toeplitz form** on polynomials: `⟨p, q⟩_N = Σ_{j,k≤N} κ(j − k)p_j\overline{q_k}`. -/
def hform (κ : ℤ → ℝ) (N : ℕ) (p q : ℂ[X]) : ℂ :=
  ∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1), (κ ((j : ℤ) - k) : ℂ) * p.coeff j * conj (q.coeff k)

/-! ### Sesquilinearity and symmetry -/

theorem hform_sub_left (N : ℕ) (p p' q : ℂ[X]) :
    hform κ N (p - p') q = hform κ N p q - hform κ N p' q := by
  simp only [hform, coeff_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem hform_smul_left (N : ℕ) (c : ℂ) (p q : ℂ[X]) :
    hform κ N (C c * p) q = c * hform κ N p q := by
  simp only [hform, coeff_C_mul, mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem hform_sub_right (N : ℕ) (p q q' : ℂ[X]) :
    hform κ N p (q - q') = hform κ N p q - hform κ N p q' := by
  simp only [hform, coeff_sub, map_sub, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

theorem hform_smul_right (N : ℕ) (c : ℂ) (p q : ℂ[X]) :
    hform κ N p (C c * q) = conj c * hform κ N p q := by
  simp only [hform, coeff_C_mul, map_mul, mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  ring

/-- Hermitian symmetry: `\overline{⟨p, q⟩} = ⟨q, p⟩`. -/
theorem conj_hform (hκ : IsEvenSeq κ) (N : ℕ) (p q : ℂ[X]) :
    conj (hform κ N p q) = hform κ N q p := by
  simp only [hform, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [← hκ, neg_sub]
  ring

/-- `Re⟨p, p⟩_N` is the real Toeplitz form of the real parts plus that of the imaginary parts. -/
theorem re_hform_self (N : ℕ) (p : ℂ[X]) :
    (hform κ N p p).re = toeplitzForm κ (N + 1) (fun k => (p.coeff k).re) +
      toeplitzForm κ (N + 1) (fun k => (p.coeff k).im) := by
  simp only [hform, toeplitzForm, Complex.re_sum, ← sum_add_distrib]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ range (N + 1), _)]
  refine sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k => _)]
  refine sum_congr rfl fun k _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
  ring

/-- Positive definiteness of the real window gives `Re⟨p, p⟩_N > 0` for every nonzero polynomial of
degree `≤ N`. -/
theorem re_hform_self_pos (hpd : ToeplitzPosDef κ (N + 1)) {p : ℂ[X]} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N) : 0 < (hform κ N p p).re := by
  rw [re_hform_self]
  have hnn : ∀ x : Fin (N + 1) → ℝ, 0 ≤ toeplitzForm κ (N + 1) x := fun x => by
    by_cases hx : x = 0
    · subst hx; simp [toeplitzForm]
    · exact (hpd x hx).le
  -- some coefficient of degree `≤ N` is nonzero
  obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), p.coeff j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hp
    ext k
    by_cases hk : k ≤ N
    · exact hc ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; rfl
  by_cases hre : (p.coeff j).re = 0
  · have him : (p.coeff j).im ≠ 0 := fun him => hj (Complex.ext hre him)
    have := hpd (fun k => (p.coeff k).im) fun h0 => him (by simpa using congrFun h0 j)
    linarith [hnn (fun k => (p.coeff k).re)]
  · have := hpd (fun k => (p.coeff k).re) fun h0 => hre (by simpa using congrFun h0 j)
    linarith [hnn (fun k => (p.coeff k).im)]

/-! ### Translation is multiplication by `z` -/

/-- Dropping a top coefficient that vanishes. -/
theorem hform_succ_of_coeff (N : ℕ) {p q : ℂ[X]} (hp : p.coeff (N + 1) = 0)
    (hq : q.coeff (N + 1) = 0) : hform κ (N + 1) p q = hform κ N p q := by
  simp only [hform, sum_range_succ, hp, hq, map_zero, mul_zero, zero_mul, add_zero, sum_const_zero]

/-- **The lattice translation is an isometry**: `⟨zp, zq⟩_N = ⟨p, q⟩_N` when the coefficients of
degree `N` vanish. -/
theorem hform_X_mul (N : ℕ) {p q : ℂ[X]} (hp : p.coeff N = 0) (hq : q.coeff N = 0) :
    hform κ N (X * p) (X * q) = hform κ N p q := by
  cases N with
  | zero =>
    simp [hform, hq]
  | succ N =>
    rw [hform_succ_of_coeff N hp hq]
    unfold hform
    rw [sum_range_succ']
    simp only [coeff_X_mul_zero, mul_zero, zero_mul, sum_const_zero, add_zero]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_range_succ']
    simp only [coeff_X_mul_zero, coeff_X_mul, map_zero, mul_zero, add_zero]
    refine sum_congr rfl fun k _ => ?_
    rw [show ((j + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) = (j : ℤ) - k by push_cast; ring]

/-! ### Predictor and zero-mode polynomials -/

/-- The polynomial of an amplitude vector of size `n + 1`. -/
def vecPoly {n : ℕ} (v : Fin (n + 1) → ℝ) : ℂ[X] := ∑ k : Fin (n + 1), C (v k : ℂ) * X ^ (k : ℕ)

theorem coeff_vecPoly {n : ℕ} (v : Fin (n + 1) → ℝ) (j : ℕ) :
    (vecPoly v).coeff j = if h : j < n + 1 then (v ⟨j, h⟩ : ℂ) else 0 := by
  simp only [vecPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨j, h⟩ : Fin (n + 1))]
    · simp
    · intro b _ hb
      have : j ≠ (b : ℕ) := fun hbj => hb (Fin.ext hbj.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun b _ => ?_
    have : j ≠ (b : ℕ) := fun hbj => h (by rw [hbj]; exact b.isLt)
    simp [this]

theorem natDegree_vecPoly_le {n : ℕ} (v : Fin (n + 1) → ℝ) : (vecPoly v).natDegree ≤ n := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
  rw [coeff_vecPoly, dif_neg (by omega)]

/-- Orthogonality of a vector to the sites `k ∈ s` gives orthogonality of its polynomial to every
polynomial supported on `s`. -/
theorem hform_eq_zero_of_orth {n : ℕ} (v : Fin (n + 1) → ℝ) (G : ℂ[X])
    (h : ∀ k, k ≤ n → G.coeff k ≠ 0 → ∑ j : Fin (n + 1), κ ((j : ℤ) - k) * v j = 0) :
    hform κ n (vecPoly v) G = 0 := by
  rw [hform, sum_comm]
  refine sum_eq_zero fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  by_cases hG : G.coeff k = 0
  · simp [hG]
  · have hrow := h k hk' hG
    rw [← sum_mul, ← Fin.sum_univ_eq_sum_range (fun j => (κ ((j : ℤ) - k) : ℂ) *
      (vecPoly v).coeff j)]
    have : ∑ j : Fin (n + 1), (κ ((j : ℤ) - k) : ℂ) * (vecPoly v).coeff j =
        ((∑ j : Fin (n + 1), κ ((j : ℤ) - k) * v j : ℝ) : ℂ) := by
      push_cast
      refine sum_congr rfl fun j _ => ?_
      rw [coeff_vecPoly, dif_pos j.isLt]
    rw [this, hrow, Complex.ofReal_zero, zero_mul]

/-- The predictor rows: `Σ_j κ(j − k)f_j = 0` for the vector `f = (1, a)` and `1 ≤ k ≤ n`. -/
theorem predictor_rows (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∑ j : Fin (n + 1), κ ((j : ℤ) - k) * (Fin.cons 1 a : Fin (n + 1) → ℝ) j = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Nat.cast_zero, mul_one,
    Nat.cast_add, Nat.cast_one]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hrow := ha ⟨k', by omega⟩
  simp only at hrow
  have e1 : κ (0 - ((k' + 1 : ℕ) : ℤ)) = κ ((k' : ℤ) + 1) := by
    rw [zero_sub, hκ]; push_cast; ring_nf
  have e2 : ∀ i : Fin n, κ ((i : ℤ) + 1 - ((k' + 1 : ℕ) : ℤ)) = κ ((k' : ℤ) - i) := fun i => by
    rw [← hκ]; congr 1; push_cast; ring
  simp only [e2]
  rw [e1, hrow]
  ring

/-- **Positive windows have outer predictors.** If the lattice window of size `n + 1` is positive
definite, every zero `z₀` of the predictor polynomial `1 + Σ_k a_kz^{k+1}` satisfies `1 < ‖z₀‖`. -/
theorem norm_gt_one_of_predictor_root (hκ : IsEvenSeq κ) {n : ℕ}
    (hpd : ToeplitzPosDef κ (n + 1)) {a : Fin n → ℝ} (ha : IsPredictor κ n a) {z₀ : ℂ}
    (hroot : (vecPoly (Fin.cons 1 a : Fin (n + 1) → ℝ)).IsRoot z₀) : 1 < ‖z₀‖ := by
  set F := vecPoly (Fin.cons 1 a : Fin (n + 1) → ℝ)
  set Q := F /ₘ (X - C z₀)
  have hF0 : F.coeff 0 = 1 := by simp [F, coeff_vecPoly]
  have hFne : F ≠ 0 := fun h => by simp [h] at hF0
  have hfac : (X - C z₀) * Q = F := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hz0 : z₀ ≠ 0 := fun hz => by
    have := congrArg (fun p => p.coeff 0) hfac
    simp only [hz, map_zero, sub_zero, coeff_X_mul_zero] at this
    rw [hF0] at this
    exact zero_ne_one this
  have hQne : Q ≠ 0 := fun h => hFne (by rw [← hfac, h, mul_zero])
  have hdegF : F.natDegree ≤ n := natDegree_vecPoly_le _
  have hdegQ : Q.natDegree + 1 ≤ n := by
    have h1 := natDegree_mul (X_sub_C_ne_zero z₀) hQne
    rw [hfac, natDegree_X_sub_C] at h1
    have : 1 ≤ F.natDegree := by
      by_contra hc
      have hF := eq_C_of_natDegree_eq_zero (by omega : F.natDegree = 0)
      rw [hF] at hroot
      simp [IsRoot, hF0] at hroot
    omega
  have hQn : Q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  -- `F` is orthogonal to `zQ`, which lives on the sites `1, …, n`
  have horth : hform κ n F (X * Q) = 0 := by
    refine hform_eq_zero_of_orth _ _ fun k hkn hk => predictor_rows hκ ha k ?_ hkn
    by_contra h0
    rw [show k = 0 by omega, coeff_X_mul_zero] at hk
    exact hk rfl
  have hFsplit : F = X * Q - C z₀ * Q := by rw [← hfac]; ring
  set q := hform κ n Q Q
  set m := hform κ n Q (X * Q)
  have hshift : hform κ n (X * Q) (X * Q) = q := hform_X_mul n hQn hQn
  -- `⟨F, zQ⟩ = 0` gives `q = z₀m`
  have h1 : q = z₀ * m := by
    have := horth
    rw [hFsplit, hform_sub_left, hform_smul_left, hshift] at this
    linear_combination this
  -- `⟨F, F⟩ = (|z₀|² − 1)q`
  have hFF : hform κ n F F = (z₀ * conj z₀ - 1) * q := by
    have hconj : hform κ n (X * Q) Q = conj m := by rw [← conj_hform hκ]
    have e : hform κ n F F = -conj z₀ * hform κ n F Q := by
      conv_lhs => rw [hFsplit]
      rw [hform_sub_right, hform_smul_right]
      rw [← hFsplit, horth]; ring
    rw [e, hFsplit, hform_sub_left, hform_smul_left, hconj]
    have hm : m = q / z₀ := by rw [h1]; field_simp
    have hcm : conj m = conj q / conj z₀ := by rw [hm, map_div₀]
    have hq : conj q = q := by rw [conj_hform hκ]
    rw [hcm, hq]
    have hcz : conj z₀ ≠ 0 := (map_ne_zero _).mpr hz0
    field_simp
    ring
  have hFpos := re_hform_self_pos hpd hFne hdegF
  have hqpos := re_hform_self_pos hpd hQne (by omega)
  have hqim : q.im = 0 := by
    have := congrArg Complex.im (conj_hform hκ n Q Q)
    simp only [Complex.conj_im] at this
    linarith
  rw [hFF] at hFpos
  have hzz : z₀ * conj z₀ = ((‖z₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hzz] at hFpos
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.sub_im,
    Complex.ofReal_im, Complex.one_im, sub_zero, hqim, mul_zero] at hFpos
  have : 0 < ‖z₀‖ ^ 2 - 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith [norm_nonneg z₀]

/-! ### Zero modes of a degenerate window -/

/-- Expansion of the Toeplitz form along one site: `T(v + te_k) = T(v) + 2tR_k + t²κ(0)` with
`R_k = Σ_j κ(j − k)v_j`. -/
theorem toeplitzForm_add_single (hκ : IsEvenSeq κ) {N : ℕ} (v : Fin N → ℝ) (k : Fin N) (t : ℝ) :
    toeplitzForm κ N (fun j => v j + t * if j = k then 1 else 0) =
      toeplitzForm κ N v + 2 * t * ∑ j : Fin N, κ ((j : ℤ) - k) * v j + t ^ 2 * κ 0 := by
  set δ : Fin N → ℝ := fun j => if j = k then 1 else 0 with hδ
  have hδk : δ k = 1 := by simp [δ]
  have hδo : ∀ j, j ≠ k → δ j = 0 := fun j hj => by simp [δ, hj]
  show toeplitzForm κ N (fun j => v j + t * δ j) = _
  have expand : toeplitzForm κ N (fun j => v j + t * δ j) =
      toeplitzForm κ N v + t * ∑ i : Fin N, ∑ j : Fin N, κ ((i : ℤ) - j) * v i * δ j +
        t * ∑ i : Fin N, ∑ j : Fin N, κ ((i : ℤ) - j) * δ i * v j +
          t ^ 2 * ∑ i : Fin N, ∑ j : Fin N, κ ((i : ℤ) - j) * δ i * δ j := by
    simp only [toeplitzForm, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  have s1 : ∑ i : Fin N, ∑ j : Fin N, κ ((i : ℤ) - j) * v i * δ j =
      ∑ i : Fin N, κ ((i : ℤ) - k) * v i := by
    refine sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_eq_single k (fun j hj => by rw [hδo j hj, mul_zero]), hδk, mul_one]
  have s2 : ∑ i : Fin N, ∑ j : Fin N, κ ((i : ℤ) - j) * δ i * v j =
      ∑ j : Fin N, κ ((j : ℤ) - k) * v j := by
    rw [Fintype.sum_eq_single k (fun i hi => by simp [hδo i hi])]
    refine sum_congr rfl fun j _ => ?_
    rw [hδk, ← hκ, neg_sub]; ring
  have s3 : ∑ i : Fin N, ∑ j : Fin N, κ ((i : ℤ) - j) * δ i * δ j = κ 0 := by
    rw [Fintype.sum_eq_single k (fun i hi => by simp [hδo i hi]),
      Fintype.sum_eq_single k (fun j hj => by rw [hδo j hj, mul_zero]), hδk, sub_self]
    ring
  rw [expand, s1, s2, s3]
  ring

/-- **A zero of a nonnegative Toeplitz form is in its radical**: all rows `Σ_j κ(j − k)v_j` vanish. -/
theorem toeplitz_rows_eq_zero (hκ : IsEvenSeq κ) {N : ℕ}
    (hpsd : ∀ x : Fin N → ℝ, 0 ≤ toeplitzForm κ N x) {v : Fin N → ℝ}
    (hv : toeplitzForm κ N v = 0) (k : Fin N) : ∑ j : Fin N, κ ((j : ℤ) - k) * v j = 0 := by
  set R := ∑ j : Fin N, κ ((j : ℤ) - k) * v j
  have hk0 : 0 ≤ κ 0 := by
    have := hpsd (fun j => if j = k then 1 else 0)
    have e := toeplitzForm_add_single hκ (fun _ => 0) k 1
    simp only [zero_add, one_mul, mul_zero, sum_const_zero, one_pow] at e
    have hz : toeplitzForm κ N (fun _ => 0) = 0 := by simp [toeplitzForm]
    linarith
  have h := hpsd (fun j => v j + (-R / (κ 0 + 1)) * if j = k then 1 else 0)
  rw [toeplitzForm_add_single hκ, hv] at h
  have hden : 0 < κ 0 + 1 := by linarith
  have : 0 ≤ -R ^ 2 * (κ 0 + 2) / (κ 0 + 1) ^ 2 := by
    have e : 0 + 2 * (-R / (κ 0 + 1)) * R + (-R / (κ 0 + 1)) ^ 2 * κ 0 =
        -R ^ 2 * (κ 0 + 2) / (κ 0 + 1) ^ 2 := by field_simp; ring
    linarith
  have h2 : -R ^ 2 * (κ 0 + 2) ≥ 0 := by
    rcases div_nonneg_iff.mp this with h | h
    · exact h.1
    · exact absurd h.2 (not_le.mpr (by positivity))
  have : R ^ 2 = 0 := by nlinarith [sq_nonneg R]
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- **A degenerate window has all its angles on the circle.** If the lattice window of size `n + 1`
is positive definite and the next margin vanishes, every zero of the zero-mode polynomial
`V(z) = Σ_k v_kz^k` of the Levinson vector lies on the unit circle. -/
theorem norm_eq_one_of_critical_root (hκ : IsEvenSeq κ) {n : ℕ}
    (hpd : ToeplitzPosDef κ (n + 1)) (h0 : levinsonErr κ (n + 1) = 0) {z₀ : ℂ}
    (hroot : (vecPoly (levinsonVec κ (n + 1))).IsRoot z₀) : ‖z₀‖ = 1 := by
  obtain ⟨hpsd, hker⟩ := toeplitzForm_kernel_of_first_critical hκ hpd h0
  set v := levinsonVec κ (n + 1)
  have hv : toeplitzForm κ (n + 2) v = 0 := (hker v).mpr (funext fun k => by simp [v, levinsonVec])
  have hrows := toeplitz_rows_eq_zero hκ hpsd hv
  set V := vecPoly v
  set Q := V /ₘ (X - C z₀)
  have hV0 : V.coeff 0 = 1 := by simp [V, coeff_vecPoly, v, levinsonVec]
  have hVne : V ≠ 0 := fun h => by simp [h] at hV0
  have hfac : (X - C z₀) * Q = V := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hz0 : z₀ ≠ 0 := fun hz => by
    have := congrArg (fun p => p.coeff 0) hfac
    simp only [hz, map_zero, sub_zero, coeff_X_mul_zero] at this
    rw [hV0] at this
    exact zero_ne_one this
  have hQne : Q ≠ 0 := fun h => hVne (by rw [← hfac, h, mul_zero])
  have hdegV : V.natDegree ≤ n + 1 := natDegree_vecPoly_le v
  have hdegQ : Q.natDegree ≤ n := by
    have h1 := natDegree_mul (X_sub_C_ne_zero z₀) hQne
    rw [hfac, natDegree_X_sub_C] at h1
    omega
  have hQn : Q.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  -- the zero mode is orthogonal to every polynomial of degree `≤ n + 1`
  have hrad : ∀ G : ℂ[X], hform κ (n + 1) V G = 0 := fun G =>
    hform_eq_zero_of_orth v G fun k hk _ => hrows ⟨k, by omega⟩
  have hVsplit : V = X * Q - C z₀ * Q := by rw [← hfac]; ring
  set q := hform κ (n + 1) Q Q
  set m := hform κ (n + 1) Q (X * Q)
  have hshift : hform κ (n + 1) (X * Q) (X * Q) = q := hform_X_mul (n + 1) hQn hQn
  have h1 : q = z₀ * m := by
    have := hrad (X * Q)
    rw [hVsplit, hform_sub_left, hform_smul_left, hshift] at this
    linear_combination this
  have h2 : conj m = z₀ * q := by
    have := hrad Q
    rw [hVsplit, hform_sub_left, hform_smul_left] at this
    have hc : hform κ (n + 1) (X * Q) Q = conj m := by rw [← conj_hform hκ]
    rw [hc] at this
    linear_combination this
  have hq : conj q = q := by rw [conj_hform hκ]
  have hqpos : 0 < q.re := by
    have : q = hform κ n Q Q := hform_succ_of_coeff n hQn hQn
    rw [this]
    exact re_hform_self_pos hpd hQne hdegQ
  -- `q = |z₀|²q`
  have h3 : q = z₀ * conj z₀ * q := by
    have hm : m = q / z₀ := by rw [h1]; field_simp
    have := h2
    rw [hm, map_div₀, hq] at this
    have hcz : conj z₀ ≠ 0 := (map_ne_zero _).mpr hz0
    field_simp at this
    linear_combination this
  have hzz : z₀ * conj z₀ = ((‖z₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hzz] at h3
  have h4 := congrArg Complex.re h3
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h4
  have h5 : ‖z₀‖ ^ 2 = 1 := by
    have : (‖z₀‖ ^ 2 - 1) * q.re = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have := norm_nonneg z₀
  nlinarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
