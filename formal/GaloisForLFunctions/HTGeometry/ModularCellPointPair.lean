import GaloisForLFunctions.HTGeometry.ModularStripUnfolding
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Point-pair invariants and the local finiteness of the modular tiling

`u(z,w) = |z-w|²/(4 Im z Im w) = (cosh d(z,w) - 1)/2` is symmetric and `SL(2,ℝ)`-invariant, so its radial
integrals do not depend on the centre (`lintegral_pairU_eq`).  The `SL(2,ℤ)`-translates of the modular
cell `𝒟` tile `ℍ` twice over (`tsum_lintegral_fd_smul`, the factor `2` being `±1`).  If `B𝒟` comes within
`u ≤ R` of a point `z`, every entry of `B` is bounded by an explicit function of `z` and `R`
(`entries_sq_le_of_pairU_le`: lower row from `Im(Bz') ≥ Im z/(4R+2)`, upper row from the inverse and
the determinant), so only finitely many translates are that close (`finite_near_fd`).
-/

open MeasureTheory UpperHalfPlane
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The point-pair invariant `u(z,w) = |z - w|² / (4 Im z Im w) = (cosh d(z,w) - 1)/2`. -/
def pairU (z w : ℍ) : ℝ := dist (z : ℂ) w ^ 2 / (4 * z.im * w.im)

theorem pairU_eq_cosh (z w : ℍ) : pairU z w = (Real.cosh (dist z w) - 1) / 2 := by
  rw [UpperHalfPlane.cosh_dist, pairU]
  have hz := z.im_pos; have hw := w.im_pos
  field_simp
  ring

theorem pairU_nonneg (z w : ℍ) : 0 ≤ pairU z w := by
  unfold pairU; have := z.im_pos; have := w.im_pos; positivity

theorem pairU_comm (z w : ℍ) : pairU z w = pairU w z := by
  rw [pairU_eq_cosh, pairU_eq_cosh, dist_comm]

theorem pairU_smul (g : SL(2, ℝ)) (z w : ℍ) : pairU (g • z) (g • w) = pairU z w := by
  rw [pairU_eq_cosh, pairU_eq_cosh, dist_smul]

theorem pairU_smul_left (g : SL(2, ℝ)) (z w : ℍ) : pairU (g • z) w = pairU z (g⁻¹ • w) := by
  rw [← pairU_smul g⁻¹, inv_smul_smul]

/-- **The radial integral does not depend on the centre.**  `∫⁻ f(u(z,w)) dμ(w) = ∫⁻ f(u(i,w)) dμ(w)`
for every measurable `f ≥ 0`. -/
theorem lintegral_pairU_eq (f : ℝ → ℝ≥0∞) (z : ℍ) :
    ∫⁻ w, f (pairU z w) = ∫⁻ w, f (pairU UpperHalfPlane.I w) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) UpperHalfPlane.I z
  subst hg
  have hmp := measurePreserving_smul ((g : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have e : ∀ w : ℍ, ((g : GL (Fin 2) ℝ)) • w = g • w := fun w => rfl
  rw [← hmp.lintegral_comp_emb (measurableEmbedding_const_smul _)]
  simp only [e, pairU_smul]

/-- The fibre of `SL(2,ℤ) → PSL(2,ℤ)` over `mk a` is `{a, -a}`. -/
theorem tsum_fiber_PSL2Z (F : PSL2Z → ℝ≥0∞) (b : PSL2Z) :
    ∑' B : (QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}, F (QuotientGroup.mk (B : SL(2, ℤ))) =
      2 * F b := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  have hne : a ≠ -a := by
    intro h
    have h2 : (a : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -(a : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
        (a : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -(a : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
        (a : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(a : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
        (a : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -(a : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        · have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) h
          simp only [Matrix.SpecialLinearGroup.coe_neg] at this
          first
          | exact congrFun (congrFun this 0) 0
          | exact congrFun (congrFun this 0) 1
          | exact congrFun (congrFun this 1) 0
          | exact congrFun (congrFun this 1) 1
    obtain ⟨e1, e2, -, -⟩ := h2
    have hdet := Matrix.SpecialLinearGroup.det_coe a
    rw [Matrix.det_fin_two] at hdet
    have z1 : (a : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by omega
    have z2 : (a : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by omega
    rw [z1, z2] at hdet
    simp at hdet
  have hfib : (QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {QuotientGroup.mk a} = {a, -a} := by
    ext B
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
    rw [eq_comm, PSL2Z_mk_eq_iff]
  have hc : ∀ B : (QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {QuotientGroup.mk a},
      F (QuotientGroup.mk (B : SL(2, ℤ))) = F (QuotientGroup.mk a) := fun B => by
    rw [show (QuotientGroup.mk (B : SL(2, ℤ)) : PSL2Z) = QuotientGroup.mk a from B.2]
  rw [tsum_congr hc, ENNReal.tsum_const, hfib]
  rw [show ENat.card ↑({a, -a} : Set SL(2, ℤ)) = 2 from Set.encard_pair hne]
  norm_num

/-- **Tiling by `SL(2,ℤ)`-translates of the modular cell.** `Σ_{B ∈ SL(2,ℤ)} ∫_𝒟 g(Bz) = 2 ∫_ℍ g`. -/
theorem tsum_lintegral_fd_smul (g : ℍ → ℝ≥0∞) :
    ∑' B : SL(2, ℤ), ∫⁻ z in ModularGroup.fd, g (B • z) = 2 * ∫⁻ w, g w := by
  rw [isFundamentalDomain_fd.lintegral_eq_tsum'' g, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_fiberwise _ (QuotientGroup.mk : SL(2, ℤ) → PSL2Z)]
  refine tsum_congr fun b => ?_
  have := tsum_fiber_PSL2Z (fun c : PSL2Z => ∫⁻ z in ModularGroup.fd, g (c • z)) b
  simpa only [PSL2Z_mk_smul] using this

/-- Coordinates of `Bz` for an integral matrix: `Im(Bz) = Im z / ((c x + d)² + (c y)²)`. -/
theorem im_smul_int (B : SL(2, ℤ)) (z : ℍ) :
    (B • z).im = z.im / (((B 1 0 : ℝ) * z.re + B 1 1) ^ 2 + ((B 1 0 : ℝ) * z.im) ^ 2) := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  congr 1
  simp [ModularGroup.denom_apply, Complex.normSq_apply]
  ring

/-- **Near a point, a height bound.**  If `u(z,w) ≤ R` then `Im z/(4R+2) ≤ Im w ≤ (4R+2) Im z` and
`|Re w - Re z|² ≤ 4R(4R+2) (Im z)²`. -/
theorem pairU_le_bounds {z w : ℍ} {R : ℝ} (h : pairU z w ≤ R) :
    z.im / (4 * R + 2) ≤ w.im ∧ w.im ≤ (4 * R + 2) * z.im ∧
      (w.re - z.re) ^ 2 ≤ 4 * R * (4 * R + 2) * z.im ^ 2 := by
  have hy := z.im_pos; have hv := w.im_pos
  have hR : 0 ≤ R := (pairU_nonneg z w).trans h
  have hd : dist (z : ℂ) w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  unfold pairU at h
  rw [div_le_iff₀ (by positivity), hd] at h
  have h1 : (z.im - w.im) ^ 2 ≤ R * (4 * z.im * w.im) := by nlinarith [sq_nonneg (z.re - w.re)]
  have h2 : (z.re - w.re) ^ 2 ≤ R * (4 * z.im * w.im) := by nlinarith [sq_nonneg (z.im - w.im)]
  have hK : 0 < 4 * R + 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hK]; nlinarith
  · nlinarith
  · have hwv : w.im ≤ (4 * R + 2) * z.im := by nlinarith
    have : (w.re - z.re) ^ 2 = (z.re - w.re) ^ 2 := by ring
    rw [this]
    calc (z.re - w.re) ^ 2 ≤ R * (4 * z.im * w.im) := h2
      _ ≤ R * (4 * z.im * ((4 * R + 2) * z.im)) := by gcongr
      _ = 4 * R * (4 * R + 2) * z.im ^ 2 := by ring

/-- `|n| ≤ n²` for integers. -/
theorem int_abs_le_sq (n : ℤ) : (|n| : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : |n| ≤ n ^ 2 := by
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · have h1 : 1 ≤ |n| := Int.one_le_abs h
      calc |n| = |n| * 1 := (mul_one _).symm
        _ ≤ |n| * |n| := by gcongr
        _ = n ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  exact_mod_cast h

/-- The squared-entry bound for matrices moving the modular cell near `z`. -/
def modularEntryBound (z : ℍ) (R : ℝ) : ℝ :=
  let Q := (4 * R + 2) / z.im
  let X := 2 * z.re ^ 2 + 8 * R * (4 * R + 2) * z.im ^ 2
  2 * (4 * (4 * R + 2) * z.im + 8 * Q * X) * (2 * Q ^ 2 + Q + 1) + 2 * X + 2 * Q +
    4 * (4 * R + 2) * z.im + 8 * Q * X + 2 * Q ^ 2 + Q + 4

theorem re_smul_int_of_c_eq_zero (B : SL(2, ℤ)) (hc : B 1 0 = 0) (z : ℍ) :
    (B • z).re = ((B 0 0 : ℝ) * z.re + B 0 1) / B 1 1 := by
  have h := UpperHalfPlane.coe_specialLinearGroup_apply B z
  have hre := congrArg Complex.re h
  rw [UpperHalfPlane.coe_re] at hre
  rw [hre, hc]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_zero, Complex.ofReal_zero, zero_mul,
    zero_add, Complex.ofReal_intCast]
  rw [Complex.div_intCast_re]
  simp

theorem entry_c_bound {c d x' y' Q : ℝ} (hy' : 1 / 2 ≤ y')
    (hD : (c * x' + d) ^ 2 + (c * y') ^ 2 ≤ Q * y') : c ^ 2 * y' ≤ Q ∧ c ^ 2 ≤ 2 * Q := by
  have hy0 : 0 < y' := by linarith
  have h1 : c ^ 2 * y' ^ 2 ≤ Q * y' := by nlinarith [sq_nonneg (c * x' + d)]
  have h2 : c ^ 2 * y' ≤ Q := by
    by_contra hc; push Not at hc
    have := mul_lt_mul_of_pos_right hc hy0
    nlinarith
  refine ⟨h2, ?_⟩
  have hc0 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith

theorem entry_d_bound {c d x' y' Q : ℝ} (hy' : 1 / 2 ≤ y') (hx' : x' ^ 2 ≤ 1 / 4) (hQ : 0 ≤ Q)
    (hD : (c * x' + d) ^ 2 + (c * y') ^ 2 ≤ Q * y') (hcd : 1 ≤ c ^ 2 ∨ (c = 0 ∧ d ^ 2 = 1)) :
    d ^ 2 ≤ 2 * Q ^ 2 + Q + 1 := by
  obtain ⟨hcy, hc2⟩ := entry_c_bound hy' hD
  rcases hcd with hc1 | ⟨-, hd1⟩
  · have hy'Q : y' ≤ Q := by nlinarith
    have h2 : (c * x' + d) ^ 2 ≤ Q * y' := by nlinarith [sq_nonneg (c * y')]
    have h3 : (c * x' + d) ^ 2 ≤ Q ^ 2 := by nlinarith
    have h4 : (c * x') ^ 2 ≤ c ^ 2 / 4 := by rw [mul_pow]; nlinarith [sq_nonneg c]
    nlinarith [sq_nonneg (c * x' - d), sq_nonneg (c * x' + d)]
  · nlinarith [sq_nonneg Q]

theorem entry_a_bound {a c u v K y Q X : ℝ} (hE : (-c * u + a) ^ 2 + (-c * v) ^ 2 ≤ 2 * v)
    (hv : v ≤ K * y) (hc2 : c ^ 2 ≤ 2 * Q) (hu : u ^ 2 ≤ X) (hQ : 0 ≤ Q) :
    a ^ 2 ≤ 4 * K * y + 8 * Q * X := by
  have h1 : (a - c * u) ^ 2 ≤ 2 * K * y := by nlinarith [sq_nonneg (-c * v)]
  have h2 : (c * u) ^ 2 ≤ 2 * Q * X := by
    rw [mul_pow]; exact mul_le_mul hc2 hu (sq_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a - 2 * c * u)]

theorem entry_b_bound {a b c d A Dd : ℝ} (hdet : a * d - b * c = 1) (hc1 : 1 ≤ c ^ 2)
    (ha : a ^ 2 ≤ A) (hd : d ^ 2 ≤ Dd) (hA : 0 ≤ A) : b ^ 2 ≤ 2 * (A * Dd) + 2 := by
  have hbc : b * c = a * d - 1 := by linarith
  have h1 : b ^ 2 ≤ (a * d - 1) ^ 2 := by
    rw [← hbc, mul_pow]; nlinarith [sq_nonneg b]
  have h2 : (a * d - 1) ^ 2 ≤ 2 * (a ^ 2 * d ^ 2) + 2 := by nlinarith [sq_nonneg (a * d + 1)]
  have h3 : a ^ 2 * d ^ 2 ≤ A * Dd := mul_le_mul ha hd (sq_nonneg _) hA
  linarith

theorem entryBound_eq (z : ℍ) (R : ℝ) :
    modularEntryBound z R = 2 * ((4 * (4 * R + 2) * z.im + 8 * ((4 * R + 2) / z.im) *
      (2 * z.re ^ 2 + 8 * R * (4 * R + 2) * z.im ^ 2)) *
      (2 * ((4 * R + 2) / z.im) ^ 2 + (4 * R + 2) / z.im + 1)) +
      2 * (2 * z.re ^ 2 + 8 * R * (4 * R + 2) * z.im ^ 2) + 2 * ((4 * R + 2) / z.im) +
      (4 * (4 * R + 2) * z.im + 8 * ((4 * R + 2) / z.im) *
        (2 * z.re ^ 2 + 8 * R * (4 * R + 2) * z.im ^ 2)) +
      (2 * ((4 * R + 2) / z.im) ^ 2 + (4 * R + 2) / z.im + 1) + 3 := by
  simp only [modularEntryBound]; ring

theorem entries_final {a b c d A Dd X Q : ℝ} (hQ : 0 ≤ Q) (hX : 0 ≤ X) (hA : 0 ≤ A) (hDd : 0 ≤ Dd)
    (ha : a ^ 2 ≤ A) (hb : b ^ 2 ≤ 2 * (A * Dd) + 2 * X + 2) (hc : c ^ 2 ≤ 2 * Q) (hd : d ^ 2 ≤ Dd) :
    let S := 2 * (A * Dd) + 2 * X + 2 * Q + A + Dd + 3
    a ^ 2 ≤ S ∧ b ^ 2 ≤ S ∧ c ^ 2 ≤ S ∧ d ^ 2 ≤ S := by
  intro S
  have hAD : 0 ≤ A * Dd := mul_nonneg hA hDd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [S] <;> linarith

theorem sq_le_two_add_sq (x b : ℝ) : b ^ 2 ≤ 2 * (x + b) ^ 2 + 2 * x ^ 2 := by
  nlinarith [sq_nonneg (2 * x + b)]

theorem sq_le_two_sub_sq (x b : ℝ) : b ^ 2 ≤ 2 * (x - b) ^ 2 + 2 * x ^ 2 := by
  nlinarith [sq_nonneg (2 * x - b)]

theorem det_real (B : SL(2, ℤ)) : (B 0 0 : ℝ) * B 1 1 - B 0 1 * B 1 0 = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe B
  rw [Matrix.det_fin_two] at this
  have h' : ((B 0 0 * B 1 1 - B 0 1 * B 1 0 : ℤ) : ℝ) = 1 := by exact_mod_cast this
  push_cast at h'; linarith

/-- For `c = 0` the upper right entry is the horizontal translation: `b² ≤ 2 Re(Bz)² + 2 Re(z)²`. -/
theorem b_sq_le_of_c_eq_zero (B : SL(2, ℤ)) (hc0 : B 1 0 = 0) (z : ℍ) :
    ((B 0 1 : ℤ) : ℝ) ^ 2 ≤ 2 * (B • z).re ^ 2 + 2 * z.re ^ 2 := by
  have hre := re_smul_int_of_c_eq_zero B hc0 z
  have hdet := det_real B
  have had : (B 0 0 : ℝ) * B 1 1 = 1 := by rw [hc0] at hdet; simpa using hdet
  have hd' : (B 0 0) * (B 1 1) = 1 := by
    have : ((B 0 0 * B 1 1 : ℤ) : ℝ) = 1 := by push_cast; exact had
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e : (B • z).re = z.re + (B 0 1 : ℝ) := by rw [hre]; simp [h1, h2]
    rw [e]; exact sq_le_two_add_sq _ _
  · have e : (B • z).re = z.re - (B 0 1 : ℝ) := by
      rw [hre]; simp only [h1, h2]; push_cast; ring
    rw [e]; exact sq_le_two_sub_sq _ _

/-- The two alternatives for the lower row. -/
theorem lower_row_alternative (B : SL(2, ℤ)) :
    1 ≤ ((B 1 0 : ℤ) : ℝ) ^ 2 ∨ (B 1 0 = 0 ∧ ((B 1 1 : ℤ) : ℝ) ^ 2 = 1) := by
  by_cases hc0 : (B 1 0) = 0
  · right
    have hdet := det_real B
    have hd' : (B 0 0) * (B 1 1) = 1 := by
      have : ((B 0 0 * B 1 1 : ℤ) : ℝ) = 1 := by push_cast; rw [hc0] at hdet; simpa using hdet
      exact_mod_cast this
    refine ⟨hc0, ?_⟩
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> simp [h1]
  · left
    have h1 : (1 : ℝ) ≤ |((B 1 0 : ℤ) : ℝ)| := by
      have := Int.one_le_abs hc0; exact_mod_cast this
    nlinarith [abs_nonneg ((B 1 0 : ℤ) : ℝ), sq_abs ((B 1 0 : ℤ) : ℝ)]

/-- The height inequality at a near point: `(cx'+d)² + (cy')² ≤ Q y'` with `Q = (4R+2)/Im z`. -/
theorem denom_le_of_pairU_le {z : ℍ} {R : ℝ} {B : SL(2, ℤ)} {z' : ℍ} (h : pairU z (B • z') ≤ R) :
    ((B 1 0 : ℝ) * z'.re + B 1 1) ^ 2 + ((B 1 0 : ℝ) * z'.im) ^ 2 ≤
      (4 * R + 2) / z.im * z'.im := by
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  have hy := z.im_pos
  have hK0 : 0 < 4 * R + 2 := by linarith
  obtain ⟨hv₀, -, -⟩ := pairU_le_bounds h
  have hIm := im_smul_int B z'
  have hDpos : 0 < ((B 1 0 : ℝ) * z'.re + B 1 1) ^ 2 + ((B 1 0 : ℝ) * z'.im) ^ 2 := by
    have : 0 < (B • z').im := (B • z').im_pos
    rw [hIm] at this
    exact (div_pos_iff_of_pos_left z'.im_pos).1 this
  rw [hIm, div_le_div_iff₀ hK0 hDpos] at hv₀
  rw [div_mul_eq_mul_div, le_div_iff₀ hy]; nlinarith

/-- The upper-left entry through the inverse: `(a - c Re w)² + (c Im w)² ≤ 2 Im w` for `w = Bz'`,
`z' ∈ 𝒟`. -/
theorem inverse_row_le {B : SL(2, ℤ)} {z' : ℍ} (hz' : z' ∈ ModularGroup.fd) :
    (-(B 1 0 : ℝ) * (B • z').re + B 0 0) ^ 2 + (-(B 1 0 : ℝ) * (B • z').im) ^ 2 ≤
      2 * (B • z').im := by
  have hy'2 : 3 ≤ 4 * z'.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz'
  have hy'0 := z'.im_pos
  have hy' : 1 / 2 ≤ z'.im := by nlinarith
  have hinv := im_smul_int B⁻¹ (B • z')
  rw [inv_smul_smul, Matrix.SpecialLinearGroup.SL2_inv_expl] at hinv
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_neg] at hinv
  have hw0 := (B • z').im_pos
  have hE0 : 0 < (-(B 1 0 : ℝ) * (B • z').re + B 0 0) ^ 2 + (-(B 1 0 : ℝ) * (B • z').im) ^ 2 := by
    have : 0 < z'.im := hy'0
    rw [hinv] at this
    exact (div_pos_iff_of_pos_left hw0).1 this
  rw [hinv, le_div_iff₀ hE0] at hy'
  nlinarith

/-- **All entries of a matrix moving the modular cell near a point are bounded.** -/
theorem entries_sq_le_of_pairU_le {z : ℍ} {R : ℝ} {B : SL(2, ℤ)} {z' : ℍ}
    (hz' : z' ∈ ModularGroup.fd) (h : pairU z (B • z') ≤ R) :
    ∀ i j, ((B i j : ℤ) : ℝ) ^ 2 ≤ modularEntryBound z R := by
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  have hy := z.im_pos
  obtain ⟨-, hvK, hx⟩ := pairU_le_bounds h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (4 * R + 2) / z.im := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = 2 * z.re ^ 2 + 8 * R * (4 * R + 2) * z.im ^ 2 := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hy'2 : 3 ≤ 4 * z'.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz'
  have hy' : 1 / 2 ≤ z'.im := by nlinarith [z'.im_pos]
  have hx'2 : z'.re ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 hz'.2; nlinarith
  have hxw : (B • z').re ^ 2 ≤ X := by
    rw [hX]; nlinarith [sq_nonneg ((B • z').re - 2 * z.re)]
  have hDle := denom_le_of_pairU_le h
  rw [← hQ] at hDle
  obtain ⟨-, hc2⟩ := entry_c_bound hy' hDle
  have hcd := lower_row_alternative B
  have hcd' : 1 ≤ ((B 1 0 : ℤ) : ℝ) ^ 2 ∨ (((B 1 0 : ℤ) : ℝ) = 0 ∧ ((B 1 1 : ℤ) : ℝ) ^ 2 = 1) := by
    rcases hcd with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨by simp [h1], h2⟩
  have hd2 := entry_d_bound hy' hx'2 hQ0.le hDle hcd'
  have ha2 := entry_a_bound (inverse_row_le hz') hvK hc2 hxw hQ0.le
  obtain ⟨A, hA⟩ : ∃ A, A = 4 * (4 * R + 2) * z.im + 8 * Q * X := ⟨_, rfl⟩
  obtain ⟨Dd, hDd⟩ : ∃ Dd, Dd = 2 * Q ^ 2 + Q + 1 := ⟨_, rfl⟩
  rw [← hA] at ha2; rw [← hDd] at hd2
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hDd0 : 0 ≤ Dd := by rw [hDd]; positivity
  have hAD := mul_nonneg hA0 hDd0
  have hb2 : ((B 0 1 : ℤ) : ℝ) ^ 2 ≤ 2 * (A * Dd) + 2 * X + 2 := by
    rcases hcd with hc1 | ⟨hc0, -⟩
    · have := entry_b_bound (det_real B) hc1 ha2 hd2 hA0
      linarith
    · have := b_sq_le_of_c_eq_zero B hc0 z'
      linarith
  obtain ⟨h00, h01, h10, h11⟩ := entries_final hQ0.le hX0 hA0 hDd0 ha2 hb2 hc2 hd2
  have hS : modularEntryBound z R = 2 * (A * Dd) + 2 * X + 2 * Q + A + Dd + 3 := by
    rw [entryBound_eq, hA, hDd, hQ, hX]
  intro i j
  rw [hS]
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- **Local finiteness.**  Only finitely many `SL(2,ℤ)`-translates of the modular cell come within
`u ≤ R` of a given point. -/
theorem finite_near_fd (z : ℍ) (R : ℝ) :
    {B : SL(2, ℤ) | ∃ z' ∈ ModularGroup.fd, pairU z (B • z') ≤ R}.Finite := by
  set M : ℤ := ⌈modularEntryBound z R⌉ with hM
  have hbox : ({A : Fin 2 → Fin 2 → ℤ | ∀ i j, A i j ∈ Set.Icc (-M) M}).Finite := by
    have : {A : Fin 2 → Fin 2 → ℤ | ∀ i j, A i j ∈ Set.Icc (-M) M} =
        Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (-M) M)) := by
      ext A; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    rw [this]
    exact Set.Finite.pi (fun _ => Set.Finite.pi (fun _ => Set.finite_Icc _ _))
  refine (hbox.preimage (f := fun B : SL(2, ℤ) => ((B : Matrix (Fin 2) (Fin 2) ℤ) :
    Fin 2 → Fin 2 → ℤ)) (fun a _ b _ hab => Subtype.ext hab)).subset ?_
  rintro B ⟨z', hz', h⟩
  intro i j
  have h1 := entries_sq_le_of_pairU_le hz' h i j
  have h2 := int_abs_le_sq (B i j)
  have h3 : (|B i j| : ℝ) ≤ M := by
    have := Int.le_ceil (modularEntryBound z R)
    rw [← hM] at this
    linarith
  have h4 : |B i j| ≤ M := by exact_mod_cast h3
  exact abs_le.1 h4

end

end GaloisForLFunctions.HTGeometry
