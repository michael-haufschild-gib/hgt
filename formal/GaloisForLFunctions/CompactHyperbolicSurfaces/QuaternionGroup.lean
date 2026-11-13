import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionOrder
import GaloisForLFunctions.CompactHyperbolicSurfaces.CocompactGroups

/-!
# The congruence subgroups `Γ(N)` of the unit group of `O`

`Γ(N) = {quatMat x : nrd x = 1, x ≡ 1 mod N·O}` is a subgroup of `SL(2, ℝ)` (`congGroup`).

* `four_mul_pairU_I_smul_I_add_two`: `4u(i, g·i) + 2 = a² + b² + c² + d²` for `g ∈ SL(2, ℝ)`;
* `finite_dist_congGroup`: only finitely many `γ` move `i` a bounded distance — bounded entries
  give bounded integer coordinates;
* `eq_one_of_smul_eq_congGroup` (`N ≥ 3`): `Γ(N)` acts freely.  A fixed point forces `γ = ±1` or
  `(tr γ)² < 4`, while `tr γ = 2x₀` with `x₀ ≡ 1 mod N`.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem nrd_quatMul (x y : Fin 4 → ℤ) : nrd (quatMul x y) = nrd x * nrd y := by
  have h := det_quatMat (quatMul x y)
  rw [← quatMat_mul, det_mul, det_quatMat, det_quatMat] at h
  exact_mod_cast h.symm

/-- `x ≡ 1 mod N·O`. -/
def IsCong (N : ℕ) (x : Fin 4 → ℤ) : Prop := ∃ u : Fin 4 → ℤ, x = quatOne + (N : ℤ) • u

theorem isCong_one (N : ℕ) : IsCong N quatOne := ⟨0, by simp⟩

theorem isCong_mul {N : ℕ} {x y : Fin 4 → ℤ} (hx : IsCong N x) (hy : IsCong N y) :
    IsCong N (quatMul x y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u + v + (N : ℤ) • quatMul u v, ?_⟩
  funext k
  fin_cases k <;> simp [quatMul, quatOne, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem isCong_conj {N : ℕ} {x : Fin 4 → ℤ} (hx : IsCong N x) : IsCong N (quatConj x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨quatConj u, ?_⟩
  funext k
  fin_cases k <;> simp [quatConj, quatOne]

/-- **The congruence subgroup** `Γ(N) = {γ ∈ O¹ : γ ≡ 1 mod N}` of `SL(2, ℝ)`. -/
def congGroup (N : ℕ) : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ x, nrd x = 1 ∧ IsCong N x ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) = quatMat x}
  one_mem' := ⟨quatOne, by simp [nrd, quatOne], isCong_one N, by
    rw [Matrix.SpecialLinearGroup.coe_one, quatMat_one]⟩
  mul_mem' := by
    rintro g h ⟨x, hx1, hxc, hxg⟩ ⟨y, hy1, hyc, hyg⟩
    refine ⟨quatMul x y, by rw [nrd_quatMul, hx1, hy1, one_mul], isCong_mul hxc hyc, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hxg, hyg, quatMat_mul]
  inv_mem' := by
    rintro g ⟨x, hx1, hxc, hxg⟩
    refine ⟨quatConj x, by rw [nrd_quatConj, hx1], isCong_conj hxc, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hxg, adjugate_quatMat]

theorem mem_congGroup {N : ℕ} {g : SL(2, ℝ)} : g ∈ congGroup N ↔
    ∃ x, nrd x = 1 ∧ IsCong N x ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) = quatMat x := Iff.rfl

/-! ### The point-pair invariant of `i` and `g·i` -/

/-- **The norm formula.**  `4u(i, g·i) + 2 = a² + b² + c² + d²`. -/
theorem four_mul_pairU_I_smul_I_add_two (g : SL(2, ℝ)) :
    4 * pairU I (g • I) + 2 = g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = g 0 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = g 0 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = g 1 0 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = g 1 1 := ⟨_, rfl⟩
  have hdet : a * d - b * c = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    rw [ha, hb, hc, hd]; exact h
  rw [← ha, ← hb, ← hc, ← hd]
  set w : ℍ := g • I with hw
  have hcd : (c : ℂ) * Complex.I + d ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    rw [h1, h2] at hdet
    simp at hdet
  have hwc : (w : ℂ) = ((a : ℂ) * Complex.I + b) / ((c : ℂ) * Complex.I + d) := by
    rw [hw, coe_specialLinearGroup_apply, UpperHalfPlane.coe_I]
    subst ha hb hc hd
    simp
  have hmul : (w : ℂ) * ((c : ℂ) * Complex.I + d) = (a : ℂ) * Complex.I + b := by
    rw [hwc, div_mul_cancel₀ _ hcd]
  have hre := congrArg Complex.re hmul
  have him := congrArg Complex.im hmul
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
    sub_self] at hre him
  have hS : 0 < c ^ 2 + d ^ 2 := by
    rcases eq_or_ne c 0 with h | h
    · rcases eq_or_ne d 0 with h' | h'
      · rw [h, h'] at hdet; simp at hdet
      · positivity
    · positivity
  have hyS : (w : ℂ).im * (c ^ 2 + d ^ 2) = 1 := by linear_combination d * him - c * hre + hdet
  have hxS : (w : ℂ).re * (c ^ 2 + d ^ 2) = a * c + b * d := by
    linear_combination d * hre + c * him
  have hy' : (w : ℂ).im = 1 / (c ^ 2 + d ^ 2) := by field_simp; linarith
  have hx' : (w : ℂ).re = (a * c + b * d) / (c ^ 2 + d ^ 2) := by field_simp; linarith
  have hwim : w.im = 1 / (c ^ 2 + d ^ 2) := by rw [← UpperHalfPlane.coe_im]; exact hy'
  rw [pairU, Complex.dist_eq, UpperHalfPlane.I_im, UpperHalfPlane.coe_I, Complex.sq_norm,
    Complex.normSq_apply, hwim]
  simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  have hL : (a * c + b * d) ^ 2 + 1 = (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) := by
    linear_combination (-(a * d - b * c) - 1) * hdet
  rw [hy', hx']
  field_simp
  linear_combination hL

/-! ### Discreteness -/

/-- **`Γ(N)` is discrete**: only finitely many `γ` move `i` within distance `R`. -/
theorem finite_dist_congGroup (N : ℕ) (R : ℝ) :
    {γ : congGroup N | dist I ((γ : SL(2, ℝ)) • I) ≤ R}.Finite := by
  set r := max R 0
  set t := Real.sqrt (4 * ((Real.cosh r - 1) / 2) + 2)
  have hbound : ∀ γ : congGroup N, dist I ((γ : SL(2, ℝ)) • I) ≤ R →
      ∀ i j, |(γ : SL(2, ℝ)) i j| ≤ t := by
    intro γ hγ i j
    have hd : dist I ((γ : SL(2, ℝ)) • I) ≤ r := hγ.trans (le_max_left _ _)
    have hu := (dist_le_iff_pairU_le (le_max_right R 0)).mp hd
    have h4 := four_mul_pairU_I_smul_I_add_two (γ : SL(2, ℝ))
    have hsq : ((γ : SL(2, ℝ)) i j) ^ 2 ≤ 4 * ((Real.cosh r - 1) / 2) + 2 := by
      have e00 := sq_nonneg ((γ : SL(2, ℝ)) 0 0)
      have e01 := sq_nonneg ((γ : SL(2, ℝ)) 0 1)
      have e10 := sq_nonneg ((γ : SL(2, ℝ)) 1 0)
      have e11 := sq_nonneg ((γ : SL(2, ℝ)) 1 1)
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith
    exact Real.abs_le_sqrt hsq
  have hfin : ((fun n : Fin 4 → ℤ => fun k => (n k : ℝ)) ''
      Set.univ.pi fun _ => Set.Icc (-⌈t⌉) ⌈t⌉).Finite :=
    (Set.Finite.pi fun _ => Set.finite_Icc _ _).image _
  refine Set.Finite.of_finite_image
    (f := fun γ : congGroup N => quatCoeff ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ))
    (hfin.subset ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨x, -, -, hx⟩ := γ.2
    have hb := abs_coord_le_of_entries (x := x) (t := t) fun i j => by
      rw [← hx]; exact hbound γ hγ i j
    refine ⟨x, fun k _ => ⟨?_, ?_⟩, ?_⟩
    · have h1 := (abs_le.mp (hb k)).1
      have h2 := Int.le_ceil t
      have : (-(⌈t⌉ : ℝ)) ≤ (x k : ℝ) := by linarith
      exact_mod_cast this
    · have h1 := (abs_le.mp (hb k)).2
      have h2 := Int.le_ceil t
      have : (x k : ℝ) ≤ (⌈t⌉ : ℝ) := by linarith
      exact_mod_cast this
    · simp only
      rw [hx, quatMat, quatCoeff_quatMatR]
  · intro γ _ γ' _ h
    obtain ⟨x, -, -, hx⟩ := γ.2
    obtain ⟨x', -, -, hx'⟩ := γ'.2
    simp only at h
    rw [hx, hx', quatMat, quatMat, quatCoeff_quatMatR, quatCoeff_quatMatR] at h
    have hm : ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = ((γ' : SL(2, ℝ)) : Matrix _ _ ℝ) := by
      rw [hx, hx', quatMat, quatMat, h]
    exact Subtype.ext (Subtype.ext hm)

/-! ### Freeness -/

/-- **Fixed points.**  If `g ∈ SL(2, ℝ)` fixes a point of `ℍ`, then either `g` is the scalar
`diag(a, a)` or `(tr g)² < 4`: with `z = x + iy`, `a − d = 2cx`, `b = −c(x² + y²)`, so
`(tr g)² − 4 = (a − d)² + 4bc = −4c²y²`. -/
theorem fixed_point_trace {g : SL(2, ℝ)} {z : ℍ} (h : g • z = z) :
    (g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) ∨ (g 0 0 + g 1 1) ^ 2 < 4 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  have hy : 0 < z.im := z.im_pos
  have hc : (((g 0 0 : ℝ) : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) = z := by
    have := congrArg UpperHalfPlane.coe h
    rw [coe_specialLinearGroup_apply] at this
    exact this
  have hden : ((g 1 0 : ℝ) : ℂ) * z + (g 1 1 : ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.im h0
    have h2 := congrArg Complex.re h0
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero, Complex.zero_re,
      UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at h1 h2
    have hc0 : g 1 0 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hy.ne'
    rw [hc0, zero_mul, zero_add] at h2
    rw [hc0, h2] at hdet
    simp at hdet
  rw [div_eq_iff hden] at hc
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.add_re, Complex.mul_re, sub_zero, UpperHalfPlane.coe_im,
    UpperHalfPlane.coe_re] at hre him
  -- `him : a y = (x)(c y) + y (c x + d)`, `hre : a x + b = x (c x + d) − y (c y)`
  have had : g 0 0 - g 1 1 = 2 * g 1 0 * z.re := by
    have : (g 0 0 - g 1 1 - 2 * g 1 0 * z.re) * z.im = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hy.ne'
  have hb : g 0 1 = -(g 1 0) * (z.re ^ 2 + z.im ^ 2) := by
    linear_combination hre - z.re * had
  by_cases hc0 : g 1 0 = 0
  · left
    refine ⟨hc0, ?_, ?_⟩
    · rw [hb, hc0]; ring
    · rw [hc0] at had; linarith
  · right
    have hneg : (g 0 0 + g 1 1) ^ 2 - 4 = -4 * (g 1 0) ^ 2 * z.im ^ 2 := by
      have e1 : (g 0 0 + g 1 1) ^ 2 - 4 = (g 0 0 - g 1 1) ^ 2 + 4 * (g 0 1 * g 1 0) := by
        linear_combination 4 * hdet
      rw [e1, had, hb]; ring
    have : 0 < (g 1 0) ^ 2 * z.im ^ 2 := by positivity
    linarith

/-- **`Γ(N)` acts freely for `N ≥ 3`.** -/
theorem eq_one_of_smul_eq_congGroup {N : ℕ} (hN : 3 ≤ N) (γ : congGroup N) (z : ℍ)
    (h : (γ : SL(2, ℝ)) • z = z) : γ = 1 := by
  obtain ⟨x, hx1, ⟨u, hu⟩, hxg⟩ := γ.2
  have hent : ∀ i j, (γ : SL(2, ℝ)) i j = quatMat x i j := fun i j => by
    rw [show (γ : SL(2, ℝ)) i j = ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j from rfl, hxg]
  have hx0 : x 0 = 1 + (N : ℤ) * u 0 := by
    have := congrFun hu 0
    simpa [quatOne] using this
  have htr : (γ : SL(2, ℝ)) 0 0 + (γ : SL(2, ℝ)) 1 1 = 2 * (x 0 : ℝ) := by
    rw [hent, hent]; simp [quatMat_apply]; ring
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  rcases fixed_point_trace h with ⟨h10, h01, hdiag⟩ | hlt
  · -- `γ` is scalar: its coordinates are `(a, 0, 0, 0)` with `a² = 1`
    have hco : ∀ k, (x k : ℝ) = quatCoeff (quatMat x) k := fun k => by
      rw [quatMat, quatCoeff_quatMatR]
    have e1 : x 1 = 0 := by
      have := hco 1
      rw [show quatCoeff (quatMat x) 1 = (quatMat x 0 0 - quatMat x 1 1) / (2 * √2) from rfl,
        ← hent, ← hent, hdiag, sub_self, zero_div] at this
      exact_mod_cast this
    have e2 : x 2 = 0 := by
      have := hco 2
      rw [show quatCoeff (quatMat x) 2 = (quatMat x 0 1 / 3 + quatMat x 1 0) / 2 from rfl,
        ← hent, ← hent, h01, h10] at this
      norm_num at this
      exact_mod_cast this
    have e3 : x 3 = 0 := by
      have := hco 3
      rw [show quatCoeff (quatMat x) 3 = (quatMat x 0 1 / 3 - quatMat x 1 0) / (2 * √2) from rfl,
        ← hent, ← hent, h01, h10] at this
      norm_num at this
      exact_mod_cast this
    have hsq : x 0 ^ 2 = 1 := by rw [← hx1, nrd, e1, e2, e3]; ring
    have hx0' : x 0 = 1 := by
      have hfac : (x 0 - 1) * (x 0 + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h' | h'
      · linarith
      · exfalso
        have hd : (N : ℤ) ∣ 2 := ⟨-u 0, by linarith⟩
        have := Int.le_of_dvd (by norm_num) hd
        omega
    have hxe : x = quatOne := by
      funext k; fin_cases k
      · simp [quatOne, hx0']
      · simp [quatOne, e1]
      · simp [quatOne, e2]
      · simp [quatOne, e3]
    apply Subtype.ext
    apply Subtype.ext
    rw [hxg, hxe, quatMat_one]
    rfl
  · exfalso
    rw [htr] at hlt
    have hx00 : x 0 = 0 := by
      have : ((x 0) : ℝ) ^ 2 < 1 := by nlinarith
      have h' : x 0 ^ 2 < 1 := by exact_mod_cast this
      nlinarith [sq_nonneg (x 0)]
    have hd : (N : ℤ) ∣ 1 := ⟨-u 0, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd
    omega

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
