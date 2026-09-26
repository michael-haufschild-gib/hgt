import GaloisForLFunctions.RHTower.ThetaPowerSaddleFarField

/-!
# Two-sided modular bounds for the theta-power family

For `g ∈ SL(2,ℤ)` the modulus law `|θ_v(τ)| = |c'z+d'|^{1/2}|θ_{v·ḡ}(z)|` (`z = gτ`) turns
`|F_a| = |θ₂|^a|θ₄|^a|θ₃|^{1-2a}` into the exact identity

  `|F_a(τ)| (Im τ)^{1/4} = (Im gτ)^{1/4} · A^a C^a B^{1-2a}`,

with `A, B, C` the moduli of the three theta constants at `gτ`, in a permuted order.  Reducing `τ` into
the fundamental domain (`Im gτ ≥ 4/5`) gives:

* for `0 < a < 1/2` a Hecke bound `|F_a(τ)| ≤ C (Im τ)^{-1/4}` on all of `ℍ`: the theta constant `θ₂`,
  the only small one, always carries a positive exponent `a` or `1 - 2a`;
* for `0 ≤ a ≤ 1/2` a lower bound `|F_a(τ)| (Im τ)^{1/4} ≥ (4/5)^{1/4} min(e^{-πK/4}, 1/2)` whenever
  `Im gτ ≤ K`.
-/

open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Real

namespace RHTower

noncomputable section

open Bottcher

/-- **The modular modulus identity.** -/
theorem norm_thetaPowerForm_mul_im_rpow (a : ℝ) (τ : ℍ) (g : SL(2, ℤ)) :
    ∃ v2 v3 v4 : Fin 2 → ZMod 2, v2 ≠ 0 ∧ v3 ≠ 0 ∧ v4 ≠ 0 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧
      ‖thetaPowerForm a (τ : ℂ)‖ * τ.im ^ (1 / 4 : ℝ) =
        (g • τ).im ^ (1 / 4 : ℝ) *
          (‖thetaChar v2 ((g • τ : ℍ) : ℂ)‖ ^ a * ‖thetaChar v4 ((g • τ : ℍ) : ℂ)‖ ^ a *
            ‖thetaChar v3 ((g • τ : ℍ) : ℂ)‖ ^ (1 - 2 * a)) := by
  set z' : ℍ := g • τ with hz'
  have hτeq : (τ : ℂ) = ((g⁻¹ • z' : ℍ) : ℂ) := by rw [hz', inv_smul_smul]
  have hlaw := thetaModulusLaw g⁻¹ z'
  set D : ℝ := ‖slDen g⁻¹ (z' : ℂ)‖ with hD
  have hDpos : 0 < D := norm_pos_iff.mpr (slDen_ne_zero _ _)
  set a2 := charAct ![0, 1] (slRed g⁻¹)
  set a3 := charAct ![1, 1] (slRed g⁻¹)
  set a4 := charAct ![1, 0] (slRed g⁻¹)
  have hn2 : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hn3 : (![1, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hn4 : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have e2 := hlaw _ hn2
  have e3 := hlaw _ hn3
  have e4 := hlaw _ hn4
  rw [thetaChar_two, ← hτeq] at e2
  rw [thetaChar_three, ← hτeq] at e3
  rw [thetaChar_four, ← hτeq] at e4
  have hinj : ∀ {u v : Fin 2 → ZMod 2}, charAct u (slRed g⁻¹) = charAct v (slRed g⁻¹) → u = v := by
    intro u v h
    have := congrArg (fun w => charAct w (slRed g⁻¹)⁻¹) h
    simp only [← charAct_mul, mul_inv_cancel] at this
    simpa [charAct] using this
  refine ⟨a2, a3, a4, charAct_ne_zero hn2 _, charAct_ne_zero hn3 _, charAct_ne_zero hn4 _,
    fun h => absurd (hinj h) (by decide), fun h => absurd (hinj h) (by decide),
    fun h => absurd (hinj h) (by decide), ?_⟩
  set A := ‖thetaChar a2 (z' : ℂ)‖
  set B := ‖thetaChar a3 (z' : ℂ)‖
  set C := ‖thetaChar a4 (z' : ℂ)‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hsD : 0 < D ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hB0 : 0 < B := by
    have h' : 0 < ‖thetaThree (τ : ℂ)‖ := norm_pos_iff.mpr (thetaThree_ne_zero_of_im_pos τ.im_pos)
    rw [show ‖thetaThree (τ : ℂ)‖ = D ^ (1 / 2 : ℝ) * B from e3] at h'
    exact pos_of_mul_pos_right h' hsD.le
  have hnorm : ‖thetaPowerForm a (τ : ℂ)‖ = D ^ (1 / 2 : ℝ) * (A ^ a * C ^ a * B ^ (1 - 2 * a)) := by
    rw [norm_thetaPowerForm_rpow a τ.im_pos, e2, e3, e4]
    exact rpow_theta_modulus hsD hA0 hB0 hC0
  have him : τ.im = z'.im / D ^ 2 := by
    have h := ModularGroup.im_smul_eq_div_normSq g⁻¹ z'
    rw [ModularGroup.denom_apply, Complex.normSq_eq_norm_sq] at h
    have h' : (τ.im : ℝ) = (g⁻¹ • z').im := by
      rw [← UpperHalfPlane.coe_im, hτeq, UpperHalfPlane.coe_im]
    rw [h', h, hD, slDen]
  have hz'pos : 0 < z'.im := z'.im_pos
  have hquart : τ.im ^ (1 / 4 : ℝ) = z'.im ^ (1 / 4 : ℝ) * (D ^ (1 / 2 : ℝ))⁻¹ := by
    rw [him, Real.div_rpow hz'pos.le (by positivity), div_eq_mul_inv]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]; norm_num
  rw [hnorm, hquart]
  field_simp

/-- Exactly one of three distinct nonzero vectors of `𝔽₂²` is `(0,1)`. -/
theorem char_triple_cases {v2 v3 v4 : Fin 2 → ZMod 2} (h2 : v2 ≠ 0) (h3 : v3 ≠ 0) (h4 : v4 ≠ 0)
    (h23 : v2 ≠ v3) (h24 : v2 ≠ v4) (h34 : v3 ≠ v4) :
    (v2 = ![0, 1] ∧ v3 ≠ ![0, 1] ∧ v4 ≠ ![0, 1]) ∨
      (v3 = ![0, 1] ∧ v2 ≠ ![0, 1] ∧ v4 ≠ ![0, 1]) ∨
        (v4 = ![0, 1] ∧ v2 ≠ ![0, 1] ∧ v3 ≠ ![0, 1]) := by
  rcases char_cases v2 h2 with rfl | rfl | rfl <;> rcases char_cases v3 h3 with rfl | rfl | rfl <;>
    rcases char_cases v4 h4 with rfl | rfl | rfl <;> simp_all

/-- `u^{1/4} ≤ e^u` for `u ≥ 0`. -/
theorem rpow_quarter_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ (1 / 4 : ℝ) ≤ Real.exp u := by
  rcases le_total u 1 with h1 | h1
  · calc u ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hu h1 (by norm_num)
      _ ≤ Real.exp u := Real.one_le_exp hu
  · calc u ^ (1 / 4 : ℝ) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = u := Real.rpow_one u
      _ ≤ u + 1 := by linarith
      _ ≤ Real.exp u := Real.add_one_le_exp u

/-- `y^{1/4} e^{-cy} ≤ c^{-1/4}` for `c > 0`, `y ≥ 0`. -/
theorem rpow_quarter_mul_exp_neg_le {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    y ^ (1 / 4 : ℝ) * Real.exp (-(c * y)) ≤ c ^ (-(1 / 4 : ℝ)) := by
  have h := rpow_quarter_le_exp (mul_nonneg hc.le hy)
  rw [Real.mul_rpow hc.le hy] at h
  have hc4 : 0 < c ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hc _
  rw [Real.rpow_neg hc.le, Real.exp_neg]
  have h' : y ^ (1 / 4 : ℝ) ≤ Real.exp (c * y) / c ^ (1 / 4 : ℝ) := by
    rw [le_div_iff₀ hc4]; linarith
  calc y ^ (1 / 4 : ℝ) * (Real.exp (c * y))⁻¹ ≤ Real.exp (c * y) / c ^ (1 / 4 : ℝ) *
        (Real.exp (c * y))⁻¹ := by gcongr
    _ = (c ^ (1 / 4 : ℝ))⁻¹ := by field_simp

/-- The product bound when `θ₂` is the only small theta constant. -/
theorem theta_product_le {a A B C y : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hC0 : 0 ≤ C) (hy : 0 ≤ y)
    (hcase : (A ≤ 3 * Real.exp (-π * y / 4) ∧ B ≤ 2 ∧ C ≤ 2) ∨
      (B ≤ 3 * Real.exp (-π * y / 4) ∧ A ≤ 2 ∧ C ≤ 2) ∨
        (C ≤ 3 * Real.exp (-π * y / 4) ∧ A ≤ 2 ∧ B ≤ 2)) :
    A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ 12 * Real.exp (-(π * min a (1 - 2 * a) / 4 * y)) := by
  have hb : 0 < 1 - 2 * a := by linarith
  set κ := min a (1 - 2 * a) with hκ
  have hκa : κ ≤ a := min_le_left _ _
  have hκb : κ ≤ 1 - 2 * a := min_le_right _ _
  have hE : ∀ p : ℝ, κ ≤ p → Real.exp (-π * y / 4) ^ p ≤ Real.exp (-(π * κ / 4 * y)) := by
    intro p hp
    rw [← Real.exp_mul]; apply Real.exp_le_exp.mpr
    have : 0 ≤ π * y / 4 := by positivity
    nlinarith
  have h2a : (2 : ℝ) ^ a ≤ 2 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h2b : (2 : ℝ) ^ (1 - 2 * a) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - 2 * a) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h3a : (3 : ℝ) ^ a ≤ 3 := by
    calc (3 : ℝ) ^ a ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := Real.rpow_one 3
  have h3b : (3 : ℝ) ^ (1 - 2 * a) ≤ 3 := by
    calc (3 : ℝ) ^ (1 - 2 * a) ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := Real.rpow_one 3
  have hsmall : ∀ {X : ℝ} {p : ℝ}, 0 ≤ X → 0 < p → κ ≤ p → X ≤ 3 * Real.exp (-π * y / 4) →
      (3 : ℝ) ^ p ≤ 3 → X ^ p ≤ 3 * Real.exp (-(π * κ / 4 * y)) := by
    intro X p hX hp hκp hXle h3p
    calc X ^ p ≤ (3 * Real.exp (-π * y / 4)) ^ p := Real.rpow_le_rpow hX hXle hp.le
      _ = 3 ^ p * Real.exp (-π * y / 4) ^ p := Real.mul_rpow (by norm_num) (Real.exp_pos _).le
      _ ≤ 3 * Real.exp (-(π * κ / 4 * y)) :=
          mul_le_mul h3p (hE p hκp) (by positivity) (by norm_num)
  have hbig : ∀ {X : ℝ} {p : ℝ}, 0 ≤ X → 0 < p → X ≤ 2 → (2 : ℝ) ^ p ≤ 2 → X ^ p ≤ 2 := by
    intro X p hX hp hX2 h2p
    exact (Real.rpow_le_rpow hX hX2 hp.le).trans h2p
  have hEpos : 0 < Real.exp (-(π * κ / 4 * y)) := Real.exp_pos _
  rcases hcase with ⟨hA, hB, hC⟩ | ⟨hB, hA, hC⟩ | ⟨hC, hA, hB⟩
  · have e1 := hsmall hA0 ha0 hκa hA h3a
    have e2 := hbig hC0 ha0 hC h2a
    have e3 := hbig hB0 hb hB h2b
    calc A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ (3 * Real.exp (-(π * κ / 4 * y))) * 2 * 2 := by
          gcongr
      _ = 12 * Real.exp (-(π * κ / 4 * y)) := by ring
  · have e1 := hsmall hB0 hb hκb hB h3b
    have e2 := hbig hA0 ha0 hA h2a
    have e3 := hbig hC0 ha0 hC h2a
    calc A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ 2 * 2 * (3 * Real.exp (-(π * κ / 4 * y))) := by
          gcongr
      _ = 12 * Real.exp (-(π * κ / 4 * y)) := by ring
  · have e1 := hsmall hC0 ha0 hκa hC h3a
    have e2 := hbig hA0 ha0 hA h2a
    have e3 := hbig hB0 hb hB h2b
    calc A ^ a * C ^ a * B ^ (1 - 2 * a) ≤ 2 * (3 * Real.exp (-(π * κ / 4 * y))) * 2 := by
          gcongr
      _ = 12 * Real.exp (-(π * κ / 4 * y)) := by ring

/-- The Hecke constant of `F_a`. -/
def thetaPowerHeckeConstant (a : ℝ) : ℝ := 12 * (π * min a (1 - 2 * a) / 4) ^ (-(1 / 4 : ℝ))

/-- **Hecke bound.** For `0 < a < 1/2`, `|F_a(τ)| (Im τ)^{1/4}` is bounded on `ℍ`. -/
theorem norm_thetaPowerForm_mul_im_le (ha0 : 0 < a) (ha1 : a < 1 / 2) (τ : ℍ) :
    ‖thetaPowerForm a (τ : ℂ)‖ * τ.im ^ (1 / 4 : ℝ) ≤ thetaPowerHeckeConstant a := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have him : (4 : ℝ) / 5 ≤ ((g • τ : ℍ) : ℂ).im := by
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • τ).im_pos
    show (4 : ℝ) / 5 ≤ (g • τ).im
    nlinarith
  obtain ⟨v2, v3, v4, h2, h3, h4, h23, h24, h34, hid⟩ := norm_thetaPowerForm_mul_im_rpow a τ g
  rw [hid]
  set y := (g • τ).im with hy
  have hy0 : 0 ≤ y := (g • τ).im_pos.le
  have hθ2 : ∀ v : Fin 2 → ZMod 2, v = ![0, 1] →
      ‖thetaChar v ((g • τ : ℍ) : ℂ)‖ ≤ 3 * Real.exp (-π * y / 4) := by
    intro v hv; rw [hv, thetaChar_two]; exact (norm_thetaTwo_bounds him).2
  have hθo : ∀ v : Fin 2 → ZMod 2, v ≠ 0 → v ≠ ![0, 1] → ‖thetaChar v ((g • τ : ℍ) : ℂ)‖ ≤ 2 :=
    fun v hv hv2 => norm_thetaChar_le_two hv hv2 him
  have hcase : (‖thetaChar v2 ((g • τ : ℍ) : ℂ)‖ ≤ 3 * Real.exp (-π * y / 4) ∧
        ‖thetaChar v3 ((g • τ : ℍ) : ℂ)‖ ≤ 2 ∧ ‖thetaChar v4 ((g • τ : ℍ) : ℂ)‖ ≤ 2) ∨
      (‖thetaChar v3 ((g • τ : ℍ) : ℂ)‖ ≤ 3 * Real.exp (-π * y / 4) ∧
        ‖thetaChar v2 ((g • τ : ℍ) : ℂ)‖ ≤ 2 ∧ ‖thetaChar v4 ((g • τ : ℍ) : ℂ)‖ ≤ 2) ∨
      (‖thetaChar v4 ((g • τ : ℍ) : ℂ)‖ ≤ 3 * Real.exp (-π * y / 4) ∧
        ‖thetaChar v2 ((g • τ : ℍ) : ℂ)‖ ≤ 2 ∧ ‖thetaChar v3 ((g • τ : ℍ) : ℂ)‖ ≤ 2) := by
    rcases char_triple_cases h2 h3 h4 h23 h24 h34 with ⟨e2, e3, e4⟩ | ⟨e3, e2, e4⟩ | ⟨e4, e2, e3⟩
    · exact Or.inl ⟨hθ2 _ e2, hθo _ h3 e3, hθo _ h4 e4⟩
    · exact Or.inr (Or.inl ⟨hθ2 _ e3, hθo _ h2 e2, hθo _ h4 e4⟩)
    · exact Or.inr (Or.inr ⟨hθ2 _ e4, hθo _ h2 e2, hθo _ h3 e3⟩)
  have hprod := theta_product_le ha0 ha1 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hy0 hcase
  have hκ : 0 < π * min a (1 - 2 * a) / 4 := by
    have : 0 < min a (1 - 2 * a) := lt_min ha0 (by linarith)
    positivity
  have hkey := rpow_quarter_mul_exp_neg_le hκ hy0
  unfold thetaPowerHeckeConstant
  calc y ^ (1 / 4 : ℝ) * (‖thetaChar v2 ((g • τ : ℍ) : ℂ)‖ ^ a *
        ‖thetaChar v4 ((g • τ : ℍ) : ℂ)‖ ^ a * ‖thetaChar v3 ((g • τ : ℍ) : ℂ)‖ ^ (1 - 2 * a))
      ≤ y ^ (1 / 4 : ℝ) * (12 * Real.exp (-(π * min a (1 - 2 * a) / 4 * y))) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hy0 _)
    _ = 12 * (y ^ (1 / 4 : ℝ) * Real.exp (-(π * min a (1 - 2 * a) / 4 * y))) := by ring
    _ ≤ 12 * (π * min a (1 - 2 * a) / 4) ^ (-(1 / 4 : ℝ)) := by gcongr

/-- **Hecke bound**, stated on `ℂ`. -/
theorem norm_thetaPowerForm_le_hecke (ha0 : 0 < a) (ha1 : a < 1 / 2) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖thetaPowerForm a τ‖ ≤ thetaPowerHeckeConstant a * τ.im ^ (-(1 / 4 : ℝ)) := by
  have h := norm_thetaPowerForm_mul_im_le ha0 ha1 ⟨τ, hτ⟩
  have hq : 0 < τ.im ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hτ _
  rw [Real.rpow_neg hτ.le, ← div_eq_mul_inv, le_div_iff₀ hq]
  exact h

/-- The lower-bound constant `(4/5)^{1/4} min(e^{-πK/4}, 1/2)`. -/
def thetaPowerLowerConstant (K : ℝ) : ℝ :=
  (4 / 5 : ℝ) ^ (1 / 4 : ℝ) * min (Real.exp (-π * K / 4)) (1 / 2)

theorem thetaPowerLowerConstant_pos (K : ℝ) : 0 < thetaPowerLowerConstant K := by
  unfold thetaPowerLowerConstant
  have : 0 < min (Real.exp (-π * K / 4)) (1 / 2) := lt_min (Real.exp_pos _) (by norm_num)
  positivity

/-- **Lower bound on the compact part.** If `g` reduces `τ` into the fundamental domain with
`Im gτ ≤ K`, then `|F_a(τ)| (Im τ)^{1/4} ≥ (4/5)^{1/4} min(e^{-πK/4}, 1/2)`, for `0 ≤ a ≤ 1/2`. -/
theorem thetaPowerLowerConstant_le (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (τ : ℍ) (g : SL(2, ℤ))
    (hfd : g • τ ∈ ModularGroup.fd) {K : ℝ} (hK : (g • τ).im ≤ K) :
    thetaPowerLowerConstant K ≤ ‖thetaPowerForm a (τ : ℂ)‖ * τ.im ^ (1 / 4 : ℝ) := by
  have him : (4 : ℝ) / 5 ≤ ((g • τ : ℍ) : ℂ).im := by
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hfd
    have hpos := (g • τ).im_pos
    show (4 : ℝ) / 5 ≤ (g • τ).im
    nlinarith
  obtain ⟨v2, v3, v4, h2, h3, h4, -, -, -, hid⟩ := norm_thetaPowerForm_mul_im_rpow a τ g
  rw [hid]
  set m : ℝ := min (Real.exp (-π * K / 4)) (1 / 2) with hm
  have hm0 : 0 < m := lt_min (Real.exp_pos _) (by norm_num)
  have hlow : ∀ v : Fin 2 → ZMod 2, v ≠ 0 → m ≤ ‖thetaChar v ((g • τ : ℍ) : ℂ)‖ := by
    intro v hv
    by_cases hv2 : v = ![0, 1]
    · rw [hv2, thetaChar_two]
      refine le_trans (min_le_left _ _) (le_trans ?_ (norm_thetaTwo_bounds him).1)
      apply Real.exp_le_exp.mpr
      have : ((g • τ : ℍ) : ℂ).im ≤ K := hK
      nlinarith [Real.pi_pos]
    · exact le_trans (min_le_right _ _) (half_le_norm_thetaChar hv hv2 him)
  have hb : 0 ≤ 1 - 2 * a := by linarith
  have hprod : m ≤ ‖thetaChar v2 ((g • τ : ℍ) : ℂ)‖ ^ a * ‖thetaChar v4 ((g • τ : ℍ) : ℂ)‖ ^ a *
      ‖thetaChar v3 ((g • τ : ℍ) : ℂ)‖ ^ (1 - 2 * a) := by
    have e2 := Real.rpow_le_rpow hm0.le (hlow v2 h2) ha0
    have e4 := Real.rpow_le_rpow hm0.le (hlow v4 h4) ha0
    have e3 := Real.rpow_le_rpow hm0.le (hlow v3 h3) hb
    have hmm : m ^ a * m ^ a * m ^ (1 - 2 * a) = m := by
      rw [← Real.rpow_add hm0, ← Real.rpow_add hm0, show a + a + (1 - 2 * a) = 1 by ring,
        Real.rpow_one]
    calc m = m ^ a * m ^ a * m ^ (1 - 2 * a) := hmm.symm
      _ ≤ _ := by gcongr
  have hy45 : (4 / 5 : ℝ) ^ (1 / 4 : ℝ) ≤ (g • τ).im ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) him (by norm_num)
  unfold thetaPowerLowerConstant
  exact mul_le_mul hy45 hprod hm0.le (Real.rpow_nonneg (g • τ).im_pos.le _)

end

end RHTower
