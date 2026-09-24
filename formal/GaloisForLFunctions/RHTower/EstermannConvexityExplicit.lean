import GaloisForLFunctions.RHTower.EstermannLeftEdgePolynomial
import GaloisForLFunctions.RHTower.EstermannStripPolynomialBound
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The convexity bound, explicit in the modulus

Both edges of the strip `−1 ≤ Re s ≤ 2` are now polynomial with known modulus dependence: `q⁰` on
`Re s = 2` and `q³` on `Re s = −1`.  Normalising by `q^{s−2}`, whose modulus `q^{σ−2}` is `1` on the
right edge and `q^{−3}` on the left, makes **both** edge bounds free of `q`.  Dividing by `(s+2)^5`
turns them into genuine constants, and Phragmén–Lindelöf — whose conclusion uses only the edge
constants, never the admissible-growth constant — propagates them across the strip.  Unwinding gives
the classical convexity exponent

`‖D(1/2 + it, a/q)‖ ≤ C q^{3/2} (1+|t|)³`,  `C` absolute, `|t| ≥ 1`.
-/

open Complex Filter Set Asymptotics

namespace RHTower

noncomputable section

/-! ## A single polynomial left edge, valid at every height -/

/-- The absolute constant of the uniform left edge. -/
def estermannLeftEdgeUniformConstant : ℝ :=
  max (estermannLeftEdgeConstant * Real.exp Real.pi) estermannLeftEdgePolyConstant

theorem estermannLeftEdgeUniformConstant_nonneg : 0 ≤ estermannLeftEdgeUniformConstant :=
  le_max_of_le_right estermannLeftEdgePolyConstant_nonneg

/-- **The uniform polynomial left edge.**  `‖D(−1 + it, a/q)‖ ≤ K q³ (1+|t|)³` for every real `t`. -/
theorem norm_estermannZeta_left_edge_uniform_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (t : ℝ) :
    ‖estermannZeta q ((a : ZMod q)) (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannLeftEdgeUniformConstant * (q : ℝ) ^ (3 : ℕ) * (1 + |t|) ^ (3 : ℕ) := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := by positivity
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  by_cases ht : 1 ≤ |t|
  · have h := norm_estermannZeta_left_edge_poly_le q a ht
    refine h.trans ?_
    have hmono : |t| ^ (3 : ℕ) ≤ (1 + |t|) ^ (3 : ℕ) := pow_le_pow_left₀ habs (by linarith) 3
    have hC : estermannLeftEdgePolyConstant ≤ estermannLeftEdgeUniformConstant := le_max_right _ _
    have hCnn : 0 ≤ estermannLeftEdgePolyConstant := estermannLeftEdgePolyConstant_nonneg
    have hbase : (0 : ℝ) ≤ estermannLeftEdgePolyConstant * (q : ℝ) ^ (3 : ℕ) := mul_nonneg hCnn hq0
    have hpownn : (0 : ℝ) ≤ (1 + |t|) ^ (3 : ℕ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hmono hbase
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hq0) hpownn
    linarith [h1, h2]
  · have htlt : |t| < 1 := not_le.mp ht
    have h := norm_estermannZeta_left_edge_le q a t
    refine h.trans ?_
    have hexp : Real.exp (Real.pi * |t|) ≤ Real.exp Real.pi := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.pi_pos, habs, htlt]
    have hone : (1 : ℝ) ≤ (1 + |t|) ^ (3 : ℕ) := one_le_pow₀ (by linarith)
    have hCnn : 0 ≤ estermannLeftEdgeConstant := estermannLeftEdgeConstant_nonneg
    have hC : estermannLeftEdgeConstant * Real.exp Real.pi ≤ estermannLeftEdgeUniformConstant :=
      le_max_left _ _
    have hbase : (0 : ℝ) ≤ estermannLeftEdgeConstant * (q : ℝ) ^ (3 : ℕ) := mul_nonneg hCnn hq0
    have hstep : estermannLeftEdgeConstant * (q : ℝ) ^ (3 : ℕ) * Real.exp (Real.pi * |t|)
        ≤ estermannLeftEdgeConstant * Real.exp Real.pi * (q : ℝ) ^ (3 : ℕ) := by
      have h1 := mul_le_mul_of_nonneg_left hexp hbase
      linarith [h1]
    refine hstep.trans ?_
    have h1 := mul_le_mul_of_nonneg_right hC hq0
    have h2 := mul_le_mul_of_nonneg_left hone
      (mul_nonneg estermannLeftEdgeUniformConstant_nonneg hq0)
    linarith [h1, h2]

/-! ## The modulus normalisation -/

/-- `q^{s−2}` written as an exponential, manifestly entire. -/
def modulusNormalizer (q : ℕ) (s : ℂ) : ℂ := Complex.exp ((s - 2) * Complex.log (q : ℂ))

theorem differentiable_modulusNormalizer (q : ℕ) : Differentiable ℂ (modulusNormalizer q) := by
  unfold modulusNormalizer
  fun_prop

theorem norm_modulusNormalizer (q : ℕ) [NeZero q] (s : ℂ) :
    ‖modulusNormalizer q s‖ = (q : ℝ) ^ (s.re - 2) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hlog : Complex.log (q : ℂ) = ((Real.log (q : ℝ) : ℝ) : ℂ) := by
    have hcast : ((q : ℕ) : ℂ) = (((q : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_log hq0.le]
  rw [modulusNormalizer, Complex.norm_exp, hlog]
  rw [Real.rpow_def_of_pos hq0]
  congr 1
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem modulusNormalizer_ne_zero (q : ℕ) (s : ℂ) : modulusNormalizer q s ≠ 0 :=
  Complex.exp_ne_zero _

/-! ## The strip bound for the normalised test function -/

/-- The `q`-free edge constant. -/
def estermannStripConstant : ℝ :=
  max (32 * divisorSquareMass) (128 * estermannLeftEdgeUniformConstant)

theorem estermannStripConstant_nonneg : 0 ≤ estermannStripConstant := by
  refine le_max_of_le_left ?_
  have := divisorSquareMass_nonneg
  positivity

/-- The normalised, shifted test function of the convexity argument. -/
def estermannPLTest (q : ℕ) [NeZero q] (a : ZMod q) (s : ℂ) : ℂ :=
  modulusNormalizer q s * estermannEntire q a s / (s + 2) ^ (5 : ℕ)

theorem differentiableAt_estermannPLTest (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {z : ℂ}
    (hz : -(3 : ℝ) / 2 < z.re) :
    DifferentiableAt ℂ (estermannPLTest q ((a : ZMod q))) z := by
  unfold estermannPLTest
  refine DifferentiableAt.div ?_ (((differentiable_id.add_const (2 : ℂ)).pow 5) z) ?_
  · exact (differentiable_modulusNormalizer q z).mul (differentiable_estermannEntire a z)
  · exact pow_ne_zero _ (shift_ne_zero hz)

/-- On the strip the normaliser has modulus at most one. -/
theorem norm_modulusNormalizer_le_one (q : ℕ) [NeZero q] {z : ℂ} (h1 : z.re ≤ 2) :
    ‖modulusNormalizer q z‖ ≤ 1 := by
  rw [norm_modulusNormalizer]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  exact Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)

/-- **The `q`-free edge bound.**  Both edges of the strip give the same constant. -/
theorem norm_estermannPLTest_edge (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {z : ℂ}
    (hz : z.re = -1 ∨ z.re = 2) :
    ‖estermannPLTest q ((a : ZMod q)) z‖ ≤ estermannStripConstant := by
  have hre1 : -1 ≤ z.re := by rcases hz with h | h <;> linarith [h.le, h.ge]
  have hshift : (0 : ℝ) < ‖z + 2‖ := norm_pos_iff.mpr (shift_ne_zero (by linarith))
  have hcmp : 1 + |z.im| ≤ 2 * ‖z + 2‖ := one_add_abs_im_le_two_mul_norm hre1
  have hb0 : (0 : ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
  have hpow : (1 + |z.im|) ^ (5 : ℕ) ≤ (2 * ‖z + 2‖) ^ (5 : ℕ) :=
    pow_le_pow_left₀ hb0 hcmp 5
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hne : z ≠ 1 := by
    intro hcon
    rcases hz with h | h <;> rw [hcon] at h <;> norm_num at h
  have hfz : ‖estermannEntire q ((a : ZMod q)) z‖
      = ‖z - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) z‖ := by
    rw [estermannEntire_eq _ hne, norm_mul, norm_pow]
  -- a uniform shape for the whole product
  have hkey : ‖modulusNormalizer q z‖ * ‖estermannEntire q ((a : ZMod q)) z‖
      ≤ (estermannStripConstant / 32) * (1 + |z.im|) ^ (5 : ℕ) := by
    rcases hz with hzl | hzr
    · -- left edge
      have hzz : z = ((-1 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
        conv_lhs => rw [← Complex.re_add_im z]
        rw [hzl]
      have hD := norm_estermannZeta_left_edge_uniform_le q a z.im
      rw [← hzz] at hD
      have hnorm : ‖modulusNormalizer q z‖ = (q : ℝ) ^ (-(3 : ℝ)) := by
        rw [norm_modulusNormalizer, hzl]
        norm_num
      have hsm : ‖z - 1‖ ≤ 2 * (1 + |z.im|) := by
        have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
        have hre : (z - 1).re = z.re - 1 := by simp
        have him : (z - 1).im = z.im := by simp
        rw [hre, him, hzl] at h
        have : |(-1 : ℝ) - 1| = 2 := by norm_num
        rw [this] at h
        linarith [abs_nonneg z.im]
      have hsmsq : ‖z - 1‖ ^ (2 : ℕ) ≤ 4 * (1 + |z.im|) ^ (2 : ℕ) := by
        have := pow_le_pow_left₀ (norm_nonneg (z - 1)) hsm 2
        calc ‖z - 1‖ ^ (2 : ℕ) ≤ (2 * (1 + |z.im|)) ^ (2 : ℕ) := this
          _ = 4 * (1 + |z.im|) ^ (2 : ℕ) := by ring
      have hcancel : (q : ℝ) ^ (-(3 : ℝ)) * (q : ℝ) ^ (3 : ℕ) = 1 := by
        rw [← Real.rpow_natCast (q : ℝ) 3, ← Real.rpow_add hq0]
        norm_num
      have hKnn : 0 ≤ estermannLeftEdgeUniformConstant := estermannLeftEdgeUniformConstant_nonneg
      have hq3 : (0 : ℝ) ≤ (q : ℝ) ^ (3 : ℕ) := by positivity
      have hzn : (0 : ℝ) ≤ ‖estermannZeta q ((a : ZMod q)) z‖ := norm_nonneg _
      have hpw : (0 : ℝ) ≤ (1 + |z.im|) ^ (2 : ℕ) := by positivity
      have hpw3 : (0 : ℝ) ≤ (1 + |z.im|) ^ (3 : ℕ) := by positivity
      have hCle : 128 * estermannLeftEdgeUniformConstant ≤ estermannStripConstant :=
        le_max_right _ _
      rw [hnorm, hfz]
      have hstep1 : ‖z - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) z‖
          ≤ (4 * (1 + |z.im|) ^ (2 : ℕ)) *
              (estermannLeftEdgeUniformConstant * (q : ℝ) ^ (3 : ℕ) * (1 + |z.im|) ^ (3 : ℕ)) :=
        mul_le_mul hsmsq hD hzn (by positivity)
      have hshape : (4 * (1 + |z.im|) ^ (2 : ℕ)) *
          (estermannLeftEdgeUniformConstant * (q : ℝ) ^ (3 : ℕ) * (1 + |z.im|) ^ (3 : ℕ))
          = (4 * estermannLeftEdgeUniformConstant) * (q : ℝ) ^ (3 : ℕ) *
              (1 + |z.im|) ^ (5 : ℕ) := by ring
      have hmul := mul_le_mul_of_nonneg_left hstep1
        (le_of_lt (Real.rpow_pos_of_pos hq0 (-(3 : ℝ))))
      rw [hshape] at hmul
      have hfinal : (q : ℝ) ^ (-(3 : ℝ)) *
          ((4 * estermannLeftEdgeUniformConstant) * (q : ℝ) ^ (3 : ℕ) * (1 + |z.im|) ^ (5 : ℕ))
          = (4 * estermannLeftEdgeUniformConstant) * (1 + |z.im|) ^ (5 : ℕ) := by
        calc (q : ℝ) ^ (-(3 : ℝ)) *
              ((4 * estermannLeftEdgeUniformConstant) * (q : ℝ) ^ (3 : ℕ) *
                (1 + |z.im|) ^ (5 : ℕ))
            = (4 * estermannLeftEdgeUniformConstant) *
                ((q : ℝ) ^ (-(3 : ℝ)) * (q : ℝ) ^ (3 : ℕ)) * (1 + |z.im|) ^ (5 : ℕ) := by ring
          _ = (4 * estermannLeftEdgeUniformConstant) * (1 + |z.im|) ^ (5 : ℕ) := by
              rw [hcancel]; ring
      rw [hfinal] at hmul
      have hpw5 : (0 : ℝ) ≤ (1 + |z.im|) ^ (5 : ℕ) := by positivity
      have hconst : 4 * estermannLeftEdgeUniformConstant ≤ estermannStripConstant / 32 := by
        linarith [hCle]
      have := mul_le_mul_of_nonneg_right hconst hpw5
      linarith [hmul, this]
    · -- right edge
      have hzz : z = ((2 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I := by
        conv_lhs => rw [← Complex.re_add_im z]
        rw [hzr]
      have hD : ‖estermannZeta q ((a : ZMod q)) z‖ ≤ divisorSquareMass :=
        norm_estermannZeta_le_divisorSquareMass q _ (by rw [hzr])
      have hnorm : ‖modulusNormalizer q z‖ = 1 := by
        rw [norm_modulusNormalizer, hzr]
        norm_num
      have hsm : ‖z - 1‖ ≤ 1 + |z.im| := by
        have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
        have hre : (z - 1).re = z.re - 1 := by simp
        have him : (z - 1).im = z.im := by simp
        rw [hre, him, hzr] at h
        have : |(2 : ℝ) - 1| = 1 := by norm_num
        rw [this] at h
        linarith
      have hsmsq : ‖z - 1‖ ^ (2 : ℕ) ≤ (1 + |z.im|) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) hsm 2
      have hCle : 32 * divisorSquareMass ≤ estermannStripConstant := le_max_left _ _
      rw [hnorm, hfz, one_mul]
      have hstep1 : ‖z - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) z‖
          ≤ (1 + |z.im|) ^ (2 : ℕ) * divisorSquareMass :=
        mul_le_mul hsmsq hD (norm_nonneg _) (by positivity)
      have hgrow : (1 + |z.im|) ^ (2 : ℕ) ≤ (1 + |z.im|) ^ (5 : ℕ) :=
        pow_le_pow_right₀ (by linarith [abs_nonneg z.im]) (by omega)
      have hDnn : 0 ≤ divisorSquareMass := divisorSquareMass_nonneg
      have h2 := mul_le_mul_of_nonneg_right hgrow hDnn
      have hconst : divisorSquareMass ≤ estermannStripConstant / 32 := by linarith [hCle]
      have hpw5 : (0 : ℝ) ≤ (1 + |z.im|) ^ (5 : ℕ) := by positivity
      have h3 := mul_le_mul_of_nonneg_left hconst hpw5
      linarith [hstep1, h2, h3]
  rw [estermannPLTest]
  simp only [norm_div, norm_pow, norm_mul]
  rw [div_le_iff₀ (by positivity)]
  calc ‖modulusNormalizer q z‖ * ‖estermannEntire q ((a : ZMod q)) z‖
      ≤ (estermannStripConstant / 32) * (1 + |z.im|) ^ (5 : ℕ) := hkey
    _ ≤ (estermannStripConstant / 32) * (2 * ‖z + 2‖) ^ (5 : ℕ) := by
        refine mul_le_mul_of_nonneg_left hpow ?_
        linarith [estermannStripConstant_nonneg]
    _ = estermannStripConstant * ‖z + 2‖ ^ (5 : ℕ) := by rw [mul_pow]; ring

/-! ## Phragmén–Lindelöf across the strip -/

/-- **The `q`-free strip bound.**  The edge constant propagates across the whole strip. -/
theorem norm_estermannPLTest_strip (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {s : ℂ}
    (h0 : -1 ≤ s.re) (h1 : s.re ≤ 2) :
    ‖estermannPLTest q ((a : ZMod q)) s‖ ≤ estermannStripConstant := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_bound_norm_estermannZeta_strip_exp q ((a : ZMod q)) (-1) 2 (by norm_num)
  refine PhragmenLindelof.vertical_strip (f := estermannPLTest q ((a : ZMod q)))
    (a := (-1 : ℝ)) (b := (2 : ℝ)) (C := estermannStripConstant)
    ⟨?_, ?_⟩ ?_ (fun z hz => norm_estermannPLTest_edge q a (Or.inl hz))
    (fun z hz => norm_estermannPLTest_edge q a (Or.inr hz)) h0 h1
  · intro z hz
    have : (-1 : ℝ) < z.re := hz.1
    exact (differentiableAt_estermannPLTest q a (by linarith)).differentiableWithinAt
  · have hsub : closure (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ⊆ Complex.re ⁻¹' Icc (-1 : ℝ) 2 := by
      refine closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) ?_
      exact IsClosed.preimage Complex.continuous_re isClosed_Icc
    refine fun z hz => ((differentiableAt_estermannPLTest q a ?_).continuousAt.continuousWithinAt)
    have := (hsub hz).1
    linarith
  · refine ⟨1 / 2, ?_, 2 * (Real.pi + 2), ?_⟩
    · rw [show (2 : ℝ) - (-1) = 3 by norm_num]
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith [Real.pi_gt_three]
    · refine Asymptotics.isBigO_iff.mpr ⟨9 * K, ?_⟩
      have hmem : {z : ℂ | 2 ≤ |z.im|} ∈
          comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) := by
        refine Filter.mem_inf_of_left ?_
        exact Filter.mem_comap.mpr ⟨Ici (2 : ℝ), Ici_mem_atTop 2, fun z hz => hz⟩
      have hmemU : (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ∈
          comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) :=
        Filter.mem_inf_of_right (Filter.mem_principal_self _)
      filter_upwards [hmem, hmemU] with z hz hzU
      have hz2 : (2 : ℝ) ≤ |z.im| := hz
      have hzre : z.re ∈ Ioo (-1 : ℝ) 2 := hzU
      have hne : z ≠ 1 := by
        intro hcon
        rw [hcon] at hz2
        norm_num at hz2
      have hD : ‖estermannZeta q ((a : ZMod q)) z‖ ≤ K * Real.exp (Real.pi * |z.im|) :=
        hK z hzre.1.le hzre.2.le hz2
      have hsm : ‖z - 1‖ ≤ 3 + |z.im| := by
        have h := Complex.norm_le_abs_re_add_abs_im (z - 1)
        have hre : (z - 1).re = z.re - 1 := by simp
        have him : (z - 1).im = z.im := by simp
        rw [hre, him] at h
        have hb : |z.re - 1| ≤ 3 := by
          rw [abs_le]; constructor <;> linarith [hzre.1, hzre.2]
        linarith
      have hfz : ‖estermannEntire q ((a : ZMod q)) z‖
          ≤ (3 + |z.im|) ^ (2 : ℕ) * (K * Real.exp (Real.pi * |z.im|)) := by
        rw [estermannEntire_eq _ hne, norm_mul, norm_pow]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsm 2) hD (norm_nonneg _)
          (by positivity)
      have hone' : (1 : ℝ) ≤ ‖z + 2‖ := by
        have := one_add_abs_im_le_two_mul_norm (z := z) (by linarith [hzre.1])
        linarith [abs_nonneg z.im]
      have hgz : ‖estermannPLTest q ((a : ZMod q)) z‖
          ≤ ‖estermannEntire q ((a : ZMod q)) z‖ := by
        rw [estermannPLTest]
        simp only [norm_div, norm_pow, norm_mul]
        have hstep : ‖modulusNormalizer q z‖ * ‖estermannEntire q ((a : ZMod q)) z‖
            ≤ ‖estermannEntire q ((a : ZMod q)) z‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (norm_modulusNormalizer_le_one q hzre.2.le)
        refine le_trans (div_le_self (by positivity) (one_le_pow₀ hone')) hstep
      set u : ℝ := |z.im| with hu
      have hu0 : (0 : ℝ) ≤ u := abs_nonneg _
      have hexp1 : (3 : ℝ) + u ≤ 3 * Real.exp u := by
        have := Real.add_one_le_exp u
        linarith
      have hsq : (3 + u) ^ (2 : ℕ) ≤ 9 * Real.exp (2 * u) := by
        have h3 : (0 : ℝ) ≤ 3 + u := by linarith
        calc (3 + u) ^ (2 : ℕ) ≤ (3 * Real.exp u) ^ (2 : ℕ) := pow_le_pow_left₀ h3 hexp1 2
          _ = 9 * (Real.exp u * Real.exp u) := by ring
          _ = 9 * Real.exp (2 * u) := by rw [← Real.exp_add]; congr 2; ring
      have hfin : ‖estermannEntire q ((a : ZMod q)) z‖
          ≤ 9 * K * Real.exp ((Real.pi + 2) * u) := by
        refine hfz.trans ?_
        calc (3 + u) ^ (2 : ℕ) * (K * Real.exp (Real.pi * u))
            ≤ (9 * Real.exp (2 * u)) * (K * Real.exp (Real.pi * u)) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = 9 * K * (Real.exp (2 * u) * Real.exp (Real.pi * u)) := by ring
          _ = 9 * K * Real.exp ((Real.pi + 2) * u) := by rw [← Real.exp_add]; congr 2; ring
      have hdom : Real.exp ((Real.pi + 2) * u)
          ≤ Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * u)) := by
        refine Real.exp_le_exp.mpr ?_
        have hhalf : (1 / 2 : ℝ) * u ≤ Real.exp (1 / 2 * u) := by
          have := Real.add_one_le_exp ((1 / 2 : ℝ) * u)
          linarith
        nlinarith [Real.pi_pos, hhalf]
      have hnormg : ‖Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * |z.im|))‖
          = Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * |z.im|)) :=
        Real.norm_of_nonneg (Real.exp_pos _).le
      rw [hnormg]
      calc ‖estermannPLTest q ((a : ZMod q)) z‖ ≤ ‖estermannEntire q ((a : ZMod q)) z‖ := hgz
        _ ≤ 9 * K * Real.exp ((Real.pi + 2) * u) := hfin
        _ ≤ 9 * K * Real.exp (2 * (Real.pi + 2) * Real.exp (1 / 2 * u)) :=
            mul_le_mul_of_nonneg_left hdom (by positivity)

/-! ## The convexity bound on the critical line -/

/-- The absolute constant of the convexity bound. -/
def estermannCriticalLineConstant : ℝ := 8192 * estermannStripConstant

/-- **The convexity bound, explicit in the modulus.**
`‖D(1/2 + it, a/q)‖ ≤ C q^{3/2} (1+|t|)³` for every real `t`, with `C` absolute. -/
theorem norm_estermannZeta_critical_line_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (t : ℝ) :
    ‖estermannZeta q ((a : ZMod q)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ estermannCriticalLineConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ (3 : ℕ) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hsdef
  have hsre : s.re = 1 / 2 := by rw [hsdef]; simp
  have hsim : s.im = t := by rw [hsdef]; simp
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hne : s ≠ 1 := by
    intro hcon
    have := congrArg Complex.re hcon
    rw [hsre] at this
    norm_num at this
  have hPL := norm_estermannPLTest_strip q a (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  have hshift : (0 : ℝ) < ‖s + 2‖ := norm_pos_iff.mpr (shift_ne_zero (by rw [hsre]; norm_num))
  have hnorm : ‖modulusNormalizer q s‖ = (q : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [norm_modulusNormalizer, hsre]
    norm_num
  have hexpand : ‖estermannPLTest q ((a : ZMod q)) s‖
      = (q : ℝ) ^ (-(3 : ℝ) / 2) * (‖s - 1‖ ^ (2 : ℕ) *
          ‖estermannZeta q ((a : ZMod q)) s‖) / ‖s + 2‖ ^ (5 : ℕ) := by
    rw [estermannPLTest]
    simp only [norm_div, norm_pow, norm_mul]
    rw [hnorm, estermannEntire_eq _ hne, norm_mul, norm_pow]
  rw [hexpand, div_le_iff₀ (by positivity)] at hPL
  -- geometry of the two shifts
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hsm : |t| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have him : (s - 1).im = t := by rw [hsdef]; simp
    rw [him] at h
    exact h
  have hbig : ‖s + 2‖ ≤ 4 * (1 + |t|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre : (s + 2).re = s.re + 2 := by simp
    have him : (s + 2).im = s.im := by simp
    rw [hre, him, hsre, hsim] at h
    have habs2 : |(1 / 2 : ℝ) + 2| = 5 / 2 := by
      rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2 + 2)]
      norm_num
    rw [habs2] at h
    linarith
  have hsmexact : ‖s - 1‖ ^ (2 : ℕ) = 1 / 4 + t ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (s - 1).re = -(1 / 2) := by rw [hsdef]; simp; ring
    have him : (s - 1).im = t := by rw [hsdef]; simp
    rw [hre, him]
    ring
  have hsmsq : (1 + |t|) ^ (2 : ℕ) ≤ 8 * ‖s - 1‖ ^ (2 : ℕ) := by
    rw [hsmexact]
    have habs2 : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := sq_abs t
    nlinarith [sq_nonneg (|t| - 1), habs, habs2]
  have hbigpow : ‖s + 2‖ ^ (5 : ℕ) ≤ 1024 * (1 + |t|) ^ (5 : ℕ) := by
    have h := pow_le_pow_left₀ (norm_nonneg (s + 2)) hbig 5
    calc ‖s + 2‖ ^ (5 : ℕ) ≤ (4 * (1 + |t|)) ^ (5 : ℕ) := h
      _ = 1024 * (1 + |t|) ^ (5 : ℕ) := by ring
  -- unwind
  have hsmpos : (0 : ℝ) < ‖s - 1‖ ^ (2 : ℕ) := by
    rw [hsmexact]
    positivity
  have hrpowpos : (0 : ℝ) < (q : ℝ) ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
  have hDnn : (0 : ℝ) ≤ ‖estermannZeta q ((a : ZMod q)) s‖ := norm_nonneg _
  have hcancel : (q : ℝ) ^ ((3 : ℝ) / 2) * (q : ℝ) ^ (-(3 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hq0]
    norm_num
  have hstep : (q : ℝ) ^ (-(3 : ℝ) / 2) *
      (‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖)
      ≤ estermannStripConstant * (1024 * (1 + |t|) ^ (5 : ℕ)) := by
    refine hPL.trans ?_
    exact mul_le_mul_of_nonneg_left hbigpow estermannStripConstant_nonneg
  -- multiply by `q^{3/2}` and divide by `‖s-1‖²`
  have hmul := mul_le_mul_of_nonneg_left hstep
    (le_of_lt (Real.rpow_pos_of_pos hq0 ((3 : ℝ) / 2)))
  have hleft : (q : ℝ) ^ ((3 : ℝ) / 2) * ((q : ℝ) ^ (-(3 : ℝ) / 2) *
      (‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖))
      = ‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖ := by
    calc (q : ℝ) ^ ((3 : ℝ) / 2) * ((q : ℝ) ^ (-(3 : ℝ) / 2) *
          (‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖))
        = ((q : ℝ) ^ ((3 : ℝ) / 2) * (q : ℝ) ^ (-(3 : ℝ) / 2)) *
            (‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖) := by ring
      _ = ‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖ := by rw [hcancel]; ring
  rw [hleft] at hmul
  -- now divide by `(1+|t|)²`, using `(1+|t|)² ≤ 4‖s-1‖²`
  have hpos2 : (0 : ℝ) < (1 + |t|) ^ (2 : ℕ) := by positivity
  have hRHS : (8 : ℝ) * ((q : ℝ) ^ ((3 : ℝ) / 2) *
      (estermannStripConstant * (1024 * (1 + |t|) ^ (5 : ℕ))))
      = estermannCriticalLineConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ (3 : ℕ) *
        (1 + |t|) ^ (2 : ℕ) := by
    rw [estermannCriticalLineConstant]
    ring
  refine le_of_mul_le_mul_right ?_ hpos2
  calc ‖estermannZeta q ((a : ZMod q)) s‖ * (1 + |t|) ^ (2 : ℕ)
      ≤ ‖estermannZeta q ((a : ZMod q)) s‖ * (8 * ‖s - 1‖ ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hsmsq hDnn
    _ = 8 * (‖s - 1‖ ^ (2 : ℕ) * ‖estermannZeta q ((a : ZMod q)) s‖) := by ring
    _ ≤ 8 * ((q : ℝ) ^ ((3 : ℝ) / 2) *
          (estermannStripConstant * (1024 * (1 + |t|) ^ (5 : ℕ)))) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ = estermannCriticalLineConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * (1 + |t|) ^ (3 : ℕ) *
          (1 + |t|) ^ (2 : ℕ) := hRHS

end

end RHTower
