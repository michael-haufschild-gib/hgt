import GaloisForLFunctions.RHTower.PoleVanishingWeilPrimeTwoEntry
import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityHalfLogTwo

/-!
# Explicit Weil positivity past the entry of the prime 2

Let `b = ½ (log 2 + 1/50)`, so `e^{b} = √2 · e^{1/100} ≈ 1.4284`.  The pole-vanishing restricted
Weil form at the aperture `b` contains the prime `2` (translation by `log 2 < 2b`), and its
pole-vanishing ground energy is at least `1/20`.  By monotonicity in the aperture, the
restricted Weil form, prime `2` included, is positive definite on pole-vanishing test functions
supported in `[λ^{-1}, λ]` for every `λ ≤ √2 · e^{1/100}`.

The proof evaluates the trace certificate for the symbol
`W(ξ) - √2 log 2 (cos(2π log 2 · ξ) - cos(2π · 2b · ξ))` on eighteen shells of width `1/10`,
with the optimal plane-wave residual `2b - C²/(b + sinh b) - S²/(sinh b - b)`.  On the shells
inside `[1/(2 log 2 + 1/50), 2/(2 log 2 + 1/50)]` the prime term is nonpositive; elsewhere it is at
most `0.12319 |ξ|`, and at most `1.9606` everywhere.
-/

open MeasureTheory Complex Set
open scoped FourierTransform InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The optimal residual -/

/-- The residual at the optimal parameters `p = C/(a + sinh a)`, `q = S/(sinh a - a)`. -/
def poleResidualOptimal (a ω : ℝ) : ℝ :=
  2 * a - poleCosCoshIntegral a ω ^ 2 / (a + Real.sinh a) -
    poleSinSinhIntegral a ω ^ 2 / (Real.sinh a - a)

theorem poleResidualClosedForm_optimal {a ω : ℝ} (h1 : a + Real.sinh a ≠ 0)
    (h2 : Real.sinh a - a ≠ 0) :
    poleResidualClosedForm a ω (poleCosCoshIntegral a ω / (a + Real.sinh a))
        (poleSinSinhIntegral a ω / (Real.sinh a - a)) = poleResidualOptimal a ω := by
  unfold poleResidualClosedForm poleResidualOptimal
  field_simp
  ring

theorem poleResidualOptimal_neg (a ω : ℝ) :
    poleResidualOptimal a (-ω) = poleResidualOptimal a ω := by
  have hC : poleCosCoshIntegral a (-ω) = poleCosCoshIntegral a ω := by
    unfold poleCosCoshIntegral
    simp only [neg_mul, Real.cos_neg, Real.sin_neg, neg_sq]
    ring
  have hS : poleSinSinhIntegral a (-ω) = -poleSinSinhIntegral a ω := by
    unfold poleSinSinhIntegral
    simp only [neg_mul, Real.cos_neg, Real.sin_neg, neg_sq]
    ring
  unfold poleResidualOptimal
  rw [hC, hS, neg_sq]

/-- The constrained Fourier bound with the optimal residual at a reference frequency. -/
theorem norm_fourier_sq_le_of_polar_optimal (a : SuzukiPositiveAperture)
    (h1 : a.1 + Real.sinh a.1 ≠ 0) (h2 : Real.sinh a.1 - a.1 ≠ 0)
    (f : suzukiApertureHilbert a)
    (hplus : inner ℂ (ccmPolarL2Vector a (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector a (-1 / 2)) f.1 = 0) (ξ m η : ℝ) (hη : 0 < η) :
    ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤
      ((1 + η) * poleResidualOptimal a.1 (2 * Real.pi * m) +
        (1 + 1 / η) * (4 * Real.pi ^ 2 * (ξ - m) ^ 2 * (2 * a.1 ^ 3 / 3))) * ‖f‖ ^ 2 := by
  have := norm_fourier_sq_le_of_polar a f hplus hminus ξ m
    (poleCosCoshIntegral a.1 (2 * Real.pi * m) / (a.1 + Real.sinh a.1))
    (poleSinSinhIntegral a.1 (2 * Real.pi * m) / (Real.sinh a.1 - a.1)) η hη
  rwa [poleResidualClosedForm_optimal h1 h2] at this

/-! ## The aperture and its constants -/

/-- The aperture `½ (log 2 + 1/50)`. -/
def primeTwoAperture : SuzukiPositiveAperture :=
  ⟨(Real.log 2 + 1 / 50) / 2, by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity⟩

theorem primeTwoAperture_log_two_le : Real.log 2 ≤ 2 * primeTwoAperture.1 := by
  change Real.log 2 ≤ 2 * ((Real.log 2 + 1 / 50) / 2)
  linarith

theorem primeTwoAperture_lt_log_three : 2 * primeTwoAperture.1 < Real.log 3 := by
  change 2 * ((Real.log 2 + 1 / 50) / 2) < Real.log 3
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have := Real.log_two_lt_d9
  linarith

theorem exp_one_two_hundredth_bounds :
    (1.0050125 : ℝ) ≤ Real.exp (1 / 200) ∧ Real.exp (1 / 200) ≤ 1.005012626 := by
  constructor
  · have := Real.quadratic_le_exp_of_nonneg (x := (1 / 200 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  · have := Real.exp_bound' (x := (1 / 200 : ℝ)) (by norm_num) (by norm_num) (n := 3)
      (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢
    linarith

/-- `e^{b/2}` in terms of `2^{1/4}` and `e^{1/200}`. -/
theorem exp_primeTwo_quarter :
    Real.exp ((Real.log 2 + 1 / 50) / 4) = Real.exp (Real.log 2 / 4) * Real.exp (1 / 200) := by
  rw [← Real.exp_add]
  congr 1
  ring

def primeTwoQuarterEncl : Encl :=
  Encl.ofBounds (1.1892071150 * 1.0050125) (1.1892071151 * 1.005012626)

theorem holds_primeTwoQuarterEncl :
    Encl.Holds (Real.exp ((Real.log 2 + 1 / 50) / 4)) primeTwoQuarterEncl := by
  rw [exp_primeTwo_quarter]
  have h1 := quarter_root_two_bounds
  have h2 := exp_one_two_hundredth_bounds
  apply Encl.holds_ofBounds
  · exact mul_le_mul h1.1 h2.1 (by norm_num) (Real.exp_pos _).le
  · exact mul_le_mul h1.2 h2.2 (Real.exp_pos _).le (by norm_num)

def primeTwoApertureEncl : Encl := Encl.ofBounds (0.6931471803 + 1 / 50) (0.6931471808 + 1 / 50)

theorem holds_primeTwoApertureEncl : Encl.Holds (Real.log 2 + 1 / 50) primeTwoApertureEncl :=
  Encl.holds_ofBounds (by linarith [Real.log_two_gt_d9]) (by linarith [Real.log_two_lt_d9])

/-! ## The optimal residual as an expression tree -/

/-- The optimal residual in the variables `S = 2a`, `x = e^{a/2}`, `sin θ`, `cos θ`, `θ = ωa`. -/
def optimalResidualExpr (S x s c θ : ℝ) : ℝ :=
  2 * ((1 / 2) * S) -
    (4 * (((c * ((1 / 2) * (x - x⁻¹))) + (2 * (2 * θ * S⁻¹)) * (s * ((1 / 2) * (x + x⁻¹)))) *
      (1 + 4 * ((2 * θ * S⁻¹) * (2 * θ * S⁻¹)))⁻¹)) *
      (4 * (((c * ((1 / 2) * (x - x⁻¹))) + (2 * (2 * θ * S⁻¹)) * (s * ((1 / 2) * (x + x⁻¹)))) *
      (1 + 4 * ((2 * θ * S⁻¹) * (2 * θ * S⁻¹)))⁻¹)) *
      ((1 / 2) * S + (1 / 2) * (x * x - (x * x)⁻¹))⁻¹ -
    (4 * (((s * ((1 / 2) * (x + x⁻¹))) - (2 * (2 * θ * S⁻¹)) * (c * ((1 / 2) * (x - x⁻¹)))) *
      (1 + 4 * ((2 * θ * S⁻¹) * (2 * θ * S⁻¹)))⁻¹)) *
      (4 * (((s * ((1 / 2) * (x + x⁻¹))) - (2 * (2 * θ * S⁻¹)) * (c * ((1 / 2) * (x - x⁻¹)))) *
      (1 + 4 * ((2 * θ * S⁻¹) * (2 * θ * S⁻¹)))⁻¹)) *
      ((1 / 2) * (x * x - (x * x)⁻¹) - (1 / 2) * S)⁻¹

theorem poleResidualOptimal_eq_expr {S θ : ℝ} (hS : 0 < S) :
    poleResidualOptimal (S / 2) (2 * Real.pi * (θ / (Real.pi * S))) =
      optimalResidualExpr S (Real.exp (S / 4)) (Real.sin θ) (Real.cos θ) θ := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hθ : 2 * Real.pi * (θ / (Real.pi * S)) * (S / 2) = θ := by
    field_simp
  have hω : 2 * Real.pi * (θ / (Real.pi * S)) = 2 * θ * S⁻¹ := by
    field_simp
  have hsh : Real.sinh (S / 2) = (1 / 2) * (Real.exp (S / 4) * Real.exp (S / 4) -
      (Real.exp (S / 4) * Real.exp (S / 4))⁻¹) := by
    rw [Real.sinh_eq, ← Real.exp_add, show S / 4 + S / 4 = S / 2 by ring, Real.exp_neg]
    ring
  have hsh2 : Real.sinh (S / 2 / 2) = (1 / 2) * (Real.exp (S / 4) - (Real.exp (S / 4))⁻¹) := by
    rw [show S / 2 / 2 = S / 4 by ring, Real.sinh_eq, Real.exp_neg]
    ring
  have hch2 : Real.cosh (S / 2 / 2) = (1 / 2) * (Real.exp (S / 4) + (Real.exp (S / 4))⁻¹) := by
    rw [show S / 2 / 2 = S / 4 by ring, Real.cosh_eq, Real.exp_neg]
    ring
  unfold poleResidualOptimal poleCosCoshIntegral poleSinSinhIntegral optimalResidualExpr
  rw [hθ, hsh, hsh2, hch2, hω]
  have ha : S / 2 = (1 / 2) * S := by ring
  rw [ha]
  simp only [div_eq_mul_inv]
  ring

/-- The enclosure tree of `optimalResidualExpr`. -/
def optimalResidualEncl (eS ex es ec : Encl) (θ : ℝ) : Encl :=
  let eω := Encl.smul (2 * θ) (Encl.inv eS)
  let es2 := Encl.smul (1 / 2) (Encl.sub ex (Encl.inv ex))
  let ec2 := Encl.smul (1 / 2) (Encl.add ex (Encl.inv ex))
  let exx := Encl.mul ex ex
  let esh := Encl.smul (1 / 2) (Encl.sub exx (Encl.inv exx))
  let ea := Encl.smul (1 / 2) eS
  let eD := Encl.inv (Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul eω eω)))
  let eC := Encl.smul 4 (Encl.mul (Encl.add (Encl.mul ec es2)
    (Encl.mul (Encl.smul 2 eω) (Encl.mul es ec2))) eD)
  let eSv := Encl.smul 4 (Encl.mul (Encl.sub (Encl.mul es ec2)
    (Encl.mul (Encl.smul 2 eω) (Encl.mul ec es2))) eD)
  Encl.sub (Encl.sub (Encl.smul 2 ea) (Encl.mul (Encl.mul eC eC) (Encl.inv (Encl.add ea esh))))
    (Encl.mul (Encl.mul eSv eSv) (Encl.inv (Encl.sub esh ea)))

theorem holds_optimalResidualEncl {S x s c θ : ℝ} {eS ex es ec : Encl}
    (hS : Encl.Holds S eS) (hx : Encl.Holds x ex) (hs : Encl.Holds s es) (hc : Encl.Holds c ec)
    (hSi : eS.r < |eS.c|) (hxi : ex.r < |ex.c|)
    (hxxi : (Encl.mul ex ex).r < |(Encl.mul ex ex).c|)
    (hDi : (Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul (Encl.smul (2 * θ) (Encl.inv eS))
      (Encl.smul (2 * θ) (Encl.inv eS))))).r <
      |(Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul (Encl.smul (2 * θ) (Encl.inv eS))
      (Encl.smul (2 * θ) (Encl.inv eS))))).c|)
    (hAi : (Encl.add (Encl.smul (1 / 2) eS) (Encl.smul (1 / 2) (Encl.sub (Encl.mul ex ex)
      (Encl.inv (Encl.mul ex ex))))).r < |(Encl.add (Encl.smul (1 / 2) eS)
      (Encl.smul (1 / 2) (Encl.sub (Encl.mul ex ex) (Encl.inv (Encl.mul ex ex))))).c|)
    (hBi : (Encl.sub (Encl.smul (1 / 2) (Encl.sub (Encl.mul ex ex) (Encl.inv (Encl.mul ex ex))))
      (Encl.smul (1 / 2) eS)).r < |(Encl.sub (Encl.smul (1 / 2) (Encl.sub (Encl.mul ex ex)
      (Encl.inv (Encl.mul ex ex)))) (Encl.smul (1 / 2) eS)).c|) :
    Encl.Holds (optimalResidualExpr S x s c θ) (optimalResidualEncl eS ex es ec θ) := by
  have hSinv := Encl.holds_inv hS hSi
  have hxinv := Encl.holds_inv hx hxi
  have hω : Encl.Holds (2 * θ * S⁻¹) (Encl.smul (2 * θ) (Encl.inv eS)) :=
    Encl.holds_smul (2 * θ) hSinv
  have hs2 := Encl.holds_smul (1 / 2) (Encl.holds_sub hx hxinv)
  have hc2 := Encl.holds_smul (1 / 2) (Encl.holds_add hx hxinv)
  have hxx := Encl.holds_mul hx hx
  have hsh := Encl.holds_smul (1 / 2) (Encl.holds_sub hxx (Encl.holds_inv hxx hxxi))
  have ha := Encl.holds_smul (1 / 2) hS
  have hD := Encl.holds_inv (Encl.holds_add (Encl.holds_exact 1)
    (Encl.holds_smul 4 (Encl.holds_mul hω hω))) hDi
  have hC := Encl.holds_smul 4 (Encl.holds_mul (Encl.holds_add (Encl.holds_mul hc hs2)
    (Encl.holds_mul (Encl.holds_smul 2 hω) (Encl.holds_mul hs hc2))) hD)
  have hSv := Encl.holds_smul 4 (Encl.holds_mul (Encl.holds_sub (Encl.holds_mul hs hc2)
    (Encl.holds_mul (Encl.holds_smul 2 hω) (Encl.holds_mul hc hs2))) hD)
  exact Encl.holds_sub (Encl.holds_sub (Encl.holds_smul 2 ha)
    (Encl.holds_mul (Encl.holds_mul hC hC) (Encl.holds_inv (Encl.holds_add ha hsh) hAi)))
    (Encl.holds_mul (Encl.holds_mul hSv hSv) (Encl.holds_inv (Encl.holds_sub hsh ha) hBi))

theorem sinh_primeTwoAperture_bounds :
    primeTwoAperture.1 + Real.sinh primeTwoAperture.1 ≠ 0 ∧
      Real.sinh primeTwoAperture.1 - primeTwoAperture.1 ≠ 0 := by
  have hb : 0 < primeTwoAperture.1 := primeTwoAperture.property
  constructor
  · have := Real.sinh_pos_iff.mpr hb
    linarith
  · have := Real.self_lt_sinh_iff.mpr hb
    linarith

/-- **The residual at the aperture `b` and a rational phase `θ`.** -/
theorem poleResidualOptimal_primeTwo_le (θ : ℝ) (hθ : |θ| ≤ 10)
    (hDi : (Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul
      (Encl.smul (2 * θ) (Encl.inv primeTwoApertureEncl))
      (Encl.smul (2 * θ) (Encl.inv primeTwoApertureEncl))))).r <
      |(Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul
      (Encl.smul (2 * θ) (Encl.inv primeTwoApertureEncl))
      (Encl.smul (2 * θ) (Encl.inv primeTwoApertureEncl))))).c|) :
    poleResidualOptimal primeTwoAperture.1
        (2 * Real.pi * (θ / (Real.pi * (Real.log 2 + 1 / 50)))) ≤
      (optimalResidualEncl primeTwoApertureEncl primeTwoQuarterEncl
        ⟨sinTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩
        ⟨cosTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩ θ).c +
      (optimalResidualEncl primeTwoApertureEncl primeTwoQuarterEncl
        ⟨sinTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩
        ⟨cosTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩ θ).r := by
  have hS : 0 < Real.log 2 + 1 / 50 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hb : primeTwoAperture.1 = (Real.log 2 + 1 / 50) / 2 := rfl
  rw [hb, poleResidualOptimal_eq_expr hS]
  apply Encl.le_of_holds
  apply holds_optimalResidualEncl holds_primeTwoApertureEncl holds_primeTwoQuarterEncl
    (encl_sin θ hθ) (encl_cos θ hθ)
  · norm_num [primeTwoApertureEncl, Encl.ofBounds]
  · norm_num [primeTwoQuarterEncl, Encl.ofBounds]
  · norm_num [primeTwoQuarterEncl, Encl.ofBounds, Encl.mul]
  · exact hDi
  · norm_num [primeTwoQuarterEncl, primeTwoApertureEncl, Encl.ofBounds, Encl.mul, Encl.add,
      Encl.sub, Encl.smul, Encl.inv]
  · norm_num [primeTwoQuarterEncl, primeTwoApertureEncl, Encl.ofBounds, Encl.mul, Encl.add,
      Encl.sub, Encl.smul, Encl.inv]

/-! ## The prime term -/

/-- The prime term `√2 log 2 (cos(2π log 2 · ξ) - cos(2π · 2b · ξ))` at the aperture `b`. -/
def primeTwoShiftTerm (ξ : ℝ) : ℝ :=
  Real.sqrt 2 * Real.log 2 *
    (Real.cos (2 * Real.pi * Real.log 2 * ξ) -
      Real.cos (2 * Real.pi * (2 * primeTwoAperture.1) * ξ))

theorem primeTwoShiftSymbol_eq (ξ : ℝ) :
    primeTwoShiftSymbol primeTwoAperture.1 ξ = archimedeanWeilSymbol ξ - primeTwoShiftTerm ξ :=
  rfl

theorem primeTwoShiftTerm_eq (ξ : ℝ) :
    primeTwoShiftTerm ξ = 2 * (Real.sqrt 2 * Real.log 2) *
      (Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ) * Real.sin (Real.pi * ξ / 50)) := by
  unfold primeTwoShiftTerm
  rw [Real.cos_sub_cos]
  have h1 : (2 * Real.pi * Real.log 2 * ξ + 2 * Real.pi * (2 * primeTwoAperture.1) * ξ) / 2 =
      Real.pi * (2 * Real.log 2 + 1 / 50) * ξ := by
    change (2 * Real.pi * Real.log 2 * ξ +
      2 * Real.pi * (2 * ((Real.log 2 + 1 / 50) / 2)) * ξ) / 2 = _
    ring
  have h2 : (2 * Real.pi * Real.log 2 * ξ - 2 * Real.pi * (2 * primeTwoAperture.1) * ξ) / 2 =
      -(Real.pi * ξ / 50) := by
    change (2 * Real.pi * Real.log 2 * ξ -
      2 * Real.pi * (2 * ((Real.log 2 + 1 / 50) / 2)) * ξ) / 2 = _
    ring
  rw [h1, h2, Real.sin_neg]
  ring

theorem primeTwoShiftTerm_even (ξ : ℝ) : primeTwoShiftTerm (-ξ) = primeTwoShiftTerm ξ := by
  unfold primeTwoShiftTerm
  simp only [mul_neg, Real.cos_neg]

theorem sqrt_two_mul_log_two_bounds : 0 ≤ Real.sqrt 2 * Real.log 2 ∧
    Real.sqrt 2 * Real.log 2 ≤ 0.98027 := by
  have hs : Real.sqrt 2 ≤ 1.4142136 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hl := Real.log_two_lt_d9
  have hl0 := Real.log_two_gt_d9
  constructor
  · positivity
  · nlinarith [Real.sqrt_nonneg 2]

/-- The prime term is at most `0.12319 · |ξ|`. -/
theorem primeTwoShiftTerm_le_linear (ξ : ℝ) : primeTwoShiftTerm ξ ≤ 0.12319 * |ξ| := by
  rw [primeTwoShiftTerm_eq]
  have hc := sqrt_two_mul_log_two_bounds
  have hs1 := Real.abs_sin_le_one (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ)
  have hs2 : |Real.sin (Real.pi * ξ / 50)| ≤ Real.pi * |ξ| / 50 := by
    refine Real.abs_sin_le_abs.trans (le_of_eq ?_)
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  have hpi := Real.pi_lt_d6
  have hprod : Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ) * Real.sin (Real.pi * ξ / 50) ≤
      Real.pi * |ξ| / 50 := by
    calc _ ≤ |Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ) *
          Real.sin (Real.pi * ξ / 50)| := le_abs_self _
      _ = |Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ)| *
          |Real.sin (Real.pi * ξ / 50)| := abs_mul _ _
      _ ≤ 1 * (Real.pi * |ξ| / 50) :=
          mul_le_mul hs1 hs2 (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hprod0 : Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ) *
      Real.sin (Real.pi * ξ / 50) ≤ Real.pi * |ξ| / 50 := hprod
  have := mul_le_mul_of_nonneg_left hprod0 (by linarith [hc.1] :
    (0 : ℝ) ≤ 2 * (Real.sqrt 2 * Real.log 2))
  have hξ := abs_nonneg ξ
  have hcpi : 2 * (Real.sqrt 2 * Real.log 2) * Real.pi / 50 ≤ 0.12319 := by
    nlinarith [hc.1, hc.2, Real.pi_pos]
  calc 2 * (Real.sqrt 2 * Real.log 2) * (Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * ξ) *
        Real.sin (Real.pi * ξ / 50)) ≤ 2 * (Real.sqrt 2 * Real.log 2) * (Real.pi * |ξ| / 50) :=
        this
    _ = (2 * (Real.sqrt 2 * Real.log 2) * Real.pi / 50) * |ξ| := by ring
    _ ≤ 0.12319 * |ξ| := mul_le_mul_of_nonneg_right hcpi hξ

/-- The prime term is at most `1.9606`. -/
theorem primeTwoShiftTerm_le_const (ξ : ℝ) : primeTwoShiftTerm ξ ≤ 1.9606 := by
  unfold primeTwoShiftTerm
  have hc := sqrt_two_mul_log_two_bounds
  have h1 := Real.neg_one_le_cos (2 * Real.pi * (2 * primeTwoAperture.1) * ξ)
  have h2 := Real.cos_le_one (2 * Real.pi * Real.log 2 * ξ)
  nlinarith

/-- On `[1/(2 log 2 + 1/50), 2/(2 log 2 + 1/50)]` the prime term is nonpositive. -/
theorem primeTwoShiftTerm_nonpos {ξ : ℝ} (h1 : 0.7111 ≤ |ξ|) (h2 : |ξ| ≤ 1.4221) :
    primeTwoShiftTerm ξ ≤ 0 := by
  have hev : primeTwoShiftTerm ξ = primeTwoShiftTerm |ξ| := by
    rcases le_or_gt 0 ξ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, primeTwoShiftTerm_even]
  rw [hev, primeTwoShiftTerm_eq]
  set t := |ξ|
  have hc := sqrt_two_mul_log_two_bounds
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d6
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  have hA1 : Real.pi ≤ Real.pi * (2 * Real.log 2 + 1 / 50) * t := by
    have : 1 ≤ (2 * Real.log 2 + 1 / 50) * t := by nlinarith
    nlinarith [Real.pi_pos]
  have hA2 : Real.pi * (2 * Real.log 2 + 1 / 50) * t ≤ 2 * Real.pi := by
    have : (2 * Real.log 2 + 1 / 50) * t ≤ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hsA : Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * t) ≤ 0 := by
    have := Real.sin_nonneg_of_nonneg_of_le_pi
      (x := Real.pi * (2 * Real.log 2 + 1 / 50) * t - Real.pi) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this
    linarith
  have hsB : 0 ≤ Real.sin (Real.pi * t / 50) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have : t ≤ 50 := by linarith
    nlinarith [Real.pi_pos]
  have : Real.sin (Real.pi * (2 * Real.log 2 + 1 / 50) * t) * Real.sin (Real.pi * t / 50) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hsA hsB
  nlinarith [hc.1]

/-! ## The archimedean symbol at the grid and tail points -/

/-- The grid lower bound for `W` with the logarithm compared at `2^j · 264.0625`. -/
theorem archimedeanWeilSymbol_ge_of_sq_pow (j : ℕ) {ξ Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : Y ≤ (Real.pi * ξ) ^ 2) :
    (4 * 0.6931471803 + (1 - 64 / 65)) +
        (1 / 2) * (j * 0.6931471803 + (1 - 2 ^ j * 264.0625 / (264.0625 + Y))) -
        13.125 / (264.0625 + Y) -
        ∑ i ∈ Finset.range 16, ((i : ℝ) + 1 / 4) / (((i : ℝ) + 1 / 4) ^ 2 + Y) - 1.146 ≤
      archimedeanWeilSymbol ξ := by
  rw [archimedeanWeilSymbol_eq]
  have hmain := re_digamma_quarter_ge (Real.pi * ξ)
  set y2 := (Real.pi * ξ) ^ 2 with hy2
  have hX : 0 < 264.0625 + Y := by positivity
  have hXY : 264.0625 + Y ≤ 264.0625 + y2 := by linarith
  have hpow : (0 : ℝ) < 2 ^ j * 264.0625 := by positivity
  have hlogX : Real.log (2 ^ j * 264.0625) + (1 - 2 ^ j * 264.0625 / (264.0625 + y2)) ≤
      Real.log (264.0625 + y2) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (264.0625 + y2) / (2 ^ j * 264.0625))
      (by positivity)
    rw [Real.log_div (by positivity) hpow.ne', inv_div] at h
    linarith
  have hlogpow : Real.log (2 ^ j * 264.0625) =
      j * Real.log 2 + Real.log 264.0625 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have hlog264 : 2 * (4 * 0.6931471803 + (1 - 64 / 65)) ≤ Real.log 264.0625 := by
    rw [show (264.0625 : ℝ) = 16.25 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [log_sixteen_quarter_ge]
  have hj : (j : ℝ) * 0.6931471803 ≤ j * Real.log 2 :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg j)
  have hfrac : 1 - 2 ^ j * 264.0625 / (264.0625 + Y) ≤
      1 - 2 ^ j * 264.0625 / (264.0625 + y2) := by
    have := div_le_div_of_nonneg_left hpow.le hX hXY
    linarith
  have hfrac2 : 13.125 / (264.0625 + y2) ≤ 13.125 / (264.0625 + Y) :=
    div_le_div_of_nonneg_left (by norm_num) hX hXY
  have hsum : ∑ i ∈ Finset.range 16, ((i : ℝ) + 1 / 4) / (((i : ℝ) + 1 / 4) ^ 2 + y2) ≤
      ∑ i ∈ Finset.range 16, ((i : ℝ) + 1 / 4) / (((i : ℝ) + 1 / 4) ^ 2 + Y) := by
    apply Finset.sum_le_sum
    intro i _
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have hlp := log_pi_lt
  linarith

theorem archimedeanWeilSymbol_ge_grid_pow (j : ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    (4 * 0.6931471803 + (1 - 64 / 65)) +
        (1 / 2) * (j * 0.6931471803 +
          (1 - 2 ^ j * 264.0625 / (264.0625 + (3.141592 * ξ) ^ 2))) -
        13.125 / (264.0625 + (3.141592 * ξ) ^ 2) -
        ∑ i ∈ Finset.range 16, ((i : ℝ) + 1 / 4) / (((i : ℝ) + 1 / 4) ^ 2 + (3.141592 * ξ) ^ 2) -
        1.146 ≤ archimedeanWeilSymbol ξ :=
  archimedeanWeilSymbol_ge_of_sq_pow j (by positivity)
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right Real.pi_gt_d6.le hξ) 2)

theorem gridSymbol_15 : (0.38 : ℝ) ≤ archimedeanWeilSymbol ((15 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_16 : (0.44 : ℝ) ≤ archimedeanWeilSymbol ((16 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_17 : (0.50 : ℝ) ≤ archimedeanWeilSymbol ((17 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem tailSymbol_0 : (0.55254 : ℝ) ≤ archimedeanWeilSymbol 1.8 := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid_pow 0 (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem tailSymbol_1 : (0.69421 : ℝ) ≤ archimedeanWeilSymbol 2.05 := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid_pow 0 (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem tailSymbol_2 : (1.113054 : ℝ) ≤ archimedeanWeilSymbol 3.2 := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid_pow 0 (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem tailSymbol_3 : (1.839875 : ℝ) ≤ archimedeanWeilSymbol 6.6 := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid_pow 1 (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem tailSymbol_4 : (2.2606 : ℝ) ≤ archimedeanWeilSymbol 12.5 := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid_pow 3 (by norm_num))
  norm_num [Finset.sum_range_succ]

/-! ## The eighteen shell residuals at the aperture `b` -/

theorem primeTwoShellResidual_0 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((1120 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0002 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_1 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((3361 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0006 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_2 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((5601 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0021 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_3 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((7841 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0066 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_4 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((10082 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0160 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_5 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((12322 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0330 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_6 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((14563 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0590 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_7 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((16803 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.0930 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_8 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((19043 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.145 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_9 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((21284 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.203 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_10 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((23524 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.270 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_11 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((25765 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.340 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_12 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((28005 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.412 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_13 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((30246 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.480 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_14 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((32486 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.545 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_15 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((34726 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.5800 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_16 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((36967 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.6300 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

theorem primeTwoShellResidual_17 : poleResidualOptimal primeTwoAperture.1
    (2 * Real.pi * ((39207 / 10000 : ℝ) / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ 0.6750 := by
  refine (poleResidualOptimal_primeTwo_le _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, primeTwoApertureEncl,
      Encl.ofBounds]
  · norm_num [optimalResidualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      primeTwoApertureEncl, primeTwoQuarterEncl, Encl.ofBounds, sinTaylor, cosTaylor,
      Finset.sum_range_succ, Nat.factorial]

/-! ## Shells, tail and assembly -/

theorem pi_mul_primeTwo_bounds :
    (2.2404174 : ℝ) ≤ Real.pi * (Real.log 2 + 1 / 50) ∧
      Real.pi * (Real.log 2 + 1 / 50) ≤ 2.2404182 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  constructor <;> nlinarith

theorem primeTwo_ref_le {θ : ℝ} (hθ : 0 ≤ θ) :
    θ / (Real.pi * (Real.log 2 + 1 / 50)) ≤ θ / 2.2404174 :=
  div_le_div_of_nonneg_left hθ (by norm_num) pi_mul_primeTwo_bounds.1

theorem primeTwo_ref_ge {θ : ℝ} (hθ : 0 ≤ θ) :
    θ / 2.2404182 ≤ θ / (Real.pi * (Real.log 2 + 1 / 50)) :=
  div_le_div_of_nonneg_left hθ (by nlinarith [pi_mul_primeTwo_bounds.1])
    pi_mul_primeTwo_bounds.2

/-- The Lipschitz offset at the aperture `b`. -/
theorem lipschitz_offset_primeTwo_le {d : ℝ} (hd : |d| ≤ 0.0501) :
    4 * Real.pi ^ 2 * d ^ 2 * (2 * primeTwoAperture.1 ^ 3 / 3) ≤ 0.00301 := by
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have hL := Real.log_two_lt_d9
  have hL0 := Real.log_two_gt_d9
  have hb : primeTwoAperture.1 = (Real.log 2 + 1 / 50) / 2 := rfl
  rw [hb]
  have hd2 : d ^ 2 ≤ 0.0501 ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hpi2 : Real.pi ^ 2 ≤ 3.141593 ^ 2 := pow_le_pow_left₀ hpi0.le hpi.le 2
  have hb3 : ((Real.log 2 + 1 / 50) / 2) ^ 3 ≤ ((0.6931471808 + 1 / 50) / 2) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  calc 4 * Real.pi ^ 2 * d ^ 2 * (2 * ((Real.log 2 + 1 / 50) / 2) ^ 3 / 3) ≤
        4 * 3.141593 ^ 2 * 0.0501 ^ 2 * (2 * ((0.6931471808 + 1 / 50) / 2) ^ 3 / 3) := by
        gcongr
    _ ≤ 0.00301 := by norm_num

/-- **One shell at the aperture `b`.** -/
theorem shell_fourier_bound_primeTwo {θ r η lo hi : ℝ} (hη : 0 < η)
    (hres : poleResidualOptimal primeTwoAperture.1
      (2 * Real.pi * (θ / (Real.pi * (Real.log 2 + 1 / 50)))) ≤ r)
    (hlo : θ / (Real.pi * (Real.log 2 + 1 / 50)) - lo ≤ 0.0501)
    (hhi : hi - θ / (Real.pi * (Real.log 2 + 1 / 50)) ≤ 0.0501)
    (f : suzukiApertureHilbert primeTwoAperture)
    (hplus : inner ℂ (ccmPolarL2Vector primeTwoAperture (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector primeTwoAperture (-1 / 2)) f.1 = 0)
    (ξ : ℝ) (hξlo : lo ≤ |ξ|) (hξhi : |ξ| < hi) :
    ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ ((1 + η) * r + (1 + 1 / η) * 0.00301) * ‖f‖ ^ 2 := by
  set m := θ / (Real.pi * (Real.log 2 + 1 / 50)) with hm
  have hsh := sinh_primeTwoAperture_bounds
  have h1η : 0 ≤ 1 + 1 / η := by positivity
  have hf2 : 0 ≤ ‖f‖ ^ 2 := sq_nonneg _
  rcases le_or_gt 0 ξ with hξ | hξ
  · rw [abs_of_nonneg hξ] at hξlo hξhi
    have hb := norm_fourier_sq_le_of_polar_optimal primeTwoAperture hsh.1 hsh.2 f hplus hminus
      ξ m η hη
    have hoff := lipschitz_offset_primeTwo_le (d := ξ - m)
      (by rw [abs_le]; constructor <;> linarith)
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hf2)
    have := mul_le_mul_of_nonneg_left hres (by linarith : (0 : ℝ) ≤ 1 + η)
    have := mul_le_mul_of_nonneg_left hoff h1η
    linarith
  · rw [abs_of_neg hξ] at hξlo hξhi
    have hb := norm_fourier_sq_le_of_polar_optimal primeTwoAperture hsh.1 hsh.2 f hplus hminus
      ξ (-m) η hη
    rw [show 2 * Real.pi * -m = -(2 * Real.pi * m) by ring, poleResidualOptimal_neg] at hb
    have hoff := lipschitz_offset_primeTwo_le (d := ξ - -m)
      (by rw [abs_le]; constructor <;> linarith)
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hf2)
    have := mul_le_mul_of_nonneg_left hres (by linarith : (0 : ℝ) ≤ 1 + η)
    have := mul_le_mul_of_nonneg_left hoff h1η
    linarith

theorem shell_symbol_bound_primeTwo {ξ lo w pb : ℝ} (hlo0 : 0 ≤ lo) (hξlo : lo ≤ |ξ|)
    (hW : w ≤ archimedeanWeilSymbol lo) (hP : primeTwoShiftTerm ξ ≤ pb) :
    w - pb ≤ primeTwoShiftSymbol primeTwoAperture.1 ξ := by
  rw [primeTwoShiftSymbol_eq]
  have := archimedeanWeilSymbol_mono (ξ := lo) (ζ := ξ) (by rw [abs_of_nonneg hlo0]; exact hξlo)
  linarith

/-- The step heights at the aperture `b`. -/
def certG2 : ℕ → ℝ
  | 0 => 3 / 10 - (-5.40) + 0.12319 * 1 / 10
  | 1 => 3 / 10 - (-2.89) + 0.12319 * 2 / 10
  | 2 => 3 / 10 - (-1.73) + 0.12319 * 3 / 10
  | 3 => 3 / 10 - (-1.26) + 0.12319 * 4 / 10
  | 4 => 3 / 10 - (-0.955) + 0.12319 * 5 / 10
  | 5 => 3 / 10 - (-0.725) + 0.12319 * 6 / 10
  | 6 => 3 / 10 - (-0.54) + 0.12319 * 7 / 10
  | 7 => 3 / 10 - (-0.385) + 0.12319 * 8 / 10
  | 8 => 3 / 10 - (-0.252) + 0
  | 9 => 3 / 10 - (-0.133) + 0
  | 10 => 3 / 10 - (-0.027) + 0
  | 11 => 3 / 10 - (0.068) + 0
  | 12 => 3 / 10 - (0.155) + 0
  | 13 => 3 / 10 - (0.235) + 0
  | 14 => 3 / 10 - (0.3) + 0.12319 * 15 / 10
  | 15 => 3 / 10 - (0.38) + 0.12319 * 16 / 10
  | 16 => 3 / 10 - (0.44) + 0.12319 * 17 / 10
  | 17 => 3 / 10 - (0.50) + 0.12319 * 18 / 10
  | _ => 0

/-- The shell Fourier-mass constants at the aperture `b`. -/
def certR2 : ℕ → ℝ
  | 0 => (1 + 4) * 0.0002 + (1 + 1 / 4) * 0.00301
  | 1 => (1 + 2) * 0.0006 + (1 + 1 / 2) * 0.00301
  | 2 => (1 + 1.2) * 0.0021 + (1 + 1 / 1.2) * 0.00301
  | 3 => (1 + 0.7) * 0.0066 + (1 + 1 / 0.7) * 0.00301
  | 4 => (1 + 0.45) * 0.0160 + (1 + 1 / 0.45) * 0.00301
  | 5 => (1 + 0.3) * 0.0330 + (1 + 1 / 0.3) * 0.00301
  | 6 => (1 + 0.23) * 0.0590 + (1 + 1 / 0.23) * 0.00301
  | 7 => (1 + 0.18) * 0.0930 + (1 + 1 / 0.18) * 0.00301
  | 8 => (1 + 0.15) * 0.145 + (1 + 1 / 0.15) * 0.00301
  | 9 => (1 + 0.125) * 0.203 + (1 + 1 / 0.125) * 0.00301
  | 10 => (1 + 0.11) * 0.270 + (1 + 1 / 0.11) * 0.00301
  | 11 => (1 + 0.097) * 0.340 + (1 + 1 / 0.097) * 0.00301
  | 12 => (1 + 0.088) * 0.412 + (1 + 1 / 0.088) * 0.00301
  | 13 => (1 + 0.081) * 0.480 + (1 + 1 / 0.081) * 0.00301
  | 14 => (1 + 0.076) * 0.545 + (1 + 1 / 0.076) * 0.00301
  | 15 => (1 + 0.072) * 0.5800 + (1 + 1 / 0.072) * 0.00301
  | 16 => (1 + 0.069) * 0.6300 + (1 + 1 / 0.069) * 0.00301
  | 17 => (1 + 0.067) * 0.6750 + (1 + 1 / 0.067) * 0.00301
  | _ => 0

theorem certG2_nonneg (k : ℕ) : 0 ≤ certG2 k := by
  unfold certG2
  split <;> norm_num

theorem cert2_hshell : ∀ k : ℕ, k < 18 → ∀ ξ : ℝ, (k : ℝ) * (1 / 10) ≤ |ξ| →
    |ξ| < ((k : ℝ) + 1) * (1 / 10) →
    3 / 10 - certG2 k ≤ primeTwoShiftSymbol primeTwoAperture.1 ξ := by
  intro k hk ξ hlo hhi
  interval_cases k
  · have h := shell_symbol_bound_primeTwo (lo := ((0 : ℕ) : ℝ) * (1 / 10)) (w := -5.40)
      (pb := 0.12319 * 1 / 10) (by norm_num) hlo gridSymbol_0
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((1 : ℕ) : ℝ) * (1 / 10)) (w := -2.89)
      (pb := 0.12319 * 2 / 10) (by norm_num) hlo gridSymbol_1
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((2 : ℕ) : ℝ) * (1 / 10)) (w := -1.73)
      (pb := 0.12319 * 3 / 10) (by norm_num) hlo gridSymbol_2
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((3 : ℕ) : ℝ) * (1 / 10)) (w := -1.26)
      (pb := 0.12319 * 4 / 10) (by norm_num) hlo gridSymbol_3
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((4 : ℕ) : ℝ) * (1 / 10)) (w := -0.955)
      (pb := 0.12319 * 5 / 10) (by norm_num) hlo gridSymbol_4
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((5 : ℕ) : ℝ) * (1 / 10)) (w := -0.725)
      (pb := 0.12319 * 6 / 10) (by norm_num) hlo gridSymbol_5
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((6 : ℕ) : ℝ) * (1 / 10)) (w := -0.54)
      (pb := 0.12319 * 7 / 10) (by norm_num) hlo gridSymbol_6
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((7 : ℕ) : ℝ) * (1 / 10)) (w := -0.385)
      (pb := 0.12319 * 8 / 10) (by norm_num) hlo gridSymbol_7
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((8 : ℕ) : ℝ) * (1 / 10)) (w := -0.252)
      (pb := 0) (by norm_num) hlo gridSymbol_8
      (primeTwoShiftTerm_nonpos (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((9 : ℕ) : ℝ) * (1 / 10)) (w := -0.133)
      (pb := 0) (by norm_num) hlo gridSymbol_9
      (primeTwoShiftTerm_nonpos (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((10 : ℕ) : ℝ) * (1 / 10)) (w := -0.027)
      (pb := 0) (by norm_num) hlo gridSymbol_10
      (primeTwoShiftTerm_nonpos (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((11 : ℕ) : ℝ) * (1 / 10)) (w := 0.068)
      (pb := 0) (by norm_num) hlo gridSymbol_11
      (primeTwoShiftTerm_nonpos (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((12 : ℕ) : ℝ) * (1 / 10)) (w := 0.155)
      (pb := 0) (by norm_num) hlo gridSymbol_12
      (primeTwoShiftTerm_nonpos (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((13 : ℕ) : ℝ) * (1 / 10)) (w := 0.235)
      (pb := 0) (by norm_num) hlo gridSymbol_13
      (primeTwoShiftTerm_nonpos (by norm_num at hlo ⊢; linarith) (by norm_num at hhi ⊢; linarith))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((14 : ℕ) : ℝ) * (1 / 10)) (w := 0.3)
      (pb := 0.12319 * 15 / 10) (by norm_num) hlo gridSymbol_14
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((15 : ℕ) : ℝ) * (1 / 10)) (w := 0.38)
      (pb := 0.12319 * 16 / 10) (by norm_num) hlo gridSymbol_15
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((16 : ℕ) : ℝ) * (1 / 10)) (w := 0.44)
      (pb := 0.12319 * 17 / 10) (by norm_num) hlo gridSymbol_16
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith
  · have h := shell_symbol_bound_primeTwo (lo := ((17 : ℕ) : ℝ) * (1 / 10)) (w := 0.50)
      (pb := 0.12319 * 18 / 10) (by norm_num) hlo gridSymbol_17
      ((primeTwoShiftTerm_le_linear ξ).trans (by norm_num at hhi ⊢; nlinarith [abs_nonneg ξ]))
    norm_num [certG2] at h ⊢
    linarith

theorem cert2_htail : ∀ ξ : ℝ, ((18 : ℕ) : ℝ) * (1 / 10) ≤ |ξ| →
    3 / 10 ≤ primeTwoShiftSymbol primeTwoAperture.1 ξ := by
  intro ξ hξ
  norm_num at hξ
  rw [primeTwoShiftSymbol_eq]
  have hlin := primeTwoShiftTerm_le_linear ξ
  have hconst := primeTwoShiftTerm_le_const ξ
  have hmono : ∀ t : ℝ, 0 ≤ t → t ≤ |ξ| → archimedeanWeilSymbol t ≤ archimedeanWeilSymbol ξ :=
    fun t ht htξ => archimedeanWeilSymbol_mono (by rw [abs_of_nonneg ht]; exact htξ)
  by_cases h1 : |ξ| < 2.05
  · have := hmono 1.8 (by norm_num) (by linarith)
    have := tailSymbol_0
    nlinarith
  by_cases h2 : |ξ| < 3.2
  · have := hmono 2.05 (by norm_num) (by linarith)
    have := tailSymbol_1
    nlinarith
  by_cases h3 : |ξ| < 6.6
  · have := hmono 3.2 (by norm_num) (by linarith)
    have := tailSymbol_2
    nlinarith
  by_cases h4 : |ξ| < 12.5
  · have := hmono 6.6 (by norm_num) (by linarith)
    have := tailSymbol_3
    nlinarith
  · have := hmono 12.5 (by norm_num) (by linarith)
    have := tailSymbol_4
    linarith

theorem cert2_hR : ∀ k : ℕ, k < 18 → ∀ f : suzukiApertureHilbert primeTwoAperture,
    inner ℂ (ccmPolarL2Vector primeTwoAperture (1 / 2)) f.1 = 0 →
    inner ℂ (ccmPolarL2Vector primeTwoAperture (-1 / 2)) f.1 = 0 →
    ∀ ξ : ℝ, (k : ℝ) * (1 / 10) ≤ |ξ| → |ξ| < ((k : ℝ) + 1) * (1 / 10) →
      ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ certR2 k * ‖f‖ ^ 2 := by
  intro k hk f hplus hminus ξ hlo hhi
  interval_cases k
  · have h1 := primeTwo_ref_le (θ := (1120 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (1120 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 4) (by norm_num) primeTwoShellResidual_0
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (3361 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (3361 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 2) (by norm_num) primeTwoShellResidual_1
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (5601 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (5601 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 1.2) (by norm_num) primeTwoShellResidual_2
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (7841 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (7841 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.7) (by norm_num) primeTwoShellResidual_3
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (10082 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (10082 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.45) (by norm_num) primeTwoShellResidual_4
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (12322 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (12322 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.3) (by norm_num) primeTwoShellResidual_5
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (14563 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (14563 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.23) (by norm_num) primeTwoShellResidual_6
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (16803 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (16803 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.18) (by norm_num) primeTwoShellResidual_7
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (19043 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (19043 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.15) (by norm_num) primeTwoShellResidual_8
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (21284 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (21284 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.125) (by norm_num) primeTwoShellResidual_9
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (23524 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (23524 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.11) (by norm_num) primeTwoShellResidual_10
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (25765 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (25765 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.097) (by norm_num) primeTwoShellResidual_11
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (28005 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (28005 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.088) (by norm_num) primeTwoShellResidual_12
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (30246 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (30246 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.081) (by norm_num) primeTwoShellResidual_13
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (32486 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (32486 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.076) (by norm_num) primeTwoShellResidual_14
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (34726 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (34726 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.072) (by norm_num) primeTwoShellResidual_15
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (36967 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (36967 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.069) (by norm_num) primeTwoShellResidual_16
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := primeTwo_ref_le (θ := (39207 / 10000 : ℝ)) (by norm_num)
    have h2 := primeTwo_ref_ge (θ := (39207 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound_primeTwo (η := 0.067) (by norm_num) primeTwoShellResidual_17
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi

/-- **Explicit Weil positivity past the entry of the prime 2, without numerical assistance.**
At the aperture `b = ½ (log 2 + 1/50)` (multiplicative support `[λ^{-1}, λ]`,
`λ = √2 · e^{1/100} ≈ 1.4284`), where the form contains the prime `2`, the pole-vanishing
ground energy of the exact restricted Weil form is at least `1/20`. -/
theorem one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo :
    (1 / 20 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy primeTwoAperture := by
  have h := le_ccmRestrictedWeilPolarGroundEnergy_of_symbol_grid (a := primeTwoAperture)
    (primeTwoShiftSymbol primeTwoAperture.1)
    (fun u hu => ccmRestrictedWeilSourceQuadratic_primeTwo_eq primeTwoAperture
      primeTwoAperture_log_two_le primeTwoAperture_lt_log_three u hu)
    (fun u => integrable_primeTwoShiftSymbol_mul primeTwoAperture primeTwoAperture u)
    (α := 3 / 10) (h := 1 / 10) (K := 18) (G := certG2) (R := certR2) (by norm_num)
    certG2_nonneg cert2_hshell cert2_htail cert2_hR
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, certG2, certR2]

/-- **Every aperture up to `½ (log 2 + 1/50)`.**  The pole-vanishing restricted Weil form is
positive definite, with ground energy at least `1/20`, on every aperture `c ≤ ½ (log 2 + 1/50)`;
past `½ log 2` it contains the prime `2`. -/
theorem one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_of_le_primeTwo
    (c : SuzukiPositiveAperture) (hc : c.1 ≤ (Real.log 2 + 1 / 50) / 2) :
    (1 / 20 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy c :=
  one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo.trans
    (ccmRestrictedWeilPolarGroundEnergy_antitone hc)

end RHTower
