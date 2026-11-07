import GaloisForLFunctions.BlackHoleRingdown.TheMetricRingdown

/-!
# The scalar gravitational wave of a pulse

The corpus scalar reconstruction `(e^{st} (1-r⁻²)^{s/2} S(z)) • M_s(r, y)`, with `y²ΔS = (s+1)(s+2) S`, has matrix entries polynomial in
`s` of degree two. Write `D = ∂_τ - 3/2` and replace `s` by `D`: for every pulse `h`,

`H_{ij}(t, r, z) = e^{-3τ/2} (M_D(r, y) Π_h)_{ij}(τ, z)`,  `τ = t + γ(r)`,

is an exact vacuum perturbation of the metric. No spatial derivative of `Π_h` enters, so the scalar sector needs no jets of
the numerator. Each entry is `e^{-3τ/2}` times the image field of a pulse `g = α h + β h' + γ h''`.

The proof is the interpolation of the vector sector: for one row the perturbation depends on `m, m', m''` for
`m(S) = e^{-3S/2} h(S)`, so its two-jet at a point depends on five values, and five exponentials realize them.

The mean of `Π_g` contributes `e^{-τ}` times a constant, the mode `s = -1` of the constant eigenfunction. The rest rings down in
the modes of the zeros, with amplitude `(A + B s + C s²) a(-ip) N(p)` at `s = p - 3/2`, which is the entry of `M_s` for the
scalar mode of the zero.
-/

open Complex Filter Topology Set
open scoped ContDiff BigOperators

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMHorizon _root_.RHTower.D4BMMetricReconstruction
open EisensteinSeries

/-! ### The coefficients of the reconstruction -/

/-- The square of the height of the row. -/
def rowSq (c d : ℝ) (x : Fin 4 → ℝ) : ℂ := ((rowHgt c d (x 2) (x 3) : ℝ) : ℂ) ^ 2

/-- A coefficient triple `A m + B m' + C m''`. -/
structure Coeff where
  A : (Fin 4 → ℝ) → ℂ
  B : (Fin 4 → ℝ) → ℂ
  C : (Fin 4 → ℝ) → ℂ

/-- The radius and its inverse powers as complex fields. -/
def rC (x : Fin 4 → ℝ) : ℂ := (x 1 : ℂ)
def yC (x : Fin 4 → ℝ) : ℂ := (x 3 : ℂ)

/-- `tt = s²(½ + 1/(2r²)) + s(-3/2 + 1/(2r²))`. -/
def coeffTT : Coeff := ⟨fun _ => 0, fun x => -(3 / 2) + (2 * rC x ^ 2)⁻¹, fun x => 1 / 2 + (2 * rC x ^ 2)⁻¹⟩

/-- `tr = (s² - s r²)/(r f)`. -/
def coeffTR : Coeff :=
  ⟨fun _ => 0, fun x => -(rC x ^ 2) * (rC x * (rC x ^ 2 - 1))⁻¹, fun x => (rC x * (rC x ^ 2 - 1))⁻¹⟩

/-- `rr = tt/f²`. -/
def coeffRR : Coeff :=
  ⟨fun _ => 0, fun x => (-(3 / 2) + (2 * rC x ^ 2)⁻¹) * ((rC x ^ 2 - 1) ^ 2)⁻¹,
    fun x => (1 / 2 + (2 * rC x ^ 2)⁻¹) * ((rC x ^ 2 - 1) ^ 2)⁻¹⟩

/-- `aa = (-r² - s(s+1)/2)/y²`. -/
def coeffAA : Coeff :=
  ⟨fun x => -(rC x ^ 2) * (yC x ^ 2)⁻¹, fun x => -(1 / 2) * (yC x ^ 2)⁻¹, fun x => -(1 / 2) * (yC x ^ 2)⁻¹⟩

/-- The entry of a row. -/
def rowEntry (c d : ℝ) (K : Coeff) (m m₁ m₂ : ℝ → ℂ) (x : Fin 4 → ℝ) : ℂ :=
  rowSq c d x * K.A x * m (rowS c d x) + rowSq c d x * K.B x * m₁ (rowS c d x) +
    rowSq c d x * K.C x * m₂ (rowS c d x)

/-- **The scalar perturbation of a row.** -/
def scalarRow (c d : ℝ) (m m₁ m₂ : ℝ → ℂ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![rowEntry c d coeffTT m m₁ m₂ x, rowEntry c d coeffTR m m₁ m₂ x, 0, 0;
    rowEntry c d coeffTR m m₁ m₂ x, rowEntry c d coeffRR m m₁ m₂ x, 0, 0;
    0, 0, rowEntry c d coeffAA m m₁ m₂ x, 0;
    0, 0, 0, rowEntry c d coeffAA m m₁ m₂ x]

section Smooth

variable {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y) (q : D4BMBackground.ExteriorPoint)

theorem contDiffAt_rC {p : Fin 4 → ℝ} : ContDiffAt ℝ 2 rC p :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt

theorem contDiffAt_yC {p : Fin 4 → ℝ} : ContDiffAt ℝ 2 yC p :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 3)).contDiffAt

include hden in
theorem contDiffAt_rowSq : ContDiffAt ℝ 2 (rowSq c d) q.val := by
  have hD := hden (q.val 2) (q.val 3) q.property.2
  have hS : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => rowHgt c d (x 2) (x 3)) q.val :=
    ContDiffAt.div (by fun_prop) contDiffAt_rowDen hD.ne'
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp q.val hS).pow 2

theorem rC_ne : rC q.val ≠ 0 := by
  have h : (q.val 1 : ℝ) ≠ 0 := by linarith [q.property.1]
  exact Complex.ofReal_ne_zero.mpr h

theorem rC_factor_ne : rC q.val ^ 2 - 1 ≠ 0 := by
  have h : (q.val 1 : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith [q.property.1]
  change ((q.val 1 : ℝ) : ℂ) ^ 2 - 1 ≠ 0
  exact_mod_cast h

theorem yC_ne : yC q.val ≠ 0 := by
  have h : (q.val 3 : ℝ) ≠ 0 := q.property.2.ne'
  exact Complex.ofReal_ne_zero.mpr h

/-- A coefficient triple is regular. -/
def Coeff.Regular (K : Coeff) (p : Fin 4 → ℝ) : Prop :=
  ContDiffAt ℝ 2 K.A p ∧ ContDiffAt ℝ 2 K.B p ∧ ContDiffAt ℝ 2 K.C p

theorem regular_TT : coeffTT.Regular q.val := by
  have h1 : ContDiffAt ℝ 2 (fun x => (2 * rC x ^ 2)⁻¹) q.val :=
    (contDiffAt_const.mul (contDiffAt_rC.pow 2)).inv
      (mul_ne_zero two_ne_zero (pow_ne_zero 2 (rC_ne q)))
  exact ⟨contDiffAt_const, contDiffAt_const.add h1, contDiffAt_const.add h1⟩

theorem regular_TR : coeffTR.Regular q.val := by
  have hF : ContDiffAt ℝ 2 (fun x => rC x ^ 2 - 1) q.val := (contDiffAt_rC.pow 2).sub contDiffAt_const
  have h1 : ContDiffAt ℝ 2 (fun x => (rC x * (rC x ^ 2 - 1))⁻¹) q.val :=
    (contDiffAt_rC.mul hF).inv (mul_ne_zero (rC_ne q) (rC_factor_ne q))
  exact ⟨contDiffAt_const, ((contDiffAt_rC.pow 2).neg).mul h1, h1⟩

theorem regular_RR : coeffRR.Regular q.val := by
  have h1 : ContDiffAt ℝ 2 (fun x => (2 * rC x ^ 2)⁻¹) q.val :=
    (contDiffAt_const.mul (contDiffAt_rC.pow 2)).inv
      (mul_ne_zero two_ne_zero (pow_ne_zero 2 (rC_ne q)))
  have hF : ContDiffAt ℝ 2 (fun x => ((rC x ^ 2 - 1) ^ 2)⁻¹) q.val :=
    (((contDiffAt_rC.pow 2).sub contDiffAt_const).pow 2).inv (pow_ne_zero 2 (rC_factor_ne q))
  exact ⟨contDiffAt_const, (contDiffAt_const.add h1).mul hF, (contDiffAt_const.add h1).mul hF⟩

theorem regular_AA : coeffAA.Regular q.val := by
  have h1 : ContDiffAt ℝ 2 (fun x => (yC x ^ 2)⁻¹) q.val :=
    (contDiffAt_yC.pow 2).inv (pow_ne_zero 2 (yC_ne q))
  exact ⟨((contDiffAt_rC.pow 2).neg).mul h1, contDiffAt_const.mul h1, contDiffAt_const.mul h1⟩

variable {m m₁ m₂ n n₁ n₂ : ℝ → ℂ} {K : Coeff}

include hden in
theorem contDiffAt_rowEntry (hK : K.Regular q.val) (hm : ContDiffAt ℝ 2 m (rowS c d q.val))
    (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val)) (hm₂ : ContDiffAt ℝ 2 m₂ (rowS c d q.val)) :
    ContDiffAt ℝ 2 (rowEntry c d K m m₁ m₂) q.val := by
  have hS := contDiffAt_rowS hden q
  have hg := contDiffAt_rowSq hden q
  exact (((hg.mul hK.1).mul (hm.comp q.val hS)).add ((hg.mul hK.2.1).mul (hm₁.comp q.val hS))).add
    ((hg.mul hK.2.2).mul (hm₂.comp q.val hS))

include hden in
theorem ofField_rowEntry_congr (hK : K.Regular q.val)
    (hm : ContDiffAt ℝ 2 m (rowS c d q.val)) (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val))
    (hm₂ : ContDiffAt ℝ 2 m₂ (rowS c d q.val)) (hn : ContDiffAt ℝ 2 n (rowS c d q.val))
    (hn₁ : ContDiffAt ℝ 2 n₁ (rowS c d q.val)) (hn₂ : ContDiffAt ℝ 2 n₂ (rowS c d q.val))
    (h0 : ofField (fun x => m (rowS c d x)) q.val = ofField (fun x => n (rowS c d x)) q.val)
    (h1 : ofField (fun x => m₁ (rowS c d x)) q.val = ofField (fun x => n₁ (rowS c d x)) q.val)
    (h2 : ofField (fun x => m₂ (rowS c d x)) q.val = ofField (fun x => n₂ (rowS c d x)) q.val) :
    ofField (rowEntry c d K m m₁ m₂) q.val = ofField (rowEntry c d K n n₁ n₂) q.val := by
  have hS := contDiffAt_rowS hden q
  have hg := contDiffAt_rowSq hden q
  have e : ∀ (u u₁ u₂ : ℝ → ℂ), ContDiffAt ℝ 2 u (rowS c d q.val) → ContDiffAt ℝ 2 u₁ (rowS c d q.val) →
      ContDiffAt ℝ 2 u₂ (rowS c d q.val) → ofField (rowEntry c d K u u₁ u₂) q.val =
        (((ofField (fun x => rowSq c d x * K.A x) q.val).mul (ofField (fun x => u (rowS c d x)) q.val)).add
          ((ofField (fun x => rowSq c d x * K.B x) q.val).mul (ofField (fun x => u₁ (rowS c d x)) q.val))).add
          ((ofField (fun x => rowSq c d x * K.C x) q.val).mul (ofField (fun x => u₂ (rowS c d x)) q.val)) := by
    intro u u₁ u₂ hu hu₁ hu₂
    have a0 : ContDiffAt ℝ 2 (fun x => u (rowS c d x)) q.val := hu.comp q.val hS
    have a1 : ContDiffAt ℝ 2 (fun x => u₁ (rowS c d x)) q.val := hu₁.comp q.val hS
    have a2 : ContDiffAt ℝ 2 (fun x => u₂ (rowS c d x)) q.val := hu₂.comp q.val hS
    have gA := hg.mul hK.1
    have gB := hg.mul hK.2.1
    have gC := hg.mul hK.2.2
    change ofField (fun x => rowSq c d x * K.A x * u (rowS c d x) + rowSq c d x * K.B x * u₁ (rowS c d x) +
      rowSq c d x * K.C x * u₂ (rowS c d x)) q.val = _
    rw [ofField_add ((gA.mul a0).add (gB.mul a1)) (gC.mul a2), ofField_add (gA.mul a0) (gB.mul a1),
      ofField_mul gA a0, ofField_mul gB a1, ofField_mul gC a2]
  rw [e m m₁ m₂ hm hm₁ hm₂, e n n₁ n₂ hn hn₁ hn₂, h0, h1, h2]

include hden in
theorem contDiffAt_scalarRow (hm : ContDiffAt ℝ 2 m (rowS c d q.val))
    (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val)) (hm₂ : ContDiffAt ℝ 2 m₂ (rowS c d q.val)) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun x => scalarRow c d m m₁ m₂ x a b) q.val := by
  have hT := contDiffAt_rowEntry hden q (regular_TT q) hm hm₁ hm₂
  have hR := contDiffAt_rowEntry hden q (regular_TR q) hm hm₁ hm₂
  have hRR := contDiffAt_rowEntry hden q (regular_RR q) hm hm₁ hm₂
  have hA := contDiffAt_rowEntry hden q (regular_AA q) hm hm₁ hm₂
  fin_cases a <;> fin_cases b
  all_goals first | exact contDiffAt_const | exact hT | exact hR | exact hRR | exact hA

include hden in
/-- **The jet of the scalar perturbation depends only on finitely many derivatives.** -/
theorem scalarRow_congr_jet (hm : ContDiffAt ℝ 2 m (rowS c d q.val))
    (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val)) (hm₂ : ContDiffAt ℝ 2 m₂ (rowS c d q.val))
    (hn : ContDiffAt ℝ 2 n (rowS c d q.val)) (hn₁ : ContDiffAt ℝ 2 n₁ (rowS c d q.val))
    (hn₂ : ContDiffAt ℝ 2 n₂ (rowS c d q.val))
    (h0 : ofField (fun x => m (rowS c d x)) q.val = ofField (fun x => n (rowS c d x)) q.val)
    (h1 : ofField (fun x => m₁ (rowS c d x)) q.val = ofField (fun x => n₁ (rowS c d x)) q.val)
    (h2 : ofField (fun x => m₂ (rowS c d x)) q.val = ofField (fun x => n₂ (rowS c d x)) q.val) :
    ofMetricField (scalarRow c d m m₁ m₂) q.val = ofMetricField (scalarRow c d n n₁ n₂) q.val := by
  have hE := fun (K : Coeff) (hK : K.Regular q.val) =>
    ofField_rowEntry_congr hden q hK hm hm₁ hm₂ hn hn₁ hn₂ h0 h1 h2
  have hT := hE _ (regular_TT q)
  have hR := hE _ (regular_TR q)
  have hRR := hE _ (regular_RR q)
  have hA := hE _ (regular_AA q)
  unfold ofMetricField
  congr 1
  funext a b
  fin_cases a <;> fin_cases b
  all_goals first
    | exact (ofField_constant 0 q.val).trans (ofField_constant 0 q.val).symm
    | exact hT | exact hR | exact hRR | exact hA

end Smooth

/-! ### The exponential case -/

section Exponential

variable {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y) (s a : ℂ)

theorem bm_phase {r : ℝ} (hr : 1 < r) :
    Complex.log (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)) = 2 * (((radialPhase r + Real.log 2 : ℝ)) : ℂ) := by
  have hr0 : 0 < r := by linarith
  have hpos : 0 < 1 - (r⁻¹) ^ 2 := by
    have : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    have h0 : 0 < r⁻¹ := inv_pos.mpr hr0
    nlinarith
  have hc : (1 - (r : ℂ)⁻¹ ^ (2 : ℕ)) = ((1 - (r⁻¹) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, ← Complex.ofReal_log hpos.le, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
  congr 1
  have hF : 0 < r ^ 2 - 1 := by nlinarith
  have heq : 1 - (r⁻¹) ^ 2 = (r ^ 2 - 1) / r ^ 2 := by
    field_simp
  rw [heq, Real.log_div hF.ne' (by positivity), Real.log_pow, radialPhase,
    Real.log_mul (by norm_num) hr0.ne']
  push_cast
  ring

/-- The envelope in the hyperboloidal time. -/
theorem envelope_eq {x : Fin 4 → ℝ} (hr : 1 < x 1) :
    D4BMFundamentalScalarMetric.envelope s (a * Complex.exp (-(s * (Real.log 2 : ℝ)))) x =
      a * Complex.exp (s * ((x 0 + radialPhase (x 1) : ℝ) : ℂ)) := by
  rw [D4BMFundamentalScalarMetric.envelope_eq_exp, bmCoordinate, bm_phase hr, mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The eigenfunction `s_γ^{s+2}`, as the potential of the vector sector. -/
def rowScalar (c d : ℝ) (s : ℂ) : Field := rowPotential c d (s + 1) (s + 2)

theorem rowScalar_apply (hs : s + 2 ≠ 0) (z : Point) :
    rowScalar c d s z = Complex.exp ((s + 2) * ((Real.log (rowHgt c d (z 0) (z 1)) : ℝ) : ℂ)) := by
  have h1 : s + 1 + 1 = s + 2 := by ring
  rw [rowScalar, rowPotential, h1, mul_inv_cancel₀ hs, one_mul]

include hden in
/-- **The perturbation of an exponential is the corpus scalar mode.** -/
theorem scalarRow_exp (hs : s + 2 ≠ 0) {x : Fin 4 → ℝ} (hr : 1 < x 1) (hy : 0 < x 3) :
    scalarRow c d (fun S => a * Complex.exp (s * S)) (fun S => a * (s * Complex.exp (s * S)))
      (fun S => a * (s ^ 2 * Complex.exp (s * S))) x =
      D4BMFundamentalScalarMetric.field s (a * Complex.exp (-(s * (Real.log 2 : ℝ)))) (rowScalar c d s) x := by
  have hspos := rowHgt_pos' hden (c := c) (d := d) (x := x 2) hy
  have hsC : ((rowHgt c d (x 2) (x 3) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hlog : ((rowHgt c d (x 2) (x 3) : ℝ) : ℂ) = Complex.exp ((Real.log (rowHgt c d (x 2) (x 3)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hspos]
  have hK : D4BMFundamentalScalarMetric.envelope s (a * Complex.exp (-(s * (Real.log 2 : ℝ)))) x *
      rowScalar c d s (angularPoint x) =
      rowSq c d x * (a * Complex.exp (s * ((rowS c d x : ℝ) : ℂ))) := by
    rw [envelope_eq s a hr, rowScalar_apply s hs]
    change _ * Complex.exp ((s + 2) * ((Real.log (rowHgt c d (x 2) (x 3)) : ℝ) : ℂ)) = _
    have e1 : Complex.exp ((s + 2) * ((Real.log (rowHgt c d (x 2) (x 3)) : ℝ) : ℂ)) =
        rowSq c d x * Complex.exp (s * ((Real.log (rowHgt c d (x 2) (x 3)) : ℝ) : ℂ)) := by
      rw [rowSq, hlog, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have e2 : Complex.exp (s * ((rowS c d x : ℝ) : ℂ)) = Complex.exp (s * ((x 0 + radialPhase (x 1) : ℝ) : ℂ)) *
        Complex.exp (s * ((Real.log (rowHgt c d (x 2) (x 3)) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [rowS]
      push_cast
      ring
    rw [e1, e2]
    ring
  set E := Complex.exp (s * ((rowS c d x : ℝ) : ℂ)) with hE
  have hentry : ∀ K : Coeff, rowEntry c d K (fun S => a * Complex.exp (s * S))
      (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S))) x =
      rowSq c d x * (a * E) * (K.A x + K.B x * s + K.C x * s ^ 2) := fun K => by
    simp only [rowEntry, hE]
    ring
  have hTT : rowEntry c d coeffTT (fun S => a * Complex.exp (s * S))
      (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S))) x =
      rowSq c d x * (a * E) * (s * (s - 3) / 2 + s * (s + 1) / (2 * (x 1 : ℂ) ^ (2 : ℕ))) := by
    rw [hentry]
    simp only [coeffTT, rC]
    ring
  have hTR : rowEntry c d coeffTR (fun S => a * Complex.exp (s * S))
      (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S))) x =
      rowSq c d x * (a * E) * (-s * ((x 1 : ℂ) ^ (2 : ℕ) - s) / ((x 1 : ℂ) * ((x 1 : ℂ) ^ (2 : ℕ) - 1))) := by
    rw [hentry]
    simp only [coeffTR, rC]
    ring
  have hRR : rowEntry c d coeffRR (fun S => a * Complex.exp (s * S))
      (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S))) x =
      rowSq c d x * (a * E) * ((s * (s - 3) / 2 + s * (s + 1) / (2 * (x 1 : ℂ) ^ (2 : ℕ))) /
        ((x 1 : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ)) := by
    rw [hentry]
    simp only [coeffRR, rC]
    ring
  have hAA : rowEntry c d coeffAA (fun S => a * Complex.exp (s * S))
      (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S))) x =
      rowSq c d x * (a * E) * ((-(x 1 : ℂ) ^ (2 : ℕ) - s * (s + 1) / 2) * (x 3 : ℂ)⁻¹ ^ (2 : ℕ)) := by
    rw [hentry]
    simp only [coeffAA, rC, yC]
    ring
  rw [D4BMFundamentalScalarMetric.field, hK]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hTT | exact hTR | exact hRR | exact hAA | exact (mul_zero _).symm

include hden in
/-- The exponential perturbation is vacuum, by the corpus reconstruction. -/
theorem vac_scalar_row (hs : s + 2 ≠ 0) (q : D4BMBackground.ExteriorPoint) :
    Vac (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (scalarRow c d (fun S => a * Complex.exp (s * S))
        (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S)))) q.val) := by
  have hgerm : scalarRow c d (fun S => a * Complex.exp (s * S))
      (fun S => a * (s * Complex.exp (s * S))) (fun S => a * (s ^ 2 * Complex.exp (s * S))) =ᶠ[𝓝 q.val]
      D4BMFundamentalScalarMetric.field s (a * Complex.exp (-(s * (Real.log 2 : ℝ)))) (rowScalar c d s) := by
    have hopen : {x : Fin 4 → ℝ | 1 < x 1 ∧ 0 < x 3} ∈ 𝓝 q.val :=
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt continuous_const (continuous_apply 3))).mem_nhds q.property
    filter_upwards [hopen] with x hx
    exact scalarRow_exp hden s a hs hx.1 hx.2
  rw [ofMetricField_congr_germ hgerm]
  intro i j
  have hz : 0 < angularPoint q.val 1 := q.property.2
  have hw : s + 1 + 1 ≠ 0 := by
    have : s + 1 + 1 = s + 2 := by ring
    rwa [this]
  have hR := D4BMScalarLinearEquation.field_residual_zero s (a * Complex.exp (-(s * (Real.log 2 : ℝ))))
    (rowScalar c d s) q (contDiffAt_rowPotential hden _ _ hz) (by
      rw [scalarLaplacian_eq _ _ hz, rowScalar, rowPotential_eigen hden (s + 1) (s + 2) hw hz]
      ring_nf) i j
  rw [D4BMLinearizedEinsteinSource.residual, D4BMBackground.actualJet_eq] at hR
  exact hR

end Exponential

/-! ### Interpolation with five exponentials -/

/-- The exponent `j`. -/
def rate5 (j : Fin 5) : ℂ := ((j : ℕ) : ℂ)

/-- The sum `Σ_j a_j j^n e^{jS}`. -/
def expSum5 (a : Fin 5 → ℂ) (n : ℕ) (S : ℝ) : ℂ :=
  ∑ j, a j * (rate5 j ^ n * Complex.exp (rate5 j * S))

theorem hasDerivAt_expSum5 (a : Fin 5 → ℂ) (n : ℕ) (S : ℝ) :
    HasDerivAt (expSum5 a n) (expSum5 a (n + 1) S) S := by
  have h : HasDerivAt (fun S : ℝ => ∑ j, a j * (rate5 j ^ n * Complex.exp (rate5 j * S)))
      (∑ j, a j * (rate5 j ^ n * (rate5 j * Complex.exp (rate5 j * S)))) S :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_exp_real_mul (rate5 j) S).const_mul (rate5 j ^ n)).const_mul (a j)
  refine h.congr_deriv (Finset.sum_congr rfl fun j _ => ?_)
  ring

theorem deriv_expSum5 (a : Fin 5 → ℂ) (n : ℕ) : deriv (expSum5 a n) = expSum5 a (n + 1) :=
  funext fun S => (hasDerivAt_expSum5 a n S).deriv

theorem contDiff_expSum5 (a : Fin 5 → ℂ) (n : ℕ) : ContDiff ℝ 2 (expSum5 a n) := by
  unfold expSum5
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_const.mul (contDiff_exp_real_mul _))

theorem exists_expSum5_eq (b : Fin 5 → ℂ) (S₀ : ℝ) :
    ∃ a : Fin 5 → ℂ, ∀ n : Fin 5, expSum5 a n S₀ = b n := by
  have hinj : Function.Injective rate5 := fun i j h => by
    have h' : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := h
    have : (i : ℕ) = j := by exact_mod_cast h'
    exact Fin.ext this
  set A := Matrix.transpose (Matrix.vandermonde rate5) with hA
  have hdet : A.det ≠ 0 := by
    rw [hA, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  set e := A⁻¹.mulVec b with he
  have hsol : A.mulVec e = b := by
    rw [he, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  refine ⟨fun j => e j * Complex.exp (-(rate5 j * S₀)), fun n => ?_⟩
  have h := congrFun hsol n
  rw [← h]
  simp only [expSum5, Matrix.mulVec, dotProduct, hA, Matrix.transpose_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : Complex.exp (-(rate5 j * S₀)) * Complex.exp (rate5 j * S₀) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (e j * rate5 j ^ (n : ℕ)) * hc

section Main

variable {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y) (q : D4BMBackground.ExteriorPoint)

include hden

/-- A sum of exponentials has a vacuum perturbation. -/
theorem vac_scalarRow_expSum (a : Fin 5 → ℂ) :
    Vac (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (scalarRow c d (expSum5 a 0) (expSum5 a 1) (expSum5 a 2)) q.val) := by
  set g : Fin 5 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ := fun j =>
    scalarRow c d (fun S => a j * Complex.exp (rate5 j * S))
      (fun S => a j * (rate5 j * Complex.exp (rate5 j * S)))
      (fun S => a j * (rate5 j ^ 2 * Complex.exp (rate5 j * S))) with hg
  have hsum : scalarRow c d (expSum5 a 0) (expSum5 a 1) (expSum5 a 2) = fun x => ∑ j, (1 : ℂ) • g j x := by
    funext x
    have hE : ∀ K : Coeff, rowEntry c d K (expSum5 a 0) (expSum5 a 1) (expSum5 a 2) x =
        ∑ j, rowEntry c d K (fun S => a j * Complex.exp (rate5 j * S))
          (fun S => a j * (rate5 j * Complex.exp (rate5 j * S)))
          (fun S => a j * (rate5 j ^ 2 * Complex.exp (rate5 j * S))) x := fun K => by
      simp only [rowEntry, expSum5, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    ext u v
    simp only [one_smul, Matrix.sum_apply, hg]
    fin_cases u <;> fin_cases v
    all_goals first
      | (simp [scalarRow]; done)
      | exact hE _
  rw [hsum]
  have h0 (j : Fin 5) : ContDiffAt ℝ 2 (fun S : ℝ => a j * Complex.exp (rate5 j * S)) (rowS c d q.val) :=
    contDiffAt_const.mul (contDiff_exp_real_mul _).contDiffAt
  have h1 (j : Fin 5) : ContDiffAt ℝ 2 (fun S : ℝ => a j * (rate5 j * Complex.exp (rate5 j * S)))
      (rowS c d q.val) :=
    contDiffAt_const.mul (contDiffAt_const.mul (contDiff_exp_real_mul _).contDiffAt)
  have h2 (j : Fin 5) : ContDiffAt ℝ 2 (fun S : ℝ => a j * (rate5 j ^ 2 * Complex.exp (rate5 j * S)))
      (rowS c d q.val) :=
    contDiffAt_const.mul (contDiffAt_const.mul (contDiff_exp_real_mul _).contDiffAt)
  refine vac_sum _ Finset.univ _ g
    (fun j _ u v => contDiffAt_scalarRow hden q (h0 j) (h1 j) (h2 j) u v) (fun j _ => ?_)
  have hs : rate5 j + 2 ≠ 0 := by
    have : rate5 j + 2 = (((j : ℕ) + 2 : ℕ) : ℂ) := by
      simp [rate5]
    rw [this]
    exact_mod_cast (by omega : (j : ℕ) + 2 ≠ 0)
  exact vac_scalar_row hden (rate5 j) (a j) hs q

/-- **The scalar perturbation of a row is vacuum, for every `C⁴` function.** -/
theorem scalarRow_vacuum {m : ℝ → ℂ} (hm : ContDiffAt ℝ 4 m (rowS c d q.val)) :
    Vac (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (scalarRow c d m (deriv m) (deriv (deriv m))) q.val) := by
  set S₀ := rowS c d q.val with hS₀
  have hm3 : ContDiffAt ℝ 3 m S₀ := hm.of_le (by norm_num)
  have hm2 : ContDiffAt ℝ 2 m S₀ := hm.of_le (by norm_num)
  have hd : ContDiffAt ℝ 3 (deriv m) S₀ := by
    have h := (hm.fderiv_right (m := 3) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : ℝ)))
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => (fderiv_apply_one_eq_deriv).symm)
  have hd2 : ContDiffAt ℝ 2 (deriv m) S₀ := hd.of_le (by norm_num)
  have hdd : ContDiffAt ℝ 2 (deriv (deriv m)) S₀ := contDiffAt_deriv_two hd
  obtain ⟨a, ha⟩ := exists_expSum5_eq ![m S₀, deriv m S₀, deriv (deriv m) S₀, deriv (deriv (deriv m)) S₀,
    deriv (deriv (deriv (deriv m))) S₀] S₀
  have h0 : expSum5 a 0 S₀ = m S₀ := ha 0
  have h1 : expSum5 a 1 S₀ = deriv m S₀ := ha 1
  have h2 : expSum5 a 2 S₀ = deriv (deriv m) S₀ := ha 2
  have h3 : expSum5 a 3 S₀ = deriv (deriv (deriv m)) S₀ := ha 3
  have h4 : expSum5 a 4 S₀ = deriv (deriv (deriv (deriv m))) S₀ := ha 4
  have hS := contDiffAt_rowS hden q
  have hn0 := (contDiff_expSum5 a 0).contDiffAt (x := S₀)
  have hn1 := (contDiff_expSum5 a 1).contDiffAt (x := S₀)
  have hn2 := (contDiff_expSum5 a 2).contDiffAt (x := S₀)
  have hjet := scalarRow_congr_jet hden q hm2 hd2 hdd hn0 hn1 hn2
    (by
      rw [ofField_comp_real hm2 hS, ofField_comp_real hn0 hS, deriv_expSum5, deriv_expSum5]
      rw [show rowS c d q.val = S₀ from rfl, h0, h1, h2])
    (by
      rw [ofField_comp_real hd2 hS, ofField_comp_real hn1 hS, deriv_expSum5, deriv_expSum5]
      rw [show rowS c d q.val = S₀ from rfl, h1, h2, h3])
    (by
      rw [ofField_comp_real hdd hS, ofField_comp_real hn2 hS, deriv_expSum5, deriv_expSum5]
      rw [show rowS c d q.val = S₀ from rfl, h2, h3, h4])
  rw [hjet]
  exact vac_scalarRow_expSum hden q a

end Main

/-! ### The sum over rows -/

namespace CompactPulse

/-- The profile `m(S) = e^{-3S/2} h(S)`. -/
def scalarProfile (h : CompactPulse) : CompactPulse where
  toFun S := Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) * h S
  smooth := (contDiff_exp_real_mul _).mul h.smooth
  compact := h.compact.mul_left

theorem hasDerivAt_scalarProfile (h : CompactPulse) (S : ℝ) :
    HasDerivAt h.scalarProfile (Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) * (h.D S - (3 / 2 : ℂ) * h S)) S := by
  refine ((hasDerivAt_exp_real_mul (-(3 / 2 : ℂ)) S).mul (h.hasDerivAt S)).congr_deriv ?_
  ring

theorem scalarProfile_D (h : CompactPulse) (S : ℝ) :
    h.scalarProfile.D S = Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) * (h.D S - (3 / 2 : ℂ) * h S) :=
  (h.hasDerivAt_scalarProfile S).deriv

theorem scalarProfile_DD (h : CompactPulse) (S : ℝ) :
    h.scalarProfile.D.D S = Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) *
      (h.D.D S - 3 * h.D S + (9 / 4 : ℂ) * h S) := by
  have he : (h.scalarProfile.D : ℝ → ℂ) =
      fun S : ℝ => Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) * (h.D S - (3 / 2 : ℂ) * h S) :=
    funext h.scalarProfile_D
  have h1 := (hasDerivAt_exp_real_mul (-(3 / 2 : ℂ)) S).mul
    ((h.D.hasDerivAt S).sub ((h.hasDerivAt S).const_mul (3 / 2 : ℂ)))
  have h2 : HasDerivAt (fun S : ℝ => Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) * (h.D S - (3 / 2 : ℂ) * h S))
      (Complex.exp (-(3 / 2 : ℂ) * (S : ℂ)) * (h.D.D S - 3 * h.D S + (9 / 4 : ℂ) * h S)) S := by
    refine HasDerivAt.congr_deriv (f' := _) h1 ?_
    simp only [Pi.sub_apply]
    ring
  change deriv (h.scalarProfile.D : ℝ → ℂ) S = _
  rw [he]
  exact h2.deriv

/-- The pulse `α h + β h' + γ h''`. -/
def pulseComb (α β γ : ℂ) (h : CompactPulse) : CompactPulse where
  toFun S := α * h S + β * h.D S + γ * h.D.D S
  smooth := ((contDiff_const.mul h.smooth).add (contDiff_const.mul h.D.smooth)).add
    (contDiff_const.mul h.D.D.smooth)
  compact := ((h.compact.mul_left (f := fun _ => α)).add (h.D.compact.mul_left (f := fun _ => β))).add
    (h.D.D.compact.mul_left (f := fun _ => γ))

theorem pulseAmplitude_comb (α β γ : ℂ) (h : CompactPulse) (w : ℂ) :
    pulseAmplitude (pulseComb α β γ h) w = (α + β * (I * w) + γ * (I * w) ^ 2) * pulseAmplitude h w := by
  have hsplit : (∫ S : ℝ, (pulseComb α β γ h) S * Complex.exp (-(I * w * (S : ℂ)))) =
      α * (∫ S : ℝ, h S * Complex.exp (-(I * w * (S : ℂ)))) +
        β * (∫ S : ℝ, h.D S * Complex.exp (-(I * w * (S : ℂ)))) +
        γ * ∫ S : ℝ, h.D.D S * Complex.exp (-(I * w * (S : ℂ))) := by
    have hi1 := (h.integrable_mul_cexp w).const_mul α
    have hi2 := (h.D.integrable_mul_cexp w).const_mul β
    have hi3 := (h.D.D.integrable_mul_cexp w).const_mul γ
    have hi12 : MeasureTheory.Integrable fun S : ℝ => α * (h S * Complex.exp (-(I * w * (S : ℂ)))) +
        β * (h.D S * Complex.exp (-(I * w * (S : ℂ)))) := hi1.add hi2
    have e : (∫ S : ℝ, (pulseComb α β γ h) S * Complex.exp (-(I * w * (S : ℂ)))) =
        ∫ S : ℝ, (α * (h S * Complex.exp (-(I * w * (S : ℂ)))) +
          β * (h.D S * Complex.exp (-(I * w * (S : ℂ))))) +
            γ * (h.D.D S * Complex.exp (-(I * w * (S : ℂ)))) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun S => ?_)
      change (α * h S + β * h.D S + γ * h.D.D S) * _ = _
      ring
    rw [e, MeasureTheory.integral_add hi12 hi3, MeasureTheory.integral_add hi1 hi2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  have h1 := h.amplitude_D w
  have h2 := h.D.amplitude_D w
  rw [h1] at h2
  simp only [pulseAmplitude] at h1 h2 ⊢
  rw [hsplit, mul_add, mul_add]
  linear_combination β * h1 + γ * h2

end CompactPulse

/-- The coefficients of the pulse of an entry. -/
def Coeff.alpha (K : Coeff) (x : Fin 4 → ℝ) : ℂ := K.A x - (3 / 2 : ℂ) * K.B x + (9 / 4 : ℂ) * K.C x
def Coeff.beta (K : Coeff) (x : Fin 4 → ℝ) : ℂ := K.B x - 3 * K.C x
def Coeff.gamma (K : Coeff) (x : Fin 4 → ℝ) : ℂ := K.C x

/-- The pulse of an entry. -/
def entryPulse (K : Coeff) (h : CompactPulse) (x : Fin 4 → ℝ) : CompactPulse :=
  CompactPulse.pulseComb (K.alpha x) (K.beta x) (K.gamma x) h

/-- **The entry of the scalar wave is an image field.** -/
def scalarEntry (K : Coeff) (h : CompactPulse) (x : Fin 4 → ℝ) : ℂ :=
  Complex.exp (-(3 / 2 : ℂ) * (hyperTime x : ℂ)) * imageField (entryPulse K h x) (hyperTime x) (x 2) (x 3)

/-- **The scalar gravitational wave of a pulse.** -/
def scalarMetric (h : CompactPulse) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![scalarEntry coeffTT h x, scalarEntry coeffTR h x, 0, 0;
    scalarEntry coeffTR h x, scalarEntry coeffRR h x, 0, 0;
    0, 0, scalarEntry coeffAA h x, 0;
    0, 0, 0, scalarEntry coeffAA h x]

/-- The term of a row. -/
theorem rowEntry_profile (h : CompactPulse) (K : Coeff) {c d : ℝ} {x : Fin 4 → ℝ}
    (hs : 0 < rowHgt c d (x 2) (x 3)) :
    rowEntry c d K h.scalarProfile h.scalarProfile.D h.scalarProfile.D.D x =
      Complex.exp (-(3 / 2 : ℂ) * (hyperTime x : ℂ)) *
        imageTerm (entryPulse K h x) c d (hyperTime x) (x 2) (x 3) := by
  set s := rowHgt c d (x 2) (x 3) with hsdef
  set L := Real.log s with hL
  have hS : rowS c d x = hyperTime x + L := rfl
  have hsC : (s : ℂ) = Complex.exp ((L : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, hL, Real.exp_log hs]
  have hq : ((Real.sqrt s : ℝ) : ℂ) = Complex.exp ((L : ℂ) / 2) := by
    have h1 : Real.sqrt s = Real.exp (L / 2) := by
      rw [Real.exp_half, hL, Real.exp_log hs]
    rw [h1, Complex.ofReal_exp]
    push_cast
    rfl
  have hkey : rowSq c d x * Complex.exp (-(3 / 2 : ℂ) * ((hyperTime x + L : ℝ) : ℂ)) =
      Complex.exp (-(3 / 2 : ℂ) * (hyperTime x : ℂ)) * ((Real.sqrt s : ℝ) : ℂ) := by
    rw [rowSq, ← hsdef, hsC, hq, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [rowEntry, imageTerm, pulseF, hS, ← hsdef, ← hL]
  rw [h.scalarProfile_D, h.scalarProfile_DD]
  change _ = Complex.exp (-(3 / 2 : ℂ) * (hyperTime x : ℂ)) * (((Real.sqrt s : ℝ) : ℂ) *
    (K.alpha x * h (hyperTime x + L) + K.beta x * h.D (hyperTime x + L) + K.gamma x * h.D.D (hyperTime x + L)))
  have hprof : h.scalarProfile (hyperTime x + L) =
      Complex.exp (-(3 / 2 : ℂ) * ((hyperTime x + L : ℝ) : ℂ)) * h (hyperTime x + L) := rfl
  rw [hprof]
  simp only [Coeff.alpha, Coeff.beta, Coeff.gamma]
  linear_combination (K.A x * h (hyperTime x + L) +
    K.B x * (h.D (hyperTime x + L) - (3 / 2 : ℂ) * h (hyperTime x + L)) +
    K.C x * (h.D.D (hyperTime x + L) - 3 * h.D (hyperTime x + L) + (9 / 4 : ℂ) * h (hyperTime x + L))) * hkey

/-- Near a point only finitely many rows are active, for the pulse and its two derivatives. -/
theorem exists_finset_scalar (h : CompactPulse) (q : D4BMBackground.ExteriorPoint) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ᶠ x in 𝓝 q.val, ∀ p ∉ S,
      h (rowS (rowC p) (rowD p) x) = 0 ∧ h.D (rowS (rowC p) (rowD p) x) = 0 ∧
        h.D.D (rowS (rowC p) (rowD p) x) = 0 := by
  classical
  obtain ⟨S₁, h₁⟩ := exists_finset_metric h q
  obtain ⟨S₂, h₂⟩ := exists_finset_metric h.D q
  refine ⟨S₁ ∪ S₂, ?_⟩
  filter_upwards [h₁, h₂] with x a1 a2 p hp
  simp only [Finset.mem_union, not_or] at hp
  exact ⟨(a1 p hp.1).1, (a2 p hp.2).1, (a2 p hp.2).2⟩

/-- **The scalar gravitational wave of a pulse is an exact vacuum perturbation.** -/
theorem scalarMetric_vacuum (h : CompactPulse) (q : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (scalarMetric h) q.val) (-3) i j = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_scalar h q
  set m := h.scalarProfile with hm
  have hopen : ∀ᶠ x : Fin 4 → ℝ in 𝓝 q.val, 0 < x 3 :=
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds q.property.2
  have hgerm : scalarMetric h =ᶠ[𝓝 q.val] fun x => ∑ p ∈ S, (1 / 2 : ℂ) •
      scalarRow (rowC p) (rowD p) m m.D m.D.D x := by
    filter_upwards [hS, hopen] with x hx hy
    have hE : ∀ K : Coeff, scalarEntry K h x =
        (1 / 2 : ℂ) * ∑ p ∈ S, rowEntry (rowC p) (rowD p) K m m.D m.D.D x := fun K => by
      rw [scalarEntry, imageField, tsum_eq_sum (s := S) fun p hp => ?_, mul_left_comm, Finset.mul_sum]
      · congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [rowEntry_profile h K (rowHgt_pos_row p (x 2) hy)]
      · obtain ⟨a0, a1, a2⟩ := hx p hp
        simp only [rowS_eq] at a0 a1 a2
        change _ * ((K.alpha x * h _ + K.beta x * h.D _ + K.gamma x * h.D.D _)) = 0
        rw [a0, a1, a2]
        simp
    ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    fin_cases u <;> fin_cases v
    all_goals first
      | (simp [scalarRow, scalarMetric]; done)
      | exact hE _
  rw [ofMetricField_congr_germ hgerm]
  have hm4 : ∀ s, ContDiffAt ℝ 4 m s := fun s => by
    exact_mod_cast (contDiff_infty.mp m.smooth 4).contDiffAt
  have hm2 : ∀ s, ContDiffAt ℝ 2 m s := fun s => (hm4 s).of_le (by norm_num)
  have hm1 : ∀ s, ContDiffAt ℝ 2 m.D s := fun s => by
    exact_mod_cast (contDiff_infty.mp m.D.smooth 2).contDiffAt
  have hm0 : ∀ s, ContDiffAt ℝ 2 m.D.D s := fun s => by
    exact_mod_cast (contDiff_infty.mp m.D.D.smooth 2).contDiffAt
  exact vac_sum _ S (fun _ => (1 / 2 : ℂ)) (fun p => scalarRow (rowC p) (rowD p) m m.D m.D.D)
    (fun p _ a b => contDiffAt_scalarRow (fun x y hy => rowDen_pos p x hy) q (hm2 _) (hm1 _) (hm0 _) a b)
    (fun p _ => scalarRow_vacuum (fun x y hy => rowDen_pos p x hy) q (hm4 _)) i j

/-! ### The ringdown of the scalar wave -/

/-- **The ringdown of an entry**: a constant times `e^{-τ}`, the modes of the zeros, and a remainder below every exponential. -/
theorem image_scalar_ringdown (g : CompactPulse) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ τ : ℝ, Tendsto (fun k => Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) *
          contourPartial (pulseNumerator g x y) τ k) atTop
        (𝓝 (Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) * imageField g τ x y -
          Complex.exp (-(τ : ℂ)) * meanCoefficient g - Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) * Rem τ)) := by
  obtain ⟨Rem, hRem, hlim⟩ := pulse_ringdown g x hy
  refine ⟨Rem, hRem, fun τ => ?_⟩
  have hat := (hlim |τ| (abs_nonneg τ)).tendsto_at (neg_abs_le τ : τ ∈ Ici (-|τ|))
  have h2 := hat.const_mul (Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)))
  have hval : Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) * (pulsePacket g τ x y - Rem τ) =
      Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) * imageField g τ x y -
        Complex.exp (-(τ : ℂ)) * meanCoefficient g - Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) * Rem τ := by
    have he : Complex.exp (-(3 / 2 : ℂ) * (τ : ℂ)) * Complex.exp ((τ : ℂ) / 2) = Complex.exp (-(τ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [imageField_eq_packet g τ x hy]
    linear_combination (-meanCoefficient g) * he
  rw [hval] at h2
  exact h2

/-- The coefficients of the entries depend only on `r` and `y`. -/
def Coeff.Static (K : Coeff) : Prop :=
  ∀ t t' r x y, K.A (chart4 t r x y) = K.A (chart4 t' r x y) ∧
    K.B (chart4 t r x y) = K.B (chart4 t' r x y) ∧ K.C (chart4 t r x y) = K.C (chart4 t' r x y)

theorem static_TT : coeffTT.Static := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩
theorem static_TR : coeffTR.Static := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩
theorem static_RR : coeffRR.Static := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩
theorem static_AA : coeffAA.Static := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- The entry at a fixed point of the horizon and a fixed radius. -/
theorem entryPulse_static {K : Coeff} (hK : K.Static) (h : CompactPulse) (t r x y : ℝ) :
    entryPulse K h (chart4 t r x y) = entryPulse K h (chart4 0 r x y) := by
  obtain ⟨a, b, c⟩ := hK t 0 r x y
  simp only [entryPulse, Coeff.alpha, Coeff.beta, Coeff.gamma, a, b, c]

/-- **The ringdown of the scalar wave, entry by entry.** -/
theorem scalarEntry_ringdown {K : Coeff} (hK : K.Static) (h : CompactPulse) (r x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      ∀ t : ℝ, Tendsto (fun k => Complex.exp (-(3 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
          contourPartial (pulseNumerator (entryPulse K h (chart4 0 r x y)) x y) (t + radialPhase r) k) atTop
        (𝓝 (scalarEntry K h (chart4 t r x y) -
          Complex.exp (-((t + radialPhase r : ℝ) : ℂ)) * meanCoefficient (entryPulse K h (chart4 0 r x y)) -
          Complex.exp (-(3 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) * Rem (t + radialPhase r))) := by
  obtain ⟨Rem, hRem, hlim⟩ := image_scalar_ringdown (entryPulse K h (chart4 0 r x y)) x hy
  refine ⟨Rem, hRem, fun t => ?_⟩
  have hval : scalarEntry K h (chart4 t r x y) =
      Complex.exp (-(3 / 2 : ℂ) * ((t + radialPhase r : ℝ) : ℂ)) *
        imageField (entryPulse K h (chart4 0 r x y)) (t + radialPhase r) x y := by
    rw [scalarEntry, entryPulse_static hK]
    rfl
  rw [hval]
  exact hlim (t + radialPhase r)

/-- **The modes of the scalar wave**: at a zero `p`, with `s = p - 3/2`, the top coefficient vanishes exactly when
`A + B s + C s²`, the amplitude or the numerator does. -/
theorem scalarEntry_mode (K : Coeff) (h : CompactPulse) (X : Fin 4 → ℝ) (x : ℝ) {y : ℝ} (hy : 0 < y) {p : ℂ}
    (hp : xi (1 + 2 * p) = 0) :
    ∃ (n : ℕ) (e : ℕ → ℂ),
      analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p = ((n + 1 : ℕ) : ℕ∞) ∧
      (e 0 = 0 ↔ K.A X + K.B X * (p - 3 / 2) + K.C X * (p - 3 / 2) ^ 2 = 0 ∨
        pulseAmplitude h (-I * p) = 0 ∨ eisensteinNumerator p x y = 0) ∧
      ∀ τ : ℝ, laurentCoeff (inverseXiQuotient (timeNumerator (pulseNumerator (entryPulse K h X) x y) τ))
          p (-1) = Complex.exp (p * (τ : ℂ)) * ∑ j ∈ Finset.range (n + 1),
            e j * (τ : ℂ) ^ (n - j) / ((n - j).factorial : ℂ) := by
  obtain ⟨n, e, h1, h2, h3⟩ := exists_pulseMode (entryPulse K h X) x hy hp
  refine ⟨n, e, h1, ?_, h3⟩
  rw [h2, entryPulse, CompactPulse.pulseAmplitude_comb]
  have hI : I * (-I * p) = p := by linear_combination (-p) * I_sq
  rw [hI, mul_eq_zero, or_assoc]
  have hpoly : K.alpha X + K.beta X * p + K.gamma X * p ^ 2 =
      K.A X + K.B X * (p - 3 / 2) + K.C X * (p - 3 / 2) ^ 2 := by
    simp only [Coeff.alpha, Coeff.beta, Coeff.gamma]
    ring
  rw [hpoly]

end GaloisForLFunctions.BlackHoleRingdown

end
