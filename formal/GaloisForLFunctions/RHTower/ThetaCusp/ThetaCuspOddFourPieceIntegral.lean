import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourPieceSetup
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourNativeBulk

/-!
# Piece certificates under the seam-split integral

On the ray `q = π e^r` a positive semidefinite piece matrix with compensation `X` bounds the odd
fibre form below by `−κ(r)·q·F_X(q,v)`, where `κ(r) = 4q²e^{r/2−2q}·8(2q−3)²` and
`F_X(q,v) = yᵀXy` with `y = coordinates q v`, a polynomial in `q`. On a seam piece (`X ⪰ 0`)
this bounds `r²·min(f,0)` from below by `−Ω·q·F_X`, with `Ω ≥ r²κ` on the piece; on a bulk piece
(`X ⪯ 0`) it makes `f ≥ 0` with reserve `Ω·q·(−F_X)`, with `Ω ≤ r²κ`. Against `π e^r dr = dq`
the polynomial `F_X` integrates exactly.
-/

namespace RHTower.ThetaCuspOddFourPieces
noncomputable section
open MeasureTheory Set intervalIntegral
open ThetaCuspOddCentral ThetaCuspOddCentralTail ThetaCuspOddFourCentralEntries
  ThetaCuspOddFourCentralBound ThetaCuspOddFourNativeBulk ThetaCuspOddFourCertificateTools

/-- The center scale at `x = r/2` is `π e^r`. -/
theorem scale_half (r : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 (r/2) = Real.pi * Real.exp r := by
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one]
  rw [show 2*(r/2) = r by ring]

theorem coordinates_0 (q : ℝ) (c : Fin 4 → ℝ) : coordinates q c 0 =
    c 0 - (4-24*q)*(c 1 - (20-80*q)*(c 2 - (56-168*q)*c 3) - (784-3360*q+6720*q^2)*c 3) -
      (64-320*q+960*q^2)*(c 2 - (56-168*q)*c 3) - (2304-10752*q+26880*q^2-53760*q^3)*c 3 := rfl
theorem coordinates_1 (q : ℝ) (c : Fin 4 → ℝ) : coordinates q c 1 =
    -24*q*(c 1 - (20-80*q)*(c 2 - (56-168*q)*c 3) - (784-3360*q+6720*q^2)*c 3) := rfl
theorem coordinates_2 (q : ℝ) (c : Fin 4 → ℝ) : coordinates q c 2 =
    768*q^2*(c 2 - (56-168*q)*c 3) := rfl
theorem coordinates_3 (q : ℝ) (c : Fin 4 → ℝ) : coordinates q c 3 = -43008*q^3*c 3 := rfl

/-- The compensation form in the moving frame: `yᵀXy` with `y = coordinates q v`. -/
def frameForm (X : Fin 4 → Fin 4 → ℝ) (q : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, coordinates q v i * coordinates q v j * X i j

theorem frameForm_eq (X : Fin 4 → Fin 4 → ℝ) (q : ℝ) (v : Fin 4 → ℝ) :
    frameForm X q v = ∑ i : Fin 4, ∑ j : Fin 4,
      ![coordinates q v 0, coordinates q v 1, coordinates q v 2, coordinates q v 3] i *
      ![coordinates q v 0, coordinates q v 1, coordinates q v 2, coordinates q v 3] j * X i j := by
  unfold frameForm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem continuous_frameForm (X : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    Continuous fun q => frameForm X q v := by
  simp only [frameForm, Fin.sum_univ_four, coordinates_0, coordinates_1, coordinates_2,
    coordinates_3]
  fun_prop

/-- The piece kernel `4q²e^{r/2−2q}·8(2q−3)²` at `q = π e^r`. -/
def pieceKernel (r : ℝ) : ℝ :=
  4*(Real.pi*Real.exp r)^2*Real.exp (r/2 - 2*(Real.pi*Real.exp r)) *
    (8*(2*(Real.pi*Real.exp r)-3)^2)

theorem pieceKernel_nonneg (r : ℝ) : 0 ≤ pieceKernel r := by unfold pieceKernel; positivity

/-- The odd fibre form is the native odd reflection block at center `r/2`. -/
theorem fibreForm_eq_native (r : ℝ) (v : Fin 4 → ℝ) :
    thetaCuspOddFourFibreForm r v = ∑ i : Fin 4, ∑ j : Fin 4, v i*v j*(-1:ℝ)^(i.val+j.val+1)*
      thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) (r/2) := by
  unfold thetaCuspOddFourFibreForm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show 2*(i.val+j.val)+2 = 2*(i.val+j.val+1) by ring, signedJet_even_eq]
  ring

/-- **Pointwise bound from a piece.** A positive semidefinite piece matrix at `q = π e^r` bounds
the odd fibre form below by `−κ(r)·q·F_X(q,v)`. -/
theorem fibreForm_ge_of_piece {r : ℝ} (hr : 0 ≤ r) {X : Fin 4 → Fin 4 → ℝ} (v : Fin 4 → ℝ)
    (hW : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j *
      pieceW (Real.pi*Real.exp r) X i j) :
    -(pieceKernel r * (Real.pi*Real.exp r) * frameForm X (Real.pi*Real.exp r) v) ≤
      thetaCuspOddFourFibreForm r v := by
  have hs := scale_half r
  have hq3 : 3 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2) := by
    rw [hs]; nlinarith [Real.add_one_le_exp r, Real.pi_gt_three]
  have hq0 : Real.pi*Real.exp r ≠ 0 := by positivity
  have h := nativeOddForm_ge_of_piece hq3 X (coordinates (Real.pi*Real.exp r) v)
    (by rw [hs]; exact hW _)
  dsimp only at h
  rw [hs, centralBasis_coordinates' hq0] at h
  rw [fibreForm_eq_native]
  refine le_trans (le_of_eq ?_) h
  unfold pieceKernel frameForm
  ring

/-- On a bulk piece (`X ⪯ 0`) the odd fibre form is nonnegative. -/
theorem fibreForm_nonneg_of_bulk {r : ℝ} (hr : 0 ≤ r) {X : Fin 4 → Fin 4 → ℝ}
    (hX : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-X i j))
    (hW : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j *
      pieceW (Real.pi*Real.exp r) X i j) (v : Fin 4 → ℝ) :
    0 ≤ thetaCuspOddFourFibreForm r v := by
  have h := fibreForm_ge_of_piece hr v hW
  have hF : frameForm X (Real.pi*Real.exp r) v ≤ 0 := by
    have := hX (coordinates (Real.pi*Real.exp r) v)
    unfold frameForm
    simp only [mul_neg, Finset.sum_neg_distrib] at this
    linarith
  have hk := pieceKernel_nonneg r
  have hq : 0 ≤ Real.pi*Real.exp r := by positivity
  nlinarith [mul_nonneg hk hq]

/-- `∫ π e^r P(π e^r) dr = ∫ P(q) dq` for a polynomial `P` given by its coefficients. -/
theorem integral_exp_poly (c : ℕ → ℝ) (n : ℕ) (a b : ℝ) :
    ∫ r in a..b, Real.pi*Real.exp r * ∑ e ∈ Finset.range n, c e * (Real.pi*Real.exp r)^e =
      ∑ e ∈ Finset.range n,
        c e * ((Real.pi*Real.exp b)^(e+1) - (Real.pi*Real.exp a)^(e+1)) / (e+1) := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt
      (fun r => ∑ e ∈ Finset.range n, c e * (Real.pi*Real.exp r)^(e+1) / (e+1))
      (Real.pi*Real.exp x * ∑ e ∈ Finset.range n, c e * (Real.pi*Real.exp x)^e) x := by
    intro x _
    have hq : HasDerivAt (fun r => Real.pi*Real.exp r) (Real.pi*Real.exp x) x :=
      (Real.hasDerivAt_exp x).const_mul _
    have h := HasDerivAt.fun_sum (u := Finset.range n) (fun e _ =>
      ((hq.fun_pow (e+1)).const_mul (c e)).div_const ((e:ℝ)+1))
    refine h.congr_deriv ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have he : (e:ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable
    fun_prop), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- `π e^{log(q/π)} = q`. -/
theorem pi_mul_exp_log_div {q : ℝ} (hq : 0 < q) : Real.pi * Real.exp (Real.log (q/Real.pi)) = q := by
  rw [Real.exp_log (by positivity)]
  field_simp

/-- Interval integrability of the seam-split integrand on any interval in `[0,∞)`. -/
theorem intervalIntegrable_seamSplit {rc a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (v : Fin 4 → ℝ) :
    IntervalIntegrable (fun r => thetaCuspOddFourSeamSplitIntegrand rc r v) volume a b := by
  have h := integrableOn_thetaCuspOddFourSeamSplitIntegrand rc v
  refine ⟨h.mono_set ?_, h.mono_set ?_⟩
  · exact Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha)
  · exact Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hb)

/-- **Seam piece.** If the piece matrix is positive semidefinite on `(r_a, r_b) ⊂ [0, r_c]`,
`X ⪰ 0` and `r²κ ≤ Ω` there, the seam-split integral over the piece is at least
`−Ω ∫_{r_a'}^{r_b} π e^r F_X` for any `r_a' ≤ r_a`. -/
theorem seam_piece_integral {ra' ra rb rc Ω : ℝ} (hra : ra' ≤ ra) (hab : ra ≤ rb) (ha0 : 0 ≤ ra)
    (hbc : rb ≤ rc) {X : Fin 4 → Fin 4 → ℝ}
    (hX : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * X i j)
    (hW : ∀ r ∈ Ioo ra rb, ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j *
      pieceW (Real.pi*Real.exp r) X i j)
    (hΩ0 : 0 ≤ Ω) (hΩ : ∀ r ∈ Ioo ra rb, r^2 * pieceKernel r ≤ Ω) (v : Fin 4 → ℝ) :
    -(Ω * ∫ r in ra'..rb, Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v) ≤
      ∫ r in ra..rb, thetaCuspOddFourSeamSplitIntegrand rc r v := by
  have hF : ∀ q, 0 ≤ frameForm X q v := fun q => hX (coordinates q v)
  have hcont : Continuous fun r => Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v := by
    have := continuous_frameForm X v
    fun_prop
  have hmono : (∫ r in ra..rb, Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v) ≤
      ∫ r in ra'..rb, Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v :=
    integral_mono_interval hra hab le_rfl
      (Filter.Eventually.of_forall fun r => mul_nonneg (by positivity) (hF _))
      (hcont.intervalIntegrable _ _)
  have hstep : -(Ω * ∫ r in ra..rb, Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v) ≤
      ∫ r in ra..rb, thetaCuspOddFourSeamSplitIntegrand rc r v := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine integral_mono_on_of_le_Ioo hab ((hcont.const_mul Ω).neg.intervalIntegrable _ _)
      (intervalIntegrable_seamSplit ha0 (ha0.trans hab) v) fun r hr => ?_
    have hr0 : 0 ≤ r := ha0.trans hr.1.le
    have hf := fibreForm_ge_of_piece hr0 v (hW r hr)
    have hk := pieceKernel_nonneg r
    have hq : 0 ≤ Real.pi*Real.exp r := by positivity
    have hFr := hF (Real.pi*Real.exp r)
    have hmin : -(pieceKernel r * (Real.pi*Real.exp r) * frameForm X (Real.pi*Real.exp r) v) ≤
        min (thetaCuspOddFourFibreForm r v) 0 :=
      le_min hf (by have := mul_nonneg (mul_nonneg hk hq) hFr; linarith)
    unfold thetaCuspOddFourSeamSplitIntegrand
    rw [if_pos (hr.2.le.trans hbc)]
    have hqF : 0 ≤ Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v := mul_nonneg hq hFr
    have hΩr := hΩ r hr
    calc -(Ω * (Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v))
        ≤ -(r^2 * pieceKernel r * (Real.pi*Real.exp r * frameForm X (Real.pi*Real.exp r) v)) :=
          neg_le_neg (mul_le_mul_of_nonneg_right hΩr hqF)
      _ = r^2 * -(pieceKernel r * (Real.pi*Real.exp r) * frameForm X (Real.pi*Real.exp r) v) := by
          ring
      _ ≤ r^2 * min (thetaCuspOddFourFibreForm r v) 0 :=
          mul_le_mul_of_nonneg_left hmin (sq_nonneg r)
  exact le_trans (neg_le_neg (mul_le_mul_of_nonneg_left hmono hΩ0)) hstep

/-- **Bulk piece.** If the piece matrix is positive semidefinite on `(r_a, r_b)` with
`r_c ≤ r_a`, `X ⪯ 0` and `Ω ≤ r²κ` there, the seam-split integral over the piece is at least
`Ω ∫ π e^r (−F_X)`. -/
theorem bulk_piece_integral {ra rb rc Ω : ℝ} (hab : ra ≤ rb) (hcr : rc ≤ ra) (ha0 : 0 ≤ ra)
    {X : Fin 4 → Fin 4 → ℝ}
    (hX : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j * (-X i j))
    (hW : ∀ r ∈ Ioo ra rb, ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, y i * y j *
      pieceW (Real.pi*Real.exp r) X i j)
    (hΩ : ∀ r ∈ Ioo ra rb, Ω ≤ r^2 * pieceKernel r) (v : Fin 4 → ℝ) :
    Ω * (∫ r in ra..rb, Real.pi*Real.exp r * -frameForm X (Real.pi*Real.exp r) v) ≤
      ∫ r in ra..rb, thetaCuspOddFourSeamSplitIntegrand rc r v := by
  have hF : ∀ q, 0 ≤ -frameForm X q v := by
    intro q
    have := hX (coordinates q v)
    unfold frameForm
    simp only [mul_neg, Finset.sum_neg_distrib] at this
    linarith
  have hcont : Continuous fun r => Real.pi*Real.exp r * -frameForm X (Real.pi*Real.exp r) v := by
    have := continuous_frameForm X v
    fun_prop
  rw [← intervalIntegral.integral_const_mul]
  refine integral_mono_on_of_le_Ioo hab ((hcont.const_mul Ω).intervalIntegrable _ _)
    (intervalIntegrable_seamSplit ha0 (ha0.trans hab) v) fun r hr => ?_
  have hr0 : 0 ≤ r := ha0.trans hr.1.le
  have hf := fibreForm_ge_of_piece hr0 v (hW r hr)
  have hq : 0 ≤ Real.pi*Real.exp r := by positivity
  have hqF : 0 ≤ Real.pi*Real.exp r * -frameForm X (Real.pi*Real.exp r) v := mul_nonneg hq (hF _)
  unfold thetaCuspOddFourSeamSplitIntegrand
  rw [if_neg (not_le.mpr (hcr.trans_lt hr.1))]
  calc Ω * (Real.pi*Real.exp r * -frameForm X (Real.pi*Real.exp r) v)
      ≤ r^2 * pieceKernel r * (Real.pi*Real.exp r * -frameForm X (Real.pi*Real.exp r) v) :=
        mul_le_mul_of_nonneg_right (hΩ r hr) hqF
    _ = r^2 * -(pieceKernel r * (Real.pi*Real.exp r) * frameForm X (Real.pi*Real.exp r) v) := by
        ring
    _ ≤ r^2 * thetaCuspOddFourFibreForm r v := mul_le_mul_of_nonneg_left hf (sq_nonneg r)

theorem neg_sym4 (a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 : ℝ) (i j : Fin 4) :
    -sym4 a00 a01 a02 a03 a11 a12 a13 a22 a23 a33 i j =
      sym4 (-a00) (-a01) (-a02) (-a03) (-a11) (-a12) (-a13) (-a22) (-a23) (-a33) i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The seam-split integral over `(0,∞)` is the integral over `(0, r_*]` plus the tail. -/
theorem seamSplit_integral_split {rc rs : ℝ} (hrs : 0 ≤ rs) (v : Fin 4 → ℝ) :
    ∫ r in Ioi 0, thetaCuspOddFourSeamSplitIntegrand rc r v =
      (∫ r in (0:ℝ)..rs, thetaCuspOddFourSeamSplitIntegrand rc r v) +
        ∫ r in Ioi rs, thetaCuspOddFourSeamSplitIntegrand rc r v := by
  have h := integrableOn_thetaCuspOddFourSeamSplitIntegrand rc v
  rw [intervalIntegral.integral_of_le hrs, ← setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (h.mono_set Ioc_subset_Ioi_self)
    (h.mono_set (Ioi_subset_Ioi hrs)), Ioc_union_Ioi_eq_Ioi hrs]

/-! ### Weight bounds on a piece -/

/-- Upper weight on a seam piece `q ∈ [q_a, q_b]` from `r ≤ L`, `e^{L/2} ≤ U`, `E ≤ e^{2q_a}`. -/
theorem seam_weight_le {r qa qb L U E : ℝ} (hr0 : 0 ≤ r) (hqa : qa ≤ Real.pi*Real.exp r)
    (hqb : Real.pi*Real.exp r ≤ qb) (h32 : 3/2 ≤ qa) (hrL : r ≤ L) (hU : Real.exp (L/2) ≤ U)
    (hE0 : 0 < E) (hE : E ≤ Real.exp (2*qa)) :
    r^2 * pieceKernel r ≤ L^2 * (4*qb^2*(U*(1/E))*(8*(2*qb-3)^2)) := by
  set q := Real.pi*Real.exp r with hqd
  have hsplit : Real.exp (r/2 - 2*q) = Real.exp (r/2) * Real.exp (-(2*q)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : Real.exp (r/2) ≤ U := (Real.exp_le_exp.mpr (by linarith)).trans hU
  have h2 : Real.exp (-(2*q)) ≤ 1/E := by
    refine (Real.exp_le_exp.mpr (show -(2*q) ≤ -(2*qa) by linarith)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hE0 hE
  have h12 : Real.exp (r/2) * Real.exp (-(2*q)) ≤ U*(1/E) :=
    mul_le_mul h1 h2 (Real.exp_pos _).le ((Real.exp_pos _).le.trans h1)
  have hr2 : r^2 ≤ L^2 := pow_le_pow_left₀ hr0 hrL 2
  have hq2 : q^2 ≤ qb^2 := pow_le_pow_left₀ (by linarith) hqb 2
  have hd2 : (2*q-3)^2 ≤ (2*qb-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  unfold pieceKernel
  rw [← hqd, hsplit]
  have hx : 0 ≤ 4*qb^2*(U*(1/E)) :=
    mul_nonneg (by positivity) (mul_nonneg ((Real.exp_pos _).le.trans h1) (by positivity))
  calc r^2 * (4*q^2*(Real.exp (r/2) * Real.exp (-(2*q)))*(8*(2*q-3)^2))
      ≤ L^2 * (4*qb^2*(U*(1/E))*(8*(2*qb-3)^2)) := by gcongr

/-- Lower weight on a bulk piece `q ∈ [q_a, q_b]` from `L ≤ r`, `U ≤ e^{L/2}`,
`e^{2q_b} ≤ E`. -/
theorem bulk_weight_ge {r qa qb L U E : ℝ} (hqa : qa ≤ Real.pi*Real.exp r)
    (hqb : Real.pi*Real.exp r ≤ qb) (h32 : 3/2 ≤ qa) (hL0 : 0 ≤ L) (hrL : L ≤ r) (hU0 : 0 ≤ U)
    (hU : U ≤ Real.exp (L/2)) (hE : Real.exp (2*qb) ≤ E) :
    L^2 * (4*qa^2*(U*(1/E))*(8*(2*qa-3)^2)) ≤ r^2 * pieceKernel r := by
  set q := Real.pi*Real.exp r with hqd
  have hsplit : Real.exp (r/2 - 2*q) = Real.exp (r/2) * Real.exp (-(2*q)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : U ≤ Real.exp (r/2) := hU.trans (Real.exp_le_exp.mpr (by linarith))
  have h2 : 1/E ≤ Real.exp (-(2*q)) := by
    refine le_trans ?_ (Real.exp_le_exp.mpr (show -(2*qb) ≤ -(2*q) by linarith))
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hE
  have hE0 : 0 < E := (Real.exp_pos _).trans_le hE
  have h12 : U*(1/E) ≤ Real.exp (r/2) * Real.exp (-(2*q)) :=
    mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
  have hr2 : L^2 ≤ r^2 := pow_le_pow_left₀ hL0 hrL 2
  have hq2 : qa^2 ≤ q^2 := pow_le_pow_left₀ (by linarith) hqa 2
  have hd2 : (2*qa-3)^2 ≤ (2*q-3)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  unfold pieceKernel
  rw [← hqd, hsplit]
  calc L^2 * (4*qa^2*(U*(1/E))*(8*(2*qa-3)^2))
      ≤ r^2 * (4*q^2*(Real.exp (r/2) * Real.exp (-(2*q)))*(8*(2*q-3)^2)) := by gcongr

/-- `r ∈ (log(q_a/π), log(q_b/π))` puts `π e^r` in `(q_a, q_b)`. -/
theorem scale_mem_of_mem {r qa qb : ℝ} (hqa : 0 < qa) (hqb : 0 < qb)
    (hr : r ∈ Ioo (Real.log (qa/Real.pi)) (Real.log (qb/Real.pi))) :
    qa ≤ Real.pi*Real.exp r ∧ Real.pi*Real.exp r ≤ qb := by
  constructor
  · rw [← pi_mul_exp_log_div hqa]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr.1.le) Real.pi_pos.le
  · rw [← pi_mul_exp_log_div hqb]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr.2.le) Real.pi_pos.le

end
end RHTower.ThetaCuspOddFourPieces
