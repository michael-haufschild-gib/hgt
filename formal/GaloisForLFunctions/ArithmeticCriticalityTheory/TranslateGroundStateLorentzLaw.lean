import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateSpanPlateauLaw

/-!
# On the translates of Riemann's kernel the Markov form is Lorentzian

The **translate ground state** `τ_b = Φ(· − b)/Φ` satisfies an exact source equation: by the theta
harmonic identity at `x` and `x − b` (the diagonal archimedean densities cancel),

    (𝓛_D τ_b)(x) − Φ(x) cosh(x/2) τ_b(x) = −Φ(x) cosh((x − b)/2)          for all b, x.

The shifted ground states are its antisymmetrisations, `ω_a = τ_a − τ_{−a}`; the constant `1 = τ_0`
gives `𝓛_D 1 = 0`. For a finite combination `ω = Σ_j α_j τ_{b_j}` put

    A = Σ_j α_j cosh(b_j/2),     B = Σ_j α_j sinh(b_j/2),

so the source is `−Φ(x)(A cosh(x/2) − B sinh(x/2))`. With the smooth plateaus `u_L` the general
plateau law gives

    | markovEnergy(Φ(ω u_L)) − (B² − A²)/2 | ≤ K e^{−8L}.

On the translates of `Φ` the Markov form is the **Lorentzian form** `(B² − A²)/2`: one negative
direction (the even pole, `A`), one positive direction (the odd pole, `B`), and an
infinite-dimensional null space `A = B = 0`. Special cases: `Q(Φ u_L) → −1/2` (the even pole
calibration `Q(1) = −1/2` as a theorem about compactly supported tests), even pairs
`τ_b + τ_{−b}` tend to `−2 cosh²(b/2)`, odd pairs `ω_b` to `2 sinh²(b/2)`. This is the explicit
formula restricted to the theta span with every zero erased: the Mellin transform of `Φ` is `ξ`,
which vanishes at the zeros, and what remains is the pole form of signature `(1, 1)`, the
"one negative square" of the Weil form.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

variable {ι : Type*}

/-! ### The translate ground state and its source equation -/

/-- The translate ground state `τ_b(x) = Φ(x − b)/Φ(x)`. -/
def translateGroundState (b x : ℝ) : ℝ := riemannKernelReal (x - b) / riemannKernelReal x

theorem riemannKernelReal_mul_translateGroundState (b x : ℝ) :
    riemannKernelReal x * translateGroundState b x = riemannKernelReal (x - b) := by
  unfold translateGroundState
  rw [mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem contDiff_translateGroundState (b : ℝ) : ContDiff ℝ 2 (translateGroundState b) := by
  unfold translateGroundState
  exact (contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).div
    contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'

theorem twoSidedShiftGenerator_translateGroundState (b t x : ℝ) :
    twoSidedShiftGenerator (translateGroundState b) t x =
      riemannKernelReal (x - b) * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x *
          (riemannKernelReal (x - b + t) + riemannKernelReal (x - b - t)) := by
  unfold twoSidedShiftGenerator
  have h1 := riemannKernelReal_mul_translateGroundState b x
  have h2 := riemannKernelReal_mul_translateGroundState b (x + t)
  have h3 := riemannKernelReal_mul_translateGroundState b (x - t)
  rw [show x + t - b = x - b + t by ring] at h2
  rw [show x - t - b = x - b - t by ring] at h3
  linear_combination (riemannKernelReal (x + t) + riemannKernelReal (x - t)) * h1 -
    riemannKernelReal x * h2 - riemannKernelReal x * h3

/-- The archimedean integrand against the symmetrised archimedean terms; diagonals cancel. -/
theorem archLevy_twoSidedShiftGenerator_translateGroundState (b x u : ℝ) :
    archLevyDensity u * twoSidedShiftGenerator (translateGroundState b) u x =
      -(riemannKernelReal (x - b) * symArchTerm x u -
        riemannKernelReal x * symArchTerm (x - b) u) := by
  rw [twoSidedShiftGenerator_translateGroundState]
  unfold symArchTerm
  ring

theorem integrableOn_archLevy_twoSidedShiftGenerator_translateGroundState (b x : ℝ) :
    IntegrableOn (fun u => archLevyDensity u * twoSidedShiftGenerator (translateGroundState b) u x)
      (Ioi 0) := by
  have h : IntegrableOn (fun u => -(riemannKernelReal (x - b) * symArchTerm x u -
      riemannKernelReal x * symArchTerm (x - b) u)) (Ioi 0) :=
    (((integrableOn_symArchTerm x).const_mul (riemannKernelReal (x - b))).sub
      ((integrableOn_symArchTerm (x - b)).const_mul (riemannKernelReal x))).neg
  exact h.congr_fun (fun u _ => (archLevy_twoSidedShiftGenerator_translateGroundState b x u).symm)
    measurableSet_Ioi

theorem atom_twoSidedShiftGenerator_translateGroundState (b x : ℝ) (n : ℕ) :
    vonMangoldtAtom n * twoSidedShiftGenerator (translateGroundState b) (Real.log n) x =
      riemannKernelReal (x - b) * (vonMangoldtAtom n *
          (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) -
        riemannKernelReal x * (vonMangoldtAtom n *
          (riemannKernelReal (x - b + Real.log n) + riemannKernelReal (x - b - Real.log n))) := by
  rw [twoSidedShiftGenerator_translateGroundState]
  ring

theorem summable_atom_twoSidedShiftGenerator_translateGroundState (b x : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * twoSidedShiftGenerator (translateGroundState b) (Real.log n) x :=
  (((summable_primeKernelSum x).mul_left (riemannKernelReal (x - b))).sub
    ((summable_primeKernelSum (x - b)).mul_left (riemannKernelReal x))).congr fun n =>
      (atom_twoSidedShiftGenerator_translateGroundState b x n).symm

/-- **Source equation of the translate ground state.**
`(𝓛_D τ_b)(x) − Φ(x) cosh(x/2) τ_b(x) = −Φ(x) cosh((x − b)/2)`. -/
theorem twoSidedGenerator_translateGroundState_sub_potential (b x : ℝ) :
    twoSidedGenerator (translateGroundState b) x -
        riemannKernelReal x * Real.cosh (x / 2) * translateGroundState b x =
      riemannKernelReal x * -Real.cosh ((x - b) / 2) := by
  have harch : (∫ u in Ioi (0 : ℝ), archLevyDensity u *
      twoSidedShiftGenerator (translateGroundState b) u x) =
      -(riemannKernelReal (x - b) * (∫ u in Ioi (0 : ℝ), symArchTerm x u) -
        riemannKernelReal x * ∫ u in Ioi (0 : ℝ), symArchTerm (x - b) u) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((integrableOn_symArchTerm x).const_mul _)
        ((integrableOn_symArchTerm (x - b)).const_mul _), ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi fun u _ =>
      archLevy_twoSidedShiftGenerator_translateGroundState b x u
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (translateGroundState b) (Real.log n) x) =
      riemannKernelReal (x - b) * primeKernelSum x -
        riemannKernelReal x * primeKernelSum (x - b) := by
    rw [tsum_congr (atom_twoSidedShiftGenerator_translateGroundState b x),
      ((summable_primeKernelSum x).mul_left _).tsum_sub ((summable_primeKernelSum (x - b)).mul_left _),
      tsum_mul_left, tsum_mul_left]
    rfl
  unfold twoSidedGenerator
  rw [harch, hprime]
  have hPx := theta_harmonic_identity x
  have hPb := theta_harmonic_identity (x - b)
  have hmul := riemannKernelReal_mul_translateGroundState b x
  linear_combination riemannKernelReal (x - b) * hPx - riemannKernelReal x * hPb -
    Real.cosh (x / 2) * hmul

/-! ### Finite combinations of translates -/

/-- The combination `Σ_j α_j τ_{b_j}` in Doob coordinates. -/
def translateSpan (s : Finset ι) (α b : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ s, α j * translateGroundState (b j) x

/-- The even pole coefficient `A = Σ_j α_j cosh(b_j/2)`. -/
def translateCoshCoefficient (s : Finset ι) (α b : ι → ℝ) : ℝ :=
  ∑ j ∈ s, α j * Real.cosh (b j / 2)

/-- The odd pole coefficient `B = Σ_j α_j sinh(b_j/2)`. -/
def translateSinhCoefficient (s : Finset ι) (α b : ι → ℝ) : ℝ :=
  ∑ j ∈ s, α j * Real.sinh (b j / 2)

theorem riemannKernelReal_mul_translateSpan (s : Finset ι) (α b : ι → ℝ) (x : ℝ) :
    riemannKernelReal x * translateSpan s α b x = ∑ j ∈ s, α j * riemannKernelReal (x - b j) := by
  unfold translateSpan
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [← riemannKernelReal_mul_translateGroundState]
    ring

theorem contDiff_translateSpan (s : Finset ι) (α b : ι → ℝ) : ContDiff ℝ 2 (translateSpan s α b) := by
  unfold translateSpan
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_translateGroundState (b j))

theorem integrableOn_archLevy_twoSidedShiftGenerator_translateSpan (s : Finset ι) (α b : ι → ℝ)
    (x : ℝ) :
    IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator (translateSpan s α b) t x)
      (Ioi 0) := by
  have h : IntegrableOn (fun t => ∑ j ∈ s, α j *
      (archLevyDensity t * twoSidedShiftGenerator (translateGroundState (b j)) t x)) (Ioi 0) :=
    integrable_finsetSum s fun j _ =>
      (integrableOn_archLevy_twoSidedShiftGenerator_translateGroundState (b j) x).const_mul (α j)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [show translateSpan s α b = fun y => ∑ j ∈ s, α j * translateGroundState (b j) y from rfl,
    twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem summable_atom_twoSidedShiftGenerator_translateSpan (s : Finset ι) (α b : ι → ℝ) (x : ℝ) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * twoSidedShiftGenerator (translateSpan s α b) (Real.log n) x := by
  have h := summable_sum (s := s) fun j _ =>
    (summable_atom_twoSidedShiftGenerator_translateGroundState (b j) x).mul_left (α j)
  refine h.congr fun n => ?_
  rw [show translateSpan s α b = fun y => ∑ j ∈ s, α j * translateGroundState (b j) y from rfl,
    twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem twoSidedGenerator_translateSpan (s : Finset ι) (α b : ι → ℝ) (x : ℝ) :
    twoSidedGenerator (translateSpan s α b) x =
      ∑ j ∈ s, α j * twoSidedGenerator (translateGroundState (b j)) x := by
  have hspan : translateSpan s α b = fun y => ∑ j ∈ s, α j * translateGroundState (b j) y := rfl
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      twoSidedShiftGenerator (translateSpan s α b) t x) =
      ∑ j ∈ s, α j * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        twoSidedShiftGenerator (translateGroundState (b j)) t x := by
    have e : (fun t => archLevyDensity t * twoSidedShiftGenerator (translateSpan s α b) t x) =
        fun t => ∑ j ∈ s, α j * (archLevyDensity t *
          twoSidedShiftGenerator (translateGroundState (b j)) t x) := by
      funext t
      rw [hspan, twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum s fun j _ =>
      (integrableOn_archLevy_twoSidedShiftGenerator_translateGroundState (b j) x).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      twoSidedShiftGenerator (translateSpan s α b) (Real.log n) x) =
      ∑ j ∈ s, α j * ∑' n : ℕ, vonMangoldtAtom n *
        twoSidedShiftGenerator (translateGroundState (b j)) (Real.log n) x := by
    have e : (fun n : ℕ => vonMangoldtAtom n *
        twoSidedShiftGenerator (translateSpan s α b) (Real.log n) x) =
        fun n => ∑ j ∈ s, α j * (vonMangoldtAtom n *
          twoSidedShiftGenerator (translateGroundState (b j)) (Real.log n) x) := by
      funext n
      rw [hspan, twoSidedShiftGenerator_finsetSum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, Summable.tsum_finsetSum fun j _ =>
      (summable_atom_twoSidedShiftGenerator_translateGroundState (b j) x).mul_left _]
    exact Finset.sum_congr rfl fun j _ => tsum_mul_left
  unfold twoSidedGenerator
  rw [harch, hprime, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The source of a combination of translates: `−Φ(x)(A cosh(x/2) − B sinh(x/2))`. -/
def translateSource (s : Finset ι) (α b : ι → ℝ) (x : ℝ) : ℝ :=
  -(translateCoshCoefficient s α b * Real.cosh (x / 2) -
    translateSinhCoefficient s α b * Real.sinh (x / 2))

theorem twoSidedGenerator_translateSpan_sub_potential (s : Finset ι) (α b : ι → ℝ) (x : ℝ) :
    twoSidedGenerator (translateSpan s α b) x -
        riemannKernelReal x * Real.cosh (x / 2) * translateSpan s α b x =
      riemannKernelReal x * translateSource s α b x := by
  rw [twoSidedGenerator_translateSpan]
  unfold translateSpan translateSource translateCoshCoefficient translateSinhCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := twoSidedGenerator_translateGroundState_sub_potential (b j) x
  have hc : Real.cosh ((x - b j) / 2) =
      Real.cosh (x / 2) * Real.cosh (b j / 2) - Real.sinh (x / 2) * Real.sinh (b j / 2) := by
    rw [show (x - b j) / 2 = x / 2 - b j / 2 by ring, Real.cosh_sub]
  rw [hc] at h
  linear_combination α j * h

theorem continuous_translateSource (s : Finset ι) (α b : ι → ℝ) :
    Continuous (translateSource s α b) := by
  unfold translateSource
  exact ((continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).sub
    (continuous_const.mul (Real.continuous_sinh.comp (continuous_id.div_const 2)))).neg

/-- The test coordinate of a combination of translates decays like `e^{−24|y|}`. -/
theorem exists_abs_riemannKernelReal_mul_translateSpan_le (s : Finset ι) (α b : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y,
      |riemannKernelReal y * translateSpan s α b y| ≤ C * Real.exp (-(24 * |y|)) := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_riemannKernelReal_le_exp_twentyFour
  refine ⟨∑ j ∈ s, |α j| * (C₀ * Real.exp (24 * |b j|)),
    Finset.sum_nonneg fun j _ => by positivity, fun y => ?_⟩
  rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, mul_assoc, abs_of_pos (riemannKernelReal_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc riemannKernelReal (y - b j) ≤ C₀ * Real.exp (-(24 * |y - b j|)) := hC _
    _ ≤ C₀ * (Real.exp (24 * |b j|) * Real.exp (-(24 * |y|))) :=
        mul_le_mul_of_nonneg_left (exp_neg_mul_abs_sub_le 24 y (b j) (by norm_num)) hC₀
    _ = _ := by ring

/-! ### The moments of the translates -/

theorem integrable_riemannKernelReal_sub_mul_cosh_half (b : ℝ) :
    Integrable fun x => riemannKernelReal (x - b) * Real.cosh (x / 2) := by
  have h := (integrable_cosh_mul_theta_shift (-b)).const_mul (1 / 2)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [show -b + x = x - b by ring]
  ring

theorem integral_riemannKernelReal_sub_mul_cosh_half (b : ℝ) :
    (∫ x, riemannKernelReal (x - b) * Real.cosh (x / 2)) = Real.cosh (b / 2) / 2 := by
  have h := integral_cosh_mul_theta_shift (-b)
  have e : (fun x => riemannKernelReal (x - b) * Real.cosh (x / 2)) =
      fun x => (1 / 2) * (2 * Real.cosh (x / 2) * riemannKernelReal (-b + x)) := by
    funext x
    rw [show -b + x = x - b by ring]
    ring
  rw [e, integral_const_mul, h, show -b / 2 = -(b / 2) by ring, Real.cosh_neg]
  ring

theorem integrable_riemannKernelReal_sub_mul_sinh_half (b : ℝ) :
    Integrable fun x => riemannKernelReal (x - b) * Real.sinh (x / 2) := by
  refine (integrable_sinh_mul_kernel_sub b).congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [show b - x = -(x - b) by ring, riemannKernelReal_neg']
  ring

theorem integral_riemannKernelReal_sub_mul_sinh_half (b : ℝ) :
    (∫ x, riemannKernelReal (x - b) * Real.sinh (x / 2)) = Real.sinh (b / 2) / 2 := by
  rw [← integral_sinh_mul_kernel_sub b]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [show b - x = -(x - b) by ring, riemannKernelReal_neg']
  ring

/-- `∫ M(x) g(x) dx = (B² − A²)/2` for the test coordinate `M` and source `g` of a combination of
translates. -/
theorem integral_translateSpan_mul_translateSource (s : Finset ι) (α b : ι → ℝ) :
    (∫ x, (riemannKernelReal x * translateSpan s α b x) * translateSource s α b x) =
      (translateSinhCoefficient s α b ^ 2 - translateCoshCoefficient s α b ^ 2) / 2 := by
  set A := translateCoshCoefficient s α b
  set B := translateSinhCoefficient s α b
  have e : (fun x => (riemannKernelReal x * translateSpan s α b x) * translateSource s α b x) =
      fun x => ∑ j ∈ s, α j * (B * (riemannKernelReal (x - b j) * Real.sinh (x / 2)) -
        A * (riemannKernelReal (x - b j) * Real.cosh (x / 2))) := by
    funext x
    rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
    unfold translateSource
    exact Finset.sum_congr rfl fun j _ => by ring
  have hint : ∀ j ∈ s, Integrable fun x => α j * (B * (riemannKernelReal (x - b j) *
      Real.sinh (x / 2)) - A * (riemannKernelReal (x - b j) * Real.cosh (x / 2))) := fun j _ =>
    (((integrable_riemannKernelReal_sub_mul_sinh_half (b j)).const_mul B).sub
      ((integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul A)).const_mul _
  rw [e, integral_finsetSum s hint]
  have hterm : ∀ j ∈ s, (∫ x, α j * (B * (riemannKernelReal (x - b j) * Real.sinh (x / 2)) -
      A * (riemannKernelReal (x - b j) * Real.cosh (x / 2)))) =
      α j * (B * (Real.sinh (b j / 2) / 2) - A * (Real.cosh (b j / 2) / 2)) := fun j _ => by
    rw [integral_const_mul, integral_sub
      ((integrable_riemannKernelReal_sub_mul_sinh_half (b j)).const_mul B)
      ((integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul A),
      integral_const_mul, integral_const_mul, integral_riemannKernelReal_sub_mul_sinh_half,
      integral_riemannKernelReal_sub_mul_cosh_half]
  rw [Finset.sum_congr rfl hterm]
  have hA : A = ∑ j ∈ s, α j * Real.cosh (b j / 2) := rfl
  have hB : B = ∑ j ∈ s, α j * Real.sinh (b j / 2) := rfl
  have hsum : (∑ j ∈ s, α j * (B * (Real.sinh (b j / 2) / 2) - A * (Real.cosh (b j / 2) / 2))) =
      B * (∑ j ∈ s, α j * Real.sinh (b j / 2)) / 2 - A * (∑ j ∈ s, α j * Real.cosh (b j / 2)) / 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, ← hA, ← hB]
  ring

/-! ### The Lorentz law -/

theorem cosh_le_exp_abs (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.mpr (le_abs_self y)
  have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.mpr (neg_le_abs y)
  rw [Real.cosh_eq]
  linarith

theorem exp_abs_half_le_exp_eight (x : ℝ) : Real.exp |x / 2| ≤ Real.exp (8 * |x|) :=
  Real.exp_le_exp.mpr (by rw [abs_div, abs_two]; linarith [abs_nonneg x])

/-- The source of a combination of translates grows at most like `e^{8|x|}`. -/
theorem abs_translateSource_le (s : Finset ι) (α b : ι → ℝ) (x : ℝ) :
    |translateSource s α b x| ≤
      (|translateCoshCoefficient s α b| + |translateSinhCoefficient s α b|) * Real.exp (8 * |x|) := by
  have hc : |Real.cosh (x / 2)| ≤ Real.exp (8 * |x|) := by
    rw [abs_of_pos (Real.cosh_pos _)]
    exact (cosh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)
  have hs : |Real.sinh (x / 2)| ≤ Real.exp (8 * |x|) :=
    (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight x)
  unfold translateSource
  rw [abs_neg]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (translateCoshCoefficient s α b)),
    mul_le_mul_of_nonneg_left hs (abs_nonneg (translateSinhCoefficient s α b))]

/-- The source integrand converges at rate `e^{−8L}`: `|(u_L² − 1) M h| ≤ C H e^{−8L} e^{−8|x|}`
when `|M| ≤ C e^{−24|·|}` and `|h| ≤ H e^{8|·|}`. -/
theorem abs_smoothPlateau_sq_sub_one_mul_le_of_growth {M h : ℝ → ℝ} {C H : ℝ} (hC0 : 0 ≤ C)
    (hH0 : 0 ≤ H) (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|)))
    (hh : ∀ y, |h y| ≤ H * Real.exp (8 * |y|)) (L x : ℝ) :
    |(smoothPlateau L x ^ 2 - 1) * (M x * h x)| ≤
      C * H * Real.exp (-(8 * L)) * Real.exp (-(8 * |x|)) := by
  have hR : 0 ≤ C * H * Real.exp (-(8 * L)) * Real.exp (-(8 * |x|)) := by positivity
  by_cases hxL : |x| ≤ L
  · rw [smoothPlateau_eq_one hxL]
    simpa using hR
  · have hx := exp_neg_mul_abs_le_of_lt (not_le.mp hxL)
    have h1 : |smoothPlateau L x ^ 2 - 1| ≤ 1 := by
      have := smoothPlateau_nonneg L x
      have := smoothPlateau_le_one L x
      rw [abs_le]
      constructor <;> nlinarith
    have h2 : |M x| ≤ C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |x|))) :=
      (hM x).trans (mul_le_mul_of_nonneg_left hx hC0)
    have hxx : Real.exp (-(16 * |x|)) * Real.exp (8 * |x|) = Real.exp (-(8 * |x|)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [abs_mul, abs_mul]
    calc |smoothPlateau L x ^ 2 - 1| * (|M x| * |h x|)
        ≤ 1 * ((C * (Real.exp (-(8 * L)) * Real.exp (-(16 * |x|)))) * (H * Real.exp (8 * |x|))) :=
          mul_le_mul h1 (mul_le_mul h2 (hh x) (abs_nonneg _) (by positivity))
            (by positivity) zero_le_one
      _ = C * H * Real.exp (-(8 * L)) * (Real.exp (-(16 * |x|)) * Real.exp (8 * |x|)) := by ring
      _ = _ := by rw [hxx]

theorem integrable_translateSpan_mul_translateSource (s : Finset ι) (α b : ι → ℝ) :
    Integrable fun x => (riemannKernelReal x * translateSpan s α b x) * translateSource s α b x := by
  have h : Integrable fun x => ∑ j ∈ s, α j *
      (translateSinhCoefficient s α b * (riemannKernelReal (x - b j) * Real.sinh (x / 2)) -
        translateCoshCoefficient s α b * (riemannKernelReal (x - b j) * Real.cosh (x / 2))) :=
    integrable_finsetSum s fun j _ =>
      (((integrable_riemannKernelReal_sub_mul_sinh_half (b j)).const_mul _).sub
        ((integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul _)).const_mul (α j)
  refine h.congr (Eventually.of_forall fun x => ?_)
  show _ = riemannKernelReal x * translateSpan s α b x * translateSource s α b x
  rw [riemannKernelReal_mul_translateSpan, Finset.sum_mul]
  unfold translateSource
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The Lorentz law.** For every finite combination of translates `ω = Σ_j α_j τ_{b_j}` there is
`K` with `|markovEnergy(Φ(ω u_L)) − (B² − A²)/2| ≤ K e^{−8L}` for all `L`. -/
theorem exists_abs_markovEnergy_translatePlateau_sub_le (s : Finset ι) (α b : ι → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |markovEnergy (fun x =>
          (phiDoobTest (fun y => translateSpan s α b y * smoothPlateau L y) x : ℂ)) -
        (translateSinhCoefficient s α b ^ 2 - translateCoshCoefficient s α b ^ 2) / 2| ≤
        K * Real.exp (-(8 * L)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le s α b
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  set H := |translateCoshCoefficient s α b| + |translateSinhCoefficient s α b|
  have hH0 : 0 ≤ H := by positivity
  set I₈ := ∫ x : ℝ, Real.exp (-(8 * |x|))
  have hI₈0 : 0 ≤ I₈ := integral_nonneg fun x => (Real.exp_pos _).le
  set K₁ := C ^ 2 * (2 * Λ * archFirstMoment + 2 * primeEighthMoment)
  have hK₁0 : 0 ≤ K₁ := by
    have := archFirstMoment_nonneg
    have := primeEighthMoment_nonneg
    positivity
  have hgen := abs_markovEnergy_plateau_sub_integral_le (contDiff_translateSpan s α b) hC0 hC hΛ0
    hΛ (integrableOn_archLevy_twoSidedShiftGenerator_translateSpan s α b)
    (summable_atom_twoSidedShiftGenerator_translateSpan s α b)
    (twoSidedGenerator_translateSpan_sub_potential s α b) (continuous_translateSource s α b)
  refine ⟨K₁ * I₈ + C * H * I₈, by positivity, fun L => ?_⟩
  have hu := (contDiff_smoothPlateau L).continuous
  have hMc : Continuous fun x => riemannKernelReal x * translateSpan s α b x :=
    continuous_riemannKernelReal.mul (contDiff_translateSpan s α b).continuous
  have hAi : Integrable fun x => smoothPlateau L x ^ 2 * (riemannKernelReal x * translateSpan s α b x) *
      translateSource s α b x := by
    refine Continuous.integrable_of_hasCompactSupport (((hu.pow 2).mul hMc).mul
      (continuous_translateSource s α b)) ?_
    exact ((hasCompactSupport_sq (hasCompactSupport_smoothPlateau L)).mul_right).mul_right
  have hpole : |(∫ x, smoothPlateau L x ^ 2 * (riemannKernelReal x * translateSpan s α b x) *
      translateSource s α b x) -
      (translateSinhCoefficient s α b ^ 2 - translateCoshCoefficient s α b ^ 2) / 2| ≤
      C * H * Real.exp (-(8 * L)) * I₈ := by
    rw [← integral_translateSpan_mul_translateSource,
      ← integral_sub hAi (integrable_translateSpan_mul_translateSource s α b), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_exp_neg_eight_mul_abs.const_mul
      (C * H * Real.exp (-(8 * L)))) (Eventually.of_forall fun x => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, show smoothPlateau L x ^ 2 * (riemannKernelReal x * translateSpan s α b x) *
          translateSource s α b x - riemannKernelReal x * translateSpan s α b x *
            translateSource s α b x = (smoothPlateau L x ^ 2 - 1) *
          ((riemannKernelReal x * translateSpan s α b x) * translateSource s α b x) by ring]
      exact abs_smoothPlateau_sq_sub_one_mul_le_of_growth hC0 hH0 hC
        (abs_translateSource_le s α b) L x
    · rw [integral_const_mul]
  calc _ ≤ K₁ * I₈ * Real.exp (-(8 * L)) + C * H * Real.exp (-(8 * L)) * I₈ := by
        refine (abs_sub_le _ _ _).trans (add_le_add (hgen L) hpole)
    _ = (K₁ * I₈ + C * H * I₈) * Real.exp (-(8 * L)) := by ring

/-! ### Special cases -/

theorem translateGroundState_zero (x : ℝ) : translateGroundState 0 x = 1 := by
  unfold translateGroundState
  rw [sub_zero, div_self (riemannKernelReal_pos x).ne']

/-- **The even pole calibration as a limit.** `markovEnergy(Φ u_L) → −1/2`: the constant profile,
truncated by smooth plateaus, realises `Q(1) = −1/2` on compactly supported even tests. -/
theorem tendsto_markovEnergy_phiDoob_smoothPlateau :
    Tendsto (fun L => markovEnergy (fun x => (phiDoobTest (smoothPlateau L) x : ℂ))) atTop
      (𝓝 (-(1 / 2))) := by
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_translatePlateau_sub_le
    (Finset.univ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0)
  have hval : (translateSinhCoefficient (Finset.univ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) ^ 2 -
      translateCoshCoefficient (Finset.univ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) ^ 2) / 2 =
      -(1 / 2) := by
    simp [translateSinhCoefficient, translateCoshCoefficient]
    norm_num
  have hfun : ∀ L, (fun y => translateSpan (Finset.univ : Finset (Fin 1)) (fun _ => 1) (fun _ => 0) y *
      smoothPlateau L y) = smoothPlateau L := fun L => by
    funext y
    simp [translateSpan, translateGroundState_zero]
  have h0 : Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
    simpa [Function.comp_def, neg_mul] using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun L => norm_nonneg _)
    (fun L => ?_) h0)
  have := hK L
  rw [hfun L, hval] at this
  rwa [Real.norm_eq_abs]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
