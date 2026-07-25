import GaloisForLFunctions.HTGeometry.AbstractSpectralCharge
import GaloisForLFunctions.HTGeometry.AbstractSpectralRigidity
import GaloisForLFunctions.HTGeometry.AbstractSpectralDefect
import GaloisForLFunctions.HTGeometry.PrincipalSquareRoot

/-!
# The mass deformation of an abstract spectral family

For a mass `a ≥ 1/2` the map `p ↦ sqrt (p ^ 2 + a ^ 2)` sends an admissible family of spectral
points to another one.  Nothing beyond the admissibility interface is used: the displacement bound
`|Im p| < 1/2` already forces `a ^ 2 > (Im p) ^ 2`, which puts the argument of the root in the open
right half-plane.

The deformation is not a lossy smoothing.  Writing `p = R + i J`, the quantity

`chi = Im (p ^ 2) = 2 R J`

is unchanged by the deformation, so the new displacement is `chi / (2 R')` with `R'` the new height,
and the new height satisfies `R < R' ≤ sqrt (R ^ 2 + a ^ 2)`.  Displacements are therefore
contracted, but by a factor that is bounded below in terms of the base height alone:

`base ^ 2 * J ^ 2 ≤ (base ^ 2 + a ^ 2) * J' ^ 2`.

Consequently every quantitative conclusion about the deformed family — a line bound, a defect bound,
an explicit displacement bound — transfers back to the original family with an explicit constant,
and reality of one family is reality of the other.
-/

open Complex

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- The argument of the mass-shifted root: the squared spectral point pushed right by `a ^ 2`. -/
def massArg (a : ℝ) (i : ι) : ℂ := F.pt i ^ 2 + ((a ^ 2 : ℝ) : ℂ)

theorem massArg_re (a : ℝ) (i : ι) :
    (F.massArg a i).re = (F.pt i).re ^ 2 - (F.pt i).im ^ 2 + a ^ 2 := by
  rw [massArg, Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re]; ring

theorem massArg_im (a : ℝ) (i : ι) :
    (F.massArg a i).im = 2 * ((F.pt i).re * (F.pt i).im) := by
  rw [massArg, Complex.add_im, Complex.ofReal_im, pow_two, Complex.mul_im]; ring

theorem sq_im_lt_sq {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) : (F.pt i).im ^ 2 < a ^ 2 := by
  have h := F.abs_im_lt i
  have h0 : (0 : ℝ) ≤ |(F.pt i).im| := abs_nonneg _
  nlinarith [sq_abs (F.pt i).im]

theorem massArg_re_pos {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) : 0 < (F.massArg a i).re := by
  have h := F.sq_im_lt_sq ha i
  have hr := F.re_pos i
  rw [massArg_re]
  nlinarith

/-- **The mass shift strictly increases every height.** -/
theorem re_lt_csqrtRe_massArg {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    (F.pt i).re < csqrtRe (F.massArg a i) := by
  have hpos := F.massArg_re_pos ha i
  have hr := F.re_pos i
  have hle : (F.massArg a i).re ≤ csqrtRe (F.massArg a i) ^ 2 := re_le_sq_csqrtRe hpos
  have hgt : (F.pt i).re ^ 2 < (F.massArg a i).re := by
    rw [massArg_re]; nlinarith [F.sq_im_lt_sq ha i]
  nlinarith [csqrtRe_nonneg (F.massArg a i)]

/-- **The mass shift raises every height by at most the mass.**  The proof is the identity
`(R ^ 2 + J ^ 2 + a ^ 2) ^ 2 - ‖p ^ 2 + a ^ 2‖ ^ 2 = 4 J ^ 2 a ^ 2`. -/
theorem sq_csqrtRe_massArg_le {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    csqrtRe (F.massArg a i) ^ 2 ≤ (F.pt i).re ^ 2 + a ^ 2 := by
  have hpos := F.massArg_re_pos ha i
  have hsq : csqrtRe (F.massArg a i) ^ 2 = (‖F.massArg a i‖ + (F.massArg a i).re) / 2 :=
    sq_csqrtRe hpos
  have hn2 : ‖F.massArg a i‖ ^ 2 =
      (F.massArg a i).re ^ 2 + (F.massArg a i).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre := F.massArg_re a i
  have him := F.massArg_im a i
  have hb : (0 : ℝ) ≤ (F.pt i).re ^ 2 + (F.pt i).im ^ 2 + a ^ 2 := by positivity
  have hsqle : ‖F.massArg a i‖ ^ 2 ≤ ((F.pt i).re ^ 2 + (F.pt i).im ^ 2 + a ^ 2) ^ 2 := by
    rw [hn2, hre, him]
    nlinarith [sq_nonneg ((F.pt i).im * a)]
  have hnorm : ‖F.massArg a i‖ ≤ (F.pt i).re ^ 2 + (F.pt i).im ^ 2 + a ^ 2 := by
    have h1 : ‖F.massArg a i‖ = Real.sqrt (‖F.massArg a i‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    have h2 := Real.sqrt_le_sqrt hsqle
    rw [Real.sqrt_sq hb] at h2
    rw [h1]
    exact h2
  rw [hsq, hre]
  linarith

/-- The mass-shifted height is at most the original height plus the mass. -/
theorem csqrtRe_massArg_le_add {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    csqrtRe (F.massArg a i) ≤ (F.pt i).re + a := by
  have h := F.sq_csqrtRe_massArg_le ha i
  have hr := F.re_pos i
  nlinarith [csqrtRe_nonneg (F.massArg a i), ha]

/-- **The displacement law.**  The mass-shifted displacement times the mass-shifted height is the
original height times the original displacement. -/
theorem csqrtIm_massArg_mul_csqrtRe {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    csqrtIm (F.massArg a i) * csqrtRe (F.massArg a i) = (F.pt i).re * (F.pt i).im := by
  rw [csqrtIm_mul_csqrtRe (F.massArg_re_pos ha i), F.massArg_im a i]
  ring

/-- **The mass shift contracts displacements.** -/
theorem abs_csqrtIm_massArg_le {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    |csqrtIm (F.massArg a i)| ≤ |(F.pt i).im| := by
  have hpos := F.massArg_re_pos ha i
  have hgt := F.re_lt_csqrtRe_massArg ha i
  have hr := F.re_pos i
  have hkey := F.csqrtIm_massArg_mul_csqrtRe ha i
  have habs : |csqrtIm (F.massArg a i)| * csqrtRe (F.massArg a i)
      = (F.pt i).re * |(F.pt i).im| := by
    have h1 : |csqrtIm (F.massArg a i) * csqrtRe (F.massArg a i)|
        = |csqrtIm (F.massArg a i)| * csqrtRe (F.massArg a i) := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < csqrtRe (F.massArg a i))]
    have h2 : |(F.pt i).re * (F.pt i).im| = (F.pt i).re * |(F.pt i).im| := by
      rw [abs_mul, abs_of_pos hr]
    rw [← h1, hkey, h2]
  nlinarith [abs_nonneg (csqrtIm (F.massArg a i)), abs_nonneg ((F.pt i).im)]

/-- **The mass-shifted family.**  Nothing beyond the admissibility interface is used: no height
lower bound past `base > 0` and no property of the underlying divisor. -/
def mass {a : ℝ} (ha : 1 / 2 ≤ a) : AbstractSpectralFamily ι where
  pt := fun i => csqrt (F.massArg a i)
  inv := F.inv
  base := F.base
  base_pos := F.base_pos
  base_le := by
    intro i
    rw [csqrt_re]
    exact le_trans (F.base_le i) (F.re_lt_csqrtRe_massArg ha i).le
  abs_im_lt := by
    intro i
    rw [csqrt_im]
    exact lt_of_le_of_lt (F.abs_csqrtIm_massArg_le ha i) (F.abs_im_lt i)
  summable_weight := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun i => ?_)
      (F.summable_weight hσ)
    rw [csqrt_re]
    exact Real.exp_le_exp.mpr (by nlinarith [F.re_lt_csqrtRe_massArg ha i])
  shell_finite := by
    intro R
    refine (F.shell_finite R).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    rw [csqrt_re] at hi
    linarith [F.re_lt_csqrtRe_massArg ha i]
  conj_stable := by
    intro i
    have harg : F.massArg a (F.inv i) = (starRingEnd ℂ) (F.massArg a i) := by
      rw [massArg, massArg, F.conj_stable i, map_add, map_pow, Complex.conj_ofReal]
    rw [harg, csqrt_conj]

@[simp]
theorem mass_pt {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    (F.mass ha).pt i = csqrt (F.massArg a i) := rfl

@[simp]
theorem mass_base {a : ℝ} (ha : 1 / 2 ≤ a) : (F.mass ha).base = F.base := rfl

theorem mass_pt_sq {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    (F.mass ha).pt i ^ 2 = F.pt i ^ 2 + ((a ^ 2 : ℝ) : ℂ) := by
  rw [mass_pt, csqrt_sq (F.massArg_re_pos ha i), massArg]

/-! ### The conserved charge -/

/-- **The charge is a deformation invariant.**  Every mass shift leaves `Im (p ^ 2)` unchanged, so
the whole one-parameter deformation moves the height and the displacement while preserving their
product. -/
theorem charge_mass {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    (F.mass ha).charge i = F.charge i := by
  rw [charge, charge, F.mass_pt_sq ha i, Complex.add_im, Complex.ofReal_im, add_zero]

/-- **The mass deformation preserves the real locus exactly.** -/
theorem mass_im_eq_zero_iff {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    ((F.mass ha).pt i).im = 0 ↔ (F.pt i).im = 0 := by
  rw [← (F.mass ha).charge_eq_zero_iff i, F.charge_mass ha i, F.charge_eq_zero_iff i]

/-! ### Faithfulness: the deformation loses a bounded factor only -/

/-- **The exact distortion identity.**  Heights and displacements move, but the product of the
height with the displacement is the same for both families. -/
theorem re_mul_im_mass {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    ((F.mass ha).pt i).re * ((F.mass ha).pt i).im = (F.pt i).re * (F.pt i).im := by
  rw [mass_pt, csqrt_re, csqrt_im, mul_comm]
  exact F.csqrtIm_massArg_mul_csqrtRe ha i

/-- **Pointwise faithfulness.**  A displacement bound for the deformed family bounds the original
displacement, with a loss factor controlled by the point's own height. -/
theorem sq_re_mul_sq_im_le {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    (F.pt i).re ^ 2 * (F.pt i).im ^ 2
      ≤ ((F.pt i).re ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2 := by
  have hprod := F.re_mul_im_mass ha i
  have hcap : ((F.mass ha).pt i).re ^ 2 ≤ (F.pt i).re ^ 2 + a ^ 2 := by
    rw [mass_pt, csqrt_re]; exact F.sq_csqrtRe_massArg_le ha i
  have hsq : ((F.mass ha).pt i).re ^ 2 * ((F.mass ha).pt i).im ^ 2
      = (F.pt i).re ^ 2 * (F.pt i).im ^ 2 := by
    have := congrArg (fun t : ℝ => t ^ 2) hprod
    simpa [mul_pow] using this
  nlinarith [sq_nonneg (((F.mass ha).pt i).im), hsq, hcap]

/-- **Uniform faithfulness.**  With `base` the family's height floor, every displacement of the
original family is bounded by the corresponding displacement of the deformed family times the
explicit factor `sqrt ((base ^ 2 + a ^ 2) / base ^ 2)`, uniformly in the index. -/
theorem sq_im_le_of_mass {a : ℝ} (ha : 1 / 2 ≤ a) (i : ι) :
    F.base ^ 2 * (F.pt i).im ^ 2
      ≤ (F.base ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2 := by
  have hpoint := F.sq_re_mul_sq_im_le ha i
  have hbase := F.base_le i
  have hbpos := F.base_pos
  have hprod := F.re_mul_im_mass ha i
  have hsq : ((F.mass ha).pt i).re ^ 2 * ((F.mass ha).pt i).im ^ 2
      = (F.pt i).re ^ 2 * (F.pt i).im ^ 2 := by
    have := congrArg (fun t : ℝ => t ^ 2) hprod
    simpa [mul_pow] using this
  have hcap : ((F.mass ha).pt i).re ^ 2 ≤ (F.pt i).re ^ 2 + a ^ 2 := by
    rw [mass_pt, csqrt_re]; exact F.sq_csqrtRe_massArg_le ha i
  have hR2 : 0 < (F.pt i).re ^ 2 := by
    have := F.re_pos i; positivity
  have hb2 : F.base ^ 2 ≤ (F.pt i).re ^ 2 := by nlinarith
  have hj2 : (0 : ℝ) ≤ ((F.mass ha).pt i).im ^ 2 := sq_nonneg _
  have key : (F.pt i).re ^ 2 * (F.base ^ 2 * (F.pt i).im ^ 2)
      ≤ (F.pt i).re ^ 2 * ((F.base ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hpoint (sq_nonneg F.base),
      mul_nonneg (mul_nonneg (sq_nonneg a) hj2) (sub_nonneg.mpr hb2)]
  exact le_of_mul_le_mul_left key hR2

/-! ### Transfer of the criteria -/

/-- **The line criterion transfers.**  A bounded vertical line for the mass-shifted trace makes the
*original* family real.  For `a = 1/2` this is the abstract form of the mass-shifted criterion; the
deformation is the one that makes the trace prime-accessible. -/
theorem im_eq_zero_of_mass_line_bound [Nonempty ι] {a σ C : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖(F.mass ha).traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ i : ι, (F.pt i).im = 0 := by
  intro i
  exact (F.mass_im_eq_zero_iff ha i).mp ((F.mass ha).im_eq_zero_of_line_bound_all hσ hline i)

/-- **The line criterion is an equivalence.** -/
theorem im_eq_zero_iff_exists_mass_line_bound [Nonempty ι] {a : ℝ} (ha : 1 / 2 ≤ a) :
    (∀ i : ι, (F.pt i).im = 0) ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ, ‖(F.mass ha).traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  constructor
  · intro him
    refine (F.mass ha).im_eq_zero_iff_exists_line_bound.mp fun i => ?_
    exact (F.mass_im_eq_zero_iff ha i).mpr (him i)
  · rintro ⟨σ, C, hσ, hline⟩
    exact F.im_eq_zero_of_mass_line_bound ha hσ hline

/-- **A defect bound for the deformed family is an explicit zero-free region for the original
one.**  The deformation costs a factor `(base ^ 2 + a ^ 2) / base ^ 2` from the distortion and a
factor `exp (σ a)` from the raised heights; both are explicit and bounded. -/
theorem sq_im_le_of_mass_defect_le {a σ M : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ)
    (hσ' : σ ≤ 2 * Real.pi) (h : (F.mass ha).defect σ ≤ M) (i : ι) :
    F.base ^ 2 * (F.pt i).im ^ 2
      ≤ (F.base ^ 2 + a ^ 2) *
        (Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * a) * Real.exp (σ * (F.pt i).re)) := by
  have hmass := (F.mass ha).sq_im_le_of_defect_le hσ hσ' h i
  have hheight : ((F.mass ha).pt i).re ≤ (F.pt i).re + a := by
    rw [mass_pt, csqrt_re]; exact F.csqrtRe_massArg_le_add ha i
  have hexp : Real.exp (σ * ((F.mass ha).pt i).re) ≤ Real.exp (σ * a) * Real.exp (σ * (F.pt i).re) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hMnn : 0 ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M := by
    have hd := (F.mass ha).defect_nonneg hσ
    have : (0 : ℝ) ≤ M := le_trans hd h
    positivity
  have hstep : ((F.mass ha).pt i).im ^ 2
      ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * a) * Real.exp (σ * (F.pt i).re) := by
    refine le_trans hmass ?_
    calc Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * ((F.mass ha).pt i).re)
        ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M *
            (Real.exp (σ * a) * Real.exp (σ * (F.pt i).re)) :=
          mul_le_mul_of_nonneg_left hexp hMnn
      _ = Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * a) * Real.exp (σ * (F.pt i).re) := by
          ring
  have hfaith := F.sq_im_le_of_mass ha i
  have hbpos : 0 < F.base ^ 2 + a ^ 2 := by nlinarith [F.base_pos, ha]
  nlinarith [hfaith, hstep, hbpos]

/-! ### The deformation semigroup -/

/-- **The mass deformations compose additively in `a ^ 2`.** -/
theorem mass_mass_pt {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) (i : ι) :
    ((F.mass ha).mass hb).pt i = csqrt (F.pt i ^ 2 + (((a ^ 2 + b ^ 2 : ℝ)) : ℂ)) := by
  rw [mass_pt, massArg, F.mass_pt_sq ha i]
  congr 1
  push_cast
  ring

/-- The composite of two mass shifts is the mass shift of the Pythagorean sum. -/
theorem mass_mass_pt_eq_mass_pt {a b c : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) (hc : 1 / 2 ≤ c)
    (hsum : c ^ 2 = a ^ 2 + b ^ 2) (i : ι) :
    ((F.mass ha).mass hb).pt i = (F.mass hc).pt i := by
  rw [F.mass_mass_pt ha hb i, mass_pt, massArg, hsum]

end AbstractSpectralFamily

end

end HTGeometry

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-! ### Global faithfulness: the displacement energies are comparable -/

theorem weight_mass_le {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) (i : ι) :
    (F.mass ha).weight σ i ≤ F.weight σ i := by
  rw [weight, weight, mass_pt, csqrt_re]
  exact Real.exp_le_exp.mpr (by nlinarith [F.re_lt_csqrtRe_massArg ha i])

theorem weight_le_weight_mass {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) (i : ι) :
    Real.exp (-(σ * a)) * F.weight σ i ≤ (F.mass ha).weight σ i := by
  rw [weight, weight, mass_pt, csqrt_re, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [F.csqrtRe_massArg_le_add ha i])

/-- **The mass deformation never increases the displacement energy.** -/
theorem energy_mass_le {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) :
    (F.mass ha).energy σ ≤ F.energy σ := by
  refine Summable.tsum_le_tsum (fun i => ?_) ((F.mass ha).summable_energyTerm hσ)
    (F.summable_energyTerm hσ)
  have hw := F.weight_mass_le ha hσ i
  have hj : ((F.mass ha).pt i).im ^ 2 ≤ (F.pt i).im ^ 2 := by
    have h := F.abs_csqrtIm_massArg_le ha i
    rw [mass_pt, csqrt_im]
    nlinarith [abs_nonneg (csqrtIm (F.massArg a i)), abs_nonneg ((F.pt i).im),
      sq_abs (csqrtIm (F.massArg a i)), sq_abs ((F.pt i).im)]
  have hwpos := (F.mass ha).weight_pos σ i
  have hwpos' := F.weight_pos σ i
  nlinarith [sq_nonneg (((F.mass ha).pt i).im), sq_nonneg ((F.pt i).im)]

/-- **The mass deformation loses only an explicit bounded factor of the energy.**  Together with
`energy_mass_le` this makes the deformed and undeformed displacement energies comparable, so the
prime-accessible carrier carries the same global invariant up to explicit constants. -/
theorem energy_le_mass_energy {a σ : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ) :
    F.base ^ 2 * (Real.exp (-(σ * a)) * F.energy σ)
      ≤ (F.base ^ 2 + a ^ 2) * (F.mass ha).energy σ := by
  have hleft : F.base ^ 2 * (Real.exp (-(σ * a)) * F.energy σ)
      = ∑' i : ι, F.base ^ 2 * Real.exp (-(σ * a)) * (F.weight σ i * (F.pt i).im ^ 2) := by
    rw [energy, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun i => by ring
  have hright : (F.base ^ 2 + a ^ 2) * (F.mass ha).energy σ
      = ∑' i : ι, (F.base ^ 2 + a ^ 2) *
          ((F.mass ha).weight σ i * ((F.mass ha).pt i).im ^ 2) := by
    rw [energy, ← tsum_mul_left]
  rw [hleft, hright]
  refine Summable.tsum_le_tsum (fun i => ?_)
    ((F.summable_energyTerm hσ).mul_left _)
    (((F.mass ha).summable_energyTerm hσ).mul_left _)
  have hfaith := F.sq_im_le_of_mass ha i
  have hw := F.weight_le_weight_mass ha hσ i
  have hwpos := F.weight_pos σ i
  have hexp : (0 : ℝ) < Real.exp (-(σ * a)) := Real.exp_pos _
  have hja : (0 : ℝ) ≤ ((F.mass ha).pt i).im ^ 2 := sq_nonneg _
  have hstep : Real.exp (-(σ * a)) * F.weight σ i * (F.base ^ 2 * (F.pt i).im ^ 2)
      ≤ (F.mass ha).weight σ i * ((F.base ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2) := by
    have h1 : Real.exp (-(σ * a)) * F.weight σ i *
        (F.base ^ 2 * (F.pt i).im ^ 2)
        ≤ Real.exp (-(σ * a)) * F.weight σ i *
          ((F.base ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2) :=
      mul_le_mul_of_nonneg_left hfaith (by positivity)
    have h2 : Real.exp (-(σ * a)) * F.weight σ i *
        ((F.base ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2)
        ≤ (F.mass ha).weight σ i *
          ((F.base ^ 2 + a ^ 2) * ((F.mass ha).pt i).im ^ 2) := by
      refine mul_le_mul_of_nonneg_right hw ?_
      have : (0 : ℝ) ≤ F.base ^ 2 + a ^ 2 := by positivity
      exact mul_nonneg this hja
    linarith
  nlinarith [hstep]

end AbstractSpectralFamily

end

end HTGeometry
