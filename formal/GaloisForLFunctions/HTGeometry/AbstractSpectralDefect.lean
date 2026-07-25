import GaloisForLFunctions.HTGeometry.AbstractSpectralFamily
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The defect of an abstract spectral family

At real time the trace and its majorant differ by

`traceReal σ - Re (traceC σ) = ∑ᵢ exp (-(σ Re αᵢ)) (1 - cos (σ Im αᵢ)) ≥ 0`,

a manifestly nonnegative quantity, quadratic in the displacements to leading order.  It vanishes at
one real time `σ ∈ (0, 4π]` exactly when every point is real: the displacement bound `|Im α| < 1/2`
confines `σ Im α` to `(-2π, 2π)`, where `cos = 1` forces the argument to vanish.

Where the vertical-line criterion is a uniform bound along a whole line, this is a single scalar
equation at a single point.  Both are equivalent to reality of the spectrum; the defect is the form
in which the obstruction is an energy rather than an estimate, and its evenness in the displacements
is forced -- conjugation stability kills every odd functional of them.
-/

open Complex
open scoped BigOperators

namespace HTGeometry

namespace AbstractSpectralFamily

noncomputable section

variable {ι : Type*} (F : AbstractSpectralFamily ι)

theorem re_term_ofReal (σ : ℝ) (i : ι) :
    (F.term (σ : ℂ) i).re = F.weight σ i * Real.cos (σ * (F.pt i).im) := by
  have hre : (-(σ : ℂ) * F.pt i).re = -(σ * (F.pt i).re) := by simp [Complex.mul_re]
  have him : (-(σ : ℂ) * F.pt i).im = -(σ * (F.pt i).im) := by simp [Complex.mul_im]
  rw [term, Complex.exp_re, hre, him, Real.cos_neg, weight]

theorem summable_weight_mul_cos {σ : ℝ} (hσ : 0 < σ) :
    Summable fun i => F.weight σ i * Real.cos (σ * (F.pt i).im) := by
  refine Summable.of_norm_bounded (F.summable_weight hσ) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (F.weight_pos σ i)]
  calc F.weight σ i * |Real.cos (σ * (F.pt i).im)|
      ≤ F.weight σ i * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (F.weight_pos σ i).le
    _ = F.weight σ i := mul_one _

theorem re_traceC_ofReal {σ : ℝ} (hσ : 0 < σ) :
    (F.traceC (σ : ℂ)).re = ∑' i : ι, F.weight σ i * Real.cos (σ * (F.pt i).im) := by
  have hre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  rw [traceC, Complex.re_tsum ((F.summable_norm_term hre).of_norm)]
  exact tsum_congr fun i => F.re_term_ofReal σ i

/-- The gap between the real-time trace and its majorant. -/
def defect (σ : ℝ) : ℝ := F.traceReal σ - (F.traceC (σ : ℂ)).re

theorem summable_defectTerm {σ : ℝ} (hσ : 0 < σ) :
    Summable fun i => F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) := by
  refine Summable.of_norm_bounded ((F.summable_weight hσ).mul_left 2) fun i => ?_
  have hc : |1 - Real.cos (σ * (F.pt i).im)| ≤ 2 := by
    have h1 := Real.neg_one_le_cos (σ * (F.pt i).im)
    have h2 := Real.cos_le_one (σ * (F.pt i).im)
    rw [abs_le]
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (F.weight_pos σ i)]
  calc F.weight σ i * |1 - Real.cos (σ * (F.pt i).im)|
      ≤ F.weight σ i * 2 := mul_le_mul_of_nonneg_left hc (F.weight_pos σ i).le
    _ = 2 * F.weight σ i := by ring

/-- **The defect is a nonnegative sum, term by term.** -/
theorem defect_eq_tsum {σ : ℝ} (hσ : 0 < σ) :
    F.defect σ = ∑' i : ι, F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) := by
  have hw : Summable fun i : ι => F.weight σ i := F.summable_weight hσ
  rw [defect, F.re_traceC_ofReal hσ, traceReal,
    ← Summable.tsum_sub hw (F.summable_weight_mul_cos hσ)]
  exact tsum_congr fun i => by ring

theorem defectTerm_nonneg (σ : ℝ) (i : ι) :
    0 ≤ F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) :=
  mul_nonneg (F.weight_pos σ i).le (by linarith [Real.cos_le_one (σ * (F.pt i).im)])

theorem defect_nonneg {σ : ℝ} (hσ : 0 < σ) : 0 ≤ F.defect σ := by
  rw [F.defect_eq_tsum hσ]
  exact tsum_nonneg fun i => F.defectTerm_nonneg σ i

/-- **A vanishing defect at one admissible real time makes the family real.** -/
theorem im_eq_zero_of_defect_eq_zero {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi)
    (h : F.defect σ = 0) : ∀ i : ι, (F.pt i).im = 0 := by
  intro i
  have hup : F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) ≤ 0 := by
    have hb := (F.summable_defectTerm hσ).le_tsum i fun j _ => F.defectTerm_nonneg σ j
    rw [← F.defect_eq_tsum hσ, h] at hb
    exact hb
  have hz : F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) = 0 :=
    le_antisymm hup (F.defectTerm_nonneg σ i)
  have hcos : Real.cos (σ * (F.pt i).im) = 1 := by
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact absurd h1 (ne_of_gt (F.weight_pos σ i))
    · linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : |σ * (F.pt i).im| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos hσ]
    calc σ * |(F.pt i).im| < σ * (1 / 2) :=
          mul_lt_mul_of_pos_left (F.abs_im_lt i) hσ
      _ ≤ (4 * Real.pi) * (1 / 2) := by nlinarith
      _ = 2 * Real.pi := by ring
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hzero : σ * (F.pt i).im = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).mp hcos
  rcases mul_eq_zero.mp hzero with h1 | h1
  · exact absurd h1 (ne_of_gt hσ)
  · exact h1

theorem defect_eq_zero_of_im_eq_zero {σ : ℝ} (hσ : 0 < σ)
    (him : ∀ i : ι, (F.pt i).im = 0) : F.defect σ = 0 := by
  rw [F.defect_eq_tsum hσ]
  have hz : ∀ i : ι, F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) = 0 := by
    intro i
    rw [him i, mul_zero, Real.cos_zero]
    ring
  rw [tsum_congr hz, tsum_zero]

/-- **The defect criterion.**  For an admissible family and any real time `σ ∈ (0, 4π]`, the single
scalar equation `traceReal σ = Re (traceC σ)` is equivalent to reality of the whole family. -/
theorem im_eq_zero_iff_defect_eq_zero {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi) :
    (∀ i : ι, (F.pt i).im = 0) ↔ F.defect σ = 0 :=
  ⟨fun him => F.defect_eq_zero_of_im_eq_zero hσ him,
    fun h => F.im_eq_zero_of_defect_eq_zero hσ hle h⟩

/-- Jordan's inequality in quadratic form: on `[-π, π]` the cosine defect is bounded below by a
multiple of the square. -/
theorem two_div_pi_sq_mul_sq_le_one_sub_cos {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set t : ℝ := |x| / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t ≤ Real.pi / 2 := by rw [ht]; linarith
  have hcos : Real.cos x = 1 - 2 * Real.sin t ^ 2 := by
    rw [← Real.cos_abs, show |x| = 2 * t from by rw [ht]; ring, Real.cos_two_mul_eq_one_sub]
  have hjor : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin ht0 ht2
  have hnn : 0 ≤ 2 / Real.pi * t := by positivity
  have hsq : (2 / Real.pi * t) ^ 2 ≤ Real.sin t ^ 2 := by
    exact pow_le_pow_left₀ hnn hjor 2
  have hxt : x ^ 2 = 4 * t ^ 2 := by
    rw [ht, div_pow, sq_abs]
    ring
  rw [hcos, hxt]
  have hexp : (2 / Real.pi * t) ^ 2 = 4 / Real.pi ^ 2 * t ^ 2 := by
    rw [mul_pow, div_pow]
    ring
  rw [hexp] at hsq
  have heq : 2 / Real.pi ^ 2 * (4 * t ^ 2) = 2 * (4 / Real.pi ^ 2 * t ^ 2) := by ring
  rw [heq]
  linarith [hsq]

theorem defectTerm_le_defect {σ : ℝ} (hσ : 0 < σ) (i : ι) :
    F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) ≤ F.defect σ := by
  have hb := (F.summable_defectTerm hσ).le_tsum i fun j _ => F.defectTerm_nonneg σ j
  rwa [← F.defect_eq_tsum hσ] at hb

/-- **Quantitative rigidity.**  On the admissible range `σ ≤ 2π` the defect dominates a positive
multiple of every single weighted squared displacement. -/
theorem sq_im_mul_weight_le_defect {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) (i : ι) :
    2 * σ ^ 2 / Real.pi ^ 2 * ((F.pt i).im ^ 2 * F.weight σ i) ≤ F.defect σ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : |σ * (F.pt i).im| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hσ]
    calc σ * |(F.pt i).im| ≤ σ * (1 / 2) :=
          mul_le_mul_of_nonneg_left (F.abs_im_lt i).le hσ.le
      _ ≤ (2 * Real.pi) * (1 / 2) := by nlinarith
      _ = Real.pi := by ring
  have hlow := two_div_pi_sq_mul_sq_le_one_sub_cos habs
  have hmul : F.weight σ i * (2 / Real.pi ^ 2 * (σ * (F.pt i).im) ^ 2) ≤
      F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) :=
    mul_le_mul_of_nonneg_left hlow (F.weight_pos σ i).le
  refine le_trans (le_of_eq ?_) (le_trans hmul (F.defectTerm_le_defect hσ i))
  ring

/-- **A defect bound is a zero-free region.**  An upper bound `M` for the defect at one admissible
real time bounds every displacement explicitly, with a loss growing only like `exp(σ Re α / 2)`. -/
theorem sq_im_le_of_defect_le {σ M : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi)
    (h : F.defect σ ≤ M) (i : ι) :
    (F.pt i).im ^ 2 ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M * Real.exp (σ * (F.pt i).re) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkey := le_trans (F.sq_im_mul_weight_le_defect hσ hσ' i) h
  have hw : F.weight σ i = Real.exp (-(σ * (F.pt i).re)) := rfl
  have hwpos : 0 < F.weight σ i := F.weight_pos σ i
  have hinv : F.weight σ i * Real.exp (σ * (F.pt i).re) = 1 := by
    rw [hw, ← Real.exp_add]
    simp
  have hσ2 : 0 < 2 * σ ^ 2 / Real.pi ^ 2 := by positivity
  have hstep : (F.pt i).im ^ 2 * F.weight σ i ≤ Real.pi ^ 2 / (2 * σ ^ 2) * M := by
    rw [← le_div_iff₀' hσ2] at hkey
    refine le_trans hkey (le_of_eq ?_)
    field_simp
  calc (F.pt i).im ^ 2
      = ((F.pt i).im ^ 2 * F.weight σ i) * Real.exp (σ * (F.pt i).re) := by
        rw [mul_assoc, hinv, mul_one]
    _ ≤ (Real.pi ^ 2 / (2 * σ ^ 2) * M) * Real.exp (σ * (F.pt i).re) :=
        mul_le_mul_of_nonneg_right hstep (Real.exp_pos _).le

/-- The weighted displacement energy. -/
def energy (σ : ℝ) : ℝ := ∑' i : ι, F.weight σ i * (F.pt i).im ^ 2

theorem summable_energyTerm {σ : ℝ} (hσ : 0 < σ) :
    Summable fun i => F.weight σ i * (F.pt i).im ^ 2 := by
  refine Summable.of_norm_bounded ((F.summable_weight hσ).mul_left (1 / 4)) fun i => ?_
  have hb : (F.pt i).im ^ 2 ≤ 1 / 4 := by
    have h := F.abs_im_lt i
    nlinarith [abs_nonneg ((F.pt i).im), sq_abs ((F.pt i).im)]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (F.weight_pos σ i), abs_of_nonneg (sq_nonneg _)]
  calc F.weight σ i * (F.pt i).im ^ 2 ≤ F.weight σ i * (1 / 4) :=
        mul_le_mul_of_nonneg_left hb (F.weight_pos σ i).le
    _ = 1 / 4 * F.weight σ i := by ring

theorem energy_nonneg (σ : ℝ) : 0 ≤ F.energy σ :=
  tsum_nonneg fun i => mul_nonneg (F.weight_pos σ i).le (sq_nonneg _)

/-- **The defect is bounded above by the energy.**  This is the second-order expansion of the cosine,
valid at every real time. -/
theorem defect_le_energy {σ : ℝ} (hσ : 0 < σ) : F.defect σ ≤ σ ^ 2 / 2 * F.energy σ := by
  rw [F.defect_eq_tsum hσ, energy, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_defectTerm hσ)
    ((F.summable_energyTerm hσ).mul_left _)
  have hcos : 1 - Real.cos (σ * (F.pt i).im) ≤ (σ * (F.pt i).im) ^ 2 / 2 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := σ * (F.pt i).im)
    linarith
  calc F.weight σ i * (1 - Real.cos (σ * (F.pt i).im))
      ≤ F.weight σ i * ((σ * (F.pt i).im) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcos (F.weight_pos σ i).le
    _ = σ ^ 2 / 2 * (F.weight σ i * (F.pt i).im ^ 2) := by ring

/-- **The defect is bounded below by the energy on the admissible range.**  Together with
`defect_le_energy` the two are comparable: `defect σ ≍ σ² · energy σ`. -/
theorem energy_le_defect {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) :
    2 * σ ^ 2 / Real.pi ^ 2 * F.energy σ ≤ F.defect σ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [F.defect_eq_tsum hσ, energy, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) ((F.summable_energyTerm hσ).mul_left _)
    (F.summable_defectTerm hσ)
  have habs : |σ * (F.pt i).im| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hσ]
    calc σ * |(F.pt i).im| ≤ σ * (1 / 2) :=
          mul_le_mul_of_nonneg_left (F.abs_im_lt i).le hσ.le
      _ ≤ (2 * Real.pi) * (1 / 2) := by nlinarith
      _ = Real.pi := by ring
  have hlow := two_div_pi_sq_mul_sq_le_one_sub_cos habs
  calc 2 * σ ^ 2 / Real.pi ^ 2 * (F.weight σ i * (F.pt i).im ^ 2)
      = F.weight σ i * (2 / Real.pi ^ 2 * (σ * (F.pt i).im) ^ 2) := by ring
    _ ≤ F.weight σ i * (1 - Real.cos (σ * (F.pt i).im)) :=
        mul_le_mul_of_nonneg_left hlow (F.weight_pos σ i).le

/-- **The energy criterion.**  Reality of the family is the vanishing of the weighted displacement
energy at any one admissible real time. -/
theorem im_eq_zero_iff_energy_eq_zero {σ : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 2 * Real.pi) :
    (∀ i : ι, (F.pt i).im = 0) ↔ F.energy σ = 0 := by
  constructor
  · intro him
    rw [energy]
    have hz : ∀ i : ι, F.weight σ i * (F.pt i).im ^ 2 = 0 := by
      intro i; rw [him i]; ring
    rw [tsum_congr hz, tsum_zero]
  · intro h
    have hd : F.defect σ ≤ 0 := by
      have := F.defect_le_energy hσ
      rw [h, mul_zero] at this
      exact this
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    exact F.im_eq_zero_of_defect_eq_zero hσ (by nlinarith)
      (le_antisymm hd (F.defect_nonneg hσ))

/-- **RH-shaped form.**  One inequality between two real numbers, whose converse is unconditional:
the trace never exceeds its majorant, and equality at one admissible time is reality. -/
theorem im_eq_zero_iff_traceReal_le {σ : ℝ} (hσ : 0 < σ) (hle : σ ≤ 4 * Real.pi) :
    (∀ i : ι, (F.pt i).im = 0) ↔ F.traceReal σ ≤ (F.traceC (σ : ℂ)).re := by
  rw [F.im_eq_zero_iff_defect_eq_zero hσ hle, defect, sub_eq_zero]
  constructor
  · exact le_of_eq
  · intro h
    have hge : (F.traceC (σ : ℂ)).re ≤ F.traceReal σ := by
      have hd := F.defect_nonneg hσ
      rw [defect] at hd
      linarith
    exact le_antisymm h hge

/-- The energy decays at least at the base-height rate. -/
theorem energy_le_exp_mul_energy {σ σ' : ℝ} (hσ : 0 < σ) (h : σ ≤ σ') :
    F.energy σ' ≤ Real.exp (-((σ' - σ) * F.base)) * F.energy σ := by
  have hσ' : 0 < σ' := lt_of_lt_of_le hσ h
  rw [energy, energy, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_energyTerm hσ')
    ((F.summable_energyTerm hσ).mul_left _)
  have hw : F.weight σ' i ≤ Real.exp (-((σ' - σ) * F.base)) * F.weight σ i := by
    rw [weight, weight, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [F.base_le i, F.base_pos, sub_nonneg.mpr h]
  calc F.weight σ' i * (F.pt i).im ^ 2
      ≤ (Real.exp (-((σ' - σ) * F.base)) * F.weight σ i) * (F.pt i).im ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = Real.exp (-((σ' - σ) * F.base)) * (F.weight σ i * (F.pt i).im ^ 2) := by ring

/-- **A zero-density bound from an energy bound.**  If the energy at time `σ` is at most `M`, then
any finite set of points of height at most `T` whose displacements all exceed `η` has at most
`M exp(σ T) / η²` elements. -/
theorem card_le_of_energy_le {σ M T η : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (h : F.energy σ ≤ M) (s : Finset ι)
    (hs : ∀ i ∈ s, (F.pt i).re ≤ T ∧ η ≤ |(F.pt i).im|) :
    (s.card : ℝ) * (η ^ 2 * Real.exp (-(σ * T))) ≤ M := by
  have hsub : ∑ i ∈ s, F.weight σ i * (F.pt i).im ^ 2 ≤ F.energy σ :=
    (F.summable_energyTerm hσ).sum_le_tsum s
      (fun i _ => mul_nonneg (F.weight_pos σ i).le (sq_nonneg _))
  have hterm : ∀ i ∈ s, η ^ 2 * Real.exp (-(σ * T)) ≤ F.weight σ i * (F.pt i).im ^ 2 := by
    intro i hi
    obtain ⟨hT, hη'⟩ := hs i hi
    have hw : Real.exp (-(σ * T)) ≤ F.weight σ i := by
      rw [weight]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hj : η ^ 2 ≤ (F.pt i).im ^ 2 := by
      rw [← sq_abs ((F.pt i).im)]
      exact pow_le_pow_left₀ hη.le hη' 2
    calc η ^ 2 * Real.exp (-(σ * T)) ≤ η ^ 2 * F.weight σ i :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ ≤ (F.pt i).im ^ 2 * F.weight σ i :=
          mul_le_mul_of_nonneg_right hj (F.weight_pos σ i).le
      _ = F.weight σ i * (F.pt i).im ^ 2 := by ring
  have hcard : (s.card : ℝ) * (η ^ 2 * Real.exp (-(σ * T))) ≤
      ∑ i ∈ s, F.weight σ i * (F.pt i).im ^ 2 := by
    calc (s.card : ℝ) * (η ^ 2 * Real.exp (-(σ * T)))
        = ∑ _i ∈ s, η ^ 2 * Real.exp (-(σ * T)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, F.weight σ i * (F.pt i).im ^ 2 := Finset.sum_le_sum hterm
  linarith [hcard, hsub, h]

/-- The energy never exceeds a quarter of the majorant: the displacement bound `|Im α| < 1/2` caps
it termwise. -/
theorem energy_le_quarter_traceReal {σ : ℝ} (hσ : 0 < σ) :
    F.energy σ ≤ 1 / 4 * F.traceReal σ := by
  have hw : Summable fun i : ι => F.weight σ i := F.summable_weight hσ
  rw [energy, traceReal, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (F.summable_energyTerm hσ) (hw.mul_left _)
  have hb : (F.pt i).im ^ 2 ≤ 1 / 4 := by
    have h := F.abs_im_lt i
    nlinarith [abs_nonneg ((F.pt i).im), sq_abs ((F.pt i).im)]
  calc F.weight σ i * (F.pt i).im ^ 2 ≤ F.weight σ i * (1 / 4) :=
        mul_le_mul_of_nonneg_left hb (F.weight_pos σ i).le
    _ = 1 / 4 * F.weight σ i := by ring

/-- **The defect is a relative-`σ²` quantity.**  Unconditionally the gap between the trace and its
majorant is at most `σ²/8` of the majorant. -/
theorem defect_le_traceReal {σ : ℝ} (hσ : 0 < σ) :
    F.defect σ ≤ σ ^ 2 / 8 * F.traceReal σ := by
  refine le_trans (F.defect_le_energy hσ) ?_
  have h := F.energy_le_quarter_traceReal hσ
  have hpos : (0 : ℝ) ≤ σ ^ 2 / 2 := by positivity
  calc σ ^ 2 / 2 * F.energy σ ≤ σ ^ 2 / 2 * (1 / 4 * F.traceReal σ) :=
        mul_le_mul_of_nonneg_left h hpos
    _ = σ ^ 2 / 8 * F.traceReal σ := by ring

/-- **The unconditional window.**  The real part of the trace at real time is within a relative
`σ²/8` of the majorant, with no hypothesis on the family beyond admissibility; reality of the family
is exactly the assertion that the factor can be taken to be `1`. -/
theorem traceReal_mul_le_re_traceC {σ : ℝ} (hσ : 0 < σ) :
    (1 - σ ^ 2 / 8) * F.traceReal σ ≤ (F.traceC (σ : ℂ)).re := by
  have h := F.defect_le_traceReal hσ
  rw [defect] at h
  nlinarith [h]

end

end AbstractSpectralFamily

end HTGeometry
