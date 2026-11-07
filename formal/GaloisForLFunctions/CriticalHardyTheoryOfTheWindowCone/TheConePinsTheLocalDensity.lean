import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheDatumOfTheWindowCone
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowConeCollapses
import GaloisForLFunctions.RHTower.EvenSectorFarBumpPoleFreeCombination

/-!
# The cone pins the local density of its weights at square-root precision

Let `φ` be the far-bump profile (an even bump of radius `≤ 1/12`), `k = φ ⋆ φ̃`, `J = ∫ φ(x) e^{−x/2} dx`,
and for a weight system `λ` let

  `S_λ(a) = Σ_{n ≥ 2} λ(n) n^{−1/2} k(log n − 2a)`

be its smoothed sum over the integers with `|log n − 2a| ≤ 1/6`. The two far bumps `φ(· − a) ± φ(· + a)` are
window tests for `a + 1 ≤ c`. Their pole terms are `±2J²(e^{a/2} ± e^{−a/2})²`, their atoms are `±2S_λ(a)`,
and their archimedean energies and masses are bounded uniformly in `a`. Positivity of the datum energy on the two
tests gives, for every point of the cone of the datum `(β, s)` (`farSum_mem_Icc_of_mem_datumCone`),

  `β J² (e^{a/2} − e^{−a/2})² − D_s ≤ S_λ(a) ≤ β J² (e^{a/2} + e^{−a/2})² + D_s`,

with `D_s = A + 2|s| ∫φ` absolute (`localDensityConst`). Hence:

* **Local density law** (`abs_farSum_sub_le_of_mem_windowCone`). Every `λ ∈ 𝒜(c)` has
  `|S_λ(a) − J² e^a| ≤ 3J² + D₀` for `0 ≤ a ≤ c − 1`. Normalized by `e^a ≈ Σ n^{−1/2} k(log n − 2a)/J²`, the local
  density of `λ` near `e^{2a}` is `1 + O(e^{−a})`: a square-root error at every scale of the box, not only on the
  pinned range `n ≲ c` of individual atoms.
* **The pole weight is the density** (`abs_farSum_sub_le_of_mem_datumCone`). On the cone of `(β, s)` the local
  density is `β + O((1 + |β| + |s|) e^{−a})`. No-pole data have bounded local sums.
* **Data separate** (`abs_sub_le_of_mem_datumCone_inter`, `datumCone_inter_eq_empty`). A weight system in the
  cones of `(β, s)` and `(β', s')` at the window `c ≥ 1` has `|β − β'| ≤ K(1 + |β| + |β'| + |s| + |s'|) e^{−c}`:
  cones of distinct pole weights are disjoint from a finite window on.
* **Diameter in local averages** (`abs_farSum_sub_farSum_le`). Two points of `𝒜(c)` have local sums within
  `4J² + 2D₀` at every scale `a ≤ c − 1`, against the box, which allows `e^a log` deviations.

What this does not say about `ζ`: it is a statement about points of the cone. For `Λ` the error `O(1)` is the size
of the zero sum `Σ_ρ |φ̂(γ)|² cos²(aγ)`, which is bounded exactly when no zero is off the line; so the local law for
`Λ` at every scale is RH, and an off-line zero makes `S_Λ(a) − J²e^a` grow like `e^{2δa}`, which is why the cones
empty. The law is uniform in `c` only through the cone, which is empty off RH.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.OddSector _root_.RHTower.EvenSector _root_.Zeta23

/-! ### The two far bumps are window tests -/

theorem oddFarBump_eq_zero {a x : ℝ} (ha : 0 ≤ a) (hx : a + 1 < |x|) : oddFarBump a x = 0 := by
  have hr := nodeBump_rOut_le 2
  have h1 := abs_sub_abs_le_abs_sub x a
  have h2 := abs_sub_abs_le_abs_sub x (-a)
  rw [abs_of_nonneg ha] at h1
  rw [abs_neg, abs_of_nonneg ha, sub_neg_eq_add] at h2
  unfold oddFarBump
  rw [farBump_eq_zero (by linarith), farBump_eq_zero (by linarith), sub_zero]

theorem tsupport_ofReal_oddFarBump_subset {a c : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    tsupport (fun u => ((oddFarBump a u : ℝ) : ℂ)) ⊆ Icc (-c) c :=
  (tsupport_ofReal_subset_Icc_of_abs_gt fun _ hx => oddFarBump_eq_zero ha hx).trans
    (Icc_subset_Icc (by linarith) hac)

theorem tsupport_ofReal_evenFarBump_subset {a c : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    tsupport (fun u => ((evenFarBump a u : ℝ) : ℂ)) ⊆ Icc (-c) c :=
  (tsupport_ofReal_subset_Icc_of_abs_gt fun _ hx => evenFarBump_eq_zero ha hx).trans
    (Icc_subset_Icc (by linarith) hac)

/-! ### Uniform bounds on the archimedean energy and the mass -/

theorem abs_farArch_oddFarBump_le (a : ℝ) :
    |farArch (oddFarBump a)| ≤ 1 / (2 * Real.pi) * farBumpArchMass :=
  (abs_farArch_le (oddFarBump a)).trans (mul_le_mul_of_nonneg_left
    (integral_normSq_mul_abs_gammaBracket_le 2 (norm_paperFT_oddFarBump_le a)) (by positivity))

theorem integrable_farBump_shift (b : ℝ) : Integrable fun x => farBump (x - b) :=
  (continuous_farBump.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
    (hasCompactSupport_farBump.comp_homeomorph (Homeomorph.subRight b))

theorem integral_farBump_shift (b : ℝ) : ∫ x, farBump (x - b) = farMass :=
  integral_sub_right_eq_self (fun x => farBump x) b

/-- A two-bump test `φ(· − a) + σ φ(· + a)`, `|σ| ≤ 1`, has mass at most `4 ∫φ`. -/
theorem integral_twoBump_sq_le (a : ℝ) {σ : ℝ} (hσ : |σ| ≤ 1) :
    ∫ x, ‖(((farBump (x - a) + σ * farBump (x + a) : ℝ)) : ℂ)‖ ^ 2 ≤ 4 * farMass := by
  have hi : Integrable fun x => 2 * farBump (x - a) + 2 * farBump (x - (-a)) :=
    ((integrable_farBump_shift a).const_mul 2).add ((integrable_farBump_shift (-a)).const_mul 2)
  have hval : ∫ x, (2 * farBump (x - a) + 2 * farBump (x - (-a))) = 4 * farMass := by
    rw [integral_add ((integrable_farBump_shift a).const_mul 2)
      ((integrable_farBump_shift (-a)).const_mul 2), integral_const_mul, integral_const_mul,
      integral_farBump_shift, integral_farBump_shift]
    ring
  rw [← hval]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hi
    (Eventually.of_forall fun x => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_neg_eq_add]
  have p0 := farBump_nonneg (x - a)
  have p1 := farBump_le_one (x - a)
  have q0 := farBump_nonneg (x + a)
  have q1 := farBump_le_one (x + a)
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [abs_nonneg σ, sq_abs σ]
  have h1 : farBump (x - a) ^ 2 ≤ farBump (x - a) := by nlinarith
  have h2 : farBump (x + a) ^ 2 ≤ farBump (x + a) := by nlinarith
  nlinarith [sq_nonneg (farBump (x - a) - σ * farBump (x + a)),
    mul_le_mul_of_nonneg_right hσ2 (sq_nonneg (farBump (x + a)))]

/-- The constant of the local law for log-conductor `s`. -/
def localDensityConst (s : ℝ) : ℝ := 1 / (4 * Real.pi) * farBumpArchMass + 2 * |s| * farMass

theorem farBumpArchMass_nonneg : 0 ≤ farBumpArchMass :=
  (integral_nonneg fun _ => by positivity).trans (integral_evenFarBump_arch_le 0)

theorem farMass_nonneg : 0 ≤ farMass := integral_nonneg farBump_nonneg

theorem localDensityConst_nonneg (s : ℝ) : 0 ≤ localDensityConst s := by
  unfold localDensityConst
  have := farBumpArchMass_nonneg
  have := farMass_nonneg
  positivity

/-! ### The datum energy of the far bumps -/

theorem datumEnergy_ofReal (β s : ℝ) (lam : ℕ → ℝ) {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    datumEnergy β s lam (fun u => (F u : ℂ)) =
      β * (weilPoleTerm (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re + farArch F -
        atomPairing lam (crossCorr F F) + s * ∫ u, ‖((F u : ℝ) : ℂ)‖ ^ 2 := by
  rw [datumEnergy_eq, re_weilFullFunctional_ofReal_eq lam hF hFc]
  ring

/-- **The far bumps bracket the local sum.** On the cone of the datum `(β, s)`, for `0 ≤ a ≤ c − 1`,
`βJ²(e^{a/2} − e^{−a/2})² − D_s ≤ S_λ(a) ≤ βJ²(e^{a/2} + e^{−a/2})² + D_s`. -/
theorem farSum_mem_Icc_of_mem_datumCone {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    β * farJ ^ 2 * (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 - localDensityConst s ≤
        farSum lam a ∧
      farSum lam a ≤
        β * farJ ^ 2 * (Real.exp (a / 2) + Real.exp (-a / 2)) ^ 2 + localDensityConst s := by
  have hpi := Real.pi_pos
  have hA := farBumpArchMass_nonneg
  have hm := farMass_nonneg
  have hsm : ∀ M : ℝ, 0 ≤ M → M ≤ 4 * farMass → |s * M| ≤ 4 * |s| * farMass := fun M h0 h1 => by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg s]
  constructor
  · -- the odd far bump
    have hcont : Continuous (oddFarBump a) := (contDiff_oddFarBump a).continuous
    have hE := h _ (contDiff_ofReal_comp (contDiff_oddFarBump a))
      (tsupport_ofReal_oddFarBump_subset ha hac)
    rw [datumEnergy_ofReal β s lam hcont (hasCompactSupport_oddFarBump a),
      atomPairing_oddFarBump lam ha] at hE
    have hodd : ∀ x, (fun u => ((oddFarBump a u : ℝ) : ℂ)) (-x) =
        -(fun u => ((oddFarBump a u : ℝ) : ℂ)) x := fun x => by
      simp only [oddFarBump_neg]; push_cast; ring
    rw [re_weilPoleTerm_weilTest_of_odd (f := fun u => ((oddFarBump a u : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hcont)
      ((hasCompactSupport_oddFarBump a).comp_left Complex.ofReal_zero) hodd,
      paperFT_ofRealFun_I_div_two, integral_oddFarBump_mul_exp, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] at hE
    have hmass := integral_twoBump_sq_le a (σ := -1) (by norm_num)
    have hmass' : ∫ u, ‖((oddFarBump a u : ℝ) : ℂ)‖ ^ 2 ≤ 4 * farMass := by
      refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => ?_)) hmass
      simp only [oddFarBump]; ring_nf
    have hM0 : 0 ≤ ∫ u, ‖((oddFarBump a u : ℝ) : ℂ)‖ ^ 2 := integral_nonneg fun _ => by positivity
    have h1 := abs_le.mp (hsm _ hM0 hmass')
    have h2 := abs_le.mp (abs_farArch_oddFarBump_le a)
    have e : ((Real.exp (-a / 2) - Real.exp (a / 2)) * farJ) ^ 2 =
        farJ ^ 2 * (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 := by ring
    rw [e] at hE
    unfold localDensityConst
    have e2 : 1 / (4 * Real.pi) * farBumpArchMass = (1 / (2 * Real.pi) * farBumpArchMass) / 2 := by
      field_simp; ring
    rw [e2]
    nlinarith
  · -- the even far bump
    have hcont : Continuous (evenFarBump a) := continuous_evenFarBump a
    have hE := h _ (contDiff_ofReal_comp (contDiff_evenFarBump a))
      (tsupport_ofReal_evenFarBump_subset ha hac)
    rw [datumEnergy_ofReal β s lam hcont (hasCompactSupport_evenFarBump a),
      atomPairing_evenFarBump lam ha,
      re_weilPoleTerm_ofReal_even hcont (hasCompactSupport_evenFarBump a) (evenFarBump_neg a),
      integral_evenFarBump_mul_exp] at hE
    have hmass := integral_twoBump_sq_le a (σ := 1) (by norm_num)
    have hmass' : ∫ u, ‖((evenFarBump a u : ℝ) : ℂ)‖ ^ 2 ≤ 4 * farMass := by
      refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => ?_)) hmass
      simp only [evenFarBump]; ring_nf
    have hM0 : 0 ≤ ∫ u, ‖((evenFarBump a u : ℝ) : ℂ)‖ ^ 2 := integral_nonneg fun _ => by positivity
    have h1 := abs_le.mp (hsm _ hM0 hmass')
    have h2 := abs_le.mp (abs_farArch_evenFarBump_le a)
    have e : ((Real.exp (-a / 2) + Real.exp (a / 2)) * farJ) ^ 2 =
        farJ ^ 2 * (Real.exp (a / 2) + Real.exp (-a / 2)) ^ 2 := by ring
    rw [e] at hE
    unfold localDensityConst
    have e2 : 1 / (4 * Real.pi) * farBumpArchMass = (1 / (2 * Real.pi) * farBumpArchMass) / 2 := by
      field_simp; ring
    rw [e2]
    nlinarith

/-! ### The local density law -/

theorem exp_half_sub_sq (a : ℝ) :
    (Real.exp (a / 2) - Real.exp (-a / 2)) ^ 2 = Real.exp a - 2 + Real.exp (-a) := by
  have h1 : Real.exp (a / 2) ^ 2 = Real.exp a := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h2 : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h3 : Real.exp (a / 2) * Real.exp (-a / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  nlinarith

theorem exp_half_add_sq (a : ℝ) :
    (Real.exp (a / 2) + Real.exp (-a / 2)) ^ 2 = Real.exp a + 2 + Real.exp (-a) := by
  have h1 : Real.exp (a / 2) ^ 2 = Real.exp a := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h2 : Real.exp (-a / 2) ^ 2 = Real.exp (-a) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h3 : Real.exp (a / 2) * Real.exp (-a / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  nlinarith

/-- **The pole weight is the local density.** On the cone of `(β, s)`, for `0 ≤ a ≤ c − 1`,
`|S_λ(a) − βJ²e^a| ≤ 3|β|J² + D_s`. -/
theorem abs_farSum_sub_le_of_mem_datumCone {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c)
    {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    |farSum lam a - β * farJ ^ 2 * Real.exp a| ≤ 3 * |β| * farJ ^ 2 + localDensityConst s := by
  obtain ⟨h1, h2⟩ := farSum_mem_Icc_of_mem_datumCone h ha hac
  rw [exp_half_sub_sq] at h1
  rw [exp_half_add_sq] at h2
  have he0 := Real.exp_pos (-a)
  have he1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hJ := sq_nonneg farJ
  have hb1 : β * farJ ^ 2 * (Real.exp a - 2 + Real.exp (-a)) =
      β * farJ ^ 2 * Real.exp a + β * farJ ^ 2 * (Real.exp (-a) - 2) := by ring
  have hb2 : β * farJ ^ 2 * (Real.exp a + 2 + Real.exp (-a)) =
      β * farJ ^ 2 * Real.exp a + β * farJ ^ 2 * (Real.exp (-a) + 2) := by ring
  rw [hb1] at h1
  rw [hb2] at h2
  have k1 : |β * farJ ^ 2 * (Real.exp (-a) - 2)| ≤ 3 * |β| * farJ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hJ]
    have : |Real.exp (-a) - 2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg β) hJ)
    linarith
  have k2 : |β * farJ ^ 2 * (Real.exp (-a) + 2)| ≤ 3 * |β| * farJ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hJ]
    have : |Real.exp (-a) + 2| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul_of_nonneg_left this (mul_nonneg (abs_nonneg β) hJ)
    linarith
  rw [abs_le]
  constructor
  · linarith [(abs_le.mp k1).1]
  · linarith [(abs_le.mp k2).2]

theorem mem_datumCone_one_zero_of_mem_windowCone {c : ℝ} {lam : ℕ → ℝ}
    (h : lam ∈ windowCone c) : lam ∈ datumCone 1 0 c := by
  rw [mem_datumCone_one_iff]
  intro f hf hfs
  rw [neg_zero, zero_mul]
  exact h f hf hfs

/-- **The local density law on the window cone.** Every `λ ∈ 𝒜(c)` has
`|S_λ(a) − J²e^a| ≤ 3J² + D₀` for `0 ≤ a ≤ c − 1`. -/
theorem abs_farSum_sub_le_of_mem_windowCone {c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ windowCone c)
    {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    |farSum lam a - farJ ^ 2 * Real.exp a| ≤ 3 * farJ ^ 2 + localDensityConst 0 := by
  have := abs_farSum_sub_le_of_mem_datumCone (mem_datumCone_one_zero_of_mem_windowCone h) ha hac
  simpa using this

/-- The local density in normalized form: `|e^{−a} S_λ(a) − J²| ≤ (3J² + D₀) e^{−a}`. -/
theorem abs_exp_neg_mul_farSum_sub_le {c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ windowCone c) {a : ℝ}
    (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    |Real.exp (-a) * farSum lam a - farJ ^ 2| ≤ (3 * farJ ^ 2 + localDensityConst 0) * Real.exp (-a) := by
  have h1 := abs_farSum_sub_le_of_mem_windowCone h ha hac
  have he : Real.exp (-a) * farSum lam a - farJ ^ 2 =
      Real.exp (-a) * (farSum lam a - farJ ^ 2 * Real.exp a) := by
    rw [mul_sub, ← mul_assoc, mul_comm (Real.exp (-a)) (farJ ^ 2), mul_assoc, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, mul_one]
  rw [he, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le

/-- **Diameter of the cone in local averages.** Two points of `𝒜(c)` have local sums within
`4J² + 2D₀` at every scale `0 ≤ a ≤ c − 1`. -/
theorem abs_farSum_sub_farSum_le {c : ℝ} {lam lam' : ℕ → ℝ} (h : lam ∈ windowCone c)
    (h' : lam' ∈ windowCone c) {a : ℝ} (ha : 0 ≤ a) (hac : a + 1 ≤ c) :
    |farSum lam a - farSum lam' a| ≤ 4 * farJ ^ 2 + 2 * localDensityConst 0 := by
  obtain ⟨l1, u1⟩ := farSum_mem_Icc_of_mem_datumCone (mem_datumCone_one_zero_of_mem_windowCone h)
    ha hac
  obtain ⟨l2, u2⟩ := farSum_mem_Icc_of_mem_datumCone (mem_datumCone_one_zero_of_mem_windowCone h')
    ha hac
  rw [exp_half_sub_sq] at l1 l2
  rw [exp_half_add_sq] at u1 u2
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Distinct pole weights separate -/

theorem farJ_sq_pos : 0 < farJ ^ 2 := pow_pos farJ_pos 2

/-- **A weight system reads its own pole weight at precision `e^{−c}`.** If `λ` lies in the cones of the
data `(β, s)` and `(β', s')` at a window `c ≥ 1`, then
`|β − β'| J² e^{c−1} ≤ 3(|β| + |β'|) J² + D_s + D_{s'}`. -/
theorem abs_sub_le_of_mem_datumCone_inter {β β' s s' c : ℝ} {lam : ℕ → ℝ}
    (h : lam ∈ datumCone β s c) (h' : lam ∈ datumCone β' s' c) (hc : 1 ≤ c) :
    |β - β'| * farJ ^ 2 * Real.exp (c - 1) ≤
      3 * (|β| + |β'|) * farJ ^ 2 + localDensityConst s + localDensityConst s' := by
  have h1 := abs_farSum_sub_le_of_mem_datumCone h (a := c - 1) (by linarith) (by linarith)
  have h2 := abs_farSum_sub_le_of_mem_datumCone h' (a := c - 1) (by linarith) (by linarith)
  have e : |β - β'| * farJ ^ 2 * Real.exp (c - 1) =
      |(farSum lam (c - 1) - β' * farJ ^ 2 * Real.exp (c - 1)) -
        (farSum lam (c - 1) - β * farJ ^ 2 * Real.exp (c - 1))| := by
    rw [show (farSum lam (c - 1) - β' * farJ ^ 2 * Real.exp (c - 1)) -
        (farSum lam (c - 1) - β * farJ ^ 2 * Real.exp (c - 1)) =
        (β - β') * (farJ ^ 2 * Real.exp (c - 1)) by ring, abs_mul,
      abs_of_pos (mul_pos farJ_sq_pos (Real.exp_pos _))]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-- **Cones of distinct pole weights are disjoint from a finite window on.** -/
theorem datumCone_inter_eq_empty {β β' s s' : ℝ} (hne : β ≠ β') :
    ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → datumCone β s c ∩ datumCone β' s' c = ∅ := by
  set R : ℝ := 3 * (|β| + |β'|) * farJ ^ 2 + localDensityConst s + localDensityConst s' with hR
  have hd : 0 < |β - β'| * farJ ^ 2 := mul_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) farJ_sq_pos
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, R < |β - β'| * farJ ^ 2 * Real.exp (c₁ - 1) := by
    set x : ℝ := R / (|β - β'| * farJ ^ 2) + 1 with hx
    refine ⟨x + 1, ?_⟩
    rw [add_sub_cancel_right]
    have hRx : R / (|β - β'| * farJ ^ 2) < Real.exp x := by
      linarith [Real.add_one_le_exp x]
    rw [div_lt_iff₀ hd] at hRx
    linarith
  refine ⟨max c₁ 1, fun c hc => Set.eq_empty_of_forall_notMem fun lam ⟨h, h'⟩ => ?_⟩
  have hle := abs_sub_le_of_mem_datumCone_inter h h' ((le_max_right _ _).trans hc)
  have hmono : |β - β'| * farJ ^ 2 * Real.exp (c₁ - 1) ≤ |β - β'| * farJ ^ 2 * Real.exp (c - 1) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [le_max_left c₁ 1])) hd.le
  rw [← hR] at hle
  linarith

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
