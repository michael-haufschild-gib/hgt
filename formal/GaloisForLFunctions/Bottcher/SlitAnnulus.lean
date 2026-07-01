/-
# Slit annuli are simply connected

The pinch-crossing pieces of the sub-critical tower live on annuli minus a radial slit: the
`exp`-image of an open coordinate box (log-radii × one angle period), which is convex, hence
contractible; `exp` embeds it (injective on height-`2π` boxes).  Bricks: the definition, openness,
containment in the round annulus, simple connectivity, membership characterization, exclusion of
the slit ray, and connectivity of box sub-pieces.  Pattern: `AnalyticRoot.isSimplyConnected_sector`.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.AnnulusRoot

open Complex Set Filter Metric Topology

namespace Bottcher

/-- The open coordinate box of a slit annulus. -/
def slitBox (r R θ₀ : ℝ) : Set ℂ :=
  {ξ : ℂ | Real.log r < ξ.re ∧ ξ.re < Real.log R ∧ θ₀ < ξ.im ∧ ξ.im < θ₀ + 2 * Real.pi}

/-- The slit annulus: the round annulus minus the radial ray at angle `θ₀`. -/
def slitAnnulus (r R θ₀ : ℝ) : Set ℂ := Complex.exp '' slitBox r R θ₀

theorem isOpen_slitBox (r R θ₀ : ℝ) : IsOpen (slitBox r R θ₀) := by
  have h : slitBox r R θ₀ =
      ({ξ : ℂ | Real.log r < ξ.re} ∩ {ξ : ℂ | ξ.re < Real.log R})
        ∩ ({ξ : ℂ | θ₀ < ξ.im} ∩ {ξ : ℂ | ξ.im < θ₀ + 2 * Real.pi}) := by
    ext ξ
    simp only [slitBox, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact (((isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)).inter
    ((isOpen_lt continuous_const continuous_im).inter
      (isOpen_lt continuous_im continuous_const)))

theorem convex_slitBox (r R θ₀ : ℝ) : Convex ℝ (slitBox r R θ₀) := by
  have h : slitBox r R θ₀ =
      ({ξ : ℂ | Real.log r < ξ.re} ∩ {ξ : ℂ | ξ.re < Real.log R})
        ∩ ({ξ : ℂ | θ₀ < ξ.im} ∩ {ξ : ℂ | ξ.im < θ₀ + 2 * Real.pi}) := by
    ext ξ
    simp only [slitBox, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [h]
  exact (((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
    ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)))

/-- `exp` is injective on the box (height `< 2π`). -/
theorem exp_injOn_slitBox (r R θ₀ : ℝ) : Set.InjOn Complex.exp (slitBox r R θ₀) := by
  rintro a ⟨_, _, ha3, ha4⟩ b ⟨_, _, hb3, hb4⟩ hab
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have him : a.im = b.im + (n : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn
    simpa [Complex.add_im, Complex.mul_im, Complex.mul_re] using h
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have h2 : |a.im - b.im| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos]
    rw [him] at h2
    have h3 : |(n:ℝ) * (2 * Real.pi)| = |(n:ℝ)| * (2 * Real.pi) := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    have h4 : |b.im + (n:ℝ) * (2 * Real.pi) - b.im| = |(n:ℝ) * (2 * Real.pi)| := by
      congr 1
      ring
    rw [h4, h3] at h2
    nlinarith [Real.pi_pos]
  rw [hn0] at hn
  simpa using hn

theorem isOpen_slitAnnulus (r R θ₀ : ℝ) : IsOpen (slitAnnulus r R θ₀) :=
  Complex.isOpenMap_exp _ (isOpen_slitBox r R θ₀)

theorem slitAnnulus_subset {r R θ₀ : ℝ} (hr : 0 < r) (hrR : r < R) :
    slitAnnulus r R θ₀ ⊆ annulusSet r R := by
  rintro z ⟨ξ, ⟨h1, h2, _, _⟩, rfl⟩
  have hR : 0 < R := lt_trans hr hrR
  constructor
  · rw [Complex.norm_exp]
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ < Real.exp ξ.re := Real.exp_lt_exp.mpr h1
  · rw [Complex.norm_exp]
    calc Real.exp ξ.re < Real.exp (Real.log R) := Real.exp_lt_exp.mpr h2
      _ = R := Real.exp_log hR

theorem isSimplyConnected_slitAnnulus {r R : ℝ} (θ₀ : ℝ) (hr : 0 < r) (hrR : r < R) :
    IsSimplyConnected (slitAnnulus r R θ₀) := by
  have hlog := Real.log_lt_log hr hrR
  have hne : (slitBox r R θ₀).Nonempty := by
    refine ⟨(((Real.log r + Real.log R) / 2 : ℝ) : ℂ)
      + ((θ₀ + Real.pi : ℝ) : ℂ) * Complex.I, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have hemb : IsEmbedding fun ξ : slitBox r R θ₀ => Complex.exp (ξ : ℂ) := by
    have hcont : Continuous fun ξ : slitBox r R θ₀ => Complex.exp (ξ : ℂ) :=
      Complex.continuous_exp.comp continuous_subtype_val
    have hinj : Function.Injective fun ξ : slitBox r R θ₀ => Complex.exp (ξ : ℂ) := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      exact Subtype.ext (exp_injOn_slitBox r R θ₀ ha hb h)
    have hopen : IsOpenMap fun ξ : slitBox r R θ₀ => Complex.exp (ξ : ℂ) :=
      Complex.isOpenMap_exp.comp ((isOpen_slitBox r R θ₀).isOpenMap_subtype_val)
    exact (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj hopen).isEmbedding
  have himg : (fun ξ : slitBox r R θ₀ => Complex.exp (ξ : ℂ)) '' univ
      = slitAnnulus r R θ₀ := by
    ext z
    constructor
    · rintro ⟨⟨ξ, hξ⟩, -, rfl⟩
      exact ⟨ξ, hξ, rfl⟩
    · rintro ⟨ξ, hξ, rfl⟩
      exact ⟨⟨ξ, hξ⟩, mem_univ _, rfl⟩
  show IsSimplyConnected (slitAnnulus r R θ₀)
  rw [← himg, hemb.isSimplyConnected_image]
  haveI : ContractibleSpace (slitBox r R θ₀) :=
    (convex_slitBox r R θ₀).contractibleSpace hne
  haveI : SimplyConnectedSpace (slitBox r R θ₀) :=
    SimplyConnectedSpace.ofContractible _
  exact ((Homeomorph.Set.univ (slitBox r R θ₀)).toHomotopyEquiv).simplyConnectedSpace_iff.mpr
    ‹_›

/-- Every annulus point off the ray at angle `θ₀` lies in the slit annulus. -/
theorem mem_slitAnnulus_of_arg_ne {r R θ₀ : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ annulusSet r R)
    (harg : ∃ θ : ℝ, θ₀ < θ ∧ θ < θ₀ + 2 * Real.pi ∧ z = ‖z‖ * Complex.exp (θ * Complex.I)) :
    z ∈ slitAnnulus r R θ₀ := by
  obtain ⟨θ, h1, h2, h3⟩ := harg
  have hzpos : (0:ℝ) < ‖z‖ := lt_trans hr hz.1
  refine ⟨((Real.log ‖z‖ : ℝ) : ℂ) + (θ : ℂ) * Complex.I, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · show Real.log r < (((Real.log ‖z‖ : ℝ) : ℂ) + (θ : ℂ) * Complex.I).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    have : Real.log r < Real.log ‖z‖ := Real.log_lt_log hr hz.1
    linarith
  · show (((Real.log ‖z‖ : ℝ) : ℂ) + (θ : ℂ) * Complex.I).re < Real.log R
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    have : Real.log ‖z‖ < Real.log R := Real.log_lt_log hzpos hz.2
    linarith
  · show θ₀ < (((Real.log ‖z‖ : ℝ) : ℂ) + (θ : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    linarith
  · show (((Real.log ‖z‖ : ℝ) : ℂ) + (θ : ℂ) * Complex.I).im < θ₀ + 2 * Real.pi
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    linarith
  · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hzpos]
    exact h3.symm

end Bottcher
