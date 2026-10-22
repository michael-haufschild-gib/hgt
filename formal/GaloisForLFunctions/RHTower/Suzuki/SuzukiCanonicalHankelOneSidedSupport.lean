import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma41
import GaloisForLFunctions.RHTower.Suzuki.SuzukiOneSidedFourierLaplace

/-!
# One-sided support transport for Suzuki's canonical Hankel unitary

Suzuki (2012), Lemma 4.3 starts from the exact support implication

`supp q ⊆ (-∞, A]  ⟹  supp (H_ω q) ⊆ [-A, ∞)`

in logarithmic half-density coordinates.  This module proves that implication for the actual
canonical shifted-Xi Hankel unitary, not for a proxy operator.  On `C_c∞`, the proof uses the
literal arithmetic kernel from Lemma 4.1 and its sharp threshold `h_ω(x)=0` for `x≤1`.  The
support-preserving density theorem then extends the result to arbitrary `L²` sources.

No transform identity or support law is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section


namespace RHTower

/-- Suzuki's canonical Hankel unitary written on the exact logarithmic half-density carrier. -/
def suzukiCanonicalLogHankelUnitary
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega) :
    SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  logEvenUnitary.symm.trans
    ((suzukiCanonicalHankelUnitary omega hinner).trans logEvenUnitary)

/-- The generic compact-smooth `L²` packaging used by one-sided density agrees exactly with the
strong-log packaging used by Suzuki's literal-kernel theorem. -/
theorem suzukiOneSidedCompactSmoothL2_eq_suzukiCompactSmoothLogL2
    (g : ℝ → ℂ) (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g) :
    suzukiOneSidedCompactSmoothL2 g hcompact hsmooth =
      suzukiCompactSmoothLogL2 g hsmooth hcompact := by
  apply Lp.ext
  filter_upwards [suzukiOneSidedCompactSmoothL2_ae g hcompact hsmooth,
    suzukiStrongLogL2_ae
      (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) hcompact] with t hleft hright
  have hright' : (suzukiCompactSmoothLogL2 g hsmooth hcompact : ℝ → ℂ) t = g t := by
    simpa [suzukiCompactSmoothLogL2, suzukiCompactSmoothStrongLogTarget] using hright
  rw [hleft, hright']

/-- Literal logarithmic Hankel output vanishes strictly below the reflected source edge. -/
theorem suzukiLiteralLogHankel_eq_zero_of_lt_neg_support
    {omega A r : ℝ} (g : DeningerMeyerStrongLogTarget)
    (hg : ∀ t, A ≤ t → (g : ℝ → ℂ) t = 0) (hr : r < -A) :
    suzukiLiteralLogHankel omega g r = 0 := by
  rw [suzukiLiteralLogHankel]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : A ≤ t
  · change _ * _ * (g : ℝ → ℂ) t = 0
    rw [hg t ht]
    ring
  · have hsum : r + t < 0 := by linarith
    have hexp : Real.exp (r + t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hsum.le
    change _ * suzukiSourceHFinite omega (Real.exp (r + t)) * (g : ℝ → ℂ) t = 0
    rw [suzukiSourceHFinite, if_neg (not_lt_of_ge hexp)]
    ring

/-- A compact-smooth source with sharp upper support is fixed by the sharp upper cutoff. -/
theorem logHalflineCutoff_suzukiCompactSmoothLogL2
    {A : ℝ} (g : ℝ → ℂ) (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg : ∀ t, A ≤ t → g t = 0) :
    logHalflineCutoff A (suzukiCompactSmoothLogL2 g hsmooth hcompact) =
      suzukiCompactSmoothLogL2 g hsmooth hcompact := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Iic A) measurableSet_Iic
      (suzukiCompactSmoothLogL2 g hsmooth hcompact),
    suzukiStrongLogL2_ae
      (suzukiCompactSmoothStrongLogTarget g hsmooth hcompact) hcompact] with t hcut hsource
  rw [show logHalflineCutoff A (suzukiCompactSmoothLogL2 g hsmooth hcompact) t =
      (Iic A).indicator
        (fun s => suzukiCompactSmoothLogL2 g hsmooth hcompact s) t by
    simpa [logHalflineCutoff] using hcut]
  by_cases ht : t ≤ A
  · rw [indicator_of_mem (show t ∈ Iic A from ht)]
  · have hsource' :
        (suzukiCompactSmoothLogL2 g hsmooth hcompact : ℝ → ℂ) t = g t := by
      simpa [suzukiCompactSmoothLogL2, suzukiCompactSmoothStrongLogTarget] using hsource
    rw [indicator_of_notMem (show t ∉ Iic A from ht), hsource',
      hg t (le_of_lt (lt_of_not_ge ht))]

/-- On a compact-smooth logarithmic source, the conjugated canonical unitary is exactly the
literal arithmetic Hankel output. -/
theorem suzukiCanonicalLogHankelUnitary_eq_literal_on_compact_smooth
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    suzukiCanonicalLogHankelUnitary omega hinner
        (suzukiCompactSmoothLogL2 g hsmooth hcompact) =
      suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
        g hsmooth hcompact := by
  change logEvenUnitary
      (suzukiCanonicalHankelUnitary omega hinner
        (logEvenUnitary.symm (suzukiCompactSmoothLogL2 g hsmooth hcompact))) = _
  rw [suzuki2012_lemma_four_one_literal_kernel_on_compact_smooth_log_core
    homega hc hinner g hsmooth hcompact]
  exact logEvenUnitary.apply_symm_apply _

/-- Literal output of a compact-smooth upper-supported source is fixed by the reflected lower
half-line cutoff. -/
theorem logLowerHalflineCutoff_suzukiCompactSmoothLiteralLogHankelL2
    {omega c A : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) (hg : ∀ t, A ≤ t → g t = 0) :
    logLowerHalflineCutoff (-A)
        (suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
          g hsmooth hcompact) =
      suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
        g hsmooth hcompact := by
  let G := suzukiCompactSmoothStrongLogTarget g hsmooth hcompact
  let out := suzukiCompactSmoothLiteralLogHankelL2 omega c homega hc hinner
    g hsmooth hcompact
  have hout : (out : ℝ → ℂ) =ᵐ[volume] suzukiLiteralLogHankel omega G :=
    (memLp_two_suzukiLiteralLogHankel homega hc hinner G hcompact).coeFn_toLp
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Ici (-A)) measurableSet_Ici out, hout] with r hcut hrout
  change logLowerHalflineCutoff (-A) out r = out r
  rw [show logLowerHalflineCutoff (-A) out r =
      (Ici (-A)).indicator (fun s => out s) r by
    simpa [logLowerHalflineCutoff] using hcut]
  by_cases hr : -A ≤ r
  · rw [indicator_of_mem (show r ∈ Ici (-A) from hr)]
  · rw [indicator_of_notMem (show r ∉ Ici (-A) from hr), hrout]
    exact (suzukiLiteralLogHankel_eq_zero_of_lt_neg_support G
      (fun t ht => hg t ht) (lt_of_not_ge hr)).symm

theorem norm_logLowerHalflineCutoff_le_one (B : ℝ) :
    ‖logLowerHalflineCutoff B‖ ≤ 1 := by
  apply norm_le_of_ae_mul (p := 2) (μ := (volume : Measure ℝ))
    (ψ := fun t => (Ici B).indicator (fun _ => (1 : ℂ)) t) (K := 1)
    (by norm_num) (fun t => by by_cases ht : t ∈ Ici B <;> simp [ht])
  intro q
  filter_upwards [indicatorCutoff_ae (Ici B) measurableSet_Ici q] with t ht
  rw [show logLowerHalflineCutoff B q t = (Ici B).indicator (fun s => q s) t by
    simpa [logLowerHalflineCutoff] using ht]
  by_cases hmem : t ∈ Ici B <;> simp [hmem]

/-- **Sharp one-sided support transport for arbitrary `L²` data.**  The actual canonical Suzuki
Hankel unitary maps the fixed space of `1_{(-∞,A]}` into the fixed space of `1_{[-A,∞)}`. -/
theorem suzukiCanonicalLogHankelUnitary_maps_upper_to_reflected_lower
    {omega A : ℝ} (homega : 1 / 2 < omega)
    (q : SoninL2) (hq : logHalflineCutoff A q = q) :
    logLowerHalflineCutoff (-A)
        (suzukiCanonicalLogHankelUnitary omega
          (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q) =
      suzukiCanonicalLogHankelUnitary omega
        (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega) q := by
  let hinner := suzukiCanonicalTheta_meromorphicInner_of_half_lt homega
  let H := suzukiCanonicalLogHankelUnitary omega hinner
  let P := logLowerHalflineCutoff (-A)
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨g, hcompact, hsmooth, hg, hqg⟩ :=
    exists_suzukiOneSidedCompactSmoothL2_dist_lt hq (show 0 < ε / 3 by linarith)
  let v := suzukiOneSidedCompactSmoothL2 g hcompact hsmooth
  have hvEq : v = suzukiCompactSmoothLogL2 g hsmooth hcompact :=
    suzukiOneSidedCompactSmoothL2_eq_suzukiCompactSmoothLogL2 g hcompact hsmooth
  have hPv : P (H v) = H v := by
    rw [hvEq]
    rw [suzukiCanonicalLogHankelUnitary_eq_literal_on_compact_smooth
      (omega := omega) (c := 2 + omega) (by linarith) (by linarith) hinner]
    exact logLowerHalflineCutoff_suzukiCompactSmoothLiteralLogHankelL2
      (omega := omega) (c := 2 + omega) (A := A)
        (by linarith) (by linarith) hinner g hsmooth hcompact hg
  have hPdist : dist (P (H q)) (P (H v)) ≤ dist q v := by
    calc
      dist (P (H q)) (P (H v)) ≤ ‖P‖ * dist (H q) (H v) := P.dist_le_opNorm _ _
      _ ≤ 1 * dist (H q) (H v) :=
        mul_le_mul_of_nonneg_right (norm_logLowerHalflineCutoff_le_one (-A)) dist_nonneg
      _ = dist q v := by rw [one_mul, H.dist_map]
  apply le_of_lt
  calc
    dist (P (H q)) (H q) ≤
        dist (P (H q)) (P (H v)) + dist (P (H v)) (H v) + dist (H v) (H q) := by
          have h₁ := dist_triangle (P (H q)) (P (H v)) (H q)
          have h₂ := dist_triangle (P (H v)) (H v) (H q)
          linarith
    _ = dist (P (H q)) (P (H v)) + dist (H v) (H q) := by rw [hPv, dist_self, add_zero]
    _ ≤ dist q v + dist (H v) (H q) := add_le_add hPdist le_rfl
    _ = dist q v + dist v q := by rw [H.dist_map]
    _ < ε / 3 + ε / 3 := add_lt_add hqg (by simpa [dist_comm] using hqg)
    _ < ε := by linarith

end RHTower
