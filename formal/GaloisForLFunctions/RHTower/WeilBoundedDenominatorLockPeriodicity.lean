import GaloisForLFunctions.RHTower.WeilBoundedDenominatorLockConvolution
import GaloisForLFunctions.Bottcher.SchwarzReflection
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient

/-!
# Bounded-denominator locks force periodic Dirichlet coefficients

**Theorem** (`bounded_denominator_lock_periodic`).  Let `G` be a Herglotz producer for the weights
`lam`, with Dirichlet coefficients `a = exp⋆(lam/log)`.  Suppose that on the lower critical line

`G(1 − s) = N^{s−½} D(s) G(s)`,   `D(s) = Σ_k P(k) k^{−(s−½)}`,   `Σ |P(k)| < ∞`.

This is an almost-periodic lock whose rational frequencies `k/N` have denominators dividing `N` and
lie on both sides of `1`.  Then `a` is `N`-periodic: `a(n) = Ψ(n mod N)` for some `Ψ : ℤ/N → ℂ`.
So `F(s) = Σ a(n) n^{−s}` is the L-function of a periodic function.

**Proof.**
1. The period law makes `h(j) = √j Σ_{nm=j} a(n) n^{−1/2} P(m)` `N`-periodic, and
   `L(s, h) = F(s) D(s)` (`sqrtConv_periodic`, `LSeries_sqrtConv`).
2. By the identity theorem on the lower half of the strip `½ < Re s < 3/2`, and by continuity up to
   the line, `G(s) N^{s−½} D(s) = s(s − 1) Γ_ℝ(s) N^{s−½} L(s, h)` on the lower line.
3. The lock and the functional equation of `L(s, h)` (`ZMod.LFunction_one_sub`) give, at the points
   `w = 1 − s` of the upper line,
   `G(w) = w(w − 1) Γ_ℝ(1 − w) (2π)^{−w} Γ(w) N^{−1/2} (e^{πiw/2} L(w, ĥ) + e^{−πiw/2} L(w, ĥ⁻))`,
   where `ĥ` is the discrete Fourier transform and `h⁻(x) = h(−x)`.
4. Both sides are holomorphic on the quadrant `Re w > ½, Im w > 0` and agree on its boundary
   half-line, so they agree on the quadrant (`eq_zero_of_vertical_halfLine`, Painlevé reflection).
5. On `Re w > 1`, `Γ_ℝ(1 − w) (2π)^{−w} Γ(w) = Γ_ℝ(w)/(2 cos(πw/2))`, so
   `(F(w) − N^{−1/2} L(w, ĥ⁻)) (1 + e^{−πiw}) = N^{−1/2} (L(w, ĥ) − L(w, ĥ⁻))`.  Hence
   `F(w) − N^{−1/2} L(w, ĥ⁻) → 0` as `Im w → +∞`.  The left side is almost periodic in `Im w`, so
   it vanishes, and `a(n) = N^{−1/2} ĥ⁻(n)` by uniqueness of Dirichlet coefficients.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral

noncomputable section

/-! ### Uniqueness from a boundary half-line -/

/-- **Uniqueness from a vertical boundary half-line.**  A function holomorphic on the quadrant
`{Re w > a, Im w > 0}`, continuous at every point of the half-line `{Re w = a, Im w > 0}` and
vanishing there, vanishes on the quadrant.  Extended by `0` to `Re w < a` it is continuous on the
upper half-plane and holomorphic off the line `Re w = a`, hence holomorphic (Painlevé), and it
vanishes on an open set. -/
theorem eq_zero_of_vertical_halfLine {E : ℂ → ℂ} {a : ℝ}
    (hd : ∀ w : ℂ, a < w.re → 0 < w.im → DifferentiableAt ℂ E w)
    (hc : ∀ w : ℂ, w.re = a → 0 < w.im → ContinuousAt E w)
    (h0 : ∀ w : ℂ, w.re = a → 0 < w.im → E w = 0)
    {w : ℂ} (hw : a < w.re) (hwi : 0 < w.im) : E w = 0 := by
  classical
  set U : Set ℂ := {z | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  set F : ℂ → ℂ := fun z => if a ≤ z.re then E z else 0 with hF
  have hright : ∀ z : ℂ, a < z.re → F =ᶠ[𝓝 z] E := by
    intro z hz
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with ζ hζ
    simp only [hF, if_pos (le_of_lt (show a < ζ.re from hζ))]
  have hleft : ∀ z : ℂ, z.re < a → F =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz] with ζ hζ
    simp only [hF, if_neg (not_le.mpr (show ζ.re < a from hζ))]
  have hcont : ContinuousOn F U := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy z.re a with hlt | heq | hgt
    · exact continuousAt_const.congr (hleft z hlt).symm
    · have hEz : E z = 0 := h0 z heq hz
      have hFz : F z = 0 := by simp only [hF, if_pos heq.ge, hEz]
      have hE : Tendsto (fun ζ => ‖E ζ‖) (𝓝 z) (𝓝 0) := by
        have h' : Tendsto (fun ζ => ‖E ζ‖) (𝓝 z) (𝓝 ‖E z‖) := (hc z heq hz).norm
        rwa [hEz, norm_zero] at h'
      rw [ContinuousAt, hFz]
      refine squeeze_zero_norm (fun ζ => ?_) hE
      simp only [hF]
      split_ifs <;> simp
    · exact (hd z hgt hz).continuousAt.congr (hright z hgt).symm
  have hdiff : DifferentiableOn ℂ F (U ∩ {z : ℂ | (I * z + 0).im ≠ a}) := by
    intro z hz
    have hre : z.re ≠ a := by simpa using hz.2
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · exact ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
        (hleft z hlt)).differentiableWithinAt
    · exact ((hd z hgt hz.1).congr_of_eventuallyEq (hright z hgt)).differentiableWithinAt
  have hFd : DifferentiableOn ℂ F U :=
    Bottcher.differentiableOn_of_off_line (c := I) (d := 0) (a := a) I_ne_zero hUo hcont hdiff
  have hz₀ : ((a - 1 : ℝ) : ℂ) + I ∈ U := by simp [hU]
  have hzero : Set.EqOn F 0 U :=
    (hFd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected hz₀ (hleft _ (by simp))
  have := hzero (show w ∈ U from hwi)
  simpa [hF, if_pos hw.le] using this

/-! ### Gamma factors -/

theorem differentiableAt_Gammaℝ_of_im_ne {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ Gammaℝ z := by
  have hG : DifferentiableAt ℂ Gamma (z / 2) := differentiableAt_Gamma _ fun m h => hz (by
    have := congrArg Complex.im h
    simp at this
    linarith)
  have he : Gammaℝ = fun z => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) := funext Gammaℝ_def
  rw [he]
  exact ((differentiableAt_id.neg.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))).mul (hG.comp z (differentiableAt_id.div_const 2))

/-- `Γ_ℝ(1 − w) (2π)^{−w} Γ(w) = Γ_ℝ(w) / (2 cos(πw/2))`. -/
theorem gammaR_one_sub_mul_Gamma {w : ℂ} (hw : cos ((Real.pi : ℂ) * w / 2) ≠ 0) :
    Gammaℝ (1 - w) * ((2 * (Real.pi : ℂ)) ^ (-w) * Gamma w) =
      Gammaℝ w / (2 * cos ((Real.pi : ℂ) * w / 2)) := by
  have h1 : (2 * (Real.pi : ℂ)) ^ (-w) * Gamma w = Gammaℝ w * Gammaℝ (1 + w) / 2 := by
    rw [add_comm, Gammaℝ_mul_Gammaℝ_add_one, Gammaℂ_def]; ring
  rw [h1, show Gammaℝ (1 - w) * (Gammaℝ w * Gammaℝ (1 + w) / 2) =
    Gammaℝ w * (Gammaℝ (1 - w) * Gammaℝ (1 + w)) / 2 by ring, Gammaℝ_one_sub_mul_Gammaℝ_one_add]
  field_simp

theorem cos_pi_mul_div_two_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    cos ((Real.pi : ℂ) * w / 2) ≠ 0 := by
  rw [Ne, Complex.cos_eq_zero_iff]
  rintro ⟨k, hk⟩
  have h1 : ((Real.pi : ℂ) * w / 2).im = 0 := by rw [hk]; simp
  have h2 : ((Real.pi : ℂ) * w / 2).im = Real.pi * w.im / 2 := by simp
  rw [h2] at h1
  exact hw ((mul_eq_zero.mp (by linarith : Real.pi * w.im = 0)).resolve_left Real.pi_ne_zero)

/-! ### The dual side of the lock -/

/-- The functional equation of `L(s, Ψ)` read at `w = 1 − s`, multiplied by the archimedean factor
of the producer. -/
def lockDual (N : ℕ) [NeZero N] (Ψ : ZMod N → ℂ) (w : ℂ) : ℂ :=
  w * (w - 1) * Gammaℝ (1 - w) * ((2 * (Real.pi : ℂ)) ^ (-w) * Gamma w) *
    (N : ℂ) ^ (-(1 / 2 : ℂ)) *
    (cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (ZMod.dft Ψ) w +
      cexp (-(Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) w)

theorem differentiableAt_lockDual (N : ℕ) [NeZero N] (Ψ : ZMod N → ℂ) {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ (lockDual N Ψ) w := by
  have hw1 : w ≠ 1 := fun h => hw (by rw [h]; simp)
  have hΓ : DifferentiableAt ℂ Gamma w := differentiableAt_Gamma w fun m h => hw (by rw [h]; simp)
  have hΓR : DifferentiableAt ℂ (fun z => Gammaℝ (1 - z)) w :=
    (differentiableAt_Gammaℝ_of_im_ne (by simpa using hw)).comp w
      ((differentiableAt_const _).sub differentiableAt_id)
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl hpi)
  have hL1 := ZMod.differentiableAt_LFunction (ZMod.dft Ψ) w (Or.inl hw1)
  have hL2 := ZMod.differentiableAt_LFunction (ZMod.dft fun x => Ψ (-x)) w (Or.inl hw1)
  have he1 : DifferentiableAt ℂ (fun z : ℂ => cexp ((Real.pi : ℂ) * I * z / 2)) w := by fun_prop
  have he2 : DifferentiableAt ℂ (fun z : ℂ => cexp (-(Real.pi : ℂ) * I * z / 2)) w := by fun_prop
  unfold lockDual
  exact (((((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hΓR).mul
    (hpow.mul hΓ)).mul (differentiableAt_const _)).mul ((he1.mul hL1).add (he2.mul hL2)))

/-! ### Almost periodicity on vertical lines -/

theorem term_vertical_eq (f : ℕ → ℂ) (n : ℕ) (σ y : ℝ) :
    LSeries.term f ((σ : ℂ) + (y : ℂ) * I) n =
      LSeries.term f (σ : ℂ) n * GaloisForLFunctions.expChar (-Real.log n) y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log n = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
    GaloisForLFunctions.expChar, Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hn0, hlog]
  have e : Complex.exp ((Real.log n : ℂ) * ((σ : ℂ) + (y : ℂ) * I)) =
      Complex.exp ((Real.log n : ℂ) * σ) *
        (Complex.exp (((-Real.log n * y : ℝ) : ℂ) * I))⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  field_simp

theorem isBohrAlmostPeriodic_LSeries_vertical {f : ℕ → ℂ} {σ : ℝ}
    (hf : LSeriesSummable f (σ : ℂ)) :
    HTGeometry.IsBohrAlmostPeriodic fun y : ℝ => LSeries f ((σ : ℂ) + (y : ℂ) * I) := by
  have h : (fun y : ℝ => LSeries f ((σ : ℂ) + (y : ℂ) * I)) = GaloisForLFunctions.expSeriesCarrier
      (fun n => LSeries.term f (σ : ℂ) n) (fun n => -Real.log n) := by
    funext y
    simp only [LSeries, GaloisForLFunctions.expSeriesCarrier]
    exact tsum_congr fun n => term_vertical_eq f n σ y
  rw [h]
  exact GaloisForLFunctions.isBohrAlmostPeriodic_expSeriesCarrier (summable_norm_iff.mpr hf) _

theorem norm_LSeries_vertical_le {f : ℕ → ℂ} {σ : ℝ} (hf : LSeriesSummable f (σ : ℂ)) (y : ℝ) :
    ‖LSeries f ((σ : ℂ) + (y : ℂ) * I)‖ ≤ ∑' n, ‖LSeries.term f (σ : ℂ) n‖ := by
  have heq : ∀ n, ‖LSeries.term f ((σ : ℂ) + (y : ℂ) * I) n‖ = ‖LSeries.term f (σ : ℂ) n‖ := by
    intro n
    rw [term_vertical_eq, norm_mul, GaloisForLFunctions.expChar, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hs : Summable fun n => ‖LSeries.term f ((σ : ℂ) + (y : ℂ) * I) n‖ := by
    simp_rw [heq]; exact summable_norm_iff.mpr hf
  calc ‖LSeries f ((σ : ℂ) + (y : ℂ) * I)‖ ≤ ∑' n, ‖LSeries.term f ((σ : ℂ) + (y : ℂ) * I) n‖ :=
        norm_tsum_le_tsum_norm hs
    _ = ∑' n, ‖LSeries.term f (σ : ℂ) n‖ := tsum_congr heq

/-! ### The theorem -/

/-- **Bounded-denominator locks force periodic coefficients.**  If a Herglotz producer satisfies
`G(1 − s) = N^{s−½} (Σ_k P(k) k^{−(s−½)}) G(s)` on the lower critical line, with
`Σ |P(k)| < ∞`, then its Dirichlet coefficients are `N`-periodic. -/
theorem bounded_denominator_lock_periodic {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {N : ℕ} [NeZero N] {P : ℕ → ℂ} (hP : Summable fun k => ‖P k‖)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (N : ℂ) ^ (lineS τ - 1 / 2) * LSeries P (lineS τ - 1 / 2) * G (lineS τ)) :
    ∃ Ψ : ZMod N → ℂ, ∀ n : ℕ, n ≠ 0 → dirichletExp (lamLog lam) n = Ψ n := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  set a := dirichletExp (lamLog lam) with ha
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  /- Step 1: the periodic convolution and its L-function. -/
  set h := sqrtConv a P with hh
  have hper : ∀ j, 0 < j → h (j + N) = h j := fun j hj =>
    sqrtConv_periodic hsl hΦre hid hGc hGd hG2 hN hP hlock hj
  set Ψ' : ZMod N → ℂ := fun r => h (if r.val = 0 then N else r.val) with hΨ'
  have hΨ'eq : ∀ j : ℕ, 0 < j → h j = Ψ' (j : ZMod N) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjN : N < j
      · have e : j = (j - N) + N := by omega
        rw [e, hper (j - N) (by omega), ih (j - N) (by omega) (by omega)]
        congr 1
        push_cast
        simp
      · rcases eq_or_lt_of_le (not_lt.mp hjN) with hjeq | hlt
        · rw [hjeq]; simp [hΨ']
        · simp only [hΨ', ZMod.val_natCast, Nat.mod_eq_of_lt hlt, if_neg hj.ne']
  have hLF : ∀ s : ℂ, 1 < s.re → ZMod.LFunction Ψ' s = LSeries a s * LSeries P (s - 1 / 2) := by
    intro s hs
    have hPs : LSeriesSummable P (s - 1 / 2) :=
      lseriesSummable_of_nonneg hP (by rw [Complex.sub_re]; norm_num; linarith)
    rw [ZMod.LFunction_eq_LSeries Ψ' hs, ← (LSeries_sqrtConv (hLa s hs).1 hPs).2]
    exact LSeries_congr (fun {n} hn => (hΨ'eq n (Nat.pos_of_ne_zero hn)).symm) s
  /- Step 2: the identity on the lower half-strip, and on the lower line. -/
  have hu := denFreq_pos hN
  have hcw := summable_denFreq_weight hN hP
  set R : ℂ → ℂ := fun z =>
    z * (z - 1) * Gammaℝ z * ((N : ℂ) ^ (z - 1 / 2) * ZMod.LFunction Ψ' z) with hR
  set L : ℂ → ℂ := fun z => G z * apLock (fun k => P (k + 1)) (denFreq N) z with hL
  set Ω : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 3 / 2 ∧ z.im < 0} with hΩ
  have hΩo : IsOpen Ω :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hΩc : Convex ℝ Ω :=
    (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_lt _))
  have hRat : ∀ z : ℂ, 0 < z.re → z ≠ 1 → DifferentiableAt ℂ R z := fun z hre hz1 =>
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (RHTower.TruncatedRadial.differentiableAt_Gammaℝ_of_re_pos hre)).mul
      (((differentiableAt_id.sub_const _).const_cpow (Or.inl hN0)).mul
        (ZMod.differentiableAt_LFunction Ψ' z (Or.inl hz1)))
  have hLd : DifferentiableOn ℂ L Ω := fun z hz =>
    ((hGd z hz.1).differentiableAt.mul
      (differentiableAt_apLock hu hcw hz.1 hz.2.1)).differentiableWithinAt
  have hRd : DifferentiableOn ℂ R Ω := fun z hz =>
    (hRat z (by linarith [hz.1]) (fun h1 => by
      have h3 := hz.2.2
      rw [h1] at h3
      simp at h3)).differentiableWithinAt
  have hbase : ∀ z : ℂ, 1 < z.re → z.re < 3 / 2 → L z = R z := by
    intro z h1 h2
    simp only [hL, hR]
    rw [G_eq_bigG hsl hid hGd hG2 h1, bigG, apLock_denFreq hN hP (by linarith) h2.le,
      hLF z h1, ← (hLa z h1).2]
    ring
  set z₀ : ℂ := ((5 / 4 : ℝ) : ℂ) - I with hz₀
  have hz₀Ω : z₀ ∈ Ω := by simp only [hΩ, hz₀, mem_setOf_eq]; norm_num
  have hEq : Set.EqOn L R Ω := by
    refine (hLd.analyticOnNhd hΩo).eqOn_of_preconnected_of_eventuallyEq (hRd.analyticOnNhd hΩo)
      hΩc.isPreconnected hz₀Ω ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.re < 3 / 2} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show z₀ ∈ {z : ℂ | 1 < z.re ∧ z.re < 3 / 2} by
      simp only [hz₀, mem_setOf_eq]; norm_num)] with z hz
    exact hbase z hz.1 hz.2
  have hline : ∀ τ : ℝ, τ < 0 → L (lineS τ) = R (lineS τ) := by
    intro τ hτ
    set s₀ := lineS τ with hs₀
    have hs₀re : s₀.re = 1 / 2 := lineS_re τ
    have hs₀im : s₀.im = 2 * τ := by rw [hs₀, lineS_eq]; simp
    have hs₀1 : s₀ ≠ 1 := fun h1 => by
      have := congrArg Complex.im h1
      rw [hs₀im] at this
      simp at this
      linarith
    have hcL : ContinuousAt L s₀ :=
      (hGc s₀ hs₀re.symm.le).mul (continuous_apLock hu hcw).continuousAt
    have hcR : ContinuousAt R s₀ := (hRat s₀ (by rw [hs₀re]; norm_num) hs₀1).continuousAt
    have hpath : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
      have hc : Continuous (fun ε : ℝ => s₀ + (ε : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, s₀ + (ε : ℂ) ∈ Ω := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      simp only [hΩ, mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.add_im,
        Complex.ofReal_im, add_zero, hs₀re, hs₀im]
      refine ⟨by linarith [hε.1], by linarith [hε.2], by linarith⟩
    have h1 : Tendsto (fun ε : ℝ => L (s₀ + (ε : ℂ)) - R (s₀ + (ε : ℂ))) (𝓝[>] 0)
        (𝓝 (L s₀ - R s₀)) :=
      (hcL.sub hcR).tendsto.comp hpath
    have h2 : Tendsto (fun ε : ℝ => L (s₀ + (ε : ℂ)) - R (s₀ + (ε : ℂ))) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [hev] with ε hε
        rw [hEq hε, sub_self])
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  /- Step 3: the dual identity on the upper line. -/
  have hupper : ∀ w : ℂ, w.re = 1 / 2 → 0 < w.im → G w = lockDual N Ψ' w := by
    intro w hwre hwim
    set τ : ℝ := -(w.im / 2) with hτdef
    have hτ : τ < 0 := by rw [hτdef]; linarith
    have hw : w = 1 - lineS τ := by
      rw [one_sub_lineS, lineS_eq]
      apply Complex.ext
      · simp [hwre]
      · simp [hτdef]; ring
    set s := lineS τ with hs
    have hsre : s.re = 1 / 2 := lineS_re τ
    have hlk := hlock τ hτ
    rw [← apLock_denFreq hN hP hsre.symm.le (by rw [hsre]; norm_num)] at hlk
    have hLR := hline τ hτ
    simp only [hL] at hLR
    have hws : (1 - s).re = 1 / 2 := by rw [Complex.sub_re, hsre]; norm_num
    have hwim' : (1 - s).im ≠ 0 := by rw [← hw]; exact hwim.ne'
    have hFE := ZMod.LFunction_one_sub Ψ' (s := 1 - s)
      (fun n hn => by
        have := congrArg Complex.re hn
        rw [hws] at this
        simp at this
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (Or.inr fun h1 => hwim' (by rw [h1]; simp))
    rw [sub_sub_cancel] at hFE
    have hpow : (N : ℂ) ^ (s - 1 / 2) * (N : ℂ) ^ (1 - s - 1) = (N : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [← cpow_add _ _ hN0]; ring_nf
    rw [hw, hlk, mul_comm, hLR]
    simp only [hR, lockDual, sub_sub_cancel]
    rw [hFE, ← hpow]
    ring
  /- Step 4: the dual identity on the quadrant. -/
  have hquad : ∀ w : ℂ, 1 / 2 < w.re → 0 < w.im → G w = lockDual N Ψ' w := by
    intro w hw hwi
    have := eq_zero_of_vertical_halfLine (E := fun z => G z - lockDual N Ψ' z) (a := 1 / 2)
      (fun z hz hzi => (hGd z hz).differentiableAt.sub (differentiableAt_lockDual N Ψ' hzi.ne'))
      (fun z hz hzi => (hGc z hz.symm.le).sub (differentiableAt_lockDual N Ψ' hzi.ne').continuousAt)
      (fun z hz hzi => sub_eq_zero.mpr (hupper z hz hzi)) hw hwi
    exact sub_eq_zero.mp this
  /- Step 5: decay in the vertical direction. -/
  set κ : ℂ := (N : ℂ) ^ (-(1 / 2 : ℂ)) with hκ
  set bA : ℕ → ℂ := fun n => ZMod.dft Ψ' (n : ZMod N) with hbA
  set b : ℕ → ℂ := fun n => ZMod.dft (fun x => Ψ' (-x)) (n : ZMod N) with hb
  have hkey : ∀ w : ℂ, 1 < w.re → 0 < w.im →
      (LSeries a w - κ * LSeries b w) * (1 + cexp (-(Real.pi : ℂ) * I * w)) =
        κ * (LSeries bA w - LSeries b w) := by
    intro w hw hwi
    have hq := hquad w (by linarith) hwi
    have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hw; simp at hw; linarith
    have hw1 : w - 1 ≠ 0 := fun h0 => by
      rw [sub_eq_zero] at h0; rw [h0] at hw; simp at hw
    have hΓw : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hcos := cos_pi_mul_div_two_ne_zero hwi.ne'
    rw [G_eq_bigG hsl hid hGd hG2 hw, bigG, ← (hLa w hw).2] at hq
    simp only [lockDual] at hq
    rw [show w * (w - 1) * Gammaℝ (1 - w) * ((2 * (Real.pi : ℂ)) ^ (-w) * Gamma w) =
      w * (w - 1) * (Gammaℝ (1 - w) * ((2 * (Real.pi : ℂ)) ^ (-w) * Gamma w)) by ring,
      gammaR_one_sub_mul_Gamma hcos, ZMod.LFunction_eq_LSeries _ hw,
      ZMod.LFunction_eq_LSeries _ hw] at hq
    have h2cos : 2 * cos ((Real.pi : ℂ) * w / 2) =
        cexp ((Real.pi : ℂ) * I * w / 2) + cexp (-(Real.pi : ℂ) * I * w / 2) := by
      rw [two_cos]; congr 1 <;> congr 1 <;> ring
    have hexp : cexp (-(Real.pi : ℂ) * I * w) =
        cexp (-(Real.pi : ℂ) * I * w / 2) * (cexp ((Real.pi : ℂ) * I * w / 2))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
    have he1 : cexp ((Real.pi : ℂ) * I * w / 2) ≠ 0 := Complex.exp_ne_zero _
    have hsum : cexp ((Real.pi : ℂ) * I * w / 2) + cexp (-(Real.pi : ℂ) * I * w / 2) ≠ 0 := by
      rw [← h2cos]; exact mul_ne_zero two_ne_zero hcos
    rw [h2cos] at hq
    simp only [hbA, hb, hκ]
    set Ep := cexp ((Real.pi : ℂ) * I * w / 2) with hEp
    set Em := cexp (-(Real.pi : ℂ) * I * w / 2) with hEm
    set A := LSeries (fun n : ℕ => ZMod.dft Ψ' (n : ZMod N)) w with hA
    set B := LSeries (fun n : ℕ => ZMod.dft (fun x => Ψ' (-x)) (n : ZMod N)) w with hB
    have hne : w * (w - 1) * Gammaℝ w ≠ 0 := mul_ne_zero (mul_ne_zero hw0 hw1) hΓw
    have hS := inv_mul_cancel₀ hsum
    have hmain : LSeries a w * (Ep + Em) = (N : ℂ) ^ (-(1 / 2 : ℂ)) * (Ep * A + Em * B) := by
      apply mul_left_cancel₀ hne
      linear_combination (Ep + Em) * hq +
        (w * (w - 1) * Gammaℝ w * (N : ℂ) ^ (-(1 / 2 : ℂ)) * (Ep * A + Em * B)) * hS
    rw [hexp]
    field_simp
    linear_combination hmain
  have hbS : ∀ s : ℂ, 1 < s.re → LSeriesSummable b s := fun s hs =>
    ZMod.LSeriesSummable_of_one_lt_re _ hs
  have hbAS : ∀ s : ℂ, 1 < s.re → LSeriesSummable bA s := fun s hs =>
    ZMod.LSeriesSummable_of_one_lt_re _ hs
  have hcoef : ∀ σ : ℝ, 1 < σ → LSeries a σ = LSeries (κ • b) σ := by
    intro σ hσ
    have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
    have hvre : ∀ y : ℝ, 1 < ((σ : ℂ) + (y : ℂ) * I).re := fun y => by simpa using hσ
    set g : ℕ → ℂ := a - κ • b with hg
    have hgS : LSeriesSummable g (σ : ℂ) := (hLa _ hσ').1.sub ((hbS _ hσ').smul κ)
    have hgv : ∀ y : ℝ, LSeries g ((σ : ℂ) + (y : ℂ) * I) =
        LSeries a ((σ : ℂ) + (y : ℂ) * I) - κ * LSeries b ((σ : ℂ) + (y : ℂ) * I) := by
      intro y
      rw [hg, LSeries_sub (hLa _ (hvre y)).1 ((hbS _ (hvre y)).smul κ), LSeries_smul]
    set M : ℝ := ‖κ‖ * ((∑' n, ‖LSeries.term bA (σ : ℂ) n‖) + ∑' n, ‖LSeries.term b (σ : ℂ) n‖)
      with hM
    have hbound : ∀ y : ℝ, 1 ≤ y →
        ‖LSeries g ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M / (Real.exp (Real.pi * y) - 1) := by
      intro y hy
      set w : ℂ := (σ : ℂ) + (y : ℂ) * I with hwdef
      have hwim : 0 < w.im := by simp [hwdef]; linarith
      have hk := hkey w (hvre y) hwim
      have hnorm_e : ‖cexp (-(Real.pi : ℂ) * I * w)‖ = Real.exp (Real.pi * y) := by
        rw [Complex.norm_exp]; congr 1; simp [hwdef]
      have hexp1 : 1 < Real.exp (Real.pi * y) :=
        Real.one_lt_exp_iff.mpr (mul_pos Real.pi_pos (by linarith))
      have hden : Real.exp (Real.pi * y) - 1 ≤ ‖1 + cexp (-(Real.pi : ℂ) * I * w)‖ := by
        have := norm_sub_le (1 + cexp (-(Real.pi : ℂ) * I * w)) 1
        rw [add_sub_cancel_left, norm_one, hnorm_e] at this
        linarith
      have hAB : ‖κ * (LSeries bA w - LSeries b w)‖ ≤ M := by
        rw [norm_mul, hM]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
          (norm_nonneg _)
        · exact norm_LSeries_vertical_le (hbAS _ hσ') y
        · exact norm_LSeries_vertical_le (hbS _ hσ') y
      rw [hgv y, le_div_iff₀ (by linarith)]
      calc ‖LSeries a w - κ * LSeries b w‖ * (Real.exp (Real.pi * y) - 1)
          ≤ ‖LSeries a w - κ * LSeries b w‖ * ‖1 + cexp (-(Real.pi : ℂ) * I * w)‖ :=
            mul_le_mul_of_nonneg_left hden (norm_nonneg _)
        _ = ‖κ * (LSeries bA w - LSeries b w)‖ := by rw [← norm_mul, hk]
        _ ≤ M := hAB
    have hdiv : Tendsto (fun y : ℝ => Real.exp (Real.pi * y) - 1) atTop atTop := by
      have h1 := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
      simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right atTop (-1) h1
    have hlim : Tendsto (fun y : ℝ => M / (Real.exp (Real.pi * y) - 1)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := M)).div_atTop hdiv
    have htend : Tendsto (fun y : ℝ => LSeries g ((σ : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) :=
      squeeze_zero_norm' (by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
        exact hbound y hy) hlim
    have h0 := HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
      (isBohrAlmostPeriodic_LSeries_vertical hgS) htend 0
    rw [hgv 0] at h0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    rw [LSeries_smul]
    exact sub_eq_zero.mp h0
  /- Step 6: uniqueness of Dirichlet coefficients. -/
  refine ⟨fun r => κ * ZMod.dft (fun x => Ψ' (-x)) r, fun n hn => ?_⟩
  have habs_a : LSeries.abscissaOfAbsConv a < ⊤ :=
    ((hLa 2 (by norm_num)).1.abscissaOfAbsConv_le).trans_lt (EReal.coe_lt_top _)
  have habs_b : LSeries.abscissaOfAbsConv (κ • b) < ⊤ :=
    (((hbS 2 (by norm_num)).smul κ).abscissaOfAbsConv_le).trans_lt (EReal.coe_lt_top _)
  have hev : (fun x : ℝ => LSeries a x) =ᶠ[atTop] fun x : ℝ => LSeries (κ • b) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hcoef x hx
  have := LSeries.eq_of_LSeries_eventually_eq habs_a habs_b hev hn
  simpa [hb] using this

end

end AbelianTwist

end RHTower
