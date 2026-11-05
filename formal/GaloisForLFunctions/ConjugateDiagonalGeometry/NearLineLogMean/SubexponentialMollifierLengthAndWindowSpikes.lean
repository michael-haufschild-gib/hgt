import GaloisForLFunctions.ArithmeticProduction.LongMollifiersImplyCriticalClustering
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TwoSidedThetaMollifierTrap
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount

/-!
# Complex Necessary-Length Law up to `exp(T^{1/60})`, Exact `exp(c log²T)` Rate Threshold, and Multi-Window Critical-Line Spikes

This module establishes three unconditional bridges across the near-line mollifier hierarchy:

1. **Hermitian analytic trace and unconditional removal of real-coefficient assumptions (`hbr`):**
   Replacing `(Ψ(z + iT) + Ψ(z - iT)) / 2` by the Hermitian analytic trace
   `edPolyHermitianTrace a s T z = (Ψ(z + iT) + Ψ*(z - iT)) / 2`, where `Ψ*(w) = ∑_{n ∈ s} conj(a_n) n^{-w}`,
   recovers `edPolyHermitianTrace a s T x = Re Ψ(x + iT)` identically for all complex coefficients
   `a : ℕ → ℂ` and preserves both the `5 / 16` head-dominance bound at `z = 4` and the half-plane
   `ℓ¹` bound. Consequently, Backlund's horizontal-edge bound, the Levinson Littlewood budget,
   the critical-line log-integral ceiling, the implications `ComplexMollifiedSecondMomentLaw → CriticalClustering`
   and `ComplexSecondMomentRate K₀ → LogFreeNearLineZeroDensity ∧ LogFreeNearLineWindowOccupancy`,
   and the left-of-line second-moment floor hold unconditionally for all complex Dirichlet polynomials.

2. **Uniform stretched-exponential necessary-length law and exact `exp(c log²T)` rate threshold:**
   Eventually as `T → ∞`, simultaneously for all `1 ≤ N` with `log N ≤ T^{1/60}` and all complex
   Dirichlet polynomials `M(s) = ∑_{n=1}^N b_n n^{-s}` (`b 1 = 1`, `‖b n‖ ≤ 1`),
   `∫_T^{2T} ‖ζ(1/2 + it) M(1/2 + it)‖² dt ≥ (1 + log T / (8 log T + 6 log N)) T`.
   In particular, achieving the `D_zero`/`D_win`-forcing excess `K₀ / log T` requires
   `log N(T) ≥ (log T)² / (6 K₀) - (4 / 3) log T` eventually, ruling out all polynomial and all
   sub-threshold `exp(δ (log T)²)` (`δ < 1 / (6 K₀)`) complex mollifier families, while any complex
   mollifier family with normalized second moment tending to `1` forces `log N(T) / log T → +∞`.

3. **Superposed multi-window critical-line zero spikes (`D_win`):**
   Coloring occupied Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]` modulo `⌈2R + 7⌉₊` superposes
   `TwoSidedThetaMollifierTrap`'s localized critical-line zero spikes across pairwise disjoint
   ordinate intervals, forcing a lower bound `(S.card / ⌈2R + 7⌉₊) · (3 δ / 4) e^{-α/2} Y^{2δ}`
   (and `(S.card / ⌈2R + 7⌉₊) · (3 δ / 4) e^{-2αδ²} Y^{2δ}` whenever `α ≤ log Y`) on the
   critical-line second moment over `[V - R - 3, 2V + R + 3]`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Metric MeromorphicOn intervalIntegral Topology
open scoped BigOperators Interval Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticProduction
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect
open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1. Hermitian analytic trace and complex-coefficient Littlewood / clustering / rate theorems -/

/-- Exact conjugation law for finite complex Dirichlet polynomials:
`conj(∑_{n ∈ s} a_n n^{-z}) = ∑_{n ∈ s} conj(a_n) n^{-conj(z)}`. -/
theorem edPoly_conj_star (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (z : ℂ) :
    (starRingEnd ℂ) (edPoly a s z) =
      edPoly (fun n => (starRingEnd ℂ) (a n)) s ((starRingEnd ℂ) z) := by
  unfold edPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hn
  have hne : (((n : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have hlog : Complex.log ((n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.ofReal_log hpos.le).symm
  rw [map_mul, Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
    hlog, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, map_neg]

/-- The Hermitian analytic trace `(Ψ(z + iT) + Ψ*(z - iT)) / 2` of a complex Dirichlet polynomial
at height `T`, extending `x ↦ Re Ψ(x + iT)` holomorphically to all `z ∈ ℂ`. -/
def edPolyHermitianTrace (a : ℕ → ℂ) (s : Finset ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (edPoly a s (z + (T : ℂ) * I) +
    edPoly (fun n => (starRingEnd ℂ) (a n)) s (z - (T : ℂ) * I)) / 2

theorem differentiable_edPolyHermitianTrace (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) :
    Differentiable ℂ (edPolyHermitianTrace a s T) := by
  have hd1 := differentiable_edPoly a hs
  have hd2 := differentiable_edPoly (fun n => (starRingEnd ℂ) (a n)) hs
  exact fun z => (((hd1 _).comp z (differentiableAt_id.add_const _)).add
    ((hd2 _).comp z (differentiableAt_id.sub_const _))).div_const 2

theorem analyticOnNhd_edPolyHermitianTrace (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) (K : Set ℂ) :
    AnalyticOnNhd ℂ (edPolyHermitianTrace a s T) K :=
  fun z _ => (analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_edPolyHermitianTrace a hs T)) z (Set.mem_univ z)

/-- On the real axis `z = x ∈ ℝ`, `edPolyHermitianTrace a s T x = Re Ψ(x + iT)` identically for all
complex coefficient sequences `a : ℕ → ℂ`. -/
theorem edPolyHermitianTrace_ofReal (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (T x : ℝ) :
    edPolyHermitianTrace a s T (x : ℂ) =
      (((edPoly a s ((x : ℂ) + (T : ℂ) * I)).re : ℝ) : ℂ) := by
  have hconj : ((x : ℂ) - (T : ℂ) * I) = (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [edPolyHermitianTrace, hconj, ← edPoly_conj_star a hs, Complex.add_conj]
  push_cast
  ring

/-- Uniform half-plane `ℓ¹` bound on `Re z ≥ x` for the Hermitian analytic trace. -/
theorem norm_edPolyHermitianTrace_le_of_re_ge (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) {x : ℝ} {z : ℂ} (hz : x ≤ z.re) :
    ‖edPolyHermitianTrace a s T z‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) := by
  have hkey : ∀ (c : ℕ → ℂ) (w : ℂ), (∀ n ∈ s, ‖c n‖ = ‖a n‖) → w.re = z.re →
      ‖edPoly c s w‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) := by
    intro c w hnorm hw
    refine (norm_edPoly_le c hs w).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [hnorm n hn]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs n hn
    have hmono : ((n : ℝ) ^ (-w.re)) ≤ ((n : ℝ) ^ (-x)) := by
      refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
      rw [hw]; linarith
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have h1 : ‖edPoly a s (z + (T : ℂ) * I)‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) :=
    hkey a _ (fun _ _ => rfl) (by simp)
  have h2 : ‖edPoly (fun n => (starRingEnd ℂ) (a n)) s (z - (T : ℂ) * I)‖ ≤
      ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) :=
    hkey _ _ (fun n _ => Complex.norm_conj (a n)) (by simp)
  rw [edPolyHermitianTrace, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have htri := norm_add_le (edPoly a s (z + (T : ℂ) * I))
    (edPoly (fun n => (starRingEnd ℂ) (a n)) s (z - (T : ℂ) * I))
  linarith [htri, h1, h2]

/-- Head dominance at `z = 4` for the Hermitian analytic trace of any normalized bounded complex
Dirichlet polynomial (`b 1 = 1`, `‖b n‖ ≤ 1`). -/
theorem five_sixteenth_le_norm_edPolyHermitianTrace_four (b : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (h1 : 1 ∈ s) (hb1 : b 1 = 1) (hbn : ∀ n ∈ s, ‖b n‖ ≤ 1) (T : ℝ) :
    (5 / 16 : ℝ) ≤ ‖edPolyHermitianTrace b s T 4‖ := by
  have hexp4 : Real.exp (-(Real.log 2) * (4 : ℝ)) = 1 / 16 := by
    rw [exp_neg_log_two_eq, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hp : ‖edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1‖ ≤ 11 / 16 := by
    have h := norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn
      (z := (4 : ℂ) + (T : ℂ) * I) (by simp; norm_num)
    have hre : ((4 : ℂ) + (T : ℂ) * I).re = 4 := by simp
    rw [hre, hexp4] at h; linarith
  have hb1_conj : (starRingEnd ℂ) (b 1) = 1 := by rw [hb1, map_one]
  have hbn_conj : ∀ n ∈ s, ‖(starRingEnd ℂ) (b n)‖ ≤ 1 := fun n hn => by
    rw [Complex.norm_conj]; exact hbn n hn
  have hm : ‖edPoly (fun n => (starRingEnd ℂ) (b n)) s ((4 : ℂ) - (T : ℂ) * I) - 1‖ ≤ 11 / 16 := by
    have h := norm_edPoly_sub_one_le_exp (fun n => (starRingEnd ℂ) (b n)) hs h1 hb1_conj hbn_conj
      (z := (4 : ℂ) - (T : ℂ) * I) (by simp; norm_num)
    have hre : ((4 : ℂ) - (T : ℂ) * I).re = 4 := by simp
    rw [hre, hexp4] at h; linarith
  have htr : edPolyHermitianTrace b s T 4 - 1 =
      ((edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1) +
        (edPoly (fun n => (starRingEnd ℂ) (b n)) s ((4 : ℂ) - (T : ℂ) * I) - 1)) / 2 := by
    unfold edPolyHermitianTrace; ring
  have hdist : ‖edPolyHermitianTrace b s T 4 - 1‖ ≤ 11 / 16 := by
    rw [htr, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have htri := norm_add_le (edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1)
      (edPoly (fun n => (starRingEnd ℂ) (b n)) s ((4 : ℂ) - (T : ℂ) * I) - 1)
    linarith [htri, hp, hm]
  have hrev := norm_sub_norm_le (1 : ℂ) (edPolyHermitianTrace b s T 4)
  rw [norm_one, norm_sub_rev] at hrev
  linarith

/-- Jensen's disc divisor bound on `closedBall 4 |r|` (`0 < r < 8`) for `edPolyHermitianTrace`. -/
theorem edPolyHermitianTrace_count_le (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    {r m Mb : ℝ} (hr : 0 < r) (hrlt : r < 8) (hm : 0 < m) (hM1 : 1 ≤ Mb)
    (hcentre : m ≤ ‖edPolyHermitianTrace a s T 4‖)
    (hmass : (∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb) :
    ∑ᶠ u, MeromorphicOn.divisor (edPolyHermitianTrace a s T) (closedBall (4 : ℂ) |r|) u
      ≤ Real.log (Mb / m) / Real.log (8 / r) := by
  have hsphere : ∀ z ∈ sphere (4 : ℂ) |(8 : ℝ)|, ‖edPolyHermitianTrace a s T z‖ ≤ Mb := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hz
    have hre : (-4 : ℝ) ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - 4)
      have hrz : (z - 4).re = z.re - 4 := by simp
      rw [hrz, hz, abs_le] at h
      linarith [h.1]
    refine (norm_edPolyHermitianTrace_le_of_re_ge a hs T hre).trans (le_trans ?_ hmass)
    exact le_of_eq (Finset.sum_congr rfl fun _ _ => by norm_num)
  exact sum_divisor_le_of_bounds (c := (4 : ℂ)) (r := r) (R := (8 : ℝ))
    (M := Mb) (m := m) (f := edPolyHermitianTrace a s T)
    (by rwa [abs_of_pos hr])
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0 : ℝ) < 8)]; exact hrlt)
    hM1 hm (analyticOnNhd_edPolyHermitianTrace a hs T _) hcentre hsphere

/-- **Backlund weighted horizontal-edge bound for arbitrary complex Dirichlet polynomials.** -/
theorem abs_integral_weighted_im_logDeriv_edPoly_complex_le
    (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    {c e r m Mb : ℝ} (hce : c < e) (hr : 0 < r) (hrlt : r < 8)
    (hcr : 4 - r ≤ c) (her : e ≤ 4 + r)
    (hne : ∀ x ∈ Set.Icc c e, edPoly a s ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hm : 0 < m) (hM1 : 1 ≤ Mb)
    (hcentre : m ≤ ‖edPolyHermitianTrace a s T 4‖)
    (hmass : (∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb) :
    |∫ x in c..e, (x - c) *
        (logDeriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ 2 * (e - c) *
        ((Real.log (Mb / m) / Real.log (8 / r) + 1) * Real.pi) := by
  classical
  set K : Set ℂ := closedBall (4 : ℂ) |r| with hK
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hana : AnalyticOnNhd ℂ (edPolyHermitianTrace a s T) K :=
    analyticOnNhd_edPolyHermitianTrace a hs T K
  have htracene : ∃ z : ℂ, edPolyHermitianTrace a s T z ≠ 0 := by
    refine ⟨4, fun h0 => ?_⟩
    rw [h0, norm_zero] at hcentre; linarith
  have hord : ∀ z ∈ K, analyticOrderAt (edPolyHermitianTrace a s T) z ≠ ⊤ := fun z _ =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero
      (analyticOnNhd_edPolyHermitianTrace a hs T Set.univ) htracene z
  have hfin : {u : ℂ | u ∈ K ∧ edPolyHermitianTrace a s T u = 0}.Finite := by
    refine ((MeromorphicOn.divisor (edPolyHermitianTrace a s T) K).finiteSupport hKcompact).subset ?_
    intro u hu
    rw [Function.mem_support]
    have h1 := one_le_divisor_of_zero hana hu.1 hu.2 (hord u hu.1)
    omega
  have hfinR : {x : ℝ | (x : ℂ) ∈ K ∧ edPolyHermitianTrace a s T (x : ℂ) = 0}.Finite := by
    refine Set.Finite.ofFinset (hfin.toFinset.preimage (fun x : ℝ => (x : ℂ))
      (fun _ _ _ _ h => Complex.ofReal_inj.mp h)) ?_
    intro x; rw [Finset.mem_preimage, Set.Finite.mem_toFinset]; rfl
  set Z : Finset ℝ := hfinR.toFinset with hZdef
  set f : ℝ → ℂ := fun x => edPoly a s ((x : ℂ) + (T : ℂ) * I) with hfdef
  set f' : ℝ → ℂ := fun x => deriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I) with hf'def
  have hZmem : ∀ x ∈ Set.Ioo c e, (f x).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [hK, mem_closedBall, abs_of_pos hr, Complex.dist_eq]
      have hval : ‖((x : ℂ) - 4)‖ = |x - 4| := by
        rw [show ((x : ℂ) - 4) = ((x - 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le]; constructor <;> linarith [hx.1, hx.2]
    · rw [edPolyHermitianTrace_ofReal a hs T x]
      rw [hfdef] at hzero; simp only at hzero; rw [hzero]; norm_num
  have hbound := abs_integral_weighted_im_logDeriv_le_of_finite_re_zeros hce.le
    (f := f) (f' := f') (fun x => hasDerivAt_edPoly_horiz a hs T x)
    (continuous_edPoly_horiz a hs T) (continuous_deriv_edPoly_horiz a hs T)
    (fun x hx => hne x hx) Z hZmem
  have hcongr : ∀ x ∈ Set.uIcc c e,
      (x - c) * (f' x / f x).im =
        (x - c) * (logDeriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)).im := by
    intro x _; rw [hf'def, hfdef, logDeriv_apply]
  rw [intervalIntegral.integral_congr hcongr] at hbound
  refine hbound.trans ?_
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo c e)).card : ℝ)
      ≤ Real.log (Mb / m) / Real.log (8 / r) := by
    have hsubc : (Z.filter (fun z => z ∈ Set.Ioo c e)).card ≤ Z.card := Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun _ _ h => Complex.ofReal_inj.mp h)
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ K ∧ edPolyHermitianTrace a s T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rwa [hZdef, Set.Finite.mem_toFinset] at hx
    have hle := card_le_divisor_sum hKcompact hana hord _ hS
    rw [himg] at hle
    have hjensen := edPolyHermitianTrace_count_le a hs T hr hrlt hm hM1 hcentre hmass
    have hcast : ((Z.card : ℤ) : ℝ)
        ≤ ((∑ᶠ u, MeromorphicOn.divisor (edPolyHermitianTrace a s T) K u : ℤ) : ℝ) := by
      exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo c e)).card : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast hsubc
    push_cast at hcast; linarith
  have hstep : (((Z.filter (fun z => z ∈ Set.Ioo c e)).card : ℝ) + 1) * Real.pi
      ≤ (Real.log (Mb / m) / Real.log (8 / r) + 1) * Real.pi :=
    mul_le_mul_of_nonneg_right (by linarith [hcard]) Real.pi_pos.le
  have hwidth : (0 : ℝ) < e - c := by linarith
  nlinarith [hstep, hwidth]

/-- **Littlewood's floor for any normalized bounded complex Dirichlet polynomial on `Re s = 1/2`.** -/
theorem exists_edPoly_line_logMean_floor_complex :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ : ℝ, T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        -(C + K * Real.log Mb) ≤
          ∫ t in T₁..T₂,
            Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  classical
  set α : ℝ := Real.log 2
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 11 * Real.exp (-α * (15 / 2)) / α)
  set Cfar' : ℝ := 2 * ((2 * 11 * Real.exp α) * Real.exp (-α * (15 / 2)) / α)
  set L : ℝ := Real.log (32 / 15)
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  set KH : ℝ := 2 * 7 * Real.pi
  have hKHpos : 0 < KH := by positivity
  refine ⟨Cfar + 7 * Cfar' + 2 * (KH * (Real.log (16 / 5) / L + 1)), 2 * (KH / L),
    by positivity, by positivity, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ hT hP1 hP2
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  set Ψ : ℂ → ℂ := edPoly b s
  have hΨan : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have huIccx : uIcc (1 / 2 : ℝ) (15 / 2 : ℝ) = Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) :=
    uIcc_of_le (by norm_num)
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re → AnalyticAt ℂ Ψ z := fun z _ => hΨan z (Set.mem_univ z)
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re → ‖Ψ z - 1‖ ≤ 11 * Real.exp (-α * z.re) :=
    fun z hz => norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn (z := z) (by linarith)
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re → ‖Ψ z - 1‖ ≤ 1 / 2 :=
    fun z hz => norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn hz.le
  have hfarlog : |∫ t in T₁..T₂, Real.log ‖Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂, (logDeriv Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    have h := hfarsmall (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
    rw [h0, show ‖(0 : ℂ) - 1‖ = 1 by simp] at h
    norm_num at h
  have hhoriz : ∀ T : ℝ,
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), Ψ ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..(15 / 2 : ℝ), (x - 1 / 2) *
          (logDeriv Ψ ((x : ℂ) + (T : ℂ) * I)).im| ≤
        KH * (Real.log (16 / 5) / L + 1) + (KH / L) * Real.log Mb := by
    intro T hne
    have h := abs_integral_weighted_im_logDeriv_edPoly_complex_le b hs T
      (c := 1 / 2) (e := 15 / 2) (r := 15 / 4) (m := 5 / 16) (Mb := Mb)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hne (by norm_num)
      hMb1 (five_sixteenth_le_norm_edPolyHermitianTrace_four b hs h1 hb1 hbn T) hmass
    have hlogq : Real.log (Mb / (5 / 16)) = Real.log Mb + Real.log (16 / 5) := by
      rw [div_eq_mul_inv, Real.log_mul (by positivity) (by norm_num)]; congr 1; norm_num
    have hL' : Real.log (8 / (15 / 4 : ℝ)) = L := by dsimp [L]; norm_num
    rw [hlogq, hL', show ((15 / 2 : ℝ) - 1 / 2) = 7 by norm_num] at h
    refine h.trans (le_of_eq ?_)
    dsimp [KH]; field_simp; ring
  have hH1 := hhoriz T₁ hP1
  have hH2 := hhoriz T₂ hP2
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨_, hΨright T₁⟩
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hΨan hΨne
      (by norm_num : (1 / 2 : ℝ) < 15 / 2) hT
      (fun x hx => hP1 x (by rwa [huIccx] at hx))
      (fun x hx => hP2 x (by rwa [huIccx] at hx))
      (fun t _ => hΨright t)
  have hmass0 : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt Ψ w).toNat : ℝ) * (w.re - 1 / 2) := by
    refine Finset.sum_nonneg fun w hw => ?_
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hwlb : 0 ≤ weightedLittlewoodBoundary Ψ (1 / 2) (15 / 2) T₁ T₂ := by
    rw [← hident]; exact mul_nonneg (by positivity) hmass0
  unfold weightedLittlewoodBoundary at hwlb
  rw [show ((15 / 2 : ℝ) - 1 / 2) = 7 by norm_num] at hwlb
  have hlogMb : 0 ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨hfl1, hfl2⟩ := abs_le.mp hfarlog
  obtain ⟨hfd1, hfd2⟩ := abs_le.mp hfarld
  obtain ⟨hh11, hh12⟩ := abs_le.mp hH1
  obtain ⟨hh21, hh22⟩ := abs_le.mp hH2
  have hKL : 0 ≤ KH / L := by positivity
  nlinarith [hKL, hlogMb]

/-- **The Littlewood budget of the Levinson mollified detector for complex mollifiers.** -/
theorem exists_levinson_mollified_budget_complex_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ lam : ℝ, |lam| ≤ 1 →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧
          levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite →
        (∃ t ∈ Set.Ioo T₁ T₂,
          levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
        weightedLittlewoodBoundary
            (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)) σ₀ (15 / 2) T₁ T₂
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨KG, hKG, hGhoriz⟩ := exists_horizontal_weighted_levinsonG_bound
  set α : ℝ := Real.log 2
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 22 * Real.exp (-α * (15 / 2)) / α)
  set Cfar' : ℝ := 2 * ((2 * 22 * Real.exp α) * Real.exp (-α * (15 / 2)) / α)
  have hCfar0 : 0 < Cfar := by positivity
  have hCfar'0 : 0 < Cfar' := by positivity
  set Kpsi : ℝ := 2 * (15 / 2 : ℝ) * Real.pi / Real.log (8 / (15 / 4 : ℝ)) with hKpsi
  have hlog2pos : 0 < Real.log (8 / (15 / 4 : ℝ)) := Real.log_pos (by norm_num)
  have hKpsi0 : 0 < Kpsi := by rw [hKpsi]; positivity
  refine ⟨Cfar + (15 / 2) * Cfar' + 2 * (2 * (15 / 2 : ℝ) *
      ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)) + 1,
    2 * KG + 2 * Kpsi + 1, by positivity, by positivity, ?_⟩
  intro lam hlam b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hfin hex hMsq
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hlamC : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hleft : (∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) := by
    have hana : ∀ t ∈ uIcc T₁ T₂,
        AnalyticAt ℂ (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((σ₀ : ℂ) + (t : ℂ) * I) := by
      intro t ht; rw [huIcct] at ht
      exact analyticAt_levinsonMollifiedDetector _ b hs (hne1 σ₀ t (by linarith [ht.1]))
    linarith [integral_log_norm_le_of_meanSquare hT hana hfin hex hMsq]
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re →
      AnalyticAt ℂ (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) z := by
    intro z hz
    refine analyticAt_levinsonMollifiedDetector _ b hs fun hEq => ?_
    rw [hEq, Complex.one_re] at hz; linarith
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s z - 1‖ ≤ 22 * Real.exp (-α * z.re) :=
    fun _ hz => norm_levinsonMollifiedDetector_sub_one_le_exp hlamC b hs h1 hb1 hbn hz.le
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s z - 1‖ ≤ 1 / 2 :=
    fun _ hz => norm_levinsonMollifiedDetector_sub_one_le_half hlamC b hs h1 hb1 hbn hz.le
  have hfarlog : |∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hhoriz : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), edPoly b s ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
          (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
            ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ KG * Real.log T + (Kpsi * Real.log Mb
            + 2 * (15 / 2 : ℝ) *
              ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)) := by
    intro T hT20 hGne hPne
    have hGana : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
        AnalyticAt ℂ (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I) := fun x _ =>
      analyticAt_levinsonG _ (hne1 x T hT20)
    have hPana : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
        AnalyticAt ℂ (edPoly b s) ((x : ℂ) + (T : ℂ) * I) := fun x _ =>
      (analyticOnNhd_edPoly b hs) _ (Set.mem_univ _)
    have hGi := (continuousOn_weighted_im_logDeriv_horizontal hGana
      (fun x hx => hGne x (by rwa [huIccx] at hx))).intervalIntegrable
    have hPi := (continuousOn_weighted_im_logDeriv_horizontal hPana
      (fun x hx => hPne x (by rwa [huIccx] at hx))).intervalIntegrable
    have hsplit : (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
        (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((x : ℂ) + (T : ℂ) * I)).im)
        = (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
            (logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im)
          + ∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
            (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im := by
      rw [← intervalIntegral.integral_add hGi hPi]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [huIccx] at hx
      have hld : logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((x : ℂ) + (T : ℂ) * I)
          = logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)
            + logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I) :=
        logDeriv_mul _ (hGne x hx) (hPne x hx)
          (analyticAt_levinsonG _ (hne1 x T hT20)).differentiableAt
          (differentiable_edPoly b hs _)
      rw [hld, Complex.add_im]; ring
    rw [hsplit]
    have hGbound := hGhoriz lam hlam T (by linarith) σ₀ (15 / 2 : ℝ) hσ₀ hσ₀15 le_rfl hGne
    have hPbound := abs_integral_weighted_im_logDeriv_edPoly_complex_le b hs T
      (c := σ₀) (e := (15 / 2 : ℝ)) (r := (15 / 4 : ℝ)) (m := (5 / 16 : ℝ)) (Mb := Mb)
      hσ₀15 (by norm_num) (by norm_num) (by linarith) (by norm_num) hPne (by norm_num) hMb1
      (five_sixteenth_le_norm_edPolyHermitianTrace_four b hs h1 hb1 hbn T) hmass
    have hlogsplit : Real.log (Mb / (5 / 16 : ℝ)) = Real.log Mb + Real.log (16 / 5 : ℝ) := by
      rw [Real.log_div (by linarith) (by norm_num),
        show (16 / 5 : ℝ) = ((5 / 16 : ℝ))⁻¹ by norm_num, Real.log_inv]; ring
    rw [hlogsplit] at hPbound
    have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
    have hPfinal : |∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
        (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ Kpsi * Real.log Mb
          + 2 * (15 / 2 : ℝ) *
            ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi) := by
      refine hPbound.trans ?_
      have hlog165 : (0 : ℝ) ≤ Real.log (16 / 5 : ℝ) := Real.log_nonneg (by norm_num)
      have hq : (0 : ℝ) ≤ (Real.log Mb + Real.log (16 / 5 : ℝ)) /
          Real.log (8 / (15 / 4 : ℝ)) := div_nonneg (by linarith) hlog2pos.le
      have hnn : (0 : ℝ) ≤ ((Real.log Mb + Real.log (16 / 5 : ℝ)) /
          Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi :=
        mul_nonneg (by linarith) Real.pi_pos.le
      have hexpand := mul_le_mul_of_nonneg_right
        (by linarith : 2 * ((15 / 2 : ℝ) - σ₀) ≤ 2 * (15 / 2 : ℝ)) hnn
      refine hexpand.trans (le_of_eq ?_)
      rw [hKpsi]; field_simp; ring
    exact (abs_add_le _ _).trans (by linarith [hGbound, hPfinal])
  have hH1 := hhoriz T₁ h20 hG1 hP1
  have hH2 := hhoriz T₂ (by linarith) hG2 hP2
  have hlogT1 : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log (by linarith) hT.le
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
  unfold weightedLittlewoodBoundary
  have hR : ((15 / 2 : ℝ) - σ₀) * (∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) ≤ (15 / 2 : ℝ) * Cfar' := by
    have hstep1 := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans hfarld) (by linarith : (0 : ℝ) ≤ (15 / 2 : ℝ) - σ₀)
    have hstep2 := mul_le_mul_of_nonneg_right (by linarith : (15 / 2 : ℝ) - σ₀ ≤ 15 / 2) hCfar'0.le
    linarith
  have hL1 : -(∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ Cfar := by
    linarith [hfarlog, neg_abs_le (∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)]
  have hHa := le_abs_self (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
    (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) ((x : ℂ) + (T₁ : ℂ) * I)).im)
  have hHb := neg_abs_le (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
    (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) ((x : ℂ) + (T₂ : ℂ) * I)).im)
  have hKbound : KG * Real.log T₁ + KG * Real.log T₂ + 2 * Kpsi * Real.log Mb
      ≤ (2 * KG + 2 * Kpsi + 1) * (Real.log T₂ + Real.log Mb) := by
    have hstep := mul_le_mul_of_nonneg_left hlogT1 hKG.le
    nlinarith [hlogT2, hlogMb, hKG.le, hKpsi0.le]
  linarith [hleft, hL1, hR, hH1, hH2, hHa, hHb, hKbound]

/-- **Wide-rectangle horizontal moment of `ζ`-zeros from a complex mollified mean square.** -/
theorem exists_zetaWideMoment_le_of_complex_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hbudget⟩ := exists_levinson_mollified_budget_complex_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hMsq Z hZ
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hlamN : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hG0 : ∀ z : ℂ, levinsonG ((0 : ℝ) : ℂ) z = riemannZeta z := fun z => by simp [levinsonG]
  set Ψ : ℂ → ℂ := edPoly b s
  set g : ℂ → ℂ := levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s
  set F : ℂ → ℂ := fun z => levinsonGEntire ((0 : ℝ) : ℂ) z * Ψ z
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    have hd := norm_edPoly_sub_one_le_half_of_six_le b hs h1mem hb1 hbn
      (z := ((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
    rw [show edPoly b s = Ψ from rfl, h0, show ‖(0 : ℂ) - 1‖ = 1 by simp] at hd
    norm_num at hd
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, hΨright T₁⟩
  have hGeright : ∀ t : ℝ,
      levinsonGEntire ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun _ => levinsonGEntire_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hGright : ∀ t : ℝ,
      levinsonG ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun _ => levinsonG_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hG1' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := fun x hx => by
    rw [hG0]; exact hG1 x hx
  have hG2' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := fun x hx => by
    rw [hG0]; exact hG2 x hx
  have hFbot : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ), F ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP1 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20)]; exact hG1' x hx
  have hFtop : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ), F ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP2 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith))]; exact hG2' x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂, F (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => mul_ne_zero (hGeright t) (hΨright t)
  have hGan : AnalyticOnNhd ℂ (levinsonGEntire ((0 : ℝ) : ℂ)) Set.univ :=
    analyticOnNhd_levinsonGEntire _
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz => (hGan z hz).mul (hΨana z hz)
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, mul_ne_zero (hGeright T₁) (hΨright T₁)⟩
  have hGorder : ∀ w : ℂ, analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hGan ⟨_, hGeright T₁⟩ w
  have hPorder : ∀ w : ℂ, analyticOrderAt Ψ w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hΨana hΨne w
  have hrectfin : {z ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) | F z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hFan hFne
      ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    simpa using h
  have hmemleft : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      ((σ₀ : ℂ) + (t : ℂ) * I) ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) := fun t ht =>
    Complex.mem_reProdIm.mpr ⟨by simp [left_mem_uIcc], by simpa using ht⟩
  have hgFzero : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      (g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 ↔ F ((σ₀ : ℂ) + (t : ℂ) * I) = 0) := by
    intro t ht; rw [huIcct] at ht
    have hzne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
    constructor
    · intro h0
      have hrel : F ((σ₀ : ℂ) + (t : ℂ) * I) =
          (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) := by
        dsimp [F, g, levinsonMollifiedDetector]; rw [levinsonGEntire_eq _ hzne]; ring
      rw [hrel, h0, mul_zero]
    · intro h0
      have hgauge : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hzne
      have heq : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
        rw [← h0]; dsimp [F, g, levinsonMollifiedDetector]; rw [levinsonGEntire_eq _ hzne]; ring
      rcases mul_eq_zero.mp heq with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hgauge
      · exact h
  have hgfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    refine Set.Finite.of_finite_image (Set.Finite.subset hrectfin ?_)
      (fun _ _ _ _ hxy => by simpa using congrArg Complex.im hxy)
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨hmemleft t ht, (hgFzero t ht).mp hz⟩
  have hgex : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact (Set.Ioo_infinite hT) (hgfin.subset fun t ht =>
      ⟨by rw [huIcct]; exact Set.Ioo_subset_Icc_self ht, hall t ht⟩)
  have hMsq' : (∫ t in T₁..T₂,
      ‖levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq := by
    refine le_trans (le_of_eq (intervalIntegral.integral_congr fun t _ => ?_)) hMsq
    simp only [levinsonMollifiedDetector, hG0]
  have hbud := hbudget 0 (by simp) b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀ hσ₀' h20 hT hG1' hG2' hP1 hP2 hgfin hgex hMsq'
  have hUsub : (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} := by
    intro z hz hEq
    have him := (Complex.mem_reProdIm.mp hz).2
    rw [huIcct, hEq, Complex.one_im] at him; linarith [him.1]
  have hcongrF : weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr isOpen_ne hUsub fun z hz => ?_
    dsimp [F, g, levinsonMollifiedDetector]; rw [levinsonGEntire_eq _ hz]; ring
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul hσ₀15 hT ?_ ?_ ?_ ?_ ?_ hgfin
    · intro hmem; exact hUsub hmem rfl
    · intro z hz; exact analyticAt_levinsonMollifiedDetector _ b hs (hUsub hz)
    · intro x hx; rw [huIccx] at hx; exact mul_ne_zero (hG1' x hx) (hP1 x hx)
    · intro x hx; rw [huIccx] at hx; exact mul_ne_zero (hG2' x hx) (hP2 x hx)
    · intro t _; exact mul_ne_zero (hGright t) (hΨright t)
  obtain ⟨Z', hZ', hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hFan hFne hσ₀15 hT
      hFbot hFtop hFright
  have hsub : Z ⊆ Z' := by
    intro w hw
    obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hw
    refine (hZ' w).mpr ⟨hwmem, ?_⟩
    have hw1 : w ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hwzero)
    dsimp [F]; rw [levinsonGEntire_eq _ hw1, hG0, hwzero]; ring
  have horderG : ∀ w ∈ Z,
      analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w = analyticOrderAt riemannZeta w := by
    intro w hw
    obtain ⟨_, hwzero⟩ := (hZ w).mp hw
    have hw1 : w ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hwzero)
    have hev : levinsonGEntire ((0 : ℝ) : ℂ) =ᶠ[nhds w]
        (fun z : ℂ => (z - 1) ^ 2) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
      rw [Pi.mul_apply, levinsonGEntire_eq _ hz, hG0]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2) w :=
      (analyticAt_id.sub analyticAt_const).pow 2
    rw [analyticOrderAt_congr hev,
      analyticOrderAt_mul hpow_an (analyticAt_riemannZeta_of_ne_one hw1),
      (hpow_an.analyticOrderAt_eq_zero).mpr (pow_ne_zero 2 (sub_ne_zero.mpr hw1)), zero_add]
  have hterm : ∀ w ∈ Z,
      ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
        ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [huIccx] at hre
    have hmul : analyticOrderAt F w
        = analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w + analyticOrderAt Ψ w :=
      analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨana w (Set.mem_univ _))
    have hord : ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤ ((analyticOrderAt F w).toNat : ℝ) := by
      rw [hmul, ENat.toNat_add (hGorder w) (hPorder w), ← horderG w hw]
      push_cast; linarith [Nat.cast_nonneg (analyticOrderAt Ψ w).toNat]
    exact mul_le_mul_of_nonneg_right hord (by linarith [hre.1])
  have hZ'nonneg : ∀ w ∈ Z', 0 ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ' w).mp hw).1).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hsum : (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀))
      ≤ ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) :=
    (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w hw _ => hZ'nonneg w hw)
  calc 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
      ≤ 2 * Real.pi * ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂ := hident
    _ = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by rw [hcongrF, hgaugefree]
    _ ≤ _ := hbud

/-- **Left-of-line second-moment floor for arbitrary complex mollifiers.** -/
theorem exists_left_floor_complex :
    ∃ C K₁ : ℝ, 0 < C ∧ 0 < K₁ ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb → (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ a T₁ T₂ : ℝ, 0 < a → a ≤ 1 / 4 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      0 < 2 * Real.pi * (a * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)) - C -
          K₁ * (Real.log T₂ + Real.log Mb) →
      (T₂ - T₁) * Real.exp (2 / (T₂ - T₁) * (2 * Real.pi * (a * ((xiPosZeroCount T₂ : ℝ) -
          xiPosZeroCount T₁)) - C - K₁ * (Real.log T₂ + Real.log Mb))) ≤
        ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨C, K₁, hC, hK₁, hwide⟩ := exists_zetaWideMoment_le_of_complex_mollified_meanSquare
  refine ⟨C, K₁, hC, hK₁, ?_⟩
  intro b N hN hb1 hbn Mb hMb hmass a T₁ T₂ ha0 ha1 h20 hT hG1 hG2 hP1 hP2 hpos
  have hlen : 0 < T₂ - T₁ := by linarith
  set σ₀ : ℝ := 1 / 2 - a with hσ₀
  have hσ₀a : 1 / 4 ≤ σ₀ := by rw [hσ₀]; linarith
  have hσ₀b : σ₀ < 1 / 2 := by rw [hσ₀]; linarith
  have hsub : Set.Icc σ₀ (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc_left hσ₀a
  set I₀ : ℝ := ∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
    edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hI₀
  obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT
  have hc := hwide b N hN hb1 hbn Mb hMb hmass σ₀ T₁ T₂ I₀ hσ₀a hσ₀b h20 hT
    (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx))
    (fun x hx => hP1 x (hsub hx)) (fun x hx => hP2 x (hsub hx)) le_rfl Z hZ
  have hbridge := window_count_add_tail_le_zetaWideSum (d := a) ha0.le hT.le Z (by
    rw [← hσ₀]; exact hZ)
  rw [← hσ₀] at hbridge
  have htail : 0 ≤ offLineTail a T₂ - offLineTail a T₁ := sub_nonneg.mpr (offLineTail_mono hT.le)
  set Δ := (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁
  have hchain : 2 * Real.pi * (a * Δ) ≤
      (T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁)) + C + K₁ * (Real.log T₂ + Real.log Mb) := by
    have h1 := mul_le_mul_of_nonneg_left hbridge (by positivity : 0 ≤ 2 * Real.pi)
    have h2 : 0 ≤ 2 * Real.pi * (offLineTail a T₂ - offLineTail a T₁) :=
      mul_nonneg (by positivity) htail
    have h3 : 2 * Real.pi * (a * Δ + (offLineTail a T₂ - offLineTail a T₁)) =
        2 * Real.pi * (a * Δ) + 2 * Real.pi * (offLineTail a T₂ - offLineTail a T₁) := by ring
    linarith
  set E₀ := 2 * Real.pi * (a * Δ) - C - K₁ * (Real.log T₂ + Real.log Mb) with hE₀
  have hlog : E₀ ≤ (T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁)) := by rw [hE₀]; linarith
  have hI₀nn : 0 ≤ I₀ := by
    rw [hI₀]; exact intervalIntegral.integral_nonneg hT.le fun _ _ => by positivity
  have hI₀pos : 0 < I₀ := by
    rcases hI₀nn.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_div, Real.log_zero, mul_zero] at hlog; linarith
  have hexp : 2 / (T₂ - T₁) * E₀ ≤ Real.log (I₀ / (T₂ - T₁)) := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / (T₂ - T₁))
    have h2 : 2 / (T₂ - T₁) * ((T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁))) =
        Real.log (I₀ / (T₂ - T₁)) := by field_simp
    linarith
  have h3 := Real.exp_le_exp.mpr hexp
  rw [Real.exp_log (by positivity), le_div_iff₀ hlen] at h3
  linarith

/-- **Off-line first moment from a complex mollified mean square on `σ₀ ∈ [1/4, 1/2)`.** -/
theorem exists_zetaOffLineFirstMoment_le_of_complex_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_complex_mollified_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hMsq Z hZ
  obtain ⟨Z', hZ'⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT
  have hw := hwide b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hMsq Z' hZ'
  have hsub : Z ⊆ Z' := by
    intro z hz
    obtain ⟨hmem, hζ⟩ := (hZ z).mp hz
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hmem
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    refine (hZ' z).mpr ⟨Complex.mem_reProdIm.mpr ⟨?_, him⟩, hζ⟩
    rw [uIcc_of_le (by linarith : σ₀ ≤ 15 / 2)]
    exact ⟨hσ₀'.le.trans hre.1, hre.2⟩
  have hterm : ∀ z ∈ Z,
      ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - 1 / 2) ≤
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - σ₀) := by
    intro z _
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hnn : ∀ z ∈ Z', 0 ≤ ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - σ₀) := by
    intro z hz
    have hre := (Complex.mem_reProdIm.mp ((hZ' z).mp hz).1).1
    rw [uIcc_of_le (by linarith : σ₀ ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hsum := (Finset.sum_le_sum hterm).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => hnn z hz)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hw

/-- **Off-line first moment from the complex mollified mean square on the critical line.** -/
theorem exists_zetaOffLineFirstMoment_le_of_complex_line_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaOffLineFirstMoment_le_of_complex_mollified_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq Z hZ
  have hlen : (0 : ℝ) < T₂ - T₁ := by linarith
  set m : ℝ → ℝ := fun σ : ℝ => ∫ t in T₁..T₂,
      ‖riemannZeta ((lineClamp σ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((lineClamp σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hm
  have hmcont : Continuous m := continuous_clamped_meanSquare b N T₁ T₂
  have hmhalf : m (1 / 2) ≤ Msq := by
    simp only [hm]; rw [lineClamp_of_mem (by norm_num)]; exact hMsq
  have hstep : ∀ ε : ℝ, 0 < ε →
      2 * Real.pi *
          (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
        ≤ (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁))
            + C + K * (Real.log T₂ + Real.log Mb) := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hmcont.continuousAt ε hε
    set σ₀ : ℝ := max (1 / 4) (1 / 2 - δ / 2) with hσ₀def
    have hσ₀ : 1 / 4 ≤ σ₀ := le_max_left _ _
    have hσ₀' : σ₀ < 1 / 2 := by rw [hσ₀def]; exact max_lt (by norm_num) (by linarith)
    have hdist : dist σ₀ (1 / 2) < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith, by linarith [le_max_right (1 / 4 : ℝ) (1 / 2 - δ / 2)]⟩
    have hmσ₀ : m σ₀ ≤ Msq + ε := by
      have h := hδε hdist
      rw [Real.dist_eq, abs_sub_lt_iff] at h
      linarith [h.1, hmhalf]
    have hmσ₀' : (∫ t in T₁..T₂,
        ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq + ε := by
      simpa only [hm, lineClamp_of_mem ⟨hσ₀, hσ₀'.le⟩] using hmσ₀
    have hsub : Set.Icc σ₀ (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
      Set.Icc_subset_Icc hσ₀ le_rfl
    exact hmain b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ (Msq + ε) hσ₀ hσ₀' h20 hT
      (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx))
      (fun x hx => hP1 x (hsub hx)) (fun x hx => hP2 x (hsub hx)) hmσ₀' Z hZ
  have hlim : Tendsto (fun ε : ℝ =>
      (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
      (𝓝[>] 0) (𝓝 ((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
        + C + K * (Real.log T₂ + Real.log Mb))) := by
    have hcont : ContinuousAt (fun ε : ℝ =>
        (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
        0 := by
      have hlog : ContinuousAt (fun ε : ℝ => Real.log ((Msq + ε) / (T₂ - T₁))) 0 :=
        ContinuousAt.comp (g := Real.log)
          (Real.continuousAt_log (by simp only [add_zero]; exact (div_pos hMsqpos hlen).ne'))
          (by fun_prop)
      exact ((continuousAt_const.mul hlog).add continuousAt_const).add continuousAt_const
    have h := hcont.tendsto; simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hstep ε hε

/-- **Critical-line log-mean sandwich for arbitrary complex mollifiers.** -/
theorem exists_zetaLine_logMean_complex_sandwich :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ Msq →
        -(C + K * Real.log T₂) ≤
            (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ∧
          (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
            ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
                + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hedge⟩ := exists_zetaLine_littlewood_edge_budget
  obtain ⟨C₂, K₂, hC₂, hK₂, hmoment⟩ := exists_zetaOffLineFirstMoment_le_of_complex_line_meanSquare
  refine ⟨C₁ + C₂, K₁ + K₂, by positivity, by positivity, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq
  have hsub : Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc (by norm_num) le_rfl
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset h20 hT
  have h1 := hedge T₁ T₂ h20 hT (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx)) Z hZ
  have h2 := hmoment b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos
    hG1 hG2 hP1 hP2 hMsq Z hZ
  have hmass0 : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    refine Finset.sum_nonneg fun w hw => ?_
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  exact ⟨by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hmass0], by nlinarith⟩

/-- **Log-integral ceiling on `[T, 2T]` from any complex mollified second moment.** -/
theorem exists_logIntegral_le_of_complex_secondMoment :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ T : ℝ, 22 ≤ T → ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) → ∀ ε : ℝ, 0 ≤ ε →
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T →
      (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
        ε / 2 * T + C + K * (Real.log T + Real.log N) := by
  obtain ⟨C₀, K₀, hC₀, hK₀, hs⟩ := exists_zetaLine_logMean_complex_sandwich
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_riemannZeta_le_leftStrip
  refine ⟨1 + C₀ + K₀ + 2 * Real.log (Cz + 1) + 8, 5 * K₀ + 4, ?_, by positivity, ?_⟩
  · linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ Cz + 1)]
  intro T hT b N hN hb1 hb ε hε hsecond
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  obtain ⟨T₁, ⟨hT₁a, hT₁b⟩, T₂, ⟨hT₂a, hT₂b⟩, hs1, hs2⟩ :=
    exists_admissible_slices (b := b) (N := N) hN hb1 hb
      (A₁ := T) (B₁ := T + 1) (A₂ := 2 * T - 1) (B₂ := 2 * T)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hT12 : T₁ < T₂ := by linarith
  have hcont := continuous_norm_sq_zeta_mul_edPoly b N (c := 1 / 2) (by norm_num)
  have hMsq : (∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ (1 + ε) * T :=
    (intervalIntegral.integral_mono_interval hT₁a.le hT12.le hT₂b.le
      (Filter.Eventually.of_forall fun _ => by positivity)
      (hcont.intervalIntegrable _ _)).trans hsecond
  have hMsq0 : 0 < (1 + ε) * T := by positivity
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hN)
  have hsw := (hs b N hN hb1 hb ((N : ℝ) ^ 5) hMb1 (sum_norm_mul_rpow_four_le hb)
    T₁ T₂ ((1 + ε) * T) (by linarith) hT12 hMsq0
    (fun x hx => (hs1 x hx).1) (fun x hx => (hs2 x hx).1)
    (fun x hx => (hs1 x hx).2) (fun x hx => (hs2 x hx).2) hMsq).2
  have hL0 : 0 < T₂ - T₁ := by linarith
  have hjensen : (T₂ - T₁) / 2 * Real.log ((1 + ε) * T / (T₂ - T₁)) ≤ ε / 2 * T + 1 := by
    have h2 := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hMsq0 hL0)) (by positivity : 0 ≤ (T₂ - T₁) / 2)
    have h3 : (T₂ - T₁) / 2 * ((1 + ε) * T / (T₂ - T₁) - 1) = ((1 + ε) * T - (T₂ - T₁)) / 2 := by
      field_simp
    rw [h3] at h2
    linarith [show (1 + ε) * T = T + ε * T by ring, show ε / 2 * T = ε * T / 2 by ring]
  have hlogT₂ : Real.log T₂ ≤ Real.log T + 1 := by
    have h1 : Real.log T₂ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hT₂b.le
    rw [Real.log_mul two_ne_zero hT0.ne'] at h1
    linarith [Real.log_two_lt_d9]
  have hlogMb : Real.log ((N : ℝ) ^ 5) = 5 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  set Y : ℝ := Real.log (Cz + 1) + 2 * Real.log 3 + 2 * Real.log T with hY
  have hCz1 : 0 ≤ Real.log (Cz + 1) := Real.log_nonneg (by linarith)
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hpoint : ∀ t ∈ Icc T (2 * T),
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Y := by
    intro t ht
    by_cases h0 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ = 0
    · rw [h0, Real.log_zero]; exact hY0
    have hpos : 0 < ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h1 := hCz (1 / 2) t (by norm_num) (by norm_num)
    rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)] at h1
    have h2 : ((1 + t) : ℝ) ^ 2 ≤ (3 * T) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
    have h3 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (Cz + 1) * (3 * T) ^ 2 :=
      h1.trans (mul_le_mul (by linarith) h2 (by positivity) (by linarith))
    refine (Real.log_le_log hpos h3).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) hT0.ne', hY]
    push_cast; ring
  have htail : ∀ a c : ℝ, T ≤ a → a ≤ c → c ≤ 2 * T → c - a ≤ 1 →
      (∫ t in a..c, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ Y := by
    intro a c ha hac hc hlen
    have h1 := intervalIntegral.integral_mono_on hac
      (intervalIntegrable_log_norm_riemannZeta_line a c) intervalIntegrable_const
      fun t ht => hpoint t ⟨ha.trans ht.1, ht.2.trans hc⟩
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_right hlen hY0).trans_eq (one_mul Y))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_norm_riemannZeta_line T T₁)
    (intervalIntegrable_log_norm_riemannZeta_line T₁ T₂)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_norm_riemannZeta_line T T₂)
    (intervalIntegrable_log_norm_riemannZeta_line T₂ (2 * T))
  have ht1 := htail T T₁ le_rfl hT₁a.le (by linarith) (by linarith)
  have ht2 := htail T₂ (2 * T) (by linarith) hT₂b.le le_rfl (by linarith)
  rw [hlogMb] at hsw
  rw [← hsplit2, ← hsplit]
  rw [hY] at ht1 ht2
  have hK1 : K₀ * (Real.log T₂ + 5 * Real.log N) ≤ K₀ * (Real.log T + 1 + 5 * Real.log N) :=
    mul_le_mul_of_nonneg_left (by linarith) hK₀.le
  have hK2 : K₀ * Real.log T ≤ 5 * K₀ * Real.log T :=
    mul_le_mul_of_nonneg_right (by linarith) hlogT
  have hexp : (5 * K₀ + 4) * (Real.log T + Real.log N) =
      5 * K₀ * Real.log T + 5 * K₀ * Real.log N + 4 * Real.log T + 4 * Real.log N := by ring
  have hexp2 : K₀ * (Real.log T + 1 + 5 * Real.log N) =
      K₀ * Real.log T + K₀ + 5 * K₀ * Real.log N := by ring
  rw [hexp]; linarith

/-- Complex-coefficient mollified second moment tending to `1` at length `exp(o(T))`. -/
def ComplexMollifiedSecondMomentLaw : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
    (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧ Real.log N ≤ ε * T ∧
    (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T

/-- Complex-coefficient mollified second moment with excess `K₀ / log T` at length
`exp(T / log T)`. -/
def ComplexSecondMomentRate (K₀ : ℝ) : Prop :=
  ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
    (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧ Real.log N ≤ T / Real.log T ∧
    (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (1 + K₀ / Real.log T) * T

/-- **Complex mollified second moment tending to `1` implies `(L)`.** -/
theorem logMean_tendsto_zero_of_complexMollifiedSecondMomentLaw
    (h : ComplexMollifiedSecondMomentLaw) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) atTop (𝓝 0) := by
  obtain ⟨C, K, hC, hK, hup⟩ := exists_logIntegral_le_of_complex_secondMoment
  obtain ⟨C', K', hC', hK', hlow⟩ := exists_logIntegral_floor
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε : ℝ := η / (4 * (1 / 2 + K)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεK : ε / 2 + K * ε = η / 4 := by rw [hε]; field_simp
  have hlog1 := eventually_log_pow_mul_exp_le 1 (c := 1)
    (ε := η / (8 * (K + K'))) one_pos (by positivity)
  filter_upwards [h ε hε0, hlog1, eventually_ge_atTop (22 : ℝ),
    eventually_ge_atTop (8 * (C + C' + K') / η)] with T hlaw hl hT22 hTC
  obtain ⟨b, N, hN, hb1, hb, hlogN, hmom⟩ := hlaw
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hu := hup T hT22 b N hN hb1 hb ε hε0.le hmom
  have hd := hlow T (by linarith)
  have hlogT' : (K + K') * Real.log T ≤ η / 8 * T := by
    have hTe : Real.exp (-(1 * Real.log T)) = T⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hT0]
    rw [hTe, pow_one, ← div_eq_mul_inv, div_le_iff₀ hT0] at hl
    exact (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ K + K')).trans (by field_simp; rfl)
  have hTC' : C + C' + K' ≤ η / 8 * T := by linarith [(div_le_iff₀ hη).mp hTC]
  have hlog2T : Real.log (2 * T) ≤ Real.log T + 1 := by
    rw [Real.log_mul two_ne_zero hT0.ne']; linarith [Real.log_two_lt_d9]
  have hup2 : (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
      η / 2 * T := by
    have h1 : K * (Real.log T + Real.log N) ≤ K * Real.log T + K * (ε * T) := by
      rw [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogN hK.le)
    have h2 : ε / 2 * T + K * (ε * T) = η / 4 * T := by rw [← hεK]; ring
    have hKK : K * Real.log T + K' * Real.log T = (K + K') * Real.log T := by ring
    have hK'0 : 0 ≤ K' * Real.log T := by positivity
    linarith [show 0 < C' + K' by positivity]
  have hlow2 : -(η / 2 * T) ≤
      ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    have h1 : K' * Real.log (2 * T) ≤ K' * Real.log T + K' :=
      (mul_le_mul_of_nonneg_left hlog2T hK'.le).trans_eq (by ring)
    have hKK : K * Real.log T + K' * Real.log T = (K + K') * Real.log T := by ring
    have hK0 : 0 ≤ K * Real.log T := by positivity
    have hpos_ηT : 0 < η * T := by positivity
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hT0)]
  have h5 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hlow2, hup2⟩) (inv_pos.mpr hT0).le
  have h6 : T⁻¹ * (η / 2 * T) = η / 2 := by field_simp
  linarith

/-- **`100%` critical-scale clustering from complex long mollifiers.** -/
theorem criticalClustering_of_complexMollifiedSecondMomentLaw
    (h : ComplexMollifiedSecondMomentLaw) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
      (V * Real.log V)) atTop (𝓝 0) := by
  have hTFAE := criticalClustering_logMean_mollifier_hecke_tfae
    (c := 1 / 4) (by norm_num) (by norm_num)
  exact (hTFAE.out 0 4).mp (logMean_tendsto_zero_of_complexMollifiedSecondMomentLaw h) κ hκ

/-- **`ComplexSecondMomentRate K₀` implies `LogFreeNearLineZeroDensity` (`D_zero`).** -/
theorem logFreeNearLineZeroDensity_of_complexSecondMomentRate {K₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (h : ComplexSecondMomentRate K₀) :
    LogFreeNearLineZeroDensity := by
  obtain ⟨C, K, hC, hK, hup⟩ := exists_logIntegral_le_of_complex_secondMoment
  obtain ⟨C', K', hC', hK', hbud⟩ := exists_zetaLine_littlewood_edge_budget_all_heights
  set K₁ : ℝ := K₀ / 2 + K + 1 with hK₁
  refine ⟨fun A => K₁ / Real.pi / A, tendsto_const_nhds.div_atTop tendsto_id, fun A hA => ?_⟩
  set D : ℝ := C + C' + K' + K + K' + 1 with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  filter_upwards [h, eventually_log_pow_mul_exp_le 2 (c := 1) (ε := 1 / D) one_pos (by positivity),
    eventually_ge_atTop (22 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with
    V hrate hsm hV22 hℓ
  obtain ⟨b, N, hN, hb1, hb, hlogN, hmom⟩ := hrate
  have hV0 : 0 < V := by linarith
  have hℓ0 : 0 < Real.log V := by linarith
  have hu := hup V hV22 b N hN hb1 hb _ (by positivity) hmom
  have hbudget := (abs_le.mp (hbud V (by linarith))).1
  set M : ℝ := ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => 1 / 2 < z.re),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) with hM
  rw [← hM] at hbudget
  have hsm2 : D * Real.log V ^ 2 ≤ V := by
    have hTe : Real.exp (-(1 * Real.log V)) = V⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hV0]
    rw [hTe, ← div_eq_mul_inv, div_le_iff₀ hV0] at hsm
    exact (mul_le_mul_of_nonneg_left hsm hD0.le).trans (by field_simp; rfl)
  have hVdiv : D * Real.log V ≤ V / Real.log V := by
    rw [le_div_iff₀ hℓ0]
    calc D * Real.log V * Real.log V = D * Real.log V ^ 2 := by ring
      _ ≤ V := hsm2
  have hlog2V : Real.log (2 * V) ≤ Real.log V + 1 := by
    rw [Real.log_mul two_ne_zero hV0.ne']; linarith [Real.log_two_lt_d9]
  have hsum : 2 * Real.pi * M ≤ K₁ * (V / Real.log V) := by
    have h1 : K * (Real.log V + Real.log N) ≤ K * Real.log V + K * (V / Real.log V) := by
      rw [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogN hK.le)
    have h2 : K' * Real.log (2 * V) ≤ K' * Real.log V + K' :=
      (mul_le_mul_of_nonneg_left hlog2V hK'.le).trans_eq (by ring)
    have h3 : K₀ / Real.log V / 2 * V = K₀ / 2 * (V / Real.log V) := by ring
    have h4 : K₁ * (V / Real.log V) =
        K₀ / 2 * (V / Real.log V) + K * (V / Real.log V) + V / Real.log V := by rw [hK₁]; ring
    have h5 : C + C' + K' + (K + K') * Real.log V ≤ D * Real.log V := by
      have h6 : C + C' + K' ≤ (C + C' + K') * Real.log V :=
        le_mul_of_one_le_right (by positivity) hℓ
      rw [hD]; linarith
    linarith
  have hfold := sum_order_filter_abs_le (V₁ := V) (V₂ := 2 * V) (x := A / Real.log V) (by positivity)
  rw [← hM] at hfold
  refine hfold.trans ?_
  have hval : 2 / (A / Real.log V) * M = Real.log V / (Real.pi * A) * (2 * Real.pi * M) := by
    field_simp
  rw [hval]
  calc Real.log V / (Real.pi * A) * (2 * Real.pi * M)
      ≤ Real.log V / (Real.pi * A) * (K₁ * (V / Real.log V)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K₁ / Real.pi / A * V := by field_simp

/-- **`ComplexSecondMomentRate K₀` implies `LogFreeNearLineWindowOccupancy` (`D_win`).** -/
theorem logFreeNearLineWindowOccupancy_of_complexSecondMomentRate {K₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (h : ComplexSecondMomentRate K₀) :
    LogFreeNearLineWindowOccupancy :=
  (logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean
    (logFreeNearLineZeroDensity_of_complexSecondMomentRate hK₀ h)).1


/-! ## §2. Uniform complex necessary-length law up to `exp(T^{1/60})` and the `exp(c log²T)` rate threshold -/

private theorem two_mul_cosh_log_two' : 2 * Real.cosh (Real.log 2) = 5 / 2 := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log two_pos]
  norm_num

private theorem exp_le_three' {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 3 := by
  have h1 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx
  linarith [Real.exp_one_lt_d9]

/-- Right-of-line window floor taking `a² / w² ≤ ε / 4` directly rather than `1 / (4 ε) ≤ w²`,
removing the polynomial-length bottleneck when `ε` decays stretched-exponentially. -/
theorem le_integral_window_right_of_sq_le {t₀ w a K ε : ℝ} {b : ℕ → ℂ} {N : ℕ}
    (ht₀ : 0 < t₀) (hw : 0 < w) (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hK : 5 ≤ K)
    (hN : 1 ≤ N) (hb1 : b 1 = 1) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2000)
    (he : Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
      (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) ≤ ε / 8)
    (ha_sq : a ^ 2 / w ^ 2 ≤ ε / 4) :
    (1 - ε) * (w * √Real.pi) ≤ ∫ t, ‖lineFun (mollifiedWindow t₀ w b N) a t‖ ^ 2 := by
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
      (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  rw [← hedef] at he
  have hfloor := right_floor (a := a) (K := K) ht₀ hw ha0.le (by linarith) hK hN hb1 hb
    (by rw [← hedef]; linarith)
  rw [← hedef] at hfloor
  have hz0 : 0 ≤ a ^ 2 / w ^ 2 := by positivity
  have hfac : 1 - ε ≤ (1 - e) ^ 2 * Real.exp (-(a ^ 2 / w ^ 2)) := by
    have h3 : 1 - a ^ 2 / w ^ 2 ≤ Real.exp (-(a ^ 2 / w ^ 2)) := by
      linarith [Real.add_one_le_exp (-(a ^ 2 / w ^ 2))]
    have h4 : 1 - 2 * e ≤ (1 - e) ^ 2 := by
      have h9 : (1 - e) ^ 2 = 1 - 2 * e + e ^ 2 := by ring
      rw [h9]; linarith [sq_nonneg e]
    have h5 : 0 ≤ 1 - 2 * e := by linarith
    have h6 : 0 ≤ 1 - a ^ 2 / w ^ 2 := by linarith
    have h7 : 0 ≤ e * (a ^ 2 / w ^ 2) := mul_nonneg he0 hz0
    have h8 : (1 - 2 * e) * (1 - a ^ 2 / w ^ 2) =
        1 - 2 * e - a ^ 2 / w ^ 2 + 2 * (e * (a ^ 2 / w ^ 2)) := by ring
    calc 1 - ε ≤ (1 - 2 * e) * (1 - a ^ 2 / w ^ 2) := by rw [h8]; linarith
      _ ≤ _ := mul_le_mul h4 h3 h6 (sq_nonneg _)
  refine le_trans ?_ hfloor
  calc (1 - ε) * (w * √Real.pi) ≤ ((1 - e) ^ 2 * Real.exp (-(a ^ 2 / w ^ 2))) * (w * √Real.pi) :=
        mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = _ := by ring

private theorem uniform_remainder_right_le {w c L a ℓ : ℝ} (hw4 : 4 ≤ w) (hc2 : c ^ 2 = 2 * Real.pi)
    (ha1 : a ≤ 1 / 4) (hℓ0 : 0 < ℓ) (hexpLa : Real.exp (L * a) ≤ 2) :
    (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 * Real.exp (L * a) *
        Real.exp (-(2 * (ℓ / 100) * (3 / 2 - a))) / (2 * Real.pi * (3 / 2 - a)) ≤
      288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) := by
  have hπ := Real.pi_pos
  have hw0 : 0 < w := by linarith
  have hw16 : (16 : ℝ) ≤ w ^ 2 := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ w ^ 2 := pow_le_pow_left₀ (by norm_num) hw4 2
  have hE₁ : Real.exp (9 / 4 / (2 * w ^ 2)) ≤ 3 :=
    exp_le_three' ((div_le_one (by positivity)).mpr (by linarith))
  have hd : 2 * Real.pi ≤ 2 * Real.pi * (3 / 2 - a) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hE2 : Real.exp (-(2 * (ℓ / 100) * (3 / 2 - a))) ≤ Real.exp (-(1 / 50 * ℓ)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : 2 * (ℓ / 100) * 1 ≤ 2 * (ℓ / 100) * (3 / 2 - a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hsq : (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 ≤ 144 * w ^ 2 * (2 * Real.pi) := by
    have h3 : (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 =
        16 * Real.exp (9 / 4 / (2 * w ^ 2)) ^ 2 * (w ^ 2 * c ^ 2) := by ring
    rw [h3, hc2]
    have h4 : Real.exp (9 / 4 / (2 * w ^ 2)) ^ 2 ≤ 3 ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hE₁ 2
    calc 16 * Real.exp (9 / 4 / (2 * w ^ 2)) ^ 2 * (w ^ 2 * (2 * Real.pi))
        ≤ 16 * 3 ^ 2 * (w ^ 2 * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) (by positivity)
      _ = _ := by ring
  have hd0 : 0 < 2 * Real.pi * (3 / 2 - a) := mul_pos (by positivity) (by linarith)
  rw [div_le_iff₀ hd0]
  calc (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * c)) ^ 2 * Real.exp (L * a) *
        Real.exp (-(2 * (ℓ / 100) * (3 / 2 - a)))
      ≤ (144 * w ^ 2 * (2 * Real.pi)) * 2 * Real.exp (-(1 / 50 * ℓ)) :=
        mul_le_mul (mul_le_mul hsq hexpLa (Real.exp_pos _).le (by positivity)) hE2
          (Real.exp_pos _).le (by positivity)
    _ = 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) * (2 * Real.pi) := by ring
    _ ≤ 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) * (2 * Real.pi * (3 / 2 - a)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)

private theorem uniform_remainder_left_le {A θ T ℓ w c L a t₀ : ℝ} {N : ℕ}
    (hT0 : 0 < T) (hT1 : 1 ≤ T) (hℓdef : ℓ = Real.log T) (hw4 : 4 ≤ w)
    (hc : c = √(2 * Real.pi)) (ha1 : a ≤ 1 / 4) (ht1 : T ≤ t₀) (ht2 : t₀ ≤ 2 * T)
    (hN : (N : ℝ) ≤ T ^ θ) (hL : L = (2 + 3 / 2 * θ + 1 / 100) * ℓ) (hLa0 : 0 ≤ L * a)
    (hLBa : (L + ℓ / 100) * a ≤ Real.log 2) :
    (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
        (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c))) ^ 2 * Real.exp (-(L * a)) *
        Real.exp (-(2 * (L + ℓ / 100) * (1 - a))) / (2 * Real.pi * (1 - a)) ≤
      (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) := by
  have hw0 : 0 < w := by linarith
  have hw16 : (16 : ℝ) ≤ w ^ 2 := by
    calc (16 : ℝ) = 4 ^ 2 := by norm_num
      _ ≤ w ^ 2 := pow_le_pow_left₀ (by norm_num) hw4 2
  have hsqrtπ2 : √Real.pi ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [Real.pi_le_four]⟩
  have hE₂ : Real.exp (1 / (2 * w ^ 2)) ≤ 3 :=
    exp_le_three' ((div_le_one (by positivity)).mpr (by linarith))
  have ht0 : 0 ≤ t₀ := by linarith
  have ht3 : (1 + |t₀|) ^ 2 ≤ 9 * T ^ 2 := by
    rw [abs_of_nonneg ht0]
    calc (1 + t₀) ^ 2 ≤ (3 * T) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = 9 * T ^ 2 := by ring
  have hw3 : 1 + 2 * w ^ 2 ≤ 3 * w ^ 2 := by linarith
  have hsq2 : √2 * w * c ≤ 4 * w := by
    have h3 : √(2 : ℝ) * c = 2 * √Real.pi := by
      rw [hc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc √2 * w * c = w * (√(2 : ℝ) * c) := by ring
      _ = w * (2 * √Real.pi) := by rw [h3]
      _ ≤ w * (2 * 2) := mul_le_mul_of_nonneg_left (by linarith) hw0.le
      _ = 4 * w := by ring
  have hY : 4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c) ≤ 432 * T ^ 2 * w ^ 3 := by
    calc 4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)
        ≤ 4 * (9 * T ^ 2) * (3 * w ^ 2) * (4 * w) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ht3 (by norm_num)) hw3
            (by positivity) (by positivity)) hsq2 (by positivity) (by positivity)
      _ = 432 * T ^ 2 * w ^ 3 := by ring
  have hN3 : ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ Real.exp (3 * θ * ℓ) := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h3 : ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (N : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, ← Real.rpow_natCast]; norm_num
    rw [h3]
    have h4 : (T ^ θ) ^ (3 : ℕ) = Real.exp (3 * θ * ℓ) := by
      rw [Real.rpow_def_of_pos hT0, ← Real.exp_nat_mul, ← hℓdef]
      congr 1; push_cast; ring
    rw [← h4]
    exact pow_le_pow_left₀ hN0 hN 3
  have hX : (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
      (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c))) ^ 2 ≤
      A ^ 2 * 9 * 432 ^ 2 * Real.exp (3 * θ * ℓ) * T ^ 4 * w ^ 6 := by
    have h3 : (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
        (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c))) ^ 2 =
        A ^ 2 * ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 * Real.exp (1 / (2 * w ^ 2)) ^ 2 *
          (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)) ^ 2 := by ring
    rw [h3]
    have h4 : Real.exp (1 / (2 * w ^ 2)) ^ 2 ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hE₂ 2
    have h5 : (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)) ^ 2 ≤ (432 * T ^ 2 * w ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hY 2
    calc A ^ 2 * ((N : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 * Real.exp (1 / (2 * w ^ 2)) ^ 2 *
          (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * c)) ^ 2
        ≤ A ^ 2 * Real.exp (3 * θ * ℓ) * 3 ^ 2 * (432 * T ^ 2 * w ^ 3) ^ 2 :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hN3 (by positivity)) h4
            (by positivity) (by positivity)) h5 (by positivity) (by positivity)
      _ = _ := by ring
  have hTexp : T = Real.exp ℓ := by rw [hℓdef, Real.exp_log hT0]
  have hd : (1 : ℝ) ≤ 2 * Real.pi * (1 - a) := by
    have h3 : 2 * 3 * (3 / 4 : ℝ) ≤ 2 * Real.pi * (1 - a) :=
      mul_le_mul (by linarith [Real.pi_gt_three]) (by linarith) (by norm_num) (by positivity)
    linarith
  have hE3 : Real.exp (-(L * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE4 : Real.exp (-(2 * (L + ℓ / 100) * (1 - a))) ≤
      4 * Real.exp (-(2 * (L + ℓ / 100))) := by
    have h3 : -(2 * (L + ℓ / 100) * (1 - a)) = 2 * ((L + ℓ / 100) * a) + -(2 * (L + ℓ / 100)) := by ring
    rw [h3, Real.exp_add]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have h4 : 2 * ((L + ℓ / 100) * a) ≤ Real.log 4 := by
      have h5 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h5]; linarith
    have h6 := Real.exp_le_exp.mpr h4
    rwa [Real.exp_log (by norm_num)] at h6
  have hexpmain : Real.exp (3 * θ * ℓ) * T ^ 4 * Real.exp (-(2 * (L + ℓ / 100))) =
      Real.exp (-(1 / 25 * ℓ)) := by
    rw [hTexp, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, hL]
    congr 1; push_cast; ring
  rw [div_le_iff₀ (by linarith)]
  calc _ ≤ (A ^ 2 * 9 * 432 ^ 2 * Real.exp (3 * θ * ℓ) * T ^ 4 * w ^ 6) * 1 *
          (4 * Real.exp (-(2 * (L + ℓ / 100)))) :=
        mul_le_mul (mul_le_mul hX hE3 (Real.exp_pos _).le (by positivity)) hE4
          (Real.exp_pos _).le (by positivity)
    _ = (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 *
          (Real.exp (3 * θ * ℓ) * T ^ 4 * Real.exp (-(2 * (L + ℓ / 100)))) := by ring
    _ = (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) * 1 := by
        rw [hexpmain]; ring
    _ ≤ (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) *
          (2 * Real.pi * (1 - a)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)

private theorem length_combine' {x y z ε T D δ I₀ Il J : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2000) (hT0 : 0 < T) (hD0 : 0 < D)
    (hδ1 : (1 - ε) * T ≤ δ) (hδ2 : δ ≤ T) (hJ : I₀ ≤ J)
    (hI : (1 - ε) ^ 2 * z * T ≤ Il)
    (h : x * ((1 - ε) * D) * δ + y * ((1 - ε) * D) * Il ≤ 5 / 2 * D * I₀ + ε / 2 * D * δ) :
    (1 - ε) ^ 2 * x * T + y * ((1 - ε) ^ 3 * z * T) ≤ 5 / 2 * J + 2 * ε * T := by
  have hε' : 0 ≤ 1 - ε := by linarith
  have hdiv : x * (1 - ε) * δ + y * (1 - ε) * Il ≤ 5 / 2 * I₀ + ε / 2 * δ := by
    refine le_of_mul_le_mul_right ?_ hD0
    calc (x * (1 - ε) * δ + y * (1 - ε) * Il) * D
        = x * ((1 - ε) * D) * δ + y * ((1 - ε) * D) * Il := by ring
      _ ≤ 5 / 2 * D * I₀ + ε / 2 * D * δ := h
      _ = _ := by ring
  have h3 : (1 - ε) ^ 2 * x * T ≤ x * (1 - ε) * δ := by
    have h4 := mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hx0 hε')
    calc (1 - ε) ^ 2 * x * T = x * (1 - ε) * ((1 - ε) * T) := by ring
      _ ≤ _ := h4
  have h5 : y * ((1 - ε) ^ 3 * z * T) ≤ y * (1 - ε) * Il := by
    have h6 := mul_le_mul_of_nonneg_left hI (mul_nonneg hy0 hε')
    calc y * ((1 - ε) ^ 3 * z * T) = y * (1 - ε) * ((1 - ε) ^ 2 * z * T) := by ring
      _ ≤ _ := h6
  have h7 : ε / 2 * δ ≤ ε / 2 * T := mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have h8 : 0 ≤ ε * T := by positivity
  have h9 := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 5 / 2)
  linarith

private theorem length_constant_nonneg {θ q p : ℝ} (hθ : 0 ≤ θ) (hq : q = 2 + 3 / 2 * θ + 3 / 100)
    (hp0 : 0 < p) (hpq : p * q = 2) : 1 / (8 + 6 * θ) ≤ 129 / 1000 * p := by
  have h8 : 0 < 8 + 6 * θ := by positivity
  rw [div_le_iff₀ h8]
  have h1 : q ≤ 258 / 1000 * (8 + 6 * θ) := by rw [hq]; linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hp0.le
  rw [hpq] at h2
  linarith

/-- **Uniform stretched-exponential complex necessary-length law up to `exp(T^{1/60})`.**
Eventually as `T → ∞`, simultaneously for every `1 ≤ N` with `Real.log (N : ℝ) ≤ T ^ (1 / 60 : ℝ)`
and every complex Dirichlet polynomial `M(s) = ∑_{n=1}^N b_n n^{-s}` with `b 1 = 1` and `‖b n‖ ≤ 1`,
`∫_T^{2T} ‖ζ(1/2 + it) M(1/2 + it)‖² dt ≥ (1 + log T / (8 log T + 6 log N)) T`. -/
theorem eventually_uniform_complex_necessary_length :
    ∀ᶠ T : ℝ in atTop, ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N →
      Real.log (N : ℝ) ≤ T ^ (1 / 60 : ℝ) →
      b 1 = 1 → (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (1 + Real.log T / (8 * Real.log T + 6 * Real.log (N : ℝ))) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨A, -, hwin⟩ := exists_window_inequality
  obtain ⟨Cc, hCc, hcenter⟩ := exists_center_tail
  obtain ⟨Cl, Kl, hCl, hKl, hleft_floor⟩ := exists_left_floor_complex
  set B₁ : ℝ := 4 * (A ^ 2 * 9 * 432 ^ 2) + 1 with hB₁_def
  have hB₁_pos : 0 < B₁ := by rw [hB₁_def]; positivity
  set C_cen : ℝ := Cc * 8100 * (2 * Real.exp 1) * 2 + 1 with hC_cen_def
  have hC_cen_pos : 0 < C_cen := by rw [hC_cen_def]; positivity
  set C_lf : ℝ := Cl + 7 * Kl + 1 with hC_lf_def
  have hC_lf_pos : 0 < C_lf := by rw [hC_lf_def]; positivity
  filter_upwards [
    eventually_ge_atTop (1000 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 10,
    eventually_zero_count_increment,
    eventually_log_pow_mul_exp_le 2 (c := 1 / 300) (ε := 1 / (64000 * 288))
      (by norm_num) (by positivity),
    eventually_log_pow_mul_exp_le 10 (c := 7 / 300) (ε := 1 / (64000 * B₁))
      (by norm_num) (by positivity),
    eventually_log_pow_mul_exp_le 8 (c := 239 / 60) (ε := 1 / (32000 * C_cen))
      (by norm_num) (by positivity),
    eventually_log_pow_mul_exp_le 5 (c := 1) (ε := 1 / 8)
      (by norm_num) (by norm_num),
    eventually_log_pow_mul_exp_le 0 (c := 29 / 60) (ε := 1 / (66 * 32000))
      (by norm_num) (by norm_num),
    eventually_log_pow_mul_exp_le 3 (c := 29 / 30) (ε := 1 / 1024000000)
      (by norm_num) (by norm_num),
    eventually_log_pow_mul_exp_le 0 (c := 59 / 60) (ε := 1 / 128000000)
      (by norm_num) (by norm_num),
    eventually_log_pow_mul_exp_le 0 (c := 959 / 60) (ε := 1 / 8000)
      (by norm_num) (by norm_num),
    eventually_log_pow_mul_exp_le 1 (c := 29 / 30) (ε := (6 / 8000) / C_lf)
      (by norm_num) (by positivity)
  ] with T hT1000 hℓ10 hcnt hr₁ hr₂ hcen_sm hf_gauss hf_err hR_sm hT_big hmass_sm hlf_sm
    b N hN hlogN hb1 hb
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  set ℓ : ℝ := Real.log T with hℓ_def
  have hℓ0 : 0 < ℓ := by linarith
  have hT_exp : Real.exp ℓ = T := Real.exp_log hT0
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set Θ : ℝ := Real.log (N : ℝ) with hΘ_def
  have hΘ0 : 0 ≤ Θ := Real.log_nonneg hN_ge1
  have hT60_eq : T ^ (1 / 60 : ℝ) = Real.exp (1 / 60 * ℓ) := by
    rw [Real.rpow_def_of_pos hT0, ← hℓ_def]; ring_nf
  have hΘ_le : Θ ≤ Real.exp (1 / 60 * ℓ) := hlogN.trans_eq hT60_eq
  set θ : ℝ := Θ / ℓ with hθ_def
  have hθ0 : 0 ≤ θ := div_nonneg hΘ0 hℓ0.le
  have hN_eq_Tθ : (N : ℝ) = T ^ θ := by
    rw [Real.rpow_def_of_pos hT0, ← hℓ_def, hθ_def, mul_div_cancel₀ _ hℓ0.ne', hΘ_def,
      Real.exp_log hN_pos]
  have hNT : (N : ℝ) ≤ T ^ θ := hN_eq_Tθ.le
  set q : ℝ := 2 + 3 / 2 * θ + 3 / 100 with hq_def
  have hq0 : 0 < q := by rw [hq_def]; positivity
  have hq2 : 2 ≤ q := by rw [hq_def]; linarith
  have hexp60_ge1 : 1 ≤ Real.exp (1 / 60 * ℓ) := Real.one_le_exp (by positivity)
  have hθ_le_exp : θ ≤ (1 / 10) * Real.exp (1 / 60 * ℓ) := by
    rw [hθ_def, div_le_iff₀ hℓ0]
    have h1 : Θ ≤ (1 / 10) * Real.exp (1 / 60 * ℓ) * 10 := by linarith
    calc Θ ≤ (1 / 10) * Real.exp (1 / 60 * ℓ) * 10 := h1
      _ ≤ (1 / 10) * Real.exp (1 / 60 * ℓ) * ℓ :=
          mul_le_mul_of_nonneg_left hℓ10 (by positivity)
  have hq_le : q ≤ 4 * Real.exp (1 / 60 * ℓ) := by
    rw [hq_def]; linarith
  set p : ℝ := 2 / q with hp_def
  have hp0 : 0 < p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := (div_le_one hq0).mpr hq2
  have hpq : p * q = 2 := by rw [hp_def]; exact div_mul_cancel₀ _ hq0.ne'
  have hp_ge : (1 / 2) * Real.exp (-(1 / 60 * ℓ)) ≤ p := by
    rw [hp_def, le_div_iff₀ hq0]
    calc (1 / 2) * Real.exp (-(1 / 60 * ℓ)) * q
        ≤ (1 / 2) * Real.exp (-(1 / 60 * ℓ)) * (4 * Real.exp (1 / 60 * ℓ)) :=
          mul_le_mul_of_nonneg_left hq_le (by positivity)
      _ = 2 * (Real.exp (-(1 / 60 * ℓ)) * Real.exp (1 / 60 * ℓ)) := by ring
      _ = 2 := by rw [← Real.exp_add]; simp
  set ε : ℝ := p / 2000 with hε_def
  have hε0 : 0 < ε := by rw [hε_def]; positivity
  have hε1 : ε ≤ 1 / 2000 := by rw [hε_def]; linarith
  have hε_ge : (1 / 4000) * Real.exp (-(1 / 60 * ℓ)) ≤ ε := by rw [hε_def]; linarith
  set w : ℝ := ℓ ^ 2 with hw_def
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw4 : 4 ≤ w := by rw [hw_def]; nlinarith
  have hw100 : 100 ≤ w := by rw [hw_def]; nlinarith
  set R : ℝ := 4 * w * Real.sqrt (Θ + 2 * ℓ) with hR_def
  have hR0 : 0 ≤ R := by rw [hR_def]; positivity
  set L : ℝ := (2 + 3 / 2 * θ + 1 / 100) * ℓ with hL_def
  set B : ℝ := ℓ / 100 with hB_def
  have hL0 : 0 ≤ L := by rw [hL_def]; positivity
  have hB0 : 0 ≤ B := by rw [hB_def]; positivity
  set a : ℝ := Real.log 2 / (q * ℓ) with ha_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog2_gt_half : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haq : a * (q * ℓ) = Real.log 2 := by
    rw [ha_def]; exact div_mul_cancel₀ _ (mul_pos hq0 hℓ0).ne'
  have ha4 : a ≤ 1 / 4 := by
    rw [ha_def, div_le_iff₀ (mul_pos hq0 hℓ0)]
    have h4 : (2 : ℝ) * 10 ≤ q * ℓ := mul_le_mul hq2 hℓ10 (by norm_num) hq0.le
    linarith
  have hLa : L * a = (1 - p / 100) * Real.log 2 := by
    have h3 : L = (q - 2 / 100) * ℓ := by rw [hL_def, hq_def]; ring
    rw [h3, ← haq]
    linear_combination (a * ℓ / 100) * hpq
  have hLa0 : 0 ≤ L * a := mul_nonneg hL0 ha0.le
  have hLBa_le : (L + B) * a ≤ Real.log 2 := by
    have h1 : (L + B) * a ≤ a * (q * ℓ) := by
      have h2 : L + B ≤ q * ℓ := by rw [hL_def, hB_def, hq_def]; linarith
      calc (L + B) * a = a * (L + B) := mul_comm _ _
        _ ≤ a * (q * ℓ) := mul_le_mul_of_nonneg_left h2 ha0.le
    exact h1.trans_eq haq
  have hexpLa_le2 : Real.exp (L * a) ≤ 2 := by
    have h1 : L * a ≤ Real.log 2 := by
      have h2 : 0 ≤ B * a := mul_nonneg hB0 ha0.le
      linarith
    exact (Real.exp_le_exp.mpr h1).trans_eq (Real.exp_log two_pos)
  -- Margin `R` and `ε * T` bounds
  have hεT_ge32000 : 32000 ≤ ε * T := by
    have h1 : 128000000 ≤ Real.exp (59 / 60 * ℓ) := by
      rw [pow_zero, one_mul, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)] at hT_big
      simpa using hT_big
    calc (32000 : ℝ) = (1 / 4000) * 128000000 := by norm_num
      _ ≤ (1 / 4000) * Real.exp (59 / 60 * ℓ) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (1 / 4000) * Real.exp (-(1 / 60 * ℓ)) * Real.exp ℓ := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ ε * T := by rw [← hT_exp]; exact mul_le_mul_of_nonneg_right hε_ge (Real.exp_pos ℓ).le
  have hRT : R ≤ ε / 16000 * T := by
    have hsqrt_le : Real.sqrt (Θ + 2 * ℓ) ≤ Θ + 2 * ℓ + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    have hsum_le : Θ + 2 * ℓ + 1 ≤ 4 * ℓ * Real.exp (1 / 60 * ℓ) := by
      have h2 : 2 * ℓ ≤ 2 * ℓ * Real.exp (1 / 60 * ℓ) :=
        le_mul_of_one_le_right (by positivity) hexp60_ge1
      have h3 : 1 + Real.exp (1 / 60 * ℓ) ≤ 2 * ℓ * Real.exp (1 / 60 * ℓ) := by nlinarith
      linarith
    have hR_up : R ≤ 16 * ℓ ^ 3 * Real.exp (1 / 60 * ℓ) := by
      calc R ≤ 4 * w * (4 * ℓ * Real.exp (1 / 60 * ℓ)) :=
            mul_le_mul_of_nonneg_left (hsqrt_le.trans hsum_le) (by positivity)
        _ = 16 * ℓ ^ 3 * Real.exp (1 / 60 * ℓ) := by rw [hw_def]; ring
    have hsm' : 16 * ℓ ^ 3 * Real.exp (1 / 60 * ℓ) ≤
        (1 / 64000000) * Real.exp (59 / 60 * ℓ) := by
      have hmul := mul_le_mul_of_nonneg_right hR_sm (Real.exp_pos (59 / 60 * ℓ)).le
      have hexp_eq : Real.exp (-(29 / 30 * ℓ)) * Real.exp (59 / 60 * ℓ) =
          Real.exp (1 / 60 * ℓ) := by rw [← Real.exp_add]; congr 1; ring
      have hlhs : ℓ ^ 3 * Real.exp (-(29 / 30 * ℓ)) * Real.exp (59 / 60 * ℓ) =
          ℓ ^ 3 * Real.exp (1 / 60 * ℓ) := by rw [mul_assoc, hexp_eq]
      rw [hlhs] at hmul
      linarith
    calc R ≤ 16 * ℓ ^ 3 * Real.exp (1 / 60 * ℓ) := hR_up
      _ ≤ (1 / 64000000) * Real.exp (59 / 60 * ℓ) := hsm'
      _ = ((1 / 4000) * Real.exp (-(1 / 60 * ℓ))) / 16000 * Real.exp ℓ := by
          have hexp2 : Real.exp (59 / 60 * ℓ) = Real.exp (-(1 / 60 * ℓ)) * Real.exp ℓ := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp2]; ring
      _ ≤ ε / 16000 * T := by
          rw [← hT_exp]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hε_ge (by norm_num))
            (Real.exp_pos ℓ).le
  have h2T : 2 ≤ ε / 16000 * T := by linarith
  have hεT2 : ε * T ≤ T / 2000 := by
    have := mul_le_mul_of_nonneg_right hε1 hT0.le; linarith
  have hsmallR : 4 * R + 2 ≤ ε * T / 1000 := by linarith
  have hAB : T + R ≤ 2 * T - R := by linarith
  obtain ⟨T₁, ⟨hT₁a, hT₁b⟩, T₂, ⟨hT₂a, hT₂b⟩, hs1, hs2⟩ :=
    exists_admissible_slices (b := b) (N := N) hN hb1 hb
      (A₁ := T + 2 * R) (B₁ := T + 2 * R + 1) (A₂ := 2 * T - 2 * R - 1) (B₂ := 2 * T - 2 * R)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hT12 : T₁ ≤ T₂ := by linarith
  have hT12_lt : T₁ < T₂ := by linarith
  -- Pointwise height inequality for every `t₀ ∈ [T + R, 2T - R]`
  have hheight : ∀ t₀ ∈ Icc (T + R) (2 * T - R),
      Real.exp (L * a) * ((1 - ε) * (w * √Real.pi)) +
        Real.exp (-(L * a)) * (∫ t in T₁..T₂, linePower b N (-a) t * gaussKernel w t t₀) ≤
      5 / 2 * (∫ t in T..(2 * T), linePower b N 0 t * gaussKernel w t t₀) +
        ε / 2 * (w * √Real.pi) := by
    intro t₀ ht₀
    have ht₁ : T ≤ t₀ := by linarith [ht₀.1]
    have ht₂ : t₀ ≤ 2 * T := by linarith [ht₀.2]
    have ht₀0 : 0 < t₀ := by linarith
    have hsqrtπ_ge1 : 1 ≤ √Real.pi :=
      Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_three])
    -- Spectral remainder bound (`≤ (ε / 8) * (w * √π)`)
    have hc_sq : (√(2 * Real.pi)) ^ 2 = 2 * Real.pi :=
      Real.sq_sqrt (by positivity)
    have hrem_r := uniform_remainder_right_le hw4 hc_sq ha4 hℓ0 hexpLa_le2
    have hrem_l := uniform_remainder_left_le (A := A) (θ := θ) hT0 hT1 rfl hw4 rfl ha4
      ht₁ ht₂ hNT hL_def hLa0 (by rw [← hB_def]; exact hLBa_le)
    have hr₁_bound : 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) ≤ ε / 16 * (w * √Real.pi) := by
      have hmul := mul_le_mul_of_nonneg_right hr₁ (Real.exp_pos (-(1 / 60 * ℓ))).le
      have hexp_eq : Real.exp (-(1 / 300 * ℓ)) * Real.exp (-(1 / 60 * ℓ)) =
          Real.exp (-(1 / 50 * ℓ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [mul_assoc, hexp_eq] at hmul
      have h1 : 288 * ℓ ^ 2 * Real.exp (-(1 / 50 * ℓ)) ≤ ε / 16 := by
        calc 288 * ℓ ^ 2 * Real.exp (-(1 / 50 * ℓ))
            = 288 * (ℓ ^ 2 * Real.exp (-(1 / 50 * ℓ))) := by ring
          _ ≤ 288 * (1 / (64000 * 288) * Real.exp (-(1 / 60 * ℓ))) :=
              mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = ((1 / 4000) * Real.exp (-(1 / 60 * ℓ))) / 16 := by ring
          _ ≤ ε / 16 := div_le_div_of_nonneg_right hε_ge (by norm_num)
      calc 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ))
          = (288 * ℓ ^ 2 * Real.exp (-(1 / 50 * ℓ))) * (w * 1) := by rw [hw_def]; ring
        _ ≤ (ε / 16) * (w * √Real.pi) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left hsqrtπ_ge1 hw0.le)
              (by positivity) (by positivity)
    have hr₂_bound : (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) ≤
        ε / 16 * (w * √Real.pi) := by
      have hmul := mul_le_mul_of_nonneg_right hr₂ (Real.exp_pos (-(1 / 60 * ℓ))).le
      have hexp_eq : Real.exp (-(7 / 300 * ℓ)) * Real.exp (-(1 / 60 * ℓ)) =
          Real.exp (-(1 / 25 * ℓ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [mul_assoc, hexp_eq] at hmul
      have h1 : B₁ * ℓ ^ 10 * Real.exp (-(1 / 25 * ℓ)) ≤ ε / 16 := by
        calc B₁ * ℓ ^ 10 * Real.exp (-(1 / 25 * ℓ))
            = B₁ * (ℓ ^ 10 * Real.exp (-(1 / 25 * ℓ))) := by ring
          _ ≤ B₁ * (1 / (64000 * B₁) * Real.exp (-(1 / 60 * ℓ))) :=
              mul_le_mul_of_nonneg_left hmul hB₁_pos.le
          _ = ((1 / 4000) * Real.exp (-(1 / 60 * ℓ))) / 16 := by field_simp; ring
          _ ≤ ε / 16 := div_le_div_of_nonneg_right hε_ge (by norm_num)
      calc (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 * Real.exp (-(1 / 25 * ℓ))
          ≤ B₁ * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by rw [hB₁_def]; linarith) (by positivity))
              (by positivity)
        _ = (B₁ * ℓ ^ 10 * Real.exp (-(1 / 25 * ℓ))) * (w * 1) := by rw [hw_def]; ring
        _ ≤ (ε / 16) * (w * √Real.pi) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left hsqrtπ_ge1 hw0.le)
              (by positivity) (by positivity)
    -- Right floor at `K := 5 + ℓ`
    set K : ℝ := 5 + ℓ with hK_def
    have hK5 : 5 ≤ K := by rw [hK_def]; linarith
    have ha_sq : a ^ 2 / w ^ 2 ≤ ε / 4 := by
      have ha_eq : a = (1000 * Real.log 2 / ℓ) * ε := by
        rw [ha_def, hε_def, hp_def]; field_simp; ring
      have ha_le : a ≤ 100 * ε := by
        rw [ha_eq]
        refine mul_le_mul_of_nonneg_right ?_ hε0.le
        rw [div_le_iff₀ hℓ0]; linarith
      have haw_le : a / w ≤ ε := by
        rw [div_le_iff₀ hw0]; nlinarith
      calc a ^ 2 / w ^ 2 = (a / w) ^ 2 := (div_pow a w 2).symm
        _ ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) haw_le 2
        _ ≤ ε / 4 := by nlinarith
    have hright_err : Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
        (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2)))) ≤
        ε / 8 := by
      have hexpK_le2 : Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) ≤ 2 := by
        have h1 : (K - 1 / 2) ^ 2 / w ^ 2 ≤ Real.log 2 := by
          rw [div_le_iff₀ (by positivity), hK_def, hw_def]
          have h2 : (5 + ℓ - 1 / 2) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
          have h3 : 4 * ℓ ^ 2 ≤ Real.log 2 * (ℓ ^ 2) ^ 2 := by
            have h4 : (4 : ℝ) ≤ Real.log 2 * ℓ ^ 2 := by nlinarith
            nlinarith
          linarith
        exact (Real.exp_le_exp.mpr h1).trans_eq (Real.exp_log two_pos)
      have hterm1 : 19 * Real.exp (-(Real.log 2 * K)) ≤ 19 * Real.exp (-(1 / 2 * ℓ)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        rw [hK_def]; nlinarith
      have hterm2 : 8 / t₀ ≤ 8 * Real.exp (-(1 / 2 * ℓ)) := by
        calc 8 / t₀ ≤ 8 / T := div_le_div_of_nonneg_left (by norm_num) hT0 ht₁
          _ = 8 * Real.exp (-ℓ) := by rw [div_eq_mul_inv, ← hT_exp, Real.exp_neg]
          _ ≤ 8 * Real.exp (-(1 / 2 * ℓ)) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      have hterm3 : 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))) ≤ 6 * Real.exp (-(1 / 2 * ℓ)) := by
        have hT_w : 8 * w ^ 2 * ℓ ≤ T := by
          have h1 := hf_gauss
          rw [one_mul, Real.exp_neg, hT_exp, ← div_eq_mul_inv, div_le_iff₀ hT0] at h1
          have h2 : w ^ 2 * ℓ = ℓ ^ 5 := by rw [hw_def]; ring
          rw [h2]; linarith
        have ht₀_sq : T ≤ t₀ ^ 2 := by nlinarith
        have hdiv : 1 / 2 * ℓ ≤ t₀ ^ 2 / (8 * w ^ 2) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hdiv)) (by norm_num)
      have hmul := mul_le_mul_of_nonneg_right hf_err (Real.exp_pos (-(1 / 60 * ℓ))).le
      have hexp_eq : Real.exp (-(29 / 60 * ℓ)) * Real.exp (-(1 / 60 * ℓ)) =
          Real.exp (-(1 / 2 * ℓ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [pow_zero, one_mul, hexp_eq] at hmul
      calc Real.exp ((K - 1 / 2) ^ 2 / w ^ 2) *
            (19 * Real.exp (-(Real.log 2 * K)) + 8 / t₀ + 6 * Real.exp (-(t₀ ^ 2 / (8 * w ^ 2))))
          ≤ 2 * (33 * Real.exp (-(1 / 2 * ℓ))) := by
            refine mul_le_mul hexpK_le2 (by linarith) (by positivity) (by norm_num)
        _ = 66 * Real.exp (-(1 / 2 * ℓ)) := by ring
        _ ≤ 66 * (1 / (66 * 32000) * Real.exp (-(1 / 60 * ℓ))) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = ((1 / 4000) * Real.exp (-(1 / 60 * ℓ))) / 8 := by ring
        _ ≤ ε / 8 := div_le_div_of_nonneg_right hε_ge (by norm_num)
    -- Center tail bound (`≤ (ε / 8) * (w * √π)`)
    have hcen_err : Cc * (N : ℝ) ^ (3 : ℝ) *
        ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 * 2 * Real.exp 1) *
          Real.exp (-(R ^ 2 / (4 * w ^ 2))) * (w * √(2 * Real.pi)) ≤
        ε / 8 * (w * √Real.pi) := by
      have hR_gauss : R ^ 2 / (4 * w ^ 2) = 4 * Θ + 8 * ℓ := by
        rw [hR_def]
        have hsq : (4 * w * Real.sqrt (Θ + 2 * ℓ)) ^ 2 = 16 * w ^ 2 * (Θ + 2 * ℓ) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
        rw [hsq, mul_div_right_comm]
        have hdiv : 16 * w ^ 2 / (4 * w ^ 2) = 4 := by field_simp; ring
        rw [hdiv]; ring
      have hN3_eq : (N : ℝ) ^ (3 : ℝ) = Real.exp (3 * Θ) := by
        rw [Real.rpow_def_of_pos hN_pos, ← hΘ_def]; congr 1; ring
      have hbase : (2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 ≤
          8100 * Real.exp (4 * ℓ) * ℓ ^ 8 := by
        have ht_abs : |t₀| ≤ 2 * T := by rw [abs_of_nonneg ht₀0.le]; exact ht₂
        have h1 : (1 + |t₀|) ^ 2 ≤ 9 * T ^ 2 := by
          calc (1 + |t₀|) ^ 2 ≤ (3 * T) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
            _ = 9 * T ^ 2 := by ring
        have h2 : 1 + 4 * w ^ 2 ≤ 5 * ℓ ^ 4 := by
          have hℓ4 : 1 ≤ ℓ ^ 4 := one_le_pow₀ (by linarith)
          rw [hw_def]; nlinarith
        have h3 : 2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2) ≤ 90 * T ^ 2 * ℓ ^ 4 := by
          calc 2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2) ≤ 2 * (9 * T ^ 2) * (5 * ℓ ^ 4) :=
                mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
                  (by positivity) (by positivity)
            _ = 90 * T ^ 2 * ℓ ^ 4 := by ring
        refine (pow_le_pow_left₀ (by positivity) h3 2).trans_eq ?_
        have hT4 : T ^ 4 = Real.exp (4 * ℓ) := by
          rw [← hT_exp, ← Real.exp_nat_mul]; norm_num
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, hT4]; ring
      have hexp_prod : Real.exp (3 * Θ) * Real.exp (4 * ℓ) * Real.exp (-(4 * Θ + 8 * ℓ)) ≤
          Real.exp (-4 * ℓ) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have hsqrt2 : √(2 * Real.pi) ≤ 2 * √Real.pi := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_right
          (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right hcen_sm (Real.exp_pos (-(1 / 60 * ℓ))).le
      have hexp_eq : Real.exp (-(239 / 60 * ℓ)) * Real.exp (-(1 / 60 * ℓ)) =
          Real.exp (-4 * ℓ) := by rw [← Real.exp_add]; congr 1; ring
      rw [mul_assoc, hexp_eq] at hmul
      have hsmall : C_cen * (ℓ ^ 8 * Real.exp (-4 * ℓ)) ≤ ε / 8 := by
        calc C_cen * (ℓ ^ 8 * Real.exp (-4 * ℓ))
            ≤ C_cen * (1 / (32000 * C_cen) * Real.exp (-(1 / 60 * ℓ))) :=
              mul_le_mul_of_nonneg_left hmul hC_cen_pos.le
          _ = ((1 / 4000) * Real.exp (-(1 / 60 * ℓ))) / 8 := by field_simp; ring
          _ ≤ ε / 8 := div_le_div_of_nonneg_right hε_ge (by norm_num)
      rw [hR_gauss, hN3_eq]
      calc Cc * Real.exp (3 * Θ) * ((2 * (1 + |t₀|) ^ 2 * (1 + 4 * w ^ 2)) ^ 2 * 2 * Real.exp 1) *
            Real.exp (-(4 * Θ + 8 * ℓ)) * (w * √(2 * Real.pi))
          ≤ Cc * Real.exp (3 * Θ) * ((8100 * Real.exp (4 * ℓ) * ℓ ^ 8) * 2 * Real.exp 1) *
              Real.exp (-(4 * Θ + 8 * ℓ)) * (w * (2 * √Real.pi)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase (by norm_num))
                (by positivity)) (by positivity)) (by positivity))
              (mul_le_mul_of_nonneg_left hsqrt2 hw0.le) (by positivity) (by positivity)
        _ = (Cc * 8100 * (2 * Real.exp 1) * 2) *
              (ℓ ^ 8 * (Real.exp (3 * Θ) * Real.exp (4 * ℓ) * Real.exp (-(4 * Θ + 8 * ℓ)))) *
              (w * √Real.pi) := by ring
        _ ≤ C_cen * (ℓ ^ 8 * Real.exp (-4 * ℓ)) * (w * √Real.pi) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul (by rw [hC_cen_def]; linarith)
              (mul_le_mul_of_nonneg_left hexp_prod (by positivity))
              (by positivity) hC_cen_pos.le
        _ ≤ ε / 8 * (w * √Real.pi) :=
            mul_le_mul_of_nonneg_right hsmall (by positivity)
    have hcosh : 2 * Real.cosh (a * (L + 2 * B)) = 5 / 2 := by
      have h3 : a * (L + 2 * B) = Real.log 2 := by rw [← haq, hL_def, hB_def]; ring
      rw [h3]; exact two_mul_cosh_log_two'
    have hmain := hwin t₀ hw0 ha0 ha4 hL0 hB0 hb
    rw [hcosh] at hmain
    have hrem_tot : (4 * Real.exp (9 / 4 / (2 * w ^ 2)) * (w * √(2 * Real.pi))) ^ 2 *
          Real.exp (L * a) * Real.exp (-(2 * B * (3 / 2 - a))) / (2 * Real.pi * (3 / 2 - a)) +
        (A * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.exp (1 / (2 * w ^ 2)) *
          (4 * (1 + |t₀|) ^ 2 * (1 + 2 * w ^ 2) * (√2 * w * √(2 * Real.pi)))) ^ 2 *
          Real.exp (-(L * a)) * Real.exp (-(2 * (L + B) * (1 - a))) / (2 * Real.pi * (1 - a)) ≤
        ε / 8 * (w * √Real.pi) := by
      rw [hB_def]
      calc _ ≤ 288 * w ^ 2 * Real.exp (-(1 / 50 * ℓ)) +
              (4 * (A ^ 2 * 9 * 432 ^ 2)) * w ^ 6 * Real.exp (-(1 / 25 * ℓ)) :=
            add_le_add hrem_r hrem_l
        _ ≤ ε / 16 * (w * √Real.pi) + ε / 16 * (w * √Real.pi) :=
            add_le_add hr₁_bound hr₂_bound
        _ = ε / 8 * (w * √Real.pi) := by ring
    have hmain2 := hmain.trans (add_le_add le_rfl hrem_tot)
    have hA₀ := le_integral_window_right_of_sq_le ht₀0 hw0 ha0 ha4 hK5 hN hb1 hb hε0 hε1
      hright_err ha_sq
    have hX := integral_gauss_linePower_left_le t₀ hw0 ha0 ha4 hT12 hb
    have hF₀ := (hcenter t₀ hw0 hR0 (T₃ := T) (T₄ := 2 * T) ht₀.1 (by linarith [ht₀.2]) hb).trans
      (add_le_add le_rfl hcen_err)
    have h3 := mul_le_mul_of_nonneg_left hA₀ (Real.exp_pos (L * a)).le
    have h4 := mul_le_mul_of_nonneg_left hX (Real.exp_pos (-(L * a))).le
    have h5 := mul_le_mul_of_nonneg_left hF₀ (by norm_num : (0 : ℝ) ≤ 5 / 2)
    have hD : 0 ≤ ε * (w * √Real.pi) := by positivity
    linarith
  -- Gaussian kernel mass on `[T + R, 2T - R]` for `t ∈ [T₁, T₂]`
  have hψ : ∀ t ∈ Icc T₁ T₂, (1 - ε) * (w * √Real.pi) ≤
      ∫ t₀ in (T + R)..(2 * T - R), gaussKernel w t t₀ := by
    intro t ht
    refine le_trans ?_ (gaussKernel_mass_ge hw0 hAB hR0 (by linarith [ht.1]) (by linarith [ht.2]))
    have hR2 : 16 * ℓ ≤ R ^ 2 / (2 * w ^ 2) := by
      rw [hR_def]
      have hsq : (4 * w * Real.sqrt (Θ + 2 * ℓ)) ^ 2 = 16 * w ^ 2 * (Θ + 2 * ℓ) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
      rw [hsq, mul_div_right_comm]
      have hdiv : 16 * w ^ 2 / (2 * w ^ 2) = 8 := by field_simp; ring
      rw [hdiv]; linarith
    have hexp_le : Real.exp (-(R ^ 2 / (2 * w ^ 2))) ≤ ε / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hmass_sm (Real.exp_pos (-(1 / 60 * ℓ))).le
      have hexp_eq : Real.exp (-(959 / 60 * ℓ)) * Real.exp (-(1 / 60 * ℓ)) =
          Real.exp (-16 * ℓ) := by rw [← Real.exp_add]; congr 1; ring
      rw [pow_zero, one_mul, hexp_eq] at hmul
      calc Real.exp (-(R ^ 2 / (2 * w ^ 2)))
          ≤ Real.exp (-16 * ℓ) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 1 / 8000 * Real.exp (-(1 / 60 * ℓ)) := hmul
        _ = ((1 / 4000) * Real.exp (-(1 / 60 * ℓ))) / 2 := by ring
        _ ≤ ε / 2 := div_le_div_of_nonneg_right hε_ge (by norm_num)
    have hsqrt2 : √(2 * Real.pi) ≤ 2 * √Real.pi := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right
        (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (Real.sqrt_nonneg _)
    have h4 : Real.exp (-(R ^ 2 / (2 * w ^ 2))) * (w * √(2 * Real.pi)) ≤
        ε / 2 * (w * (2 * √Real.pi)) :=
      mul_le_mul hexp_le (mul_le_mul_of_nonneg_left hsqrt2 hw0.le) (by positivity) (by positivity)
    linarith [show ε / 2 * (w * (2 * √Real.pi)) = ε * (w * √Real.pi) by ring,
      show (1 - ε) * (w * √Real.pi) = w * √Real.pi - ε * (w * √Real.pi) by ring]
  have hm1 : -3 / 2 < -a := by linarith
  have hm0 : -3 / 2 < (0 : ℝ) := by norm_num
  have hint := integrated_gauss_inequality (c₁ := Real.exp (L * a) * ((1 - ε) * (w * √Real.pi)))
    (c₂ := Real.exp (-(L * a))) (c₃ := 5 / 2) (τ := ε / 2 * (w * √Real.pi))
    (T₃ := T) (T₄ := 2 * T) hw0 hAB hT12 (by linarith)
    (continuous_linePower b N hm1) (continuous_linePower b N hm0)
    (linePower_nonneg b N _) (linePower_nonneg b N _) (Real.exp_pos _).le (by norm_num)
    hheight hψ
  -- Complex left floor on `[T₁, T₂]`
  set z : ℝ := Real.exp (99 / 100 * p * Real.log 2) with hz_def
  have hz0 : 0 < z := by rw [hz_def]; positivity
  have hzval : (T₂ - T₁) * z ≤
      ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    set v : ℝ := Real.log 2 / q with hv_def
    have hv0 : 0 < v := by rw [hv_def]; positivity
    have hv_eq : 2 * v = p * Real.log 2 := by rw [hv_def, hp_def]; ring
    have hv_ge : (1 / 8) * Real.exp (-(1 / 60 * ℓ)) ≤ v := by
      have h1 : p * (1 / 2) ≤ p * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2_gt_half.le hp0.le
      linarith
    have haℓ : a * ℓ = v := by
      rw [ha_def, hv_def]; field_simp
    have hcount := hcnt T₁ T₂ (by linarith) (by linarith) (by linarith) (by linarith)
    set Δ : ℝ := (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁
    have hmain_cnt : 996 / 1000 * (v * T) ≤ 2 * Real.pi * (a * Δ) := by
      have h1 := mul_le_mul_of_nonneg_left hcount ha0.le
      have h2 : a * (996 / 1000 * (T * ℓ)) = 996 / 1000 * ((a * ℓ) * T) := by ring
      have h3 : a * (2 * Real.pi * Δ) = 2 * Real.pi * (a * Δ) := by ring
      rw [← hℓ_def] at h1
      rw [h2, haℓ, h3] at h1
      exact h1
    have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ hN_ge1
    have hlog_err : Cl + Kl * (Real.log T₂ + Real.log ((N : ℝ) ^ 5)) ≤ 6 / 1000 * (v * T) := by
      have hlogT2 : Real.log T₂ ≤ ℓ + 1 := by
        have h1 : Real.log T₂ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_mul two_ne_zero hT0.ne', ← hℓ_def] at h1
        linarith [Real.log_two_lt_d9]
      have hlogN5 : Real.log ((N : ℝ) ^ 5) = 5 * Θ := by
        rw [Real.log_pow, ← hΘ_def]; push_cast; ring
      have herr_up : Cl + Kl * (Real.log T₂ + Real.log ((N : ℝ) ^ 5)) ≤
          C_lf * ℓ * Real.exp (1 / 60 * ℓ) := by
        rw [hlogN5, hC_lf_def]
        have h1 : Cl ≤ Cl * ℓ * Real.exp (1 / 60 * ℓ) := by nlinarith
        have h2 : Kl * (ℓ + 1) ≤ 2 * Kl * ℓ * Real.exp (1 / 60 * ℓ) := by nlinarith
        have h3 : Kl * (5 * Θ) ≤ 5 * Kl * ℓ * Real.exp (1 / 60 * ℓ) := by nlinarith
        linarith
      have hmul := mul_le_mul_of_nonneg_right hlf_sm (Real.exp_pos (59 / 60 * ℓ)).le
      have hexp_eq : Real.exp (-(29 / 30 * ℓ)) * Real.exp (59 / 60 * ℓ) =
          Real.exp (1 / 60 * ℓ) := by rw [← Real.exp_add]; congr 1; ring
      rw [pow_one, mul_assoc, hexp_eq] at hmul
      calc Cl + Kl * (Real.log T₂ + Real.log ((N : ℝ) ^ 5))
          ≤ C_lf * ℓ * Real.exp (1 / 60 * ℓ) := herr_up
        _ = C_lf * (ℓ * Real.exp (1 / 60 * ℓ)) := by ring
        _ ≤ C_lf * (((6 / 8000) / C_lf) * Real.exp (59 / 60 * ℓ)) :=
            mul_le_mul_of_nonneg_left hmul hC_lf_pos.le
        _ = 6 / 1000 * ((1 / 8) * Real.exp (-(1 / 60 * ℓ)) * Real.exp ℓ) := by
            have hexp2 : Real.exp (59 / 60 * ℓ) = Real.exp (-(1 / 60 * ℓ)) * Real.exp ℓ := by
              rw [← Real.exp_add]; congr 1; ring
            rw [hexp2]; field_simp; ring
        _ ≤ 6 / 1000 * (v * T) := by
            rw [← hT_exp]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hv_ge (Real.exp_pos ℓ).le) (by norm_num)
    set E₀ : ℝ := 2 * Real.pi * (a * Δ) - Cl - Kl * (Real.log T₂ + Real.log ((N : ℝ) ^ 5))
    have hE₀_ge : 99 / 100 * (v * T) ≤ E₀ := by linarith
    have hE₀_pos : 0 < E₀ := lt_of_lt_of_le (by positivity) hE₀_ge
    have hfl := hleft_floor b N hN hb1 hb ((N : ℝ) ^ 5) hMb1 (sum_norm_mul_rpow_four_le hb)
      a T₁ T₂ ha0 ha4 (by linarith) hT12_lt
      (fun x hx => (hs1 x hx).1) (fun x hx => (hs2 x hx).1)
      (fun x hx => (hs1 x hx).2) (fun x hx => (hs2 x hx).2) hE₀_pos
    have hexp_ge : z ≤ Real.exp (2 / (T₂ - T₁) * E₀) := by
      rw [hz_def]
      refine Real.exp_le_exp.mpr ?_
      have hlen_pos : 0 < T₂ - T₁ := by linarith
      have hlen_le : T₂ - T₁ ≤ T := by linarith
      have hdiv_ge : 2 / T ≤ 2 / (T₂ - T₁) :=
        div_le_div_of_nonneg_left (by norm_num) hlen_pos hlen_le
      calc 99 / 100 * p * Real.log 2
          = (2 / T) * (99 / 100 * (v * T)) := by rw [← hv_eq]; field_simp; ring
        _ ≤ (2 / (T₂ - T₁)) * E₀ :=
            mul_le_mul hdiv_ge hE₀_ge (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_left hexp_ge (by linarith)).trans hfl
  have hTε : 4 / ε ≤ T₁ := by
    rw [div_le_iff₀ hε0]
    calc (4 : ℝ) ≤ 32000 := by norm_num
      _ ≤ ε * T := hεT_ge32000
      _ ≤ ε * T₁ := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have hIlow := le_integral_linePower_left b N hε0 ha0 ha4 hT12 (by linarith) hTε
  have hε' : 0 ≤ 1 - ε := by linarith
  have hlen12 : (1 - ε) * T ≤ T₂ - T₁ := by linarith
  have hIz : (1 - ε) ^ 2 * z * T ≤ ∫ t in T₁..T₂, linePower b N (-a) t := by
    have h3 := (mul_le_mul_of_nonneg_left hzval hε').trans hIlow
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlen12 hz0.le) hε'
    calc (1 - ε) ^ 2 * z * T = (1 - ε) * ((1 - ε) * T * z) := by ring
      _ ≤ _ := h4
      _ ≤ _ := h3
  have hfinal := length_combine' (x := Real.exp (L * a)) (y := Real.exp (-(L * a))) (z := z)
    (Real.exp_pos _).le (Real.exp_pos _).le hε0 hε1 hT0 (by positivity : 0 < w * √Real.pi)
    (δ := 2 * T - R - (T + R)) (by linarith) (by linarith)
    (integral_linePower_zero_le b N (by linarith : T ≤ 2 * T)) hIz hint
  have hnum := final_numeric hp0 hp1 hε_def (congrArg Real.exp hLa) (by rw [hLa]) hz_def hT0 hfinal
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hT0.le) hnum
  have hcomp := length_constant_nonneg hθ0 hq_def hp0 hpq
  have hfrac_eq : ℓ / (8 * ℓ + 6 * Θ) = 1 / (8 + 6 * θ) := by
    rw [hθ_def]; field_simp
  linarith

/-- Exponent-parametrized form of `eventually_uniform_complex_necessary_length`: uniformly in
`0 ≤ θ ≤ T^{1/60} / log T` and all complex Dirichlet polynomials of length `N ≤ T^θ`. -/
theorem eventually_uniform_complex_necessary_length_exp :
    ∀ᶠ T : ℝ in atTop, ∀ θ : ℝ, 0 ≤ θ → θ * Real.log T ≤ T ^ (1 / 60 : ℝ) →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → (N : ℝ) ≤ T ^ θ → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (1 + 1 / (8 + 6 * θ)) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  filter_upwards [eventually_uniform_complex_necessary_length, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hmain hT3 hℓ1 θ hθ0 hθ_up b N hN hNT hb1 hb
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < Real.log T := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogN_le_θ : Real.log (N : ℝ) ≤ θ * Real.log T := by
    calc Real.log (N : ℝ) ≤ Real.log (T ^ θ) := Real.log_le_log hN_pos hNT
      _ = θ * Real.log T := Real.log_rpow hT0
  have hlogN_up : Real.log (N : ℝ) ≤ T ^ (1 / 60 : ℝ) := hlogN_le_θ.trans hθ_up
  have h1 := hmain b N hN hlogN_up hb1 hb
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hT0.le) h1
  have hden1 : 0 < 8 + 6 * θ := by positivity
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hden2 : 0 < 8 * Real.log T + 6 * Real.log (N : ℝ) := by positivity
  have hfrac : 1 / (8 + 6 * θ) ≤ Real.log T / (8 * Real.log T + 6 * Real.log (N : ℝ)) := by
    rw [div_le_div_iff₀ hden1 hden2]; nlinarith
  linarith

/-- **Logarithmic mollifier length forced by a small second-moment excess.**
Eventually as `T → ∞`, simultaneously for every `E > 0` and every complex Dirichlet polynomial
`M` of length `N ≥ 1` (`b 1 = 1`, `‖b n‖ ≤ 1`), if
`∫_T^{2T} ‖ζ(1/2 + it) M(1/2 + it)‖² dt ≤ (1 + E) T`, then
`min (T^{1/60}) (log T / (6 E) - (4 / 3) log T) ≤ log N`. -/
theorem eventually_log_mollifier_length_ge_of_excess :
    ∀ᶠ T : ℝ in atTop, ∀ (b : ℕ → ℂ) (N : ℕ) (E : ℝ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) → 0 < E →
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + E) * T →
      min (T ^ (1 / 60 : ℝ)) (Real.log T / (6 * E) - 4 / 3 * Real.log T) ≤ Real.log (N : ℝ) := by
  filter_upwards [eventually_uniform_complex_necessary_length, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hmain hT3 hℓ1 b N E hN hb1 hb hE hmom
  by_cases hcap : T ^ (1 / 60 : ℝ) ≤ Real.log (N : ℝ)
  · exact (min_le_left _ _).trans hcap
  · push Not at hcap
    refine (min_le_right _ _).trans ?_
    have hT0 : 0 < T := by linarith
    have hℓ0 : 0 < Real.log T := by linarith
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlow := (hmain b N hN hcap.le hb1 hb).trans hmom
    have h1 : 1 + Real.log T / (8 * Real.log T + 6 * Real.log (N : ℝ)) ≤ 1 + E :=
      le_of_mul_le_mul_right hlow hT0
    have h2 : Real.log T / (8 * Real.log T + 6 * Real.log (N : ℝ)) ≤ E := by linarith
    have hden : 0 < 8 * Real.log T + 6 * Real.log (N : ℝ) := by positivity
    rw [div_le_iff₀ hden] at h2
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : 0 < 6 * E)]
    linarith

/-- **Exact `exp(c (log T)²)` length threshold for `ComplexSecondMomentRate K₀`.**
Any witness family `(b T, N T)` achieving the `D_zero`/`D_win`-forcing rate
`∫_T^{2T} ‖ζ M_T(1/2 + it)‖² dt ≤ (1 + K₀ / log T) T` (`K₀ > 0`) must satisfy
`(log T)² / (6 K₀) - (4 / 3) log T ≤ log (N T)` for all sufficiently large `T`. -/
theorem complexSecondMomentRate_forces_exp_logSq_length {K₀ : ℝ} (hK₀ : 0 < K₀)
    {b : ℝ → ℕ → ℂ} {N : ℝ → ℕ}
    (hN : ∀ᶠ T : ℝ in atTop, 1 ≤ N T)
    (hb1 : ∀ᶠ T : ℝ in atTop, b T 1 = 1)
    (hb : ∀ᶠ T : ℝ in atTop, ∀ n ∈ Finset.Icc 1 (N T), ‖b T n‖ ≤ 1)
    (hmom : ∀ᶠ T : ℝ in atTop,
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (b T) (Finset.Icc 1 (N T)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (1 + K₀ / Real.log T) * T) :
    ∀ᶠ T : ℝ in atTop,
      (Real.log T) ^ 2 / (6 * K₀) - 4 / 3 * Real.log T ≤ Real.log (N T : ℝ) := by
  filter_upwards [eventually_log_mollifier_length_ge_of_excess, hN, hb1, hb, hmom,
    eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_log_pow_mul_exp_le 2 (c := 1 / 60) (ε := 6 * K₀) (by norm_num) (by positivity)]
    with T hex hNT hb1T hbT hmomT hT3 hℓ1 hcap_dom
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < Real.log T := by linarith
  have hE0 : 0 < K₀ / Real.log T := div_pos hK₀ hℓ0
  have hmin := hex (b T) (N T) (K₀ / Real.log T) hNT hb1T hbT hE0 hmomT
  have hrew : Real.log T / (6 * (K₀ / Real.log T)) = (Real.log T) ^ 2 / (6 * K₀) := by
    field_simp; ring
  rw [hrew] at hmin
  have hdom : (Real.log T) ^ 2 / (6 * K₀) - 4 / 3 * Real.log T ≤ T ^ (1 / 60 : ℝ) := by
    have hT60 : T ^ (1 / 60 : ℝ) = Real.exp (1 / 60 * Real.log T) := by
      rw [Real.rpow_def_of_pos hT0]; ring_nf
    rw [hT60]
    have h1 := mul_le_mul_of_nonneg_right hcap_dom (Real.exp_pos (1 / 60 * Real.log T)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h1
    have h2 : (Real.log T) ^ 2 / (6 * K₀) ≤ Real.exp (1 / 60 * Real.log T) :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith
  rwa [min_eq_right hdom] at hmin

/-- **Sub-`exp(c (log T)²)` complex mollifier impossibility for `ComplexSecondMomentRate K₀`.**
For every `K₀ > 0` and every `δ < 1 / (6 K₀)`, no complex Dirichlet polynomial family of length
`log N(T) ≤ δ (log T)²` can achieve `(1 + K₀ / log T) T` eventually. -/
theorem not_complexSecondMomentRate_below_exp_logSq {K₀ δ : ℝ} (hK₀ : 0 < K₀)
    (hδ : δ < 1 / (6 * K₀)) {b : ℝ → ℕ → ℂ} {N : ℝ → ℕ}
    (hN : ∀ᶠ T : ℝ in atTop, 1 ≤ N T)
    (hb1 : ∀ᶠ T : ℝ in atTop, b T 1 = 1)
    (hb : ∀ᶠ T : ℝ in atTop, ∀ n ∈ Finset.Icc 1 (N T), ‖b T n‖ ≤ 1)
    (hlen : ∀ᶠ T : ℝ in atTop, Real.log (N T : ℝ) ≤ δ * (Real.log T) ^ 2) :
    ¬ (∀ᶠ T : ℝ in atTop,
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (b T) (Finset.Icc 1 (N T)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (1 + K₀ / Real.log T) * T) := by
  intro hmom
  have hgap : 0 < 1 / (6 * K₀) - δ := sub_pos.mpr hδ
  have hlow := complexSecondMomentRate_forces_exp_logSq_length hK₀ hN hb1 hb hmom
  have hbig : ∀ᶠ T : ℝ in atTop,
      (4 / 3 : ℝ) / (1 / (6 * K₀) - δ) + 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨T, hlowT, hlenT, hbigT, hℓ1⟩ :=
    (hlow.and (hlen.and (hbig.and (Real.tendsto_log_atTop.eventually_ge_atTop 1)))).exists
  have hℓ0 : 0 < Real.log T := by linarith
  have hcomb : (1 / (6 * K₀) - δ) * (Real.log T) ^ 2 ≤ 4 / 3 * Real.log T := by
    have : (Real.log T) ^ 2 / (6 * K₀) = (1 / (6 * K₀)) * (Real.log T) ^ 2 := by ring
    linarith
  have hdiv : (1 / (6 * K₀) - δ) * Real.log T ≤ 4 / 3 := by
    refine le_of_mul_le_mul_right ?_ hℓ0
    calc (1 / (6 * K₀) - δ) * Real.log T * Real.log T
        = (1 / (6 * K₀) - δ) * (Real.log T) ^ 2 := by ring
      _ ≤ 4 / 3 * Real.log T := hcomb
  have hlt : 4 / 3 < (1 / (6 * K₀) - δ) * Real.log T := by
    have h1 := (div_le_iff₀ hgap).mp (by linarith : (4 / 3 : ℝ) / (1 / (6 * K₀) - δ) ≤ Real.log T - 1)
    nlinarith
  linarith

/-- **Critical-line `θ(T) → +∞` law for arbitrary complex mollifiers.**
Any complex Dirichlet polynomial family `(b T, N T)` (`1 ≤ N T`, `b T 1 = 1`, `‖b T n‖ ≤ 1`)
whose normalized critical-line second moment tends to `1` forces
`Real.log (N T : ℝ) / Real.log T → +∞`. -/
theorem tendsto_log_length_div_log_atTop_of_complex_second_moment_tendsto_one
    {b : ℝ → ℕ → ℂ} {N : ℝ → ℕ}
    (hN : ∀ᶠ T : ℝ in atTop, 1 ≤ N T)
    (hb1 : ∀ᶠ T : ℝ in atTop, b T 1 = 1)
    (hb : ∀ᶠ T : ℝ in atTop, ∀ n ∈ Finset.Icc 1 (N T), ‖b T n‖ ≤ 1)
    (htend : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (b T) (Finset.Icc 1 (N T)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop (𝓝 1)) :
    Tendsto (fun T : ℝ => Real.log (N T : ℝ) / Real.log T) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  set M' : ℝ := max M 1
  have hM' : 1 ≤ M' := le_max_right _ _
  have hE : 0 < 1 / (6 * (M' + 2)) := by positivity
  have hev_mom : ∀ᶠ T : ℝ in atTop,
      T⁻¹ * (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly (b T) (Finset.Icc 1 (N T)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) <
        1 + 1 / (6 * (M' + 2)) :=
    htend.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [eventually_log_mollifier_length_ge_of_excess, hN, hb1, hb, hev_mom,
    eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_log_pow_mul_exp_le 1 (c := 1 / 60) (ε := 1 / (M' + 2)) (by norm_num) (by positivity)]
    with T hex hNT hb1T hbT hmomT hT3 hℓ1 hcap
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < Real.log T := by linarith
  have hmom_le : (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly (b T) (Finset.Icc 1 (N T)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (1 + 1 / (6 * (M' + 2))) * T := by
    have h1 := mul_le_mul_of_nonneg_right (mem_Iio.mp hmomT).le hT0.le
    rwa [inv_mul_cancel_left₀ hT0.ne' _] at h1
  have hmin := hex (b T) (N T) (1 / (6 * (M' + 2))) hNT hb1T hbT hE hmom_le
  have hrew : Real.log T / (6 * (1 / (6 * (M' + 2)))) - 4 / 3 * Real.log T =
      (M' + 2 / 3) * Real.log T := by field_simp; ring
  rw [hrew] at hmin
  have hdom : (M' + 2) * Real.log T ≤ T ^ (1 / 60 : ℝ) := by
    have hT60 : T ^ (1 / 60 : ℝ) = Real.exp (1 / 60 * Real.log T) := by
      rw [Real.rpow_def_of_pos hT0]; ring_nf
    rw [hT60]
    have h1 := mul_le_mul_of_nonneg_right hcap (Real.exp_pos (1 / 60 * Real.log T)).le
    rw [pow_one, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h1
    exact (div_le_iff₀ (by positivity : 0 < M' + 2)).mp (by field_simp; linarith)
  have hlow : M' * Real.log T ≤ Real.log (N T : ℝ) := by
    have hsub : M' * Real.log T ≤ min (T ^ (1 / 60 : ℝ)) ((M' + 2 / 3) * Real.log T) :=
      le_min (by nlinarith) (by nlinarith)
    exact hsub.trans hmin
  exact (le_max_left M 1).trans ((le_div_iff₀ hℓ0).mpr hlow)


/-! ## §3. Superposed multi-window critical-line zero spikes (`D_win`) -/

/-- Pigeonhole principle modulo `k > 0` on a finite set of natural numbers. -/
theorem finset_exists_mod_class_card_ge {k : ℕ} (hk : 0 < k) (B : Finset ℕ) :
    ∃ j : Fin k, B.card ≤ k * (B.filter (fun m => m % k = j.val)).card := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hpart : B.card = ∑ j : Fin k, (B.filter (fun m => m % k = j.val)).card := by
    have h1 : ∀ m ∈ B, (1 : ℕ) = ∑ j : Fin k, if m % k = j.val then 1 else 0 := by
      intro m _
      let j₀ : Fin k := ⟨m % k, Nat.mod_lt m hk⟩
      rw [Finset.sum_eq_single j₀]
      · simp [j₀]
      · intro j _ hj; rw [if_neg]; intro heq; apply hj; ext; exact heq.symm
      · intro h; exact absurd (Finset.mem_univ j₀) h
    calc B.card = ∑ m ∈ B, 1 := Finset.card_eq_sum_ones B
      _ = ∑ m ∈ B, ∑ j : Fin k, if m % k = j.val then 1 else 0 :=
          Finset.sum_congr rfl fun m hm => h1 m hm
      _ = ∑ j : Fin k, ∑ m ∈ B, if m % k = j.val then 1 else 0 := Finset.sum_comm
      _ = ∑ j : Fin k, (B.filter (fun m => m % k = j.val)).card := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_filter]
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin k => (B.filter (fun m => m % k = j.val)).card) Finset.univ_nonempty
  refine ⟨j₀, ?_⟩
  calc B.card = ∑ j : Fin k, (B.filter (fun m => m % k = j.val)).card := hpart
    _ ≤ ∑ _j : Fin k, (B.filter (fun m => m % k = j₀.val)).card :=
        Finset.sum_le_sum fun j hj => hj₀ j hj
    _ = k * (B.filter (fun m => m % k = j₀.val)).card := by
        rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]

/-- Superadditivity of a nonnegative continuous integrand over pairwise disjoint `Ioc` subintervals
contained in `Ioc a b`. -/
theorem sum_Ioc_integral_le_intervalIntegral {S : Finset ℕ} {L U : ℕ → ℝ} {a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hg_cont : Continuous g) (hg_nn : ∀ t, 0 ≤ g t)
    (hLU : ∀ m ∈ S, L m ≤ U m)
    (hsub : ∀ m ∈ S, Ioc (L m) (U m) ⊆ Ioc a b)
    (hdisj : (S : Set ℕ).PairwiseDisjoint (fun m => Ioc (L m) (U m))) :
    (∑ m ∈ S, ∫ t in (L m)..(U m), g t) ≤ ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab]
  have hint_ab : IntegrableOn g (Ioc a b) volume :=
    hg_cont.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hint_ind_ab : Integrable ((Ioc a b).indicator g) volume :=
    hint_ab.integrable_indicator measurableSet_Ioc
  have hint_m : ∀ m ∈ S, Integrable ((Ioc (L m) (U m)).indicator g) volume := fun m hm =>
    (hint_ab.mono_set (hsub m hm)).integrable_indicator measurableSet_Ioc
  have hrew : (∑ m ∈ S, ∫ t in (L m)..(U m), g t) =
      ∫ t, ∑ m ∈ S, (Ioc (L m) (U m)).indicator g t := by
    calc (∑ m ∈ S, ∫ t in (L m)..(U m), g t)
        = ∑ m ∈ S, ∫ t in Ioc (L m) (U m), g t :=
          Finset.sum_congr rfl fun m hm => intervalIntegral.integral_of_le (hLU m hm)
      _ = ∑ m ∈ S, ∫ t, (Ioc (L m) (U m)).indicator g t :=
          Finset.sum_congr rfl fun m _ => (integral_indicator measurableSet_Ioc).symm
      _ = ∫ t, ∑ m ∈ S, (Ioc (L m) (U m)).indicator g t :=
          (integral_finsetSum S fun m hm => hint_m m hm).symm
  rw [hrew, ← integral_indicator measurableSet_Ioc]
  refine integral_mono (integrable_finsetSum S fun m hm => hint_m m hm) hint_ind_ab fun t => ?_
  by_cases hex : ∃ m ∈ S, t ∈ Ioc (L m) (U m)
  · obtain ⟨m₀, hm₀S, htm₀⟩ := hex
    have hab_mem : t ∈ Ioc a b := hsub m₀ hm₀S htm₀
    rw [Finset.sum_eq_single m₀]
    · rw [Set.indicator_of_mem htm₀, Set.indicator_of_mem hab_mem]
    · intro n hnS hnm₀
      have hnot : t ∉ Ioc (L n) (U n) :=
        Set.disjoint_left.mp (hdisj hm₀S hnS hnm₀.symm) htm₀
      exact Set.indicator_of_notMem hnot g
    · intro hm₀_not; exact absurd hm₀S hm₀_not
  · push Not at hex
    have hzero : (∑ m ∈ S, (Ioc (L m) (U m)).indicator g t) = 0 :=
      Finset.sum_eq_zero fun m hm => Set.indicator_of_notMem (hex m hm) g
    rw [hzero]
    exact Set.indicator_nonneg (fun x _ => hg_nn x) t

private theorem nat_add_le_of_lt_of_mod_eq {k m₁ m₂ : ℕ} (hlt : m₁ < m₂)
    (hmod : m₁ % k = m₂ % k) : m₁ + k ≤ m₂ := by
  have hd₁ := (Nat.div_add_mod m₁ k).symm
  have hd₂ := (Nat.div_add_mod m₂ k).symm
  have hdiv_lt : m₁ / k < m₂ / k := by
    by_contra hge
    have hle : k * (m₂ / k) ≤ k * (m₁ / k) := Nat.mul_le_mul_left k (Nat.not_lt.mp hge)
    omega
  have hdiv_succ : k * (m₁ / k + 1) ≤ k * (m₂ / k) := Nat.mul_le_mul_left k hdiv_lt
  have hmul_add : k * (m₁ / k + 1) = k * (m₁ / k) + k := Nat.mul_add k (m₁ / k) 1
  omega

/-- **Superposed multi-window critical-line zero spikes (`D_win`, general `α > 0`).**
Let `S ⊆ [⌈V⌉, ⌊2V⌋]` be any collection of Burnol unit windows each containing a `ξ`-zero with
`|Re ρ - 1/2| ≥ δ` (`δ > 0`). Coloring `S` modulo `⌈2R + 7⌉₊` extracts pairwise disjoint ordinate
intervals `[Im ρ_m - R, Im ρ_m + R] ⊆ [V - R - 3, 2V + R + 3]` on which every prefix-cancelling
Dirichlet polynomial `M(s) = ∑_{d=1}^X b_d d^{-s}` exhibits a critical-line spike of size at least
`(3 / 4) δ e^{-α / 2} Y^{2δ}`, forcing their sum onto the critical-line second moment. -/
theorem occupiedBurnolWindows_criticalLine_spike_ge
    {V δ R α Y B : ℝ} (hR1 : 1 ≤ R) (hRV : R + 4 ≤ V) (hδ0 : 0 < δ)
    (hα : 0 < α) (hY : 1 ≤ Y) (hYα : 2 * Real.sqrt α ≤ Real.log Y) (hB : 1 ≤ B)
    {X X₁ : ℕ} (hX : 1 ≤ X) (hX₁ : 1 ≤ X₁) (hYX₁ : Y < (X₁ : ℝ))
    (hslope : 5 * α ≤ Real.log (X₁ : ℝ) - Real.log Y)
    {b : ℕ → ℂ} (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B)
    (hshort : ∑ n ∈ Finset.Icc 2 X₁,
      ‖_root_.RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-(1 / 2 + δ)) ≤ 1 / 8)
    (htail : 2 * B * (Real.sqrt α / (Real.log (X₁ : ℝ) - Real.log Y)) *
      (X₁ : ℝ) ^ (3 / 2 : ℝ) *
      Real.exp (-(Real.log (X₁ : ℝ) - Real.log Y) ^ 2 / (4 * α)) ≤ 1 / 12)
    (hvtail : 4 * B * (1 / Real.sqrt α) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) ≤ 1 / 12)
    (hhoriz : 5 * B * (X : ℝ) * Real.sqrt (2 * V + R + 9) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) ≤ 1 / 12)
    {S : Finset ℕ} (hS_sub : S ⊆ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)))
    (hS_occ : ∀ m ∈ S, ∃ ρ ∈ burnolUnitXiZeros m, δ ≤ |ρ.re - 1 / 2|) :
    ((S.card : ℝ) / (Nat.ceil (2 * R + 7) : ℝ)) *
        ((3 / 4 : ℝ) * δ * Real.exp (-(α / 2)) * Y ^ (2 * δ)) ≤
      ∫ t in (V - R - 3)..(2 * V + R + 3),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  classical
  have hV_pos : 0 < V := by linarith
  have hR_pos : 0 < R := by linarith
  set P_R : ℕ := Nat.ceil (2 * R + 7) with hP_R_def
  have hP_R_pos : 0 < P_R := Nat.ceil_pos.mpr (by positivity)
  have hP_R_ge : 2 * R + 7 ≤ (P_R : ℝ) := Nat.le_ceil (2 * R + 7)
  have hP_R_cast_pos : (0 : ℝ) < (P_R : ℝ) := by exact_mod_cast hP_R_pos
  have hex_right : ∀ m ∈ S, ∃ ρ ∈ burnolUnitXiZeros m, 1 / 2 + δ ≤ ρ.re := by
    intro m hm
    obtain ⟨ρ, hρ_mem, hρ_abs⟩ := hS_occ m hm
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
    · refine ⟨ρ, hρ_mem, ?_⟩
      rw [abs_of_nonneg (by linarith)] at hρ_abs; linarith
    · refine ⟨1 - star ρ, one_sub_star_mem_burnolUnitXiZeros m ρ hρ_mem, ?_⟩
      rw [abs_of_neg (by linarith)] at hρ_abs
      have hre_star : (1 - star ρ).re = 1 - ρ.re := by simp
      linarith
  let ρ_sel : ℕ → ℂ := fun m =>
    if hm : m ∈ S then Classical.choose (hex_right m hm) else 0
  have hρ_prop : ∀ m (hm : m ∈ S),
      ρ_sel m ∈ burnolUnitXiZeros m ∧ 1 / 2 + δ ≤ (ρ_sel m).re := by
    intro m hm; dsimp [ρ_sel]; rw [dif_pos hm]; exact Classical.choose_spec (hex_right m hm)
  obtain ⟨j₀, hj₀_card⟩ := finset_exists_mod_class_card_ge hP_R_pos S
  set B₀ : Finset ℕ := S.filter (fun m => m % P_R = j₀.val) with hB₀_def
  have hcard_div : (S.card : ℝ) / (P_R : ℝ) ≤ (B₀.card : ℝ) := by
    rw [div_le_iff₀ hP_R_cast_pos, mul_comm]
    exact_mod_cast hj₀_card
  have hm_info : ∀ m ∈ B₀,
      riemannZeta (ρ_sel m) = 0 ∧ 1 / 2 + δ ≤ (ρ_sel m).re ∧ (ρ_sel m).re < 1 ∧
      (m : ℝ) - 3 < (ρ_sel m).im ∧ (ρ_sel m).im < (m : ℝ) + 3 ∧
      V - 3 < (ρ_sel m).im ∧ (ρ_sel m).im < 2 * V + 3 := by
    intro m hm₀
    have hmS : m ∈ S := (Finset.mem_filter.mp hm₀).1
    have hmIcc : m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)) := hS_sub hmS
    obtain ⟨hρ_mem, hρ_re_lo⟩ := hρ_prop m hmS
    have hρ_iff := (mem_burnolUnitXiZeros_iff m (ρ_sel m)).mp hρ_mem
    have hcoords := burnolUnit_coords m
    have hm_lo : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hmIcc).1)
    have hm_hi : (m : ℝ) ≤ 2 * V :=
      (by exact_mod_cast (Finset.mem_Icc.mp hmIcc).2 : (m : ℝ) ≤ (Nat.floor (2 * V) : ℝ)).trans
        (Nat.floor_le (by positivity))
    have hre_pos : 0 < (ρ_sel m).re := by linarith
    have hne1 : ρ_sel m ≠ 1 := by
      intro h1; rw [h1, Complex.one_re] at hρ_iff; exact lt_irrefl 1 hρ_iff.1.2.1
    have hζ0 : riemannZeta (ρ_sel m) = 0 :=
      (_root_.RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hre_pos hne1).mp hρ_iff.2
    refine ⟨hζ0, hρ_re_lo, hρ_iff.1.2.1, ?_, ?_, ?_, ?_⟩
    · linarith [hcoords.2.2.1, hcoords.2.2.2.2, hρ_iff.1.2.2.1]
    · linarith [hcoords.2.2.2.1, hρ_iff.1.2.2.2]
    · linarith [hcoords.2.2.1, hcoords.2.2.2.2, hρ_iff.1.2.2.1]
    · linarith [hcoords.2.2.2.1, hρ_iff.1.2.2.2]
  have hsub_Ioc : ∀ m ∈ B₀,
      Ioc ((ρ_sel m).im - R) ((ρ_sel m).im + R) ⊆ Ioc (V - R - 3) (2 * V + R + 3) := by
    intro m hm₀ t ht
    obtain ⟨_, _, _, _, _, him_lo, him_hi⟩ := hm_info m hm₀
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdisj : (B₀ : Set ℕ).PairwiseDisjoint
      (fun m => Ioc ((ρ_sel m).im - R) ((ρ_sel m).im + R)) := by
    intro m₁ hm₁ m₂ hm₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro t ht₁ ht₂
    rw [Finset.mem_coe, hB₀_def, Finset.mem_filter] at hm₁ hm₂
    have hmod : m₁ % P_R = m₂ % P_R := hm₁.2.trans hm₂.2.symm
    obtain ⟨_, _, _, hm₁_lo, hm₁_hi, _, _⟩ := hm_info m₁ (Finset.mem_filter.mpr hm₁)
    obtain ⟨_, _, _, hm₂_lo, hm₂_hi, _, _⟩ := hm_info m₂ (Finset.mem_filter.mpr hm₂)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : m₁ + P_R ≤ m₂ := nat_add_le_of_lt_of_mod_eq hlt hmod
      have hstep_r : (m₁ : ℝ) + (P_R : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hstep
      linarith [ht₁.2, ht₂.1]
    · have hstep : m₂ + P_R ≤ m₁ := nat_add_le_of_lt_of_mod_eq hgt hmod.symm
      have hstep_r : (m₂ : ℝ) + (P_R : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast hstep
      linarith [ht₂.2, ht₁.1]
  have hspike_m : ∀ m ∈ B₀,
      (3 / 4 : ℝ) * δ * Real.exp (-(α / 2)) * Y ^ (2 * δ) ≤
        ∫ t in ((ρ_sel m).im - R)..((ρ_sel m).im + R),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro m hm₀
    obtain ⟨hζ0, hre_lo, hre_lt1, _, _, him_lo, him_hi⟩ := hm_info m hm₀
    have hre_gt : 1 / 2 < (ρ_sel m).re := by linarith
    have hRγ : R + 1 ≤ (ρ_sel m).im := by linarith
    have hshort_m : ∑ n ∈ Finset.Icc 2 X₁,
        ‖_root_.RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-(ρ_sel m).re) ≤ 1 / 8 := by
      refine (Finset.sum_le_sum fun n hn => ?_).trans hshort
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (norm_nonneg _)
    have hhoriz_m : 5 * B * (X : ℝ) * Real.sqrt ((ρ_sel m).im + R + 6) *
        Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) ≤ 1 / 12 := by
      refine le_trans ?_ hhoriz
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity))
        (Real.exp_pos _).le
    have hsp := integral_normSq_zetaMollified_criticalLine_spike_of_zero hζ0 hre_gt hR1 hRγ
      hα hY hYα hB hX hX₁ hYX₁ hslope hb1 hb hshort_m htail hvtail hhoriz_m
    refine le_trans ?_ hsp
    have hd_sq : ((ρ_sel m).re - 1 / 2) ^ 2 ≤ 1 / 4 := by
      have hd1 : (ρ_sel m).re - 1 / 2 ≤ 1 / 2 := by linarith
      calc ((ρ_sel m).re - 1 / 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (by linarith) hd1 2
        _ = 1 / 4 := by norm_num
    have hexp_ge : Real.exp (-(α / 2)) ≤ Real.exp (-2 * α * ((ρ_sel m).re - 1 / 2) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hY_ge : Y ^ (2 * δ) ≤ Y ^ (2 * ((ρ_sel m).re - 1 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    have hd_ge : (3 / 4 : ℝ) * δ ≤ (3 / 4 : ℝ) * ((ρ_sel m).re - 1 / 2) := by linarith
    exact mul_le_mul (mul_le_mul hd_ge hexp_ge (Real.exp_pos _).le (by positivity))
      hY_ge (by positivity) (by positivity)
  have hsum_le := sum_Ioc_integral_le_intervalIntegral
    (a := V - R - 3) (b := 2 * V + R + 3) (by linarith)
    (continuous_norm_sq_zeta_mul_edPoly b X (by norm_num))
    (fun _ => by positivity)
    (fun m _ => by linarith) hsub_Ioc hdisj
  calc ((S.card : ℝ) / (P_R : ℝ)) * ((3 / 4 : ℝ) * δ * Real.exp (-(α / 2)) * Y ^ (2 * δ))
      ≤ (B₀.card : ℝ) * ((3 / 4 : ℝ) * δ * Real.exp (-(α / 2)) * Y ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_right hcard_div (by positivity)
    _ = ∑ _m ∈ B₀, (3 / 4 : ℝ) * δ * Real.exp (-(α / 2)) * Y ^ (2 * δ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ B₀, ∫ t in ((ρ_sel m).im - R)..((ρ_sel m).im + R),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        Finset.sum_le_sum hspike_m
    _ ≤ _ := hsum_le

/-- **Sharp `e^{-2 α δ²}` multi-window critical-line zero spikes (`α ≤ log Y`).**
Whenever `α ≤ Real.log Y`, the function `u ↦ -2 α u² + 2 u log Y` is nondecreasing on `[δ, 1/2]`,
sharpening `occupiedBurnolWindows_criticalLine_spike_ge` from `e^{-α / 2}` to `e^{-2 α δ²}`. -/
theorem occupiedBurnolWindows_criticalLine_sharp_spike_ge
    {V δ R α Y B : ℝ} (hR1 : 1 ≤ R) (hRV : R + 4 ≤ V) (hδ0 : 0 < δ)
    (hα : 0 < α) (hY : 1 ≤ Y) (hYα : 2 * Real.sqrt α ≤ Real.log Y)
    (hα_le_logY : α ≤ Real.log Y) (hB : 1 ≤ B)
    {X X₁ : ℕ} (hX : 1 ≤ X) (hX₁ : 1 ≤ X₁) (hYX₁ : Y < (X₁ : ℝ))
    (hslope : 5 * α ≤ Real.log (X₁ : ℝ) - Real.log Y)
    {b : ℕ → ℂ} (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B)
    (hshort : ∑ n ∈ Finset.Icc 2 X₁,
      ‖_root_.RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-(1 / 2 + δ)) ≤ 1 / 8)
    (htail : 2 * B * (Real.sqrt α / (Real.log (X₁ : ℝ) - Real.log Y)) *
      (X₁ : ℝ) ^ (3 / 2 : ℝ) *
      Real.exp (-(Real.log (X₁ : ℝ) - Real.log Y) ^ 2 / (4 * α)) ≤ 1 / 12)
    (hvtail : 4 * B * (1 / Real.sqrt α) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) ≤ 1 / 12)
    (hhoriz : 5 * B * (X : ℝ) * Real.sqrt (2 * V + R + 9) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) ≤ 1 / 12)
    {S : Finset ℕ} (hS_sub : S ⊆ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)))
    (hS_occ : ∀ m ∈ S, ∃ ρ ∈ burnolUnitXiZeros m, δ ≤ |ρ.re - 1 / 2|) :
    ((S.card : ℝ) / (Nat.ceil (2 * R + 7) : ℝ)) *
        ((3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ)) ≤
      ∫ t in (V - R - 3)..(2 * V + R + 3),
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  classical
  have hV_pos : 0 < V := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  set P_R : ℕ := Nat.ceil (2 * R + 7) with hP_R_def
  have hP_R_pos : 0 < P_R := Nat.ceil_pos.mpr (by positivity)
  have hP_R_ge : 2 * R + 7 ≤ (P_R : ℝ) := Nat.le_ceil (2 * R + 7)
  have hP_R_cast_pos : (0 : ℝ) < (P_R : ℝ) := by exact_mod_cast hP_R_pos
  have hex_right : ∀ m ∈ S, ∃ ρ ∈ burnolUnitXiZeros m, 1 / 2 + δ ≤ ρ.re := by
    intro m hm
    obtain ⟨ρ, hρ_mem, hρ_abs⟩ := hS_occ m hm
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
    · refine ⟨ρ, hρ_mem, ?_⟩
      rw [abs_of_nonneg (by linarith)] at hρ_abs; linarith
    · refine ⟨1 - star ρ, one_sub_star_mem_burnolUnitXiZeros m ρ hρ_mem, ?_⟩
      rw [abs_of_neg (by linarith)] at hρ_abs
      have hre_star : (1 - star ρ).re = 1 - ρ.re := by simp
      linarith
  let ρ_sel : ℕ → ℂ := fun m =>
    if hm : m ∈ S then Classical.choose (hex_right m hm) else 0
  have hρ_prop : ∀ m (hm : m ∈ S),
      ρ_sel m ∈ burnolUnitXiZeros m ∧ 1 / 2 + δ ≤ (ρ_sel m).re := by
    intro m hm; dsimp [ρ_sel]; rw [dif_pos hm]; exact Classical.choose_spec (hex_right m hm)
  obtain ⟨j₀, hj₀_card⟩ := finset_exists_mod_class_card_ge hP_R_pos S
  set B₀ : Finset ℕ := S.filter (fun m => m % P_R = j₀.val) with hB₀_def
  have hcard_div : (S.card : ℝ) / (P_R : ℝ) ≤ (B₀.card : ℝ) := by
    rw [div_le_iff₀ hP_R_cast_pos, mul_comm]
    exact_mod_cast hj₀_card
  have hm_info : ∀ m ∈ B₀,
      riemannZeta (ρ_sel m) = 0 ∧ 1 / 2 + δ ≤ (ρ_sel m).re ∧ (ρ_sel m).re < 1 ∧
      (m : ℝ) - 3 < (ρ_sel m).im ∧ (ρ_sel m).im < (m : ℝ) + 3 ∧
      V - 3 < (ρ_sel m).im ∧ (ρ_sel m).im < 2 * V + 3 := by
    intro m hm₀
    have hmS : m ∈ S := (Finset.mem_filter.mp hm₀).1
    have hmIcc : m ∈ Finset.Icc (Nat.ceil V) (Nat.floor (2 * V)) := hS_sub hmS
    obtain ⟨hρ_mem, hρ_re_lo⟩ := hρ_prop m hmS
    have hρ_iff := (mem_burnolUnitXiZeros_iff m (ρ_sel m)).mp hρ_mem
    have hcoords := burnolUnit_coords m
    have hm_lo : V ≤ (m : ℝ) := (Nat.le_ceil V).trans (by exact_mod_cast (Finset.mem_Icc.mp hmIcc).1)
    have hm_hi : (m : ℝ) ≤ 2 * V :=
      (by exact_mod_cast (Finset.mem_Icc.mp hmIcc).2 : (m : ℝ) ≤ (Nat.floor (2 * V) : ℝ)).trans
        (Nat.floor_le (by positivity))
    have hre_pos : 0 < (ρ_sel m).re := by linarith
    have hne1 : ρ_sel m ≠ 1 := by
      intro h1; rw [h1, Complex.one_re] at hρ_iff; exact lt_irrefl 1 hρ_iff.1.2.1
    have hζ0 : riemannZeta (ρ_sel m) = 0 :=
      (_root_.RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hre_pos hne1).mp hρ_iff.2
    refine ⟨hζ0, hρ_re_lo, hρ_iff.1.2.1, ?_, ?_, ?_, ?_⟩
    · linarith [hcoords.2.2.1, hcoords.2.2.2.2, hρ_iff.1.2.2.1]
    · linarith [hcoords.2.2.2.1, hρ_iff.1.2.2.2]
    · linarith [hcoords.2.2.1, hcoords.2.2.2.2, hρ_iff.1.2.2.1]
    · linarith [hcoords.2.2.2.1, hρ_iff.1.2.2.2]
  have hsub_Ioc : ∀ m ∈ B₀,
      Ioc ((ρ_sel m).im - R) ((ρ_sel m).im + R) ⊆ Ioc (V - R - 3) (2 * V + R + 3) := by
    intro m hm₀ t ht
    obtain ⟨_, _, _, _, _, him_lo, him_hi⟩ := hm_info m hm₀
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdisj : (B₀ : Set ℕ).PairwiseDisjoint
      (fun m => Ioc ((ρ_sel m).im - R) ((ρ_sel m).im + R)) := by
    intro m₁ hm₁ m₂ hm₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro t ht₁ ht₂
    rw [Finset.mem_coe, hB₀_def, Finset.mem_filter] at hm₁ hm₂
    have hmod : m₁ % P_R = m₂ % P_R := hm₁.2.trans hm₂.2.symm
    obtain ⟨_, _, _, hm₁_lo, hm₁_hi, _, _⟩ := hm_info m₁ (Finset.mem_filter.mpr hm₁)
    obtain ⟨_, _, _, hm₂_lo, hm₂_hi, _, _⟩ := hm_info m₂ (Finset.mem_filter.mpr hm₂)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : m₁ + P_R ≤ m₂ := nat_add_le_of_lt_of_mod_eq hlt hmod
      have hstep_r : (m₁ : ℝ) + (P_R : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hstep
      linarith [ht₁.2, ht₂.1]
    · have hstep : m₂ + P_R ≤ m₁ := nat_add_le_of_lt_of_mod_eq hgt hmod.symm
      have hstep_r : (m₂ : ℝ) + (P_R : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast hstep
      linarith [ht₂.2, ht₁.1]
  have hspike_m : ∀ m ∈ B₀,
      (3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ) ≤
        ∫ t in ((ρ_sel m).im - R)..((ρ_sel m).im + R),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro m hm₀
    obtain ⟨hζ0, hre_lo, hre_lt1, _, _, him_lo, him_hi⟩ := hm_info m hm₀
    have hre_gt : 1 / 2 < (ρ_sel m).re := by linarith
    have hRγ : R + 1 ≤ (ρ_sel m).im := by linarith
    have hshort_m : ∑ n ∈ Finset.Icc 2 X₁,
        ‖_root_.RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-(ρ_sel m).re) ≤ 1 / 8 := by
      refine (Finset.sum_le_sum fun n hn => ?_).trans hshort
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (norm_nonneg _)
    have hhoriz_m : 5 * B * (X : ℝ) * Real.sqrt ((ρ_sel m).im + R + 6) *
        Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) ≤ 1 / 12 := by
      refine le_trans ?_ hhoriz
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity))
        (Real.exp_pos _).le
    have hsp := integral_normSq_zetaMollified_criticalLine_spike_of_zero hζ0 hre_gt hR1 hRγ
      hα hY hYα hB hX hX₁ hYX₁ hslope hb1 hb hshort_m htail hvtail hhoriz_m
    refine le_trans ?_ hsp
    set u : ℝ := (ρ_sel m).re - 1 / 2
    have hu_ge : δ ≤ u := by linarith
    have hu_lt : u < 1 / 2 := by linarith
    have hδ_lt : δ < 1 / 2 := lt_of_le_of_lt hu_ge hu_lt
    have hexp_mono : Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ) ≤
        Real.exp (-2 * α * u ^ 2) * Y ^ (2 * u) := by
      rw [Real.rpow_def_of_pos hY0, Real.rpow_def_of_pos hY0, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hdiff : (-2 * α * u ^ 2 + Real.log Y * (2 * u)) -
          (-2 * α * δ ^ 2 + Real.log Y * (2 * δ)) =
          2 * (u - δ) * (Real.log Y - α * (u + δ)) := by ring
      have hsum_le1 : u + δ ≤ 1 := by linarith
      have hfac : 0 ≤ Real.log Y - α * (u + δ) := by nlinarith
      nlinarith
    have hd_ge : (3 / 4 : ℝ) * δ ≤ (3 / 4 : ℝ) * u := by linarith
    calc (3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ)
        = ((3 / 4 : ℝ) * δ) * (Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ)) := by ring
      _ ≤ ((3 / 4 : ℝ) * u) * (Real.exp (-2 * α * u ^ 2) * Y ^ (2 * u)) :=
          mul_le_mul hd_ge hexp_mono (by positivity) (by positivity)
      _ = (3 / 4 : ℝ) * u * Real.exp (-2 * α * u ^ 2) * Y ^ (2 * u) := by ring
  have hsum_le := sum_Ioc_integral_le_intervalIntegral
    (a := V - R - 3) (b := 2 * V + R + 3) (by linarith)
    (continuous_norm_sq_zeta_mul_edPoly b X (by norm_num))
    (fun _ => by positivity)
    (fun m _ => by linarith) hsub_Ioc hdisj
  calc ((S.card : ℝ) / (P_R : ℝ)) * ((3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ))
      ≤ (B₀.card : ℝ) * ((3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ)) :=
        mul_le_mul_of_nonneg_right hcard_div (by positivity)
    _ = ∑ _m ∈ B₀, (3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ B₀, ∫ t in ((ρ_sel m).im - R)..((ρ_sel m).im + R),
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
        Finset.sum_le_sum hspike_m
    _ ≤ _ := hsum_le

/-- **Window-occupancy upper bound from a prefix-cancelling critical-line second moment (`D_win`).**
Rearranging `occupiedBurnolWindows_criticalLine_sharp_spike_ge` on the full set of `δ`-occupied
Burnol windows in `[⌈V⌉, ⌊2V⌋]` bounds the occupied window count directly by
`(4 / 3) ⌈2R + 7⌉₊ · e^{2 α δ²} · δ⁻¹ · Y^{-2δ} · Msq`. At depth `δ = A / log V` and cancellation
scale `Y = V^θ` (`θ > 0`), the critical-line spike factor `δ⁻¹ Y^{-2δ} = (log V / A) V^{-2θA / log V}
= (log V / A) e^{-2θA}` still carries an explicit `log V` factor unless `Y` is super-polynomial
(`log Y / log V → ∞`) or `Msq` already beats `V` by `(log V)⁻¹`. -/
theorem occupiedBurnolWindows_le_of_prefixCancelling_secondMoment
    {V δ R α Y B Msq : ℝ} (hR1 : 1 ≤ R) (hRV : R + 4 ≤ V) (hδ0 : 0 < δ)
    (hα : 0 < α) (hY : 1 ≤ Y) (hYα : 2 * Real.sqrt α ≤ Real.log Y)
    (hα_le_logY : α ≤ Real.log Y) (hB : 1 ≤ B)
    {X X₁ : ℕ} (hX : 1 ≤ X) (hX₁ : 1 ≤ X₁) (hYX₁ : Y < (X₁ : ℝ))
    (hslope : 5 * α ≤ Real.log (X₁ : ℝ) - Real.log Y)
    {b : ℕ → ℂ} (hb1 : b 1 = 1) (hb : ∀ d ∈ Finset.Icc 1 X, ‖b d‖ ≤ B)
    (hshort : ∑ n ∈ Finset.Icc 2 X₁,
      ‖_root_.RHTower.mollifiedZetaCoeff b X n‖ * (n : ℝ) ^ (-(1 / 2 + δ)) ≤ 1 / 8)
    (htail : 2 * B * (Real.sqrt α / (Real.log (X₁ : ℝ) - Real.log Y)) *
      (X₁ : ℝ) ^ (3 / 2 : ℝ) *
      Real.exp (-(Real.log (X₁ : ℝ) - Real.log Y) ^ 2 / (4 * α)) ≤ 1 / 12)
    (hvtail : 4 * B * (1 / Real.sqrt α) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2 / 2) ≤ 1 / 12)
    (hhoriz : 5 * B * (X : ℝ) * Real.sqrt (2 * V + R + 9) *
      Real.exp ((25 / 4) * α + (5 / 2) * Real.log Y - α * R ^ 2) ≤ 1 / 12)
    (hMsq : (∫ t in (V - R - 3)..(2 * V + R + 3),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        _root_.RHTower.edPoly b (Finset.Icc 1 X) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq) :
    (((Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
      (fun m => ∃ ρ ∈ burnolUnitXiZeros m, δ ≤ |ρ.re - 1 / 2|)).card : ℝ) ≤
      (4 / 3 : ℝ) * (Nat.ceil (2 * R + 7) : ℝ) * Real.exp (2 * α * δ ^ 2) *
        δ⁻¹ * Y ^ (-(2 * δ)) * Msq := by
  set S := (Finset.Icc (Nat.ceil V) (Nat.floor (2 * V))).filter
    (fun m => ∃ ρ ∈ burnolUnitXiZeros m, δ ≤ |ρ.re - 1 / 2|)
  have hsp := (occupiedBurnolWindows_criticalLine_sharp_spike_ge hR1 hRV hδ0 hα hY hYα hα_le_logY
    hB hX hX₁ hYX₁ hslope hb1 hb hshort htail hvtail hhoriz
    (Finset.filter_subset _ _) (fun m hm => (Finset.mem_filter.mp hm).2)).trans hMsq
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hP_pos : (0 : ℝ) < (Nat.ceil (2 * R + 7) : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr (by positivity : 0 < 2 * R + 7)
  have hfac_pos : 0 < (3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ) := by positivity
  have hcard_div : (S.card : ℝ) / (Nat.ceil (2 * R + 7) : ℝ) ≤
      Msq / ((3 / 4 : ℝ) * δ * Real.exp (-2 * α * δ ^ 2) * Y ^ (2 * δ)) :=
    (le_div_iff₀ hfac_pos).mpr hsp
  have hcard_le := (div_le_iff₀ hP_pos).mp hcard_div
  refine hcard_le.trans_eq ?_
  have hexp_inv : (Real.exp (-2 * α * δ ^ 2))⁻¹ = Real.exp (2 * α * δ ^ 2) := by
    rw [← Real.exp_neg]; congr 1; ring
  have hY_inv : (Y ^ (2 * δ))⁻¹ = Y ^ (-(2 * δ)) := (Real.rpow_neg hY0.le (2 * δ)).symm
  rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv, hexp_inv, hY_inv]
  ring

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.edPolyHermitianTrace_count_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_edPoly_line_logMean_floor_complex
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_left_floor_complex
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.exists_logIntegral_le_of_complex_secondMoment
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.criticalClustering_of_complexMollifiedSecondMomentLaw
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logFreeNearLineZeroDensity_of_complexSecondMomentRate
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.logFreeNearLineWindowOccupancy_of_complexSecondMomentRate
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_uniform_complex_necessary_length
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.eventually_log_mollifier_length_ge_of_excess
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.complexSecondMomentRate_forces_exp_logSq_length
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.not_complexSecondMomentRate_below_exp_logSq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.tendsto_log_length_div_log_atTop_of_complex_second_moment_tendsto_one
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_criticalLine_spike_ge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_criticalLine_sharp_spike_ge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.occupiedBurnolWindows_le_of_prefixCancelling_secondMoment
